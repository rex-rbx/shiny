use cfg::{block::BranchType, function::Function};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};

use petgraph::{
    algo::dominators::{simple_fast, Dominators},
    stable_graph::{EdgeIndex, NodeIndex, StableDiGraph},
    visit::*,
};
use tuple::Map;

mod conditional;
mod jump;
mod r#loop;

// TODO: REFACTOR: move
pub fn post_dominators<N: Default, E: Default>(
    graph: &mut StableDiGraph<N, E>,
) -> Dominators<NodeIndex> {
    let exits = graph
        .node_identifiers()
        .filter(|&n| graph.neighbors(n).count() == 0)
        .collect_vec();
    let fake_exit = graph.add_node(Default::default());
    for exit in exits {
        graph.add_edge(exit, fake_exit, Default::default());
    }
    let res = simple_fast(Reversed(&*graph), fake_exit);
    assert!(graph.remove_node(fake_exit).is_some());
    res
}

struct GraphStructurer {
    pub function: Function,
    loop_headers: FxHashSet<NodeIndex>,
    label_to_node: FxHashMap<ast::Label, NodeIndex>,
}

impl GraphStructurer {
    fn find_loop_headers(&mut self) {
        self.loop_headers.clear();
        depth_first_search(
            self.function.graph(),
            Some(self.function.entry().unwrap()),
            |event| {
                if let DfsEvent::BackEdge(_, header) = event {
                    self.loop_headers.insert(header);
                }
            },
        );
    }
    fn new(function: Function) -> Self {
        let mut this = Self {
            function,
            loop_headers: FxHashSet::default(),
            label_to_node: FxHashMap::default(),
        };
        this.find_loop_headers();
        this
    }

    fn block_is_no_op(block: &ast::Block) -> bool {
        !block.iter().any(|s| s.as_comment().is_none())
    }

    fn statement_is_inlineable(statement: &ast::Statement) -> bool {
        matches!(
            statement,
            ast::Statement::Empty(_)
                | ast::Statement::Call(_)
                | ast::Statement::MethodCall(_)
                | ast::Statement::Assign(_)
                | ast::Statement::Return(_)
                | ast::Statement::Close(_)
                | ast::Statement::SetList(_)
                | ast::Statement::Comment(_)
        )
    }

    fn inlineable_block(block: &ast::Block) -> Option<ast::Block> {
        let skip = usize::from(block.first().and_then(|s| s.as_label()).is_some());
        if block.iter().skip(skip).all(Self::statement_is_inlineable) {
            Some(block.iter().skip(skip).cloned().collect_vec().into())
        } else {
            None
        }
    }

    fn collect_labels(block: &ast::Block, labels: &mut Vec<ast::Label>) {
        for statement in &block.0 {
            match statement {
                ast::Statement::Label(label) => labels.push(label.clone()),
                ast::Statement::If(r#if) => {
                    Self::collect_labels(&r#if.then_block.lock(), labels);
                    Self::collect_labels(&r#if.else_block.lock(), labels);
                }
                ast::Statement::While(r#while) => {
                    Self::collect_labels(&r#while.block.lock(), labels);
                }
                ast::Statement::Repeat(repeat) => {
                    Self::collect_labels(&repeat.block.lock(), labels);
                }
                ast::Statement::NumericFor(numeric_for) => {
                    Self::collect_labels(&numeric_for.block.lock(), labels);
                }
                ast::Statement::GenericFor(generic_for) => {
                    Self::collect_labels(&generic_for.block.lock(), labels);
                }
                _ => {}
            }
        }
    }

    fn remap_labels(&mut self, block: &ast::Block, node: NodeIndex) {
        let mut labels = Vec::new();
        Self::collect_labels(block, &mut labels);
        for label in labels {
            self.label_to_node.insert(label, node);
        }
    }

    fn try_match_pattern(
        &mut self,
        node: NodeIndex,
        dominators: &Dominators<NodeIndex>,
        post_dom: &Dominators<NodeIndex>,
    ) -> bool {
        let successors = self.function.successor_blocks(node).collect_vec();

        // cfg::dot::render_to(&self.function, &mut std::io::stdout()).unwrap();
        if self.try_collapse_loop(node, dominators, post_dom) {
            self.find_loop_headers();
            // println!("matched loop");
            return true;
        }

        if self.try_remove_unnecessary_condition(node) {
            return true;
        }

        let changed = match successors.len() {
            0 => false,
            1 => {
                // remove unnecessary jumps to allow pattern matching
                self.match_jump(node, Some(successors[0]))
            }
            2 => {
                let (then_target, else_target) = self
                    .function
                    .conditional_edges(node)
                    .unwrap()
                    .map(|e| e.target());
                self.match_conditional(node, then_target, else_target)
            }

            _ => unreachable!(),
        };

        //println!("after");
        //dot::render_to(&self.function, &mut std::io::stdout()).unwrap();

        changed
    }

    fn match_blocks(&mut self) -> bool {
        let dfs = Dfs::new(self.function.graph(), self.function.entry().unwrap())
            .iter(self.function.graph())
            .collect::<FxHashSet<_>>();
        let mut dfs_postorder =
            DfsPostOrder::new(self.function.graph(), self.function.entry().unwrap());
        let mut dominators = simple_fast(self.function.graph(), self.function.entry().unwrap());
        let mut post_dom = post_dominators(self.function.graph_mut());

        // cfg::dot::render_to(&self.function, &mut std::io::stdout()).unwrap();

        let mut changed = false;
        while let Some(node) = dfs_postorder.next(self.function.graph()) {
            // println!("matching {:?}", node);
            let matched = self.try_match_pattern(node, &dominators, &post_dom);
            if matched {
                dominators = simple_fast(self.function.graph(), self.function.entry().unwrap());
                post_dom = post_dominators(self.function.graph_mut());
            }
            changed |= matched;
            // if matched {
            //     cfg::dot::render_to(&self.function, &mut std::io::stdout()).unwrap();
            // }
        }

        for node in self
            .function
            .graph()
            .node_indices()
            .filter(|node| !dfs.contains(node))
            .collect_vec()
        {
            // block may have been removed in a previous iteration
            if self.function.has_block(node)
                && self.function.predecessor_blocks(node).next().is_none()
            {
                if self
                    .function
                    .block(node)
                    .unwrap()
                    .first()
                    .and_then(|s| s.as_label())
                    .is_none()
                {
                    self.function.remove_block(node);
                } else {
                    //let dominators = simple_fast(self.function.graph(), node);
                    let matched = self.try_match_pattern(node, &dominators, &post_dom);
                    changed |= matched;
                }
            }
        }

        changed
    }

    fn insert_goto_for_edge(&mut self, edge: EdgeIndex) {
        let (source, target) = self.function.graph().edge_endpoints(edge).unwrap();
        if self.function.graph().edge_weight(edge).unwrap().branch_type == BranchType::Unconditional
            && self.function.predecessor_blocks(target).count() == 1
        {
            assert!(self.function.successor_blocks(source).count() == 1);
            // TODO: this code is repeated in match_jump, move to a new function
            let edges = self.function.remove_edges(target);
            let block = self.function.remove_block(target).unwrap();
            self.remap_labels(&block, source);
            self.function.block_mut(source).unwrap().extend(block.0);
            self.function.set_edges(source, edges);
        } else if self.function.entry() != &Some(target)
            && !self.is_loop_header(target)
            && !self.is_for_next(target)
            && let Some(block) = Self::inlineable_block(self.function.block(target).unwrap())
        {
            let edges = self
                .function
                .edges(target)
                .map(|e| (e.target(), e.weight().clone()))
                .collect_vec();
            self.function.block_mut(source).unwrap().extend(block.0);
            self.function.set_edges(source, edges);
        } else {
            // TODO: make label an Rc and have a global counter for block name
            let label = ast::Label(format!("l{}", target.index()));
            let target_block = self.function.block_mut(target).unwrap();
            if target_block.first().and_then(|s| s.as_label()).is_none() {
                self.label_to_node.insert(label.clone(), target);
                target_block.insert(0, label.clone().into());
            }
            let goto_block = self.function.new_block();
            self.function
                .block_mut(goto_block)
                .unwrap()
                .push(ast::Goto::new(label).into());

            let edge = self.function.graph_mut().remove_edge(edge).unwrap();
            self.function.graph_mut().add_edge(source, goto_block, edge);
        }
    }

    fn remove_last_return(block: ast::Block) -> ast::Block {
        if let Some(ast::Statement::Return(last_statement)) = block.last() {
            if last_statement.values.is_empty() {
                let take = block.len() - 1;
                return block.0.into_iter().take(take).collect_vec().into();
            }
        }
        block
    }

    fn collapse(&mut self) {
        loop {
            while self.match_blocks() {}
            if self.function.graph().node_count() == 1 {
                break;
            }
            // last resort refinement
            let edges = self.function.graph().edge_indices().collect::<Vec<_>>();
            // https://edmcman.github.io/papers/usenix13.pdf
            // we prefer to remove edges whose source does not dominate its target, nor whose target dominates its source
            // TODO: try all possible paths and return the one with the least gotos, i don't think there's any other way
            // to get best output
            let mut changed = false;
            for &edge in &edges {
                // edge might have been invalidated by a previous iteration due to insert_goto_for_edge
                // calling remove_block(target)
                if self.function.graph().edge_weight(edge).is_none() {
                    continue;
                }

                let (source, target) = self.function.graph().edge_endpoints(edge).unwrap();
                let dominators = simple_fast(self.function.graph(), self.function.entry().unwrap());
                let target_dominators = dominators.dominators(target);
                let source_dominators = dominators.dominators(source);
                // TODO: check if blocks in dfs instead
                if target_dominators.is_none() || source_dominators.is_none() {
                    continue;
                }
                let mut target_dominators = target_dominators.unwrap();
                let mut source_dominators = source_dominators.unwrap();
                if target_dominators.contains(&source) || source_dominators.contains(&target) {
                    continue;
                }

                changed = self.try_refine_with_edge(edge);
                if changed {
                    break;
                }
            }

            if !changed {
                for edge in edges {
                    // edge might have been invalidated by a previous iteration due to insert_goto_for_edge
                    // calling remove_block(target)
                    if self.function.graph().edge_weight(edge).is_none() {
                        continue;
                    }
                    changed = self.try_refine_with_edge(edge);
                    if changed {
                        break;
                    }
                }
                if !changed {
                    break;
                }
            }
        }
    }

    fn try_refine_with_edge(&mut self, edge: EdgeIndex) -> bool {
        let function_snapshot = self.function.clone();
        let loop_headers_snapshot = self.loop_headers.clone();
        let label_to_node_snapshot = self.label_to_node.clone();

        self.insert_goto_for_edge(edge);
        self.find_loop_headers();
        if self.match_blocks() {
            true
        } else {
            self.function = function_snapshot;
            self.loop_headers = loop_headers_snapshot;
            self.label_to_node = label_to_node_snapshot;
            false
        }
    }

    fn structure(mut self) -> ast::Block {
        self.collapse();
        if self.function.graph().node_count() != 1 {
            let mut res_block = ast::Block::default();
            let entry = self.function.entry().unwrap();
            let mut stack = vec![entry];
            let mut visited = FxHashSet::default();
            while let Some(node) = stack.pop() {
                if visited.contains(&node) {
                    continue;
                }
                visited.insert(node);

                fn collect_gotos(block: &ast::Block, gotos: &mut Vec<ast::Label>) {
                    for statement in &block.0 {
                        match statement {
                            ast::Statement::Goto(goto) => {
                                gotos.push(goto.0.clone());
                            }
                            ast::Statement::If(r#if) => {
                                collect_gotos(&r#if.then_block.lock(), gotos);
                                collect_gotos(&r#if.else_block.lock(), gotos);
                            }
                            ast::Statement::While(r#while) => {
                                collect_gotos(&r#while.block.lock(), gotos);
                            }
                            ast::Statement::Repeat(repeat) => {
                                collect_gotos(&repeat.block.lock(), gotos);
                            }
                            ast::Statement::NumericFor(numeric_for) => {
                                collect_gotos(&numeric_for.block.lock(), gotos);
                            }
                            ast::Statement::GenericFor(generic_for) => {
                                collect_gotos(&generic_for.block.lock(), gotos);
                            }
                            _ => {}
                        }
                    }
                }

                let block = self.function.remove_block(node).unwrap();
                let mut goto_destinations = Vec::new();
                collect_gotos(&block, &mut goto_destinations);
                let mut seen_goto_destinations = FxHashSet::default();
                for label in goto_destinations {
                    if !seen_goto_destinations.insert(label.clone()) {
                        continue;
                    }
                    // TODO: block might have been merged/structured into another, output that block instead
                    // will require collecting label definitions in addition to references (gotos)
                    let target_node = self.label_to_node[&label];
                    if self.function.has_block(target_node) {
                        stack.push(target_node);
                    }
                }
                if let Some(ast::Statement::Goto(goto)) = res_block.last()
                // TODO: keep label -> block map instead
                    && goto.0.0[1..] == node.index().to_string()
                {
                    res_block.pop();
                }
                if !block
                    .first()
                    .is_some_and(|s| matches!(s, ast::Statement::Label(_)))
                {
                    res_block.push(ast::Comment::new(format!("block {}", node.index())).into());
                }
                res_block.extend(block.0)
            }
            // TODO: these nodes are never executed (i think), comment them out or dont include them
            for node in self.function.graph().node_indices().collect::<Vec<_>>() {
                let block = self.function.remove_block(node).unwrap();
                if !block
                    .first()
                    .is_some_and(|s| matches!(s, ast::Statement::Label(_)))
                {
                    res_block.push(ast::Comment::new(format!("block {}", node.index())).into());
                }
                res_block.extend(block.0)
            }

            res_block
        } else {
            Self::remove_last_return(
                self.function
                    .remove_block(self.function.entry().unwrap())
                    .unwrap(),
            )
        }
    }
}

pub fn lift(function: cfg::function::Function) -> ast::Block {
    GraphStructurer::new(function).structure()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn remap_labels_recurses_into_nested_blocks() {
        let mut function = Function::new(0);
        let node = function.new_block();
        function.set_entry(node);

        let mut inner_block = ast::Block::default();
        inner_block.push(ast::Label::from("inner").into());
        let outer_block = ast::Block::from(vec![
            ast::If::new(
                ast::Literal::Boolean(true).into(),
                inner_block,
                ast::Block::default(),
            )
            .into(),
        ]);

        let mut structurer = GraphStructurer::new(function);
        structurer.remap_labels(&outer_block, node);

        assert_eq!(
            structurer.label_to_node.get(&ast::Label::from("inner")).copied(),
            Some(node)
        );
    }

    #[test]
    fn inlineable_block_strips_leading_label() {
        let block = ast::Block::from(vec![
            ast::Label::from("target").into(),
            ast::Assign::new(
                vec![ast::RcLocal::default().into()],
                vec![ast::Literal::Boolean(true).into()],
            )
            .into(),
        ]);

        let inlineable = GraphStructurer::inlineable_block(&block).unwrap();
        assert!(inlineable.first().and_then(|s| s.as_label()).is_none());
        assert!(matches!(inlineable.last(), Some(ast::Statement::Assign(_))));
    }

    #[test]
    fn match_jump_inlines_simple_target_blocks() {
        let mut function = Function::new(0);
        let source = function.new_block();
        let target = function.new_block();
        let other_pred = function.new_block();

        function.set_entry(source);
        function.block_mut(target).unwrap().push(
            ast::Assign::new(
                vec![ast::RcLocal::default().into()],
                vec![ast::Literal::Boolean(true).into()],
            )
            .into(),
        );
        function.block_mut(target).unwrap().push(ast::Return::new(vec![]).into());

        function.set_edges(
            source,
            vec![(target, cfg::block::BlockEdge::new(cfg::block::BranchType::Unconditional))],
        );
        function.set_edges(
            other_pred,
            vec![(target, cfg::block::BlockEdge::new(cfg::block::BranchType::Unconditional))],
        );

        let mut structurer = GraphStructurer::new(function);
        assert!(structurer.match_jump(source, Some(target)));

        let source_block = structurer.function.block(source).unwrap();
        assert_eq!(source_block.len(), 2);
        assert!(source_block.iter().all(|s| s.as_goto().is_none()));
        assert!(matches!(source_block.last(), Some(ast::Statement::Return(_))));
        assert!(structurer.function.has_block(target));
    }
}
