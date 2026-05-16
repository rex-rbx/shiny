use axum::{
    Router,
    body::Bytes,
    extract::Query,
    routing::{get, post},
    response::Json,
};
use tower_http::services::{ServeDir, ServeFile};
use serde::{Deserialize, Serialize};
use tokio::net::TcpListener;
use tokio::time::{interval, Duration};
use tokio::io::AsyncWriteExt;
use tracing::info;
use crate::commands::decompile_no_io;

pub async fn serve(port: u16, luau: bool, lua51: bool) -> Result<(), std::io::Error> {
    let mut app = Router::new()
        .route("/health", get(health))
        .route("/ping", get(ping));

    if luau {
        app = app.route("/luau/decompile", post(decompile_luau));
    }
    if lua51 {
        app = app.route("/lua51/decompile", post(decompile_lua51));
    }

    app = app.fallback_service(
        ServeDir::new("public").fallback(ServeFile::new("public/index.html"))
    );

    let listener = TcpListener::bind(format!("0.0.0.0:{port}")).await?;
    info!("🚀 Listening on {}", listener.local_addr()?);

    tokio::spawn(self_ping_task(port));

    axum::serve(listener, app).await
}

#[derive(Serialize)]
struct HealthResponse {
    status: &'static str,
    timestamp: String,
}

async fn health() -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "OK",
        timestamp: chrono::Utc::now().to_rfc3339(),
    })
}

async fn ping() -> &'static str {
    "pong"
}

async fn self_ping_task(port: u16) {
    let mut ticker = interval(Duration::from_secs(60));
    loop {
        ticker.tick().await;
        for i in 1..=3u8 {
            tokio::time::sleep(Duration::from_millis((i as u64 - 1) * 200)).await;
            let request = format!(
                "GET /health HTTP/1.1\r\nHost: localhost:{port}\r\nConnection: close\r\n\r\n"
            );
            match tokio::net::TcpStream::connect(format!("127.0.0.1:{port}")).await {
                Ok(mut stream) => {
                    let _ = stream.write_all(request.as_bytes()).await;
                    info!("Self-ping #{i}: sent");
                }
                Err(e) => tracing::error!("Self-ping #{i} failed: {e}"),
            }
        }
    }
}

#[inline]
pub const fn default_encode_key() -> u8 {
    203
}

#[derive(Deserialize)]
struct EncodeKey {
    #[serde(default = "default_encode_key")]
    encode_key: u8,
}

async fn decompile_luau(query: Query<EncodeKey>, body: Bytes) -> String {
    decompile_no_io(body, query.encode_key, false)
}

async fn decompile_lua51(body: Bytes) -> String {
    decompile_no_io(body, default_encode_key(), true)
}