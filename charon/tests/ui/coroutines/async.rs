//@ known-failure
//@ charon-args=--mir elaborated

async fn unit() {}

async fn chain() {
    unit().await
}
