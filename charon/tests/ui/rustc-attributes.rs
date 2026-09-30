#[unsafe(export_name = "exported")]
fn export_name() {}

#[unsafe(link_section = "__TEXT,__custom")]
fn link_section() {}
