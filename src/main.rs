use std::io::Write;

fn main() {
    loop {
        let Some(cmd) = readline() else {
            continue;
        };
        if let Some(r) = nrmcalc::calc(&cmd) {
            println!("{}", r);
        }
    }
}

fn readline() -> Option<String> {
    std::io::stdout().write(b"> ").ok()?;
    std::io::stdout().flush().unwrap();
    let mut cmd = String::new();
    std::io::stdin().read_line(&mut cmd).unwrap();
    Some(cmd)
}

