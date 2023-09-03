use std::io::Write;

fn main() {
    let mut calc = nrmcalc::Calc::new();
    loop {
        let Some(cmd) = readline() else {
            continue;
        };
        let cmd = cmd.trim_end_matches(['\r', '\n']);
        if let Some(r) = calc.calc(&cmd) {
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

