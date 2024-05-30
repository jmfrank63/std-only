use std::{env, process::exit};

use std_only::Stack;
use std::str::FromStr;

enum Operation {
    Add,
    Subtract,
    Multiply,
    Divide,
}

fn perform_operation(stack: &mut Stack<i32>, operation: Operation) {
    let a = stack.pop().unwrap();
    let b = stack.pop().unwrap();

    let result = match operation {
        Operation::Add => a + b,
        Operation::Subtract => b - a,
        Operation::Multiply => b * b,
        Operation::Divide => {
            if a == 0 {
                eprintln!("Error: Division by zero");
                exit(0);
            }
            b / a
        },
    };

    stack.push(result);
}

type Result<T> = std::result::Result<T, ()>;

fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();

    if args.len() != 4 {
        eprintln!("Usage: calc a b [+|-|*|/]");
        return Ok(());
    }

    let a = i32::from_str(&args[1]).unwrap();
    let b = i32::from_str(&args[2]).unwrap();
    let operation = match args[3].as_str() {
        "+" => Operation::Add,
        "-" => Operation::Subtract,
        "*" => Operation::Multiply,
        "/" => Operation::Divide,
        _ => {
            eprintln!("Unknown operation. Use add, subtract, multiply, or divide.");
            return Ok(());
        }
    };

    let mut stack = Stack::default();
    stack.push(a);
    stack.push(b);
    perform_operation(&mut stack, operation);
    println!("Result: {}", stack.peek().unwrap());

    Ok(())
}
