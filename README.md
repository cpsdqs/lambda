# lambda
Small lambda calculus evaluator

## Usage
- Clone the repository
- Ensure [`cargo`](https://www.rust-lang.org/) is installed
- `cargo run`

### Examples
```
true := λa.λb.a
false := λa.λb.b
and := λa.λb.a b a
or := λa.λb.a a b
not := λa.a false true

not true
-> false
or true false
-> true
and true false
-> false
and true (not false)
-> true
or true
-> λb.true true b
and true
-> λb.true b true
```
