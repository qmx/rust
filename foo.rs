fn main() {
    let mut i = 0;
    let mut next_int = move || {
        i += 1;
        i
    }; 
    let mut next_int_2 = next_int;
    
    println!("next_int = {}", next_int());
    println!("next_int = {}", next_int());
    println!("next_int = {}", next_int());
    println!("next_int_2 = {}", next_int_2());
    println!("i = {}", i);
}
