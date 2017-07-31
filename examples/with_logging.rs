extern crate env_logger;

#[macro_use]
extern crate log;

extern crate lz_diet;

use lz_diet::Diet;
use std::borrow::Cow;

pub fn main() {
    env_logger::init().expect("failed to initialize logger");

    let mut diet = Diet::new();

    diet.insert(1);

    diet.insert(3);

    diet.insert(5);

    info!("Diet: {:?}", diet);

    diet.insert(2);

    diet.insert(4);

    info!("Diet: {:?}", diet);

    diet.remove(Cow::Owned(4));

    info!("Diet: {:?}", diet);

    diet.remove(Cow::Owned(2));

    info!("Diet: {:?}", diet);
}
