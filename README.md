# Finite Field
A pure Rust implementation of Finite Field Elements with no third party dependencies.
It is a generic implementation which is currently implemented for all unsigned integer types in Rust.
It could also be easily extended for signed versions as well.

# Operations
All the basic math operation are supported over the finite field:
- Addition
- Substraction
- Multiplication
- Division
- Modulo
- Pow

Identities for addition and multiplication are also coded dependant on the type in the finite field.
Typically the Additive Identity is 0 and the Multiplication Identity is 1.
