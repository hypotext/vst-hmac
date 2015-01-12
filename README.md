In progress. Many technical lemmas are still admitted, and some assumptions regarding length need to be added.

The theorems relating each spec are as such:
1. abstract <- - -> 2. list <-> 3. concat <-> 4. pad <- - ->
5. HMAC_functional_prog_Z <-> 6. HMAC_functional_prog

where <-> indicates equality and <- - -> indicates equivalence.

The theorem relating spec 1 with spec 2 is located in the file for spec 1, and so on for the rest.

See the paper for more documentation: VST_HMAC_Paper.pdf

TODO: 
- check that the framework relating vector to list is admissible
- add and prove assumptions regarding length and blocks
- prove front ~ FRONT, back ~ BACK
- bits to bytes proofs
- Z, byte in range in specs 5 and 6
- technical lemmas throughout the structure
