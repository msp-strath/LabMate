28.06.2024
[ ] Check the damage if we *switch off* rigid-rigid solving for matrices.
[ ] Limit the damage by waiting for matrix types to propagate instead of inventing them.
[ ] Relax compatibility for multiplication, don't insist on the *same* middle. Make sure the compatibility check is stable under header list wrangling.
[ ] Substitute out nonempty uniform header lists making the header type One.
[ ] If the header type is Abel and the header list is Cons, divide all the headers by the head header (making it unit). Fix up the cell type by substitution.
[ ] See if we need any equation solving on matrix types at all.

26.08.2024

[ ] Emacs minor mode to hide generated code
[ ] Combine dimensions directive with standard units (add comment explaining that generated code is in order to make sense for MATLAB)
[ ] Make One = Abel (Enum nil)
[ ] Do division
[ ] Do transpose
[ ] Main target: Matrices of dimensioned constants
[ ] Main target: Matrix multiplication

27.08.2024

[ ] Do addition
