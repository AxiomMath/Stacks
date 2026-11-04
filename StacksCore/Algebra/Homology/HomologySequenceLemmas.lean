module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
import StacksCore.Tactic.StacksAttribute

/-! # The long exact homology sequence

Stacks tags 0111 for chain complexes and 0117 for cochain complexes. A short exact sequence
`0 → A → B → C → 0` of complexes gives an exact sequence

`Hᵢ(A) → Hᵢ(B) → Hᵢ(C) →ᵟ Hⱼ(A) → Hⱼ(B) → Hⱼ(C)`

for every step `c.Rel i j` of the complex shape, which is `j = i - 1` for chain complexes and
`j = i + 1` for cochain complexes. Mathlib assembles it as a `ComposableArrows C 5`, and iterating
over the steps of the shape is what recovers the doubly infinite sequence the Stacks project
draws.

Of the three clauses of 0117 the first two are recorded below: the sequence, and its
functoriality in the short exact sequence. The third, compatibility with shifts, is stated
against the identification `H^{i+k}(A) ≅ Hⁱ(A[k])` of Definition 12.14.8, tag 011H, and so is
proved where that identification lives: `CochainComplex.shiftIso_hom_app_comp_δ`, in
`StacksCore.Algebra.Homology.HomotopyCategory.ShiftSequence`.

**That third clause is not sign-free, although the Stacks project's wording suggests it is.**
The proof of 12.13.12 says only "compatibility with shifts is immediate from the definitions".
But with the Stacks project's own conventions — 011G shifts differentials by `(-1)^k`, while the
identification of 011H is the plain unsigned re-indexing — the long exact sequence of `A[k]` and
the reindexed long exact sequence of `A` agree on the two functorial maps and differ by `(-1)^k`
on the connecting map:

`shiftIso k i i' |>.hom.app C ≫ δ i' j' = (-1)^k • (δ i j ≫ shiftIso k j j' |>.hom.app A)`

The sign comes from one place. In `CochainComplex.shiftShortComplexFunctor'` the shift multiplies
the outer two legs of the short complex by `(-1)^k` and leaves the middle one alone, so the maps
`homologyι` and `homologyπ` are unaffected while `opcyclesToCycles`, which is built from `d`,
picks the sign up; the connecting map is the one built from `opcyclesToCycles`. Equivalently, and
this is how it was checked: `δ` is pinned by `ShortComplex.ShortExact.δ_eq`, whose witness `x₁` is
unique because `S.f` is mono, and the witness for the shifted sequence is `(-1)^k` times the
witness for the original.

The proved statement therefore carries the `(-1)^k`; asserting strict compatibility would be
asserting something the Stacks text implies but which is false as stated.
-/

add_to_stacks 0111 "the exact sequence itself, as a `ComposableArrows C 5` for one step of the
complex shape; the doubly infinite sequence is the family of these over all steps."
  HomologicalComplex.HomologySequence.composableArrows₅_exact

add_to_stacks 0117 "the exact sequence itself"
  HomologicalComplex.HomologySequence.composableArrows₅_exact

add_to_stacks 0117 "functorial in the short exact sequence; the shift-compatibility clause is
`CochainComplex.shiftIso_hom_app_comp_δ`, which carries a `(-1)^k` on the connecting map that the
Stacks wording does not lead you to expect — see the module docstring."
  HomologicalComplex.HomologySequence.mapComposableArrows₅
