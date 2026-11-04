module

public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import StacksFrontier.CategoryTheory.Triangulated.WeakBrownRepresentability
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjectsLocalizing
import StacksCore.Tactic.StacksAttribute

/-!
# Brown representability for cartesian objects in the derived category of a category

Let `C` be a category, regarded as a site with the chaotic topology, let `O` be a presheaf of
rings on `C` and let `bc` be derived base-change data for `O`. By Stacks 0GYW the cartesian
objects form a localizing triangulated subcategory `QC(O)` of `D(O)`, closed under arbitrary
direct sums. Weak Brown representability (Stacks 0GYG) therefore applies to `QC(O)` as soon as
`QC(O)` has a family of generators in the sense of that tag: a family `E : ι → QC(O)` indexed
by a type in the module universe such that every nonzero object receives a nonzero map from
some `E i`, and such that every map from some `E i` into a countable direct sum factors through
a direct sum of members of the family.

`exists_iso_preadditiveYoneda_of_isHomological_of_generating` records that
application: a contravariant cohomological functor on `QC(O)` which sends direct sums to
products is representable. What the file contributes beyond the statement of Stacks 0GYG is the
verification that `QC(O)` satisfies every structural hypothesis of that tag — it is
pretriangulated, triangulated, and has direct sums indexed by the module universe — each of
which comes from the corresponding assertion of Stacks 0GYW together with the small-Hom model
of Tag 079Q for `D(O)`.

## Main results

* `exists_iso_preadditiveYoneda_of_isHomological_of_generating`: weak Brown
  representability for `QC(O)`, given a generating family.

## Implementation notes

The generating family is a hypothesis here, not a conclusion. Producing it for `QC(O)` is the
content of Stacks 0GYZ, which bounds the size of a cartesian object by a cardinal depending
only on `C` and `O`; converting that cardinal bound into an *indexed family* additionally needs
the essential smallness of the cartesian objects of bounded size, which is not in the source.
Both are now in the repository — Stacks 0GYZ as
`exists_cardinal_small_nonzero_map_and_factorization` and the smallness as
`exists_small_qc_family_of_derivedObjectSize_le` — so the family is available unconditionally,
and the unconditional statement of Stacks 0GZ0 is this theorem applied to it. That is carried
out in the sibling file `BrownRepresentabilityUnconditional.lean`.

The statement is given for an arbitrary `bc :
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BaseChangeData O`, which generalizes
the source: specializing `bc` to the derived extension of scalars along the restriction maps of
`O` recovers the assertion of the source verbatim.

## References

* [Stacks Project, Tag 0GZ0](https://stacks.math.columbia.edu/tag/0GZ0)
* [Stacks Project, Tag 0GYG](https://stacks.math.columbia.edu/tag/0GYG)
* [Stacks Project, Tag 0GYW](https://stacks.math.columbia.edu/tag/0GYW)
* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}}

/-- **Weak Brown representability for `QC(O)`** (Stacks 0GYG applied to Stacks 0GYW). Let
`E : ι → QC(O)` be a family of cartesian objects, indexed by a type in the module universe,
such that every nonzero cartesian object receives a nonzero morphism from some `E i`, and such
that every morphism from some `E i` into a countable direct sum `∐ X` factors as a direct sum
of morphisms `E (j n) ⟶ X n` followed by the induced map. Then every contravariant
cohomological functor on `QC(O)` which sends direct sums to products is representable.

All the structural hypotheses of Stacks 0GYG hold for `QC(O)`: it is a triangulated subcategory
of `D(O)` closed under arbitrary direct sums by Stacks 0GYW, and the direct sums of `D(O)` are
indexed by the module universe because `D(O)` is taken in the small-Hom model of Tag 079Q. -/
theorem exists_iso_preadditiveYoneda_of_isHomological_of_generating
    (bc : BaseChangeData.{w} O)
    {ι : Type (max u v r w)} (E : ι → QC.{w} bc)
    (hE : ∀ X : QC.{w} bc, ¬ IsZero X → ∃ (i : ι) (f : E i ⟶ X), f ≠ 0)
    (hE' : ∀ (X : ℕ → QC.{w} bc) (i : ι) (α : E i ⟶ ∐ X),
      ∃ (j : ℕ → ι) (β : ∀ n, E (j n) ⟶ X n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
        α = γ ≫ Limits.Sigma.map β)
    (H : (QC.{w} bc)ᵒᵖ ⥤ AddCommGrpCat.{max u v r w}) [H.IsHomological]
    [∀ J : Type (max u v r w), PreservesLimitsOfShape (Discrete J) H] :
    ∃ K : QC.{w} bc, Nonempty (preadditiveYoneda.obj K ≅ H) :=
  Pretriangulated.exists_iso_preadditiveYoneda_of_generating_of_factorsThroughSigma
    E hE hE' H

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end
