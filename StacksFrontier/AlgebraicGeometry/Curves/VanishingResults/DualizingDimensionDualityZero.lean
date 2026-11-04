module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingDimensionDualityBundle
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The duality of dimensions on a proper curve at `i = 0`

Let `k` be a field and `X` a proper `k`-scheme of dimension at most one, with
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` the dualizing sheaf of [Stacks, Tag 0BS2]. The duality of
dimensions of [Stacks, Tag 0BS6], clause (3), is

`dim_k Hⁱ(X, ℰ) = dim_k H^{1-i}(X, ℰ^∨ ⊗ ω_X)` for all `i ∈ ℤ`

for a locally free `ℰ` of constant rank. The member at `i = 1` is proved with nothing carried, as
`AlgebraicGeometry.finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one`.
This file derives the member at `i = 0` from it.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `dualTensorDualizingSheafOverField`: the twist `ℰ ↦ ℰ^∨ ⊗ ω_X`.
* `finrank_cohomologyOverField_zero_eq_one_dualTensorDualizingSheafOverField`:
  **`dim_k H⁰(X, ℰ) = dim_k H¹(X, ℰ^∨ ⊗ ω_X)`**, the duality of dimensions of
  [Stacks, Tag 0BS6], clause (3), at `i = 0`.

## The derivation, and what it carries

Write `T(ℰ) = ℰ^∨ ⊗ ω_X`. The member at `i = 1`, applied not to `ℰ` but to `T(ℰ)`, reads

`dim_k H⁰(X, T(T(ℰ))) = dim_k H¹(X, T(ℰ))`,

so the member at `i = 0` is that equality together with `T(T(ℰ)) ≅ ℰ`. Two things are needed to
run this and both are taken as hypotheses below:

* that `T(ℰ)` is again finite locally free of constant rank `r`, which is what lets the
  member at `i = 1` be applied to it at all;
* an isomorphism `T(T(ℰ)) ≅ ℰ`.

Both are consequences of clause (1) of [Stacks, Tag 0BS6], that `ω_X` is invertible: for an
invertible `ω_X` the twist `T` preserves finite local freeness of rank `r`, and
`T(T(ℰ)) = (ℰ^∨ ⊗ ω_X)^∨ ⊗ ω_X ≅ ℰ ⊗ ω_X^∨ ⊗ ω_X ≅ ℰ`. Clause (1) itself is proved, for `X`
Gorenstein and equidimensional of dimension one, as
`Stacks.Duality.isInvertible_dualizingSheafOverField_of_isGorenstein` of
`Curves/VanishingResults/GorensteinDualizingInvertible.lean`; the statement below is for every
proper `X` of dimension at most one, where `ω_X` need not be invertible, so it keeps the two
hypotheses. The duality of dimensions at `i = 0` under the hypotheses of the tag, with nothing
carried, is clause (3) in `Curves/VanishingResults/GorensteinCurveRiemannRoch.lean`.

Nor are the two hypotheses derived here from clause (1): the closure of
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` under the dual is absent (only the
rank-free `Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf` exists), and
the closure under the tensor product,
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf`, is stated at the
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` spelling rather than the
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` spelling used here.

## Why nothing below carries an attribute of [Stacks, Tag 0BS6]

Each statement below proves strictly less than the tag says, because each takes among its
binders a hypothesis that is not part of the tag's setup, and in one case is a clause of the tag
itself. A registration of that shape is a weakening, and the convention of this library is to
leave such a statement untagged and to say in the documentation exactly what it assumes, which
is what the section above does. Registering them would also cost the tag what it already has:
a tag counts as not formalized as soon as *any* declaration bearing it declares an assumed
input, so a conditional registration here would mask
the two members of the duality of dimensions at `i = 1` that are proved with nothing assumed, in
`Curves/VanishingResults/DualizingDimensionDuality.lean` and
`Curves/VanishingResults/DualizingDimensionDualityBundle.lean`.

## Implementation notes

The twist is a `def` rather than written out at each occurrence, because the statement below
mentions it three times and once nested in itself. It is exposed, so it unfolds to the spelling
that
`AlgebraicGeometry.finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one`
uses.

Transport along the isomorphism is
`AlgebraicGeometry.finrank_cohomologyOverField_eq_of_iso`, which is the `k`-linear form of
`Hⁿ(X, -)` applied to an isomorphism of modules.

## References

* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS4](https://stacks.math.columbia.edu/tag/0BS4)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **The twist `ℰ ↦ ℰ^∨ ⊗ ω_X`** by the dualizing sheaf `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` of
[Stacks, Tag 0BS2], at the spelling of the tensor product and of the dual that
`AlgebraicGeometry.finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one`
uses. It is the sheaf against which the duality of dimensions of [Stacks, Tag 0BS6], clause (3),
pairs `ℰ`. -/
public def dualTensorDualizingSheafOverField (E : X.Modules) : X.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.sheaf.obj, CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ X.sheaf.obj
        (CategoryTheory.forget₂ CommRingCat RingCat) X.ringCatSheaf.property⟩).obj
      (Stacks.SheafOfModules.dualSheaf X.sheaf.obj X.ringCatSheaf.property E)).obj
    (Stacks.Duality.dualizingSheafOverField f))

/-- **`dim_k H⁰(X, ℰ) = dim_k H¹(X, ℰ^∨ ⊗ ω_X)`** for a finite locally free `ℰ` of constant rank
on a proper scheme `X` of dimension at most one over a field `k`, with
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` the dualizing sheaf of [Stacks, Tag 0BS2]: the duality of
dimensions of [Stacks, Tag 0BS6], clause (3), at `i = 0`.

Writing `T(ℰ) = ℰ^∨ ⊗ ω_X`, the proof is the member of that family at `i = 1`,
`AlgebraicGeometry.finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one`,
applied to `T(ℰ)` instead of to `ℰ`, read through `T(T(ℰ)) ≅ ℰ`. The two hypotheses that make
that step available — that `T(ℰ)` is again finite locally free of rank `r`, and the isomorphism
`T(T(ℰ)) ≅ ℰ` — are carried, not proved; both follow from clause (1) of the tag, that `ω_X` is
invertible, which holds for `X` Gorenstein and equidimensional of dimension one
(`Stacks.Duality.isInvertible_dualizingSheafOverField_of_isGorenstein`) but not for every `X`
admitted here. See the module documentation. Neither the
Gorenstein nor the equidimensionality hypothesis of the tag is used. -/
public theorem finrank_cohomologyOverField_zero_eq_one_dualTensorDualizingSheafOverField
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualTensorDualizingSheafOverField f E) r]
    (e : dualTensorDualizingSheafOverField f (dualTensorDualizingSheafOverField f E) ≅ E) :
    Module.finrank k (cohomologyOverField k f E 0) =
      Module.finrank k
        (cohomologyOverField k f (dualTensorDualizingSheafOverField f E) 1) :=
  (finrank_cohomologyOverField_eq_of_iso k f e 0).symm.trans
    (finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one f hdim
      (dualTensorDualizingSheafOverField f E) r)

end AlgebraicGeometry

end
