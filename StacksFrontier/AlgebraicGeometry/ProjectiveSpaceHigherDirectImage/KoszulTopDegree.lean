module

public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.DimensionShifting
public import StacksFrontier.AlgebraicGeometry.ProjKoszulOverBase.ComplexOverBase
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.AcyclicComplex
public import StacksFrontier.CategoryTheory.Limits.BiproductMatrixFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The top higher direct images along the Koszul resolution of a very negative twist

Let `S` be a scheme, let `n = m + 1 ≥ 1`, let `f : ℙⁿ_S ⟶ S` be the structure morphism and let
`a` be an integer with `a + n + 1 < 0`. The Koszul complex of the coordinates on `ℙⁿ_S`,

`0 ⟶ 𝒪(a) ⟶ 𝒪(a+1)^{⊕ binom(n+1,1)} ⟶ ⋯ ⟶ 𝒪(a+n+1) ⟶ 0`,

is acyclic, and **every one of its terms is silent for `f_*` outside the degree `n`**: the twists
occurring in it are `𝒪(a), …, 𝒪(a+n+1)`, all of them negative, so the degree-zero row of the
display of [Stacks, Tag 01XW] vanishes on them, and the rows in the degrees `q ≠ 0, n` vanish on
every twist. Dimension shifting therefore makes the complex of degree-`n` higher direct images

`0 ⟶ Rⁿ f_* 𝒪(a) ⟶ Rⁿ f_* 𝒪(a+1)^{⊕ binom(n+1,1)} ⟶ ⋯ ⟶ Rⁿ f_* 𝒪(a+n+1) ⟶ 0`

**exact**, which is what this file proves. It is the exact sequence that computes `Rⁿ f_* 𝒪(a)`
from the higher twists, and the induction of the degree-`n` row of [Stacks, Tag 01XW] on the
complementary degree `-n-1-a` runs on it.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `pullPush`: the inverse image from the integral model followed by the degree-`q` higher direct
  image along `f`, the additive functor whose values on the terms of the Koszul complex the
  argument reads.

## Main results

* `isZero_push_twistOver_of_neg`: `Rᵠ f_* 𝒪(d) = 0` for `d < 0` and `q ≠ n`.
* `isZero_push_koszulOver_X`: the terms of the Koszul complex are silent outside the degree `n`.
* `acyclic_push_koszulOver`: **the complex of degree-`n` higher direct images of the terms of the
  Koszul complex is exact**, for `a + n + 1 < 0`.

## Implementation notes

The vanishing on a term is `CategoryTheory.Functor.isZero_obj_biproduct` for the composite
functor `pullPush`: a term of the Koszul complex is the inverse image of a direct sum of twists of
the integral model, and the inverse image of each summand is a twist of `ℙⁿ_S` on the nose, so no
comparison of the summands is needed.

The two vanishing inputs are stated in the `ℤ`-indexing
`CategoryTheory.Functor.rightDerivedPlus` while the long exact sequence is stated in Mathlib's
`ℕ`-indexed `CategoryTheory.Functor.rightDerived`; `Stacks.DerivedIndexing.rightDerivedIso` is
the comparison, and `CategoryTheory.HasDerivedCategory.standard` is installed as a local instance
at priority `2000` so that `rightDerivedPlus` elaborates in the model the inputs are stated in.

Left exactness of `R⁰ f_*`, which the dimension-shifting lemma asks for, is the direct image
preserving monomorphisms read through
`Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso`.

No `stacks` attribute is attached: what is below is the combination of the vanishing rows of
[Stacks, Tag 01XW] with the long exact sequence of [Stacks, Tag 010Q] at one complex.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

open Stacks.AlgebraicGeometry.ProjKoszulComplex (koszulFamily koszulIndex)
open Stacks.AlgebraicGeometry.ProjKoszulOverBase (koszulOver toProj)
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

variable (m : ℕ) (S : Scheme.{u}) (a : ℤ)

/-- The degree-`q` higher direct image along the structure morphism of `ℙⁿ_S`, in Mathlib's
`ℕ`-indexing. -/
abbrev push (q : ℕ) : (projectiveSpaceOver (m + 1) S).Modules ⥤ S.Modules :=
  (Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerived q

/-- The inverse image from the integral model followed by the degree-`q` higher direct image
along the structure morphism of `ℙⁿ_S`. The terms of the Koszul complex of `ℙⁿ_S` are inverse
images of direct sums of twists of the integral model, so this is the functor in which they are
direct sums. -/
abbrev pullPush (q : ℕ) :
    (AlgebraicGeometry.Proj (ProjPolyChart.polyGrading (ULift.{u} ℤ) (m + 1))).Modules ⥤
      S.Modules :=
  Scheme.Modules.pullback (toProj (m + 1) S) ⋙ push m S q

/-- **A negative twist has no higher direct image outside the degree `n`**: in the degree zero
because the degree-zero row of the display of [Stacks, Tag 01XW] is indexed by the monomials of
the negative degree `d`, and in the degrees `q ≠ 0, n` because that row of the display vanishes
for every twist. -/
@[sga "2 XII 1.5" "Clause, special case"]
theorem isZero_push_twistOver_of_neg (q : ℕ) (hq : q ≠ m + 1) {d : ℤ} (hd : d < 0) :
    IsZero ((push m S q).obj (twistOver (m + 1) S d)) := by
  refine IsZero.of_iso ?_ ((Stacks.DerivedIndexing.rightDerivedIso
    (Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)) q).app _)
  by_cases hq0 : q = 0
  · subst hq0
    exact MiddleVanishing.isZero_rightDerivedPlus_pushforward_twistOver_zero_of_neg (m + 1)
      (Nat.succ_pos m) S d hd
  · exact MiddleVanishing.isZero_rightDerivedPlus_pushforward_twistOver_of_ne (m + 1) S d (q : ℤ)
      (by exact_mod_cast hq0) (by exact_mod_cast hq)

/-- **The terms of the Koszul complex of `ℙⁿ_S` are silent for `f_*` outside the degree `n`**,
when `a + n + 1 < 0`: a term is a direct sum of copies of a twist `𝒪(a+i)`, which is negative in
the degrees `0 ≤ i ≤ n + 1` where the term is nonzero, and the term vanishes outside them. -/
theorem isZero_push_koszulOver_X (ha : a + ((m + 1 : ℕ) : ℤ) + 1 < 0) (i : ℤ) (q : ℕ)
    (hq : q ≠ m + 1) :
    IsZero ((push m S q).obj ((koszulOver (m + 1) S a).X i)) := by
  by_cases hi : i < 0 ∨ ((m + 1 : ℕ) : ℤ) + 1 < i
  · exact Functor.map_isZero _ (ProjKoszulOverBase.isZero_koszulOver_X (m + 1) S a i hi)
  exact Functor.isZero_obj_biproduct (pullPush m S q) (koszulFamily (ULift.{u} ℤ) (m + 1) a i)
    fun _ => isZero_push_twistOver_of_neg m S q hq (by push_cast at hi ⊢; omega)

/-- **Left exactness of `R⁰ f_*`**: the degree-zero higher direct image preserves
monomorphisms, being naturally isomorphic to the direct image. -/
theorem mono_push_zero_map {X Y : (projectiveSpaceOver (m + 1) S).Modules} (g : X ⟶ Y)
    (hg : Mono g) : Mono ((push m S 0).map g) := by
  have hnat := (Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso
    (projectiveSpaceOver (m + 1) S ↘ S)).hom.naturality g
  have h : (push m S 0).map g =
      (Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso
          (projectiveSpaceOver (m + 1) S ↘ S)).hom.app X ≫
        (Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).map g ≫
        (Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso
          (projectiveSpaceOver (m + 1) S ↘ S)).inv.app Y := by
    rw [← Category.assoc, ← hnat, Category.assoc, ← NatTrans.comp_app, Iso.hom_inv_id,
      NatTrans.id_app, Category.comp_id]
  rw [h]
  haveI : Mono ((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).map g) :=
    Functor.map_mono _ g
  haveI : Mono ((Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso
      (projectiveSpaceOver (m + 1) S ↘ S)).hom.app X) :=
    inferInstanceAs
      (Mono ((Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso
        (projectiveSpaceOver (m + 1) S ↘ S)).app X).hom)
  haveI : Mono ((Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso
      (projectiveSpaceOver (m + 1) S ↘ S)).inv.app Y) :=
    inferInstanceAs
      (Mono ((Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso
        (projectiveSpaceOver (m + 1) S ↘ S)).app Y).inv)
  exact mono_comp _ _

/-- **The complex of degree-`n` higher direct images of the terms of the Koszul complex of `ℙⁿ_S`
is exact**, for `a + n + 1 < 0`:

`0 ⟶ Rⁿ f_* 𝒪(a) ⟶ Rⁿ f_* 𝒪(a+1)^{⊕ binom(n+1,1)} ⟶ ⋯ ⟶ Rⁿ f_* 𝒪(a+n+1) ⟶ 0`.

The Koszul complex is acyclic over every base and all of its terms are silent for `f_*` outside
the degree `n`, which is the hypothesis of
`CategoryTheory.DeltaFunctor.acyclic_mapHomologicalComplex_top`. -/
theorem acyclic_push_koszulOver (ha : a + ((m + 1 : ℕ) : ℤ) + 1 < 0) :
    (((push m S (m + 1)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (koszulOver (m + 1) S a)).Acyclic :=
  CategoryTheory.DeltaFunctor.acyclic_mapHomologicalComplex_top
    (HigherDirectImage.pushforwardDeltaFunctor (projectiveSpaceOver (m + 1) S ↘ S))
    (koszulOver (m + 1) S a) m (ProjKoszulOverBase.acyclic_koszulOver (m + 1) S a)
    (fun i q hq => isZero_push_koszulOver_X m S a ha i q hq)
    (fun i hi => ProjKoszulOverBase.isZero_koszulOver_X (m + 1) S a i (Or.inl hi))
    (fun g hg => mono_push_zero_map m S g hg)

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
