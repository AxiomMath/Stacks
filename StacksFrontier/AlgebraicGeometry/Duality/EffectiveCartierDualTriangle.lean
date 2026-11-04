module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHomBifunctor
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierIdealDerivedDual

/-!
# The comparison morphism of Tag 0B4B lands on the dual triangle of the ideal sequence

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor with closed immersion `i : D ⟶ X`.
Two reductions of the isomorphism assertion of
[Stacks, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B) are in place:

* `Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_iff_derivedSheafHom`
  reduces it to the assertion that
  `α : Ri_*(𝒩[-1]) ⟶ R ℰom(Ri_* 𝒪_D, 𝒪_X)` is an isomorphism, where the target is a value of the
  derived internal Hom bifunctor; and
* `Stacks.Divisors.exists_distinguished_derivedDual_divisorIdeal` is the distinguished triangle
  `R ℰom(i_* 𝒪_D, 𝒪_X) ⟶ R ℰom(𝒪_X, 𝒪_X) ⟶ R ℰom(ℐ_D, 𝒪_X) ⟶` obtained by applying the derived
  internal Hom into `𝒪_X` to the ideal sequence, whose third vertex is `𝒪_X(D)[0]` by
  `Stacks.Divisors.derivedDualIdealSheafIso`.

This file joins them: the target of `α` **is** the first vertex of that triangle. The two differ
only in that `α`'s target is written with the derived pushforward `Ri_* 𝒪_D` of the structure
sheaf of `D` — that is how [Stacks, Tag 0A77] produces it — while the triangle is written with
`i_* 𝒪_D` placed in degree zero, which is how the ideal sequence produces it. Derived pushforward
along `i` is the pushforward of an exact functor, so it carries a single complex to a single
complex: the identification is `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, read in
the contravariant variable of the bifunctor.

## Main definitions

* `Stacks.Divisors.derivedSheafHomPushforwardStructureSheafIsoDualVertex`: the identification
  `R ℰom(Ri_* 𝒪_D, 𝒪_X) ≅ R ℰom((i_* 𝒪_D)[0], 𝒪_X)` of the target of `α` with the first vertex
  of the dual triangle.
* `Stacks.Divisors.normalShiftToDualTriangleVertex`: the comparison morphism of
  [Stacks, Tag 0B4B] as a morphism `Ri_*(𝒩[-1]) ⟶ R ℰom((i_* 𝒪_D)[0], 𝒪_X)` into that vertex.

## Main results

* `Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_iff_dualTriangleVertex`:
  the isomorphism assertion of [Stacks, Tag 0B4B] is equivalent to the assertion that
  `Stacks.Divisors.normalShiftToDualTriangleVertex` is an isomorphism — an assertion about a
  morphism into the first vertex of a distinguished triangle whose other two vertices are `𝒪_X`
  and `𝒪_X(D)[0]`.

## What is still owed

The triangulated argument is carried out in
`StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierDualTriangleComparison.lean`, as
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_dualTriangleFirstMap`:
the dual triangle is compared with the inverse rotation of the triangle of the normal short exact
sequence `0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_* 𝒩 ⟶ 0`, whose first morphism is `ψ : Ri_*(𝒩[-1]) ⟶ 𝒪_X` up to
sign, and the existential connecting morphism of [Stacks, Tag 08I0] suffices. What that argument
still assumes is one identity: that under `Stacks.Divisors.dualTriangleSecondVertexIso`, the
identification `R ℰom(𝒪_X[0], 𝒪_X) ≅ 𝒪_X[0]` of the second vertex of the dual triangle, the
triangle's first morphism is `Stacks.Divisors.derivedSheafHomEvaluationAtOne`.

The two further inputs the argument needs are proved. That the second morphism of the dual
triangle — induced by `ℐ_D ⟶ 𝒪_X` — is, through that identification and
`Stacks.Divisors.derivedDualIdealSheafIso`, multiplication by the canonical section
`1_D : 𝒪_X ⟶ 𝒪_X(D)` is
`Stacks.Divisors.dualTriangleSecondVertexIso_hom_comp_normalMor₁`; and the vanishing
`Hom_{𝒪_X}(i_* 𝒩, 𝒪_X(D)) = 0`, which holds because the local equation of `D` is a
nonzerodivisor, is `Stacks.Divisors.hom_normalQuotient_divisorSheaf_eq_zero`.

## References

* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (StructureSheafModules derivedSheafHom ringedSite)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- **The target of the comparison morphism of [Stacks, Tag 0B4B] is the first vertex of the
dual triangle of the ideal sequence:**

`R ℰom(Ri_* 𝒪_D, 𝒪_X) ≅ R ℰom((i_* 𝒪_D)[0], 𝒪_X)`.

Derived pushforward along the closed immersion of `D` is the derived functor of an exact functor
and so takes a complex concentrated in degree zero to a complex concentrated in degree zero
(`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`); this is that identification read in
the contravariant variable of the derived internal Hom bifunctor. -/
def derivedSheafHomPushforwardStructureSheafIsoDualVertex :
    derivedSheafHomPushforwardStructureSheaf D ≅
      ((derivedSheafHom X.sheaf).flip.obj
          (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).obj
        (op (divisorIdealShortComplex_shortExact D).singleTriangle.obj₃) :=
  ((derivedSheafHom X.sheaf).mapIso (Iso.op
      (((modulePushforward (closedQuotient D).i).mapDerivedCategorySingleFunctor 0).app
        (SheafOfModules.unit
          (structureSheafRing D.subscheme.toRingedSpace))).symm)).app _

/-- **The comparison morphism of [Stacks, Tag 0B4B] as a morphism into the dual triangle of the
ideal sequence:**

`Ri_*(𝒩[-1]) ⟶ R ℰom((i_* 𝒪_D)[0], 𝒪_X)`.

This is `Stacks.Divisors.pushforwardNormalShiftToDerivedSheafHom` followed by the identification
of its target with the first vertex of that triangle. -/
def normalShiftToDualTriangleVertex :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor D.subscheme.Modules 1).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ⟶
      ((derivedSheafHom X.sheaf).flip.obj
          (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).obj
        (op (divisorIdealShortComplex_shortExact D).singleTriangle.obj₃) :=
  pushforwardNormalShiftToDerivedSheafHom D ≫
    (derivedSheafHomPushforwardStructureSheafIsoDualVertex D).hom

/-- `CategoryTheory.isIso_comp_right_iff` with the invertible factor given as an isomorphism
rather than as a morphism with an `IsIso` instance.

The adapter is needed because this file makes `HasDerivedCategory.standard` a local instance at
priority 10000, and instance search then does not produce `IsIso e.hom` for the isomorphism
below; passing `e` explicitly avoids the search. Its proof is Mathlib's lemma. -/
private theorem isIso_comp_iso_iff {C : Type*} [Category C] {A B B' : C} (f : A ⟶ B)
    (e : B ≅ B') : IsIso (f ≫ e.hom) ↔ IsIso f :=
  isIso_comp_right_iff f e.hom

/-- **The isomorphism assertion of [Stacks, Tag 0B4B] is equivalent to an assertion about the
first vertex of the dual triangle of the ideal sequence.** The canonical comparison morphism
`𝒩_{D/X}[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` is an isomorphism if and only if
`Stacks.Divisors.normalShiftToDualTriangleVertex` is.

The dual triangle has `R ℰom(𝒪_X, 𝒪_X)` and `R ℰom(ℐ_D, 𝒪_X) ≅ 𝒪_X(D)[0]` for its other two
vertices, so this is the form in which the source's computation can be carried out. -/
theorem isIso_normalSheafShiftToDerivedSheafHomExactSupport_iff_dualTriangleVertex :
    IsIso (normalSheafShiftToDerivedSheafHomExactSupport D) ↔
      IsIso (normalShiftToDualTriangleVertex D) :=
  (isIso_normalSheafShiftToDerivedSheafHomExactSupport_iff_derivedSheafHom D).trans
    (isIso_comp_iso_iff _ (derivedSheafHomPushforwardStructureSheafIsoDualVertex D)).symm

end Stacks.Divisors

end
