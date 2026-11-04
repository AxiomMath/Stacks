module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapOnSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalPullback
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.DegreeZero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksCore.Tactic.StacksAttribute

/-!
# Clause (2) of Stacks 0FUR in degree zero, at every `n`

In the standing situation of Section 50.16 of the source — `S = Spec R`, the centre
`Z = 𝐀^m_S` (`Stacks.DeRham.coordinateBlowupCentre`), the projective bundle `P = 𝐏^{n-1}_Z` and
its projection `p : P ⟶ Z` — clause (2) of [Stacks, Tag 0FUR] asserts that

`Ω^a_{Z/S} ⟶ p_*Ω^a_{P/S}`

is an isomorphism for every `a ≥ 0`. For `n = 1`, the case in which `p` is an isomorphism, this
is `Stacks.DeRham.isIso_coordinateBundleFormsDirectImage_of_one`, in every degree. This file
proves the single degree `a = 0`, with no restriction on `n`.

In degree zero both sides are structure sheaves, and the assertion is `p_*𝒪_P = 𝒪_Z`. Making
that precise is the content of the first half of the file: the comparison map of
`AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison`, conjugated by the degree-zero
identifications `Ω^0 ≅ 𝒪` on both sides, *is* the canonical map `𝒪_X ⟶ f_*𝒪_Y` attached to
`f^♯`. The second half supplies `p_*𝒪_P = 𝒪_Z` itself, by assembling the sectionwise
computation `ProjectiveSpaceHigherDirectImage.bijective_app_structureMorphism_projectiveSpaceOver`
into an isomorphism of sheaves of modules.

## Main results

* `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPieceZeroIsoUnit_hom_smul_one`: the
  degree-zero identification of an exterior algebra carries `r • 1` back to `r`.
* `AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison_zero`: **in degree zero the
  comparison map on direct images of forms is the canonical map on structure sheaves.**
* `AlgebraicGeometry.Scheme.Hom.isIso_formsDirectImageComparison_zero_of_bijective_app`: it is
  therefore an isomorphism as soon as `f^♯` is bijective on the sections over every affine open.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage`
  `.isIso_unitToPushforwardObjUnit_structureMorphism_projectiveSpaceOver`: **`p_*𝒪_{ℙⁿ_S} = 𝒪_S`
  as sheaves of modules**, over an arbitrary base scheme.
* `Stacks.DeRham.isIso_coordinateBundleFormsDirectImage_zero`: **clause (2) of
  [Stacks, Tag 0FUR] in degree `a = 0`, at every `n`.**

## Which clause of the tag this is

Only the degree `a = 0` of clause (2) is covered here, and the attribute says so. The source's
proof of clause (2) decomposes `Ω^a_{P/S}` as the direct sum over `a = r + s` of
`pr₁^*Ω^r_{Z/S} ⊗ pr₂^*Ω^s_{𝐏^{n-1}_S/S}` and pushes each summand forward by the projection
formula, so that only the `s = 0` summand survives; this file reaches that surviving summand
without the decomposition, and so reaches no other degree.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` carrying its own category instance, equal to the
one on `SheafOfModules` only after unfolding it. Instance search does not see through that, so
the isomorphism obtained from the affine criterion — which is stated for `X.Modules` — has to be
transported by hand to the category in which the right-hand side of
`formsDirectImageComparison_zero` composes, and the composition of isomorphisms is taken with
`CategoryTheory.IsIso.comp_isIso'`, whose `IsIso` arguments are explicit, rather than by
instance search.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Section 50.2](https://stacks.math.columbia.edu/tag/0FL5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {F : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)}

/-- The degree-zero identification of the exterior algebra inverts `r ↦ r • 1`: it carries the
multiple `r • 1` of the algebra unit back to the scalar `r`. This is the companion of
`exteriorPieceZeroIsoUnit_smul_one`, which goes the other way. -/
theorem exteriorPieceZeroIsoUnit_hom_smul_one
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (U : Cᵒᵖ)
    (r : (Sheaf.toRingCat J Osharp).obj.obj U) :
    A.exteriorPieceZeroIsoUnit.hom.val.app U (r • A.exterior.one.eval U) = r := by
  rw [map_smul, A.exteriorPieceZeroIsoUnit_one U]
  exact mul_one r

end SheafOfModules.TensorExteriorSymmetricAlgebras

namespace AlgebraicGeometry.Scheme.Hom

/-- **In degree zero the comparison map on direct images of forms is the canonical map on
structure sheaves.** Conjugated by the degree-zero identifications `Ω^0_{X/S} ≅ 𝒪_X` and
`Ω^0_{Y/S} ≅ 𝒪_Y` of [Stacks, Tag 0FL5], the map `Ω^0_{X/S} ⟶ f_*Ω^0_{Y/S}` attached to
`f : Y ⟶ X` over `π : X ⟶ S` is the map `𝒪_X ⟶ f_*𝒪_Y` corresponding to `f^♯`.

Both sides are computed on a local section over an open `U` of `X`. Degree zero of the exterior
algebra is free of rank one on the algebra unit, so a section is `r • 1` with `r` its image under
the degree-zero identification; pulling back a form is unital and semilinear over `f^♯`
([Stacks, Tag 01UV]), so `r • 1` goes to `f^♯ r • 1`; and the degree-zero identification
downstairs carries that back to `f^♯ r`. -/
theorem formsDirectImageComparison_zero {X Y S : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) :
    formsDirectImageComparison f π 0 ≫
        (Scheme.Modules.pushforward f).map (relativeDifferentialFormsZeroIso (f ≫ π)).hom =
      (relativeDifferentialFormsZeroIso π).hom ≫
        _root_.SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  have hcomm : f ≫ π = (f ≫ π) ≫ 𝟙 S := by simp
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  show (relativeDifferentialFormsZeroIso (f ≫ π)).hom.val.app (op (f ⁻¹ᵁ U))
        (relativeDifferentialFormsPullback f π (f ≫ π) (𝟙 S) hcomm 0 U x) =
      (f.app U).hom ((relativeDifferentialFormsZeroIso π).hom.val.app (op U) x)
  obtain ⟨r, hr⟩ : ∃ r : Γ(X, U),
      (relativeDifferentialFormsZeroIso π).hom.val.app (op U) x = r := ⟨_, rfl⟩
  have hpull := Eq.trans
    (congrArg (relativeDifferentialFormsPullback f π (f ≫ π) (𝟙 S) hcomm 0 U)
      ((deRhamAlgebras π).exteriorPieceZeroIsoUnit_smul_one (op U) x r hr).symm)
    (Eq.trans
      (relativeDifferentialFormsPullback_smul f π (f ≫ π) (𝟙 S) hcomm 0 U r
        ((relativeDifferentialFormsAlgebra π).one.eval (op U)))
      (congrArg (fun ω => (f.app U).hom r • ω)
        (relativeDifferentialFormsPullback_one f π (f ≫ π) (𝟙 S) hcomm U)))
  rw [hr, hpull]
  exact (deRhamAlgebras (f ≫ π)).exteriorPieceZeroIsoUnit_hom_smul_one (op (f ⁻¹ᵁ U)) _

/-- **In degree zero the comparison map on direct images of forms is an isomorphism as soon as
`f^♯` is bijective on the sections over every affine open.** By
`formsDirectImageComparison_zero` the map is, after conjugation by the degree-zero
identifications, the canonical map `𝒪_X ⟶ f_*𝒪_Y`; a morphism of sheaves of modules bijective
on the sections over every affine open is an isomorphism, the affine opens being a basis; and
the two conjugating maps are isomorphisms. -/
theorem isIso_formsDirectImageComparison_zero_of_bijective_app {X Y S : Scheme.{u}} (f : Y ⟶ X)
    (π : X ⟶ S) (hf : ∀ V : X.affineOpens, Function.Bijective (f.app V.1)) :
    IsIso (formsDirectImageComparison f π 0) := by
  -- `isIso_of_affine_sections_bijective` concludes in the category `X.Modules`, while the
  -- right-hand side of `formsDirectImageComparison_zero` composes in
  -- `SheafOfModules X.ringCatSheaf`; the two category instances are equal only after unfolding
  -- `AlgebraicGeometry.Scheme.Modules`, which instance search does not do, so the transport is
  -- made explicitly here.
  have hunit : IsIso (C := _root_.SheafOfModules X.ringCatSheaf)
      (_root_.SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :=
    Stacks.Algebraization.isIso_of_affine_sections_bijective
      (_root_.SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) hf
  have hzY : IsIso (relativeDifferentialFormsZeroIso (f ≫ π)).hom :=
    Iso.isIso_hom (relativeDifferentialFormsZeroIso (f ≫ π))
  have hzX : IsIso (relativeDifferentialFormsZeroIso π).hom :=
    Iso.isIso_hom (relativeDifferentialFormsZeroIso π)
  have hpush : IsIso ((Scheme.Modules.pushforward f).map
      (relativeDifferentialFormsZeroIso (f ≫ π)).hom) :=
    Functor.map_isIso (Scheme.Modules.pushforward f)
      (relativeDifferentialFormsZeroIso (f ≫ π)).hom
  have hcomp : IsIso (formsDirectImageComparison f π 0 ≫
      (Scheme.Modules.pushforward f).map (relativeDifferentialFormsZeroIso (f ≫ π)).hom) := by
    rw [formsDirectImageComparison_zero f π]
    exact IsIso.comp_isIso' hzX hunit
  exact IsIso.of_isIso_comp_right (formsDirectImageComparison f π 0)
    ((Scheme.Modules.pushforward f).map (relativeDifferentialFormsZeroIso (f ≫ π)).hom)

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

/-- **`p_*𝒪_{ℙⁿ_S} = 𝒪_S` as sheaves of `𝒪_S`-modules**, for the structure morphism
`p : ℙⁿ_S ⟶ S` over an arbitrary scheme `S` and an arbitrary `n`: the canonical map
`𝒪_S ⟶ p_*𝒪_{ℙⁿ_S}` of sheaves of modules attached to `p^♯` is an isomorphism.

This is the assembled form of `isIso_app_structureMorphism_projectiveSpaceOver`, which gives
the same statement on the sections over an affine open. A morphism of sheaves of modules that is
bijective on the sections over every affine open is an isomorphism, the affine opens being a
basis of the topology. -/
theorem isIso_unitToPushforwardObjUnit_structureMorphism_projectiveSpaceOver
    (n : ℕ) (S : Scheme.{u}) :
    IsIso (_root_.SheafOfModules.unitToPushforwardObjUnit
      (projectiveSpaceOver n S ↘ S).toRingCatSheafHom) :=
  Stacks.Algebraization.isIso_of_affine_sections_bijective _ fun V =>
    bijective_app_structureMorphism_projectiveSpaceOver n S V.2

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

namespace Stacks.DeRham

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- **[Stacks, Tag 0FUR], clause (2), in degree `a = 0`, for every `n`.** The canonical map
`Ω^0_{Z/S} ⟶ p_*Ω^0_{P/S}` is an isomorphism, with no restriction on `n`.

In degree zero both sides are structure sheaves: the comparison map is, after conjugation by the
degree-zero identifications, the canonical map `𝒪_Z ⟶ p_*𝒪_P`
(`AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison_zero`), and that map is an isomorphism
because the direct image of the structure sheaf of projective space over any base is the
structure sheaf of the base, which is the degree-zero row of [Stacks, Tag 01XW] at the zeroth
twist. This is the `s = 0` summand that the source's own proof of clause (2) is left with after
the projection formula kills the others; what is avoided here is the decomposition of the forms
of a product, at the cost of reaching only degree `0`. -/
@[stacks 0FUR "clause (2) in the single degree a = 0, at general n: the canonical map \
Ω^0_{Z/S} ⟶ p_*Ω^0_{P/S} is an isomorphism for every n, with no restriction on n; the degrees \
a > 0 of clause (2) at n > 1, clause (1) at n > 1, and clause (3) in any case, are not proved \
here"]
theorem isIso_coordinateBundleFormsDirectImage_zero :
    IsIso (coordinateBundleFormsDirectImage R m n 0) :=
  Scheme.Hom.isIso_formsDirectImageComparison_zero_of_bijective_app _ _ fun V =>
    bijective_app_structureMorphism_projectiveSpaceOver (n - 1)
      (coordinateBlowupCentre R m) V.2

end Stacks.DeRham

end
