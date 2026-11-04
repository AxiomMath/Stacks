module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamWedgeSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.Connection
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.AffineSections
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.RingTheory.DeRham.Basic
public import StacksFrontier.RingTheory.FormsTrace.Basic

/-!
# The absolute de Rham complex of a scheme on an affine open

Let `Y` be a scheme and `V ⊆ Y` an affine open, with ring of functions `B = Γ(Y, V)`. The
identification `AlgebraicGeometry.Scheme.absoluteFormsSectionsEquiv` of the sections over `V` of
the sheaf `Ω^p_{Y/ℤ}` of absolute differential forms with `⋀ᵖ_B Ω[B⁄ℤ]` (Stacks 01UT, 01I8)
carries the differential of the absolute de Rham complex
`AlgebraicGeometry.Scheme.Hom.deRhamComplex Y.toSpecZ` to the ring-level de Rham differential
`KaehlerDifferential.deRhamDifferential` of `B` over `ℤ`: on sections over an affine open, the
absolute de Rham complex of `Y` is the de Rham complex `Ω^•_B` of its ring of functions.

## Main results

* `AlgebraicGeometry.Scheme.absoluteFormsSectionsEquiv_exactWedge`: the identification carries an
  exact wedge `d b₁ ∧ ⋯ ∧ d b_p` of the sheaf of forms to `D b₁ ∧ ⋯ ∧ D b_p`.
* `AlgebraicGeometry.Scheme.absoluteFormsSectionsEquiv_deRhamComplex_d`: **the identification
  commutes with the de Rham differentials**.
* `AlgebraicGeometry.Scheme.absoluteFormsSectionsEquiv_restrict_deRhamComplex_d` and
  `AlgebraicGeometry.Scheme.absoluteFormsSectionsEquiv_deRhamComplex_d_restrict`: the same
  together with restriction to a smaller affine open `V' ≤ V`, where restriction becomes the
  pull-back of forms `Stacks.FormsTrace.formsMap` along `Γ(Y, V) → Γ(Y, V')`.

## References

* [Stacks Project, Tag 0FKG](https://stacks.math.columbia.edu/tag/0FKG)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/


@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

open Stacks.AffineExteriorPower
open Stacks.AlgebraicGeometry.AffineOpenDifferentialForms
  (isExteriorAlgebra_relativeDifferentialFormsAlgebra relativeDifferentialFormsGenerator)

variable (Y : Scheme.{u}) {V : Y.Opens} (hV : IsAffineOpen V)

/-- The identification of absolute forms on an affine open carries the ordered product of the
degree-one forms `d c₁, …, d c_p` of `Ω^•_{Y/ℤ}` to the wedge `D c₁ ∧ ⋯ ∧ D c_p`. -/
theorem absoluteFormsSectionsEquiv_homogeneousProd_d (p : ℕ) (c : Fin p → Γ(Y, V)) :
    absoluteFormsSectionsEquiv Y hV p
        ((absoluteDifferentialFormsAlgebra Y).toPresheafGradedAlgebra.homogeneousProd (op V) p
          fun i => (relativeDifferentialFormsGenerator Y.toSpecZ).val.app (op V)
            ((Hom.universalRelativeDerivation Y.toSpecZ).d (c i))) =
      exteriorPower.ιMulti Γ(Y, V) p fun i => KaehlerDifferential.D ℤ Γ(Y, V) (c i) := by
  refine (absoluteFormsSectionsEquiv_apply_hom Y hV p _).trans ?_
  refine (congrArg (exteriorPower.map p (absoluteDifferentialsSectionsEquiv Y hV).toLinearMap)
    (affineOpenExteriorPowerΓIso_hom_homogeneousProd (Hom.relativeDifferentials Y.toSpecZ) hV
      (isExteriorAlgebra_relativeDifferentialFormsAlgebra Y.toSpecZ) p _)).trans ?_
  refine (exteriorPower.map_apply_ιMulti _ _).trans ?_
  exact congrArg (exteriorPower.ιMulti Γ(Y, V) p)
    (funext fun i => absoluteDifferentialsSectionsEquiv_d Y hV (c i))

/-- The exact wedges of the de Rham package of `Y ⟶ Spec ℤ` are the ordered products of the
degree-one forms `d cᵢ` of `Ω^•_{Y/ℤ}`, by definition. -/
private theorem homogeneousProd_exactOne_eq (p : ℕ) (c : Fin p → Γ(Y, V)) :
    (Hom.deRhamAlgebras Y.toSpecZ).exterior.toPresheafGradedAlgebra.homogeneousProd
        (op V) p (fun i => SheafOfModules.exactOne (Hom.deRhamAlgebras Y.toSpecZ) (op V) (c i)) =
      (absoluteDifferentialFormsAlgebra Y).toPresheafGradedAlgebra.homogeneousProd (op V) p
          fun i => (relativeDifferentialFormsGenerator Y.toSpecZ).val.app (op V)
            ((Hom.universalRelativeDerivation Y.toSpecZ).d (c i)) := rfl

/-- **The identification of absolute forms on an affine open, on an exact wedge**: it carries
`d c₁ ∧ ⋯ ∧ d c_p`, in the spelling of the de Rham package of `Y ⟶ Spec ℤ`, to
`D c₁ ∧ ⋯ ∧ D c_p`. -/
theorem absoluteFormsSectionsEquiv_exactWedge (p : ℕ) (c : Fin p → Γ(Y, V)) :
    absoluteFormsSectionsEquiv Y hV p
        ((Hom.deRhamAlgebras Y.toSpecZ).exterior.toPresheafGradedAlgebra.homogeneousProd
          (op V) p fun i => SheafOfModules.exactOne (Hom.deRhamAlgebras Y.toSpecZ) (op V) (c i)) =
      exteriorPower.ιMulti Γ(Y, V) p fun i => KaehlerDifferential.D ℤ Γ(Y, V) (c i) :=
  (congrArg (absoluteFormsSectionsEquiv Y hV p) (homogeneousProd_exactOne_eq Y p c)).trans
    (absoluteFormsSectionsEquiv_homogeneousProd_d Y hV p c)

/-- **The absolute de Rham complex on an affine open is the de Rham complex of the ring of
functions**: the identification `Γ(Ω^p_{Y/ℤ}, V) ≃ ⋀ᵖ Ω[Γ(Y, V)⁄ℤ]` carries the differential of
`Y.toSpecZ.deRhamComplex`, evaluated on sections over `V`, to
`KaehlerDifferential.deRhamDifferential`. -/
theorem absoluteFormsSectionsEquiv_deRhamComplex_d (p : ℕ)
    (ω : Γ(absoluteDifferentialForms Y p, V)) :
    absoluteFormsSectionsEquiv Y hV (p + 1)
        ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op V) ω) =
      KaehlerDifferential.deRhamDifferential p (absoluteFormsSectionsEquiv Y hV p ω) := by
  obtain ⟨ξ, rfl⟩ := (absoluteFormsSectionsEquiv Y hV p).symm.surjective ω
  rw [LinearEquiv.apply_symm_apply]
  have hξ : ξ ∈ Submodule.span ℤ (Set.range fun b : Fin (p + 1) → Γ(Y, V) =>
      b 0 • exteriorPower.ιMulti Γ(Y, V) p fun i =>
        KaehlerDifferential.D ℤ Γ(Y, V) (b i.succ)) := by
    rw [Crystalline.span_range_smul_ιMulti_eq_top (R := ℤ) (KaehlerDifferential.D ℤ Γ(Y, V))
      (KaehlerDifferential.span_range_derivation ℤ Γ(Y, V)) p]
    exact Submodule.mem_top
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    have h := Hom.deRhamComplex_d_homogeneousProdLeft Y.toSpecZ (op V) p b
    rw [Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd,
      Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd] at h
    have h1 := congrArg (absoluteFormsSectionsEquiv Y hV (p + 1)) h
    have h2 := absoluteFormsSectionsEquiv_exactWedge Y hV (p + 1) b
    have h3 := (absoluteFormsSectionsEquiv Y hV p).map_smul (b 0)
      ((Hom.deRhamAlgebras Y.toSpecZ).exterior.toPresheafGradedAlgebra.homogeneousProd
          (op V) p fun i => SheafOfModules.exactOne (Hom.deRhamAlgebras Y.toSpecZ) (op V)
            (b i.succ))
    rw [absoluteFormsSectionsEquiv_exactWedge] at h3
    have h12 := h1.trans (by convert h2 using 3)
    have hs : (absoluteFormsSectionsEquiv Y hV p).symm
        (b 0 • exteriorPower.ιMulti Γ(Y, V) p fun i => KaehlerDifferential.D ℤ Γ(Y, V) (b i.succ)) =
        _ := (LinearEquiv.symm_apply_eq _).mpr h3.symm
    refine Eq.trans ?_ (KaehlerDifferential.deRhamDifferential_smul_ιMulti_D p b).symm
    refine Eq.trans ?_ h12
    refine congrArg (absoluteFormsSectionsEquiv Y hV (p + 1)) ?_
    refine congrArg ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op V)).hom ?_
    refine hs.trans ?_
    congr 1
  | zero =>
    refine Eq.trans ?_
      (map_zero (KaehlerDifferential.deRhamDifferential (A := ℤ) (B := Γ(Y, V)) p)).symm
    refine Eq.trans ?_ (map_zero (absoluteFormsSectionsEquiv Y hV (p + 1)))
    refine congrArg (absoluteFormsSectionsEquiv Y hV (p + 1)) ?_
    refine Eq.trans ?_ (map_zero ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op V)).hom)
    refine congrArg ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op V)).hom ?_
    exact map_zero _
  | add x y _ _ hx hy =>
    refine Eq.trans ?_
      (map_add (KaehlerDifferential.deRhamDifferential (A := ℤ) (B := Γ(Y, V)) p) x y).symm
    refine Eq.trans ?_ (congrArg₂ (· + ·) hx hy)
    refine Eq.trans ?_ (map_add (absoluteFormsSectionsEquiv Y hV (p + 1)) _ _)
    refine congrArg (absoluteFormsSectionsEquiv Y hV (p + 1)) ?_
    refine Eq.trans ?_ (map_add ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op V)).hom _ _)
    refine congrArg ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op V)).hom ?_
    exact map_add _ _ _
  | smul n x _ hx =>
    refine Eq.trans ?_
      (map_zsmul (KaehlerDifferential.deRhamDifferential (A := ℤ) (B := Γ(Y, V)) p) n x).symm
    refine Eq.trans ?_ (congrArg (n • ·) hx)
    refine Eq.trans ?_ (map_zsmul (absoluteFormsSectionsEquiv Y hV (p + 1)) _ _)
    refine congrArg (absoluteFormsSectionsEquiv Y hV (p + 1)) ?_
    refine Eq.trans ?_ (map_zsmul ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op V)).hom _ _)
    refine congrArg ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op V)).hom ?_
    exact (map_zsmul (absoluteFormsSectionsEquiv Y hV p).symm.toLinearMap.toAddMonoidHom n x :
      _)

variable {Y} {V' : Y.Opens} (hV' : IsAffineOpen V')

/-- **Differential, then restriction, on affine opens.** For affine opens `V' ≤ V`, restricting
the differential of a form `ω` over `V` to `V'` is, through the identifications, the de Rham
differential of the pull-back of `ω` along `Γ(Y, V) → Γ(Y, V')`. -/
theorem absoluteFormsSectionsEquiv_restrict_deRhamComplex_d (h : V' ≤ V) (p : ℕ)
    (ω : Γ(absoluteDifferentialForms Y p, V)) :
    letI := Y.restrictAlgebra h
    absoluteFormsSectionsEquiv Y hV' (p + 1)
        ((absoluteDifferentialForms Y ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE h).op
          ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op V) ω)) =
      KaehlerDifferential.deRhamDifferential p
        (Stacks.FormsTrace.formsMap Γ(Y, V) Γ(Y, V') p (absoluteFormsSectionsEquiv Y hV p ω)) := by
  let := Y.restrictAlgebra h
  refine (absoluteFormsSectionsEquiv_restrict_kaehlerMapₛₗ hV hV' h (p + 1) _).trans ?_
  refine (congrArg (Stacks.FormsTrace.formsMap Γ(Y, V) Γ(Y, V') (p + 1))
    (absoluteFormsSectionsEquiv_deRhamComplex_d Y hV p ω)).trans ?_
  exact Stacks.FormsTrace.formsMap_deRhamDifferential p _

/-- **Restriction, then differential, on affine opens.** For affine opens `V' ≤ V`, the
differential over `V'` of the restriction of a form `ω` over `V` is, through the identifications,
the de Rham differential of the pull-back of `ω` along `Γ(Y, V) → Γ(Y, V')`. -/
theorem absoluteFormsSectionsEquiv_deRhamComplex_d_restrict (h : V' ≤ V) (p : ℕ)
    (ω : Γ(absoluteDifferentialForms Y p, V)) :
    letI := Y.restrictAlgebra h
    absoluteFormsSectionsEquiv Y hV' (p + 1)
        ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op V')
          ((absoluteDifferentialForms Y p).presheaf.map (homOfLE h).op ω)) =
      KaehlerDifferential.deRhamDifferential p
        (Stacks.FormsTrace.formsMap Γ(Y, V) Γ(Y, V') p (absoluteFormsSectionsEquiv Y hV p ω)) := by
  let := Y.restrictAlgebra h
  refine (absoluteFormsSectionsEquiv_deRhamComplex_d Y hV' p _).trans ?_
  exact congrArg (KaehlerDifferential.deRhamDifferential p)
    (absoluteFormsSectionsEquiv_restrict_kaehlerMapₛₗ hV hV' h p ω)

end AlgebraicGeometry.Scheme

end
