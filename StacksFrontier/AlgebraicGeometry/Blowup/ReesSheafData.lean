module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal
public import StacksFrontier.RingTheory.ReesBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The blowup of a scheme in a quasi-coherent ideal sheaf

Let `S` be a scheme and `ℐ` a quasi-coherent sheaf of ideals on `S`, given by Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData`. The *blowup* of `S` in `ℐ` is the relative `Proj` of
the Rees algebra `⨁_{n ≥ 0} ℐⁿ`. This file constructs it.

Over an affine open `U` the Rees algebra is the ordinary Rees algebra `Γ(S, U)[ℐ(U)t]`, and the
restriction maps of the structure sheaf induce homomorphisms of graded rings between them. For
affine opens `U ≤ V` the induced morphism `Proj (Γ(S, U)[ℐ(U)t]) ⟶ Proj (Γ(S, V)[ℐ(V)t])` is an
open immersion with image the part lying over `U` (Stacks tag 01NO for the Rees algebra), and the
blowup is glued from these charts.

## Main definitions

* `Stacks.Blowup.reesRestrict` is the homomorphism of graded Rees algebras induced by the
  restriction map of the structure sheaf.
* `Stacks.Blowup.reesData` is the relative-`Proj` datum of the Rees algebra of `ℐ`.
* `Stacks.Blowup.blowUp` is the blowup of `S` in `ℐ`.
* `Stacks.Blowup.blowUpToBase` is its structure morphism to `S`.
* `Stacks.Blowup.blowUpChart` is its chart over an affine open `U`, the ordinary `Proj` of
  `Γ(S, U)[ℐ(U)t]`.
* `Stacks.Blowup.exceptionalIdeal` is the inverse-image ideal sheaf of `ℐ` on the blowup, and
  `Stacks.Blowup.exceptionalDivisor` the closed subscheme it cuts out.

## Main results

* `Stacks.Blowup.isOpenImmersion_proj_map_reesRestrict` and
  `Stacks.Blowup.opensRange_proj_map_reesRestrict`: the comparison morphism of charts is an open
  immersion with image the preimage of the smaller open. Together these say that
  `Proj (Γ(S, U)[ℐ(U)t])` is the part of `Proj (Γ(S, V)[ℐ(V)t])` lying over `U`, which is Stacks
  tag 01NO for the Rees algebra.
* `Stacks.Blowup.isPullback_blowUpChart`: the chart over `U` is the preimage of `U` in the
  blowup.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Polynomial HomogeneousIdeal Graded CommRingCat
  Stacks.ProjBaseChange

universe u

namespace Stacks.Blowup

variable {S : Scheme.{u}} (ℐ : S.IdealSheafData)

/-- The restriction map `Γ(S, V) ⟶ Γ(S, U)` of the structure sheaf along an inclusion `U ≤ V` of
affine opens. -/
abbrev sheafRestrict {U V : S.affineOpens} (h : U ≤ V) : Γ(S, V.1) ⟶ Γ(S, U.1) :=
  S.presheaf.map (homOfLE h).op

/-- `Spec` of the restriction map between two affine opens is an open immersion. -/
instance isOpenImmersion_Spec_map_sheafRestrict {U V : S.affineOpens} (h : U ≤ V) :
    IsOpenImmersion (Spec.map (sheafRestrict h)) :=
  AlgebraicGeometry.Scheme.isOpenImmersion_Spec_map_presheaf_map U.2 V.2 h

/-- The homomorphism of graded Rees algebras induced by the restriction map of the structure
sheaf. -/
def reesRestrict {U V : S.affineOpens} (h : U ≤ V) :
    reesGrading (ℐ.ideal V) →+*ᵍ reesGrading (ℐ.ideal U) :=
  reesGradedMap (sheafRestrict h).hom (ℐ.ideal V) (ℐ.ideal U) (by exact ℐ.map_ideal h)

/-- The restriction homomorphism of Rees algebras is coefficientwise restriction of sections. -/
@[simp]
theorem coe_reesRestrict {U V : S.affineOpens} (h : U ≤ V) (f : reesAlgebra (ℐ.ideal V)) :
    ((reesRestrict ℐ h f : reesAlgebra (ℐ.ideal U)) : Γ(S, U.1)[X]) =
      Polynomial.map (sheafRestrict h).hom (f : Γ(S, V.1)[X]) :=
  rfl

/-- The degree-zero identification of the Rees algebra over an affine open: `Γ(S, U)` is the
degree-zero part of `Γ(S, U)[ℐ(U)t]`. -/
def reesBase (U : S.affineOpens) : Γ(S, U.1) ⟶ CommRingCat.of ↥(reesGrading (ℐ.ideal U) 0) :=
  CommRingCat.ofHom (algebraMap Γ(S, U.1) ↥(reesGrading (ℐ.ideal U) 0))

/-- The degree-zero identification sends a section to the corresponding constant polynomial. -/
@[simp]
theorem coe_reesBase_apply (U : S.affineOpens) (a : Γ(S, U.1)) :
    ((((reesBase ℐ U).hom a : ↥(reesGrading (ℐ.ideal U) 0)) :
        ↥(reesAlgebra (ℐ.ideal U))) : Γ(S, U.1)[X]) = Polynomial.C a := by
  rw [show (reesBase ℐ U).hom a = algebraMap Γ(S, U.1) ↥(reesGrading (ℐ.ideal U) 0) a from rfl,
    SetLike.GradeZero.coe_algebraMap]
  simp

/-- The restriction homomorphism of Rees algebras factors through the base change of the Rees
algebra along `Γ(S, V) ⟶ Γ(S, U)`. -/
private theorem reesRestrict_eq_comp_includeRight {U V : S.affineOpens} (h : U ≤ V)
    [Algebra Γ(S, V.1) Γ(S, U.1)] (halg : algebraMap Γ(S, V.1) Γ(S, U.1) = (sheafRestrict h).hom)
    (hK : (ℐ.ideal V).map (algebraMap Γ(S, V.1) Γ(S, U.1)) = ℐ.ideal U) :
    reesRestrict ℐ h =
      (reesBaseChangeGradedHom (ℐ.ideal V) (ℐ.ideal U) hK).comp
        (includeRight (reesGrading (ℐ.ideal V)) Γ(S, U.1)) := by
  rw [reesRestrict, reesGradedMap_congr (sheafRestrict h).hom (ℐ.ideal V) (ℐ.ideal U) _
    halg.symm hK]
  exact GradedRingHom.ext fun y ↦ (reesBaseChange_one_tmul _ _ hK y).symm

/-- The irrelevant ideal of the Rees algebra over `U` is contained in the ideal generated by the
image under `Stacks.Blowup.reesRestrict` of the irrelevant ideal of the Rees algebra over `V`. -/
theorem reesIrrelevant_le {U V : S.affineOpens} (h : U ≤ V) :
    irrelevant (reesGrading (ℐ.ideal U)) ≤
      (irrelevant (reesGrading (ℐ.ideal V))).map (reesRestrict ℐ h) := by
  let _ : Algebra Γ(S, V.1) Γ(S, U.1) := (sheafRestrict h).hom.toAlgebra
  have hK : (ℐ.ideal V).map (algebraMap Γ(S, V.1) Γ(S, U.1)) = ℐ.ideal U := ℐ.map_ideal h
  have hfe := reesRestrict_eq_comp_includeRight ℐ h rfl hK
  rw [hfe]
  exact irrelevant_le_map_comp (irrelevant_le_map _ _)
    (irrelevant_le_reesBaseChangeGradedHom (ℐ.ideal V) (ℐ.ideal U) hK)

/-- For affine opens `U ≤ V`, the comparison morphism of charts
`Proj (Γ(S, U)[ℐ(U)t]) ⟶ Proj (Γ(S, V)[ℐ(V)t])` is an open immersion. -/
@[stacks 01NO "open immersion, for the Rees algebra of a quasi-coherent ideal sheaf"]
theorem isOpenImmersion_proj_map_reesRestrict {U V : S.affineOpens} (h : U ≤ V) :
    IsOpenImmersion (Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h)) := by
  let _ : Algebra Γ(S, V.1) Γ(S, U.1) := (sheafRestrict h).hom.toAlgebra
  have hK : (ℐ.ideal V).map (algebraMap Γ(S, V.1) Γ(S, U.1)) = ℐ.ideal U := ℐ.map_ideal h
  have _ : Module.Flat Γ(S, V.1) Γ(S, U.1) :=
    AlgebraicGeometry.Scheme.flat_presheaf_map_of_isAffineOpen U.2 V.2 h
  have _ : IsOpenImmersion (Spec.map (ofHom (algebraMap Γ(S, V.1) Γ(S, U.1)))) :=
    isOpenImmersion_Spec_map_sheafRestrict h
  have hfe := reesRestrict_eq_comp_includeRight ℐ h rfl hK
  exact isOpenImmersion_map_of_baseChange (reesGrading (ℐ.ideal V)) Γ(S, U.1)
    (reesIrrelevant_le ℐ h)
    (irrelevant_le_reesBaseChangeGradedHom (ℐ.ideal V) (ℐ.ideal U) hK)
    (irrelevant_le_reesBaseChangeGradedHomSymm (ℐ.ideal V) (ℐ.ideal U) hK)
    (reesBaseChangeGradedHomSymm_comp (ℐ.ideal V) (ℐ.ideal U) hK)
    (reesBaseChangeGradedHom_comp (ℐ.ideal V) (ℐ.ideal U) hK) hfe

attribute [local instance] isOpenImmersion_proj_map_reesRestrict

section Aux

variable {U V : S.affineOpens} (h : U ≤ V) [Algebra Γ(S, V.1) Γ(S, U.1)]
  [Module.Flat Γ(S, V.1) Γ(S, U.1)]
  [IsOpenImmersion (Spec.map (ofHom (algebraMap Γ(S, V.1) Γ(S, U.1))))]
  (halg : algebraMap Γ(S, V.1) Γ(S, U.1) = (sheafRestrict h).hom)

include halg in
/-- The image of the comparison morphism of charts, read in `Spec Γ(S, V)`: it is the preimage of
the open subscheme `Spec Γ(S, U)` under the structure morphism of `Proj (Γ(S, V)[ℐ(V)t])`, for an
algebra structure of `Γ(S, U)` over `Γ(S, V)` given by the restriction map. -/
theorem opensRange_proj_map_reesRestrict_aux
    (hK : (ℐ.ideal V).map (algebraMap Γ(S, V.1) Γ(S, U.1)) = ℐ.ideal U) :
    (Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h)).opensRange =
      (Proj.toSpecZero (reesGrading (ℐ.ideal V)) ≫ Spec.map (reesBase ℐ V)) ⁻¹ᵁ
        (Spec.map (ofHom (algebraMap Γ(S, V.1) Γ(S, U.1)))).opensRange := by
  have hfe := reesRestrict_eq_comp_includeRight ℐ h halg hK
  exact @Proj.opensRange_eq_preimage_of_isPullback _ _ _ _ _ _ _ _ _
    (isOpenImmersion_proj_map_reesRestrict ℐ h)
    (isPullback_map_of_baseChange (reesGrading (ℐ.ideal V)) Γ(S, U.1)
      (reesIrrelevant_le ℐ h)
      (irrelevant_le_reesBaseChangeGradedHom (ℐ.ideal V) (ℐ.ideal U) hK)
      (irrelevant_le_reesBaseChangeGradedHomSymm (ℐ.ideal V) (ℐ.ideal U) hK)
      (reesBaseChangeGradedHomSymm_comp (ℐ.ideal V) (ℐ.ideal U) hK)
      (reesBaseChangeGradedHom_comp (ℐ.ideal V) (ℐ.ideal U) hK) hfe).flip

end Aux

/-- For affine opens `U ≤ V`, the image of the comparison morphism of charts is the preimage of
`U` in the chart over `V`. -/
@[stacks 01NO "image is the preimage, for the Rees algebra of a quasi-coherent ideal sheaf"]
theorem opensRange_proj_map_reesRestrict {U V : S.affineOpens} (h : U ≤ V) :
    Stacks.RelativeProj.chartToOpen (fun W : S.affineOpens ↦ reesGrading (ℐ.ideal W)) V
        (reesBase ℐ V) ⁻¹ᵁ (S.homOfLE h).opensRange =
      (Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h)).opensRange := by
  let _ : Algebra Γ(S, V.1) Γ(S, U.1) := (sheafRestrict h).hom.toAlgebra
  have hK : (ℐ.ideal V).map (algebraMap Γ(S, V.1) Γ(S, U.1)) = ℐ.ideal U := ℐ.map_ideal h
  have _ : Module.Flat Γ(S, V.1) Γ(S, U.1) :=
    AlgebraicGeometry.Scheme.flat_presheaf_map_of_isAffineOpen U.2 V.2 h
  have _ : IsOpenImmersion (Spec.map (ofHom (algebraMap Γ(S, V.1) Γ(S, U.1)))) :=
    isOpenImmersion_Spec_map_sheafRestrict h
  have hsq : (Stacks.RelativeProj.isAffineOpen U).isoSpec.inv ≫ S.homOfLE h =
      Spec.map (ofHom (algebraMap Γ(S, V.1) Γ(S, U.1))) ≫
        (Stacks.RelativeProj.isAffineOpen V).isoSpec.inv :=
    Stacks.RelativeProj.isoSpec_inv_homOfLE (Stacks.RelativeProj.isAffineOpen U)
      (Stacks.RelativeProj.isAffineOpen V) h
  rw [opensRange_proj_map_reesRestrict_aux ℐ h rfl hK,
    Proj.opensRange_eq_preimage_of_isPullback (IsPullback.of_horiz_isIso ⟨hsq⟩)]
  simp only [Stacks.RelativeProj.chartToOpen, Scheme.Hom.comp_preimage]

/-- The restriction maps of the Rees algebras are compatible with the degree-zero
identifications: both composites send a section `a` over `V` to the constant polynomial of its
restriction to `U`. -/
theorem reesBase_restrict {U V : S.affineOpens} (h : U ≤ V) :
    sheafRestrict h ≫ reesBase ℐ U =
      reesBase ℐ V ≫ CommRingCat.ofHom (reesRestrict ℐ h).gradedZeroRingHom := by
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ Subtype.ext (Subtype.ext ?_))
  change Polynomial.C ((sheafRestrict h).hom a) =
    Polynomial.map (sheafRestrict h).hom (Polynomial.C a)
  rw [Polynomial.map_C]

/-- **The relative-`Proj` datum of the Rees algebra of a quasi-coherent ideal sheaf.** Its graded
ring over an affine open `U` is the Rees algebra `Γ(S, U)[ℐ(U)t]`, its degree-zero
identification is the structure map of that algebra, and its restriction maps are
`Stacks.Blowup.reesRestrict`. -/
def reesData : Stacks.RelativeProj.Data (fun U : S.affineOpens ↦ reesGrading (ℐ.ideal U)) where
  base U := reesBase ℐ U
  restrict h := reesRestrict ℐ h
  irrelevant_le h := reesIrrelevant_le ℐ h
  restrict_id U := by
    refine GradedRingHom.ext fun f ↦ Subtype.ext ?_
    rw [coe_reesRestrict]
    refine Eq.trans ?_ Polynomial.map_id
    congr 1
    exact congrArg CommRingCat.Hom.hom (S.presheaf.map_id (Opposite.op (U.1 : S.Opens)))
  restrict_comp hUV hVW := by
    refine GradedRingHom.ext fun f ↦ Subtype.ext ?_
    rw [coe_reesRestrict]
    change _ = Polynomial.map _ (Polynomial.map _ _)
    rw [Polynomial.map_map, ← CommRingCat.hom_comp, ← S.presheaf.map_comp]
    rfl
  base_restrict h := reesBase_restrict ℐ h
  isOpenImmersion_map h := isOpenImmersion_proj_map_reesRestrict ℐ h
  opensRange_map h := opensRange_proj_map_reesRestrict ℐ h

/-- The blowup of a scheme `S` in a quasi-coherent sheaf of ideals
`ℐ`: the relative `Proj` of the Rees algebra `⨁_{n ≥ 0} ℐⁿ`. -/
@[stacks 01OG "the blowup as a scheme", ega "II 8.1.3", ega "IV 19.4.1", sga "6 VII 1.8"]
def blowUp : Scheme.{u} := (reesData ℐ).relativeProj

/-- The structure morphism of the blowup to its base. -/
@[stacks 01OG "the blowup morphism"]
def blowUpToBase : blowUp ℐ ⟶ S := (reesData ℐ).toBase

/-- The blowup is canonically a scheme over its base. -/
instance : (blowUp ℐ).CanonicallyOver S where
  hom := blowUpToBase ℐ

/-- The chart of the blowup over an affine open `U` of the base: the ordinary `Proj` of the Rees
algebra `Γ(S, U)[ℐ(U)t]`, as an open subscheme of the blowup. -/
def blowUpChart (U : S.affineOpens) : Proj (reesGrading (ℐ.ideal U)) ⟶ blowUp ℐ :=
  (reesData ℐ).chartι U

/-- Each chart is an open subscheme of the blowup. -/
instance (U : S.affineOpens) : IsOpenImmersion (blowUpChart ℐ U) :=
  (reesData ℐ).isOpenImmersion_chartι U

/-- The blowup restricted to an affine open `U` of the base is `Proj` of the Rees algebra of
`ℐ(U)`: the chart over `U` is the preimage of `U` under the blowup morphism. -/
@[stacks 01OG "the affine charts of the blowup",
  stacks 0804 "the canonical identification of b⁻¹(U) with Proj of the Rees algebra"]
theorem isPullback_blowUpChart (U : S.affineOpens) :
    IsPullback (Stacks.RelativeProj.chartToOpen (fun W : S.affineOpens ↦ reesGrading (ℐ.ideal W))
      U (reesBase ℐ U)) (blowUpChart ℐ U) U.1.ι (blowUpToBase ℐ) :=
  (reesData ℐ).isPullback_chartι U

/-- The charts cover the blowup. -/
theorem iSup_opensRange_blowUpChart :
    ⨆ U : S.affineOpens, (blowUpChart ℐ U).opensRange = ⊤ :=
  (reesData ℐ).iSup_opensRange_chartι

/-- The ideal sheaf of the exceptional divisor: the inverse image of `ℐ` under the blowup
morphism. -/
@[stacks 01OG "the exceptional ideal sheaf"]
def exceptionalIdeal : (blowUp ℐ).IdealSheafData := ℐ.comap (blowUpToBase ℐ)

/-- The exceptional divisor of the blowup: the closed subscheme of the blowup cut out by the
inverse image of `ℐ`. -/
@[stacks 01OG "the exceptional divisor", sga "7 XVIII 2.1"]
def exceptionalDivisor : Scheme.{u} := (exceptionalIdeal ℐ).subscheme

end Stacks.Blowup

end
