module

public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.SpecGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.ChartTransition
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.IsoOfInverse

/-!
# The relative `Proj` of `B̃` over `Spec R` is `Proj B`

Let `B` be an `ℕ`-graded `R`-algebra with grading `𝒢` and `𝓑 = B̃` its associated quasi-coherent
graded algebra on `Spec R` (`Stacks.PolarizedAlgebraization.specSheafGradedAlgebra`). The chart of
`Proj_{Spec R}(𝓑)` over the whole base, together with `Proj` of the isomorphism of graded rings
`B ≅ Γ(Spec R, 𝓑)`, identifies `Proj B` with `Proj_{Spec R}(𝓑)` over `Spec R`, and the Serre twist
`𝒪(n)` of the relative `Proj` with the twist `𝒪(n)` of `Proj B`.

## Main definitions

* `Stacks.PolarizedAlgebraization.projComparison`: `Proj B ⟶ Proj_{Spec R}(𝓑)`, an isomorphism.
* `Stacks.PolarizedAlgebraization.twistComparison`: the identification of the Serre twists.

## Main results

* `Stacks.PolarizedAlgebraization.projComparison_toBase`: the comparison lies over `Spec R`.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.PolarizedAlgebraization

variable {R : CommRingCat.{u}} {B : Type u} [CommRing B] [Algebra R B]
  (𝒢 : ℕ → Submodule R B) [_root_.GradedAlgebra 𝒢]

/-- The inverse of `B ⟶ Γ(Spec R, B̃)`, as a homomorphism of graded rings. -/
def globalSectionsInv : (specSheafGradedAlgebra 𝒢).grading ⊤ →+*ᵍ 𝒢 where
  __ := (RingEquiv.ofBijective (globalSectionsHom 𝒢).toRingHom
    (bijective_globalSectionsHom 𝒢)).symm.toRingHom
  map_mem {i x} hx := by
    let e := RingEquiv.ofBijective (globalSectionsHom 𝒢).toRingHom (bijective_globalSectionsHom 𝒢)
    change e.symm x ∈ 𝒢 i
    have hy : globalSectionsHom 𝒢 (e.symm x) = x := e.apply_symm_apply x
    have hd : globalSectionsHom 𝒢 (DirectSum.decompose 𝒢 (e.symm x) i : B) = x := by
      rw [GradedRingHom.map_directSumDecompose, hy, DirectSum.decompose_of_mem_same _ hx]
    exact (bijective_globalSectionsHom 𝒢).1 (hy.trans hd.symm) ▸ SetLike.coe_mem _

/-- `globalSectionsInv` is a left inverse of `globalSectionsHom`. -/
theorem globalSectionsInv_comp :
    (globalSectionsInv 𝒢).comp (globalSectionsHom 𝒢) = GradedRingHom.id 𝒢 :=
  GradedRingHom.ext fun x =>
    (RingEquiv.ofBijective (globalSectionsHom 𝒢).toRingHom
      (bijective_globalSectionsHom 𝒢)).symm_apply_apply x

/-- `globalSectionsInv` is a right inverse of `globalSectionsHom`. -/
theorem globalSectionsHom_comp :
    (globalSectionsHom 𝒢).comp (globalSectionsInv 𝒢) =
      GradedRingHom.id ((specSheafGradedAlgebra 𝒢).grading ⊤) :=
  GradedRingHom.ext fun x =>
    (RingEquiv.ofBijective (globalSectionsHom 𝒢).toRingHom
      (bijective_globalSectionsHom 𝒢)).apply_symm_apply x

/-- The irrelevant ideal of `Γ(Spec R, B̃)` is contained in the image of the irrelevant ideal of
`B`, as `B ⟶ Γ(Spec R, B̃)` is surjective; this is the hypothesis of `Proj.map`. -/
theorem irrelevant_le_map_globalSectionsHom :
    HomogeneousIdeal.irrelevant ((specSheafGradedAlgebra 𝒢).grading ⊤) ≤
      (HomogeneousIdeal.irrelevant 𝒢).map (globalSectionsHom 𝒢) :=
  AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _ (bijective_globalSectionsHom 𝒢).2

/-- `Proj` of `B ≅ Γ(Spec R, B̃)`: `Proj Γ(Spec R, B̃) ⟶ Proj B`. -/
abbrev projTopMap : AlgebraicGeometry.Proj ((specSheafGradedAlgebra 𝒢).grading ⊤) ⟶
    AlgebraicGeometry.Proj 𝒢 :=
  AlgebraicGeometry.Proj.map (globalSectionsHom 𝒢) (irrelevant_le_map_globalSectionsHom 𝒢)

/-- The irrelevant ideal of `B` is contained in the image of the irrelevant ideal of
`Γ(Spec R, B̃)` under `globalSectionsInv`, which is surjective. -/
theorem irrelevant_le_map_globalSectionsInv :
    HomogeneousIdeal.irrelevant 𝒢 ≤
      (HomogeneousIdeal.irrelevant ((specSheafGradedAlgebra 𝒢).grading ⊤)).map
        (globalSectionsInv 𝒢) :=
  AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _ fun x =>
    ⟨globalSectionsHom 𝒢 x, GradedRingHom.ext_iff.1 (globalSectionsInv_comp 𝒢) x⟩

/-- `Proj.map` only depends on the graded ring homomorphism. -/
theorem proj_map_congr {A A' σ σ' : Type u} [CommRing A] [CommRing A'] [SetLike σ A]
    [AddSubgroupClass σ A] [SetLike σ' A'] [AddSubgroupClass σ' A'] {𝒜 : ℕ → σ} {𝒜' : ℕ → σ'}
    [GradedRing 𝒜] [GradedRing 𝒜'] {φ φ' : 𝒜 →+*ᵍ 𝒜'} (h : φ = φ')
    (hφ : HomogeneousIdeal.irrelevant 𝒜' ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    (hφ' : HomogeneousIdeal.irrelevant 𝒜' ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ') :
    AlgebraicGeometry.Proj.map φ hφ = AlgebraicGeometry.Proj.map φ' hφ' := by
  subst h
  rfl

/-- `projTopMap` is an isomorphism, with inverse `Proj` of `globalSectionsInv`. -/
instance isIso_projTopMap : IsIso (projTopMap 𝒢) :=
  ⟨AlgebraicGeometry.Proj.map (globalSectionsInv 𝒢) (irrelevant_le_map_globalSectionsInv 𝒢),
    by rw [← AlgebraicGeometry.Proj.map_comp, proj_map_congr (globalSectionsHom_comp 𝒢) _ (by simp),
      AlgebraicGeometry.Proj.map_id],
    by rw [← AlgebraicGeometry.Proj.map_comp, proj_map_congr (globalSectionsInv_comp 𝒢) _ (by simp),
      AlgebraicGeometry.Proj.map_id]⟩

/-- **The comparison `Proj B ⟶ Proj_{Spec R}(B̃)`**: the inverse of `Proj` of `B ≅ Γ(Spec R, B̃)`
followed by the chart over the whole base. -/
def projComparison : AlgebraicGeometry.Proj 𝒢 ⟶ (relativeProj (specSheafGradedAlgebra 𝒢)).scheme :=
  inv (projTopMap 𝒢) ≫ topChart (specSheafGradedAlgebra 𝒢)

/-- `projComparison` is an isomorphism. -/
instance isIso_projComparison : IsIso (projComparison 𝒢) := by
  unfold projComparison
  infer_instance

/-- **The comparison lies over `Spec R`.** -/
theorem projComparison_toBase :
    projComparison 𝒢 ≫ (relativeProj (specSheafGradedAlgebra 𝒢)).toBase =
      Proj.toSpecZero 𝒢 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒢 0))) := by
  have hw := ((relativeProj (specSheafGradedAlgebra 𝒢)).chart_isPullback ⊤
    (isAffineOpen_top _)).w
  unfold projComparison
  rw [Category.assoc, hw, IsIso.inv_comp_eq, projTopMap,
    ← Category.assoc, AlgebraicGeometry.Proj.map_toSpecZero, Category.assoc, ← Spec.map_comp]
  refine (GradedAlgebra.toOpen_ι (specSheafGradedAlgebra 𝒢).toGradedAlgebra _).trans ?_
  unfold GradedAlgebra.toBase
  refine congrArg (Proj.toSpecZero ((specSheafGradedAlgebra 𝒢).grading ⊤) ≫ ·) ?_
  have hf : (isAffineOpen_top (Spec R)).fromSpec = Spec.map (Scheme.ΓSpecIso R).inv :=
    IsAffineOpen.fromSpec_top.trans (Scheme.isoSpec_Spec_inv _)
  refine (congrArg (Spec.map _ ≫ ·) hf).trans ((Spec.map_comp _ _).symm.trans ?_)
  congr 1
  ext r
  refine (GradedAlgebra.coe_strZero_apply _ _ _).trans ?_
  exact (globalSectionsHom_algebraMap 𝒢 r).symm

/-- **The Serre twists correspond**: the inverse image along `projComparison` of the `n`-th
relative twist of `Proj_{Spec R}(B̃)` is the `n`-th twist of `Proj B`. -/
def twistComparison (n : ℤ) :
    (Scheme.Modules.pullback (projComparison 𝒢)).obj
        (relativeTwist (specSheafGradedAlgebra 𝒢) n) ≅ twistingSheaf 𝒢 n :=
  haveI := Stacks.ProjTwistComparison.isIso_twistMap_of_comp_eq_id (globalSectionsHom 𝒢)
    (irrelevant_le_map_globalSectionsHom 𝒢) n (globalSectionsInv 𝒢) (globalSectionsHom_comp 𝒢)
    (globalSectionsInv_comp 𝒢)
  ((Scheme.Modules.pullbackComp (inv (projTopMap 𝒢))
      (topChart (specSheafGradedAlgebra 𝒢))).app _).symm ≪≫
    (Scheme.Modules.pullback (inv (projTopMap 𝒢))).mapIso
      (chartTwistIso (specSheafGradedAlgebra 𝒢) n ⟨⊤, isAffineOpen_top _⟩) ≪≫
    (Scheme.Modules.pullback (inv (projTopMap 𝒢))).mapIso
      (asIso (Stacks.ProjTwistComparison.twistMap (globalSectionsHom 𝒢)
        (irrelevant_le_map_globalSectionsHom 𝒢) n)).symm ≪≫
    (Scheme.Modules.pullbackComp (inv (projTopMap 𝒢)) (projTopMap 𝒢)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id (projTopMap 𝒢))).app _ ≪≫
    (Scheme.Modules.pullbackId _).app _

end Stacks.PolarizedAlgebraization

end
