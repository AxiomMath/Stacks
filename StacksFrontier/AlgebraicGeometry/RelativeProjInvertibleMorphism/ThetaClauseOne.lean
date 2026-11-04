module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaGlue

/-!
# The relative `θ` of Stacks Tag 01O9 and its clause (1)

Let `(S, 𝒜, f : T ⟶ S, ℒ, ψ)` be the data of [Stacks, Tag 01O8] and
`r = r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)` the morphism of [Stacks, Tag 01O9]. This file assembles

`θ : r^*(⨁_{d ∈ ℤ} 𝒪_{Proj_S(𝒜)}(d)) ⟶ ⨁_{d ∈ ℤ} ℒ^{⊗ d}|_{U(ψ)}`

as a map of sheaves of `ℤ`-graded `𝒪_{U(ψ)}`-algebras — the adjoint transpose of the glued
pushforward form — and proves clause (1) of the tag for every open `V` of the base and every
`d ≥ 0`. The part of `θ` in nonnegative degrees is the map of graded algebras of the tag.

## Main definitions

* `…GradedPowerMap.thetaPushHom`: `θ` in pushforward form, as a homomorphism of graded algebras.
* `…GradedPowerMap.theta`: **`θ`.**

## Main results

* `…GradedPowerMap.thetaPush_psiU`: clause (1) in pushforward form.
* `…GradedPowerMap.theta_clauseOne`: **clause (1) of [Stacks, Tag 01O9].**
* `…GradedPowerMap.eq_theta`: `θ` is the only map of graded algebras whose adjoint transpose is
  [Stacks, Tag 01NK]'s `θ` over the chart of every affine open of the base.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ModuleHomGlue

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace GradedPowerMap

attribute [local irreducible] GradedPowerMap.globalMorphism
  Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

/-- `f^{-1}(V) ∩ U(ψ) = r_{ℒ,ψ}^{-1}(π^{-1}(V))`. -/
theorem toBase_preimage_eq (V : S.Opens) :
    P.toBase ⁻¹ᵁ V =
      P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, P.globalMorphism_comp_toBase]

/-- The inverse image under `r_{ℒ,ψ}` of `π^{-1}(V)` lies over `f^{-1}(V)`: `r_{ℒ,ψ}` is a morphism
over the base. -/
theorem image_preimage_preimage_le (V : S.Opens) :
    P.coveringOpen.ι ''ᵁ (P.globalMorphism (relativeProj A) ⁻¹ᵁ
      ((relativeProj A).toBase ⁻¹ᵁ V)) ≤ f ⁻¹ᵁ V := by
  rw [← P.toBase_preimage_eq V]
  rintro _ ⟨y, hy, rfl⟩
  exact hy

/-- **Clause (1) of [Stacks, Tag 01O9] for the pushforward form of `θ`**, over every open `V` of
the base: `θ(ψ_{univ}(a)) = ψ(a)|_{f^{-1}(V) ∩ U(ψ)}` for every homogeneous section `a` of
`𝒜_d` over `V`. -/
theorem thetaPush_psiU (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)) :
    (P.thetaPush d).app ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a) =
      (tensorPowerModule T P.L d).presheaf.map (homOfLE (P.image_preimage_preimage_le V)).op
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
          (P.value d V a)) := by
  let U : {m : S.affineOpens // m.1 ≤ V} → (relativeProj A).scheme.Opens := fun m =>
    (relativeProj A).toBase ⁻¹ᵁ m.1.1
  have hU : ∀ m, U m ≤ (relativeProj A).toBase ⁻¹ᵁ V := fun m =>
    (relativeProj A).toBase.preimage_mono m.2
  have hcov : (relativeProj A).toBase ⁻¹ᵁ V ≤ ⨆ m, U m := by
    intro x hx
    obtain ⟨-, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWV⟩, hxW⟩
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (P.pushK d).isSheaf U hU hcov
    fun m => ?_
  have hm := RelativeProjTwistGlue.chart_image_top (relativeProj A) m.1.1 m.1.2
  have e1 := Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map (P.thetaPush d) (hU m)
    (psiU A d V a)
  have e2 : (Otw A d).presheaf.map (homOfLE (hU m)).op (psiU A d V a) =
      (Otw A d).presheaf.map (homOfLE (le_refl ((relativeProj A).toBase ⁻¹ᵁ m.1.1))).op
        (psiU A d m.1.1 ((A.piece (d : ℤ)).presheaf.map (homOfLE m.2).op a)) :=
    (psiU_res d m.2 a).symm.trans (map_id_apply _ _ _).symm
  have e3 := P.thetaPush_app_eq_localApp m.1.1 m.1.2 d hm
    ((Otw A d).presheaf.map (homOfLE (le_refl ((relativeProj A).toBase ⁻¹ᵁ m.1.1))).op
        (psiU A d m.1.1 ((A.piece (d : ℤ)).presheaf.map (homOfLE m.2).op a)))
  have e4 := P.localApp_thetaLoc_psiU m.1.1 m.1.2 d hm le_rfl (P.image_preimage_preimage_le m.1.1)
    ((A.piece (d : ℤ)).presheaf.map (homOfLE m.2).op a)
  have e6 := pushforward_restrict_map P.coveringOpen.ι (P.globalMorphism (relativeProj A))
    (tensorPowerModule T P.L d) (homOfLE (hU m))
    ((tensorPowerModule T P.L d).presheaf.map (homOfLE (P.image_preimage_preimage_le V)).op
      ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
        (P.value d V a)))
  refine e1.trans ((congrArg ((P.thetaPush d).app _) e2).trans (e3.trans (e4.trans
    ((congrArg ((tensorPowerModule T P.L d).presheaf.map _) (P.powValue_res d m.2 a)).trans ?_))))
  refine Eq.trans ?_ e6.symm
  have hX : P.coveringOpen.ι ''ᵁ (P.globalMorphism (relativeProj A) ⁻¹ᵁ U m) ≤ f ⁻¹ᵁ V :=
    (P.image_preimage_preimage_le m.1.1).trans (f.preimage_mono m.2)
  exact (map_map _ _ _ (homOfLE hX).op _).trans (map_map _ _ _ (homOfLE hX).op _).symm

/-! ### `θ` itself -/

/-- **`θ` of [Stacks, Tag 01O9] in pushforward form**: the homomorphism of sheaves of `ℤ`-graded
algebras `⨁_{d ∈ ℤ} 𝒪_{Proj_S(𝒜)}(d) ⟶ (r_{ℒ,ψ})_*(⨁_{d ∈ ℤ} ℒ^{⊗ d}|_{U(ψ)})`. -/
def thetaPushHom : SheafOfModules.GradedAlgebra.Hom ((twD A).algebra)
    (Stacks.RingedSpace.pushforwardAlgebra (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
      (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen)) where
  app n := P.thetaPush n
  map_mul := P.thetaPush_mul

/-- **`θ` of [Stacks, Tag 01O9]**: the map of `ℤ`-graded `𝒪_{U(ψ)}`-algebras
`θ : r_{ℒ,ψ}^*(⨁_{d ∈ ℤ} 𝒪_{Proj_S(𝒜)}(d)) ⟶ ⨁_{d ∈ ℤ} ℒ^{⊗ d}|_{U(ψ)}`, the adjoint transpose of
`thetaPushHom`. Its part in nonnegative degrees is the map of the tag. -/
def theta : SheafOfModules.GradedAlgebra.Hom
    (Stacks.Conormal.gradedPullback (P.globalMorphism (relativeProj A))
      ((twD A).algebra))
    (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen) :=
  Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.transposeHom
    (P.globalMorphism (relativeProj A)).toLRSHom.toShHom P.thetaPushHom

/-- `θ` is the adjoint transpose of `thetaPushHom` along `r_{ℒ,ψ}^* ⊣ (r_{ℒ,ψ})_*`. -/
theorem theta_eq_transposeHom :
    P.theta = Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.transposeHom
      (P.globalMorphism (relativeProj A)).toLRSHom.toShHom P.thetaPushHom := rfl

/-- **Clause (1) of [Stacks, Tag 01O9].** For every open `V ⊆ S` and every `d ≥ 0` the square

`𝒜_d(V) --ψ--> Γ(f^{-1}(V), ℒ^{⊗ d}) --restrict--> Γ(f^{-1}(V) ∩ U(ψ), ℒ^{⊗ d})`
`𝒜_d(V) --ψ--> Γ(π^{-1}(V), 𝒪(d)) --θ--> Γ(f^{-1}(V) ∩ U(ψ), ℒ^{⊗ d})`

commutes. On the second row `ψ` is [Stacks, Tag 01NR]'s homogeneous-section map and `θ` acts on a
section of `𝒪(d)` over `π^{-1}(V)` through the unit of `r^* ⊣ r_*`, landing on
`r_{ℒ,ψ}^{-1}(π^{-1}(V)) = f^{-1}(V) ∩ U(ψ)`; on the first row `ψ(a)` is read in
[Stacks, Tag 01CU]'s tensor powers through
`Stacks.AlgebraicGeometry.CoherentMulSections.powCompare`. -/
theorem theta_clauseOne (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)) :
    (P.powK d).presheaf.map (eqToHom (P.toBase_preimage_eq V)).op
        ((P.theta.app d).val.app
          (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
          (Stacks.RingedSpace.pullbackUnit (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
            (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V)) (psiU A d V a))) =
      (tensorPowerModule T P.L d).presheaf.map
        (homOfLE (P.coveringOpen.ι.image_preimage_le (f ⁻¹ᵁ V))).op
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
          (P.value d V a)) := by
  have h1 : (P.theta.app d).val.app
          (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
          (Stacks.RingedSpace.pullbackUnit (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
            (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V)) (psiU A d V a)) =
        (P.thetaPushHom.app d).val.app (op ((relativeProj A).toBase ⁻¹ᵁ V)) (psiU A d V a) :=
    Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.transposeAppHom_pullbackUnit
      (P.globalMorphism (relativeProj A)).toLRSHom.toShHom P.thetaPushHom (d : ℤ)
      ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)
  have h4 : (P.powK d).presheaf.map (eqToHom (P.toBase_preimage_eq V)).op
      ((tensorPowerModule T P.L d).presheaf.map (homOfLE (P.image_preimage_preimage_le V)).op
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
          (P.value d V a))) =
      (tensorPowerModule T P.L d).presheaf.map
        (homOfLE (P.coveringOpen.ι.image_preimage_le (f ⁻¹ᵁ V))).op
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
          (P.value d V a)) := by
    have e : ∀ y : Γ(tensorPowerModule T P.L d, P.coveringOpen.ι ''ᵁ
        (P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))),
        (P.powK d).presheaf.map (eqToHom (P.toBase_preimage_eq V)).op y =
        (tensorPowerModule T P.L d).presheaf.map
          (P.coveringOpen.ι.opensFunctor.map (eqToHom (P.toBase_preimage_eq V))).op y :=
      fun y => rfl
    exact (e _).trans (map_map _ _ _ _ _)
  exact (congrArg ((P.powK d).presheaf.map (eqToHom (P.toBase_preimage_eq V)).op)
    (h1.trans (P.thetaPush_psiU V d a))).trans h4

/-- The degree-`n` component of `θ` is the adjoint transpose of `thetaPush n`. -/
theorem theta_app (n : ℤ) :
    P.theta.app n = ((Stacks.RingedSpace.pullbackAdjunction
      (P.globalMorphism (relativeProj A)).toLRSHom.toShHom).homEquiv _ _).symm (P.thetaPush n) :=
  rfl

/-- **`θ` is the only map of graded algebras whose adjoint transpose restricts, over the chart of
every affine open `V` of the base, to the local datum built from [Stacks, Tag 01NK]'s `θ` for the
induced datum over `V`.** -/
theorem eq_theta {θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.Conormal.gradedPullback (P.globalMorphism (relativeProj A)) (twD A).algebra)
      (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen)}
    (h : ∀ (n : ℤ) (V : S.Opens) (hV : IsAffineOpen V),
      (Scheme.Modules.restrictFunctor ((relativeProj A).chart V hV)).map
        (((Stacks.RingedSpace.pullbackAdjunction
          (P.globalMorphism (relativeProj A)).toLRSHom.toShHom).homEquiv _ _) (θ'.app n)) =
        P.thetaLoc V hV n) :
    θ' = P.theta := by
  refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
  rw [theta_app, ← P.eq_thetaPush n (h n)]
  exact (((Stacks.RingedSpace.pullbackAdjunction
    (P.globalMorphism (relativeProj A)).toLRSHom.toShHom).homEquiv _ _).symm_apply_apply _).symm

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
