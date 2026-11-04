module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HypercohomologyCechComputes
public import StacksFrontier.AlgebraicGeometry.SerreCriterionH1.Hgroup
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBrutalCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.RestrictScalarsCohomology

/-!
# Čech cohomology computes cohomology after restricting the sheaf of rings

Let `X` be a scheme with affine diagonal and let `R ⟶ 𝒪_X` be a morphism of sheaves of rings on
`X`, for instance `p⁻¹𝒪_S ⟶ 𝒪_X` for a morphism `p : X ⟶ S`. A quasi-coherent `𝒪_X`-module `ℱ`
read as a sheaf of `R`-modules still has no higher cohomology on affine opens, because
restricting the sheaf of rings changes no cohomology group
(`Stacks.Cohomology.ModuleComparison.isZero_hgroup_restrictScalars_iff`). So the covering by all
affine opens is acyclic for it, and Čech cohomology computes its cohomology as a sheaf of
`R`-modules. This is what makes the cup product of Cohomology, Section 01FP available on the
cohomology of complexes such as the relative de Rham complex, which are complexes of
`p⁻¹𝒪_S`-modules with quasi-coherent terms.

## Main results

* `Stacks.Cech.Hypercohomology.cechComputesSheaf_restrictScalars_of_isQuasicoherent`: Čech
  cohomology computes the cohomology of a quasi-coherent module read over `R`.
* `Stacks.Cech.Hypercohomology.cechComputes_of_isZero_X`: and that of a complex with zero terms.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] HasDerivedCategory.standard

/-- **Čech cohomology computes the hypercohomology of a complex all of whose terms vanish**: both
sides are zero. -/
theorem cechComputes_of_isZero_X {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (hK : ∀ q, IsZero (K.obj.X q)) :
    CechComputes O K := by
  have h0 : Homotopy (𝟙 K.obj) 0 :=
    Homotopy.ofEq (HomologicalComplex.hom_ext _ _ fun q => (hK q).eq_of_src _ _)
  rw [cechComputes_iff]
  exact fun n => ⟨cechSurjAt_of_isZero O K n (isZero_hypercohomology_of_homotopy O K h0 n),
    cechInjAt_of_isZero O K n fun U hU => isZero_cech_homology_of_homotopy O U hU K.obj h0 n⟩

section Scheme

variable (S : Scheme.{u}) {R : Sheaf (Opens.grothendieckTopology S.carrier) CommRingCat.{u}}
  (ψ : ringSheaf R ⟶ S.ringCatSheaf)

/-- **A quasi-coherent module read over `R` and placed in degree zero is acyclic on a covering by
affine opens of a scheme with affine diagonal**: the finite intersections of the covering are
affine, a quasi-coherent module has no higher cohomology on an affine open
([Stacks, Tag 01XB]), and restricting the sheaf of rings changes no cohomology group. -/
theorem isZero_rightDerived_singlePlus_restrictScalars_of_isAffineOpen
    [IsAffineHom (pullback.diagonal (terminal.from S))] {J : Type u} (V : J → S.Opens)
    (hV : ∀ j, IsAffineOpen (V j)) (F : S.Modules) [F.IsQuasicoherent] (q : ℤ) (r : ℕ)
    (s : Fin (r + 1) → J) (m : ℕ) (hm : 0 < m) :
    IsZero (((SheafOfModules.evaluation.{u} (ringSheaf R) (op (⨅ k, V (s k)))).rightDerived
      m).obj ((singlePlus R ((SheafOfModules.restrictScalars ψ).obj F) 0).1.X q)) := by
  by_cases hq : q = 0
  · subst hq
    refine (Stacks.SerreCriterionH1.isZero_rightDerived_evaluation_of_isZero_hgroup (ringSheaf R)
      _ m _ ((Stacks.Cohomology.ModuleComparison.isZero_hgroup_restrictScalars_iff ψ _ m F).2
        (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen S F _
          (IsAffineOpen.iInf fun k => hV (s k)) m hm))).of_iso
      (((SheafOfModules.evaluation.{u} (ringSheaf R) (op (⨅ k, V (s k)))).rightDerived
        m).mapIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _))
  · have := Stacks.Cohomology.FlasqueAcyclic.evaluation_additive.{u, u} (ringSheaf R)
      (op (⨅ k, V (s k)))
    exact Functor.map_isZero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)

/-- **Čech cohomology computes the cohomology of a quasi-coherent module read over `R`**, on a
scheme with affine diagonal: every cohomology class is represented on the covering by all affine
opens, and a Čech class with vanishing image becomes zero on the refinement by the affine opens
contained in the members of its covering. -/
theorem cechComputesSheaf_restrictScalars_of_isQuasicoherent
    [IsAffineHom (pullback.diagonal (terminal.from S))] (F : S.Modules) [F.IsQuasicoherent] :
    CechComputesSheaf R ((SheafOfModules.restrictScalars ψ).obj F) := by
  intro n
  refine ⟨fun a => ?_, fun I U hU z hz => ?_⟩
  · have hb := bijective_cechClass_of_acyclic R (fun W : S.affineOpens => (W : S.Opens))
      (top_eq_iSup_affineOpens S) (singlePlus R ((SheafOfModules.restrictScalars ψ).obj F) 0)
      (isZero_rightDerived_singlePlus_restrictScalars_of_isAffineOpen S ψ _ (fun W => W.2) F) n
    obtain ⟨z, hz⟩ := hb.2 a
    exact ⟨_, _, _, z, hz⟩
  · let V := fun j : AffineRefinementIndex S U => (j.1.2 : S.Opens)
    have hV := top_eq_iSup_affineRefinement S U hU
    have hc : ∀ j : AffineRefinementIndex S U, V j ≤ U j.1.1 := fun j => j.2
    have hb := bijective_cechClass_of_acyclic R V hV
      (singlePlus R ((SheafOfModules.restrictScalars ψ).obj F) 0)
      (isZero_rightDerived_singlePlus_restrictScalars_of_isAffineOpen S ψ V (fun j => j.1.2.2) F) n
    refine ⟨_, V, hV, fun j => j.1.1, hc, hb.1 ?_⟩
    have h := ConcreteCategory.congr_hom (cechClass_refinement R U hU V hV
      (fun j => j.1.1) hc (singlePlus R ((SheafOfModules.restrictScalars ψ).obj F) 0) n) z
    rw [ConcreteCategory.comp_apply] at h
    rw [map_zero, h, hz]

end Scheme

end Stacks.Cech.Hypercohomology

end
