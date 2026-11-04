module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineIntersectionComparison
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.DeRhamTypeComplexAcyclicCover
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyDevissage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Čech cohomology computes the cohomology of a quasi-coherent module

Let `X` be a scheme with affine diagonal, for instance a separated scheme. For a quasi-coherent
`𝒪_X`-module `ℱ` the canonical map from the colimit over all open coverings of the Čech
cohomology groups to the cohomology of `ℱ` is bijective in every degree: every cohomology class
is represented by a Čech cocycle on some open covering, and a Čech class whose image in
cohomology vanishes becomes zero on a refinement. This is the hypothesis
`Stacks.Cech.Hypercohomology.CechComputesSheaf` under which the cup product of Cohomology,
Section 01FP is defined by Čech cocycles.

## Main results

* `Stacks.Cech.Hypercohomology.isIso_cechClass_of_acyclic`: on an open covering whose finite
  intersections are acyclic for the terms of a bounded below complex, the Čech class map of the
  covering is an isomorphism ([Stacks, Tag 0FLH], read on cohomology).
* `Stacks.Cech.Hypercohomology.cechComputesSheaf_of_isQuasicoherent`: a quasi-coherent module on
  a scheme with affine diagonal satisfies `CechComputesSheaf`.

## Implementation notes

Every open covering of `X` is refined by the covering by all affine opens contained in one of its
members, and on a scheme with affine diagonal the finite intersections of affine opens are affine,
so quasi-coherent modules have no higher cohomology on them ([Stacks, Tag 01XB]). On such a
covering the Čech class map is an isomorphism by the module-coefficient form of
[Stacks, Tag 0FLH], `AlgebraicGeometry.DeRhamTypeComplex.isIso_cechToDerivedSections_app`.

## References

* [Stacks Project, Tag 0FLH](https://stacks.math.columbia.edu/tag/0FLH)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- **On an open covering acyclic for the terms of a bounded below complex, the Čech class map
is an isomorphism**: the comparison `Tot(Č(𝒰, K)) ⟶ RΓ(X, K)` of [Stacks, Tag 08BN] is then an
isomorphism in the derived category ([Stacks, Tag 0FLH]), so it is one on cohomology. -/
@[ega "0 12.4.7"]
theorem isIso_cechClass_of_acyclic {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (hac : ∀ (q : ℤ) (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation.{u} (ringSheaf O) (op (⨅ k, U (s k)))).rightDerived
        m).obj (K.1.X q))) (n : ℤ) :
    IsIso (cechClass O U hU K n) := by
  have h := AlgebraicGeometry.DeRhamTypeComplex.isIso_cechToDerivedSections_app X (ringSheaf O)
    ⊤ U hU K hac
  dsimp only [cechClass]
  have : IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((Stacks.Cech.Linear.totalCechToDerivedSections X (ringSheaf O) ⊤ U hU).app K)) := by
    have h' : IsIso ((Stacks.Cech.Linear.totalCechToDerivedSections X (ringSheaf O) ⊤ U
      hU).app K) := h
    infer_instance
  exact IsIso.comp_isIso' (Iso.isIso_inv ((DerivedCategory.homologyFunctorFactors _ n).app _)) this

/-- **The Čech class map of a covering is bijective when the covering is acyclic.** -/
@[ega "0 12.4.7"]
theorem bijective_cechClass_of_acyclic {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (hac : ∀ (q : ℤ) (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation.{u} (ringSheaf O) (op (⨅ k, U (s k)))).rightDerived
        m).obj (K.1.X q))) (n : ℤ) :
    Function.Bijective (cechClass O U hU K n) := by
  have := isIso_cechClass_of_acyclic O U hU K hac n
  exact ConcreteCategory.bijective_of_isIso _

section Scheme

variable (S : Scheme.{u})

/-- The affine opens of a scheme contained in some member of an open covering, indexed together
with that member. -/
abbrev AffineRefinementIndex {I : Type u} (U : I → S.Opens) : Type u :=
  {p : I × S.affineOpens // (p.2 : S.Opens) ≤ U p.1}

/-- **The affine opens contained in the members of an open covering cover the scheme.** -/
theorem top_eq_iSup_affineRefinement {I : Type u} (U : I → S.Opens) (hU : ⊤ = ⨆ i, U i) :
    (⊤ : S.Opens) = ⨆ j : AffineRefinementIndex S U, (j.1.2 : S.Opens) := by
  refine (eq_top_iff.2 fun x _ => ?_).symm
  have hx : x ∈ (⨆ i, U i) := hU ▸ trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens hi
  exact Opens.mem_iSup.2 ⟨⟨(i, ⟨W, hW⟩), hWU⟩, hxW⟩

/-- **The affine opens of a scheme cover it.** -/
theorem top_eq_iSup_affineOpens : (⊤ : S.Opens) = ⨆ W : S.affineOpens, (W : S.Opens) := by
  refine (eq_top_iff.2 fun x _ => ?_).symm
  obtain ⟨W, hW, hxW, -⟩ :=
    Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens (show x ∈ (⊤ : S.Opens) from trivial)
  exact Opens.mem_iSup.2 ⟨⟨W, hW⟩, hxW⟩

/-- **A quasi-coherent module placed in degree zero is acyclic on a covering by affine opens of a
scheme with affine diagonal**: the finite intersections of the covering are affine, and a
quasi-coherent module has no higher cohomology on an affine open ([Stacks, Tag 01XB]). -/
theorem isZero_rightDerived_singlePlus_of_isAffineOpen
    [IsAffineHom (pullback.diagonal (terminal.from S))] {J : Type u} (V : J → S.Opens)
    (hV : ∀ j, IsAffineOpen (V j)) (F : S.Modules) [F.IsQuasicoherent] (q : ℤ) (r : ℕ)
    (s : Fin (r + 1) → J) (m : ℕ) (hm : 0 < m) :
    IsZero (((SheafOfModules.evaluation.{u} (ringSheaf S.sheaf) (op (⨅ k, V (s k)))).rightDerived
      m).obj ((singlePlus S.sheaf F 0).1.X q)) := by
  by_cases hq : q = 0
  · subst hq
    exact (Stacks.Cohomology.Cech.isZero_rightDerived_evaluation_of_isZero_hgroup S _ F m
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen S F _
        (IsAffineOpen.iInf fun k => hV (s k)) m hm)).of_iso
      (((SheafOfModules.evaluation.{u} (ringSheaf S.sheaf) (op (⨅ k, V (s k)))).rightDerived
        m).mapIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F))
  · have := Stacks.Cohomology.FlasqueAcyclic.evaluation_additive.{u, u} (ringSheaf S.sheaf)
      (op (⨅ k, V (s k)))
    exact Functor.map_isZero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)

/-- **Čech cohomology computes the cohomology of a quasi-coherent module on a scheme with affine
diagonal**: every cohomology class is represented on the covering by all affine opens, and a Čech
class with vanishing image becomes zero on the refinement by the affine opens contained in the
members of its covering. -/
theorem cechComputesSheaf_of_isQuasicoherent
    [IsAffineHom (pullback.diagonal (terminal.from S))] (F : S.Modules) [F.IsQuasicoherent] :
    CechComputesSheaf S.sheaf F := by
  intro n
  refine ⟨fun a => ?_, fun I U hU z hz => ?_⟩
  · have hb := bijective_cechClass_of_acyclic S.sheaf (fun W : S.affineOpens => (W : S.Opens))
      (top_eq_iSup_affineOpens S) (singlePlus S.sheaf F 0)
      (isZero_rightDerived_singlePlus_of_isAffineOpen S _ (fun W => W.2) F) n
    obtain ⟨z, hz⟩ := hb.2 a
    exact ⟨_, _, _, z, hz⟩
  · let V := fun j : AffineRefinementIndex S U => (j.1.2 : S.Opens)
    have hV := top_eq_iSup_affineRefinement S U hU
    have hc : ∀ j : AffineRefinementIndex S U, V j ≤ U j.1.1 := fun j => j.2
    have hb := bijective_cechClass_of_acyclic S.sheaf V hV (singlePlus S.sheaf F 0)
      (isZero_rightDerived_singlePlus_of_isAffineOpen S V (fun j => j.1.2.2) F) n
    refine ⟨_, V, hV, fun j => j.1.1, hc, hb.1 ?_⟩
    have h := ConcreteCategory.congr_hom (cechClass_refinement S.sheaf U hU V hV
      (fun j => j.1.1) hc (singlePlus S.sheaf F 0) n) z
    rw [ConcreteCategory.comp_apply] at h
    rw [map_zero, h, hz]

end Scheme

end Stacks.Cech.Hypercohomology

namespace Stacks.Cech.Hypercohomology

attribute [local instance] HasDerivedCategory.standard

/-- **The cohomology `Hⁿ(X, ℱ)` of a module on a scheme, computed by Mathlib's right derived
functors of sections, is its hypercohomology placed in degree zero**: the identification
`Stacks.DerivedIndexing.rightDerivedIso` of the `ℕ`-indexed with the `ℤ`-indexed right derived
functors, the latter being the cohomology of `RΓ(X, ℱ[0])`. -/
def rightDerivedIsoHypercohomology (S : Scheme.{u}) (F : S.Modules) (n : ℕ) :
    ((Stacks.Cohomology.sectionsFunctor S ⊤).rightDerived n).obj F ≅
      hypercohomology S.sheaf (singlePlus S.sheaf F 0) n :=
  (Stacks.DerivedIndexing.rightDerivedIso (Stacks.Cohomology.sectionsFunctor S ⊤) n).app F

end Stacks.Cech.Hypercohomology
