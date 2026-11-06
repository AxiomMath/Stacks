module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.BoundedBelowObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.MilnorSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationConvergenceAcyclicCover
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EventuallyConstantDifference
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorTriangleOfTower
import StacksCore.Tactic.StacksAttribute

/-! # Hypercohomology over an acyclic object of a ringed site

Let `(C, O)` be a ringed site, `K` an object of the unbounded derived category of `O`-modules and
`B` a class of objects of `C` large enough to cover the site. If every cohomology sheaf of `K` has
vanishing higher cohomology over every member of `B`, then over each member `U` of `B` the
hypercohomology edge morphism

`H^q(U, K) ⟶ Γ(U, H^q(K))`

is an isomorphism in every degree. This is Stacks 0BKZ.

`K` is the derived limit of its truncation tower `τ_{≥ -n}K` (Tag 0D6P with `d = 0`), so derived
sections over `U` give the Milnor short exact sequence of Tag 0BKX

`0 ⟶ R¹lim H^{q-1}(U, τ_{≥ -n}K) ⟶ H^q(U, K) ⟶ lim H^q(U, τ_{≥ -n}K) ⟶ 0`.

The tower of hypercohomology modules is eventually constant, so `H^q(U, K) ⟶ H^q(U, τ_{≥ -N}K)`
is an isomorphism for `N` large, and the claim reduces to the bounded below case.

## Main results

* `Stacks.Cohomology.HypercohomologyEdge.hasProduct_truncGETower`: the truncation tower of an
  object of the derived category has a product.
* `Stacks.Cohomology.HypercohomologyEdge.isEventuallyConstantTo_truncGETower_derivedSections`: the
  tower of degree-`q` hypercohomology modules over `U` is eventually constant.
* `Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover`:
  **Stacks 0BKZ**.

## Implementation notes

Three steps are taken in term mode rather than by `rw`: the identification of
`τ_{≥ -(n+1)}K ⟶ τ_{≥ -n}K` with the transition map of the tower, and the two identifications of
the limit projection with the comparison induced by `τ_{≥ -N}`. In each case the two sides print
identically but carry different `HasProduct` instance terms, so `rw` reports no occurrence.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 0BKX](https://stacks.math.columbia.edu/tag/0BKX)
* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
* [Stacks Project, Tag 0BK7](https://stacks.math.columbia.edu/tag/0BK7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace Stacks.Cohomology.HypercohomologyEdge

universe u v wRing wModule g

attribute [local instance] HasDerivedCategory.standard

section Tower

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- **The canonical maps into the truncation tower form a cone.** The truncation map
`K ⟶ τ_{≥ -m}K` composed with any transition map of `Stacks.DerivedLimit.truncGETower` is the
truncation map of the target stage. -/
lemma truncGEπ_comp_truncGETower_map (K : DerivedCategory A) {j k : ℕᵒᵖ} (φ : j ⟶ k) :
    (DerivedCategory.TStructure.t.truncGEπ (-(j.unop : ℤ))).app K ≫
        (Stacks.DerivedLimit.truncGETower A K).map φ =
      (DerivedCategory.TStructure.t.truncGEπ (-(k.unop : ℤ))).app K := by
  refine Stacks.InverseSystem.comp_map_of_comp_map_succ
    (T := Stacks.DerivedLimit.truncGETower A K)
    (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K) (fun n ↦ ?_) φ
  rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
  exact DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app
    (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) K

end Tower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{wRing})
  [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]
  [EnoughInjectives (SheafOfModules.{wModule} O)]

attribute [local instance] evaluation_additive

omit [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)] in
/-- The truncation tower of an object has a product in the derived category. -/
lemma hasProduct_truncGETower (K : DerivedCategory (SheafOfModules.{wModule} O)) :
    HasProduct fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) K).obj ⟨n⟩ :=
  (DerivedCategory.exists_isDerivedLimit_of_forall_isGE
    (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) K)
    (fun n ↦ ⟨-(n : ℤ), inferInstanceAs
      (((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K).IsGE (-(n : ℤ)))⟩)).fst

/-- **The tower of hypercohomology modules of the truncation tower is eventually constant.** If
the cohomology sheaves of `K` have no higher cohomology over `U`, then every transition map of the
tower `n ↦ H^q(U, τ_{≥ -n}K)` landing at an index `N` with `-N ≤ q` is invertible. -/
lemma isEventuallyConstantTo_truncGETower_derivedSections (U : C)
    (K : DerivedCategory (SheafOfModules.{wModule} O))
    (hK : ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation O (.op U)).rightDerived p).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).obj K)))
    (q : ℤ) (N : ℕ) (hN : -(N : ℤ) ≤ q) :
    ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) K ⋙
      derivedSections O U) ⋙ DerivedCategory.homologyFunctor
        (ModuleCat.{wModule} (O.obj.obj (.op U))) q).IsEventuallyConstantTo ⟨N⟩ := by
  intro j φ
  have hjN : N ≤ j.unop := leOfHom φ.unop
  have hπj := DerivedCategory.isIso_homologyMap_truncGEπ_app
    (-(j.unop : ℤ)) q (by omega) K
  have hπN := DerivedCategory.isIso_homologyMap_truncGEπ_app (-(N : ℤ)) q (by omega) K
  have heq := congrArg (DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).map
    (truncGEπ_comp_truncGETower_map K φ)
  have heq' : (DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(j.unop : ℤ))).app K) ≫
      (DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).map
        ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) K).map φ) =
      (DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(N : ℤ))).app K) :=
    ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).map_comp _ _).symm.trans heq
  have hsheaf : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).map
      ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) K).map φ)) := by
    have hcomp : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(j.unop : ℤ))).app K) ≫
        (DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).map
          ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) K).map φ)) := by
      rw [heq']; exact hπN
    have := hπj
    have := hcomp
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(j.unop : ℤ))).app K))
      ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).map
        ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) K).map φ))
  have hG : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q ⋙
      SheafOfModules.evaluation O (.op U)).map
      ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) K).map φ)) := by
    have := hsheaf
    exact Functor.map_isIso (SheafOfModules.evaluation O (.op U)) _
  exact Stacks.NatTransSquare.isIso_map_of_isIso_app (hypercohomologyEdge O U q)
    ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) K).map φ)
    (isIso_hypercohomologyEdge_app_truncGE O U K hK (-(j.unop : ℤ)) q)
    (isIso_hypercohomologyEdge_app_truncGE O U K hK (-(N : ℤ)) q) hG

/-- **Stacks Project Tag 0BKZ.** If the cohomology sheaves of an object of the unbounded derived
category of `O`-modules have no higher cohomology over the members of a class of objects covering
the site, then over each member its degree-`q` hypercohomology is the module of sections of its
degree-`q` cohomology sheaf: the hypercohomology edge morphism is invertible there, in every
degree. -/
@[stacks 0BKZ]
theorem isIso_hypercohomologyEdge_app_of_acyclic_cover (U : C)
    (K : DerivedCategory (SheafOfModules.{wModule} O))
    (B : ObjectProperty C) (hB : J.HasEnoughObjects B)
    (hvan : ∀ V : C, B V → ∀ p : ℕ, 0 < p → ∀ m : ℤ,
      IsZero (((SheafOfModules.evaluation O (.op V)).rightDerived p).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) m).obj K)))
    (hU : B U) (q : ℤ) :
    IsIso ((hypercohomologyEdge O U q).app K) := by
  have hK : ∀ (m : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation O (.op U)).rightDerived p).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) m).obj K)) :=
    fun m p hp ↦ hvan U hU p hp m
  have hprod := hasProduct_truncGETower O K
  obtain ⟨N, hN⟩ : ∃ N : ℕ, -(N : ℤ) ≤ q - 1 := ⟨(1 - q).toNat, by omega⟩
  obtain ⟨δ, hδ⟩ := Stacks.InverseSystem.exists_distTriang_milnor_of_isIso
    (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) K)
    (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)
    (fun n ↦ by
      rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
      exact DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) K)
    (fun L c pr d hL hc ↦
      Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic
        O K B hB hvan L c pr d hL hc)
  obtain ⟨hprodE, ar, br, htr, har, ep, i, r, hz, hep, hi, hseq, hr⟩ :=
    exists_milnor_shortExact_derivedSections O U
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) K) K
      (Pi.lift fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)
      ⟨δ, hδ⟩ q
  have hzero := Stacks.InverseSystem.isZero_cokernel_milnorDifference_functor
    ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) K ⋙ derivedSections O U) ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) (q - 1)) N
    (fun n hn ↦ isIso_homologyMap_derivedSections_truncGETower_map O U K hK (q - 1) n (by omega))
  have hπlim : IsIso (limit.π ((Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{wModule} O) K ⋙ derivedSections O U) ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) ⟨N⟩) :=
    (isEventuallyConstantTo_truncGETower_derivedSections O U K hK q N
      (by omega)).isIso_π_of_isLimit (limit.isLimit _)
  have hlift : (Pi.lift (f := fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{wModule} O) K).obj ⟨n⟩)
        fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K) ≫
      Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{wModule} O) K).obj ⟨n⟩) N =
      (DerivedCategory.TStructure.t.truncGEπ (-(N : ℤ))).app K :=
    Pi.lift_comp_π (f := fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{wModule} O) K).obj ⟨n⟩)
      (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K) N
  have h1 : IsIso ((DerivedCategory.homologyFunctor
      (ModuleCat.{wModule} (O.obj.obj (.op U))) q).map ((derivedSections O U).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(N : ℤ))).app K))) := by
    have h3 : (DerivedCategory.homologyFunctor
        (ModuleCat.{wModule} (O.obj.obj (.op U))) q).map ((derivedSections O U).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(N : ℤ))).app K)) =
        r ≫ limit.π ((Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{wModule} O) K ⋙ derivedSections O U) ⋙
          DerivedCategory.homologyFunctor
            (ModuleCat.{wModule} (O.obj.obj (.op U))) q) ⟨N⟩ :=
      (congrArg (fun f ↦ (DerivedCategory.homologyFunctor
        (ModuleCat.{wModule} (O.obj.obj (.op U))) q).map
          ((derivedSections O U).map f)) hlift).symm.trans (hr N).symm
    rw [h3]
    exact IsIso.comp_isIso' (hseq.isIso_g_iff.mpr hzero) hπlim
  exact (isIso_hypercohomologyEdge_app_iff_of_isIso_map O U q
    ((DerivedCategory.TStructure.t.truncGEπ (-(N : ℤ))).app K) h1
    (DerivedCategory.isIso_homologyMap_truncGEπ_app (-(N : ℤ)) q (by omega) K)).2
    (isIso_hypercohomologyEdge_app_truncGE O U K hK (-(N : ℤ)) q)

end Stacks.Cohomology.HypercohomologyEdge

end
