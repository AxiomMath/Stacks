module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleColimitQuotientClauses

/-!
# Descending an exact sequence along a pullback system

Let `A` be a pullback system (`Stacks.ModuleColimit.PullbackSystem`) of abelian categories over a
cofiltered index category, with right exact inverse images, satisfying the faithfulness and
fullness clauses of Stacks 07V7 for a property `P` stable under inverse images and cokernels.
Given objects `E`, `M`, `N` of `P` at a stage, a morphism `c : M ⟶ N` and a morphism
`g : E_L ⟶ M_L` over the limit with which the epimorphism `c_L` is exact, this file produces a
later stage and a morphism `E ⟶ M` there with which (the inverse image of) `c` is exact.

This is the descent step of the proof of Stacks 0GV2: the image of `ℰ ⟶ π_*𝒪_Y` is
`π_*ℐ`, which is the kernel of `π_*𝒪_Y ⟶ π_*(𝒪_Y/ℐ)`, and the proof makes the same true at a
stage by comparing the two quotients `Coker(ℰ_i ⟶ π_{i,*}𝒪_{Y_i})` and
`π_{i,*}(𝒪_{Y_i}/ℐ_i)` of `π_{i,*}𝒪_{Y_i}` with Stacks 07V7.

## Main results

* `Stacks.ModuleColimit.PullbackSystem.exact_of_kernelSubobject_eq`: exactness passes to a
  morphism with the same kernel.
* `Stacks.ModuleColimit.PullbackSystem.exists_stage_exact_of_pbL`: the descent of exactness.

## References

* [Stacks Project, Tag 0GV2](https://stacks.math.columbia.edu/tag/0GV2)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' v₁ u₁

namespace Stacks.ModuleColimit.PullbackSystem

/-- **Exactness passes to a morphism with the same kernel.**  If `f` and `ψ` are exact and
`ψ'` has the same kernel subobject as `ψ`, then `f` and `ψ'` are exact. -/
theorem exact_of_kernelSubobject_eq {C : Type*} [Category* C] [Abelian C] {A B Q D : C}
    (f : A ⟶ B) (ψ : B ⟶ Q) (ψ' : B ⟶ D) (hfψ : f ≫ ψ = 0)
    (hex : (ShortComplex.mk f ψ hfψ).Exact) (hk : kernelSubobject ψ = kernelSubobject ψ') :
    ∃ w : f ≫ ψ' = 0, (ShortComplex.mk f ψ' w).Exact := by
  have hfac : (kernelSubobject ψ').Factors f := by
    rw [← hk]; exact (kernelSubobject_factors_iff ψ f).2 hfψ
  have w : f ≫ ψ' = 0 := (kernelSubobject_factors_iff ψ' f).1 hfac
  refine ⟨w, ?_⟩
  rw [ShortComplex.exact_iff_epi_kernel_lift] at hex ⊢
  let i : kernel ψ ≅ kernel ψ' :=
    (kernelSubobjectIso ψ).symm ≪≫ Subobject.isoOfEq _ _ hk ≪≫ kernelSubobjectIso ψ'
  have : kernel.lift ψ' f w = kernel.lift ψ f hfψ ≫ i.hom := by
    ext
    simp [i]
  rw [this]
  exact epi_comp _ _

/-- The inverse image over the limit of a transported epimorphism is an epimorphism. -/
private theorem epi_pbL_map_pb_map {J : Type w} [Category.{w'} J]
    (A : PullbackSystem.{w, w', v₁, u₁} J) {j k : J} (e : j ⟶ k) {M N : A.C k} (c : M ⟶ N)
    (hepi : Epi ((A.pbL k).map c)) : Epi ((A.pbL j).map ((A.pb e).map c)) := by
  have nat := (A.comp e).inv.naturality c
  simp only [Functor.comp_map] at nat
  have : (A.pbL j).map ((A.pb e).map c) =
      (A.comp e).inv.app M ≫ (A.pbL k).map c ≫ (A.comp e).hom.app N := by
    rw [← Category.assoc, ← nat, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [this]
  exact epi_comp _ _

variable {J : Type w} [Category.{w'} J] (A : PullbackSystem.{w, w', v₁, u₁} J)
  [∀ j, Abelian (A.C j)] [Abelian A.L]
  [∀ {j k : J} (e : j ⟶ k), (A.pb e).PreservesZeroMorphisms]
  [∀ {j k : J} (e : j ⟶ k), PreservesColimitsOfShape WalkingParallelPair (A.pb e)]
  [∀ j, (A.pbL j).PreservesZeroMorphisms]
  [∀ j, PreservesColimitsOfShape WalkingParallelPair (A.pbL j)]

/-- **Descent of an exact sequence along the system.**  Let `E`, `M`, `N` be objects of `P` at a
stage `k`, `c : M ⟶ N`, and `g : E_L ⟶ M_L` a morphism over the limit with which the epimorphism
`c_L` is exact.  Then along a chain of transition morphisms `e, e₁, …, e₄` there is a morphism
`φ : E ⟶ M` (inverse images understood) with which the inverse image of `c` is exact. -/
theorem exists_stage_exact_of_pbL (hF : A.Faithfulness) (hFu : A.Fullness)
    (hpb : ∀ {j k : J} (e : j ⟶ k) (N : A.C k), A.P k N → A.P j ((A.pb e).obj N))
    (hcoker : ∀ j {M N : A.C j} (f : M ⟶ N), A.P j M → A.P j N → A.P j (cokernel f))
    {k : J} {E M N : A.C k} (hE : A.P k E) (hM : A.P k M) (hN : A.P k N) (c : M ⟶ N)
    (g : (A.pbL k).obj E ⟶ (A.pbL k).obj M) (hw : g ≫ (A.pbL k).map c = 0)
    (hex : (ShortComplex.mk g ((A.pbL k).map c) hw).Exact) (hepi : Epi ((A.pbL k).map c)) :
    ∃ (j : J) (e : j ⟶ k) (j₁ : J) (e₁ : j₁ ⟶ j) (j₂ : J) (e₂ : j₂ ⟶ j₁) (j₃ : J)
      (e₃ : j₃ ⟶ j₂) (j₄ : J) (e₄ : j₄ ⟶ j₃)
      (φ : (A.pb e ⋙ A.pb e₁ ⋙ A.pb e₂ ⋙ A.pb e₃ ⋙ A.pb e₄).obj E ⟶
        (A.pb e ⋙ A.pb e₁ ⋙ A.pb e₂ ⋙ A.pb e₃ ⋙ A.pb e₄).obj M)
      (w : φ ≫ (A.pb e ⋙ A.pb e₁ ⋙ A.pb e₂ ⋙ A.pb e₃ ⋙ A.pb e₄).map c = 0),
      (ShortComplex.mk φ _ w).Exact := by
  obtain ⟨j, e, φ', hφ'⟩ := hFu k E M hE hM g
  let ψ := cokernel.π φ'
  let ψ' := (A.pb e).map c
  have hψP := hcoker j φ' (hpb e E hE) (hpb e M hM)
  -- `pbL ψ` is a cokernel of `pbL φ'`
  have h1 := CokernelCofork.mapIsColimit _ (cokernelIsCokernel φ') (A.pbL j)
  -- `pbL ψ'` is a cokernel of `pbL φ'`
  have nat := (A.comp e).hom.naturality c
  simp only [Functor.comp_map] at nat
  have hw' : (A.pbL j).map φ' ≫ (A.pbL j).map ψ' = 0 := by
    rw [hφ']
    simp only [ψ', Category.assoc]
    rw [← nat, ← Category.assoc g, hw, zero_comp, comp_zero]
  have hexj : (ShortComplex.mk ((A.pbL j).map φ') ((A.pbL j).map ψ') hw').Exact := by
    refine (ShortComplex.exact_iff_of_iso ?_).1 hex
    refine ShortComplex.isoMk ((A.comp e).app E) ((A.comp e).app M) ((A.comp e).app N) ?_ ?_
    · simp [hφ']
    · simp [ψ']
  have hepij := epi_pbL_map_pb_map A e c hepi
  have h2 := hexj.gIsCokernel
  let ι := IsColimit.coconePointUniqueUpToIso h1 h2
  have hι : (A.pbL j).map ψ ≫ ι.hom = (A.pbL j).map ψ' :=
    IsColimit.comp_coconePointUniqueUpToIso_hom h1 h2 WalkingParallelPair.one
  obtain ⟨j₁, e₁, j₂, e₂, j₃, e₃, j₄, e₄, hk⟩ := A.exists_kernelSubobject_eq_of_pbL hF hFu hpb
    (hpb e M hM) hψP (hpb e N hN) ψ ψ' ι hι
  let G := A.pb e₁ ⋙ A.pb e₂ ⋙ A.pb e₃ ⋙ A.pb e₄
  have hG := CokernelCofork.mapIsColimit _ (cokernelIsCokernel φ') G
  have hGex : (ShortComplex.mk (G.map φ') (G.map ψ)
      (by rw [← G.map_comp, cokernel.condition, G.map_zero])).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ hG
  obtain ⟨w, hwex⟩ := exact_of_kernelSubobject_eq (G.map φ') (G.map ψ) (G.map ψ') _ hGex hk
  exact ⟨j, e, j₁, e₁, j₂, e₂, j₃, e₃, j₄, e₄, G.map φ', w, hwex⟩

variable [IsCofiltered J]

/-- **Descent of an exact sequence along the system, from two stages.**  Let `M`, `N` be objects
of `P` at a stage `i₀` and `c : M ⟶ N`, let `E` be an object of `P` at a stage `j` with
`ε : E_L ≅ ℰ` over the limit, and let `g : ℰ ⟶ M_L` be a morphism with which the epimorphism
`c_L` is exact.  Then at a stage `k` below `j` and `i₀`, and further along a chain of transition
morphisms, there is a morphism `E ⟶ M` (inverse images understood) with which the inverse image
of `c` is exact. -/
theorem exists_stage_exact_of_pbL_of_iso (hF : A.Faithfulness) (hFu : A.Fullness)
    (hpb : ∀ {j k : J} (e : j ⟶ k) (N : A.C k), A.P k N → A.P j ((A.pb e).obj N))
    (hcoker : ∀ j {M N : A.C j} (f : M ⟶ N), A.P j M → A.P j N → A.P j (cokernel f))
    {i₀ : J} {M N : A.C i₀} (hM : A.P i₀ M) (hN : A.P i₀ N) (c : M ⟶ N)
    {j : J} {E : A.C j} (hE : A.P j E) {EL : A.L} (ε : (A.pbL j).obj E ≅ EL)
    (g : EL ⟶ (A.pbL i₀).obj M) (hw : g ≫ (A.pbL i₀).map c = 0)
    (hex : (ShortComplex.mk g ((A.pbL i₀).map c) hw).Exact) (hepi : Epi ((A.pbL i₀).map c)) :
    ∃ (k : J) (a : k ⟶ j) (b : k ⟶ i₀) (j₀ : J) (e : j₀ ⟶ k) (j₁ : J) (e₁ : j₁ ⟶ j₀)
      (j₂ : J) (e₂ : j₂ ⟶ j₁) (j₃ : J) (e₃ : j₃ ⟶ j₂) (j₄ : J) (e₄ : j₄ ⟶ j₃)
      (φ : (A.pb e ⋙ A.pb e₁ ⋙ A.pb e₂ ⋙ A.pb e₃ ⋙ A.pb e₄).obj ((A.pb a).obj E) ⟶
        (A.pb e ⋙ A.pb e₁ ⋙ A.pb e₂ ⋙ A.pb e₃ ⋙ A.pb e₄).obj ((A.pb b).obj M))
      (w : φ ≫ (A.pb e ⋙ A.pb e₁ ⋙ A.pb e₂ ⋙ A.pb e₃ ⋙ A.pb e₄).map ((A.pb b).map c) = 0),
      (ShortComplex.mk φ _ w).Exact := by
  let k := IsCofiltered.min j i₀
  let a : k ⟶ j := IsCofiltered.minToLeft j i₀
  let b : k ⟶ i₀ := IsCofiltered.minToRight j i₀
  have nat := (A.comp b).inv.naturality c
  simp only [Functor.comp_map] at nat
  let gL : (A.pbL k).obj ((A.pb a).obj E) ⟶ (A.pbL k).obj ((A.pb b).obj M) :=
    (A.comp a).inv.app E ≫ ε.hom ≫ g ≫ (A.comp b).hom.app M
  have hwL : gL ≫ (A.pbL k).map ((A.pb b).map c) = 0 := by
    have h1 : (A.comp b).hom.app M ≫ (A.pbL k).map ((A.pb b).map c) =
        (A.pbL i₀).map c ≫ (A.comp b).hom.app N := by
      simpa only [Functor.comp_map] using ((A.comp b).hom.naturality c).symm
    simp only [gL, Category.assoc]
    rw [h1, ← Category.assoc g, hw, zero_comp, comp_zero, comp_zero]
  have hexL : (ShortComplex.mk gL ((A.pbL k).map ((A.pb b).map c)) hwL).Exact := by
    refine (ShortComplex.exact_iff_of_iso ?_).2 hex
    refine ShortComplex.isoMk (((A.comp a).app E).symm ≪≫ ε) ((A.comp b).app M).symm
      ((A.comp b).app N).symm ?_ ?_
    · simp [gL]
    · exact nat.symm
  have hepiL := epi_pbL_map_pb_map A b c hepi
  exact ⟨k, a, b, A.exists_stage_exact_of_pbL hF hFu hpb hcoker (hpb a E hE) (hpb b M hM)
    (hpb b N hN) ((A.pb b).map c) gL hwL hexL hepiL⟩

end Stacks.ModuleColimit.PullbackSystem

end
