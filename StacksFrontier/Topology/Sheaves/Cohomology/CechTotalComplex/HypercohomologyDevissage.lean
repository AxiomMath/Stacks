module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCechClasses
public import StacksFrontier.Algebra.Homology.StupidTruncation

/-!
# Čech cohomology computing hypercohomology, from the terms of a complex

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings.  If Čech cohomology
agrees with cohomology for every term `Kᵖ` of a bounded below complex `K` of `𝒪_X`-modules, then
it agrees with hypercohomology for `K`: the canonical map
`colim_𝒰 Hⁿ(Tot(Č(𝒰, K))) ⟶ Hⁿ(X, K)` is bijective for every `n`.

The proof is a dévissage along short exact sequences of complexes which are split in each
degree, for which the sequences of total Čech complexes are again short exact, so that both
sides have long exact sequences compatible with the classes; the five lemma, applied with
refinements of coverings, propagates the bijectivity.

## Main definitions

* `Stacks.Cech.Hypercohomology.CechComputesSheaf`: Čech cohomology agrees with cohomology for a
  sheaf of `𝒪_X`-modules.

## Main results

* `Stacks.Cech.Hypercohomology.cechComputes_of_terms`: the dévissage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.RightDerivedBoundary
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing coverObject)

universe u w uC vC uR

namespace Stacks.Cech.LinearCupProduct

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

section Composition

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C] [Quiver.IsThin C]
  {ι ι' ι'' : Type w} [UnivLE.{w, u}] (W : ι → C) (W' : ι' → C) (W'' : ι'' → C) (R : Type uR)
  [CommRing R] (c : ι' → ι) (ρ : ∀ j, W' j ⟶ W (c j)) (c' : ι'' → ι')
  (ρ' : ∀ k, W'' k ⟶ W' (c' k)) (ρ'' : ∀ k, W'' k ⟶ W ((c ∘ c') k))

/-- **Refinement maps of Čech complexes compose**: refining along `c` and then along `c'` is
refining along `c ∘ c'`. -/
theorem cechRefinement_comp (P : PresheafModules.{u} C R) :
    cechRefinement W W' R c ρ P ≫ cechRefinement W' W'' R c' ρ' P =
      cechRefinement W W'' R (c ∘ c') ρ'' P := by
  refine HomologicalComplex.hom_ext _ _ fun n =>
    Stacks.CategoryTheory.CechComplex.hom_ext W'' P fun x => ?_
  rw [HomologicalComplex.comp_f, Category.assoc, cechRefinement_f_comp_π,
    cechRefinement_f_comp_π_assoc, cechRefinement_f_comp_π, ← Functor.map_comp, ← op_comp]
  rw [Subsingleton.elim (refinementInter W' W'' c' ρ' n x ≫ refinementInter W W' c ρ n (c' ∘ x))
    (refinementInter W W'' (c ∘ c') ρ'' n x)]
  rfl

/-- Refinement maps of the integer-indexed Čech complexes compose. -/
theorem cechIntRefinement_comp (P : PresheafModules.{u} C R) :
    (cechIntRefinement W W' R c ρ).app P ≫ (cechIntRefinement W' W'' R c' ρ').app P =
      (cechIntRefinement W W'' R (c ∘ c') ρ'').app P := by
  dsimp only [cechIntRefinement, Functor.whiskerRight_app]
  rw [← Functor.map_comp]
  exact congrArg _ (cechRefinement_comp W W' W'' R c ρ c' ρ' ρ'' P)

end Composition

end Stacks.Cech.LinearCupProduct

namespace Stacks.Cech.Refinement

attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  {I J K : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) (V : J → Opens X)
  (hV : ⊤ = ⨆ j, V j) (W : K → Opens X) (hW : ⊤ = ⨆ k, W k) (c : J → I)
  (hc : ∀ j, V j ≤ U (c j)) (c' : K → J) (hc' : ∀ k, W k ≤ V (c' k))

/-- Three squares pasted, stated with every object and morphism a variable. -/
theorem comp_eq_of_squares {C : Type*} [Category* C] {A B B' D D' E : C} (ιU : A ⟶ B)
    (r₁ : B ⟶ D) (r₂ : D ⟶ E) (r : B ⟶ E) (i₁ : A ⟶ B') (ιV : B' ⟶ D) (i₂ : B' ⟶ D')
    (ιW : D' ⟶ E) (i : A ⟶ D') (h₁ : ιU ≫ r₁ = i₁ ≫ ιV) (h₂ : ιV ≫ r₂ = i₂ ≫ ιW)
    (h₃ : i₁ ≫ i₂ = i) (h : ιU ≫ r = i ≫ ιW) : ιU ≫ r₁ ≫ r₂ = ιU ≫ r := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc, h₃, h]

/-- **Refinement maps of total Čech complexes compose.** -/
theorem cechRefinement_comp :
    cechRefinement O U hU V hV c hc ≫ cechRefinement O V hV W hW c' hc' =
      cechRefinement O U hU W hW (c ∘ c') (fun k => (hc' k).trans (hc (c' k))) := by
  have h : ∀ F : SheafOfModules.{u} (ringSheaf O),
      (cechIntRefinement O U hU V hV c hc).app F ≫ (cechIntRefinement O V hV W hW c' hc').app F =
        (cechIntRefinement O U hU W hW (c ∘ c') (fun k => (hc' k).trans (hc (c' k)))).app F :=
    fun F => by
      dsimp only [cechIntRefinement, Functor.whiskerLeft_app]
      exact Stacks.Cech.LinearCupProduct.cechIntRefinement_comp (coverObject U hU)
        (coverObject V hV) (coverObject W hW) (SectionRing (ringSheaf O) ⊤) c
        (coverRefinementHom U hU V hV c hc) c' (coverRefinementHom V hV W hW c' hc')
        (coverRefinementHom U hU W hW (c ∘ c') (fun k => (hc' k).trans (hc (c' k))))
        ((Stacks.Cohomology.CechSheaf.sectionsPresheafFunctor (R := ringSheaf O) ⊤).obj F)
  ext K : 2
  refine HomologicalComplex.hom_ext _ _ fun n =>
    HomologicalComplex₂.total.hom_ext _ fun p a hpa => ?_
  exact comp_eq_of_squares _ _ _ _ _ _ _ _ _ (ιTotal_cechRefinement O U hU V hV c hc K p a n hpa)
    (ιTotal_cechRefinement O V hV W hW c' hc' K p a n hpa)
    ((HomologicalComplex.comp_f _ _ p).symm.trans (congrArg (fun φ => φ.f p) (h (K.X a))))
    (ιTotal_cechRefinement O U hU W hW _ _ K p a n hpa)

end Stacks.Cech.Refinement

namespace Stacks.Cech.Hypercohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

section Split

variable {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)

/-- **The total Čech complexes of a short exact sequence of complexes which is split in each
degree form a short exact sequence.** -/
theorem shortExact_totalCech_of_splitting
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (σ : ∀ q, ((toSC S).map (HomologicalComplex.eval _ (up ℤ) q)).Splitting) :
    ((toSC S).map (cech O U hU)).ShortExact := by
  let T := (toSC S).map
    ((Stacks.Cohomology.CechDerived.cechComplexIntFunctor
        (ringSheaf O) ⊤ U hU).mapHomologicalComplex
      (up ℤ) ⋙ HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℤ))
  have σ' : ∀ p q,
      (T.map (HomologicalComplex.eval _ _ p ⋙ HomologicalComplex.eval _ _ q)).Splitting :=
    fun p q => ((σ q).map
        (Stacks.Cohomology.CechDerived.cechComplexIntFunctor (ringSheaf O) ⊤ U hU ⋙
          HomologicalComplex.eval _ _ p)).ofIso
        (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          ((Category.id_comp _).trans (Category.comp_id _).symm)
          ((Category.id_comp _).trans (Category.comp_id _).symm))
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
      ((Category.id_comp _).trans (Category.comp_id _).symm))
    (HomologicalComplex₂.shortExact_total_of_splitting (c₁₂ := up ℤ) T σ')

/-- Two morphisms out of a module agree as soon as they agree on every element. -/
theorem hom_ext_toMor {M N : ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)} {f g : M ⟶ N}
    (h : ∀ m : M, toMor m ≫ f = toMor m ≫ g) : f = g := by
  ext m
  have := congrArg (fun φ => (ConcreteCategory.hom φ) (1 : SectionRing (ringSheaf O) ⊤)) (h m)
  simpa [toMor] using this

/-- A rearrangement of a square of compositions through a snake identity. -/
theorem comp_comp_eq_of_snake {C : Type*} [Category* C] {A B D E F : C} (x x₀ : A ⟶ B)
    (δ : B ⟶ D) (c₁ : D ⟶ F) (c₃ : B ⟶ E) (bd : E ⟶ F) (y : A ⟶ D) (y' : A ⟶ B)
    (hx : x = x₀) (hy : y = x₀ ≫ δ) (hy' : y' = x₀) (hkey : y ≫ c₁ = y' ≫ c₃ ≫ bd) :
    x ≫ δ ≫ c₁ = x ≫ c₃ ≫ bd := by
  subst hx hy hy'
  rw [← Category.assoc]
  exact hkey

/-- The connecting morphism of the sequence of total Čech complexes and the boundary map of
hypercohomology agree on the class of a cocycle, computed through a lift. -/
theorem cocycleClass_δ_comp_cechClass
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (hC : ((toSC S).map (cech O U hU)).ShortExact) (k : ℤ)
    (z : unitModule _ ⟶ ((cech O U hU).obj S.X₃.obj).X k)
    (hz : z ≫ ((cech O U hU).obj S.X₃.obj).d k (k + 1) = 0)
    (α₂ : unitModule _ ⟶ ((cech O U hU).obj S.X₂.obj).X k)
    (hα₂ : α₂ ≫ ((cech O U hU).map S.g.hom).f k = z)
    (α₁ : unitModule _ ⟶ ((cech O U hU).obj S.X₁.obj).X (k + 1))
    (hα₁ : α₁ ≫ ((cech O U hU).map S.f.hom).f (k + 1) =
      α₂ ≫ ((cech O U hU).obj S.X₂.obj).d k (k + 1)) :
    cocycleClass k z hz ≫ hC.δ k (k + 1) rfl ≫ cechClass O U hU S.X₁ (k + 1) =
      cocycleClass k z hz ≫ cechClass O U hU S.X₃ k ≫ boundary O S hS k (k + 1) rfl := by
  have hα₃ : (α₂ ≫ ((cech O U hU).map S.g.hom).f k) ≫
      ((cech O U hU).obj S.X₃.obj).d k (k + 1) = 0 := by rw [hα₂, hz]
  have : Mono (((cech O U hU).map S.f.hom).f (k + 1 + 1)) :=
    Stacks.CupProduct.mono_f_f hC (k + 1 + 1)
  have hα₁c : α₁ ≫ ((cech O U hU).obj S.X₁.obj).d (k + 1) (k + 1 + 1) = 0 :=
    Stacks.CupProduct.comp_d_eq_zero_of_comp_eq_comp_d ((cech O U hU).map S.f.hom) k α₂ α₁ hα₁
  exact comp_comp_eq_of_snake _ _ _ _ _ _ _ _ rfl
    (Stacks.CupProduct.liftCycles_homologyπ_eq_δ hC k z hz α₂ hα₂ α₁ hα₁)
    (cocycleClass_congr k hα₂ hα₃ hz) (cechClass_boundary O U hU S hS k α₂ α₁ hα₃ hα₁c hα₁)

/-- **The connecting morphism of the sequence of total Čech complexes is the boundary map of
hypercohomology**, read through the classes. -/
theorem δ_comp_cechClass
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (hC : ((toSC S).map (cech O U hU)).ShortExact) (k : ℤ) :
    hC.δ k (k + 1) rfl ≫ cechClass O U hU S.X₁ (k + 1) =
      cechClass O U hU S.X₃ k ≫ boundary O S hS k (k + 1) rfl := by
  refine hom_ext_toMor O fun m => ?_
  obtain ⟨z, hz, hzm⟩ := Stacks.CupProduct.exists_liftCycles_homologyπ_eq
    ((cech O U hU).obj S.X₃.obj) k (k + 1) (CochainComplex.next ℤ k) (toMor m)
  obtain ⟨α₂, hα₂⟩ : ∃ α₂ : unitModule _ ⟶ ((cech O U hU).obj S.X₂.obj).X k,
      α₂ ≫ ((cech O U hU).map S.g.hom).f k = z := Stacks.CupProduct.exists_comp_g_f hC k z
  have hd : (α₂ ≫ ((cech O U hU).obj S.X₂.obj).d k (k + 1)) ≫
      ((cech O U hU).map S.g.hom).f (k + 1) = 0 := by
    rw [Category.assoc, ← ((cech O U hU).map S.g.hom).comm, ← Category.assoc, hα₂, hz]
  obtain ⟨α₁, hα₁⟩ : ∃ α₁ : unitModule _ ⟶ ((cech O U hU).obj S.X₁.obj).X (k + 1),
      α₁ ≫ ((cech O U hU).map S.f.hom).f (k + 1) =
        α₂ ≫ ((cech O U hU).obj S.X₂.obj).d k (k + 1) :=
    Stacks.CupProduct.exists_comp_f_f hC (k + 1) (α₂ ≫ ((cech O U hU).obj S.X₂.obj).d k (k + 1)) hd
  have hzm' : toMor m = cocycleClass k z hz := hzm.symm
  rw [hzm']
  exact cocycleClass_δ_comp_cechClass O U hU S hS hC k z hz α₂ hα₂ α₁ hα₁

/-! ### Elementwise forms -/

/-- `cechClass` is natural in the complex, on elements. -/
theorem cechClass_map_apply {K L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (f : K ⟶ L) (n : ℤ) (z : ((cech O U hU).obj K.obj).homology n) :
    cechClass O U hU L n (HomologicalComplex.homologyMap ((cech O U hU).map f.hom) n z) =
      hypercohomologyMap O f n (cechClass O U hU K n z) := by
  rw [← ConcreteCategory.comp_apply, cechClass_naturality, ConcreteCategory.comp_apply]

/-- The connecting morphism `Hᵏ(Tot(Č(𝒰, K₃))) ⟶ Hᵏ⁺¹(Tot(Č(𝒰, K₁)))` of a short exact sequence of
total Čech complexes. -/
abbrev cechδ (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hC : ((toSC S).map (cech O U hU)).ShortExact) (k : ℤ) :
    ((cech O U hU).obj S.X₃.obj).homology k ⟶ ((cech O U hU).obj S.X₁.obj).homology (k + 1) :=
  hC.δ k (k + 1) rfl

/-- The connecting morphism and the boundary map, on elements. -/
theorem cechClass_δ_apply
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (hC : ((toSC S).map (cech O U hU)).ShortExact) (k : ℤ)
    (z : ((cech O U hU).obj S.X₃.obj).homology k) :
    cechClass O U hU S.X₁ (k + 1) (cechδ O U hU S hC k z) =
      boundary O S hS k (k + 1) rfl (cechClass O U hU S.X₃ k z) := by
  rw [← ConcreteCategory.comp_apply, δ_comp_cechClass O U hU S hS hC k,
    ConcreteCategory.comp_apply]

/-- The map induced by a morphism of complexes, on the homology of total Čech complexes. -/
abbrev cechMap {K L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))} (f : K ⟶ L)
    (n : ℤ) : ((cech O U hU).obj K.obj).homology n ⟶ ((cech O U hU).obj L.obj).homology n :=
  HomologicalComplex.homologyMap ((cech O U hU).map f.hom) n

/-- **Exactness of `Ȟⁿ(𝒰, K₁) ⟶ Ȟⁿ(𝒰, K₂) ⟶ Ȟⁿ(𝒰, K₃)`**, on elements. -/
theorem cech_exact₂ (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hC : ((toSC S).map (cech O U hU)).ShortExact) (n : ℤ)
    (z : ((cech O U hU).obj S.X₂.obj).homology n) (hz : cechMap O U hU S.g n z = 0) :
    ∃ z₁, cechMap O U hU S.f n z₁ = z := by
  exact (ShortComplex.moduleCat_exact_iff _).1 (hC.homology_exact₂ n) z hz

/-- **Exactness of `Ȟᵏ(𝒰, K₂) ⟶ Ȟᵏ(𝒰, K₃) ⟶ Ȟᵏ⁺¹(𝒰, K₁)`**, on elements. -/
theorem cech_exact₃ (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hC : ((toSC S).map (cech O U hU)).ShortExact) (k : ℤ)
    (z : ((cech O U hU).obj S.X₃.obj).homology k) (hz : cechδ O U hU S hC k z = 0) :
    ∃ z₂, cechMap O U hU S.g k z₂ = z := by
  exact (ShortComplex.moduleCat_exact_iff _).1 (hC.homology_exact₃ k (k + 1) rfl) z hz

/-- **Exactness of `Ȟᵏ(𝒰, K₃) ⟶ Ȟᵏ⁺¹(𝒰, K₁) ⟶ Ȟᵏ⁺¹(𝒰, K₂)`**, on elements. -/
theorem cech_exact₁ (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hC : ((toSC S).map (cech O U hU)).ShortExact) (k : ℤ)
    (z : ((cech O U hU).obj S.X₁.obj).homology (k + 1)) (hz : cechMap O U hU S.f (k + 1) z = 0) :
    ∃ z₃, cechδ O U hU S hC k z₃ = z := by
  exact (ShortComplex.moduleCat_exact_iff _).1 (hC.homology_exact₁ k (k + 1) rfl) z hz

/-- The connecting morphism followed by the map to `K₂` vanishes, on elements. -/
theorem cechMap_δ (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hC : ((toSC S).map (cech O U hU)).ShortExact) (k : ℤ)
    (z : ((cech O U hU).obj S.X₃.obj).homology k) :
    cechMap O U hU S.f (k + 1) (cechδ O U hU S hC k z) = 0 := by
  rw [← ConcreteCategory.comp_apply]
  exact congrArg (fun φ => φ z) (hC.δ_comp k (k + 1) rfl)

end Split

/-! ### The long exact sequence of hypercohomology, on elements -/

/-- **Exactness of `Hⁿ(X, K₁) ⟶ Hⁿ(X, K₂) ⟶ Hⁿ(X, K₃)`**, on elements. -/
theorem hypercohomology_exact₂
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n : ℤ) (b : hypercohomology O S.X₂ n)
    (hb : hypercohomologyMap O S.g n b = 0) :
    ∃ a, hypercohomologyMap O S.f n a = b := by
  exact (ShortComplex.moduleCat_exact_iff _).1
    (DerivedCategory.HomologySequence.exact₂ _ (derivedTriangle_distinguished O S hS) n) b hb

/-- **Exactness of `Hᵏ(X, K₃) ⟶ Hᵏ⁺¹(X, K₁) ⟶ Hᵏ⁺¹(X, K₂)`**, on elements. -/
theorem hypercohomology_exact₁
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (k : ℤ) (a : hypercohomology O S.X₁ (k + 1))
    (ha : hypercohomologyMap O S.f (k + 1) a = 0) :
    ∃ c, boundary O S hS k (k + 1) rfl c = a := by
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (DerivedCategory.HomologySequence.exact₁ _ (derivedTriangle_distinguished O S hS) k
      (k + 1) rfl) a ha
  exact ⟨c, by rw [boundary_eq]; exact hc⟩

/-- The map to `K₃` followed by the boundary map vanishes, on elements. -/
theorem boundary_hypercohomologyMap
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (k : ℤ) (b : hypercohomology O S.X₂ k) :
    boundary O S hS k (k + 1) rfl (hypercohomologyMap O S.g k b) = 0 := by
  have h : hypercohomologyMap O S.g k ≫ boundary O S hS k (k + 1) rfl = 0 := by
    rw [boundary_eq]
    exact DerivedCategory.HomologySequence.comp_δ _ (derivedTriangle_distinguished O S hS) k
      (k + 1) rfl
  rw [← ConcreteCategory.comp_apply, h]
  rfl

/-! ### Refinements, on elements -/

section Refinement

variable {I J : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) (V : J → Opens X)
  (hV : ⊤ = ⨆ j, V j) (c : J → I) (hc : ∀ j, V j ≤ U (c j))

/-- The refinement map on the homology of total Čech complexes. -/
abbrev refine (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (n : ℤ) :
    ((cech O U hU).obj K.obj).homology n ⟶ ((cech O V hV).obj K.obj).homology n :=
  HomologicalComplex.homologyMap
    ((Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app K.obj) n

/-- Refining does not change the class, on elements. -/
theorem cechClass_refine_apply (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (n : ℤ) (z : ((cech O U hU).obj K.obj).homology n) :
    cechClass O V hV K n (refine O U hU V hV c hc K n z) = cechClass O U hU K n z := by
  rw [← ConcreteCategory.comp_apply, cechClass_refinement]

/-- Refinement commutes with the maps induced by morphisms of complexes, on elements. -/
theorem refine_cechMap {K L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (f : K ⟶ L) (n : ℤ) (z : ((cech O U hU).obj K.obj).homology n) :
    refine O U hU V hV c hc L n (cechMap O U hU f n z) =
      cechMap O V hV f n (refine O U hU V hV c hc K n z) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    (Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).naturality]

/-- Refinement commutes with the connecting morphisms, on elements. -/
theorem refine_δ (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hCU : ((toSC S).map (cech O U hU)).ShortExact)
    (hCV : ((toSC S).map (cech O V hV)).ShortExact) (k : ℤ)
    (z : ((cech O U hU).obj S.X₃.obj).homology k) :
    refine O U hU V hV c hc S.X₁ (k + 1) (cechδ O U hU S hCU k z) =
      cechδ O V hV S hCV k (refine O U hU V hV c hc S.X₃ k z) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  exact congrArg (fun φ => φ z) (HomologicalComplex.HomologySequence.δ_naturality
    ((toSC S).mapNatTrans (Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc)) hCU hCV k
    (k + 1) rfl)

end Refinement

/-- Refining twice is refining along the composite, on elements. -/
theorem refine_refine {I J K' : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) (V : J → Opens X)
    (hV : ⊤ = ⨆ j, V j) (W : K' → Opens X) (hW : ⊤ = ⨆ k, W k) (c : J → I)
    (hc : ∀ j, V j ≤ U (c j)) (c' : K' → J) (hc' : ∀ k, W k ≤ V (c' k))
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (n : ℤ)
    (z : ((cech O U hU).obj K.obj).homology n) :
    refine O V hV W hW c' hc' K n (refine O U hU V hV c hc K n z) =
      refine O U hU W hW (c ∘ c') (fun k => (hc' k).trans (hc (c' k))) K n z := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp, ← NatTrans.comp_app,
    Stacks.Cech.Refinement.cechRefinement_comp]

/-! ### Čech cohomology computing hypercohomology in one degree -/

/-- Every class of `Hⁿ(X, K)` is the class of a Čech class for some covering. -/
def CechSurjAt (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (n : ℤ) : Prop :=
  ∀ a : hypercohomology O K n, ∃ (I : Type u) (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (z : ((cech O U hU).obj K.obj).homology n), cechClass O U hU K n z = a

/-- A Čech class of degree `n` of `K` whose image in `Hⁿ(X, K)` vanishes vanishes after refining
the covering. -/
def CechInjAt (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (n : ℤ) : Prop :=
  ∀ (I : Type u) (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (z : ((cech O U hU).obj K.obj).homology n), cechClass O U hU K n z = 0 →
    ∃ (J : Type u) (V : J → Opens X) (hV : ⊤ = ⨆ j, V j) (c : J → I)
      (hc : ∀ j, V j ≤ U (c j)), refine O U hU V hV c hc K n z = 0

/-- `CechComputes` is surjectivity and injectivity of the comparison in every degree. -/
theorem cechComputes_iff (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) :
    CechComputes O K ↔ ∀ n, CechSurjAt O K n ∧ CechInjAt O K n :=
  Iff.rfl

/-! ### The five lemma -/

section FiveLemma

variable (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
  (hS : (toSC S).ShortExact)
  (hC : ∀ {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i),
    ((toSC S).map (cech O U hU)).ShortExact)

include hS hC in
/-- **Surjectivity in the middle of a short exact sequence**: if every class of `Hⁿ(X, K₃)` and of
`Hⁿ(X, K₁)` comes from a Čech class, and Čech classes of degree `n + 1` of `K₁` with zero image
vanish after refinement, then every class of `Hⁿ(X, K₂)` comes from a Čech class. -/
theorem cechSurjAt_of_shortExact (n : ℤ) (h₃ : CechSurjAt O S.X₃ n)
    (h₁ : CechSurjAt O S.X₁ n) (h₁' : CechInjAt O S.X₁ (n + 1)) : CechSurjAt O S.X₂ n := by
  intro a
  obtain ⟨I, U, hU, z₃, hz₃⟩ := h₃ (hypercohomologyMap O S.g n a)
  have hδ : cechClass O U hU S.X₁ (n + 1) (cechδ O U hU S (hC U hU) n z₃) = 0 := by
    rw [cechClass_δ_apply O U hU S hS (hC U hU), hz₃, boundary_hypercohomologyMap]
  obtain ⟨J, V, hV, c, hc, hρ⟩ := h₁' I U hU _ hδ
  rw [refine_δ O U hU V hV c hc S (hC U hU) (hC V hV)] at hρ
  obtain ⟨w, hw⟩ := cech_exact₃ O V hV S (hC V hV) n _ hρ
  have hg : hypercohomologyMap O S.g n (a - cechClass O V hV S.X₂ n w) = 0 := by
    rw [map_sub, ← cechClass_map_apply, hw, cechClass_refine_apply, hz₃, sub_self]
  obtain ⟨a₁, ha₁⟩ := hypercohomology_exact₂ O S hS n _ hg
  obtain ⟨I', U', hU', z₁, hz₁⟩ := h₁ a₁
  have hW := iSup_inf_eq_top V hV U' hU'
  refine ⟨J × I', _, hW,
    refine O V hV _ hW Prod.fst (fun _ => inf_le_left) S.X₂ n w +
      cechMap O _ hW S.f n (refine O U' hU' _ hW Prod.snd (fun _ => inf_le_right) S.X₁ n z₁), ?_⟩
  rw [map_add, cechClass_refine_apply, cechClass_map_apply, cechClass_refine_apply, hz₁, ha₁,
    add_sub_cancel]

include hS hC in
/-- **Injectivity in the middle of a short exact sequence**: if every class of `Hᵏ(X, K₃)` comes
from a Čech class, and Čech classes of degree `k + 1` of `K₃` and of `K₁` with zero image vanish
after refinement, then so do those of `K₂`. -/
theorem cechInjAt_of_shortExact (k : ℤ) (h₃ : CechSurjAt O S.X₃ k)
    (h₃' : CechInjAt O S.X₃ (k + 1)) (h₁ : CechInjAt O S.X₁ (k + 1)) :
    CechInjAt O S.X₂ (k + 1) := by
  intro I U hU z hz
  have hg : cechClass O U hU S.X₃ (k + 1) (cechMap O U hU S.g (k + 1) z) = 0 := by
    rw [cechClass_map_apply, hz, map_zero]
  obtain ⟨J, V, hV, c, hc, hρ⟩ := h₃' I U hU _ hg
  rw [refine_cechMap] at hρ
  obtain ⟨z₁, hz₁⟩ := cech_exact₂ O V hV S (hC V hV) (k + 1) _ hρ
  have hf : hypercohomologyMap O S.f (k + 1) (cechClass O V hV S.X₁ (k + 1) z₁) = 0 := by
    rw [← cechClass_map_apply, hz₁, cechClass_refine_apply, hz]
  obtain ⟨b, hb⟩ := hypercohomology_exact₁ O S hS k _ hf
  obtain ⟨I', V', hV', y, hy⟩ := h₃ b
  have hW := iSup_inf_eq_top V hV V' hV'
  have ht : cechClass O _ hW S.X₁ (k + 1)
      (refine O V hV _ hW Prod.fst (fun _ => inf_le_left) S.X₁ (k + 1) z₁ -
        cechδ O _ hW S (hC _ hW) k
          (refine O V' hV' _ hW Prod.snd (fun _ => inf_le_right) S.X₃ k y)) = 0 := by
    rw [map_sub, cechClass_refine_apply, cechClass_δ_apply O _ hW S hS (hC _ hW),
      cechClass_refine_apply, hy, hb, sub_self]
  obtain ⟨L, W', hW', c', hc', ht'⟩ := h₁ _ _ hW _ ht
  rw [map_sub, sub_eq_zero, refine_δ O _ hW W' hW' c' hc' S (hC _ hW) (hC W' hW')] at ht'
  have e : refine O _ hW W' hW' c' hc' S.X₂ (k + 1)
      (refine O V hV _ hW Prod.fst (fun _ => inf_le_left) S.X₂ (k + 1)
        (refine O U hU V hV c hc S.X₂ (k + 1) z)) = 0 := by
    rw [← hz₁, refine_cechMap, refine_cechMap, ht', cechMap_δ]
  rw [refine_refine, refine_refine] at e
  exact ⟨L, W', hW', _, _, e⟩

end FiveLemma

/-! ### Vanishing below the bound -/

/-- **Hypercohomology of a complex in degrees `≥ p` vanishes below `p`.** -/
theorem isZero_hypercohomology (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (p : ℤ) [K.obj.IsStrictlyGE p] (k : ℤ) (hk : k < p) : IsZero (hypercohomology O K k) := by
  have : (DerivedCategory.Plus.Q.obj K).IsGE p := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    exact (inferInstance : (DerivedCategory.Q.obj K.obj).IsGE p)
  have := Functor.isGE_rightDerivedFunctorPlus_obj
    (SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)) (DerivedCategory.Plus.Q.obj K) p
  exact DerivedCategory.Plus.isZero_homology_of_isGE _ p k hk

/-- **The total Čech complex of a complex in degrees `≥ p` vanishes below `p`.** -/
theorem isZero_cech_X {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (K : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) (p : ℤ) [K.IsStrictlyGE p] (k : ℤ)
    (hk : k < p) : IsZero (((cech O U hU).obj K).X k) := by
  refine StacksDraft.TotalComplexQuasiIso.isZero_cofan_pt _
    (HomologicalComplex₂.toGradedObject
      (Stacks.Cohomology.CechDerived.cechBicomplex (ringSheaf O) ⊤ U hU K).flip
      |>.isColimitCofanMapObj (ComplexShape.π (up ℤ) (up ℤ) (up ℤ)) k) fun i => ?_
  obtain ⟨⟨a, b⟩, hab⟩ := i
  have hab' : a + b = k := hab
  by_cases h : 0 ≤ a
  · exact Stacks.Cohomology.CechDerived.isZero_cechBicomplex_X_X _ _ _ _ K b a
      (Or.inl (K.isZero_of_isStrictlyGE p b (by omega)))
  · exact Stacks.Cohomology.CechDerived.isZero_cechBicomplex_X_X _ _ _ _ K b a (Or.inr (by omega))

/-- The comparison is surjective in a degree where hypercohomology vanishes. -/
theorem cechSurjAt_of_isZero (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (n : ℤ)
    (h : IsZero (hypercohomology O K n)) : CechSurjAt O K n := by
  have := ModuleCat.subsingleton_of_isZero h
  have hU₀ : (⊤ : Opens X) = ⨆ _ : PUnit.{u + 1}, (⊤ : Opens X) := by simp
  exact fun a => ⟨PUnit, fun _ => ⊤, hU₀, 0, Subsingleton.elim _ _⟩

/-- The comparison is injective in a degree where the total Čech complexes have no
cohomology. -/
theorem cechInjAt_of_isZero (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (n : ℤ)
    (h : ∀ {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i),
      IsZero (((cech O U hU).obj K.obj).homology n)) : CechInjAt O K n := by
  intro I U hU z _
  have := ModuleCat.subsingleton_of_isZero (h U hU)
  exact ⟨I, U, hU, id, fun _ => le_rfl, Subsingleton.elim _ _⟩

/-- **Čech cohomology computes the cohomology of a complex in degrees `≥ p` below `p`**: both
sides vanish. -/
theorem cechSurjAt_cechInjAt_of_lt (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (p : ℤ) [K.obj.IsStrictlyGE p] (k : ℤ) (hk : k < p) : CechSurjAt O K k ∧ CechInjAt O K k :=
  ⟨cechSurjAt_of_isZero O K k (isZero_hypercohomology O K p k hk),
    cechInjAt_of_isZero O K k fun U hU =>
      StacksDraft.TotalComplexQuasiIso.isZero_homology_of_isZero_X k
        (isZero_cech_X O U hU K.obj p k hk)⟩

/-! ### Invariance under isomorphism -/

/-- The map induced on hypercohomology by a composite is the composite of the induced maps. -/
theorem hypercohomologyMap_comp {K L M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (f : K ⟶ L) (g : L ⟶ M) (n : ℤ) :
    hypercohomologyMap O (f ≫ g) n = hypercohomologyMap O f n ≫ hypercohomologyMap O g n := by
  dsimp only [hypercohomologyMap]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  rfl

/-- The identity of a complex induces the identity on hypercohomology. -/
theorem hypercohomologyMap_id (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (n : ℤ) : hypercohomologyMap O (𝟙 K) n = 𝟙 _ := by
  dsimp only [hypercohomologyMap]
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

/-- The map induced on Čech cohomology by a composite is the composite of the induced maps. -/
theorem cechMap_comp {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    {K L M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))} (f : K ⟶ L) (g : L ⟶ M)
    (n : ℤ) : cechMap O U hU (f ≫ g) n = cechMap O U hU f n ≫ cechMap O U hU g n := by
  rw [cechMap, cechMap, cechMap, ← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
  rfl

/-- The identity of a complex induces the identity on Čech cohomology. -/
theorem cechMap_id {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (n : ℤ) :
    cechMap O U hU (𝟙 K) n = 𝟙 _ := by
  rw [cechMap, ← HomologicalComplex.homologyMap_id]
  exact congrArg (fun φ => HomologicalComplex.homologyMap φ n) (CategoryTheory.Functor.map_id _ _)

/-- **Čech cohomology computing hypercohomology is invariant under isomorphism.** -/
theorem cechSurjAt_cechInjAt_of_iso {K L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (e : K ≅ L) (n : ℤ) (h : CechSurjAt O K n ∧ CechInjAt O K n) :
    CechSurjAt O L n ∧ CechInjAt O L n := by
  refine ⟨fun a => ?_, fun I U hU z hz => ?_⟩
  · obtain ⟨I, U, hU, z, hz⟩ := h.1 (hypercohomologyMap O e.inv n a)
    refine ⟨I, U, hU, cechMap O U hU e.hom n z, ?_⟩
    rw [cechClass_map_apply, hz, ← ConcreteCategory.comp_apply, ← hypercohomologyMap_comp,
      e.inv_hom_id, hypercohomologyMap_id, ConcreteCategory.id_apply]
  · have hz' : cechClass O U hU K n (cechMap O U hU e.inv n z) = 0 := by
      rw [cechClass_map_apply, hz, map_zero]
    obtain ⟨J, V, hV, c, hc, hρ⟩ := h.2 I U hU _ hz'
    refine ⟨J, V, hV, c, hc, ?_⟩
    have hzz : z = cechMap O U hU e.hom n (cechMap O U hU e.inv n z) := by
      rw [← ConcreteCategory.comp_apply, ← cechMap_comp, e.inv_hom_id, cechMap_id,
        ConcreteCategory.id_apply]
    rw [hzz, refine_cechMap, hρ, map_zero]

/-! ### The dévissage along brutal truncations -/

section Truncation

open StacksDraft.StupidTruncation

/-- A sheaf of `𝒪_X`-modules placed in degree `p`, as a bounded below complex. -/
def singlePlus (F : SheafOfModules.{u} (ringSheaf O)) (p : ℤ) :
    CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)) :=
  ⟨(HomologicalComplex.single _ (up ℤ) p).obj F, ⟨p, inferInstance⟩⟩

/-- The complex `singlePlus O F p` is strictly concentrated in degrees `≥ p`. -/
instance (F : SheafOfModules.{u} (ringSheaf O)) (p : ℤ) : (singlePlus O F p).obj.IsStrictlyGE p :=
  inferInstanceAs (CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (up ℤ) p).obj F) p)

variable (L : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ)

/-- The brutal truncation `σ^{≥p}L`, as a bounded below complex. -/
def truncPlus (p : ℤ) : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)) :=
  ⟨L.stupidTrunc (embeddingUpIntGE p), ⟨p, inferInstance⟩⟩

/-- The brutal truncation `σ^{≥p}L` is strictly concentrated in degrees `≥ p`. -/
instance (p : ℤ) : (truncPlus O L p).obj.IsStrictlyGE p :=
  inferInstanceAs (CochainComplex.IsStrictlyGE (L.stupidTrunc (embeddingUpIntGE p)) p)

/-- The short exact sequence `0 ⟶ σ^{≥p+1}L ⟶ σ^{≥p}L ⟶ Lᵖ[-p] ⟶ 0` of bounded below
complexes. -/
def truncSC (p : ℤ) : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) :=
  ShortComplex.mk (X₁ := truncPlus O L (p + 1)) (X₂ := truncPlus O L p)
    (X₃ := singlePlus O (L.X p) p)
    (ObjectProperty.homMk (stupidTruncGEMapLE L (show p ≤ p + 1 by omega)))
    (ObjectProperty.homMk (stupidTruncGEπ L p))
    (ObjectProperty.hom_ext _ (stupidTruncGEShortComplex L p).zero)

/-- The sequence `0 ⟶ σ^{≥p+1}L ⟶ σ^{≥p}L ⟶ Lᵖ[-p] ⟶ 0` is short exact. -/
theorem truncSC_shortExact (p : ℤ) : (toSC (truncSC O L p)).ShortExact :=
  stupidTruncGEShortComplex_shortExact L p

/-- The sequence `0 ⟶ σ^{≥p+1}L ⟶ σ^{≥p}L ⟶ Lᵖ[-p] ⟶ 0` is split in each degree. -/
theorem nonempty_truncSC_splitting (p q : ℤ) :
    Nonempty (((toSC (truncSC O L p)).map (HomologicalComplex.eval _ (up ℤ) q)).Splitting) := by
  by_cases hq : q = p
  · subst hq
    have hi : IsIso ((stupidTruncGEπ L q).f q) := by
      rw [stupidTruncGEπ_f]
      infer_instance
    exact ⟨ShortComplex.Splitting.ofIsZeroOfIsIso _
      (CochainComplex.isZero_of_isStrictlyGE (L.stupidTrunc (embeddingUpIntGE (q + 1))) (q + 1) q
        (by omega)) hi⟩
  · have hi : IsIso ((stupidTruncGEMapLE L (show p ≤ p + 1 by omega)).f q) := by
      by_cases hpq : p < q
      · rw [stupidTruncGEMapLE_f L _ q (by omega)]
        infer_instance
      · exact IsZero.isIso
          (CochainComplex.isZero_of_isStrictlyGE (L.stupidTrunc (embeddingUpIntGE (p + 1)))
            (p + 1) q (by omega))
          (CochainComplex.isZero_of_isStrictlyGE (L.stupidTrunc (embeddingUpIntGE p)) p q
            (by omega)) _
    exact ⟨ShortComplex.Splitting.ofIsIsoOfIsZero _ hi
      (HomologicalComplex.isZero_single_obj_X (up ℤ) p (L.X p) q hq)⟩

/-- The total Čech complexes of `0 ⟶ σ^{≥p+1}L ⟶ σ^{≥p}L ⟶ Lᵖ[-p] ⟶ 0` form a short exact
sequence. -/
theorem truncSC_shortExact_cech (p : ℤ) {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) :
    ((toSC (truncSC O L p)).map (cech O U hU)).ShortExact :=
  shortExact_totalCech_of_splitting O U hU (truncSC O L p)
    (fun q => (nonempty_truncSC_splitting O L p q).some)

/-- A complex in degrees `≥ a` is its own brutal truncation `σ^{≥a}`. -/
def truncPlusIso (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (a : ℤ)
    [K.obj.IsStrictlyGE a] : truncPlus O K.obj a ≅ K := by
  have : ∀ q, IsIso ((HomologicalComplex.ιStupidTrunc K.obj (embeddingUpIntGE a)).f q) := by
    intro q
    by_cases h : a ≤ q
    · rw [ιStupidTruncGE_f K.obj a q h]
      infer_instance
    · exact IsZero.isIso
        (CochainComplex.isZero_of_isStrictlyGE (K.obj.stupidTrunc (embeddingUpIntGE a)) a q
          (by omega))
        (CochainComplex.isZero_of_isStrictlyGE K.obj a q (by omega)) _
  have hi : IsIso (HomologicalComplex.ιStupidTrunc K.obj (embeddingUpIntGE a)) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact ObjectProperty.isoMk _ (@asIso _ _ _ _ _ hi)

end Truncation

/-- **Čech cohomology computes the cohomology of a bounded below complex as soon as it computes
that of each of its terms**, each placed in its own degree.  The proof runs the five lemma down
the brutal truncations `σ^{≥p}K`, starting from a truncation above the degree in question, where
both sides vanish. -/
theorem cechComputes_of_singlePlus (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (hK : ∀ p, CechComputes O (singlePlus O (K.obj.X p) p)) : CechComputes O K := by
  rw [cechComputes_iff]
  intro N
  have key : ∀ m : ℕ, (∀ n ≤ N, CechSurjAt O (truncPlus O K.obj (N + 2 - m)) n) ∧
      (∀ n ≤ N + 1, CechInjAt O (truncPlus O K.obj (N + 2 - m)) n) := by
    intro m
    induction m with
    | zero =>
      exact ⟨fun n hn => (cechSurjAt_cechInjAt_of_lt O _ (N + 2 - ((0 : ℕ) : ℤ)) n
          (by omega)).1,
        fun n hn => (cechSurjAt_cechInjAt_of_lt O _ (N + 2 - ((0 : ℕ) : ℤ)) n (by omega)).2⟩
    | succ m ih =>
      have e : N + 2 - (m : ℤ) = N + 2 - ((m + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      rw [e] at ih
      set p := N + 2 - ((m + 1 : ℕ) : ℤ)
      have hS := truncSC_shortExact O K.obj p
      have hC := fun {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) =>
        truncSC_shortExact_cech O K.obj p U hU
      refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · exact cechSurjAt_of_shortExact O (truncSC O K.obj p) hS hC n ((hK p n).1) (ih.1 n hn)
          (ih.2 (n + 1) (by omega))
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        exact cechInjAt_of_shortExact O (truncSC O K.obj p) hS hC k ((hK p k).1)
          ((hK p (k + 1)).2) (ih.2 (k + 1) hn)
  obtain ⟨a, ha⟩ := K.property
  have : K.obj.IsStrictlyGE (min a (N + 2)) :=
    CochainComplex.isStrictlyGE_of_ge _ _ _ (min_le_left _ _)
  obtain ⟨h₁, h₂⟩ := key (N + 2 - min a (N + 2)).toNat
  have e : N + 2 - (((N + 2 - min a (N + 2)).toNat : ℕ) : ℤ) = min a (N + 2) := by omega
  rw [e] at h₁ h₂
  exact cechSurjAt_cechInjAt_of_iso O (truncPlusIso O K (min a (N + 2))) N
    ⟨h₁ N le_rfl, h₂ N (by omega)⟩

/-! ### Contractible complexes -/

/-- **A contractible bounded below complex has no hypercohomology.** -/
theorem isZero_hypercohomology_of_homotopy
    (C : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (h : Homotopy (𝟙 C.obj) 0)
    (n : ℤ) : IsZero (hypercohomology O C n) := by
  have h₁ : IsZero (DerivedCategory.Plus.Q.obj C) := by
    rw [IsZero.iff_id_eq_zero]
    exact ObjectProperty.hom_ext _ ((DerivedCategory.Q.map_id C.obj).symm.trans
      ((DerivedCategory.Q_map_eq_of_homotopy _ h).trans (DerivedCategory.Q.map_zero _ _)))
  have := CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus
    (SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤))
  exact (DerivedCategory.homologyFunctor _ n).map_isZero (DerivedCategory.Plus.ι.map_isZero
    ((SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).rightDerivedFunctorPlus.map_isZero h₁))

/-- **The total Čech complex of a contractible complex has no cohomology.** -/
theorem isZero_cech_homology_of_homotopy {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (L : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) (h : Homotopy (𝟙 L) 0) (n : ℤ) :
    IsZero (((cech O U hU).obj L).homology n) := by
  let F := Stacks.Cohomology.CechDerived.cechComplexIntFunctor (ringSheaf O) ⊤ U hU
  have h₁ := HomologicalComplex₂.totalMapHomotopy₂
    (f := (HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℤ)).map
      ((F.mapHomologicalComplex (up ℤ)).map (𝟙 L)))
    (g := (HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℤ)).map
      ((F.mapHomologicalComplex (up ℤ)).map 0)) (F.mapHomotopy h) (up ℤ)
  have h₂ : HomologicalComplex.homologyMap ((cech O U hU).map (𝟙 L)) n =
      HomologicalComplex.homologyMap ((cech O U hU).map 0) n := h₁.homologyMap_eq n
  rw [CategoryTheory.Functor.map_id, Functor.map_zero, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h₂
  exact (IsZero.iff_id_eq_zero _).2 h₂

/-! ### Shifting the degree -/

section Shift

variable (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
  (hS : (toSC S).ShortExact)
  (hC : ∀ {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i),
    ((toSC S).map (cech O U hU)).ShortExact)
  (h₂ : ∀ n, IsZero (hypercohomology O S.X₂ n))
  (h₂' : ∀ {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) (n : ℤ),
    IsZero (((cech O U hU).obj S.X₂.obj).homology n))

include h₂ in
/-- If the middle term of a short exact sequence has vanishing hypercohomology, then the boundary
map `H^k(S.X₃) ⟶ H^{k+1}(S.X₁)` is injective. -/
theorem boundary_injective (k : ℤ) (b : hypercohomology O S.X₃ k)
    (hb : boundary O S hS k (k + 1) rfl b = 0) : b = 0 := by
  obtain ⟨x, rfl⟩ := exact_boundary O S hS k b hb
  have := ModuleCat.subsingleton_of_isZero (h₂ k)
  rw [Subsingleton.elim x 0, map_zero]

include hS hC h₂ h₂' in
/-- **Čech cohomology computing hypercohomology moves across the boundary map** of a short exact
sequence whose middle term has neither hypercohomology nor Čech cohomology. -/
theorem cechComputesAt_iff_of_acyclic (k : ℤ) :
    (CechSurjAt O S.X₃ k ∧ CechInjAt O S.X₃ k) ↔
      (CechSurjAt O S.X₁ (k + 1) ∧ CechInjAt O S.X₁ (k + 1)) := by
  constructor
  · rintro ⟨hs, hi⟩
    refine ⟨fun a => ?_, fun I U hU z hz => ?_⟩
    · have := ModuleCat.subsingleton_of_isZero (h₂ (k + 1))
      obtain ⟨c, rfl⟩ := hypercohomology_exact₁ O S hS k a (Subsingleton.elim _ _)
      obtain ⟨I, U, hU, z, rfl⟩ := hs c
      exact ⟨I, U, hU, _, cechClass_δ_apply O U hU S hS (hC U hU) k z⟩
    · have := ModuleCat.subsingleton_of_isZero (h₂' U hU (k + 1))
      obtain ⟨y, rfl⟩ := cech_exact₁ O U hU S (hC U hU) k z (Subsingleton.elim _ _)
      rw [cechClass_δ_apply O U hU S hS (hC U hU)] at hz
      obtain ⟨J, V, hV, c, hc, hy⟩ := hi I U hU y (boundary_injective O S hS h₂ k _ hz)
      exact ⟨J, V, hV, c, hc, by rw [refine_δ O U hU V hV c hc S (hC U hU) (hC V hV), hy, map_zero]⟩
  · rintro ⟨hs, hi⟩
    refine ⟨fun b => ?_, fun I U hU y hy => ?_⟩
    · obtain ⟨I, U, hU, z₁, hz₁⟩ := hs (boundary O S hS k (k + 1) rfl b)
      have := ModuleCat.subsingleton_of_isZero (h₂' U hU (k + 1))
      obtain ⟨y, rfl⟩ := cech_exact₁ O U hU S (hC U hU) k z₁ (Subsingleton.elim _ _)
      refine ⟨I, U, hU, y, ?_⟩
      rw [cechClass_δ_apply O U hU S hS (hC U hU)] at hz₁
      exact sub_eq_zero.1 (boundary_injective O S hS h₂ k _ (by rw [map_sub, hz₁, sub_self]))
    · have h0 : cechClass O U hU S.X₁ (k + 1) (cechδ O U hU S (hC U hU) k y) = 0 := by
        rw [cechClass_δ_apply O U hU S hS (hC U hU), hy, map_zero]
      obtain ⟨J, V, hV, c, hc, hρ⟩ := hi I U hU _ h0
      rw [refine_δ O U hU V hV c hc S (hC U hU) (hC V hV)] at hρ
      obtain ⟨x, hx⟩ := cech_exact₃ O V hV S (hC V hV) k _ hρ
      have := ModuleCat.subsingleton_of_isZero (h₂' V hV k)
      exact ⟨J, V, hV, c, hc, by rw [← hx, Subsingleton.elim x 0, map_zero]⟩

end Shift

/-- The short exact sequence `0 ⟶ F[-p-1] ⟶ Cone(𝟙) ⟶ F[-p-1][1] ⟶ 0` of bounded below complexes,
whose middle term is contractible. -/
def coneSC (F : SheafOfModules.{u} (ringSheaf O)) (p : ℤ) :
    ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) :=
  ShortComplex.mk (X₁ := singlePlus O F (p + 1))
    (X₂ := ⟨CochainComplex.mappingCone (𝟙 (singlePlus O F (p + 1)).obj),
      ⟨p, CochainComplex.isStrictlyGE_mappingCone _ (p + 1) (p + 1) p⟩⟩)
    (X₃ := ⟨((singlePlus O F (p + 1)).obj)⟦(1 : ℤ)⟧,
      ⟨p, ((singlePlus O F (p + 1)).obj).isStrictlyGE_shift (p + 1) 1 p (by omega)⟩⟩)
    (ObjectProperty.homMk
      (CochainComplex.mappingCone.triangleRotateShortComplex (𝟙 (singlePlus O F (p + 1)).obj)).f)
    (ObjectProperty.homMk
      (CochainComplex.mappingCone.triangleRotateShortComplex (𝟙 (singlePlus O F (p + 1)).obj)).g)
    (ObjectProperty.hom_ext _
      (CochainComplex.mappingCone.triangleRotateShortComplex (𝟙 (singlePlus O F (p + 1)).obj)).zero)

/-- **Čech cohomology agrees with cohomology for a sheaf in degree `p` if and only if it does in
degree `p + 1`.** -/
theorem cechComputes_singlePlus_iff (F : SheafOfModules.{u} (ringSheaf O)) (p : ℤ) :
    CechComputes O (singlePlus O F p) ↔ CechComputes O (singlePlus O F (p + 1)) := by
  have hS : (toSC (coneSC O F p)).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
      (CochainComplex.mappingCone.triangleRotateShortComplexSplitting
        (𝟙 (singlePlus O F (p + 1)).obj) n).shortExact
  have hC : ∀ {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i),
      ((toSC (coneSC O F p)).map (cech O U hU)).ShortExact := fun U hU =>
    shortExact_totalCech_of_splitting O U hU (coneSC O F p)
      (CochainComplex.mappingCone.triangleRotateShortComplexSplitting
        (𝟙 (singlePlus O F (p + 1)).obj))
  have hcontr := CochainComplex.mappingCone.homotopyToZeroOfId (singlePlus O F (p + 1)).obj
  have h₂ := isZero_hypercohomology_of_homotopy O (coneSC O F p).X₂ hcontr
  have h₂' := fun {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) =>
    isZero_cech_homology_of_homotopy O U hU (coneSC O F p).X₂.obj hcontr
  have e : (coneSC O F p).X₃ ≅ singlePlus O F p := ObjectProperty.isoMk _
    (((CochainComplex.singleFunctors (SheafOfModules.{u} (ringSheaf O))).shiftIso 1 p (p + 1)
      (by omega)).app F)
  rw [cechComputes_iff, cechComputes_iff]
  refine ⟨fun h n => ?_, fun h k => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact (cechComputesAt_iff_of_acyclic O (coneSC O F p) hS hC h₂ h₂' k).1
      (cechSurjAt_cechInjAt_of_iso O e.symm k (h k))
  · exact cechSurjAt_cechInjAt_of_iso O e k
      ((cechComputesAt_iff_of_acyclic O (coneSC O F p) hS hC h₂ h₂' k).2 (h (k + 1)))

/-- **Čech cohomology agrees with cohomology for the sheaf `F`**: for every `n` the canonical map
`colim_𝒰 Ȟⁿ(𝒰, F) ⟶ Hⁿ(X, F)` from the colimit over all open coverings of the Čech cohomology
groups is bijective. -/
def CechComputesSheaf (F : SheafOfModules.{u} (ringSheaf O)) : Prop :=
  CechComputes O (singlePlus O F 0)

/-- The sheaf placed in any degree. -/
theorem CechComputesSheaf.singlePlus {F : SheafOfModules.{u} (ringSheaf O)}
    (hF : CechComputesSheaf O F) (p : ℤ) : CechComputes O (singlePlus O F p) := by
  induction p using Int.induction_on with
  | zero => exact hF
  | succ p ih => exact (cechComputes_singlePlus_iff O F p).1 ih
  | pred p ih =>
    refine (cechComputes_singlePlus_iff O F (-(p : ℤ) - 1)).2 ?_
    rw [sub_add_cancel]
    exact ih

/-- **Čech cohomology agrees with hypercohomology for a bounded below complex as soon as it agrees
with cohomology for each of its terms.** -/
theorem cechComputes_of_terms (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (hK : ∀ p, CechComputesSheaf O (K.obj.X p)) : CechComputes O K :=
  cechComputes_of_singlePlus O K fun p => (hK p).singlePlus O p

end Stacks.Cech.Hypercohomology
