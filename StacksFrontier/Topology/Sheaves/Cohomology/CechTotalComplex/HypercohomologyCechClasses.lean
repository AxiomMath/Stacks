module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBoundary
public import StacksFrontier.Algebra.Homology.CupProductBoundaryClass
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Čech classes in hypercohomology

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings.  This file records the
formal properties of the classes `Hⁿ(Tot(Č(𝒰, K))) ⟶ Hⁿ(X, K)` of [Stacks, Tag 08BN] used to
compute with Čech cocycles: they are compatible with refinement, the boundary maps of a short exact
sequence sit in a long exact sequence, and — when Čech cohomology computes hypercohomology — every
class of `Hⁿ(X, K₃)` is represented by the image of a cochain of `K₂` whose coboundary comes
from `K₁`.

## Main definitions

* `Stacks.Cech.Hypercohomology.CechComputes`: Čech cohomology agrees with cohomology for a
  bounded below complex in a given degree: the canonical map
  `colim_𝒰 Hᵏ(Tot(Č(𝒰, K))) ⟶ Hᵏ(X, K)` is bijective, written out as surjectivity and as the
  vanishing after refinement of every Čech class with zero image.

## Main results

* `Stacks.Cech.Hypercohomology.cechClass_refinement`: refining does not change the class.
* `Stacks.Cech.Hypercohomology.exact_boundary`: exactness of
  `Hⁿ(X, K₂) ⟶ Hⁿ(X, K₃) ⟶ Hⁿ⁺¹(X, K₁)`.
* `Stacks.Cech.Hypercohomology.exists_cechLift`: the representation of a class of `Hⁿ(X, K₃)` by
  a lift to `K₂` with coboundary in `K₁`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace Pretriangulated
open Stacks.Cohomology.RightDerivedBoundary
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit
attribute [local instance] additive_evaluation_ringSheaf

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-! ### The long exact sequence -/

section Triangle

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- **The distinguished triangle of `D⁺(𝒜)` of a short exact sequence of bounded below
complexes.** -/
def plusTriangle (S : ShortComplex (CochainComplex.Plus A)) (hS : (toSC S).ShortExact) :
    Triangle (DerivedCategory.Plus A) :=
  Triangle.mk (DerivedCategory.Plus.Q.map S.f) (DerivedCategory.Plus.Q.map S.g) (plusδ S hS)

/-- The triangle of a short exact sequence of bounded below complexes is distinguished. -/
theorem plusTriangle_distinguished (S : ShortComplex (CochainComplex.Plus A))
    (hS : (toSC S).ShortExact) : plusTriangle S hS ∈ distTriang _ := by
  rw [← DerivedCategory.Plus.ι.map_distinguished_iff]
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · refine Eq.trans ?_ (Category.id_comp _).symm
    refine Eq.trans (eq_whisker (mapδ_ι_plusδ S hS) _) ?_
    exact Eq.trans (whisker_eq _ (CategoryTheory.Functor.map_id _ _)) (Category.comp_id _)

end Triangle

/-- **The image under `RΓ(X, -)` of the distinguished triangle** of a short exact sequence of
bounded below complexes of `𝒪_X`-modules. -/
def derivedTriangle (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) :
    Triangle (DerivedCategory (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤))) :=
  DerivedCategory.Plus.ι.mapTriangle.obj
    ((SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).rightDerivedFunctorPlus.mapTriangle.obj
      (plusTriangle S hS))

/-- The triangle `derivedTriangle O S hS` is distinguished. -/
theorem derivedTriangle_distinguished
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) : derivedTriangle O S hS ∈ distTriang _ :=
  have := CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus
    (SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤))
  DerivedCategory.Plus.ι.map_distinguished _
    (Functor.map_distinguished _ _ (plusTriangle_distinguished S hS))

/-- The boundary map is the connecting morphism of the long exact sequence of `derivedTriangle`. -/
theorem boundary_eq (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    boundary O S hS n₀ n₁ h =
      DerivedCategory.HomologySequence.δ (derivedTriangle O S hS) n₀ n₁ h := by
  dsimp only [boundary, DerivedCategory.HomologySequence.δ, boundaryD]
  congr 1
  exact Functor.mapδ_comp
    (SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).rightDerivedFunctorPlus
    DerivedCategory.Plus.ι (plusδ S hS)

/-- **Exactness of `Hⁿ(X, K₂) ⟶ Hⁿ(X, K₃) ⟶ Hⁿ⁺¹(X, K₁)`.** -/
theorem exact_boundary
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n : ℤ) (a : hypercohomology O S.X₃ n)
    (ha : boundary O S hS n (n + 1) rfl a = 0) :
    ∃ b : hypercohomology O S.X₂ n, hypercohomologyMap O S.g n b = a := by
  have hex := DerivedCategory.HomologySequence.exact₃ _ (derivedTriangle_distinguished O S hS) n
    (n + 1) rfl
  rw [ShortComplex.moduleCat_exact_iff] at hex
  rw [boundary_eq] at ha
  exact hex a ha

/-- **The boundary map followed by the map induced by `K₁ ⟶ K₂` vanishes.** -/
theorem boundary_comp_hypercohomologyMap
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n : ℤ) :
    boundary O S hS n (n + 1) rfl ≫ hypercohomologyMap O S.f (n + 1) = 0 := by
  rw [boundary_eq]
  exact DerivedCategory.HomologySequence.δ_comp _ (derivedTriangle_distinguished O S hS) n (n + 1)
    rfl

/-! ### Refinement -/

/-- Two squares pasted, stated with every object and morphism a variable. -/
theorem comp_comp_eq_of_comp_eq {C : Type*} [Category* C] {a b c d e : C} (x : a ⟶ b)
    (y : b ⟶ c) (z : c ⟶ d) (y' : a ⟶ e) (w : e ⟶ c) (z' : e ⟶ d) (h₁ : x ≫ y = y' ≫ w)
    (h₂ : w ≫ z = z') : x ≫ y ≫ z = y' ≫ z' := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

section Refinement

variable {I J : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) (V : J → Opens X)
  (hV : ⊤ = ⨆ j, V j) (c : J → I) (hc : ∀ j, V j ≤ U (c j))

/-- **Refining the covering does not change the class in hypercohomology.** -/
@[reassoc]
theorem cechClass_refinement (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (n : ℤ) :
    HomologicalComplex.homologyMap
        ((Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app K.obj) n ≫
      cechClass O V hV K n = cechClass O U hU K n := by
  dsimp only [cechClass]
  have h1 := (DerivedCategory.homologyFunctorFactors
    (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) n).inv.naturality
      ((Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app K.obj)
  have h2 := congrArg (fun g => (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) n).map (g.app K))
    (Stacks.Cech.Refinement.cechRefinementDerived_comp_totalCechToDerivedSections O U hU V hV c hc)
  simp only [NatTrans.comp_app, Functor.map_comp] at h2
  exact comp_comp_eq_of_comp_eq _ _ _ _ _ _ h1 h2

end Refinement

/-! ### Čech cohomology computing hypercohomology -/

/-- **Čech cohomology agrees with cohomology for a bounded below complex `K`**: for every `n` the
canonical map `colim_𝒰 Hⁿ(Tot(Č(𝒰, K))) ⟶ Hⁿ(X, K)` from the colimit over all open coverings
(the transition maps being the refinement maps, compatible with the classes by
`cechClass_refinement`) is bijective.  Written out: every class of `Hⁿ(X, K)` is the class of a
Čech class for some covering, and a Čech class whose image vanishes vanishes after refining the
covering. -/
def CechComputes (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) : Prop :=
  ∀ n : ℤ,
    (∀ a : hypercohomology O K n, ∃ (I : Type u) (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
      (z : ((Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU).obj
        K.obj).homology n), cechClass O U hU K n z = a) ∧
    (∀ (I : Type u) (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
      (z : ((Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU).obj
        K.obj).homology n), cechClass O U hU K n z = 0 →
      ∃ (J : Type u) (V : J → Opens X) (hV : ⊤ = ⨆ j, V j) (c : J → I)
        (hc : ∀ j, V j ≤ U (c j)),
        HomologicalComplex.homologyMap
          ((Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app K.obj) n z = 0)

/-! ### Common refinements -/

/-- The pairwise intersections of two open coverings of `X` cover `X`. -/
theorem iSup_inf_eq_top {I I' : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (U' : I' → Opens X) (hU' : ⊤ = ⨆ i, U' i) :
    ⊤ = ⨆ ij : I × I', U ij.1 ⊓ U' ij.2 := by
  refine (eq_top_iff.2 fun x _ => ?_).symm
  have hx : x ∈ (⨆ i, U i) := hU ▸ trivial
  have hx' : x ∈ (⨆ i, U' i) := hU' ▸ trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  obtain ⟨i', hi'⟩ := Opens.mem_iSup.1 hx'
  exact Opens.mem_iSup.2 ⟨(i, i'), ⟨hi, hi'⟩⟩

/-! ### Elements as morphisms out of the ring -/

section Elements

variable {R : Type u} [Ring R]

/-- The ring `R` as a module over itself: the test object through which elements of an
`R`-module are morphisms. -/
abbrev unitModule (R : Type u) [Ring R] : ModuleCat.{u} R := ModuleCat.of R R

/-- The ring `R`, as a module over itself, is projective. -/
instance (R : Type u) [Ring R] : Projective (unitModule R) :=
  ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{1} R)

/-- The morphism `R ⟶ M` sending `1` to `x`. -/
def toMor {M : ModuleCat.{u} R} (x : M) : unitModule R ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)

/-- The morphism `toMor x` sends `1` to `x`. -/
@[simp]
theorem toMor_apply_one {M : ModuleCat.{u} R} (x : M) : toMor x (1 : R) = x := by
  simp [toMor]

/-- Composing `toMor x` with `f` gives `toMor (f x)`. -/
theorem toMor_comp {M N : ModuleCat.{u} R} (x : M) (f : M ⟶ N) : toMor x ≫ f = toMor (f x) := by
  ext : 1
  exact LinearMap.ext_ring (by simp [toMor])

/-- `toMor` sends a difference of elements to the difference of the morphisms. -/
theorem toMor_sub {M : ModuleCat.{u} R} (x y : M) : toMor (x - y) = toMor x - toMor y := by
  ext : 1
  exact LinearMap.ext_ring (by simp [toMor])

/-- `toMor` sends a sum of elements to the sum of the morphisms. -/
theorem toMor_add {M : ModuleCat.{u} R} (x y : M) : toMor (x + y) = toMor x + toMor y := by
  ext : 1
  exact LinearMap.ext_ring (by simp [toMor])

/-- Every morphism `f : R ⟶ M` is `toMor` of the image of `1` under `f`. -/
theorem toMor_apply {M : ModuleCat.{u} R} (f : unitModule R ⟶ M) : toMor (f (1 : R)) = f := by
  ext : 1
  exact LinearMap.ext_ring (by simp [toMor])

end Elements

/-- The class of a cocycle depends only on the cocycle. -/
theorem cocycleClass_congr {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ} {P : C}
    (n : ℤ) {x y : P ⟶ K.X n} (h : x = y) (hx : x ≫ K.d n (n + 1) = 0)
    (hy : y ≫ K.d n (n + 1) = 0) : cocycleClass n x hx = cocycleClass n y hy := by
  subst h
  rfl

/-- The class of a cocycle is additive in the cocycle. -/
theorem cocycleClass_add {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ} {P : C}
    (n : ℤ) (x y : P ⟶ K.X n) (hx : x ≫ K.d n (n + 1) = 0) (hy : y ≫ K.d n (n + 1) = 0) :
    cocycleClass n (x + y) (by rw [Preadditive.add_comp, hx, hy, add_zero]) =
      cocycleClass n x hx + cocycleClass n y hy := by
  dsimp only [cocycleClass]
  rw [← Preadditive.add_comp]
  congr 1
  rw [← cancel_mono (K.iCycles n)]
  simp

/-- The total Čech complex of a covering of `X`, on complexes of `𝒪_X`-modules. -/
abbrev cech {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) :=
  Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU

/-- A cocycle pushed along a morphism of complexes is a cocycle. -/
theorem comp_f_d_eq_zero {C : Type*} [Category* C] [Preadditive C] {K L : CochainComplex C ℤ}
    {P : C} (φ : K ⟶ L) {n m : ℤ} {x : P ⟶ K.X n} (hx : x ≫ K.d n m = 0) :
    (x ≫ φ.f n) ≫ L.d n m = 0 := by
  rw [Category.assoc, φ.comm, ← Category.assoc, hx, zero_comp]

/-- The Čech complexes of `K₁ ⟶ K₂ ⟶ K₃` compose to zero. -/
theorem cech_map_f_comp_map_g_f
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))) {I : Type u}
    (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) (k : ℤ) :
    ((cech O U hU).map S.f.hom).f k ≫ ((cech O U hU).map S.g.hom).f k = 0 := by
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp,
    show S.f.hom ≫ S.g.hom = 0 from congrArg (fun z => z.hom) S.zero, Functor.map_zero,
    HomologicalComplex.zero_f]

/-- A natural transformation between functors to complexes commutes with the components of the
maps of complexes. -/
private theorem map_f_comp_app_f {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms D]
    {F G : C ⥤ HomologicalComplex D (ComplexShape.up ℤ)} (α : F ⟶ G) {A B : C} (f : A ⟶ B)
    (n : ℤ) {P : D} (x : P ⟶ (F.obj A).X n) :
    (x ≫ (F.map f).f n) ≫ (α.app B).f n = (x ≫ (α.app A).f n) ≫ (G.map f).f n := by
  simp only [Category.assoc, ← HomologicalComplex.comp_f, α.naturality]

/-- A cochain of `K₂` whose coboundary comes from `K₁` maps to a cocycle of `K₃`. -/
private theorem comp_map_g_f_d_eq_zero
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))) {I : Type u}
    (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) {n : ℤ} {P : ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)}
    {x : P ⟶ ((cech O U hU).obj S.X₂.obj).X n} {y : P ⟶ ((cech O U hU).obj S.X₁.obj).X (n + 1)}
    (h : y ≫ ((cech O U hU).map S.f.hom).f (n + 1) = x ≫ ((cech O U hU).obj S.X₂.obj).d n (n + 1)) :
    (x ≫ ((cech O U hU).map S.g.hom).f n) ≫ ((cech O U hU).obj S.X₃.obj).d n (n + 1) = 0 := by
  rw [Category.assoc, ((cech O U hU).map S.g.hom).comm, ← Category.assoc, ← h, Category.assoc,
    cech_map_f_comp_map_g_f, comp_zero]

/-- The boundary of a class of `Hⁿ(X, K₃)` is the class of a Čech cocycle `α₁` of `K₁` whose image
in `K₂` is a coboundary `d(σ)`, for some open covering. -/
theorem exists_cechCocycle_boundary
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n : ℤ) (h₁ : CechComputes O S.X₁) (h₂ : CechComputes O S.X₂)
    (a : unitModule _ ⟶ hypercohomology O S.X₃ n) :
    ∃ (J : Type u) (V : J → Opens X) (hV : ⊤ = ⨆ j, V j)
      (σ : unitModule _ ⟶ ((cech O V hV).obj S.X₂.obj).X n)
      (α₁ : unitModule _ ⟶ ((cech O V hV).obj S.X₁.obj).X (n + 1))
      (hα₁ : α₁ ≫ ((cech O V hV).obj S.X₁.obj).d (n + 1) (n + 1 + 1) = 0),
      α₁ ≫ ((cech O V hV).map S.f.hom).f (n + 1) = σ ≫ ((cech O V hV).obj S.X₂.obj).d n (n + 1) ∧
        cocycleClass (n + 1) α₁ hα₁ ≫ cechClass O V hV S.X₁ (n + 1) =
          a ≫ boundary O S hS n (n + 1) rfl := by
  obtain ⟨I, U, hU, z, hz⟩ := (h₁ (n + 1)).1 ((a ≫ boundary O S hS n (n + 1) rfl) (1 : _))
  obtain ⟨z₁, hz₁, hz₁c⟩ := Stacks.CupProduct.exists_liftCycles_homologyπ_eq
    ((cech O U hU).obj S.X₁.obj) (n + 1) (n + 1 + 1) (CochainComplex.next ℤ (n + 1)) (toMor z)
  have hz₁c' : cocycleClass (n + 1) z₁ hz₁ = toMor z := hz₁c
  have hb : cocycleClass (n + 1) z₁ hz₁ ≫ cechClass O U hU S.X₁ (n + 1) =
      a ≫ boundary O S hS n (n + 1) rfl := by
    rw [hz₁c', toMor_comp, hz, toMor_apply]
  have hfz := comp_f_d_eq_zero ((cech O U hU).map S.f.hom) hz₁
  have hb₂ : cocycleClass (n + 1) _ hfz ≫ cechClass O U hU S.X₂ (n + 1) = 0 := by
    rw [← cocycleClass_comp_homologyMap ((cech O U hU).map S.f.hom) (n + 1) z₁ hz₁,
      Category.assoc, cechClass_naturality, ← Category.assoc, hb, Category.assoc,
      boundary_comp_hypercohomologyMap, comp_zero]
  obtain ⟨J, V, hV, c, hc, hzero⟩ := (h₂ (n + 1)).2 I U hU ((cocycleClass (n + 1) _ hfz) (1 : _))
    (by
      rw [← ConcreteCategory.comp_apply, hb₂]
      rfl)
  let r₁ := (Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app S.X₁.obj
  let r₂ := (Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app S.X₂.obj
  have hr₂z : (z₁ ≫ ((cech O U hU).map S.f.hom).f (n + 1) ≫ r₂.f (n + 1)) ≫
      ((cech O V hV).obj S.X₂.obj).d (n + 1) (n + 1 + 1) = 0 := by
    simpa only [Category.assoc] using comp_f_d_eq_zero r₂ hfz
  have hzero' : cocycleClass (n + 1) _ hr₂z = 0 := by
    have := cocycleClass_comp_homologyMap r₂ (n + 1) _ hfz
    simp only [Category.assoc] at this
    rw [← this, ← toMor_apply (cocycleClass (n + 1) _ hfz ≫ _), ConcreteCategory.comp_apply,
      hzero]
    ext : 1
    exact LinearMap.ext_ring (by simp [toMor])
  obtain ⟨σ, hσ⟩ := Stacks.CupProduct.exists_eq_add_comp_d_of_liftCycles_homologyπ_eq
    ((cech O V hV).obj S.X₂.obj) n (n + 1) (n + 1 + 1) (by simp)
    (CochainComplex.next ℤ (n + 1)) _ 0 hr₂z zero_comp
    (by
      have h0 := HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary
        ((cech O V hV).obj S.X₂.obj) (0 : unitModule _ ⟶ _) (n + 1 + 1)
        (CochainComplex.next ℤ (n + 1)) (i' := n) 0 (by simp)
      exact hzero'.trans h0.symm)
  rw [zero_add] at hσ
  have hα₁σ : (z₁ ≫ r₁.f (n + 1)) ≫ ((cech O V hV).map S.f.hom).f (n + 1) =
      σ ≫ ((cech O V hV).obj S.X₂.obj).d n (n + 1) := by
    rw [← map_f_comp_app_f (Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc) S.f.hom]
    rwa [Category.assoc]
  refine ⟨J, V, hV, σ, z₁ ≫ r₁.f (n + 1), comp_f_d_eq_zero r₁ hz₁, hα₁σ, ?_⟩
  rw [← cocycleClass_comp_homologyMap r₁ (n + 1) z₁ hz₁, Category.assoc, cechClass_refinement, hb]

/-- A class of `Hⁿ(X, K₃)` with vanishing boundary is the image of the class of a Čech cocycle of
`K₂`, for some open covering. -/
theorem exists_cechCocycle_of_boundary_eq_zero
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n : ℤ) (h₂ : CechComputes O S.X₂)
    (a : unitModule _ ⟶ hypercohomology O S.X₃ n) (ha : a ≫ boundary O S hS n (n + 1) rfl = 0) :
    ∃ (J : Type u) (W : J → Opens X) (hW : ⊤ = ⨆ j, W j)
      (w : unitModule _ ⟶ ((cech O W hW).obj S.X₂.obj).X n)
      (hw : w ≫ ((cech O W hW).obj S.X₂.obj).d n (n + 1) = 0),
      cocycleClass n w hw ≫ cechClass O W hW S.X₂ n ≫ hypercohomologyMap O S.g n = a := by
  obtain ⟨b₂, hb₂⟩ := exact_boundary O S hS n (a (1 : _))
    (by
      rw [← ConcreteCategory.comp_apply, ha]
      rfl)
  obtain ⟨J, W, hW, y, hy⟩ := (h₂ n).1 b₂
  obtain ⟨w, hw, hwc⟩ := Stacks.CupProduct.exists_liftCycles_homologyπ_eq
    ((cech O W hW).obj S.X₂.obj) n (n + 1) (CochainComplex.next ℤ n) (toMor y)
  have hwc' : cocycleClass n w hw = toMor y := hwc
  refine ⟨J, W, hW, w, hw, ?_⟩
  rw [hwc', ← Category.assoc, toMor_comp, hy, toMor_comp, hb₂, toMor_apply]

/-- **A class of `Hⁿ(X, K₃)` is represented by a lift to `K₂` with coboundary in `K₁`.**  Let
`0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` be a short exact sequence of bounded below complexes of `𝒪_X`-modules
for which Čech cohomology computes the cohomology of `K₁` and of `K₂`.  For every class
`a ∈ Hⁿ(X, K₃)` there are an open covering `𝒰`, a cochain `α₂` of `Tot(Č(𝒰, K₂))` of degree `n`
whose image `ᾱ₂` in `Tot(Č(𝒰, K₃))` is a cocycle with class `a`, and a cocycle `α₁` of
`Tot(Č(𝒰, K₁))` whose image in `Tot(Č(𝒰, K₂))` is `d(α₂)`. -/
theorem exists_cechLift
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n : ℤ) (h₁ : CechComputes O S.X₁) (h₂ : CechComputes O S.X₂)
    (a : unitModule _ ⟶ hypercohomology O S.X₃ n) :
    ∃ (I : Type u) (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
      (α₂ : unitModule _ ⟶ ((cech O U hU).obj S.X₂.obj).X n)
      (α₁ : unitModule _ ⟶ ((cech O U hU).obj S.X₁.obj).X (n + 1))
      (hα₃ : (α₂ ≫ ((cech O U hU).map S.g.hom).f n) ≫
        ((cech O U hU).obj S.X₃.obj).d n (n + 1) = 0)
      (_ : α₁ ≫ ((cech O U hU).obj S.X₁.obj).d (n + 1) (n + 1 + 1) = 0),
      α₁ ≫ ((cech O U hU).map S.f.hom).f (n + 1) =
          α₂ ≫ ((cech O U hU).obj S.X₂.obj).d n (n + 1) ∧
        cocycleClass n _ hα₃ ≫ cechClass O U hU S.X₃ n = a := by
  obtain ⟨J, V, hV, σ, α₁, hα₁c, hα₁σ, hb⟩ := exists_cechCocycle_boundary O S hS n h₁ h₂ a
  have hpσ := comp_map_g_f_d_eq_zero O S V hV hα₁σ
  obtain ⟨J', W, hW, w, hw, hb₂c⟩ := exists_cechCocycle_of_boundary_eq_zero O S hS n h₂
    (a - cocycleClass n _ hpσ ≫ cechClass O V hV S.X₃ n) (by
      rw [Preadditive.sub_comp, Category.assoc,
        ← cechClass_boundary O V hV S hS n σ α₁ hpσ hα₁c hα₁σ, hb, sub_self])
  let Z : J × J' → Opens X := fun jj => V jj.1 ⊓ W jj.2
  have hZ : ⊤ = ⨆ jj, Z jj := iSup_inf_eq_top V hV W hW
  let ρV := Stacks.Cech.Refinement.cechRefinement O V hV Z hZ Prod.fst (fun jj => inf_le_left)
  let ρW := Stacks.Cech.Refinement.cechRefinement O W hW Z hZ Prod.snd (fun jj => inf_le_right)
  have h3 : (α₁ ≫ (ρV.app S.X₁.obj).f (n + 1)) ≫ ((cech O Z hZ).map S.f.hom).f (n + 1) =
      (σ ≫ (ρV.app S.X₂.obj).f n + w ≫ (ρW.app S.X₂.obj).f n) ≫
        ((cech O Z hZ).obj S.X₂.obj).d n (n + 1) := by
    rw [← map_f_comp_app_f ρV S.f.hom, hα₁σ, Preadditive.add_comp, Category.assoc, Category.assoc,
      (ρV.app S.X₂.obj).comm, Category.assoc, (ρW.app S.X₂.obj).comm, ← Category.assoc w, hw,
      zero_comp, add_zero]
  have h1 := comp_map_g_f_d_eq_zero O S Z hZ h3
  refine ⟨J × J', Z, hZ, σ ≫ (ρV.app S.X₂.obj).f n + w ≫ (ρW.app S.X₂.obj).f n,
    α₁ ≫ (ρV.app S.X₁.obj).f (n + 1), h1, comp_f_d_eq_zero _ hα₁c, h3, ?_⟩
  have hwG := comp_f_d_eq_zero ((cech O W hW).map S.g.hom) hw
  have e₁ := comp_f_d_eq_zero (ρV.app S.X₃.obj) hpσ
  have e₂ := comp_f_d_eq_zero (ρW.app S.X₃.obj) hwG
  have hsum : (σ ≫ (ρV.app S.X₂.obj).f n + w ≫ (ρW.app S.X₂.obj).f n) ≫
      ((cech O Z hZ).map S.g.hom).f n =
      (σ ≫ ((cech O V hV).map S.g.hom).f n) ≫ (ρV.app S.X₃.obj).f n +
        (w ≫ ((cech O W hW).map S.g.hom).f n) ≫ (ρW.app S.X₃.obj).f n := by
    rw [Preadditive.add_comp, map_f_comp_app_f ρV S.g.hom, map_f_comp_app_f ρW S.g.hom,
      Category.assoc, Category.assoc]
  rw [cocycleClass_congr n hsum h1 (by rw [Preadditive.add_comp, e₁, e₂, add_zero]),
    cocycleClass_add n _ _ e₁ e₂, Preadditive.add_comp,
    ← cocycleClass_comp_homologyMap (ρV.app S.X₃.obj) n _ hpσ,
    ← cocycleClass_comp_homologyMap (ρW.app S.X₃.obj) n _ hwG, Category.assoc, Category.assoc,
    cechClass_refinement, cechClass_refinement,
    ← cocycleClass_comp_homologyMap ((cech O W hW).map S.g.hom) n w hw, Category.assoc,
    cechClass_naturality, hb₂c, add_sub_cancel]

/-- **Čech cohomology computes the cohomology of a bounded below complex of flasque modules.**
For such a complex the comparison `Tot(Č(𝒰, K)) ⟶ RΓ(X, K)` is an isomorphism for every open
covering, by [Stacks, Tag 0FKV]'s identification `Γ(X, K) = Tot(Č(𝒰, K)) = RΓ(X, K)`. -/
theorem cechComputes_of_isFlasque (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (hK : ∀ n : ℤ, (Stacks.Cohomology.CechSheaf.abSheaf (K.1.X n)).IsFlasque) :
    CechComputes O K := by
  have hiso : ∀ {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) (n : ℤ),
      IsIso (cechClass O U hU K n) := by
    intro I U hU n
    have := Stacks.Cech.Linear.isIso_totalCechToDerivedSections_app_of_isFlasque X (ringSheaf O)
      ⊤ U hU K hK
    have : IsIso ((DerivedCategory.homologyFunctor _ n).map
        ((Stacks.Cech.Linear.totalCechToDerivedSections X (ringSheaf O) ⊤ U hU).app K)) :=
      Functor.map_isIso _ _
    exact IsIso.comp_isIso'
      (Iso.isIso_hom ((DerivedCategory.homologyFunctorFactors _ n).app _).symm) this
  have hU₀ : (⊤ : Opens X) = ⨆ _ : PUnit.{u + 1}, (⊤ : Opens X) := by simp
  refine fun n => ⟨fun a => ⟨PUnit, fun _ => ⊤, hU₀, inv (cechClass O _ hU₀ K n) a, ?_⟩,
    fun I U hU z hz => ⟨I, U, hU, id, fun _ => le_rfl, ?_⟩⟩
  · rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
  · have := hiso U hU n
    have hz0 : z = 0 := by
      rw [← ConcreteCategory.id_apply (X := ((cech O U hU).obj K.obj).homology n) z,
        ← IsIso.hom_inv_id (cechClass O U hU K n), ConcreteCategory.comp_apply, hz, map_zero]
    rw [hz0, map_zero]

end Stacks.Cech.Hypercohomology
