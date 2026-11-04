module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InverseSystems.AdicQuotientSystems.MittagLeffler
import StacksCore.Tactic.StacksAttribute

/-!
# The limit topology on the cohomology

Stacks 0GYS: the ascending chain condition on `⨁ₙ Hᵖ(C, IⁿFₙ)` makes the limit topology on
`lim Hᵖ(C, Fₙ)` the `I`-adic topology.

Part of `StacksFrontier.CategoryTheory.Sites.Cohomology.InverseSystems.AdicQuotientSystems`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative
open scoped DirectSum

attribute [local instance] HasDerivedCategory.standard

universe u v r w

namespace Stacks.Cohomology.AdicInverseSystems

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{r}) [∀ X : Cᵒᵖ, IsMulCommutative (O.obj.obj X)]

section AdicSystem

variable (I : Ideal ↥(GlobalSectionRing O)) (F : ℕᵒᵖ ⥤ SheafOfModules.{max u v r w} O)

variable {O I F}

/-! ### The limit topology on the cohomology of an adic quotient system -/

section AdicTopology

/-- Multiplication by an element of `I^(n+1)` on `Fₙ₊₁` followed by the transition map `Fₙ₊₁ ⟶ Fₙ`
is zero. -/
theorem IsAdicQuotientSystem.globalSmul_comp_towerMap_succ (hF : IsAdicQuotientSystem O I F)
    (n : ℕ) {a : ↥(GlobalSectionRing O)} (ha : a ∈ I ^ (n + 1)) :
    globalSmul O a (F.obj (op (n + 1))) ≫ towerMap F (Nat.le_succ n) = 0 := by
  rw [← idealSmulFactor_comp_ι O (I ^ (n + 1)) (F.obj (op (n + 1))) ha, Category.assoc,
    hF.idealSmulι_comp_towerMap_succ n, comp_zero]

variable (O I F)

/-- The inverse system `n ↦ Hᵖ(C, Fₙ)` of cohomology modules of the tower. -/
abbrev cohomologySystem (p : ℕ) : ℕᵒᵖ ⥤ ModuleCat.{max u v r w} ↥(GlobalSectionRing O) :=
  F ⋙ globalModuleCohomology.{u, v, r, w} O p

/-- The transition maps of the inverse system `n ↦ Hᵖ(C, Fₙ)`. -/
def cohomologyTransition (p n : ℕ) :
    (cohomologySystem O F p).obj (op (n + 1)) →ₗ[↥(GlobalSectionRing O)]
      (cohomologySystem O F p).obj (op n) :=
  ((globalModuleCohomology.{u, v, r, w} O p).map (towerMap F (Nat.le_succ n))).hom

/-- The inverse limit `lim Hᵖ(C, Fₙ)`, as a submodule of the product. -/
abbrev cohomologyLimit (p : ℕ) :=
  Stacks.AdicLimit.towerLimit (fun n => ((cohomologySystem O F p).obj (op n) : Type _))
    (cohomologyTransition O F p)

/-- Cohomology turns multiplication by a global section `a` on a sheaf of modules into
multiplication by `a`. -/
theorem map_globalSmul (p : ℕ) (a : ↥(GlobalSectionRing O))
    (M : SheafOfModules.{max u v r w} O) :
    (globalModuleCohomology.{u, v, r, w} O p).map (globalSmul O a M) = a • 𝟙 _ := by
  rw [globalSmul_eq_smul_id, Functor.map_smul, CategoryTheory.Functor.map_id]

/-- Cohomology turns multiplication by a global section `a` on a sheaf of modules into
multiplication by `a`, elementwise. -/
theorem map_globalSmul_apply (p : ℕ) (a : ↥(GlobalSectionRing O))
    (M : SheafOfModules.{max u v r w} O)
    (x : (globalModuleCohomology.{u, v, r, w} O p).obj M) :
    ((globalModuleCohomology.{u, v, r, w} O p).map (globalSmul O a M)).hom x = a • x := by
  rw [map_globalSmul]
  rfl

/-- Cohomology of a composite, elementwise. -/
private theorem cohomology_map_comp_apply (O : Sheaf J RingCat.{r})
    [∀ X : Cᵒᵖ, IsMulCommutative (O.obj.obj X)] (p : ℕ) {M N P : SheafOfModules.{max u v r w} O}
    (f : M ⟶ N) (g : N ⟶ P) (x : (globalModuleCohomology.{u, v, r, w} O p).obj M) :
    ((globalModuleCohomology.{u, v, r, w} O p).map g).hom
        (((globalModuleCohomology.{u, v, r, w} O p).map f).hom x) =
      ((globalModuleCohomology.{u, v, r, w} O p).map (f ≫ g)).hom x := by
  rw [Functor.map_comp]
  rfl

/-- The transition `Hᵖ(C, Fₙ₊₁) → Hᵖ(C, Fₙ)` is killed by `I^(n+1)`. -/
theorem pow_smul_le_ker_cohomologyTransition (hF : IsAdicQuotientSystem O I F) (p n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule ↥(GlobalSectionRing O)
        ((cohomologySystem O F p).obj (op (n + 1)))) ≤
      LinearMap.ker (cohomologyTransition O F p n) := by
  refine Submodule.smul_le.mpr ?_
  intro a ha x _
  refine LinearMap.mem_ker.mpr ?_
  have h := cohomology_map_comp_apply O p (globalSmul O a (F.obj (op (n + 1))))
    (towerMap F (Nat.le_succ n)) x
  rw [hF.globalSmul_comp_towerMap_succ n ha, Functor.map_zero, map_globalSmul_apply] at h
  exact h

/-- The subsheaf `IⁿF_m` of a later term of the tower, mapped into `IⁿFₙ`. -/
abbrev gradedPieceMap {n m : ℕ} (h : n ≤ m) :
    idealSmul O (I ^ n) (F.obj (op m)) ⟶ gradedPiece O I F n :=
  idealSmulMap O (I ^ n) (F.obj (op m)) (towerMap F h)

/-- The stable image in `Hᵖ(C, IⁿFₙ)`: the classes coming from `Hᵖ(C, IⁿF_m)` for every
`m ≥ n`. -/
def stableImage (p n : ℕ) :
    Submodule ↥(GlobalSectionRing O)
      ((globalModuleCohomology.{u, v, r, w} O p).obj (gradedPiece O I F n)) :=
  ⨅ (m : ℕ) (h : n ≤ m), LinearMap.range
    ((globalModuleCohomology.{u, v, r, w} O p).map (gradedPieceMap O I F h)).hom

/-- Multiplying an element of `Iⁿ` by one of `Iᵐ` lands in `I^(n+m)`. -/
theorem pow_mul_mem_pow_add (n m : ℕ) (a : ↥(I ^ m)) : ∀ b ∈ I ^ n, b * a.1 ∈ I ^ (n + m) := by
  intro b hb
  rw [pow_add]
  exact Ideal.mul_mem_mul hb a.2

/-- The graded action is the descent of multiplication by `a ∈ Iᵐ` along the quotient. -/
theorem gradedPieceMap_comp_act (hF : IsAdicQuotientSystem O I F) (m n : ℕ) (a : ↥(I ^ m)) :
    gradedPieceMap O I F (Nat.le_add_right n m) ≫ act hF m n a =
      idealSmulScalarMap O (I ^ n) (F.obj (op (n + m))) (I ^ (n + m))
        (pow_mul_mem_pow_add O I n m a) := by
  apply (cancel_mono (idealSmulι O (I ^ (n + m)) (F.obj (op (n + m))))).1
  rw [Category.assoc, act_comp_ι, idealSmulMap_comp_ι_assoc, towerMap_comp_mulLift,
    idealSmulScalarMap_comp_ι]

/-- The stable image is closed under the canonical graded action. -/
theorem map_act_mem_stableImage (hF : IsAdicQuotientSystem O I F) (p m n : ℕ) (a : ↥(I ^ m))
    (s : (globalModuleCohomology.{u, v, r, w} O p).obj (gradedPiece O I F n))
    (hs : s ∈ stableImage O I F p n) :
    ((globalModuleCohomology.{u, v, r, w} O p).map (act hF m n a)).hom s ∈
      stableImage O I F p (n + m) := by
  refine (Submodule.mem_iInf _).mpr fun j => (Submodule.mem_iInf _).mpr fun hj => ?_
  have hnj : n ≤ j := le_trans (Nat.le_add_right n m) hj
  obtain ⟨z, hz⟩ := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hs j) hnj
  refine ⟨((globalModuleCohomology.{u, v, r, w} O p).map
    (idealSmulScalarMap O (I ^ n) (F.obj (op j)) (I ^ (n + m))
      (pow_mul_mem_pow_add O I n m a))).hom z, ?_⟩
  have hmor : idealSmulScalarMap O (I ^ n) (F.obj (op j)) (I ^ (n + m))
        (pow_mul_mem_pow_add O I n m a) ≫ gradedPieceMap O I F hj =
      gradedPieceMap O I F hnj ≫ act hF m n a := by
    rw [idealSmulScalarMap_naturality, ← gradedPieceMap_comp_act O I F hF m n a,
      ← Category.assoc]
    congr 1
    rw [idealSmulMap_comp, towerMap_comp]
  rw [cohomology_map_comp_apply, hmor, ← cohomology_map_comp_apply, hz]


/-- The stable image is closed under the canonical graded action, with the degree written as a
given sum. -/
theorem map_actTo_mem_stableImage (hF : IsAdicQuotientSystem O I F) (p m n k : ℕ)
    (h : n + m = k) (a : ↥(I ^ m))
    (s : (globalModuleCohomology.{u, v, r, w} O p).obj (gradedPiece O I F n))
    (hs : s ∈ stableImage O I F p n) :
    ((globalModuleCohomology.{u, v, r, w} O p).map (actTo hF m n k h a)).hom s ∈
      stableImage O I F p k := by
  subst k
  simpa only [actTo, eqToHom_refl, Category.comp_id] using
    map_act_mem_stableImage O I F hF p m n a s hs

/-- A coordinate of an element of the inverse limit is the image of any later coordinate. -/
theorem cohomologyLimit_coord (p : ℕ) (x : cohomologyLimit O F p) {n m : ℕ} (h : n ≤ m) :
    ((globalModuleCohomology.{u, v, r, w} O p).map (towerMap F h)).hom (x.1 m) = x.1 n := by
  induction m, h using Nat.le_induction with
  | base =>
    have hid : towerMap F (le_refl n) = 𝟙 (F.obj (op n)) := by
      rw [← F.map_id]
      rfl
    rw [hid, CategoryTheory.Functor.map_id]
    rfl
  | succ m h ih =>
    have he : towerMap F (h.trans (Nat.le_succ m)) =
        towerMap F (Nat.le_succ m) ≫ towerMap F h := (towerMap_comp F h (Nat.le_succ m)).symm
    rw [he, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [show ((globalModuleCohomology.{u, v, r, w} O p).map
        (towerMap F (Nat.le_succ m))).hom (x.1 (m + 1)) = x.1 m from x.2 m]
    exact ih

/-- Composing the lift of multiplication by `a ∈ Iᵐ` with the transition map gives
multiplication by `a`. -/
theorem map_mulLift_map_towerMap (hF : IsAdicQuotientSystem O I F) (p m n : ℕ) (a : ↥(I ^ m))
    (z : (globalModuleCohomology.{u, v, r, w} O p).obj (F.obj (op (n + m)))) :
    ((globalModuleCohomology.{u, v, r, w} O p).map (mulLift hF m n a)).hom
        (((globalModuleCohomology.{u, v, r, w} O p).map
          (towerMap F (Nat.le_add_right n m))).hom z) = a.1 • z := by
  rw [cohomology_map_comp_apply, towerMap_comp_mulLift, map_globalSmul_apply]

/-- On the inverse limit, the lift of multiplication by `a ∈ Iᵐ` sends the coordinate at `n` to
`a` times the coordinate at `n + m`. -/
theorem map_mulLift_coord (hF : IsAdicQuotientSystem O I F) (p m n : ℕ) (a : ↥(I ^ m))
    (x : cohomologyLimit O F p) :
    ((globalModuleCohomology.{u, v, r, w} O p).map (mulLift hF m n a)).hom (x.1 n) =
      a.1 • x.1 (n + m) := by
  rw [← cohomologyLimit_coord O F p x (Nat.le_add_right n m),
    map_mulLift_map_towerMap O I F hF p m n a]

/-- Stacks 0GYS's compatibility: on a class of the stable image lifting a coordinate of the
inverse limit, the canonical action by `a ∈ Iᵐ` lifts `a` times the later coordinate. -/
theorem ι_map_act_eq_smul_coord (hF : IsAdicQuotientSystem O I F) (p m n : ℕ) (a : ↥(I ^ m))
    (s : (globalModuleCohomology.{u, v, r, w} O p).obj (gradedPiece O I F n))
    (hsStable : s ∈ stableImage O I F p n) (x : cohomologyLimit O F p)
    (hs : ((globalModuleCohomology.{u, v, r, w} O p).map
      (idealSmulι O (I ^ n) (F.obj (op n)))).hom s = x.1 n) :
    ((globalModuleCohomology.{u, v, r, w} O p).map
        (idealSmulι O (I ^ (n + m)) (F.obj (op (n + m))))).hom
      (((globalModuleCohomology.{u, v, r, w} O p).map (act hF m n a)).hom s) =
      a.1 • x.1 (n + m) := by
  obtain ⟨z, hz⟩ := (Submodule.mem_iInf _).mp
    ((Submodule.mem_iInf _).mp hsStable (n + m)) (Nat.le_add_right n m)
  have hcompat : ((globalModuleCohomology.{u, v, r, w} O p).map
      (towerMap F (Nat.le_add_right n m))).hom
        (((globalModuleCohomology.{u, v, r, w} O p).map
          (idealSmulι O (I ^ n) (F.obj (op (n + m))))).hom z) = x.1 n := by
    rw [cohomology_map_comp_apply, ← idealSmulMap_comp_ι, ← cohomology_map_comp_apply, hz, hs]
  rw [← hz, cohomology_map_comp_apply, cohomology_map_comp_apply, ← Category.assoc,
    gradedPieceMap_comp_act O I F hF m n a, idealSmulScalarMap_comp_ι,
    ← cohomology_map_comp_apply, map_globalSmul_apply,
    ← map_mulLift_map_towerMap O I F hF p m n a, hcompat, map_mulLift_coord O I F hF p m n a]

/-- The homogeneous piece `Hᵖ(C, IⁿFₙ)` of the graded module of Stacks 0GYS. -/
abbrev gradedCohomology (p n : ℕ) : Type (max u v r w) :=
  ((globalModuleCohomology.{u, v, r, w} O p).obj (gradedPiece O I F n) : Type _)

/-- The graded module `⨁ₙ Hᵖ(C, IⁿFₙ)` of Stacks 0GYS. -/
abbrev CohomologySum (p : ℕ) := ⨁ n, gradedCohomology O I F p n

/-- The canonical graded action on `⨁ₙ Hᵖ(C, IⁿFₙ)`: a homogeneous scalar of degree `m` acts
through the canonical degree-raising map on the ideal-power subsheaves. -/
def IsCanonicalAction (hF : IsAdicQuotientSystem O I F) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (CohomologySum O I F p)] : Prop :=
  ∀ (m n : ℕ) (a : ↥(I ^ m))
    (x : (globalModuleCohomology.{u, v, r, w} O p).obj (gradedPiece O I F n)),
    AssociatedGraded.classOfPow I m a •
        DirectSum.of (gradedCohomology O I F p) n x =
      DirectSum.of (gradedCohomology O I F p) (m + n)
        (((globalModuleCohomology.{u, v, r, w} O p).map
          (actTo hF m n (m + n) (by omega) a)).hom x)

/-- Stacks 0GYS's hypothesis: `⨁ₙ Hᵖ(C, IⁿFₙ)` satisfies the ascending chain condition as a
graded module over `⨁ₙ Iⁿ/Iⁿ⁺¹`, for the canonical graded action. -/
def HasGradedACC (hF : IsAdicQuotientSystem O I F) (p : ℕ) : Prop :=
  ∃ action : Module (AssociatedGraded.gradedRing I) (CohomologySum O I F p),
    letI := action
    IsCanonicalAction O I F hF p ∧
      IsNoetherian (AssociatedGraded.gradedRing I) (CohomologySum O I F p)


/-- For a canonical action, the class of `a ∈ Iᵐ` acts on the degree `n` component `x` by `actTo`
into degree `k = m + n`. -/
theorem isCanonicalAction_of_eq (hF : IsAdicQuotientSystem O I F) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (CohomologySum O I F p)]
    (hc : IsCanonicalAction O I F hF p) (m n k : ℕ) (h : m + n = k) (a : ↥(I ^ m))
    (x : (globalModuleCohomology.{u, v, r, w} O p).obj (gradedPiece O I F n)) :
    AssociatedGraded.classOfPow I m a •
        DirectSum.of (gradedCohomology O I F p) n x =
      DirectSum.of (gradedCohomology O I F p) k
        (((globalModuleCohomology.{u, v, r, w} O p).map
          (actTo hF m n k (by omega) a)).hom x) := by
  subst k
  exact hc m n a x

/-- If a stable class `s` of `Hᵖ(C, IⁿFₙ)` maps to the `n`-th coordinate of an element `x` of the
inverse limit, then its image under the action of `a ∈ Iᵐ` maps to `a • x` at coordinate
`k = n + m`. -/
theorem ι_map_actTo_eq_smul_coord (hF : IsAdicQuotientSystem O I F) (p m n k : ℕ)
    (h : n + m = k) (a : ↥(I ^ m))
    (s : (globalModuleCohomology.{u, v, r, w} O p).obj (gradedPiece O I F n))
    (hsStable : s ∈ stableImage O I F p n) (x : cohomologyLimit O F p)
    (hs : ((globalModuleCohomology.{u, v, r, w} O p).map
      (idealSmulι O (I ^ n) (F.obj (op n)))).hom s = x.1 n) :
    ((globalModuleCohomology.{u, v, r, w} O p).map
        (idealSmulι O (I ^ k) (F.obj (op k)))).hom
      (((globalModuleCohomology.{u, v, r, w} O p).map (actTo hF m n k h a)).hom s) =
      a.1 • x.1 k := by
  subst k
  simpa only [actTo, eqToHom_refl, Category.comp_id] using
    ι_map_act_eq_smul_coord O I F hF p m n a s hsStable x hs

private theorem mem_range_of_exact_commutative_diagram
    {Rg K B B' D D' E : Type*} [CommRing Rg]
    [AddCommGroup K] [Module Rg K] [AddCommGroup B] [Module Rg B]
    [AddCommGroup B'] [Module Rg B'] [AddCommGroup D] [Module Rg D]
    [AddCommGroup D'] [Module Rg D'] [AddCommGroup E] [Module Rg E]
    (f : K →ₗ[Rg] B) (f' : K →ₗ[Rg] B') (b : B' →ₗ[Rg] B)
    (g : B →ₗ[Rg] D) (g' : B' →ₗ[Rg] D') (c : D' →ₗ[Rg] D) (h : D' →ₗ[Rg] E)
    (hex : LinearMap.range f = LinearMap.ker g)
    (hex' : LinearMap.range g' = LinearMap.ker h)
    (hf : b.comp f' = f) (hg : g.comp b = c.comp g')
    (s : B) (t : D') (ht : h t = 0) (hs : c t = g s) : s ∈ LinearMap.range b := by
  obtain ⟨z, hz⟩ : t ∈ LinearMap.range g' := by
    rw [hex']
    exact ht
  have hsz : s - b z ∈ LinearMap.range f := by
    rw [hex]
    show g (s - b z) = 0
    rw [map_sub, ← LinearMap.comp_apply, hg, LinearMap.comp_apply, hz, hs, sub_self]
  obtain ⟨y, hy⟩ := hsz
  exact ⟨f' y + z, by rw [map_add, ← LinearMap.comp_apply, hf, hy, sub_add_cancel]⟩

/-- A coordinate of the inverse limit that dies one step earlier lifts to a class of the stable
image of `Hᵖ(C, I^(n+1)Fₙ₊₁)`. -/
theorem exists_stable_lift (hF : IsAdicQuotientSystem O I F) (p n : ℕ)
    (x : cohomologyLimit O F p) (hx : x.1 n = 0) :
    ∃ s : (globalModuleCohomology.{u, v, r, w} O p).obj (gradedPiece O I F (n + 1)),
      s ∈ stableImage O I F p (n + 1) ∧
      ((globalModuleCohomology.{u, v, r, w} O p).map
        (idealSmulι O (I ^ (n + 1)) (F.obj (op (n + 1))))).hom s = x.1 (n + 1) := by
  let S : ∀ (m : ℕ), n + 1 ≤ m → ShortComplex (SheafOfModules.{max u v r w} O) :=
    fun m hm => ShortComplex.mk (idealSmulι O (I ^ (n + 1)) (F.obj (op m)))
      (towerMap F (Nat.le_of_succ_le hm)) (hF.idealSmulι_comp_towerMap hm)
  have hS (m : ℕ) (hm : n + 1 ≤ m) : (S m hm).ShortExact := hF.shortExact hm
  have hex (m : ℕ) (hm : n + 1 ≤ m) :
      LinearMap.range ((globalModuleCohomology.{u, v, r, w} O p).map (S m hm).f).hom =
        LinearMap.ker ((globalModuleCohomology.{u, v, r, w} O p).map (S m hm).g).hom :=
    ((cohomologyDeltaFunctor.{u, v, r, w} O).exact_map (hS m hm) p).moduleCat_range_eq_ker
  have hzero (m : ℕ) (hm : n + 1 ≤ m) :
      ((globalModuleCohomology.{u, v, r, w} O p).map (S m hm).g).hom (x.1 m) = 0 :=
    (cohomologyLimit_coord O F p x (Nat.le_of_succ_le hm)).trans hx
  obtain ⟨s, hs⟩ : x.1 (n + 1) ∈
      LinearMap.range ((globalModuleCohomology.{u, v, r, w} O p).map
        (S (n + 1) le_rfl).f).hom := by
    rw [hex (n + 1) le_rfl]
    exact hzero (n + 1) le_rfl
  refine ⟨s, ?_, hs⟩
  refine (Submodule.mem_iInf _).mpr fun j => (Submodule.mem_iInf _).mpr fun hj => ?_
  let φ : S j hj ⟶ S (n + 1) le_rfl :=
    { τ₁ := gradedPieceMap O I F hj
      τ₂ := towerMap F hj
      τ₃ := 𝟙 _
      comm₁₂ := idealSmulMap_comp_ι O (I ^ (n + 1)) (F.obj (op j)) (towerMap F hj)
      comm₂₃ := by
        show towerMap F hj ≫ towerMap F (Nat.le_succ n) =
          towerMap F (Nat.le_of_succ_le hj) ≫ 𝟙 _
        rw [Category.comp_id, towerMap_comp] }
  have hcomm : (((globalModuleCohomology.{u, v, r, w} O p).map
          (S (n + 1) le_rfl).f).hom).comp
        (((globalModuleCohomology.{u, v, r, w} O p).map φ.τ₁).hom) =
      (((globalModuleCohomology.{u, v, r, w} O p).map φ.τ₂).hom).comp
        (((globalModuleCohomology.{u, v, r, w} O p).map (S j hj).f).hom) := by
    show ((globalModuleCohomology.{u, v, r, w} O p).map φ.τ₁ ≫
      (globalModuleCohomology.{u, v, r, w} O p).map (S (n + 1) le_rfl).f).hom = _
    rw [← Functor.map_comp, φ.comm₁₂, Functor.map_comp]
    rfl
  have hxmap : (((globalModuleCohomology.{u, v, r, w} O p).map φ.τ₂).hom) (x.1 j) =
      (((globalModuleCohomology.{u, v, r, w} O p).map (S (n + 1) le_rfl).f).hom) s := by
    rw [hs]
    exact cohomologyLimit_coord O F p x hj
  cases p with
  | zero =>
    obtain ⟨z, hz⟩ : x.1 j ∈ LinearMap.range
        ((globalModuleCohomology.{u, v, r, w} O 0).map (S j hj).f).hom := by
      rw [hex j hj]
      exact hzero j hj
    refine ⟨z, ?_⟩
    refine (ModuleCat.mono_iff_injective ((globalModuleCohomology.{u, v, r, w} O 0).map
      (S (n + 1) le_rfl).f)).mp
      ((cohomologyDeltaFunctor.{u, v, r, w} O).mono_map_f (hS (n + 1) le_rfl)) ?_
    show (((globalModuleCohomology.{u, v, r, w} O 0).map (S (n + 1) le_rfl).f).hom)
      ((((globalModuleCohomology.{u, v, r, w} O 0).map φ.τ₁).hom) z) =
        (((globalModuleCohomology.{u, v, r, w} O 0).map (S (n + 1) le_rfl).f).hom) s
    rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply, hz, hxmap]
  | succ q =>
    refine mem_range_of_exact_commutative_diagram
      ((cohomologyDeltaFunctor.{u, v, r, w} O).δ (hS (n + 1) le_rfl) q).hom
      ((cohomologyDeltaFunctor.{u, v, r, w} O).δ (hS j hj) q).hom
      (((globalModuleCohomology.{u, v, r, w} O (q + 1)).map φ.τ₁).hom)
      (((globalModuleCohomology.{u, v, r, w} O (q + 1)).map (S (n + 1) le_rfl).f).hom)
      (((globalModuleCohomology.{u, v, r, w} O (q + 1)).map (S j hj).f).hom)
      (((globalModuleCohomology.{u, v, r, w} O (q + 1)).map φ.τ₂).hom)
      (((globalModuleCohomology.{u, v, r, w} O (q + 1)).map (S j hj).g).hom)
      ((cohomologyDeltaFunctor.{u, v, r, w} O).exact_δ₂
        (hS (n + 1) le_rfl) q).moduleCat_range_eq_ker
      (hex j hj) ?_ hcomm s (x.1 j) (hzero j hj) hxmap
    have he := (cohomologyDeltaFunctor.{u, v, r, w} O).δ_naturality (hS j hj)
      (hS (n + 1) le_rfl) φ q
    have hid : φ.τ₃ = 𝟙 _ := rfl
    rw [hid, CategoryTheory.Functor.map_id, Category.id_comp] at he
    exact congrArg ModuleCat.Hom.hom he.symm


section Approximation

/-- The map `Hᵖ(C, IⁿFₙ) → Hᵖ(C, Fₙ)` induced by the inclusion of the ideal-power subsheaf. -/
def gradedIncl (p n : ℕ) : gradedCohomology O I F p n →ₗ[↥(GlobalSectionRing O)]
    (cohomologySystem O F p).obj (op n) :=
  ((globalModuleCohomology.{u, v, r, w} O p).map (idealSmulι O (I ^ n) (F.obj (op n)))).hom

/-- The projection from the inverse limit `lim Hᵖ(C, Fₙ)` to its `n`-th coordinate. -/
abbrev limitProj (p n : ℕ) : cohomologyLimit O F p →ₗ[↥(GlobalSectionRing O)]
    (cohomologySystem O F p).obj (op n) :=
  Stacks.AdicLimit.towerLimit.proj (fun j => ((cohomologySystem O F p).obj (op j) : Type _))
    (cohomologyTransition O F p) n

/-- Stacks 0GYS's graded submodule `⨁ₙ Eₙ`, degreewise: the classes of the stable image of
`Hᵖ(C, IⁿFₙ)` that lift a coordinate of the inverse limit vanishing one step earlier. -/
def liftingSubgroup (p : ℕ) : ∀ n, AddSubgroup (gradedCohomology O I F p n)
  | 0 => ⊥
  | n + 1 => (stableImage O I F p (n + 1)).toAddSubgroup ⊓
      (((LinearMap.ker (limitProj O F p n)).map (limitProj O F p (n + 1))).comap
        (gradedIncl O I F p (n + 1))).toAddSubgroup

/-- A class of `Hᵖ(C, I^(n+1)Fₙ₊₁)` lies in `liftingSubgroup` if and only if it is stable and its
image in `Hᵖ(C, Fₙ₊₁)` is the coordinate of an element of the inverse limit whose `n`-th coordinate
vanishes. -/
theorem mem_liftingSubgroup_succ_iff (p n : ℕ) (s : gradedCohomology O I F p (n + 1)) :
    s ∈ liftingSubgroup O I F p (n + 1) ↔
      s ∈ stableImage O I F p (n + 1) ∧
        ∃ x : cohomologyLimit O F p, x.1 n = 0 ∧
          gradedIncl O I F p (n + 1) s = x.1 (n + 1) := by
  show s ∈ stableImage O I F p (n + 1) ∧
    (∃ x : cohomologyLimit O F p, x ∈ (limitProj O F p n).ker ∧
      limitProj O F p (n + 1) x = gradedIncl O I F p (n + 1) s) ↔ _
  exact and_congr_right fun _ => exists_congr fun x => and_congr_right fun _ => eq_comm

/-- For a canonical action, the class of `a ∈ Iᵏ` sends the degree `n` component to a single
component of degree `k + n`. -/
theorem exists_classOfPow_smul_eq (hF : IsAdicQuotientSystem O I F) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (CohomologySum O I F p)]
    (hcanonical : IsCanonicalAction O I F hF p) (k : ℕ) (a : ↥(I ^ k)) (n : ℕ)
    (x : gradedCohomology O I F p n) :
    ∃ y : gradedCohomology O I F p (k + n),
      AssociatedGraded.classOfPow I k a • DirectSum.of (gradedCohomology O I F p) n x =
        DirectSum.of (gradedCohomology O I F p) (k + n) y :=
  ⟨_, hcanonical k n a x⟩

/-- For a canonical action, `liftingSubgroup` is closed under the action of the classes of elements
of `Iᵏ`. -/
theorem liftingSubgroup_classOfPow_smul (hF : IsAdicQuotientSystem O I F) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (CohomologySum O I F p)]
    (hcanonical : IsCanonicalAction O I F hF p) (k : ℕ) (a : ↥(I ^ k)) (n : ℕ)
    (s : gradedCohomology O I F p n) (hs : s ∈ liftingSubgroup O I F p n) :
    ∃ t : gradedCohomology O I F p (k + n), t ∈ liftingSubgroup O I F p (k + n) ∧
      AssociatedGraded.classOfPow I k a • DirectSum.of (gradedCohomology O I F p) n s =
        DirectSum.of (gradedCohomology O I F p) (k + n) t := by
  cases n with
  | zero =>
    have hs0 : s = 0 := by
      simpa only [liftingSubgroup, AddSubgroup.mem_bot] using hs
    subst s
    exact ⟨0, (liftingSubgroup O I F p k).zero_mem, by simp⟩
  | succ n =>
    obtain ⟨hsStable, xl, hxl, hsx⟩ := (mem_liftingSubgroup_succ_iff O I F p n s).mp hs
    refine ⟨_, ?_, isCanonicalAction_of_eq O I F hF p hcanonical k (n + 1) (k + (n + 1))
      (by omega) a s⟩
    refine (mem_liftingSubgroup_succ_iff O I F p (k + n) _).mpr ⟨?_, a.1 • xl, ?_, ?_⟩
    · exact map_actTo_mem_stableImage O I F hF p k (n + 1) (k + (n + 1)) (by omega) a s hsStable
    · have hzero : a.1 • xl.1 (n + k) = 0 := by
        rw [← map_mulLift_coord O I F hF p k n a xl, hxl, map_zero]
      show a.1 • xl.1 (k + n) = 0
      rw [Nat.add_comm k n]
      exact hzero
    · exact ι_map_actTo_eq_smul_coord O I F hF p k (n + 1) (k + (n + 1)) (by omega) a s
        hsStable xl hsx

/-- Stacks 0GYS's successive approximation: one finite family of elements of `I` such that above
a uniform degree every element of `Ker(M → Hᵖ(C, Fₙ₊₁))` is a combination of elements of
`Ker(M → Hᵖ(C, Fₙ))`, modulo `Ker(M → Hᵖ(C, Fₙ₊₂))`. -/
theorem exists_approx (hF : IsAdicQuotientSystem O I F) (p : ℕ)
    (hACC : HasGradedACC O I F hF p) :
    ∃ (t : ℕ) (a : Fin t → ↥(GlobalSectionRing O)) (c : ℕ), (∀ i, a i ∈ I) ∧
      ∀ n, c ≤ n → ∀ x : cohomologyLimit O F p, x.1 (n + 1) = 0 →
        ∃ y : Fin t → cohomologyLimit O F p,
          (∀ i, (y i).1 n = 0) ∧ (x - ∑ i, a i • y i).1 (n + 2) = 0 := by
  classical
  obtain ⟨action, hcanonical, hnoeth⟩ := hACC
  let := action
  let : IsNoetherian (AssociatedGraded.gradedRing I) (CohomologySum O I F p) := hnoeth
  have hgraded := exists_classOfPow_smul_eq O I F hF p hcanonical
  have hP := liftingSubgroup_classOfPow_smul O I F hF p hcanonical
  let E := AssociatedGraded.homogeneousSubmodule I (liftingSubgroup O I F p) hP
  have hhom : ∀ n x, x ∈ E →
      AssociatedGraded.homogeneousPart (gradedCohomology O I F p) n x ∈ E := fun n x hx =>
    (AssociatedGraded.of_mem_homogeneousSubmodule_iff I (liftingSubgroup O I F p) hP n
      (x n)).mpr
      ((AssociatedGraded.mem_homogeneousSubmodule I (liftingSubgroup O I F p) hP x).mp hx n)
  obtain ⟨sg, ag, c, hc⟩ :=
    AssociatedGraded.exists_eventual_degree_one_generators I hgraded E hhom
  let e := Fintype.equivFin sg
  refine ⟨Fintype.card sg, fun i => (ag (e.symm i)).1, c, ?_, ?_⟩
  · intro i
    simpa only [pow_one] using (ag (e.symm i)).2
  · intro n hn x hx
    obtain ⟨tt, htStable, ht⟩ := exists_stable_lift O I F hF p (n + 1) x hx
    have htE : DirectSum.of (gradedCohomology O I F p) (n + 2) tt ∈ E :=
      (AssociatedGraded.of_mem_homogeneousSubmodule_iff I (liftingSubgroup O I F p) hP
        (n + 2) tt).mpr
        ((mem_liftingSubgroup_succ_iff O I F p (n + 1) tt).mpr ⟨htStable, x, hx, ht⟩)
    obtain ⟨z, hz, htz⟩ := hc (n + 1) (by omega) tt htE
    have hzx (i : sg) : ∃ yl : cohomologyLimit O F p,
        yl.1 n = 0 ∧ gradedIncl O I F p (n + 1) (z i) = yl.1 (n + 1) := by
      obtain ⟨-, yl, hyl, hzy⟩ := (mem_liftingSubgroup_succ_iff O I F p n (z i)).mp
        ((AssociatedGraded.of_mem_homogeneousSubmodule_iff I (liftingSubgroup O I F p)
          hP _ _).mp (hz i))
      exact ⟨yl, hyl, hzy⟩
    choose yl hyl hzy using hzx
    refine ⟨fun i => yl (e.symm i), fun i => hyl (e.symm i), ?_⟩
    have heval (i : sg) :
        gradedIncl O I F p (n + 2) ((AssociatedGraded.classOfPow I 1 (ag i) •
          DirectSum.of (gradedCohomology O I F p) (n + 1) (z i)) (n + 2)) =
            (ag i).1 • (yl i).1 (n + 2) := by
      have hzi := (mem_liftingSubgroup_succ_iff O I F p n (z i)).mp
        ((AssociatedGraded.of_mem_homogeneousSubmodule_iff I (liftingSubgroup O I F p)
          hP _ _).mp (hz i))
      rw [isCanonicalAction_of_eq O I F hF p hcanonical 1 (n + 1) (n + 2) (by omega) (ag i) (z i),
        DirectSum.of_eq_same]
      exact ι_map_actTo_eq_smul_coord O I F hF p 1 (n + 1) (n + 2) (by omega) (ag i) (z i)
        hzi.1 (yl i) (hzy i)
    let ev : CohomologySum O I F p →ₗ[↥(GlobalSectionRing O)]
        (cohomologySystem O F p).obj (op (n + 2)) :=
      (gradedIncl O I F p (n + 2)).comp
        (DirectSum.component ↥(GlobalSectionRing O) ℕ (gradedCohomology O I F p) (n + 2))
    have hevt : ev (DirectSum.of (gradedCohomology O I F p) (n + 2) tt) =
        gradedIncl O I F p (n + 2) tt := by
      show gradedIncl O I F p (n + 2)
        (DirectSum.of (gradedCohomology O I F p) (n + 2) tt (n + 2)) = _
      rw [DirectSum.of_eq_same]
    have hsum := congrArg ev htz
    rw [map_sum, hevt] at hsum
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply]
    refine sub_eq_zero.mpr ?_
    rw [← ht]
    show gradedIncl O I F p (n + 2) tt = _
    rw [hsum]
    calc ∑ i : sg, ev (AssociatedGraded.classOfPow I 1 (ag i) •
            DirectSum.of (gradedCohomology O I F p) (n + 1) (z i))
        = ∑ i : sg, (ag i).1 • (yl i).1 (n + 2) := Finset.sum_congr rfl fun i _ => heval i
      _ = _ := (Equiv.sum_comp e.symm fun i : sg => (ag i).1 • (yl i).1 (n + 2)).symm

end Approximation

/-- **Stacks Project, Tag 0GYS.** For an inverse system of sheaves of modules on a site with
`Fₙ = Fₙ₊₁/IⁿFₙ₊₁`, the ascending chain condition on `⨁ₙ Hᵖ(C, IⁿFₙ₊₁)` as a graded
`⨁ₙ Iⁿ/Iⁿ⁺¹`-module implies that the limit topology on `lim Hᵖ(C, Fₙ)` is the `I`-adic
topology. -/
@[stacks 0GYS]
theorem limitTopology_eq_adicModuleTopology (hF : IsAdicQuotientSystem O I F) (p : ℕ)
    (hACC : HasGradedACC O I F hF p) :
    Stacks.AdicLimit.towerLimit.limitTopology
        (fun n => ((cohomologySystem O F p).obj (op n) : Type _))
        (cohomologyTransition O F p) =
      I.adicModuleTopology (cohomologyLimit O F p) := by
  obtain ⟨t, a, c, ha, happ⟩ := exists_approx O I F hF p hACC
  have happ' : ∀ n, c ≤ n → ∀ x : cohomologyLimit O F p,
      x ∈ LinearMap.ker (limitProj O F p (n + 1)) →
      ∃ y : Fin t → cohomologyLimit O F p,
        (∀ i, y i ∈ LinearMap.ker (limitProj O F p n)) ∧
        x - ∑ i, a i • y i ∈ LinearMap.ker (limitProj O F p (n + 2)) := by
    intro n hn x hx
    obtain ⟨y, hy, hxy⟩ := happ n hn x (LinearMap.mem_ker.mp hx)
    exact ⟨y, fun i => LinearMap.mem_ker.mpr (hy i), LinearMap.mem_ker.mpr hxy⟩
  rw [Stacks.AdicLimit.limitTopology_eq_iInf_induced_proj]
  refine Stacks.AdicLimit.iInf_induced_eq_adicModuleTopology I (fun n => limitProj O F p n)
    (fun i j hij => Stacks.AdicLimit.towerLimit_proj_ker_antitone _ i j hij) (fun n => ?_)
    (fun k => ?_)
  · exact ⟨n + 1, Stacks.AdicLimit.pow_smul_le_proj_ker _ I
      (fun j => pow_smul_le_ker_cohomologyTransition O I F hF p j) n⟩
  · exact ⟨c + k, Stacks.AdicLimit.proj_ker_le_pow_smul _ I a ha c happ' k⟩

end AdicTopology


end AdicSystem

end Stacks.Cohomology.AdicInverseSystems

end
