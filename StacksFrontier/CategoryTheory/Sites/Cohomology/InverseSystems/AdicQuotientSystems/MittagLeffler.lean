module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InverseSystems.AdicQuotientSystems.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Mittag-Leffler for the cohomology

Stacks 0GYQ: the ascending chain condition on the graded object `⨁ₙ H^(p+1)(C, IⁿFₙ)` makes the
inverse system `n ↦ Hᵖ(C, Fₙ)` Mittag-Leffler, with a shift uniform in the degree.

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

/-! ### Mittag-Leffler for the cohomology of an adic quotient system -/

section MittagLeffler

variable (hF : IsAdicQuotientSystem O I F) (p : ℕ)

/-- Multiplication by `a ∈ Iᵐ` as a map `Fₙ ⟶ F_k`, for a given `k = n + m`. -/
def mulTo (m n k : ℕ) (h : n + m = k) (a : ↥(I ^ m)) : F.obj (op n) ⟶ F.obj (op k) :=
  mulLift hF m n a ≫ eqToHom (by rw [h])

/-- The graded action of `a ∈ Iᵐ` as a map `IⁿFₙ ⟶ I^k F_k`, for a given `k = n + m`. -/
def actTo (m n k : ℕ) (h : n + m = k) (a : ↥(I ^ m)) :
    gradedPiece O I F n ⟶ gradedPiece O I F k :=
  act hF m n a ≫ eqToHom (by rw [h])

/-- The transition map `F_k ⟶ Fₙ` followed by `mulTo hF m n k h a` is multiplication by `a` on
`F_k`. -/
theorem towerMap_comp_mulTo (m n k : ℕ) (h : n + m = k) (a : ↥(I ^ m)) :
    towerMap F (show n ≤ k by omega) ≫ mulTo hF m n k h a =
      globalSmul O a.1 (F.obj (op k)) := by
  subst k
  simpa [mulTo] using towerMap_comp_mulLift hF m n a

/-- `actTo` commutes with the inclusions `IⁿFₙ ⟶ Fₙ` and `I^k F_k ⟶ F_k` and the map `mulTo`. -/
theorem actTo_comp_ι (m n k : ℕ) (h : n + m = k) (a : ↥(I ^ m)) :
    actTo hF m n k h a ≫ idealSmulι O (I ^ k) (F.obj (op k)) =
      idealSmulι O (I ^ n) (F.obj (op n)) ≫ mulTo hF m n k h a := by
  subst k
  simpa [actTo, mulTo] using act_comp_ι hF m n a

/-- `mulTo` is compatible with the transition maps: for `n ≤ n'`, the two ways from `Fₙ'` to `F_k`
agree. -/
theorem mulTo_naturality (m n k n' k' : ℕ) (h : n + m = k) (h' : n' + m = k')
    (hn : n ≤ n') (a : ↥(I ^ m)) :
    towerMap F hn ≫ mulTo hF m n k h a =
      mulTo hF m n' k' h' a ≫ towerMap F (show k ≤ k' by omega) := by
  have hepi := hF.epi_towerMap (show n' ≤ k' by omega)
  refine (cancel_epi (towerMap F (show n' ≤ k' by omega))).1 ?_
  have ht : towerMap F (show n' ≤ k' by omega) ≫ towerMap F hn =
      towerMap F (show k ≤ k' by omega) ≫ towerMap F (show n ≤ k by omega) := by
    rw [towerMap_comp, towerMap_comp]
  rw [← Category.assoc, ht, Category.assoc, towerMap_comp_mulTo, ← Category.assoc,
    towerMap_comp_mulTo, comp_globalSmul]

/-- For `i < m`, multiplication by `a ∈ Iᵐ` from `Fₙ` to `F_k` followed by the transition map
`F_k ⟶ Fᵢ` is zero. -/
theorem mulTo_comp_towerMap_eq_zero (m n k i : ℕ) (h : n + m = k) (hi : i < m)
    (a : ↥(I ^ m)) :
    mulTo hF m n k h a ≫ towerMap F (show i ≤ k by omega) = 0 := by
  have hepi := hF.epi_towerMap (show n ≤ k by omega)
  refine (cancel_epi (towerMap F (show n ≤ k by omega))).1 ?_
  rw [comp_zero, ← Category.assoc, towerMap_comp_mulTo, ← comp_globalSmul,
    hF.globalSmul_eq_zero i (Ideal.pow_le_pow_right (show i + 1 ≤ m by omega) a.2), comp_zero]

/-- The short exact sequence `0 → I^(n+1)Fₙ₊₁ → Fₙ₊₁ → Fₙ → 0` at stage `n`. -/
def adicShortComplex (n : ℕ) : ShortComplex (SheafOfModules.{max u v r w} O) :=
  ShortComplex.mk (idealSmulι O (I ^ (n + 1)) (F.obj (op (n + 1))))
    (towerMap F (Nat.le_succ n)) (hF.idealSmulι_comp_towerMap_succ n)

/-- The sequence `adicShortComplex hF n` is short exact. -/
theorem adicShortComplex_shortExact (n : ℕ) : (adicShortComplex hF n).ShortExact :=
  hF.shortExact_succ n

/-- The boundary map `Hᵖ(C, Fₙ) ⟶ H^(p+1)(C, I^(n+1)Fₙ₊₁)` of Stacks 0GYQ. -/
def cohomologyBoundary (n : ℕ) :
    (globalModuleCohomology.{u, v, r, w} O p).obj (F.obj (op n)) ⟶
      (globalModuleCohomology.{u, v, r, w} O (p + 1)).obj (gradedPiece O I F (n + 1)) :=
  (cohomologyDeltaFunctor.{u, v, r, w} O).δ (adicShortComplex_shortExact hF n) p

/-- The boundary maps commute with the canonical graded action: `mulTo` on `Hᵖ` followed by the
boundary map at stage `k` equals the boundary map at stage `n` followed by `actTo` on `H^(p+1)`. -/
theorem cohomologyBoundary_naturality (m n k : ℕ) (h : n + m = k) (a : ↥(I ^ m)) :
    (globalModuleCohomology.{u, v, r, w} O p).map (mulTo hF m n k h a) ≫
        cohomologyBoundary hF p k =
      cohomologyBoundary hF p n ≫ (globalModuleCohomology.{u, v, r, w} O (p + 1)).map
        (actTo hF m (n + 1) (k + 1) (by omega) a) := by
  refine (cohomologyDeltaFunctor.{u, v, r, w} O).δ_naturality
    (adicShortComplex_shortExact hF n) (adicShortComplex_shortExact hF k)
    { τ₁ := actTo hF m (n + 1) (k + 1) (by omega) a
      τ₂ := mulTo hF m (n + 1) (k + 1) (by omega) a
      τ₃ := mulTo hF m n k h a
      comm₁₂ := actTo_comp_ι hF m (n + 1) (k + 1) (by omega) a
      comm₂₃ := (mulTo_naturality hF m n k (n + 1) (k + 1) h (by omega)
        (Nat.le_succ n) a).symm } p

/-- Exactness at `Hᵖ(C, Fₙ)`: the image of `Hᵖ(C, Fₙ₊₁) → Hᵖ(C, Fₙ)` is the kernel of the boundary
map at stage `n`. -/
theorem cohomologyBoundary_range_eq_ker (n : ℕ) :
    LinearMap.range ((globalModuleCohomology.{u, v, r, w} O p).map
        (towerMap F (Nat.le_succ n))).hom =
      LinearMap.ker (cohomologyBoundary hF p n).hom :=
  ShortComplex.Exact.moduleCat_range_eq_ker
    ((cohomologyDeltaFunctor.{u, v, r, w} O).exact_δ₁ (adicShortComplex_shortExact hF n) p)


/-- A functor to modules sends a composite to the composite of the linear maps. -/
private theorem functor_map_comp_hom_apply {D : Type*} [Category D] {R : Type*} [Ring R]
    (G : D ⥤ ModuleCat R) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (x : G.obj X) :
    (G.map (f ≫ g)).hom x = (G.map g).hom ((G.map f).hom x) := by
  simp

/-- Multiplication by `a ∈ Iᵐ` on cohomology sends classes vanishing `c` steps earlier at stage `n`
to classes vanishing `c` steps earlier at stage `k = n + m`. -/
theorem mulTo_mem_vanishingSubmodule (c m n k : ℕ) (h : n + m = k) (a : ↥(I ^ m))
    (x : (globalModuleCohomology.{u, v, r, w} O p).obj (F.obj (op n)))
    (hx : x ∈ vanishingSubmodule (F ⋙ globalModuleCohomology.{u, v, r, w} O p) c n) :
    (globalModuleCohomology.{u, v, r, w} O p).map (mulTo hF m n k h a) x ∈
      vanishingSubmodule (F ⋙ globalModuleCohomology.{u, v, r, w} O p) c k := by
  intro i hi
  change ((globalModuleCohomology.{u, v, r, w} O p).map (towerMap F (show i ≤ k by omega))).hom
    (((globalModuleCohomology.{u, v, r, w} O p).map (mulTo hF m n k h a)).hom x) = 0
  by_cases him : i < m
  · rw [← functor_map_comp_hom_apply, mulTo_comp_towerMap_eq_zero hF m n k i h him a]
    simp
  · have hn : i - m ≤ n := by omega
    rw [← functor_map_comp_hom_apply,
      ← mulTo_naturality hF m (i - m) i n k (by omega) h hn a, functor_map_comp_hom_apply,
      show ((globalModuleCohomology.{u, v, r, w} O p).map (towerMap F hn)).hom x = 0 from
        hx (i - m) (by omega), map_zero]

/-- The images under the boundary maps of the classes vanishing `c` steps earlier. -/
def boundarySubmodule (c : ℕ) : (n : ℕ) → Submodule ↥(GlobalSectionRing O)
    ((globalModuleCohomology.{u, v, r, w} O (p + 1)).obj (gradedPiece O I F n))
  | 0 => ⊥
  | n + 1 => (vanishingSubmodule (F ⋙ globalModuleCohomology.{u, v, r, w} O p) c n).map
      (cohomologyBoundary hF p n).hom

/-- The boundary images of classes vanishing `c` steps earlier are closed under the canonical
graded action. -/
theorem boundarySubmodule_actTo (c m n k : ℕ) (h : n + m = k) (a : ↥(I ^ m))
    (x : (globalModuleCohomology.{u, v, r, w} O (p + 1)).obj (gradedPiece O I F n))
    (hx : x ∈ boundarySubmodule hF p c n) :
    (globalModuleCohomology.{u, v, r, w} O (p + 1)).map (actTo hF m n k h a) x ∈
      boundarySubmodule hF p c k := by
  cases n with
  | zero =>
    have hx0 : x = 0 := hx
    subst x
    simp
  | succ n =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨(globalModuleCohomology.{u, v, r, w} O p).map (mulTo hF m n k (by omega) a) y,
      mulTo_mem_vanishingSubmodule hF p c m n k (by omega) a y hy, ?_⟩
    exact congrArg (fun g => g y) (cohomologyBoundary_naturality hF p m n k (by omega) a)

/-- A graded submodule of `⨁ₙ H^(p+1)(C, IⁿFₙ)`: a family of submodules closed under the
canonical graded action. -/
@[ext]
structure GradedSubmodule where
  /-- The degree `n` part. -/
  carrier (n : ℕ) : Submodule ↥(GlobalSectionRing O)
    ((globalModuleCohomology.{u, v, r, w} O (p + 1)).obj (gradedPiece O I F n))
  /-- The family is closed under the canonical action of `Iᵐ`, which raises degrees by `m`. -/
  smul_mem (m n : ℕ) (a : ↥(I ^ m))
    (x : (globalModuleCohomology.{u, v, r, w} O (p + 1)).obj (gradedPiece O I F n))
    (hx : x ∈ carrier n) :
    ((globalModuleCohomology.{u, v, r, w} O (p + 1)).map (act hF m n a)).hom x ∈ carrier (n + m)

/-- Graded submodules are ordered by degreewise inclusion. -/
instance : PartialOrder (GradedSubmodule hF p) where
  le P Q := ∀ n, P.carrier n ≤ Q.carrier n
  le_refl _ _ := le_rfl
  le_trans _ _ _ h k n := (h n).trans (k n)
  le_antisymm _ _ h k := GradedSubmodule.ext (funext fun n => le_antisymm (h n) (k n))

/-- The graded submodule of boundary images of classes vanishing `c` steps earlier. -/
def boundaryGradedSubmodule (c : ℕ) : GradedSubmodule hF p where
  carrier := boundarySubmodule hF p c
  smul_mem m n a x hx := by
    simpa only [actTo, eqToHom_refl, Category.comp_id] using
      boundarySubmodule_actTo hF p c m n (n + m) rfl a x hx

/-- The boundary graded submodules increase with `c`. -/
theorem boundaryGradedSubmodule_monotone : Monotone (boundaryGradedSubmodule hF p) := by
  intro c d h n
  cases n with
  | zero => exact le_rfl
  | succ n => exact Submodule.map_mono (vanishingSubmodule_mono _ h n)

/-- Under the ascending chain condition on graded submodules of `⨁ₙ H^(p+1)(C, IⁿFₙ)` there is one
`c` such that the boundary of every class of `Hᵖ(C, Fₙ)` is the boundary of a class vanishing `c`
steps earlier. -/
theorem exists_boundary_lift_vanishing
    (hacc : WellFoundedGT (GradedSubmodule hF p)) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : (globalModuleCohomology.{u, v, r, w} O p).obj (F.obj (op n))),
      ∃ y ∈ vanishingSubmodule (F ⋙ globalModuleCohomology.{u, v, r, w} O p) c n,
        (cohomologyBoundary hF p n).hom y = (cohomologyBoundary hF p n).hom x := by
  obtain ⟨c, hc⟩ := (wellFoundedGT_iff_monotone_chain_condition.mp hacc)
    ⟨boundaryGradedSubmodule hF p, boundaryGradedSubmodule_monotone hF p⟩
  refine ⟨c, fun n x => ?_⟩
  have he := congrArg (fun P : GradedSubmodule hF p => P.carrier (n + 1))
    (hc (max c (n + 1)) (le_max_left _ _))
  change boundarySubmodule hF p c (n + 1) =
    boundarySubmodule hF p (max c (n + 1)) (n + 1) at he
  change (cohomologyBoundary hF p n).hom x ∈ boundarySubmodule hF p c (n + 1)
  rw [he]
  refine ⟨x, ?_, rfl⟩
  rw [vanishingSubmodule_eq_top _ (show n < max c (n + 1) by omega)]
  trivial

/-- If the boundary of every class is the boundary of a class vanishing `c` steps earlier, then for
`i + c ≤ n` the image in `Hᵖ(C, Fᵢ)` of a class of `Hᵖ(C, Fₙ)` is also the image of a class of
`Hᵖ(C, Fₙ₊₁)`. -/
theorem exists_lift_preserving_image (c : ℕ)
    (hc : ∀ (n : ℕ) (x : (globalModuleCohomology.{u, v, r, w} O p).obj (F.obj (op n))),
      ∃ y ∈ vanishingSubmodule (F ⋙ globalModuleCohomology.{u, v, r, w} O p) c n,
        (cohomologyBoundary hF p n).hom y = (cohomologyBoundary hF p n).hom x)
    (i n : ℕ) (hi : i + c ≤ n)
    (x : (globalModuleCohomology.{u, v, r, w} O p).obj (F.obj (op n))) :
    ∃ z : (globalModuleCohomology.{u, v, r, w} O p).obj (F.obj (op (n + 1))),
      ((globalModuleCohomology.{u, v, r, w} O p).map
          (towerMap F ((Nat.le_add_right i c).trans (hi.trans (Nat.le_succ n))))).hom z =
        ((globalModuleCohomology.{u, v, r, w} O p).map
          (towerMap F ((Nat.le_add_right i c).trans hi))).hom x := by
  obtain ⟨y, hy, hδ⟩ := hc n x
  change (globalModuleCohomology.{u, v, r, w} O p).obj (F.obj (op n)) at y
  have hker : x - y ∈ LinearMap.ker (cohomologyBoundary hF p n).hom := by
    simp only [LinearMap.mem_ker, map_sub, hδ, sub_self]
  rw [← cohomologyBoundary_range_eq_ker hF p n] at hker
  obtain ⟨z, hz⟩ := hker
  refine ⟨z, ?_⟩
  rw [← towerMap_comp F ((Nat.le_add_right i c).trans hi) (Nat.le_succ n),
    functor_map_comp_hom_apply, hz, map_sub, show ((globalModuleCohomology.{u, v, r, w} O p).map
      (towerMap F ((Nat.le_add_right i c).trans hi))).hom y = 0 from hy i hi, sub_zero]


theorem subobjectModule_image {R : Type*} [Ring R] {X Y : ModuleCat R} (f : X ⟶ Y) :
    ModuleCat.subobjectModule Y (imageSubobject f) = LinearMap.range f.hom := by
  change LinearMap.range (imageSubobject f).arrow.hom = LinearMap.range f.hom
  conv_rhs => rw [← imageSubobject_arrow_comp f]
  rw [ModuleCat.hom_comp, LinearMap.range_comp,
    ModuleCat.range_eq_top_of_epi (factorThruImageSubobject f), Submodule.map_top]

/-- **Stacks Project, Tag 0GYQ**, the footnote: the images of `Hᵖ(C, F_k) → Hᵖ(C, Fᵢ)` are the
stable image already at `k = i + c`, for one `c` independent of `i`. -/
@[stacks 0GYQ "the uniform shift of the footnote", sga "2 IX 2.1" "(iii)"]
theorem exists_uniform_stable_image (hacc : WellFoundedGT (GradedSubmodule hF p)) :
    ∃ c : ℕ, ∀ i k : ℕ, ∀ h : i + c ≤ k,
      transitionImage (F ⋙ globalModuleCohomology.{u, v, r, w} O p) i k (by omega) =
        transitionImage (F ⋙ globalModuleCohomology.{u, v, r, w} O p) i (i + c) (by omega) := by
  obtain ⟨c, hc⟩ := exists_boundary_lift_vanishing hF p hacc
  refine ⟨c, fun i k h => ?_⟩
  have hstep (n : ℕ) (hn : i + c ≤ n) :
      LinearMap.range ((F ⋙ globalModuleCohomology.{u, v, r, w} O p).map
          (homOfLE ((Nat.le_add_right i c).trans (hn.trans (Nat.le_succ n)))).op).hom =
        LinearMap.range ((F ⋙ globalModuleCohomology.{u, v, r, w} O p).map
          (homOfLE ((Nat.le_add_right i c).trans hn)).op).hom := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨(F ⋙ globalModuleCohomology.{u, v, r, w} O p).map (homOfLE (Nat.le_succ n)).op z,
        congrArg (fun g => ModuleCat.Hom.hom g z)
          (towerMap_comp (F ⋙ globalModuleCohomology.{u, v, r, w} O p)
            ((Nat.le_add_right i c).trans hn) (Nat.le_succ n))⟩
    · rintro ⟨z, rfl⟩
      exact exists_lift_preserving_image hF p c hc i n hn z
  apply (ModuleCat.subobjectModule
    ((F ⋙ globalModuleCohomology.{u, v, r, w} O p).obj (op i))).injective
  change ModuleCat.subobjectModule _ (imageSubobject _) =
    ModuleCat.subobjectModule _ (imageSubobject _)
  rw [subobjectModule_image, subobjectModule_image]
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k hk ih => exact (hstep k hk).trans ih

/-- **Stacks Project, Tag 0GYQ.** For an inverse system of sheaves of modules on a site with
`Fₙ = Fₙ₊₁/IⁿFₙ₊₁`, the ascending chain condition on the graded submodules of
`⨁ₙ H^(p+1)(C, IⁿFₙ₊₁)` implies that the inverse system `n ↦ Hᵖ(C, Fₙ)` satisfies the
Mittag-Leffler condition. -/
@[stacks 0GYQ]
theorem isMittagLefflerCategorical_cohomology (hacc : WellFoundedGT (GradedSubmodule hF p)) :
    IsMittagLefflerCategorical (F ⋙ globalModuleCohomology.{u, v, r, w} O p) := by
  obtain ⟨c, hc⟩ := exists_uniform_stable_image hF p hacc
  exact fun i => ⟨i + c, Nat.le_add_right i c, hc i⟩

end MittagLeffler


end AdicSystem

end Stacks.Cohomology.AdicInverseSystems

end
