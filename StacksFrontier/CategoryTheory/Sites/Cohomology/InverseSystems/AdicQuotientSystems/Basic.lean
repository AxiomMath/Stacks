module

public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Order.OrderIsoNat
public import StacksFrontier.CategoryTheory.Abelian.InverseSystem
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedGenerators
public import StacksFrontier.Topology.Algebra.AdicLimitTopology
import StacksCore.Tactic.StacksAttribute

/-!
# Basic theory of inverse systems with adic quotients

The transition maps of an `ℕ`-indexed inverse system, the hypothesis `IsAdicQuotientSystem`
(`Fₙ = Fₙ₊₁/I^(n+1)Fₙ₊₁`), its short exact sequences `0 → I^(n+1)Fₘ → Fₘ → Fₙ → 0`, and the
canonical graded action of `Iᵐ` on the system.

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


/-- The transition map `Fₘ ⟶ Fₙ` of an inverse system indexed by `ℕ`, for `n ≤ m`. -/
abbrev towerMap {D : Type*} [Category D] (F : ℕᵒᵖ ⥤ D) {n m : ℕ} (h : n ≤ m) :
    F.obj (op m) ⟶ F.obj (op n) := F.map (homOfLE h).op

/-- The transition maps of an inverse system compose: `Fₖ ⟶ Fₘ ⟶ Fₙ` is `Fₖ ⟶ Fₙ`. -/
@[reassoc]
theorem towerMap_comp {D : Type*} [Category D] (F : ℕᵒᵖ ⥤ D) {n m k : ℕ}
    (hnm : n ≤ m) (hmk : m ≤ k) :
    towerMap F hmk ≫ towerMap F hnm = towerMap F (hnm.trans hmk) := by
  rw [← F.map_comp]
  rfl

/-- The transition map `Fₙ ⟶ Fₙ` of an inverse system is the identity. -/
private theorem towerMap_self {D : Type*} [Category D] (F : ℕᵒᵖ ⥤ D) {n : ℕ} (h : n ≤ n) :
    towerMap F h = 𝟙 (F.obj (op n)) := by
  rw [← F.map_id]
  rfl

/-- The classes of an inverse system of modules that vanish at every stage at least `c` steps
earlier. -/
def vanishingSubmodule {R : Type*} [Ring R] (M : ℕᵒᵖ ⥤ ModuleCat R) (c n : ℕ) :
    Submodule R (M.obj (op n)) where
  carrier := {x | ∀ i (_ : i + c ≤ n), (M.map (homOfLE (show i ≤ n by omega)).op).hom x = 0}
  zero_mem' := by simp
  add_mem' hx hy i hi := by simp [hx i hi, hy i hi]
  smul_mem' a _ hx i hi := by simp [hx i hi]

/-- Classes vanishing `c` steps earlier vanish `d ≥ c` steps earlier. -/
theorem vanishingSubmodule_mono {R : Type*} [Ring R] (M : ℕᵒᵖ ⥤ ModuleCat R) {c d : ℕ}
    (h : c ≤ d) (n : ℕ) : vanishingSubmodule M c n ≤ vanishingSubmodule M d n :=
  fun _ hx i hi => hx i (by omega)

/-- At a stage `n < c` the condition of vanishing `c` steps earlier is vacuous. -/
theorem vanishingSubmodule_eq_top {R : Type*} [Ring R] (M : ℕᵒᵖ ⥤ ModuleCat R) {c n : ℕ}
    (h : n < c) : vanishingSubmodule M c n = ⊤ :=
  top_unique fun _ _ i hi => absurd hi (by omega)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{r}) [∀ X : Cᵒᵖ, IsMulCommutative (O.obj.obj X)]

/-! ### Inverse systems with adic quotients -/

section AdicSystem

variable (I : Ideal ↥(GlobalSectionRing O)) (F : ℕᵒᵖ ⥤ SheafOfModules.{max u v r w} O)

/-- The subsheaf `Iⁿ Fₙ`, the `n`-th homogeneous piece of the graded object of Stacks 0GYQ. -/
abbrev gradedPiece (n : ℕ) : SheafOfModules.{max u v r w} O :=
  idealSmul O (I ^ n) (F.obj (op n))

/-- The hypothesis `Fₙ = Fₙ₊₁/I^(n+1)Fₙ₊₁` of Stacks 0GYQ and 0GYS, with the term `Fₙ` of the
system standing for the source's `F₍ₙ₊₁₎`. -/
def IsAdicQuotientSystem : Prop :=
  ∀ n : ℕ, ∃ z : idealSmulι O (I ^ (n + 1)) (F.obj (op (n + 1))) ≫
      towerMap F (Nat.le_succ n) = 0,
    (ShortComplex.mk (idealSmulι O (I ^ (n + 1)) (F.obj (op (n + 1))))
      (towerMap F (Nat.le_succ n)) z).ShortExact

variable {O I F}

/-- The subsheaf `I^(n+1)Fₙ₊₁` is killed by the transition map `Fₙ₊₁ ⟶ Fₙ`. -/
theorem IsAdicQuotientSystem.idealSmulι_comp_towerMap_succ (hF : IsAdicQuotientSystem O I F)
    (n : ℕ) : idealSmulι O (I ^ (n + 1)) (F.obj (op (n + 1))) ≫
      towerMap F (Nat.le_succ n) = 0 := (hF n).choose

/-- The sequence `0 → I^(n+1)Fₙ₊₁ → Fₙ₊₁ → Fₙ → 0` is short exact. -/
theorem IsAdicQuotientSystem.shortExact_succ (hF : IsAdicQuotientSystem O I F) (n : ℕ) :
    (ShortComplex.mk (idealSmulι O (I ^ (n + 1)) (F.obj (op (n + 1))))
      (towerMap F (Nat.le_succ n)) (hF.idealSmulι_comp_towerMap_succ n)).ShortExact :=
  (hF n).choose_spec

/-- Every transition map `Fₘ ⟶ Fₙ` of an adic quotient system is an epimorphism. -/
theorem IsAdicQuotientSystem.epi_towerMap (hF : IsAdicQuotientSystem O I F) {n m : ℕ}
    (h : n ≤ m) : Epi (towerMap F h) := by
  induction h with
  | refl =>
    rw [towerMap_self]
    infer_instance
  | @step m hm ih =>
    have h₁ : Epi (towerMap F (Nat.le_succ m)) := (hF.shortExact_succ m).epi_g
    have h₂ : Epi (towerMap F hm) := ih
    show Epi (towerMap F (Nat.le_trans hm (Nat.le_succ m)))
    rw [← towerMap_comp F hm (Nat.le_succ m)]
    infer_instance

/-- Multiplication by an element of `I^(n+1)` is zero on `Fₙ`. -/
theorem IsAdicQuotientSystem.globalSmul_eq_zero (hF : IsAdicQuotientSystem O I F) (n : ℕ)
    {a : ↥(GlobalSectionRing O)} (ha : a ∈ I ^ (n + 1)) :
    globalSmul O a (F.obj (op n)) = 0 := by
  have hepi := hF.epi_towerMap (Nat.le_succ n)
  refine (cancel_epi (towerMap F (Nat.le_succ n))).1 ?_
  rw [comp_zero, comp_globalSmul, ← idealSmulFactor_comp_ι O (I ^ (n + 1))
    (F.obj (op (n + 1))) ha, Category.assoc, hF.idealSmulι_comp_towerMap_succ n, comp_zero]

/-- For `m ≥ n + 1` the subsheaf `I^(n+1)Fₘ` is killed by the transition map `Fₘ ⟶ Fₙ`. -/
theorem IsAdicQuotientSystem.idealSmulι_comp_towerMap (hF : IsAdicQuotientSystem O I F)
    {n m : ℕ} (h : n + 1 ≤ m) :
    idealSmulι O (I ^ (n + 1)) (F.obj (op m)) ≫ towerMap F (Nat.le_of_succ_le h) = 0 := by
  refine (idealSmulι_comp_eq_zero_iff O (I ^ (n + 1)) (F.obj (op m)) _).mpr ?_
  intro a ha
  rw [← towerMap_comp F (Nat.le_succ n) h, ← Category.assoc, ← comp_globalSmul,
    Category.assoc, ← idealSmulFactor_comp_ι O (I ^ (n + 1)) (F.obj (op (n + 1))) ha,
    Category.assoc, hF.idealSmulι_comp_towerMap_succ n, comp_zero, comp_zero]


/-- A map out of `Fₙ₊₁` that kills `I^(n+1)Fₙ₊₁` factors through the transition map `Fₙ₊₁ ⟶ Fₙ`. -/
theorem IsAdicQuotientSystem.exists_desc_succ (hF : IsAdicQuotientSystem O I F) (n : ℕ)
    {G : SheafOfModules.{max u v r w} O} (f : F.obj (op (n + 1)) ⟶ G)
    (hf : idealSmulι O (I ^ (n + 1)) (F.obj (op (n + 1))) ≫ f = 0) :
    ∃ g : F.obj (op n) ⟶ G, towerMap F (Nat.le_succ n) ≫ g = f := by
  refine ⟨(CokernelCofork.IsColimit.desc' (hF.shortExact_succ n).gIsCokernel f hf).1, ?_⟩
  exact (CokernelCofork.IsColimit.desc' (hF.shortExact_succ n).gIsCokernel f hf).2

/-- For `m ≥ n + 1`, a map out of `Fₘ` that kills `I^(n+1)Fₘ` factors through the transition map
`Fₘ ⟶ Fₙ`. -/
theorem IsAdicQuotientSystem.exists_desc (hF : IsAdicQuotientSystem O I F) {n m : ℕ}
    (h : n + 1 ≤ m) {G : SheafOfModules.{max u v r w} O} (f : F.obj (op m) ⟶ G)
    (hf : idealSmulι O (I ^ (n + 1)) (F.obj (op m)) ≫ f = 0) :
    ∃ g : F.obj (op n) ⟶ G, towerMap F (Nat.le_of_succ_le h) ≫ g = f := by
  induction m, h using Nat.le_induction with
  | base => exact hF.exists_desc_succ n f hf
  | succ m h ih =>
    have hkill := (idealSmulι_comp_eq_zero_iff O (I ^ (n + 1)) (F.obj (op (m + 1))) f).mp hf
    have hm : idealSmulι O (I ^ (m + 1)) (F.obj (op (m + 1))) ≫ f = 0 :=
      (idealSmulι_comp_eq_zero_iff O (I ^ (m + 1)) (F.obj (op (m + 1))) f).mpr
        fun a ha => hkill a (Ideal.pow_le_pow_right (by omega) ha)
    obtain ⟨g, hg⟩ := hF.exists_desc_succ m f hm
    have hgkill : idealSmulι O (I ^ (n + 1)) (F.obj (op m)) ≫ g = 0 := by
      refine (idealSmulι_comp_eq_zero_iff O (I ^ (n + 1)) (F.obj (op m)) g).mpr ?_
      intro a ha
      have hepi := hF.epi_towerMap (Nat.le_succ m)
      refine (cancel_epi (towerMap F (Nat.le_succ m))).1 ?_
      rw [comp_zero, ← Category.assoc, comp_globalSmul, Category.assoc, hg]
      exact hkill a ha
    obtain ⟨g', hg'⟩ := ih g hgkill
    refine ⟨g', ?_⟩
    rw [← towerMap_comp F (Nat.le_of_succ_le h) (Nat.le_succ m), Category.assoc, hg', hg]

/-- The short exact sequence `0 → I^(n+1)Fₘ → Fₘ → Fₙ → 0` for every `m ≥ n + 1`. -/
theorem IsAdicQuotientSystem.shortExact (hF : IsAdicQuotientSystem O I F) {n m : ℕ}
    (h : n + 1 ≤ m) :
    (ShortComplex.mk (idealSmulι O (I ^ (n + 1)) (F.obj (op m)))
      (towerMap F (Nat.le_of_succ_le h)) (hF.idealSmulι_comp_towerMap h)).ShortExact := by
  have hepi : Epi (towerMap F (Nat.le_of_succ_le h)) := hF.epi_towerMap _
  refine ⟨ShortComplex.exact_of_g_is_cokernel _ ?_⟩
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {G} f hf => (hF.exists_desc h f hf).choose) ?_ ?_
  · intro G f hf
    exact (hF.exists_desc h f hf).choose_spec
  · intro G f hf g hg
    refine (cancel_epi (towerMap F (Nat.le_of_succ_le h))).mp ?_
    exact hg.trans (hF.exists_desc h f hf).choose_spec.symm


/-! ### The canonical graded action -/

/-- Multiplication by `a ∈ I` on `Fₙ₊₁` factors through the transition map `Fₙ₊₁ ⟶ Fₙ`. -/
theorem IsAdicQuotientSystem.exists_lift_one (hF : IsAdicQuotientSystem O I F) (n : ℕ)
    {a : ↥(GlobalSectionRing O)} (ha : a ∈ I) :
    ∃ g : F.obj (op n) ⟶ F.obj (op (n + 1)),
      towerMap F (Nat.le_succ n) ≫ g = globalSmul O a (F.obj (op (n + 1))) := by
  refine hF.exists_desc_succ n _ ?_
  refine (idealSmulι_comp_eq_zero_iff O (I ^ (n + 1)) (F.obj (op (n + 1))) _).mpr ?_
  intro b hb
  rw [← globalSmul_mul]
  refine hF.globalSmul_eq_zero (n + 1) ?_
  rw [pow_succ]
  exact Ideal.mul_mem_mul hb ha

/-- Multiplication by `a ∈ Iᵐ` on `Fₙ₊ₘ` factors through the transition map `Fₙ₊ₘ ⟶ Fₙ`. -/
theorem IsAdicQuotientSystem.exists_mul_lift (hF : IsAdicQuotientSystem O I F) (m n : ℕ)
    {a : ↥(GlobalSectionRing O)} (ha : a ∈ I ^ m) :
    ∃ g : F.obj (op n) ⟶ F.obj (op (n + m)),
      towerMap F (Nat.le_add_right n m) ≫ g = globalSmul O a (F.obj (op (n + m))) := by
  induction m generalizing a with
  | zero =>
    refine ⟨globalSmul O a (F.obj (op (n + 0))), ?_⟩
    rw [towerMap_self]
    exact Category.id_comp _
  | succ m ih =>
    have ha' : a ∈ (I ^ m) * I := by
      rw [← pow_succ]
      exact ha
    refine Submodule.mul_induction_on
      (C := fun c => ∃ g : F.obj (op n) ⟶ F.obj (op (n + (m + 1))),
        towerMap F (Nat.le_add_right n (m + 1)) ≫ g =
          globalSmul O c (F.obj (op (n + (m + 1))))) ha' ?_ ?_
    · intro y hy x hx
      obtain ⟨gy, hgy⟩ := ih hy
      obtain ⟨gx, hgx⟩ := hF.exists_lift_one (n + m) hx
      refine ⟨gy ≫ gx, ?_⟩
      calc towerMap F (Nat.le_add_right n (m + 1)) ≫ (gy ≫ gx)
          = (towerMap F (Nat.le_succ (n + m)) ≫ towerMap F (Nat.le_add_right n m)) ≫
              (gy ≫ gx) := by rw [towerMap_comp]
        _ = towerMap F (Nat.le_succ (n + m)) ≫
              (towerMap F (Nat.le_add_right n m) ≫ gy) ≫ gx := by
              simp only [Category.assoc]
        _ = towerMap F (Nat.le_succ (n + m)) ≫
              globalSmul O y (F.obj (op (n + m))) ≫ gx := by rw [hgy]
        _ = globalSmul O y (F.obj (op (n + m + 1))) ≫
              (towerMap F (Nat.le_succ (n + m)) ≫ gx) := by
              rw [← Category.assoc, comp_globalSmul, Category.assoc]
        _ = globalSmul O y (F.obj (op (n + m + 1))) ≫
              globalSmul O x (F.obj (op (n + m + 1))) := by rw [hgx]
        _ = globalSmul O (y * x) (F.obj (op (n + (m + 1)))) :=
              (globalSmul_mul O y x (F.obj (op (n + (m + 1))))).symm
    · rintro b c ⟨gb, hgb⟩ ⟨gc, hgc⟩
      exact ⟨gb + gc, by rw [Preadditive.comp_add, hgb, hgc, ← globalSmul_add]⟩

/-- Multiplication by `a ∈ Iᵐ`, lifted through the quotients to a map `Fₙ ⟶ Fₙ₊ₘ`. -/
def mulLift (hF : IsAdicQuotientSystem O I F) (m n : ℕ) (a : ↥(I ^ m)) :
    F.obj (op n) ⟶ F.obj (op (n + m)) :=
  (hF.exists_mul_lift m n a.2).choose

/-- `mulLift` lifts multiplication by `a`: the transition map `Fₙ₊ₘ ⟶ Fₙ` followed by
`mulLift hF m n a` is multiplication by `a` on `Fₙ₊ₘ`. -/
@[reassoc]
theorem towerMap_comp_mulLift (hF : IsAdicQuotientSystem O I F) (m n : ℕ) (a : ↥(I ^ m)) :
    towerMap F (Nat.le_add_right n m) ≫ mulLift hF m n a =
      globalSmul O a.1 (F.obj (op (n + m))) :=
  (hF.exists_mul_lift m n a.2).choose_spec

/-- The canonical degree-raising action of `a ∈ Iᵐ` on the subsheaves `IⁿFₙ`. -/
def act (hF : IsAdicQuotientSystem O I F) (m n : ℕ) (a : ↥(I ^ m)) :
    gradedPiece O I F n ⟶ gradedPiece O I F (n + m) :=
  idealSmulLift O (I ^ (n + m)) (F.obj (op (n + m)))
    (idealSmulι O (I ^ n) (F.obj (op n)) ≫ mulLift hF m n a)
    (comp_cokernelπ_eq_zero O (I ^ n) (F.obj (op n)) (I ^ (n + m)) (mulLift hF m n a) (by
      intro b hb
      have hepi := hF.epi_towerMap (Nat.le_add_right n m)
      refine (cancel_epi (towerMap F (Nat.le_add_right n m))).1 ?_
      rw [comp_zero]
      calc towerMap F (Nat.le_add_right n m) ≫ globalSmul O b (F.obj (op n)) ≫
            mulLift hF m n a ≫ cokernel.π (idealSmulHom O (I ^ (n + m)) (F.obj (op (n + m))))
          = (towerMap F (Nat.le_add_right n m) ≫ globalSmul O b (F.obj (op n))) ≫
              mulLift hF m n a ≫
                cokernel.π (idealSmulHom O (I ^ (n + m)) (F.obj (op (n + m)))) := by
              simp only [Category.assoc]
        _ = globalSmul O b (F.obj (op (n + m))) ≫
              (towerMap F (Nat.le_add_right n m) ≫ mulLift hF m n a) ≫
                cokernel.π (idealSmulHom O (I ^ (n + m)) (F.obj (op (n + m)))) := by
              rw [comp_globalSmul]
              simp only [Category.assoc]
        _ = globalSmul O (b * a.1) (F.obj (op (n + m))) ≫
              cokernel.π (idealSmulHom O (I ^ (n + m)) (F.obj (op (n + m)))) := by
              rw [towerMap_comp_mulLift, globalSmul_mul]
              simp only [Category.assoc]
        _ = 0 := globalSmul_comp_cokernelπ O (I ^ (n + m)) (F.obj (op (n + m))) (by
              rw [pow_add]
              exact Ideal.mul_mem_mul hb a.2)))

/-- `act` is the restriction of `mulLift` to the ideal-power subsheaves: it commutes with the
inclusions `IⁿFₙ ⟶ Fₙ` and `I^(n+m)Fₙ₊ₘ ⟶ Fₙ₊ₘ`. -/
@[reassoc]
theorem act_comp_ι (hF : IsAdicQuotientSystem O I F) (m n : ℕ) (a : ↥(I ^ m)) :
    act hF m n a ≫ idealSmulι O (I ^ (n + m)) (F.obj (op (n + m))) =
      idealSmulι O (I ^ n) (F.obj (op n)) ≫ mulLift hF m n a :=
  idealSmulLift_comp_ι O (I ^ (n + m)) (F.obj (op (n + m))) _ _


end AdicSystem

end Stacks.Cohomology.AdicInverseSystems

end
