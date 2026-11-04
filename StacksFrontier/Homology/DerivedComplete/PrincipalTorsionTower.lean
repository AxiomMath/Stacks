module

public import Mathlib
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products

/-!
# The principal power-torsion and cone towers, and their Mittag--Leffler comparison

Let `f` be an element of a commutative ring `A`. This file introduces two inverse systems
attached to the positive powers `f ^ (n + 1)`, `n : ℕ`, of `f`: the system of `f`-power torsion
submodules of a module, and the system of cones of multiplication by `f ^ (n + 1)` on a complex,
whose image in the derived category models `K ⊗ᴸ (A →[f^(n+1)] A)`. The cohomology tower of the
second system is Mittag--Leffler exactly when the torsion tower of the next cohomology module is,
the Mittag--Leffler condition being that of the underlying type-valued functors.

## Main definitions

* `PrincipalTorsionTower.powerMultiplication`: multiplication by an element of `A` on a module,
  as a morphism.
* `PrincipalTorsionTower.powerTorsionSystem`: the inverse system `M[f^(n+1)]` of `f`-power
  torsion submodules, with transition maps multiplication by `f`.
* `PrincipalTorsionTower.principalComplexSystem`: the tower of cones of `f ^ (n + 1) • 𝟙 C` on a
  cochain complex.
* `PrincipalTorsionTower.principalDerivedTensorSystem`: the induced inverse system in `D(A)`, the
  derived reductions of an object of `D(A)` modulo the positive powers of `f`.

## Main results

* `PrincipalTorsionTower.isMittagLeffler_principalDerivedTensor_iff_powerTorsion`: the
  Mittag--Leffler equivalence between the cohomology tower of the derived reductions and the
  power-torsion tower of the next cohomology module.

## References

* [Stacks Project, Tag 0BKG](https://stacks.math.columbia.edu/tag/0BKG)
* [Stacks Project, Tag 0H32](https://stacks.math.columbia.edu/tag/0H32)
* [Stacks Project, Tag 0H33](https://stacks.math.columbia.edu/tag/0H33)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Preadditive CategoryTheory.Linear DerivedCategory

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace PrincipalTorsionTower

section Torsion

variable (A : Type u) [CommRing A]

/-- Multiplication by `a` on an `A`-module, regarded as a morphism of `ModuleCat A`. -/
def powerMultiplication (M : ModuleCat.{v} A) (a : A) : M ⟶ M :=
  ModuleCat.ofHom (LinearMap.lsmul A M a)

/-- `powerMultiplication A M a` sends `x` to `a • x`. -/
@[simp]
lemma powerMultiplication_apply (M : ModuleCat.{v} A) (a : A) (x : M) :
    powerMultiplication A M a x = a • x := rfl

/-- Multiplication by `f` sends the `f ^ (n + 2)`-torsion submodule into the
`f ^ (n + 1)`-torsion submodule. -/
def powerTorsionTransition (M : ModuleCat.{v} A) (f : A) (n : ℕ) :
    kernel (powerMultiplication A M (f ^ (n + 2))) ⟶
      kernel (powerMultiplication A M (f ^ (n + 1))) :=
  kernel.lift (powerMultiplication A M (f ^ (n + 1)))
    (kernel.ι (powerMultiplication A M (f ^ (n + 2))) ≫ powerMultiplication A M f) (by
      rw [Category.assoc, show powerMultiplication A M f ≫
          powerMultiplication A M (f ^ (n + 1)) =
            powerMultiplication A M (f ^ (n + 2)) by
        ext x
        simp [powerMultiplication, pow_succ', smul_smul]]
      exact kernel.condition _)

/-- The transition map `powerTorsionTransition A M f n`, followed by the inclusion of the
`f ^ (n + 1)`-torsion submodule, is the inclusion of the `f ^ (n + 2)`-torsion submodule followed
by multiplication by `f`. -/
@[reassoc (attr := simp)]
lemma powerTorsionTransition_ι (M : ModuleCat.{v} A) (f : A) (n : ℕ) :
    powerTorsionTransition A M f n ≫
        kernel.ι (powerMultiplication A M (f ^ (n + 1))) =
      kernel.ι (powerMultiplication A M (f ^ (n + 2))) ≫ powerMultiplication A M f := by
  apply kernel.lift_ι

/-- The inverse system `M[f^(n+1)]`, whose transition maps are multiplication by `f`. -/
def powerTorsionSystem (M : ModuleCat.{v} A) (f : A) : ℕᵒᵖ ⥤ ModuleCat.{v} A :=
  Functor.ofOpSequence
    (X := fun n ↦ kernel (powerMultiplication A M (f ^ (n + 1))))
    (powerTorsionTransition A M f)

/-- The `n`-th term of `powerTorsionSystem A M f` is the `f ^ (n + 1)`-torsion submodule. -/
@[simp]
lemma powerTorsionSystem_obj (M : ModuleCat.{v} A) (f : A) (n : ℕ) :
    (powerTorsionSystem A M f).obj ⟨n⟩ =
      kernel (powerMultiplication A M (f ^ (n + 1))) := rfl

/-- The transition map of `powerTorsionSystem A M f` from `n + 1` to `n` is
`powerTorsionTransition A M f n`. -/
@[simp]
lemma powerTorsionSystem_map_succ (M : ModuleCat.{v} A) (f : A) (n : ℕ) :
    (powerTorsionSystem A M f).map (homOfLE (Nat.le_succ n)).op =
      powerTorsionTransition A M f n := by
  apply Functor.ofOpSequence_map_homOfLE_succ

/-- The principal Koszul tower with coefficients in `C`: the cones of multiplication by
`f ^ (n + 1)` on `C`, with transition maps induced by multiplication by `f`. -/
abbrev principalComplexSystem (f : A) (C : CochainComplex (ModuleCat.{v} A) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ :=
  Functor.ofOpSequence (X := fun n ↦ CochainComplex.mappingCone (f ^ (n + 1) • 𝟙 C))
    (fun n ↦ CochainComplex.mappingCone.map _ _ (f • 𝟙 C) (𝟙 C) (by
      simp [comp_smul, smul_smul, pow_succ', mul_comm]))

/-- The inverse system `K ⊗ᴸ_A (A →[f^(n+1)] A)`, represented by the cones of multiplication by
`f^(n+1)` on the chosen complex representing `K`. -/
def principalDerivedTensorSystem (f : A) (K : DerivedCategory (ModuleCat.{v} A)) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{v} A) :=
  principalComplexSystem A f (DerivedCategory.Q.objPreimage K) ⋙ DerivedCategory.Q

/-- The `n`-th term of `principalDerivedTensorSystem A f K` is the image in `D(A)` of the cone of
multiplication by `f ^ (n + 1)` on the chosen complex representing `K`. -/
@[simp]
lemma principalDerivedTensorSystem_obj (f : A) (K : DerivedCategory (ModuleCat.{v} A)) (n : ℕ) :
    (principalDerivedTensorSystem A f K).obj ⟨n⟩ =
      DerivedCategory.Q.obj (CochainComplex.mappingCone
        (f ^ (n + 1) • 𝟙 (DerivedCategory.Q.objPreimage K))) := rfl

end Torsion

section MittagLeffler

private lemma isMittagLeffler_of_pointwise_surjective
    {J : Type*} [Category J] [IsCofilteredOrEmpty J]
    {F G : J ⥤ Type v} (q : F ⟶ G)
    (hq : ∀ i, Function.Surjective (q.app i))
    (hF : F.IsMittagLeffler) : G.IsMittagLeffler := by
  apply (G.isMittagLeffler_iff_subset_range_comp).2
  intro j
  obtain ⟨i, f, hf⟩ := (F.isMittagLeffler_iff_subset_range_comp).1 hF j
  refine ⟨i, f, fun k g y hy ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨a, rfl⟩ := hq i x
  obtain ⟨b, hb⟩ := hf g ⟨a, rfl⟩
  refine ⟨q.app k b, ?_⟩
  rw [← NatTrans.naturality_apply q (g ≫ f), hb,
    NatTrans.naturality_apply q f]

/-- A quotient of a module system with kernel generated by a constant system
has the same Mittag--Leffler condition as the original system. -/
private lemma isMittagLeffler_iff_of_constant_kernel
    {J : Type*} [Category J] [IsCofilteredOrEmpty J]
    {R : Type*} [Ring R] {F G : J ⥤ ModuleCat.{v} R}
    (M : ModuleCat.{v} R) (a : (Functor.const J).obj M ⟶ F) (q : F ⟶ G)
    (hq : ∀ i, Function.Surjective (q.app i))
    (hker : ∀ i (x : F.obj i), q.app i x = 0 → ∃ m, a.app i m = x) :
    (F ⋙ forget _).IsMittagLeffler ↔ (G ⋙ forget _).IsMittagLeffler := by
  refine ⟨isMittagLeffler_of_pointwise_surjective (Functor.whiskerRight q (forget _)) hq,
    fun hG ↦ ((F ⋙ forget _).isMittagLeffler_iff_subset_range_comp).2 fun j ↦ ?_⟩
  obtain ⟨i, f, hf⟩ := ((G ⋙ forget _).isMittagLeffler_iff_subset_range_comp).1 hG j
  refine ⟨i, f, fun k g y hy ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨z, hz⟩ := hf g ⟨q.app i x, rfl⟩
  obtain ⟨t, rfl⟩ := hq k z
  have hn (i j : J) (h : i ⟶ j) (x : F.obj i) :
      q.app j (F.map h x) = G.map h (q.app i x) :=
    congrArg (fun e : F.obj i ⟶ G.obj j ↦ e x) (q.naturality h)
  have hz' : q.app j (F.map f x - F.map (g ≫ f) t) = 0 := by
    rw [map_sub, hn, hn]
    exact sub_eq_zero.mpr hz.symm
  obtain ⟨m, hm⟩ := hker j _ hz'
  refine ⟨t + a.app k m, ?_⟩
  show F.map (g ≫ f) (t + a.app k m) = F.map f x
  have ha : F.map (g ≫ f) (a.app k m) = a.app j m :=
    (congrArg (fun e : M ⟶ F.obj j ↦ e m) (a.naturality (g ≫ f))).symm
  rw [map_add, ha, hm]
  abel

private lemma homologyMap_smul_id
    {R : Type u} [CommRing R] (C : CochainComplex (ModuleCat.{v} R) ℤ)
    (p : ℤ) (r : R) :
    HomologicalComplex.homologyMap (r • 𝟙 C) p = r • 𝟙 (C.homology p) := by
  rw [HomologicalComplex.homologyMap]
  have h : (HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℤ) p).map
      (r • 𝟙 C) = r • 𝟙 _ := by
    ext <;> simp <;> rfl
  rw [h, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

/-- Scalars act on the cohomology of the image of a complex in `D(R)` through the scalar action
on the complex. -/
private lemma homologyFunctor_map_Q_smul_id
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C : CochainComplex (ModuleCat.{v} R) ℤ)
    (p : ℤ) (r : R) :
    (homologyFunctor (ModuleCat.{v} R) p).map (Q.map (r • 𝟙 C)) =
      r • 𝟙 ((homologyFunctor (ModuleCat.{v} R) p).obj (Q.obj C)) := by
  let i : (homologyFunctor (ModuleCat.{v} R) p).obj (Q.obj C) ≅ C.homology p :=
    (homologyFunctorFactors (ModuleCat.{v} R) p).app C
  apply (cancel_mono i.hom).1
  show (homologyFunctor (ModuleCat.{v} R) p).map (Q.map (r • 𝟙 C)) ≫
    (homologyFunctorFactors (ModuleCat.{v} R) p).hom.app C = _
  rw [homologyFunctorFactors_hom_naturality, homologyMap_smul_id]
  show i.hom ≫ (r • 𝟙 (C.homology p)) = (r • 𝟙 _) ≫ i.hom
  simp only [comp_smul, smul_comp, Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The cohomology tower of the derived reductions of `K` modulo the positive
powers of `f` is Mittag--Leffler if and only if the tower of elements of `H^(p + 1)(K)` killed
by those powers is Mittag--Leffler. -/
@[stacks 0H33]
theorem isMittagLeffler_principalDerivedTensor_iff_powerTorsion
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ) :
    ((principalDerivedTensorSystem A f K ⋙
        homologyFunctor (ModuleCat.{v} A) p) ⋙ forget (ModuleCat.{v} A)).IsMittagLeffler ↔
      ((powerTorsionSystem A ((homologyFunctor (ModuleCat.{v} A) (p + 1)).obj K) f) ⋙
          forget (ModuleCat.{v} A)).IsMittagLeffler := by
  let C := Q.objPreimage K
  let e := Q.objObjPreimageIso K
  let H := homologyFunctor (ModuleCat.{v} A)
  let F := principalDerivedTensorSystem A f K ⋙ H p
  let G := powerTorsionSystem A ((H (p + 1)).obj K) f
  let T (n : ℕ) := Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C))
  have hT (n : ℕ) : T n ∈ distTriang _ :=
    DerivedCategory.mappingCone_triangle_distinguished _
  let δ (n : ℕ) := (H 0).homologySequenceδ (T n) p (p + 1) rfl
  have hm (r : A) : (H (p + 1)).map (Q.map (r • 𝟙 C)) =
      powerMultiplication A ((H (p + 1)).obj (Q.obj C)) r :=
    homologyFunctor_map_Q_smul_id C (p + 1) r
  have hcomm (r : A) : (H (p + 1)).map e.hom ≫
      powerMultiplication A ((H (p + 1)).obj K) r =
      powerMultiplication A ((H (p + 1)).obj (Q.obj C)) r ≫
        (H (p + 1)).map e.hom := by
    ext x
    show r • ((H (p + 1)).map e.hom) x = ((H (p + 1)).map e.hom) (r • x)
    exact (map_smul _ _ _).symm
  let d (n : ℕ) : F.obj ⟨n⟩ ⟶ (H (p + 1)).obj K :=
    δ n ≫ (H (p + 1)).map e.hom
  have hd (n : ℕ) : d n ≫
      powerMultiplication A ((H (p + 1)).obj K) (f ^ (n + 1)) = 0 := by
    dsimp only [d]
    rw [Category.assoc, hcomm, ← hm, ← Category.assoc]
    show (δ n ≫ (H (p + 1)).map (T n).mor₁) ≫ (H (p + 1)).map e.hom = 0
    have hzero : δ n ≫ (H (p + 1)).map (T n).mor₁ = 0 :=
      (H 0).homologySequenceδ_comp (T n) (hT n) p (p + 1) rfl
    rw [hzero, zero_comp]
  let φ (n : ℕ) : T (n + 1) ⟶ T n :=
    Q.mapTriangle.map (CochainComplex.mappingCone.triangleMap _ _
      (f • 𝟙 C) (𝟙 C) (by
        simp [comp_smul, smul_smul, pow_succ', mul_comm]))
  have hF (n : ℕ) : F.map (homOfLE (Nat.le_succ n)).op = (H p).map (φ n).hom₃ := by
    dsimp [F, principalDerivedTensorSystem, principalComplexSystem, φ]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    rfl
  have hδ (n : ℕ) : F.map (homOfLE (Nat.le_succ n)).op ≫ δ n =
      δ (n + 1) ≫ powerMultiplication A ((H (p + 1)).obj (Q.obj C)) f := by
    rw [hF, ← hm]
    exact (H 0).homologySequenceδ_naturality (φ n) p (p + 1) rfl
  have hd_nat (n : ℕ) : F.map (homOfLE (Nat.le_succ n)).op ≫ d n =
      d (n + 1) ≫ powerMultiplication A ((H (p + 1)).obj K) f := by
    dsimp only [d]
    rw [← Category.assoc, hδ, Category.assoc, Category.assoc, hcomm]
  let q : F ⟶ G := NatTrans.ofOpSequence
    (fun n ↦ kernel.lift _ (d n) (hd n)) (by
      intro n
      apply (cancel_mono (kernel.ι
        (powerMultiplication A ((H (p + 1)).obj K) (f ^ (n + 1))))).1
      dsimp only [G]
      rw [Category.assoc, kernel.lift_ι, Category.assoc,
        powerTorsionSystem_map_succ, powerTorsionTransition_ι, kernel.lift_ι_assoc]
      exact hd_nat n)
  have hqι (n : ℕ) : q.app ⟨n⟩ ≫
      kernel.ι (powerMultiplication A ((H (p + 1)).obj K) (f ^ (n + 1))) =
      d n := kernel.lift_ι _ _ _
  let a : (Functor.const ℕᵒᵖ).obj ((H p).obj (Q.obj C)) ⟶ F :=
    NatTrans.ofOpSequence (fun n ↦ (H p).map (T n).mor₂) (by
      intro n
      show 𝟙 _ ≫ _ = _
      rw [Category.id_comp, hF, ← Functor.map_comp]
      have h := (φ n).comm₂
      rw [show (φ n).hom₂ = 𝟙 _ from Q.map_id C, Category.id_comp] at h
      exact congrArg (H p).map h.symm)
  apply isMittagLeffler_iff_of_constant_kernel ((H p).obj (Q.obj C)) a q
  · rintro ⟨n⟩ y
    let z := (H (p + 1)).map e.inv
      (kernel.ι (powerMultiplication A ((H (p + 1)).obj K) (f ^ (n + 1))) y)
    have hz : (H (p + 1)).map (T n).mor₁ z = 0 := by
      show (H (p + 1)).map (Q.map (f ^ (n + 1) • 𝟙 C)) z = 0
      rw [hm]
      have hy := congrArg (fun g ↦ g y) (kernel.condition
        (powerMultiplication A ((H (p + 1)).obj K) (f ^ (n + 1))))
      show f ^ (n + 1) • z = 0
      dsimp only [z]
      rw [← map_smul]
      show (H (p + 1)).map e.inv
        ((powerMultiplication A ((H (p + 1)).obj K) (f ^ (n + 1)))
          ((kernel.ι (powerMultiplication A ((H (p + 1)).obj K)
            (f ^ (n + 1)))) y)) = 0
      rw [show (powerMultiplication A ((H (p + 1)).obj K) (f ^ (n + 1)))
          ((kernel.ι (powerMultiplication A ((H (p + 1)).obj K)
            (f ^ (n + 1)))) y) = 0 from hy]
      exact map_zero _
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).1
      ((H 0).homologySequence_exact₁ (T n) (hT n) p (p + 1) rfl) z hz
    refine ⟨x, ?_⟩
    apply (ModuleCat.mono_iff_injective (kernel.ι
      (powerMultiplication A ((H (p + 1)).obj K) (f ^ (n + 1))))).1
        inferInstance
    show (q.app ⟨n⟩ ≫ kernel.ι _) x = _
    rw [hqι]
    show (H (p + 1)).map e.hom (δ n x) = _
    rw [hx]
    show ((H (p + 1)).map e.inv ≫ (H (p + 1)).map e.hom) _ = _
    rw [← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]
    rfl
  · rintro ⟨n⟩ x hx
    have hd_zero : d n x = 0 := by
      rw [← hqι]
      show (kernel.ι (powerMultiplication A ((H (p + 1)).obj K)
        (f ^ (n + 1)))) (q.app ⟨n⟩ x) = 0
      rw [hx, map_zero]
    have hδ_zero : δ n x = 0 := by
      apply (ModuleCat.mono_iff_injective ((H (p + 1)).map e.hom)).1 inferInstance
      show ((H (p + 1)).map e.hom) (δ n x) = ((H (p + 1)).map e.hom) 0
      rwa [map_zero]
    exact (ShortComplex.moduleCat_exact_iff _).1
      ((H 0).homologySequence_exact₃ (T n) (hT n) p (p + 1) rfl) x hδ_zero

end MittagLeffler

end PrincipalTorsionTower

end
