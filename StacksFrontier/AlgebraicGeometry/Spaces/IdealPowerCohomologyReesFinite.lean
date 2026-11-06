module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealMultipleModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFiniteAlgebra
public import StacksFrontier.RingTheory.Filtration.IdealPowerSystemNoetherian
import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology of the modules `Iⁿ F` is a finite graded module over the Rees algebra

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` a proper morphism of algebraic
spaces and `F` a coherent `𝒪_X`-module (Situation 08AV).  [Stacks, Tag 08AW] says that for
every `p` the graded module `⨁ₙ Hᵖ(X, Iⁿ F)` is finite over the Rees algebra `B = ⨁ₙ Iⁿ`, and
[Stacks, Tag 08AX] draws the two uniform consequences used by the theorem on formal functions:
there is a `c` such that

1. `Iⁿ⁻ᶜ ⊗ Hᵖ(X, Iᶜ F) ⟶ Hᵖ(X, Iⁿ F)` is surjective for `n ≥ c`, and
2. the image of `Hᵖ(X, Iⁿ⁺ᵐ F) ⟶ Hᵖ(X, Iⁿ F)` lies in `Iᵐ⁻ᶜ Hᵖ(X, Iⁿ F)` for `m ≥ c`.

The graded module structure is that of a `Stacks.RingTheory.ReesSystem`: an element `a ∈ Iᵏ`
acts as the cohomology of multiplication by `a`, a morphism `Iⁿ F ⟶ Iᵏ⁺ⁿ F`.

The proof of 08AW is the source's.  The Rees algebra acts on `⨁ₙ Iⁿ F` (as a coproduct of
`𝒪_X`-modules), which is quasi-coherent and of finite type over `𝒪_X ⊗_A B` since `F` is
coherent; so its cohomology is finite over `B` by [Stacks, Tag 08AT].  The cohomology of the
summands embeds into it: on a finite sub-sum the coproduct is a biproduct, so
`⨁ₙ Hᵖ(X, Iⁿ F) ⟶ Hᵖ(X, ⨁ₙ Iⁿ F)` is injective, and it is `B`-linear.  A submodule of a finite
module over the Noetherian ring `B` is finite.

The proof of 08AX is the source's degree argument from finitely many homogeneous generators.

## Main definitions

* `AlgebraicGeometry.Space.cohomologyRes`: `Hᵖ(X, M)` as a module over a ring `A` mapping to
  the global functions.
* `AlgebraicGeometry.Space.cohomologyIdealPowerMul`: the multiplication map
  `Iᵏ ⊗ Hᵖ(X, Iⁿ F) ⟶ Hᵖ(X, Iᵏ⁺ⁿ F)`, as a bilinear map.
* `AlgebraicGeometry.Space.cohomologyIdealPowerSystem`: the system `n ↦ Hᵖ(X, Iⁿ F)` over
  `Hᵖ(X, F)`, as a Rees system for `⨁ₙ Iⁿ`.
* `AlgebraicGeometry.Space.reesModule` and `AlgebraicGeometry.Space.reesAction`: the
  `𝒪_X`-module `⨁ₙ Iⁿ F` and the action of the Rees algebra on it.

## Main results

* `AlgebraicGeometry.Space.isReesFinite_cohomologyIdealPowerSystem`: **[Stacks, Tag 08AW]**.
* `AlgebraicGeometry.Space.exists_surjective_cohomologyIdealPowerMul_and_range_le`:
  **[Stacks, Tag 08AX]**.

## Implementation notes

Part (1) of Tag 08AX is stated for `n = m + c`, `m ≥ 0`, which is the same range of degrees as
the source's `n ≥ c` and avoids transporting along `n - c + c = n`.

## References

* [Stacks Project, Tag 08AW](https://stacks.math.columbia.edu/tag/08AW)
* [Stacks Project, Tag 08AX](https://stacks.math.columbia.edu/tag/08AX)
* [Stacks Project, Tag 08AT](https://stacks.math.columbia.edu/tag/08AT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite DirectSum
open Stacks.Cohomology.SiteModules Stacks.Blowup Stacks.RingTheory
open scoped IsMulCommutative

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] hasInjectiveResolutions_modules

/-- The cohomology of `𝒪_X`-modules on an algebraic space is linear over the global functions. -/
instance spaceCohomology_linear (X : AlgebraicSpaces B S hS) (p : ℕ) :
    Functor.Linear ↥(GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
      (spaceCohomology B S hS X p) := by
  have := enoughInjectives_modules B S hS X.1 X.2
  exact Stacks.DerivedLinear.rightDerived_linear _ p

variable {X : AlgebraicSpaces B S hS} {A : Type u} [CommRing A]
  (φ : A →+* ↥(GlobalSectionRing
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))

/-! ### Cohomology as a module over a ring of functions -/

section CohomologyRes

variable (p : ℕ)

/-- `Hᵖ(X, M)` as an `A`-module, the action being through `φ`. -/
abbrev cohomologyRes (M : Modules.{u, u} B S hS X.1 X.2) : ModuleCat.{u + 1} A :=
  (ModuleCat.restrictScalars φ).obj ((spaceCohomology B S hS X p).obj M)

/-- The `A`-linear map `Hᵖ(X, M) ⟶ Hᵖ(X, N)` induced by `g : M ⟶ N`. -/
abbrev cohomologyResMap {M N : Modules.{u, u} B S hS X.1 X.2} (g : M ⟶ N) :
    cohomologyRes φ p M →ₗ[A] cohomologyRes φ p N :=
  ((ModuleCat.restrictScalars φ).map ((spaceCohomology B S hS X p).map g)).hom

/-- `cohomologyResMap` sends a composite `g ≫ g'` to the composite of the induced maps. -/
theorem cohomologyResMap_comp_apply {M N P : Modules.{u, u} B S hS X.1 X.2} (g : M ⟶ N)
    (g' : N ⟶ P) (x : cohomologyRes φ p M) :
    cohomologyResMap φ p g' (cohomologyResMap φ p g x) = cohomologyResMap φ p (g ≫ g') x := by
  simp only [cohomologyResMap, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The identity of `M` induces the identity of `Hᵖ(X, M)`. -/
theorem cohomologyResMap_id_apply {M : Modules.{u, u} B S hS X.1 X.2} (x : cohomologyRes φ p M) :
    cohomologyResMap φ p (𝟙 M) x = x := by
  simp only [cohomologyResMap, CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.id_apply]

/-- `cohomologyResMap` is additive in the morphism. -/
theorem cohomologyResMap_add {M N : Modules.{u, u} B S hS X.1 X.2} (g g' : M ⟶ N) :
    cohomologyResMap φ p (g + g') = cohomologyResMap φ p g + cohomologyResMap φ p g' := by
  simp only [cohomologyResMap, Functor.map_add, ModuleCat.hom_add]

/-- The zero morphism induces the zero map on cohomology. -/
theorem cohomologyResMap_zero {M N : Modules.{u, u} B S hS X.1 X.2} :
    cohomologyResMap φ p (0 : M ⟶ N) = 0 := by
  simp only [cohomologyResMap, Functor.map_zero, ModuleCat.hom_zero]

/-- The cohomology of multiplication by `φ a` is multiplication by `a`. -/
theorem cohomologyResMap_globalSmul (a : A) {M : Modules.{u, u} B S hS X.1 X.2}
    (x : cohomologyRes φ p M) :
    cohomologyResMap φ p (globalSmul _ (φ a) M) x = a • x := by
  have h : (spaceCohomology B S hS X p).map (globalSmul _ (φ a) M) = φ a • 𝟙 _ :=
    (congrArg (spaceCohomology B S hS X p).map (globalSmul_eq_smul_id _ (φ a) M)).trans <|
      (@Functor.map_smul _ _ _ _ _ _ _ _ _ _ _ (spaceCohomology_linear X p) M M (φ a) (𝟙 M)).trans
        (by rw [CategoryTheory.Functor.map_id])
  exact congrArg (fun g : (spaceCohomology B S hS X p).obj M ⟶ (spaceCohomology B S hS X p).obj M =>
    g.hom x) h

end CohomologyRes

/-! ### The multiplication maps between the modules `Iⁿ F` -/

section Multiplication

variable (F : Modules.{u, u} B S hS X.1 X.2) (I : Ideal A)

/-- For `a ∈ Iᵏ` and `m ≤ k + n`, multiplication by `a` carries `Iⁿ` into `Iᵐ`. -/
theorem mul_mem_pow_of_le {k n m : ℕ} (hm : m ≤ k + n) {a : A} (ha : a ∈ I ^ k) :
    ∀ b ∈ I ^ n, b * a ∈ I ^ m := fun b hb =>
  Ideal.pow_le_pow_right hm (by rw [pow_add]; exact mul_comm a b ▸ Ideal.mul_mem_mul ha hb)

/-- For `m ≤ n`, multiplication by `1` carries `Iⁿ` into `Iᵐ`. -/
theorem one_mem_pow_of_le {m n : ℕ} (h : m ≤ n) : ∀ b ∈ I ^ n, b * 1 ∈ I ^ m := fun b hb => by
  simpa using Ideal.pow_le_pow_right h hb

variable (p : ℕ)

/-- `Hᵖ(X, Iⁿ F)`, as an `A`-module. -/
abbrev cohomologyIdealPower (n : ℕ) : ModuleCat.{u + 1} A :=
  cohomologyRes φ p (idealMultiple φ F (I ^ n))

/-- The transition map `Hᵖ(X, Iⁿ F) ⟶ Hᵖ(X, Iᵐ F)` for `m ≤ n`. -/
abbrev cohomologyIdealPowerTr {m n : ℕ} (h : m ≤ n) :
    cohomologyIdealPower φ F I p n →ₗ[A] cohomologyIdealPower φ F I p m :=
  cohomologyResMap φ p (idealMultipleMap φ F (I ^ m) 1 (one_mem_pow_of_le I h))

/-- The map `Hᵖ(X, Iⁿ F) ⟶ Hᵖ(X, F)` induced by the inclusion. -/
abbrev cohomologyIdealPowerProj (n : ℕ) :
    cohomologyIdealPower φ F I p n →ₗ[A] cohomologyRes φ p F :=
  cohomologyResMap φ p (idealMultipleι φ F (I ^ n))

/-- Composition of the cohomology of two multiplication maps, read on elements. -/
theorem cohomologyResMap_idealMultipleMap_comp_apply {J K L : Ideal A} (a b : A)
    (h : ∀ c ∈ J, c * a ∈ K) (h' : ∀ c ∈ K, c * b ∈ L) (h'' : ∀ c ∈ J, c * (a * b) ∈ L)
    (x : cohomologyRes φ p (idealMultiple φ F J)) :
    cohomologyResMap φ p (idealMultipleMap φ F L b h')
        (cohomologyResMap φ p (idealMultipleMap φ F K a h) x) =
      cohomologyResMap φ p (idealMultipleMap φ F L (a * b) h'') x := by
  rw [cohomologyResMap_comp_apply, idealMultipleMap_comp]

/-- **The multiplication map `J ⊗ Hᵖ(X, Iⁿ F) ⟶ Hᵖ(X, Iᵏ⁺ⁿ F)`** for an ideal `J ⊆ Iᵏ`: `a ⊗ x`
goes to the cohomology class of `x` multiplied by `a`, as a bilinear map. -/
def cohomologyIdealPowerMul (k n : ℕ) {J : Ideal A} (hJ : J ≤ I ^ k) :
    ↥J →ₗ[A] cohomologyIdealPower φ F I p n →ₗ[A] cohomologyIdealPower φ F I p (k + n) where
  toFun a := cohomologyResMap φ p
    (idealMultipleMap φ F (I ^ (k + n)) (a : A) (mul_mem_pow_of_le I le_rfl (hJ a.2)))
  map_add' a a' := by
    rw [← cohomologyResMap_add, ← idealMultipleMap_add]
    exact congrArg (cohomologyResMap φ p)
      (idealMultipleMap_congr _ _ _ (Submodule.coe_add a a') _ _)
  map_smul' r a := by
    refine LinearMap.ext fun x => ?_
    have e : ((r • a : ↥J) : A) = r * (a : A) := Submodule.coe_smul r a
    refine (congrArg (fun g => cohomologyResMap φ p g x) (idealMultipleMap_congr φ F _ e _
      (fun b hb => by
        rw [← mul_assoc]
        exact mul_mem_pow_of_le I le_rfl (hJ a.2) _ (Ideal.mul_mem_right r _ hb)))).trans ?_
    rw [idealMultipleMap_mul_left φ F _ r (a : A)
      (mul_mem_pow_of_le I le_rfl (hJ a.2)), ← cohomologyResMap_comp_apply,
      cohomologyResMap_globalSmul, map_smul]
    rfl

/-- `cohomologyIdealPowerMul` sends `a ⊗ x` to the cohomology of multiplication by `a`
applied to `x`. -/
theorem cohomologyIdealPowerMul_apply {k n : ℕ} {J : Ideal A} (hJ : J ≤ I ^ k) (a : ↥J)
    (x : cohomologyIdealPower φ F I p n) :
    cohomologyIdealPowerMul φ F I p k n hJ a x = cohomologyResMap φ p
      (idealMultipleMap φ F (I ^ (k + n)) (a : A) (mul_mem_pow_of_le I le_rfl (hJ a.2))) x :=
  rfl

/-- Two multiplication maps by the same function into equal degrees agree, as elements of
`Σ n, Hᵖ(X, Iⁿ F)`. -/
theorem sigma_cohomologyResMap_idealMultipleMap_congr {J : Ideal A} {m m' : ℕ} (e : m = m')
    (a : A) (h : ∀ b ∈ J, b * a ∈ I ^ m) (h' : ∀ b ∈ J, b * a ∈ I ^ m')
    (x : cohomologyRes φ p (idealMultiple φ F J)) :
    (⟨m, cohomologyResMap φ p (idealMultipleMap φ F (I ^ m) a h) x⟩ :
        Σ j, cohomologyIdealPower φ F I p j) =
      ⟨m', cohomologyResMap φ p (idealMultipleMap φ F (I ^ m') a h') x⟩ := by
  subst e; rfl

/-- The `k`-th power of the image of `I` under the identity is contained in `Iᵏ`. -/
theorem map_id_pow_le (k : ℕ) : (I.map (RingHom.id A)) ^ k ≤ I ^ k := by
  rw [Ideal.map_id]

/-- **The system `n ↦ Hᵖ(X, Iⁿ F)` over `Hᵖ(X, F)`, as a Rees system for `⨁ₙ Iⁿ`.**  The
transition maps and the projection are induced by the inclusions `Iⁿ F ⊆ Iᵐ F ⊆ F`, and the
multiplication maps by multiplication by the elements of the powers of `I`. -/
def cohomologyIdealPowerSystem :
    ReesSystem (RingHom.id A) I (fun n => cohomologyIdealPower φ F I p n)
      (cohomologyRes φ p F) where
  tr := fun {_ _} h => cohomologyIdealPowerTr φ F I p h
  tr_tr h₁ h₂ x :=
    (cohomologyResMap_idealMultipleMap_comp_apply φ F p 1 1 _ _
      (fun c hc => by rw [mul_one]; exact one_mem_pow_of_le I (h₁.trans h₂) c hc) x).trans
      (congrArg (fun g => cohomologyResMap φ p g x)
        (idealMultipleMap_congr φ F _ (mul_one 1) _ _))
  proj n := cohomologyIdealPowerProj φ F I p n
  proj_tr h x := by
    rw [cohomologyResMap_comp_apply, idealMultipleMap_one_ι φ F (Ideal.pow_le_pow_right h)]
  mul k n := cohomologyIdealPowerMul φ F I p k n (map_id_pow_le I k)
  proj_mul k n a x := by
    rw [cohomologyIdealPowerMul_apply, cohomologyResMap_comp_apply, idealMultipleMap_ι,
      ← cohomologyResMap_comp_apply, cohomologyResMap_globalSmul]
  tr_mul_of_proj_eq_zero k n a x hx := by
    have ha : (a : A) ∈ I ^ k := map_id_pow_le I k a.2
    have key : idealMultipleMap φ F (I ^ (k + n)) (a : A) (mul_mem_pow_of_le I le_rfl ha) ≫
        idealMultipleMap φ F (I ^ k) 1 (one_mem_pow_of_le I (Nat.le_add_right k n)) =
        idealMultipleι φ F (I ^ n) ≫ idealMultipleFactor φ F (I ^ k) ha := by
      refine (cancel_mono (idealMultipleι φ F (I ^ k))).1 ?_
      simp only [Category.assoc, idealMultipleMap_ι,
        idealMultipleFactor_ι, map_one, globalSmul_one, Category.comp_id]
    rw [cohomologyIdealPowerMul_apply]
    refine (cohomologyResMap_comp_apply φ p _ _ x).trans ?_
    rw [key, ← cohomologyResMap_comp_apply]
    refine (congrArg (cohomologyResMap φ p (idealMultipleFactor φ F (I ^ k) ha)) hx).trans ?_
    exact map_zero _
  tr_of_eq := fun {_ _} h e x => by
    subst e
    refine congrArg (Sigma.mk _) ?_
    refine (congrArg (fun g => cohomologyResMap φ p g x)
      (idealMultipleMap_one φ F (one_mem_pow_of_le I h))).trans ?_
    exact cohomologyResMap_id_apply φ p x
  mul_zero_eq_smul n a x := by
    refine (sigma_cohomologyResMap_idealMultipleMap_congr φ F I p (Nat.zero_add n) (a : A)
      _ (mul_mem_pow_of_le I (Nat.le_add_left n 0) a.2) x).trans (congrArg (Sigma.mk n) ?_)
    rw [idealMultipleMap_self, cohomologyResMap_globalSmul]
    rfl
  mul_mul k l n a b c x hc := by
    have hassoc : k + (l + n) ≤ k + l + n := le_of_eq (Nat.add_assoc k l n).symm
    refine (sigma_cohomologyResMap_idealMultipleMap_congr φ F I p (Nat.add_assoc k l n) (c : A)
      _ (mul_mem_pow_of_le I hassoc c.2) x).trans (congrArg (Sigma.mk (k + (l + n))) ?_)
    refine Eq.trans ?_ (cohomologyResMap_idealMultipleMap_comp_apply φ F p (b : A) (a : A)
      (mul_mem_pow_of_le I le_rfl b.2) (mul_mem_pow_of_le I le_rfl a.2)
      (mul_mem_pow_of_le I hassoc (hc.trans (mul_comm _ _) ▸ c.2)) x).symm
    exact congrArg (fun g => cohomologyResMap φ p g x)
      (idealMultipleMap_congr φ F _ (hc.trans (mul_comm _ _)) _ _)

end Multiplication

/-! ### The Rees module `⨁ₙ Iⁿ F` and the action of the Rees algebra -/

section ReesModule

variable (F : Modules.{u, u} B S hS X.1 X.2) (I : Ideal A)

/-- **The `𝒪_X`-module `⨁ₙ Iⁿ F`**, the coproduct of the modules `Iⁿ F`. -/
abbrev reesModule : Modules.{u, u} B S hS X.1 X.2 :=
  ∐ fun n : ℕ => idealMultiple φ F (I ^ n)

/-- The element of `Iⁱ` underlying a homogeneous element of degree `i` of the Rees algebra. -/
abbrev reesCoeff {i : ℕ} (b : ↥(reesGrading I i)) : A :=
  ((reesGradingEquivPow I i).symm b : A)

/-- The element underlying a homogeneous element of degree `i` lies in `Iⁱ`. -/
theorem reesCoeff_mem {i : ℕ} (b : ↥(reesGrading I i)) : reesCoeff I b ∈ I ^ i :=
  ((reesGradingEquivPow I i).symm b).2

/-- Multiplication by a homogeneous element `b` of degree `i` of the Rees algebra on
`⨁ₙ Iⁿ F`: on the summand `Iⁿ F` it is multiplication by the underlying element of `Iⁱ`, landing
in the summand `Iⁱ⁺ⁿ F`. -/
def reesShift (i : ℕ) (b : ↥(reesGrading I i)) : reesModule φ F I ⟶ reesModule φ F I :=
  Sigma.desc fun n => idealMultipleMap φ F (I ^ (i + n)) (reesCoeff I b)
    (mul_mem_pow_of_le I le_rfl (reesCoeff_mem I b)) ≫
      Sigma.ι (fun n => idealMultiple φ F (I ^ n)) (i + n)

/-- On the summand `Iⁿ F`, `reesShift` is multiplication by the underlying element of `Iⁱ`
followed by the inclusion of the summand `Iⁱ⁺ⁿ F`. -/
@[reassoc]
theorem ι_reesShift (i n : ℕ) (b : ↥(reesGrading I i)) :
    Sigma.ι (fun n => idealMultiple φ F (I ^ n)) n ≫ reesShift φ F I i b =
      idealMultipleMap φ F (I ^ (i + n)) (reesCoeff I b)
        (mul_mem_pow_of_le I le_rfl (reesCoeff_mem I b)) ≫
        Sigma.ι (fun n => idealMultiple φ F (I ^ n)) (i + n) :=
  Sigma.ι_desc _ _

/-- A multiplication map into a summand of `⨁ₙ Iⁿ F` depends only on the function and on the
degree of the summand. -/
theorem idealMultipleMap_comp_ι_congr {J : Ideal A} {m m' : ℕ} (e : m = m') {a a' : A}
    (ea : a = a') (h : ∀ b ∈ J, b * a ∈ I ^ m) (h' : ∀ b ∈ J, b * a' ∈ I ^ m') :
    idealMultipleMap φ F (I ^ m) a h ≫ Sigma.ι (fun n => idealMultiple φ F (I ^ n)) m =
      idealMultipleMap φ F (I ^ m') a' h' ≫ Sigma.ι (fun n => idealMultiple φ F (I ^ n)) m' := by
  subst e ea; rfl

/-- `reesShift` is additive in the homogeneous element. -/
theorem reesShift_add (i : ℕ) (b b' : ↥(reesGrading I i)) :
    reesShift φ F I i (b + b') = reesShift φ F I i b + reesShift φ F I i b' := by
  refine Sigma.hom_ext _ _ fun n => ?_
  rw [Preadditive.comp_add, ι_reesShift, ι_reesShift, ι_reesShift, ← Preadditive.add_comp,
    ← idealMultipleMap_add]
  exact idealMultipleMap_comp_ι_congr φ F I rfl
    (by rw [reesCoeff, LinearEquiv.map_add]; rfl) _ _

/-- Multiplication by the zero element of degree `i` is zero. -/
theorem reesShift_zero (i : ℕ) : reesShift φ F I i 0 = 0 := by
  refine Sigma.hom_ext _ _ fun n => ?_
  rw [comp_zero, ι_reesShift]
  rw [idealMultipleMap_congr φ F _ (show reesCoeff I (0 : ↥(reesGrading I i)) = 0 by
    rw [reesCoeff, LinearEquiv.map_zero]; rfl) _ (fun b _ => by rw [mul_zero]; exact Submodule.zero_mem _),
    idealMultipleMap_zero, zero_comp]

/-- `reesShift` as an additive map in the homogeneous element. -/
def reesShiftHom (i : ℕ) : ↥(reesGrading I i) →+ End (reesModule φ F I) where
  toFun b := End.of (reesShift φ F I i b)
  map_zero' := End.ext (reesShift_zero φ F I i)
  map_add' b b' := End.ext (reesShift_add φ F I i b b')

/-- The element underlying the unit of the graded Rees algebra is `1`. -/
theorem reesCoeff_one :
    reesCoeff I (GradedMonoid.GOne.one (A := fun n => ↥(reesGrading I n))) = 1 := by
  rw [reesCoeff, coe_reesGradingEquivPow_symm]
  simp

/-- Multiplication by the unit of the graded Rees algebra is the identity of `⨁ₙ Iⁿ F`. -/
theorem reesShift_one :
    reesShift φ F I 0 (GradedMonoid.GOne.one (A := fun n => ↥(reesGrading I n))) = 𝟙 _ := by
  refine Sigma.hom_ext _ _ fun n => ?_
  rw [ι_reesShift, Category.comp_id]
  refine (idealMultipleMap_comp_ι_congr φ F I (Nat.zero_add n) (reesCoeff_one I) _
    (one_mem_pow_of_le I le_rfl)).trans ?_
  rw [idealMultipleMap_one, Category.id_comp]

/-- Multiplication by a product `b * b'` of homogeneous elements is multiplication by `b'`
followed by multiplication by `b`. -/
theorem reesShift_mul {i j : ℕ} (b : ↥(reesGrading I i)) (b' : ↥(reesGrading I j)) :
    reesShift φ F I (i + j) (GradedMonoid.GMul.mul (A := fun n => ↥(reesGrading I n)) b b') =
      reesShift φ F I j b' ≫ reesShift φ F I i b := by
  refine Sigma.hom_ext _ _ fun n => ?_
  rw [ι_reesShift, ι_reesShift_assoc, ι_reesShift, idealMultipleMap_comp_assoc]
  exact idealMultipleMap_comp_ι_congr φ F I (Nat.add_assoc i j n)
    ((ReesSystem.coe_symm_gMul (I := I) b b').trans (mul_comm _ _)) _ _

/-- **The action of the graded Rees algebra `⨁ₙ Iⁿ` on `⨁ₙ Iⁿ F`.** -/
def reesActionHom : (⨁ n, ↥(reesGrading I n)) →+* End (reesModule φ F I) :=
  DirectSum.toSemiring (reesShiftHom φ F I) (End.ext (reesShift_one φ F I))
    (fun b b' => End.ext (reesShift_mul φ F I b b'))

/-- A homogeneous element `b` of degree `i` acts on `⨁ₙ Iⁿ F` by `reesShift`. -/
theorem reesActionHom_of {i : ℕ} (b : ↥(reesGrading I i)) :
    reesActionHom φ F I (DirectSum.of _ i b) = End.of (reesShift φ F I i b) :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- **The action of the Rees algebra `A[It]` on `⨁ₙ Iⁿ F`**, through its homogeneous
decomposition. -/
def reesAction : reesAlgebra I →+* End (reesModule φ F I) :=
  (reesActionHom φ F I).comp (DirectSum.decomposeRingEquiv (reesGrading I)).toRingHom

/-- On the elements of `A` the action of the Rees algebra is multiplication by the functions. -/
theorem reesAction_algebraMap (a : A) :
    reesAction φ F I (algebraMap A (reesAlgebra I) a) =
      End.of (globalSmul _ (φ a) (reesModule φ F I)) := by
  let b : ↥(reesGrading I 0) := ⟨algebraMap A (reesAlgebra I) a,
    SetLike.algebraMap_mem_graded (reesGrading I) a⟩
  have hb : reesCoeff I b = a := by
    rw [reesCoeff, coe_reesGradingEquivPow_symm]
    simp [b]
  show reesActionHom φ F I (DirectSum.decompose (reesGrading I) (b : reesAlgebra I)) = _
  rw [DirectSum.decompose_coe, reesActionHom_of]
  congr 1
  refine Sigma.hom_ext _ _ fun n => ?_
  rw [ι_reesShift, comp_globalSmul]
  refine (idealMultipleMap_comp_ι_congr φ F I (Nat.zero_add n) hb _
    (mul_mem_pow_of_le I (Nat.le_add_left n 0) (by simp))).trans ?_
  rw [idealMultipleMap_self]

/-- `1 ∈ I⁰`. -/
theorem one_mem_pow_zero : (1 : A) ∈ I ^ 0 := by
  simp

/-- The inclusion of `F = I⁰ F` as the degree-zero summand of `⨁ₙ Iⁿ F`. -/
abbrev reesDegreeZero : F ⟶ reesModule φ F I :=
  idealMultipleFactor φ F (I ^ 0) (one_mem_pow_zero I) ≫
    Sigma.ι (fun n => idealMultiple φ F (I ^ n)) 0

/-- Multiplication by `a ∈ Iⁿ`, read in degree `n` of the Rees algebra, carries the degree-zero
copy of `F` to the multiples by `a` in degree `n`. -/
theorem reesDegreeZero_reesShift (n : ℕ) {a : A} (ha : a ∈ I ^ n) :
    reesDegreeZero φ F I ≫ reesShift φ F I n (reesGradingEquivPow I n ⟨a, ha⟩) =
      idealMultipleFactor φ F (I ^ n) ha ≫ Sigma.ι (fun n => idealMultiple φ F (I ^ n)) n := by
  rw [Category.assoc, ι_reesShift, ← Category.assoc]
  have hc : reesCoeff I (reesGradingEquivPow I n ⟨a, ha⟩) = a := by
    simp [reesCoeff]
  have h1 : idealMultipleFactor φ F (I ^ 0) (one_mem_pow_zero I) ≫
      idealMultipleMap φ F (I ^ (n + 0)) (reesCoeff I (reesGradingEquivPow I n ⟨a, ha⟩))
        (mul_mem_pow_of_le I le_rfl (reesCoeff_mem I _)) =
      idealMultipleFactor φ F (I ^ (n + 0)) ha := by
    refine (cancel_mono (idealMultipleι φ F _)).1 ?_
    rw [Category.assoc, idealMultipleMap_ι, idealMultipleFactor_ι_assoc, ← globalSmul_mul,
      idealMultipleFactor_ι, map_one, one_mul, hc]
  rw [h1]
  rfl

/-- **`⨁ₙ Iⁿ F` is of finite type over the Rees algebra.**  For `F` coherent and an affine étale
chart `U` of `X`, the sections of `⨁ₙ Iⁿ F` over `U` are generated over `𝒪(U)` by the
translates under the Rees algebra of finitely many sections in degree zero: the images of
generators of `F(U)`. -/
theorem exists_finset_span_reesAction_eq_top (hF : IsCoherent B S hS X.1 X.2 F)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    ∃ g : Finset ((reesModule φ F I).val.obj (op U)),
      Submodule.span (chartRing B S hS X.1 X.2 U)
        {x | ∃ r, ∃ y ∈ g, x = (reesAction φ F I r).asHom.val.app (op U) y} = ⊤ := by
  classical
  have := moduleFinite_sections_of_isCoherent B S hS X.1 X.2 F hF hU
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := chartRing B S hS X.1 X.2 U)
    (M := F.val.obj (op U))
  refine ⟨s.image fun t => (reesDegreeZero φ F I).val.app (op U) t, ?_⟩
  set P := Submodule.span (chartRing B S hS X.1 X.2 U)
    {x | ∃ r, ∃ y ∈ s.image fun t => (reesDegreeZero φ F I).val.app (op U) t,
      x = (reesAction φ F I r).asHom.val.app (op U) y}
  have key : ∀ (n : ℕ) (a : A) (ha : a ∈ I ^ n) (t : F.val.obj (op U)),
      (idealMultipleFactor φ F (I ^ n) ha ≫
        Sigma.ι (fun n => idealMultiple φ F (I ^ n)) n).val.app (op U) t ∈ P := by
    intro n a ha t
    have ht : t ∈ Submodule.span (chartRing B S hS X.1 X.2 U) (s : Set (F.val.obj (op U))) :=
      hs ▸ Submodule.mem_top
    induction ht using Submodule.span_induction with
    | mem t ht =>
      refine Submodule.subset_span ⟨(DirectSum.decomposeRingEquiv (reesGrading I)).symm
        (DirectSum.of _ n (reesGradingEquivPow I n ⟨a, ha⟩)), _,
        Finset.mem_image_of_mem _ ht, ?_⟩
      have hr : reesAction φ F I ((DirectSum.decomposeRingEquiv (reesGrading I)).symm
          (DirectSum.of _ n (reesGradingEquivPow I n ⟨a, ha⟩))) =
          End.of (reesShift φ F I n (reesGradingEquivPow I n ⟨a, ha⟩)) := by
        rw [reesAction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          RingEquiv.apply_symm_apply, reesActionHom_of]
      rw [hr, ← reesDegreeZero_reesShift φ F I n ha]
      rfl
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul γ x _ hx => rw [map_smul]; exact Submodule.smul_mem _ γ hx
  rw [eq_top_iff]
  rintro y -
  obtain ⟨z, rfl⟩ := (Stacks.Sites.bijective_coproductSectionsMap _
    (coproductIsCoproduct fun n : ℕ => idealMultiple φ F (I ^ n)) U
    (isQuasiCompactObject_of_isAffine B S hS X.1 U hU)).2 y
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | of n t =>
    rw [← DirectSum.lof_eq_of (R := ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj (op U)),
      Stacks.Sites.coproductSectionsMap_lof
        (Cofan.mk _ (Sigma.ι fun n : ℕ => idealMultiple φ F (I ^ n))) (op U) n t]
    have ht : t ∈ Submodule.span (chartRing B S hS X.1 X.2 U)
        {t | ∃ (a : A) (ha : a ∈ I ^ n) (s : F.val.obj (op U)),
          t = (idealMultipleFactor φ F (I ^ n) ha).val.app (op U) s} :=
      (span_idealMultipleFactor_sections φ F (I ^ n) hF.toIsQuasicoherentOnSite U hU) ▸
        Submodule.mem_top
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨a, ha, t', rfl⟩ := ht
      exact key n a ha t'
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul γ x _ hx => rw [map_smul]; exact Submodule.smul_mem _ γ hx
  | add z z' hz hz' => rw [map_add]; exact Submodule.add_mem _ hz hz'

/-- `⨁ₙ Iⁿ F` is quasi-coherent when `F` is. -/
theorem isQuasicoherentOnSite_reesModule (hF : F.IsQuasicoherentOnSite) :
    (reesModule φ F I).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_coproduct_of_isCartesian B S hS X.1 X.2 _
    (coproductIsCoproduct fun n : ℕ => idealMultiple φ F (I ^ n)) fun n =>
      isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 _
        (isQuasicoherentOnSite_idealMultiple φ F (I ^ n) hF)

end ReesModule

/-! ### The cohomology of the summands inside the cohomology of `⨁ₙ Iⁿ F` -/

section Comparison

variable (F : Modules.{u, u} B S hS X.1 X.2) (I : Ideal A) (p : ℕ)

/-- **The comparison `⨁ₙ Hᵖ(X, Iⁿ F) ⟶ Hᵖ(X, ⨁ₙ Iⁿ F)`**, the sum of the cohomology of the
coproduct inclusions. -/
def cohomologyReesComparison :
    (⨁ n, cohomologyIdealPower φ F I p n) →ₗ[A] cohomologyRes φ p (reesModule φ F I) :=
  DirectSum.toModule A ℕ (cohomologyRes φ p (reesModule φ F I)) fun n =>
    cohomologyResMap φ p (Sigma.ι (fun n => idealMultiple φ F (I ^ n)) n)

/-- On the summand `Hᵖ(X, Iⁿ F)`, the comparison is the cohomology of the inclusion of `Iⁿ F`
into `⨁ₙ Iⁿ F`. -/
theorem cohomologyReesComparison_of (n : ℕ) (x : cohomologyIdealPower φ F I p n) :
    cohomologyReesComparison φ F I p (DirectSum.of _ n x) =
      cohomologyResMap φ p (Sigma.ι (fun n => idealMultiple φ F (I ^ n)) n) x := by
  rw [← DirectSum.lof_eq_of A, cohomologyReesComparison, DirectSum.toModule_lof]

/-- The cohomology of the projection of `⨁ₙ Iⁿ F` onto a summand reads off the corresponding
component. -/
theorem cohomologyReesComparison_π (y : ⨁ n, cohomologyIdealPower φ F I p n) (m : ℕ) :
    cohomologyResMap φ p (Sigma.π (fun n => idealMultiple φ F (I ^ n)) m)
      (cohomologyReesComparison φ F I p y) = y m := by
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]; rfl
  | of n x =>
    rw [cohomologyReesComparison_of, cohomologyResMap_comp_apply]
    by_cases h : n = m
    · subst h
      rw [Sigma.ι_π_eq_id, cohomologyResMap_id_apply, DirectSum.of_eq_same]
    · rw [Sigma.ι_π_of_ne _ h, cohomologyResMap_zero, LinearMap.zero_apply,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', DirectSum.add_apply]

/-- **`⨁ₙ Hᵖ(X, Iⁿ F) ⟶ Hᵖ(X, ⨁ₙ Iⁿ F)` is injective**: each component is recovered through the
projection onto the corresponding summand. -/
theorem cohomologyReesComparison_injective :
    Function.Injective (cohomologyReesComparison φ F I p) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => DFinsupp.ext fun m => ?_
  rw [← cohomologyReesComparison_π φ F I p y m, hy, map_zero]
  rfl

/-- **The comparison is linear over the Rees algebra**, acting on the source by the graded
module structure of `cohomologyIdealPowerSystem` and on the target through its action on
`⨁ₙ Iⁿ F`. -/
theorem cohomologyReesComparison_smul (b : ⨁ n, ↥(reesGrading I n))
    (y : ⨁ n, cohomologyIdealPower φ F I p n) :
    letI := (cohomologyIdealPowerSystem φ F I p).gmodule
    cohomologyReesComparison φ F I p (b • y) =
      cohomologyResMap φ p (reesActionHom φ F I b).asHom
        (cohomologyReesComparison φ F I p y) := by
  let := (cohomologyIdealPowerSystem φ F I p).gmodule
  induction b using DirectSum.induction_on with
  | zero => rw [zero_smul, map_zero, map_zero, End.zero_asHom, cohomologyResMap_zero]; rfl
  | of i b =>
    induction y using DirectSum.induction_on with
    | zero => rw [smul_zero, map_zero, map_zero]
    | of j x =>
      rw [DirectSum.Gmodule.of_smul_of, cohomologyReesComparison_of, cohomologyReesComparison_of,
        reesActionHom_of]
      dsimp only
      rw [cohomologyResMap_comp_apply, ι_reesShift,
        ← cohomologyResMap_comp_apply]
      rfl
    | add y y' hy hy' => rw [smul_add, map_add, hy, hy', map_add, map_add]
  | add b b' hb hb' =>
    rw [add_smul, map_add, hb, hb', RingHom.map_add, End.add_asHom, cohomologyResMap_add]
    rfl

end Comparison

/-! ### The uniform bounds from finitely many homogeneous generators -/

section UniformBounds

variable (F : Modules.{u, u} B S hS X.1 X.2) (I : Ideal A) (p : ℕ)

/-- Multiplication by `a ∈ Iᵏ` on cohomology, as an `A`-linear map
`Hᵖ(X, Iᵈ F) ⟶ Hᵖ(X, Iᴺ F)` for `N ≤ k + d`. -/
abbrev cohomologyIdealPowerSmul {d N k : ℕ} (hk : N ≤ k + d) (a : A) (ha : a ∈ I ^ k) :
    cohomologyIdealPower φ F I p d →ₗ[A] cohomologyIdealPower φ F I p N :=
  cohomologyResMap φ p (idealMultipleMap φ F (I ^ N) a (mul_mem_pow_of_le I hk ha))

/-- `cohomologyIdealPowerSmul` is additive in the multiplier. -/
theorem cohomologyIdealPowerSmul_add {d N k : ℕ} (hk : N ≤ k + d) {a a' : A} (ha : a ∈ I ^ k)
    (ha' : a' ∈ I ^ k) (x : cohomologyIdealPower φ F I p d) :
    cohomologyIdealPowerSmul φ F I p hk (a + a') (Ideal.add_mem _ ha ha') x =
      cohomologyIdealPowerSmul φ F I p hk a ha x +
        cohomologyIdealPowerSmul φ F I p hk a' ha' x := by
  rw [cohomologyIdealPowerSmul, idealMultipleMap_add φ F (I ^ N) a a'
    (mul_mem_pow_of_le I hk ha) (mul_mem_pow_of_le I hk ha'), cohomologyResMap_add]
  rfl

/-- Multiplication by `a` followed by multiplication by `b` is multiplication by `a * b`. -/
theorem cohomologyIdealPowerSmul_comp {d e N k l : ℕ} (hk : e ≤ k + d) (hl : N ≤ l + e)
    (hkl : N ≤ (k + l) + d) {a b : A} (ha : a ∈ I ^ k) (hb : b ∈ I ^ l)
    (x : cohomologyIdealPower φ F I p d) :
    cohomologyIdealPowerSmul φ F I p hl b hb (cohomologyIdealPowerSmul φ F I p hk a ha x) =
      cohomologyIdealPowerSmul φ F I p hkl (a * b)
        (by rw [pow_add]; exact Ideal.mul_mem_mul ha hb) x :=
  cohomologyResMap_idealMultipleMap_comp_apply φ F p a b _ _ _ x

/-- `cohomologyIdealPowerSmul` depends only on the multiplier. -/
theorem cohomologyIdealPowerSmul_congr {d N k : ℕ} (hk : N ≤ k + d) {a a' : A} (e : a = a')
    (ha : a ∈ I ^ k) (ha' : a' ∈ I ^ k) :
    cohomologyIdealPowerSmul φ F I p hk a ha = cohomologyIdealPowerSmul φ F I p hk a' ha' := by
  subst e; rfl

/-- Multiplication by `a` from `Hᵖ(X, Iᵈ F)` to itself is the scalar action of `a`. -/
theorem cohomologyIdealPowerSmul_self {d k : ℕ} (hk : d ≤ k + d) {a : A} (ha : a ∈ I ^ k)
    (x : cohomologyIdealPower φ F I p d) :
    cohomologyIdealPowerSmul φ F I p hk a ha x = a • x := by
  rw [cohomologyIdealPowerSmul, idealMultipleMap_self, cohomologyResMap_globalSmul]

/-- Multiplication by `a` followed by the transition map is multiplication by `a`. -/
private theorem cohomologyIdealPowerTr_smul {d N N' k : ℕ} (h : N ≤ N') (hk : N' ≤ k + d)
    (hk' : N ≤ k + d) {a : A} (ha : a ∈ I ^ k) (x : cohomologyIdealPower φ F I p d) :
    cohomologyIdealPowerTr φ F I p h (cohomologyIdealPowerSmul φ F I p hk a ha x) =
      cohomologyIdealPowerSmul φ F I p hk' a ha x := by
  have htr : ∀ z, cohomologyIdealPowerTr φ F I p h z =
      cohomologyIdealPowerSmul φ F I p (show N ≤ 0 + N' by omega) 1 (one_mem_pow_zero I) z :=
    fun _ => rfl
  rw [htr, cohomologyIdealPowerSmul_comp φ F I p _ _ (show N ≤ (k + 0) + d by omega),
    cohomologyIdealPowerSmul_congr φ F I p _ (mul_one a) _ ha]

/-- If multiplication of `w` by `g * e` lands in `P` for all `g ∈ J`, `e ∈ K`, then so does
multiplication by every element of `J * K`. -/
private theorem cohomologyIdealPowerSmul_mem_of_mem_mul {d N k : ℕ} (hk : N ≤ k + d)
    {J K : Ideal A} (hJK : J * K ≤ I ^ k) (P : Submodule A (cohomologyIdealPower φ F I p N))
    (w : cohomologyIdealPower φ F I p d)
    (h : ∀ g (hg : g ∈ J) e (he : e ∈ K),
      cohomologyIdealPowerSmul φ F I p hk (g * e) (hJK (Ideal.mul_mem_mul hg he)) w ∈ P)
    {r : A} (hr : r ∈ J * K) : cohomologyIdealPowerSmul φ F I p hk r (hJK hr) w ∈ P := by
  induction hr using Submodule.mul_induction_on' with
  | mem_mul_mem g hg e he => exact h g hg e he
  | add r hr r' hr' h h' =>
    rw [cohomologyIdealPowerSmul_add φ F I p _ (hJK hr) (hJK hr')]
    exact Submodule.add_mem _ h h'

/-- **The degree argument.**  If `⨁ₙ Hᵖ(X, Iⁿ F)` is generated by homogeneous elements of
degrees at most `c`, then every element of `Hᵖ(X, Iᴺ F)`, `N ≥ c`, is a sum of multiples by
elements of `Iᴺ⁻ᶜ` of elements of `Hᵖ(X, Iᶜ F)`. -/
theorem mem_span_cohomologyIdealPowerSmul {t c : ℕ} (d : Fin t → ℕ)
    (x : ∀ i, cohomologyIdealPower φ F I p (d i)) (hd : ∀ i, d i ≤ c)
    (hgen : ∀ n, (⊤ : Submodule A (cohomologyIdealPower φ F I p n)) ≤
      (cohomologyIdealPowerSystem φ F I p).genSubmodule d x n)
    {N : ℕ} (hcN : c ≤ N) (y : cohomologyIdealPower φ F I p N) :
    y ∈ Submodule.span A {z | ∃ (a : A) (ha : a ∈ I ^ (N - c))
      (w : cohomologyIdealPower φ F I p c),
        z = cohomologyIdealPowerSmul φ F I p (show N ≤ (N - c) + c by omega) a ha w} := by
  set P := Submodule.span A {z | ∃ (a : A) (ha : a ∈ I ^ (N - c))
      (w : cohomologyIdealPower φ F I p c),
        z = cohomologyIdealPowerSmul φ F I p (show N ≤ (N - c) + c by omega) a ha w}
  refine (iSup_le fun i => Submodule.span_le.2 ?_) (hgen N Submodule.mem_top)
  rintro _ ⟨a, rfl⟩
  have ha : (a : A) ∈ I ^ (N - d i) := map_id_pow_le I _ a.2
  have hN : N ≤ (N - d i) + d i := by omega
  change cohomologyIdealPowerTr φ F I p hN
    (cohomologyIdealPowerSmul φ F I p le_rfl (a : A) ha (x i)) ∈ P
  rw [cohomologyIdealPowerTr_smul φ F I p hN le_rfl hN ha]
  have hJK : I ^ (c - d i) * I ^ (N - c) ≤ I ^ (N - d i) := by
    rw [← pow_add, show c - d i + (N - c) = N - d i by have := hd i; omega]
  refine cohomologyIdealPowerSmul_mem_of_mem_mul φ F I p _ hJK P (x i) (fun g hg e he => ?_)
    (show (a : A) ∈ _ from by
      rw [← pow_add, show c - d i + (N - c) = N - d i by have := hd i; omega]; exact ha)
  rw [← cohomologyIdealPowerSmul_comp φ F I p (show c ≤ (c - d i) + d i by omega)
    (show N ≤ (N - c) + c by omega) (by have := hd i; omega) hg he]
  exact Submodule.subset_span ⟨e, he, _, rfl⟩

/-- **The uniform bounds from finiteness over the Rees algebra.**  If `⨁ₙ Hᵖ(X, Iⁿ F)` is a finite
module over the Rees algebra of an ideal `I` of a Noetherian ring, there is a `c` such that
`Iᵐ ⊗ Hᵖ(X, Iᶜ F) ⟶ Hᵖ(X, Iᵐ⁺ᶜ F)` is surjective for all `m`, and the image of
`Hᵖ(X, Iᴺ F) ⟶ Hᵖ(X, Iⁿ F)` lies in `Iᴺ⁻ⁿ⁻ᶜ Hᵖ(X, Iⁿ F)` whenever `n + c ≤ N`. -/
theorem exists_cohomologyIdealPower_bounds_of_isReesFinite
    [IsNoetherianRing A] (h : (cohomologyIdealPowerSystem φ F I p).IsReesFinite) :
    ∃ c : ℕ, (∀ m : ℕ, Function.Surjective
        (TensorProduct.lift (cohomologyIdealPowerMul φ F I p m c le_rfl))) ∧
      ∀ (n N : ℕ) (hnN : n ≤ N), n + c ≤ N →
        LinearMap.range (cohomologyIdealPowerTr φ F I p hnN) ≤
          I ^ (N - n - c) • (⊤ : Submodule A (cohomologyIdealPower φ F I p n)) := by
  obtain ⟨t, d, x, -, hgen⟩ := ReesSystem.isNoetherianSystem_of_isReesFinite _ h
    (IdealPowerSystem.topSubsystem _)
  set c := Finset.univ.sup d
  have hd : ∀ i, d i ≤ c := fun i => Finset.le_sup (Finset.mem_univ i)
  have hspan : ∀ {N : ℕ} (hcN : c ≤ N) (y : cohomologyIdealPower φ F I p N), _ :=
    fun {N} hcN y => mem_span_cohomologyIdealPowerSmul φ F I p d x hd hgen (N := N) hcN y
  refine ⟨c, fun m => ?_, fun n N hnN hcN => ?_⟩
  · rw [← LinearMap.range_eq_top]
    refine eq_top_iff.2 fun y _ => ?_
    refine Submodule.span_le.2 ?_ (hspan (by omega : c ≤ m + c) y)
    rintro _ ⟨a, ha, w, rfl⟩
    have ha' : a ∈ I ^ m := by rwa [Nat.add_sub_cancel] at ha
    exact ⟨⟨a, ha'⟩ ⊗ₜ w, by rw [TensorProduct.lift.tmul]; rfl⟩
  · rintro _ ⟨y, rfl⟩
    have hy := hspan (show c ≤ N by omega) y
    set T := I ^ (N - n - c) • (⊤ : Submodule A (cohomologyIdealPower φ F I p n))
    refine (Submodule.span_le.2 ?_ : _ ≤ Submodule.comap
      (cohomologyIdealPowerTr φ F I p hnN) T) hy
    rintro _ ⟨a, ha, w, rfl⟩
    have hJK : I ^ n * I ^ (N - n - c) ≤ I ^ (N - c) := by
      rw [← pow_add, show n + (N - n - c) = N - c by omega]
    show cohomologyIdealPowerTr φ F I p hnN _ ∈ T
    rw [cohomologyIdealPowerTr_smul φ F I p hnN _ (show n ≤ (N - c) + c by omega)]
    refine cohomologyIdealPowerSmul_mem_of_mem_mul φ F I p _ hJK T w (fun g hg e he => ?_)
      (show a ∈ _ from by rw [← pow_add, show n + (N - n - c) = N - c by omega]; exact ha)
    rw [← cohomologyIdealPowerSmul_comp φ F I p (show n ≤ n + c by omega)
      (show n ≤ (N - n - c) + n by omega) (by omega) hg he, cohomologyIdealPowerSmul_self]
    exact Submodule.smul_mem_smul he Submodule.mem_top

/-- **Stacks 08AX from finiteness over the Rees algebra**, in the source's form. -/
theorem exists_surjective_cohomologyIdealPowerMul_and_range_le_of_isReesFinite
    [IsNoetherianRing A] (h : (cohomologyIdealPowerSystem φ F I p).IsReesFinite) :
    ∃ c : ℕ, (∀ m : ℕ, Function.Surjective
        (TensorProduct.lift (cohomologyIdealPowerMul φ F I p m c le_rfl))) ∧
      ∀ n m : ℕ, c ≤ m →
        LinearMap.range (cohomologyIdealPowerTr φ F I p (Nat.le_add_right n m)) ≤
          I ^ (m - c) • (⊤ : Submodule A (cohomologyIdealPower φ F I p n)) := by
  obtain ⟨c, h1, h2⟩ := exists_cohomologyIdealPower_bounds_of_isReesFinite φ F I p h
  refine ⟨c, h1, fun n m hm => ?_⟩
  have := h2 n (n + m) (Nat.le_add_right n m) (by omega)
  rwa [show n + m - n - c = m - c by omega] at this

end UniformBounds

end AlgebraicGeometry.Space

/-! ### Stacks 08AW and 08AX over an affine object of the site -/

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules

section OverAffine

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {V : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] {A : Type u} [CommRing A]
  (α : A ≃+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {X : AlgebraicSpaces B S hS}

/-- The cohomology of `⨁ₙ Iⁿ F` is a finite module over the Rees algebra, by Stacks 08AT, for a
proper morphism to an affine object `V` of the site whose functions are identified with the
Noetherian ring `A` by `α`; `φ` is the resulting map from `A` to the global functions of `X`. -/
theorem moduleFinite_cohomology_reesModule_of_isAffine [IsNoetherianRing A]
    (f : X ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)
    (φ : A →+* ↥(GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
    (hφ : ∀ a, φ a = pullbackToGlobalFunctions B S hS X V f (α a))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (I : Ideal A) (p : ℕ) :
    letI := (spaceCohomology B S hS X p).endActionModule (reesActionHom φ F I)
    Module.Finite (⨁ n, ↥(reesGrading I n))
      ((spaceCohomology B S hS X p).obj (reesModule φ F I)) := by
  have h := moduleFinite_cohomology_of_isProper_of_algebra_of_isAffine B S hS A α (reesAlgebra I)
    f hf (reesModule φ F I) (isQuasicoherentOnSite_reesModule _ F I hF.toIsQuasicoherentOnSite)
    (reesAction φ F I) (fun a => by rw [reesAction_algebraMap, hφ])
    (fun U hU => exists_finset_span_reesAction_eq_top _ F I hF U hU) p
  let := (spaceCohomology B S hS X p).endActionModule (reesAction φ F I)
  let := (spaceCohomology B S hS X p).endActionModule (reesActionHom φ F I)
  let e := (DirectSum.decomposeRingEquiv (reesGrading I)).toRingHom
  have : RingHomSurjective e := ⟨(DirectSum.decomposeRingEquiv (reesGrading I)).surjective⟩
  let l : @LinearMap _ _ _ _ e
      ((spaceCohomology B S hS X p).obj (reesModule φ F I))
      ((spaceCohomology B S hS X p).obj (reesModule φ F I))
      _ _ ((spaceCohomology B S hS X p).endActionModule (reesAction φ F I))
      ((spaceCohomology B S hS X p).endActionModule (reesActionHom φ F I)) :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (l.finite_iff_of_bijective Function.bijective_id).1 h

/-- **Stacks 08AW over an affine object of the site**: for a proper morphism `f : X ⟶ V` to an
affine object whose functions are identified with the Noetherian ring `A`, an ideal `I ⊆ A` and a
coherent `𝒪_X`-module `F`, the graded module `⨁ₙ Hᵖ(X, Iⁿ F)` is finite over the Rees algebra. -/
@[sga "2 XII 5.8" "(ii), special case"]
theorem isReesFinite_cohomologyIdealPowerSystem_of_isAffine [IsNoetherianRing A]
    (f : X ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)
    (φ : A →+* ↥(GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
    (hφ : ∀ a, φ a = pullbackToGlobalFunctions B S hS X V f (α a))
    (F : Modules.{u, u} B S hS X.1 X.2) [hF : IsCoherent B S hS X.1 X.2 F] (I : Ideal A) (p : ℕ) :
    (cohomologyIdealPowerSystem φ F I p).IsReesFinite := by
  let := (cohomologyIdealPowerSystem φ F I p).gmodule
  let := (spaceCohomology B S hS X p).endActionModule (reesActionHom φ F I)
  have := moduleFinite_cohomology_reesModule_of_isAffine α f hf φ hφ F hF I p
  have := isNoetherianRing_reesGradingDirectSum I
  have := isNoetherian_of_isNoetherianRing_of_finite (⨁ n, ↥(reesGrading I n))
    ((spaceCohomology B S hS X p).obj (reesModule φ F I))
  let Φ : (⨁ n, cohomologyIdealPower φ F I p n) →ₗ[⨁ n, ↥(reesGrading I n)]
      (spaceCohomology B S hS X p).obj (reesModule φ F I) :=
    { toFun := cohomologyReesComparison φ F I p
      map_add' := map_add _
      map_smul' := cohomologyReesComparison_smul φ F I p }
  exact Module.Finite.of_injective Φ (cohomologyReesComparison_injective _ F I p)

end OverAffine

end AlgebraicGeometry.Space

/-! ### Stacks 08AW and 08AX -/

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X : AlgebraicSpaces B (Spec (.of A)) hA}

/-- **Stacks 08AW.**  In Situation 08AV — `A` Noetherian, `I ⊆ A` an ideal, `f : X ⟶ Spec A`
proper and `F` a coherent `𝒪_X`-module — for every `p` the graded module `⨁ₙ Hᵖ(X, Iⁿ F)` is a
finite module over the Rees algebra `B = ⨁ₙ Iⁿ`.

The graded module structure is that of the Rees system `cohomologyIdealPowerSystem`: an element
`a ∈ Iᵏ` acts as the cohomology of multiplication by `a`, from `Iⁿ F` to `Iᵏ⁺ⁿ F`. -/
@[stacks 08AW, sga "2 XII 5.8" "(ii), special case"]
theorem isReesFinite_cohomologyIdealPowerSystem [IsNoetherianRing A]
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f.hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [hF : IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
    (I : Ideal A) (p : ℕ) :
    (cohomologyIdealPowerSystem (baseRingHom A B hA X.1 X.2) F I p).IsReesFinite :=
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseObject A B hA)) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  isReesFinite_cohomologyIdealPowerSystem_of_isAffine (V := baseObject A B hA)
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv f hf _
    (fun a => (pullbackToGlobalFunctions_baseObject B A hA f a).symm) F I p

/-- **Stacks 08AX.**  In Situation 08AV — `A` Noetherian, `I ⊆ A` an ideal, `f : X ⟶ Spec A`
proper and `F` a coherent `𝒪_X`-module — for every `p` there is an integer `c ≥ 0` such that

1. the multiplication map `Iⁿ⁻ᶜ ⊗ Hᵖ(X, Iᶜ F) ⟶ Hᵖ(X, Iⁿ F)` is surjective for all `n ≥ c`,
   here written for `n = m + c`;
2. the image of `Hᵖ(X, Iⁿ⁺ᵐ F) ⟶ Hᵖ(X, Iⁿ F)` is contained in `Iᵐ⁻ᶜ Hᵖ(X, Iⁿ F)` for all
   `n ≥ 0` and `m ≥ c`. -/
@[stacks 08AX]
theorem exists_surjective_cohomologyIdealPowerMul_and_range_le [IsNoetherianRing A]
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f.hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
    (I : Ideal A) (p : ℕ) :
    ∃ c : ℕ, (∀ m : ℕ, Function.Surjective (TensorProduct.lift
        (cohomologyIdealPowerMul (baseRingHom A B hA X.1 X.2) F I p m c le_rfl))) ∧
      ∀ n m : ℕ, c ≤ m →
        LinearMap.range (cohomologyIdealPowerTr (baseRingHom A B hA X.1 X.2) F I p
          (Nat.le_add_right n m)) ≤
          I ^ (m - c) • (⊤ : Submodule A
            (cohomologyIdealPower (baseRingHom A B hA X.1 X.2) F I p n)) :=
  exists_surjective_cohomologyIdealPowerMul_and_range_le_of_isReesFinite _ F I p
    (isReesFinite_cohomologyIdealPowerSystem f hf F I p)

end AlgebraicGeometry.Space

end
