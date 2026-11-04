module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SheafSubmodule
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyLinear
public import StacksFrontier.RingTheory.Filtration.IdealPowerSystemNoetherian
public import StacksFrontier.RingTheory.LocalCohomology.UniformCohomologyBound
public import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology of the ideal-power filtration as a Rees system

Let `A` be a ring, `I ⊆ A` an ideal, `X` a scheme over `Spec A` and `ℱ` a sheaf of
`𝒪_X`-modules. The subsheaves `Iⁿℱ` of `ℱ` are built in
`StacksFrontier/AlgebraicGeometry/Modules/IdealPowerMultiple.lean`, and the purely algebraic
Artin-Rees argument of [Stacks, Tag 02OA] is carried out in
`StacksFrontier/RingTheory/Filtration/IdealPowerSystem.lean` for an abstract
`Stacks.RingTheory.IdealPowerSystem`. This file supplies the missing link between the two: the
cohomology modules `Hᵖ(X, Iⁿℱ)` form such a system, and in fact a
`Stacks.RingTheory.ReesSystem` — the refinement whose graded-module laws turn the finiteness
statement [Stacks, Tag 02O8] into the Noetherianity hypothesis the Artin-Rees argument
consumes.

## Main definitions

* `Stacks.Cohomology.FormalFunctions.idealPowerSmul` is multiplication by `a ∈ Iᵏ` as a
  morphism `Iⁿℱ ⟶ Iᵐℱ` of sheaves of modules, for `m ≤ k + n`.
* `Stacks.Cohomology.FormalFunctions.cohomologyIdealPowerSystem` is **the system
  `n ↦ Hᵖ(X, Iⁿℱ)` over `Hᵖ(X, ℱ)`, as a `ReesSystem` for the Rees algebra `⨁ₙ Iⁿ` of `I`.**

## Main results

* `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology`: parts (2) at `n = 0` and
  (3) of [Stacks, Tag 02OA], granted [Stacks, Tag 02O8] in general form.

## Implementation notes

All the morphisms of sheaves of modules appearing here are multiplication by a single global
function, read between two members of the filtration. They are therefore constructed uniformly
by `AlgebraicGeometry.sheafSubmoduleMap` out of the endomorphism `a • 𝟙` of `ℱ`, and *every*
identity between them is proved by `AlgebraicGeometry.cancel_sheafSubmodule_ι`: a morphism into
a subsheaf is determined by its composite with the inclusion into `ℱ`, and after that composite
all the identities are the module laws of `a • 𝟙`. No computation on sections is needed beyond
the single containment `idealPowerSub_le_comap_smul`, which is where `a ∈ Iᵏ` is used.

The ring over which the cohomology modules are taken as modules is the base ring `A` itself,
not `Γ(X, 𝒪_X)`: the `A`-action comes from `Stacks.Cohomology.AffineBase.baseSectionsAlgebra`
by restriction of scalars, and `A`-linearity of the multiplication maps is
`Stacks.Cohomology.AffineBase.linear_rightDerived_moduleGlobalSections`. This is why the
structure morphism `X ⟶ Spec A` is part of the data (`X : Over (Spec A)`): `Γ(X, ⊤)`-linearity
of cohomology is not available as an instance, whereas `A`-linearity for a scheme over `Spec A`
is. Accordingly `Stacks.RingTheory.ReesSystem` is instantiated with `φ = RingHom.id A`.

The three graded-module laws of `ReesSystem` are equalities in the sigma type `Σ n, M n`,
because the index of the target of a multiplication map is `k + n` on the nose. Each is reduced
by `sigma_idealPowerSmul_congr` — whose proof is `subst` followed by proof irrelevance for the
`≤` argument — to an identity of morphisms with a *fixed* target index, so no `eqToHom` appears
anywhere.

## References

* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower Stacks.Cohomology.AffineBase
open scoped ModuleCat.Algebra

universe u

namespace Stacks.Cohomology.FormalFunctions

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))
  (F : X.left.Modules)

/-! ### The filtration and multiplication by a function on the base -/

/-- The subsheaf `Iⁿℱ` of `ℱ`: the `n`-th member of the ideal-power filtration attached to the
extension of `I ⊆ A` to `X`. -/
abbrev idealPowerSub (n : ℕ) : F.Submodule :=
  idealPowerMultiple (baseIdealSheaf A I X.hom) n F

/-- Multiplying a section in `Iⁿ ℱ(U)` by `a ∈ Iᵏ` gives a section of `Iᵐℱ`, for `m ≤ k + n`. -/
private theorem smul_mem_idealPowerSub_obj {k n m : ℕ} (hm : m ≤ k + n) {a : A} (ha : a ∈ I ^ k)
    (U : X.left.affineOpens) {x : Γ(F, U.1)}
    (hx : x ∈ ((baseIdealSheaf A I X.hom).ideal U) ^ n •
      (⊤ : Submodule Γ(X.left, U.1) Γ(F, U.1))) :
    (show Γ(X.left, U.1) from baseRingToSections A X (op U.1) a) • x ∈
      (idealPowerSub I X F m).toSubmodule.obj (op U.1) := by
  have haU : (show Γ(X.left, U.1) from baseRingToSections A X (op U.1) a) ∈
      ((baseIdealSheaf A I X.hom).ideal U) ^ k := by
    rw [baseIdealSheaf_ideal, ← Ideal.map_pow, ← baseIdeal_pow]
    exact Ideal.mem_map_of_mem _ (mem_baseIdeal A (I ^ k) X.hom ha)
  exact le_idealPowerMultiple_obj (baseIdealSheaf A I X.hom) m F U
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right hm)
      (by rw [pow_add, mul_smul]; exact Submodule.smul_mem_smul haU hx))

/-- Multiplication by `a ∈ Iᵏ` carries `Iⁿℱ` into `Iᵏ⁺ⁿℱ`, hence into `Iᵐℱ` for any
`m ≤ k + n`. This is the only place where the hypothesis `a ∈ Iᵏ` is used; everything else is
formal. -/
theorem idealPowerSub_le_comap_smul {k n m : ℕ} (hm : m ≤ k + n) {a : A} (ha : a ∈ I ^ k) :
    idealPowerSub I X F n ≤ sheafSubmoduleComap (a • 𝟙 F) (idealPowerSub I X F m) := by
  rw [idealPowerMultiple_le_iff]
  intro U x hx
  exact smul_mem_idealPowerSub_obj I X F hm ha U hx

/-- Multiplication by `a ∈ Iᵏ` carries all of `ℱ` into `Iᵐℱ` for `m ≤ k`. This is the case
`n = 0` of `idealPowerSub_le_comap_smul`, except that the source is `ℱ` itself rather than the
zeroth member of the filtration. -/
theorem top_le_comap_smul {k m : ℕ} (hm : m ≤ k) {a : A} (ha : a ∈ I ^ k) :
    (⊤ : F.Submodule) ≤ sheafSubmoduleComap (a • 𝟙 F) (idealPowerSub I X F m) := by
  refine ge_of_eq (sheafSubmodule_eq_top_of_affine _ fun U x _ ↦ ?_)
  exact smul_mem_idealPowerSub_obj (n := 0) I X F hm ha U
    (by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact Submodule.mem_top)

/-- The `n`-th member `Iⁿℱ` of the filtration, as a sheaf of modules on `X`. -/
abbrev idealPowerMod (n : ℕ) : X.left.Modules := (idealPowerSub I X F n).toSheafOfModules

/-- **Multiplication by `a ∈ Iᵏ` as a morphism `Iⁿℱ ⟶ Iᵐℱ`**, for `m ≤ k + n`. -/
def idealPowerSmul {k n m : ℕ} (hm : m ≤ k + n) (a : A) (ha : a ∈ I ^ k) :
    idealPowerMod I X F n ⟶ idealPowerMod I X F m :=
  sheafSubmoduleMap (a • 𝟙 F) _ _ (idealPowerSub_le_comap_smul I X F hm ha)

/-- A multiple by `a ∈ Iᵏ` of any section of `ℱ` is a section of `Iᵐℱ`, for `m ≤ k`. This is
`top_le_comap_smul` read as a statement about sections. -/
theorem smul_mem_idealPowerSub {k m : ℕ} (hm : m ≤ k) (a : A) (ha : a ∈ I ^ k)
    (U : (Opens X.left)ᵒᵖ) (x : F.val.obj U) :
    ((a • 𝟙 F).val.app U).hom x ∈ (idealPowerSub I X F m).toSubmodule.obj U :=
  top_le_comap_smul I X F hm ha U (by rw [sheafTop_obj]; exact Submodule.mem_top)

/-- **Multiplication by `a ∈ Iᵏ` as a morphism `ℱ ⟶ Iᵐℱ`**, for `m ≤ k`. -/
def idealPowerSmulTop {k m : ℕ} (hm : m ≤ k) (a : A) (ha : a ∈ I ^ k) :
    F ⟶ idealPowerMod I X F m :=
  ⟨{ app U := ModuleCat.ofHom
        { toFun x := ⟨((a • 𝟙 F).val.app U).hom x, smul_mem_idealPowerSub I X F hm a ha U x⟩
          map_add' := fun x y ↦ Subtype.ext (map_add _ x y)
          map_smul' := fun r x ↦ Subtype.ext (map_smul _ r x) }
     naturality := by
       intro U V g
       apply ModuleCat.Hom.ext
       ext x
       exact Subtype.ext (PresheafOfModules.naturality_apply (a • 𝟙 F).val g x) }⟩

/-- Two morphisms of sheaves of modules on `X` agree as soon as they agree on sections over
every open. Used throughout the next section, where every morphism is multiplication by one
function on the base and so every identity is visible on sections. -/
theorem hom_ext_of_sections {M N : X.left.Modules} {f g : M ⟶ N}
    (h : ∀ (U : (Opens X.left)ᵒᵖ) (x : M.val.obj U),
      (f.val.app U).hom x = (g.val.app U).hom x) :
    f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  funext U
  apply ModuleCat.Hom.ext
  ext x
  exact h U x

@[simp]
theorem idealPowerSmul_comp_ι {k n m : ℕ} (hm : m ≤ k + n) (a : A) (ha : a ∈ I ^ k) :
    idealPowerSmul I X F hm a ha ≫ (idealPowerSub I X F m).ι =
      (idealPowerSub I X F n).ι ≫ (a • 𝟙 F) :=
  sheafSubmoduleMap_comp_ι _ _ _ _

@[simp]
theorem idealPowerSmulTop_comp_ι {k m : ℕ} (hm : m ≤ k) (a : A) (ha : a ∈ I ^ k) :
    idealPowerSmulTop I X F hm a ha ≫ (idealPowerSub I X F m).ι = a • 𝟙 F :=
  hom_ext_of_sections X fun _ _ ↦ rfl

/-- An equality of morphisms of sheaves of modules, read on sections. -/
theorem apply_congr {M N : X.left.Modules} {f g : M ⟶ N} (h : f = g)
    (U : (Opens X.left)ᵒᵖ) (y : M.val.obj U) :
    (f.val.app U).hom y = (g.val.app U).hom y :=
  congrArg (fun φ : M ⟶ N ↦ (φ.val.app U).hom y) h

/-! ### The identities between the multiplication maps

Every morphism below is multiplication by one function on the base, read between two members of
the filtration. Each identity is therefore reduced by `cancel_sheafSubmodule_ι` to an identity
of maps into `ℱ`, where it either holds on sections by definition or is the corresponding
module law for `• 𝟙 ℱ`. -/

/-- Composing the multiplications by `b` and by `a` on `ℱ` is multiplication by `a * b`. -/
theorem smul_id_comp_smul_id (a b : A) :
    (b • 𝟙 F) ≫ (a • 𝟙 F) = (a * b) • 𝟙 F := by
  rw [Linear.smul_comp, Category.id_comp, smul_smul, mul_comm]

/-- The inclusion of a member of the filtration into itself is the identity. -/
@[simp]
theorem idealPowerMultipleMap_refl (n : ℕ) :
    idealPowerMultipleMap (baseIdealSheaf A I X.hom) F (le_refl n) = 𝟙 _ :=
  cancel_sheafSubmodule_ι _ _ _ (hom_ext_of_sections X fun _ _ ↦ rfl)

/-- Multiplying and then including is multiplying into the smaller member. -/
theorem idealPowerSmul_comp_idealPowerMultipleMap {k n m m' : ℕ} (hm : m ≤ k + n) (h : m' ≤ m)
    (hm' : m' ≤ k + n) (a : A) (ha : a ∈ I ^ k) :
    idealPowerSmul I X F hm a ha ≫ idealPowerMultipleMap (baseIdealSheaf A I X.hom) F h =
      idealPowerSmul I X F hm' a ha :=
  cancel_sheafSubmodule_ι _ _ _ (hom_ext_of_sections X fun _ _ ↦ rfl)

/-- Multiplication out of a member of the filtration into itself is `a • 𝟙`. -/
theorem idealPowerSmul_self {k n : ℕ} (hm : n ≤ k + n) (a : A) (ha : a ∈ I ^ k) :
    idealPowerSmul I X F hm a ha = a • 𝟙 (idealPowerMod I X F n) :=
  cancel_sheafSubmodule_ι _ _ _ (hom_ext_of_sections X fun _ _ ↦ rfl)

/-- The compatibility of multiplication with the transition maps that [Stacks, Tag 02OA] uses:
multiplying a section of `Iⁿℱ` by `a ∈ Iᵏ` and then dropping to `Iᵏℱ` is the same as first
forgetting the filtration and then multiplying `ℱ` into `Iᵏℱ`. -/
theorem idealPowerSmul_comp_idealPowerMultipleMap_eq {k n : ℕ} (a : A) (ha : a ∈ I ^ k) :
    idealPowerSmul I X F (le_refl (k + n)) a ha ≫
        idealPowerMultipleMap (baseIdealSheaf A I X.hom) F (Nat.le_add_right k n) =
      (idealPowerSub I X F n).ι ≫ idealPowerSmulTop I X F (le_refl k) a ha :=
  cancel_sheafSubmodule_ι _ _ _ (hom_ext_of_sections X fun _ _ ↦ rfl)

/-- Multiplication maps compose to multiplication by the product. -/
theorem idealPowerSmul_comp_idealPowerSmul {k l n q m : ℕ} (hq : q ≤ l + n) (hm : m ≤ k + q)
    (hm' : m ≤ k + l + n) (a b : A) (ha : a ∈ I ^ k) (hb : b ∈ I ^ l) :
    idealPowerSmul I X F hq b hb ≫ idealPowerSmul I X F hm a ha =
      idealPowerSmul I X F hm' (a * b) (by rw [pow_add]; exact Ideal.mul_mem_mul ha hb) :=
  cancel_sheafSubmodule_ι _ _ _ (hom_ext_of_sections X fun U x ↦
    apply_congr X (smul_id_comp_smul_id X F a b) U x.1)

/-- Multiplication is additive in the function. -/
theorem idealPowerSmul_add {k n m : ℕ} (hm : m ≤ k + n) (a a' : A) (ha : a ∈ I ^ k)
    (ha' : a' ∈ I ^ k) :
    idealPowerSmul I X F hm (a + a') (Ideal.add_mem _ ha ha') =
      idealPowerSmul I X F hm a ha + idealPowerSmul I X F hm a' ha' :=
  cancel_sheafSubmodule_ι _ _ _ (hom_ext_of_sections X fun U x ↦
    apply_congr X (add_smul a a' (𝟙 F)) U x.1)

/-- Multiplication is `A`-linear in the function. -/
theorem idealPowerSmul_smul {k n m : ℕ} (hm : m ≤ k + n) (r a : A) (ha : a ∈ I ^ k) :
    idealPowerSmul I X F hm (r * a) (Ideal.mul_mem_left _ r ha) =
      r • idealPowerSmul I X F hm a ha :=
  cancel_sheafSubmodule_ι _ _ _ (hom_ext_of_sections X fun U x ↦
    apply_congr X
      (((smul_id_comp_smul_id X F a r).trans
        (congrArg (fun c : A ↦ c • 𝟙 F) (mul_comm a r))).symm) U x.1)

/-! ### The cohomology of the filtration as a Rees system -/

variable (p : ℕ)

/-- `Hᵖ(X, −)` on sheaves of modules over `X`, valued in modules over `Γ(X, 𝒪_X)`. -/
abbrev cohomologyFunctor : X.left.Modules ⥤ ModuleCat.{u} Γ(X.left, ⊤) :=
  (moduleGlobalSections X.left).rightDerived p

/-- **`Hᵖ(X, −)` is `A`-linear.** This is
`Stacks.Cohomology.AffineBase.linear_rightDerived_moduleGlobalSections`, registered so that
`CategoryTheory.Functor.map_smul` applies below. -/
instance cohomologyFunctor_linear : (cohomologyFunctor X p).Linear A :=
  linear_rightDerived_moduleGlobalSections A X p

/-- `Hᵖ(X, ℱ)`, as an `A`-module. -/
abbrev cohomology : Type u := (cohomologyFunctor X p).obj F

/-- `Hᵖ(X, Iⁿℱ)`, as an `A`-module. -/
abbrev cohomologyIdealPower (n : ℕ) : Type u :=
  (cohomologyFunctor X p).obj (idealPowerMod I X F n)

/-- Functoriality of `Hᵖ(X, −)`, read on elements. -/
theorem cohomologyFunctor_map_comp_apply {M N P : X.left.Modules} (f : M ⟶ N) (g : N ⟶ P)
    (x : (cohomologyFunctor X p).obj M) :
    ((cohomologyFunctor X p).map g).hom (((cohomologyFunctor X p).map f).hom x) =
      ((cohomologyFunctor X p).map (f ≫ g)).hom x :=
  (congrArg (fun φ : (cohomologyFunctor X p).obj M ⟶ (cohomologyFunctor X p).obj P ↦ φ.hom x)
    ((cohomologyFunctor X p).map_comp f g)).symm

/-- `Hᵖ(X, −)` sends an identity to an identity, read on elements. -/
theorem cohomologyFunctor_map_id_apply {M : X.left.Modules}
    (y : (cohomologyFunctor X p).obj M) :
    ((cohomologyFunctor X p).map (𝟙 M)).hom y = y := by
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- `Hᵖ(X, −)` sends multiplication by `a` to multiplication by `a`: this is the `A`-linearity
of cohomology, read on elements. -/
theorem cohomologyFunctor_map_smul_id_apply (a : A) {M : X.left.Modules}
    (y : (cohomologyFunctor X p).obj M) :
    ((cohomologyFunctor X p).map (a • 𝟙 M)).hom y = a • y := by
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

/-- `Hᵖ(X, Iⁿℱ) ⟶ Hᵖ(X, Iᵐℱ)` for `m ≤ n`: the transition map of the system. -/
def cohomologyTr {m n : ℕ} (h : m ≤ n) :
    cohomologyIdealPower I X F p n →ₗ[A] cohomologyIdealPower I X F p m :=
  (((cohomologyFunctor X p).map
    (idealPowerMultipleMap (baseIdealSheaf A I X.hom) F h)).hom).restrictScalars A

/-- `Hᵖ(X, Iⁿℱ) ⟶ Hᵖ(X, ℱ)`: the projection of the system. -/
def cohomologyProj (n : ℕ) :
    cohomologyIdealPower I X F p n →ₗ[A] cohomology X F p :=
  (((cohomologyFunctor X p).map (idealPowerSub I X F n).ι).hom).restrictScalars A

/-- An element of a power of the extension of `I` along the identity lies in that power
of `I`. -/
theorem mem_pow_of_mem_map_id {k : ℕ} {a : A} (ha : a ∈ (I.map (RingHom.id A)) ^ k) :
    a ∈ I ^ k := by
  rwa [Ideal.map_id] at ha

/-- Multiplication by `a` depends on `a` alone. -/
theorem idealPowerSmul_congr {k n m : ℕ} (hm : m ≤ k + n) {a a' : A} (ha : a ∈ I ^ k)
    (ha' : a' ∈ I ^ k) (e : a = a') :
    idealPowerSmul I X F hm a ha = idealPowerSmul I X F hm a' ha' := by
  subst e; rfl

/-- **`Iᵏ ⊗ Hᵖ(X, Iⁿℱ) ⟶ Hᵖ(X, Iᵏ⁺ⁿℱ)`**: the multiplication map of the system, `A`-linear in
the function by `A`-linearity of cohomology. -/
def cohomologyMul (k n : ℕ) :
    ↥((I.map (RingHom.id A)) ^ k) →ₗ[A]
      cohomologyIdealPower I X F p n →ₗ[A] cohomologyIdealPower I X F p (k + n) where
  toFun a := (((cohomologyFunctor X p).map (idealPowerSmul I X F (le_refl (k + n)) (a : A)
    (mem_pow_of_mem_map_id I a.2))).hom).restrictScalars A
  map_add' a a' := by
    refine LinearMap.ext fun x ↦ ?_
    change ((cohomologyFunctor X p).map (idealPowerSmul I X F (le_refl (k + n))
      ((a : A) + (a' : A)) _)).hom x = _
    rw [idealPowerSmul_add I X F (le_refl (k + n)) (a : A) (a' : A)
        (mem_pow_of_mem_map_id I a.2) (mem_pow_of_mem_map_id I a'.2),
      Functor.map_add]
    rfl
  map_smul' r a := by
    refine LinearMap.ext fun x ↦ ?_
    change ((cohomologyFunctor X p).map (idealPowerSmul I X F (le_refl (k + n))
      (r * (a : A)) _)).hom x = _
    rw [idealPowerSmul_smul I X F (le_refl (k + n)) r (a : A) (mem_pow_of_mem_map_id I a.2),
      Functor.map_smul]
    rfl

/-- Two multiplication maps with the same function and equal target degrees agree, as elements
of `Σ n, Hᵖ(X, Iⁿℱ)`. The `≤` arguments are irrelevant once the degrees are substituted, which
is what makes the graded-module laws of `ReesSystem` provable without any transport. -/
theorem sigma_cohomologyMul_congr {k n m m' : ℕ} (e : m = m') (hm : m ≤ k + n) (hm' : m' ≤ k + n)
    (a : A) (ha : a ∈ I ^ k) (x : cohomologyIdealPower I X F p n) :
    (⟨m, ((cohomologyFunctor X p).map (idealPowerSmul I X F hm a ha)).hom x⟩ :
        Σ j, cohomologyIdealPower I X F p j) =
      ⟨m', ((cohomologyFunctor X p).map (idealPowerSmul I X F hm' a ha)).hom x⟩ := by
  subst e; rfl

/-- **The system `n ↦ Hᵖ(X, Iⁿℱ)` over `Hᵖ(X, ℱ)`, as a Rees system for `⨁ₙ Iⁿ`.**

This is the cohomological input of [Stacks, Tag 02OA]: the transition maps are induced by the
inclusions `Iⁿℱ ⊆ Iᵐℱ`, the projections by the inclusions `Iⁿℱ ⊆ ℱ`, and the multiplication
maps by multiplication by a function on the base. -/
def cohomologyIdealPowerSystem :
    Stacks.RingTheory.ReesSystem (RingHom.id A) I (cohomologyIdealPower I X F p)
      (cohomology X F p) where
  tr := fun {_ _} h ↦ cohomologyTr I X F p h
  tr_tr h₁ h₂ x :=
    (cohomologyFunctor_map_comp_apply X p _ _ x).trans
      (congrArg (fun φ : _ ⟶ _ ↦ ((cohomologyFunctor X p).map φ).hom x)
        (idealPowerMultipleMap_comp (baseIdealSheaf A I X.hom) F h₁ h₂))
  proj n := cohomologyProj I X F p n
  proj_tr h x :=
    (cohomologyFunctor_map_comp_apply X p _ _ x).trans
      (congrArg (fun φ : _ ⟶ _ ↦ ((cohomologyFunctor X p).map φ).hom x)
        (idealPowerMultipleMap_comp_ι (baseIdealSheaf A I X.hom) F h))
  mul k n := cohomologyMul I X F p k n
  proj_mul k n a x :=
    (cohomologyFunctor_map_comp_apply X p _ _ x).trans
      ((congrArg (fun φ : _ ⟶ _ ↦ ((cohomologyFunctor X p).map φ).hom x)
        (idealPowerSmul_comp_ι I X F (le_refl (k + n)) (a : A)
          (mem_pow_of_mem_map_id I a.2))).trans
        ((cohomologyFunctor_map_comp_apply X p _ _ x).symm.trans
          (cohomologyFunctor_map_smul_id_apply X p (a : A) _)))
  tr_mul_of_proj_eq_zero k n a x hx :=
    (cohomologyFunctor_map_comp_apply X p _ _ x).trans
      ((congrArg (fun φ : _ ⟶ _ ↦ ((cohomologyFunctor X p).map φ).hom x)
        (idealPowerSmul_comp_idealPowerMultipleMap_eq I X F (a : A)
          (mem_pow_of_mem_map_id I a.2))).trans
        ((cohomologyFunctor_map_comp_apply X p _ _ x).symm.trans
          ((congrArg (fun y ↦ ((cohomologyFunctor X p).map
            (idealPowerSmulTop I X F (le_refl k) (a : A)
              (mem_pow_of_mem_map_id I a.2))).hom y) hx).trans (map_zero _))))
  tr_of_eq := fun {_ _} h e x ↦ by
    subst e
    exact congrArg (Sigma.mk _)
      ((congrArg (fun φ : _ ⟶ _ ↦ ((cohomologyFunctor X p).map φ).hom x)
        (idealPowerMultipleMap_refl I X F _)).trans (cohomologyFunctor_map_id_apply X p x))
  mul_zero_eq_smul n a x :=
    (sigma_cohomologyMul_congr I X F p (Nat.zero_add n) (le_refl (0 + n))
      (Nat.le_add_left n 0) (a : A) a.2 x).trans
      (congrArg (Sigma.mk n)
        ((congrArg (fun φ : _ ⟶ _ ↦ ((cohomologyFunctor X p).map φ).hom x)
          (idealPowerSmul_self I X F (Nat.le_add_left n 0) (a : A) a.2)).trans
          (cohomologyFunctor_map_smul_id_apply X p (a : A) x)))
  mul_mul k l n a b c x hc := by
    have hab : (a : A) * (b : A) ∈ I ^ (k + l) := by
      rw [pow_add]; exact Ideal.mul_mem_mul a.2 b.2
    have hassoc : k + (l + n) ≤ k + l + n := le_of_eq (Nat.add_assoc k l n).symm
    have key : ((cohomologyFunctor X p).map
          (idealPowerSmul I X F hassoc (c : A) c.2)).hom x =
        ((cohomologyFunctor X p).map
          (idealPowerSmul I X F (le_refl (k + (l + n))) (a : A) a.2)).hom
            (((cohomologyFunctor X p).map
              (idealPowerSmul I X F (le_refl (l + n)) (b : A) b.2)).hom x) := by
      rw [cohomologyFunctor_map_comp_apply, idealPowerSmul_comp_idealPowerSmul I X F
          (le_refl (l + n)) (le_refl (k + (l + n))) hassoc (a : A) (b : A) a.2 b.2]
      exact congrArg (fun φ : _ ⟶ _ ↦ ((cohomologyFunctor X p).map φ).hom x)
        (idealPowerSmul_congr I X F hassoc c.2 hab hc)
    exact (sigma_cohomologyMul_congr I X F p (Nat.add_assoc k l n) (le_refl (k + l + n))
      hassoc (c : A) c.2 x).trans (congrArg (Sigma.mk (k + (l + n))) key)

/-! ### The uniform bound -/

/-- **The conclusion of [Stacks, Tag 02O8]** for the data `A`, `I`, `X`, `ℱ`, `p`: the graded
module `⨁ₙ Hᵖ(X, Iⁿℱ)` is a finite module over the Rees algebra `B = ⨁ₙ Iⁿ`, the graded module
structure being the one carried by `cohomologyIdealPowerSystem`.

This is *not* proved here. Its proof in the source is [Stacks, Tag 0897] part (1) applied to the
finite type graded `⨁ₙ Iⁿ𝒪_X`-module `⨁ₙ Iⁿℱ`, and Tag 0897 is absent from this branch (it
rests on the coherence of higher direct images, [Stacks, Tag 02O5], which is unproved -- see the
implementation notes of `StacksFrontier/AlgebraicGeometry/HigherDirectImageCoherent/Basic.lean`).
What the present file supplies is that the statement is now *expressible*: before
`cohomologyIdealPowerSystem` there was no graded `⨁ₙ Iⁿ`-module `⨁ₙ Hᵖ(X, Iⁿℱ)` in the tree to
be finite over anything. -/
abbrev IsCohomologyReesFinite : Prop :=
  (cohomologyIdealPowerSystem I X F p).IsReesFinite

/-- **[Stacks, Tag 02OA], part (2) in the case `n = 0` and part (3).**

For `A` Noetherian, `f : X → Spec A` proper and `ℱ` coherent there is one integer `c ≥ 0` such
that

* the image of `Hᵖ(X, Iʳℱ) → Hᵖ(X, ℱ)` is contained in `Iʳ⁻ᶜHᵖ(X, ℱ)` for `r ≥ c` -- this is
  part (2) of the source at `n = 0`, where its `e = max(0, c - n)` is `c`; and
* `Ker(Hᵖ(X, Iᵏℱ) → Hᵖ(X, ℱ)) = Ker(Hᵖ(X, Iᵏℱ) → Hᵖ(X, Iᵐℱ))` whenever `m + c ≤ k` -- this is
  part (3) of the source, which is the case `m = k - c`.

Parts (1), (4) and (5) of the source, and part (2) for general `n`, are **not** proved here;
neither is the case `n > 0` of part (2), which needs a compatibility between the transition maps
and the multiplication maps that `Stacks.RingTheory.IdealPowerSystem` deliberately does not
assume.

The hypothesis `h02O8` is [Stacks, Tag 02O8] -- a *different* Stacks tag, absent from this
branch -- carried in general form: it is quantified over every Noetherian base ring, every
ideal of it, every proper scheme over it, every coherent module and every degree, and is
instantiated inside the proof at the data of this statement. See `IsCohomologyReesFinite` for
why it is absent and what is new about its being statable. -/
@[stacks 02OA "parts (2) at n = 0 and (3); parts (1), (4), (5) and part (2) \
  for n > 0 are not proved here"]
theorem exists_uniform_bound_cohomology [IsNoetherianRing A]
    (hX : AlgebraicGeometry.IsProper X.hom) (hF : SheafOfModules.IsCoherent F) (p : ℕ)
    (h02O8 : ∀ (A' : Type u) [CommRing A'] [IsNoetherianRing A'] (I' : Ideal A')
      (X' : Over (Spec (.of A'))) (_ : AlgebraicGeometry.IsProper X'.hom)
      (F' : X'.left.Modules) (_ : SheafOfModules.IsCoherent F') (p' : ℕ),
      (cohomologyIdealPowerSystem I' X' F' p').IsReesFinite) :
    ∃ c : ℕ,
      (∀ r : ℕ, c ≤ r → LinearMap.range (cohomologyProj I X F p r) ≤
        I ^ (r - c) • (⊤ : Submodule A (cohomology X F p))) ∧
      (∀ (m k : ℕ) (hmk : m + c ≤ k),
        LinearMap.ker (cohomologyProj I X F p k) =
          LinearMap.ker (cohomologyTr I X F p
            (show m ≤ k from le_trans (Nat.le_add_right m c) hmk))) := by
  have hfin : (cohomologyIdealPowerSystem I X F p).IsReesFinite := h02O8 A I X hX F hF p
  have hnoe := (cohomologyIdealPowerSystem I X F p).isNoetherianSystem_of_isReesFinite hfin
  obtain ⟨c, h1, h2⟩ :=
    (cohomologyIdealPowerSystem I X F p).toIdealPowerSystem.exists_uniform_bound hnoe
  refine ⟨c, fun r hr ↦ (h1 r hr).trans (le_of_eq ?_), h2⟩
  rw [Ideal.map_id]

end Stacks.Cohomology.FormalFunctions

end
