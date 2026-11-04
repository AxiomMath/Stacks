module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import StacksFrontier.RingTheory.AdicCompletion.KerEval
public import StacksFrontier.RingTheory.AdicCompletion.MapOfPowLe
public import StacksFrontier.RingTheory.Rig.CategoryLimit

/-!
# Base change for the two categories of Stacks chapter 88

Let `A₁ → A₂` be a ring map and `I₁ ⊆ A₁`, `I₂ ⊆ A₂` ideals such that `I₁ ^ c` maps into `I₂`
for some `c ≥ 1`. Stacks chapter 88 attaches to `(A, I)` the category `Rig.AdicAlgebraSystem A I`
of inverse systems `(Bₙ)` of finite type `A ⧸ Iⁿ`-algebras with `B_{n+1} ⧸ IⁿB_{n+1} = Bₙ`, and the
category `Rig.AdicFiniteTypeAlgebra A I` of `I`-adically complete `A`-algebras of finite type
modulo `I`. This file constructs the base change `(Bₙ) ↦ (B_{cn} ⊗ A₂ ⧸ I₂ⁿ)` of systems and shows
that, when `I₂` is finitely generated, it agrees with the completed base change
`B ↦ (B ⊗[A₁] A₂)^` of `Rig.completedBaseChange` through the functors `B ↦ (B ⧸ IⁿB)ₙ`.

## Main definitions

* `Rig.AdicAlgebraSystem.transitionOfLE` — the composite transition `B_j → B_i` of a system.
* `Rig.AdicAlgebraSystem.baseChangeFunctor` — the base change of systems; its terms are tensor
  products over `A₁`, identified with the tensor products over `A₁ ⧸ I₁ ^ (cn)` by
  `Rig.AdicAlgebraSystem.baseChangeStageEquiv`.
* `Rig.completedBaseChangeAgreement` — for `I₂` finitely generated, the isomorphism between the
  quotient systems of the completed base change and the base change of the quotient systems.
* `Rig.adicBaseChange` — Stacks 0AL5, bundled as a `Rig.AdicBaseChange`.

## Implementation notes

The terms of a system are indexed from zero, `X.B n` standing for the source's `B_{n+1}`. The
base change therefore has at the Lean index `n` the term `X.B (c * (n + 1) - 1)` (the source's
`B_{c(n+1)}`) tensored with `A₂ ⧸ I₂ ^ (n + 1)`.

## References

* [Stacks Project, Tag 0AL5](https://stacks.math.columbia.edu/tag/0AL5)
* [Stacks Project, Tag 0AJP](https://stacks.math.columbia.edu/tag/0AJP)
* [Stacks Project, Tag 0AK0](https://stacks.math.columbia.edu/tag/0AK0)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u v u₁ u₂

namespace Rig

namespace AdicAlgebraSystem

section Transition

variable {A : Type u} [CommRing A] {I : Ideal A} (X : AdicAlgebraSystem.{u, v} A I)

/-- The composite `B_j → B_i` of the transition maps of a system, for `i ≤ j`. -/
public def transitionOfLE {i j : ℕ} (h : i ≤ j) : X.B j →+* X.B i :=
  Nat.leRec (motive := fun j _ => X.B j →+* X.B i) (RingHom.id _)
    (fun k _ f => f.comp (X.transition k)) h

/-- The composite transition from a term to itself is the identity. -/
public theorem transitionOfLE_self (i : ℕ) :
    X.transitionOfLE (le_refl i) = RingHom.id _ :=
  Nat.leRec_self (motive := fun j _ => X.B j →+* X.B i) _ _

/-- The composite transition `B_{j+1} → B_i` is `B_{j+1} → B_j → B_i`. -/
public theorem transitionOfLE_succ {i j : ℕ} (h : i ≤ j) (h' : i ≤ j + 1) :
    X.transitionOfLE h' = (X.transitionOfLE h).comp (X.transition j) :=
  Nat.leRec_succ (motive := fun j _ => X.B j →+* X.B i) _ _ h

/-- The composite transition from `B_{i+1}` to `B_i` is the transition map. -/
public theorem transitionOfLE_add_one (i : ℕ) (h : i ≤ i + 1) :
    X.transitionOfLE h = X.transition i := by
  rw [X.transitionOfLE_succ le_rfl h, transitionOfLE_self, RingHom.id_comp]

/-- The composite transitions commute with the structure maps from `A`. -/
public theorem transitionOfLE_baseMap {i j : ℕ} (h : i ≤ j) (a : A) :
    X.transitionOfLE h (X.baseMap j a) = X.baseMap i a := by
  induction j, h using Nat.le_induction with
  | base => rw [transitionOfLE_self]; rfl
  | succ j hij ih =>
    rw [X.transitionOfLE_succ hij, RingHom.comp_apply, transition_baseMap, ih]

/-- The composite transitions are surjective. -/
public theorem transitionOfLE_surjective {i j : ℕ} (h : i ≤ j) :
    Function.Surjective (X.transitionOfLE h) := by
  induction j, h using Nat.le_induction with
  | base => rw [transitionOfLE_self]; exact Function.surjective_id
  | succ j hij ih =>
    rw [X.transitionOfLE_succ hij]
    exact ih.comp (X.transition_surjective j)

/-- The kernel of the composite transition `B_j → B_i` is `I ^ (i + 1) B_j`. -/
public theorem ker_transitionOfLE {i j : ℕ} (h : i ≤ j) :
    RingHom.ker (X.transitionOfLE h) = (I ^ (i + 1)).map (X.baseMap j) := by
  induction j, h using Nat.le_induction with
  | base =>
    rw [transitionOfLE_self, (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id,
      baseMap, ← Ideal.map_map, Ideal.map_quotient_self, Ideal.map_bot]
  | succ j hij ih =>
    rw [X.transitionOfLE_succ hij, ← RingHom.comap_ker, ih]
    have hb : X.baseMap j = (X.transition j).comp (X.baseMap (j + 1)) :=
      RingHom.ext fun a => (X.transition_baseMap j a).symm
    rw [hb, ← Ideal.map_map, Ideal.comap_map_of_surjective _ (X.transition_surjective j),
      ← RingHom.ker_eq_comap_bot, X.transition_ker]
    exact sup_eq_left.mpr (Ideal.map_mono (Ideal.pow_le_pow_right (by omega)))

/-- The composite transitions commute with morphisms of systems. -/
public theorem Hom.app_transitionOfLE {Y : AdicAlgebraSystem.{u, v} A I} (f : Hom X Y)
    {i j : ℕ} (h : i ≤ j) :
    (Y.transitionOfLE h).comp (f.app j) = (f.app i).comp (X.transitionOfLE h) := by
  induction j, h using Nat.le_induction with
  | base => rw [transitionOfLE_self, transitionOfLE_self]; rfl
  | succ j hij ih =>
    rw [X.transitionOfLE_succ hij, Y.transitionOfLE_succ hij, RingHom.comp_assoc,
      f.naturality, ← RingHom.comp_assoc, ih, RingHom.comp_assoc]

end Transition

section BaseChange

variable {A₁ : Type u₁} [CommRing A₁] {A₂ : Type u₂} [CommRing A₂] [Algebra A₁ A₂]
  {I₁ : Ideal A₁} (I₂ : Ideal A₂) (c : ℕ)

attribute [local instance] algebraB

/-- A composite transition of a system, as a map of `A₁`-algebras. -/
public def transitionOfLEₐ (X : AdicAlgebraSystem.{u₁, v} A₁ I₁) {i j : ℕ} (h : i ≤ j) :
    X.B j →ₐ[A₁] X.B i :=
  { X.transitionOfLE h with commutes' := X.transitionOfLE_baseMap h }

/-- A component of a morphism of systems, as a map of `A₁`-algebras. -/
public def Hom.appₐ {X Y : AdicAlgebraSystem.{u₁, v} A₁ I₁} (f : Hom X Y) (n : ℕ) :
    X.B n →ₐ[A₁] Y.B n :=
  { f.app n with commutes' := f.app_baseMap n }

/-- The level indices `c * (n + 1) - 1` of the terms entering the base change increase. -/
public theorem baseChangeIndex_le (n : ℕ) : c * (n + 1) - 1 ≤ c * (n + 1 + 1) - 1 :=
  Nat.sub_le_sub_right (Nat.mul_le_mul_left c (Nat.le_succ _)) 1

/-- The term `B_{c(n+1)} ⊗[A₁] A₂ ⧸ I₂ ^ (n + 1)` of the base change of a system, at the Lean
index `n` (the source's index `n + 1`). -/
public abbrev baseChangeTerm (X : AdicAlgebraSystem.{u₁, v} A₁ I₁) (n : ℕ) : Type (max v u₂) :=
  X.B (c * (n + 1) - 1) ⊗[A₁] (A₂ ⧸ I₂ ^ (n + 1))

/-- The transition `B_{c(n+2)} ⊗ A₂ ⧸ I₂ ^ (n + 2) → B_{c(n+1)} ⊗ A₂ ⧸ I₂ ^ (n + 1)` of the base
change of a system. -/
public noncomputable def baseChangeTransition (X : AdicAlgebraSystem.{u₁, v} A₁ I₁) (n : ℕ) :
    X.baseChangeTerm I₂ c (n + 1) →ₐ[A₁] X.baseChangeTerm I₂ c n :=
  Algebra.TensorProduct.map (X.transitionOfLEₐ (baseChangeIndex_le c n))
    (Ideal.Quotient.factorₐ A₁ (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))

/-- The term `B_{c(n+1)} ⊗[A₁] A₂ ⧸ I₂ ^ (n + 1)` of the base change of a system is of finite
type over `A₂ ⧸ I₂ ^ (n + 1)`. -/
theorem baseChangeTerm_finiteType (X : AdicAlgebraSystem.{u₁, v} A₁ I₁) (n : ℕ) :
    (Algebra.TensorProduct.includeRight.toRingHom :
      A₂ ⧸ I₂ ^ (n + 1) →+* X.baseChangeTerm I₂ c n).FiniteType := by
  have hX : (X.baseMap (c * (n + 1) - 1)).FiniteType :=
    (X.finiteType _).comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective)
  have : Algebra.FiniteType A₁ (X.B (c * (n + 1) - 1)) := hX
  have h : (Algebra.algebraMap (A₂ ⧸ I₂ ^ (n + 1))
      ((A₂ ⧸ I₂ ^ (n + 1)) ⊗[A₁] X.B (c * (n + 1) - 1))).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  let e := Algebra.TensorProduct.comm A₁ (A₂ ⧸ I₂ ^ (n + 1)) (X.B (c * (n + 1) - 1))
  convert h.comp_surjective (g := e.toRingEquiv.toRingHom) e.surjective using 1
  ext a
  exact (Algebra.TensorProduct.comm_tmul A₁ _ _).symm

/-- If `I₁ ^ c` maps into `I₂`, then `I₁ ^ (c * m)` maps into `I₂ ^ m`. -/
private theorem algebraMap_mem_pow_of_mem_pow {I₂ : Ideal A₂} {c m : ℕ}
    (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂) {a : A₁} (ha : a ∈ I₁ ^ (c * m)) :
    Algebra.algebraMap A₁ A₂ a ∈ I₂ ^ m := by
  refine (?_ : (I₁ ^ (c * m)).map (Algebra.algebraMap A₁ A₂) ≤ I₂ ^ m)
    (Ideal.mem_map_of_mem _ ha)
  rw [pow_mul, Ideal.map_pow]
  exact Ideal.pow_right_mono hmap _

/-- The kernel of the transition of the base change of a system is generated by `I₂ ^ (n + 1)`. -/
public theorem ker_baseChangeTransition (hc : 0 < c)
    (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂)
    (X : AdicAlgebraSystem.{u₁, v} A₁ I₁) (n : ℕ) :
    RingHom.ker (X.baseChangeTransition I₂ c n).toRingHom =
      (I₂ ^ (n + 1)).map ((Algebra.TensorProduct.includeRight.toRingHom :
        A₂ ⧸ I₂ ^ (n + 1 + 1) →+* X.baseChangeTerm I₂ c (n + 1)).comp
          (Ideal.Quotient.mk (I₂ ^ (n + 1 + 1)))) := by
  have hT : RingHom.ker (X.transitionOfLEₐ (baseChangeIndex_le c n)) =
      (I₁ ^ (c * (n + 1) - 1 + 1)).map (X.baseMap (c * (n + 1 + 1) - 1)) :=
    X.ker_transitionOfLE _
  have hq : RingHom.ker (Ideal.Quotient.factorₐ A₁
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I₂ ^ (n + 1 + 1) ≤ I₂ ^ (n + 1))) =
      (I₂ ^ (n + 1)).map (Ideal.Quotient.mk (I₂ ^ (n + 1 + 1))) :=
    Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  show RingHom.ker (Algebra.TensorProduct.map _ _) = _
  rw [Algebra.TensorProduct.map_ker _ _ (X.transitionOfLE_surjective _)
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))), hT, hq]
  have hR : Ideal.map (Algebra.TensorProduct.includeRight : A₂ ⧸ I₂ ^ (n + 1 + 1) →ₐ[A₁]
      X.baseChangeTerm I₂ c (n + 1)) ((I₂ ^ (n + 1)).map (Ideal.Quotient.mk (I₂ ^ (n + 1 + 1)))) =
      (I₂ ^ (n + 1)).map ((Algebra.TensorProduct.includeRight.toRingHom :
        A₂ ⧸ I₂ ^ (n + 1 + 1) →+* X.baseChangeTerm I₂ c (n + 1)).comp
          (Ideal.Quotient.mk (I₂ ^ (n + 1 + 1)))) := by
    rw [← Ideal.map_map]; rfl
  rw [hR]
  refine sup_eq_right.mpr (Ideal.map_le_iff_le_comap.mpr
    (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_))
  have hk : c * (n + 1) - 1 + 1 = c * (n + 1) := Nat.sub_add_cancel (Nat.mul_pos hc n.succ_pos)
  rw [hk] at ha
  have ha' := algebraMap_mem_pow_of_mem_pow hmap ha
  rw [Ideal.mem_comap, Ideal.mem_comap]
  have he : (Algebra.TensorProduct.includeLeft : X.B (c * (n + 1 + 1) - 1) →ₐ[A₁]
      X.baseChangeTerm I₂ c (n + 1)) (X.baseMap _ a) =
      Algebra.TensorProduct.includeRight
        (Ideal.Quotient.mk (I₂ ^ (n + 1 + 1)) (Algebra.algebraMap A₁ A₂ a)) := by
    show (X.baseMap _ a) ⊗ₜ[A₁] (1 : A₂ ⧸ I₂ ^ (n + 1 + 1)) = 1 ⊗ₜ[A₁] _
    rw [← algebraMap_B, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one]
    rfl
  show (Algebra.TensorProduct.includeLeft : X.B (c * (n + 1 + 1) - 1) →ₐ[A₁]
      X.baseChangeTerm I₂ c (n + 1)) (X.baseMap _ a) ∈ _
  rw [he]
  exact Ideal.mem_map_of_mem _ ha'

/-- The base change `(B_{cn} ⊗ A₂ ⧸ I₂ ^ n)ₙ` of a system `(Bₙ)` over `(A₁, I₁)`, a system over
`(A₂, I₂)`. -/
public noncomputable def baseChangeObj (hc : 0 < c)
    (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂)
    (X : AdicAlgebraSystem.{u₁, v} A₁ I₁) : AdicAlgebraSystem.{u₂, max v u₂} A₂ I₂ where
  B n := CommRingCat.of (X.baseChangeTerm I₂ c n)
  algebraMap n := Algebra.TensorProduct.includeRight.toRingHom
  finiteType n := X.baseChangeTerm_finiteType I₂ c n
  transition n := (X.baseChangeTransition I₂ c n).toRingHom
  transition_comp_algebraMap n := by
    ext a
    simp [baseChangeTransition]
  transition_surjective n := Algebra.TensorProduct.map_surjective _ _
    (X.transitionOfLE_surjective _) (Ideal.Quotient.factor_surjective
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
  transition_ker n := X.ker_baseChangeTransition I₂ c hc hmap n

variable {I₂ c}

/-- The base change of a morphism of systems: the tensor product of its components with the
identity of `A₂ ⧸ I₂ ^ (n + 1)`. -/
public noncomputable def baseChangeHom (hc : 0 < c)
    (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂)
    {X Y : AdicAlgebraSystem.{u₁, v} A₁ I₁} (f : Hom X Y) :
    Hom (X.baseChangeObj I₂ c hc hmap) (Y.baseChangeObj I₂ c hc hmap) where
  app n := (Algebra.TensorProduct.map (f.appₐ (c * (n + 1) - 1))
    (AlgHom.id A₁ (A₂ ⧸ I₂ ^ (n + 1)))).toRingHom
  commutes_algebraMap n := by
    ext a
    change Algebra.TensorProduct.map _ _ (1 ⊗ₜ _) = 1 ⊗ₜ _
    simp
  naturality n := by
    have h : (Y.baseChangeTransition I₂ c n).comp (Algebra.TensorProduct.map
        (f.appₐ (c * (n + 1 + 1) - 1)) (AlgHom.id A₁ (A₂ ⧸ I₂ ^ (n + 1 + 1)))) =
        (Algebra.TensorProduct.map (f.appₐ (c * (n + 1) - 1))
          (AlgHom.id A₁ (A₂ ⧸ I₂ ^ (n + 1)))).comp (X.baseChangeTransition I₂ c n) := by
      refine Algebra.TensorProduct.ext' fun x s => ?_
      simp only [baseChangeTransition, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      congr 1
      exact DFunLike.congr_fun (Hom.app_transitionOfLE X f (baseChangeIndex_le c n)) x
    exact congrArg AlgHom.toRingHom h

variable (I₂ c)

/-- **Base change of systems.** If `I₁ ^ c` maps into `I₂` for some `c ≥ 1`, then
`(Bₙ) ↦ (B_{cn} ⊗[A₁] A₂ ⧸ I₂ ^ n)` is a functor from systems over `(A₁, I₁)` to systems over
`(A₂, I₂)`. -/
public noncomputable def baseChangeFunctor (hc : 0 < c)
    (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂) :
    AdicAlgebraSystem.{u₁, v} A₁ I₁ ⥤ AdicAlgebraSystem.{u₂, max v u₂} A₂ I₂ where
  obj X := X.baseChangeObj I₂ c hc hmap
  map f := baseChangeHom hc hmap f
  map_id X := hom_ext fun n => by
    apply RingHom.ext
    intro z
    change Algebra.TensorProduct.map (AlgHom.id A₁ _) (AlgHom.id A₁ _) z = z
    rw [Algebra.TensorProduct.map_id]
    rfl
  map_comp f g := hom_ext fun n => by
    apply RingHom.ext
    intro z
    change Algebra.TensorProduct.map ((g.appₐ _).comp (f.appₐ _)) (AlgHom.id A₁ _) z =
      Algebra.TensorProduct.map (g.appₐ _) (AlgHom.id A₁ _)
        (Algebra.TensorProduct.map (f.appₐ _) (AlgHom.id A₁ _) z)
    have h := Algebra.TensorProduct.map_comp (g.appₐ (c * (n + 1) - 1)) (f.appₐ _)
      (AlgHom.id A₁ (A₂ ⧸ I₂ ^ (n + 1))) (AlgHom.id A₁ _)
    rw [AlgHom.id_comp] at h
    exact DFunLike.congr_fun h z

section Stage

variable {I₂ c}

/-- The term `B_{c(n+1)}` of a system (Lean index `c * (n + 1) - 1`) as an algebra over
`A₁ ⧸ I₁ ^ (c * (n + 1))`. -/
public noncomputable abbrev stageAlgebra (hc : 0 < c) (X : AdicAlgebraSystem.{u₁, v} A₁ I₁)
    (n : ℕ) :
    Algebra (A₁ ⧸ I₁ ^ (c * (n + 1))) (X.B (c * (n + 1) - 1)) :=
  ((X.algebraMap (c * (n + 1) - 1)).comp (Ideal.Quotient.factor (Ideal.pow_le_pow_right
    (Nat.sub_add_cancel (Nat.mul_pos hc n.succ_pos)).le))).toAlgebra

/-- The quotient `A₂ ⧸ I₂ ^ n` as an algebra over `A₁ ⧸ I₁ ^ (c * n)`, through `quotientPowMap`. -/
public noncomputable abbrev quotientPowAlgebra
    (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂) (n : ℕ) :
    Algebra (A₁ ⧸ I₁ ^ (c * n)) (A₂ ⧸ I₂ ^ n) :=
  (quotientPowMap (Algebra.algebraMap A₁ A₂) I₁ I₂ c n hmap).toAlgebra

/-- The tensor product `B_{c(n+1)} ⊗[A₁ ⧸ I₁ ^ (c(n+1))] A₂ ⧸ I₂ ^ (n + 1)`, the source's
`B_{cn} ⊗_{A_{1,cn}} A_{2,n}` at the source's index `n + 1`. -/
public def baseChangeStage (hc : 0 < c) (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂)
    (X : AdicAlgebraSystem.{u₁, v} A₁ I₁) (n : ℕ) : Type (max v u₂) :=
  letI := X.stageAlgebra hc n
  letI := quotientPowAlgebra hmap (n + 1)
  X.B (c * (n + 1) - 1) ⊗[A₁ ⧸ I₁ ^ (c * (n + 1))] (A₂ ⧸ I₂ ^ (n + 1))

/-- The ring structure of `B_{c(n+1)} ⊗[A₁ ⧸ I₁ ^ (c(n+1))] A₂ ⧸ I₂ ^ (n + 1)`. -/
public noncomputable instance (hc : 0 < c) (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂)
    (X : AdicAlgebraSystem.{u₁, v} A₁ I₁) (n : ℕ) : CommRing (X.baseChangeStage hc hmap n) :=
  letI := X.stageAlgebra hc n
  letI := quotientPowAlgebra hmap (n + 1)
  Algebra.TensorProduct.instCommRing

/-- The pure tensor `x ⊗ s` in `B_{c(n+1)} ⊗[A₁ ⧸ I₁ ^ (c(n+1))] A₂ ⧸ I₂ ^ (n + 1)`. -/
public noncomputable def baseChangeStage.tmul {hc : 0 < c}
    {hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂}
    {X : AdicAlgebraSystem.{u₁, v} A₁ I₁} {n : ℕ} (x : X.B (c * (n + 1) - 1))
    (s : A₂ ⧸ I₂ ^ (n + 1)) : X.baseChangeStage hc hmap n :=
  letI := X.stageAlgebra hc n
  letI := quotientPowAlgebra hmap (n + 1)
  x ⊗ₜ[A₁ ⧸ I₁ ^ (c * (n + 1))] s

/-- The term `B_{c(n+1)} ⊗[A₁] A₂ ⧸ I₂ ^ (n + 1)` of the base change of a system is the tensor
product over `A₁ ⧸ I₁ ^ (c(n+1))`. -/
public noncomputable def baseChangeStageEquiv (hc : 0 < c)
    (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂)
    (X : AdicAlgebraSystem.{u₁, v} A₁ I₁) (n : ℕ) :
    X.baseChangeTerm I₂ c n ≃+* X.baseChangeStage hc hmap n :=
  letI := X.stageAlgebra hc n
  letI := quotientPowAlgebra hmap (n + 1)
  haveI : IsScalarTower A₁ (A₁ ⧸ I₁ ^ (c * (n + 1))) (X.B (c * (n + 1) - 1)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A₁ (A₁ ⧸ I₁ ^ (c * (n + 1))) (A₂ ⧸ I₂ ^ (n + 1)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : TensorProduct.CompatibleSMul A₁ (A₁ ⧸ I₁ ^ (c * (n + 1))) (X.B (c * (n + 1) - 1))
      (A₂ ⧸ I₂ ^ (n + 1)) :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective _ _ Ideal.Quotient.mk_surjective
  (Algebra.TensorProduct.equivOfCompatibleSMul A₁ (A₁ ⧸ I₁ ^ (c * (n + 1))) A₁
    (X.B (c * (n + 1) - 1)) (A₂ ⧸ I₂ ^ (n + 1))).symm.toRingEquiv

/-- The identification of the two tensor products sends pure tensors to pure tensors. -/
public theorem baseChangeStageEquiv_tmul (hc : 0 < c)
    (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂)
    (X : AdicAlgebraSystem.{u₁, v} A₁ I₁) (n : ℕ) (x : X.B (c * (n + 1) - 1))
    (s : A₂ ⧸ I₂ ^ (n + 1)) :
    X.baseChangeStageEquiv hc hmap n (x ⊗ₜ[A₁] s) = baseChangeStage.tmul x s :=
  rfl

/-- The inverse identification of the two tensor products sends pure tensors to pure tensors. -/
public theorem baseChangeStageEquiv_symm_tmul (hc : 0 < c)
    (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂)
    (X : AdicAlgebraSystem.{u₁, v} A₁ I₁) (n : ℕ) (x : X.B (c * (n + 1) - 1))
    (s : A₂ ⧸ I₂ ^ (n + 1)) :
    (X.baseChangeStageEquiv hc hmap n).symm (baseChangeStage.tmul x s) = x ⊗ₜ[A₁] s := by
  rw [RingEquiv.symm_apply_eq, baseChangeStageEquiv_tmul]

end Stage

end BaseChange

end AdicAlgebraSystem

/-! ### Comparison with completed base change -/

section Agreement

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- The composite transitions of the system of quotients of a complete algebra are the quotient
maps. -/
public theorem adicQuotientFunctor_obj_transitionOfLE_mk (B : AdicFiniteTypeAlgebra.{u, v} A I)
    {i j : ℕ} (h : i ≤ j) (b : B.carrier) :
    ((adicQuotientFunctor A I).obj B).transitionOfLE h
        (Ideal.Quotient.mk (B.adicIdeal ^ (j + 1)) b) =
      Ideal.Quotient.mk (B.adicIdeal ^ (i + 1)) b := by
  induction j, h using Nat.le_induction with
  | base => rw [AdicAlgebraSystem.transitionOfLE_self]; rfl
  | succ j hij ih =>
    rw [AdicAlgebraSystem.transitionOfLE_succ _ hij]
    exact ih

variable {A₁ : Type u₁} [CommRing A₁] {A₂ : Type u₂} [CommRing A₂] [Algebra A₁ A₂]
  {I₁ : Ideal A₁} {I₂ : Ideal A₂} {c : ℕ}

attribute [local instance] Algebra.TensorProduct.rightAlgebra AdicAlgebraSystem.algebraB

/-- The quotient map `B → B ⧸ (I₁B) ^ (m + 1)` onto a term of the system of quotients, as a map of
`A₁`-algebras. -/
public def adicQuotientMkₐ (B : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁) (m : ℕ) :
    B.carrier →ₐ[A₁] ((adicQuotientFunctor A₁ I₁).obj B).B m :=
  { Ideal.Quotient.mk (B.adicIdeal ^ (m + 1)) with commutes' := fun _ => rfl }

variable (I₂ c) in
/-- The reduction `B ⊗[A₁] A₂ → B_{c(n+1)} ⊗[A₁] A₂ ⧸ I₂ ^ (n + 1)` of the tensor product onto a
term of the base change of the system of quotients of `B`. -/
public noncomputable def baseChangedAlgebraReduction (B : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁)
    (n : ℕ) : baseChangedAlgebra (A₂ := A₂) B →ₐ[A₁]
      ((adicQuotientFunctor A₁ I₁).obj B).baseChangeTerm I₂ c n :=
  Algebra.TensorProduct.map (adicQuotientMkₐ B (c * (n + 1) - 1))
    (Ideal.Quotient.mkₐ A₁ (I₂ ^ (n + 1)))

/-- The kernel of the reduction of `B ⊗[A₁] A₂` is `I₂ ^ (n + 1) (B ⊗[A₁] A₂)`. -/
public theorem ker_baseChangedAlgebraReduction (hc : 0 < c)
    (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂)
    (B : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁) (n : ℕ) :
    RingHom.ker (baseChangedAlgebraReduction I₂ c B n) =
      baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B ^ (n + 1) := by
  have hJ : baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B ^ (n + 1) =
      Ideal.map (Algebra.TensorProduct.includeRight : A₂ →ₐ[A₁] baseChangedAlgebra (A₂ := A₂) B)
        (I₂ ^ (n + 1)) := by
    rw [baseChangedIdeal, ← Ideal.map_pow]
  have hq : RingHom.ker (adicQuotientMkₐ B (c * (n + 1) - 1)) =
      B.adicIdeal ^ (c * (n + 1) - 1 + 1) := Ideal.mk_ker
  have hq' : RingHom.ker (Ideal.Quotient.mkₐ A₁ (I₂ ^ (n + 1))) = I₂ ^ (n + 1) :=
    Ideal.Quotient.mkₐ_ker A₁ _
  rw [baseChangedAlgebraReduction, Algebra.TensorProduct.map_ker _ _
    Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective, hq, hq', hJ]
  refine sup_eq_right.mpr ?_
  rw [AdicFiniteTypeAlgebra.adicIdeal, ← Ideal.map_pow,
    Nat.sub_add_cancel (Nat.mul_pos hc n.succ_pos)]
  refine Ideal.map_le_iff_le_comap.mpr (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_)
  have ha' := AdicAlgebraSystem.algebraMap_mem_pow_of_mem_pow hmap ha
  rw [Ideal.mem_comap, Ideal.mem_comap]
  show Algebra.algebraMap A₁ B.carrier a ⊗ₜ[A₁] (1 : A₂) ∈ _
  rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
  exact Ideal.mem_map_of_mem _ ha'

/-- The reduction of `B ⊗[A₁] A₂` onto a term of the base change of the system of quotients
of `B` is onto. -/
public theorem baseChangedAlgebraReduction_surjective (B : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁)
    (n : ℕ) : Function.Surjective (baseChangedAlgebraReduction I₂ c B n) :=
  Algebra.TensorProduct.map_surjective _ _ Ideal.Quotient.mk_surjective
    Ideal.Quotient.mk_surjective

/-- The extension of `I₂ ^ (n + 1)` to the completed base change is the kernel of the evaluation
of the completion at level `n + 1`. -/
public theorem completedBaseChange_adicIdeal_pow_eq_ker (hI₂ : I₂.FG)
    (B : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁)
    (n : ℕ) :
    (I₂.map (algebraMap A₂ (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B))) ^ (n + 1) =
      RingHom.ker (AdicCompletion.evalₐ (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B)
        (n + 1)).toRingHom := by
  rw [AdicCompletion.ker_evalₐ _ (baseChangedIdeal_fg B hI₂), ← baseChangedIdeal_completionMap_eq]

/-- The `n`-th quotient of the completed base change `(B ⊗[A₁] A₂)^` is the term
`B_{c(n+1)} ⊗[A₁] A₂ ⧸ I₂ ^ (n + 1)` of the base change of the system of quotients of `B`. -/
public noncomputable def completedBaseChangeQuotientEquiv (hc : 0 < c)
    (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂) (hI₂ : I₂.FG)
    (B : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁) (n : ℕ) :
    completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B ⧸
        (I₂.map (algebraMap A₂ (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B))) ^ (n + 1)
      ≃+* ((adicQuotientFunctor A₁ I₁).obj B).baseChangeTerm I₂ c n :=
  ((Ideal.quotEquivOfEq (completedBaseChange_adicIdeal_pow_eq_ker hI₂ B n)).trans
    (RingHom.quotientKerEquivOfSurjective (AdicCompletion.surjective_evalₐ _ (n + 1)))).trans
    ((Ideal.quotEquivOfEq (ker_baseChangedAlgebraReduction hc hmap B n).symm).trans
      (RingHom.quotientKerEquivOfSurjective (baseChangedAlgebraReduction_surjective B n)))

/-- The comparison sends the class of the image of `x ∈ B ⊗[A₁] A₂` to its reduction. -/
public theorem completedBaseChangeQuotientEquiv_mk_of (hc : 0 < c)
    (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂) (hI₂ : I₂.FG)
    (B : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁)
    (n : ℕ) (x : baseChangedAlgebra (A₂ := A₂) B) :
    completedBaseChangeQuotientEquiv hc hmap hI₂ B n
        (Ideal.Quotient.mk _ (AdicCompletion.of (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B) _ x)) =
      baseChangedAlgebraReduction I₂ c B n x := by
  simp only [completedBaseChangeQuotientEquiv, RingEquiv.trans_apply, AlgHom.toRingHom_eq_coe]
  rfl

/-- Two ring maps out of a quotient of the completed base change `(B ⊗[A₁] A₂)^` agree as soon as
they agree on the classes of the images of the elements of `B ⊗[A₁] A₂`. -/
public theorem completedBaseChangeQuotient_ringHom_ext (hI₂ : I₂.FG)
    (B : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁) (n : ℕ) {T : Type*} [Semiring T]
    {φ ψ : completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B ⧸
        (I₂.map (algebraMap A₂ (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B))) ^ (n + 1)
      →+* T}
    (h : ∀ x : baseChangedAlgebra (A₂ := A₂) B,
      φ (Ideal.Quotient.mk _ (AdicCompletion.of (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B) _ x)) =
        ψ (Ideal.Quotient.mk _
          (AdicCompletion.of (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B) _ x))) :
    φ = ψ := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun y => ?_)
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B) (n + 1) y)
  have hy : Ideal.Quotient.mk ((I₂.map (algebraMap A₂
      (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B))) ^ (n + 1)) y =
      Ideal.Quotient.mk _ (AdicCompletion.of (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B) _ p) := by
    rw [Ideal.Quotient.eq, completedBaseChange_adicIdeal_pow_eq_ker hI₂ B n, RingHom.mem_ker]
    show AdicCompletion.evalₐ _ (n + 1) (y - _) = 0
    rw [map_sub, AdicCompletion.evalₐ_of, hp, sub_self]
  simp only [RingHom.comp_apply]
  rw [hy, h]

/-- The transitions of the base change of the system of quotients of `B` are compatible with the
reductions of `B ⊗[A₁] A₂`. -/
public theorem baseChangeTransition_comp_baseChangedAlgebraReduction
    (B : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁) (n : ℕ) :
    (((adicQuotientFunctor A₁ I₁).obj B).baseChangeTransition I₂ c n).comp
        (baseChangedAlgebraReduction I₂ c B (n + 1)) =
      baseChangedAlgebraReduction I₂ c B n := by
  refine Algebra.TensorProduct.ext' fun b a => ?_
  simp only [AlgHom.comp_apply, baseChangedAlgebraReduction, Algebra.TensorProduct.map_tmul,
    AdicAlgebraSystem.baseChangeTransition]
  congr 1
  exact adicQuotientFunctor_obj_transitionOfLE_mk B _ b

/-- **Agreement of the two base changes.** If `I₂` is finitely generated, the quotient systems
of the completed base change `(B ⊗[A₁] A₂)^` are the base changes of the quotient systems of
`B`. -/
public noncomputable def completedBaseChangeAgreement (hc : 0 < c)
    (hmap : (I₁ ^ c).map (Algebra.algebraMap A₁ A₂) ≤ I₂) (hI₂ : I₂.FG) :
    completedBaseChangeFunctor I₁ I₂ c hc hmap hI₂ ⋙ adicQuotientFunctor A₂ I₂ ≅
      adicQuotientFunctor A₁ I₁ ⋙ AdicAlgebraSystem.baseChangeFunctor I₂ c hc hmap :=
  NatIso.ofComponents
    (fun B => AdicAlgebraSystem.isoOfRingEquiv
      (fun n => completedBaseChangeQuotientEquiv hc hmap hI₂ B n)
      (fun n => by
        refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
        change completedBaseChangeQuotientEquiv hc hmap hI₂ B n (Ideal.Quotient.mk _
          (AdicCompletion.of _ _ (Algebra.TensorProduct.includeRight a))) =
            (1 : ((adicQuotientFunctor A₁ I₁).obj B).B (c * (n + 1) - 1)) ⊗ₜ[A₁]
              Ideal.Quotient.mk (I₂ ^ (n + 1)) a
        rw [completedBaseChangeQuotientEquiv_mk_of]
        exact Algebra.TensorProduct.map_tmul _ _ _ _)
      (fun n => completedBaseChangeQuotient_ringHom_ext hI₂ B (n + 1) fun x => by
        change ((adicQuotientFunctor A₁ I₁).obj B).baseChangeTransition I₂ c n
            (completedBaseChangeQuotientEquiv hc hmap hI₂ B (n + 1)
              (Ideal.Quotient.mk _ (AdicCompletion.of _ _ x))) =
          completedBaseChangeQuotientEquiv hc hmap hI₂ B n
            (Ideal.Quotient.mk _ (AdicCompletion.of _ _ x))
        rw [completedBaseChangeQuotientEquiv_mk_of, completedBaseChangeQuotientEquiv_mk_of]
        exact DFunLike.congr_fun (baseChangeTransition_comp_baseChangedAlgebraReduction B n) x))
    (fun {B B'} f => AdicAlgebraSystem.hom_ext fun n =>
      completedBaseChangeQuotient_ringHom_ext hI₂ B n fun x => by
        change completedBaseChangeQuotientEquiv hc hmap hI₂ B' n (Ideal.Quotient.mk
            ((I₂.map (algebraMap A₂ (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B'))) ^
              (n + 1))
            (completedBaseChangeMap (A₂ := A₂) (I₂ := I₂) f
              (AdicCompletion.of (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B) _ x))) =
          Algebra.TensorProduct.map (AdicAlgebraSystem.Hom.appₐ
              ((adicQuotientFunctor A₁ I₁).map f) (c * (n + 1) - 1))
            (AlgHom.id A₁ (A₂ ⧸ I₂ ^ (n + 1)))
            (completedBaseChangeQuotientEquiv hc hmap hI₂ B n
              (Ideal.Quotient.mk _ (AdicCompletion.of _ _ x)))
        rw [completedBaseChangeMap_of, completedBaseChangeQuotientEquiv_mk_of,
          completedBaseChangeQuotientEquiv_mk_of, ← AlgHom.comp_apply, ← AlgHom.comp_apply]
        congr 1
        refine Algebra.TensorProduct.ext' fun b a => ?_
        simp only [AlgHom.comp_apply, baseChangedAlgebraReduction, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply]
        rfl)

end Agreement

/-! ### Stacks 0AL5 -/

section Statement

variable (A₁ : Type u₁) [CommRing A₁] (A₂ : Type u₂) [CommRing A₂] [Algebra A₁ A₂]
  (I₁ : Ideal A₁) (I₂ : Ideal A₂) {c : ℕ} (hc : 0 < c)
  (hmap : (I₁ ^ c).map (algebraMap A₁ A₂) ≤ I₂)

/-- The base change functors of Stacks 0AL5 attached to a ring map `A₁ → A₂` and ideals
`I₁ ⊆ A₁`, `I₂ ⊆ A₂` with `I₁ ^ c` mapping into `I₂`, `c ≥ 1`:

* the ring maps `A₁ ⧸ I₁ ^ (c n) → A₂ ⧸ I₂ ^ n`;
* a functor on systems whose value on `(Bₙ)` has terms `B_{cn} ⊗[A₁ ⧸ I₁ ^ (cn)] A₂ ⧸ I₂ ^ n`,
  with the transitions and the action on morphisms induced by those of `(Bₙ)`; the Lean index
  `n` of a system stands for the source's `n + 1`, so the term at index `n` is the source's term
  at `n + 1`;
* for `I₂` finitely generated, the completed base change `B ↦ (B ⊗[A₁] A₂)^`;
* for `I₁` and `I₂` finitely generated, an isomorphism between the two composites through the
  equivalences `B ↦ (B ⧸ IⁿB)ₙ` of Stacks 0AJP. -/
public structure AdicBaseChange where
  /-- The ring map `A₁ ⧸ I₁ ^ (c n) → A₂ ⧸ I₂ ^ n`. -/
  quotientMap (n : ℕ) : A₁ ⧸ I₁ ^ (c * n) →+* A₂ ⧸ I₂ ^ n
  /-- The ring map `A₁ ⧸ I₁ ^ (c n) → A₂ ⧸ I₂ ^ n` is induced by `A₁ → A₂`. -/
  quotientMap_mk (n : ℕ) (a : A₁) :
    quotientMap n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (algebraMap A₁ A₂ a)
  /-- The base change functor on systems. -/
  systemFunctor : AdicAlgebraSystem.{u₁, v} A₁ I₁ ⥤ AdicAlgebraSystem.{u₂, max v u₂} A₂ I₂
  /-- The term of the base change of `(Bₙ)` at the source's index `n + 1` is
  `B_{c(n+1)} ⊗[A₁ ⧸ I₁ ^ (c(n+1))] A₂ ⧸ I₂ ^ (n + 1)`. -/
  stageEquiv (X : AdicAlgebraSystem.{u₁, v} A₁ I₁) (n : ℕ) :
    (systemFunctor.obj X).B n ≃+* X.baseChangeStage hc hmap n
  /-- The structure map of a term of the base change is `s ↦ 1 ⊗ s`. -/
  stageEquiv_algebraMap (X : AdicAlgebraSystem.{u₁, v} A₁ I₁) (n : ℕ) (s : A₂ ⧸ I₂ ^ (n + 1)) :
    stageEquiv X n ((systemFunctor.obj X).algebraMap n s) =
      AdicAlgebraSystem.baseChangeStage.tmul 1 s
  /-- The transitions of the base change are induced by those of the system and of the
  quotients of `A₂`. -/
  stageEquiv_transition (X : AdicAlgebraSystem.{u₁, v} A₁ I₁) (n : ℕ)
    (x : X.B (c * (n + 1 + 1) - 1)) (s : A₂ ⧸ I₂ ^ (n + 1 + 1)) :
    stageEquiv X n ((systemFunctor.obj X).transition n
        ((stageEquiv X (n + 1)).symm (AdicAlgebraSystem.baseChangeStage.tmul x s))) =
      AdicAlgebraSystem.baseChangeStage.tmul
        (X.transitionOfLE (AdicAlgebraSystem.baseChangeIndex_le c n) x)
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) s)
  /-- The base change of a morphism of systems acts by its components on the first factor. -/
  stageEquiv_map {X Y : AdicAlgebraSystem.{u₁, v} A₁ I₁} (f : X ⟶ Y) (n : ℕ)
    (x : X.B (c * (n + 1) - 1)) (s : A₂ ⧸ I₂ ^ (n + 1)) :
    stageEquiv Y n (AdicAlgebraSystem.Hom.app (systemFunctor.map f) n
        ((stageEquiv X n).symm (AdicAlgebraSystem.baseChangeStage.tmul x s))) =
      AdicAlgebraSystem.baseChangeStage.tmul (AdicAlgebraSystem.Hom.app f _ x) s
  /-- For `I₂` finitely generated, the completed base change `B ↦ (B ⊗[A₁] A₂)^`. -/
  completed (hI₂ : I₂.FG) : CompletedBaseChange (A₁ := A₁) (A₂ := A₂) (I₁ := I₁) (I₂ := I₂)
  /-- For `I₁` and `I₂` finitely generated, the two base change functors agree through the
  equivalences `B ↦ (B ⧸ IⁿB)ₙ`. -/
  agree (hI₁ : I₁.FG) (hI₂ : I₂.FG) :
    (completed hI₂).functor ⋙ (adicQuotientEquivalence A₂ I₂ hI₂).functor ≅
      (adicQuotientEquivalence A₁ I₁ hI₁).functor ⋙ systemFunctor

attribute [local instance] AdicAlgebraSystem.algebraB in
/-- **Stacks Project, Tag 0AL5.** Let `A₁ → A₂` be a ring map and `I₁ ⊆ A₁`, `I₂ ⊆ A₂` ideals
with `I₁ ^ c` mapping into `I₂` for some `c ≥ 1`. This induces ring maps
`A₁ ⧸ I₁ ^ (cn) → A₂ ⧸ I₂ ^ n`, and there is a base change functor `(Bₙ) ↦ (B_{cn} ⊗ A₂ ⧸ I₂ ^ n)`
between the categories of systems. If `I₂` is finitely generated there is a base change functor
`B ↦ (B ⊗[A₁] A₂)^` between the categories of complete algebras, and if both ideals are
finitely generated the two base change functors agree via the equivalences `B ↦ (B ⧸ IⁿB)ₙ`. -/
@[stacks 0AL5]
public noncomputable def adicBaseChange :
    AdicBaseChange.{v, u₁, u₂} A₁ A₂ I₁ I₂ hc hmap where
  quotientMap n := quotientPowMap (algebraMap A₁ A₂) I₁ I₂ c n hmap
  quotientMap_mk n a := quotientPowMap_mk _ I₁ I₂ c n hmap a
  systemFunctor := AdicAlgebraSystem.baseChangeFunctor I₂ c hc hmap
  stageEquiv X n := X.baseChangeStageEquiv hc hmap n
  stageEquiv_algebraMap X n s := rfl
  stageEquiv_transition X n x s := by
    change X.baseChangeStageEquiv hc hmap n (X.baseChangeTransition I₂ c n
      ((X.baseChangeStageEquiv hc hmap (n + 1)).symm
        (AdicAlgebraSystem.baseChangeStage.tmul x s))) = _
    rw [AdicAlgebraSystem.baseChangeStageEquiv_symm_tmul]
    rfl
  stageEquiv_map {X Y} f n x s := by
    change Y.baseChangeStageEquiv hc hmap n (Algebra.TensorProduct.map
      (AdicAlgebraSystem.Hom.appₐ f (c * (n + 1) - 1)) (AlgHom.id A₁ (A₂ ⧸ I₂ ^ (n + 1)))
      ((X.baseChangeStageEquiv hc hmap n).symm
        (AdicAlgebraSystem.baseChangeStage.tmul x s))) = _
    rw [AdicAlgebraSystem.baseChangeStageEquiv_symm_tmul]
    rfl
  completed hI₂ := completedBaseChange I₁ I₂ c hc hmap hI₂
  agree _ hI₂ := completedBaseChangeAgreement hc hmap hI₂

end Statement

end Rig
