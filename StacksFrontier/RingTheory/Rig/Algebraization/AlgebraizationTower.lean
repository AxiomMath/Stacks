module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.RingTheory.NaiveCotangent.PresentationHomology
public import StacksFrontier.RingTheory.Rig.Algebraization.AlgebraizationTowerComparison
public import StacksFrontier.RingTheory.Rig.Algebraization.PrincipalIsomorphism
public import StacksFrontier.RingTheory.Rig.Algebraization.UniformCotangent
public import StacksFrontier.RingTheory.Rig.CategoryLimit
public import StacksFrontier.RingTheory.Rig.RigEtaleLocus
public import StacksFrontier.RingTheory.Rig.RigEtaleTFAE

/-!
# Compatible systems of algebraizations of the quotients `B ⧸ aⁿ⁺¹ B`

Let `A` be Noetherian, `a ∈ I`, and `B` rig-étale over `(A, I)`.  An `AlgebraizationTower` is a
system of finite type `A ⧸ (aⁿ⁺¹)`-algebras `Cₙ` with surjections `Cₙ₊₁ → Cₙ` of kernel
`aⁿ⁺¹ Cₙ₊₁` and identifications `Cₙ^∧ ≅ B ⧸ aⁿ⁺¹ B`. Its limit `B'` is rig-étale over `(A, (a))`
and algebraizes `B`.

## Main definitions

* `Rig.AlgebraizationTowerData`: the data of such a system with no condition on the levels.
* `Rig.AlgebraizationTowerData.system`: the system as an inverse system of finite type
  `A ⧸ (a)ⁿ⁺¹`-algebras, and `Rig.AlgebraizationTowerData.limit` its limit `B' = lim Cₙ`.
* `Rig.AlgebraizationTowerData.toCarrier`: the comparison map `B' → B`.
* `Rig.AlgebraizationTower`: the system with levels étale off `V(I)`;
  `Rig.AlgebraizationTower.system`, `Rig.AlgebraizationTower.limit` and
  `Rig.AlgebraizationTower.toCarrier` are those of its data.

## Main results

* `Rig.AlgebraizationTowerData.isBijectiveMod_toCarrier`: `B' → B` induces isomorphisms
  `B' ⧸ IⁿB' ≅ B ⧸ IⁿB`.
* `Rig.AlgebraizationTower.isRigEtale_limit`: `B'` is rig-étale over `(A, (a))`.
* `Rig.AlgebraizationTower.exists_algebraization`: there is a finite type `A`-algebra `D` whose
  `I`-adic completion is `B`.
-/

@[expose] public section

namespace Rig

universe u

/-- The data of a compatible system of algebraizations of the quotients `B ⧸ aⁿ⁺¹ B`, with no
condition on the levels: finite type `A ⧸ (aⁿ⁺¹)`-algebras `Cₙ` with surjections `Cₙ₊₁ → Cₙ` of
kernel `aⁿ⁺¹ Cₙ₊₁` and `A`-algebra isomorphisms `Cₙ^∧ ≅ B ⧸ aⁿ⁺¹ B` of `I`-adic completions
compatible with the transitions.  The Lean index `n` stands for the source's `C_{n+1}`. -/
public structure AlgebraizationTowerData {A : Type u} [CommRing A] (I : Ideal A) (a : A)
    (B : Type u) [CommRing B] [Algebra A B] where
  /-- The algebra `C_{n+1}`. -/
  C : ℕ → Type u
  [commRing : ∀ n, CommRing (C n)]
  [algebraQuot : ∀ n, Algebra (A ⧸ Ideal.span {a ^ (n + 1)}) (C n)]
  [algebra : ∀ n, Algebra A (C n)]
  [isScalarTower : ∀ n, IsScalarTower A (A ⧸ Ideal.span {a ^ (n + 1)}) (C n)]
  [finiteType : ∀ n, Algebra.FiniteType (A ⧸ Ideal.span {a ^ (n + 1)}) (C n)]
  /-- The transition `C_{n+2} → C_{n+1}`. -/
  transition : ∀ n, C (n + 1) →ₐ[A] C n
  transition_surjective : ∀ n, Function.Surjective (transition n)
  transition_ker : ∀ n, RingHom.ker (transition n).toRingHom =
    (Ideal.span {a ^ (n + 1)}).map (algebraMap A (C (n + 1)))
  /-- The identification of the completion of `C_{n+1}` with `B ⧸ aⁿ⁺¹ B`. -/
  equiv : ∀ n, AdicCompletion (I.map (algebraMap A (C n))) (C n) ≃ₐ[A]
    B ⧸ (Ideal.span {a ^ (n + 1)}).map (algebraMap A B)
  /-- The identifications are compatible with the transitions. -/
  equiv_transition : ∀ n (x : C (n + 1)),
    equiv n (algebraMap (C n) _ (transition n x)) =
      Ideal.Quotient.factor (Ideal.map_mono (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow a (Nat.le_succ (n + 1)))))
        (equiv (n + 1) (algebraMap (C (n + 1)) _ x))

attribute [instance] AlgebraizationTowerData.commRing AlgebraizationTowerData.algebraQuot
  AlgebraizationTowerData.algebra AlgebraizationTowerData.isScalarTower
  AlgebraizationTowerData.finiteType

/-- A compatible system of algebraizations of the quotients `B ⧸ aⁿ⁺¹ B`: finite type
`A ⧸ (aⁿ⁺¹)`-algebras `Cₙ`, étale over the complement of `V(I)`,
with surjections `Cₙ₊₁ → Cₙ` of kernel `aⁿ⁺¹ Cₙ₊₁` and `A`-algebra isomorphisms
`Cₙ^∧ ≅ B ⧸ aⁿ⁺¹ B` of `I`-adic completions compatible with the transitions.  The Lean index
`n` stands for the source's `C_{n+1}`. -/
public structure AlgebraizationTower {A : Type u} [CommRing A] (I : Ideal A) (a : A)
    (B : Type u) [CommRing B] [Algebra A B] where
  /-- The algebra `C_{n+1}`. -/
  C : ℕ → Type u
  [commRing : ∀ n, CommRing (C n)]
  [algebraQuot : ∀ n, Algebra (A ⧸ Ideal.span {a ^ (n + 1)}) (C n)]
  [algebra : ∀ n, Algebra A (C n)]
  [isScalarTower : ∀ n, IsScalarTower A (A ⧸ Ideal.span {a ^ (n + 1)}) (C n)]
  [finiteType : ∀ n, Algebra.FiniteType (A ⧸ Ideal.span {a ^ (n + 1)}) (C n)]
  /-- Each `C_{n+1}` is étale over the complement of `V(I)`. -/
  etale : ∀ n, IsEtaleOutside (I.map (Ideal.Quotient.mk (Ideal.span {a ^ (n + 1)}))) (C n)
  /-- The transition `C_{n+2} → C_{n+1}`. -/
  transition : ∀ n, C (n + 1) →ₐ[A] C n
  transition_surjective : ∀ n, Function.Surjective (transition n)
  transition_ker : ∀ n, RingHom.ker (transition n).toRingHom =
    (Ideal.span {a ^ (n + 1)}).map (algebraMap A (C (n + 1)))
  /-- The identification of the completion of `C_{n+1}` with `B ⧸ aⁿ⁺¹ B`. -/
  equiv : ∀ n, AdicCompletion (I.map (algebraMap A (C n))) (C n) ≃ₐ[A]
    B ⧸ (Ideal.span {a ^ (n + 1)}).map (algebraMap A B)
  /-- The identifications are compatible with the transitions. -/
  equiv_transition : ∀ n (x : C (n + 1)),
    equiv n (algebraMap (C n) _ (transition n x)) =
      Ideal.Quotient.factor (Ideal.map_mono (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow a (Nat.le_succ (n + 1)))))
        (equiv (n + 1) (algebraMap (C (n + 1)) _ x))

attribute [instance] AlgebraizationTower.commRing AlgebraizationTower.algebraQuot
  AlgebraizationTower.algebra AlgebraizationTower.isScalarTower AlgebraizationTower.finiteType

namespace AlgebraizationTower

section Ideals

variable {A : Type u} [CommRing A] {I : Ideal A} {a : A} {B : Type u} [CommRing B] [Algebra A B]

/-- The ideals `aⁿ⁺¹ B` decrease with `n`. -/
theorem stage_le {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.span {a ^ (n + 1)}).map (algebraMap A B) ≤
      (Ideal.span {a ^ (m + 1)}).map (algebraMap A B) :=
  Ideal.map_mono (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (by omega)))

private theorem stage_le_pow (ha : a ∈ I) (n : ℕ) :
    (Ideal.span {a ^ (n + 1)}).map (algebraMap A B) ≤ (I ^ n).map (algebraMap A B) :=
  Ideal.map_mono ((Ideal.span_singleton_le_iff_mem _).mpr (by
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ha n)))

end Ideals

end AlgebraizationTower

namespace AlgebraizationTowerData

section System

variable {A : Type u} [CommRing A] {I : Ideal A} {a : A} {B : Type u} [CommRing B] [Algebra A B]

/-- The structure map `A ⧸ (a)ⁿ⁺¹ → Cₙ` of the system, through `(a)ⁿ⁺¹ = (aⁿ⁺¹)`. -/
noncomputable def systemAlgebraMap (T : AlgebraizationTowerData I a B) (n : ℕ) :
    A ⧸ Ideal.span {a} ^ (n + 1) →+* T.C n :=
  (algebraMap (A ⧸ Ideal.span {a ^ (n + 1)}) (T.C n)).comp
    (Ideal.quotEquivOfEq (Ideal.span_singleton_pow a (n + 1))).toRingHom

/-- The structure map of the system composed with the quotient map is the structure map of
`Cₙ` as an `A`-algebra. -/
theorem systemAlgebraMap_comp_mk (T : AlgebraizationTowerData I a B) (n : ℕ) :
    (T.systemAlgebraMap n).comp (Ideal.Quotient.mk (Ideal.span {a} ^ (n + 1))) =
      algebraMap A (T.C n) := by
  refine RingHom.ext fun x ↦ ?_
  simp only [systemAlgebraMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, Ideal.quotEquivOfEq_mk]
  exact (IsScalarTower.algebraMap_apply A (A ⧸ Ideal.span {a ^ (n + 1)}) (T.C n) x).symm

/-- The system as an inverse system of finite type `A ⧸ (a)ⁿ⁺¹`-algebras. -/
noncomputable def system (T : AlgebraizationTowerData I a B) :
    AdicAlgebraSystem.{u, u} A (Ideal.span {a}) where
  B n := CommRingCat.of (T.C n)
  algebraMap n := T.systemAlgebraMap n
  finiteType n :=
    (RingHom.finiteType_algebraMap.mpr inferInstance).comp
      (RingHom.FiniteType.of_surjective _ (Ideal.quotEquivOfEq _).surjective)
  transition n := (T.transition n).toRingHom
  transition_comp_algebraMap n := by
    change (T.transition n).toRingHom.comp
        ((T.systemAlgebraMap (n + 1)).comp (Ideal.Quotient.mk _)) =
      (T.systemAlgebraMap n).comp (Ideal.Quotient.mk _)
    rw [T.systemAlgebraMap_comp_mk, T.systemAlgebraMap_comp_mk]
    exact RingHom.ext (T.transition n).commutes
  transition_surjective := T.transition_surjective
  transition_ker n := by
    change RingHom.ker (T.transition n).toRingHom =
      (Ideal.span {a} ^ (n + 1)).map ((T.systemAlgebraMap (n + 1)).comp (Ideal.Quotient.mk _))
    rw [T.systemAlgebraMap_comp_mk, Ideal.span_singleton_pow]
    exact T.transition_ker n

/-- The limit `B' = lim Cₙ` of the system, an `(a)`-adically complete `A`-algebra. -/
noncomputable abbrev limit (T : AlgebraizationTowerData I a B) :
    AdicFiniteTypeAlgebra.{u, u} A (Ideal.span {a}) :=
  T.system.limitObj (Submodule.fg_span_singleton a)

/-- The projection `B' → Cₙ`, as a map of `A`-algebras. -/
noncomputable def proj (T : AlgebraizationTowerData I a B) (n : ℕ) :
    T.limit.carrier →ₐ[A] T.C n :=
  { T.system.limitProj n with
    commutes' := fun x ↦ (T.system.limitVal_algebraMap x n).trans
      (DFunLike.congr_fun (T.systemAlgebraMap_comp_mk n) x) }

/-- The projection `B' → Cₙ` is surjective. -/
theorem proj_surjective (T : AlgebraizationTowerData I a B) (n : ℕ) :
    Function.Surjective (T.proj n) :=
  T.system.limitProj_surjective n

/-- The kernel of `B' → Cₙ` is `aⁿ⁺¹ B'`. -/
theorem ker_proj (T : AlgebraizationTowerData I a B) (n : ℕ) :
    RingHom.ker (T.proj n : T.limit.carrier →+* T.C n) =
      (Ideal.span {a ^ (n + 1)}).map (algebraMap A T.limit.carrier) := by
  rw [← Ideal.span_singleton_pow, Ideal.map_pow]
  exact T.system.ker_limitProj (Submodule.fg_span_singleton a) n

/-- The projections `B' → Cₙ` are compatible with the transitions. -/
theorem transition_proj (T : AlgebraizationTowerData I a B) (n : ℕ) (x : T.limit.carrier) :
    T.transition n (T.proj (n + 1) x) = T.proj n x :=
  T.system.transition_limitVal x n

/-- The quotient `B' ⧸ aⁿ⁺¹ B'` is `Cₙ`. -/
noncomputable def quotientEquiv (T : AlgebraizationTowerData I a B) (n : ℕ) :
    (T.limit.carrier ⧸ (Ideal.span {a ^ (n + 1)}).map (algebraMap A T.limit.carrier)) ≃ₐ[A]
      T.C n :=
  (Ideal.quotientEquivAlgOfEq A (T.ker_proj n).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (T.proj_surjective n))

/-- The map `B' → Cₙ → Cₙ^∧ ≅ B ⧸ aⁿ⁺¹ B`. -/
noncomputable def stage (T : AlgebraizationTowerData I a B) (n : ℕ) :
    T.limit.carrier →ₐ[A] B ⧸ (Ideal.span {a ^ (n + 1)}).map (algebraMap A B) :=
  (T.equiv n : _ →ₐ[A] _).comp
    ((toAdicCompletionAlgHom (I.map (algebraMap A (T.C n)))).comp (T.proj n))

/-- The maps `B' → B ⧸ aⁿ⁺¹ B` are compatible with the quotient maps, one step at a time. -/
theorem stage_succ (T : AlgebraizationTowerData I a B) (n : ℕ) (x : T.limit.carrier) :
    T.stage n x = Ideal.Quotient.factor (AlgebraizationTower.stage_le n.le_succ)
      (T.stage (n + 1) x) := by
  have h := T.equiv_transition n (T.proj (n + 1) x)
  rwa [T.transition_proj] at h

/-- The maps `B' → B ⧸ aⁿ⁺¹ B` are compatible with the quotient maps. -/
theorem factor_stage (T : AlgebraizationTowerData I a B) {m n : ℕ} (hmn : m ≤ n)
    (x : T.limit.carrier) :
    Ideal.Quotient.factor (AlgebraizationTower.stage_le hmn) (T.stage n x) = T.stage m x := by
  induction n, hmn using Nat.le_induction with
  | base =>
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (T.stage m x)
    rw [← hb, Ideal.Quotient.factor_mk]
  | succ n hmn ih =>
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (T.stage (n + 1) x)
    rw [← hb, Ideal.Quotient.factor_mk, ← ih, T.stage_succ n x, ← hb, Ideal.Quotient.factor_mk,
      Ideal.Quotient.factor_mk]

/-- The map `B' → B ⧸ IⁿB` through `B ⧸ aⁿ⁺¹ B`. -/
noncomputable def levelMap (T : AlgebraizationTowerData I a B) (ha : a ∈ I) (n : ℕ) :
    T.limit.carrier →ₐ[A] B ⧸ (I.map (algebraMap A B)) ^ n :=
  (Ideal.Quotient.factorₐ A (by
    rw [← Ideal.map_pow]
    exact AlgebraizationTower.stage_le_pow ha n)).comp (T.stage n)

/-- The maps `B' → B ⧸ IⁿB` form a compatible family. -/
theorem levelMap_compat (T : AlgebraizationTowerData I a B) (ha : a ∈ I) {m n : ℕ}
    (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp (T.levelMap ha n) =
      T.levelMap ha m := by
  refine AlgHom.ext fun x ↦ ?_
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (T.stage n x)
  have h := T.factor_stage hmn x
  rw [← hb, Ideal.Quotient.factor_mk] at h
  simp only [levelMap, AlgHom.comp_apply]
  rw [← hb, ← h, Ideal.Quotient.factorₐ_apply_mk, Ideal.Quotient.factorₐ_apply_mk,
    Ideal.Quotient.factorₐ_apply_mk]

variable [IsAdicComplete (I.map (algebraMap A B)) B]

/-- The comparison map `B' → B`, the limit of the maps `B' → B ⧸ IⁿB`. -/
noncomputable def toCarrier (T : AlgebraizationTowerData I a B) (ha : a ∈ I) :
    T.limit.carrier →ₐ[A] B where
  toRingHom := (AdicCompletion.ofAlgEquiv (I.map (algebraMap A B))).symm.toRingHom.comp
    (AdicCompletion.liftAlgHom (I.map (algebraMap A B)) (T.levelMap ha)
      (T.levelMap_compat ha)).toRingHom
  commutes' r := by
    change (AdicCompletion.ofAlgEquiv (I.map (algebraMap A B))).symm
      (AdicCompletion.liftAlgHom (I.map (algebraMap A B)) (T.levelMap ha) (T.levelMap_compat ha)
        (algebraMap A T.limit.carrier r)) = algebraMap A B r
    rw [AlgHom.commutes, AdicCompletion.algebraMap_apply, AdicCompletion.ofAlgEquiv_symm_of]

/-- Modulo `IⁿB`, the comparison map `B' → B` is the map `B' → B ⧸ IⁿB`. -/
theorem mk_toCarrier (T : AlgebraizationTowerData I a B) (ha : a ∈ I) (n : ℕ)
    (x : T.limit.carrier) :
    Ideal.Quotient.mk ((I.map (algebraMap A B)) ^ n) (T.toCarrier ha x) = T.levelMap ha n x := by
  change Ideal.Quotient.mk _ ((AdicCompletion.ofAlgEquiv _).symm
    (AdicCompletion.liftAlgHom _ (T.levelMap ha) (T.levelMap_compat ha) x)) = _
  rw [AdicCompletion.mk_ofAlgEquiv_symm, AdicCompletion.evalₐ_liftAlgHom]

/-- The comparison map `B' → B` induces isomorphisms `B' ⧸ IⁿB' ≅ B ⧸ IⁿB`. -/
theorem isBijectiveMod_toCarrier [IsNoetherianRing A] (T : AlgebraizationTowerData I a B)
    (ha : a ∈ I) (n : ℕ) :
    IsBijectiveMod (I ^ n) (T.toCarrier ha) := by
  have hle : Ideal.span {a ^ (n + 1)} ≤ I ^ n := (Ideal.span_singleton_le_iff_mem _).mpr (by
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ha n))
  have hq : IsBijectiveMod (I ^ n)
      (Ideal.Quotient.mkₐ A ((Ideal.span {a ^ (n + 1)}).map (algebraMap A B))) :=
    (IsBijectiveMod.of_surjective (𝔞 := Ideal.span {a ^ (n + 1)})
      (f := Ideal.Quotient.mkₐ A ((Ideal.span {a ^ (n + 1)}).map (algebraMap A B)))
      (Ideal.Quotient.mkₐ_surjective A _)
      fun _ hx ↦ Ideal.Quotient.eq_zero_iff_mem.1 hx).mono hle
  have hproj : IsBijectiveMod (I ^ n) (T.proj n) :=
    (IsBijectiveMod.of_surjective (𝔞 := Ideal.span {a ^ (n + 1)}) (T.proj_surjective n)
      fun _ hx ↦ (T.ker_proj n).le hx).mono hle
  have hstage : IsBijectiveMod (I ^ n) (T.stage n) :=
    (IsBijectiveMod.of_algEquiv (T.equiv n)).comp
      ((isBijectiveMod_toAdicCompletionAlgHom I
        (Ideal.FG.map (IsNoetherian.noetherian I) _) n).comp hproj)
  refine IsBijectiveMod.of_comp (f := T.toCarrier ha) hq hstage fun x ↦ ?_
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (T.stage n x)
  have h := T.mk_toCarrier ha n x
  simp only [levelMap, AlgHom.comp_apply] at h
  rw [← hb, Ideal.Quotient.factorₐ_apply_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
    ← Ideal.map_pow] at h
  rw [← hb]
  have h' := map_mem_map_algebraMap
    (Ideal.Quotient.mkₐ A ((Ideal.span {a ^ (n + 1)}).map (algebraMap A B))) h
  rwa [map_sub] at h'

end System

end AlgebraizationTowerData

namespace AlgebraizationTower

section System

variable {A : Type u} [CommRing A] {I : Ideal A} {a : A} {B : Type u} [CommRing B] [Algebra A B]
  (T : AlgebraizationTower I a B)

/-- The data of the tower, forgetting that its levels are étale off `V(I)`. -/
noncomputable def toData : AlgebraizationTowerData I a B where
  C := T.C
  commRing := T.commRing
  algebraQuot := T.algebraQuot
  algebra := T.algebra
  isScalarTower := T.isScalarTower
  finiteType := T.finiteType
  transition := T.transition
  transition_surjective := T.transition_surjective
  transition_ker := T.transition_ker
  equiv := T.equiv
  equiv_transition := T.equiv_transition

/-- The structure map `A ⧸ (a)ⁿ⁺¹ → Cₙ` of the tower, through `(a)ⁿ⁺¹ = (aⁿ⁺¹)`. -/
noncomputable def systemAlgebraMap (n : ℕ) : A ⧸ Ideal.span {a} ^ (n + 1) →+* T.C n :=
  T.toData.systemAlgebraMap n

/-- The structure map of the tower composed with the quotient map is the structure map of
`Cₙ` as an `A`-algebra. -/
theorem systemAlgebraMap_comp_mk (n : ℕ) :
    (T.systemAlgebraMap n).comp (Ideal.Quotient.mk (Ideal.span {a} ^ (n + 1))) =
      algebraMap A (T.C n) :=
  T.toData.systemAlgebraMap_comp_mk n

/-- The tower as an inverse system of finite type `A ⧸ (a)ⁿ⁺¹`-algebras. -/
noncomputable def system : AdicAlgebraSystem.{u, u} A (Ideal.span {a}) :=
  T.toData.system

/-- The limit `B' = lim Cₙ` of the tower, an `(a)`-adically complete `A`-algebra. -/
noncomputable abbrev limit : AdicFiniteTypeAlgebra.{u, u} A (Ideal.span {a}) :=
  T.system.limitObj (Submodule.fg_span_singleton a)

/-- The projection `B' → Cₙ`, as a map of `A`-algebras. -/
noncomputable def proj (n : ℕ) : T.limit.carrier →ₐ[A] T.C n :=
  T.toData.proj n

/-- The projection `B' → Cₙ` is surjective. -/
theorem proj_surjective (n : ℕ) : Function.Surjective (T.proj n) :=
  T.toData.proj_surjective n

/-- The kernel of `B' → Cₙ` is `aⁿ⁺¹ B'`. -/
theorem ker_proj (n : ℕ) : RingHom.ker (T.proj n : T.limit.carrier →+* T.C n) =
    (Ideal.span {a ^ (n + 1)}).map (algebraMap A T.limit.carrier) :=
  T.toData.ker_proj n

/-- The projections `B' → Cₙ` are compatible with the transitions. -/
theorem transition_proj (n : ℕ) (x : T.limit.carrier) :
    T.transition n (T.proj (n + 1) x) = T.proj n x :=
  T.toData.transition_proj n x

/-- The map `B' → Cₙ → Cₙ^∧ ≅ B ⧸ aⁿ⁺¹ B`. -/
noncomputable def stage (n : ℕ) :
    T.limit.carrier →ₐ[A] B ⧸ (Ideal.span {a ^ (n + 1)}).map (algebraMap A B) :=
  T.toData.stage n

/-- The maps `B' → B ⧸ aⁿ⁺¹ B` are compatible with the quotient maps, one step at a time. -/
theorem stage_succ (n : ℕ) (x : T.limit.carrier) :
    T.stage n x = Ideal.Quotient.factor (stage_le n.le_succ) (T.stage (n + 1) x) :=
  T.toData.stage_succ n x

/-- The maps `B' → B ⧸ aⁿ⁺¹ B` are compatible with the quotient maps. -/
theorem factor_stage {m n : ℕ} (hmn : m ≤ n) (x : T.limit.carrier) :
    Ideal.Quotient.factor (stage_le hmn) (T.stage n x) = T.stage m x :=
  T.toData.factor_stage hmn x

/-- The map `B' → B ⧸ IⁿB` through `B ⧸ aⁿ⁺¹ B`. -/
noncomputable def levelMap (ha : a ∈ I) (n : ℕ) :
    T.limit.carrier →ₐ[A] B ⧸ (I.map (algebraMap A B)) ^ n :=
  T.toData.levelMap ha n

/-- The maps `B' → B ⧸ IⁿB` form a compatible family. -/
theorem levelMap_compat (ha : a ∈ I) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp (T.levelMap ha n) =
      T.levelMap ha m :=
  T.toData.levelMap_compat ha hmn

variable [IsAdicComplete (I.map (algebraMap A B)) B]

/-- The comparison map `B' → B`, the limit of the maps `B' → B ⧸ IⁿB`. -/
noncomputable def toCarrier (ha : a ∈ I) : T.limit.carrier →ₐ[A] B :=
  T.toData.toCarrier ha

/-- Modulo `IⁿB`, the comparison map `B' → B` is the map `B' → B ⧸ IⁿB`. -/
theorem mk_toCarrier (ha : a ∈ I) (n : ℕ) (x : T.limit.carrier) :
    Ideal.Quotient.mk ((I.map (algebraMap A B)) ^ n) (T.toCarrier ha x) = T.levelMap ha n x :=
  T.toData.mk_toCarrier ha n x

/-- The comparison map `B' → B` induces isomorphisms `B' ⧸ IⁿB' ≅ B ⧸ IⁿB`. -/
theorem isBijectiveMod_toCarrier [IsNoetherianRing A] (ha : a ∈ I) (n : ℕ) :
    IsBijectiveMod (I ^ n) (T.toCarrier ha) :=
  T.toData.isBijectiveMod_toCarrier ha n

end System


section RigEtale

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {a : A}

/-- The limit of the tower is rig-étale over `(A, (a))`. -/
theorem isRigEtale_limit (ha : a ∈ I) (B : AdicFiniteTypeAlgebra.{u, u} A I) (hB : IsRigEtale B)
    (T : AlgebraizationTower I a B.carrier) : IsRigEtale T.limit := by
  obtain ⟨d, hd⟩ := exists_pow_annihilates_cotangent_of_quotient B hB a
  obtain ⟨P⟩ := nonempty_completedPolynomialPresentation (Submodule.fg_span_singleton a) T.limit
  refine ((tfae_isRigEtale T.limit P).out 4 1 :
    IsReductionCohomologyAnnihilated T.limit ↔ IsRigEtale T.limit).mp ⟨d, fun n hn x hx ↦ ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨h1, h0⟩ := hd (k + 1) (T.C k) (T.etale k) (T.equiv k) x
    (Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem _).mpr ha) d hx)
  have hker : (Ideal.span {a} ^ (k + 1)).map (algebraMap A T.limit.carrier) =
      RingHom.ker (T.proj k) := by
    rw [Ideal.span_singleton_pow]
    exact (T.ker_proj k).symm
  let e : (T.limit.carrier ⧸ (Ideal.span {a} ^ (k + 1)).map (algebraMap A T.limit.carrier))
      ≃ₐ[A] T.C k :=
    (Ideal.quotientEquivAlgOfEq A hker).trans
      (Ideal.quotientKerAlgEquivOfSurjective (T.proj_surjective k))
  refine ⟨?_, ?_⟩
  · rw [NaiveCotangent.annihilator_homology_one_eq (Algebra.Generators.self _ _)]
    exact algebraMap_mem_annihilator_h1Cotangent_of_algEquiv (Ideal.span_singleton_pow a (k + 1))
      e x h1
  · rw [NaiveCotangent.annihilator_homology_zero_eq (Algebra.Generators.self _ _),
      (Algebra.Extension.quotRangeCotangentComplexEquivKaehler _).annihilator_eq]
    exact algebraMap_mem_annihilator_kaehler_of_algEquiv (Ideal.span_singleton_pow a (k + 1))
      e x h0

end RigEtale

end AlgebraizationTower

/-- A compatible system of algebraizations of the quotients `B ⧸ aⁿ⁺¹ B`, for an element `a ∈ I`
and a rig-étale `B` over `(A, I)`, algebraizes `B`: there is a finite type `A`-algebra `D` whose
`I`-adic completion is `B`. -/
public theorem AlgebraizationTower.exists_algebraization
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {a : A} (ha : a ∈ I)
    (B : AdicFiniteTypeAlgebra.{u, u} A I) (hB : IsRigEtale B)
    (T : AlgebraizationTower I a B.carrier) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      Algebra.FiniteType A D ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A D)) D) := by
  have : IsAdicComplete (I.map (algebraMap A B.carrier)) B.carrier := B.isAdicallyComplete
  obtain ⟨D, _, _, hD, ⟨E⟩⟩ := exists_finiteType_algEquiv_of_isRigEtale_principal
    (show (Ideal.span {a}).IsPrincipal from ⟨a, rfl⟩)
    T.limit (T.isRigEtale_limit ha B hB)
  let θ : D →ₐ[A] B.carrier := (T.toCarrier ha).comp ((E.symm : _ →ₐ[A] T.limit.carrier).comp
    (toAdicCompletionAlgHom ((Ideal.span {a}).map (algebraMap A D))))
  exact ⟨D, inferInstance, inferInstance, hD,
    nonempty_algEquiv_adicCompletion I θ B.isAdicallyComplete fun n ↦
      (T.isBijectiveMod_toCarrier ha n).comp ((IsBijectiveMod.of_algEquiv E.symm).comp
        ((isBijectiveMod_toAdicCompletionAlgHom (Ideal.span {a})
          (Ideal.FG.map (Submodule.fg_span_singleton a) _) n).mono
          (Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem _).mpr ha) n)))⟩

end Rig

end
