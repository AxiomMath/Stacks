module

public import StacksFrontier.RingTheory.Flat.HenselianFlattening

/-!
# Two readings of the local flatness condition

The flatness condition of Stacks Tag 05ML on a local `A`-algebra `A'` asks that the base change
`M' = (B ⊗_A A') ⊗_B M` be flat over `A'` at every prime of `B' = B ⊗_A A'` containing the
extensions of the maximal ideals of `A'` and of `B`. There are two ways to put the `A'`-module
structure on the localization `M'_q`: restrict the `B'`-action along `A' → B'`, or localize the
`A'`-action on `M'`. `Module.FlatAtPointSituation.ConditionOn` uses the second, through
`Module.IsFlatAtPrimesOver`; the first is the one that reads off the source. This file proves the
two readings agree, the point being that the two `A'`-module structures are literally the same
structure (`Module.compHom_algebraMap_eq`).

It also computes the condition for a *surjection* `A → A ⧸ J`, where the closed fibre of
`B ⧸ JB` has a single point: there the condition collapses to flatness of `M ⧸ JM` over `A ⧸ J`,
which is the shape in which the henselian lemmas of Stacks Tag 0AT3 consume it.

## Main definitions

* `TensorProduct.quotTensorEquivQuotSMulₐ` upgrades `TensorProduct.quotTensorEquivQuotSMul` from
  an `A`-linear to an `A ⧸ J`-linear equivalence.

## Main results

* `Module.compHom_algebraMap_eq`: restricting an `A`-module structure along `algebraMap R A`
  gives back the `R`-module structure, as an equality of `Module` structures; consequently
  `Module.flat_compHom_algebraMap_iff`.
* `Module.FlatAtPointSituation.conditionOn_iff_flatAtClosedFiberPrimes`: the condition of
  Stacks Tag 05ML as stated in the source — with the `A'`-action on `M'_q` restricted from `B'`
  — is equivalent to `Module.FlatAtPointSituation.ConditionOn`.
* `Module.FlatAtPointSituation.flattens_iff_flat_quotient`: an ideal `J ⊆ A` flattens the
  situation exactly when `M ⧸ J M` is flat over `A ⧸ J`.
* `Algebra.TensorProduct.includeLeftRingHom_surjective` and
  `Algebra.TensorProduct.includeRight_algebraMap`: the two facts about `B ⊗_A C` for a quotient
  `C` of `A` which make the previous result work.

## Implementation notes

The quotient `M ⧸ J M` is written `S.M ⧸ (J • ⊤)` for `⊤ : Submodule S.A S.M`, rather than with
the extended ideal `J B` and `⊤ : Submodule S.B S.M`: the two submodules have the same elements,
but only the first carries Mathlib's `Module (S.A ⧸ J) (S.M ⧸ J • ⊤)` instance, which is what
makes the statement say "flat over `A ⧸ J`" without a hand-built action.

No primality or locality hypothesis is needed for
`Module.FlatAtPointSituation.flattens_iff_flat_quotient`: when `B ⊗_A (A ⧸ J)` is the zero ring
there is no prime to test, and both sides hold because the base change of `M` vanishes.

## References

* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 0AT3](https://stacks.math.columbia.edu/tag/0AT3)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

universe u v w x

namespace Module

/-- Restricting a module structure along `algebraMap R A` returns the `R`-module structure it
came from: the two structures are equal, not merely isomorphic, because they have the same
scalar multiplication by `IsScalarTower.algebraMap_smul`. -/
theorem compHom_algebraMap_eq {R : Type u} {A : Type v} [CommSemiring R] [Semiring A]
    [Algebra R A] (X : Type w) [AddCommMonoid X] [Module A X] [Module R X]
    [IsScalarTower R A X] :
    Module.compHom X (algebraMap R A) = (inferInstance : Module R X) :=
  Module.ext' _ _ fun r x ↦ IsScalarTower.algebraMap_smul A r x

/-- Flatness over `R` does not depend on whether the `R`-action is taken as given or restricted
from the `A`-action along `algebraMap R A`. -/
theorem flat_compHom_algebraMap_iff {R : Type u} {A : Type v} [CommSemiring R] [Semiring A]
    [Algebra R A] (X : Type w) [AddCommMonoid X] [Module A X] [Module R X]
    [IsScalarTower R A X] :
    @Module.Flat R X _ _ (Module.compHom X (algebraMap R A)) ↔ Module.Flat R X := by
  rw [compHom_algebraMap_eq]

/-- Flatness of `X ⧸ J X` over `R ⧸ J` does not depend on which of two equal `R`-module
structures on `X` is used to form `J X`.

Unlike `Module.flat_compHom_algebraMap_iff`, the submodule `J • ⊤` itself depends on the module
structure, so the two sides are not one proposition with two instance arguments and the equality
of structures has to be transported. This is the step a consumer needs whenever a result stated
for a structure restricted along `algebraMap R A` meets a statement carrying the ambient one. -/
theorem flat_quotient_smul_top_congr {R X : Type*} [CommRing R] [AddCommGroup X]
    (i₁ i₂ : Module R X) (h : i₁ = i₂) (J : Ideal R) :
    (letI := i₁; Module.Flat (R ⧸ J) (X ⧸ (J • ⊤ : Submodule R X))) ↔
      (letI := i₂; Module.Flat (R ⧸ J) (X ⧸ (J • ⊤ : Submodule R X))) := by
  subst h
  rfl

end Module

namespace Algebra.TensorProduct

/-- If `A → C` is surjective then so is `B → B ⊗[A] C`, because `b ⊗ₜ algebraMap A C a` is the
image of `a • b`. -/
theorem includeLeftRingHom_surjective {A : Type u} {B : Type v} {C : Type w} [CommRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (h : Function.Surjective (algebraMap A C)) :
    Function.Surjective (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C) := by
  intro x
  induction x with
  | add x y hx hy =>
      obtain ⟨b, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hy
      exact ⟨b + c, map_add _ _ _⟩
  | tmul b c =>
      obtain ⟨a, rfl⟩ := h c
      refine ⟨a • b, ?_⟩
      show (a • b) ⊗ₜ[A] (1 : C) = b ⊗ₜ[A] (algebraMap A C a)
      rw [_root_.TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

/-- The two inclusions of `B ⊗[A] C` agree on the image of the base ring `A`. -/
theorem includeRight_algebraMap {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra A C] (a : A) :
    (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)) (algebraMap A C a) =
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C) (algebraMap A B a) := by
  show (1 : B) ⊗ₜ[A] (algebraMap A C a) = (algebraMap A B a) ⊗ₜ[A] (1 : C)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    _root_.TensorProduct.smul_tmul]

end Algebra.TensorProduct

/-- `TensorProduct.quotTensorEquivQuotSMul` is linear over `A ⧸ J`, not merely over `A`: both
sides are `A ⧸ J`-modules whose action is restricted from `A`, and `A → A ⧸ J` is surjective. -/
noncomputable def TensorProduct.quotTensorEquivQuotSMulₐ {A : Type u} [CommRing A] (M : Type w)
    [AddCommGroup M] [Module A M] (J : Ideal A) :
    ((A ⧸ J) ⊗[A] M) ≃ₗ[A ⧸ J] M ⧸ (J • (⊤ : Submodule A M)) :=
  AddEquiv.toLinearEquiv (TensorProduct.quotTensorEquivQuotSMul M J).toAddEquiv (by
    intro c x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hx : (Ideal.Quotient.mk J a) • x = a • x := IsScalarTower.algebraMap_smul (A ⧸ J) a x
    have hy : (Ideal.Quotient.mk J a) •
          (TensorProduct.quotTensorEquivQuotSMul M J).toAddEquiv x =
        a • (TensorProduct.quotTensorEquivQuotSMul M J).toAddEquiv x :=
      IsScalarTower.algebraMap_smul (A ⧸ J) a _
    rw [hx, hy]
    exact (TensorProduct.quotTensorEquivQuotSMul M J).map_smul a x)

namespace Module.FlatAtPointSituation

/-- **Stacks Project, Tag 05ML.** The flatness condition as the source states it — for every
prime `q` of `B' = B ⊗_A A'` containing the extensions of the maximal ideals of `A'` and of `B`,
the localization `M'_q` is flat over `A'` for the `A'`-action restricted along `A' → B'` — agrees
with `Module.FlatAtPointSituation.ConditionOn`, which localizes the `A'`-action instead. The two
`A'`-module structures on `M'_q` are equal by `Module.compHom_algebraMap_eq`.

No hypothesis that `A → A'` be local is needed; the condition itself does not use one. -/
theorem conditionOn_iff_flatAtClosedFiberPrimes (S : FlatAtPointSituation.{u, v, w}) (R : Type x)
    [CommRing R] [IsLocalRing R] [Algebra S.A R] :
    S.ConditionOn R ↔
      (let B' := S.B ⊗[S.A] R
      letI : Algebra R B' :=
        (Algebra.TensorProduct.includeRight (R := S.A) (A := S.B) (B := R)).toRingHom.toAlgebra
      let M' := B' ⊗[S.B] S.M
      ∀ (q : Ideal B') (hq : q.IsPrime),
        letI := hq
        letI : Module R (LocalizedModule q.primeCompl M') :=
          Module.compHom _ (algebraMap R B')
        Ideal.map (algebraMap R B') (IsLocalRing.maximalIdeal R) ⊔
            Ideal.map (algebraMap S.B B') (IsLocalRing.maximalIdeal S.B) ≤ q →
          Module.Flat R (LocalizedModule q.primeCompl M')) := by
  let _ : Algebra R (S.B ⊗[S.A] R) := Algebra.TensorProduct.rightAlgebra
  simp only [ConditionOn, Module.IsFlatAtPrimesOver, Ideal.add_eq_sup]
  refine forall_congr' fun q ↦ forall_congr' fun hq ↦ ?_
  let _ := hq
  exact imp_congr Iff.rfl (Module.flat_compHom_algebraMap_iff _).symm

/-- An ideal `J ⊆ A` flattens the situation exactly when `M ⧸ J M` is flat over `A ⧸ J`.

The closed fibre of `B ⊗_A (A ⧸ J) = B ⧸ J B` over the closed point of `A ⧸ J` is a single
point, so every prime of `B ⊗_A (A ⧸ J)` allowed by the condition has all of
`(B ⊗_A (A ⧸ J)) ∖ q` consisting of units and the localization at `q` does nothing; what is left
is `(B ⊗_A (A ⧸ J)) ⊗_B M ≅ (A ⧸ J) ⊗_A M ≅ M ⧸ J M`. This is the form in which the henselian
flatness criterion of Stacks Tag 0AT3 applies. -/
theorem flattens_iff_flat_quotient (S : FlatAtPointSituation.{u, v, w}) (J : Ideal S.A) :
    S.Flattens J ↔ Module.Flat (S.A ⧸ J) (S.M ⧸ (J • (⊤ : Submodule S.A S.M))) := by
  have hsurj : Function.Surjective
      (Algebra.TensorProduct.includeLeftRingHom : S.B →+* S.B ⊗[S.A] (S.A ⧸ J)) :=
    Algebra.TensorProduct.includeLeftRingHom_surjective Ideal.Quotient.mk_surjective
  let _ : Algebra (S.A ⧸ J) (S.B ⊗[S.A] (S.A ⧸ J)) := Algebra.TensorProduct.rightAlgebra
  have _ : Algebra.IsPushout S.A (S.A ⧸ J) S.B (S.B ⊗[S.A] (S.A ⧸ J)) :=
    Algebra.IsPushout.symm inferInstance
  let e : (S.B ⊗[S.A] (S.A ⧸ J)) ⊗[S.B] S.M ≃ₗ[S.A ⧸ J] S.M ⧸ (J • (⊤ : Submodule S.A S.M)) :=
    (Algebra.IsPushout.cancelBaseChange S.A (S.A ⧸ J) S.B (S.B ⊗[S.A] (S.A ⧸ J)) S.M).trans
      (TensorProduct.quotTensorEquivQuotSMulₐ S.M J)
  have hiff : Module.Flat (S.A ⧸ J) ((S.B ⊗[S.A] (S.A ⧸ J)) ⊗[S.B] S.M) ↔
      Module.Flat (S.A ⧸ J) (S.M ⧸ (J • (⊤ : Submodule S.A S.M))) :=
    Module.Flat.equiv_iff e
  have hloc : ∀ (q : Ideal (S.B ⊗[S.A] (S.A ⧸ J))) (_ : q.IsPrime),
      Ideal.map (Algebra.TensorProduct.includeLeftRingHom : S.B →+* S.B ⊗[S.A] (S.A ⧸ J))
        (maximalIdeal S.B) ≤ q →
      (Module.Flat (S.A ⧸ J)
          (LocalizedModule q.primeCompl ((S.B ⊗[S.A] (S.A ⧸ J)) ⊗[S.B] S.M)) ↔
        Module.Flat (S.A ⧸ J) ((S.B ⊗[S.A] (S.A ⧸ J)) ⊗[S.B] S.M)) := by
    intro q hq hle
    have hunit : q.primeCompl ≤ IsUnit.submonoid (S.B ⊗[S.A] (S.A ⧸ J)) := by
      intro s hs
      obtain ⟨b, rfl⟩ := hsurj s
      exact (of_not_not fun hcon ↦
        hs (hle (Ideal.mem_map_of_mem _ ((mem_maximalIdeal b).mpr hcon))) : IsUnit b).map _
    have _ : IsLocalization q.primeCompl (S.B ⊗[S.A] (S.A ⧸ J)) :=
      IsLocalization.of_le_isUnit hunit
    have _ : IsLocalizedModule q.primeCompl (LinearMap.id
        (R := S.B ⊗[S.A] (S.A ⧸ J)) (M := (S.B ⊗[S.A] (S.A ⧸ J)) ⊗[S.B] S.M)) :=
      isLocalizedModule_id q.primeCompl _ (S.B ⊗[S.A] (S.A ⧸ J))
    let e₂ : LocalizedModule q.primeCompl ((S.B ⊗[S.A] (S.A ⧸ J)) ⊗[S.B] S.M) ≃ₗ[S.A ⧸ J]
        (S.B ⊗[S.A] (S.A ⧸ J)) ⊗[S.B] S.M :=
      LinearEquiv.restrictScalars (S.A ⧸ J) (IsLocalizedModule.iso q.primeCompl LinearMap.id)
    exact Module.Flat.equiv_iff e₂
  rw [← hiff]
  refine ⟨fun h ↦ ?_, fun h q hq hcontain ↦ ?_⟩
  · rcases subsingleton_or_nontrivial (S.B ⊗[S.A] (S.A ⧸ J)) with hs | hn
    · have : Subsingleton ((S.B ⊗[S.A] (S.A ⧸ J)) ⊗[S.B] S.M) :=
        Module.subsingleton (S.B ⊗[S.A] (S.A ⧸ J)) _
      exact Module.Flat.of_free
    have hne : Ideal.map
        (Algebra.TensorProduct.includeLeftRingHom : S.B →+* S.B ⊗[S.A] (S.A ⧸ J))
        (maximalIdeal S.B) ≠ ⊤ := by
      intro htop
      obtain ⟨b, hb, hb1⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp
        ((Ideal.eq_top_iff_one _).mp htop)
      have hu : IsUnit (1 - b) := by
        by_contra hcon
        have h1 : (1 : S.B) ∈ maximalIdeal S.B := by
          simpa using (maximalIdeal S.B).add_mem ((mem_maximalIdeal (1 - b)).mpr hcon) hb
        exact (maximalIdeal.isMaximal S.B).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
      have h2 := hu.map (Algebra.TensorProduct.includeLeftRingHom :
        S.B →+* S.B ⊗[S.A] (S.A ⧸ J))
      rw [map_sub, map_one, hb1, sub_self] at h2
      exact not_isUnit_zero h2
    obtain ⟨q₀, hq₀, hq₀le⟩ := Ideal.exists_le_maximal _ hne
    refine (hloc q₀ hq₀.isPrime hq₀le).mp (h q₀ hq₀.isPrime ?_)
    rw [Ideal.add_eq_sup, sup_le_iff]
    refine ⟨le_trans (Ideal.map_le_iff_le_comap.mpr ?_) hq₀le, hq₀le⟩
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
    refine Ideal.mem_comap.mpr ?_
    rw [show (Algebra.TensorProduct.includeRight (R := S.A) (A := S.B) (B := S.A ⧸ J)).toRingHom
      (Ideal.Quotient.mk J a) = _ from Algebra.TensorProduct.includeRight_algebraMap a]
    exact Ideal.mem_map_of_mem _
      (Module.FlatAtPointSituation.map_maximalIdeal_le (algebraMap S.A S.B)
        (Ideal.mem_map_of_mem _ ha))
  · rw [Ideal.add_eq_sup, sup_le_iff] at hcontain
    exact (hloc q hq hcontain.2).mpr h

end Module.FlatAtPointSituation

end
