module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatAtPointFinite
public import StacksFrontier.RingTheory.Flat.FlatAtPrimesAbove
public import StacksFrontier.RingTheory.Flat.DevissageProjectiveStages
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.LocalizedFlatness
public import StacksFrontier.RingTheory.Flat.FlatteningEquivalence

/-!
# Transfer of flatness at the primes above a prime

`Module.IsFlatAtPrimesAbove A C Q N R` is the flatness condition of Stacks Tag 05ML for the local
situation `(C_Q, N_Q)`, read on the possibly non-local `A`-algebra `C`. This file proves the
invariances of that condition which the proof of Stacks Tag 05PG uses to pass from one stage of a
complete dévissage to the next.

## Main results

* `Module.isFlatAtPrimesAbove_congr`: invariance under an isomorphism of modules.
* `Module.isFlatAtPrimesAbove_iff_of_finite`: invariance along a finite map `C → D` and a prime
  of `D` which is the only one above its contraction; this is Stacks Tag 05P4 for non-local
  stage algebras.
* `Module.isFlatAtPrimesAbove_iff_conditionOn`: the condition is the flatness condition of
  Stacks Tag 05ML for `(C_Q, N_Q)` when `Q` lies over the closed point of a local ring `A`.
* `Module.isFlatAtPrimesAbove_ulift_iff` and `Module.IsFlatAtPrimesAbove.of_isLocalHom`:
  invariance under a universe lift and stability under a local homomorphism of local
  `A`-algebras.

## References

* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
* [Stacks Project, Tag 05P4](https://stacks.math.columbia.edu/tag/05P4)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v v' w w' x y

namespace Module

/-- `Module.IsFlatAtPrimesAbove` is invariant under an isomorphism of modules. -/
theorem isFlatAtPrimesAbove_congr {A : Type u} [CommRing A] {C : Type v} [CommRing C]
    [Algebra A C] {Q : Ideal C} {N : Type w} [AddCommGroup N] [Module C N] {N' : Type w'}
    [AddCommGroup N'] [Module C N'] (e : N ≃ₗ[C] N') (R : Type x) [CommRing R]
    [IsLocalRing R] [Algebra A R] :
    IsFlatAtPrimesAbove A C Q N R ↔ IsFlatAtPrimesAbove A C Q N' R := by
  let : Algebra R (C ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  have key : ∀ (𝔮 : Ideal (C ⊗[A] R)) [𝔮.IsPrime],
      Module.Flat R (LocalizedModule 𝔮.primeCompl ((C ⊗[A] R) ⊗[C] N)) ↔
        Module.Flat R (LocalizedModule 𝔮.primeCompl ((C ⊗[A] R) ⊗[C] N')) := fun 𝔮 _ ↦
    flat_localizedModule_congr 𝔮.primeCompl
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (C ⊗[A] R) (C ⊗[A] R)) e)
  exact forall_congr' fun 𝔮 ↦ forall_congr' fun h𝔮 ↦ imp_congr_right fun _ ↦
    imp_congr_right fun _ ↦ @key 𝔮 h𝔮

/-- **Stacks Project, Tag 05P4, for the stage algebras of a dévissage.** Let `C → D` be a finite
map of `A`-algebras, `P` a prime of `D` which is the only prime above its contraction to `C`, and
`N` a `D`-module. For every local `A`-algebra `R`, flatness of the base change of `N` at the primes
of `C ⊗[A] R` above the contraction of `P` and the closed point is flatness at the primes of
`D ⊗[A] R` above `P` and the closed point. -/
theorem isFlatAtPrimesAbove_iff_of_finite {A : Type u} [CommRing A] {C : Type v} [CommRing C]
    [Algebra A C] {D : Type v'} [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower A C D]
    [Module.Finite C D] {N : Type w} [AddCommGroup N] [Module C N] [Module D N]
    [IsScalarTower C D N] (P : Ideal D) [P.IsPrime]
    (huniq : ∀ P' : Ideal D, P'.IsPrime →
      P'.comap (algebraMap C D) = P.comap (algebraMap C D) → P' = P)
    (R : Type x) [CommRing R] [IsLocalRing R] [Algebra A R] :
    IsFlatAtPrimesAbove A C (P.comap (algebraMap C D)) N R ↔ IsFlatAtPrimesAbove A D P N R := by
  let f : C →ₐ[A] D := IsScalarTower.toAlgHom A C D
  let CR := C ⊗[A] R
  let DR := D ⊗[A] R
  let : Algebra R CR := Algebra.TensorProduct.rightAlgebra
  let : Algebra R DR := Algebra.TensorProduct.rightAlgebra
  let g : CR →ₐ[A] DR := Algebra.TensorProduct.map f (AlgHom.id A R)
  let : Algebra CR DR := g.toRingHom.toAlgebra
  have hR : g.toRingHom.comp (algebraMap R CR) = algebraMap R DR := by
    ext r
    change g ((1 : C) ⊗ₜ[A] r) = (1 : D) ⊗ₜ[A] r
    rw [Algebra.TensorProduct.map_tmul]
    simp
  have hC : g.toRingHom.comp (algebraMap C CR) = (algebraMap D DR).comp (algebraMap C D) := by
    ext c
    change g (c ⊗ₜ[A] (1 : R)) = (algebraMap C D c) ⊗ₜ[A] (1 : R)
    rw [Algebra.TensorProduct.map_tmul]
    simp [f]
  have _ : IsScalarTower R CR DR :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (congrArg (fun φ : R →+* DR ↦ φ r) hR).symm
  have hfin : (algebraMap C D).Finite := RingHom.finite_algebraMap.mpr inferInstance
  have _ : Algebra.IsIntegral CR DR :=
    ⟨(RingHom.Finite.tensorProductMap (f := f) hfin (AlgHom.Finite.id A R)).to_isIntegral⟩
  let : Module DR (DR ⊗[D] N) := TensorProduct.leftModule
  have hmod : Module.compHom N f.toRingHom = (inferInstance : Module C N) :=
    Module.ext' _ _ fun c n ↦ IsScalarTower.algebraMap_smul D c n
  let eN : @LinearEquiv C C _ _ (RingHom.id C) (RingHom.id C) _ _ N N _ _ ‹Module C N›
      (Module.compHom N f.toRingHom) := hmod ▸ LinearEquiv.refl C N
  let eD : CR ⊗[C] N ≃ₗ[CR] DR ⊗[D] N :=
    FlatAtPointSituation.tensorBaseChangeEquiv (R := R) f eN
  let : Module CR (DR ⊗[D] N) := Module.compHom (DR ⊗[D] N) g.toRingHom
  have _ : IsScalarTower CR DR (DR ⊗[D] N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module CR (CR ⊗[C] N) := TensorProduct.leftModule
  have towerM : IsScalarTower R CR (CR ⊗[C] N) := inferInstance
  have towerE : IsScalarTower R CR (DR ⊗[D] N) :=
    IsScalarTower.of_algebraMap_smul fun r n ↦ by
      change g ((algebraMap R CR) r) • n = (algebraMap R DR r) • n
      rw [IsScalarTower.algebraMap_apply R CR DR r]
      rfl
  have hlocal (p : Ideal CR) [p.IsPrime] :=
    @Module.flat_localizedModule_atPrime_congr R CR (CR ⊗[C] N) (DR ⊗[D] N) _ _ _ _
      (inferInstance : Module CR (CR ⊗[C] N)) (inferInstance : Module R (CR ⊗[C] N)) towerM
      _ (inferInstance : Module CR (DR ⊗[D] N)) (inferInstance : Module R (DR ⊗[D] N)) towerE eD p
      inferInstance
  have hintegral (p : Ideal CR) [p.IsPrime] :=
    @FlatAtPointSituation.flat_localizedModule_atPrime_iff_forall_primesOver R CR DR (DR ⊗[D] N)
      _ _ _ _ _ _ _ _ _
      (inferInstance : Module R (DR ⊗[D] N)) (inferInstance : Module CR (DR ⊗[D] N))
      (inferInstance : Module DR (DR ⊗[D] N)) towerE
      (inferInstance : IsScalarTower CR DR (DR ⊗[D] N))
      (inferInstance : IsScalarTower R DR (DR ⊗[D] N)) p inferInstance
  have hcomapC : ∀ 𝔓 : Ideal DR, (𝔓.comap g.toRingHom).comap (algebraMap C CR) =
      (𝔓.comap (algebraMap D DR)).comap (algebraMap C D) := fun 𝔓 ↦ by
    rw [Ideal.comap_comap, Ideal.comap_comap, hC]
  constructor <;> intro h
  · intro 𝔓 h𝔓 hm hP
    have _ : 𝔓.IsPrime := h𝔓
    have hp : (𝔓.comap g.toRingHom).IsPrime := Ideal.comap_isPrime _ 𝔓
    have hM := h (𝔓.comap g.toRingHom) hp (by
        rw [← hR, ← Ideal.map_map] at hm
        exact Ideal.map_le_iff_le_comap.mp hm)
      (by rw [hcomapC, hP])
    exact ((hintegral (𝔓.comap g.toRingHom)).mp ((hlocal (𝔓.comap g.toRingHom)).mp hM)) 𝔓 rfl
  · intro 𝔮 h𝔮 hm hq
    have _ : 𝔮.IsPrime := h𝔮
    refine (hlocal 𝔮).mpr ((hintegral 𝔮).mpr fun 𝔓 h𝔓 h𝔓q ↦ h 𝔓 h𝔓 ?_ ?_)
    · rw [← hR, ← Ideal.map_map]
      exact Ideal.map_le_iff_le_comap.mpr (h𝔓q ▸ hm)
    · refine huniq _ (Ideal.comap_isPrime _ 𝔓) ?_
      rw [← hcomapC]
      change (𝔓.comap (algebraMap CR DR)).comap (algebraMap C CR) = _
      rw [h𝔓q, hq]


/-- The structure map `A → C_Q` is a local homomorphism when the prime `Q` of the `A`-algebra `C`
lies over the maximal ideal of the local ring `A`. -/
theorem isLocalHom_algebraMap_localizationAtPrime {A : Type u} [CommRing A] [IsLocalRing A]
    {C : Type v} [CommRing C] [Algebra A C] (Q : Ideal C) [Q.IsPrime]
    (hQ : Q.comap (algebraMap A C) = maximalIdeal A) :
    IsLocalHom (algebraMap A (Localization.AtPrime Q)) := by
  refine ⟨fun a ha ↦ ?_⟩
  rw [IsScalarTower.algebraMap_apply A C (Localization.AtPrime Q)] at ha
  have hC : algebraMap A C a ∉ Q :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q _).mp ha
  by_contra hna
  exact hC (show a ∈ Q.comap (algebraMap A C) from hQ ▸ (mem_maximalIdeal a).mpr hna)

/-- The local situation `(C_Q, N_Q)` of Stacks Tag 05MK attached to a prime `Q` of an
`A`-algebra `C` over the closed point of `A` and a `C`-module `N`. -/
noncomputable abbrev flatAtPointSituationAtPrime (A : Type u) [CommRing A] [IsLocalRing A]
    (C : Type v) [CommRing C] [Algebra A C] (Q : Ideal C) [Q.IsPrime]
    (hQ : Q.comap (algebraMap A C) = maximalIdeal A) (N : Type w) [AddCommGroup N]
    [Module C N] : FlatAtPointSituation.{u, v, max v w} :=
  haveI := isLocalHom_algebraMap_localizationAtPrime Q hQ
  { A := A, B := Localization.AtPrime Q, M := LocalizedModule Q.primeCompl N }

/-- `Module.IsFlatAtPrimesAbove` is the flatness condition of Stacks Tag 05ML for the local
situation `(C_Q, N_Q)`. -/
theorem isFlatAtPrimesAbove_iff_conditionOn {A : Type u} [CommRing A] [IsLocalRing A]
    {C : Type v} [CommRing C] [Algebra A C] (Q : Ideal C) [Q.IsPrime]
    (hQ : Q.comap (algebraMap A C) = maximalIdeal A) (N : Type w) [AddCommGroup N]
    [Module C N] (R : Type x) [CommRing R] [IsLocalRing R] [Algebra A R] :
    IsFlatAtPrimesAbove A C Q N R ↔ (flatAtPointSituationAtPrime A C Q hQ N).ConditionOn R :=
  (FlatAtPointSituation.conditionOn_iff_isFlatAtPrimesAbove
    (S := flatAtPointSituationAtPrime A C Q hQ N) (C := C) Q
    (LocalizedModule.mkLinearMap Q.primeCompl N) R).symm

/-- `Module.IsFlatAtPrimesAbove` is invariant under a universe lift of the local algebra. -/
theorem isFlatAtPrimesAbove_ulift_iff {A : Type u} [CommRing A] [IsLocalRing A]
    {C : Type v} [CommRing C] [Algebra A C] {Q : Ideal C} [Q.IsPrime]
    (hQ : Q.comap (algebraMap A C) = maximalIdeal A) {N : Type w} [AddCommGroup N]
    [Module C N] (R : Type x) [CommRing R] [IsLocalRing R] [Algebra A R] :
    IsFlatAtPrimesAbove A C Q N (ULift.{y} R) ↔ IsFlatAtPrimesAbove A C Q N R := by
  rw [isFlatAtPrimesAbove_iff_conditionOn Q hQ, isFlatAtPrimesAbove_iff_conditionOn Q hQ]
  exact FlatAtPointSituation.conditionOn_ulift_iff _ R

/-- `Module.IsFlatAtPrimesAbove` passes along a local homomorphism of local `A`-algebras, which
may live in different universes. -/
theorem IsFlatAtPrimesAbove.of_isLocalHom {A : Type u} [CommRing A] [IsLocalRing A]
    {C : Type v} [CommRing C] [Algebra A C] {Q : Ideal C} [Q.IsPrime]
    (hQ : Q.comap (algebraMap A C) = maximalIdeal A) {N : Type w} [AddCommGroup N]
    [Module C N] {R : Type x} [CommRing R] [IsLocalRing R] [Algebra A R] (T : Type y)
    [CommRing T] [IsLocalRing T] [Algebra A T] [Algebra R T] [IsScalarTower A R T]
    [IsLocalHom (algebraMap R T)] (h : IsFlatAtPrimesAbove A C Q N R) :
    IsFlatAtPrimesAbove A C Q N T := by
  rw [isFlatAtPrimesAbove_iff_conditionOn Q hQ] at h ⊢
  exact FlatAtPointSituation.ConditionOn.of_isLocalHom
    (S := flatAtPointSituationAtPrime A C Q hQ N) R T h

end Module

end
