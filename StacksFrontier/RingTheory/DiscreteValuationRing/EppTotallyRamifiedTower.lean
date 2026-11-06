module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppRamificationTransport
public import StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel

/-!
# Total ramification composes along a tower

Let `A ⊆ A'` be discrete valuation rings with fraction fields `K ⊆ K' ⊆ K''`, with `A'` the
integral closure of `A` in `K'`. If `K' / K` is totally ramified with respect to `A` and
`K'' / K'` is totally ramified with respect to `A'`, then `K'' / K` is totally ramified with
respect to `A`.

The definition `IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo` (a unique maximal ideal
above `𝔪 A`, with trivial residue field extension) does not compose directly: rebuilding it at the
top of a tower means redoing the uniqueness and the inertia bookkeeping, including the
identification `integralClosure A K'' = integralClosure A' K''`. What composes is the
**numerical** form. `Ideal.ramificationIdx'` and `Module.finrank` are both multiplicative in a
tower, so the equality `ramificationIdx' = finrank` transports through an intermediate field by
arithmetic. The two directions of that equality are
`IsDiscreteValuationRing.ramificationIdx_eq_finrank_of_totallyRamified` and
`Stacks.DiscreteValuationRing.EppLevelInduction.isTotallyRamified_of_dvd_ramificationIdx`.

## Main results

All in the namespace `Stacks.DiscreteValuationRing.EppLevelInduction`.

* `isTotallyRamified_of_ramificationIdx_eq_finrank_tower`: from the numerical fact at each of
  the two steps, total ramification at the top.
* `ramificationIdx'_eq_finrank_of_totallyRamified_transport`: the numerical fact read off total
  ramification, at an arbitrary integral closure of `A'` in `K''`. A tower presents the ring
  above as such an integral closure (for the lower step `A'` itself, for the upper
  `integralClosure A K''`), equal to `integralClosure A' K''` only up to the canonical
  isomorphism.
* `isTotallyRamified_trans`: total ramification is transitive along a tower.

Nothing here assumes anything about the residue characteristic, completeness, or henselianness.
-/

@[expose] public noncomputable section

namespace Stacks.DiscreteValuationRing.EppLevelInduction

open IsDiscreteValuationRing

/-- If `R → T` factors through `S` and is injective, then `R → S` is injective. -/
private theorem injective_of_injective_comp_tower (R S T : Type*) [CommSemiring R]
    [CommSemiring S] [CommSemiring T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] (h : Function.Injective (algebraMap R T)) :
    Function.Injective (algebraMap R S) := by
  rw [IsScalarTower.algebraMap_eq R S T] at h
  exact Function.Injective.of_comp (f := algebraMap S T) h

/-- **Total ramification composes along a tower, in numerical form.**

Given a tower `A ⊆ A'` of discrete valuation rings with fraction fields `K ⊆ K' ⊆ K''`, in which
`A'` is the integral closure of `A` in `K'`, suppose

* every maximal ideal of `A'` above `𝔪 A` has ramification index `Module.finrank K K'`, and
* every maximal ideal of `integralClosure A K''` has ramification index `Module.finrank K' K''`
  over the ideal of `A'` it lies over.

Then `K'' / K` is totally ramified with respect to `A`.

The ramification index at the top is the product of the index at the intermediate ideal and the
index above it, and the degree `[K'' : K]` is the product `[K'' : K'] [K' : K]`; so every maximal
ideal of `integralClosure A K''` has ramification index `[K'' : K]`, which is total ramification.

`FiniteDimensional K K''` and `Algebra.IsSeparable K K''` are derived in the statement from the
corresponding facts at the two steps, rather than assumed. -/
theorem isTotallyRamified_of_ramificationIdx_eq_finrank_tower
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (A' : Type*) [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
    (K' : Type*) [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    (K'' : Type*) [Field K'']
    [Algebra K K'] [Algebra A K'] [IsScalarTower A K K']
    [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
    [Algebra A K''] [IsScalarTower A K K'']
    [Algebra A A'] [IsScalarTower A A' K']
    [Algebra A' K''] [IsScalarTower A' K' K'']
    [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    [FiniteDimensional K' K''] [Algebra.IsSeparable K' K'']
    [Algebra A' (integralClosure A K'')]
    [IsScalarTower A A' (integralClosure A K'')]
    [IsScalarTower A' (integralClosure A K'') K'']
    (hlower : ∀ m' : Ideal A', m'.IsMaximal → m'.LiesOver (IsLocalRing.maximalIdeal A) →
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m' = Module.finrank K K')
    (hupper : ∀ m : Ideal (integralClosure A K''), m.IsMaximal →
      ∀ m' : Ideal A', m.LiesOver m' →
        Ideal.ramificationIdx' m' m = Module.finrank K' K'') :
    letI : FiniteDimensional K K'' := FiniteDimensional.trans K K' K''
    letI : Algebra.IsSeparable K K'' := Algebra.IsSeparable.trans K K' K''
    IsTotallyRamifiedWithRespectTo A K K'' := by
  have : FiniteDimensional K K'' := FiniteDimensional.trans K K' K''
  have : Algebra.IsSeparable K K'' := Algebra.IsSeparable.trans K K' K''
  refine Stacks.DiscreteValuationRing.EppLevelInduction.isTotallyRamified_of_dvd_ramificationIdx A K
    K'' (Module.finrank K K'') Module.finrank_pos le_rfl ?_
  intro m hm hlies
  classical
  set m' : Ideal A' := m.under A' with hm'def
  have hmP : m.IsPrime := hm.isPrime
  have hDed : IsDedekindDomain (integralClosure A K'') :=
    integralClosure.isDedekindDomain A K K''
  have hAK' : Function.Injective (algebraMap A K') := by
    rw [IsScalarTower.algebraMap_eq A K K']
    exact (algebraMap K K').injective.comp (IsFractionRing.injective A K)
  have hinjAA' : Function.Injective (algebraMap A A') :=
    injective_of_injective_comp_tower A A' K' hAK'
  have hA'K'' : Function.Injective (algebraMap A' K'') := by
    rw [IsScalarTower.algebraMap_eq A' K' K'']
    exact (algebraMap K' K'').injective.comp (IsFractionRing.injective A' K')
  have hinjA'B : Function.Injective (algebraMap A' (integralClosure A K'')) :=
    injective_of_injective_comp_tower A' (integralClosure A K'') K'' hA'K''
  have htf1 : Module.IsTorsionFree A A' :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjAA'
  have htf2 : Module.IsTorsionFree A' (integralClosure A K'') :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjA'B
  have hintA' : Algebra.IsIntegral A' (integralClosure A K'') :=
    Algebra.IsIntegral.tower_top (R := A) (S := A') (T := integralClosure A K'')
  have hlo1 : m.LiesOver m' := ⟨rfl⟩
  have hlo2 : m'.LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨by simpa [hm'def, Ideal.under, Ideal.comap_comap,
      ← IsScalarTower.algebraMap_eq A A' (integralClosure A K'')] using hlies.over⟩
  have hm'max : m'.IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A') (hI := hm) m
  rw [Ideal.ramificationIdx'_algebra_tower'
      (R := A) (S := A') (T := integralClosure A K'')
      (IsLocalRing.maximalIdeal A) m' m,
    hlower m' hm'max hlo2, hupper m hm m' hlo1,
    Module.finrank_mul_finrank K K' K'']

/-- **In a totally ramified extension, the ramification index at a maximal ideal of any integral
closure is the degree.**

If `K'' / K'` is totally ramified with respect to `A'` and `B` is an integral closure of `A'` in
`K''`, then every maximal ideal of `B` has ramification index `[K'' : K']` over the ideal of `A'`
it lies over. For `B = integralClosure A' K''` this is
`IsDiscreteValuationRing.ramificationIdx_eq_finrank_of_totallyRamified`; in general `B` is
isomorphic to `integralClosure A' K''` as an `A'`-algebra, by `IsIntegralClosure.equiv`, and
ramification indices are invariant under that isomorphism. -/
theorem ramificationIdx'_eq_finrank_of_totallyRamified_transport
    (A' : Type*) [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
    (K' : Type*) [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    (K'' : Type*) [Field K''] [Algebra K' K''] [Algebra A' K'']
    [IsScalarTower A' K' K''] [FiniteDimensional K' K''] [Algebra.IsSeparable K' K'']
    (B : Type*) [CommRing B] [Algebra A' B] [Algebra B K'']
    [IsScalarTower A' B K''] [IsIntegralClosure B A' K'']
    (htot : IsTotallyRamifiedWithRespectTo A' K' K'')
    (m : Ideal B) (hm : m.IsMaximal) (m' : Ideal A') (hlo : m.LiesOver m') :
    Ideal.ramificationIdx' m' m = Module.finrank K' K'' := by
  classical
  set C := integralClosure A' K''
  let e : C ≃ₐ[A'] B := IsIntegralClosure.equiv A' C K'' B
  have hsq : ∀ x : A', algebraMap A' B (RingEquiv.refl A' x) = e.toRingEquiv (algebraMap A' C x) :=
    fun x => (e.commutes x).symm
  set m₀ : Ideal C := m.comap (e.toRingEquiv : C →+* B)
  have hsurj : Function.Surjective (e.toRingEquiv : C →+* B) := e.toRingEquiv.surjective
  have hmap : m₀.map (e.toRingEquiv : C →+* B) = m :=
    Ideal.map_comap_of_surjective _ hsurj m
  have hintB : Algebra.IsIntegral A' B := IsIntegralClosure.isIntegral_algebra A' K''
  have hm'eq : m' = IsLocalRing.maximalIdeal A' :=
    hlo.over.trans (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A') (hI := hm) m))
  have htr := Stacks.DiscreteValuationRing.EppLevelInduction.ramificationIdx'_eq_of_ringEquiv_square
    (RingEquiv.refl A') e.toRingEquiv hsq (IsLocalRing.maximalIdeal A') m₀
  simp only [Ideal.map_id, RingEquiv.coe_ringHom_refl, hmap] at htr
  have hm₀max : m₀.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
  have hm₀lo : m₀.LiesOver (IsLocalRing.maximalIdeal A') :=
    ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A') (hI := hm₀max) m₀)).symm⟩
  rw [hm'eq, ← htr]
  exact IsDiscreteValuationRing.ramificationIdx_eq_finrank_of_totallyRamified
    A' K' K'' htot m₀ hm₀max hm₀lo

/-- **Total ramification is transitive along a tower of discrete valuation rings.**

If `K' / K` is totally ramified with respect to `A`, and `K'' / K'` is totally ramified with
respect to `A'` — the integral closure of `A` in `K'` — then `K'' / K` is totally ramified with
respect to `A`.

Nothing here assumes anything about the residue characteristic, completeness, or henselianness. -/
theorem isTotallyRamified_trans
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (A' : Type*) [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
    (K' : Type*) [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    (K'' : Type*) [Field K'']
    [Algebra K K'] [Algebra A K'] [IsScalarTower A K K']
    [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
    [Algebra A K''] [IsScalarTower A K K'']
    [Algebra A A'] [IsScalarTower A A' K']
    [Algebra A' K''] [IsScalarTower A' K' K''] [IsScalarTower A A' K'']
    [IsIntegralClosure A' A K']
    [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    [FiniteDimensional K' K''] [Algebra.IsSeparable K' K'']
    [Algebra A' (integralClosure A K'')]
    [IsScalarTower A A' (integralClosure A K'')]
    [IsScalarTower A' (integralClosure A K'') K'']
    (h1 : IsTotallyRamifiedWithRespectTo A K K')
    (h2 : IsTotallyRamifiedWithRespectTo A' K' K'') :
    letI : FiniteDimensional K K'' := FiniteDimensional.trans K K' K''
    letI : Algebra.IsSeparable K K'' := Algebra.IsSeparable.trans K K' K''
    IsTotallyRamifiedWithRespectTo A K K'' := by
  have hintAA' : Algebra.IsIntegral A A' := IsIntegralClosure.isIntegral_algebra A K'
  have : IsIntegralClosure (integralClosure A K'') A' K'' :=
    IsIntegralClosure.tower_top (R := A) (A := A') (B := K'') (C := integralClosure A K'')
  exact isTotallyRamified_of_ramificationIdx_eq_finrank_tower A K A' K' K''
    (fun m' hm' hlo =>
      ramificationIdx'_eq_finrank_of_totallyRamified_transport A K K' A' h1 m' hm'
        (IsLocalRing.maximalIdeal A) hlo)
    (fun m hm m' hlo =>
      ramificationIdx'_eq_finrank_of_totallyRamified_transport A' K' K''
        (integralClosure A K'') h2 m hm m' hlo)

end Stacks.DiscreteValuationRing.EppLevelInduction

end
