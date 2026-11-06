module

public import Mathlib.RingTheory.Localization.Integral
public import StacksFrontier.RingTheory.Invariant.Primes

/-!
# The inertia group at a prime does not change under localization

Let `A` be a domain with fraction field `K`, let `L / K` be an algebraic extension, let
`B = integralClosure A L` and let `q` be a prime of `B` lying over a prime `p` of `A`. Write `A_p`
for a localization of `A` at `p` and `C = integralClosure A_p L`. Then `C` is a localization of
`B`, the extension of `q` to `C` is a maximal ideal, and the inertia groups of `q` and of that
extension inside `Gal(L/K)` coincide.

The inertia group is insensitive to localization because the denominators are inverted already in
`A_p`, hence fixed by `Gal(L/K)`: for `z = b / m` in `C` with `m` in the image of `A \ p`,
`σ z - z = (σ b - b) / m` up to a unit.

## Main results

* `Ideal.inertia_comap_of_isLocalization`: the inertia group of an ideal of a localization is the
  inertia group of its contraction.
* `Ideal.exists_isMaximal_comap_eq_of_isLocalization`: a prime of `B` lying over `p` is the
  contraction of a maximal ideal of the localization of `B` at `A \ p`, when that localization is
  integral over `A_p`.
* `IsIntegralClosure.exists_isMaximal_inertia_eq_of_isLocalization`: for `q` a prime of
  `integralClosure A L` lying over `p`, there is a maximal ideal `Q` of `integralClosure A_p L`
  lying over the maximal ideal of `A_p` whose inertia group is that of `q`.

## Implementation notes

The actions of `Gal(L/K)` on the two integral closures are the ones of
`IsIntegralClosure.MulSemiringAction`, so both are the restriction of the action on `L` and the
inclusion is equivariant.

## References

* [Stacks Project, Tag 0BTD](https://stacks.math.columbia.edu/tag/0BTD)

## Tags

inertia group, localization, integral closure, maximal ideal
-/

@[expose] public noncomputable section

open IsLocalRing

open scoped Pointwise

/-! ### Inertia and localization, abstractly -/

/-- Let `C` be a localization of `B` at `M`, and let `G` act on `B` and on `C` compatibly with
`algebraMap B C`. Then the inertia group of an ideal `Q` of `C` is the inertia group of its
contraction to `B`. -/
theorem Ideal.inertia_comap_of_isLocalization
    {B C G : Type*} [CommRing B] [CommRing C] [Algebra B C]
    [Group G] [MulSemiringAction G B] [MulSemiringAction G C]
    (M : Submonoid B) [IsLocalization M C]
    (hmap : ∀ (σ : G) (b : B), algebraMap B C (σ • b) = σ • algebraMap B C b)
    (Q : Ideal C) :
    (Q.comap (algebraMap B C)).inertia G = Q.inertia G := by
  ext σ
  simp only [Ideal.mem_inertia, Ideal.mem_comap]
  refine ⟨fun h z ↦ ?_, fun h b ↦ by simpa only [map_sub, hmap] using h (algebraMap B C b)⟩
  obtain ⟨⟨b, m⟩, he⟩ := IsLocalization.surj M z
  apply (Q.mul_unit_mem_iff_mem (IsLocalization.map_units C m)).mp
  have heq : (σ • z - z) * algebraMap B C m =
      algebraMap B C (σ • b - b) - (σ • z) * algebraMap B C (σ • (m : B) - m) := by
    rw [map_sub, map_sub, hmap, hmap, ← he, smul_mul']
    ring
  exact heq ▸ Q.sub_mem (h b) (Q.mul_mem_left _ (h m))

/-- Let `A_p` be the localization of `A` at a prime `p`, and `C` the localization of the
`A`-algebra `B` at the image of `A \ p`, integral over `A_p`. Then every prime `q` of `B` lying
over `p` is the contraction of a maximal ideal of `C` lying over the maximal ideal of `A_p`. -/
theorem Ideal.exists_isMaximal_comap_eq_of_isLocalization
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime]
    (Ap C : Type*) [CommRing Ap] [CommRing C] [IsLocalRing Ap]
    [Algebra A Ap] [IsLocalization.AtPrime Ap p]
    [Algebra B C] [IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) C]
    [Algebra Ap C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A Ap C]
    [Algebra.IsIntegral Ap C]
    (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    ∃ Q : Ideal C, Q.IsMaximal ∧ Q.LiesOver (maximalIdeal Ap) ∧
      Q.comap (algebraMap B C) = q := by
  have hd : Disjoint ((Algebra.algebraMapSubmonoid B p.primeCompl : Submonoid B) : Set B)
      (q : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hb
    exact ha ((congrArg (fun I : Ideal A ↦ a ∈ I) (Ideal.over_def q p)).mpr hb)
  have hQprime : (q.map (algebraMap B C)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid B p.primeCompl) C q inferInstance hd
  have hQover : (q.map (algebraMap B C)).LiesOver (p.map (algebraMap A Ap)) :=
    IsLocalization.liesOver_of_isPrime_of_disjoint p.primeCompl
      (Algebra.algebraMapSubmonoid B p.primeCompl) p hd
  have hunder : ((q.map (algebraMap B C)).under Ap).IsMaximal := by
    rw [← Ideal.over_def (q.map (algebraMap B C)) (p.map (algebraMap A Ap))]
    infer_instance
  exact ⟨q.map (algebraMap B C),
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Ap) _ hunder,
    ⟨(IsLocalRing.eq_maximalIdeal hunder).symm⟩, IsLocalization.under_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid B p.primeCompl) C inferInstance hd⟩

/-! ### Inertia at a prime of the integral closure -/

namespace IsIntegralClosure

/-- Let `A` be a domain with fraction field `K`, let `L / K` be algebraic, and let `A_p` be a
localization of `A` at a prime `p`, also with fraction field `K`. For a prime `q` of
`integralClosure A L` lying over `p`, there is a maximal ideal `Q` of `integralClosure A_p L` lying
over the maximal ideal of `A_p` whose inertia group in `Gal(L/K)` is that of `q`. -/
theorem exists_isMaximal_inertia_eq_of_isLocalization
    (A Ap K L : Type*) [CommRing A] [CommRing Ap] [IsDomain A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra.IsAlgebraic K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra A Ap] [Algebra Ap K] [IsFractionRing Ap K] [IsScalarTower A Ap K]
    [Algebra Ap L] [IsScalarTower Ap K L] [IsScalarTower A Ap L]
    [IsLocalRing Ap] (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime Ap p]
    (q : Ideal (integralClosure A L)) [q.IsPrime] [q.LiesOver p] :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI := IsIntegralClosure.MulSemiringAction Ap K L (integralClosure Ap L)
    ∃ Q : Ideal (integralClosure Ap L), Q.IsMaximal ∧ Q.LiesOver (maximalIdeal Ap) ∧
      Q.inertia Gal(L/K) = q.inertia Gal(L/K) := by
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let := IsIntegralClosure.MulSemiringAction Ap K L (integralClosure Ap L)
  let f : integralClosure A L →ₐ[A] integralClosure Ap L :=
    { toFun := fun b ↦ ⟨b, b.property.tower_top⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  let : Algebra (integralClosure A L) (integralClosure Ap L) := f.toRingHom.toAlgebra
  have : IsScalarTower (integralClosure A L) (integralClosure Ap L) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A (integralClosure A L) (integralClosure Ap L) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (f.commutes a).symm
  have : IsLocalization (Algebra.algebraMapSubmonoid L p.primeCompl) L := by
    apply IsLocalization.self
    rintro _ ⟨a, ha, rfl⟩
    refine isUnit_iff_ne_zero.mpr fun h ↦ ha ?_
    have hinj : Function.Injective (algebraMap A L) := by
      rw [IsScalarTower.algebraMap_eq A K L]
      exact (RingHom.injective (algebraMap K L)).comp (IsFractionRing.injective A K)
    exact (hinj (h.trans (map_zero _).symm)) ▸ p.zero_mem
  have : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) p.primeCompl)
      (integralClosure Ap L) := IsLocalization.integralClosure p.primeCompl
  obtain ⟨Q, hQ, hQover, hQq⟩ :=
    Ideal.exists_isMaximal_comap_eq_of_isLocalization p Ap (integralClosure Ap L) q
  refine ⟨Q, hQ, hQover, ?_⟩
  rw [← hQq, Ideal.inertia_comap_of_isLocalization
    (Algebra.algebraMapSubmonoid (integralClosure A L) p.primeCompl) fun σ b ↦ ?_]
  refine Subtype.ext ?_
  change (algebraMap (integralClosure A L) L) (galRestrict A K L (integralClosure A L) σ b) =
    (algebraMap (integralClosure Ap L) L)
      (galRestrict Ap K L (integralClosure Ap L) σ (f b))
  rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
  rfl

end IsIntegralClosure

end
