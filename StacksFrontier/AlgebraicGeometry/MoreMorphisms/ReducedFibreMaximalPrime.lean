module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.StalkStructureMap

/-!
# Maximality of the prime describing the local ring of a normalized base change

Let `O` be a one-dimensional local domain and let `T` be integral over `O`.  A prime `q` of `T`
whose localization `T_q` is a discrete valuation ring — in particular a domain which is not a
field — is **maximal**.  Indeed `T_q` then has a prime strictly below `q T_q`, which produces a
prime `q₀ < q` of `T`; an integral extension cannot have two comparable primes with the same
contraction, so the contraction of `q` to `O` is nonzero, hence maximal, and a prime of an
integral extension lying over a maximal ideal is maximal.

This is applied to the identification of the local rings of a normalized base change: the local
ring of the normalization of `X ×_{Spec A} Spec B` at a point `y` is the localization at a prime
`p` of the integral closure of `𝒪_{X, x}` in the reduction of `R(X) ⊗_K L`
(`Scheme.exists_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ`),
and when that local ring is a discrete valuation ring — which is the case at a generic point of an
irreducible component of a fibre over a closed point, the scheme being normal — the prime `p` is
maximal.  Maximality is what the solution property of Tag 09EN(2) quantifies over
(`IsDiscreteValuationRing.IntegralClosureBaseChange.IsSolution` ranges over the *maximal* ideals of
the integral closure upstairs), so it is needed before a solution can be read on `p`.

## Main results

* `Ideal.isMaximal_of_isIntegral_of_isDomain_localizationAtPrime`: a prime of an integral
  extension of a one-dimensional local domain whose localization is a domain and not a field is
  maximal.
* `Ideal.isMaximal_of_isIntegral_of_ringEquiv_isDiscreteValuationRing`: the same with the
  localization presented by a ring isomorphism with a discrete valuation ring, which is the form
  in which the stalk identification delivers it.
* `Scheme.exists_isMaximal_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ`:
  the prime in the identification of the local ring of the normalization of a base change is
  maximal, as soon as that local ring is a discrete valuation ring.

## Implementation notes

The hypothesis on the base is `Ring.DimensionLEOne` together with `IsDomain`, which a discrete
valuation ring satisfies; locality of the base is not needed, since the contraction of `q` is
shown to be nonzero and a nonzero prime of such a ring is already maximal.

The second statement is phrased with the isomorphism pointing *out of* the discrete valuation
ring, `D ≃+* Localization.AtPrime q`, because that is the direction in which
`Scheme.exists_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ`
produces it: its `φ` goes from the stalk to the localization.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 09EN](https://stacks.math.columbia.edu/tag/09EN)
* [Stacks Project, Tag 00GS](https://stacks.math.columbia.edu/tag/00GS)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w

/-- **A prime of an integral extension with a one-dimensional localization is maximal.** Let `O`
be a domain of dimension at most one and let `T` be an `O`-algebra which is integral over `O`. If
the localization of `T` at a prime `q` is a domain and not a field, then `q` is maximal.

The localization has a prime strictly below its maximal ideal, which contracts to a prime
`q₀ < q` of `T`; by `Ideal.comap_lt_comap_of_integral_mem_sdiff` the contractions of `q₀` and `q`
to `O` are then distinct, so the contraction of `q` is nonzero, hence maximal, and
`Ideal.isMaximal_of_isIntegral_of_isMaximal_under` carries that back up to `q`. -/
theorem Ideal.isMaximal_of_isIntegral_of_isDomain_localizationAtPrime {O : Type u} [CommRing O]
    [IsDomain O] [Ring.DimensionLEOne O] {T : Type v} [CommRing T] [Algebra O T]
    [Algebra.IsIntegral O T] (q : Ideal T) [q.IsPrime] [IsDomain (Localization.AtPrime q)]
    (hfield : ¬ IsField (Localization.AtPrime q)) : q.IsMaximal := by
  have hcomapmax :
      (maximalIdeal (Localization.AtPrime q)).comap (algebraMap T (Localization.AtPrime q)) = q :=
    IsLocalization.AtPrime.comap_maximalIdeal (I := q) _
  have hmapmax : q.map (algebraMap T (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q)
  set q₀ : Ideal T :=
    (⊥ : Ideal (Localization.AtPrime q)).comap (algebraMap T (Localization.AtPrime q)) with hq₀
  have hle : q₀ ≤ q := by
    rw [← hcomapmax]
    exact Ideal.comap_mono bot_le
  have hne : q₀ ≠ q := by
    intro h
    refine hfield (isField_iff_maximalIdeal_eq.mpr ?_)
    rw [← hmapmax]
    refine le_antisymm ?_ bot_le
    rw [Ideal.map_le_iff_le_comap]
    exact h.ge
  obtain ⟨x, hxq, hxq₀⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have hcomaplt : q₀.comap (algebraMap O T) < q.comap (algebraMap O T) :=
    Ideal.comap_lt_comap_of_integral_mem_sdiff (I := q₀) (J := q) hle ⟨hxq, hxq₀⟩
      (Algebra.IsIntegral.isIntegral x)
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) q
    (Ring.DimensionLEOne.maximalOfPrime (fun h => absurd (hcomaplt.trans_le h.le) not_lt_bot)
      (Ideal.IsPrime.comap _))

/-- **A prime of an integral extension whose localization is a discrete valuation ring is
maximal.** This is `Ideal.isMaximal_of_isIntegral_of_isDomain_localizationAtPrime` with the
localization presented by a ring isomorphism with a discrete valuation ring `D`: such a `D` is a
domain and is not a field, and both properties transport along the isomorphism. -/
theorem Ideal.isMaximal_of_isIntegral_of_ringEquiv_isDiscreteValuationRing {O : Type u}
    [CommRing O] [IsDomain O] [Ring.DimensionLEOne O] {T : Type v} [CommRing T] [Algebra O T]
    [Algebra.IsIntegral O T] (q : Ideal T) [q.IsPrime] {D : Type w} [CommRing D] [IsDomain D]
    [IsDiscreteValuationRing D] (e : D ≃+* Localization.AtPrime q) : q.IsMaximal := by
  have _ : IsDomain (Localization.AtPrime q) :=
    Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  exact Ideal.isMaximal_of_isIntegral_of_isDomain_localizationAtPrime (O := O) q
    fun hF => (IsDiscreteValuationRing.not_isField D) (e.isField hF)

namespace AlgebraicGeometry.Scheme

open scoped nonZeroDivisors TensorProduct

variable (A O K F B L : Type u) [CommRing A] [CommRing O] [CommRing K] [CommRing F]
  [CommRing B] [CommRing L] [Algebra A O] [Algebra A K] [Algebra A F] [Algebra A B]
  [Algebra A L] [Algebra K F] [Algebra K L] [Algebra O F] [Algebra B L]
  [IsScalarTower A O F] [IsScalarTower A K F] [IsScalarTower A B L] [IsScalarTower A K L]
  [IsArtinianRing F] [IsDomain O] [Ring.DimensionLEOne O] [Module.Flat A B] [Module.Finite A B]
  [Module.Finite K L] [IsLocalization (nonZeroDivisors A) K]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
  [IsLocalization (nonZeroDivisors O) F]

/-- **The prime describing the local ring of a normalized base change is maximal.** In the
situation of
`exists_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ`
— `W = X ×_{Spec A} Spec B`, `y` a point of the normalization of `W` over `w`, and the local ring
of `X` below `w` identified with a one-dimensional local domain `O` with fraction field `F` — the
prime `p` of the integral closure of `O` in the reduction of `F ⊗[K] L` describing `𝒪_{Y, y}` is
*maximal*, provided `𝒪_{Y, y}` is a discrete valuation ring.

That proviso holds at the points at which the reduced fibre theorem applies this identification:
a generic point of an irreducible component of a fibre over a closed point of `Spec B`, the
normalization being normal and flat over the Dedekind base there
(`AlgebraicGeometry.isDiscreteValuationRing_stalk_of_mem_genericPoints`). Maximality is what
`IsDiscreteValuationRing.IntegralClosureBaseChange.IsSolution` quantifies over, so it is the step
that lets the solution property be read at `p`. -/
theorem exists_isMaximal_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (hW : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B))) : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        : Scheme.{u})) → (irreducibleComponents U).Finite)
    (w : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B))) : Scheme.{u}))
    (e : O ≃+* X.presheaf.stalk
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A B))) w))
    (he : ∀ a : A, e (algebraMap A O a) =
      ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A B))) w) trivial).hom a)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      : Scheme.{u}).normalizationScheme hW)
    (hy : (normalization _ hW).base y = w)
    [IsDomain (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      : Scheme.{u}).normalizationScheme hW).presheaf.stalk y)]
    [IsDiscreteValuationRing (((pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        : Scheme.{u}).normalizationScheme hW).presheaf.stalk y)] :
    letI := integralClosureTensorProductAlgebra A O K F B L
    ∃ p : PrimeSpectrum ↥(integralClosure O ((F ⊗[K] L) ⧸ _root_.nilradical (F ⊗[K] L))),
      p.asIdeal.IsMaximal ∧
      ∃ φ : ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
          : Scheme.{u}).normalizationScheme hW).presheaf.stalk y ≃+*
          Localization.AtPrime p.asIdeal,
        ∀ b : B, φ (((Scheme.ΓSpecIso (.of B)).inv ≫ (normalization _ hW ≫
              pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A B)))).appTop ≫
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
              : Scheme.{u}).normalizationScheme hW).presheaf.germ ⊤ y trivial).hom b) =
          algebraMap ↥(integralClosure O ((F ⊗[K] L) ⧸ _root_.nilradical (F ⊗[K] L)))
            (Localization.AtPrime p.asIdeal)
            (algebraMap (O ⊗[A] B)
              ↥(integralClosure O ((F ⊗[K] L) ⧸ _root_.nilradical (F ⊗[K] L)))
              ((Algebra.TensorProduct.includeRight : B →ₐ[A] O ⊗[A] B) b)) := by
  let := integralClosureTensorProductAlgebra A O K F B L
  obtain ⟨p, φ, hφ⟩ :=
    exists_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ
      A O K F B L f hW w e he y hy
  exact ⟨p, Ideal.isMaximal_of_isIntegral_of_ringEquiv_isDiscreteValuationRing (O := O)
    p.asIdeal φ, φ, hφ⟩

end AlgebraicGeometry.Scheme

end
