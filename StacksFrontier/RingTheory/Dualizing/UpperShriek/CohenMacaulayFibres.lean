module

public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayLocus
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBound
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.GorensteinFibres
public import StacksFrontier.RingTheory.RelativeDimension.FlatLocalExtension
public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension
public import StacksFrontier.RingTheory.CohenMacaulay.Witnesses

/-!
# Cohen–Macaulay fibres from the relative dualizing complex

Let `R → A` be a flat homomorphism of finite type of Noetherian rings, `q ⊂ A` a prime over
`P ⊂ R` and `Q` the matching prime of the fibre `κ(P) ⊗_R A`. If `ω^•_{A/R}` has no cohomology
above a degree `n` with `n ≤ -dim_q`, `dim_q` the dimension at `q` of the fibre through `q`, then
the fibre is Cohen–Macaulay at `Q`. This is the ring-level core of the converse of
[Stacks, Tag 0C0Z].

## Main results

* `Dualizing.isCohenMacaulayLocalRing_fiber_of_isZero_homology_gt`.

## Implementation notes

The derived base change `D` of `ω^•_{A/R}` to the fibre is a dualizing complex for the fibre
([Stacks, Tag 0BZW] (2)(b)). It has no cohomology above `n`, derived extension of scalars being
right t-exact, and its cohomology modules are those of `ω^•_{κ(P) ⊗ A/κ(P)}` ([Stacks, Tag 0BZV]),
whose localizations at `Q` vanish below `-dim_q` by [Stacks, Tag 0E9P]. So the localization of
`D` at `Q` is concentrated in degree `n`, and [Stacks, Tag 0AWS] gives Cohen–Macaulayness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **The fibre of `R → A` is Cohen–Macaulay at `Q` when `ω^•_{A/R}` stops at a degree
`n ≤ -dim_q`.** -/
theorem isCohenMacaulayLocalRing_fiber_of_isZero_homology_gt
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] [Module.Flat R A] (p : PolynomialPresentation (algebraMap R A)) (n : ℤ)
    (hz : ∀ i : ℤ, n < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))))
    (q : Ideal A) [q.IsPrime] (Q : Ideal ((q.under R).Fiber A)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight :
      A →ₐ[R] (q.under R).Fiber A).toRingHom = q)
    (d : ℕ) (hd : Algebra.relativeDimensionAt R q = (d : WithBot ℕ∞)) (hnd : n ≤ -(d : ℤ)) :
    letI : IsNoetherianRing ((q.under R).Fiber A) :=
      isNoetherianRing_baseChange (q.under R).ResidueField p
    IsCohenMacaulayLocalRing (Localization.AtPrime Q) := by
  let : IsNoetherianRing ((q.under R).Fiber A) :=
    isNoetherianRing_baseChange (q.under R).ResidueField p
  have hflat : (algebraMap R A).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let P := q.under R
  let κ := P.ResidueField
  let F := P.Fiber A
  let ι : A →+* F := (Algebra.TensorProduct.includeRight : A →ₐ[R] F).toRingHom
  let ω := p.upperShriekFunctor.{u, 0}.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  let D := (totalDerivedExtensionScalars.{u, u, u} ι).functor.obj ω
  have hD : IsDualizingComplex D :=
    isDualizingComplex_derivedExtensionScalars_upperShriekFunctor_unit_of_field κ p hflat
  rw [Stacks.Duality.isCohenMacaulayLocalRing_localization_iff D hD Q]
  refine ⟨n, fun i hi => ?_⟩
  rcases lt_or_gt_of_ne hi with h | h
  · -- below `n`: the bound of Tag 0E9P on the fibre
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    obtain ⟨e⟩ := nonempty_homology_iso_relativeDualizing_baseChange_of_flatAlgebra
      (R' := κ) p hflat i
    let eL := IsLocalizedModule.mapEquiv Q.primeCompl
      (LocalizedModule.mkLinearMap Q.primeCompl _) (LocalizedModule.mkLinearMap Q.primeCompl _)
      (Localization Q.primeCompl) e.toLinearEquiv
    have hdF : Algebra.relativeDimensionAt κ Q = (d : WithBot ℕ∞) := by
      rw [IsLocalRing.relativeDimensionAt_eq_localKrullDim_of_field,
        ← Algebra.relativeDimensionAt_eq_localKrullDim q P rfl Q hQ, hd]
    have := upperShriekFunctor_neg_relativeDimensionAt_le_of_nontrivial_localizedHomology
      (R := κ) (A := F) (p.baseChange (R' := κ)) ⟨Q, inferInstance⟩ d hdF i
      (by exact eL.toEquiv.symm.nontrivial)
    omega
  · -- above `n`: right t-exactness of derived extension of scalars
    have : ω.IsLE n := (DerivedCategory.isLE_iff ω n).2 hz
    have : D.IsLE n := (totalDerivedExtensionScalars.{u, u, u} ι).maps_t_le ω n
    have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} F) i).obj D) :=
      ModuleCat.isZero_iff_subsingleton.mp (DerivedCategory.isZero_of_isLE D n i h)
    infer_instance


section Generization

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- A prime of the fibre `κ(P) ⊗_R A` contracts to a prime of `A` lying over `P`. -/
theorem under_comap_includeRight (P : Ideal R) [P.IsPrime] (Q : Ideal (P.Fiber A)) [Q.IsPrime] :
    (Q.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] P.Fiber A).toRingHom).under R = P :=
  (((PrimeSpectrum.primesOverOrderIsoFiber R A P).symm ⟨Q, inferInstance⟩).2.2.over).symm

/-- Two primes of the fibre `κ(P) ⊗_R A` with the same contraction to `A` are equal. -/
theorem eq_of_comap_includeRight_eq (P : Ideal R) [P.IsPrime] (Q Q' : Ideal (P.Fiber A))
    [Q.IsPrime] [Q'.IsPrime]
    (h : Q.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] P.Fiber A).toRingHom =
      Q'.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] P.Fiber A).toRingHom) :
    Q = Q' :=
  congrArg PrimeSpectrum.asIdeal <| (PrimeSpectrum.primesOverOrderIsoFiber R A P).symm.injective
    (a₁ := ⟨Q, inferInstance⟩) (a₂ := ⟨Q', inferInstance⟩) (Subtype.ext h)

/-- **The fibre is Cohen–Macaulay at a prime minimal in its fibre.** If `z ⊂ A` is minimal among
the primes of `A` over `z ∩ R`, the local ring of the fibre at the matching prime has dimension
zero, so it is Cohen–Macaulay. -/
theorem isCohenMacaulayLocalRing_fiber_of_minimal (z : Ideal A) [z.IsPrime]
    (hmin : ∀ z' : Ideal A, z'.IsPrime → z'.under R = z.under R → z' ≤ z → z' = z)
    (Q : Ideal ((z.under R).Fiber A)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight :
      A →ₐ[R] (z.under R).Fiber A).toRingHom = z)
    [IsNoetherianRing (Localization.AtPrime Q)] :
    IsCohenMacaulayLocalRing (Localization.AtPrime Q) := by
  let ι := (Algebra.TensorProduct.includeRight : A →ₐ[R] (z.under R).Fiber A).toRingHom
  have hQmin : Q ∈ minimalPrimes ((z.under R).Fiber A) := by
    refine ⟨⟨inferInstance, bot_le⟩, fun Q'' hQ'' hle => ?_⟩
    have := hQ''.1
    have h1 : Q''.comap ι = z := hmin _ inferInstance (under_comap_includeRight (z.under R) Q'')
      (hQ.le.trans' (Ideal.comap_mono hle))
    exact (eq_of_comap_includeRight_eq (z.under R) Q Q'' (hQ.trans h1.symm)).le
  have := Ring.KrullDimLE.of_isLocalization Q hQmin (Localization.AtPrime Q)
  exact isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero _
    (ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance)

/-- **A generization in the fibre carrying the local fibre dimension.** For `R → A` of finite
type and a prime `q ⊂ A` at which the fibre has dimension `d`, there is a prime `q₀ ⊆ q` over the
same prime of `R`, minimal among the primes of `A` over it, at which the fibre has dimension at
least `d`: a minimal prime of the fibre below `q` whose closure has dimension `d`. -/
theorem exists_minimal_le_le_relativeDimensionAt [Algebra.FiniteType R A] (q : Ideal A)
    [q.IsPrime] (d : ℕ) (hd : Algebra.relativeDimensionAt R q = (d : WithBot ℕ∞)) :
    ∃ q₀ : Ideal A, ∃ _ : q₀.IsPrime, q₀ ≤ q ∧ q₀.under R = q.under R ∧
      (∀ z' : Ideal A, z'.IsPrime → z'.under R = q₀.under R → z' ≤ q₀ → z' = q₀) ∧
      (d : WithBot ℕ∞) ≤ Algebra.relativeDimensionAt R q₀ := by
  let P := q.under R
  let ι := (Algebra.TensorProduct.includeRight : A →ₐ[R] P.Fiber A).toRingHom
  obtain ⟨Q, hQp, hQ⟩ := Ideal.Fiber.exists_comap_includeRight_eq q P rfl
  have hloc := Stacks.Spectrum.LocalDimension.localKrullDim_eq_iSup_coheight P.ResidueField
    (⟨Q, hQp⟩ : PrimeSpectrum (P.Fiber A))
  rw [← Algebra.relativeDimensionAt_eq_localKrullDim q P rfl Q hQ, hd] at hloc
  -- a minimal prime below `Q` of coheight at least `d`
  obtain ⟨Q₀, ⟨hQ₀min, hQ₀le⟩, hQ₀d⟩ : ∃ Q₀ : PrimeSpectrum (P.Fiber A),
      (IsMin Q₀ ∧ Q₀ ≤ ⟨Q, hQp⟩) ∧ (d : WithBot ℕ∞) ≤ (Order.coheight Q₀ : WithBot ℕ∞) := by
    by_contra hcon
    push Not at hcon
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · obtain ⟨m, hm, hmQ⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := Q) bot_le
      have := hcon ⟨m, hm.1.1⟩ ⟨PrimeSpectrum.isMin_iff.mpr hm, hmQ⟩
      subst h0
      exact absurd this (not_lt.mpr (by exact_mod_cast bot_le))
    · have hle : (⨆ Q₀ ∈ {Q₀ : PrimeSpectrum (P.Fiber A) | IsMin Q₀ ∧ Q₀ ≤ ⟨Q, hQp⟩},
          (Order.coheight Q₀ : WithBot ℕ∞)) ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
        refine iSup₂_le fun Q₀ hQ₀ => ?_
        have h := hcon Q₀ hQ₀
        have h' : Order.coheight Q₀ < (d : ℕ∞) := by exact_mod_cast h
        have h'' : Order.coheight Q₀ ≤ ((d - 1 : ℕ) : ℕ∞) := by
          rw [← ENat.lt_add_one_iff (by simp)]
          exact_mod_cast (show (d : ℕ∞) = ((d - 1 : ℕ) : ℕ∞) + 1 by
            norm_cast; omega) ▸ h'
        exact WithBot.coe_le_coe.mpr h''
      rw [← hloc] at hle
      have : d ≤ d - 1 := by exact_mod_cast hle
      omega
  let q₀ := Q₀.asIdeal.comap ι
  have hP0 : q₀.under R = P := under_comap_includeRight P Q₀.asIdeal
  have hq₀q : q₀ ≤ q := by
    rw [← hQ]
    exact Ideal.comap_mono hQ₀le
  refine ⟨q₀, inferInstance, hq₀q, hP0, fun z' hz' hz'P hz'le => ?_, ?_⟩
  · -- `q₀` is minimal over `P`
    obtain ⟨Q', hQ'p, hQ'⟩ := Ideal.Fiber.exists_comap_includeRight_eq z' P (hz'P.trans hP0)
    have hle : (⟨Q', hQ'p⟩ : PrimeSpectrum (P.Fiber A)) ≤ Q₀ :=
      (PrimeSpectrum.primesOverOrderIsoFiber R A P).symm.le_iff_le.mp <| by
        change Q'.comap ι ≤ Q₀.asIdeal.comap ι
        exact hQ'.le.trans hz'le
    rw [← hQ']
    exact congrArg (fun T : PrimeSpectrum (P.Fiber A) => T.asIdeal.comap ι) (hQ₀min.eq_of_le hle)
  · -- the fibre dimension at `q₀`
    rw [Algebra.relativeDimensionAt_eq_localKrullDim q₀ P hP0 Q₀.asIdeal rfl,
      Stacks.Spectrum.LocalDimension.localKrullDim_eq_iSup_coheight P.ResidueField Q₀]
    exact hQ₀d.trans (le_iSup₂_of_le Q₀ ⟨hQ₀min, le_rfl⟩ le_rfl)

end Generization

end Dualizing
