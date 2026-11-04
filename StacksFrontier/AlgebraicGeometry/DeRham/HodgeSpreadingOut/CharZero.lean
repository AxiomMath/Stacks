module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.ArithmeticPoints
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.DeRhamFibreBetti
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.FiniteTypeModel
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.FormsVanishing
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.HodgeFibreBetti
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.WittLift
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiSemicontinuity

/-!
# The Hodge numbers add up to the de Rham numbers in characteristic zero, from characteristic `p`

Let `k` be a field of characteristic zero and let `f : X ⟶ Spec k` be proper and smooth. Then for
every `n`

`∑_{p + q = n} h^{p,q}(X/k) = h^n_{dR}(X/k)`,

where `h^{p,q}(X/k) = dim_k H^q(X, Ω^p_{X/k})` and `h^n_{dR}(X/k) = dim_k H^n_{dR}(X/k)`, granted
the same equality for every proper smooth scheme `X₀` over a finite field `F` whose forms vanish in
degrees at least the characteristic of `F` and which lifts to a proper smooth scheme over the
Witt vectors `W₂(F)` of length two. That characteristic `p` statement is the theorem of Deligne
and Illusie; it is a hypothesis here, `hDI`.

This is the spreading out argument of Deligne–Illusie, Corollaire 2.4, the step that deduces the
degeneration of the Hodge-to-de Rham spectral sequence in characteristic zero from the
characteristic `p` statement.

## Main results

* `AlgebraicGeometry.HodgeSpreadingOut.derivedFiberBetti_eq_of_specializes`: an upper
  semicontinuous function is constant on the open set where it is at most its value at a point
  specializing to every point.
* `AlgebraicGeometry.HodgeSpreadingOut.sum_hodgeNumbers_eq_deRhamBetti_of_charZero`: the theorem
  above.

## Implementation notes

The proof follows the source.

1. `X` is the base change of a proper smooth `Y ⟶ Spec R` along an injection `R ⟶ k`, with `R` of
   finite type over `ℤ` (`exists_isPullback_finiteType_properSmooth`); `R` is a domain of
   characteristic zero and the point of `Spec k` maps to the generic point `η` of `Spec R`.
2. The derived-fibre Betti numbers of the perfect objects `Rh_*Ω^p_{Y/R}` and `Rh_*Ω^•_{Y/R}` of
   [Stacks, Tag 0FM0] at a point `x` with a field-valued point `Spec K ⟶ Spec R` over it are the
   Hodge and de Rham numbers of the base change of `Y` to `K` (`derivedFiberBetti_hodgeDirectImage`
   and `derivedFiberBetti_deRhamDirectImage`). They are upper semicontinuous
   ([Stacks, Tag 0BDI]), so each takes its generic value on an open neighbourhood of `η`. This
   replaces generic freeness and cohomology and base change: no module is shown to be free.
3. `Spec R` is smooth over `ℤ` near `η` (`mem_smoothLocus_int_bot`). The intersection of the
   smooth locus with the finitely many neighbourhoods of step 2 contains a maximal ideal `s` with
   finite residue field `κ(s)` of characteristic `p` larger than a bound `N` for the degrees of the
   nonzero forms on `Y` (`exists_isMaximal_finite_lt_ringChar`,
   `exists_isZero_relativeDifferentialForms`).
4. `R ⟶ κ(s)` lifts to `W₂(κ(s))` (`exists_wittTwo_lift`), and the base change of `Y` along the
   lift is a proper smooth lift over `W₂(κ(s))` of the fibre `Y_s`, whose forms vanish in degrees
   at least `p`. The hypothesis `hDI` applies to `Y_s`, and step 2 transports its conclusion to
   `X`.

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, pinned at
priority `10000` for the reason given in
`StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.DeRhamFibreBetti`.

## References

* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* P. Deligne and L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987), Corollaire 2.4.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.HodgeSpreadingOut

/-- **An upper semicontinuous function takes its value at a point `η` everywhere it is at most
that value, when `η` specializes to every such point.** For `η ⤳ x`, every neighbourhood of `x`
contains `η`, so upper semicontinuity at `x` gives `β η ≤ β x`. -/
theorem eq_of_le_of_specializes {Z : Type*} [TopologicalSpace Z] {β : Z → ℕ}
    (hβ : UpperSemicontinuous β) {η x : Z} (hηx : η ⤳ x) (hx : β x ≤ β η) : β x = β η := by
  refine le_antisymm hx ?_
  have h : ∀ᶠ y in 𝓝 x, β y < β x + 1 := hβ x (β x + 1) (Nat.lt_succ_self _)
  exact Nat.lt_succ_iff.mp (show ∀ᶠ y in 𝓝 η, β y < β x + 1 from hηx h).self_of_nhds

/-- The set where an upper semicontinuous function is at most `m` is open. -/
theorem isOpen_setOf_le {Z : Type*} [TopologicalSpace Z] {β : Z → ℕ}
    (hβ : UpperSemicontinuous β) (m : ℕ) : IsOpen {x | β x ≤ m} := by
  simpa [Set.preimage, Nat.lt_succ_iff] using hβ.isOpen_preimage (m + 1)

/-- The generic point of `Spec K` maps to the point of `Spec R` given by the kernel of `g`. -/
private theorem base_generic_point_eq {R K : Type u} [CommRing R] [Field K] (g : R →+* K)
    (I : PrimeSpectrum R) (hI : RingHom.ker g = I.asIdeal) :
    (Spec.map (CommRingCat.ofHom g)).base (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K)) = I := by
  refine PrimeSpectrum.ext ?_
  ext x
  change x ∈ Ideal.comap g ⊥ ↔ x ∈ I.asIdeal
  rw [← RingHom.ker_eq_comap_bot, hI]

section

attribute [local instance 10000] HasDerivedCategory.standard

open DeRhamCohomologyDirectImage

/-- **The Hodge numbers add up to the de Rham numbers in characteristic zero, granted
Deligne–Illusie in characteristic `p`.** Let `k` be a field of characteristic zero and let
`f : X ⟶ Spec k` be proper and smooth. Assume `hDI`: for every prime `p`, every finite field `F`
of characteristic `p` and every proper smooth `f₀ : X₀ ⟶ Spec F` whose forms `Ω^i_{X₀/F}` vanish
for `i ≥ p` and which is the base change along `W₂(F) ⟶ F` of a proper smooth scheme over
`W₂(F)`, `∑_{i ≤ n} dim_F H^{n-i}(X₀, Ω^i_{X₀/F}) = dim_F H^n_{dR}(X₀/F)` for every `n`. Then

`∑_{i ≤ n} dim_k H^{n-i}(X, Ω^i_{X/k}) = dim_k H^n_{dR}(X/k)`

for every `n`. The hypothesis `hDI` is the theorem of Deligne and Illusie, not proved here. -/
theorem sum_hodgeNumbers_eq_deRhamBetti_of_charZero (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    (hDI : ∀ (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Finite F] [CharP F p]
      (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (.of F)) [IsProper f₀] [Smooth f₀],
      (∀ i : ℕ, p ≤ i → IsZero (Scheme.Hom.relativeDifferentialForms f₀ (i : ℤ))) →
      (∃ (X₁ : Scheme.{u}) (f₁ : X₁ ⟶ Spec (.of (TruncatedWittVector p 2 F))) (j : X₀ ⟶ X₁),
        IsProper f₁ ∧ Smooth f₁ ∧
          IsPullback j f₀ f₁ (Spec.map (CommRingCat.ofHom (wittTwoToField p F)))) →
      ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), Module.finrank F
          (cohomologyOverField F f₀ (Scheme.Hom.relativeDifferentialForms f₀ (i : ℤ)) (n - i)) =
        Module.finrank F ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of F)).inv.hom).obj
          (Scheme.Hom.deRhamCohomologyBaseModule f₀ (n : ℤ))))
    (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), Module.finrank k
        (cohomologyOverField k f (Scheme.Hom.relativeDifferentialForms f (i : ℤ)) (n - i)) =
      Module.finrank k ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).obj
        (Scheme.Hom.deRhamCohomologyBaseModule f (n : ℤ))) := by
  -- step 1: the model over a finitely generated `ℤ`-algebra
  obtain ⟨R, _, φ, Y, h, q', hft, hinj, hpr, hsm, hpb⟩ :=
    exists_isPullback_finiteType_properSmooth k f
  have : IsDomain R := hinj.isDomain φ
  have : CharZero R := φ.charZero
  have : Algebra.FinitePresentation ℤ R := Algebra.FinitePresentation.of_finiteType.mp hft
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  let pt : Spec (.of k) := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : (Spec.map (CommRingCat.ofHom φ)).base pt = η :=
    base_generic_point_eq φ η ((RingHom.injective_iff_ker_eq_bot φ).mp hinj)
  have hspec : ∀ x : PrimeSpectrum R, η ⤳ x := fun x =>
    (PrimeSpectrum.le_iff_specializes η x).mp bot_le
  -- step 2: the Betti functions and the open set where they take their generic values
  let βH : ℕ → Spec (.of R) → ℕ := fun i =>
    DerivedFibreBetti.derivedFiberBetti (Spec (.of R)) (hodgeDirectImage h i)
      (isPseudoCoherent_hodgeDirectImage h i) ((n - i : ℕ) : ℤ)
  let βD : Spec (.of R) → ℕ :=
    DerivedFibreBetti.derivedFiberBetti (Spec (.of R)) (derivedDeRhamDirectImageUnbounded h)
      (isPseudoCoherent_derivedDeRhamDirectImageUnbounded h) (n : ℤ)
  have hβH : ∀ i, UpperSemicontinuous (βH i) := fun i =>
    DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti _ _ _ _
  have hβD : UpperSemicontinuous βD :=
    DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti _ _ _ _
  let U : Set (PrimeSpectrum R) := Algebra.smoothLocus ℤ R ∩ {x | βD x ≤ βD η} ∩
    ⋂ i ∈ Finset.range (n + 1), {x | βH i x ≤ βH i η}
  have hUo : IsOpen U :=
    (Algebra.isOpen_smoothLocus.inter (isOpen_setOf_le hβD _)).inter
      (isOpen_biInter_finset fun i _ => isOpen_setOf_le (hβH i) _)
  have hηU : η ∈ U :=
    ⟨⟨mem_smoothLocus_int_bot R, show βD η ≤ βD η from le_rfl⟩,
      Set.mem_iInter₂.mpr fun i _ => show βH i η ≤ βH i η from le_rfl⟩
  -- step 3: a closed point with finite residue field of large characteristic
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace h
  obtain ⟨N, hN⟩ := exists_isZero_relativeDifferentialForms h
  obtain ⟨s, hsU, hsmax, hsfin, hsN⟩ := exists_isMaximal_finite_lt_ringChar R hUo ⟨η, hηU⟩ N
  set κ := s.asIdeal.ResidueField
  set p := ringChar κ
  have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero κ p).resolve_right (by omega)⟩
  -- the fibre at `s`
  let gs : Spec (.of κ) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R κ))
  have hsq : IsPullback (pullback.fst h gs) (pullback.snd h gs) h gs :=
    IsPullback.of_hasPullback h gs
  let ps : Spec (.of κ) := ⟨⊥, Ideal.isPrime_bot⟩
  have hs : gs.base ps = s :=
    base_generic_point_eq (algebraMap R κ) s (Ideal.ker_algebraMap_residueField _)
  -- step 4: the lift over `W₂(κ)`
  obtain ⟨ψ, hψ⟩ := exists_wittTwo_lift R hsU.1.1 p
  let gW : Spec (.of (TruncatedWittVector p 2 κ)) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom ψ)
  let πs : Spec (.of κ) ⟶ Spec (.of (TruncatedWittVector p 2 κ)) :=
    Spec.map (CommRingCat.ofHom (wittTwoToField p κ))
  have hcomp : πs ≫ gW = gs := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
  have hW : IsPullback (pullback.fst h gW) (pullback.snd h gW) h gW :=
    IsPullback.of_hasPullback h gW
  have hcond : pullback.fst h gs ≫ h = (pullback.snd h gs ≫ πs) ≫ gW := by
    rw [Category.assoc, hcomp, pullback.condition]
  have hlift : IsPullback (pullback.lift (pullback.fst h gs) (pullback.snd h gs ≫ πs) hcond)
      (pullback.snd h gs) (pullback.snd h gW) πs := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hW
    rw [pullback.lift_fst, hcomp]
    exact hsq
  have hΩ : ∀ i : ℕ, p ≤ i →
      IsZero (Scheme.Hom.relativeDifferentialForms (pullback.snd h gs) (i : ℤ)) := fun i hi =>
    isZero_relativeDifferentialForms_of_isPullback hsq i (hN i (by omega))
  have hfib := hDI p κ _ (pullback.snd h gs) hΩ
    ⟨_, pullback.snd h gW, _, inferInstance, inferInstance, hlift⟩ n
  -- comparison of the two fibres
  have hηs : ∀ {β : Spec (.of R) → ℕ}, UpperSemicontinuous β → β s ≤ β η → β s = β η :=
    fun hβ hle => eq_of_le_of_specializes hβ (hspec s) hle
  have hD : βD η = Module.finrank k
      ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).obj
        (Scheme.Hom.deRhamCohomologyBaseModule f (n : ℤ))) := by
    rw [← hη]
    exact derivedFiberBetti_deRhamDirectImage h k hpb n pt
  have hDs : βD s = Module.finrank κ
      ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of κ)).inv.hom).obj
        (Scheme.Hom.deRhamCohomologyBaseModule (pullback.snd h gs) (n : ℤ))) := by
    exact (congrArg βD hs).symm.trans (derivedFiberBetti_deRhamDirectImage h κ hsq n ps)
  have hH : ∀ i, βH i η = Module.finrank k
      (cohomologyOverField k f (Scheme.Hom.relativeDifferentialForms f (i : ℤ)) (n - i)) := by
    intro i
    rw [← hη]
    exact derivedFiberBetti_hodgeDirectImage h k hpb i (n - i) pt
  have hHs : ∀ i, βH i s = Module.finrank κ (cohomologyOverField κ (pullback.snd h gs)
      (Scheme.Hom.relativeDifferentialForms (pullback.snd h gs) (i : ℤ)) (n - i)) := by
    intro i
    exact (congrArg (βH i) hs).symm.trans
      (derivedFiberBetti_hodgeDirectImage h κ hsq i (n - i) ps)
  rw [← hD, ← hηs hβD hsU.1.2, hDs, ← hfib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← hH, ← hηs (hβH i) (Set.mem_iInter₂.mp hsU.2 i hi), hHs]

end

end AlgebraicGeometry.HodgeSpreadingOut
