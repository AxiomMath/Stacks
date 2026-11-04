module

public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreFormula

/-!
# Weakly associated primes of a flat tensor product over a finite type algebra

Let `R → A` be a ring map of finite type, let `P` be a finite `A`-module and let `q` be a prime
of `A`, lying over a prime `p` of `R`, at which `P` is flat over `R`.  For an arbitrary
`R`-module `M` this file proves

`q ∈ WeakAss_A(P ⊗_R M) ↔ (p ∈ WeakAss_R(M) and q ∈ WeakAss_A(P ⊗_R κ(p)))`,

the second clause being the fibre condition of [Stacks, Tag 05IG] written over `A`:  over a
Noetherian fibre ring `A ⊗_R κ(p)` it says exactly that some prime of the fibre ring associated
to the fibre module contracts to `q`.

The input is [Stacks, Tag 05IG] itself, the case of a ring map of *finite presentation* and a
*finitely presented* module, proved in
`StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreFormula` as
`Stacks.WeaklyAssociatedPrimes.tensorFibreFormula05IG`.  Two reductions carry the tag from there
to the statement above, and they are the content of this file.  They live here rather than
alongside the comparisons they use — in
`StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreFiniteType`, which states the tag
— because the proof of the tag runs through those comparisons, so only a module downstream of it
can apply it.

First, the module.  A finite module flat over the base at `q` need not be finitely presented —
`Module.not_forall_finitePresentation_of_finite_of_flat` is the counterexample — but by
[Stacks, Tag 05I7], available here as
`Stacks.Flatness.finitePresentation_isLocalizedModule_of_flat`, its localization at `q` is
finitely presented over `A_q`.  A finitely presented `A`-module `P'` with the same localization
then exists, and its relative flat locus is open ([Stacks, Tag 00RC]), so `P'` becomes flat over
`R` on a basic open `D(g)` around `q`.  Tag 05IG applies to `A_g` and `P'_g`, and both sides of
the equivalence depend only on the localization at `q`, so the answer transports back to `P`.

Second, the algebra.  A finite type `R`-algebra is a quotient of a polynomial algebra, which is
of finite presentation, and both sides of the equivalence are insensitive to a surjective change
of the ring: the module is unchanged and the primes correspond under contraction.

## Main results

* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_tensorProduct_iff_of_finitePresentation'`
  is the equivalence for a ring map of finite presentation and a finitely presented module.
* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_tensorProduct_iff_of_finite'` removes
  finite presentation of the module.
* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteType'`
  removes finite presentation of the ring map; it is the form the essentially-finite-type
  statement is deduced from.

## References

* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 05I7](https://stacks.math.columbia.edu/tag/05I7)
* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks.WeaklyAssociatedPrimes

/-- **[Stacks, Tag 05IG] with the fibre condition read over `S`.**  For a ring map `R → S` of
finite presentation and a finitely presented `S`-module `N` flat over `R`, a prime `q` of `S`
lying over `p` is weakly associated to `N ⊗[R] M` exactly when `p` is weakly associated to `M`
and `q` is weakly associated to `N ⊗[R] κ(p)`. -/
theorem isWeaklyAssociatedPrime_tensorProduct_iff_of_finitePresentation'
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    {M : Type u} [AddCommGroup M] [Module R M]
    {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] [Module.Flat R N]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    IsWeaklyAssociatedPrime S (N ⊗[R] M) q ↔
      IsWeaklyAssociatedPrime R M p ∧
        IsWeaklyAssociatedPrime S (N ⊗[R] p.ResidueField) q := by
  have : IsNoetherianRing (S ⊗[R] p.ResidueField) := isNoetherianRing_tensorResidueField p
  rw [tensorFibreFormula05IG R S M N p q, isWeaklyAssociatedPrime_tensorResidueField_iff p q]

/-- **The equivalence of [Stacks, Tag 05IG] for a module that is merely finite.**  For a ring map
`R → A` of finite presentation, a finite `A`-module `P` and a prime `q` of `A` lying over `p` at
which `P` is flat over `R`, the prime `q` is weakly associated to `P ⊗[R] M` exactly when `p` is
weakly associated to `M` and `q` is weakly associated to `P ⊗[R] κ(p)`.

By [Stacks, Tag 05I7] the localization of `P` at `q` is finitely presented, so `P` agrees at `q`
with a finitely presented `A`-module which, the relative flat locus being open, is flat over `R`
on a basic open around `q`;  both sides of the equivalence depend only on the localization
at `q`. -/
theorem isWeaklyAssociatedPrime_tensorProduct_iff_of_finite'
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    {P : Type u} [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower R A P]
    [Module.Finite A P]
    {M : Type u} [AddCommGroup M] [Module R M]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p]
    (hflat : Module.Flat R (LocalizedModule q.primeCompl P)) :
    IsWeaklyAssociatedPrime A (P ⊗[R] M) q ↔
      IsWeaklyAssociatedPrime R M p ∧
        IsWeaklyAssociatedPrime A (P ⊗[R] p.ResidueField) q := by
  classical
  have hfpq : Module.FinitePresentation (Localization.AtPrime q) (LocalizedModule.AtPrime q P) :=
    Stacks.Flatness.finitePresentation_isLocalizedModule_of_flat R A P ⟨q, inferInstance⟩
      (LocalizedModule.mkLinearMap q.primeCompl P) hflat
  obtain ⟨P', iAdd, iMod, φ, hP'fin, hloc, hP'fp⟩ :=
    Module.exists_finite_isLocalizedModule_comp_atPrime (R := A) q
      (Localization.AtPrime q) (LocalizedModule.mkLinearMap q.primeCompl P)
  let : AddCommGroup P' := iAdd
  let : Module A P' := iMod
  let : Module R P' := Module.compHom P' (algebraMap R A)
  have : IsScalarTower R A P' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite A P' := hP'fin
  have hlocφ : IsLocalizedModule q.primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl P) ∘ₗ φ) := hloc
  have : Module.FinitePresentation A P' := hP'fp hfpq
  have hflat' : Module.Flat R (LocalizedModule q.primeCompl P') :=
    Module.Flat.of_linearEquiv ((IsLocalizedModule.linearEquiv q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl P')
      ((LocalizedModule.mkLinearMap q.primeCompl P) ∘ₗ φ)).restrictScalars R)
  have hqmem : (⟨q, inferInstance⟩ : PrimeSpectrum A) ∈ {q' : PrimeSpectrum A |
      Module.Flat R (LocalizedModule.AtPrime q'.asIdeal P')} := hflat'
  rw [PrimeSpectrum.eq_biUnion_of_isOpen
    (Module.isOpen_setOf_flat_localizedModule_atPrime (R := R) (S := A) (M := P'))] at hqmem
  obtain ⟨g, hgsub, hgmem⟩ := Set.mem_iUnion₂.mp hqmem
  have hgq : g ∉ q := (PrimeSpectrum.mem_basicOpen g _).mp hgmem
  have : Module.Flat R (LocalizedModule.Away g P') :=
    Stacks.Flatness.OpenFlatLocus.flat_localizedModule_away_of_forall_flat_atPrime g
      fun _ hq' => hgsub hq'
  have : Algebra.FinitePresentation A (Localization.Away g) :=
    IsLocalization.Away.finitePresentation g
  have : Algebra.FinitePresentation R (Localization.Away g) :=
    Algebra.FinitePresentation.trans R A (Localization.Away g)
  have hdisj : Disjoint (Submonoid.powers g : Set A) (q : Set A) := by
    refine Set.disjoint_left.mpr ?_
    rintro a ⟨n, rfl⟩ ha
    exact hgq ((‹q.IsPrime›).mem_of_pow_mem n ha)
  have hqgp : (q.map (algebraMap A (Localization.Away g))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) _ q inferInstance hdisj
  have hqgc : (q.map (algebraMap A (Localization.Away g))).comap
      (algebraMap A (Localization.Away g)) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) _ inferInstance hdisj
  -- the two sides of the equivalence only depend on the localization of `P` at `q`
  have htrans : ∀ (X : Type u) [AddCommGroup X] [Module R X],
      IsWeaklyAssociatedPrime (Localization.Away g)
          (LocalizedModule.Away g P' ⊗[R] X) (q.map (algebraMap A (Localization.Away g))) ↔
        IsWeaklyAssociatedPrime A (P ⊗[R] X) q := by
    intro X _ _
    have h1 := isWeaklyAssociatedPrime_tensor_comap_iff_of_isLocalization
      (R := R) (A := A) (A' := Localization.Away g) (P := P') (P' := LocalizedModule.Away g P')
      (X := X) (Submonoid.powers g) (LocalizedModule.mkLinearMap (Submonoid.powers g) P')
      (q.map (algebraMap A (Localization.Away g))) hqgp
    rw [hqgc] at h1
    have h2 := isWeaklyAssociatedPrime_tensor_comap_iff_of_isLocalization
      (R := R) (A := A) (A' := Localization.AtPrime q) (P := P')
      (P' := LocalizedModule.AtPrime q P) (X := X) q.primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl P) ∘ₗ φ)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) inferInstance
    have h3 := isWeaklyAssociatedPrime_tensor_comap_iff_of_isLocalization
      (R := R) (A := A) (A' := Localization.AtPrime q) (P := P)
      (P' := LocalizedModule.AtPrime q P) (X := X) q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) inferInstance
    have hmq : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).comap
        (algebraMap A (Localization.AtPrime q)) = q :=
      IsLocalization.AtPrime.under_maximalIdeal (S := Localization.AtPrime q) (I := q)
    rw [hmq] at h2 h3
    exact h1.trans (h2.symm.trans h3)
  have : (q.map (algebraMap A (Localization.Away g))).LiesOver q := ⟨hqgc.symm⟩
  have : (q.map (algebraMap A (Localization.Away g))).LiesOver p :=
    Ideal.LiesOver.trans _ q p
  rw [← htrans M, isWeaklyAssociatedPrime_tensorProduct_iff_of_finitePresentation' p
      (q.map (algebraMap A (Localization.Away g))),
    htrans p.ResidueField]

/-- **The equivalence of [Stacks, Tag 05IG] over a finite type algebra.**  For a ring map `R → A`
of finite type, a finite `A`-module `P` and a prime `q` of `A` lying over `p` at which `P` is
flat over `R`, the prime `q` is weakly associated to `P ⊗[R] M` exactly when `p` is weakly
associated to `M` and `q` is weakly associated to `P ⊗[R] κ(p)`.

A finite type algebra is a quotient of a polynomial algebra, which is of finite presentation,
and neither side of the equivalence changes under a surjective change of the ring. -/
theorem isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteType'
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    {P : Type u} [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower R A P]
    [Module.Finite A P]
    {M : Type u} [AddCommGroup M] [Module R M]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p]
    (hflat : Module.Flat R (LocalizedModule q.primeCompl P)) :
    IsWeaklyAssociatedPrime A (P ⊗[R] M) q ↔
      IsWeaklyAssociatedPrime R M p ∧
        IsWeaklyAssociatedPrime A (P ⊗[R] p.ResidueField) q := by
  classical
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType R A›
  set A₀ := MvPolynomial (Fin n) R with hA₀
  let : Algebra A₀ A := π.toRingHom.toAlgebra
  have halg : ∀ a : A₀, algebraMap A₀ A a = π a := fun _ => rfl
  have hsurj : Function.Surjective (algebraMap A₀ A) := hπ
  have : IsScalarTower R A₀ A := IsScalarTower.of_algebraMap_eq fun r => (π.commutes r).symm
  let : Module A₀ P := Module.compHom P (algebraMap A₀ A)
  have : IsScalarTower A₀ A P := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R A₀ P := IsScalarTower.of_algebraMap_smul fun r x => by
    rw [← algebraMap_smul A (algebraMap R A₀ r) x, ← IsScalarTower.algebraMap_apply R A₀ A,
      algebraMap_smul]
  have : Module.Finite A₀ P := by
    obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := A) (M := P)
    exact Module.finite_def.mpr ⟨T, by
      rw [← Submodule.restrictScalars_span A₀ A hsurj (T : Set P), hT,
        Submodule.restrictScalars_top]⟩
  set q₀ : Ideal A₀ := q.comap (algebraMap A₀ A) with hq₀
  have : q₀.IsPrime := Ideal.comap_isPrime _ _
  have : q₀.LiesOver p := Ideal.comap_liesOver (A := R) q p π
  have hsub : Algebra.algebraMapSubmonoid A q₀.primeCompl = q.primeCompl :=
    algebraMapSubmonoid_primeCompl_comap hsurj q
  have hup : IsLocalizedModule (Algebra.algebraMapSubmonoid A q₀.primeCompl)
      (LocalizedModule.mkLinearMap q.primeCompl P) := by
    rw [hsub]; infer_instance
  have hloc0 : IsLocalizedModule q₀.primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl P).restrictScalars A₀) :=
    IsLocalizedModule.restrictScalars (A := A) q₀.primeCompl _
  have hflat₀ : Module.Flat R (LocalizedModule q₀.primeCompl P) :=
    Module.Flat.of_linearEquiv
      ((IsLocalizedModule.linearEquiv q₀.primeCompl
        (LocalizedModule.mkLinearMap q₀.primeCompl P)
        ((LocalizedModule.mkLinearMap q.primeCompl P).restrictScalars A₀)).restrictScalars R)
  have key := isWeaklyAssociatedPrime_tensorProduct_iff_of_finite'
    (A := A₀) (P := P) (M := M) p q₀ hflat₀
  rw [isWeaklyAssociatedPrime_comap_iff_of_surjective (A := A₀) (B := A) hsurj q,
    isWeaklyAssociatedPrime_comap_iff_of_surjective (A := A₀) (B := A) hsurj
      (L := P ⊗[R] p.ResidueField) q]
  exact key

end Stacks.WeaklyAssociatedPrimes

end
