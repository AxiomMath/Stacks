module

public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.StalkFinitePresentationAffine
public import StacksFrontier.RingTheory.EssentialFiniteness.Composition
public import StacksFrontier.RingTheory.Flat.OpenFlatLocusNoetherian
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.FlatTensorProduct
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Functoriality

/-!
# Weakly associated primes of a flat tensor product over a finite type algebra

Let `R → A` be a ring map of finite type, let `P` be a finite `A`-module and let `q` be a prime
of `A`, lying over a prime `p` of `R`, at which `P` is flat over `R`.  For an arbitrary
`R`-module `M` this file proves

`q ∈ WeakAss_A(P ⊗_R M) ↔ (p ∈ WeakAss_R(M) and q ∈ WeakAss_A(P ⊗_R κ(p)))`,

the second clause being the fibre condition of [Stacks, Tag 05IG] written over `A`:  over a
Noetherian fibre ring `A ⊗_R κ(p)` it says exactly that some prime of the fibre ring associated
to the fibre module contracts to `q`.

The one input not proved here is [Stacks, Tag 05IG] itself, the case of a ring map of *finite
presentation* and a *finitely presented* module, which is named
`Stacks.WeaklyAssociatedPrimes.TensorFibreFormula05IG` and threaded through as a hypothesis.
Everything else is proved in the library.  Two reductions carry the tag from there to the statement
above, and they are the content of this file.

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

## Main definitions

* `Stacks.WeaklyAssociatedPrimes.TensorFibreFormula05IG` is [Stacks, Tag 05IG] as a
  proposition.

## Main results

* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_tensorResidueField_iff` identifies the
  fibre condition over `A` with the fibre condition over the fibre ring.
* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_tensorProduct_iff_of_finitePresentation`
  is the equivalence for a ring map of finite presentation and a finitely presented module.
* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_tensorProduct_iff_of_finite` removes
  finite presentation of the module.
* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteType`
  removes finite presentation of the ring map; it is the form the essentially-finite-type
  statement is deduced from.

## References

* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 05I7](https://stacks.math.columbia.edu/tag/05I7)
* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
-/

@[expose] public section

open TensorProduct

universe u v w t

namespace Stacks.WeaklyAssociatedPrimes

/-- **The statement of [Stacks, Tag 05IG].**  For a ring map `R → S` of finite presentation, a
finitely presented `S`-module `N` which is flat over `R`, an arbitrary `R`-module `M` and a prime
`q` of `S` lying over a prime `p` of `R`, the prime `q` is weakly associated to `N ⊗[R] M`
exactly when `p` is weakly associated to `M` and the prime of the fibre ring `S ⊗[R] κ(p)` that
corresponds to `q` is associated to the fibre module `(S ⊗[R] κ(p)) ⊗[S] N`.

The prime `q S ⊗[R] κ(p)` of the source is written as a prime of the fibre ring contracting to
`q`, making explicit the identification of the primes of `S ⊗[R] κ(p)` with the primes of `S`
lying over `p`;  this is the convention of
`Stacks.Divisors.WeaklyAssociatedPrimesTensorFormula`. -/
def TensorFibreFormula05IG : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (M : Type u) [AddCommGroup M] [Module R M]
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] [Module.Flat R N]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p],
    IsWeaklyAssociatedPrime S (N ⊗[R] M) q ↔
      IsWeaklyAssociatedPrime R M p ∧
        ∃ q' ∈ assStacks (S ⊗[R] p.ResidueField) ((S ⊗[R] p.ResidueField) ⊗[S] N),
          q = Ideal.comap (algebraMap S (S ⊗[R] p.ResidueField)) q'

section Fibre

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]

/-- If every element of `B` becomes, after multiplication by a unit coming from `A`, the image of
an element of `A`, then contracting a weakly associated prime of a `B`-module along `A → B`
gives a weakly associated prime of the same module read over `A`. -/
theorem isWeaklyAssociatedPrime_comap_of_fractions {A B L : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup L] [Module A L] [Module B L] [IsScalarTower A B L]
    (hfrac : ∀ b : B, ∃ a d : A, IsUnit (algebraMap A B d) ∧
      algebraMap A B d * b = algebraMap A B a)
    {q : Ideal B} (hq : IsWeaklyAssociatedPrime B L q) :
    IsWeaklyAssociatedPrime A L (q.comap (algebraMap A B)) := by
  obtain ⟨m, hm⟩ := hq
  have : q.IsPrime := hm.1.1
  refine ⟨m, minimalPrimes_of_radical_condition _ _ (Ideal.IsPrime.comap _) ?_ ?_⟩
  · rw [annihilator_comap (S := B)]
    exact Ideal.comap_mono hm.1.2
  · intro a ha
    obtain ⟨b, hb, n, hn⟩ := exists_mul_pow_mem_of_mem_minimalPrimes hm ha
    obtain ⟨c, d, hd, he⟩ := hfrac b
    refine ⟨c, ?_, n, ?_⟩
    · intro hc
      have hh : algebraMap A B d * b ∈ q := he.symm ▸ hc
      exact hb ((this.mem_or_mem hh).resolve_left
        (fun h => this.ne_top (q.eq_top_of_isUnit_mem h hd)))
    · rw [annihilator_comap (S := B), Ideal.mem_comap,
        Submodule.mem_annihilator_span_singleton, map_mul, map_pow, ← he,
        mul_assoc, mul_smul]
      rw [Submodule.mem_annihilator_span_singleton] at hn
      rw [hn, smul_zero]

/-- A prime of the fibre ring `S ⊗[R] κ(p)` weakly associated to a module contracts to a prime of
`S` weakly associated to the same module:  every element of the fibre ring is a fraction with
numerator and denominator coming from `S`. -/
theorem isWeaklyAssociatedPrime_comap_tensorResidueField {L : Type*}
    (p : Ideal R) [p.IsPrime]
    [AddCommGroup L] [Module S L] [Module (S ⊗[R] p.ResidueField) L]
    [IsScalarTower S (S ⊗[R] p.ResidueField) L]
    {q : Ideal (S ⊗[R] p.ResidueField)}
    (hq : IsWeaklyAssociatedPrime (S ⊗[R] p.ResidueField) L q) :
    IsWeaklyAssociatedPrime S L (q.comap (algebraMap S (S ⊗[R] p.ResidueField))) := by
  apply isWeaklyAssociatedPrime_comap_of_fractions _ hq
  intro b
  obtain ⟨r, hr, s, hs⟩ := Ideal.ResidueField.exists_smul_eq_tmul_one p b
  refine ⟨s, algebraMap R S r, ?_, ?_⟩
  · have hunit : IsUnit (algebraMap R p.ResidueField r) :=
      isUnit_iff_ne_zero.mpr (fun h => hr (Ideal.algebraMap_residueField_eq_zero.mp h))
    convert hunit.map (Algebra.TensorProduct.includeRight (R := R) (A := S)).toRingHom using 1
    exact (Algebra.TensorProduct.includeRight
      (R := R) (A := S) (B := p.ResidueField)).commutes r |>.symm
  · change algebraMap S (S ⊗[R] p.ResidueField) (algebraMap R S r) * b = s ⊗ₜ[R] 1
    rw [← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
    exact hs

/-- Over a Noetherian ring the weakly associated primes of a module are its associated primes in
the sense of [Stacks, Tag 00LA]. -/
theorem isWeaklyAssociatedPrime_iff_isAssociatedPrimeStacks {A L : Type*} [CommRing A]
    [IsNoetherianRing A] [AddCommGroup L] [Module A L] (q : Ideal A) :
    IsWeaklyAssociatedPrime A L q ↔ IsAssociatedPrimeStacks A L q := by
  simpa only [IsWeaklyAssociatedPrime, IsAssociatedPrimeStacks, Submodule.bot_colon',
    Submodule.span_eq, eq_comm] using
    (isAssociatedPrime_tfae_of_fg (M := L) (IsNoetherian.noetherian q)).out 3 1

/-- For a Noetherian fibre ring `S ⊗[R] κ(p)`, a prime of `S` is weakly associated to a module
over the fibre ring exactly when some prime of the fibre ring associated to that module
contracts to it. -/
theorem isWeaklyAssociatedPrime_iff_exists_fibre {L : Type*}
    (p : Ideal R) [p.IsPrime] [IsNoetherianRing (S ⊗[R] p.ResidueField)]
    [AddCommGroup L] [Module S L] [Module (S ⊗[R] p.ResidueField) L]
    [IsScalarTower S (S ⊗[R] p.ResidueField) L] (q : Ideal S) :
    IsWeaklyAssociatedPrime S L q ↔
      ∃ q' ∈ assStacks (S ⊗[R] p.ResidueField) L,
        q = q'.comap (algebraMap S (S ⊗[R] p.ResidueField)) := by
  constructor
  · intro hq
    obtain ⟨q', hq', he⟩ := weakAss_subset_comap_image_weakAss
      (S := S ⊗[R] p.ResidueField) q hq
    exact ⟨q', (isWeaklyAssociatedPrime_iff_isAssociatedPrimeStacks q').mp hq', he.symm⟩
  · rintro ⟨q', hq', rfl⟩
    exact isWeaklyAssociatedPrime_comap_tensorResidueField p
      ((isWeaklyAssociatedPrime_iff_isAssociatedPrimeStacks q').mpr hq')

/-- **The fibre condition over `S`.**  For a Noetherian fibre ring `S ⊗[R] κ(p)`, a prime `q` of
`S` is weakly associated to `N ⊗[R] κ(p)` exactly when some associated prime of the fibre module
`(S ⊗[R] κ(p)) ⊗[S] N` contracts to `q`. -/
theorem isWeaklyAssociatedPrime_tensorResidueField_iff {N : Type w}
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (p : Ideal R) [p.IsPrime] [IsNoetherianRing (S ⊗[R] p.ResidueField)] (q : Ideal S) :
    IsWeaklyAssociatedPrime S (N ⊗[R] p.ResidueField) q ↔
      ∃ q' ∈ assStacks (S ⊗[R] p.ResidueField) ((S ⊗[R] p.ResidueField) ⊗[S] N),
        q = q'.comap (algebraMap S (S ⊗[R] p.ResidueField)) := by
  let e : ((S ⊗[R] p.ResidueField) ⊗[S] N) ≃ₗ[S] N ⊗[R] p.ResidueField :=
    (TensorProduct.comm S _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N p.ResidueField)
  have he : IsWeaklyAssociatedPrime S ((S ⊗[R] p.ResidueField) ⊗[S] N) q ↔
      IsWeaklyAssociatedPrime S (N ⊗[R] p.ResidueField) q := by
    have hann (m) : (S ∙ e m).annihilator = (S ∙ m).annihilator := by
      ext r
      simp only [Submodule.mem_annihilator_span_singleton, ← e.map_smul, e.map_eq_zero_iff]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨e m, (hann m).symm ▸ hm⟩
    · rintro ⟨m, hm⟩
      exact ⟨e.symm m, by rwa [← hann, e.apply_symm_apply]⟩
  exact he.symm.trans (isWeaklyAssociatedPrime_iff_exists_fibre p q)

end Fibre

/-- Weak association is preserved and reflected by localization:  for a prime `q` of a
localization `S` of `R`, the prime `q` is weakly associated to the localized module exactly when
its contraction is weakly associated to the original one. -/
theorem isWeaklyAssociatedPrime_iff_of_isLocalization
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (U : Submonoid R) [IsLocalization U S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (f : M →ₗ[R] N) [IsLocalizedModule U f]
    (q : Ideal S) (hq : q.IsPrime) :
    IsWeaklyAssociatedPrime S N q ↔
      IsWeaklyAssociatedPrime R M (Ideal.comap (algebraMap R S) q) := by
  let e := IsLocalization.orderIsoOfPrime U S
  let p : Ideal R := Ideal.under R q
  have hp : p.IsPrime := Ideal.IsPrime.comap _
  have hpd : Disjoint (U : Set R) (p : Set R) := by
    change Disjoint (U : Set R) (Ideal.under R q : Set R)
    rw [IsLocalization.disjoint_under_iff U S]
    exact hq.ne_top
  have heq : (e ⟨q, hq⟩).1 = p := rfl
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨⟨m, s⟩, hsm⟩ := IsLocalizedModule.surj U f n
    obtain ⟨v, hv⟩ := IsLocalization.map_units S s
    have hmul : f m = (v : S) • n := by
      rw [hv, algebraMap_smul]
      exact hsm.symm
    have hann : (S ∙ f m).annihilator = (S ∙ n).annihilator := by
      rw [hmul, Submodule.span_singleton_smul_eq v.isUnit]
    have hn' : q ∈ ((S ∙ f m).annihilator).minimalPrimes := by
      rwa [hann]
    change Minimal (fun J : Ideal S => J.IsPrime ∧ (S ∙ f m).annihilator ≤ J) q at hn'
    have hAnnp : (R ∙ m).annihilator ≤ p := by
      simpa [annihilatorOfElem_semiring] using
        (annOfElem_localized_le_iff U f m q hq).mp hn'.1.2
    refine ⟨m, ?_⟩
    change Minimal (fun J : Ideal R => J.IsPrime ∧ (R ∙ m).annihilator ≤ J) p
    refine ⟨⟨hp, hAnnp⟩, ?_⟩
    intro p' hp' hp'le
    have hpd' : Disjoint (U : Set R) (p' : Set R) :=
      Set.disjoint_of_subset_right hp'le hpd
    let z' : {J : Ideal S // J.IsPrime} := e.symm ⟨p', hp'.1, hpd'⟩
    let q' : Ideal S := z'.1
    have hq' : q'.IsPrime := z'.property
    have hz' : (e z').1 = p' := by
      simp [z']
    have hporder : e z' ≤ e ⟨q, hq⟩ := Subtype.coe_le_coe.mp (by rwa [hz', heq])
    have hq'le : z' ≤ ⟨q, hq⟩ := e.le_iff_le.mp hporder
    have hAnnR' : annihilatorOfElem_semiring (R := R) m ≤
        Ideal.comap (algebraMap R S) q' := by
      change annihilatorOfElem_semiring (R := R) m ≤ (e z').1
      rw [hz']
      exact hp'.2
    have hAnnq' : (S ∙ f m).annihilator ≤ q' := by
      simpa [annihilatorOfElem_semiring] using
        (annOfElem_localized_le_iff U f m q' hq').mpr hAnnR'
    have hRorder := e.monotone (Subtype.mk_le_mk.mpr (hn'.2 ⟨hq', hAnnq'⟩ hq'le) :
      (⟨q, hq⟩ : {J : Ideal S // J.IsPrime}) ≤ z')
    simpa [heq, hz'] using (Subtype.mk_le_mk.mp hRorder : (e ⟨q, hq⟩).1 ≤ (e z').1)
  · rintro ⟨m, hm⟩
    change (R ∙ m).annihilator.IsMinimalPrime p at hm
    have hAnnq : (S ∙ f m).annihilator ≤ q := by
      simpa [annihilatorOfElem_semiring] using
        (annOfElem_localized_le_iff U f m q hq).mpr hm.le
    refine ⟨f m, ?_⟩
    change Minimal (fun J : Ideal S => J.IsPrime ∧ (S ∙ f m).annihilator ≤ J) q
    refine ⟨⟨hq, hAnnq⟩, ?_⟩
    intro q' hq' hq'le
    let z' : {J : Ideal S // J.IsPrime} := ⟨q', hq'.1⟩
    let p' : Ideal R := (e z').1
    have hp' : p'.IsPrime := (e z').property.1
    have hp'le : p' ≤ p := by
      have horder : e z' ≤ e ⟨q, hq⟩ := e.monotone hq'le
      change (e z').1 ≤ p
      rw [← heq]
      exact Subtype.mk_le_mk.mp horder
    have hAnnp' : (R ∙ m).annihilator ≤ p' := by
      have hh := (annOfElem_localized_le_iff U f m q' hq'.1).mp hq'.2
      simpa [annihilatorOfElem_semiring, p', z', e, IsLocalization.orderIsoOfPrime] using hh
    have hmin := hm.2 ⟨hp', hAnnp'⟩ hp'le
    have hRorder : e ⟨q, hq⟩ ≤ e z' := Subtype.coe_le_coe.mp (by rwa [heq])
    exact e.le_iff_le.mp hRorder

/-- Tensoring a localization map with an arbitrary module over the base ring again gives a
localization map:  `(P ⊗[R] M)` localizes to `(N ⊗[R] M)` at the same submonoid. -/
theorem isLocalizedModule_tensorRight
    {R T S P N M : Type*} [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
    [AddCommGroup P] [Module R P] [Module T P] [IsScalarTower R T P]
    [AddCommGroup N] [Module R N] [Module T N] [IsScalarTower R T N]
    [AddCommGroup M] [Module R M]
    (U : Submonoid T) [IsLocalization U S]
    (f : P →ₗ[T] N) [IsLocalizedModule U f] :
    IsLocalizedModule U
      (TensorProduct.AlgebraTensorModule.map f (LinearMap.id : M →ₗ[R] M)) := by
  let K := P ⊗[R] M
  let L := N ⊗[R] M
  let c : K →ₗ[T] S ⊗[T] K := TensorProduct.mk T S K 1
  let e₀ : N ≃ₗ[T] S ⊗[T] P :=
    IsLocalizedModule.linearEquiv U f (TensorProduct.mk T S P 1)
  let e : S ⊗[T] K ≃ₗ[T] L :=
    (TensorProduct.AlgebraTensorModule.assoc R T T S P M).symm.trans
      (TensorProduct.AlgebraTensorModule.congr e₀.symm (LinearEquiv.refl R M))
  have he : e.toLinearMap.comp c =
      TensorProduct.AlgebraTensorModule.map f (LinearMap.id : M →ₗ[R] M) := by
    ext p m
    exact congrArg (· ⊗ₜ[R] m)
      (IsLocalizedModule.linearEquiv_symm_apply U f (TensorProduct.mk T S P 1) p)
  rw [← he]
  exact IsLocalizedModule.of_linearEquiv U c e

/-- The fibre ring of a ring map essentially of finite type is Noetherian, being essentially of
finite type over a field. -/
theorem isNoetherianRing_tensorResidueField {R : Type u} [CommRing R] {S : Type u} [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] (p : Ideal R) [p.IsPrime] :
    IsNoetherianRing (S ⊗[R] p.ResidueField) := by
  have : Algebra.EssFiniteType p.ResidueField (p.ResidueField ⊗[R] S) := inferInstance
  have : IsNoetherianRing (p.ResidueField ⊗[R] S) :=
    Algebra.EssFiniteType.isNoetherianRing p.ResidueField _
  exact isNoetherianRing_of_ringEquiv _
    (Algebra.TensorProduct.comm R S p.ResidueField).toRingEquiv.symm

/-- Weak association of a prime to a tensor product `P ⊗[R] X` is unchanged by passing to a
localization of the ring together with the corresponding localization of `P`. -/
theorem isWeaklyAssociatedPrime_tensor_comap_iff_of_isLocalization
    {R A A' P P' X : Type*} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]
    [AddCommGroup P'] [Module R P'] [Module A P'] [IsScalarTower R A P']
    [Module A' P'] [IsScalarTower A A' P'] [IsScalarTower R A' P']
    [AddCommGroup X] [Module R X]
    (U : Submonoid A) [IsLocalization U A']
    (f : P →ₗ[A] P') [IsLocalizedModule U f]
    (q : Ideal A') (hq : q.IsPrime) :
    IsWeaklyAssociatedPrime A' (P' ⊗[R] X) q ↔
      IsWeaklyAssociatedPrime A (P ⊗[R] X) (q.comap (algebraMap A A')) := by
  have : IsLocalizedModule U
      (TensorProduct.AlgebraTensorModule.map f (LinearMap.id : X →ₗ[R] X)) :=
    isLocalizedModule_tensorRight (S := A') U f
  exact isWeaklyAssociatedPrime_iff_of_isLocalization U
    (TensorProduct.AlgebraTensorModule.map f (LinearMap.id : X →ₗ[R] X)) q hq

/-- Along a surjective ring map, the submonoid generated by the image of the complement of the
contraction of a prime is the complement of that prime. -/
theorem algebraMapSubmonoid_primeCompl_comap {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (hs : Function.Surjective (algebraMap A B)) (q : Ideal B) [q.IsPrime]
    [(q.comap (algebraMap A B)).IsPrime] :
    Algebra.algebraMapSubmonoid B (q.comap (algebraMap A B)).primeCompl = q.primeCompl := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hb
    obtain ⟨a, rfl⟩ := hs b
    exact ⟨a, hb, rfl⟩

/-- Along a surjective ring map `A → B`, weak association of an ideal of `B` to a `B`-module is
weak association of its contraction to the same module read over `A`. -/
theorem isWeaklyAssociatedPrime_comap_iff_of_surjective
    {A B L : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup L] [Module A L] [Module B L] [IsScalarTower A B L]
    (hs : Function.Surjective (algebraMap A B)) (q : Ideal B) :
    IsWeaklyAssociatedPrime B L q ↔
      IsWeaklyAssociatedPrime A L (q.comap (algebraMap A B)) := by
  constructor
  · refine isWeaklyAssociatedPrime_comap_of_fractions ?_
    intro b
    obtain ⟨a, rfl⟩ := hs b
    exact ⟨a, 1, by simp, by simp⟩
  · rintro ⟨m, hm⟩
    have hcp : (q.comap (algebraMap A B)).IsPrime := hm.1.1
    have hqp : q.IsPrime := by
      have h := Ideal.map_isPrime_of_surjective hs (Ideal.ker_le_comap (K := q) (algebraMap A B))
      rwa [Ideal.map_comap_of_surjective _ hs] at h
    refine ⟨m, minimalPrimes_of_radical_condition _ _ hqp ?_ ?_⟩
    · intro b hb
      obtain ⟨a, rfl⟩ := hs b
      exact hm.1.2 ((annihilator_comap (S := B) (R := A) m).ge hb)
    · intro f hf
      obtain ⟨a, rfl⟩ := hs f
      obtain ⟨s, hsq, n, hn⟩ := exists_mul_pow_mem_of_mem_minimalPrimes hm hf
      refine ⟨algebraMap A B s, hsq, n, ?_⟩
      have := (annihilator_comap (S := B) (R := A) m).le hn
      rwa [Ideal.mem_comap, map_mul, map_pow] at this

/-- If `f : M → N` is a localization map at `U` and `N` is `R`-flat, then so is `U⁻¹ M`. -/
private theorem flat_localizedModule_of_isLocalizedModule
    {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    (U : Submonoid A) (f : M →ₗ[A] N) [IsLocalizedModule U f] [Module.Flat R N] :
    Module.Flat R (LocalizedModule U M) :=
  Module.Flat.of_linearEquiv
    ((IsLocalizedModule.linearEquiv U (LocalizedModule.mkLinearMap U M) f).restrictScalars R)

/-- **[Stacks, Tag 05IG] with the fibre condition read over `S`.**  For a ring map `R → S` of
finite presentation and a finitely presented `S`-module `N` flat over `R`, a prime `q` of `S`
lying over `p` is weakly associated to `N ⊗[R] M` exactly when `p` is weakly associated to `M`
and `q` is weakly associated to `N ⊗[R] κ(p)`. -/
theorem isWeaklyAssociatedPrime_tensorProduct_iff_of_finitePresentation
    (h05IG : TensorFibreFormula05IG.{u})
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    {M : Type u} [AddCommGroup M] [Module R M]
    {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] [Module.Flat R N]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    IsWeaklyAssociatedPrime S (N ⊗[R] M) q ↔
      IsWeaklyAssociatedPrime R M p ∧
        IsWeaklyAssociatedPrime S (N ⊗[R] p.ResidueField) q := by
  have : IsNoetherianRing (S ⊗[R] p.ResidueField) := isNoetherianRing_tensorResidueField p
  rw [h05IG R S M N p q, isWeaklyAssociatedPrime_tensorResidueField_iff p q]

/-- **The equivalence of [Stacks, Tag 05IG] for a module that is merely finite.**  For a ring map
`R → A` of finite presentation, a finite `A`-module `P` and a prime `q` of `A` lying over `p` at
which `P` is flat over `R`, the prime `q` is weakly associated to `P ⊗[R] M` exactly when `p` is
weakly associated to `M` and `q` is weakly associated to `P ⊗[R] κ(p)`.

By [Stacks, Tag 05I7] the localization of `P` at `q` is finitely presented, so `P` agrees at `q`
with a finitely presented `A`-module which, the relative flat locus being open, is flat over `R`
on a basic open around `q`;  both sides of the equivalence depend only on the localization
at `q`. -/
theorem isWeaklyAssociatedPrime_tensorProduct_iff_of_finite
    (h05IG : TensorFibreFormula05IG.{u})
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
    flat_localizedModule_of_isLocalizedModule (R := R) q.primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl P) ∘ₗ φ)
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
  have hdisj : Disjoint (Submonoid.powers g : Set A) (q : Set A) := Set.disjoint_left.mpr <| by
    rintro a ⟨n, rfl⟩ ha
    exact hgq (‹q.IsPrime›.mem_of_pow_mem n ha)
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
    .trans _ q p
  rw [← htrans M, isWeaklyAssociatedPrime_tensorProduct_iff_of_finitePresentation h05IG p
      (q.map (algebraMap A (Localization.Away g))),
    htrans p.ResidueField]

/-- **The equivalence of [Stacks, Tag 05IG] over a finite type algebra.**  For a ring map `R → A`
of finite type, a finite `A`-module `P` and a prime `q` of `A` lying over `p` at which `P` is
flat over `R`, the prime `q` is weakly associated to `P ⊗[R] M` exactly when `p` is weakly
associated to `M` and `q` is weakly associated to `P ⊗[R] κ(p)`.

A finite type algebra is a quotient of a polynomial algebra, which is of finite presentation,
and neither side of the equivalence changes under a surjective change of the ring. -/
theorem isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteType
    (h05IG : TensorFibreFormula05IG.{u})
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
  set A₀ := MvPolynomial (Fin n) R
  let : Algebra A₀ A := π.toRingHom.toAlgebra
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
  have : q₀.LiesOver p := .tower_bot q q₀ p
  have hsub : Algebra.algebraMapSubmonoid A q₀.primeCompl = q.primeCompl :=
    algebraMapSubmonoid_primeCompl_comap hsurj q
  have hup : IsLocalizedModule (Algebra.algebraMapSubmonoid A q₀.primeCompl)
      (LocalizedModule.mkLinearMap q.primeCompl P) := by
    rw [hsub]
    infer_instance
  have hloc0 : IsLocalizedModule q₀.primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl P).restrictScalars A₀) :=
    IsLocalizedModule.restrictScalars (A := A) q₀.primeCompl _
  have hflat₀ : Module.Flat R (LocalizedModule q₀.primeCompl P) :=
    flat_localizedModule_of_isLocalizedModule (R := R) q₀.primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl P).restrictScalars A₀)
  rw [isWeaklyAssociatedPrime_comap_iff_of_surjective (A := A₀) (B := A) hsurj q,
    isWeaklyAssociatedPrime_comap_iff_of_surjective (A := A₀) (B := A) hsurj
      (L := P ⊗[R] p.ResidueField) q]
  exact isWeaklyAssociatedPrime_tensorProduct_iff_of_finite h05IG
    (A := A₀) (P := P) (M := M) p q₀ hflat₀

end Stacks.WeaklyAssociatedPrimes

end
