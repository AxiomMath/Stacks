module

public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.FlatFibreAtPrime
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreEssentiallyFiniteType

/-!
# The fibre clause of one inclusion of the fibrewise description of the weakly associated primes
of a flat tensor product

Let `R → S` be a ring map essentially of finite type, let `N` be a localization of a finite
`S`-module which is flat over `R`, and let `M` be an `R`-module. [Stacks, Tag 05II] asserts

`WeakAss_S(N ⊗_R M) = ⋃_{𝔭 ∈ WeakAss_R(M)} Ass_{S ⊗_R κ(𝔭)}(N ⊗_R κ(𝔭))`,

the right-hand sets being read inside `Spec(S)` by contraction. The equality is
`weaklyAssociatedPrimes_tensorProduct_eq_fibrewise_assStacks_of_small`, in
`StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreEssentiallyFiniteType`. This file
proves the *fibre* clause of the inclusion `⊆` without assuming [Stacks, Tag 05IG]: that a prime
`q` of `S` weakly associated to `N ⊗_R M` is weakly associated to `N ⊗_R κ(𝔭)`, `𝔭` being its
contraction to `R`. That clause asks for no finiteness of `𝔭` at all, and the work of this file
is to carry it from the finite presentation case to the essentially finite type case. Everything
below lives in the namespace `Stacks.WeaklyAssociatedPrimes`, and the names in this
documentation are relative to it.

That carrying is the forward half of the two reductions of
`StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreFiniteType` and
`StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreEssentiallyFiniteType`, which are
run there on the full equivalence and therefore only under the hypothesis
`TensorFibreFormula05IG`. Every comparison those reductions use is an equivalence proved
outright, so the forward implication alone travels along them; what is reproved here is the
choice of models the comparisons are taken against.

## Main results

* `isWeaklyAssociatedPrime_tensorResidueField_of_isWeaklyAssociatedPrime_tensorProduct`
  is the fibre clause of [Stacks, Tag 05IG] read over `S`: the library's clause states association
  over the fibre ring written as `S_𝔭 / 𝔭 S_𝔭`, and this is the same statement about weak
  association of `q` to `N ⊗_R κ(𝔭)`.
* `isWeaklyAssociatedPrime_tensorResidueField_of_finite`,
  `..._of_finiteType`, `..._of_finiteTypeModel` and `..._of_essentiallyOfFiniteType` carry that
  clause through the reductions, in the same order as the existing equivalences do.

## Implementation notes

The identification of the two spellings of the fibre ring is
`tensorResidueFieldAlgEquivFibre`, which composes Mathlib's
`Algebra.TensorProduct.commRight` with `fibreAlgEquiv`;
the `S`-algebra structure on `𝔭.Fiber S = κ(𝔭) ⊗_R S` is `Algebra.TensorProduct.rightAlgebra`,
activated as a local instance as in the file the original clause comes from. Only an `S`-linear
comparison of the fibre *modules* is needed, which is why the module structures over the fibre
ring itself never have to be reconciled.

The contraction of the fibre clause from the fibre ring to `S` is
`isWeaklyAssociatedPrime_comap_of_fractions`: every element of `S_𝔭 / 𝔭 S_𝔭` is a fraction
with numerator and denominator in `S`, which is `exists_fraction_quotient_localization` below.
Association in the strict sense of [Stacks, Tag 00LA] is turned into weak association before
contracting, the fibre ring being Noetherian.

## References

* [Stacks Project, Tag 05II](https://stacks.math.columbia.edu/tag/05II)
* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 05I7](https://stacks.math.columbia.edu/tag/05I7)
* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
-/

@[expose] public section

open TensorProduct

universe u v w t

namespace Stacks.WeaklyAssociatedPrimes

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Bridge

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
  {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
  {M : Type u} [AddCommGroup M] [Module R M]

variable (p : Ideal R) [p.IsPrime]

/-- The fibre ring `S_𝔭 / 𝔭 S_𝔭` is `S ⊗_R κ(𝔭)` as an `S`-algebra. -/
noncomputable def tensorResidueFieldAlgEquivFibre :
    (S ⊗[R] p.ResidueField) ≃ₐ[S]
      (Localization (primeComplImage S p) ⧸ fibreIdeal S p) :=
  (Algebra.TensorProduct.commRight R S p.ResidueField).trans (fibreAlgEquiv p)

variable (N) in
/-- The fibre module `(S_𝔭 / 𝔭 S_𝔭) ⊗_S N` is `N ⊗_R κ(𝔭)` as an `S`-module. -/
noncomputable def fibreTensorLinearEquiv :
    ((Localization (primeComplImage S p) ⧸ fibreIdeal S p) ⊗[S] N) ≃ₗ[S]
      N ⊗[R] p.ResidueField :=
  (TensorProduct.congr (tensorResidueFieldAlgEquivFibre p).symm.toLinearEquiv
      (LinearEquiv.refl S N)).trans
    ((TensorProduct.comm S _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N p.ResidueField))

/-- Every element of the fibre ring `S_𝔭 / 𝔭 S_𝔭` is a fraction with numerator and denominator
coming from `S`. -/
theorem exists_fraction_quotient_localization
    (b : Localization (primeComplImage S p) ⧸ fibreIdeal S p) :
    ∃ a d : S, IsUnit (algebraMap S (Localization (primeComplImage S p) ⧸ fibreIdeal S p) d) ∧
      algebraMap S (Localization (primeComplImage S p) ⧸ fibreIdeal S p) d * b =
        algebraMap S (Localization (primeComplImage S p) ⧸ fibreIdeal S p) a := by
  have halg := (Ideal.Quotient.mk_comp_algebraMap (R₁ := S) (fibreIdeal S p)).symm
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨⟨a, d⟩, rfl⟩ := IsLocalization.mk'_surjective (primeComplImage S p) y
  refine ⟨a, (d : S), ?_, ?_⟩
  · rw [halg]
    exact (IsLocalization.map_units (Localization (primeComplImage S p)) d).map
      (Ideal.Quotient.mk (fibreIdeal S p))
  · rw [halg]
    simp only [RingHom.coe_comp, Function.comp_apply, ← map_mul]
    rw [mul_comm, IsLocalization.mk'_spec]

/-- The extension of a prime of `S` lying over `𝔭` to the fibre ring `S_𝔭 / 𝔭 S_𝔭` contracts
back to it. -/
theorem comap_map_algebraMap_quotient_localization (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    (Ideal.map (algebraMap S (Localization (primeComplImage S p) ⧸ fibreIdeal S p)) q).comap
        (algebraMap S (Localization (primeComplImage S p) ⧸ fibreIdeal S p)) = q := by
  have hdisj : Disjoint ((primeComplImage S p : Submonoid S) : Set S) (q : Set S) :=
    Ideal.disjoint_primeCompl_of_liesOver q p
  have halg := (Ideal.Quotient.mk_comp_algebraMap (R₁ := S) (fibreIdeal S p)).symm
  have hker : Ideal.map (algebraMap S (Localization (primeComplImage S p))) q ⊔
      Ideal.comap (Ideal.Quotient.mk (fibreIdeal S p)) (⊥ : Ideal _) =
        Ideal.map (algebraMap S (Localization (primeComplImage S p))) q := by
    rw [show Ideal.comap (Ideal.Quotient.mk (fibreIdeal S p)) (⊥ : Ideal _) = fibreIdeal S p from
      Ideal.mk_ker]
    exact sup_eq_left.mpr (fibreIdeal_le_map p q)
  rw [← map_mk_map_algebraMap p q, halg, ← Ideal.comap_comap,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, hker]
  have h := IsLocalization.under_map_of_isPrime_disjoint (primeComplImage S p)
    (Localization (primeComplImage S p)) (show q.IsPrime from inferInstance) hdisj
  rwa [Ideal.under_def] at h

/-- **The fibre clause of [Stacks, Tag 05IG], read over `S`.** For a ring map `R → S` of finite
presentation and an `S`-module `N` of finite presentation which is flat over `R`, a prime `q` of
`S` lying over `𝔭` and weakly associated to `N ⊗_R M` is weakly associated to `N ⊗_R κ(𝔭)`.

This is
`isAssociatedPrimeStacks_fibre_of_isWeaklyAssociatedPrime_tensorProduct`, whose conclusion lives
over the fibre ring `S_𝔭 / 𝔭 S_𝔭`, transported to `S`: the fibre ring is Noetherian, so
association there is weak association, which contracts to `S` because every element of the
fibre ring is a fraction over `S`; and the fibre module is `N ⊗_R κ(𝔭)` as an `S`-module. No
finiteness hypothesis on `𝔭` enters. -/
theorem isWeaklyAssociatedPrime_tensorResidueField_of_isWeaklyAssociatedPrime_tensorProduct
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S N] [Module.Flat R N]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q) :
    IsWeaklyAssociatedPrime S (N ⊗[R] p.ResidueField) q := by
  have : Algebra.FinitePresentation p.ResidueField (p.Fiber S) :=
    Algebra.FinitePresentation.baseChange _
  have : IsNoetherianRing (p.Fiber S) :=
    Algebra.FiniteType.isNoetherianRing p.ResidueField (p.Fiber S)
  have hnoeth : IsNoetherianRing (Localization (primeComplImage S p) ⧸ fibreIdeal S p) :=
    isNoetherianRing_of_ringEquiv _ (fibreAlgEquiv p).toRingEquiv
  have h2 : IsWeaklyAssociatedPrime (Localization (primeComplImage S p) ⧸ fibreIdeal S p)
      ((Localization (primeComplImage S p) ⧸ fibreIdeal S p) ⊗[S] N)
      (Ideal.map (algebraMap S (Localization (primeComplImage S p) ⧸ fibreIdeal S p)) q) :=
    (isWeaklyAssociatedPrime_iff_isAssociatedPrimeStacks _).mpr
      (isAssociatedPrimeStacks_fibre_of_isWeaklyAssociatedPrime_tensorProduct (M := M) p q hq)
  have h3 := isWeaklyAssociatedPrime_comap_of_fractions
    (A := S) (B := Localization (primeComplImage S p) ⧸ fibreIdeal S p)
    (L := (Localization (primeComplImage S p) ⧸ fibreIdeal S p) ⊗[S] N)
    (exists_fraction_quotient_localization p) h2
  rw [comap_map_algebraMap_quotient_localization p q] at h3
  exact isWeaklyAssociatedPrime_of_linearEquiv' (fibreTensorLinearEquiv N p) h3

end Bridge

/-! ### The closed fibre over a local base -/

section ClosedFibre

variable {R B : Type u} [CommRing R] [CommRing B] [IsLocalRing R] [Algebra R B]
  (N : Type u) [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]

/-- **The closed fibre module is a base change.** Over a local base `R` the module
`N ⊗_R κ(𝔪_R)` is the closed fibre `N / 𝔪_R N`, as a `B`-module: the residue field of a local
ring is the quotient by its maximal ideal, the fibre ring `B ⊗_R R/𝔪_R` is `B / 𝔪_R B`, and
tensoring `N` over `B` with that quotient divides out `𝔪_R N`. -/
noncomputable def closedFibreTensorResidueFieldLinearEquiv :
    (N ⊗[R] (IsLocalRing.maximalIdeal R).ResidueField) ≃ₗ[B]
      (N ⧸ (Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) •
        (⊤ : Submodule B N))) :=
  letI : (IsLocalRing.maximalIdeal R).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  letI eB : (B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) ≃ₐ[B]
      (B ⊗[R] (IsLocalRing.maximalIdeal R).ResidueField) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (IsLocalRing.maximalIdeal R)).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B)
        (AlgEquiv.ofBijective
          (IsScalarTower.toAlgHom R (R ⧸ IsLocalRing.maximalIdeal R)
            (IsLocalRing.maximalIdeal R).ResidueField)
          (IsLocalRing.maximalIdeal R).bijective_algebraMap_quotient_residueField))
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B N
      (IsLocalRing.maximalIdeal R).ResidueField).symm ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl B N) eB.symm.toLinearEquiv ≪≫ₗ
      TensorProduct.comm B N _ ≪≫ₗ
        TensorProduct.quotTensorEquivQuotSMul N
          (Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R))

end ClosedFibre

/-! ### The fibre clause carried through the reductions of [Stacks, Tag 05II] -/

/-- Flatness over `R` of a localized module follows from that of any module it is a localization
of. -/
private theorem flat_localizedModule_of_isLocalizedModule {R A P Q : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower R A P]
    [AddCommGroup Q] [Module A Q] [Module R Q] [IsScalarTower R A Q] (U : Submonoid A)
    (f : P →ₗ[A] Q) [IsLocalizedModule U f] [Module.Flat R Q] :
    Module.Flat R (LocalizedModule U P) :=
  Module.Flat.of_linearEquiv
    ((IsLocalizedModule.linearEquiv U (LocalizedModule.mkLinearMap U P) f).restrictScalars R)

/-- **The fibre clause for a module that is merely finite.** For a ring map `R → A` of finite
presentation, a finite `A`-module `P` and a prime `q` of `A` lying over `𝔭` at which `P` is flat
over `R`, a prime `q` weakly associated to `P ⊗_R M` is weakly associated to `P ⊗_R κ(𝔭)`.

This is the reduction of
`Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_tensorProduct_iff_of_finite` run on the
fibre clause alone: by [Stacks, Tag 05I7] the localization of `P` at `q` is finitely presented,
a finitely presented `A`-module `P'` with the same localization exists, and its relative flat
locus being open it is flat over `R` on a basic open `D(g)` around `q`; both the hypothesis and
the conclusion depend only on the localization of `P` at `q`. -/
theorem isWeaklyAssociatedPrime_tensorResidueField_of_finite
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    {P : Type u} [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower R A P]
    [Module.Finite A P]
    {M : Type u} [AddCommGroup M] [Module R M]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p]
    (hflat : Module.Flat R (LocalizedModule q.primeCompl P))
    (hq : IsWeaklyAssociatedPrime A (P ⊗[R] M) q) :
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
    flat_localizedModule_of_isLocalizedModule q.primeCompl
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
  have hdisj : Disjoint (Submonoid.powers g : Set A) (q : Set A) := by
    refine Set.disjoint_left.mpr ?_
    rintro a ⟨n, rfl⟩ ha
    exact hgq ((‹q.IsPrime›).mem_of_pow_mem n ha)
  have hqgp : (q.map (algebraMap A (Localization.Away g))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) _ q inferInstance hdisj
  have hqgc : (q.map (algebraMap A (Localization.Away g))).comap
      (algebraMap A (Localization.Away g)) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) _ inferInstance hdisj
  -- both sides only depend on the localization of `P` at `q`
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
  have hpg : (q.map (algebraMap A (Localization.Away g))).LiesOver p := .trans _ q _
  exact (htrans p.ResidueField).mp
    (isWeaklyAssociatedPrime_tensorResidueField_of_isWeaklyAssociatedPrime_tensorProduct
      (M := M) p (q.map (algebraMap A (Localization.Away g))) ((htrans M).mpr hq))

/-- **The fibre clause over a finite type algebra.** For a ring map `R → A` of finite type, a
finite `A`-module `P` and a prime `q` of `A` lying over `𝔭` at which `P` is flat over `R`, a
prime `q` weakly associated to `P ⊗_R M` is weakly associated to `P ⊗_R κ(𝔭)`.

A finite type algebra is a quotient of a polynomial algebra, which is of finite presentation,
and neither the hypothesis nor the conclusion changes under a surjective change of the ring. -/
theorem isWeaklyAssociatedPrime_tensorResidueField_of_finiteType
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    {P : Type u} [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower R A P]
    [Module.Finite A P]
    {M : Type u} [AddCommGroup M] [Module R M]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p]
    (hflat : Module.Flat R (LocalizedModule q.primeCompl P))
    (hq : IsWeaklyAssociatedPrime A (P ⊗[R] M) q) :
    IsWeaklyAssociatedPrime A (P ⊗[R] p.ResidueField) q := by
  classical
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType R A›
  set A₀ := MvPolynomial (Fin n) R with hA₀
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
  have : q₀.LiesOver p := Ideal.LiesOver.of_eq_comap p π hq₀
  have hsub : Algebra.algebraMapSubmonoid A q₀.primeCompl = q.primeCompl :=
    algebraMapSubmonoid_primeCompl_comap hsurj q
  have hup : IsLocalizedModule (Algebra.algebraMapSubmonoid A q₀.primeCompl)
      (LocalizedModule.mkLinearMap q.primeCompl P) := by
    rw [hsub]; infer_instance
  have hloc0 : IsLocalizedModule q₀.primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl P).restrictScalars A₀) :=
    IsLocalizedModule.restrictScalars (A := A) q₀.primeCompl _
  have hflat₀ : Module.Flat R (LocalizedModule q₀.primeCompl P) :=
    flat_localizedModule_of_isLocalizedModule q₀.primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl P).restrictScalars A₀)
  exact (isWeaklyAssociatedPrime_comap_iff_of_surjective (A := A₀) (B := A) hsurj
      (L := P ⊗[R] p.ResidueField) q).mpr
    (isWeaklyAssociatedPrime_tensorResidueField_of_finite (A := A₀) (P := P) (M := M) p q₀ hflat₀
      ((isWeaklyAssociatedPrime_comap_iff_of_surjective (A := A₀) (B := A) hsurj q).mp hq))

/-- **The fibre clause through a finite type model.** For `N` a localization of a finite module
over a localization `S` of a finite type `R`-algebra `A`, with `N` flat over `R`, a prime `q` of
`S` disjoint from the localizing submonoid and weakly associated to `N ⊗_R M` is weakly
associated to `N ⊗_R κ(𝔭)`, where `𝔭` is the contraction of `q` to `R`.

Both the hypothesis and the conclusion are unchanged by passing to the model, by
`Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteTypeModel`,
and flatness of the localization of the model is
`Stacks.WeaklyAssociatedPrimes.flat_localizedModule_of_finiteTypeModel`. -/
theorem isWeaklyAssociatedPrime_tensorResidueField_of_finiteTypeModel
    (R A S : Type u) [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    [Algebra.FiniteType R A]
    (P M : Type u) (N₀ : Type w) (N : Type t)
    [AddCommGroup P] [Module A P] [Module R P]
    [IsScalarTower R A P] [Module.Finite A P]
    [AddCommGroup N₀] [Module S N₀] [Module A N₀] [Module R N₀]
    [IsScalarTower A S N₀] [IsScalarTower R A N₀] [IsScalarTower R S N₀]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Flat R N]
    [AddCommGroup M] [Module R M]
    (U : Submonoid A) [IsLocalization U S]
    (φ : P →ₗ[A] N₀) [IsLocalizedModule U φ]
    (V : Submonoid S) (f : N₀ →ₗ[S] N) [IsLocalizedModule V f]
    (q : Ideal S) [q.IsPrime] (hV : V ≤ q.primeCompl)
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q) :
    IsWeaklyAssociatedPrime S (N ⊗[R] (q.comap (algebraMap R S)).ResidueField) q := by
  let qA : Ideal A := q.comap (algebraMap A S)
  let : qA.IsPrime := Ideal.IsPrime.comap _
  let p : Ideal R := q.comap (algebraMap R S)
  let : p.IsPrime := Ideal.IsPrime.comap _
  have hdisj : Disjoint (V : Set S) (q : Set S) :=
    Set.disjoint_left.mpr fun s hs hq => hV hs hq
  have hflatA := flat_localizedModule_of_finiteTypeModel (R := R) (T := A) (S := S) U φ V f q hV
  have : q.LiesOver p := ⟨rfl⟩
  have : q.LiesOver qA := ⟨rfl⟩
  have : qA.LiesOver p := .tower_bot q qA p
  have hM := isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteTypeModel
    (R := R) (A := A) (S := S) (P := P) (N₀ := N₀) (N := N) (M := M)
    U φ V f q hdisj
  have hK := isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteTypeModel
    (R := R) (A := A) (S := S) (P := P) (N₀ := N₀) (N := N)
    (M := p.ResidueField) U φ V f q hdisj
  exact hK.mpr (isWeaklyAssociatedPrime_tensorResidueField_of_finiteType
    (A := A) (P := P) (M := M) p qA hflatA (hM.mp hq))

/-- **The fibre clause for an essentially finite type ring map.** For `R → S` essentially of
finite type and `N` a localization of a finite `S`-module which is flat over `R`, a prime `q` of
`S` disjoint from the localizing submonoid and weakly associated to `N ⊗_R M` is weakly
associated to `N ⊗_R κ(𝔭)`, where `𝔭` is the contraction of `q` to `R`.

This is the fibre clause of
`isWeaklyAssociatedPrime_tensorProduct_iff_fibre_of_essentiallyOfFiniteType`, in this namespace,
with the hypothesis `TensorFibreFormula05IG` removed: only the forward implication is asserted,
and the forward implication of its fibre clause is the one already proved. -/
theorem isWeaklyAssociatedPrime_tensorResidueField_of_essentiallyOfFiniteType
    (R S : Type u) (M : Type u) (N₀ : Type w) (N : Type t)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N₀] [Module S N₀] [Module.Finite S N₀]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Flat R N]
    (hfinite : IsEssentiallyOfFiniteType R S (algebraMap R S))
    (V : Submonoid S) (f : N₀ →ₗ[S] N) [IsLocalizedModule V f]
    (q : Ideal S) [q.IsPrime]
    (hdisj : Disjoint (V : Set S) (q : Set S))
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q) :
    IsWeaklyAssociatedPrime S (N ⊗[R] (q.comap (algebraMap R S)).ResidueField) q := by
  classical
  obtain ⟨A, hA, aRA, hFT, U, aAS, hTower, hLoc,
    P, hPAdd, hPA, hPfin, φ, hφ⟩ := exists_finite_type_model hfinite N₀
  let : CommRing A := hA
  let : Algebra R A := aRA
  let : Algebra.FiniteType R A := hFT
  let : Algebra A S := aAS
  have hcomp : (algebraMap A S).comp (algebraMap R A) = algebraMap R S := by
    ext r
    let : Algebra R S := (algebraMap R S).toAlgebra
    let : IsScalarTower R A S := hTower
    exact (IsScalarTower.algebraMap_apply R A S r).symm
  let : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq' hcomp.symm
  let : IsLocalization U S := hLoc
  let : AddCommGroup P := hPAdd
  let : Module A P := hPA
  let : Module.Finite A P := hPfin
  let : Module R P := Module.compHom P (algebraMap R A)
  let : IsScalarTower R A P := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module A N₀ := Module.compHom N₀ (algebraMap A S)
  let : IsScalarTower A S N₀ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module R N₀ := Module.compHom N₀ (algebraMap R A)
  let : IsScalarTower R A N₀ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R S N₀ := IsScalarTower.of_algebraMap_smul fun r m => by
    change algebraMap R S r • m = algebraMap A S (algebraMap R A r) • m
    rw [← hcomp]
    rfl
  let : IsLocalizedModule U φ := hφ
  have hV : V ≤ q.primeCompl := fun s hs => Set.disjoint_left.mp hdisj hs
  exact isWeaklyAssociatedPrime_tensorResidueField_of_finiteTypeModel
    R A S P M N₀ N U φ V f q hV hq

/-- **The fibre clause for a finite module.** For `R → S` essentially of finite type and `N` a
finite `S`-module which is flat over `R`, a prime `q` of `S` weakly associated to `N ⊗_R M` is
weakly associated to `N ⊗_R κ(𝔭)`, where `𝔭` is the contraction of `q` to `R`.

This is the previous statement for the trivial localization: a finite module is a localization
of itself at the trivial submonoid, from which every prime is disjoint. -/
theorem isWeaklyAssociatedPrime_tensorResidueField_of_finiteModule
    (R S M N : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N] [Module.Flat R N]
    (hfinite : IsEssentiallyOfFiniteType R S (algebraMap R S))
    (q : Ideal S) [q.IsPrime]
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q) :
    IsWeaklyAssociatedPrime S (N ⊗[R] (q.comap (algebraMap R S)).ResidueField) q := by
  have hunits : (⊥ : Submonoid S) ≤ IsUnit.submonoid S := fun s hs => by
    rw [Submonoid.mem_bot] at hs
    subst hs
    exact isUnit_one
  have : IsLocalization (⊥ : Submonoid S) S := IsLocalization.self hunits
  have : IsLocalizedModule (⊥ : Submonoid S) (LinearMap.id : N →ₗ[S] N) :=
    isLocalizedModule_id (⊥ : Submonoid S) N S
  have hdisj : Disjoint ((⊥ : Submonoid S) : Set S) (q : Set S) :=
    Set.disjoint_left.mpr fun s hs hsq => by
      rw [SetLike.mem_coe, Submonoid.mem_bot] at hs
      subst hs
      exact (show q.IsPrime from inferInstance).ne_top ((Ideal.eq_top_iff_one q).mpr hsq)
  exact isWeaklyAssociatedPrime_tensorResidueField_of_essentiallyOfFiniteType
    R S M N N hfinite (⊥ : Submonoid S) LinearMap.id q hdisj hq

end Stacks.WeaklyAssociatedPrimes

end
