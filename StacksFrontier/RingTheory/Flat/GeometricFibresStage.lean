module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeSystem
public import StacksFrontier.RingTheory.GeometricallyIntegral.Defs

/-!
# Descent of geometrically integral fibres to a finite type stage

Let `A` be a ring and `B` an `A`-algebra of finite presentation. Stacks 00R1 writes the pair
`A → B` as the base change of a pair `R₀ → S₀` with `R₀` a subring of `A` of finite type over
`ℤ`, and `Algebra.FiniteTypeSystem` organizes the intermediate finite type `ℤ`-subalgebras
`R_λ ⊆ A` into a directed system with `S_λ = R_λ ⊗_{R₀} S₀` and `B = A ⊗_{R_λ} S_λ`. The
Noetherian approximation of Stacks 05FT needs a stage at which `R_λ → S_λ` still has
geometrically integral fibres. This file settles the ring-theoretic half of that question and
isolates the one geometric input it cannot supply.

The condition on the fibres is Mathlib's `AlgebraicGeometry.GeometricallyIntegral` applied to
`Spec B ⟶ Spec A`, which is the interface the existing dévissage code uses (see
`Algebra.closedFiberIdeal_isPrime`). Unfolded, it says that `B ⊗_A K` is a domain for every
field `K` carrying an `A`-algebra structure, since `AlgebraicGeometry.geometrically` quantifies
over field-valued points of the base. Splitting that quantifier over the prime
`ker (A → K)` gives the *geometrically integral fibre locus* in `Spec A`.

**Descent.** The condition descends along `R_λ → A` at every prime in the image of
`Spec A → Spec R_λ`, and therefore descends outright along a ring map which is surjective on
spectra. This is the content the `FiniteTypeSystem` idiom contributes, and it needs no
flatness, no finiteness and no filtered colimit argument: for a field `K` over `R_λ` whose
fibre `A ⊗_{R_λ} K` is nonzero, a residue field `L` of `A ⊗_{R_λ} K` is simultaneously an
`A`-algebra and an extension of `K`, so `B ⊗_A L = S_λ ⊗_{R_λ} L` is a domain by hypothesis and
`S_λ ⊗_{R_λ} K` embeds into it.

**What descent cannot do.** `Spec A → Spec R_λ` is never surjective in the interesting cases —
for `A = ℚ` and `R_λ` a finite type `ℤ`-subalgebra the source is a point and the target is
not — so the primes of `R_λ` outside the image are genuinely uncontrolled, and a stage must be
found at which they disappear. `Algebra.FiniteTypeSystem.exists_geometricallyIntegral_stage`
does that by the unit ideal argument of
`Algebra.FiniteTypeSystem.exists_faithfullyFlat_stage`, but the argument needs the bad locus to
be *closed*, which is assumed here as the openness of the geometrically integral fibre locus
over a Noetherian base. That is the geometric input the ring theory does not provide: it is
EGA IV 12.2.4, whose Stacks form is the constructibility of the geometrically reduced and
geometrically irreducible loci (tags 0579 and 055B) together with the limit lemma 05F4. Being
closed under specialization would not be enough — the set of closed points of `Spec ℤ` is
closed under specialization and dense — so no weakening of the hypothesis to a
specialization-closedness statement will do.

## Main definitions

* `Algebra.geometricallyIntegralFibreLocus`: the set of primes `p` of `A` at which the fibre of
  `C` is geometrically integral, i.e. `C ⊗_A K` is a domain for every field `K` over `A` with
  `ker (A → K) = p`.

## Main results

* `Algebra.geometricallyIntegral_iff_forall_isDomain_tensorProduct`: the fibrewise form of
  `AlgebraicGeometry.GeometricallyIntegral` for a ring map.
* `Algebra.geometricallyIntegral_iff_forall_mem_geometricallyIntegralFibreLocus`: the same,
  split over the primes of the base.
* `Algebra.nontrivial_tensorProduct_of_mem_rangeComap`: the fibre of `S` at a field-valued point
  `K` of `R` is nonzero as soon as `ker (R → K)` is in the image of `Spec S → Spec R`. This
  generalizes `PrimeSpectrum.nontrivial_iff_mem_rangeComap` from residue fields to arbitrary
  fields.
* `Algebra.isDomain_tensorProduct_of_nontrivial`: descent of a single geometrically integral
  fibre to a field-valued point of the base that lifts.
* `Algebra.mem_geometricallyIntegralFibreLocus_of_mem_rangeComap`,
  `Algebra.geometricallyIntegral_of_comap_surjective`: descent of the locus, and descent of
  geometric integrality along a map surjective on spectra.
* `Algebra.mem_geometricallyIntegralFibreLocus_of_isPushout`: the locus is compatible with base
  change.
* `Algebra.FiniteTypeSystem.exists_geometricallyIntegral_stage`: a geometrically integral stage
  of the system of Stacks 00R1, granted openness of the locus at one stage.

## Implementation notes

`Algebra.geometricallyIntegral_iff_forall_isDomain_tensorProduct` is
`Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct` of
`StacksFrontier.RingTheory.GeometricallyIntegral.Defs` with the field hypothesis on the base
dropped; its proof is the same, as that proof never uses it. It should be deleted here as soon
as the base of `Algebra.IsGeometricallyIntegral` is relaxed to a commutative ring.

No new predicate on algebras is introduced: the hypothesis and the conclusion of every result
below are stated with Mathlib's `AlgebraicGeometry.GeometricallyIntegral` in the `Spec.map`
shape, and `Algebra.geometricallyIntegralFibreLocus` is the subset of `Spec A` cut out by it
pointwise, which is what the unit ideal argument manipulates.

All the rings and the test fields lie in one universe, as they must: the condition passes
through `Spec`.

## References

* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 05FH](https://stacks.math.columbia.edu/tag/05FH)
* [Stacks Project, Tag 05FG](https://stacks.math.columbia.edu/tag/05FG)
* [Stacks Project, Tag 00R1](https://stacks.math.columbia.edu/tag/00R1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat
open scoped TensorProduct

universe u

namespace Algebra

/-- **The fibrewise form of geometric integrality for a ring map.** `Spec S ⟶ Spec R` is
geometrically integral exactly when `S ⊗[R] K` is a domain for every field `K` carrying an
`R`-algebra structure. -/
theorem geometricallyIntegral_iff_forall_isDomain_tensorProduct (R S : Type u) [CommRing R]
    [CommRing S] [Algebra R S] :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap R S))) ↔
      ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (S ⊗[R] K) := by
  rw [geometricallyIntegral_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  refine forall_congr' fun K => ?_
  refine ⟨fun h _ _ => ?_, fun h _ _ => ?_⟩
  · rw [← affine_isIntegral_iff (.of (S ⊗[R] K))]
    exact ObjectProperty.prop_of_iso _ (pullbackSpecIso R S K) (h ..)
  · exact ObjectProperty.prop_of_iso _ (pullbackSpecIso R S K).symm
      ((affine_isIntegral_iff (.of (S ⊗[R] K))).mpr h)

/-- The **geometrically integral fibre locus** of an `A`-algebra `C`: the set of primes `p` of
`A` such that `C ⊗[A] K` is a domain for every field `K` over `A` with `ker (A → K) = p`.

This is the pointwise form of the quantifier in `AlgebraicGeometry.geometrically`: the locus is
all of `Spec A` exactly when `Spec C ⟶ Spec A` is geometrically integral, which is
`Algebra.geometricallyIntegral_iff_forall_mem_geometricallyIntegralFibreLocus`. -/
def geometricallyIntegralFibreLocus (A C : Type u) [CommRing A] [CommRing C] [Algebra A C] :
    Set (PrimeSpectrum A) :=
  {p | ∀ (K : Type u) [Field K] [Algebra A K], RingHom.ker (algebraMap A K) = p.asIdeal →
    IsDomain (C ⊗[A] K)}

/-- `Spec C ⟶ Spec A` is geometrically integral exactly when every prime of `A` lies in the
geometrically integral fibre locus of `C`. -/
theorem geometricallyIntegral_iff_forall_mem_geometricallyIntegralFibreLocus (A C : Type u)
    [CommRing A] [CommRing C] [Algebra A C] :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap A C))) ↔
      ∀ p, p ∈ geometricallyIntegralFibreLocus A C := by
  rw [geometricallyIntegral_iff_forall_isDomain_tensorProduct]
  exact ⟨fun h p K _ _ _ => h K,
    fun h K _ _ => h ⟨RingHom.ker (algebraMap A K), RingHom.ker_isPrime _⟩ K rfl⟩

/-- A field `K` over `R` is a field extension of the residue field at `ker (R → K)`, and the
fibre of any `R`-algebra at the field-valued point `K` is the base change along that extension
of the fibre at the prime `ker (R → K)`. Consequently the fibre at `K` is nonzero as soon as
`ker (R → K)` lies in the image of `Spec S → Spec R`. -/
theorem nontrivial_tensorProduct_of_mem_rangeComap {R : Type u} [CommRing R] (S : Type u)
    [CommRing S] [Algebra R S] (K : Type u) [Field K] [Algebra R K]
    (h : (⟨RingHom.ker (algebraMap R K), RingHom.ker_isPrime _⟩ : PrimeSpectrum R) ∈
      Set.range (PrimeSpectrum.comap (algebraMap R S))) :
    Nontrivial (S ⊗[R] K) := by
  set p := RingHom.ker (algebraMap R K) with hpdef
  have hp : p.IsPrime := RingHom.ker_isPrime _
  let g : (R ⧸ p) →+* K := Ideal.Quotient.lift p (algebraMap R K) fun _ ha => ha
  have hg : Function.Injective g := by
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_quotient_lift, ← hpdef]
    exact Ideal.map_quotient_self _
  let _ : Algebra p.ResidueField K := (IsFractionRing.lift hg).toAlgebra
  have : IsScalarTower R p.ResidueField K := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap R K r = IsFractionRing.lift hg (algebraMap R p.ResidueField r)
    rw [← Ideal.algebraMap_quotient_residueField_mk, IsFractionRing.lift_algebraMap]
    exact (Ideal.Quotient.lift_mk _ _ _).symm
  have h1 : Nontrivial (p.ResidueField ⊗[R] S) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap (⟨p, hp⟩ : PrimeSpectrum R)).mpr h
  have h2 : Nontrivial (K ⊗[p.ResidueField] (p.ResidueField ⊗[R] S)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
      (R := p.ResidueField) (A := K) (B := p.ResidueField ⊗[R] S)
      (algebraMap p.ResidueField (p.ResidueField ⊗[R] S)).injective
  have h3 : Nontrivial (K ⊗[R] S) :=
    (Algebra.TensorProduct.cancelBaseChange R p.ResidueField p.ResidueField K
      S).injective.nontrivial
  exact (Algebra.TensorProduct.comm R K S).injective.nontrivial

/-- The fibres at a field-valued point of the two sides of a pushout square are both domains or
neither is. -/
private theorem isDomain_tensorProduct_iff_of_isPushout {R A S B : Type u} [CommRing R]
    [CommRing A] [CommRing S] [CommRing B] [Algebra R A] [Algebra R S] [Algebra A B]
    [Algebra S B] [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B]
    [Algebra.IsPushout R A S B] (K : Type u) [Field K] [Algebra R K] [Algebra A K]
    [IsScalarTower R A K] : IsDomain (S ⊗[R] K) ↔ IsDomain (B ⊗[A] K) := by
  have := Algebra.IsPushout.symm ‹Algebra.IsPushout R A S B›
  exact (Algebra.IsPushout.cancelBaseChangeAlg R S A B K).toMulEquiv.isDomain_iff.symm

section Descent

variable {A R S₀ S : Type u} [CommRing A] [CommRing R] [CommRing S₀] [CommRing S]
  [Algebra A R] [Algebra A S₀] [Algebra R S] [Algebra S₀ S] [Algebra A S]
  [IsScalarTower A R S] [IsScalarTower A S₀ S] [Algebra.IsPushout A R S₀ S]

/-- **Descent of a geometrically integral fibre at a field-valued point.** Let `S = R ⊗_A S₀`
and let `K` be a field over `A` whose fibre `R ⊗_A K` is nonzero, i.e. a field-valued point of
`Spec A` that lifts to `Spec R`. If every field-valued fibre of `R → S` is a domain, then so is
the fibre `S₀ ⊗_A K`.

A nonzero `R ⊗_A K` has a maximal ideal, and the quotient `L` by it is a field which is at once
an `R`-algebra and an extension of `K`. The fibre `S ⊗_R L` is then a domain by hypothesis, and
it is `S₀ ⊗_A L = L ⊗_K (K ⊗_A S₀)`, into which `K ⊗_A S₀` injects because `K → L` is an
injection of `K`-modules and `K ⊗_A S₀` is flat over the field `K`. -/
theorem isDomain_tensorProduct_of_nontrivial
    (hS : ∀ (L : Type u) [Field L] [Algebra R L], IsDomain (S ⊗[R] L))
    (K : Type u) [Field K] [Algebra A K] (hnt : Nontrivial (R ⊗[A] K)) :
    IsDomain (S₀ ⊗[A] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (R ⊗[A] K)
  let L := (R ⊗[A] K) ⧸ m
  let _ : Field L := Ideal.Quotient.field m
  let _ : Algebra K L :=
    ((Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeRight : K →ₐ[A] R ⊗[A] K).toRingHom).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap A L a = Ideal.Quotient.mk m
      (Algebra.TensorProduct.includeRight (algebraMap A K a))
    rw [AlgHom.commutes]
    rfl
  have h1 : IsDomain (S₀ ⊗[A] L) :=
    (isDomain_tensorProduct_iff_of_isPushout L).mpr (hS L)
  have h2 : IsDomain (L ⊗[A] S₀) := (Algebra.TensorProduct.comm A L S₀).injective.isDomain
  have h3 : IsDomain (L ⊗[K] (K ⊗[A] S₀)) :=
    (Algebra.TensorProduct.cancelBaseChange A K K L S₀).injective.isDomain
  have h4 : IsDomain (K ⊗[A] S₀) :=
    (Algebra.TensorProduct.includeRight_injective (R := K) (A := L) (B := K ⊗[A] S₀)
      (RingHom.injective _)).isDomain _
  exact (Algebra.TensorProduct.comm A S₀ K).injective.isDomain

/-- **Descent of the geometrically integral fibre locus at a point in the image.** Let
`S = R ⊗_A S₀`. If every field-valued fibre of `R → S` is a domain, then every prime of `A` in
the image of `Spec R → Spec A` lies in the geometrically integral fibre locus of `S₀`. -/
theorem mem_geometricallyIntegralFibreLocus_of_mem_rangeComap
    (hS : ∀ (L : Type u) [Field L] [Algebra R L], IsDomain (S ⊗[R] L)) (p : PrimeSpectrum A)
    (hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A R))) :
    p ∈ geometricallyIntegralFibreLocus A S₀ := by
  intro K _ _ hker
  refine isDomain_tensorProduct_of_nontrivial hS K
    (nontrivial_tensorProduct_of_mem_rangeComap (R := A) R K ?_)
  rwa [show (⟨RingHom.ker (algebraMap A K), RingHom.ker_isPrime _⟩ : PrimeSpectrum A) = p from
    PrimeSpectrum.ext hker]

/-- **Descent of geometric integrality along a map which is surjective on spectra.** Let
`S = R ⊗_A S₀` and assume every prime of `A` is the contraction of a prime of `R`. If
`Spec S ⟶ Spec R` is geometrically integral then so is `Spec S₀ ⟶ Spec A`. -/
theorem geometricallyIntegral_of_comap_surjective
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A R)))
    (h : GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))) :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap A S₀))) := by
  rw [geometricallyIntegral_iff_forall_isDomain_tensorProduct] at h
  rw [geometricallyIntegral_iff_forall_mem_geometricallyIntegralFibreLocus]
  exact fun p => mem_geometricallyIntegralFibreLocus_of_mem_rangeComap h p (hsurj p)

end Descent

/-- **The geometrically integral fibre locus is compatible with base change.** For
`C' = A' ⊗_A C`, a prime of `A'` whose contraction to `A` lies in the locus of `C` lies in the
locus of `C'`, because the two fibres at a field-valued point agree. -/
theorem mem_geometricallyIntegralFibreLocus_of_isPushout {A A' C C' : Type u} [CommRing A]
    [CommRing A'] [CommRing C] [CommRing C'] [Algebra A A'] [Algebra A C] [Algebra A' C']
    [Algebra C C'] [Algebra A C'] [IsScalarTower A A' C'] [IsScalarTower A C C']
    [Algebra.IsPushout A A' C C'] (q : PrimeSpectrum A')
    (hq : PrimeSpectrum.comap (algebraMap A A') q ∈ geometricallyIntegralFibreLocus A C) :
    q ∈ geometricallyIntegralFibreLocus A' C' := by
  intro K _ _ hker
  let _ : Algebra A K := ((algebraMap A' K).comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hker' : RingHom.ker (algebraMap A K) =
      (PrimeSpectrum.comap (algebraMap A A') q).asIdeal := by
    show RingHom.ker (algebraMap A K) = Ideal.comap (algebraMap A A') q.asIdeal
    rw [← hker, RingHom.comap_ker]
    rfl
  exact (isDomain_tensorProduct_iff_of_isPushout K).mp (hq K hker')

namespace FiniteTypeSystem

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (R₀ : Subring A) (S₀ : Type u) [CommRing S₀] [Algebra R₀ S₀] [Algebra S₀ B]
  [IsScalarTower R₀ S₀ B] [Algebra.FiniteType ℤ R₀] [Algebra.FiniteType R₀ S₀]
  [Algebra.IsPushout R₀ A S₀ B]

omit [Algebra.FiniteType R₀ S₀] in
/-- **A geometrically integral stage of the system, granted openness of the locus.** Suppose
`Spec B ⟶ Spec A` is geometrically integral and that at the stage `λ` the geometrically integral
fibre locus of `S_λ` over `R_λ` is open. Then `Spec S_μ ⟶ Spec R_μ` is geometrically integral
for some `μ ≥ λ`.

The locus `U ⊆ Spec R_λ` contains the image of `Spec A` by
`Algebra.mem_geometricallyIntegralFibreLocus_of_mem_rangeComap`. Its complement is the zero
locus of an ideal `I` whose extension to `A` is therefore the unit ideal; a relation
`∑ cₘ xₘ = 1` with `xₘ ∈ I` and `cₘ ∈ A` already lives in some `R_μ`, so `I R_μ` is the unit
ideal and every prime of `R_μ` contracts into `U`. The fibres of `R_μ → S_μ` are the base
changes of those of `R_λ → S_λ`, so they are geometrically integral by
`Algebra.mem_geometricallyIntegralFibreLocus_of_isPushout`. -/
theorem exists_geometricallyIntegral_stage (i : Index R₀)
    (hopen : IsOpen (geometricallyIntegralFibreLocus (Base R₀ i) (Ring R₀ S₀ i)))
    (h : GeometricallyIntegral (Spec.map (ofHom (algebraMap A B)))) :
    ∃ j, i ≤ j ∧
      GeometricallyIntegral (Spec.map (ofHom (algebraMap (Base R₀ j) (Ring R₀ S₀ j)))) := by
  classical
  have : Algebra.IsPushout (Base R₀ i) A (Ring R₀ S₀ i) B := ringToRing_isPushout R₀ S₀ i
  have hS := (geometricallyIntegral_iff_forall_isDomain_tensorProduct A B).mp h
  set U := geometricallyIntegralFibreLocus (Base R₀ i) (Ring R₀ S₀ i)
  let I := PrimeSpectrum.vanishingIdeal Uᶜ
  have hZ : PrimeSpectrum.zeroLocus I = Uᶜ := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hopen.isClosed_compl.closure_eq]
  have hI : I.map (algebraMap (Base R₀ i) A) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1 : PrimeSpectrum.comap (algebraMap (Base R₀ i) A) ⟨m, hm.isPrime⟩ ∈
        PrimeSpectrum.zeroLocus I := Ideal.map_le_iff_le_comap.mp hle
    rw [hZ] at h1
    exact h1 (mem_geometricallyIntegralFibreLocus_of_mem_rangeComap hS _ ⟨⟨m, hm.isPrime⟩, rfl⟩)
  obtain ⟨n, c, x, hx⟩ := Submodule.mem_span_set'.mp (hI ▸ Submodule.mem_top (x := (1 : A)))
  choose x' hx'I hx' using fun k => (x k).2
  choose k d hd using fun m => base_jointly_surjective R₀ (c m)
  obtain ⟨j, hj⟩ := (insert i (Finset.univ.image k)).exists_le
  have hij : i ≤ j := hj i (Finset.mem_insert_self _ _)
  have hkj (m : Fin n) : k m ≤ j :=
    hj _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ m)))
  have : Fact (i ≤ j) := ⟨hij⟩
  have hIj : I.map (algebraMap (Base R₀ i) (Base R₀ j)) = ⊤ := by
    refine (Ideal.eq_top_iff_one _).mpr ?_
    have hsum :
        ∑ m, baseMap R₀ (hkj m) (d m) * algebraMap (Base R₀ i) (Base R₀ j) (x' m) = 1 := by
      apply algebraMap_base_injective R₀ j
      rw [map_one, ← hx, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, smul_eq_mul, ← hx', ← hd m]
      rfl
    rw [← hsum]
    exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hx'I m))
  refine ⟨j, hij, ?_⟩
  have : Algebra.IsPushout (Base R₀ i) (Base R₀ j) (Ring R₀ S₀ i) (Ring R₀ S₀ j) :=
    ringMap_isPushout R₀ S₀
  rw [geometricallyIntegral_iff_forall_mem_geometricallyIntegralFibreLocus]
  intro q
  refine mem_geometricallyIntegralFibreLocus_of_isPushout (A := Base R₀ i)
    (C := Ring R₀ S₀ i) q ?_
  by_contra hp
  rw [← Set.mem_compl_iff, ← hZ] at hp
  exact q.2.ne_top (top_le_iff.mp (hIj.symm.trans_le (Ideal.map_le_iff_le_comap.mpr hp)))

end FiniteTypeSystem

end Algebra

end
