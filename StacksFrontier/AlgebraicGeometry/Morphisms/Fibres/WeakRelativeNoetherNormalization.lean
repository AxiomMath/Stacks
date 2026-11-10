module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.FibreDimensionBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.EventualFibreDimension
public import StacksFrontier.RingTheory.NoetherNormalization
public import StacksFrontier.RingTheory.NoetherNormalization.Basic
public import StacksFrontier.RingTheory.QuasiFinite.AffineSpaceDimension
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.RelativeDimension.QuasiFinite
public import StacksFrontier.RingTheory.RelativeDimension.Semicontinuity
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness

/-!
# Weak relative Noether normalization

Let `R → S` be a finite type ring map and let `d` be the maximum of the dimensions of the fibres
of `Spec S → Spec R`, that is, the relative dimension `dim(S/R)` of Tag 00QD. Then there is a
quasi-finite `R`-algebra map `R[t_1, …, t_d] → S`.

## Main definitions

No new definitions are introduced.

## Main results

* `Algebra.exists_quasiFinite_mvPolynomial_of_relativeDimension_le` is the lemma, with the
  maximum of the fibre dimensions written as `Algebra.relativeDimension` and bounded by `d`.
* `Algebra.exists_quasiFinite_mvPolynomial_of_relativeDimension_eq` is the same statement with
  `d` taken to be that maximum, as in the source.
* `AlgebraicGeometry.exists_quasiFinite_mvPolynomial_of_forall_topologicalKrullDim_fiber_le` is
  the form whose hypothesis is a bound on the dimension of every scheme-theoretic fibre of
  `Spec S ⟶ Spec R`.
* `Algebra.relativeDimension_le_iff_exists_quasiFinite_mvPolynomial` records that the existence
  of such a map is *equivalent* to the bound, so the conclusion is not satisfiable for free.

## Implementation notes

The maximum of the dimensions of the fibres is `Algebra.relativeDimension R S`, the supremum of
the local relative dimensions over all primes of `S` (Tag 00QD); it takes values in
`WithBot ℕ∞`, so the two degenerate readings of a maximum are available in it. The lemma is
stated with the hypothesis `Algebra.relativeDimension R S ≤ (d : WithBot ℕ∞)` for a natural
number `d` rather than with an equality. The two are equivalent — a quasi-finite
`R[t_1, …, t_e] → S` with `e ≤ d` extends to a quasi-finite `R[t_1, …, t_d] → S` by sending the
extra variables to zero, the map `R[t_1, …, t_d] → R[t_1, …, t_e]` being surjective — and the
inequality is the form that covers the empty spectrum: when `S` is the zero ring the supremum is
`⊥`, the source's maximum is a maximum over an empty family, and every `d` is admissible. If
instead the family of fibre dimensions were unbounded the supremum would be `⊤` and no natural
number `d` would satisfy the hypothesis, matching the source, where no such `d` exists either;
for a finite type ring map this does not happen. The equality form of the source is recorded
separately as `Algebra.exists_quasiFinite_mvPolynomial_of_relativeDimension_eq`.

Quasi-finiteness of the resulting map is Mathlib's `RingHom.QuasiFinite`. That predicate asks
only that the fibres be finite, so the finite type of the resulting map, which the source's
notion of a quasi-finite ring map includes, is recorded as a separate conjunct of the
conclusion. The map is produced as an `R`-algebra map `MvPolynomial (Fin d) R →ₐ[R] S`, which is
the only compatibility the source asserts: the source's map `R[t_1, …, t_d] → S` is a map of
`R`-algebras and nothing further is claimed of it.

The argument is the source's. Steps (1) and (2), the reduction to a ring map between algebras of
finite type over `ℤ`, are carried out together: `S` is generated over `R` by a finite set `s`,
and the subalgebra of `S` generated over `ℤ` by `s` together with the image of a finite set of
elements of `R` is of finite type over the corresponding finitely generated subring of `R`.
`Spec` of this directed system of subrings has `Spec R` as its limit, so Tag 05M5 provides a
stage at which the fibre dimension bound already holds, which is step (1) and step (2)
simultaneously; `S` is recovered from the stage by Tag 00PP, quasi-finiteness being stable under
base change, together with surjectivity of `R[s] → S`. Step (3) is an induction on `d`, where
the inductive step needs an element `a` of `S` for which the map `R[x] → S`, `x ↦ a`, has fibres
of dimension at most `d - 1`; step (4) produces that element by induction on the dimension of
the Noetherian base, using Tag 0GTE for the simultaneous transcendence over the finitely many
minimal primes of relative dimension `d`, Tag 00P1 to see that the transcendence degree there is
`d`, Tag 02FZ for the openness of the locus where the fibre dimension has dropped, Tag 05F7 to
pass from the generic points to a dense open of the base, and Tag 0GTF to combine the element
found over the dense open with one found over its complement.

## References

* [Stacks Project, Tag 0GTG](https://stacks.math.columbia.edu/tag/0GTG)

## Tags

Noether normalization, quasi-finite, fibre dimension, relative dimension
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits EventualFibreDimension

universe u

namespace WeakRelativeNoetherNormalization

private lemma topologicalKrullDimAt_le {X : Type*} [TopologicalSpace X] (x : X) :
    topologicalKrullDimAt X x ≤ topologicalKrullDim X := by
  rw [topologicalKrullDimAt]
  exact iInf_le_of_le ⟨Set.univ, Set.mem_univ x, isOpen_univ⟩
    (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph).le

/-- The dimension of the fibre of `Spec S ⟶ Spec R` over `p` is that of the preimage of `p` in
`Spec S`. -/
private theorem topologicalKrullDim_fiber_eq {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Spec (.of R)) :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom f)).fiber p) =
      topologicalKrullDim (PrimeSpectrum.comap f ⁻¹' {p}) :=
  (Scheme.Hom.fiberHomeo _ p).isHomeomorph.topologicalKrullDim_eq

/-- The given bound on the dimensions of whole fibres bounds relative dimension at each point.
This is the affine bridge from the scheme-theoretic fibre to the local dimension in its prime
spectrum. -/
private theorem relativeDimensionAt_le_of_fiberDimension_le
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (d : ℕ)
    (hdim : ∀ p : Spec (.of R),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
        (d : WithBot ℕ∞)) (q : Spec (.of S)) [q.asIdeal.IsPrime] :
    Algebra.relativeDimensionAt R q.asIdeal ≤ (d : WithBot ℕ∞) := by
  let φ := CommRingCat.ofHom (algebraMap R S)
  calc
    Algebra.relativeDimensionAt R q.asIdeal =
        topologicalKrullDimAt ((Spec.map φ).fiber (Spec.map φ q))
          ((Spec.map φ).asFiber q) := (AlgebraicGeometry.affine_fiberDimensionAt_eq φ q).symm
    _ ≤ topologicalKrullDim ((Spec.map φ).fiber (Spec.map φ q)) :=
      topologicalKrullDimAt_le _
    _ ≤ (d : WithBot ℕ∞) := hdim (Spec.map φ q)

private theorem fiberDimension_le_of_relativeDimensionAt_le
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (d : ℕ)
    (h : ∀ q : PrimeSpectrum S, Algebra.relativeDimensionAt R q.asIdeal ≤
      (d : WithBot ℕ∞)) (p : Spec (.of R)) :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
      (d : WithBot ℕ∞) := by
  rw [topologicalKrullDim_fiber_eq, TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  apply iSup_le
  rintro ⟨q, hq⟩
  change PrimeSpectrum.comap (algebraMap R S) q = p at hq
  subst p
  convert! h q using 1
  rw [Algebra.relativeDimensionAt,
    TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  rfl

private theorem fiberDimension_comp_le_of_isInducing
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hg : Topology.IsInducing (PrimeSpectrum.comap g)) (p : Spec (.of R)) :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom (g.comp f))).fiber p) ≤
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom f)).fiber p) := by
  rw [topologicalKrullDim_fiber_eq, topologicalKrullDim_fiber_eq, PrimeSpectrum.comap_comp,
    Set.preimage_comp]
  exact (hg.restrictPreimage _).topologicalKrullDim_le

private theorem fiberDimension_comp_eq_of_isEmbedding
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hg : Topology.IsEmbedding (PrimeSpectrum.comap g)) (p : Spec (.of R))
    (hp : PrimeSpectrum.comap f ⁻¹' {p} ⊆ Set.range (PrimeSpectrum.comap g)) :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom (g.comp f))).fiber p) =
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom f)).fiber p) := by
  rw [topologicalKrullDim_fiber_eq, topologicalKrullDim_fiber_eq, PrimeSpectrum.comap_comp,
    Set.preimage_comp]
  have he := (hg.homeomorphImage
    (PrimeSpectrum.comap g ⁻¹' (PrimeSpectrum.comap f ⁻¹' {p}))).isHomeomorph.topologicalKrullDim_eq
  have himage : PrimeSpectrum.comap g ''
      (PrimeSpectrum.comap g ⁻¹' (PrimeSpectrum.comap f ⁻¹' {p})) =
      PrimeSpectrum.comap f ⁻¹' {p} := by
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left.mpr hp]
  exact he.trans (congrArg (fun Z : Set (PrimeSpectrum S) ↦ topologicalKrullDim Z) himage)

private theorem exists_basicOpen_subset_of_localization_range_subset
    {S L : Type*} [CommRing S] [CommRing L] [Algebra S L]
    (M : Submonoid S) [IsLocalization M L] {U : Set (PrimeSpectrum S)} (hU : IsOpen U)
    (h : Set.range (PrimeSpectrum.comap (algebraMap S L)) ⊆ U) :
    ∃ m ∈ M, (PrimeSpectrum.basicOpen m : Set (PrimeSpectrum S)) ⊆ U := by
  classical
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isOpen_iff U).mp hU
  let J := Ideal.span s
  have hJM : ¬ Disjoint (J : Set S) (M : Set S) := by
    intro hd
    obtain ⟨q, hq, hJq, hqM⟩ := Ideal.exists_le_prime_disjoint J M hd
    have hmem : (⟨q, hq⟩ : PrimeSpectrum S) ∈ U := h (by
      rw [PrimeSpectrum.localization_comap_range L M]
      exact hqM.symm)
    have hnmem : (⟨q, hq⟩ : PrimeSpectrum S) ∈ Uᶜ := by
      rw [hs]
      exact fun x hx ↦ hJq (Ideal.subset_span hx)
    exact hnmem hmem
  obtain ⟨m, hmJ, hmM⟩ := Set.not_disjoint_iff.mp hJM
  refine ⟨m, hmM, fun q hq ↦ ?_⟩
  by_contra hqU
  have hsq : s ⊆ q.asIdeal := by
    have : q ∈ Uᶜ := hqU
    rwa [hs] at this
  exact hq ((Ideal.span_le.mpr hsq) hmJ)

private theorem fiberDimension_le_of_away_and_quotient
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (r : R)
    {s : S} (hs : f r = s) (d : ℕ)
    (hloc : ∀ p : Spec (.of R), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom
        ((algebraMap S (Localization.Away s)).comp f))).fiber p) ≤
          (d : WithBot ℕ∞))
    (hquot : ∀ p : Spec (.of R), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {s})).comp f))).fiber p) ≤
          (d : WithBot ℕ∞)) (p : Spec (.of R)) :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom f)).fiber p) ≤
      (d : WithBot ℕ∞) := by
  by_cases hr : r ∈ p.asIdeal
  · rw [← fiberDimension_comp_eq_of_isEmbedding f (Ideal.Quotient.mk (Ideal.span {s}))
      (PrimeSpectrum.isEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective) p]
    · exact hquot p
    · rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker]
      intro q hq
      change PrimeSpectrum.comap f q = p at hq
      change Ideal.span {s} ≤ q.asIdeal
      rw [Ideal.span_singleton_le_iff_mem, ← hs]
      exact show r ∈ (PrimeSpectrum.comap f q).asIdeal from hq ▸ hr
  · rw [← fiberDimension_comp_eq_of_isEmbedding f
      (algebraMap S (Localization.Away s))
      (PrimeSpectrum.localization_away_isOpenEmbedding _ s).isEmbedding p]
    · exact hloc p
    · rw [PrimeSpectrum.localization_away_comap_range (Localization.Away s) s]
      intro q hq
      change PrimeSpectrum.comap f q = p at hq
      change s ∉ q.asIdeal
      rw [← hs]
      exact show r ∉ (PrimeSpectrum.comap f q).asIdeal from hq ▸ hr

private theorem comp_aeval_eq_aeval_map
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (g : S →ₐ[R] T) (a : S) :
    g.toRingHom.comp (Polynomial.aeval (R := R) a).toRingHom =
      (Polynomial.aeval (R := R) (g a)).toRingHom := by
  ext r <;> simp

private theorem fiberDimension_comp_eq_of_comap_injective
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    (f : R →+* A) (g : A →+* S)
    (hf : Function.Injective (PrimeSpectrum.comap f)) (p : Spec (.of A)) :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom (g.comp f))).fiber
      (PrimeSpectrum.comap f p)) =
        topologicalKrullDim ((Spec.map (CommRingCat.ofHom g)).fiber p) := by
  have hs : PrimeSpectrum.comap (g.comp f) ⁻¹' {PrimeSpectrum.comap f p} =
      PrimeSpectrum.comap g ⁻¹' {p} := by
    ext q
    change PrimeSpectrum.comap f (PrimeSpectrum.comap g q) = PrimeSpectrum.comap f p ↔ _
    exact hf.eq_iff
  exact (topologicalKrullDim_fiber_eq _ _).trans
    ((congrArg (fun Z : Set (PrimeSpectrum S) ↦ topologicalKrullDim Z) hs).trans
      (topologicalKrullDim_fiber_eq _ _).symm)

private theorem fiberDimension_comp_le_iff_of_comap_injective
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    (f : R →+* A) (g : A →+* S)
    (hf : Function.Injective (PrimeSpectrum.comap f)) (d : ℕ) :
    (∀ p : Spec (.of R), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom (g.comp f))).fiber p) ≤ (d : WithBot ℕ∞)) ↔
    (∀ p : Spec (.of A), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom g)).fiber p) ≤ (d : WithBot ℕ∞)) := by
  refine ⟨fun h p ↦ ?_, fun h p ↦ ?_⟩
  · rw [← fiberDimension_comp_eq_of_comap_injective f g hf p]
    exact h _
  · by_cases hp : ∃ q : PrimeSpectrum S, PrimeSpectrum.comap (g.comp f) q = p
    · obtain ⟨q, rfl⟩ := hp
      exact le_of_eq_of_le
        (fiberDimension_comp_eq_of_comap_injective f g hf (PrimeSpectrum.comap g q))
        (h _)
    · rw [topologicalKrullDim_fiber_eq]
      have he : PrimeSpectrum.comap (g.comp f) ⁻¹' {p} = ∅ := by
        ext q
        exact ⟨fun hq ↦ hp ⟨q, hq⟩, False.elim⟩
      rw [he, (topologicalKrullDim_eq_bot_iff_isEmpty _).mpr inferInstance]
      exact bot_le

/-- Quasi-finiteness of a surjective ring map. -/
private theorem quasiFinite_of_surjective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Surjective f) : f.QuasiFinite :=
  RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _ hf)

/-- Over a localization `A` of `R`, the induced map on spectra of polynomial rings is injective. -/
private theorem comap_mapRingHom_injective_of_isLocalization
    {R : Type*} [CommRing R] (M : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization M A] :
    Function.Injective (PrimeSpectrum.comap (Polynomial.mapRingHom (algebraMap R A))) := by
  have := Polynomial.isLocalization M A
  exact PrimeSpectrum.localization_comap_injective (Polynomial A) (M.map Polynomial.C)

private theorem fiberDimension_aeval_restrictScalars_iff
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    (hf : Function.Injective (PrimeSpectrum.comap
      (Polynomial.mapRingHom (algebraMap R A)))) (d : ℕ) (a : S) :
    (∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
      ((AlgebraicGeometry.specMapAeval (R := R) a).fiber p) ≤ (d : WithBot ℕ∞)) ↔
    (∀ p : Spec (.of (Polynomial A)), topologicalKrullDim
      ((AlgebraicGeometry.specMapAeval (R := A) a).fiber p) ≤ (d : WithBot ℕ∞)) := by
  have hcomp : (Polynomial.aeval (R := A) a).toRingHom.comp
      (Polynomial.mapRingHom (algebraMap R A)) =
        (Polynomial.aeval (R := R) a).toRingHom := by
    ext r <;> simp [← IsScalarTower.algebraMap_apply R A S]
  have h := fiberDimension_comp_le_iff_of_comap_injective
    (Polynomial.mapRingHom (algebraMap R A)) (Polynomial.aeval (R := A) a).toRingHom hf d
  rwa [hcomp] at h

private theorem fiberDimension_aeval_smul_le_iff
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (d : ℕ) (a : S) (r : R) (hr : IsUnit r) :
    (∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
      ((AlgebraicGeometry.specMapAeval (r • a)).fiber p) ≤ (d : WithBot ℕ∞)) ↔
    (∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
      ((AlgebraicGeometry.specMapAeval a).fiber p) ≤ (d : WithBot ℕ∞)) := by
  let := hr.invertible
  let e := Polynomial.algEquivCMulXAddC r 0
  have hcomp : (Polynomial.aeval (R := R) a).toRingHom.comp e.toRingEquiv.toRingHom =
      (Polynomial.aeval (R := R) (r • a)).toRingHom := by
    ext x <;> simp [e, Polynomial.algEquivCMulXAddC_apply, Algebra.smul_def]
  have h := fiberDimension_comp_le_iff_of_comap_injective e.toRingEquiv.toRingHom
    (Polynomial.aeval (R := R) a).toRingHom
    (PrimeSpectrum.comap_injective_of_surjective _ e.surjective) d
  rwa [hcomp] at h

attribute [local instance] Polynomial.algebra in
private theorem exists_mem_span_fiberDimension_aeval_le_of_localization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (d : ℕ) (r : R) (a : Localization.Away (algebraMap R S r))
    (ha : ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
      ((AlgebraicGeometry.specMapAeval a).fiber p) ≤ (d : WithBot ℕ∞)) :
    ∃ b ∈ Ideal.span {algebraMap R S r},
      ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
        ((AlgebraicGeometry.specMapAeval
          (algebraMap S (Localization.Away (algebraMap R S r)) b)).fiber p) ≤
            (d : WithBot ℕ∞) := by
  let A := Localization.Away r
  let L := Localization.Away (algebraMap R S r)
  have hr : IsUnit (algebraMap R L r) := by
    rw [IsScalarTower.algebraMap_apply R S L]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R S r)
  let f : A →+* L := IsLocalization.Away.lift r hr
  let := f.toAlgebra
  have : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsLocalization.Away.lift_eq r hr x).symm
  have hf := comap_mapRingHom_injective_of_isLocalization (Submonoid.powers r) A
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj (algebraMap R S r) a
  refine ⟨algebraMap R S r * b, Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)), ?_⟩
  have ha' := (fiberDimension_aeval_restrictScalars_iff (S := L) hf d a).mp ha
  have hrA : IsUnit (algebraMap R A r ^ (n + 1)) :=
    (IsLocalization.Away.algebraMap_isUnit (S := A) r).pow _
  have hscaled := (fiberDimension_aeval_smul_le_iff d a
    (algebraMap R A r ^ (n + 1)) hrA).mpr ha'
  have heq : algebraMap R A r ^ (n + 1) • a =
      algebraMap S L (algebraMap R S r * b) := by
    rw [Algebra.smul_def, map_pow, ← IsScalarTower.algebraMap_apply R A L,
      map_mul, ← hb, ← IsScalarTower.algebraMap_apply R S L, pow_succ]
    ring
  rw [heq] at hscaled
  exact (fiberDimension_aeval_restrictScalars_iff (S := L) hf d _).mpr hscaled

private theorem exists_pow_add_fiberDimension_le
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ) (r : R) (a b : S)
    (ha : a ∈ Ideal.span {algebraMap R S r})
    (hloc : ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
      ((AlgebraicGeometry.specMapAeval
        (algebraMap S (Localization.Away (algebraMap R S r)) a)).fiber p) ≤
          (d : WithBot ℕ∞))
    (hquot : ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
      ((AlgebraicGeometry.specMapAeval
        (Ideal.Quotient.mk (Ideal.span {algebraMap R S r}) b)).fiber p) ≤
          (d : WithBot ℕ∞)) :
    ∃ n : ℕ, 0 < n ∧ ∀ p : Spec (.of (Polynomial R)),
      topologicalKrullDim ((AlgebraicGeometry.specMapAeval (a ^ n + b)).fiber p) ≤
        (d : WithBot ℕ∞) := by
  let L := Localization.Away (algebraMap R S r)
  let J : Ideal S := Ideal.span {algebraMap R S r}
  let l : S →ₐ[R] L := IsScalarTower.toAlgHom R S L
  let q : S →ₐ[R] S ⧸ J := Ideal.Quotient.mkₐ R J
  obtain ⟨n₀, hn₀⟩ :=
    eventually_topologicalKrullDim_fiber_specMapAeval_pow_add_le d (l a) (l b) hloc
  let n := max n₀ 1
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  refine ⟨n, hn, ?_⟩
  have hqa : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hqb : q (a ^ n + b) = q b := by simp [hqa, hn.ne']
  apply fiberDimension_le_of_away_and_quotient
    (Polynomial.aeval (R := R) (a ^ n + b)).toRingHom (Polynomial.C r)
    (s := algebraMap R S r) (Polynomial.aeval_C _ _) d
  · change ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom
        (l.toRingHom.comp (Polynomial.aeval (R := R) (a ^ n + b)).toRingHom))).fiber p) ≤ _
    rw [comp_aeval_eq_aeval_map l, map_add, map_pow]
    exact hn₀ n (le_max_left _ _)
  · change ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom
        (q.toRingHom.comp (Polynomial.aeval (R := R) (a ^ n + b)).toRingHom))).fiber p) ≤ _
    rw [comp_aeval_eq_aeval_map q, hqb]
    exact hquot

private theorem exists_fiberDimension_aeval_le_of_away_and_quotient
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ) (r : R)
    (hloc : ∃ a : Localization.Away (algebraMap R S r),
      ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
        ((AlgebraicGeometry.specMapAeval a).fiber p) ≤ (d : WithBot ℕ∞))
    (hquot : ∃ b : S ⧸ Ideal.span {algebraMap R S r},
      ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
        ((AlgebraicGeometry.specMapAeval b).fiber p) ≤ (d : WithBot ℕ∞)) :
    ∃ a : S, ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
      ((AlgebraicGeometry.specMapAeval a).fiber p) ≤ (d : WithBot ℕ∞) := by
  obtain ⟨a, ha⟩ := hloc
  obtain ⟨a', ha'mem, ha'⟩ :=
    exists_mem_span_fiberDimension_aeval_le_of_localization d r a ha
  obtain ⟨b, hb⟩ := hquot
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨n, _, hn⟩ := exists_pow_add_fiberDimension_le d r a' b' ha'mem ha' hb
  exact ⟨a' ^ n + b', hn⟩

private theorem comap_preimage_subset_localization_range
    {R S L : Type u} [CommRing R] [CommRing S] [CommRing L] [Algebra R S] [Algebra S L]
    (M : Submonoid R) [IsLocalization (M.map (algebraMap R S)) L] (f : Polynomial R →+* S)
    (hf : ∀ r, f (Polynomial.C r) = algebraMap R S r) (qL : PrimeSpectrum L) :
    PrimeSpectrum.comap f ⁻¹' {PrimeSpectrum.comap f (PrimeSpectrum.comap (algebraMap S L) qL)} ⊆
      Set.range (PrimeSpectrum.comap (algebraMap S L)) := by
  intro q' hq'
  rw [PrimeSpectrum.localization_comap_range L (M.map (algebraMap R S))]
  refine Set.disjoint_left.mpr ?_
  rintro s ⟨r, hr, rfl⟩ hs
  have hC : Polynomial.C r ∈ (PrimeSpectrum.comap f q').asIdeal := by
    change f (Polynomial.C r) ∈ q'.asIdeal
    rw [hf]
    exact hs
  rw [show PrimeSpectrum.comap f q' = _ from hq'] at hC
  have hm : algebraMap S L (algebraMap R S r) ∈ qL.asIdeal := by
    rw [← hf]
    exact hC
  exact qL.isPrime.ne_top (qL.asIdeal.eq_top_of_isUnit_mem hm
    (IsLocalization.map_units (M := M.map (algebraMap R S)) L
      ⟨algebraMap R S r, ⟨r, hr, rfl⟩⟩))

private theorem exists_fiberDimension_aeval_le_away_of_localization
    {R S L : Type u} [CommRing R] [CommRing S] [CommRing L]
    [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L]
    [Algebra.FiniteType R S] (M : Submonoid R)
    [IsLocalization (M.map (algebraMap R S)) L] (d : ℕ) (a : S)
    (ha : ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
      ((AlgebraicGeometry.specMapAeval (algebraMap S L a)).fiber p) ≤ (d : WithBot ℕ∞)) :
    ∃ r ∈ M, ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
      ((AlgebraicGeometry.specMapAeval
        (algebraMap S (Localization.Away (algebraMap R S r)) a)).fiber p) ≤
          (d : WithBot ℕ∞) := by
  let A := Polynomial R
  let f : A →+* S := (Polynomial.aeval (R := R) a).toRingHom
  let := f.toAlgebra
  have : IsScalarTower R A S :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (Polynomial.aeval a).commutes r |>.symm
  have : Algebra.FiniteType A S := Algebra.FiniteType.of_restrictScalars_finiteType R A S
  let U : Set (PrimeSpectrum S) :=
    {q | Algebra.relativeDimensionAt A q.asIdeal ≤ (d : WithBot ℕ∞)}
  have hU : IsOpen U := Algebra.isOpen_setOf_relativeDimensionAt_le d
  have hLU : Set.range (PrimeSpectrum.comap (algebraMap S L)) ⊆ U := by
    rintro q ⟨qL, rfl⟩
    let p := PrimeSpectrum.comap f (PrimeSpectrum.comap (algebraMap S L) qL)
    have he := fiberDimension_comp_eq_of_isEmbedding f (algebraMap S L)
      (PrimeSpectrum.localization_comap_isEmbedding L (M.map (algebraMap R S))) p
      (comap_preimage_subset_localization_range M f (Polynomial.aeval_C a) qL)
    have hdim : topologicalKrullDim ((Spec.map (CommRingCat.ofHom f)).fiber p) ≤
        (d : WithBot ℕ∞) := by
      rw [← he, show (algebraMap S L).comp f =
        (Polynomial.aeval (R := R) (algebraMap S L a)).toRingHom from
          comp_aeval_eq_aeval_map (IsScalarTower.toAlgHom R S L) a]
      exact ha p
    change Algebra.relativeDimensionAt A
      (PrimeSpectrum.comap (algebraMap S L) qL).asIdeal ≤ _
    exact le_of_eq_of_le
      (AlgebraicGeometry.affine_fiberDimensionAt_eq (CommRingCat.ofHom f)
        (PrimeSpectrum.comap (algebraMap S L) qL)).symm
      ((topologicalKrullDimAt_le _).trans hdim)
  obtain ⟨s, hs, hsub⟩ :=
    exists_basicOpen_subset_of_localization_range_subset (M.map (algebraMap R S)) hU hLU
  obtain ⟨r, hr, rfl⟩ := hs
  refine ⟨r, hr, ?_⟩
  let T := Localization.Away (algebraMap R S r)
  let g : A →+* T := (algebraMap S T).comp f
  have H : ∀ p : Spec (.of A), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom g)).fiber p) ≤ (d : WithBot ℕ∞) := by
    apply fiberDimension_le_of_relativeDimensionAt_le d
    intro q
    rw [← Algebra.relativeDimensionAt_comap_eq (R := A) (algebraMap R S r) T q.asIdeal]
    have hq : PrimeSpectrum.comap (algebraMap S T) q ∈ U := hsub (by
      rw [← PrimeSpectrum.localization_away_comap_range T (algebraMap R S r)]
      exact ⟨q, rfl⟩)
    exact hq
  have hg : g = (Polynomial.aeval (R := R) (algebraMap S T a)).toRingHom :=
    comp_aeval_eq_aeval_map (IsScalarTower.toAlgHom R S T) a
  rwa [hg] at H

private theorem relativeDimensionAt_eq_of_fiber {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [hq : q.IsPrime] :
    Algebra.relativeDimensionAt R q =
      _root_.relativeDimensionAt R S
        (PrimeSpectrum.comap (algebraMap R S) (⟨q, hq⟩ : PrimeSpectrum S)).asIdeal
        (PrimeSpectrum.preimageHomeomorphFiber R S _ ⟨⟨q, hq⟩, rfl⟩) := by
  rw [_root_.relativeDimensionAt, krullDimAt_eq_topologicalKrullDimAt,
    ← topologicalKrullDimAt_eq_of_homeomorph, Algebra.relativeDimensionAt]

private theorem comap_fiberMap_preimageHomeomorphFiber {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (q : Ideal S) [hq : q.IsPrime] :
    PrimeSpectrum.comap
        (fiberMap R S
          (PrimeSpectrum.comap (algebraMap R S) (⟨q, hq⟩ : PrimeSpectrum S)).asIdeal)
        (PrimeSpectrum.preimageHomeomorphFiber R S _ ⟨⟨q, hq⟩, rfl⟩) =
      ⟨q, hq⟩ := by
  set p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) (⟨q, hq⟩ : PrimeSpectrum S)
  set e := PrimeSpectrum.preimageHomeomorphFiber R S p
  set x : ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) := ⟨⟨q, hq⟩, rfl⟩
  have key : ((e.symm (e x) : ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})) :
      PrimeSpectrum S) = PrimeSpectrum.comap (fiberMap R S p.asIdeal) (e x) := rfl
  rw [← key, e.symm_apply_apply]

/-- The pointwise quasi-finite normalization supplied by relative dimension, with its local
dimension hypothesis expressed using `Algebra.relativeDimensionAt`. -/
private theorem exists_quasiFinite_localization_of_relativeDimension
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] {n : ℕ}
    (hn : Algebra.relativeDimensionAt R q = (n : WithBot ℕ∞)) :
    ∃ g ∉ q, ∃ ψ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g,
      ψ.toRingHom.FiniteType ∧ ψ.toRingHom.QuasiFinite := by
  let qS : PrimeSpectrum S := ⟨q, ‹_›⟩
  let pS := PrimeSpectrum.comap (algebraMap R S) qS
  let qbar := PrimeSpectrum.preimageHomeomorphFiber R S pS ⟨qS, rfl⟩
  have hqbar : PrimeSpectrum.comap (fiberMap R S pS.asIdeal) qbar = qS :=
    comap_fiberMap_preimageHomeomorphFiber q
  have hdim : _root_.relativeDimensionAt R S pS.asIdeal qbar = (n : ℕ∞) := by
    rw [← relativeDimensionAt_eq_of_fiber (R := R) (S := S) q, hn]
    norm_cast
  obtain ⟨g, hg, φ, hcomm, hft, hqf⟩ :=
    quasiFinite_over_polynomial_of_relativeDimension R S qS pS.asIdeal qbar hqbar n hdim
  exact ⟨g, hg, ⟨φ, fun r ↦ DFunLike.congr_fun hcomm r⟩, hft, hqf⟩

private theorem exists_quasiFinite_mvPolynomial_of_le
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n d : ℕ}
    (hnd : n ≤ d) (ψ : MvPolynomial (Fin n) R →ₐ[R] S)
    (hψft : ψ.toRingHom.FiniteType) (hψqf : ψ.toRingHom.QuasiFinite) :
    ∃ φ : MvPolynomial (Fin d) R →ₐ[R] S,
      φ.toRingHom.FiniteType ∧ φ.toRingHom.QuasiFinite := by
  let e : MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin n) R :=
    MvPolynomial.aeval fun i => if hi : (i : ℕ) < n then
      MvPolynomial.X ⟨(i : ℕ), hi⟩ else 0
  have heX (i : Fin n) : e (MvPolynomial.X (Fin.castLE hnd i)) = MvPolynomial.X i := by
    simp [e]
  have he : Function.Surjective e := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C a => exact ⟨MvPolynomial.C a, by simp [e]⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', by simp [e]⟩
    | mul_X x i hx =>
      obtain ⟨x', rfl⟩ := hx
      refine ⟨x' * MvPolynomial.X (Fin.castLE hnd i), ?_⟩
      rw [map_mul, heX]
  exact ⟨ψ.comp e, hψft.comp (RingHom.FiniteType.of_surjective _ he),
    hψqf.comp (quasiFinite_of_surjective he)⟩

private theorem exists_quasiFinite_localization_of_fiberDimension_le
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (d : ℕ) (hdim : ∀ p : Spec (.of R),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
        (d : WithBot ℕ∞)) (q : Ideal S) [q.IsPrime] :
    ∃ g ∉ q, ∃ ψ : MvPolynomial (Fin d) R →ₐ[R] Localization.Away g,
      ψ.toRingHom.FiniteType ∧ ψ.toRingHom.QuasiFinite := by
  let qS : Spec (.of S) := ⟨q, ‹_›⟩
  obtain ⟨n, hn, hnd⟩ := Stacks.RelativeDimension.Semicontinuity.exists_nat_eq_of_zero_le_of_le_nat
    (by
      rw [Algebra.relativeDimensionAt]
      exact topologicalKrullDimAt_nonneg _)
    (relativeDimensionAt_le_of_fiberDimension_le d hdim qS)
  obtain ⟨g, hg, ψ, hψft, hψqf⟩ :=
    exists_quasiFinite_localization_of_relativeDimension q hn
  exact ⟨g, hg, exists_quasiFinite_mvPolynomial_of_le hnd ψ hψft hψqf⟩

private theorem finiteType_algHom_of_finiteType
    {R A S : Type*} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra.FiniteType R S] (φ : A →ₐ[R] S) :
    φ.toRingHom.FiniteType := by
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap R A)
  rw [show φ.toRingHom.comp (algebraMap R A) = algebraMap R S from RingHom.ext φ.commutes,
    RingHom.finiteType_algebraMap]
  infer_instance

private theorem affine_fiberDimension_eq_ringKrullDim
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : Spec (.of R)) [p.asIdeal.IsPrime] :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) =
      ringKrullDim (p.asIdeal.Fiber S) := by
  rw [topologicalKrullDim_fiber_eq]
  exact (PrimeSpectrum.preimageHomeomorphFiber R S p).isHomeomorph.topologicalKrullDim_eq.trans
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)

open scoped TensorProduct in
attribute [local instance] MvPolynomial.algebraMvPolynomial in
private theorem fiberDimension_le_of_quasiFinite_mvPolynomial
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (d : ℕ)
    (φ : MvPolynomial (Fin d) R →ₐ[R] S) (hφ : φ.toRingHom.QuasiFinite)
    (p : Spec (.of R)) :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
      (d : WithBot ℕ∞) := by
  have := p.isPrime
  let P := MvPolynomial (Fin d) R
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R P S :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  have : Algebra.QuasiFinite P S := hφ
  have hmap : ∀ x : P,
      (MvPolynomial.algebraTensorAlgEquiv R p.asIdeal.ResidueField)
          ((Algebra.TensorProduct.comm R P p.asIdeal.ResidueField)
            (algebraMap P (P ⊗[R] p.asIdeal.ResidueField) x)) =
        algebraMap P (MvPolynomial (Fin d) p.asIdeal.ResidueField) x := by
    intro x
    simp [Algebra.TensorProduct.algebraMap_apply, P]
  let eP : (P ⊗[R] p.asIdeal.ResidueField) ≃ₐ[P]
      MvPolynomial (Fin d) p.asIdeal.ResidueField :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm R P p.asIdeal.ResidueField).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv R p.asIdeal.ResidueField).toRingEquiv) hmap
  let eBC := (Algebra.TensorProduct.cancelBaseChange R P P S p.asIdeal.ResidueField).symm
  let e : p.asIdeal.Fiber S ≃+*
      (MvPolynomial (Fin d) p.asIdeal.ResidueField) ⊗[P] S :=
    (Algebra.TensorProduct.comm R p.asIdeal.ResidueField S).toRingEquiv.trans
      (eBC.toRingEquiv.trans
        ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := P) (A₁ := S)) eP).toRingEquiv.trans
          (Algebra.TensorProduct.comm P S
            (MvPolynomial (Fin d) p.asIdeal.ResidueField)).toRingEquiv))
  rw [affine_fiberDimension_eq_ringKrullDim, ringKrullDim_eq_of_ringEquiv e]
  simpa using ringKrullDim_le_natCard_of_quasiFinite_mvPolynomial p.asIdeal.ResidueField
    (σ := Fin d) (S := (MvPolynomial (Fin d) p.asIdeal.ResidueField) ⊗[P] S)

open scoped TensorProduct in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem exists_quasiFinite_mvPolynomial_tensorProduct
    {R₀ S₀ R : Type u} [CommRing R₀] [CommRing S₀] [CommRing R]
    [Algebra R₀ S₀] [Algebra R₀ R] (d : ℕ)
    (φ : MvPolynomial (Fin d) R₀ →ₐ[R₀] S₀) (hφ : φ.toRingHom.QuasiFinite) :
    ∃ ψ : MvPolynomial (Fin d) R →ₐ[R] S₀ ⊗[R₀] R,
      ψ.toRingHom.QuasiFinite := by
  let P := MvPolynomial (Fin d) R₀
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R₀ P S₀ :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  let f : P ⊗[R₀] R →ₐ[R₀] S₀ ⊗[R₀] R :=
    Algebra.TensorProduct.map φ (AlgHom.id R₀ R)
  let := f.toRingHom.toAlgebra
  have : IsScalarTower P (P ⊗[R₀] R) (S₀ ⊗[R₀] R) :=
    IsScalarTower.of_algebraMap_eq (R := P) (S := P ⊗[R₀] R)
      (A := S₀ ⊗[R₀] R) fun x ↦ by
        change φ x ⊗ₜ[R₀] 1 = f (x ⊗ₜ[R₀] 1)
        simp [f]
  have : Algebra.IsPushout P S₀ (P ⊗[R₀] R) (S₀ ⊗[R₀] R) :=
    Algebra.IsPushout.tensorProduct_tensorProduct R₀ R P S₀ (by
      ext r
      change f (1 ⊗ₜ[R₀] r) = 1 ⊗ₜ[R₀] r
      simp [f])
  have hqf : f.toRingHom.QuasiFinite :=
    RingHom.QuasiFinite.isStableUnderBaseChange P S₀ (P ⊗[R₀] R) (S₀ ⊗[R₀] R) hφ
  let fR : P ⊗[R₀] R →ₐ[R] S₀ ⊗[R₀] R :=
    { __ := f.toRingHom
      commutes' r := by
        change f (1 ⊗ₜ[R₀] r) = 1 ⊗ₜ[R₀] r
        simp [f] }
  let e₀ : P ⊗[R₀] R ≃ₐ[R] R ⊗[R₀] P :=
    { Algebra.TensorProduct.comm R₀ P R with commutes' := fun r ↦ rfl }
  let e := e₀.trans (MvPolynomial.algebraTensorAlgEquiv R₀ R)
  exact ⟨fR.comp e.symm.toAlgHom,
    hqf.comp (quasiFinite_of_surjective e.symm.surjective)⟩

private theorem exists_quasiFinite_mvPolynomial_of_surjective
    {R A S : Type*} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra.FiniteType R S] (d : ℕ)
    (g : A →ₐ[R] S) (hg : Function.Surjective g)
    (h : ∃ φ : MvPolynomial (Fin d) R →ₐ[R] A, φ.toRingHom.QuasiFinite) :
    ∃ φ : MvPolynomial (Fin d) R →ₐ[R] S,
      φ.toRingHom.FiniteType ∧ φ.toRingHom.QuasiFinite := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨g.comp φ, finiteType_algHom_of_finiteType _,
    (quasiFinite_of_surjective hg).comp hφ⟩

open scoped TensorProduct in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem exists_quasiFinite_mvPolynomial_of_adjoin_eq_top
    {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S]
    [Algebra.FiniteType R S] (B : Subalgebra A S)
    (hB : Algebra.adjoin R (B : Set S) = ⊤) (d : ℕ)
    (h : ∃ φ : MvPolynomial (Fin d) A →ₐ[A] B, φ.toRingHom.QuasiFinite) :
    ∃ φ : MvPolynomial (Fin d) R →ₐ[R] S,
      φ.toRingHom.FiniteType ∧ φ.toRingHom.QuasiFinite := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := exists_quasiFinite_mvPolynomial_tensorProduct (R := R) d φ hφ
  let g : B ⊗[A] R →ₐ[A] S :=
    Algebra.TensorProduct.productMap B.val (IsScalarTower.toAlgHom A R S)
  let gR : B ⊗[A] R →ₐ[R] S :=
    { __ := g.toRingHom
      commutes' r := by
        change g (1 ⊗ₜ[A] r) = algebraMap R S r
        simp [g] }
  have hgen : (B : Set S) ⊆ gR.range := fun b hb ↦ ⟨⟨b, hb⟩ ⊗ₜ[A] 1, by simp [gR, g]⟩
  have hg : Function.Surjective gR := by
    rw [← AlgHom.range_eq_top]
    exact top_le_iff.mp (hB ▸ Algebra.adjoin_le hgen)
  exact exists_quasiFinite_mvPolynomial_of_surjective d gR hg ⟨ψ, hψ⟩

private theorem exists_quasiFinite_mvPolynomial_of_fiberDimension_le_of_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (d : ℕ)
    (hdim : ∀ p : Spec (.of k),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap k S))).fiber p) ≤
        (d : WithBot ℕ∞)) :
    ∃ φ : MvPolynomial (Fin d) k →ₐ[k] S,
      φ.toRingHom.FiniteType ∧ φ.toRingHom.QuasiFinite := by
  classical
  cases subsingleton_or_nontrivial S with
  | inl h =>
    let φ : MvPolynomial (Fin d) k →ₐ[k] S := MvPolynomial.aeval fun _ ↦ 0
    exact ⟨φ, finiteType_algHom_of_finiteType φ,
      quasiFinite_of_surjective fun s ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  | inr h =>
    have hdimS : ringKrullDim S ≤ (d : WithBot ℕ∞) := by
      let p : Spec (.of k) := ⟨⊥, inferInstance⟩
      have hp : PrimeSpectrum.comap (algebraMap k S) ⁻¹' {p} = Set.univ :=
        Set.eq_univ_of_forall fun q ↦ Subsingleton.elim _ _
      have H := hdim p
      rw [topologicalKrullDim_fiber_eq (algebraMap k S) p] at H
      rwa [hp, (Homeomorph.Set.univ (PrimeSpectrum S)).isHomeomorph.topologicalKrullDim_eq,
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at H
    obtain ⟨n, φ, hn, _, hφ⟩ := noether_normalization_global (k := k) (T := S)
    have hnd : n ≤ d := mod_cast hn.trans_le hdimS
    exact exists_quasiFinite_mvPolynomial_of_le hnd φ hφ.finiteType
      (RingHom.QuasiFinite.of_finite hφ)

private theorem quasiFinite_of_fiberDimension_le_zero
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    (hdim : ∀ p : Spec (.of R),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
        (0 : WithBot ℕ∞)) :
    (algebraMap R S).QuasiFinite := by
  let U : Set S := {g | (algebraMap R (Localization.Away g)).QuasiFinite}
  have hU : Ideal.span U = ⊤ := by
    by_contra h
    obtain ⟨q, hq, hUq⟩ := Ideal.exists_le_maximal (Ideal.span U) h
    have := hq.isPrime
    obtain ⟨g, hg, ψ, _, hψ⟩ :=
      exists_quasiFinite_localization_of_fiberDimension_le 0 hdim q
    have hgU : g ∈ U := by
      change (algebraMap R (Localization.Away g)).QuasiFinite
      have hC : (algebraMap R (MvPolynomial (Fin 0) R)).QuasiFinite :=
        quasiFinite_of_surjective (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.surjective
      have hψC : ψ.toRingHom.comp (algebraMap R (MvPolynomial (Fin 0) R)) =
          algebraMap R (Localization.Away g) := RingHom.ext ψ.commutes
      exact hψC ▸ hψ.comp hC
    exact hg (hUq (Ideal.subset_span hgU))
  refine RingHom.QuasiFinite.ofLocalizationSpanTarget (algebraMap R S) U hU fun g ↦ ?_
  rw [← IsScalarTower.algebraMap_eq R S (Localization.Away g.1)]
  exact g.2

private theorem exists_quasiFinite_mvPolynomial_zero_of_fiberDimension_le
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    (hdim : ∀ p : Spec (.of R),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
        (0 : WithBot ℕ∞)) :
    ∃ φ : MvPolynomial (Fin 0) R →ₐ[R] S,
      φ.toRingHom.FiniteType ∧ φ.toRingHom.QuasiFinite := by
  let e := MvPolynomial.isEmptyAlgEquiv R (Fin 0)
  let φ := (Algebra.ofId R S).comp e.toAlgHom
  exact ⟨φ, finiteType_algHom_of_finiteType φ,
    (quasiFinite_of_fiberDimension_le_zero hdim).comp
      (quasiFinite_of_surjective e.surjective)⟩

/-- Polynomials in `d + 1` variables over `R` are polynomials in `d` variables over `R[X]`. -/
private noncomputable def mvPolynomialSuccEquiv (R : Type*) [CommRing R] (d : ℕ) :
    MvPolynomial (Fin (d + 1)) R ≃ₐ[R] MvPolynomial (Fin d) (Polynomial R) :=
  (MvPolynomial.renameEquiv R (finSuccEquiv d)).trans
    (MvPolynomial.optionEquivRight R (Fin d))

private theorem exists_quasiFinite_mvPolynomial_succ_of_polynomial
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ) (a : S)
    (h : letI := (Polynomial.aeval (R := R) a).toRingHom.toAlgebra
      ∃ φ : MvPolynomial (Fin d) (Polynomial R) →ₐ[Polynomial R] S,
        φ.toRingHom.QuasiFinite) :
    ∃ φ : MvPolynomial (Fin (d + 1)) R →ₐ[R] S,
      φ.toRingHom.FiniteType ∧ φ.toRingHom.QuasiFinite := by
  let := (Polynomial.aeval (R := R) a).toRingHom.toAlgebra
  have : IsScalarTower R (Polynomial R) S :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (Polynomial.aeval a).commutes r |>.symm
  obtain ⟨φ, hφ⟩ := h
  let e := mvPolynomialSuccEquiv R d
  let ψ := (φ.restrictScalars R).comp e.toAlgHom
  exact ⟨ψ, finiteType_algHom_of_finiteType ψ,
    hφ.comp (quasiFinite_of_surjective e.surjective)⟩

private theorem exists_fiberDimension_aeval_le_of_quasiFinite_mvPolynomial
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (d : ℕ)
    (φ : MvPolynomial (Fin (d + 1)) R →ₐ[R] S) (hφ : φ.toRingHom.QuasiFinite) :
    ∃ a : S, ∀ p : Spec (.of (Polynomial R)),
      topologicalKrullDim ((AlgebraicGeometry.specMapAeval a).fiber p) ≤
        (d : WithBot ℕ∞) := by
  let e := mvPolynomialSuccEquiv R d
  let g := φ.comp e.symm.toAlgHom
  let f : Polynomial R →ₐ[R] S :=
    g.comp (IsScalarTower.toAlgHom R (Polynomial R) (MvPolynomial (Fin d) (Polynomial R)))
  let := f.toRingHom.toAlgebra
  let ψ : MvPolynomial (Fin d) (Polynomial R) →ₐ[Polynomial R] S :=
    { __ := g.toRingHom
      commutes' _ := rfl }
  have hψ : ψ.toRingHom.QuasiFinite :=
    hφ.comp (quasiFinite_of_surjective e.symm.surjective)
  have hf : Polynomial.aeval (R := R) (f Polynomial.X) = f := by ext; simp
  refine ⟨f Polynomial.X, fun p ↦ ?_⟩
  change topologicalKrullDim ((Spec.map (CommRingCat.ofHom
    (Polynomial.aeval (R := R) (f Polynomial.X)).toRingHom)).fiber p) ≤ _
  rw [hf]
  exact fiberDimension_le_of_quasiFinite_mvPolynomial d ψ hψ p

private theorem exists_fiberDimension_aeval_le_of_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (d : ℕ)
    (hdim : ∀ p : Spec (.of k),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap k S))).fiber p) ≤
        ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ a : S, ∀ p : Spec (.of (Polynomial k)),
      topologicalKrullDim ((AlgebraicGeometry.specMapAeval a).fiber p) ≤
        (d : WithBot ℕ∞) := by
  obtain ⟨φ, _, hφ⟩ :=
    exists_quasiFinite_mvPolynomial_of_fiberDimension_le_of_field (d + 1) hdim
  exact exists_fiberDimension_aeval_le_of_quasiFinite_mvPolynomial d φ hφ

attribute [local instance] Algebra.TensorProduct.rightAlgebra Polynomial.algebra in
private theorem exists_fiberDimension_aeval_le_away_of_domain
    {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ)
    (hdim : ∀ p : Spec (.of R), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
        ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ r : R, r ≠ 0 ∧ ∃ a : S,
      ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
        ((AlgebraicGeometry.specMapAeval
          (algebraMap S (Localization.Away (algebraMap R S r)) a)).fiber p) ≤
            (d : WithBot ℕ∞) := by
  let K := (⊥ : Ideal R).ResidueField
  let F := (⊥ : Ideal R).Fiber S
  have : IsLocalization ((nonZeroDivisors R).map (algebraMap R S)) F :=
    IsLocalization.tensorRight K (nonZeroDivisors R)
  have hF : ringKrullDim F ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
    (affine_fiberDimension_eq_ringKrullDim (S := S)
      (⟨⊥, inferInstance⟩ : PrimeSpectrum R)) ▸ hdim ⟨⊥, inferInstance⟩
  have hdimF : ∀ p : Spec (.of K), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom (algebraMap K F))).fiber p) ≤
        ((d + 1 : ℕ) : WithBot ℕ∞) := by
    intro p
    rw [topologicalKrullDim_fiber_eq]
    exact Topology.IsInducing.subtypeVal.topologicalKrullDim_le.trans
      ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim F).trans_le hF)
  obtain ⟨a, ha⟩ := exists_fiberDimension_aeval_le_of_field d hdimF
  obtain ⟨⟨b, m⟩, hb⟩ :=
    IsLocalization.surj ((nonZeroDivisors R).map (algebraMap R S)) a
  obtain ⟨r, hr, hmr⟩ := m.2
  have hrK : IsUnit (algebraMap R K r) := IsLocalization.map_units K ⟨r, hr⟩
  have hscaled := (fiberDimension_aeval_smul_le_iff d a (algebraMap R K r) hrK).mpr ha
  have heq : algebraMap R K r • a = algebraMap S F b := by
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R K F, mul_comm,
      IsScalarTower.algebraMap_apply R S F, hmr]
    exact hb
  rw [heq] at hscaled
  have hbR := (fiberDimension_aeval_restrictScalars_iff (S := F)
    (comap_mapRingHom_injective_of_isLocalization (nonZeroDivisors R) K) d
    (algebraMap S F b)).mpr hscaled
  obtain ⟨s, hs, hgood⟩ :=
    exists_fiberDimension_aeval_le_away_of_localization (nonZeroDivisors R) d b hbR
  exact ⟨s, nonZeroDivisors.ne_zero hs, b, hgood⟩

private theorem exists_fiberDimension_aeval_le_of_subsingleton
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Subsingleton S] (d : ℕ) :
    ∃ a : S, ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
      ((AlgebraicGeometry.specMapAeval a).fiber p) ≤ (d : WithBot ℕ∞) := by
  let φ : MvPolynomial (Fin (d + 1)) R →ₐ[R] S := MvPolynomial.aeval fun _ ↦ 0
  exact exists_fiberDimension_aeval_le_of_quasiFinite_mvPolynomial d φ
    (quasiFinite_of_surjective fun s ↦ ⟨0, Subsingleton.elim _ _⟩)

private theorem exists_fiberDimension_aeval_le_away_of_prime_ker
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ)
    (hdim : ∀ p : Spec (.of R), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
        ((d + 1 : ℕ) : WithBot ℕ∞))
    (I : Ideal R) [I.IsPrime] (hI : I ≤ RingHom.ker (algebraMap R S)) :
    ∃ r ∉ I, ∃ a : Localization.Away (algebraMap R S r),
      ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
        ((AlgebraicGeometry.specMapAeval a).fiber p) ≤ (d : WithBot ℕ∞) := by
  let B := R ⧸ I
  let f : B →+* S := Ideal.Quotient.lift I (algebraMap R S) hI
  let := f.toAlgebra
  have : IsScalarTower R B S := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FiniteType B S := Algebra.FiniteType.of_restrictScalars_finiteType R B S
  have hdimB : ∀ p : Spec (.of B), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom (algebraMap B S))).fiber p) ≤
        ((d + 1 : ℕ) : WithBot ℕ∞) :=
    (fiberDimension_comp_le_iff_of_comap_injective (Ideal.Quotient.mk I)
      (algebraMap B S) (PrimeSpectrum.comap_injective_of_surjective _
        Ideal.Quotient.mk_surjective) (d + 1)).mp hdim
  obtain ⟨r, hr, a, ha⟩ := exists_fiberDimension_aeval_le_away_of_domain d hdimB
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hrI : r ∉ I := fun h ↦ hr (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  let L := Localization.Away (algebraMap R S r)
  rw [show algebraMap B S (Ideal.Quotient.mk I r) = algebraMap R S r from rfl] at ha
  have hcomap : Function.Injective
      (PrimeSpectrum.comap (Polynomial.mapRingHom (algebraMap R B))) :=
    PrimeSpectrum.comap_injective_of_surjective _
      (Polynomial.map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective)
  exact ⟨r, hrI, algebraMap S L a,
    (fiberDimension_aeval_restrictScalars_iff (S := L) hcomap d _).mpr ha⟩

private theorem le_ker_algebraMap_of_isScalarTower
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] {I : Ideal R} (hI : I ≤ RingHom.ker (algebraMap R S)) :
    I ≤ RingHom.ker (algebraMap R T) := by
  intro x hx
  change algebraMap R T x = 0
  rw [IsScalarTower.algebraMap_apply R S T, hI hx, map_zero]

private theorem fiberDimension_away_le
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (s : S) (n : WithBot ℕ∞)
    (hdim : ∀ p : Spec (.of R), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤ n)
    (p : Spec (.of R)) : topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s)))).fiber p) ≤ n := by
  rw [IsScalarTower.algebraMap_eq R S (Localization.Away s)]
  exact (fiberDimension_comp_le_of_isInducing (algebraMap R S) (algebraMap S _)
    (PrimeSpectrum.localization_away_isOpenEmbedding _ s).isInducing p).trans (hdim p)

private theorem fiberDimension_quotient_le
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (J : Ideal S) (n : WithBot ℕ∞)
    (hdim : ∀ p : Spec (.of R), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤ n)
    (p : Spec (.of R)) : topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom (algebraMap R (S ⧸ J)))).fiber p) ≤ n := by
  rw [IsScalarTower.algebraMap_eq R S (S ⧸ J)]
  exact (fiberDimension_comp_le_of_isInducing (algebraMap R S) (Ideal.Quotient.mk J)
    (PrimeSpectrum.comap_isInducing_of_surjective _ _ Ideal.Quotient.mk_surjective) p).trans
      (hdim p)

private theorem exists_fiberDimension_aeval_le_of_noetherian_generic
    {R : Type u} [CommRing R] [IsNoetherianRing R] (d : ℕ)
    (hgeneric : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.FiniteType R T],
      (∀ p : Spec (.of R), topologicalKrullDim
        ((Spec.map (CommRingCat.ofHom (algebraMap R T))).fiber p) ≤
          ((d + 1 : ℕ) : WithBot ℕ∞)) →
      ∀ I : Ideal R, I.IsPrime → I ≤ RingHom.ker (algebraMap R T) →
      ∃ r ∉ I, ∃ a : Localization.Away (algebraMap R T r),
        ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
          ((AlgebraicGeometry.specMapAeval a).fiber p) ≤ (d : WithBot ℕ∞))
    {S : Type u} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (I : Ideal R) (hI : I ≤ RingHom.ker (algebraMap R S))
    (hdim : ∀ p : Spec (.of R), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
        ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ a : S, ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
      ((AlgebraicGeometry.specMapAeval a).fiber p) ≤ (d : WithBot ℕ∞) := by
  classical
  have : WellFoundedGT (Ideal R) :=
    IsNoetherian.wellFoundedGT (h := (inferInstance : IsNoetherian R R))
  have hwf : WellFounded ((· > ·) : Ideal R → Ideal R → Prop) := wellFounded_gt
  induction I using hwf.induction generalizing S with
  | h I ih =>
    by_cases htop : I = ⊤
    · have h1 : (1 : S) = 0 := by
        simpa using (hI (by simp [htop]) : algebraMap R S 1 = 0)
      have : Subsingleton S := subsingleton_of_zero_eq_one h1.symm
      exact exists_fiberDimension_aeval_le_of_subsingleton d
    have hsup (r : R) (hr : r ∉ I) : I < I ⊔ Ideal.span {r} := by
      refine lt_of_le_of_ne le_sup_left fun h ↦ hr ?_
      rw [h]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self r)
    have hloc : ∃ r ∉ I, ∃ a : Localization.Away (algebraMap R S r),
        ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
          ((AlgebraicGeometry.specMapAeval a).fiber p) ≤ (d : WithBot ℕ∞) := by
      by_cases hp : I.IsPrime
      · exact hgeneric S hdim I hp hI
      obtain htop' | ⟨r, hr, s, hs, hrs⟩ := Ideal.not_isPrime_iff.mp hp
      · exact (htop htop').elim
      let L := Localization.Away (algebraMap R S r)
      have hrL : IsUnit (algebraMap R L r) := by
        rw [IsScalarTower.algebraMap_apply R S L]
        exact IsLocalization.Away.algebraMap_isUnit (algebraMap R S r)
      have hIL : I ≤ RingHom.ker (algebraMap R L) := le_ker_algebraMap_of_isScalarTower hI
      have hsL : algebraMap R L s = 0 := by
        apply hrL.mul_left_cancel
        simpa only [mul_zero, ← map_mul] using
          (show algebraMap R L (r * s) = 0 from hIL hrs)
      have hker : I ⊔ Ideal.span {s} ≤ RingHom.ker (algebraMap R L) :=
        sup_le hIL ((Ideal.span_singleton_le_iff_mem _).mpr hsL)
      exact ⟨r, hr, ih (I ⊔ Ideal.span {s}) (hsup s hs) hker
        (fiberDimension_away_le (algebraMap R S r) _ hdim)⟩
    obtain ⟨r, hr, a, ha⟩ := hloc
    let J : Ideal S := Ideal.span {algebraMap R S r}
    let Q := S ⧸ J
    have hIQ : I ≤ RingHom.ker (algebraMap R Q) := le_ker_algebraMap_of_isScalarTower hI
    have hrQ : algebraMap R Q r = 0 := by
      rw [← Ideal.Quotient.mk_algebraMap R J, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by simp)
    have hker : I ⊔ Ideal.span {r} ≤ RingHom.ker (algebraMap R Q) :=
      sup_le hIQ ((Ideal.span_singleton_le_iff_mem _).mpr hrQ)
    exact exists_fiberDimension_aeval_le_of_away_and_quotient d r ⟨a, ha⟩
      (ih (I ⊔ Ideal.span {r}) (hsup r hr) hker (fiberDimension_quotient_le J _ hdim))

private theorem exists_fiberDimension_aeval_le_of_isNoetherianRing
    {R S : Type u} [CommRing R] [IsNoetherianRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ)
    (hdim : ∀ p : Spec (.of R), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
        ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ a : S, ∀ p : Spec (.of (Polynomial R)), topologicalKrullDim
      ((AlgebraicGeometry.specMapAeval a).fiber p) ≤ (d : WithBot ℕ∞) :=
  exists_fiberDimension_aeval_le_of_noetherian_generic d
    (fun _ _ _ _ hdimT I _ hI ↦ exists_fiberDimension_aeval_le_away_of_prime_ker d hdimT I hI)
    ⊥ bot_le hdim

private theorem exists_quasiFinite_mvPolynomial_of_isNoetherianRing
    {R S : Type u} [CommRing R] [IsNoetherianRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ)
    (hdim : ∀ p : Spec (.of R), topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
        (d : WithBot ℕ∞)) :
    ∃ φ : MvPolynomial (Fin d) R →ₐ[R] S,
      φ.toRingHom.FiniteType ∧ φ.toRingHom.QuasiFinite := by
  induction d generalizing R S with
  | zero => exact exists_quasiFinite_mvPolynomial_zero_of_fiberDimension_le hdim
  | succ d ih =>
    obtain ⟨a, ha⟩ := exists_fiberDimension_aeval_le_of_isNoetherianRing d hdim
    apply exists_quasiFinite_mvPolynomial_succ_of_polynomial d a
    let := (Polynomial.aeval (R := R) a).toRingHom.toAlgebra
    have : IsScalarTower R (Polynomial R) S :=
      IsScalarTower.of_algebraMap_eq fun r ↦ (Polynomial.aeval a).commutes r |>.symm
    have : Algebra.FiniteType (Polynomial R) S :=
      Algebra.FiniteType.of_restrictScalars_finiteType R (Polynomial R) S
    obtain ⟨φ, _, hφ⟩ := ih (R := Polynomial R) (S := S) ha
    exact ⟨φ, hφ⟩


/-- Extending the number of variables: a quasi-finite `R`-algebra map out of the polynomial ring
in `e` variables gives one out of the polynomial ring in `d ≥ e` variables, by sending the
surplus variables to zero. -/
private theorem exists_quasiFinite_mvPolynomial_of_le_nat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {e d : ℕ} (hed : e ≤ d)
    (h : ∃ φ : MvPolynomial (Fin e) R →ₐ[R] S,
      φ.toRingHom.FiniteType ∧ φ.toRingHom.QuasiFinite) :
    ∃ φ : MvPolynomial (Fin d) R →ₐ[R] S,
      φ.toRingHom.FiniteType ∧ φ.toRingHom.QuasiFinite := by
  obtain ⟨φ, hft, hqf⟩ := h
  exact exists_quasiFinite_mvPolynomial_of_le hed φ hft hqf

end WeakRelativeNoetherNormalization

namespace AlgebraicGeometry

open WeakRelativeNoetherNormalization

/-- **Stacks Project, Tag 0GTG**, with the maximum of the fibre dimensions written as a bound on
the dimension of each scheme-theoretic fibre of `Spec S ⟶ Spec R`: for a finite type ring map
`R → S` whose fibres all have dimension at most `d`, there is a quasi-finite `R`-algebra map from
the polynomial ring in `d` variables to `S`. -/
public theorem exists_quasiFinite_mvPolynomial_of_forall_topologicalKrullDim_fiber_le
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ)
    (hdim : ∀ p : Spec (.of R),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
        (d : WithBot ℕ∞)) :
    ∃ φ : MvPolynomial (Fin d) R →ₐ[R] S,
      φ.toRingHom.FiniteType ∧ φ.toRingHom.QuasiFinite := by
  obtain ⟨A, hA, hmodel⟩ : ∃ A : Subalgebra ℤ R, A.FG ∧
      (∃ B : Subalgebra A S, B.FG ∧ Algebra.adjoin R (B : Set S) = ⊤ ∧
         ∀ p : Spec (.of A), topologicalKrullDim
           ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber p) ≤
             (d : WithBot ℕ∞)) := by
    obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R S).FG)
    obtain ⟨i, hi⟩ := exists_coefficient_stage_fiberDimension_le s hs d hdim
    exact ⟨coefficientSubalgebra (RingHom.id R) ∅ i,
      coefficientSubalgebra_fg _ Set.finite_empty i,
      coefficientAlgebra (R := R) (s : Set S) i,
      coefficientAlgebra_fg s.finite_toSet i, coefficientAlgebra_adjoin_eq_top hs i, hi⟩
  have : Algebra.FiniteType ℤ A := ⟨(Subalgebra.fg_top A).mpr hA⟩
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  obtain ⟨B, hB, hgen, hdimB⟩ := hmodel
  have : Algebra.FiniteType A B := ⟨(Subalgebra.fg_top B).mpr hB⟩
  obtain ⟨φ, _, hφ⟩ := exists_quasiFinite_mvPolynomial_of_isNoetherianRing d hdimB
  exact exists_quasiFinite_mvPolynomial_of_adjoin_eq_top B hgen d ⟨φ, hφ⟩

/-- Conversely, a quasi-finite `R`-algebra map from the polynomial ring in `d` variables to `S`
bounds the dimension of every fibre of `Spec S ⟶ Spec R` by `d`. -/
public alias forall_topologicalKrullDim_fiber_le_of_quasiFinite_mvPolynomial :=
  WeakRelativeNoetherNormalization.fiberDimension_le_of_quasiFinite_mvPolynomial

end AlgebraicGeometry

namespace WeakRelativeNoetherNormalization

/-- Weak relative Noether normalization: a uniform bound on the dimensions of fibres
gives a quasi-finite morphism from `Spec(S)` to affine space of that dimension over `Spec(R)`. -/
private alias exists_quasiFinite_mvPolynomial_of_fiberDimension_le :=
  AlgebraicGeometry.exists_quasiFinite_mvPolynomial_of_forall_topologicalKrullDim_fiber_le

end WeakRelativeNoetherNormalization

namespace Algebra

open WeakRelativeNoetherNormalization

/-- A bound on the relative dimension `dim(S/R)` of Tag 00QD is the same thing as a bound on the
dimension of every scheme-theoretic fibre of `Spec S ⟶ Spec R`. -/
public theorem relativeDimension_le_natCast_iff_forall_topologicalKrullDim_fiber_le
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (d : ℕ) :
    Algebra.relativeDimension R S ≤ (d : WithBot ℕ∞) ↔
      ∀ p : Spec (.of R),
        topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
          (d : WithBot ℕ∞) := by
  rw [Algebra.relativeDimension, iSup_le_iff]
  refine ⟨fiberDimension_le_of_relativeDimensionAt_le d, fun h q ↦ ?_⟩
  have := q.isPrime
  exact relativeDimensionAt_le_of_fiberDimension_le d h q

/-- **Stacks Project, Tag 0GTG.** Let `R → S` be a finite type ring map and let `d` bound the
maximum `Algebra.relativeDimension R S` of the dimensions of the fibres of `Spec S → Spec R`.
Then there is a quasi-finite `R`-algebra map `R[t_1, …, t_d] → S`. -/
@[stacks 0GTG "The maximum of the dimensions of the fibres is `Algebra.relativeDimension R S`
(Tag 00QD) and is bounded by, rather than equal to, the natural number `d`; the two are
equivalent, and the inequality is what covers `Spec S = ∅`, where the maximum is `⊥`.
Quasi-finiteness is Mathlib's `RingHom.QuasiFinite`, which asks only for finite fibres, so the
finite type of the map is a separate conjunct."]
public theorem exists_quasiFinite_mvPolynomial_of_relativeDimension_le
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ)
    (hd : Algebra.relativeDimension R S ≤ (d : WithBot ℕ∞)) :
    ∃ φ : MvPolynomial (Fin d) R →ₐ[R] S,
      φ.toRingHom.FiniteType ∧ φ.toRingHom.QuasiFinite :=
  exists_quasiFinite_mvPolynomial_of_fiberDimension_le d
    ((relativeDimension_le_natCast_iff_forall_topologicalKrullDim_fiber_le d).mp hd)

/-- **Stacks Project, Tag 0GTG**, in the source's form: `d` *is* the maximum of the dimensions of
the fibres of `Spec S → Spec R`. -/
@[stacks 0GTG "The source's form, with `d` equal to the maximum
`Algebra.relativeDimension R S` (Tag 00QD) of the dimensions of the fibres. Quasi-finiteness is
Mathlib's `RingHom.QuasiFinite`, which asks only for finite fibres, so the finite type of the map
is a separate conjunct."]
public theorem exists_quasiFinite_mvPolynomial_of_relativeDimension_eq
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ)
    (hd : Algebra.relativeDimension R S = (d : WithBot ℕ∞)) :
    ∃ φ : MvPolynomial (Fin d) R →ₐ[R] S,
      φ.toRingHom.FiniteType ∧ φ.toRingHom.QuasiFinite :=
  exists_quasiFinite_mvPolynomial_of_relativeDimension_le d hd.le

/-- The bound on the relative dimension is *equivalent* to the existence of the quasi-finite map,
so the conclusion of Tag 0GTG is not satisfiable for free: a quasi-finite `R`-algebra map out of
the polynomial ring in `d` variables exists exactly when the fibres of `Spec S → Spec R` have
dimension at most `d`. -/
public theorem relativeDimension_le_iff_exists_quasiFinite_mvPolynomial
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ) :
    Algebra.relativeDimension R S ≤ (d : WithBot ℕ∞) ↔
      ∃ φ : MvPolynomial (Fin d) R →ₐ[R] S,
        φ.toRingHom.FiniteType ∧ φ.toRingHom.QuasiFinite :=
  ⟨exists_quasiFinite_mvPolynomial_of_relativeDimension_le d, fun ⟨φ, _, hqf⟩ ↦
    (relativeDimension_le_natCast_iff_forall_topologicalKrullDim_fiber_le d).mpr
      (fiberDimension_le_of_quasiFinite_mvPolynomial d φ hqf)⟩

end Algebra

end
