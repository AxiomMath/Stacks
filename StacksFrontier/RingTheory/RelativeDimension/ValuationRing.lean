module

public import StacksFrontier.RingTheory.RelativeDimension.Semicontinuity
import all StacksFrontier.RingTheory.RelativeDimension.Semicontinuity
import StacksFrontier.RingTheory.RelativeDimension.QuasiFinite
public import StacksFrontier.Topology.Dimension.Equidimensional
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.RingTheory.RelativeDimension.QuasiFiniteAffineSpace

@[expose] public section

/-!
# Special and generic fibre of a domain of finite type over a valuation ring

Let `R` be a valuation ring with residue field `k = κ(𝔪_R)` and fraction field `K = κ(⊥)`, and
let `S` be a domain containing `R` which is of finite type over `R`.  This file proves Stacks
00QK: if the special fibre `S ⊗_R k` is nonzero then it has the same Krull dimension as the
generic fibre `S ⊗_R K`, and `Spec (S ⊗_R k)` is equidimensional.

Both assertions come from one computation: the *local* dimension of `Spec (S ⊗_R k)` is
`dim (S ⊗_R K)` at every one of its points.  Indeed the dimension of a space is the supremum of
its local dimensions (Stacks 0B7I), which gives the equality of dimensions, and a space all of
whose local dimensions agree and which has finitely many irreducible components is
equidimensional, because each component contains a nonempty open subset of the whole space.

Fix a point of the special fibre, that is a prime `𝔮` of `S` containing `𝔪_R S`, and let
`n = dim_𝔮(S/R)` be the relative dimension there (Stacks 00QD).

*`n ≥ dim (S ⊗_R K)`.*  By upper semicontinuity of the relative dimension (Lemma 00QH) the set
`{𝔮' | dim_{𝔮'}(S/R) ≤ n}` is open, and it contains `𝔮`.  As `S` is a domain, `Spec S` is
irreducible with generic point `(0)`, which therefore lies in every nonempty open set; so
`dim_{(0)}(S/R) ≤ n`.  Now `(0)` is a point of the generic fibre, and it is the *generic* point
of that fibre, so the local dimension of `Spec (S ⊗_R K)` there is the dimension of the whole of
`Spec (S ⊗_R K)`: the generic fibre is a domain of finite type over the field `K`, whence
`dim_{(0)}(S ⊗_R K) = ht(0) + trdeg_K κ((0)) = dim (S ⊗_R K)` by Lemmas 00P1 and 00P0.

*`n ≤ dim (S ⊗_R K)`.*  Here the valuation ring enters.  After inverting one `g ∉ 𝔮` the algebra
`S` becomes quasi-finite over `R[t_1, …, t_n]` (Lemma 00QE).  Were `dim (S ⊗_R K) < n`, the map
`K[t_1, …, t_n] → S ⊗_R K` would have a nonzero kernel; dividing an element `f = ∑_I a_I t^I` of
that kernel by a coefficient of minimal valuation puts `f` in `R[t_1, …, t_n]` with one
coefficient a unit, so its image in `k[t_1, …, t_n]` is nonzero and dies in `S ⊗_R k`.  Then
`k[t_1, …, t_n] → S ⊗_R k` has a nonzero kernel, and since it is quasi-finite this forces
`dim (S ⊗_R k) < n`, contradicting `n ≤ dim (S ⊗_R k)`.

## Main results

* `Stacks.RelativeDimension.ValuationFibres.solution`: Stacks 00QK.

## Implementation notes

*The fibre is used both as a ring and as a subspace of `Spec S`.*  `Algebra.relativeDimensionAt`
(Stacks 00QD) is the local dimension of the fibre realized as the subspace
`comap (algebraMap R S) ⁻¹' {𝔭}` of `Spec S`, while the statement of this tag speaks of the ring
`𝔭.Fiber S`.  `relativeDimensionAt_eq_localKrullDim` identifies the two along
`PrimeSpectrum.preimageHomeomorphFiber`, and is what lets Lemma 00QH be applied to a point of
`Spec (S ⊗_R k)`.

## References

* [StacksProject 00QK](https://stacks.math.columbia.edu/tag/00QK)
* [StacksProject 00QD](https://stacks.math.columbia.edu/tag/00QD)
* [StacksProject 00QE](https://stacks.math.columbia.edu/tag/00QE)
* [StacksProject 00QH](https://stacks.math.columbia.edu/tag/00QH)
* [StacksProject 00P0](https://stacks.math.columbia.edu/tag/00P0)
* [StacksProject 00P1](https://stacks.math.columbia.edu/tag/00P1)
* [StacksProject 0B7I](https://stacks.math.columbia.edu/tag/0B7I)
-/

@[expose] public section

open TopologicalSpace

open scoped TensorProduct

attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace Stacks.RelativeDimension.ValuationFibres

/-! ### Facts about `WithBot ℕ∞` and local dimension -/

/-- A nonnegative element of `WithBot ℕ∞` other than `⊤` is a natural number. -/
private theorem exists_nat_eq {x : WithBot ℕ∞} (h0 : 0 ≤ x) (htop : x ≠ ⊤) :
    ∃ m : ℕ, x = (m : WithBot ℕ∞) := by
  cases x with
  | bot => exact absurd (le_bot_iff.mp h0) (by simp)
  | coe a =>
    cases a with
    | top => exact absurd rfl htop
    | coe b => exact ⟨b, rfl⟩

/-- The dimension of a space at a point is nonnegative: every open neighbourhood of the point is
nonempty, hence of dimension `≠ -∞`. -/
private theorem zero_le_localKrullDim {X : Type*} [TopologicalSpace X] (x : X) :
    0 ≤ localKrullDim X x := by
  rw [localKrullDim]
  refine le_iInf fun U ↦ le_iInf fun hU ↦ le_iInf fun hxU ↦
    Stacks.RelativeDimension.Semicontinuity.zero_le_of_ne_bot ?_
  rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
  exact fun h ↦ h.elim ⟨x, hxU⟩

/-- The dimension of a point of `X` is at most the dimension of any open subset of `X`
containing it. -/
private theorem localKrullDim_le_of_isOpen {X : Type*} [TopologicalSpace X] {U : Set X}
    (hU : IsOpen U) {x : X} (hx : x ∈ U) : localKrullDim X x ≤ topologicalKrullDim U := by
  rw [localKrullDim]
  exact iInf_le_of_le U (iInf_le_of_le hU (iInf_le _ hx))

/-- An element of `WithBot ℕ∞` whose successor is bounded by a natural number is below it. -/
private theorem lt_of_add_one_le {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  cases x with
  | bot => exact bot_lt_iff_ne_bot.mpr (by simp)
  | coe a =>
    cases a with
    | top =>
      rw [show ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) by norm_cast,
        show ((n : ℕ) : WithBot ℕ∞) = (((n : ℕ) : ℕ∞) : WithBot ℕ∞) by norm_cast] at h
      simp only [WithBot.coe_le_coe, top_le_iff, ENat.natCast_ne_top] at h
    | coe b =>
      rw [show ((((b : ℕ) : ℕ∞) : WithBot ℕ∞)) + 1 = ((((b + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) by
        push_cast; ring, show ((n : ℕ) : WithBot ℕ∞) = (((n : ℕ) : ℕ∞) : WithBot ℕ∞) by
        norm_cast] at h
      simp only [WithBot.coe_le_coe, Nat.cast_le] at h ⊢
      exact_mod_cast Nat.lt_of_succ_le h

/-- The dimension of a space at a point is at most the dimension of the space, the latter being
the supremum of the former (Stacks 0B7I). -/
@[ega "0 14.1.6" "partial"]
private theorem localKrullDim_le_topologicalKrullDim {X : Type*} [TopologicalSpace X] (x : X) :
    localKrullDim X x ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  exact le_iSup (fun y ↦ localKrullDim X y) x


/-! ### Constant local dimension implies equidimensionality -/

/-- A space with finitely many irreducible components whose local dimension is the same at every
point is equidimensional (Definition 0058), and every irreducible component has that common
dimension.

Each component `Z` contains the open set `U` complementary to the union of the other components,
and `U` is nonempty because its closure is `Z`; so `d = dim_x X ≤ dim U ≤ dim Z` for `x ∈ U`,
while `dim Z ≤ dim X = ⨆_x dim_x X = d`. -/
private theorem topologicalKrullDim_eq_of_localKrullDim_eq {X : Type*} [TopologicalSpace X]
    (hfin : (irreducibleComponents X).Finite) {d : WithBot ℕ∞}
    (h : ∀ x : X, localKrullDim X x = d) {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    topologicalKrullDim Z = d := by
  set U : Set X := (⋃₀ (irreducibleComponents X \ {Z}))ᶜ with hUdef
  have hUopen : IsOpen U := by
    rw [hUdef, Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have hUZ : U ⊆ Z := by
    rw [hUdef]
    intro y hy
    have hy' : y ∈ ⋃₀ irreducibleComponents X := by
      rw [sUnion_irreducibleComponents]; trivial
    obtain ⟨W, hW, hyW⟩ := hy'
    by_cases hWZ : W = Z
    · exact hWZ ▸ hyW
    · exact absurd (show y ∈ ⋃₀ (irreducibleComponents X \ {Z}) from ⟨W, ⟨hW, hWZ⟩, hyW⟩) hy
  have hUne : U.Nonempty := by
    rcases Set.eq_empty_or_nonempty U with he | hne
    · have hcl := closure_sUnion_irreducibleComponents_sdiff_singleton hfin Z hZ
      rw [← hUdef, he, closure_empty] at hcl
      exact absurd hZ.1.nonempty (by rw [← hcl]; simp)
    · exact hne
  obtain ⟨x, hxU⟩ := hUne
  have hX : Nonempty X := ⟨x⟩
  have hdimX : topologicalKrullDim X = d := by
    rw [topologicalKrullDim_eq_iSup_localKrullDim]
    simp only [h]
    exact iSup_const
  refine le_antisymm ?_ ?_
  · exact (topologicalKrullDim_subspace_le X Z).trans hdimX.le
  · calc d = localKrullDim X x := (h x).symm
      _ ≤ topologicalKrullDim U := localKrullDim_le_of_isOpen hUopen hxU
      _ ≤ topologicalKrullDim Z :=
          (Topology.IsEmbedding.inclusion hUZ).isInducing.topologicalKrullDim_le

/-! ### The relative dimension at a prime, read on the fibre ring -/

/-- The relative dimension `dim_𝔮(S/R)` of Stacks 00QD, read on the fibre ring: for a point `z`
of the fibre of `Spec S → Spec R` over `𝔭`, it is the local dimension of
`Spec (S ⊗_R κ(𝔭))` at the corresponding point.

The two spaces are `PrimeSpectrum.preimageHomeomorphFiber` apart and the point at which the
dimension is taken corresponds under that homeomorphism. -/
private theorem relativeDimensionAt_eq_localKrullDim {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (𝔭 : PrimeSpectrum R)
    (z : ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {𝔭})) :
    Algebra.relativeDimensionAt R (z : PrimeSpectrum S).asIdeal
      = localKrullDim (PrimeSpectrum (𝔭.asIdeal.Fiber S))
          (PrimeSpectrum.preimageHomeomorphFiber R S 𝔭 z) := by
  obtain ⟨q, hq⟩ := z
  subst hq
  rw [Algebra.relativeDimensionAt, topologicalKrullDimAt_eq_of_homeomorph
    (PrimeSpectrum.preimageHomeomorphFiber R S (PrimeSpectrum.comap (algebraMap R S) q)),
    topologicalKrullDimAt_eq_localKrullDim]

/-- Every point of the fibre ring `Spec (S ⊗_R κ(𝔭))` has the local dimension of a point `z` of
`Spec S` lying over `𝔭`, namely the relative dimension of `S/R` at `z`. -/
private theorem exists_mem_fibre_relativeDimensionAt_eq {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (𝔭 : PrimeSpectrum R) (x : PrimeSpectrum (𝔭.asIdeal.Fiber S)) :
    ∃ z : PrimeSpectrum S, z ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹' {𝔭} ∧
      Algebra.relativeDimensionAt R z.asIdeal = localKrullDim _ x := by
  set e := PrimeSpectrum.preimageHomeomorphFiber R S 𝔭
  refine ⟨(e.symm x).1, (e.symm x).2, ?_⟩
  rw [relativeDimensionAt_eq_localKrullDim 𝔭 (e.symm x), e.apply_symm_apply]

/-! ### The generic fibre and its generic point -/

/-- The generic point `(0)` of the spectrum of a domain is dense. -/
private theorem dense_singleton_bot (A : Type*) [CommRing A] [IsDomain A] :
    Dense ({(⟨⊥, inferInstance⟩ : PrimeSpectrum A)} : Set (PrimeSpectrum A)) := by
  rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
  simp

/-- The dimension of `Spec A` at the generic point `(0)` of a domain `A` is at most its dimension
at any other point: the generic point lies in every nonempty open set, so the infimum defining the
dimension at `(0)` ranges over at least the open sets the one at `y` ranges over. -/
private theorem localKrullDim_bot_le {A : Type*} [CommRing A] [IsDomain A] (y : PrimeSpectrum A) :
    localKrullDim (PrimeSpectrum A) ⟨⊥, inferInstance⟩ ≤ localKrullDim (PrimeSpectrum A) y := by
  rw [localKrullDim]
  refine le_iInf fun U ↦ le_iInf fun hU ↦ le_iInf fun hyU ↦ ?_
  obtain ⟨p, hp1, hp2⟩ := (dense_singleton_bot A).inter_open_nonempty U hU ⟨y, hyU⟩
  rw [Set.mem_singleton_iff] at hp2
  exact localKrullDim_le_of_isOpen hU (hp2 ▸ hp1)

/-- For a domain `A` of finite type over a field `κ`, the dimension of `Spec A` at a point is at
least `dim A` — hence, `topologicalKrullDim` being the supremum of the local dimensions, exactly
`dim A` at every point.

At the generic point `(0)` Lemma 00P1 evaluates the local dimension as
`ht(0) + trdeg_κ κ((0)) = 0 + trdeg_κ Frac A`, which is `dim A` by Lemma 00P0; a general point is
handled by `localKrullDim_bot_le`. -/
private theorem ringKrullDim_le_localKrullDim {κ A : Type*} [Field κ] [CommRing A] [IsDomain A]
    [Algebra κ A] [Algebra.FiniteType κ A] (y : PrimeSpectrum A) :
    ringKrullDim A ≤ localKrullDim (PrimeSpectrum A) y := by
  refine le_trans ?_ (localKrullDim_bot_le y)
  rw [PrimeSpectrum.localKrullDim_eq_height_add_trdeg_residueField κ
      (⟨⊥, inferInstance⟩ : PrimeSpectrum A),
    (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{_, _, _, 0} κ A
      ((⊥ : Ideal A).ResidueField)).1]
  simp

/-- For a domain `S` containing a domain `R`, the image of the nonzero elements of `R` consists of
nonzerodivisors of `S`. -/
private theorem algebraMapSubmonoid_nonZeroDivisors_le {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S] :
    Algebra.algebraMapSubmonoid S (nonZeroDivisors R) ≤ nonZeroDivisors S := by
  rintro x ⟨r, hr, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero fun h ↦ ?_
  exact (mem_nonZeroDivisors_iff_ne_zero.mp hr)
    (FaithfulSMul.algebraMap_injective R S (by simpa using h))

/-- If `M` consists of nonzerodivisors of a domain `S`, any localization `T` of `S` at `M` is
compatible with a fraction field `L` of `S`, and `L` is a fraction field of `T`. -/
private theorem exists_algebra_isFractionRing_of_le_nonZeroDivisors {S T L : Type*} [CommRing S]
    [IsDomain S] [CommRing T] [Algebra S T] [Field L] [Algebra S L] [IsFractionRing S L]
    {M : Submonoid S} [IsLocalization M T] (hM : M ≤ nonZeroDivisors S) :
    ∃ _ : Algebra T L, IsScalarTower S T L ∧ IsFractionRing T L := by
  have hunit : ∀ y : M, IsUnit (algebraMap S L (y : S)) := fun y ↦
    isUnit_iff_ne_zero.mpr fun h ↦ (mem_nonZeroDivisors_iff_ne_zero.mp (hM y.2))
      (IsFractionRing.injective S L (by simpa using h))
  let : Algebra T L := (IsLocalization.lift (M := M) (g := algebraMap S L) hunit).toAlgebra
  have : IsScalarTower S T L :=
    IsScalarTower.of_algebraMap_eq fun s ↦ (IsLocalization.lift_eq hunit s).symm
  exact ⟨inferInstance, ‹_›, IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M T L⟩

/-- The generic fibre `S ⊗_R K` of a domain `S` containing a domain `R` is a domain: it is the
localization of `S` at the image of `R \ {0}`, a set of nonzerodivisors of `S`. -/
theorem isDomain_fiber_bot {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] [Algebra R S] [FaithfulSMul R S] : IsDomain ((⊥ : Ideal R).Fiber S) := by
  let : Algebra S ((⊥ : Ideal R).Fiber S) :=
    Algebra.TensorProduct.rightAlgebra (R := R) (A := (⊥ : Ideal R).ResidueField) (B := S)
  have : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))
      ((⊥ : Ideal R).Fiber S) :=
    IsLocalization.tensorRight ((⊥ : Ideal R).ResidueField) (nonZeroDivisors R)
  exact IsLocalization.isDomain_of_le_nonZeroDivisors _
    (algebraMapSubmonoid_nonZeroDivisors_le (R := R) (S := S))

/-- For a domain `S` of finite type over a domain `R` with `R → S` injective, the dimension of
the generic fibre `Spec (S ⊗_R K)` is at most the relative dimension of `S/R` at `(0)`.

The prime `(0)` of `S` lies over `(0)` of `R` because `R → S` is injective, so it is a point of
the generic fibre; the generic fibre is a domain of finite type over the field `K = κ(⊥)`, and the
dimension of such a spectrum at any of its points is the dimension of the whole
(`ringKrullDim_le_localKrullDim`). -/
private theorem ringKrullDim_fiber_bot_le_relativeDimensionAt_bot {R S : Type*} [CommRing R]
    [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]
    [Algebra.FiniteType R S] :
    ringKrullDim ((⊥ : Ideal R).Fiber S)
      ≤ Algebra.relativeDimensionAt R (⊥ : Ideal S) := by
  let := isDomain_fiber_bot (R := R) (S := S)
  have hz : PrimeSpectrum.comap (algebraMap R S) (⟨⊥, inferInstance⟩ : PrimeSpectrum S)
      ∈ ({⟨⊥, inferInstance⟩} : Set (PrimeSpectrum R)) := by
    simp only [Set.mem_singleton_iff]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap R S) ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot, RingHom.ker_eq_bot_iff_eq_zero]
    exact fun x hx ↦ FaithfulSMul.algebraMap_injective R S (by simpa using hx)
  exact le_of_le_of_eq
    (ringKrullDim_le_localKrullDim (κ := (⊥ : Ideal R).ResidueField) _)
    (relativeDimensionAt_eq_localKrullDim (⟨⊥, inferInstance⟩ : PrimeSpectrum R)
      ⟨⟨⊥, inferInstance⟩, hz⟩).symm

/-- If `m` elements of a fraction field of `S` are algebraically independent over a domain `R`
contained in `S`, then the generic fibre `S ⊗_R K` has dimension at least `m`.

The generic fibre is a domain of finite type over `K = κ(⊥)`, and `L` is a fraction field of it as
well, being a fraction field of `S` and `S ⊗_R K` a localization of `S`; so its dimension is
`trdeg_K L` by Lemma 00P0.  Algebraic independence over `R` upgrades to algebraic independence
over `K` because `K` is algebraic over `R`, and an algebraically independent family of `m`
elements bounds the transcendence degree from below. -/
@[ega "IV 5.6.5" "partial"]
private theorem le_ringKrullDim_fiber_bot_of_algebraicIndependent {R S L : Type*} [CommRing R]
    [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]
    [Algebra.FiniteType R S] [Field L] [Algebra S L] [IsFractionRing S L] [Algebra R L]
    [IsScalarTower R S L] {m : ℕ} {x : Fin m → L} (hx : AlgebraicIndependent R x) :
    (m : WithBot ℕ∞) ≤ ringKrullDim ((⊥ : Ideal R).Fiber S) := by
  have hRS : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective R S
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R S L]
    exact (IsFractionRing.injective S L).comp hRS
  -- `K = κ(⊥)` is the fraction field of `R`, so it maps to `L`
  let : Algebra (⊥ : Ideal R).ResidueField L := (IsFractionRing.lift (A := R) hRL).toAlgebra
  have : IsScalarTower R (⊥ : Ideal R).ResidueField L :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (IsFractionRing.lift_algebraMap hRL r).symm
  have : Algebra.IsAlgebraic R (⊥ : Ideal R).ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors R)
  have hcard : (m : Cardinal) ≤ Algebra.trdeg (⊥ : Ideal R).ResidueField L := by
    simpa using (hx.extendScalars (⊥ : Ideal R).ResidueField).lift_cardinalMk_le_trdeg
  -- the generic fibre is a localization of `S`, hence has `L` as a fraction field
  let : Algebra S ((⊥ : Ideal R).Fiber S) :=
    Algebra.TensorProduct.rightAlgebra (R := R) (A := (⊥ : Ideal R).ResidueField) (B := S)
  have : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))
      ((⊥ : Ideal R).Fiber S) :=
    IsLocalization.tensorRight ((⊥ : Ideal R).ResidueField) (nonZeroDivisors R)
  have := isDomain_fiber_bot (R := R) (S := S)
  obtain ⟨_, _, _⟩ := exists_algebra_isFractionRing_of_le_nonZeroDivisors (L := L)
    (T := (⊥ : Ideal R).Fiber S) (algebraMapSubmonoid_nonZeroDivisors_le (R := R) (S := S))
  have : IsScalarTower (⊥ : Ideal R).ResidueField ((⊥ : Ideal R).Fiber S) L := by
    refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext (nonZeroDivisors R) ?_)
    refine RingHom.ext fun r ↦ ?_
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R (⊥ : Ideal R).ResidueField L r,
      ← IsScalarTower.algebraMap_apply R (⊥ : Ideal R).ResidueField ((⊥ : Ideal R).Fiber S) r,
      IsScalarTower.algebraMap_apply R S ((⊥ : Ideal R).Fiber S) r,
      ← IsScalarTower.algebraMap_apply S ((⊥ : Ideal R).Fiber S) L,
      ← IsScalarTower.algebraMap_apply R S L]
  rw [(ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{_, _, _, 0}
    (⊥ : Ideal R).ResidueField ((⊥ : Ideal R).Fiber S) L).1]
  have h : (m : ℕ∞) ≤ Cardinal.toENat (Algebra.trdeg (⊥ : Ideal R).ResidueField L) := by
    calc (m : ℕ∞) = Cardinal.toENat (m : Cardinal) := by simp
      _ ≤ _ := OrderHomClass.mono Cardinal.toENat hcard
  exact_mod_cast h

/-! ### Lemma 00QH gives the lower bound on the special fibre -/

/-- Every point of the special fibre has local dimension at least `dim (S ⊗_R K)`.

Upper semicontinuity of the relative dimension (Lemma 00QH) makes
`{𝔮' | dim_{𝔮'}(S/R) ≤ n}` an open neighbourhood of the given point, where `n` is its local
dimension; `Spec S` is irreducible because `S` is a domain, so that open set contains the generic
point `(0)`, and the relative dimension there is `dim (S ⊗_R K)`. -/
private theorem ringKrullDim_fiber_bot_le_localKrullDim {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S] [Algebra.FiniteType R S]
    (𝔭 : Ideal R) [𝔭.IsPrime] (x : PrimeSpectrum (𝔭.Fiber S)) :
    ringKrullDim ((⊥ : Ideal R).Fiber S) ≤ localKrullDim (PrimeSpectrum (𝔭.Fiber S)) x := by
  obtain ⟨z, -, hxz⟩ := exists_mem_fibre_relativeDimensionAt_eq (S := S) ⟨𝔭, ‹_›⟩ x
  rw [← hxz]
  set n := Algebra.relativeDimensionAt R z.asIdeal
  have h0 : 0 ≤ n := by
    rw [hxz]
    exact zero_le_localKrullDim _
  rcases eq_or_ne n ⊤ with htop | htop
  · rw [htop]; exact le_top
  obtain ⟨m, hm⟩ := exists_nat_eq h0 htop
  have hopen : IsOpen {𝔮 : PrimeSpectrum S |
      Algebra.relativeDimensionAt R 𝔮.asIdeal ≤ (m : WithBot ℕ∞)} :=
    Algebra.isOpen_setOf_relativeDimensionAt_le m
  have hmem : z ∈ {𝔮 : PrimeSpectrum S |
      Algebra.relativeDimensionAt R 𝔮.asIdeal ≤ (m : WithBot ℕ∞)} := hm.le
  obtain ⟨p, hp1, hp2⟩ := (dense_singleton_bot S).inter_open_nonempty _ hopen ⟨_, hmem⟩
  rw [Set.mem_singleton_iff] at hp2
  subst hp2
  calc ringKrullDim ((⊥ : Ideal R).Fiber S)
      ≤ Algebra.relativeDimensionAt R (⊥ : Ideal S) :=
        ringKrullDim_fiber_bot_le_relativeDimensionAt_bot
    _ ≤ (m : WithBot ℕ∞) := hp1
    _ = n := hm.symm

/-! ### Dividing by a coefficient of minimal valuation -/

/-- In a valuation ring divisibility is total, so a nonempty finite set has a member dividing all
of its members. -/
private theorem exists_dvd_of_finset {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    {s : Finset R} (hs : s.Nonempty) : ∃ a ∈ s, ∀ b ∈ s, a ∣ b := by
  classical
  have htot := ValuationRing.iff_dvd_total.mp ‹ValuationRing R›
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, by simp, by simp⟩
  | cons a s ha _ ih =>
    obtain ⟨c, hcs, hc⟩ := ih
    rcases htot.total a c with h | h
    · refine ⟨a, Finset.mem_cons_self .., fun b hb ↦ ?_⟩
      rcases Finset.mem_cons.mp hb with rfl | hb
      · exact dvd_rfl
      · exact h.trans (hc b hb)
    · refine ⟨c, Finset.mem_cons_of_mem hcs, fun b hb ↦ ?_⟩
      rcases Finset.mem_cons.mp hb with rfl | hb
      · exact h
      · exact hc b hb

/-- Over a valuation ring a nonzero polynomial becomes, after dividing by a coefficient of
minimal valuation, a polynomial one of whose coefficients is `1`.

Divisibility in a valuation ring is total, so among the finitely many nonzero coefficients of `f`
there is one, `a`, dividing all the others; then `f = a • g` with `g` the polynomial of the
quotients, whose coefficient in the degree where `f` had `a` is `1`. -/
private theorem exists_smul_eq_coeff_one_of_valuationRing {R σ : Type*} [CommRing R]
    [IsDomain R] [ValuationRing R] {f : MvPolynomial σ R} (hf : f ≠ 0) :
    ∃ (a : R) (g : MvPolynomial σ R) (i : σ →₀ ℕ), a ≠ 0 ∧ f = a • g ∧ g.coeff i = 1 := by
  classical
  obtain ⟨a, hamem, hadvd⟩ :=
    exists_dvd_of_finset (s := f.support.image f.coeff) (by
      simpa using MvPolynomial.support_nonempty.mpr hf)
  obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.mp hamem
  have ha0 : f.coeff i₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hi₀
  have hdvd : ∀ i, f.coeff i₀ ∣ f.coeff i := by
    intro i
    by_cases hi : i ∈ f.support
    · exact hadvd _ (Finset.mem_image_of_mem _ hi)
    · simp [MvPolynomial.notMem_support_iff.mp hi]
  set c : (σ →₀ ℕ) → R := fun i ↦ (hdvd i).choose with hc
  have hcmul : ∀ i, f.coeff i₀ * c i = f.coeff i := fun i ↦ (hdvd i).choose_spec.symm
  refine ⟨f.coeff i₀, ∑ i ∈ f.support, MvPolynomial.monomial i (c i), i₀, ha0, ?_, ?_⟩
  · conv_lhs => rw [MvPolynomial.as_sum f]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, hcmul i]
  · rw [MvPolynomial.coeff_sum,
      Finset.sum_eq_single_of_mem i₀ hi₀ fun b _ hb ↦ by
        simp [MvPolynomial.coeff_monomial, hb]]
    have hone : c i₀ = 1 := mul_left_cancel₀ ha0 (by rw [hcmul i₀, mul_one])
    simp [MvPolynomial.coeff_monomial, hone]

/-- An algebra which is quasi-finite over a polynomial ring `κ[t_i ; i ∈ σ]` in finitely many
variables over a field, and in which some nonzero polynomial dies, has dimension `< #σ`.

The algebra is an algebra over `κ[t_i]/(f)`, and `Spec` of it maps strictly monotonically to
`Spec (κ[t_i]/(f))` because the fibres of a quasi-finite map are discrete
(`Algebra.QuasiFinite.eq_of_le_of_under_eq`); and `f` being a nonzerodivisor,
`dim κ[t_i]/(f) + 1 ≤ dim κ[t_i] = #σ`. -/
private theorem ringKrullDim_lt_natCard_of_quasiFinite_of_mem_ker {κ : Type*} [Field κ]
    {σ C : Type*} [Finite σ] [CommRing C] [Algebra (MvPolynomial σ κ) C]
    [Algebra.QuasiFinite (MvPolynomial σ κ) C] {f : MvPolynomial σ κ} (hf : f ≠ 0)
    (h0 : algebraMap (MvPolynomial σ κ) C f = 0) :
    ringKrullDim C < (Nat.card σ : WithBot ℕ∞) := by
  have hker : ∀ a ∈ Ideal.span {f}, algebraMap (MvPolynomial σ κ) C a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [h0]
  have hcomp : (algebraMap (MvPolynomial σ κ) C)
      = (Ideal.Quotient.lift (Ideal.span {f}) (algebraMap (MvPolynomial σ κ) C) hker).comp
          (Ideal.Quotient.mk (Ideal.span {f})) := RingHom.ext fun a ↦ rfl
  have hsm : StrictMono (PrimeSpectrum.comap
      (Ideal.Quotient.lift (Ideal.span {f}) (algebraMap (MvPolynomial σ κ) C) hker)) :=
    fun p q hpq ↦ lt_of_le_of_ne (Ideal.comap_mono hpq.le) fun h ↦ hpq.ne <| PrimeSpectrum.ext <|
      Algebra.QuasiFinite.eq_of_le_of_under_eq (R := MvPolynomial σ κ) p.asIdeal q.asIdeal hpq.le
        (by
          change Ideal.comap (algebraMap (MvPolynomial σ κ) C) p.asIdeal
            = Ideal.comap (algebraMap (MvPolynomial σ κ) C) q.asIdeal
          rw [hcomp, ← Ideal.comap_comap, ← Ideal.comap_comap]
          exact congrArg (Ideal.comap (Ideal.Quotient.mk (Ideal.span {f})))
            (congrArg PrimeSpectrum.asIdeal h))
  have h2 : ringKrullDim (MvPolynomial σ κ ⧸ Ideal.span {f}) + 1
      ≤ ringKrullDim (MvPolynomial σ κ) :=
    ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hf)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    ENat.card_eq_coe_natCard] at h2
  exact lt_of_le_of_lt (Order.krullDim_le_of_strictMono _ hsm) (lt_of_add_one_le h2)

/-- The fibre over `𝔭` of an algebra `T` which is quasi-finite over a polynomial ring
`R[t_i ; i ∈ σ]` in finitely many variables has dimension `< #σ` as soon as some
`f ∈ R[t_i ; i ∈ σ]` dies in `T` while its reduction modulo `𝔭` is nonzero.

The fibre `κ(𝔭) ⊗_R T` is `κ(𝔭)[t_i] ⊗_{R[t_i]} T`, the base change of `R[t_i] → T` along
`R[t_i] → κ(𝔭)[t_i]`, hence quasi-finite over the polynomial algebra `κ(𝔭)[t_i]` over the field
`κ(𝔭)`; and the reduction of `f` dies in it. -/
private theorem ringKrullDim_fiber_lt_natCard_of_mem_ker {R T σ : Type*} [CommRing R] [CommRing T]
    [Algebra R T] [Finite σ] [Algebra (MvPolynomial σ R) T]
    [IsScalarTower R (MvPolynomial σ R) T] [Algebra.QuasiFinite (MvPolynomial σ R) T]
    (𝔭 : Ideal R) [𝔭.IsPrime] {f : MvPolynomial σ R}
    (hf : MvPolynomial.map (algebraMap R 𝔭.ResidueField) f ≠ 0)
    (h0 : algebraMap (MvPolynomial σ R) T f = 0) :
    ringKrullDim (𝔭.Fiber T) < (Nat.card σ : WithBot ℕ∞) := by
  have hmap : ∀ x : MvPolynomial σ R,
      (MvPolynomial.algebraTensorAlgEquiv R 𝔭.ResidueField)
          ((Algebra.TensorProduct.comm R (MvPolynomial σ R) 𝔭.ResidueField)
            (algebraMap (MvPolynomial σ R) (MvPolynomial σ R ⊗[R] 𝔭.ResidueField) x))
        = algebraMap (MvPolynomial σ R) (MvPolynomial σ 𝔭.ResidueField) x := by
    intro x
    simp [Algebra.TensorProduct.algebraMap_apply]
  let eP : (MvPolynomial σ R ⊗[R] 𝔭.ResidueField) ≃ₐ[MvPolynomial σ R]
      MvPolynomial σ 𝔭.ResidueField :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm R (MvPolynomial σ R) 𝔭.ResidueField).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv R 𝔭.ResidueField).toRingEquiv) hmap
  have e : 𝔭.Fiber T ≃+* (MvPolynomial σ 𝔭.ResidueField) ⊗[MvPolynomial σ R] T :=
    (Algebra.TensorProduct.comm R 𝔭.ResidueField T).toRingEquiv.trans
      (((Algebra.TensorProduct.cancelBaseChange R (MvPolynomial σ R) (MvPolynomial σ R) T
            𝔭.ResidueField).symm.toRingEquiv).trans
        ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := MvPolynomial σ R) (A₁ := T))
            eP).toRingEquiv.trans
          (Algebra.TensorProduct.comm (MvPolynomial σ R) T
            (MvPolynomial σ 𝔭.ResidueField)).toRingEquiv))
  rw [ringKrullDim_eq_of_ringEquiv e]
  refine ringKrullDim_lt_natCard_of_quasiFinite_of_mem_ker (κ := 𝔭.ResidueField) hf ?_
  have hAM : algebraMap (MvPolynomial σ R) (MvPolynomial σ 𝔭.ResidueField) f
      = MvPolynomial.map (algebraMap R 𝔭.ResidueField) f := rfl
  rw [← hAM, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    show (algebraMap (MvPolynomial σ R) (MvPolynomial σ 𝔭.ResidueField) f)
      = f • (1 : MvPolynomial σ 𝔭.ResidueField) by rw [Algebra.smul_def, mul_one],
    TensorProduct.smul_tmul, Algebra.smul_def, h0, zero_mul, TensorProduct.tmul_zero]

/-! ### The valuation ring gives the upper bound on the special fibre -/

/-- Every point of the special fibre has local dimension at most `dim (S ⊗_R K)`.

This is the half of Stacks 00QK in which the valuation ring is used.  Let `n` be the local
dimension at the given point, that is the relative dimension at the corresponding prime `𝔮` of
`S`; it is a natural number because the special fibre is of finite type over `k`.  After inverting
one `g ∉ 𝔮` the algebra becomes quasi-finite over `R[t_1, …, t_n]` (Lemma 00QE), and the
polynomial ring maps *injectively* to `S_g`: a nonzero `f` in the kernel, divided by a coefficient
of minimal valuation (`exists_smul_eq_coeff_one_of_valuationRing`), has a unit coefficient, so its
reduction modulo `𝔪_R` is a nonzero element of the kernel of `k[t_1, …, t_n] → S_g ⊗_R k`, which
forces `dim (S_g ⊗_R k) < n` against `dim (S_g ⊗_R k) ≥ n`.  The `t_i` therefore have
algebraically independent images in a fraction field of `S`, whence `dim (S ⊗_R K) ≥ n`. -/
private theorem localKrullDim_le_ringKrullDim_fiber_bot {R S : Type*} [CommRing R] [IsDomain R]
    [ValuationRing R] [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]
    [Algebra.FiniteType R S] (x : PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S)) :
    localKrullDim (PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S)) x
      ≤ ringKrullDim ((⊥ : Ideal R).Fiber S) := by
  obtain ⟨z, hz, hxz⟩ := exists_mem_fibre_relativeDimensionAt_eq (S := S)
    ⟨IsLocalRing.maximalIdeal R, inferInstance⟩ x
  rw [← hxz]
  -- the relative dimension at `𝔮` is a natural number `m`
  have h0 : 0 ≤ Algebra.relativeDimensionAt R z.asIdeal := by
    rw [hxz]
    exact zero_le_localKrullDim _
  have htop : Algebra.relativeDimensionAt R z.asIdeal ≠ ⊤ := by
    rw [hxz]
    refine fun h ↦ ringKrullDim_ne_top_of_finiteType
      (κ := (IsLocalRing.maximalIdeal R).ResidueField)
      (A := (IsLocalRing.maximalIdeal R).Fiber S) (top_le_iff.mp ?_)
    rw [← h, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact localKrullDim_le_topologicalKrullDim _
  obtain ⟨m, hm⟩ := exists_nat_eq h0 htop
  rw [hm]
  -- Lemma 00QE: after inverting `g ∉ 𝔮`, quasi-finite over `R[t_1, …, t_m]`
  obtain ⟨g, hg, ψ, hqf⟩ := exists_quasiFinite_mvPolynomial_away (R := R) z.asIdeal hm
  let : Algebra (MvPolynomial (Fin m) R) (Localization.Away g) := ψ.toRingHom.toAlgebra
  have htower : IsScalarTower R (MvPolynomial (Fin m) R) (Localization.Away g) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  have : Algebra.QuasiFinite (MvPolynomial (Fin m) R) (Localization.Away g) := hqf
  have hg0 : g ≠ 0 := fun h ↦ hg (h ▸ Submodule.zero_mem _)
  have hpow : Submonoid.powers g ≤ nonZeroDivisors S := by
    rintro y ⟨n, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hg0)
  have : IsDomain (Localization.Away g) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hpow
  have hRT : Function.Injective (algebraMap R (Localization.Away g)) := by
    rw [IsScalarTower.algebraMap_eq R S (Localization.Away g)]
    exact (IsLocalization.injective _ hpow).comp (FaithfulSMul.algebraMap_injective R S)
  -- the polynomial ring maps injectively to `S_g`
  have hψ : ∀ f : MvPolynomial (Fin m) R, ψ f = 0 → f = 0 := by
    intro f hf0
    by_contra hfne
    obtain ⟨a, f', i, ha, hfa, hcoeff⟩ := exists_smul_eq_coeff_one_of_valuationRing hfne
    have hf' : algebraMap (MvPolynomial (Fin m) R) (Localization.Away g) f' = 0 := by
      have hmul : algebraMap R (Localization.Away g) a
          * algebraMap (MvPolynomial (Fin m) R) (Localization.Away g) f' = 0 := by
        rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin m) R) (Localization.Away g),
          ← map_mul, ← Algebra.smul_def, ← hfa]
        exact hf0
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd (hRT (by rw [map_zero]; exact h)) ha
      · exact h
    have hred : MvPolynomial.map
        (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField) f' ≠ 0 := by
      intro h
      refine zero_ne_one (α := (IsLocalRing.maximalIdeal R).ResidueField) ?_
      calc (0 : (IsLocalRing.maximalIdeal R).ResidueField)
          = (MvPolynomial.map
              (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField) f').coeff i := by
            rw [h]; simp
        _ = algebraMap R (IsLocalRing.maximalIdeal R).ResidueField (f'.coeff i) :=
            MvPolynomial.coeff_map _ _ _
        _ = 1 := by rw [hcoeff, map_one]
    have hlt := ringKrullDim_fiber_lt_natCard_of_mem_ker (T := Localization.Away g)
      (IsLocalRing.maximalIdeal R) hred hf'
    have hge : (m : WithBot ℕ∞)
        ≤ ringKrullDim ((IsLocalRing.maximalIdeal R).Fiber (Localization.Away g)) := by
      rw [← hm]
      exact Stacks.RelativeDimension.Semicontinuity.relativeDimensionAt_le_ringKrullDim_fiber g (Localization.Away g) (z : PrimeSpectrum S)
        ⟨IsLocalRing.maximalIdeal R, inferInstance⟩ hz (PrimeSpectrum.mem_basicOpen g _ |>.mpr hg)
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hlt
    exact absurd (lt_of_le_of_lt hge hlt) (lt_irrefl _)
  -- the images of the `t_i` in a fraction field of `S` are algebraically independent over `R`
  obtain ⟨_, _, _⟩ := exists_algebra_isFractionRing_of_le_nonZeroDivisors
    (T := Localization.Away g) (L := FractionRing S) hpow
  have : IsScalarTower R (Localization.Away g) (FractionRing S) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    rw [IsScalarTower.algebraMap_apply R S (Localization.Away g) r,
      ← IsScalarTower.algebraMap_apply S (Localization.Away g) (FractionRing S),
      ← IsScalarTower.algebraMap_apply R S (FractionRing S)]
  refine le_ringKrullDim_fiber_bot_of_algebraicIndependent
    (x := fun i ↦ algebraMap (Localization.Away g) (FractionRing S) (ψ (MvPolynomial.X i))) ?_
  rw [algebraicIndependent_iff_injective_aeval]
  have haeval : (MvPolynomial.aeval
        (fun i ↦ algebraMap (Localization.Away g) (FractionRing S) (ψ (MvPolynomial.X i))) :
          MvPolynomial (Fin m) R →ₐ[R] FractionRing S)
      = (IsScalarTower.toAlgHom R (Localization.Away g) (FractionRing S)).comp ψ := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    simp
  rw [haeval, AlgHom.coe_comp]
  refine (IsFractionRing.injective (Localization.Away g) (FractionRing S)).comp ?_
  intro p q hpq
  have : ψ (p - q) = 0 := by rw [map_sub, hpq, sub_self]
  exact sub_eq_zero.mp (hψ _ this)

/-! ### Stacks 00QK -/

/-- **Stacks 00QK.** Let `R` be a valuation ring with residue field `k` and fraction field `K`,
and let `S` be a domain containing `R` which is of finite type over `R`. If `S ⊗_R k` is not the
zero ring, then `dim (S ⊗_R k) = dim (S ⊗_R K)`, and in fact `Spec (S ⊗_R k)` is
equidimensional. -/
public theorem solution {R S : Type*} [CommRing R] [IsDomain R] [ValuationRing R] [CommRing S]
    [IsDomain S] [Algebra R S] [FaithfulSMul R S] [Algebra.FiniteType R S]
    (hfib : Nontrivial ((IsLocalRing.maximalIdeal R).Fiber S)) :
    ringKrullDim ((IsLocalRing.maximalIdeal R).Fiber S) =
        ringKrullDim ((⊥ : Ideal R).Fiber S) ∧
      TopologicalSpace.Equidimensional
        (PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S)) := by
  have := hfib
  have : Algebra.FiniteType (IsLocalRing.maximalIdeal R).ResidueField
      ((IsLocalRing.maximalIdeal R).Fiber S) := inferInstance
  have : IsNoetherianRing ((IsLocalRing.maximalIdeal R).Fiber S) :=
    Algebra.FiniteType.isNoetherianRing (IsLocalRing.maximalIdeal R).ResidueField _
  have : NoetherianSpace (PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S)) := inferInstance
  have key : ∀ x : PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S),
      localKrullDim (PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S)) x
        = ringKrullDim ((⊥ : Ideal R).Fiber S) := fun x =>
    le_antisymm (localKrullDim_le_ringKrullDim_fiber_bot x)
      (ringKrullDim_fiber_bot_le_localKrullDim _ x)
  refine ⟨?_, fun Z hZ W hW => ?_⟩
  · rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      topologicalKrullDim_eq_iSup_localKrullDim]
    simp only [key]
    exact iSup_const
  · rw [topologicalKrullDim_eq_of_localKrullDim_eq
      NoetherianSpace.finite_irreducibleComponents key hZ,
    topologicalKrullDim_eq_of_localKrullDim_eq
      NoetherianSpace.finite_irreducibleComponents key hW]

end Stacks.RelativeDimension.ValuationFibres

end

/-!
# Special and generic fibre of a domain of finite type over a valuation ring

Let `R` be a valuation ring with residue field `k` and fraction field `K`, and let `S` be a
domain containing `R` which is of finite type over `R`. If the special fibre `S ⊗_R k` is not the
zero ring, then it has the same dimension as the generic fibre,

`dim (S ⊗_R k) = dim (S ⊗_R K)`,

and moreover `Spec (S ⊗_R k)` is equidimensional: all of its irreducible components have one and
the same dimension, necessarily `dim (S ⊗_R K)`.

The reason is that the local dimension of the special fibre is `dim (S ⊗_R K)` at *every* one of
its points, which gives both assertions at once. Let `𝔮` be a prime of `S` containing `𝔪_R S`,
so a point of the special fibre, and let `n = dim_𝔮(S/R)` be the local dimension there. That
`n ≥ dim (S ⊗_R K)` is upper semicontinuity of relative dimension (Lemma 00QH) together with the
hypotheses on `S`: `S` is a domain in which `R` is contained, so the generic point of `Spec S`
lies in the generic fibre and belongs to every nonempty open set, in particular to a
neighbourhood of `𝔮` on which the relative dimension is at most `n`. For the reverse, after
inverting a single `g ∉ 𝔮` the algebra `S` becomes quasi-finite over `R[t_1, …, t_n]`
(Lemma 00QE). If `dim (S ⊗_R K) < n` were strict, the map `K[t_1, …, t_n] → S ⊗_R K` would have
a nonzero kernel, containing some `f = ∑_I a_I t^I`; here `R` being a valuation ring enters, in
that dividing `f` by a coefficient `a_I` of minimal valuation puts `f` in `R[t_1, …, t_n]` with
some coefficient a unit. Such an `f` has nonzero image in `k[t_1, …, t_n]` and dies in
`S ⊗_R k`, so `k[t_1, …, t_n] → S ⊗_R k` has a nonzero kernel and the special fibre has
dimension `< n`, a contradiction.

## Main results

* `ValuationRing.ringKrullDim_fiber_maximalIdeal_eq_ringKrullDim_fiber_bot_and_equidimensional`:
  Stacks 00QK.

## Implementation notes

*The two base changes are the two fibres of `Spec S → Spec R` over the two ends of `Spec R`.*
`S ⊗_R k` is `(IsLocalRing.maximalIdeal R).Fiber S`, Mathlib's fibre `κ(𝔪_R) ⊗_R S`, and
`S ⊗_R K` is `(⊥ : Ideal R).Fiber S`. The two residue fields are the source's `k` and `K`: the
localization `R → R_{𝔪_R}` is an isomorphism because `𝔪_R.primeCompl` consists of units, so
`κ(𝔪_R) = R/𝔪_R = k`, and `κ(⊥)` is a fraction field of `R` on the nose, the instance
`IsFractionRing R ((⊥ : Ideal R).ResidueField)` being available for a domain. So neither `k` nor
`K` is an extra type variable carrying a property: each is the canonical field the source names,
and the statement mentions only `R`, `S` and the `R`-algebra structure. `Ideal.Fiber` puts the
residue field on the left of the tensor product where the source writes it on the right; the two
are `Algebra.TensorProduct.comm` apart, and `ringKrullDim` is a ring isomorphism invariant.

*The fibre is preferred over the quotient and the localization it is isomorphic to, because the
bridges to those are already available.* `Ideal.Fiber.algEquivQuotient` and — for an arbitrary
localization — `Ideal.Fiber.ringEquivQuotient` of `StacksCore.RingTheory.Spectrum.Prime.Fiber`
identify `𝔭.Fiber S` with `S_𝔭 ⧸ 𝔭 S_𝔭`, the localization being at the image of `R ∖ 𝔭`. At
`𝔭 = 𝔪_R` that image consists of units, so `Sp := S` is admissible by `IsLocalization.self` and
the second bridge reads `𝔪_R.Fiber S ≃+* S ⧸ 𝔪_R S` for the special fibre; at `𝔭 = ⊥` the ideal
is zero, so the generic fibre is the localization `S[1/(R ∖ {0})]`, a subring of `Frac S`. A
consumer meeting either concrete form therefore has a one-step bridge, while the statement itself
stays with the uniform fibre notation in which the neighbouring Lemmas 00QD, 00QH and 00QI are
phrased.

*Equidimensionality* is `TopologicalSpace.Equidimensional` (Definition 0058), this project's
definition: any two irreducible components have equal `topologicalKrullDim` as subspaces.
Together with the first conjunct, every irreducible component of `Spec (S ⊗_R k)` has dimension
`dim (S ⊗_R K)`, since `ringKrullDim` is the supremum of the dimensions of the components.

*The nonvanishing hypothesis is the source's and cannot be dropped.* `S ⊗_R k ≠ 0` is
`Nontrivial ((IsLocalRing.maximalIdeal R).Fiber S)`, equivalently `𝔪_R` lies in the image of
`Spec S → Spec R` (`PrimeSpectrum.nontrivial_iff_mem_rangeComap`). It does not follow from the
other hypotheses: for a discrete valuation ring `R` with uniformizer `π`, the ring `S = R[1/π]`
is a domain containing `R`, of finite type over `R`, with `S ⊗_R k = 0`, and there the first
conjunct reads `⊥ = 0` in `WithBot ℕ∞`. The second conjunct is vacuous for the empty space and
so needs no guard, but it is stated under the same hypothesis as in the source.

*"A domain containing `R`"* is `[IsDomain S]` together with `[FaithfulSMul R S]`, Mathlib's class
for injectivity of `algebraMap R S` (`FaithfulSMul.algebraMap_injective`). Jointly they say that
no nonzero element of `R` kills a nonzero element of `S`, which is what makes `S → S ⊗_R K`
injective, and they make `Spec S` irreducible with generic point in the generic fibre.

*Dimension* is `ringKrullDim`, valued in `WithBot ℕ∞`; for the zero ring it is `⊥`, which is why
the first conjunct has content only under the nonvanishing hypothesis.

Faithfulness to [StacksProject 00QK]:

1. No hypothesis is idle. `[ValuationRing R]` is used where the source divides by a coefficient
   of minimal valuation. `[Algebra.FiniteType R S]` is the source's finite type hypothesis, used
   through Lemmas 00QE and 00QH. `[IsDomain S]` and `[FaithfulSMul R S]` are each necessary, and
   for the same conclusion: over a discrete valuation ring `R` with uniformizer `π`, the ring
   `S = R[x]/(πx)` contains `R` and is of finite type but is not a domain, and there
   `S ⊗_R k = k[x]` has dimension `1` while `S ⊗_R K = K` has dimension `0`; the ring
   `S = k[x] = (R/π)[x]` is a domain of finite type but does not contain `R`, and there
   `S ⊗_R k = k[x]` has dimension `1` while `S ⊗_R K = 0` has dimension `⊥`. The nonvanishing
   hypothesis is discussed above. Both conjuncts of the conclusion mention `S ⊗_R k`, and the
   first mentions `S ⊗_R K`.
2. The scalars and the base are the source's. Both dimensions are Krull dimensions of base
   changes of `S` along ring maps out of `R` itself for the given `Algebra R S` — not out of a
   localization, a quotient or a further base change of `R` — and `Ideal.Fiber` is formed over
   `R`, with `k = κ(𝔪_R)` and `K = κ(⊥)` the residue fields of the two primes of `R` the source
   names.
3. Nothing is left merely to exist. The residue field and the fraction field are pinned as the
   canonical `κ(𝔪_R)` and `κ(⊥)` rather than as abstract fields with a universal property, so no
   isomorphism has to be chosen — and `κ(⊥)` is a fraction field of `R` by the instance
   `IsFractionRing R ((⊥ : Ideal R).ResidueField)`, not merely up to a choice; the
   equidimensionality assertion is about `irreducibleComponents (PrimeSpectrum (𝔪_R.Fiber S))`
   itself.
4. The instantiation is not degenerate, and neither conjunct is trivially true in it. Let `R` be
   a discrete valuation ring with uniformizer `π` and residue field `k`, and let
   `S = R[x, y]/(xy - π)`. Then `S` is a domain containing `R`: it embeds in `R[x, 1/x]` by
   `y ↦ π/x`, its image being spanned by the Laurent monomials `x^i` and `(π/x)^j`. It is of
   finite type, and `S ⊗_R k = k[x, y]/(xy)` is nonzero of dimension `1`, while
   `S ⊗_R K = K[x, y]/(xy - π) ≅ K[x, 1/x]` is of dimension `1` as well, so the equality is
   `1 = 1` rather than `⊥ = ⊥` or `⊤ = ⊤`. The special fibre here has two irreducible
   components, the lines `y = 0` and `x = 0`, so its equidimensionality is not the vacuous case
   of an empty or irreducible space. Taking `S = R[x]` instead gives `1 = 1` with an irreducible
   special fibre, and `S = R` gives `0 = 0`.

## References

* [StacksProject 00QK](https://stacks.math.columbia.edu/tag/00QK)
* [StacksProject 00QD](https://stacks.math.columbia.edu/tag/00QD)
* [StacksProject 00QE](https://stacks.math.columbia.edu/tag/00QE)
* [StacksProject 00QH](https://stacks.math.columbia.edu/tag/00QH)
* [StacksProject 0058](https://stacks.math.columbia.edu/tag/0058)

## Tags

valuation ring, special fibre, generic fibre, dimension of fibres, equidimensional, finite type
-/

@[expose] public section

namespace ValuationRing

/-- **Stacks 00QK.** Let `R` be a valuation ring with residue field `k` and fraction field `K`,
and let `S` be a domain containing `R` which is of finite type over `R`. If `S ⊗_R k` is not the
zero ring, then `dim (S ⊗_R k) = dim (S ⊗_R K)`, and in fact `Spec (S ⊗_R k)` is
equidimensional, so that each of its irreducible components has dimension `dim (S ⊗_R K)`. -/
@[stacks 00QK "`S ⊗_R k` is the fibre `(IsLocalRing.maximalIdeal R).Fiber S` and `S ⊗_R K` the
fibre `(⊥ : Ideal R).Fiber S`, the residue fields `κ(𝔪_R)` and `κ(⊥)` being `k` and `K` because
`R` is a local domain; `dim` is `ringKrullDim` and equidimensionality is Definition 0058. `S` a
domain containing `R` is `[IsDomain S]` with `[FaithfulSMul R S]`. See the module docstring.",
  ega "IV 14.3.10" "affine case"]
public theorem ringKrullDim_fiber_maximalIdeal_eq_ringKrullDim_fiber_bot_and_equidimensional
    {R S : Type*} [CommRing R] [IsDomain R] [ValuationRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.FiniteType R S]
    (hfib : Nontrivial ((IsLocalRing.maximalIdeal R).Fiber S)) :
    ringKrullDim ((IsLocalRing.maximalIdeal R).Fiber S) =
        ringKrullDim ((⊥ : Ideal R).Fiber S) ∧
      TopologicalSpace.Equidimensional
        (PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S)) :=
    by exact Stacks.RelativeDimension.ValuationFibres.solution hfib

end ValuationRing

end
