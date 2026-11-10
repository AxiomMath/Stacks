module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerCycleFromCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.RingTheory.OrderOfVanishing.Defs
public import StacksFrontier.CategoryTheory.Abelian.KZeroRealisation

/-!
# From cycles to the K-group of a wide dimension layer

Let `(S, δ)` be a base situation with a dimension function and let `X` be a scheme locally of
finite type over `S`. Tag 02S9 attaches to a `k`-cycle `∑ n_Z[Z]` the element
`[⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]` of the Grothendieck group of the
dimension layer `Coh_{≤k}(X)/Coh_{≤k-1}(X)`, and Tag 02SC maps that layer to the wider layer
`Coh_{≤k+1}(X)/Coh_{≤k-1}(X)`, whose Grothendieck group receives the subgroup `Bₖ(X)`. The
composite

`Z_k(X) ⟶ K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`

is the homomorphism that [Stacks, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS) asserts
factors through rational equivalence, giving `CH_k(X) → K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`.

This file constructs that composite, records the quotient descent it would admit, and proves two
of the ingredients of the argument of the source: the identity in the Grothendieck group of a
layer produced by two short exact sequences with the same sub- and ambient object, and the
ring-level length computation at the generic point of a prime divisor.

The ring-level computation is the following. Let `A` be a one-dimensional Noetherian local domain
with fraction field `K`, let `g ∈ K` be nonzero and let `I ⊆ A` be a lattice on which
multiplication by `g` takes values in `A` — in the geometric situation the stalk at a point of
codimension one of the ideal of denominators of a rational function. Then

`length_A(A/gI) - length_A(A/I) = d(I, gI) = ord_A(g)`,

the first equality by additivity of the distance function of Stacks 02MG along `A ⊇ I, gI`
(Stacks 02MH) and the second by Stacks 02MI applied to multiplication by `g`, whose determinant
on the one-dimensional `K`-vector space `K` is `g`.

## Main definitions

* `Stacks.Chow.cycleDimensionLayerWideHom` — the composite
  `Z_k(X) → K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` of the two maps above.
* `Stacks.Chow.chowToDimensionLayerHom` — its descent to the Chow group `CH_k(X)`, given the
  vanishing of the composite on the cycles rationally equivalent to zero.

## Main results

* `Stacks.Chow.cycleDimensionLayerWideHom_apply` — the value on a cycle `∑ n_Z[Z]` is the
  difference of the classes of the two locally finite direct sums of structure sheaves, read in
  the wider layer.
* `Stacks.Chow.coherentDimensionKZeroMk_eq_of_shortExact` — two short exact sequences of
  `Coh_{≤b}(X)` whose sub-objects and whose ambient objects are isomorphic have quotients with
  the same class in `K₀(Coh_{≤b}(X)/Coh_{≤a}(X))`.
* `Stacks.Chow.length_quotient_sub_length_quotient_eq_ordR` — the ring-level computation above,
  in the form in which the two canonical maps of Tag 02P0 present it: for two linear maps
  `i, j : M → A` with `i` nonzero and `g · i(m) = j(m)` in `K` for all `m`,
  `length_A(A/j(M)) - length_A(A/i(M)) = ord_A(g)`.
* `Stacks.Chow.ord_eq_ordR` — at a point of codimension one of an integral locally Noetherian
  scheme, the order of vanishing of a nonzero rational function agrees with the order of
  vanishing of Stacks 02MD computed in the stalk.
* `Stacks.Chow.cycleDimensionLayerWideHom_dimensionLayerCycle_of_surjective` — on the cycle of a
  coherent module of support dimension at most `k`, the composite takes the value the class of
  that module in the wider layer, provided the map of Tag 02S9 from cycles is surjective.

## What this is not

No declaration here carries the `@[stacks 0FDS]` attribute. The whole content of that tag is the
existence of the homomorphism `CH_k(X) → K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`, which is **not**
established: `Stacks.Chow.chowToDimensionLayerHom` takes the vanishing on rational equivalences
as a hypothesis, and the declarations below it are the map before that descent and two
ingredients of the argument. Tagging any of them would report the tag as formalized.

## What is not proved

Tag 0FDS itself — that `Stacks.Chow.cycleDimensionLayerWideHom` kills the subgroup
`Stacks.Chow.rationalEquivalences` of cycles rationally equivalent to zero, so that
`Stacks.Chow.chowToDimensionLayerHom` applies — is **not** proved here. The argument of the
source reduces, by Tag 0FDR along the finite morphism `⨿ W_j → X` given by a locally finite
family of integral closed subschemes, to a single integral `X` of delta-dimension `k + 1` and a
nonzero rational function `f` with ideal of denominators `I` (Tag 02P1), where it runs as
follows: the two short exact sequences of Tag 02P0,

`0 → I → 𝒪_X → 𝒪_X/I → 0`  and  `0 → I →^{f} 𝒪_X → 𝒪_X/fI → 0`,

give `[𝒪_X/I] = [𝒪_X/fI]` in `K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` — this is
`Stacks.Chow.coherentDimensionKZeroMk_eq_of_shortExact` — while the cycles of the two quotients
satisfy `[𝒪_X/fI]_k - [𝒪_X/I]_k = div(f)`, by the ring-level computation of this file at the
generic point of each prime divisor. The step which closes the argument is the identification of
`div(f)` with the class `[𝒪_X/fI] - [𝒪_X/I]`, that is, the identity

`cycleDimensionLayerHom C f k (dimensionLayerCycle C f k F) =
  GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F)`

for a coherent module `F` of support dimension at most `k`. That identity is the inverse identity
of Tag 02S9 which is not formalized — equivalently the surjectivity of
`Stacks.Chow.cycleDimensionLayerHom`, or the injectivity of `Stacks.Chow.dimensionLayerCycleHom`
— recorded as missing in
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerCycleFromCycles`; the source proves it
through filtrations of the stalks at the generic points of the support and an extension of sheaf
maps off a neighbourhood of those points. It enters here only through
`Stacks.Chow.cycleDimensionLayerWideHom_dimensionLayerCycle_of_surjective`, which assumes it.

## References

* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 02MG](https://stacks.math.columbia.edu/tag/02MG)
* [Stacks Project, Tag 02MH](https://stacks.math.columbia.edu/tag/02MH)
* [Stacks Project, Tag 02MI](https://stacks.math.columbia.edu/tag/02MI)
* [Stacks Project, Tag 02MU](https://stacks.math.columbia.edu/tag/02MU)
* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02P1](https://stacks.math.columbia.edu/tag/02P1)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 02SC](https://stacks.math.columbia.edu/tag/02SC)
* [Stacks Project, Tag 0FDR](https://stacks.math.columbia.edu/tag/0FDR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The composite map from cycles -/


/-- The homomorphism out of the group of cycles whose descent to the Chow group is asserted by
[Stacks, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS): the map
`Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of Tag 02S9 followed by the map to the wider layer
`K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` of Tag 02SC. -/
def cycleDimensionLayerWideHom (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) :
    CycleGroup C f k →+ coherentDimensionKZero C f (k - 1) (k + 1) :=
  (coherentDimensionLayerHom C f k).comp
    ((KZero.ofGrothendieckGroup).comp
      (cycleDimensionLayerHom C f k))

/-- The value of the composite on a `k`-cycle `∑ n_Z[Z]` is the difference of the classes, in the
layer `(k - 1, k + 1]`, of the two locally finite direct sums of structure sheaves of the integral
closed subschemes occurring with positive, respectively negative, coefficient. -/
theorem cycleDimensionLayerWideHom_apply (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (c : CycleGroup C f k) :
    cycleDimensionLayerWideHom C f k c =
      coherentDimensionKZeroMk C f (k - 1) (k + 1) ((dimensionLayerInclusion C f k).obj
          (cycleStructureSheafDimLE C f k (cyclePositivePart C f k c))) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1) ((dimensionLayerInclusion C f k).obj
          (cycleStructureSheafDimLE C f k (cycleNegativePart C f k c))) := by
  rw [cycleDimensionLayerWideHom, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    cycleDimensionLayerHom_apply, map_sub, map_sub, KZero.ofGrothendieckGroup_of,
    KZero.ofGrothendieckGroup_of,
    show KZero.mk _ ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
      (cycleStructureSheafDimLE C f k (cyclePositivePart C f k c))) =
      coherentDimensionKZeroMk C f (k - 1) k
        (cycleStructureSheafDimLE C f k (cyclePositivePart C f k c)) from rfl,
    show KZero.mk _ ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
      (cycleStructureSheafDimLE C f k (cycleNegativePart C f k c))) =
      coherentDimensionKZeroMk C f (k - 1) k
        (cycleStructureSheafDimLE C f k (cycleNegativePart C f k c)) from rfl,
    coherentDimensionLayerHom_apply_mk, coherentDimensionLayerHom_apply_mk]

/-- The homomorphism `CH_k(X) → K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` induced by the map of Tag 02S9
on a group of cycles whose image in the wider layer kills the cycles rationally equivalent to
zero. -/
def chowToDimensionLayerHom (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ)
    (h : ∀ c ∈ rationalEquivalences C f k, cycleDimensionLayerWideHom C f k c = 0) :
    chowGroup C f k →+ coherentDimensionKZero C f (k - 1) (k + 1) :=
  QuotientAddGroup.lift _ (cycleDimensionLayerWideHom C f k) h

/-- The induced homomorphism on the Chow group sends the class of a cycle to the value of the
composite on that cycle. -/
theorem chowToDimensionLayerHom_mk (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ)
    (h : ∀ c ∈ rationalEquivalences C f k, cycleDimensionLayerWideHom C f k c = 0)
    (c : CycleGroup C f k) :
    chowToDimensionLayerHom C f k h (QuotientAddGroup.mk' (rationalEquivalences C f k) c) =
      cycleDimensionLayerWideHom C f k c :=
  QuotientAddGroup.lift_mk' _ h c

/-! ### Classes in a layer coming from short exact sequences -/

/-- Two short exact sequences of coherent `𝒪_X`-modules of support dimension at most `b` whose
sub-objects are isomorphic and whose ambient objects are isomorphic have quotients with the same
class in the Grothendieck group of the layer `(a, b]`: the class of the quotient is the class of
the ambient object minus the class of the sub-object. -/
theorem coherentDimensionKZeroMk_eq_of_shortExact (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (a b : ℤ)
    {S T : ShortComplex (CoherentModulesDimLE C f b)} (hS : S.ShortExact) (hT : T.ShortExact)
    (e₁ : S.X₁ ≅ T.X₁) (e₂ : S.X₂ ≅ T.X₂) :
    coherentDimensionKZeroMk C f a b S.X₃ = coherentDimensionKZeroMk C f a b T.X₃ := by
  have hS' := KZero.mk_of_shortExact _
    (hS.map_of_exact (lowerDimensionClass C f a b).isoModSerre.Q)
  have hT' := KZero.mk_of_shortExact _
    (hT.map_of_exact (lowerDimensionClass C f a b).isoModSerre.Q)
  have hiso : ∀ {U V : CoherentModulesDimLE C f b}, (U ≅ V) →
      KZero.mk _ ((lowerDimensionClass C f a b).isoModSerre.Q.obj U) =
        KZero.mk _ ((lowerDimensionClass C f a b).isoModSerre.Q.obj V) := fun e ↦
    KZero.mk_eq_of_iso ((lowerDimensionClass C f a b).isoModSerre.Q.mapIso e)
  simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃] at hS' hT'
  have key := hS'.symm.trans ((hiso e₂).trans hT')
  rw [hiso e₁] at key
  exact add_left_cancel key

/-! ### The ring-level computation at a prime divisor -/

/-- Multiplication by a nonzero element of a field, as a linear automorphism of that field. -/
private def mulLinearEquiv {K : Type*} [Field K] (g : Kˣ) : K ≃ₗ[K] K :=
  LinearEquiv.ofBijective
    (LinearEquiv.smul_id_of_finrank_eq_one (Module.finrank_self K) (g : K))
    ⟨fun x y hxy ↦ mul_left_cancel₀ g.ne_zero
        (by simpa [LinearEquiv.smul_id_of_finrank_eq_one_apply] using hxy),
      fun x ↦ ⟨(g : K)⁻¹ * x, by simp [LinearEquiv.smul_id_of_finrank_eq_one_apply]⟩⟩

/-- Multiplication by `g` sends `x` to `g * x`. -/
private theorem mulLinearEquiv_apply {K : Type*} [Field K] (g : Kˣ) (x : K) :
    mulLinearEquiv g x = (g : K) * x := by
  simp [mulLinearEquiv, LinearEquiv.smul_id_of_finrank_eq_one_apply]

/-- The determinant of multiplication by `g` on a field, read as a one-dimensional vector space
over itself, is `g`. -/
private theorem mulLinearEquiv_det {K : Type*} [Field K] (g : Kˣ) :
    LinearEquiv.det (mulLinearEquiv g) = g := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have hmap : (mulLinearEquiv g : K →ₗ[K] K) = Algebra.lsmul K K K (g : K) :=
    LinearMap.ext fun x ↦ by simp [mulLinearEquiv_apply]
  rw [hmap, Algebra.det_lsmul]
  simp [Module.finrank_self]

variable {R K : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

open Stacks.OrderOfVanishing in
/-- **Stacks 02MH and 02MI for multiplication by a scalar.** For two lattices `M ≤ A` in the
fraction field `K` of a one-dimensional Noetherian local domain `R` with `g M ≤ A`, the
difference of the lengths of `A / g M` and of `A / M` is the order of vanishing of `g`: it is the
distance `d(M, g M)`, the distance function being additive along `A ⊇ M, g M`, and multiplication
by `g` has determinant `g`. -/
private theorem length_quotient_mul_sub_length_quotient_eq_ordR
    (hdim : ringKrullDim R = 1) (g : Kˣ) (A M : Submodule R K)
    (hA : IsLattice (K := K) A) (hM : IsLattice (K := K) M) (hMA : M ≤ A)
    (hGM : mapLattice (K := K) (V := K) (mulLinearEquiv g) M ≤ A) :
    (Module.length R (↥A ⧸
        (mapLattice (K := K) (V := K) (mulLinearEquiv g) M).submoduleOf A)).toNat -
      (Module.length R (↥A ⧸ M.submoduleOf A)).toNat = ordR (R := R) g := by
  have hdist : latticeDist M (mapLattice (K := K) (V := K) (mulLinearEquiv g) M) =
      ordR (R := R) g := by
    simpa only [mulLinearEquiv_det g] using dist_map_eq_ord_det hdim (mulLinearEquiv g) M hM
  have hlen : ∀ N : Submodule R K, N ≤ A →
      latticeDist A N = (Module.length R (↥A ⧸ N.submoduleOf A)).toNat := fun N hN ↦ by
    unfold latticeDist lenQuot
    rw [inf_eq_right.mpr hN, inf_eq_left.mpr hN]
    simp [Submodule.submoduleOf]
    rfl
  have hadd := latticeDist_additivity hdim A M
    (mapLattice (K := K) (V := K) (mulLinearEquiv g) M) hA hM
    (mapLattice_isLattice (mulLinearEquiv g) M hM)
  rw [hlen _ hGM, hlen _ hMA, hdist] at hadd
  omega

/-- An injective linear map identifies a quotient of its source with the corresponding quotient
of its range. -/
private theorem length_quotient_eq_length_range_quotient
    {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : Function.Injective f)
    (P : Submodule R M) :
    Module.length R (M ⧸ P) =
      Module.length R (↥f.range ⧸ (P.map f).submoduleOf f.range) := by
  apply LinearEquiv.length_eq
  refine Submodule.Quotient.equiv P _ (LinearEquiv.ofInjective f hf) (Submodule.ext fun x ↦ ?_)
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, Subtype.ext h⟩

open Stacks.OrderOfVanishing in
/-- **The ring-level computation in the proof of Stacks 0FDS.** Let `R` be a one-dimensional
Noetherian local domain with fraction field `K`, let `g ∈ Kˣ` and let `i, j : M → R` be linear
maps on an `R`-module `M` with `i` nonzero and `g · i(m) = j(m)` in `K` for every `m` — the stalk
at a point of codimension one of the two canonical maps of Tag 02P0 out of the ideal of
denominators of a rational function. Then

`length_R(R / j(M)) - length_R(R / i(M)) = ord_R(g)`. -/
theorem length_quotient_sub_length_quotient_eq_ordR
    {M : Type*} [AddCommGroup M] [Module R M]
    (hdim : ringKrullDim R = 1) (g : Kˣ) (i j : M →ₗ[R] R)
    (hi : ∃ m, i m ≠ 0)
    (hij : ∀ m, (g : K) * algebraMap R K (i m) = algebraMap R K (j m)) :
    ((Module.length R (R ⧸ j.range)).toNat : ℤ) -
      ((Module.length R (R ⧸ i.range)).toNat : ℤ) = ordR (R := R) g := by
  let f := Algebra.linearMap R K
  let A := f.range
  let I := i.range.map f
  let J := j.range.map f
  have hf : Function.Injective f := IsFractionRing.injective R K
  obtain ⟨m, hm⟩ := hi
  have hfm : f (i m) ≠ 0 := (map_ne_zero_iff f hf).mpr hm
  have hA : IsLattice (K := K) A := by
    constructor
    · simpa only [Submodule.map_top] using
        Submodule.FG.map f (IsNoetherian.noetherian (⊤ : Submodule R R))
    · apply top_unique
      rw [← IsSimpleModule.span_singleton_eq_top K (one_ne_zero : (1 : K) ≠ 0)]
      exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨1, map_one (algebraMap R K)⟩)
  have hI : IsLattice (K := K) I := by
    constructor
    · exact Submodule.FG.map f (IsNoetherian.noetherian i.range)
    · apply top_unique
      rw [← IsSimpleModule.span_singleton_eq_top K hfm]
      exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨i m, ⟨m, rfl⟩, rfl⟩)
  have hIA : I ≤ A := LinearMap.map_le_range
  have hJA : J ≤ A := LinearMap.map_le_range
  have hgI : mapLattice (K := K) (V := K) (mulLinearEquiv g) I = J := by
    have he : (((mulLinearEquiv g).toLinearMap.restrictScalars R).comp f).comp i = f.comp j := by
      refine LinearMap.ext fun m ↦ ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
        LinearEquiv.coe_coe, mulLinearEquiv_apply, f, Algebra.linearMap_apply]
      exact hij m
    change (i.range.map f).map ((mulLinearEquiv g).toLinearMap.restrictScalars R) = j.range.map f
    rw [← Submodule.map_comp, ← LinearMap.range_comp, he, LinearMap.range_comp]
  have h := length_quotient_mul_sub_length_quotient_eq_ordR hdim g A I hA hI hIA
    (hgI.symm ▸ hJA)
  rwa [hgI, ← length_quotient_eq_length_range_quotient f hf j.range,
    ← length_quotient_eq_length_range_quotient f hf i.range] at h

open Stacks.OrderOfVanishing in
/-- The order of vanishing of an element of the fraction field of a one-dimensional Noetherian
local domain, as computed by `Ring.ordFrac`, is the order of vanishing of Stacks 02MD: both are
the difference of the lengths of the quotients by the numerator and by the denominator of a
presentation of the element as a fraction. -/
theorem ordFrac_eq_ordR (hdim : ringKrullDim R = 1) (g : Kˣ) :
    letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim.le
    Ring.ordFrac R (g : K) =
      (↑(Multiplicative.ofAdd (ordR (R := R) g)) : WithZero (Multiplicative ℤ)) := by
  let _ : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim.le
  set s := IsLocalization.sec (nonZeroDivisors R) (g : K) with hs
  have ha : s.1 ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (IsLocalization.sec_fst_ne_zero g.ne_zero)
  have hnum : Ring.ordMonoidWithZeroHom R s.1 =
      (↑(Multiplicative.ofAdd ((Ring.ord R s.1).toNat : ℤ)) : WithZero (Multiplicative ℤ)) :=
    Ring.ordMonoidWithZeroHom_eq_coe R ha (ENat.natCast_toNat (Ring.ord_ne_top ha)).symm
  have hden : Ring.ordMonoidWithZeroHom R (s.2 : R) =
      (↑(Multiplicative.ofAdd ((Ring.ord R (s.2 : R)).toNat : ℤ)) :
        WithZero (Multiplicative ℤ)) :=
    Ring.ordMonoidWithZeroHom_eq_coe R s.2.property
      (ENat.natCast_toNat (Ring.ord_ne_top s.2.property)).symm
  rw [← IsLocalization.mk'_sec (M := nonZeroDivisors R) K (g : K),
    Ring.ordFrac_eq_div (R := R) ⟨s.1, ha⟩ s.2, hnum, hden, ordR_def hdim]
  simp only [ordOnRing, Ring.ord, s, ← WithZero.coe_div]
  rfl

open Stacks.OrderOfVanishing in
/-- At a point of codimension one of an integral locally Noetherian scheme, the order of
vanishing of a nonzero rational function is the order of vanishing of Stacks 02MD computed in the
stalk at that point, a one-dimensional Noetherian local domain with fraction field the function
field. -/
theorem ord_eq_ordR {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : X.functionFieldˣ) (x : X) (hx : Order.coheight x = 1) :
    X.ord (g : X.functionField) x = ordR (R := X.presheaf.stalk x) g := by
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hx]
    rfl
  exact (Scheme.ord_eq_iff hx g.ne_zero).mpr (ordFrac_eq_ordR hdim g)

/-! ### The step which Tag 02S9 supplies -/

/-- Granting the inverse identity of Tag 02S9 which is not formalized — the surjectivity of the
map `Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` — the composite of this file sends the cycle of a
coherent `𝒪_X`-module whose support has delta-dimension at most `k` to the class of that module
in the layer `(k - 1, k + 1]`. This is the step by which the argument of Tag 0FDS passes from the
cycle identity `[𝒪_X/fI]_k - [𝒪_X/I]_k = div(f)` to the identity of classes in the Grothendieck
group of the wider layer. -/
theorem cycleDimensionLayerWideHom_dimensionLayerCycle_of_surjective (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (hsurj : Function.Surjective (cycleDimensionLayerHom C f k))
    (F : CoherentModulesDimLE C f k) :
    cycleDimensionLayerWideHom C f k (dimensionLayerCycle C f k F) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1) ((dimensionLayerInclusion C f k).obj F) := by
  obtain ⟨c, hc⟩ := hsurj (GrothendieckGroup.of
    ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F))
  have hcyc : c = dimensionLayerCycle C f k F := by
    rw [← dimensionLayerCycleHom_cycleDimensionLayerHom C f k c, hc,
      dimensionLayerCycleHom_of]
  rw [cycleDimensionLayerWideHom, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← hcyc, hc,
    KZero.ofGrothendieckGroup_of]
  exact coherentDimensionLayerHom_apply_mk C f k F

end Stacks.Chow

end
