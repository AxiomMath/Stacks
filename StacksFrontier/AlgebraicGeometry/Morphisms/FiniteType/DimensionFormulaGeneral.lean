module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.RingTheory.DimensionFormulaMinimalPrimes
public import StacksFrontier.Topology.Irreducible.GenericPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dimension formula without integrality assumptions

Let `f : X ⟶ S` be locally of finite type with `S` locally Noetherian and let `x` be a point of
`X`. The dimension formula for integral schemes (Stacks 02JU,
`AlgebraicGeometry.localDimension_add_trdeg_le`) compares `dim 𝒪_{X,x}` with `dim 𝒪_{S,f x}`,
correcting by the transcendence degree of the function field extension. Dropping integrality,
the function-field term is replaced by the largest transcendence degree
`trdeg_{κ(f η)} κ(η)` of a residue field extension at a generic point `η` of an irreducible
component of `X` through `x`:

`dim 𝒪_{X,x} + trdeg_{κ(f x)} κ(x) ≤ dim 𝒪_{S,f x} + E`.

The proof reads both sides on a pair of compatible affine charts `x ∈ V ≤ f ⁻¹ U`: the two local
dimensions become the heights of the primes of `Γ(X, V)` and `Γ(S, U)` cut out by `x` and `f x`,
the residue-field extension becomes the residue-field extension of those primes, and the generic
points of the irreducible components of `X` through `x` become the minimal primes of `Γ(X, V)`
contained in the prime of `x`. That turns the statement into
`height_add_trdeg_residue_le_of_forall_minimalPrimes`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.mem_genericPoints_fromSpec_of_mem_minimalPrimes`: the point of an affine
  open cut out by a minimal prime of its section ring is the generic point of an irreducible
  component of the ambient scheme.
* `AlgebraicGeometry.toNat_trdeg_residueField_eq_affine`: on a pair of compatible affine charts
  the residue-field transcendence degree of `f` at a point is that of the corresponding pair of
  primes of the chart rings.
* `AlgebraicGeometry.ringKrullDim_stalk_add_trdeg_le_of_forall_genericPoints`: the dimension
  formula bounded by the residue-field transcendence degrees at the generic points.

## Implementation notes

The bound `E` is a parameter rather than the supremum over the generic points through `x`; the
two formulations are equivalent, and the parametrised one is what the consumers of the formula
have at hand. The transcendence degrees are `Cardinal`-valued and are moved into `ℕ∞` by
`Cardinal.toENat`, matching Stacks 02FX
(`AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk_add_trdeg`); the
`κ(f x)`-algebra structure on `κ(x)` is not an instance, so it is supplied inline.

## References

* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The point of an affine open cut out by a prime of its section ring lies in that open. -/
theorem mem_of_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (r : PrimeSpectrum Γ(X, U)) : hU.fromSpec r ∈ U := by
  have hmem : hU.fromSpec r ∈ Set.range hU.fromSpec.base := ⟨r, rfl⟩
  rwa [hU.range_fromSpec] at hmem

/-- The prime of the section ring cut out by the point of an affine open determined by a prime
is that prime again. -/
theorem primeIdealOf_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (r : PrimeSpectrum Γ(X, U)) :
    hU.primeIdealOf ⟨hU.fromSpec r, mem_of_fromSpec hU r⟩ = r :=
  hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)

/-- The point of an affine open `U` cut out by a minimal prime of `Γ(X, U)` is the generic point
of an irreducible component of `X`: a generalization of it lies in `U`, because a generalization
of a point lies in every open set containing that point, and there it corresponds to a prime
below the given one, hence equal to it. -/
theorem mem_genericPoints_fromSpec_of_mem_minimalPrimes {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (r : Ideal Γ(X, U)) (hr : r ∈ minimalPrimes Γ(X, U)) :
    hU.fromSpec ⟨r, hr.isPrime⟩ ∈ genericPoints X := by
  have hrp : r.IsPrime := hr.isPrime
  set η : X := hU.fromSpec ⟨r, hrp⟩
  have hηU : η ∈ U := mem_of_fromSpec hU ⟨r, hrp⟩
  have hprime : hU.primeIdealOf ⟨η, hηU⟩ = ⟨r, hrp⟩ := primeIdealOf_fromSpec hU ⟨r, hrp⟩
  refine (mem_genericPoints_iff_forall_specializes_eq η).2 fun z hz => ?_
  have hzU : z ∈ U := hz.mem_open U.2 hηU
  have hsub : (⟨z, hzU⟩ : ↥U) ⤳ ⟨η, hηU⟩ := by
    rwa [← Topology.IsInducing.subtypeVal.specializes_iff]
  have hspec : hU.primeIdealOf ⟨z, hzU⟩ ⤳ hU.primeIdealOf ⟨η, hηU⟩ :=
    hsub.map hU.isoSpec.hom.continuous
  rw [hprime] at hspec
  have hle : (hU.primeIdealOf ⟨z, hzU⟩).asIdeal ≤ r :=
    (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr ((PrimeSpectrum.le_iff_specializes _ _).mpr hspec)
  have hmin : Minimal Ideal.IsPrime r := by
    rw [← IsMinimalPrime.iff_minimal]
    simpa using hr
  have heq : hU.primeIdealOf ⟨z, hzU⟩ = ⟨r, hrp⟩ :=
    PrimeSpectrum.ext (le_antisymm hle (hmin.2 (hU.primeIdealOf ⟨z, hzU⟩).isPrime hle))
  exact (hU.fromSpec_primeIdealOf ⟨z, hzU⟩).symm.trans (congrArg (hU.fromSpec ·) heq)

/-- A prime of `Γ(X, U)` contained in the prime cut out by `x ∈ U` corresponds to a
generalization of `x`. -/
theorem specializes_fromSpec_of_le_primeIdealOf {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (r : Ideal Γ(X, U)) [r.IsPrime] (x : X) (hx : x ∈ U)
    (hrq : r ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    hU.fromSpec ⟨r, ‹r.IsPrime›⟩ ⤳ x := by
  have hspec : (⟨r, ‹r.IsPrime›⟩ : PrimeSpectrum Γ(X, U)) ⤳ hU.primeIdealOf ⟨x, hx⟩ :=
    (PrimeSpectrum.le_iff_specializes _ _).mp ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hrq)
  have h := hspec.map hU.fromSpec.continuous
  rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h

/-- On a pair of compatible affine charts the residue-field transcendence degree of `f` at a
point of the source is the transcendence degree of the residue-field extension of the
corresponding pair of primes of the chart rings. -/
theorem toNat_trdeg_residueField_eq_affine {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (x : X)
    (hx : x ∈ V) :
    letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
    letI := (f.residueFieldMap x).hom.toAlgebra
    letI : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.LiesOver
        (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal :=
      ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
    letI := Ideal.ResidueField.algebraOfLiesOver (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal
    Algebra.trdeg (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal.ResidueField
        (hV.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField
      = Algebra.trdeg (S.residueField (f x)) (X.residueField x) := by
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  let : q.LiesOver p := ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Ideal.ResidueField.algebraOfLiesOver p q
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let eK := residueFieldEquivOfAffineOpen U hU (f x) (hVU hx)
  let eL := residueFieldEquivOfAffineOpen V hV x hx
  have hcomm := residueFieldMap_affine_compatible f U hU V hV hVU x hx
  dsimp at hcomm
  exact (Algebra.trdeg_eq_of_ringEquiv eK eL fun a => RingHom.congr_fun hcomm a).symm

/-- The residue-field extension of a morphism locally of finite type has finite transcendence
degree. -/
theorem trdeg_residueField_lt_aleph0 {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.trdeg (S.residueField (f x)) (X.residueField x) < Cardinal.aleph0 := by
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let : Algebra.EssFiniteType (S.residueField (f x)) (X.residueField x) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f x)
  exact trdeg_lt_aleph0 (S.residueField (f x)) (X.residueField x)

/-- At a minimal prime `r` of a chart ring `Γ(X, V)` below the prime of `x`, the residue-field
transcendence degree over `Γ(S, U)` is bounded by any `E` bounding the residue-field transcendence
degrees of `f` at the generic points of `X` specializing to `x`. -/
theorem underResidueTrdeg_le_of_mem_minimalPrimes {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {U : S.Opens} (hU : IsAffineOpen U) {V : X.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) {x : X} (hxV : x ∈ V) {E : ℕ∞}
    (hE : ∀ η : X, η ∈ genericPoints X → η ⤳ x →
      Cardinal.toENat (@Algebra.trdeg (S.residueField (f η)) (X.residueField η) _ _
        (f.residueFieldMap η).hom.toAlgebra) ≤ E)
    (r : Ideal Γ(X, V)) [hrp : r.IsPrime] (hr : r ∈ minimalPrimes Γ(X, V))
    (hrq : r ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) :
    letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
    (Ideal.underResidueTrdeg Γ(S, U) r : ℕ∞) ≤ E := by
  let : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  set η : X := hV.fromSpec ⟨r, hrp⟩
  have hηV : η ∈ V := mem_of_fromSpec hV ⟨r, hrp⟩
  have hprimeη : (hV.primeIdealOf ⟨η, hηV⟩).asIdeal = r :=
    congrArg PrimeSpectrum.asIdeal (primeIdealOf_fromSpec hV ⟨r, hrp⟩)
  let pη : Ideal Γ(S, U) := (hU.primeIdealOf ⟨f η, hVU hηV⟩).asIdeal
  have hpη : Ideal.under Γ(S, U) r = pη := by
    rw [← hprimeη]
    exact congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hηV)
  let : (hV.primeIdealOf ⟨η, hηV⟩).asIdeal.LiesOver pη :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hηV).1).symm⟩
  let : r.LiesOver pη := ⟨by rw [← hpη]⟩
  let : Algebra (S.residueField (f η)) (X.residueField η) := (f.residueFieldMap η).hom.toAlgebra
  have hchart := toNat_trdeg_residueField_eq_affine f U hU V hV hVU η hηV
  dsimp at hchart
  have hcongr := Ideal.toNat_trdeg_residue_congr (A := Γ(S, U)) (B := Γ(X, V))
    (Ideal.under Γ(S, U) r) pη r (hV.primeIdealOf ⟨η, hηV⟩).asIdeal hpη hprimeη.symm
  have hEη := hE η (mem_genericPoints_fromSpec_of_mem_minimalPrimes hV r hr)
    (specializes_fromSpec_of_le_primeIdealOf hV r x hxV hrq)
  rw [Cardinal.toENat_eq_toNat_of_lt_aleph0 (trdeg_residueField_lt_aleph0 f η)] at hEη
  rwa [Ideal.underResidueTrdeg, hcongr, hchart]

/-- **The general dimension formula.** Let `f : X ⟶ S` be locally of finite type with `S`
locally Noetherian, let `x` be a point of `X`, and let `E` bound the transcendence degree of the
residue-field extension `κ(η)/κ(f η)` at every generic point `η` of an irreducible component of
`X` containing `x`. Then

`dim 𝒪_{X,x} + trdeg_{κ(f x)} κ(x) ≤ dim 𝒪_{S,f x} + E`.

This is the form the dimension formula (Stacks 02JU) takes when the integrality assumptions on
`X` and `S` are dropped: the function-field term is replaced by the bound `E`. -/
@[ega "IV 5.5.8" "more general"]
theorem ringKrullDim_stalk_add_trdeg_le_of_forall_genericPoints {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (x : X) (E : ℕ∞)
    (hE : ∀ η : X, η ∈ genericPoints X → η ⤳ x →
      Cardinal.toENat (@Algebra.trdeg (S.residueField (f η)) (X.residueField η) _ _
        (f.residueFieldMap η).hom.toAlgebra) ≤ E) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    ringKrullDim (X.presheaf.stalk x)
        + (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
            WithBot ℕ∞)
      ≤ ringKrullDim (S.presheaf.stalk (f x)) + (E : WithBot ℕ∞) := by
  classical
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  let A : Type u := Γ(S, U)
  let B : Type u := Γ(X, V)
  let : Algebra A B := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Algebra.FiniteType A B := f.finiteType_appLE hU hV hVU
  let p : Ideal A := (hU.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal
  let q : Ideal B := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).1).symm⟩
  let := Ideal.ResidueField.algebraOfLiesOver p q
  have hchart := toNat_trdeg_residueField_eq_affine f U hU V hV hVU x hxV
  dsimp at hchart
  rw [hV.ringKrullDim_stalk_eq_height x hxV, hU.ringKrullDim_stalk_eq_height (f x) (hVU hxV),
    Cardinal.toENat_eq_toNat_of_lt_aleph0 (trdeg_residueField_lt_aleph0 f x), ← hchart]
  exact_mod_cast height_add_trdeg_residue_le_of_forall_minimalPrimes p q E
    fun r _ hr hrq => underResidueTrdeg_le_of_mem_minimalPrimes f hU hV hVU hxV hE r hr hrq

end AlgebraicGeometry

end
