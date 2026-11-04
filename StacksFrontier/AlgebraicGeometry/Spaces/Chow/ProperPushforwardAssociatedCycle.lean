module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCoherentCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition

/-!
# Proper pushforward of the associated cycle

In Situation 0EDT let `X/B` and `Y/B` be good and let `f : X ⟶ Y` be a morphism over `B`.
**Stacks 0EP3** asserts two equalities of `k`-cycles on `Y` (proved unconditionally in
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/ProperPushforwardModuleCycle.lean`; this file keeps
an earlier conditional route through a local datum):

* part (1), for a closed subspace `Z ⊆ X` with `dim_δ(Z) ≤ k`,

  `f_*[Z]_k = [f_*𝒪_Z]_k`;

* part (2), for a coherent `𝒪_X`-module `F` with `dim_δ(Supp(F)) ≤ k`,

  `f_*[F]_k = [f_*F]_k`.

The source derives part (1) from part (2) applied to `F = i_*𝒪_Z`, and that is the order here
too. The direct image of modules is `AlgebraicGeometry.Space.modulePushforward`, the
direct-image half of Stacks 03LU, taken here through
`AlgebraicGeometry.Space.directImageModule` so that it can be applied to a morphism of
functors together with the two witnesses that source and target are algebraic spaces, which is
the shape in which the rest of this chapter presents a morphism of good algebraic spaces.

## What is proved and what is carried

The pushforward of cycles of Stacks 0EP1 has the coefficient
`(f_*α)_{Z'} = ∑_Z α_Z · deg(Z/Z')` at an integral closed subspace `Z' ⊆ Y`
(`AlgebraicGeometry.Space.properPushforward_apply`), and the coefficient of `[F]_k` at an
integral closed subspace of δ-dimension `k` is the length of `F` at its generic point
(Stacks 0EEC). So part (2) says, at each `Z' ⊆ Y` of δ-dimension `k`,

`length(f_*F at η') = ∑_{Z} length(F at η_Z) · [R(Z) : R(Z')]`,

the sum over the integral closed subspaces of `X` whose image closure is `Z'`. Localized at the
generic point `η'` of `Z'` this is a statement about a semilocal ring finite over a local ring:
with `A = 𝒪_{Y,η'}`, with `R` the ring of the fibre of `f` over `η'` and with `M` the module of
sections of `F` there, it is Stacks 02M0,

`length_A(M) = ∑_{𝔮 ∈ MaxSpec(R)} [κ(𝔮) : κ(A)] · length_{R_𝔮}(M_𝔮)`,

which this repository has as
`Stacks.Length.length_eq_sum_finrank_mul_length_localizedModule`.

**That identity is proved here, not assumed.** What is carried is one named datum,
`AlgebraicGeometry.Space.ProperPushforwardLengthDatum`, in the same shape as
the corresponding datum for Stacks 0EPD, which is discharged by the theorem
`AlgebraicGeometry.Space.properCycleDegree_mul_flatPullbackMult_eq_finsum`
(`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeGenericPoints`), whose route via
Stacks 0EP3(1), 073K(1) in degree zero and 02M1 may discharge this one too: the two rings and the
module, together with the dictionary reading the geometric cycle coefficients of Stacks 0EEB
as lengths of those algebraic objects and the degree `deg(Z/Z')` as a residue degree. No field
of the datum relates the numbers to one another; the arithmetic is the content of
`AlgebraicGeometry.Space.cycleCoeffOfModule_modulePushforwardAlong_eq_finsum`.

Carrying that dictionary is unavoidable here: the cycle coefficients of this chapter are
lengths at *geometric* points of an algebraic space
(`AlgebraicGeometry.Space.geometricLength`), and the comparison of such a length with the
length of a stalk of a ring is Stacks 0EE1, which this library proves only for the structure
sheaf on a single étale chart — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricStalkLength.lean`. This is also why every cycle
of this chapter carries a function `γ` choosing a geometric representative of each point.

Two further inputs are carried as hypotheses of the two tagged statements, both of them
separate results that this repository does not have:

* coherence of `f_*F`, which is Stacks 08AR. The module
  `StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFinite` records in detail why neither
  Stacks 08AR nor its scheme-level counterpart Stacks 02O5 is available. It is needed only to
  *form* `[f_*F]_k`, since `AlgebraicGeometry.Space.associatedCycle` is defined on coherent
  modules.
* the bound `dim_δ(Supp(f_*F)) ≤ k`, which in the source follows from
  `Supp(f_*F) = f(Supp(F))` for a proper morphism. This library proves no description of the
  support of a direct image of modules, so the bound is a hypothesis, exactly as the
  corresponding support bound is carried in Stacks 0EED
  (`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_eq_cycleCoeffOfModule_of_eq_zero`).

Neither is assumed in the coefficientwise form
`AlgebraicGeometry.Space.properPushforwardCoeff_eq_cycleCoeffOfModule`, which is the whole
mathematical content of part (2) and needs no coherence and no dimension bound at all: the
coefficient family `AlgebraicGeometry.Space.cycleCoeffOfModule` is defined for every module.

## Main definitions

* `AlgebraicGeometry.Space.ProperPushforwardLengthDatum`: the carried local dictionary at the
  generic point of one integral closed subspace of `Y`.

## Main results

* `AlgebraicGeometry.Space.cycleCoeffOfModule_modulePushforwardAlong_eq_finsum`: **the local
  identity of Stacks 0EP3, proved from Stacks 02M0** granted one
  `AlgebraicGeometry.Space.ProperPushforwardLengthDatum`.
* `AlgebraicGeometry.Space.properPushforwardCoeff_cycleCoeffOfModule_eq_zero`: the pushforward
  coefficient vanishes at an integral closed subspace of δ-dimension other than `k`; this is
  proved outright, and it is the half of the cycle identity that no datum is needed for.
* `AlgebraicGeometry.Space.properPushforwardCoeff_eq_cycleCoeffOfModule`: part (2) of
  Stacks 0EP3 as an equality of coefficient families.
* `AlgebraicGeometry.Space.properPushforward_associatedCycleOfModule`: a conditional form of
  Stacks 0EP3, part (2), carrying the local dictionary, coherence of `f_*F` and its support bound,
  `f_*[F]_k = [f_*F]_k` in `Z_k(Y)`.
* `AlgebraicGeometry.Space.properPushforward_closedSubspaceCycle`: the corresponding conditional
  form of Stacks 0EP3, part (1),
  `f_*[Z]_k = [f_*𝒪_Z]_k` in `Z_k(Y)`, deduced from part (2) through Stacks 0EED.

## Implementation notes

**Only quasi-compactness of `f` is asked.** The source assumes `f` proper. The pushforward of
cycles `AlgebraicGeometry.Space.properCyclePushforward` is constructed under
`AlgebraicGeometry.Space.IsQuasiCompact`, properness never being used for the construction, and
the hypothesis is stated in that shape here so that the statements compose with the rest of the
chapter. Properness is what makes the carried datum inhabited — it is what makes the fibre over
a generic point finite — and it is therefore implicit in the datum rather than assumed.

**`f_*𝒪_Z` of part (1) is the iterated direct image.** The source writes `f_*𝒪_Z` for the direct
image along the composite `Z → X → Y`, and its own proof immediately factors that composite.
Here the inner direct image along the closed immersion is
`AlgebraicGeometry.Space.closedSubspacePushforwardStructureSheaf`, the one for which Stacks 0EE3
is available and through which Stacks 0EED is stated, and the outer one is
`AlgebraicGeometry.Space.directImageModule`. Identifying the composite's direct image with
the iterated one would need the comparison of Stacks 03LU for these two different constructions
of a direct image, which is not what this tag is about.

## References

* [Stacks Project, Tag 02M0](https://stacks.math.columbia.edu/tag/02M0)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EEB](https://stacks.math.columbia.edu/tag/0EEB)
* [Stacks Project, Tag 0EEC](https://stacks.math.columbia.edu/tag/0EEC)
* [Stacks Project, Tag 0EED](https://stacks.math.columbia.edu/tag/0EED)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP3](https://stacks.math.columbia.edu/tag/0EP3)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The carried local dictionary at a generic point -/

section Datum

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)

/-- **The local data at a generic point which the coefficient identity of Stacks 0EP3 is
derived from.** Fix an `𝒪_X`-module `F`, an integer `k` and an integral closed subspace
`Z' ⊆ Y`. A datum consists of

* `base`, the local ring of `Y` at the generic point `η'` of `Z'`,
* `fibre`, the ring of the fibre of `f` over `η'`, finite over `base` and semilocal, and
* `stalk`, the module of sections of `F` over that fibre, Artinian over `fibre`,

together with the dictionary between the numbers of the coefficient identity and invariants of
those objects: `pushforwardLength_eq` reads the coefficient of `Z'` in `[f_*F]_k` — a length of
`f_*F` at a geometric point over `η'`, by Stacks 0EEC — as the `base`-length of `stalk`,
`componentLength_eq` reads the coefficient of the integral closed subspace `component 𝔮`
attached to a maximal ideal `𝔮` of `fibre` in `[F]_k` as the length of the localization of
`stalk` at `𝔮`, and `componentDegree_eq` reads the degree `deg(component 𝔮 / Z')` of
Stacks 0EP1 as the residue degree at `𝔮`.

**No field relates the numbers to one another**: the coefficient identity itself is proved from
this datum, by
`AlgebraicGeometry.Space.cycleCoeffOfModule_modulePushforwardAlong_eq_finsum`, out of
Stacks 02M0. What the datum supplies is the comparison of the geometric lengths of Stacks 0EEB
with lengths of modules over rings, which is what this repository is missing — see the
implementation notes of this file. -/
structure ProperPushforwardLengthDatum
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1) (k : ℤ)
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y) where
  /-- The local ring of `Y` at the generic point of `Z'`. -/
  base : Type v
  [commRingBase : CommRing base]
  [isLocalRingBase : IsLocalRing base]
  /-- The ring of the fibre of `f` over the generic point of `Z'`. -/
  fibre : Type v
  [commRingFibre : CommRing fibre]
  [algebraFibre : Algebra base fibre]
  [finiteFibre : Module.Finite base fibre]
  [fintypeMaximalSpectrum : Fintype (MaximalSpectrum fibre)]
  [isLocalHomLocalization : ∀ q : MaximalSpectrum fibre,
    IsLocalHom (algebraMap base (Localization.AtPrime q.asIdeal))]
  /-- The module of sections of `F` over that fibre. -/
  stalk : Type v
  [addCommGroupStalk : AddCommGroup stalk]
  [moduleFibreStalk : Module fibre stalk]
  [artinianStalk : IsArtinian fibre stalk]
  [moduleBaseStalk : Module base stalk]
  [isScalarTowerStalk : IsScalarTower base fibre stalk]
  /-- The integral closed subspace of `X` at the maximal ideal `q` of `fibre`. -/
  component : MaximalSpectrum fibre → IntegralClosedSubspace D.site D.base D.base_mem X
  /-- Distinct maximal ideals name distinct subspaces. -/
  injective_component : Function.Injective component
  /-- The coefficient of `Z'` in `[f_*F]_k`, as a natural number. -/
  mult : ℕ
  /-- That number is the `base`-length of `stalk`. -/
  length_stalk : Module.length base stalk = mult
  /-- The coefficient of `component q` in `[F]_k`, as a natural number. -/
  componentMult : MaximalSpectrum fibre → ℕ
  /-- That number is the length of the localization of `stalk` at `q`. -/
  length_localization : ∀ q : MaximalSpectrum fibre,
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl stalk) = componentMult q
  /-- The coefficient of `Z'` in `[f_*F]_k` is `mult`. -/
  pushforwardLength_eq : cycleCoeffOfModule D sY hY
      (directImageModule D hX.1 hY.1 f F) k γY Z' = (mult : ℤ)
  /-- The coefficient of `component q` in `[F]_k` is `componentMult q`. -/
  componentLength_eq : ∀ q : MaximalSpectrum fibre,
    cycleCoeffOfModule D sX hX F k γX (component q) = (componentMult q : ℤ)
  /-- The degree of `component q` over `Z'` is the residue degree at `q`. -/
  componentDegree_eq : ∀ q : MaximalSpectrum fibre,
    properCycleMult D sX hX sY hY f (component q) Z' =
      (Module.finrank (IsLocalRing.ResidueField base)
        (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) : ℤ)
  /-- An integral closed subspace of `X` which is not one of the `component q` contributes
  nothing to the defining sum of the pushforward coefficient at `Z'`. -/
  vanishing : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
    (∀ q : MaximalSpectrum fibre, component q ≠ Z) →
      cycleCoeffOfModule D sX hX F k γX Z * properCycleMult D sX hX sY hY f Z Z' = 0

/-- **The coefficient identity of Stacks 0EP3 at one generic point, proved.** For an integral
closed subspace `Z' ⊆ Y`, the coefficient of `Z'` in `[f_*F]_k` is the defining sum

`∑_{Z ⊆ X} [F]_k(Z) · deg(Z/Z')`

of the pushforward coefficient of Stacks 0EP1, granted one
`AlgebraicGeometry.Space.ProperPushforwardLengthDatum` at `Z'`.

The sum on the right is over *all* integral closed subspaces of `X`; the datum confines its
support to the finitely many subspaces named by the maximal ideals of the fibre ring, so it
collapses to a finite sum over `MaximalSpectrum`. There the identity is Stacks 02M0,
`Stacks.Length.length_eq_sum_finrank_mul_length_localizedModule`: the length of the module of
sections over the base, computed directly on one side and through the localizations at the
maximal ideals of the fibre on the other. -/
theorem cycleCoeffOfModule_modulePushforwardAlong_eq_finsum
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1) (k : ℤ)
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    {Z' : IntegralClosedSubspace D.site D.base D.base_mem Y}
    (data : ProperPushforwardLengthDatum.{v, u} D sX hX sY hY f F k γX γY Z') :
    cycleCoeffOfModule D sY hY
        (directImageModule D hX.1 hY.1 f F) k γY Z' =
      ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        cycleCoeffOfModule D sX hX F k γX Z * properCycleMult D sX hX sY hY f Z Z' := by
  classical
  obtain ⟨A, R, M, comp, hcomp, m, hlenA, cm, hlenR, hmult, hcl, hcd, hvan⟩ := data
  have hsub : (Function.support fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      cycleCoeffOfModule D sX hX F k γX Z * properCycleMult D sX hX sY hY f Z Z') ⊆
      ((Finset.univ.image comp :
        Finset (IntegralClosedSubspace D.site D.base D.base_mem X)) : Set _) := by
    intro Z hZ
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    by_contra hc
    exact hZ (hvan Z fun q hq => hc ⟨q, hq⟩)
  rw [hmult, finsum_eq_finsetSum_of_support_subset _ hsub,
    Finset.sum_image fun x _ y _ hxy => hcomp hxy,
    Finset.sum_congr rfl fun q _ => by rw [hcl q, hcd q]]
  have hring := Stacks.Length.length_eq_sum_finrank_mul_length_localizedModule (A := A) (B := R) M
    fun q => by rw [hlenR q]; exact ENat.natCast_ne_top _
  rw [hlenA] at hring
  simp only [hlenR] at hring
  have hnat : m = ∑ q : MaximalSpectrum R, Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) * cm q := by
    have hcast : ((m : ℕ) : ℕ∞) = ((∑ q : MaximalSpectrum R,
        Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) * cm q : ℕ) : ℕ∞) := by
      push_cast
      exact hring
    exact_mod_cast hcast
  rw [hnat]
  push_cast
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

end Datum

/-! ### The cycle identity -/

section Main

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)

/-- **The half of Stacks 0EP3 that needs no local datum.** At an integral closed subspace
`Z' ⊆ Y` of δ-dimension other than `k` the pushforward coefficient of `[F]_k` vanishes.

A nonzero summand forces `Z'` to be the closure of the image of a subspace `Z` with nonzero
coefficient, hence of δ-dimension `k`, and forces the degree `deg(Z/Z')` to be nonzero, which
by `AlgebraicGeometry.Space.deltaDimension_closureImage_of_properCycleDegree_ne_zero` preserves
the δ-dimension. -/
theorem properPushforwardCoeff_cycleCoeffOfModule_eq_zero (f : X ⟶ Y)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1) (k : ℤ)
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    {Z' : IntegralClosedSubspace D.site D.base D.base_mem Y}
    (hZ' : deltaDimension D sY Z' ≠ k) :
    properCyclePushforwardCoeff D sX hX sY hY f (cycleCoeffOfModule D sX hX F k γX) Z' = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun Z => ?_
  by_cases hco : cycleCoeffOfModule D sX hX F k γX Z = 0
  · rw [hco, zero_mul]
  by_cases hm : properCycleMult D sX hX sY hY f Z Z' = 0
  · rw [hm, mul_zero]
  obtain ⟨him, hdeg⟩ := (properCycleMult_ne_zero_iff D sX hX sY hY f Z Z').1 hm
  refine absurd ?_ hZ'
  rw [← him, deltaDimension_closureImage_of_properCycleDegree_ne_zero D sX hX sY hY f hdeg]
  by_contra h
  exact hco (by rw [cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_right h])

/-- **A conditional form of Stacks 0EP3, part (2), as an equality of coefficient families.** The
pushforward of the
coefficient family of `[F]_k` is the coefficient family of `[f_*F]_k`, granted a local datum at
each integral closed subspace of `Y` of δ-dimension `k`.

At a subspace of δ-dimension `k` this is
`AlgebraicGeometry.Space.cycleCoeffOfModule_modulePushforwardAlong_eq_finsum`; elsewhere both
sides vanish, the left one by
`AlgebraicGeometry.Space.properPushforwardCoeff_cycleCoeffOfModule_eq_zero` and the right one
by the definition of the coefficient family. No coherence and no bound on the δ-dimension of a
support is used: the coefficient family of Stacks 0EEB is defined for every module. -/
theorem properPushforwardCoeff_eq_cycleCoeffOfModule (f : X ⟶ Y)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1) (k : ℤ)
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    (hdata : ∀ Z' : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY Z' = k →
        Nonempty (ProperPushforwardLengthDatum.{v, u} D sX hX sY hY f F k γX γY Z')) :
    properCyclePushforwardCoeff D sX hX sY hY f (cycleCoeffOfModule D sX hX F k γX) =
      cycleCoeffOfModule D sY hY (directImageModule D hX.1 hY.1 f F) k γY := by
  funext Z'
  by_cases hZ' : deltaDimension D sY Z' = k
  · exact (hdata Z' hZ').elim fun data =>
      (cycleCoeffOfModule_modulePushforwardAlong_eq_finsum D sX hX sY hY f F k γX γY data).symm
  · rw [properPushforwardCoeff_cycleCoeffOfModule_eq_zero D sX hX sY hY f F k γX hZ',
      cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_right hZ']

/-- **A conditional form of Stacks 0EP3, part (2)**, superseded by the unconditional
`AlgebraicGeometry.Space.properCyclePushforward_associatedCycle_eq`. In Situation 0EDT let `X/B`
and `Y/B` be good, let `f : X ⟶ Y`
be quasi-compact over `B`, let `F` be a coherent `𝒪_X`-module with `dim_δ(Supp(F)) ≤ k` and
assume `f_*F` is coherent with `dim_δ(Supp(f_*F)) ≤ k`. Then

`f_*[F]_k = [f_*F]_k`

in `Z_k(Y)`.

The hypothesis `hdata` is the local dictionary at the generic points,
`AlgebraicGeometry.Space.ProperPushforwardLengthDatum`. **The coefficient identity itself is
proved**, from Stacks 02M0, by
`AlgebraicGeometry.Space.cycleCoeffOfModule_modulePushforwardAlong_eq_finsum`, so no numerical
identity is assumed here. Coherence of `f_*F` is Stacks 08AR and the bound on the δ-dimension
of its support is the description `Supp(f_*F) = f(Supp(F))` for a proper morphism; neither is
proved in this library, and both are needed only to *form* the right-hand side. The underlying
equality of coefficient families, which needs neither, is
`AlgebraicGeometry.Space.properPushforwardCoeff_eq_cycleCoeffOfModule`. -/
theorem properPushforward_associatedCycleOfModule {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγX : ∀ x, (γX x).LiesOver x)
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    (hγY : ∀ y, (γY y).LiesOver y)
    (hdimF : deltaDimensionClosed D sX hX
      (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    [IsCoherent D.site D.base D.base_mem Y hY.1 (directImageModule D hX.1 hY.1 f F)]
    (hdimG : deltaDimensionClosed D sY hY
      (moduleSupport D.site D.base D.base_mem hY.1 (directImageModule D hX.1 hY.1 f F))
      (isClosed_moduleSupport D.site D.base D.base_mem hY.1
        (directImageModule D hX.1 hY.1 f F)) ≤ (k : EInt))
    (hdata : ∀ Z' : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY Z' = k →
        Nonempty (ProperPushforwardLengthDatum.{v, u} D sX hX sY hY f F k γX γY Z')) :
    properCyclePushforward D sX hX sY hY hfB hf k (associatedCycle D sX hX F k γX hγX hdimF) =
      associatedCycle D sY hY (directImageModule D hX.1 hY.1 f F) k γY hγY hdimG := by
  refine Subtype.ext ?_
  change properCyclePushforwardCoeff D sX hX sY hY f (cycleCoeffOfModule D sX hX F k γX) = _
  exact properPushforwardCoeff_eq_cycleCoeffOfModule D sX hX sY hY f F k γX γY hdata

end Main

/-! ### The cycle of a closed subspace -/

section ClosedSubspace

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)

/-- **A conditional form of Stacks 0EP3, part (1)**, superseded by the unconditional
`AlgebraicGeometry.Space.properCyclePushforward_closedSubspaceCycle_eq`. In Situation 0EDT let
`X/B` and `Y/B` be good, let `f : X ⟶ Y`
be quasi-compact over `B`, let `Z ⊆ X` be a closed subspace with `dim_δ(Z) ≤ k` and inclusion
`i : Z → X`, and assume `f_*(i_*𝒪_Z)` is coherent with support of δ-dimension at most `k`. Then

`f_*[Z]_k = [f_*𝒪_Z]_k`

in `Z_k(Y)`.

This is part (2) applied to `F = i_*𝒪_Z`, exactly as in the source, after rewriting `[Z]_k` as
`[i_*𝒪_Z]_k` by Stacks 0EED. The hypothesis `hγX` is the one that Stacks 0EED carries
in this library: that the chosen geometric representatives above `|Z|` and above `|X|` lie over
the points they are assigned to. -/
theorem properPushforward_closedSubspaceCycle {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f) (W : Subfunctor X)
    (hW : IsClosedSubspace D.site D.base D.base_mem W) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX W hW ≤ (k : EInt))
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγX : ∀ x, (γX x).LiesOver x)
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    (hγY : ∀ y, (γY y).LiesOver y)
    [IsCoherent D.site D.base D.base_mem Y hY.1
      (directImageModule D hX.1 hY.1 f
        (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 W hW))]
    (hdimG : deltaDimensionClosed D sY hY
      (moduleSupport D.site D.base D.base_mem hY.1
        (directImageModule D hX.1 hY.1 f
          (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 W hW)))
      (isClosed_moduleSupport D.site D.base D.base_mem hY.1
        (directImageModule D hX.1 hY.1 f
          (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 W hW))) ≤
        (k : EInt))
    (hdata : ∀ Z' : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY Z' = k →
        Nonempty (ProperPushforwardLengthDatum.{v, u} D sX hX sY hY f
          (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 W hW)
          k γX γY Z')) :
    properCyclePushforward D sX hX sY hY hfB hf k (closedSubspaceCycle D sX hX W hW k hdim) =
      associatedCycle D sY hY
        (directImageModule D hX.1 hY.1 f
          (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 W hW))
        k γY hγY hdimG := by
  refine Subtype.ext ?_
  change properCyclePushforwardCoeff D sX hX sY hY f
    (cycleCoeffOfClosedSubspace D sX hX W hW k
      (canonicalGeometricPoint D.site D.base D.base_mem W.toFunctor)) = _
  rw [cycleCoeffOfClosedSubspace_eq_cycleCoeffOfModule_of_eq_zero D sX hX W hW k hdim
    (canonicalGeometricPoint D.site D.base D.base_mem W.toFunctor) γX
    (canonicalGeometricPoint_image D.site D.base D.base_mem W.toFunctor) hγX]
  exact properPushforwardCoeff_eq_cycleCoeffOfModule D sX hX sY hY f
    (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 W hW) k γX γY hdata

end ClosedSubspace

end AlgebraicGeometry.Space

end
