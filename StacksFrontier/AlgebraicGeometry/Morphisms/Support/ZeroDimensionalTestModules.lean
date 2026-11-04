module

public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentHomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherent modules with zero-dimensional support, and coherence of cohomology in every degree

Two ingredients for hypotheses quantified over the coherent `𝒪_X`-modules `ℱ` with
`dim (Supp ℱ) = 0`.

The first produces such modules. For an ideal sheaf `ℐ` on a locally Noetherian scheme `X` and
`t ≥ 1`, the `𝒪_X`-module `𝒪_X/ℐ^t` — the direct image of the structure sheaf of the closed
subscheme cut out by `ℐ^t` — is coherent with support the support of `ℐ`. Taking for `ℐ` the
vanishing ideal sheaf of a closed point `x` gives, for each `t ≥ 1`, a coherent module `𝒪_X/𝔪_x^t`
whose support is exactly `{x}`, hence of topological Krull dimension zero.

The second concerns the cohomology sheaves of a pseudo-coherent, in particular of a perfect,
object of `D(𝒪_X)`: on a locally Noetherian scheme every `H^i` is coherent, hence of finite type,
with no restriction to the top nonvanishing degree.

## Main definitions

* `AlgebraicGeometry.idealPowQuotient`: `𝒪_X/ℐ^t`, the direct image of the structure sheaf of the
  closed subscheme cut out by the `t`-th power of an ideal sheaf.
* `AlgebraicGeometry.pointTestModule`: `𝒪_X/𝔪_x^t`, the case of the vanishing ideal sheaf of a
  point.

## Main results

* `AlgebraicGeometry.isCoherent_idealPowQuotient` and
  `AlgebraicGeometry.supp_idealPowQuotient`: `𝒪_X/ℐ^t` is coherent, and its support is the
  support of `ℐ^t`.
* `AlgebraicGeometry.isCoherent_pointTestModule`,
  `AlgebraicGeometry.supp_pointTestModule` and
  `AlgebraicGeometry.topologicalKrullDim_supp_pointTestModule`: for a closed point `x` and
  `t ≥ 1` the module `𝒪_X/𝔪_x^t` is coherent, its support is `{x}`, and that support has
  topological Krull dimension zero.
* `AlgebraicGeometry.isCoherent_homology_of_isPseudoCoherent` and
  `AlgebraicGeometry.isFiniteType_homology_of_isPseudoCoherent`: on a locally Noetherian scheme
  the cohomology sheaves of a pseudo-coherent object of `D(𝒪_X)` are coherent, hence of finite
  type, in every degree.
* `AlgebraicGeometry.isCoherent_homology_of_isPerfect` and
  `AlgebraicGeometry.isFiniteType_homology_of_isPerfect`: the same for a perfect object.

## Implementation notes

The support of `𝒪_X/ℐ^t` is computed through `Stacks.Chow.supp_pushforwardStructureSheaf`: the
support of the direct image of the structure sheaf along a closed immersion is the range of that
immersion, which for `(ℐ^t).subschemeι` is the support of `ℐ^t`, and powers of an ideal sheaf
have the same support as the ideal sheaf itself.

Coherence of `H^i` in every degree combines two results, neither of which gives it alone:
`AlgebraicGeometry.isCoherent_homology_of_isPseudoCoherentFrom` needs quasi-coherence of all the
cohomology sheaves, and `AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent` supplies
exactly that for a pseudo-coherent object. Pseudo-coherence gives `m`-pseudo-coherence for every
`m`, so the degree in question is never below the approximation degree and no truncation argument
is needed. The derived category is read at `CategoryTheory.HasDerivedCategory.standard`, the
model at which the quasi-coherence input is consumed.

## References

* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u d

namespace AlgebraicGeometry

/-! ### Coherent modules supported on the support of an ideal sheaf -/

variable {X : Scheme.{u}}

/-- `𝒪_X/ℐ^t`: the structure sheaf of the closed subscheme cut out by the `t`-th power of an
ideal sheaf `ℐ`, pushed forward to `X`. For `t ≥ 1` and `ℐ` the vanishing ideal sheaf of a point
this is the `t`-th infinitesimal neighbourhood of that point. -/
@[ega "II 8.10.1" "partial",
  ega "III 4.1.7" "special case",
  ega "IV 11.9.11" "special case",
  sga "2 VI 2.2" "partial"]
def idealPowQuotient (I : X.IdealSheafData) (t : ℕ) : X.Modules :=
  (Scheme.Modules.pushforward (I ^ t).subschemeι).obj
    (Stacks.Ample.unitModule (I ^ t).subscheme)

/-- **`𝒪_X/ℐ^t` is coherent** on a locally Noetherian scheme: it is the direct image of the
structure sheaf of a closed subscheme along a closed immersion. -/
@[ega "IV 11.9.11" "special case"]
theorem isCoherent_idealPowQuotient [IsLocallyNoetherian X] (I : X.IdealSheafData) (t : ℕ) :
    (idealPowQuotient I t).IsCoherent :=
  Stacks.Chow.isCoherent_pushforwardStructureSheaf (I ^ t).subschemeι

/-- **The support of `𝒪_X/ℐ^t` is the support of `ℐ^t`.** Off the range of a closed immersion the
stalks of a direct image vanish, and on the range the stalk of the structure sheaf is a local
ring. -/
@[ega "IV 19.1.7" "special case"]
theorem supp_idealPowQuotient (I : X.IdealSheafData) (t : ℕ) :
    SheafOfModules.supp (idealPowQuotient I t) = ((I ^ t).support : Set X) :=
  (Stacks.Chow.supp_pushforwardStructureSheaf (I ^ t).subschemeι).trans
    (Scheme.IdealSheafData.range_subschemeι _)

/-- The support of `𝒪_X/ℐ^t` is the support of `ℐ` once `t ≥ 1`. -/
theorem supp_idealPowQuotient_of_ne_zero (I : X.IdealSheafData) {t : ℕ} (ht : t ≠ 0) :
    SheafOfModules.supp (idealPowQuotient I t) = (I.support : Set X) := by
  rw [supp_idealPowQuotient, Scheme.IdealSheafData.support_pow I t ht]

/-! ### Test modules at a closed point -/

/-- `𝒪_X/𝔪_x^t`: the structure sheaf of the closed subscheme cut out by the `t`-th power of the
vanishing ideal sheaf of the closure of `{x}`, pushed forward to `X`. -/
def pointTestModule (x : X) (t : ℕ) : X.Modules :=
  idealPowQuotient (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))) t

/-- **`𝒪_X/𝔪_x^t` is coherent** on a locally Noetherian scheme. -/
theorem isCoherent_pointTestModule [IsLocallyNoetherian X] (x : X) (t : ℕ) :
    (pointTestModule x t).IsCoherent :=
  isCoherent_idealPowQuotient _ t

/-- **The support of `𝒪_X/𝔪_x^t` at a closed point `x` is `{x}`**, for every `t ≥ 1`: the
support of the vanishing ideal sheaf of `closure {x}` is `closure {x} = {x}`, and powers do not
change it. -/
theorem supp_pointTestModule (x : X) (hx : IsClosed ({x} : Set X)) {t : ℕ} (ht : t ≠ 0) :
    SheafOfModules.supp (pointTestModule x t) = {x} := by
  rw [pointTestModule, supp_idealPowQuotient_of_ne_zero _ ht,
    ← Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
  exact hx.closure_eq

/-- A nonempty subsingleton space has topological Krull dimension zero: the whole space is its
only irreducible closed subset. -/
theorem topologicalKrullDim_eq_zero_of_nonempty_subsingleton {Z : Type*} [TopologicalSpace Z]
    [Nonempty Z] [Subsingleton Z] : topologicalKrullDim Z = 0 := by
  have : Nonempty (IrreducibleCloseds Z) :=
    ⟨⟨Set.univ, ⟨Set.univ_nonempty, Set.subsingleton_univ.isPreirreducible⟩, isClosed_univ⟩⟩
  have : Subsingleton (IrreducibleCloseds Z) :=
    ⟨fun T T' => SetLike.ext' (T.isIrreducible'.1.eq_univ.trans T'.isIrreducible'.1.eq_univ.symm)⟩
  exact Order.krullDim_eq_zero

/-- **`𝒪_X/𝔪_x^t` has zero-dimensional support** at a closed point `x`, for every `t ≥ 1`: its
support is the one-point subspace `{x}`. This is the hypothesis under which [Stacks, Tag 0FZ9]
quantifies over coherent modules. -/
theorem topologicalKrullDim_supp_pointTestModule (x : X) (hx : IsClosed ({x} : Set X))
    {t : ℕ} (ht : t ≠ 0) :
    topologicalKrullDim (SheafOfModules.supp (pointTestModule x t)) = 0 := by
  rw [supp_pointTestModule x hx ht]
  exact topologicalKrullDim_eq_zero_of_nonempty_subsingleton

/-! ### Coherence of the cohomology sheaves in every degree -/

attribute [local instance] HasDerivedCategory.standard

/-- **The cohomology sheaves of a pseudo-coherent object of `D(𝒪_X)` on a locally Noetherian
scheme are coherent in every degree.**

A pseudo-coherent object is `m`-pseudo-coherent for every `m`, and it has quasi-coherent
cohomology in every degree by [Stacks, Tag 08E5], which is the input that [Stacks, Tag 08E8]
needs to turn `m`-pseudo-coherence into coherence of `H^i` for `i ≥ m`. -/
theorem isCoherent_homology_of_isPseudoCoherent (X : Scheme.{u}) [IsLocallyNoetherian X]
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsCoherent := by
  have hqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent X E hE
  exact isCoherent_homology_of_isPseudoCoherentFrom X E i hqc
    (RingedSpace.IsPseudoCoherent.isPseudoCoherentFrom hE i) i le_rfl

/-- **The cohomology sheaves of a pseudo-coherent object of `D(𝒪_X)` on a locally Noetherian
scheme are of finite type in every degree**, being coherent. -/
theorem isFiniteType_homology_of_isPseudoCoherent (X : Scheme.{u}) [IsLocallyNoetherian X]
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsFiniteType :=
  (isCoherent_homology_of_isPseudoCoherent X E hE i).isFiniteType

/-- **The cohomology sheaves of a perfect object of `D(𝒪_X)` on a locally Noetherian scheme are
coherent in every degree**: a perfect object is pseudo-coherent. -/
theorem isCoherent_homology_of_isPerfect (X : Scheme.{u}) [IsLocallyNoetherian X]
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsCoherent :=
  isCoherent_homology_of_isPseudoCoherent X E hE.isPseudoCoherent i

/-- **The cohomology sheaves of a perfect object of `D(𝒪_X)` on a locally Noetherian scheme are
of finite type in every degree**, with no restriction to the top nonvanishing degree. -/
theorem isFiniteType_homology_of_isPerfect (X : Scheme.{u}) [IsLocallyNoetherian X]
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsFiniteType :=
  (isCoherent_homology_of_isPerfect X E hE i).isFiniteType

/-- **The cohomology sheaves of a perfect object are coherent in every degree**, with
perfectness read in the `Stacks.Cohomology.PerfectComplexes` spelling of [Stacks, Tag 08CM]. -/
theorem isCoherent_homology_of_isPerfect' (X : Scheme.{u}) [IsLocallyNoetherian X]
    (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := X.toRingedSpace) E) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsCoherent :=
  isCoherent_homology_of_isPerfect X E hE i

/-- **The cohomology sheaves of a perfect object are of finite type in every degree**, with
perfectness read in the `Stacks.Cohomology.PerfectComplexes` spelling of [Stacks, Tag 08CM]. -/
theorem isFiniteType_homology_of_isPerfect' (X : Scheme.{u}) [IsLocallyNoetherian X]
    (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := X.toRingedSpace) E) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsFiniteType :=
  (isCoherent_homology_of_isPerfect' X E hE i).isFiniteType

end AlgebraicGeometry

end
