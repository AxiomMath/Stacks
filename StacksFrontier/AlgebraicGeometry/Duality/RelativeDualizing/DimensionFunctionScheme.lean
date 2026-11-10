module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionFunction
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionAtLocalization
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionSpecialization

/-!
# The dimension function of a dualizing complex on a locally Noetherian scheme

[Stacks, Tag 0AWF] has two conclusions for a locally Noetherian scheme `X` carrying a dualizing
complex `ω_X^•`: that `X` is universally catenary, and that the function `x ↦ δ(x)` determined by
the rule that `ω_{X,x}^•⟦-δ(x)⟧` is a *normalized* dualizing complex over `𝒪_{X,x}` is a
dimension function on `X`.  The first is
`Stacks.Duality.isUniversallyCatenary_of_isDualizingComplex`.  The second is proved here.

## Main definitions

* `Stacks.Duality.IsDualizingModelOn` — the witness of `Stacks.Duality.HasDualizingModelOn`,
  i.e. the predicate "`ω` is a dualizing complex over `Γ(X, U)` whose associated sheaf is
  `K|_U`" for an affine open `U`.
* `Stacks.Duality.IsNormalizedShiftAt` — the source's condition at one point: `ω^•_{X,y}⟦-n⟧` is
  a normalized dualizing complex over the local ring `𝒪_{X,y}`, where `ω^•_{X,y}` is the
  extension of a dualizing model to `𝒪_{X,y}`.
* `Stacks.Duality.IsDualizingShiftFunction` — the resulting condition on `δ : X → ℤ`: at every
  point some affine open neighbourhood carries a dualizing model `ω` of `K` with
  `IsNormalizedShiftAt hU ω y (δ y)` for every `y` of that neighbourhood.
* `Stacks.Duality.IsDualizingDimensionFunction` — the same condition with the shift named as the
  value of the dimension function of the model ([Stacks, Tag 0A7W],
  `Dualizing.dualizingDimension`).

## Main results

* `Stacks.Duality.isNormalizedShiftAt_iff_eq_dualizingDimension` and
  `Stacks.Duality.isDualizingShiftFunction_iff_isDualizingDimensionFunction` — the two readings
  of the condition on `δ` agree.
* `Stacks.Duality.exists_dimensionFunction_of_isDualizingShiftFunction` — the
  dimension-function clause of [Stacks, Tag 0AWF] for `δ` read off the dualizing models: such a
  `δ` is a dimension function on `X`.
* `Stacks.Duality.exists_isDualizingShiftFunction_of_isAffine` — on an affine scheme the
  function `δ` exists, so the hypothesis is satisfiable and the clause is unconditional there.
* `Stacks.Duality.isUniversallyCatenary_and_exists_dimensionFunction` — the two clauses of
  [Stacks, Tag 0AWF] together, for `δ` read off the dualizing models.

[Stacks, Tag 0AWF] itself, with `δ(x)` read off the derived stalk of `K` as in the source, is
`Stacks.Duality.isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction` in
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/DerivedStalkModel.lean`, which builds on
this file.

On a *general* locally Noetherian scheme the function `δ` exists too, so the hypothesis of the
results below is dischargeable and both clauses of [Stacks, Tag 0AWF] hold outright; that is
`Stacks.Duality.exists_isDualizingShiftFunction` and
`Stacks.Duality.isUniversallyCatenary_and_exists_dimensionFunction_of_isDualizingComplex` in
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/DimensionFunctionSchemeExistence.lean`,
which cannot live here because it uses the affine translation table of
`StacksFrontier/AlgebraicGeometry/Duality/CohenMacaulayLocus.lean`.

## Implementation notes

**Why `δ` is a hypothesis.** The integer `δ(x)` of the source is characterised by a property of
`ω_{X,x}^•`, not given by a formula, so the statement "the function `x ↦ δ(x)` is a dimension
function" is the statement that *any* function with the characterising property is one; that is
the shape used here, and it is the shape
`AlgebraicGeometry.Space.exists_dimensionFunction_of_isDualizingComplex_chart` uses for [Stacks,
Tag 0E53], the analogue for algebraic spaces.  Nothing is chosen out of an existence statement.
The hypothesis is not vacuous, and is in fact dischargeable:
`Stacks.Duality.exists_isDualizingShiftFunction_of_isAffine` produces `δ` on an affine scheme,
and `Stacks.Duality.exists_isDualizingShiftFunction` produces it on any locally Noetherian
scheme.  The latter means matching the dualizing models over two affine opens at a common
point, which is done in
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/DimensionFunctionSchemeExistence.lean`
by comparing the vanishing patterns of the two extensions to `𝒪_{X,y}` rather than by
identifying the two extensions.

**How the characterising property is spelled.**  The condition `IsNormalizedShiftAt` is the
source's, over the source's ring: `𝒪_{X,y}` is the local ring of `X` at `y`, and the condition
is that a shift of `ω^•_{X,y}` is a normalized dualizing complex over it.  What differs is how
`ω^•_{X,y}` is produced.  The source takes the derived stalk of `K`; here it is the extension
of a dualizing model `ω` over an affine open `U ∋ y` to `𝒪_{X,y}`, which is legitimate because
`𝒪_{X,y}` *is* the localization of `Γ(X, U)` at the prime of `y`
(`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), so that extension is the localization
of `ω` at that prime.  The identification of the derived stalk of `K` with the localization of
a model is `Stacks.Duality.nonempty_derivedStalkOfComplex_iso_extendScalars`, in
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/DerivedStalkModel.lean`; it is what
connects the condition here with `Stacks.Duality.associatedShiftFunction`.

**The proof.**  Being a dimension function is local
(`TopologicalSpace.exists_dimensionFunction_of_cover`), an affine open is homeomorphic to the
spectrum of its sections (`AlgebraicGeometry.IsAffineOpen.primeIdealOf`), and over that spectrum
the dimension function of a dualizing complex is a dimension function, which is the affine case
[Stacks, Tag 0A7Z] in the bundled form `Dualizing.dualizingDimensionFunction`.  This is exactly
the source's "immediate from the affine case and the definitions".

**Derived categories.** `D(𝒪_X)` is an instance argument, as in
`Stacks.Duality.IsDualizingComplex`, so no model is pinned for it.  The derived categories of
`ModuleCat Γ(X, U)` and of `𝒪_U`-modules depend on the affine open `U`, which the statements
quantify, so they are at `CategoryTheory.HasDerivedCategory.standard`, installed as a local
instance below; this is forced for `ModuleCat Γ(X, U)` anyway, because
`Dualizing.IsNormalizedDualizingComplex` and hence `Dualizing.dualizingDimension` bake that
model into their own types, and it is the choice `Stacks.Duality.HasDualizingModelOn` seals
inside its own body.

## References

* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0A7Z](https://stacks.math.columbia.edu/tag/0A7Z)
* [Stacks Project, Tag 0A7W](https://stacks.math.columbia.edu/tag/0A7W)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 02I9](https://stacks.math.columbia.edu/tag/02I9)
* [Stacks Project, Tag 0E53](https://stacks.math.columbia.edu/tag/0E53)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u w

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

omit [IsLocallyNoetherian X] [HasDerivedCategory X.Modules] in
/-- An affine open of a scheme is homeomorphic to the spectrum of its sections, by
`AlgebraicGeometry.IsAffineOpen.primeIdealOf`; in particular that map is an open embedding. -/
theorem isOpenEmbedding_primeIdealOf {U : X.Opens} (hU : IsAffineOpen U) :
    Topology.IsOpenEmbedding (fun y : U => hU.primeIdealOf y) :=
  (Scheme.homeoOfIso hU.isoSpec).isOpenEmbedding

/-- `IsDualizingModelOn K hU ω` says that `ω` is a *dualizing model* of `K` over the affine open
`U`: a dualizing complex over `Γ(X, U)` ([Stacks, Tag 0A7B]) whose associated sheaf, transported
along `U ≅ Spec Γ(X, U)`, is `K|_U`.

This is the witness of `Stacks.Duality.HasDualizingModelOn`, which is the existential over
`ω`. -/
def IsDualizingModelOn (K : DerivedCategory X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, U))) : Prop :=
  letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  Dualizing.IsDualizingComplex ω ∧
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)

/-- Carrying a dualizing model is the existence of a dualizing model. -/
theorem hasDualizingModelOn_iff_exists_isDualizingModelOn (K : DerivedCategory X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) :
    HasDualizingModelOn K U hU ↔ ∃ ω, IsDualizingModelOn K hU ω :=
  Iff.rfl

/-- **The condition characterising the function `δ` of [Stacks, Tag 0AWF].** At every point of
`X` some affine open neighbourhood `U` carries a dualizing model `ω` of `K` whose dimension
function ([Stacks, Tag 0A7W]) is `δ` on `U`: for `y ∈ U` the value `δ y` is the unique integer
`n` for which the localization of `ω` at the prime of `y` is a normalized dualizing complex over
`𝒪_{X,y}` after shifting by `-n`. -/
def IsDualizingDimensionFunction (K : DerivedCategory X.Modules) (δ : X → ℤ) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)), IsDualizingModelOn K hU ω ∧
      ∀ y : U, δ y = Dualizing.dualizingDimension.{u, u} ω (hU.primeIdealOf y)

/-- **The normalizing shift of a dualizing model at a point, the source's own condition.**
`IsNormalizedShiftAt hU ω y n` says that `ω^•_{X,y}⟦-n⟧` is a *normalized* dualizing complex
over the local ring `𝒪_{X,y}`, where `ω^•_{X,y}` is the extension of the dualizing model `ω` to
`𝒪_{X,y}`.  That local ring *is* the localization of `Γ(X, U)` at the prime of `y`
(`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), so this is the complex the source
calls `ω^•_{X,y}`, read off a dualizing model rather than off the derived stalk of `K`. -/
def IsNormalizedShiftAt {U : X.Opens} (hU : IsAffineOpen U)
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, U))) (y : U) (n : ℤ) : Prop :=
  letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := hU.isLocalization_stalk y
  letI : IsNoetherianRing ↥(X.presheaf.stalk y.1) :=
    IsLocalization.isNoetherianRing (hU.primeIdealOf y).asIdeal.primeCompl _ inferInstance
  Dualizing.IsNormalizedDualizingComplex.{u, u}
    (((StacksDraft.PseudoCoherence.derivedExtensionScalars
      (algebraMap Γ(X, U) ↥(X.presheaf.stalk y.1))).obj ω)⟦-n⟧)

omit [HasDerivedCategory X.Modules] in
/-- **The two readings of the condition on `δ` agree.** The shift normalizing `ω^•_{X,y}` is the
value at the prime of `y` of the dimension function of the model, [Stacks, Tag 0A7W]. -/
theorem isNormalizedShiftAt_iff_eq_dualizingDimension {U : X.Opens} (hU : IsAffineOpen U)
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (hω : letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
      Dualizing.IsDualizingComplex ω)
    (y : U) (n : ℤ) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    IsNormalizedShiftAt hU ω y n ↔
      n = Dualizing.dualizingDimension.{u, u} ω (hU.primeIdealOf y) :=
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := hU.isLocalization_stalk y
  Dualizing.isNormalizedDualizingComplex_derivedExtensionScalars_iff_eq_dualizingDimension
    ω hω (hU.primeIdealOf y) ↥(X.presheaf.stalk y.1) n

/-- **The condition characterising the function `δ` of [Stacks, Tag 0AWF], in the source's
shape.** At every point of `X` some affine open neighbourhood carries a dualizing model `ω` of
`K` such that, at every `y` of that neighbourhood, `ω^•_{X,y}⟦-δ(y)⟧` is a normalized dualizing
complex over `𝒪_{X,y}`. -/
def IsDualizingShiftFunction (K : DerivedCategory X.Modules) (δ : X → ℤ) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)), IsDualizingModelOn K hU ω ∧
      ∀ y : U, IsNormalizedShiftAt hU ω y (δ y)

/-- The two readings of the condition on `δ` agree. -/
theorem isDualizingShiftFunction_iff_isDualizingDimensionFunction
    (K : DerivedCategory X.Modules) (δ : X → ℤ) :
    IsDualizingShiftFunction K δ ↔ IsDualizingDimensionFunction K δ := by
  constructor <;> intro h x <;> obtain ⟨U, hU, hxU, ω, hmodel, hy⟩ := h x <;>
    exact ⟨U, hU, hxU, ω, hmodel,
      fun y => by
        have := isNormalizedShiftAt_iff_eq_dualizingDimension hU ω hmodel.1 y (δ y)
        tauto⟩

/-- **The dimension-function clause of [Stacks, Tag 0AWF], for the model reading of `δ`.** On a
locally Noetherian scheme `X` with a dualizing complex `K`, a function `δ : X → ℤ` determined at
every point by the dualizing models of `K` over affine opens is a dimension function on `X`.

Being a dimension function is local, and over an affine open `U` the function is the dimension
function of a dualizing complex over `Γ(X, U)` read along the homeomorphism
`U ≅ Spec Γ(X, U)`, which is the affine case [Stacks, Tag 0A7Z]. -/
theorem exists_dimensionFunction_of_isDualizingDimensionFunction
    (K : DerivedCategory X.Modules) (δ : X → ℤ) (hδ : IsDualizingDimensionFunction K δ) :
    ∃ d : DimensionFunction X, ∀ x : X, d x = δ x := by
  refine TopologicalSpace.exists_dimensionFunction_of_cover δ fun x => ?_
  obtain ⟨U, hU, hxU, ω, ⟨hω, -⟩, hδU⟩ := hδ x
  have hA : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  refine ⟨(U : Set X), U.isOpen, hxU,
    (Dualizing.dualizingDimensionFunction.{u, u} ω hω).comp (isOpenEmbedding_primeIdealOf hU),
    fun y => ?_⟩
  rw [TopologicalSpace.DimensionFunction.comp_apply,
    Dualizing.dualizingDimensionFunction_apply]
  exact (hδU y).symm

/-- **The dimension-function clause of [Stacks, Tag 0AWF], for the model reading of `δ`.** On a
locally Noetherian scheme `X` with a dualizing complex `K`, a function `δ : X → ℤ` such that
`ω^•_{X,x}⟦-δ(x)⟧` is a normalized dualizing complex over `𝒪_{X,x}` at every point is a dimension
function on `X`.

This is the source's statement, with `ω^•_{X,x}` read as the extension to `𝒪_{X,x}` of a
dualizing model of `K` over an affine open neighbourhood of `x`.  Being a dimension function is
local, and over an affine open `U` the function is the dimension function of a dualizing complex
over `Γ(X, U)` read along the homeomorphism `U ≅ Spec Γ(X, U)`, which is the affine case
[Stacks, Tag 0A7Z]; this is the source's "immediate from the affine case and the
definitions". -/
theorem exists_dimensionFunction_of_isDualizingShiftFunction
    (K : DerivedCategory X.Modules) (δ : X → ℤ) (hδ : IsDualizingShiftFunction K δ) :
    ∃ d : DimensionFunction X, ∀ x : X, d x = δ x :=
  exists_dimensionFunction_of_isDualizingDimensionFunction K δ
    ((isDualizingShiftFunction_iff_isDualizingDimensionFunction K δ).mp hδ)

/-- **[Stacks, Tag 0AWF] for an affine scheme, with no hypothesis on `δ`.** On an affine locally
Noetherian scheme carrying a dualizing complex the function `δ` of the source exists: the whole
space is an affine open, so a single dualizing model governs every point, and its dimension
function is a dimension function on `X`.

In particular the hypothesis `Stacks.Duality.IsDualizingShiftFunction` of the theorems above is
satisfiable.  Over a general locally Noetherian scheme producing `δ` means matching the models
over two affine opens at a common point; that is
`Stacks.Duality.exists_isDualizingShiftFunction`, which subsumes this lemma. -/
theorem exists_isDualizingShiftFunction_of_isAffine [IsAffine X]
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K) :
    ∃ δ : X → ℤ, IsDualizingShiftFunction K δ ∧
      ∃ d : DimensionFunction X, ∀ x : X, d x = δ x := by
  have hU : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  have hA : IsNoetherianRing Γ(X, (⊤ : X.Opens)) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, hU⟩
  obtain ⟨ω, hω, he⟩ := hK ⊤ hU
  have hδ : IsDualizingShiftFunction K
      fun x => Dualizing.dualizingDimension.{u, u} ω (hU.primeIdealOf ⟨x, trivial⟩) :=
    fun x => ⟨⊤, hU, trivial, ω, ⟨hω, he⟩, fun y =>
      (isNormalizedShiftAt_iff_eq_dualizingDimension hU ω hω y _).mpr rfl⟩
  exact ⟨_, hδ, exists_dimensionFunction_of_isDualizingShiftFunction K _ hδ⟩

/-- **The two clauses of [Stacks, Tag 0AWF], for the model reading of `δ`.** A locally
Noetherian scheme carrying a dualizing complex is universally catenary, and a function `δ`
satisfying `Stacks.Duality.IsDualizingShiftFunction` is a dimension function. The source's
statement, with `δ` read off the derived stalk, is
`Stacks.Duality.isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction`. -/
theorem isUniversallyCatenary_and_exists_dimensionFunction
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K)
    (δ : X → ℤ) (hδ : IsDualizingShiftFunction K δ) :
    AlgebraicGeometry.Scheme.IsUniversallyCatenary X ∧
      ∃ d : DimensionFunction X, ∀ x : X, d x = δ x :=
  ⟨isUniversallyCatenary_of_isDualizingComplex hK,
    exists_dimensionFunction_of_isDualizingShiftFunction K δ hδ⟩

end Stacks.Duality

end
