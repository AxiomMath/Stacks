module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorByBaseModuleOfHomLinearIso
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChartTensorByBaseModule
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyOverBaseFilteredColimits
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.RingTheory.Flat.TensorFunctorUniverse

/-!
# The dévissage of Stacks 073K, part (2): cohomology commutes with tensoring by a flat module

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `V₀` be a terminal chart of the small étale site of `Y` with coordinate ring
`A = Γ(chartScheme V₀, ⊤)`, and let `𝓕` be an `𝒪_X`-module.  The functor

  `M ↦ H^i(X, 𝓕 ⊗_A M)`,

with the cohomology read as an `A`-module, is an additive `A`-linear functor
`ModuleCat.{u} A ⥤ ModuleCat.{u + 1} A` which commutes with filtered colimits indexed by a
category in `Type u`, provided `X` is quasi-compact and absolutely quasi-separated: the first
factor `M ↦ 𝓕 ⊗_A M` has all three properties with nothing assumed of `X`, and the
cohomological factor has them by **Stacks 073E**.  The dévissage of **Stacks 058G** — Lazard's
theorem, in the form `Stacks.FlatDevissage.isIso_tensorComparisonUniv_app_of_flat_succ` — then
turns the value at the free module of rank one into the whole of the flat case: the canonical
comparison

  `H^i(X, 𝓕) ⊗_A M ⟶ H^i(X, 𝓕 ⊗_A M)`

is an isomorphism for every flat `A`-module `M`.

The value of the functor at `M = A` is `H^i(X, 𝓕)` itself, by
`AlgebraicGeometry.Space.cohomologyTensorFunctorUnitIso`, so the source of the comparison at
`M` is `H^i(X, 𝓕) ⊗_A M` as the source writes it.

## Main definitions

* `CategoryTheory.Functor.linear_ofRingHom`: a functor linear over `S` is linear over any
  commutative ring mapping to `S`.
* `ModuleCat.linear_restrictScalars_comp` and
  `ModuleCat.linear_restrictScalars_base`: restriction of scalars along a ring
  map is a linear functor for the linear structures that a ring map to its source induces.
* `AlgebraicGeometry.Space.baseChartBaseRingHom` and
  `AlgebraicGeometry.Space.baseChartGlobalSectionRingHom`: the ring maps `A ⟶ Γ(Y, 𝒪_Y)` and
  `A ⟶ Γ(X, 𝒪_X)`, and `AlgebraicGeometry.Space.baseChartRestrictScalars`, which reads a
  `Γ(Y, 𝒪_Y)`-module as an `A`-module.
* `AlgebraicGeometry.Space.cohomologyFunctorOverBaseChart`: the cohomology
  `H^i(X, −)` of `𝒪_X`-modules read as an `A`-module.
* `AlgebraicGeometry.Space.cohomologyTensorFunctor`: **the functor
  `M ↦ H^i(X, 𝓕 ⊗_A M)`** from `A`-modules in `Type u` to `A`-modules in `Type (u + 1)`.
* `AlgebraicGeometry.Space.cohomologyTensorComparison`: **the canonical comparison
  `H^i(X, 𝓕) ⊗_A − ⟶ H^i(X, 𝓕 ⊗_A −)`.**
* `AlgebraicGeometry.Space.cohomologyTensorFunctorUnitIso`: the value of the functor at the
  free module of rank one is `H^i(X, 𝓕)`.

## Main results

* `AlgebraicGeometry.Space.additive_cohomologyTensorFunctor`,
  `AlgebraicGeometry.Space.linear_cohomologyTensorFunctor` and
  `AlgebraicGeometry.Space.preservesFilteredColimitsOfSize_cohomologyTensorFunctor`: the
  functor `M ↦ H^i(X, 𝓕 ⊗_A M)` is additive, `A`-linear, and commutes with filtered colimits
  indexed by a category in `Type u`.
* `AlgebraicGeometry.Space.isIso_cohomologyTensorComparison_app_of_flat`: **the comparison
  `H^i(X, 𝓕) ⊗_A M ⟶ H^i(X, 𝓕 ⊗_A M)` is an isomorphism for every flat `A`-module `M`.**

## Implementation notes

*Which way the chart equivalence is used.*  The cohomology of this development is a module over
`Γ(Y, 𝒪_Y) = RingCat.sectionsSubring _`, a ring in `Type (u + 1)`, while the coordinate ring
`A` of the base lies in `Type u`.  The passage between them is
`AlgebraicGeometry.Space.globalSectionsChartRingEquiv`, whose source is `Γ(Y, 𝒪_Y)` and whose
target is `A`; restriction of scalars runs along a ring map *into* the ring of the module, so
`AlgebraicGeometry.Space.baseChartRestrictScalars` is `ModuleCat.restrictScalars` along
`AlgebraicGeometry.Space.baseChartBaseRingHom`, which is
`(globalSectionsChartRingEquiv B S hS Y hV₀).symm.toRingHom : A →+* Γ(Y, 𝒪_Y)` with its target
restated at the spelling of the sheaf of rings that the cohomology of this development uses.

*The three linear structures, and why they are passed as `letI`.*  `A`-linearity is a statement
about three categories, none of which is `A`-linear on its own: the `𝒪_X`-modules, the
`Γ(X, 𝒪_X)`-modules and the `Γ(Y, 𝒪_Y)`-modules all become `A`-linear only through a ring map
out of `A`, and such a map is data depending on `f` and on the chart.  The one on `𝒪_X`-modules
is forced: it has to be `Stacks.TensorByBaseModule.linearOfHom`, since that is the structure for
which `Stacks.TensorByBaseModule.tensorByBaseModuleOfHom_linear` holds, and it is
`CategoryTheory.Linear.ofRingHom` of the global-section form
`AlgebraicGeometry.Space.baseChartGlobalSectionRingHom` of the coefficient map.  The other two
are `CategoryTheory.Linear.ofRingHom` of that same ring map and of the chart equivalence, which
is what makes `AlgebraicGeometry.Space.baseChartGlobalSectionRingHom_eq` — that the ring map to
`Γ(X, 𝒪_X)` factors through `Γ(Y, 𝒪_Y)` — the hypothesis the middle factor needs.

*Why the composite is bracketed.*  **Stacks 073E** is available as
`AlgebraicGeometry.Space.preservesColimit_cohomologyOverBase`, a statement about the *composite*
of the derived global sections with restriction of scalars along `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` and
not about either factor; `AlgebraicGeometry.Space.cohomologyFunctorOverBaseChart` therefore
keeps those two together, so that instance search for colimit preservation of the whole
composite meets them as one functor.

*Explicit universes at the dévissage.*  `Stacks.FlatDevissage.tensorComparisonUniv` is stated
for a target `ModuleCat.{max uA w} A`, and Lean cannot solve `max u ?w = u + 1`, so its universe
arguments are supplied as `.{u, u + 1}`; see the implementation notes of
`StacksFrontier.RingTheory.Flat.TensorFunctorUniverse`.

No declaration here carries a `stacks` tag.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
* [Stacks Project, Tag 058G](https://stacks.math.columbia.edu/tag/058G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules
open Stacks.FlatDevissage
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.TensorByBaseModule hiding ringSheaf

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] AlgebraicGeometry.RingedSite.globalSectionsCommRing

noncomputable section

universe v u

namespace CategoryTheory.Functor

/-- **A functor linear over `S` is linear over any commutative ring mapping to `S`**, for the
linear structures `CategoryTheory.Linear.ofRingHom` puts on its source and target: a scalar acts
through its image, on both sides, so the identity to be checked is the one it already
satisfies. -/
theorem linear_ofRingHom {R S : Type*} [CommRing R] [CommRing S] {C D : Type*}
    [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear S C] [CategoryTheory.Linear S D]
    (φ : R →+* S) (F : C ⥤ D) [Functor.Linear S F] :
    letI := CategoryTheory.Linear.ofRingHom (D := C) φ
    letI := CategoryTheory.Linear.ofRingHom (D := D) φ
    Functor.Linear R F :=
  let := CategoryTheory.Linear.ofRingHom (D := C) φ
  let := CategoryTheory.Linear.ofRingHom (D := D) φ
  ⟨fun f r => F.map_smul (R := S) (φ r) f⟩

end CategoryTheory.Functor

namespace ModuleCat

/-- **Restriction of scalars along `g : S ⟶ T` is `R`-linear** when `S` and `T` are read over
`R` through a ring map `φ : R ⟶ S` and its composite with `g`: a scalar acts on a `T`-module by
`g (φ r)` either way. -/
theorem linear_restrictScalars_comp {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (φ : R →+* S) (g : S →+* T) (ρ : R →+* T) (hρ : ρ = g.comp φ) :
    letI := CategoryTheory.Linear.ofRingHom (D := ModuleCat.{v} T) ρ
    letI := CategoryTheory.Linear.ofRingHom (D := ModuleCat.{v} S) φ
    Functor.Linear R (ModuleCat.restrictScalars.{v} g) := by
  subst hρ
  let := CategoryTheory.Linear.ofRingHom (D := ModuleCat.{v} T) (g.comp φ)
  let := CategoryTheory.Linear.ofRingHom (D := ModuleCat.{v} S) φ
  exact ⟨fun f r => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)⟩

/-- **Restriction of scalars along `g : R ⟶ T` is `R`-linear** for the linear structure that
`g` puts on the `T`-modules and the tautological one on the `R`-modules.  This is the last
factor of the comparison below, the one that lands in the `A`-modules themselves. -/
theorem linear_restrictScalars_base {R T : Type*} [CommRing R] [CommRing T] (g : R →+* T) :
    letI := CategoryTheory.Linear.ofRingHom (D := ModuleCat.{v} T) g
    Functor.Linear R (ModuleCat.restrictScalars.{v} g) :=
  let := CategoryTheory.Linear.ofRingHom (D := ModuleCat.{v} T) g
  ⟨fun _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)⟩

end ModuleCat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The ring map `A ⟶ Γ(Y, 𝒪_Y)`**: the inverse of the chart equivalence
`AlgebraicGeometry.Space.globalSectionsChartRingEquiv`, read with its target spelled through
`AlgebraicGeometry.RingedSite.ringSheaf` of the small étale ringed site.

The restatement is what makes the restriction of scalars below usable: the chart equivalence is
stated with the `AlgebraicGeometry.Space.structureRingSheaf` spelling of that sheaf of rings, and
although the two are definitionally equal, the ring structures instance search finds on their
rings of global sections are not interchangeable for it — the additivity of a restriction of
scalars written at the first spelling is not found when the functor is composed with one written
at the second. -/
def baseChartBaseRingHom (Y : AlgebraicSpaces B S hS) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) :
    baseChartRing B S hS Y V₀ →+*
      RingCat.sectionsSubring
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj :=
  (globalSectionsChartRingEquiv B S hS Y hV₀).symm.toRingHom

/-- **The ring map `A ⟶ Γ(X, 𝒪_X)` attached to a morphism `f : X ⟶ Y` and a terminal chart of
`Y`**: a regular function on the scheme of the chart goes to the compatible family of its
restrictions to the charts of `X`.  This is the global-section form of
`AlgebraicGeometry.Space.baseChartCoefficientMap`, and it is the ring map along which every
category below is read over `A`. -/
def baseChartGlobalSectionRingHom (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) :
    baseChartRing B S hS Y V₀ →+*
      RingCat.sectionsSubring
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj :=
  globalSectionRingHomOfHom _ (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) (baseChartCoefficientMap B S hS f hV₀)

/-- **The ring map `A ⟶ Γ(X, 𝒪_X)` factors through `Γ(Y, 𝒪_Y)`**: it is the chart equivalence
of the base followed by the comparison of global function rings of **Stacks 0732**.  Indeed
`AlgebraicGeometry.Space.globalFunctionsChartRestriction` is evaluation of a compatible family
at a chart, so the family of restrictions of a global function *is* that global function. -/
theorem baseChartGlobalSectionRingHom_eq (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) :
    baseChartGlobalSectionRingHom B S hS f hV₀ =
      (globalSectionsRingHomSite B S hS f).comp (baseChartBaseRingHom B S hS Y hV₀) :=
  rfl

/-- **Reading a `Γ(Y, 𝒪_Y)`-module as a module over the coordinate ring `A` of the base.**  This
is restriction of scalars along `AlgebraicGeometry.Space.baseChartBaseRingHom`, the inverse of
the chart equivalence, which is the ring map `A ⟶ Γ(Y, 𝒪_Y)`. -/
abbrev baseChartRestrictScalars (Y : AlgebraicSpaces B S hS) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) :
    ModuleCat.{u + 1} (RingCat.sectionsSubring
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj) ⥤
      ModuleCat.{u + 1} (baseChartRing B S hS Y V₀) :=
  ModuleCat.restrictScalars (baseChartBaseRingHom B S hS Y hV₀)

/-- **The cohomology `H^i(X, −)` of `𝒪_X`-modules, read as a module over the coordinate ring
`A` of the base.**  The two inner factors are kept together because **Stacks 073E** is available
for their composite, as `AlgebraicGeometry.Space.preservesColimit_cohomologyOverBase`. -/
abbrev cohomologyFunctorOverBaseChart (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    Modules.{u, u} B S hS X.1 X.2 ⥤ ModuleCat.{u + 1} (baseChartRing B S hS Y V₀) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i ⋙
      globalSectionsRestrictScalars B S hS f) ⋙
    baseChartRestrictScalars B S hS Y hV₀

/-- **The functor `M ↦ H^i(X, 𝓕 ⊗_A M)`** of the dévissage of **Stacks 073K**, part (2): an
`A`-module in `Type u` is tensored into `𝓕` and the cohomology of the result is read back over
`A`.  Nothing is assumed of `X` for the functor to exist. -/
def cohomologyTensorFunctor (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1} (hV₀ : IsTerminal V₀)
    (𝓕 : Modules.{u, u} B S hS X.1 X.2) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    ModuleCat.{u} (baseChartRing B S hS Y V₀) ⥤
      ModuleCat.{u + 1} (baseChartRing B S hS Y V₀) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  tensorByBaseChartModule B S hS f hV₀ 𝓕 ⋙ cohomologyFunctorOverBaseChart B S hS f hV₀ i

/-- **`M ↦ H^i(X, 𝓕 ⊗_A M)` is additive.**  Tensoring is additive with nothing assumed of `X`,
a right derived functor of an additive functor is additive, and restriction of scalars is
additive. -/
instance additive_cohomologyTensorFunctor (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) (𝓕 : Modules.{u, u} B S hS X.1 X.2) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (cohomologyTensorFunctor B S hS f hV₀ 𝓕 i).Additive := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have h1 : (tensorByBaseChartModule B S hS f hV₀ 𝓕).Additive := inferInstance
  have h2 : ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).Additive :=
    inferInstance
  have h3 : (globalSectionsRestrictScalars B S hS f).Additive := inferInstance
  have h4 : (baseChartRestrictScalars B S hS Y hV₀).Additive := inferInstance
  dsimp only [cohomologyTensorFunctor, cohomologyFunctorOverBaseChart]
  infer_instance

/-- **`M ↦ H^i(X, 𝓕 ⊗_A M)` is `A`-linear.**

The `𝒪_X`-modules are read over `A` by `Stacks.TensorByBaseModule.linearOfHom`, which is the
structure for which the first factor is linear, and the `Γ(X, 𝒪_X)`- and `Γ(Y, 𝒪_Y)`-modules by
`CategoryTheory.Linear.ofRingHom` of `AlgebraicGeometry.Space.baseChartGlobalSectionRingHom` and
of the chart equivalence.  Global sections are `Γ(X, 𝒪_X)`-linear, hence `A`-linear by
`CategoryTheory.Functor.linear_ofRingHom`; their right derived functors are then `A`-linear by
`CategoryTheory.Functor.linear_rightDerived`; and the two restrictions of scalars are `A`-linear
by `ModuleCat.linear_restrictScalars_comp` and
`ModuleCat.linear_restrictScalars_base`, the first through
`AlgebraicGeometry.Space.baseChartGlobalSectionRingHom_eq`. -/
theorem linear_cohomologyTensorFunctor (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) (𝓕 : Modules.{u, u} B S hS X.1 X.2) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    letI := linearOfHom (baseChartRing B S hS Y V₀) (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (baseChartCoefficientMap B S hS f hV₀)
    letI := Linear.ofRingHom (D := ModuleCat.{u + 1} (RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj))
      (baseChartGlobalSectionRingHom B S hS f hV₀)
    letI := Linear.ofRingHom (D := ModuleCat.{u + 1} (RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj))
      (baseChartBaseRingHom B S hS Y hV₀)
    Functor.Linear (baseChartRing B S hS Y V₀)
      (cohomologyTensorFunctor B S hS f hV₀ 𝓕 i) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  let : Linear (baseChartRing B S hS Y V₀) (Modules.{u, u} B S hS X.1 X.2) :=
    linearOfHom (baseChartRing B S hS Y V₀) (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (baseChartCoefficientMap B S hS f hV₀)
  let := Linear.ofRingHom (D := ModuleCat.{u + 1} (RingCat.sectionsSubring
    (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj))
    (baseChartGlobalSectionRingHom B S hS f hV₀)
  let := Linear.ofRingHom (D := ModuleCat.{u + 1} (RingCat.sectionsSubring
    (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj))
    (baseChartBaseRingHom B S hS Y hV₀)
  have hGS : Functor.Linear (baseChartRing B S hS Y V₀)
      (globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) :=
    Functor.linear_ofRingHom (baseChartGlobalSectionRingHom B S hS f hV₀)
      (globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  have := ModuleCat.linear_restrictScalars_comp.{u + 1}
    (baseChartBaseRingHom B S hS Y hV₀)
    (globalSectionsRingHomSite B S hS f) (baseChartGlobalSectionRingHom B S hS f hV₀)
    (baseChartGlobalSectionRingHom_eq B S hS f hV₀)
  have := ModuleCat.linear_restrictScalars_base.{u + 1}
    (baseChartBaseRingHom B S hS Y hV₀)
  have : Functor.Linear (baseChartRing B S hS Y V₀)
      (tensorByBaseChartModule B S hS f hV₀ 𝓕) :=
    tensorByBaseModuleOfHom_linear (baseChartRing B S hS Y V₀)
      (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2) 𝓕
      (baseChartCoefficientMap B S hS f hV₀)
  dsimp only [cohomologyTensorFunctor, cohomologyFunctorOverBaseChart]
  have : Functor.Linear (baseChartRing B S hS Y V₀)
      ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i) :=
    inferInstance
  infer_instance

/-- **`M ↦ H^i(X, 𝓕 ⊗_A M)` commutes with filtered colimits indexed by a category in
`Type u`**, which is what the dévissage along Lazard's theorem needs.  Tensoring preserves all
colimits of that size with nothing assumed of `X`; the cohomological factor preserves filtered
ones by **Stacks 073E**, in the form
`AlgebraicGeometry.Space.preservesColimit_cohomologyOverBase`; and restriction of scalars
preserves all colimits, being a left adjoint to coextension of scalars. -/
theorem preservesFilteredColimitsOfSize_cohomologyTensorFunctor (hZ : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1} (hV₀ : IsTerminal V₀)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (𝓕 : Modules.{u, u} B S hS X.1 X.2) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    PreservesFilteredColimitsOfSize.{u, u} (cohomologyTensorFunctor B S hS f hV₀ 𝓕 i) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have hrest : PreservesColimitsOfSize.{u, u}
      (baseChartRestrictScalars B S hS Y hV₀) :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u, u + 1}
      (baseChartBaseRingHom B S hS Y hV₀)).leftAdjoint_preservesColimits
  refine ⟨fun I _ _ => ?_⟩
  have h1 : PreservesColimitsOfShape I (tensorByBaseChartModule B S hS f hV₀ 𝓕) :=
    (preservesColimitsOfSize_tensorByBaseChartModule B S hS f hV₀
      𝓕).preservesColimitsOfShape
  have h2 : PreservesColimitsOfShape I
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i ⋙
        globalSectionsRestrictScalars B S hS f) :=
    ⟨fun {D} => preservesColimit_cohomologyOverBase B S hS hZ f hqc hqs i D⟩
  have h3 : PreservesColimitsOfShape I (baseChartRestrictScalars B S hS Y hV₀) :=
    hrest.preservesColimitsOfShape
  have h4 : PreservesColimitsOfShape I
      (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i ⋙
        globalSectionsRestrictScalars B S hS f) ⋙
          baseChartRestrictScalars B S hS Y hV₀) :=
    Limits.comp_preservesColimitsOfShape _ _
  exact Limits.comp_preservesColimitsOfShape _ _

/-! ### The comparison, and its invertibility on flat modules -/

/-- **`H^i(X, 𝓕 ⊗_A A) ≅ H^i(X, 𝓕)`**: the value of the functor `M ↦ H^i(X, 𝓕 ⊗_A M)` at the
free `A`-module of rank one is the cohomology of `𝓕` itself.  This is the cohomology functor
applied to `AlgebraicGeometry.Space.tensorByBaseChartModuleUnitIso`, and it is the component at
which the dévissage of **Stacks 058G** has to see the comparison invertible. -/
def cohomologyTensorFunctorUnitIso (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) (𝓕 : Modules.{u, u} B S hS X.1 X.2) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (cohomologyTensorFunctor B S hS f hV₀ 𝓕 i).obj
        (unitModule (baseChartRing B S hS Y V₀)) ≅
      (cohomologyFunctorOverBaseChart B S hS f hV₀ i).obj 𝓕 :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  (cohomologyFunctorOverBaseChart B S hS f hV₀ i).mapIso
    (tensorByBaseChartModuleUnitIso B S hS f hV₀ 𝓕)

/-- **The canonical comparison `H^i(X, 𝓕) ⊗_A M ⟶ H^i(X, 𝓕 ⊗_A M)`**, natural in the `A`-module
`M`.  It is `Stacks.FlatDevissage.tensorComparisonUniv` of the functor
`AlgebraicGeometry.Space.cohomologyTensorFunctor`, whose value at the free module of rank one is
`H^i(X, 𝓕)` by `AlgebraicGeometry.Space.cohomologyTensorFunctorUnitIso`; on an element it sends
`x ⊗ m` to the image of `x` under the map induced by `a ↦ a • m`.

The three structural hypotheses the comparison needs are the three results above: additivity,
`A`-linearity and preservation of filtered colimits indexed by a category in `Type u`.  The last
is the only one that assumes anything of `X`, and what it assumes is what **Stacks 073E**
assumes: quasi-compactness and absolute quasi-separatedness. -/
def cohomologyTensorComparison (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y)
    {V₀ : SmallEtale B S hS Y.1} (hV₀ : IsTerminal V₀)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (𝓕 : Modules.{u, u} B S hS X.1 X.2) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    haveI : Functor.Linear (baseChartRing B S hS Y V₀)
        (cohomologyTensorFunctor B S hS f hV₀ 𝓕 i) :=
      linear_cohomologyTensorFunctor B S hS f hV₀ 𝓕 i
    haveI : PreservesFilteredColimitsOfSize.{u, u}
        (cohomologyTensorFunctor B S hS f hV₀ 𝓕 i) :=
      preservesFilteredColimitsOfSize_cohomologyTensorFunctor B S hS hZ f hV₀ hqc hqs 𝓕 i
    tensorLeftFunctor ((cohomologyTensorFunctor B S hS f hV₀ 𝓕 i).obj
        (unitModule (baseChartRing B S hS Y V₀))) ⟶
      cohomologyTensorFunctor B S hS f hV₀ 𝓕 i :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  haveI : Functor.Linear (baseChartRing B S hS Y V₀)
      (cohomologyTensorFunctor B S hS f hV₀ 𝓕 i) :=
    linear_cohomologyTensorFunctor B S hS f hV₀ 𝓕 i
  haveI : PreservesFilteredColimitsOfSize.{u, u}
      (cohomologyTensorFunctor B S hS f hV₀ 𝓕 i) :=
    preservesFilteredColimitsOfSize_cohomologyTensorFunctor B S hS hZ f hV₀ hqc hqs 𝓕 i
  tensorComparisonUniv.{u, u + 1} (cohomologyTensorFunctor B S hS f hV₀ 𝓕 i)

/-- **The comparison `H^i(X, 𝓕) ⊗_A M ⟶ H^i(X, 𝓕 ⊗_A M)` is an isomorphism for every flat
`A`-module `M`.**  This is the dévissage of **Stacks 058G** — Lazard's theorem, in the form
`Stacks.FlatDevissage.isIso_tensorComparisonUniv_app_of_flat_succ` — applied to the functor
`M ↦ H^i(X, 𝓕 ⊗_A M)`: a flat module is a filtered colimit of finite free ones, both sides
commute with such colimits, and at the free module of rank one the comparison is the right
unitor. -/
theorem isIso_cohomologyTensorComparison_app_of_flat (hZ : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1} (hV₀ : IsTerminal V₀)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (𝓕 : Modules.{u, u} B S hS X.1 X.2) (i : ℕ)
    (M : ModuleCat.{u} (baseChartRing B S hS Y V₀))
    [Module.Flat (baseChartRing B S hS Y V₀) M] :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsIso ((cohomologyTensorComparison B S hS hZ f hV₀ hqc hqs 𝓕 i).app M) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have : Functor.Linear (baseChartRing B S hS Y V₀)
      (cohomologyTensorFunctor B S hS f hV₀ 𝓕 i) :=
    linear_cohomologyTensorFunctor B S hS f hV₀ 𝓕 i
  have : PreservesFilteredColimitsOfSize.{u, u}
      (cohomologyTensorFunctor B S hS f hV₀ 𝓕 i) :=
    preservesFilteredColimitsOfSize_cohomologyTensorFunctor B S hS hZ f hV₀ hqc hqs 𝓕 i
  isIso_tensorComparisonUniv_app_of_flat_succ
    (cohomologyTensorFunctor B S hS f hV₀ 𝓕 i) M

end AlgebraicGeometry.Space

end

end
