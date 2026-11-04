module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineBase
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineSections
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeRestriction
public import StacksFrontier.Homology.RelativelyPerfect.ColimitHom
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsSelfIso

/-!
# The affine case of Tag 0DI7 over an affine open of the base

Let `V₀` be an affine open of `X₀` contained in the preimage of an affine open `W₀ ⊆ S₀`, the
situation of `AlgebraicGeometry.RelativeDescentSituation.IsAffineOpenOverAffine`. Over such a
`V₀` the restricted relative descent situation of Stacks 0DI6 is a filtered system of affine
schemes whose rings are `Γ(Vᵢ) = Rᵢ ⊗_{R₀} A₀` with `R₀ = Γ(W₀)`, `Rᵢ = Γ(g_i^{-1}W₀)` and
`A₀ = Γ(V₀)`, and `R = colim Rᵢ`; that is exactly the system the ring-theoretic Tag 0DHX
consumes. This file deduces Tag 0DI7 for the restriction to `V₀` from Tag 0DHX read over that
system, and assembles the hypothesis `haffine` of the reduction
`restrictHomDescent_family_of_isAffineOpen_over_affine_of_sup` for a family of second
arguments.

The translation between the system of morphism sets in `D(𝒪_{Vᵢ})` and the system of morphism
sets over the rings `Γ(Vᵢ)` is carried by `AffineDerivedHomEquiv` and its naturality predicate
`AffineDerivedHomEquiv.IsNatural`, which are hypotheses of the results below. They are the two
inputs the Stacks proof reads off Tags 06Z0, 08E5 and 0DHY and off the affine comparison square.
The first is reduced here to a single comparison of *objects* over `V₀`:
`affineDerivedHomEquivOfBaseIso` builds an `AffineDerivedHomEquiv` from identifications of the
derived pullbacks of `K₀|_{V₀}` and `L₀|_{V₀}` with the sheafifications of the avatars, the
passage from objects to morphism sets being Tag 06Z0 at
`CategoryTheory.HasDerivedCategory.standard` and the passage from `V₀` to the stages and to the
limit being the affine comparison square of [Stacks, Tag 08DW]. The second is the composition
cocycle of `AlgebraicGeometry.StandardModel.affinePullbackComparison` and remains a hypothesis.
Everything else — the colimit of the rings, the filteredness of the index, the flatness and
finite presentation of `R₀ ⟶ A₀`, and the shift bookkeeping which makes the family instantiation
work — is supplied here.

## Main definitions

* `AlgebraicGeometry.derivedTildeObj`, `AlgebraicGeometry.derivedPullbackIsoHomEquiv` and
  `AlgebraicGeometry.affineHomEquivOfIso`: derived sheafification read at a variable ring, the
  bijection on derived morphism sets induced by an isomorphism of schemes, and the resulting
  identification of the derived morphism sets of a scheme isomorphic to `Spec R` with those of
  `R`.
* `AlgebraicGeometry.RelativeDescentSituation.AffineDerivedHomEquiv`: the ring-level avatars of
  `K₀|_{V₀}` and `L₀|_{V₀}`, their pseudo-coherence and finite Tor dimension over `R₀`, and the
  bijections between the derived morphism sets over `Vᵢ` and over `Γ(Vᵢ)`, at a stage and at the
  limit.
* `AlgebraicGeometry.RelativeDescentSituation.AffineDerivedHomEquiv.IsNatural`: those bijections
  commute with the transition maps of the two systems and with their comparison maps to the
  limit.
* `AlgebraicGeometry.RelativeDescentSituation.AffineRingTranslation`: the two together.
* `AlgebraicGeometry.affineComparisonTransportIso`: the affine comparison square of [Stacks,
  Tag 08DW] read around two isomorphisms onto spectra.
* `AlgebraicGeometry.RelativeDescentSituation.stageSpecIso` and `limitSpecIso`: the stages and
  the limit of the restricted situation as the spectra of the algebras of Tag 0DHX.
* `AlgebraicGeometry.RelativeDescentSituation.stageAlgebraUnit` and `limitAlgebraUnit`: the units
  `A₀ ⟶ Rᵢ ⊗_{R₀} A₀` and `A₀ ⟶ R ⊗_{R₀} A₀` of those algebras.

## Main results

* `AlgebraicGeometry.RelativeDescentSituation.stageSpecIso_hom_comp` and
  `limitSpecIso_hom_comp`: `Vᵢ ⟶ V₀` and `V ⟶ V₀` are `Spec` of those units, one leg of the
  pushout squares of `isPushout_appTop_restrictToBasePreimage` and its limit analogue.
* `AlgebraicGeometry.RelativeDescentSituation.stageDerivedObjIso` and `limitDerivedObjIso`: the
  objects Tag 0DHX forms at a stage and over the colimit are the derived extensions of scalars
  along those units, the universe lift in their definition being undone by
  `CochainComplex.DerivedExtensionScalars.totalDerivedRestrictExtendScalarsSelfIso`.
* `AlgebraicGeometry.RelativeDescentSituation.affineDerivedHomEquivOfSpecIso`: **the affine
  dictionary from comparisons of objects.** Tag 06Z0 carries identifications of the derived
  pullbacks of `K₀|_{V₀}` and `L₀|_{V₀}` with sheafifications of extensions of scalars to the
  bijections on derived morphism sets of an `AffineDerivedHomEquiv`.
* `AlgebraicGeometry.RelativeDescentSituation.affineDerivedHomEquivOfBaseIso`: **the same from a
  single comparison over `V₀`.** The stage and limit comparisons are transported from `V₀` along
  `affineComparisonTransportIso`.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomDescent_of_affineDerivedHomEquiv`:
  **Tag 0DI7 for the restriction to an affine open over an affine open of the base, from Tag
  0DHX.** The surjectivity and the eventual injectivity of
  `PseudoCoherence.stageDerivedHom_descent` transported along a natural
  `AffineDerivedHomEquiv`.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomDescent_of_affineRingTranslation` and
  `restrictHomDescent_of_isAffineOpenOverAffine`: the same with the translation bundled, and
  with the affine open of the base produced by `IsAffineOpenOverAffine`.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomDescent_shift_of_isAffineOpenOverAffine`:
  **the hypothesis `haffine` of the reduction, for the family of shifts of a single second
  argument.** Tor amplitude over the base translates by `-n` under a shift and quasi-coherence
  of the cohomology sheaves is shift-stable, so one set of hypotheses on `K₀` and `L₀` serves
  every member of the family.
* `AlgebraicGeometry.isQuasicoherent_homology_shift`: quasi-coherence of the cohomology sheaves
  is stable under shifting.

## Implementation notes

The hypotheses on `K₀` and `L₀` are those of Tag 0DI7 and are deliberately asymmetric: `K₀` is
pseudo-coherent, with no quasi-coherence asked of it, while `L₀` is required to lie in
`D_QCoh(𝒪_{X₀})` as well as to have finite Tor dimension over `S₀`. Quasi-coherence of `L₀` is
not a consequence of its Tor amplitude, and it is what makes the ring-level avatar of `L₀|_{V₀}`
exist at all, by the essential surjectivity clause of Tag 06Z0.

The index universe is identified with the universe of the schemes.
`PseudoCoherence.stageDerivedObj` and its morphism sets take three universes — the index, the
index category's morphisms and the rings — and
`PseudoCoherence.isColimit_mapCocone_commAlgCat_uliftFunctor`, the only route to the colimit
hypothesis of Tag 0DHX, has all three equal. The index category here is a preorder, so
its morphism universe is already its object universe; the remaining identification is the index
with the rings, which is why `D : RelativeDescentSituation.{u, u} I` for `I : Type u` throughout.

`AffineDerivedHomEquiv` carries the `Γ(W₀)`-algebra structure of `Γ(V₀)` in the types of its
fields rather than as a parameter: it is the one induced by `D.X₀.hom.resLE W₀ V₀`, the same one
`moduleFlat_appTop_resLE` and `algebraFinitePresentation_appTop_resLE` install, so the structure
is a self-contained statement and no transport is needed when its fields are fed to Tag 0DHX.

The morphism sets over the stages and over the limit are written as a value of
`AlgebraicGeometry.RelativeDescentSituation.homFunctor` and as the vertex of
`AlgebraicGeometry.RelativeDescentSituation.homCocone`. Those are definitionally the spelled-out
derived morphism sets, and the comparison between the derived pullbacks of the restricted
situation and the restrictions of the derived pullbacks is then not re-elaborated in the type of
every field. Spelling them out instead exceeds the heartbeat limit on the `structure`
declaration under the module system, where it elaborates in seconds at the accessor spelling.

Three ways of checking which `HasDerivedCategory` instance a statement here is at report success
while checking nothing, and all three were met in writing this file. The pretty-printer gives up
on the larger types, so counting occurrences in `#check` output under `pp.explicit` scores them
as zero. Filtering constant names for `HasDerivedCategory` misses the lower-case instance names
of the competing model, for which the filter must be `erivedCategory`. And the model-carrying
constant is `HasDerivedCategory.standard` at the root namespace, so a comparison against
`CategoryTheory.HasDerivedCategory.standard` matches nothing and reports every declaration as
off-model. What does work is extracting `Lean.Expr.getUsedConstants` from the declaration's type
and comparing against the root-level name; the bodies of imported theorems are not reachable
through `Lean.ConstantInfo.value?`, so the value half is carried by `#print axioms`.

`derivedTildeObj` exists so that the sheafifications appearing in the hypotheses of
`affineDerivedHomEquivOfSpecIso` are named at a *variable* ring. Every typeclass about
`AlgebraicGeometry.tilde.functor` is stated for a variable `R : CommRingCat`, whose coercion has
head `CommRingCat.carrier`, while `↑(CommRingCat.of A)` reduces to `A`; synthesis of
`(tilde.functor (CommRingCat.of A)).Additive` therefore finds nothing, and the stage and limit
algebras of Tag 0DHX are presented exactly that way.

The hypotheses on `K₀` and `L₀` are pseudo-coherence on `X₀` and finite Tor dimension relative
to `X₀ ⟶ S₀`; no affineness or flatness beyond the fields of the datum of Stacks 0DI6 is
assumed.

## References

* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open StacksDraft.TorAmplitude
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-! ### The derived morphism sets of a scheme isomorphic to a spectrum -/

/-- The derived sheafification on `Spec R` of an object of `D(R)`. -/
def derivedTildeObj (R : CommRingCat.{u}) (M : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)) :=
  (tilde.functor R).mapDerivedCategory.obj M

/-- **Derived pullback along an isomorphism of schemes is bijective on derived morphism sets**,
as an equivalence of types. -/
def derivedPullbackIsoHomEquiv {V : Scheme.{u}} {R : CommRingCat.{u}} (ε : V ≅ Spec R)
    (A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing V.toRingedSpace))) :
    (A ⟶ B) ≃ ((derivedPullback ε.inv.toLRSHom.toShHom).obj A ⟶
      (derivedPullback ε.inv.toLRSHom.toShHom).obj B) :=
  Equiv.ofBijective _ (Stacks.DerivedPullback.bijective_derivedPullback_map
    ε.inv.toLRSHom.toShHom ε.hom.toLRSHom.toShHom
    (congrArg (fun m : Spec R ⟶ Spec R => m.toLRSHom.toShHom) ε.inv_hom_id)
    (congrArg (fun m : V ⟶ V => m.toLRSHom.toShHom) ε.hom_inv_id) A B)

/-- **The derived morphism sets over a scheme isomorphic to `Spec R` are those over `R`.** For
objects of `D(𝒪_V)` whose transports to `Spec R` are the sheafifications of objects `M`, `N` of
`D(R)`, derived pullback along `ε⁻¹` followed by Tag 06Z0 identifies `Hom(A, B)` with
`Hom(M, N)`. -/
def affineHomEquivOfIso {V : Scheme.{u}} {R : CommRingCat.{u}} (ε : V ≅ Spec R)
    {A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing V.toRingedSpace))}
    {M N : DerivedCategory (ModuleCat.{u} R)}
    (eA : (derivedPullback ε.inv.toLRSHom.toShHom).obj A ≅ derivedTildeObj R M)
    (eB : (derivedPullback ε.inv.toLRSHom.toShHom).obj B ≅ derivedTildeObj R N) :
    (A ⟶ B) ≃ (M ⟶ N) :=
  (derivedPullbackIsoHomEquiv ε A B).trans
    ((Iso.homCongr eA eB).trans (StandardModel.homEquiv R M N))

/-- **Quasi-coherence of the cohomology sheaves is stable under shifting.** The cohomology
sheaves of `E⟦m⟧` are those of `E`, reindexed by `m`. -/
theorem isQuasicoherent_homology_shift {X : Scheme.{u}} (E : DerivedCategory X.Modules)
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent)
    (m n : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules n).obj (E⟦m⟧)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctor X.Modules 0).shiftIso m n (m + n) rfl).app E).symm
    (hE (m + n))

/-- Derived sheafification on `Spec R` carries an isomorphism of objects of `D(R)` to one of
their images. -/
def derivedTildeObjMapIso (R : CommRingCat.{u}) {M N : DerivedCategory (ModuleCat.{u} R)}
    (e : M ≅ N) : derivedTildeObj R M ≅ derivedTildeObj R N :=
  (tilde.functor R).mapDerivedCategory.mapIso e

/-! ### The affine comparison square transported to schemes isomorphic to spectra -/

/-- **The affine comparison square of [Stacks, Tag 08DW] read around two isomorphisms to
spectra.** For `f : W ⟶ Z` sitting in a commutative square with `Spec g : Spec S ⟶ Spec R` along
isomorphisms `ε : W ≅ Spec S` and `ε₀ : Z ≅ Spec R`, and an object of `D(𝒪_Z)` whose transport
along `ε₀` is the sheafification of `M`, the transport of its derived pullback along `f` is the
sheafification of the derived extension of scalars of `M` along `g`. -/
def affineComparisonTransportIso {W Z : Scheme.{u}} {R S : CommRingCat.{u}}
    (ε : W ≅ Spec S) (ε₀ : Z ≅ Spec R) (f : W ⟶ Z) (g : R ⟶ S)
    (hsq : ε.hom ≫ Spec.map g = f ≫ ε₀.hom)
    {E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))}
    {M : DerivedCategory (ModuleCat.{u} R)}
    (eE : (derivedPullback ε₀.inv.toLRSHom.toShHom).obj E ≅ derivedTildeObj R M) :
    (derivedPullback ε.inv.toLRSHom.toShHom).obj
        ((derivedPullback f.toLRSHom.toShHom).obj E) ≅
      derivedTildeObj S ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj M) :=
  ((Stacks.DerivedPullback.schemeFactorSquareIso ε.inv f (Spec.map g) ε₀.inv
      (by rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]; exact hsq.symm)).app E).symm ≪≫
    (StandardModel.specDerivedPullback g).mapIso eE ≪≫
    (StandardModel.affinePullbackComparison R S g).app M

end AlgebraicGeometry

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

attribute [local implicit_reducible] restrict

/-! ### The translation of the system of derived morphism sets into the ring-level system -/

section Translation

variable (W₀ : (D.descent.system.obj (op D.descent.base)).Opens)
  (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀) (hVW : V₀ ≤ D.X₀.hom ⁻¹ᵁ W₀)
  (K₀ L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-- **The affine dictionary on `V₀`.** Objects `𝕂`, `𝕃` of `D(Γ(V₀))`, with `𝕂` pseudo-coherent
and `𝕃` of finite Tor dimension over `Γ(W₀)`, together with bijections between the morphism sets
`Hom_{D(𝒪_{Vᵢ})}(Lf_{i0}^*(K₀|_{V₀}), Lf_{i0}^*(L₀|_{V₀}))` and the morphism sets between the
extensions of scalars of `𝕂` and `𝕃` to `Γ(Vᵢ)`, at a stage and at the limit. -/
structure AffineDerivedHomEquiv where
  /-- The avatar of `K₀|_{V₀}` as an object of `D(Γ(V₀))`. -/
  moduleFst : DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤))
  /-- The avatar of `L₀|_{V₀}` as an object of `D(Γ(V₀))`. -/
  moduleSnd : DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤))
  /-- The avatar of `K₀|_{V₀}` is pseudo-coherent over `Γ(V₀)`. -/
  isPseudoCoherent_moduleFst : StacksDraft.PseudoCoherence.IsPseudoCoherent moduleFst
  /-- The avatar of `L₀|_{V₀}` has finite Tor dimension over `Γ(W₀)`. -/
  hasFiniteTorDimension_moduleSnd :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    HasFiniteTorDimensionCanonical Γ(W₀.toScheme, ⊤)
      ((ModuleCat.restrictScalars
        (algebraMap Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤))).mapDerivedCategory.obj moduleSnd)
  /-- At a stage, the derived morphism sets over `Vᵢ` and over `Γ(Vᵢ)` agree. -/
  stageEquiv :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    ∀ i : D.LaterIndex,
      ((D.restrict V₀ hV₀.isCompact).homFunctor
          ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀)
          ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀)).obj i ≃
      (PseudoCoherence.stageDerivedObj (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i moduleFst ⟶
        PseudoCoherence.stageDerivedObj (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i moduleSnd)
  /-- At the limit, the derived morphism sets over `V` and over `R ⊗_{R₀} Γ(V₀)` agree. -/
  limitEquiv :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    ((D.restrict V₀ hV₀.isCompact).homCocone
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀)
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀)).pt ≃
      (PseudoCoherence.limitDerivedObj (D.baseRingAlgCocone W₀) Γ(V₀.toScheme, ⊤) moduleFst ⟶
        PseudoCoherence.limitDerivedObj (D.baseRingAlgCocone W₀) Γ(V₀.toScheme, ⊤) moduleSnd)

/-- **The affine dictionary is a morphism of systems with their cocones.** The bijections of an
`AffineDerivedHomEquiv` carry the transition maps of the system of derived morphism sets over the
`Vᵢ` to the transition maps of extension of scalars, and the comparison maps to the limit to the
comparison maps over the colimit of the rings. This is the composition cocycle of
`AlgebraicGeometry.StandardModel.affinePullbackComparison`. -/
def AffineDerivedHomEquiv.IsNatural
    (a : D.AffineDerivedHomEquiv W₀ V₀ hV₀ hVW K₀ L₀) : Prop :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  (∀ {i j : D.LaterIndex} (f : i ⟶ j) (φ : _),
      a.stageEquiv j ((D.restrict V₀ hV₀.isCompact).homTransition
          ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀)
          ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀) (leOfHom f) φ) =
        PseudoCoherence.stageDerivedHomTransition (D.baseRingAlgDiagram W₀)
          Γ(V₀.toScheme, ⊤) f a.moduleFst a.moduleSnd (a.stageEquiv i φ)) ∧
    ∀ (i : D.LaterIndex) (φ : _),
      a.limitEquiv ((D.restrict V₀ hV₀.isCompact).homComparison
          ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀)
          ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀) i φ) =
        PseudoCoherence.stageDerivedHomComparison (D.baseRingAlgCocone W₀)
          Γ(V₀.toScheme, ⊤) i a.moduleFst a.moduleSnd (a.stageEquiv i φ)

/-- The affine dictionary on `V₀` together with its naturality. -/
def AffineRingTranslation : Prop :=
  ∃ a : D.AffineDerivedHomEquiv W₀ V₀ hV₀ hVW K₀ L₀, a.IsNatural

/-! ### The affine dictionary from the comparison of objects -/

/-- **`Vᵢ` is the spectrum of the stage algebra of Tag 0DHX.** `Vᵢ` is affine, and its ring of
sections is `Rᵢ ⊗_{R₀} A₀` by `stageAlgebraIsoSections`. -/
def stageSpecIso (hW₀ : IsAffineOpen W₀) (i : D.LaterIndex) :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    (D.restrict V₀ hV₀.isCompact).schemeAt i ≅
      Spec (CommRingCat.of (PseudoCoherence.stageAlgebra
        (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i)) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  have : IsAffine ((D.restrict V₀ hV₀.isCompact).schemeAt i) :=
    D.isAffine_restrict_schemeAt V₀ hV₀ i
  Scheme.isoSpec _ ≪≫ Scheme.Spec.mapIso (D.stageAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀ i).op

/-- **`V` is the spectrum of the algebra Tag 0DHX builds over the colimit.** `V` is affine, and
its ring of sections is `R ⊗_{R₀} A₀` by `limitAlgebraIsoSections`. -/
def limitSpecIso (hW₀ : IsAffineOpen W₀) :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    (D.restrict V₀ hV₀.isCompact).limitScheme ≅
      Spec (CommRingCat.of
        ((D.baseRingAlgCocone W₀).pt ⊗[Γ(W₀.toScheme, ⊤)] Γ(V₀.toScheme, ⊤))) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  have : IsAffine ((D.restrict V₀ hV₀.isCompact).limitScheme) :=
    D.isAffine_restrict_limitScheme V₀ hV₀
  Scheme.isoSpec _ ≪≫ Scheme.Spec.mapIso (D.limitAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀).op

/-- The unit `A₀ ⟶ Rᵢ ⊗_{R₀} A₀` of the stage algebra of Tag 0DHX, as a morphism of
`CommRingCat`. -/
def stageAlgebraUnit (i : D.LaterIndex) :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    Γ(V₀.toScheme, ⊤) ⟶ CommRingCat.of (PseudoCoherence.stageAlgebra
      (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  CommRingCat.ofHom
    (PseudoCoherence.baseToStageMap (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i)

/-- The unit `A₀ ⟶ R ⊗_{R₀} A₀` of the algebra Tag 0DHX builds over the colimit, as a morphism
of `CommRingCat`. -/
def limitAlgebraUnit :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    Γ(V₀.toScheme, ⊤) ⟶ CommRingCat.of
      ((D.baseRingAlgCocone W₀).pt ⊗[Γ(W₀.toScheme, ⊤)] Γ(V₀.toScheme, ⊤)) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  CommRingCat.ofHom (PseudoCoherence.baseToLimitMap (D.baseRingAlgCocone W₀) Γ(V₀.toScheme, ⊤))

/-- The `Spec` of a unit `u`, read around `isoSpec` and a ring isomorphism `e` of sections, is the
map `f` followed by `isoSpec`, provided `u ≫ e.hom` is the map of sections of `f`. -/
private theorem isoSpec_trans_mapIso_hom_comp {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    {A : CommRingCat.{u}} (e : A ≅ Γ(X, ⊤)) (u : Γ(Y, ⊤) ⟶ A) (f : X ⟶ Y)
    (h : u ≫ e.hom = f.appTop) :
    (Scheme.isoSpec X ≪≫ Scheme.Spec.mapIso e.op).hom ≫ Spec.map u =
      f ≫ (Scheme.isoSpec Y).hom := by
  rw [Iso.trans_hom, Category.assoc,
    show (Scheme.Spec.mapIso e.op).hom = Spec.map e.hom from rfl, ← Spec.map_comp, h,
    Scheme.isoSpec_hom_naturality]

/-- **The stage `Vᵢ ⟶ V₀` is `Spec` of the unit of the stage algebra.** The square commutes
because `stageAlgebraIsoSections` carries the unit `A₀ ⟶ Rᵢ ⊗_{R₀} A₀` of the tensor product to
the map of sections of `Vᵢ ⟶ V₀`, that being one leg of the pushout square. -/
theorem stageSpecIso_hom_comp (hW₀ : IsAffineOpen W₀) (i : D.LaterIndex) :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    haveI : IsAffine V₀.toScheme := hV₀
    (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i).hom ≫
        Spec.map (D.stageAlgebraUnit W₀ V₀ hVW i) =
      (D.restrict V₀ hV₀.isCompact).toFixedStage i ≫ (Scheme.isoSpec V₀.toScheme).hom :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  have : IsAffine V₀.toScheme := hV₀
  have : IsAffine ((D.restrict V₀ hV₀.isCompact).schemeAt i) :=
    D.isAffine_restrict_schemeAt V₀ hV₀ i
  have : IsAffine (D.restrict V₀ hV₀.isCompact).X₀.left := D.isAffine_restrict_X₀ V₀ hV₀
  isoSpec_trans_mapIso_hom_comp _ _ _
    (IsPushout.inr_isoIsPushout_hom _ _ _
      (D.isPushout_appTop_restrictToBasePreimage W₀ V₀ hV₀ hVW hW₀ i))

/-- **The limit `V ⟶ V₀` is `Spec` of the unit of the colimit algebra.** The limit analogue of
`stageSpecIso_hom_comp`. -/
theorem limitSpecIso_hom_comp (hW₀ : IsAffineOpen W₀) :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    haveI : IsAffine V₀.toScheme := hV₀
    (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀).hom ≫ Spec.map (D.limitAlgebraUnit W₀ V₀ hVW) =
      (D.restrict V₀ hV₀.isCompact).limitToFixedStage ≫ (Scheme.isoSpec V₀.toScheme).hom :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  have : IsAffine V₀.toScheme := hV₀
  have : IsAffine ((D.restrict V₀ hV₀.isCompact).limitScheme) :=
    D.isAffine_restrict_limitScheme V₀ hV₀
  have : IsAffine (D.restrict V₀ hV₀.isCompact).X₀.left := D.isAffine_restrict_X₀ V₀ hV₀
  isoSpec_trans_mapIso_hom_comp _ _ _
    (IsPushout.inr_isoIsPushout_hom _ _ _
      (D.isPushout_appTop_restrictToBasePreimageLimit W₀ V₀ hV₀ hVW hW₀))

/-- **The stage object of Tag 0DHX is the derived extension of scalars along the unit.** The
`ULift` in `PseudoCoherence.stageDerivedObj` is undone by
`CochainComplex.DerivedExtensionScalars.totalDerivedRestrictExtendScalarsSelfIso`. -/
def stageDerivedObjIso (i : D.LaterIndex)
    (M :
      letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
        ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
      DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤))) :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    PseudoCoherence.stageDerivedObj (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i M ≅
      (totalDerivedExtensionScalars.{u, u, u}
        (D.stageAlgebraUnit W₀ V₀ hVW i).hom).functor.obj M :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  ((PseudoCoherence.derivedExtensionScalarsComp
      (PseudoCoherence.liftBaseRingHom Γ(V₀.toScheme, ⊤))
      (PseudoCoherence.baseToStageMap (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i)).app _).symm ≪≫
    (totalDerivedExtensionScalars.{u, u, u}
      (PseudoCoherence.baseToStageMap (D.baseRingAlgDiagram W₀)
        Γ(V₀.toScheme, ⊤) i)).functor.mapIso
      ((totalDerivedRestrictExtendScalarsSelfIso.{u, u}
        (ULift.ringEquiv : ULift.{u} Γ(V₀.toScheme, ⊤) ≃+* Γ(V₀.toScheme, ⊤))).app M)

/-- **The colimit object of Tag 0DHX is the derived extension of scalars along the unit.** The
limit analogue of `stageDerivedObjIso`. -/
def limitDerivedObjIso
    (M :
      letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
        ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
      DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤))) :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    PseudoCoherence.limitDerivedObj (D.baseRingAlgCocone W₀) Γ(V₀.toScheme, ⊤) M ≅
      (totalDerivedExtensionScalars.{u, u, u}
        (D.limitAlgebraUnit W₀ V₀ hVW).hom).functor.obj M :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  ((PseudoCoherence.derivedExtensionScalarsComp
      (PseudoCoherence.liftBaseRingHom Γ(V₀.toScheme, ⊤))
      (PseudoCoherence.baseToLimitMap (D.baseRingAlgCocone W₀)
        Γ(V₀.toScheme, ⊤))).app _).symm ≪≫
    (totalDerivedExtensionScalars.{u, u, u}
      (PseudoCoherence.baseToLimitMap (D.baseRingAlgCocone W₀)
        Γ(V₀.toScheme, ⊤))).functor.mapIso
      ((totalDerivedRestrictExtendScalarsSelfIso.{u, u}
        (ULift.ringEquiv : ULift.{u} Γ(V₀.toScheme, ⊤) ≃+* Γ(V₀.toScheme, ⊤))).app M)

/-- **The affine dictionary from comparisons of objects.** Given the ring-level avatars with
their pseudo-coherence and finite Tor dimension, and, at every stage and at the limit,
identifications of the derived pullbacks of `K₀|_{V₀}` and `L₀|_{V₀}` with the sheafifications
of the extensions of scalars of the avatars, Tag 06Z0 turns those into the bijections on derived
morphism sets which `AffineDerivedHomEquiv` asks for. -/
def affineDerivedHomEquivOfSpecIso (hW₀ : IsAffineOpen W₀)
    (𝕂 𝕃 : DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤)))
    (h𝕂 : StacksDraft.PseudoCoherence.IsPseudoCoherent 𝕂)
    (h𝕃 :
      letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
        ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
      HasFiniteTorDimensionCanonical Γ(W₀.toScheme, ⊤)
        ((ModuleCat.restrictScalars
          (algebraMap Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤))).mapDerivedCategory.obj 𝕃))
    (eK : ∀ i : D.LaterIndex,
      letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
        ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
      (derivedPullback (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i).inv.toLRSHom.toShHom).obj
          ((derivedPullback ((D.restrict V₀ hV₀.isCompact).toFixedStage i).toLRSHom.toShHom).obj
            ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀)) ≅
        derivedTildeObj (CommRingCat.of (PseudoCoherence.stageAlgebra
            (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i))
          (PseudoCoherence.stageDerivedObj (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i 𝕂))
    (eL : ∀ i : D.LaterIndex,
      letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
        ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
      (derivedPullback (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i).inv.toLRSHom.toShHom).obj
          ((derivedPullback ((D.restrict V₀ hV₀.isCompact).toFixedStage i).toLRSHom.toShHom).obj
            ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀)) ≅
        derivedTildeObj (CommRingCat.of (PseudoCoherence.stageAlgebra
            (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i))
          (PseudoCoherence.stageDerivedObj (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i 𝕃))
    (eKlim :
      letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
        ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
      (derivedPullback (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀).inv.toLRSHom.toShHom).obj
          ((derivedPullback
              (D.restrict V₀ hV₀.isCompact).limitToFixedStage.toLRSHom.toShHom).obj
            ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀)) ≅
        derivedTildeObj (CommRingCat.of ((D.baseRingAlgCocone W₀).pt ⊗[Γ(W₀.toScheme, ⊤)]
            Γ(V₀.toScheme, ⊤)))
          (PseudoCoherence.limitDerivedObj (D.baseRingAlgCocone W₀) Γ(V₀.toScheme, ⊤) 𝕂))
    (eLlim :
      letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
        ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
      (derivedPullback (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀).inv.toLRSHom.toShHom).obj
          ((derivedPullback
              (D.restrict V₀ hV₀.isCompact).limitToFixedStage.toLRSHom.toShHom).obj
            ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀)) ≅
        derivedTildeObj (CommRingCat.of ((D.baseRingAlgCocone W₀).pt ⊗[Γ(W₀.toScheme, ⊤)]
            Γ(V₀.toScheme, ⊤)))
          (PseudoCoherence.limitDerivedObj (D.baseRingAlgCocone W₀) Γ(V₀.toScheme, ⊤) 𝕃)) :
    D.AffineDerivedHomEquiv W₀ V₀ hV₀ hVW K₀ L₀ where
  moduleFst := 𝕂
  moduleSnd := 𝕃
  isPseudoCoherent_moduleFst := h𝕂
  hasFiniteTorDimension_moduleSnd := h𝕃
  stageEquiv i :=
    affineHomEquivOfIso (ε := D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i) (eA := eK i) (eB := eL i)
  limitEquiv :=
    affineHomEquivOfIso (ε := D.limitSpecIso W₀ V₀ hV₀ hVW hW₀) (eA := eKlim) (eB := eLlim)

/-- **The affine dictionary from the comparison of objects over `V₀` alone.** The stage and limit
comparisons which `affineDerivedHomEquivOfSpecIso` asks for are the comparison over `V₀`
transported around the squares `stageSpecIso_hom_comp` and `limitSpecIso_hom_comp` by the affine
comparison square of [Stacks, Tag 08DW], followed by `stageDerivedObjIso` and
`limitDerivedObjIso`; so a single identification of `K₀|_{V₀}` and `L₀|_{V₀}` with the
sheafifications of the avatars suffices. -/
def affineDerivedHomEquivOfBaseIso (hW₀ : IsAffineOpen W₀)
    (𝕂 𝕃 : DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤)))
    (h𝕂 : StacksDraft.PseudoCoherence.IsPseudoCoherent 𝕂)
    (h𝕃 :
      letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
        ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
      HasFiniteTorDimensionCanonical Γ(W₀.toScheme, ⊤)
        ((ModuleCat.restrictScalars
          (algebraMap Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤))).mapDerivedCategory.obj 𝕃))
    (eK₀ :
      haveI : IsAffine V₀.toScheme := hV₀
      (derivedPullback (Scheme.isoSpec V₀.toScheme).inv.toLRSHom.toShHom).obj
          ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀) ≅
        derivedTildeObj Γ(V₀.toScheme, ⊤) 𝕂)
    (eL₀ :
      haveI : IsAffine V₀.toScheme := hV₀
      (derivedPullback (Scheme.isoSpec V₀.toScheme).inv.toLRSHom.toShHom).obj
          ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀) ≅
        derivedTildeObj Γ(V₀.toScheme, ⊤) 𝕃) :
    D.AffineDerivedHomEquiv W₀ V₀ hV₀ hVW K₀ L₀ :=
  have : IsAffine V₀.toScheme := hV₀
  D.affineDerivedHomEquivOfSpecIso W₀ V₀ hV₀ hVW K₀ L₀ hW₀ 𝕂 𝕃 h𝕂 h𝕃
    (fun i => affineComparisonTransportIso (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i)
        (Scheme.isoSpec V₀.toScheme) ((D.restrict V₀ hV₀.isCompact).toFixedStage i)
        (D.stageAlgebraUnit W₀ V₀ hVW i)
        (D.stageSpecIso_hom_comp W₀ V₀ hV₀ hVW hW₀ i) eK₀ ≪≫
      derivedTildeObjMapIso _ (D.stageDerivedObjIso W₀ V₀ hVW i 𝕂).symm)
    (fun i => affineComparisonTransportIso (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i)
        (Scheme.isoSpec V₀.toScheme) ((D.restrict V₀ hV₀.isCompact).toFixedStage i)
        (D.stageAlgebraUnit W₀ V₀ hVW i)
        (D.stageSpecIso_hom_comp W₀ V₀ hV₀ hVW hW₀ i) eL₀ ≪≫
      derivedTildeObjMapIso _ (D.stageDerivedObjIso W₀ V₀ hVW i 𝕃).symm)
    (affineComparisonTransportIso (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀)
        (Scheme.isoSpec V₀.toScheme) (D.restrict V₀ hV₀.isCompact).limitToFixedStage
        (D.limitAlgebraUnit W₀ V₀ hVW)
        (D.limitSpecIso_hom_comp W₀ V₀ hV₀ hVW hW₀) eK₀ ≪≫
      derivedTildeObjMapIso _ (D.limitDerivedObjIso W₀ V₀ hVW 𝕂).symm)
    (affineComparisonTransportIso (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀)
        (Scheme.isoSpec V₀.toScheme) (D.restrict V₀ hV₀.isCompact).limitToFixedStage
        (D.limitAlgebraUnit W₀ V₀ hVW)
        (D.limitSpecIso_hom_comp W₀ V₀ hV₀ hVW hW₀) eL₀ ≪≫
      derivedTildeObjMapIso _ (D.limitDerivedObjIso W₀ V₀ hVW 𝕃).symm)

/-! ### Tag 0DI7 over an affine open lying over an affine open of the base -/

/-- **Tag 0DI7 for the restriction to an affine open of `X₀` lying over an affine open of `S₀`.**
The system of rings `Rᵢ = Γ(g_i^{-1}W₀)` has colimit `R`, the index is filtered and `R₀ ⟶ A₀` is
flat of finite presentation, so Tag 0DHX applies to the avatars; the dictionary carries its
surjectivity and eventual injectivity back to the derived morphism sets over the `Vᵢ`. -/
theorem restrictHomDescent_of_affineDerivedHomEquiv (hW₀ : IsAffineOpen W₀)
    (a : D.AffineDerivedHomEquiv W₀ V₀ hV₀ hVW K₀ L₀) (ha : a.IsNatural) :
    D.RestrictHomDescent K₀ L₀ V₀ hV₀.isCompact :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  by
  have : Module.Flat Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    D.moduleFlat_appTop_resLE W₀ V₀ hVW hW₀ hV₀
  have : Algebra.FinitePresentation Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    D.algebraFinitePresentation_appTop_resLE W₀ V₀ hVW hW₀ hV₀
  have : IsFiltered D.LaterIndex := D.isFiltered_laterIndex
  have hc := PseudoCoherence.isColimit_mapCocone_commAlgCat_uliftFunctor
    (D.isColimitBaseRingAlgCocone W₀ hW₀)
  obtain ⟨htransition, hcomparison⟩ := ha
  refine ⟨fun ψ => ?_, fun i φ φ' hφ => ?_⟩
  · obtain ⟨i, φr, hφr⟩ := PseudoCoherence.exists_stageDerivedHom
      (D.baseRingAlgDiagram W₀) (D.baseRingAlgCocone W₀) hc Γ(V₀.toScheme, ⊤)
      a.moduleFst a.moduleSnd a.isPseudoCoherent_moduleFst
      a.hasFiniteTorDimension_moduleSnd (a.limitEquiv ψ)
    exact ⟨i, (a.stageEquiv i).symm φr, a.limitEquiv.injective
      ((hcomparison i _).trans
        ((congrArg _ ((a.stageEquiv i).apply_symm_apply φr)).trans hφr))⟩
  · obtain ⟨j, f, hf⟩ := PseudoCoherence.exists_stageDerivedHomTransition_eq
      (D.baseRingAlgDiagram W₀) (D.baseRingAlgCocone W₀) hc Γ(V₀.toScheme, ⊤)
      a.moduleFst a.moduleSnd a.isPseudoCoherent_moduleFst
      a.hasFiniteTorDimension_moduleSnd i (a.stageEquiv i φ) (a.stageEquiv i φ')
      (((hcomparison i φ).symm.trans (congrArg a.limitEquiv hφ)).trans (hcomparison i φ'))
    exact ⟨j, leOfHom f, (a.stageEquiv j).injective
      ((htransition f φ).trans (hf.trans (htransition f φ').symm))⟩

/-- **Tag 0DI7 for the restriction to an affine open of `X₀` lying over an affine open of `S₀`**,
with the dictionary bundled. -/
theorem restrictHomDescent_of_affineRingTranslation (hW₀ : IsAffineOpen W₀)
    (h : D.AffineRingTranslation W₀ V₀ hV₀ hVW K₀ L₀) :
    D.RestrictHomDescent K₀ L₀ V₀ hV₀.isCompact :=
  let ⟨a, ha⟩ := h
  D.restrictHomDescent_of_affineDerivedHomEquiv W₀ V₀ hV₀ hVW K₀ L₀ hW₀ a ha

end Translation

/-! ### The hypothesis `haffine` of the reduction -/

section Affine

variable (K₀ L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-- **Tag 0DI7 for the restriction to an affine open lying over an affine open of the base**, in
the form the reduction asks for: the affine open of `S₀` is the one produced by
`IsAffineOpenOverAffine`, so the dictionary is required over every such open. -/
theorem restrictHomDescent_of_isAffineOpenOverAffine (V₀ : D.X₀.left.Opens)
    (hV₀ : IsAffineOpen V₀) (hover : D.IsAffineOpenOverAffine V₀)
    (hdict : ∀ (W₀ : (D.descent.system.obj (op D.descent.base)).Opens)
      (hVW : V₀ ≤ D.X₀.hom ⁻¹ᵁ W₀), IsAffineOpen W₀ →
        D.AffineRingTranslation W₀ V₀ hV₀ hVW K₀ L₀) :
    D.RestrictHomDescent K₀ L₀ V₀ hV₀.isCompact :=
  let ⟨W₀, hW₀, hVW⟩ := hover
  D.restrictHomDescent_of_affineRingTranslation W₀ V₀ hV₀ hVW K₀ L₀ hW₀
    (hdict W₀ hVW hW₀)

/-- **The hypothesis `haffine` of
`restrictHomDescent_family_of_isAffineOpen_over_affine_of_sup`, for the family of shifts of a
single second argument.** The hypotheses are those of Tag 0DI7: `K₀` is pseudo-coherent, with no
quasi-coherence required of it, while `L₀` lies in `D_QCoh(𝒪_{X₀})` and has finite Tor dimension
over `S₀`. Shifting by `n` translates the Tor amplitude interval by `-n` and reindexes the
cohomology sheaves, so every member `L₀⟦n⟧` of the family satisfies both hypotheses over every
affine open of `X₀` lying over an affine open of `S₀`. -/
theorem restrictHomDescent_shift_of_isAffineOpenOverAffine
    (hK₀ : RingedSpace.IsPseudoCoherent (X := D.X₀.left.toRingedSpace) K₀)
    (hL₀qc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor D.X₀.left.Modules n).obj L₀).IsQuasicoherent)
    (hL₀ : ∃ a b : ℤ, HasTorAmplitudeOver D.X₀.hom L₀ a b)
    (hdict : ∀ (W₀ : (D.descent.system.obj (op D.descent.base)).Opens)
      (U₀ : D.X₀.left.Opens) (hU₀ : IsAffineOpen U₀) (hUW : U₀ ≤ D.X₀.hom ⁻¹ᵁ W₀)
      (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace))),
      IsAffineOpen W₀ → RingedSpace.IsPseudoCoherent (X := D.X₀.left.toRingedSpace) K₀ →
        (∀ m : ℤ,
          ((DerivedCategory.homologyFunctor D.X₀.left.Modules m).obj L).IsQuasicoherent) →
        (∃ a b : ℤ, HasTorAmplitudeOver D.X₀.hom L a b) →
          D.AffineRingTranslation W₀ U₀ hU₀ hUW K₀ L) :
    ∀ (n : ℤ) (U₀ : D.X₀.left.Opens) (hU₀ : IsAffineOpen U₀),
      D.IsAffineOpenOverAffine U₀ → D.RestrictHomDescent K₀ (L₀⟦n⟧) U₀ hU₀.isCompact := by
  obtain ⟨a, b, hab⟩ := hL₀
  intro n U₀ hU₀ hover
  refine D.restrictHomDescent_of_isAffineOpenOverAffine K₀ (L₀⟦n⟧) U₀ hU₀ hover
    fun W₀ hUW hW₀ => hdict W₀ U₀ hU₀ hUW (L₀⟦n⟧) hW₀ hK₀
      (fun m => isQuasicoherent_homology_shift L₀ hL₀qc n m) ⟨a - n, b - n, ?_⟩
  exact hasTorAmplitudeOver_shift D.X₀.hom L₀ a b n hab

end Affine

end AlgebraicGeometry.RelativeDescentSituation

end
