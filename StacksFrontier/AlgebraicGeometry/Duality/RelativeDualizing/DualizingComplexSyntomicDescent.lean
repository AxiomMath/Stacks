module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Fibres
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.FlatPushforwardCoherator
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.SyntomicBaseChange
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.SyntomicBaseChangeUnconditional
public import StacksFrontier.RingTheory.LocalCohomology.BaseChangeGeneralSupport
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange

/-!
# Dualizing complexes ascend and descend along a syntomic surjection

Let `f : X ⟶ Y` be a morphism of locally Noetherian schemes which is either syntomic and
surjective, or a surjective flat local complete intersection morphism, or a surjective Gorenstein
morphism of finite type. [Stacks, Tag 0E4N] says that an object `K` of `D_QCoh(𝒪_Y)` is a
dualizing complex on `Y` ([Stacks, Tag 0A87]) exactly when `Lf^*K` is a dualizing complex on `X`.

The source proves this by passing to affine opens and reading the condition through
[Stacks, Tag 06Z0], which turns it into the ring-level statement [Stacks, Tag 0E4D]. That is the
argument below. The reduction has three ingredients, all of them proved here or already in the
library:

* through every point of `X` there is a pair of affine opens `U ⊆ Y`, `V ⊆ f⁻¹(U)` on which `f`
  is *still surjective* (`Stacks.Duality.exists_affineOpens_surjective_resLE`): the image of an
  affine open is open because `f` is flat and locally of finite presentation, so it contains a
  basic open of an affine open of `Y`;
* over such a pair the derived pullback of the presenting object of `K|_U` is the derived
  extension of scalars along `f.appLE U V`
  (`AlgebraicGeometry.Scheme.Modules.restrictedDerivedPullbackModelIso`), which is the affine
  comparison square of [Stacks, Tag 08DW] part (2) transported from `Spec` to the two affine
  opens;
* being a dualizing complex is a pointwise condition
  (`Stacks.Duality.isDualizingComplex_iff_forall_exists_hasDualizingModelOn`), which is
  [Stacks, Tag 0A86].

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackRestrictionSquareIso` and its derived form
  `derivedPullbackRestrictionSquareIso` — restricting a pullback around a commutative square two
  of whose arrows are open immersions.
* `AlgebraicGeometry.Scheme.Modules.affineModelPullbackIso` and its derived form
  `affineModelPullbackDerivedIso` — **the affine comparison square at two nested affine opens**,
  the transport of [Stacks, Tag 08DW] part (2) along `U ≅ Spec Γ(Y, U)` and `V ≅ Spec Γ(X, V)`.
* `AlgebraicGeometry.Scheme.Modules.restrictedDerivedPullbackModelIso` — the presenting object of
  `Lf^*K` over `V`, given one of `K` over `U`.

## Main results

* `Stacks.Duality.isDualizingComplex_of_isDualizingComplex_derivedPullback` — **the descent
  direction, unconditionally**, for a flat surjection of finite presentation: it rests only on
  [Stacks, Tag 0E4A].
* `Stacks.Duality.isDualizingComplex_derivedPullback_of_syntomic` — **the ascent direction,
  unconditionally**, for a syntomic morphism that need not be surjective.
* `Stacks.Duality.isDualizingComplex_iff_derivedPullback_of_syntomic` — **[Stacks, Tag 0E4N]
  case (1)**, `f` syntomic and surjective.
* `Stacks.Duality.isDualizingComplex_iff_derivedPullback_of_flat_lci` — **[Stacks, Tag 0E4N]
  case (2)**, `f` a surjective flat local complete intersection morphism.
* `Stacks.Duality.isDualizingComplex_iff_derivedPullback_of_gorenstein` — **[Stacks, Tag 0E4N]
  case (3)**, `f` a surjective Gorenstein morphism of finite type.

The three cases above take ring-level inputs at each affine pair as parameters. The statements of
[Stacks, Tag 0E4N] at exactly the source's hypotheses are in
`StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexPullbackCriterion`.

## Implementation notes

*What is carried.* The hypothesis-carrying form of the ring-level input [Stacks, Tag 0E4D] is
what these statements consume, and its hypotheses are carried here too, quantified over the
affine pairs `(U, V)` of `f`: a polynomial presentation `p` of each `f.appLE U V`, the
invertibility `hInv` of the relative dualizing complex (the invertibility clause of
[Stacks, Tag 0E4B]) in cases (1) and (2), and the tensor formula `hTensor` of
[Stacks, Tag 0BZU] composed with the change-of-rings projection of [Stacks, Tag 06Y6].  Those
ring-level inputs are *not* open: they are discharged in
`StacksFrontier.RingTheory.Dualizing.DualizingComplexes.SyntomicBaseChangeUnconditional`, for a
local complete intersection ring map and, for the tensor formula, for a flat one, so what
remains between these statements and unconditional ones is the geometry — that `f.appLE U V` is a
local complete intersection ring map at each affine pair, and that a polynomial presentation of it
exists — and not the ring-level duality. The *descent* direction of each case needs none of
them: it is
[Stacks, Tag 0E4A], which is unconditional, and it is isolated as
`Stacks.Duality.isDualizingComplex_of_isDualizingComplex_derivedPullback` so that this is
visible. Nor does the ascent direction for a syntomic morphism, surjective or not: it is
`Stacks.Duality.isDualizingComplex_derivedPullback_of_syntomic`, which obtains the polynomial
presentation, the invertibility and the tensor formula at each affine pair from their
unconditional forms. Case (3) carries one further hypothesis, `hGorRing`, the Gorenstein property
of the ring-theoretic fibres of `f.appLE U V`; the geometric hypothesis `hGor` is recorded rather
than consumed, since the identification of `Spec` of such a fibre ring with an open subscheme of
the scheme-theoretic fibre of `f` — the step that turns one into the other — is not available
here.

*The model of the derived categories.* The whole file works at
`CategoryTheory.HasDerivedCategory.standard`, installed with priority `10000` as
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean` asks of its
importers. That is forced: `Stacks.Duality.HasDualizingModelOn` seals that model inside its body
for the derived categories that depend on the affine open, and
`AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso` and
`Stacks.LocalCohomology.derivedExtensionScalarsIsoMapDerivedCategory` are pinned there. Derived
pullback is consequently spelled
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom`, the
ringed-space functor of [Stacks, Tag 079W] read at the standard model, and not
`Stacks.Duality.derivedPullback`, which is the same functor pinned at the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`. `HasDerivedCategory` is
`CategoryTheory.MorphismProperty.HasLocalization`, a *data*-carrying class, so a statement at one
model says nothing about another and the two spellings cannot be mixed.

*Why degreewise pullback suffices.* All three cases have `f` flat, so degreewise pullback of
sheaves of modules is exact and the derived pullback is the functor it induces on derived
categories (`AlgebraicGeometry.Scheme.Modules.derivedPullbackIsoMapDerivedCategory`). The same
holds on the ring side for extension of scalars along `f.appLE U V`, which is flat. The affine
comparison square is therefore obtained from the *underived* [Stacks, Tag 01I9] by applying
`CategoryTheory.Functor.mapDerivedCategoryCongr`, and no left-derived-functor uniqueness argument
is needed; the two conversions to the honest derived functors happen once each.

## References

* [Stacks Project, Tag 0E4N](https://stacks.math.columbia.edu/tag/0E4N)
* [Stacks Project, Tag 0E4D](https://stacks.math.columbia.edu/tag/0E4D)
* [Stacks Project, Tag 0E4A](https://stacks.math.columbia.edu/tag/0E4A)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 069K](https://stacks.math.columbia.edu/tag/069K)
* [Stacks Project, Tag 0C04](https://stacks.math.columbia.edu/tag/0C04)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedExtensionScalars
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- The inclusion of an affine open `V ⊆ f⁻¹(U)` into an affine open `U` of the target, read on
spectra, is the spectrum of `f.appLE U V`. -/
theorem IsAffineOpen.isoSpec_hom_specMap_appLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) :
    hV.isoSpec.hom ≫ Spec.map (f.appLE U V hVU) = f.resLE U V hVU ≫ hU.isoSpec.hom := by
  rw [hU.isoSpec_hom, hV.isoSpec_hom]
  exact Scheme.Opens.toSpecΓ_SpecMap_appLE f U V hVU

namespace Scheme.Modules

attribute [local instance] AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat
  AlgebraicGeometry.preservesFiniteColimits_modulesPullback
  AlgebraicGeometry.pullback_additive

/-- **The pullback square of an open restriction.** For a commutative square `i ≫ f = g ≫ j` of
morphisms of schemes with `i` and `j` open immersions, restricting a pullback along `f` to the
source of `i` is pulling back along `g` the restriction along `j`. Both are degreewise pullback
along the common composite. -/
def pullbackRestrictionSquareIso {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (i : X' ⟶ X) (j : Y' ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ f = g ≫ j) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor i ≅
      Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.pullback g :=
  Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback i) ≪≫
    Scheme.Modules.pullbackComp i f ≪≫
    eqToIso (congrArg Scheme.Modules.pullback h) ≪≫
    (Scheme.Modules.pullbackComp g j).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback j).symm _

/-- `AlgebraicGeometry.Scheme.Modules.pullbackRestrictionSquareIso` on unbounded derived
categories, for a square whose two horizontal arrows are flat. -/
def derivedPullbackRestrictionSquareIso {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    [Flat f] [Flat g] (i : X' ⟶ X) (j : Y' ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : i ≫ f = g ≫ j) :
    (Scheme.Modules.pullback f).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor i).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory ⋙
        (Scheme.Modules.pullback g).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (Iso.refl _) ≪≫
    Functor.mapDerivedCategoryCongr (pullbackRestrictionSquareIso f g i j h) ≪≫
    (Functor.mapDerivedCategoryCompIso (Iso.refl _)).symm

/-- **Along a flat morphism the derived pullback is degreewise pullback.** This is
`AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso` with the exactness of degreewise
pullback supplied by flatness. -/
def derivedPullbackIsoMapDerivedCategory {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    derivedPullback f.toLRSHom.toShHom ≅ (Scheme.Modules.pullback f).mapDerivedCategory :=
  letI : PreservesFiniteLimits (modulePullback f.toLRSHom.toShHom) :=
    preservesFiniteLimits_modulePullback_of_isFlat _ fun x => Flat.stalkMap f x
  letI : PreservesFiniteColimits (modulePullback f.toLRSHom.toShHom) :=
    preservesFiniteColimits_modulePullback _
  SpecField.derivedPullbackMapDerivedIso f.toLRSHom.toShHom

/-- **The affine comparison square at two nested affine opens.** Let `f : X ⟶ Y` be flat, let `U`
be an affine open of `Y` and `V` an affine open of `X` with `f(V) ⊆ U`. Pulling back to `V` the
complex of sheaves associated to an object of `D(Γ(Y, U))`, read on `U`, gives the complex of
sheaves associated to its extension of scalars along `f.appLE U V`, read on `V`.

This is [Stacks, Tag 01I9] conjugated by the two canonical isomorphisms `U ≅ Spec Γ(Y, U)` and
`V ≅ Spec Γ(X, V)`, which identify `f|_V : V ⟶ U` with `Spec (f.appLE U V)`. -/
def affineModelPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) :
    (tilde.functor Γ(Y, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) ⋙
        Scheme.Modules.pullback (f.resLE U V hVU) ≅
      ModuleCat.extendScalars (f.appLE U V hVU).hom ⋙
        (tilde.functor Γ(X, V) ⋙ Scheme.Modules.restrictFunctor hV.isoSpec.hom) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (pullbackRestrictionSquareIso (Spec.map (f.appLE U V hVU)) (f.resLE U V hVU)
        hV.isoSpec.hom hU.isoSpec.hom (hU.isoSpec_hom_specMap_appLE f hV hVU)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullbackTildeIso Γ(Y, U) Γ(X, V) (f.appLE U V hVU)) _ ≪≫
    Functor.associator _ _ _

/-- `AlgebraicGeometry.Scheme.Modules.affineModelPullbackIso` on unbounded derived categories,
with derived extension of scalars on the right: along a flat ring map extension of scalars is
exact, so its left derived functor is the degreewise one. -/
def affineModelPullbackDerivedIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) :
    (tilde.functor Γ(Y, U) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory ⋙
        (Scheme.Modules.pullback (f.resLE U V hVU)).mapDerivedCategory ≅
      (derivedExtensionScalarsGeneral.{u, u, u} (f.appLE U V hVU).hom).functor ⋙
        (tilde.functor Γ(X, V) ⋙
          Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory :=
  letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (f.appLE U V hVU).hom) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ (f.flat_appLE hU hV hVU)
  Functor.mapDerivedCategoryCompIso (Iso.refl _) ≪≫
    Functor.mapDerivedCategoryCongr (affineModelPullbackIso f hU hV hVU) ≪≫
    (Functor.mapDerivedCategoryCompIso (Iso.refl _)).symm ≪≫
    (Functor.isoWhiskerRight
      (Stacks.LocalCohomology.derivedExtensionScalarsIsoMapDerivedCategory.{u, u, u}
        (f.appLE U V hVU).hom) _).symm

/-- **The presentation of `K|_U` by an object of `D(Γ(Y, U))` pulls back to `V`.** Over an affine
open `V ⊆ f⁻¹(U)` the derived pullback `Lf^*K` is presented by the derived extension of scalars
of the object presenting `K` over `U`. -/
def restrictedDerivedPullbackModelIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (K : DerivedCategory Y.Modules)
    (M : DerivedCategory (ModuleCat.{u} Γ(Y, U)))
    (eM : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(Y, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj M) :
    (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj
        ((derivedPullback f.toLRSHom.toShHom).obj K) ≅
      (tilde.functor Γ(X, V) ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj
          ((derivedExtensionScalarsGeneral.{u, u, u} (f.appLE U V hVU).hom).functor.obj M) :=
  (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.mapIso
      ((derivedPullbackIsoMapDerivedCategory f).app K) ≪≫
    (derivedPullbackRestrictionSquareIso f (f.resLE U V hVU) V.ι U.ι
      (f.resLE_comp_ι hVU).symm).app K ≪≫
    (Scheme.Modules.pullback (f.resLE U V hVU)).mapDerivedCategory.mapIso eM ≪≫
    (affineModelPullbackDerivedIso f hU hV hVU).app M

end Scheme.Modules

end AlgebraicGeometry

namespace Stacks.Duality

variable {X Y : Scheme.{u}}

/-! ### Reading the local condition off a presenting object -/

/-- **A dualizing model at an affine open is recognised on any presenting object.** If `K|_U` is
the complex of sheaves associated to `M ∈ D(Γ(X, U))`, then `K` carries a dualizing model at `U`
exactly when `M` is a dualizing complex: derived sheafification is fully faithful, so any other
presenting object is isomorphic to `M`. -/
theorem hasDualizingModelOn_iff_isDualizingComplex_of_model [IsLocallyNoetherian X]
    (K : DerivedCategory X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (M : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (e : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj M) :
    HasDualizingModelOn K U hU ↔
      letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
      Dualizing.IsDualizingComplex M := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  refine ⟨fun h => ?_, fun hM => ⟨M, hM, ⟨e⟩⟩⟩
  obtain ⟨N, hN, ⟨eN⟩⟩ := h
  exact Dualizing.isDualizingComplex_of_iso (nonempty_iso_of_nonempty_iso_tilde hU eN e).some hN

/-- **The local condition at an affine pair, read on one object of `D(Γ(Y, U))`.** For `K` with
quasi-coherent cohomology there is a single object `M` of `D(Γ(Y, U))` which computes both the
dualizing model of `K` at `U` and the dualizing model of `Lf^*K` at `V`, the latter through its
derived extension of scalars along `f.appLE U V`. -/
theorem exists_model_hasDualizingModelOn_iff [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Flat f] {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (K : DerivedCategory Y.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj K).IsQuasicoherent) :
    letI : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    ∃ M : DerivedCategory (ModuleCat.{u} Γ(Y, U)),
      (HasDualizingModelOn K U hU ↔ Dualizing.IsDualizingComplex M) ∧
        (HasDualizingModelOn ((derivedPullback f.toLRSHom.toShHom).obj K) V hV ↔
          letI : IsNoetherianRing Γ(X, V) :=
            IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
          Dualizing.IsDualizingComplex
            ((derivedExtensionScalarsGeneral.{u, u, u}
              (f.appLE U V hVU).hom).functor.obj M)) := by
  obtain ⟨M, ⟨eM⟩⟩ := exists_nonempty_iso_tilde_of_isQuasicoherent hU hK
  exact ⟨M, hasDualizingModelOn_iff_isDualizingComplex_of_model K hU M eM,
    hasDualizingModelOn_iff_isDualizingComplex_of_model _ hV _
      (Scheme.Modules.restrictedDerivedPullbackModelIso f hU hV hVU K M eM)⟩

/-! ### Being a dualizing complex is a pointwise condition -/

/-- **A dualizing complex is recognised at one affine open through each point.** This is
[Stacks, Tag 0A86] in the form the local comparison below delivers its conclusion. -/
theorem isDualizingComplex_iff_forall_exists_hasDualizingModelOn [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules} :
    IsDualizingComplex K ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ HasDualizingModelOn K U.1 U.2 := by
  classical
  refine ⟨fun h x => ?_, fun h => ?_⟩
  · obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨U, hU⟩, hxU, h U hU⟩
  · choose U hx hU using h
    refine isDualizingComplex_of_hasDualizingModelOn_cover (fun x => (U x).1)
      (fun x => (U x).2) (top_unique fun x _ => ?_) hU
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩

/-- **Descent of the dualizing property from a pointwise affine comparison.** If `f` is
surjective and through every point of `X` there is an affine pair at which a dualizing model of
`L` gives one of `K`, then `L` being a dualizing complex forces `K` to be one. -/
theorem isDualizingComplex_of_affineLocalDescent [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Surjective f] {K : DerivedCategory Y.Modules} {L : DerivedCategory X.Modules}
    (h : ∀ x : X, ∃ (U : Y.affineOpens) (V : X.affineOpens), x ∈ V.1 ∧ f x ∈ U.1 ∧
      (HasDualizingModelOn L V.1 V.2 → HasDualizingModelOn K U.1 U.2))
    (hL : IsDualizingComplex L) : IsDualizingComplex K := by
  refine isDualizingComplex_iff_forall_exists_hasDualizingModelOn.2 fun y => ?_
  obtain ⟨x, rfl⟩ := Surjective.surj (f := f) y
  obtain ⟨U, V, -, hy, himp⟩ := h x
  exact ⟨U, hy, himp (hL V.1 V.2)⟩

/-- **Ascent of the dualizing property from a pointwise affine comparison.** If through every
point of `X` there is an affine pair at which a dualizing model of `K` gives one of `L`, then `K`
being a dualizing complex forces `L` to be one. -/
theorem isDualizingComplex_of_affineLocalAscent [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) {K : DerivedCategory Y.Modules} {L : DerivedCategory X.Modules}
    (h : ∀ x : X, ∃ (U : Y.affineOpens) (V : X.affineOpens), x ∈ V.1 ∧ f x ∈ U.1 ∧
      (HasDualizingModelOn K U.1 U.2 → HasDualizingModelOn L V.1 V.2))
    (hK : IsDualizingComplex K) : IsDualizingComplex L := by
  refine isDualizingComplex_iff_forall_exists_hasDualizingModelOn.2 fun x => ?_
  obtain ⟨U, V, hx, -, himp⟩ := h x
  exact ⟨V, hx, himp (hK U.1 U.2)⟩

/-! ### Affine pairs with surjective restriction -/

/-- **Through every point there is a pair of affine opens `V ⊆ f⁻¹(U)`.** -/
private theorem exists_affineOpens_le_preimage (f : X ⟶ Y) (x : X) :
    ∃ (U : Y.affineOpens) (V : X.affineOpens), V.1 ≤ f ⁻¹ᵁ U.1 ∧ x ∈ V.1 ∧ f x ∈ U.1 := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ U from hyU) (U.isOpen.preimage f.continuous)
  exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hVU, hxV, hyU⟩

/-- **Through every point there is an affine pair on which `f` is still surjective.** For `f`
flat, locally of finite presentation and surjective the image of an affine open `V ∋ x` is open,
so it contains a basic open `D(s)` of an affine open `U ∋ f(x)`; the pair `(D(s), D(f^♯s))` then
works, and `f` restricted to it is surjective. -/
theorem exists_affineOpens_surjective_resLE (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] [Surjective f] (x : X) :
    ∃ (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
      x ∈ V.1 ∧ f x ∈ U.1 ∧ Function.Surjective (f.resLE U.1 V.1 hVU).base := by
  classical
  obtain ⟨Ua, Va, hVpre, hxV, hyU⟩ := exists_affineOpens_le_preimage f x
  let F : Va.1.toScheme ⟶ Y := Va.1.ι ≫ f
  have : Flat F := MorphismProperty.comp_mem @Flat _ _ inferInstance inferInstance
  have : LocallyOfFinitePresentation F :=
    MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ inferInstance inferInstance
  have hImage : IsOpen (Set.range F.base) := by
    simpa using Scheme.Hom.isOpenMap F Set.univ isOpen_univ
  have hfxO : f x ∈ (⟨Set.range F.base, hImage⟩ : Y.Opens) := ⟨⟨x, hxV⟩, rfl⟩
  obtain ⟨s, hsle, hys⟩ := Ua.2.exists_basicOpen_le ⟨f x, hfxO⟩ hyU
  have hbo : X.basicOpen (f.appLE Ua.1 Va.1 hVpre s) = Va.1 ⊓ f ⁻¹ᵁ Y.basicOpen s :=
    Scheme.basicOpen_appLE f Va.1 Ua.1 hVpre s
  have hmem : ∀ z : X, z ∈ Va.1 → f z ∈ Y.basicOpen s →
      z ∈ X.basicOpen (f.appLE Ua.1 Va.1 hVpre s) := fun z h1 h2 => by rw [hbo]; exact ⟨h1, h2⟩
  have hle : X.basicOpen (f.appLE Ua.1 Va.1 hVpre s) ≤ f ⁻¹ᵁ Y.basicOpen s := by
    rw [hbo]; exact inf_le_right
  have hfs : f x ∈ Y.basicOpen s := by simpa using hys
  refine ⟨⟨Y.basicOpen s, Ua.2.basicOpen s⟩,
    ⟨X.basicOpen (f.appLE Ua.1 Va.1 hVpre s), Va.2.basicOpen _⟩, hle,
    hmem x hxV hfs, hfs, ?_⟩
  intro y
  obtain ⟨z, hz⟩ := Set.mem_range.mp (hsle y.2)
  have hzW : F.base z ∈ Y.basicOpen s := by rw [hz]; exact y.2
  refine ⟨⟨z.1, hmem z.1 z.2 hzW⟩, Subtype.ext ?_⟩
  rw [Scheme.Hom.coe_resLE_apply]
  exact hz

/-- **The restriction map between the sections of a surjective affine pair is surjective on
spectra.** The inclusion `V ⟶ U` is, read on spectra, the spectrum of `f.appLE U V`. -/
theorem surjective_comap_appLE (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (hsurj : Function.Surjective (f.resLE U V hVU).base) :
    Function.Surjective (PrimeSpectrum.comap (f.appLE U V hVU).hom) := by
  intro p
  obtain ⟨q, hq⟩ := hsurj (hU.isoSpec.inv p)
  refine ⟨hV.isoSpec.hom q, ?_⟩
  have e : hU.isoSpec.hom (hU.isoSpec.inv p) = p := by
    rw [← Scheme.Hom.comp_apply hU.isoSpec.inv hU.isoSpec.hom p, hU.isoSpec.inv_hom_id]
    rfl
  have h : (Spec.map (f.appLE U V hVU)) (hV.isoSpec.hom q) = p := by
    rw [← Scheme.Hom.comp_apply hV.isoSpec.hom (Spec.map (f.appLE U V hVU)) q,
      hU.isoSpec_hom_specMap_appLE f hV hVU,
      Scheme.Hom.comp_apply (f.resLE U V hVU) hU.isoSpec.hom q, hq, e]
  exact h

/-! ### Descent, unconditionally -/

/-- **Descent of the dualizing property along a flat surjection of finite presentation.** If
`Lf^*K` is a dualizing complex on `X` then `K` is a dualizing complex on `Y`.

This is the descent half of [Stacks, Tag 0E4N] and it needs no hypothesis beyond flatness,
local finite presentation and surjectivity: on an affine pair on which `f` is still surjective
the restriction map on sections is faithfully flat, and [Stacks, Tag 0E4A] descends the
ring-level property unconditionally. -/
theorem isDualizingComplex_of_isDualizingComplex_derivedPullback [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    (K : DerivedCategory Y.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj K).IsQuasicoherent)
    (hL : IsDualizingComplex ((derivedPullback f.toLRSHom.toShHom).obj K)) :
    IsDualizingComplex K := by
  refine isDualizingComplex_of_affineLocalDescent f (fun x => ?_) hL
  obtain ⟨U, V, hVU, hx, hy, hs⟩ := exists_affineOpens_surjective_resLE f x
  refine ⟨U, V, hx, hy, fun hmodel => ?_⟩
  have : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨M, h1, h2⟩ := exists_model_hasDualizingModelOn_iff f U.2 V.2 hVU K hK
  exact h1.2 (Dualizing.isDualizingComplex_of_faithfullyFlat.{u, u, u}
    (f.appLE U.1 V.1 hVU).hom
    (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
      ⟨f.flat_appLE U.2 V.2 hVU, surjective_comap_appLE f U.2 V.2 hVU hs⟩)
    M (h2.1 hmodel))

/-! ### Ascent along a syntomic morphism, unconditionally -/

/-- **Ascent of the dualizing property along a syntomic morphism.** Let `f : X ⟶ Y` be a
syntomic morphism of locally Noetherian schemes, not necessarily surjective, and let `K` be an
object of `D_QCoh(𝒪_Y)`. If `K` is a dualizing complex on `Y` then `Lf^*K` is a dualizing
complex on `X`.

This is the ascent half of [Stacks, Tag 0E4N] case (1), whose proof never uses surjectivity. At
any pair of affine opens `V ⊆ f⁻¹(U)` the ring map `f.appLE U V` is syntomic, hence a local
complete intersection of finite type, so a polynomial presentation of it exists and
[Stacks, Tag 0BZL] together with the invertibility of `ω^•_{B/A}` ([Stacks, Tag 0E4B]) and the
tensor formula of [Stacks, Tag 0BZU] carry the dualizing model of `K` at `U` to one of `Lf^*K`
at `V`; the globalisation is [Stacks, Tag 0A86]. -/
theorem isDualizingComplex_derivedPullback_of_syntomic [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) (hf : Syntomic f) (K : DerivedCategory Y.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj K).IsQuasicoherent)
    (hKd : IsDualizingComplex K) :
    IsDualizingComplex ((derivedPullback f.toLRSHom.toShHom).obj K) := by
  have : Flat f := ((syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism f).mp hf).1
  have hsyn := ((syntomic_tfae f).out 1 2).mp hf
  refine isDualizingComplex_of_affineLocalAscent f (fun x => ?_) hKd
  obtain ⟨U, V, hVU, hxV, hyU⟩ := exists_affineOpens_le_preimage f x
  refine ⟨U, V, hxV, hyU, fun hmodel => ?_⟩
  have : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨M, h1, h2⟩ := exists_model_hasDualizingModelOn_iff f U.2 V.2 hVU K hK
  have hlci : RingHom.IsLocalCompleteIntersection (f.appLE U V hVU).hom :=
    ((RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection _).mp
      (hsyn V V.2 U U.2 hVU)).2
  obtain ⟨p⟩ := Dualizing.nonempty_polynomialPresentation _ hlci.1
  exact h2.2 (Dualizing.isDualizingComplex_derivedExtensionScalars_of_upperShriek _ p M
    (h1.1 hmodel)
    (Dualizing.isInvertible_relativeDualizingUnit_of_isLocalCompleteIntersection p hlci)
    (Dualizing.nonempty_upperShriekFunctor_obj_iso_derivedExtensionScalars_tensor_of_lci
      _ p hlci M))

/-! ### The three cases of Tag 0E4N -/

/-- **Stacks Project, Tag 0E4N, case (1).** Let `f : X ⟶ Y` be a syntomic surjection of locally
Noetherian schemes and let `K` be an object of `D_QCoh(𝒪_Y)`. Then `K` is a dualizing complex on
`Y` if and only if `Lf^*K` is a dualizing complex on `X`.

Over an affine open `U ⊆ Y` and an affine open `V ⊆ f⁻¹(U)` on which `f` is still surjective the
condition becomes the ring-level statement [Stacks, Tag 0E4D] for `f.appLE U V`, which is
syntomic and surjective on spectra; the two sides are compared by the affine comparison square of
[Stacks, Tag 08DW] and the globalisation is [Stacks, Tag 0A86]. -/
@[stacks 0E4N "variant: case (1) with a polynomial presentation p, the invertibility hInv \
and the tensor formula hTensor at each affine pair as explicit parameters; the tag is \
Stacks.Duality.isDualizingComplex_iff_derivedPullback_of_syntomic_of_surjective"]
theorem isDualizingComplex_iff_derivedPullback_of_syntomic [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Surjective f] (hf : Syntomic f)
    (p : ∀ (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
      Dualizing.PolynomialPresentation (f.appLE U.1 V.1 hVU).hom)
    (hInv : ∀ (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
      letI : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
      letI : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
      letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
        Γ(X, V.1)).choose
      MonoidalCategory.IsInvertible (Dualizing.relativeDualizingUnit (p U V hVU)))
    (hTensor : ∀ (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
      (M : DerivedCategory (ModuleCat.{u} Γ(Y, U.1))),
      letI : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
      letI : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
      letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
        Γ(X, V.1)).choose
      Nonempty ((p U V hVU).upperShriekFunctor.{u, u}.obj M ≅
        ((derivedExtensionScalarsGeneral.{u, u, u}
            (f.appLE U.1 V.1 hVU).hom).functor.obj M) ⊗
          Dualizing.relativeDualizingUnit (p U V hVU)))
    (K : DerivedCategory Y.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj K).IsQuasicoherent) :
    IsDualizingComplex K ↔
      IsDualizingComplex ((derivedPullback f.toLRSHom.toShHom).obj K) := by
  have : Flat f := ((syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism f).mp hf).1
  have : LocallyOfFinitePresentation f := AlgebraicGeometry.locallyOfFinitePresentation hf
  have hsyn := ((syntomic_tfae f).out 1 2).mp hf
  refine ⟨fun hKd => isDualizingComplex_of_affineLocalAscent f (fun x => ?_) hKd,
    fun hLd => isDualizingComplex_of_isDualizingComplex_derivedPullback f K hK hLd⟩
  obtain ⟨U, V, hVU, hx, hy, hs⟩ := exists_affineOpens_surjective_resLE f x
  refine ⟨U, V, hx, hy, fun hmodel => ?_⟩
  have : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨M, h1, h2⟩ := exists_model_hasDualizingModelOn_iff f U.2 V.2 hVU K hK
  refine h2.2 ((Dualizing.isDualizingComplex_iff_derivedExtensionScalars_of_syntomic
    (f.appLE U.1 V.1 hVU).hom (hsyn V.1 V.2 U.1 U.2 hVU)
    (surjective_comap_appLE f U.2 V.2 hVU hs) (p U V hVU) M (hInv U V hVU)
    (hTensor U V hVU M)).mp (h1.1 hmodel))

/-- **Stacks Project, Tag 0E4N, case (2).** Let `f : X ⟶ Y` be a surjective flat local complete
intersection morphism of locally Noetherian schemes and let `K` be an object of `D_QCoh(𝒪_Y)`.
Then `K` is a dualizing complex on `Y` if and only if `Lf^*K` is a dualizing complex on `X`.

A flat local complete intersection morphism is syntomic by [Stacks, Tag 069K], so this is
case (1). -/
@[stacks 0E4N "variant: case (2) with a polynomial presentation p, the invertibility hInv \
and the tensor formula hTensor at each affine pair as explicit parameters; the tag is \
Stacks.Duality.isDualizingComplex_iff_derivedPullback_of_flat_lci_of_surjective"]
theorem isDualizingComplex_iff_derivedPullback_of_flat_lci [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Surjective f] [Flat f]
    (hlci : IsLocalCompleteIntersectionMorphism f)
    (p : ∀ (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
      Dualizing.PolynomialPresentation (f.appLE U.1 V.1 hVU).hom)
    (hInv : ∀ (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
      letI : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
      letI : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
      letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
        Γ(X, V.1)).choose
      MonoidalCategory.IsInvertible (Dualizing.relativeDualizingUnit (p U V hVU)))
    (hTensor : ∀ (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
      (M : DerivedCategory (ModuleCat.{u} Γ(Y, U.1))),
      letI : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
      letI : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
      letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
        Γ(X, V.1)).choose
      Nonempty ((p U V hVU).upperShriekFunctor.{u, u}.obj M ≅
        ((derivedExtensionScalarsGeneral.{u, u, u}
            (f.appLE U.1 V.1 hVU).hom).functor.obj M) ⊗
          Dualizing.relativeDualizingUnit (p U V hVU)))
    (K : DerivedCategory Y.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj K).IsQuasicoherent) :
    IsDualizingComplex K ↔
      IsDualizingComplex ((derivedPullback f.toLRSHom.toShHom).obj K) :=
  isDualizingComplex_iff_derivedPullback_of_syntomic f
    ((syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism f).mpr ⟨‹Flat f›, hlci⟩)
    p hInv hTensor K hK

/-- **Stacks Project, Tag 0E4N, case (3).** Let `f : X ⟶ Y` be a surjective Gorenstein morphism
of finite type of locally Noetherian schemes and let `K` be an object of `D_QCoh(𝒪_Y)`. Then `K`
is a dualizing complex on `Y` if and only if `Lf^*K` is a dualizing complex on `X`.

A Gorenstein morphism is flat, and of finite type over a locally Noetherian target it is of
finite presentation, so the reduction to affine pairs of case (1) applies verbatim; at an affine
pair the ring-level statement is [Stacks, Tag 0E4D] case (3). -/
@[stacks 0E4N "variant: case (3) with a polynomial presentation p, the fibre-ring \
Gorenstein property hGorRing and the tensor formula hTensor at each affine pair as explicit \
parameters; the tag is \
Stacks.Duality.isDualizingComplex_iff_derivedPullback_of_isGorenstein_of_surjective"]
theorem isDualizingComplex_iff_derivedPullback_of_gorenstein [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Surjective f] [QuasiCompact f] [LocallyOfFiniteType f]
    (hF : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (hGor : Scheme.Hom.IsGorenstein f hF)
    (p : ∀ (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
      letI : Algebra Γ(Y, U.1) Γ(X, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      Dualizing.PolynomialPresentation (algebraMap Γ(Y, U.1) Γ(X, V.1)))
    (hGorRing : ∀ (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
      (q : Ideal Γ(Y, U.1)) [q.IsPrime],
      letI : Algebra Γ(Y, U.1) Γ(X, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      letI := Dualizing.isNoetherianRing_baseChange q.ResidueField (p U V hVU)
      Dualizing.IsGorensteinRing (q.Fiber Γ(X, V.1)))
    (hTensor : ∀ (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
      (M : DerivedCategory (ModuleCat.{u} Γ(Y, U.1))),
      letI : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
      letI : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
      letI : Algebra Γ(Y, U.1) Γ(X, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
        Γ(X, V.1)).choose
      Nonempty ((p U V hVU).upperShriekFunctor.{u, u}.obj M ≅
        ((derivedExtensionScalarsGeneral.{u, u, u}
            (algebraMap Γ(Y, U.1) Γ(X, V.1))).functor.obj M) ⊗
          Dualizing.relativeDualizingUnit (p U V hVU)))
    (K : DerivedCategory Y.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj K).IsQuasicoherent) :
    IsDualizingComplex K ↔
      IsDualizingComplex ((derivedPullback f.toLRSHom.toShHom).obj K) := by
  have : Flat f := Flat.of_stalkMap f fun x => (hGor x).1
  have : LocallyOfFinitePresentation f := inferInstance
  refine ⟨fun hKd => isDualizingComplex_of_affineLocalAscent f (fun x => ?_) hKd,
    fun hLd => isDualizingComplex_of_isDualizingComplex_derivedPullback f K hK hLd⟩
  obtain ⟨U, V, hVU, hx, hy, hs⟩ := exists_affineOpens_surjective_resLE f x
  refine ⟨U, V, hx, hy, fun hmodel => ?_⟩
  have : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  let _ : Algebra Γ(Y, U.1) Γ(X, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  obtain ⟨M, h1, h2⟩ := exists_model_hasDualizingModelOn_iff f U.2 V.2 hVU K hK
  exact h2.2 ((Dualizing.isDualizingComplex_iff_derivedExtensionScalars_of_gorensteinFibres
    (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
      ⟨f.flat_appLE U.2 V.2 hVU, surjective_comap_appLE f U.2 V.2 hVU hs⟩)
    (p U V hVU) (fun q _ => hGorRing U V hVU q) M
    (hTensor U V hVU M)).mp (h1.1 hmodel))

end Stacks.Duality

end
