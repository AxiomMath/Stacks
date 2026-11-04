module

public import StacksFrontier.AlgebraicGeometry.DeRham.FiniteCohomology
public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BoundedComparison
import StacksCore.Tactic.StacksAttribute

/-!
# De Rham cohomology as derived global sections of the derived direct image

Let `p : X ⟶ S` be a morphism of schemes. Relative de Rham cohomology
`H^i_{dR}(X/S) = H^i(RΓ(X, Ω^•_{X/S}))` is defined in
`StacksFrontier/AlgebraicGeometry/DeRham/HodgeFiltration/Basic.lean` as the cohomology of the
unbounded derived global sections of the relative de Rham complex, a complex of
`p^{-1}𝒪_S`-modules, and
`AlgebraicGeometry.Scheme.Hom.deRhamCohomologyBaseModule` reads it as a module over
`H^0(S, 𝒪_S)` by restricting scalars along `𝒪_S(S) ⟶ Γ(X, p^{-1}𝒪_S)`.

Coherence of `Rp_*Ω^•_{X/S}` — [Stacks, Tag 0FLY] — is proved in
`StacksFrontier/AlgebraicGeometry/DeRham/CoherentDirectImage.lean` for the *bounded below* derived
direct image `Stacks.DeRhamDirectImage.derivedDeRhamDirectImage`, an object of `D⁺(𝒪_S)`. This
file supplies the comparisons that connect the two, which is what [Stacks, Tag 0FLZ] needs in
order to be about `H^i_{dR}(X/S)` rather than about `H^i(RΓ(S, Rp_*Ω^•_{X/S}))`.

## Main results

In the namespace `Stacks.Cohomology.DerivedSectionsRestrictScalars` (general, for a morphism
of ringed spaces `f : X ⟶ Y` and an open `V ⊆ Y`):

* `derivedPreimageSectionsRestrictIso`: **derived sections over `f⁻¹V` with scalars restricted
  along `f^♯` are derived sections over `f⁻¹V` followed by derived restriction of scalars**,
  `RΓ(f⁻¹V, -) : D(𝒪_X) ⥤ D(Γ(V,𝒪_Y))` factors as `RΓ(f⁻¹V,-) : D(𝒪_X) ⥤ D(Γ(f⁻¹V,𝒪_X))`
  followed by `D(Γ(f⁻¹V,𝒪_X)) ⥤ D(Γ(V,𝒪_Y))`. This is the missing half of the restriction of
  scalars that [Stacks, Tag 0D5W] builds into its target; the Leray comparison
  `isIso_lerayComparison_top` lands in `derivedPreimageSections`, whereas de Rham cohomology is
  `H^i` of `derivedSectionsOverOpen` with the restriction applied afterwards.
* `isIso_derivedSectionsOverOpenUnit_app_isKInjective`: the unit of `RΓ(U, -)` is invertible at
  a K-injective complex.

In the namespace `AlgebraicGeometry.DeRhamCohomologyDirectImage`:

* `deRhamCohomologyBaseModule_eq`: **the library's `H^i_{dR}(X/S)`, as an `H^0(S,𝒪_S)`-module,
  is `H^i` of Leray's derived sections of the de Rham complex on `(X, p^{-1}𝒪_S)`, with scalars
  restricted along exactly the ring map Leray restricts along.** This holds on the nose.

## Implementation notes

**Restriction of scalars is exact but its instances must be pinned.** `ModuleCat.restrictScalars`
is exact — it does not change the underlying abelian groups — but neither `Mathlib`'s `Additive`
instance nor its exactness instances fire at the rings that occur here. `Mathlib` states
additivity with the source category spelled through `Functor.sheafPushforwardContinuous`, which
instance search does not unfold to `Γ(f⁻¹V, 𝒪_X)`, and its exactness instances are stated for
`CommRing` whereas the sections of `structureSheafRing` are `RingCat`-valued. Both are therefore
restated here at the spelling the consumer uses, following
`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/DerivedSectionsOfAPushforward.lean`
and `StacksFrontier/Topology/Sheaves/Cohomology/CechAndResolutions/`
`StacksFrontier/Topology/Sheaves/Cohomology/CechAndResolutions/DerivedGlobalSectionsViaResolutions.lean`, which carry the same local instances for the same
reason.

**The comparison is proved by the K-injective recognition criterion, not by hand.** Both
`derivedPreimageSections f V` and `derivedSectionsOverOpen X (f⁻¹V) ⋙ (derived restriction of
scalars)` are right derived functors of the same functor on the homotopy category: the second
because a right derived functor computed by K-injective resolutions is *absolute*, so
postcomposing its unit with any functor leaves the unit invertible at the K-injective complexes.
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isRightDerivedFunctor_of_isIso_app_isKInjective`
turns that into the `IsRightDerivedFunctor` instance and `Functor.rightDerivedUnique` produces
the isomorphism. This is the argument `isIso_lerayComparison` uses for its own Sierpiński-space
factorization.

**The derived category model.** `HasDerivedCategory.standard` is pinned at raised priority, as in
`CoherentDirectImage.lean` and in the Leray development: everything joined here is baked at that
model, and the locally small model arrives through the imports as a competing instance at equal
priority.

## References

* [Stacks Project, Tag 0FLZ](https://stacks.math.columbia.edu/tag/0FLZ)
* [Stacks Project, Tag 0FLY](https://stacks.math.columbia.edu/tag/0FLY)
* [Stacks Project, Tag 0FLX](https://stacks.math.columbia.edu/tag/0FLX)
* [Stacks Project, Tag 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (exists_quasiIso_isKInjective
  isRightDerivedFunctor_of_isIso_app_isKInjective)

universe u

attribute [local instance 2000] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedSectionsLeray

/-- **Restriction of scalars preserves finite limits.** `Mathlib`'s instance is stated for
`CommRing`; the sections of a structure sheaf are `RingCat`-valued, so it is restated here. -/
local instance preservesFiniteLimits_restrictScalars' {R S : Type u} [Ring R] [Ring S]
    (φ : R →+* S) : PreservesFiniteLimits (ModuleCat.restrictScalars.{u} φ) :=
  Stacks.Cohomology.CechAcyclic.preservesFiniteLimits_restrictScalars φ

/-- **Restriction of scalars preserves finite colimits**, having a right adjoint. -/
local instance preservesFiniteColimits_restrictScalars' {R S : Type u} [Ring R] [Ring S]
    (φ : R →+* S) : PreservesFiniteColimits (ModuleCat.restrictScalars.{u} φ) := by
  constructor
  intro J _ _
  constructor
  intro G
  infer_instance

/-- **Restriction of scalars is additive**, at the plain spelling used for a ring map into
`Γ(U, 𝒪_Z)`. -/
local instance restrictScalarsAdditive' {R S : Type u} [Ring R] [Ring S] (φ : R →+* S) :
    (ModuleCat.restrictScalars.{u} φ).Additive :=
  ⟨by intros; rfl⟩

/-- **Restriction of scalars along `f^♯` over `V` is additive**, stated with the source category
spelled as the target of sections over `f⁻¹V`. `Mathlib` spells it as `Γ(V, (opensMap f)_* 𝒪_X)`,
which instance search does not unfold to this form. -/
local instance restrictScalarsSectionsAdditive' {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    @Functor.Additive
      (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ((opensMap f).obj V))))
      (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)))
      _ _ _ _
      (ModuleCat.restrictScalars.{u} ((structureSheafHom f).hom.app (op V)).hom) :=
  ⟨by intros; rfl⟩

namespace Stacks.Cohomology.DerivedSectionsRestrictScalars

variable (Z : RingedSpace.{u, u}) (U : Opens Z.carrier) {R' : Type u} [Ring R']
  (φ : R' →+* (structureSheafRing Z).obj.obj (op U))

/-- **Derived restriction of scalars** `D(Γ(U, 𝒪_Z)) ⥤ D(R')` along a ring map
`φ : R' ⟶ Γ(U, 𝒪_Z)`, induced by the exact functor `ModuleCat.restrictScalars`. -/
abbrev derivedRestrictSections :
    DerivedCategory (ModuleCat.{u} ((structureSheafRing Z).obj.obj (op U))) ⥤
      DerivedCategory (ModuleCat.{u} R') :=
  (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory

/-- Sections over `U` as `R'`-modules, read on the homotopy category. -/
abbrev homotopySectionsRestrict :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{u} R') :=
  (sectionsOverOpen Z U ⋙ ModuleCat.restrictScalars.{u} φ).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- `RΓ(U, -)` with values in `D(R')`: the total right derived functor of sections over `U`
read as `R'`-modules. Both `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections` and
`AlgebraicGeometry.derivedGlobalSectionsOver` are this functor, for their own `φ`. -/
abbrev derivedSectionsRestrict :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)) ⥤
      DerivedCategory (ModuleCat.{u} R') :=
  (homotopySectionsRestrict Z U φ).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))

/-- The canonical comparison from sections over `U` as `R'`-modules to their right derived
functor. -/
abbrev derivedSectionsRestrictUnit :
    homotopySectionsRestrict Z U φ ⟶ DerivedCategory.Qh ⋙ derivedSectionsRestrict Z U φ :=
  (homotopySectionsRestrict Z U φ).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))

/-- Sections over `U` as `R'`-modules factor as sections over `U` followed by derived
restriction of scalars: restriction of scalars is applied degreewise, and an exact functor
descends to the derived category. -/
def homotopySectionsRestrictIso :
    homotopySectionsRestrict Z U φ ≅
      homotopySectionsOverOpen Z U ⋙ derivedRestrictSections Z U φ :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (F := sectionsOverOpen Z U)
        (G := ModuleCat.restrictScalars.{u} φ)
        (Iso.refl _) (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryFactorsh (ModuleCat.restrictScalars.{u} φ)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The canonical transformation from sections over `U` as `R'`-modules to derived sections over
`U` followed by derived restriction of scalars. -/
def sectionsRestrictUnit :
    homotopySectionsRestrict Z U φ ⟶ DerivedCategory.Qh ⋙
      (derivedSectionsOverOpen Z U ⋙ derivedRestrictSections Z U φ) :=
  (homotopySectionsRestrictIso Z U φ).hom ≫
    (Functor.whiskerRight (derivedSectionsOverOpenUnit Z U)
      (derivedRestrictSections Z U φ) ≫ (Functor.associator _ _ _).hom)

/-- **The unit of `RΓ(U, -)` is invertible at a K-injective complex**: a right derived functor
out of the homotopy category of complexes of modules on a ringed space is computed by K-injective
resolutions. -/
theorem isIso_derivedSectionsOverOpenUnit_app_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedSectionsOverOpenUnit Z U).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Z))
        (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, u + 1, u + 1, u + 1, u + 1, u + 1}
      (homotopySectionsOverOpen Z U) (exists_quasiIso_isKInjective Z)).2
    DerivedCategory.Qh (derivedSectionsOverOpen Z U) (derivedSectionsOverOpenUnit Z U) I hI

/-- `RΓ(U, -)` followed by derived restriction of scalars is a right derived functor of sections
over `U` read as `R'`-modules: a right derived functor computed by K-injective resolutions stays
one after postcomposition with any functor. -/
theorem isRightDerivedFunctor_sectionsRestrictUnit :
    (derivedSectionsOverOpen Z U ⋙
        derivedRestrictSections Z U φ).IsRightDerivedFunctor (sectionsRestrictUnit Z U φ)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z))
        (ComplexShape.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_isKInjective.{u, u + 1, u + 1, u + 1, u + 1, u + 1}
    _ (exists_quasiIso_isKInjective Z) DerivedCategory.Qh _ _ fun I hI => ?_
  have := isIso_derivedSectionsOverOpenUnit_app_isKInjective Z U I hI
  change IsIso ((homotopySectionsRestrictIso Z U φ).hom.app _ ≫ _)
  rw [NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

/-- **Derived sections over `U` read as `R'`-modules are derived sections over `U` followed by
derived restriction of scalars.** Both sides are right derived functors of sections over `U`
read as `R'`-modules, so the comparison between them is invertible.

For `φ = f^♯` this is the half of the restriction of scalars that [Stacks, Tag 0D5W] builds into
the target of its Leray comparison: `isIso_lerayComparison_top` compares
`derivedPreimageSections`, in which the restriction is applied *before* deriving, with the
derived direct image, whereas relative de Rham cohomology applies it *after*. For
`φ = Γ(Spec A, 𝒪) ≅ A` it is the same statement for `derivedGlobalSectionsOver`. -/
def derivedSectionsRestrictIso :
    derivedSectionsRestrict Z U φ ≅
      derivedSectionsOverOpen Z U ⋙ derivedRestrictSections Z U φ :=
  have := isRightDerivedFunctor_sectionsRestrictUnit Z U φ
  Functor.rightDerivedUnique _ _ (derivedSectionsRestrictUnit Z U φ)
    (sectionsRestrictUnit Z U φ)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))

/-- **[Stacks, Tag 0D5W]'s `derivedPreimageSections` is the case `φ = f^♯`.** Derived sections
over `f⁻¹V` with scalars restricted along `f^♯` are derived sections over `f⁻¹V` followed by
derived restriction of scalars. -/
def derivedPreimageSectionsRestrictIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    derivedPreimageSections f V ≅
      derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
        derivedRestrictSections X ((opensMap f).obj V)
          ((structureSheafHom f).hom.app (op V)).hom :=
  derivedSectionsRestrictIso X ((opensMap f).obj V) ((structureSheafHom f).hom.app (op V)).hom

end Stacks.Cohomology.DerivedSectionsRestrictScalars

namespace AlgebraicGeometry.DeRhamCohomologyDirectImage

open Stacks.Cohomology.DerivedSectionsLeray Stacks.Cohomology.DerivedSectionsRestrictScalars
open Stacks.DeRhamDirectImage (inverseImageBase inverseImageBaseProjection relativePushforward
  derivedDeRhamDirectImage
  deRhamCochainComplex)

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- **The relative de Rham complex of `p` is the complex of `p^{-1}𝒪_S`-modules that
`Stacks.DeRhamDirectImage` pushes forward.** The two spellings are the same complex. -/
theorem deRhamCochainComplex_eq :
    (deRhamCochainComplex p : CochainComplex _ ℤ)
      = SheafOfModules.deRhamComplexInt (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) :=
  rfl

/-- **The direct image used for `Rp_*Ω^•_{X/S}` is the pushforward of ringed spaces along the
projection `(X, p^{-1}𝒪_S) ⟶ S`.** -/
theorem relativePushforward_eq_modulePushforward :
    relativePushforward p = modulePushforward (inverseImageBaseProjection p) :=
  rfl

/-- **The ring map `H^0(S,𝒪_S) ⟶ Γ(X, p^{-1}𝒪_S)` along which `H^i_{dR}(X/S)` is read as an
`H^0(S,𝒪_S)`-module is the one Leray restricts scalars along.** -/
theorem structureSheafHom_app_top_eq :
    ((structureSheafHom (inverseImageBaseProjection p)).hom.app (op ⊤)).hom
      = (Scheme.Hom.inverseImageGlobalSections p).hom :=
  rfl

/-- **Relative de Rham cohomology as an `H^0(S,𝒪_S)`-module is `H^i` of Leray's derived sections
of the relative de Rham complex on the ringed space `(X, p^{-1}𝒪_S)`**, with scalars restricted
along the structure map of the projection to `S`. This holds on the nose: the ringed space
`AlgebraicGeometry.SheafOfModules.baseRingedSpace` in which `H^i_{dR}` is defined *is*
`Stacks.DeRhamDirectImage.inverseImageBase`, and the two restrictions of scalars agree. -/
theorem deRhamCohomologyBaseModule_eq (i : ℤ) :
    Scheme.Hom.deRhamCohomologyBaseModule p i
      = (ModuleCat.restrictScalars
          ((structureSheafHom (inverseImageBaseProjection p)).hom.app (op ⊤)).hom).obj
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing (inverseImageBase p)).obj.obj (op ⊤))) i).obj
          ((derivedSectionsOverOpen (inverseImageBase p) ⊤).obj
            (DerivedCategory.Q.obj (deRhamCochainComplex p)))) :=
  rfl

/-- **`Rp_*Ω^•_{X/S}` in the unbounded derived category of `𝒪_S`-modules**: the unbounded
derived direct image, along the projection `(X, p^{-1}𝒪_S) ⟶ S`, of the relative de Rham
complex. -/
abbrev derivedDeRhamDirectImageUnbounded :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
      (inverseImageBaseProjection p)).obj
    (DerivedCategory.Q.obj (deRhamCochainComplex p))

/-- **[Stacks, Tag 0D5W] for the relative de Rham complex.** Relative de Rham cohomology
`H^i_{dR}(X/S)`, read as a module over `H^0(S, 𝒪_S)`, is the `i`-th cohomology of the derived
global sections on `S` of the derived direct image of the relative de Rham complex.

Three steps: the restriction of scalars that `H^i_{dR}` applies after taking cohomology is moved
inside, past the cohomology functor and past the derived functor, by
`StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso` and
`Stacks.Cohomology.DerivedSectionsRestrictScalars.derivedPreimageSectionsRestrictIso`; what is
left is derived sections over `p^{-1}⊤ = ⊤` with scalars restricted, which is Leray's
`derivedPreimageSections`, and [Stacks, Tag 0D5W] identifies that with derived sections on `S`
of the derived direct image. -/
def deRhamCohomologyBaseModuleIso (i : ℤ) :
    Scheme.Hom.deRhamCohomologyBaseModule p i ≅
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op ⊤))) i).obj
        ((derivedSectionsOverOpen S.toRingedSpace ⊤).obj
          (derivedDeRhamDirectImageUnbounded p)) :=
  eqToIso (deRhamCohomologyBaseModule_eq p i) ≪≫
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (ModuleCat.restrictScalars
          ((structureSheafHom (inverseImageBaseProjection p)).hom.app (op ⊤)).hom) i).app
      ((derivedSectionsOverOpen (inverseImageBase p) ⊤).obj
        (DerivedCategory.Q.obj (deRhamCochainComplex p)))).symm ≪≫
    (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op ⊤))) i).mapIso
      (((derivedPreimageSectionsRestrictIso (inverseImageBaseProjection p) ⊤).app
        (DerivedCategory.Q.obj (deRhamCochainComplex p))).symm ≪≫
        ((derivedSectionsPushforwardIso (inverseImageBaseProjection p) ⊤).app
          (DerivedCategory.Q.obj (deRhamCochainComplex p))).symm)

/-! ### The bounded below and the unbounded derived direct image -/

section Plus

variable {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasDerivedCategory.{u + 1} C]

/-- The localization of a bounded below complex computed through the homotopy category agrees
with the one computed directly. This is `plusQIsoOn` of
`StacksFrontier/AlgebraicGeometry/DeRham/Functoriality.lean`, for an arbitrary abelian category. -/
def plusQhIso (L : CochainComplex.Plus C) :
    DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj L) ≅
      DerivedCategory.Plus.Q.obj L :=
  DerivedCategory.Plus.ι.preimageIso ((DerivedCategory.quotientCompQhIso C).app L.obj)

/-- **A bounded below complex has the same image in `D(C)` whether it is localized in `D⁺(C)`
and then included, or localized directly.** `DerivedCategory.Plus.QhCompιIsoιCompQh` is the
identity, so the inclusion of the homotopy-category route is the unbounded localization. -/
def plusιQIso (L : CochainComplex.Plus C) :
    DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj L) ≅
      DerivedCategory.Q.obj L.obj :=
  (DerivedCategory.Plus.ι.mapIso (plusQhIso L)).symm ≪≫
    (DerivedCategory.quotientCompQhIso C).app L.obj

end Plus

/-- The relative de Rham complex of `p` as a bounded below complex of `p^{-1}𝒪_S`-modules. -/
abbrev deRhamCochainComplexPlus : CochainComplex.Plus (Modules (inverseImageBase p)) :=
  ⟨deRhamCochainComplex p, 0, inferInstance⟩

/-- **`Rp_*Ω^•_{X/S}` computed in `D⁺(𝒪_S)` and in `D(𝒪_S)` agree.** The bounded below derived
direct image `Stacks.DeRhamDirectImage.derivedDeRhamDirectImage`, whose cohomology sheaves
[Stacks, Tag 0FLY] shows to be coherent, becomes the unbounded derived direct image that the
Leray comparison produces, once it is included into `D(𝒪_S)`.

The direct image is the same functor in both spellings
(`relativePushforward_eq_modulePushforward`), `boundedDerivedPushforwardIso` compares the two
derived functors of it, and `plusιQIso` identifies the two localizations of the de Rham
complex. -/
def derivedDeRhamDirectImageUnboundedIso :
    DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage p) ≅
      derivedDeRhamDirectImageUnbounded p :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedDerivedPushforwardIso
      (inverseImageBaseProjection p)).app
    (DerivedCategory.Plus.Q.obj (deRhamCochainComplexPlus p)) ≪≫
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
      (inverseImageBaseProjection p)).mapIso (plusιQIso (deRhamCochainComplexPlus p))

/-! ### Finiteness over a Noetherian affine base -/

section Affine

open Stacks.DeRhamDirectImage (isQuasicoherent_homology_derivedDeRhamDirectImage)

variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of A))

/-- **`Rp_*Ω^•_{X/Spec A}` as an object of `D_QCoh(𝒪_{Spec A})`**, read in the unbounded derived
category: the cohomology sheaves are quasi-coherent by [Stacks, Tag 0FLX], and
`DerivedCategory.Plus.homologyFunctor` is the inclusion followed by the unbounded one. -/
def deRhamDirectImageQCoh [QuasiCompact q] [QuasiSeparated q] :
    (DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)).FullSubcategory :=
  ⟨DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage q),
    fun n => isQuasicoherent_homology_derivedDeRhamDirectImage q n⟩

/-- **Relative de Rham cohomology over an affine base, as an `A`-module, is the cohomology of
`RΓ(Spec A, Rp_*Ω^•_{X/Spec A})` in `D(A)`.**

`AlgebraicGeometry.globalSectionsOver` at the identity of `Spec A` is sections over the whole
space with scalars restricted along `A ≅ Γ(Spec A, 𝒪)`, so `derivedGlobalSectionsOver` is
`derivedSectionsRestrict` and `derivedSectionsRestrictIso` moves that restriction outside the
derived functor, exactly as the Leray step did for `p^{-1}𝒪_S`. -/
def deRhamCohomologyModuleIso [QuasiCompact q] [QuasiSeparated q] (i : ℤ) :
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).obj
        (Scheme.Hom.deRhamCohomologyBaseModule q i) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (CommRingCat.of A)) i).obj
        ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj
          (deRhamDirectImageQCoh q)) :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).mapIso
      (deRhamCohomologyBaseModuleIso q i) ≪≫
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) i).app
      ((derivedSectionsOverOpen (Spec (CommRingCat.of A)).toRingedSpace ⊤).obj
        (derivedDeRhamDirectImageUnbounded q))).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (CommRingCat.of A)) i).mapIso
      (((derivedSectionsRestrictIso (Spec (CommRingCat.of A)).toRingedSpace ⊤
          (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).app
        (derivedDeRhamDirectImageUnbounded q)).symm ≪≫
        (derivedSectionsRestrict (Spec (CommRingCat.of A)).toRingedSpace ⊤
          (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).mapIso
          (derivedDeRhamDirectImageUnboundedIso q).symm)

/-- **[Stacks, Tag 0FLZ].** Let `A` be a Noetherian ring and let `X` be a proper scheme over
`S = Spec A`. Then `H^i_{dR}(X/S)` is a finite `A`-module, for every `i`.

The de Rham cohomology is the library's `AlgebraicGeometry.Scheme.Hom.deRhamCohomology`, read as
an `A`-module along `A ≅ Γ(Spec A, 𝒪)`; no hypothesis beyond the tag's own is assumed. By
[Stacks, Tag 0D5W] it is the cohomology of `RΓ(Spec A, Rp_*Ω^•_{X/S})`, whose cohomology sheaves
are coherent by [Stacks, Tag 0FLY] — unconditionally, [Stacks, Tag 02O5] being discharged in
this library — and over a Noetherian affine base the cohomology of derived global sections of a
complex with coherent cohomology sheaves is a finite module. -/
@[stacks 0FLZ]
theorem moduleFinite_deRhamCohomologyBaseModule_of_isProper [IsNoetherianRing A] [IsProper q]
    (i : ℤ) :
    Module.Finite A
      ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).obj
        (Scheme.Hom.deRhamCohomologyBaseModule q i)) :=
  have hcoh : ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules i).obj
      (deRhamDirectImageQCoh q).obj).IsCoherent :=
    DeRhamCoherentDirectImage.isCoherent_homology_derivedDeRhamDirectImage_of_isProper q i
  have := moduleFinite_homology_derivedGlobalSectionsQuasicoherent
    (CommRingCat.of A) i (deRhamDirectImageQCoh q) hcoh
  Module.Finite.equiv (deRhamCohomologyModuleIso q i).symm.toLinearEquiv

end Affine

end AlgebraicGeometry.DeRhamCohomologyDirectImage

end
