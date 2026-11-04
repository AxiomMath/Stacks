module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularAnyModel
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# The right adjoint of `Rf_*` on `D_QCoh`, at an arbitrary chosen derived category

[Stacks, Tag 0A9E] says that for a morphism `f : X ⟶ Y` between quasi-compact and quasi-separated
schemes the functor `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint — the twisted inverse
image `f^×`. The source's proof is Brown representability ([Stacks, Tag 0A8G]) and is carried out
in `StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QcqsCompactGeneration.lean`, as
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs`.

That proof can only be run at a **locally small** model of the derived categories.
`HasDerivedCategory.{w} C`
carries the localized category as *data*, and Brown representability asks for direct sums indexed
by the morphism universe of the category; at `CategoryTheory.HasDerivedCategory.standard` that
universe is `u + 1` while direct sums of `𝒪_X`-modules are indexed by `Type u`, so the hypothesis
is false there rather than merely unavailable. The Brown proof is therefore pinned to
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, whose morphisms live in `Type u`.

A statement proved at one model says nothing about another until it is transported, and the
consumers of the adjoint in this development — the sheafy trace map of [Stacks, Tag 0B6H] and
[Stacks, Tag 0B6I] in `StacksFrontier/AlgebraicGeometry/Duality/SheafyTrace.lean` and
`StacksFrontier/AlgebraicGeometry/Duality/SheafyTraceGlobalHom.lean` — run at
`HasDerivedCategory.standard` and take the adjoint as a hypothesis for exactly this reason. This
file removes the pin: the conclusion of [Stacks, Tag 0A9E] holds at **every** chosen model, in
particular at the standard one.

## The transport

Two chosen models of `D(𝒪_Z)` are compared by `StacksDraft.DerivedModel.modelEquiv`, the
equivalence coming from the uniqueness of the localization of the homotopy category, and that
equivalence identifies the cohomology functors of the two models
(`StacksDraft.DerivedModel.modelEquivCompHomologyFunctorIso`). So it carries the objects with
quasi-coherent cohomology to the objects with quasi-coherent cohomology, in both directions, and
restricts to an equivalence `D_QCoh(𝒪_Z)` at the one model `≌` `D_QCoh(𝒪_Z)` at the other. It
also intertwines the two readings of `Rf_*`, both being total right derived functors of degreewise
direct image followed by a localization
(`StacksDraft.DerivedModel.rightDerivedModelIso`). The square of those four functors commutes, so
a left adjoint at one model is, up to the two equivalences, a left adjoint at the other.

## Main definitions

* `Stacks.Duality.AnyModel.quasiCoherentModelEquiv` — `D_QCoh(𝒪_Z)` read at two chosen models of
  `D(𝒪_Z)`: the restriction of the comparison equivalence.
* `Stacks.Duality.AnyModel.derivedPushforwardModelIso` — `Rf_*` read at two chosen models.
* `Stacks.Duality.AnyModel.quasiCoherentDerivedPushforwardModelIso` — the restriction of `Rf_*` to
  `D_QCoh` read at two chosen models: the commuting square the transport uses.

## Main results

* `Stacks.Duality.AnyModel.isQuasicoherent_homology_derivedPushforward_of_qcqs` — part (1) of
  [Stacks, Tag 08D5] at an arbitrary chosen model, in the spelling of the hypothesis `hpush` of
  `Stacks.Duality.quasiCoherentDerivedPushforward`, so that the restricted functor can be written
  down at any model with nothing supplied.
* `Stacks.Duality.AnyModel.isLeftAdjoint_quasiCoherentDerivedPushforward_of_model` — the transport
  itself: a right adjoint of the restricted `Rf_*` at one model gives one at any other.
* `Stacks.Duality.AnyModel.isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs` — the conclusion
  of [Stacks, Tag 0A9E] at an arbitrary chosen model, for the restriction of `Rf_*` formed with an
  arbitrary proof that it preserves quasi-coherence of cohomology.
* `Stacks.Duality.AnyModel.isLeftAdjoint_restrictedDerivedPushforward` —
  **[Stacks, Tag 0A9E] at an arbitrary chosen model** of the two derived categories, for the
  canonical restriction.
* `Stacks.Duality.AnyModel.isLeftAdjoint_restrictedDerivedPushforward_standard` — the same at
  `CategoryTheory.HasDerivedCategory.standard`, which is the model the consumers of the adjoint
  run at.
* `Stacks.Duality.AnyModel.twistedInverseImage` and
  `Stacks.Duality.AnyModel.twistedInverseImageAdjunction` — the adjoint and the adjunction
  themselves, at an arbitrary chosen model.

## Implementation notes

**Nothing is assumed.** The only input about the geometry of `f` is
[Stacks, Tag 0A9E] at the locally small model and part (1) of [Stacks, Tag 08D5] at an arbitrary
model, `AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs`;
both are unconditional. The hypotheses of the statements below are `CompactSpace` and
`QuasiSeparatedSpace` on the two schemes, which is the tag's hypothesis that `X` and `Y` be
quasi-compact and quasi-separated; the quasi-compactness and quasi-separatedness of the *morphism*
that the proof uses are derived from them by instance search
(`AlgebraicGeometry.quasiCompact_of_compactSpace`,
`AlgebraicGeometry.QuasiSeparated.of_quasiSeparatedSpace`), which is the source's own step through
[Stacks, Tag 01KV] and [Stacks, Tag 03GI].

**The two models are not required to have the same morphism universe.** `D_QCoh(𝒪_X)` and
`D_QCoh(𝒪_Y)` at one model are compared with the same two at another, and the two models may be
any pair; what is required is that the chosen models of `D(𝒪_X)` and `D(𝒪_Y)` have the *same*
morphism universe as each other, which is what writing down `Rf_*` needs.

**All `HasDerivedCategory` arguments are explicit.** The import closure carries the locally small
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` as a global instance, so a left implicit
argument would silently elaborate at that model and the statements would say nothing new.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 01KV](https://stacks.math.columbia.edu/tag/01KV)
* [Stacks Project, Tag 03GI](https://stacks.math.columbia.edu/tag/03GI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open StacksDraft.DerivedModel

universe w z u

namespace Stacks.Duality.AnyModel

/-! ### `D_QCoh(𝒪_Z)` at two chosen models -/

/-- Quasi-coherence of a sheaf of modules on a scheme is closed under isomorphism: it is the first
of the three conditions in
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre`, spelled at
`AlgebraicGeometry.Scheme.Modules`, which is the spelling the quasi-coherent derived category is
cut out in. -/
theorem isClosedUnderIsomorphisms_isQuasicoherent (Z : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf :
      ObjectProperty Z.Modules).IsClosedUnderIsomorphisms :=
  (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre
    Z).isClosedUnderIsomorphisms

/-- The property of an object of a chosen model of `D(𝒪_Z)` that all of its cohomology sheaves are
quasi-coherent: the property whose full subcategory is `D_QCoh(𝒪_Z)`. -/
abbrev quasiCoherentProp (Z : Scheme.{u}) (h : HasDerivedCategory.{w} Z.Modules) :
    ObjectProperty (@DerivedCategory Z.Modules _ _ h) :=
  @DerivedCategoryB.derivedCategoryB Z.Modules _ _ h
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf)

/-- Having quasi-coherent cohomology in every degree is closed under isomorphism: the cohomology
functors carry an isomorphism to an isomorphism, and quasi-coherence of a sheaf of modules is
closed under isomorphism. -/
theorem isClosedUnderIsomorphisms_quasiCoherentProp (Z : Scheme.{u})
    (h : HasDerivedCategory.{w} Z.Modules) :
    (quasiCoherentProp Z h).IsClosedUnderIsomorphisms where
  of_iso e hK n :=
    (isClosedUnderIsomorphisms_isQuasicoherent Z).of_iso
      ((@DerivedCategory.homologyFunctor Z.Modules _ _ h n).mapIso e) (hK n)

/-- **Quasi-coherence of all cohomology sheaves is model-independent.** The comparison equivalence
of two chosen models of `D(𝒪_Z)` identifies their cohomology functors, so an object of the first
model has quasi-coherent cohomology exactly when its image in the second does. -/
theorem inverseImage_quasiCoherentProp (Z : Scheme.{u})
    (h₁ : HasDerivedCategory.{w} Z.Modules) (h₂ : HasDerivedCategory.{z} Z.Modules) :
    (quasiCoherentProp Z h₂).inverseImage (modelEquiv h₁ h₂).functor =
      quasiCoherentProp Z h₁ := by
  funext K
  exact propext (forall_congr' fun n =>
    @prop_iff_of_iso _ _ _ (isClosedUnderIsomorphisms_isQuasicoherent Z) _ _
    ((modelEquivCompHomologyFunctorIso h₁ h₂ n).app K))

/-- **`D_QCoh(𝒪_Z)` read at two chosen models of `D(𝒪_Z)`.** The comparison equivalence of the two
models restricts to the full subcategories of objects with quasi-coherent cohomology, that
property being model-independent. -/
def quasiCoherentModelEquiv (Z : Scheme.{u}) (h₁ : HasDerivedCategory.{w} Z.Modules)
    (h₂ : HasDerivedCategory.{z} Z.Modules) :
    @quasiCoherentDerivedCategory Z h₁ ≌ @quasiCoherentDerivedCategory Z h₂ :=
  letI := isClosedUnderIsomorphisms_quasiCoherentProp Z h₂
  Equivalence.congrFullSubcategory (modelEquiv h₁ h₂) (inverseImage_quasiCoherentProp Z h₁ h₂)

/-! ### `Rf_*` at two chosen models -/

section Pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hX₁ : HasDerivedCategory.{w} X.Modules) (hY₁ : HasDerivedCategory.{w} Y.Modules)
  (hX₂ : HasDerivedCategory.{z} X.Modules) (hY₂ : HasDerivedCategory.{z} Y.Modules)

/-- **`Rf_*` read at two chosen models.** Both readings are total right derived functors of
degreewise direct image followed by the localization of the target, and the comparison
equivalences identify the two localizations, so the square of the two readings and the two
comparisons commutes. -/
def derivedPushforwardModelIso :
    @derivedPushforward X Y f hX₁ hY₁ ⋙ (modelEquiv hY₁ hY₂).functor ≅
      (modelEquiv hX₁ hX₂).functor ⋙ @derivedPushforward X Y f hX₂ hY₂ :=
  rightDerivedModelIso (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    ((@homotopyPushforward X Y f hY₁).totalRightDerivedUnit
      (@DerivedCategory.Qh X.Modules _ _ hX₁)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
    ((@homotopyPushforward X Y f hY₂).totalRightDerivedUnit
      (@DerivedCategory.Qh X.Modules _ _ hX₂)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
    (Localization.compUniqFunctor (@DerivedCategory.Qh X.Modules _ _ hX₁)
      (@DerivedCategory.Qh X.Modules _ _ hX₂)
      (HomotopyCategory.subcategoryAcyclic X.Modules).trW)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (Localization.compUniqFunctor (@DerivedCategory.Qh Y.Modules _ _ hY₁)
        (@DerivedCategory.Qh Y.Modules _ _ hY₂)
        (HomotopyCategory.subcategoryAcyclic Y.Modules).trW))

/-- **The restriction of `Rf_*` to `D_QCoh` read at two chosen models.** On the full subcategories
the square commutes because it commutes on the ambient derived categories: the inclusion of a full
subcategory is fully faithful and the restricted functors are the ambient ones. -/
def quasiCoherentDerivedPushforwardModelIso
    (hpush₁ : ∀ (K : @quasiCoherentDerivedCategory X hX₁) (i : ℤ),
      ((@DerivedCategory.homologyFunctor Y.Modules _ _ hY₁ i).obj
        ((@derivedPushforward X Y f hX₁ hY₁).obj K.obj)).IsQuasicoherent)
    (hpush₂ : ∀ (K : @quasiCoherentDerivedCategory X hX₂) (i : ℤ),
      ((@DerivedCategory.homologyFunctor Y.Modules _ _ hY₂ i).obj
        ((@derivedPushforward X Y f hX₂ hY₂).obj K.obj)).IsQuasicoherent) :
    @quasiCoherentDerivedPushforward X Y f hX₁ hY₁ hpush₁ ⋙
        (quasiCoherentModelEquiv Y hY₁ hY₂).functor ≅
      (quasiCoherentModelEquiv X hX₁ hX₂).functor ⋙
        @quasiCoherentDerivedPushforward X Y f hX₂ hY₂ hpush₂ :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _
      ((derivedPushforwardModelIso f hX₁ hY₁ hX₂ hY₂).app K.obj))
    (fun g => ObjectProperty.hom_ext _
      ((derivedPushforwardModelIso f hX₁ hY₁ hX₂ hY₂).hom.naturality g.hom))

/-- **A right adjoint of the restricted `Rf_*` at one model gives one at any other model.** The
functor at the second model is, up to the two comparison equivalences, the functor at the first,
so it is isomorphic to a composite of three left adjoints: the inverse of the comparison on the
source, the functor at the first model, and the comparison on the target. -/
theorem isLeftAdjoint_quasiCoherentDerivedPushforward_of_model
    (hpush₁ : ∀ (K : @quasiCoherentDerivedCategory X hX₁) (i : ℤ),
      ((@DerivedCategory.homologyFunctor Y.Modules _ _ hY₁ i).obj
        ((@derivedPushforward X Y f hX₁ hY₁).obj K.obj)).IsQuasicoherent)
    (hpush₂ : ∀ (K : @quasiCoherentDerivedCategory X hX₂) (i : ℤ),
      ((@DerivedCategory.homologyFunctor Y.Modules _ _ hY₂ i).obj
        ((@derivedPushforward X Y f hX₂ hY₂).obj K.obj)).IsQuasicoherent)
    (hadj : (@quasiCoherentDerivedPushforward X Y f hX₁ hY₁ hpush₁).IsLeftAdjoint) :
    (@quasiCoherentDerivedPushforward X Y f hX₂ hY₂ hpush₂).IsLeftAdjoint := by
  obtain ⟨R, ⟨adj⟩⟩ := hadj.exists_rightAdjoint
  exact (((quasiCoherentModelEquiv X hX₁ hX₂).symm.toAdjunction.comp
      (adj.comp (quasiCoherentModelEquiv Y hY₁ hY₂).toAdjunction)).ofNatIsoLeft
    (Functor.isoWhiskerLeft (quasiCoherentModelEquiv X hX₁ hX₂).inverse
        (quasiCoherentDerivedPushforwardModelIso f hX₁ hY₁ hX₂ hY₂ hpush₁ hpush₂) ≪≫
      (quasiCoherentModelEquiv X hX₁ hX₂).invFunIdAssoc _)).isLeftAdjoint

end Pushforward

/-! ### Tag 0A9E at an arbitrary chosen model -/

section Qcqs

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **Part (1) of [Stacks, Tag 08D5] at an arbitrary chosen model**, in the spelling of the
hypothesis `hpush` of `Stacks.Duality.quasiCoherentDerivedPushforward`: for `f` a morphism between
quasi-compact quasi-separated schemes, `Rf_*` carries an object with quasi-coherent cohomology to
an object with quasi-coherent cohomology, so the restriction
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` can be formed at any chosen model with nothing supplied. -/
theorem isQuasicoherent_homology_derivedPushforward_of_qcqs
    (hX : HasDerivedCategory.{w} X.Modules) (hY : HasDerivedCategory.{w} Y.Modules)
    (K : @quasiCoherentDerivedCategory X hX) (i : ℤ) :
    ((@DerivedCategory.homologyFunctor Y.Modules _ _ hY i).obj
      ((@derivedPushforward X Y f hX hY).obj K.obj)).IsQuasicoherent :=
  @AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs
    X Y f hX hY _ _ _ K.obj K.2 i

/-- **The restriction of `Rf_*` to `D_QCoh` at an arbitrary chosen model**, with the
quasi-coherence of its values discharged: this is the functor
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` whose right adjoint [Stacks, Tag 0A9E] produces, read at any
chosen model. -/
abbrev restrictedDerivedPushforward (hX : HasDerivedCategory.{w} X.Modules)
    (hY : HasDerivedCategory.{w} Y.Modules) :
    @quasiCoherentDerivedCategory X hX ⥤ @quasiCoherentDerivedCategory Y hY :=
  @quasiCoherentDerivedPushforward X Y f hX hY
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f hX hY)

/-- **[Stacks, Tag 0A9E] at an arbitrary chosen model, for an arbitrary restriction of `Rf_*`.**
Let `f : X ⟶ Y` be a morphism between quasi-compact and quasi-separated schemes and let a model of
each of `D(𝒪_X)` and `D(𝒪_Y)` be chosen. Then `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right
adjoint, whichever proof that `Rf_*` preserves quasi-coherence of cohomology is used to restrict
it.

The proof transports the Brown representability argument from the locally small model, where it
runs: the comparison equivalences of the two models restrict to `D_QCoh`
(`Stacks.Duality.AnyModel.quasiCoherentModelEquiv`) and intertwine the two readings of the
restricted `Rf_*` (`Stacks.Duality.AnyModel.quasiCoherentDerivedPushforwardModelIso`), so the
functor here is isomorphic to a composite of three left adjoints. -/
theorem isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs
    (hX : HasDerivedCategory.{w} X.Modules) (hY : HasDerivedCategory.{w} Y.Modules)
    (hpush : ∀ (K : @quasiCoherentDerivedCategory X hX) (i : ℤ),
      ((@DerivedCategory.homologyFunctor Y.Modules _ _ hY i).obj
        ((@derivedPushforward X Y f hX hY).obj K.obj)).IsQuasicoherent) :
    (@quasiCoherentDerivedPushforward X Y f hX hY hpush).IsLeftAdjoint :=
  isLeftAdjoint_quasiCoherentDerivedPushforward_of_model f
    (Scheme.Modules.hasDerivedCategory X) (Scheme.Modules.hasDerivedCategory Y) hX hY
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f) hpush
    (Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs f)

/-- **[Stacks, Tag 0A9E] at an arbitrary chosen model of the two derived categories.** Let
`f : X ⟶ Y` be a morphism between quasi-compact and quasi-separated schemes. Then
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint — the twisted inverse image `f^×` — at
every chosen model of `D(𝒪_X)` and `D(𝒪_Y)`, and not only at the locally small model at which the
Brown representability argument of the source can be run.

The functor is the canonical `Stacks.Duality.AnyModel.restrictedDerivedPushforward`: that `Rf_*`
carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)` at all is part (1) of [Stacks, Tag 08D5] and is
discharged, at any model. -/
@[stacks 0A9E "at an arbitrary chosen model of the two derived categories, the Brown \
representability argument of the source being available only at a locally small one"]
theorem isLeftAdjoint_restrictedDerivedPushforward (hX : HasDerivedCategory.{w} X.Modules)
    (hY : HasDerivedCategory.{w} Y.Modules) :
    (restrictedDerivedPushforward f hX hY).IsLeftAdjoint :=
  isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs f hX hY _

/-- **[Stacks, Tag 0A9E] at `CategoryTheory.HasDerivedCategory.standard`.** For a morphism
`f : X ⟶ Y` between quasi-compact and quasi-separated schemes, `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`
has a right adjoint at the standard model of the two derived categories — the model at which the
sheafy trace map of [Stacks, Tag 0B6H] and the duality statements built on it are stated, and
which carries the adjoint as a hypothesis for want of this statement.

Brown representability cannot be run here: it asks for direct sums indexed by the morphism
universe of the category, which at the standard model is `u + 1`, while the direct sums of
`𝒪_X`-modules are indexed by `Type u`. The adjoint is obtained by transport from the locally small
model.

No `@[stacks]` attribute is placed: this is the instance at one model of
`Stacks.Duality.AnyModel.isLeftAdjoint_restrictedDerivedPushforward`, which carries the tag and
states it at every model. -/
theorem isLeftAdjoint_restrictedDerivedPushforward_standard :
    (restrictedDerivedPushforward f (HasDerivedCategory.standard X.Modules)
      (HasDerivedCategory.standard Y.Modules)).IsLeftAdjoint :=
  isLeftAdjoint_restrictedDerivedPushforward f _ _

/-- **The twisted inverse image `f^×` at an arbitrary chosen model**: the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` whose existence is [Stacks, Tag 0A9E]. -/
abbrev twistedInverseImage (hX : HasDerivedCategory.{w} X.Modules)
    (hY : HasDerivedCategory.{w} Y.Modules) :
    @quasiCoherentDerivedCategory Y hY ⥤ @quasiCoherentDerivedCategory X hX :=
  letI := isLeftAdjoint_restrictedDerivedPushforward f hX hY
  (restrictedDerivedPushforward f hX hY).rightAdjoint

/-- **The adjunction `Rf_* ⊣ f^×` at an arbitrary chosen model**, which is what the duality
statements consume. -/
def twistedInverseImageAdjunction (hX : HasDerivedCategory.{w} X.Modules)
    (hY : HasDerivedCategory.{w} Y.Modules) :
    restrictedDerivedPushforward f hX hY ⊣ twistedInverseImage f hX hY :=
  letI := isLeftAdjoint_restrictedDerivedPushforward f hX hY
  Adjunction.ofIsLeftAdjoint (restrictedDerivedPushforward f hX hY)

end Qcqs

end Stacks.Duality.AnyModel

end
