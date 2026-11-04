module

public import StacksFrontier.AlgebraicGeometry.Spaces.Coherator
public import StacksFrontier.AlgebraicGeometry.Spaces.CoheratorFlatPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectiveQuasicoherentPushforwardOfFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSeparator
public import StacksFrontier.Homology.Injectives.DerivedCategory.ExactLeftAdjointComparison
public import StacksFrontier.Homology.Injectives.DerivedCategory.RightDerivedTriangulated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The coherator and the direct image along a flat qcqs morphism of algebraic spaces

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and flat morphism of algebraic spaces over a
scheme `S` contained in a big fppf site `B`.  The direct image preserves quasi-coherence
(Stacks 03M9), so it restricts to `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`, whose total right derived
functor is written `Φ`.  **Stacks 08GZ** asserts `RQ_Y ∘ Rf_* = Φ ∘ RQ_X`, where `RQ_X` is the
total right derived functor of the coherator, the right adjoint of the inclusion
`QCoh(𝒪_X) ⥤ Mod(𝒪_X)`.

Every input of the source's proof is a result of the development:

* quasi-compactness and quasi-separatedness of `f` give Stacks 03M9,
  `AlgebraicGeometry.Space.pushforwardPreservesQuasicoherence_of_qcqs`;
* the inverse image preserves quasi-coherence along every morphism, Stacks 03GA,
  `AlgebraicGeometry.Space.quasicoherentPullbackFunctor`, and the adjunction `f^* ⊣ f_*`
  restricts to `QCoh`, `AlgebraicGeometry.Space.quasicoherentPullbackFunctorAdjunction`;
* `QCoh(𝒪_X)` is Grothendieck abelian, Stacks 077V part (1),
  `AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian`, and so is `Mod(𝒪_X)`,
  `AlgebraicGeometry.Space.isGrothendieckAbelian_modules`;
* flatness of `f` is flatness of the induced morphism of small étale ringed topoi, Stacks 073C,
  `AlgebraicGeometry.Space.isFlat_iff_smallEtaleRingedToposHom_isFlat`, so the inverse image is
  exact (Stacks 04JC), on all modules and on the quasi-coherent ones.

The comparison itself is `Stacks.DerivedModel.rightDerivedCompIsoOfExactLeftAdjoints`: both
composites are right adjoint to the same functor `D(QCoh(𝒪_Y)) ⥤ D(𝒪_X)` by Stacks 09T5.

## Main results

* `AlgebraicGeometry.Space.preservesFiniteLimits_quasicoherentPullbackFunctor_of_isFlat` and
  `AlgebraicGeometry.Space.preservesFiniteColimits_quasicoherentPullbackFunctor`: exactness of the
  inverse image on quasi-coherent modules along a flat morphism.
* `AlgebraicGeometry.Space.flatPushforwardDerivedCoheratorIsoOfQcqs`: Stacks 08GZ for arbitrary
  models of the derived categories, coherators and derived functors.
* `AlgebraicGeometry.Space.derivedQuasicoherentPushforward`: the derived direct image `Φ` on
  quasi-coherent modules, which exists by K-injective resolutions in the Grothendieck abelian
  category `QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.derivedModulePushforwardComplexUnit`: the derivation unit of the
  derived direct image `Rf_*` on all modules,
  `AlgebraicGeometry.Space.derivedModulePushforward`, read along the localization of the cochain
  complexes.
* `AlgebraicGeometry.Space.derivedModulePushforwardCompDerivedCoheratorIso`: **Stacks 08GZ**, at
  `Rf_*`, `Φ` and the derived coherators `AlgebraicGeometry.Space.derivedCoherator`.

## Implementation notes

As in `AlgebraicGeometry.Space.flatPushforwardDerivedCoheratorIso`, the derived categories, their
localizations, the coherators and the four total right derived functors are arbitrary: the source
says "the right adjoint of the inclusion" and "the right derived functor", each determined only up
to a canonical isomorphism, so its equality of functors becomes a natural isomorphism valid for
every choice.  Additivity of the coherators, which their derived functors need in order to be
stated, is not a hypothesis: it is `CategoryTheory.Adjunction.right_adjoint_additive` of the
coherator adjunction, inserted by `letI` in the binders.

`Rf_*` is the derived direct image `AlgebraicGeometry.Space.derivedModulePushforward`, the right
adjoint of `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`, and not a second
construction of it.  Its derivation unit
`AlgebraicGeometry.Space.derivedModulePushforwardUnit` is given along `DerivedCategory.Qh`, the
localization of the homotopy category, whereas the comparison here is stated for a derived
functor along `DerivedCategory.Q`, the localization of the cochain complexes;
`Stacks.Injectives.complexUnit` transports the unit between the two presentations, and
`AlgebraicGeometry.Space.derivedModulePushforward_isRightDerivedFunctor` is that transport, both
presentations being recognised by the invertibility of the unit at the K-injective complexes
(Stacks 070K).

`AlgebraicGeometry.Space.derivedModulePushforwardComplexUnit` is `@[no_expose]`: the transport
contains the `eqToHom` of an equality of functors between the two spellings of the direct image,
the modules of the small étale ringed site and those of the small étale ringed topos, which are
definitionally but not syntactically equal, and unfolding it outside this module costs the kernel
that identification at every occurrence.  The handle a consumer has on the unit is its type and
`derivedModulePushforward_isRightDerivedFunctor`, which is all any of them uses.

## References

* [Stacks Project, Tag 08GZ](https://stacks.math.columbia.edu/tag/08GZ)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 073C](https://stacks.math.columbia.edu/tag/073C)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe w w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-- The inverse image on quasi-coherent modules is additive, being the corestriction of the
additive inverse image of all modules. -/
instance quasicoherentPullbackFunctor_additive (f : X ⟶ Y) :
    (quasicoherentPullbackFunctor B S hS f).Additive :=
  have : (quasicoherentPullbackFunctor B S hS f ⋙ quasicoherentSheavesι B S hS X).Additive :=
    Functor.additive_of_iso
      (F := quasicoherentSheavesι B S hS Y ⋙ modulePullback B S hS f)
      (ObjectProperty.liftCompιIso _ _ _).symm
  Functor.additive_of_comp_faithful _ (quasicoherentSheavesι B S hS X)

/-- **The inverse image on quasi-coherent modules along a flat morphism is left exact.**  Flatness
of `f` is flatness of the morphism of small étale ringed topoi (Stacks 073C), so the inverse image
of all modules is left exact (Stacks 04JC); the inclusion of the quasi-coherent modules is exact
and reflects isomorphisms, so left exactness descends. -/
@[sga "6 0 2.9" "partial"]
theorem preservesFiniteLimits_quasicoherentPullbackFunctor_of_isFlat (f : X ⟶ Y)
    (hflat : IsFlat B S hS f.hom) :
    PreservesFiniteLimits (quasicoherentPullbackFunctor B S hS f) := by
  have := preservesFiniteLimits_modulePullback_of_isFlat B S hS f
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS f).mp hflat)
  have : PreservesFiniteLimits
      (quasicoherentPullbackFunctor B S hS f ⋙ quasicoherentSheavesι B S hS X) :=
    preservesFiniteLimits_of_natIso (ObjectProperty.liftCompιIso _ _ _).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (quasicoherentSheavesι B S hS X)

/-- **The inverse image on quasi-coherent modules is right exact.**  The inverse image of all
modules is a left adjoint, and the inclusion of the quasi-coherent modules is exact and reflects
isomorphisms, so right exactness descends. -/
theorem preservesFiniteColimits_quasicoherentPullbackFunctor (f : X ⟶ Y) :
    PreservesFiniteColimits (quasicoherentPullbackFunctor B S hS f) := by
  have := preservesFiniteColimits_modulePullback_smallEtale B S hS f
  have : PreservesFiniteColimits
      (quasicoherentPullbackFunctor B S hS f ⋙ quasicoherentSheavesι B S hS X) :=
    preservesFiniteColimits_of_natIso (ObjectProperty.liftCompιIso _ _ _).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ (quasicoherentSheavesι B S hS X)

/-- **Stacks Project, Tag 08GZ, at arbitrary models.**  Let `f : X ⟶ Y` be a quasi-compact,
quasi-separated and flat morphism of algebraic spaces over `S`.  Let `Rf_*` be a total right
derived functor of the direct image of all modules, let `RQ_X`, `RQ_Y` be total right derived
functors of the coherators, the right adjoints of the inclusions `QCoh(𝒪_X) ⥤ Mod(𝒪_X)` and
`QCoh(𝒪_Y) ⥤ Mod(𝒪_Y)`, and let `Φ` be a total right derived functor of the direct image
`f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`, a functor by Stacks 03M9.  Then `Rf_* ⋙ RQ_Y ≅ RQ_X ⋙ Φ`. -/
def flatPushforwardDerivedCoheratorIsoOfQcqs (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hflat : IsFlat B S hS f.hom)
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS Y.1 Y.2)]
    [HasDerivedCategory.{w'} (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{w'} (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2)]
    (QX : CochainComplex (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ℤ ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2))
    [QX.IsLocalization (HomologicalComplex.quasiIso
      (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (QY : CochainComplex (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2) ℤ ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2))
    [QY.IsLocalization (HomologicalComplex.quasiIso
      (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]
    (CX : Modules.{u, u} B S hS X.1 X.2 ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
    (adjX : quasicoherentSheavesι B S hS X ⊣ CX)
    (CY : Modules.{u, u} B S hS Y.1 Y.2 ⥤ QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2)
    (adjY : quasicoherentSheavesι B S hS Y ⊣ CY)
    (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (RfUnit : (modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := Modules.{u, u} B S hS Y.1 Y.2) ⟶
      DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2) ⋙ Rf)
    [Rf.IsRightDerivedFunctor RfUnit
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (RQX : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2))
    (RQXUnit : letI := adjX.right_adjoint_additive
      CX.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QX ⟶
        DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2) ⋙ RQX)
    [RQX.IsRightDerivedFunctor RQXUnit
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (RQY : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2))
    (RQYUnit : letI := adjY.right_adjoint_additive
      CY.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QY ⟶
        DerivedCategory.Q (C := Modules.{u, u} B S hS Y.1 Y.2) ⋙ RQY)
    [RQY.IsRightDerivedFunctor RQYUnit
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]
    (Φ : DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2))
    (ΦUnit : (quasicoherentPushforward B S hS f
        (pushforwardPreservesQuasicoherence_of_qcqs B S hS f hfqc hfqs)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ QY ⟶ QX ⋙ Φ)
    [Φ.IsRightDerivedFunctor ΦUnit (HomologicalComplex.quasiIso
      (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] :
    Rf ⋙ RQY ≅ RQX ⋙ Φ :=
  have := adjX.right_adjoint_additive
  have := adjY.right_adjoint_additive
  have := preservesFiniteLimits_modulePullback_of_isFlat B S hS f
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS f).mp hflat)
  have := preservesFiniteColimits_modulePullback_smallEtale B S hS f
  have := preservesFiniteLimits_quasicoherentPullbackFunctor_of_isFlat B S hS f hflat
  have := preservesFiniteColimits_quasicoherentPullbackFunctor B S hS f
  have := isGrothendieckAbelian_modules B S hS X.1 X.2
  have := isGrothendieckAbelian_modules B S hS Y.1 Y.2
  have : IsGrothendieckAbelian.{u} (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) :=
    quasicoherentSheaves_isGrothendieckAbelian B S hS X.1 X.2
  Stacks.DerivedModel.rightDerivedCompIsoOfExactLeftAdjoints
    (qpb := quasicoherentPullbackFunctor B S hS f) (ObjectProperty.liftCompιIso _ _ _) adjX adjY
    (modulePullbackAdjunction B S hS f)
    (quasicoherentPullbackFunctorAdjunction B S hS f hfqc hfqs)
    DerivedCategory.Q DerivedCategory.Q QX QY Rf RfUnit RQX RQXUnit RQY RQYUnit Φ ΦUnit

/-! ### The comparison at the source's functors -/

section Concrete

attribute [local instance] HasDerivedCategory.standard

open Stacks.Injectives.KInjectiveResolution

/-- The direct image of `𝒪`-modules, applied termwise and followed by the localization, has a total
right derived functor on the whole homotopy category: the `𝒪_X`-modules are Grothendieck abelian,
so every cochain complex has a K-injective resolution. -/
instance modulePushforward_hasRightDerivedFunctor (f : X ⟶ Y) :
    ((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := Modules.{u, u} B S hS Y.1 Y.2)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
  letI := isGrothendieckAbelian_modules B S hS X.1 X.2
  hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (A := Modules.{u, u} B S hS Y.1 Y.2) (modulePushforward B S hS f)

/-- The derivation unit of `Rf_*` on cochain complexes: the unit
`AlgebraicGeometry.Space.derivedModulePushforwardUnit` of the derived direct image, which is
given along the localization `DerivedCategory.Qh` of the homotopy category, read along the
localization `DerivedCategory.Q` of the cochain complexes instead. -/
@[no_expose] def derivedModulePushforwardComplexUnit (f : X ⟶ Y) :
    (modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := Modules.{u, u} B S hS Y.1 Y.2) ⟶
      DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2) ⋙ derivedModulePushforward B S hS f :=
  letI := isGrothendieckAbelian_modules B S hS X.1 X.2
  Stacks.Injectives.complexUnit (modulePushforward B S hS f)
    (derivedModulePushforward B S hS f) (derivedModulePushforwardUnit B S hS f)

/-- The cochain-complex derivation unit exhibits `Rf_*` as a right derived functor of the direct
image along `DerivedCategory.Q`.  Both presentations are recognised by their unit being
invertible at the K-injective complexes, where `AlgebraicGeometry.Space.derivedModulePushforward`
is a right derived functor along `DerivedCategory.Qh`. -/
instance derivedModulePushforward_isRightDerivedFunctor (f : X ⟶ Y) :
    (derivedModulePushforward B S hS f).IsRightDerivedFunctor
      (derivedModulePushforwardComplexUnit B S hS f)
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
  letI := isGrothendieckAbelian_modules B S hS X.1 X.2
  Stacks.Injectives.isRightDerivedFunctor_complexUnit (modulePushforward B S hS f)
    (derivedModulePushforward B S hS f) (derivedModulePushforwardUnit B S hS f)

/-- The direct image on quasi-coherent modules, applied termwise and followed by the localization,
has a total right derived functor on the whole homotopy category: `QCoh(𝒪_X)` is Grothendieck
abelian (Stacks 077V (1)), so every cochain complex has a K-injective resolution (Stacks 079P). -/
instance quasicoherentPushforward_hasRightDerivedFunctor (f : X ⟶ Y)
    (hpush : PushforwardPreservesQuasicoherence B S hS f) :
    ((quasicoherentPushforward B S hS f hpush).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
        (ComplexShape.up ℤ)) :=
  letI : IsGrothendieckAbelian.{u} (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) :=
    quasicoherentSheaves_isGrothendieckAbelian B S hS X.1 X.2
  hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (A := QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2) (quasicoherentPushforward B S hS f hpush)

/-- **The functor `Φ : D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))` of Stacks 08GZ**: the total right derived
functor of the direct image `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`, for a morphism whose direct image
preserves quasi-coherence. -/
def derivedQuasicoherentPushforward (f : X ⟶ Y)
    (hpush : PushforwardPreservesQuasicoherence B S hS f) :
    DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2) :=
  ((quasicoherentPushforward B S hS f hpush).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q).totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
        (ComplexShape.up ℤ))

/-- The derivation unit of `Φ`: the comparison from the termwise direct image to `Φ`. -/
def derivedQuasicoherentPushforwardUnit (f : X ⟶ Y)
    (hpush : PushforwardPreservesQuasicoherence B S hS f) :
    (quasicoherentPushforward B S hS f hpush).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2) ⟶
      DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⋙
        derivedQuasicoherentPushforward B S hS f hpush :=
  ((quasicoherentPushforward B S hS f hpush).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
      (HomologicalComplex.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
        (ComplexShape.up ℤ))

/-- The derivation unit exhibits `Φ` as a right derived functor of the direct image on
quasi-coherent modules. -/
instance derivedQuasicoherentPushforward_isRightDerivedFunctor (f : X ⟶ Y)
    (hpush : PushforwardPreservesQuasicoherence B S hS f) :
    (derivedQuasicoherentPushforward B S hS f hpush).IsRightDerivedFunctor
      (derivedQuasicoherentPushforwardUnit B S hS f hpush)
      (HomologicalComplex.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    ((((quasicoherentPushforward B S hS f hpush).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerived DerivedCategory.Q
        (HomologicalComplex.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
          (ComplexShape.up ℤ))).IsRightDerivedFunctor
      (((quasicoherentPushforward B S hS f hpush).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
          (HomologicalComplex.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
            (ComplexShape.up ℤ))) _)

/-- **The derived coherator commutes with the direct image along a flat morphism.**  Let
`f : X ⟶ Y` be a quasi-compact, quasi-separated and flat morphism of algebraic spaces over `S`,
and let `Φ : D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))` be the right derived functor of
`f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`.  Then `RQ_Y ∘ Rf_* = Φ ∘ RQ_X`, as a natural isomorphism
`Rf_* ⋙ RQ_Y ≅ RQ_X ⋙ Φ`.

Here `Rf_*` is `AlgebraicGeometry.Space.derivedModulePushforward`, `RQ_X` and `RQ_Y` are
`AlgebraicGeometry.Space.derivedCoherator`, and `Φ` is
`AlgebraicGeometry.Space.derivedQuasicoherentPushforward` at the preservation of quasi-coherence of
Stacks 03M9. -/
@[stacks 08GZ "RQ_Y ∘ Rf_* = Φ ∘ RQ_X for a flat, quasi-compact, quasi-separated morphism"]
def derivedModulePushforwardCompDerivedCoheratorIso (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) :
    derivedModulePushforward B S hS f ⋙ derivedCoherator B S hS Y.1 Y.2 ≅
      derivedCoherator B S hS X.1 X.2 ⋙ derivedQuasicoherentPushforward B S hS f
        (pushforwardPreservesQuasicoherence_of_qcqs B S hS f hfqc hfqs) :=
  flatPushforwardDerivedCoheratorIsoOfQcqs B S hS f hfqc hfqs hflat DerivedCategory.Q
    DerivedCategory.Q (coherator B S hS X.1 X.2) (coheratorAdjunction B S hS X.1 X.2)
    (coherator B S hS Y.1 Y.2) (coheratorAdjunction B S hS Y.1 Y.2)
    (derivedModulePushforward B S hS f) (derivedModulePushforwardComplexUnit B S hS f)
    (derivedCoherator B S hS X.1 X.2) (derivedCoheratorUnit B S hS X.1 X.2)
    (derivedCoherator B S hS Y.1 Y.2) (derivedCoheratorUnit B S hS Y.1 Y.2)
    (derivedQuasicoherentPushforward B S hS f _) (derivedQuasicoherentPushforwardUnit B S hS f _)

end Concrete

end AlgebraicGeometry.Space

end
