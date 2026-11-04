module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectiveQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.Homology.Injectives.DerivedCategory.ArbitraryModel

/-!
# The coherator and the flat direct image on an algebraic space

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and flat morphism of algebraic spaces over a
scheme `S` contained in a big fppf site `B`.  The direct image preserves quasi-coherence, so it
restricts to `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`, whose total right derived functor is written `Φ`;
and the inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` has a right adjoint, the coherator `Q_X`, whose
total right derived functor is written `RQ_X`.  [Stacks, Tag 08GZ] identifies the two composites
of derived functors: `RQ_Y ∘ Rf_* = Φ ∘ RQ_X`.

The proof is the source's.  Both composites are right adjoint to the same functor
`D(QCoh(𝒪_Y)) ⥤ D(𝒪_X)`.  Flatness makes the inverse image exact, so it induces functors of
derived categories with no derivation, both on all modules and on the quasi-coherent ones, and
these are left adjoint to `Rf_*` and to `Φ` respectively by [Stacks, Tag 09T5]; the inclusions of
the quasi-coherent modules are exact for the same formal reason and are left adjoint to `RQ_X`
and `RQ_Y`.  The two composite left adjoints agree because `f^* ∘ ι = ι ∘ f^*` already at the
level of modules, and a right adjoint is unique up to a canonical isomorphism.

## Main results

* `AlgebraicGeometry.Space.flatPushforwardDerivedCoheratorIso` — **Stacks 08GZ**: the natural
  isomorphism `Rf_* ⋙ RQ_Y ≅ RQ_X ⋙ Φ`.
* `AlgebraicGeometry.Space.flatPushforwardDerivedCoheratorIsoOfForallAffine` — the same in the
  binders of the source statement, with quasi-compactness and quasi-separatedness of `f` in place
  of the preservation of quasi-coherence that they are there to supply.

## Supporting results

* `AlgebraicGeometry.Space.preservesFiniteLimits_quasicoherentSheavesι` and
  `AlgebraicGeometry.Space.preservesFiniteColimits_quasicoherentSheavesι`: the inclusion of the
  quasi-coherent modules on an algebraic space is exact.
* `AlgebraicGeometry.Space.preservesFiniteLimits_quasicoherentPullback_of_isFlat` and
  `AlgebraicGeometry.Space.preservesFiniteColimits_quasicoherentPullback_smallEtale`: exactness
  of the inverse image on quasi-coherent modules along a flat morphism.

## What is assumed

Beyond the source's flatness, quasi-compactness and quasi-separatedness, three inputs are carried
as hypotheses, each named in the attribute that carries it.  They are the same three that
`AlgebraicGeometry.Space.injective_quasicoherentPushforward_obj` carries for the neighbouring
Stacks 09TK, and none of them is a restatement of the conclusion.

* **Stacks 03M9**, that the direct image preserves quasi-coherence, as
  `AlgebraicGeometry.Space.PushforwardPreservesQuasicoherence`.  In this development it is
  reduced to the exact sequence of Stacks 03M8 over the affine charts of the target by
  `AlgebraicGeometry.Space.pushforward_isQuasicoherentOnSite_of_chartwiseKernel`, and
  `flatPushforwardDerivedCoheratorIsoOfForallAffine` trades it for the affine-base case in the
  source's own binders.
* **Stacks 03GA**, that the inverse image preserves quasi-coherence, as
  `AlgebraicGeometry.Space.HasLocalInverseImagePresentations`, which is the inverse-image factor
  of Stacks 03DO left open by
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback`.
* **Stacks 077V, part (1)**, that `QCoh(𝒪_X)` is Grothendieck abelian, as the instance binder
  `CategoryTheory.IsGrothendieckAbelian`.  This is what [Stacks, Tag 09T5] needs in order to
  produce the adjunction `f^* ⊣ Φ` on the quasi-coherent side; the two adjunctions involving
  `RQ_X` and `RQ_Y` instead need it for `Mod(𝒪_X)` and `Mod(𝒪_Y)`, where it is the
  unconditional `AlgebraicGeometry.Space.isGrothendieckAbelian_modules`.  Stacks 077V obtains it
  for `QCoh(𝒪_X)` from a separator, through Stacks 03M3 and 077U.

Flatness enters in the ringed-topos form `(smallEtaleRingedToposHom B S hS f).IsFlat`, which is
the form in which Stacks 04JC delivers exactness of the inverse image and the form that
`AlgebraicGeometry.Space.preservesFiniteLimits_modulePullback_of_isFlat` consumes.

## Implementation notes

The derived categories are instance arguments and the four total right derived functors are
hypotheses: each is an arbitrary functor equipped with its derivation unit relative to an
arbitrary chosen localization of the cochain complexes of quasi-coherent modules.  So the
statement says nothing about any particular model of `D(QCoh(𝒪_X))` nor about any particular
choice of K-injective resolutions, and the source's equality of functors becomes a natural
isomorphism.  For the same reason the two coherators are hypotheses as well: the source says
"the right adjoint of the inclusion", which is determined only up to a canonical isomorphism, and
Stacks 077V, part (2) is what makes the hypothesis satisfiable.  Their additivity is an instance
binder rather than a `letI`, which adds nothing: it is `Adjunction.right_adjoint_additive` of the
coherator adjunction, so every instantiation of the two adjunctions supplies it.

The module universe is the universe `u` of the schemes and not a free one, because
`AlgebraicGeometry.Space.modulePushforward` and `AlgebraicGeometry.Space.modulePullback` exist
only at that universe; the module categories themselves have their objects in `Type (u + 1)`, so
the two derived-category universes `w` and `w'` are free and in particular may be taken to be
`u + 1`, which is where `AlgebraicGeometry.Space.hasRightDerivedFunctor_modulePushforward`
exhibits an `Rf_*`.

The modules on an algebraic space are spelled `AlgebraicGeometry.Space.Modules`, which is
`SheafOfModules` of the structure ring sheaf of the small étale ringed site; there is no
`Scheme.Modules`-style second spelling on the spaces side, so no ascription of the kind
`AlgebraicGeometry.quasicoherentModulesι` performs is needed here.

`Stacks.DerivedModel.adjunctionOfExact` is the one input doing real work: it produces the
adjunction between the functor induced by an exact left adjoint and the total right derived
functor of its right adjoint, at arbitrary chosen models.  Everything else is bookkeeping, with
one genuine step — the commutation of the inverse image with the inclusion of the quasi-coherent
modules, which holds by construction of `AlgebraicGeometry.Space.quasicoherentPullback`.

## References

* [Stacks Project, Tag 08GZ](https://stacks.math.columbia.edu/tag/08GZ)
* [Stacks Project, Tag 08D8](https://stacks.math.columbia.edu/tag/08D8)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inclusion of the quasi-coherent modules -/

/-- The inclusion `ι : QCoh(𝒪_Z) ⥤ Mod(𝒪_Z)` of the quasi-coherent modules on an algebraic
space into all modules on its small étale ringed site. -/
noncomputable abbrev quasicoherentSheavesι (Z : AlgebraicSpaces B S hS) :
    QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2 :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))).ι

/-- **The cokernel clause of Stacks 03M1, part (3), for an algebraic space, unconditionally**:
quasi-coherence of `𝒪_Z`-modules is closed under cokernels.

This is `AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`, which carries no
hypothesis; registering it as an instance is what lets the abelian structure on `QCoh(𝒪_Z)` be
an instance too. -/
instance isClosedUnderCokernels_quasicoherentSheaves_algebraicSpace
    (Z : AlgebraicSpaces B S hS) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))).IsClosedUnderCokernels :=
  isClosedUnderCokernels_quasicoherentSheaves B S hS Z.1 Z.2

/-- **Stacks 077V, part (1), abelian structure, unconditionally on an algebraic space.**  The
quasi-coherent `𝒪_Z`-modules form an abelian category.

This is `AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure` with its three closure
hypotheses discharged: under kernels by
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_algebraicSpace`, under
cokernels by
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves_algebraicSpace`, and under
finite products by `SheafOfModules.isQuasicoherentOnSite_isClosedUnderFiniteProducts`. -/
noncomputable instance abelian_quasicoherentSheaves_algebraicSpace
    (Z : AlgebraicSpaces B S hS) :
    Abelian (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) :=
  quasicoherentSheaves_abelian_of_closure B S hS Z.1 Z.2

/-- **The inclusion of the quasi-coherent modules on an algebraic space is left exact.**
Quasi-coherence is closed under kernels, so the inclusion creates them, and a functor between
preadditive categories preserving kernels preserves all finite limits. -/
instance preservesFiniteLimits_quasicoherentSheavesι (Z : AlgebraicSpaces B S hS) :
    PreservesFiniteLimits (quasicoherentSheavesι B S hS Z) :=
  SheafOfModules.preservesFiniteLimits_ι_isQuasicoherentOnSite _

/-- **The inclusion of the quasi-coherent modules on an algebraic space is right exact.**
Quasi-coherence is closed under cokernels, so the inclusion creates them, and a functor between
preadditive categories preserving cokernels preserves all finite colimits. -/
instance preservesFiniteColimits_quasicoherentSheavesι (Z : AlgebraicSpaces B S hS) :
    PreservesFiniteColimits (quasicoherentSheavesι B S hS Z) :=
  have : ∀ ⦃A C : QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2⦄ (a : A ⟶ C),
      PreservesColimit (parallelPair a 0) (quasicoherentSheavesι B S hS Z) :=
    fun {_ _} a ↦ ObjectProperty.preservesCokernels_ι _ a
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-! ### Exactness of the inverse image -/

variable {X Y : AlgebraicSpaces B S hS}

/-- The inverse image of `𝒪`-modules along a morphism of algebraic spaces is right exact, being
a left adjoint. -/
theorem preservesFiniteColimits_modulePullback_smallEtale (f : X ⟶ Y) :
    PreservesFiniteColimits (modulePullback B S hS f) :=
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS f) :=
    (modulePullbackAdjunction B S hS f).leftAdjoint_preservesColimits
  inferInstance

/-- The inverse image on quasi-coherent modules is additive, being a left adjoint between
additive categories. -/
instance quasicoherentPullback_additive (f : X ⟶ Y)
    (hpull : HasLocalInverseImagePresentations B S hS f) :
    (quasicoherentPullback B S hS f hpull).Additive :=
  have : (quasicoherentPullback B S hS f hpull ⋙ quasicoherentSheavesι B S hS X).Additive :=
    Functor.additive_of_iso
      (F := quasicoherentSheavesι B S hS Y ⋙ modulePullback B S hS f)
      (ObjectProperty.liftCompιIso _ _ _).symm
  Functor.additive_of_comp_faithful _ (quasicoherentSheavesι B S hS X)

/-- The direct image on quasi-coherent modules is additive, being the corestriction of the
additive direct image of all modules. -/
instance quasicoherentPushforward_additive (f : X ⟶ Y)
    (hpush : PushforwardPreservesQuasicoherence B S hS f) :
    (quasicoherentPushforward B S hS f hpush).Additive :=
  have : (quasicoherentPushforward B S hS f hpush ⋙ quasicoherentSheavesι B S hS Y).Additive :=
    Functor.additive_of_iso
      (F := quasicoherentSheavesι B S hS X ⋙ modulePushforward B S hS f)
      (ObjectProperty.liftCompιIso _ _ _).symm
  Functor.additive_of_comp_faithful _ (quasicoherentSheavesι B S hS Y)

/-- **The inverse image on quasi-coherent modules along a flat morphism is left exact.**  The
inclusion of the quasi-coherent modules is exact and reflects isomorphisms, so left exactness is
inherited from the inverse image of all modules, which is left exact by Stacks 04JC. -/
theorem preservesFiniteLimits_quasicoherentPullback_of_isFlat (f : X ⟶ Y)
    (hpull : HasLocalInverseImagePresentations B S hS f)
    (hflat : (smallEtaleRingedToposHom B S hS f).IsFlat) :
    PreservesFiniteLimits (quasicoherentPullback B S hS f hpull) := by
  have := preservesFiniteLimits_modulePullback_of_isFlat B S hS f hflat
  have : PreservesFiniteLimits
      (quasicoherentPullback B S hS f hpull ⋙ quasicoherentSheavesι B S hS X) :=
    preservesFiniteLimits_of_natIso (ObjectProperty.liftCompιIso _ _ _).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (quasicoherentSheavesι B S hS X)

/-- **The inverse image on quasi-coherent modules is right exact.**  The inclusion of the
quasi-coherent modules is exact and reflects isomorphisms, so right exactness is inherited from
the inverse image of all modules, which is right exact unconditionally. -/
theorem preservesFiniteColimits_quasicoherentPullback_smallEtale (f : X ⟶ Y)
    (hpull : HasLocalInverseImagePresentations B S hS f) :
    PreservesFiniteColimits (quasicoherentPullback B S hS f hpull) := by
  have := preservesFiniteColimits_modulePullback_smallEtale B S hS f
  have : PreservesFiniteColimits
      (quasicoherentPullback B S hS f hpull ⋙ quasicoherentSheavesι B S hS X) :=
    preservesFiniteColimits_of_natIso (ObjectProperty.liftCompιIso _ _ _).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ (quasicoherentSheavesι B S hS X)

/-! ### The comparison of Stacks 08GZ -/

section

variable (f : X ⟶ Y) (hflat : (smallEtaleRingedToposHom B S hS f).IsFlat)
  (hpull : HasLocalInverseImagePresentations B S hS f)
  [HasDerivedCategory.{w} (Modules.{u, u} B S hS X.1 X.2)]
  [HasDerivedCategory.{w} (Modules.{u, u} B S hS Y.1 Y.2)]
  [HasDerivedCategory.{w'} (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)]
  [HasDerivedCategory.{w'} (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2)]
  [IsGrothendieckAbelian.{u} (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)]
  (QX : CochainComplex (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ℤ ⥤
    DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2))
  [QX.IsLocalization (HomologicalComplex.quasiIso
    (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
  (QY : CochainComplex (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2) ℤ ⥤
    DerivedCategory (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2))
  [QY.IsLocalization (HomologicalComplex.quasiIso
    (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]
  (CX : Modules.{u, u} B S hS X.1 X.2 ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
  (adjX : quasicoherentSheavesι B S hS X ⊣ CX) [CX.Additive]
  (CY : Modules.{u, u} B S hS Y.1 Y.2 ⥤ QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2)
  (adjY : quasicoherentSheavesι B S hS Y ⊣ CY) [CY.Additive]
  (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
  (RfUnit : (modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := Modules.{u, u} B S hS Y.1 Y.2) ⟶
    DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2) ⋙ Rf)
  [Rf.IsRightDerivedFunctor RfUnit
    (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
  (RQX : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
    DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2))
  (RQXUnit : CX.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QX ⟶
    DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2) ⋙ RQX)
  [RQX.IsRightDerivedFunctor RQXUnit
    (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
  (RQY : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
    DerivedCategory (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2))
  (RQYUnit : CY.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QY ⟶
    DerivedCategory.Q (C := Modules.{u, u} B S hS Y.1 Y.2) ⋙ RQY)
  [RQY.IsRightDerivedFunctor RQYUnit
    (HomologicalComplex.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]

/-- **Stacks Project, Tag 08GZ.**  Let `f : X ⟶ Y` be a flat morphism of algebraic spaces whose
direct image and inverse image preserve quasi-coherence.  Let `Rf_*` be a total right derived
functor of the direct image of all modules, let `RQ_X`, `RQ_Y` be total right derived functors of
coherators of `X` and `Y`, and let `Φ` be a total right derived functor of the direct image
restricted to quasi-coherent modules.  Then `Rf_* ⋙ RQ_Y ≅ RQ_X ⋙ Φ`.

Both sides are right adjoint to the same functor `D(QCoh(𝒪_Y)) ⥤ D(𝒪_X)`: flatness makes the
inverse image exact, on all modules and on quasi-coherent modules alike, so it induces functors
of derived categories with no derivation, and these compose to one functor in two ways which
agree because the inverse image commutes with the inclusion of the quasi-coherent modules
already before deriving. -/
@[stacks 08GZ "granted Stacks 03M9 that the direct image preserves quasi-coherence, Stacks \
03GA that the inverse image does, Stacks 077V part (1) that QCoh(𝒪_X) is Grothendieck abelian, \
and flatness in the ringed-topos form of Stacks 04JC"]
noncomputable def flatPushforwardDerivedCoheratorIso
    (hpush : PushforwardPreservesQuasicoherence B S hS f)
    (Φ : DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2))
    (ΦUnit : (quasicoherentPushforward B S hS f hpush).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ QY ⟶ QX ⋙ Φ)
    [Φ.IsRightDerivedFunctor ΦUnit (HomologicalComplex.quasiIso
      (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] :
    Rf ⋙ RQY ≅ RQX ⋙ Φ := by
  have : PreservesFiniteLimits (modulePullback B S hS f) :=
    preservesFiniteLimits_modulePullback_of_isFlat B S hS f hflat
  have : PreservesFiniteColimits (modulePullback B S hS f) :=
    preservesFiniteColimits_modulePullback_smallEtale B S hS f
  have : PreservesFiniteLimits (quasicoherentPullback B S hS f hpull) :=
    preservesFiniteLimits_quasicoherentPullback_of_isFlat B S hS f hpull hflat
  have : PreservesFiniteColimits (quasicoherentPullback B S hS f hpull) :=
    preservesFiniteColimits_quasicoherentPullback_smallEtale B S hS f hpull
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
    isGrothendieckAbelian_modules B S hS X.1 X.2
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS Y.1 Y.2) :=
    isGrothendieckAbelian_modules B S hS Y.1 Y.2
  let adjRQX := Stacks.DerivedModel.adjunctionOfExact (quasicoherentSheavesι B S hS X)
    (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)) QX adjX RQX RQXUnit
  let adjRQY := Stacks.DerivedModel.adjunctionOfExact (quasicoherentSheavesι B S hS Y)
    (DerivedCategory.Q (C := Modules.{u, u} B S hS Y.1 Y.2)) QY adjY RQY RQYUnit
  let adjRf := Stacks.DerivedModel.adjunctionOfExact (modulePullback B S hS f)
    (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2))
    (DerivedCategory.Q (C := Modules.{u, u} B S hS Y.1 Y.2))
    (modulePullbackAdjunction B S hS f) Rf RfUnit
  let adjPhi := Stacks.DerivedModel.adjunctionOfExact (quasicoherentPullback B S hS f hpull)
    QX QY (quasicoherentPullbackAdjunction B S hS f hpull hpush) Φ ΦUnit
  let c := ComplexShape.up ℤ
  let QtY := Stacks.DerivedModel.homotopyLocalization QY
  let QtXall := Stacks.DerivedModel.homotopyLocalization
    (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2))
  let LincY := Stacks.DerivedModel.derivedFunctorOfExact (quasicoherentSheavesι B S hS Y)
    (DerivedCategory.Q (C := Modules.{u, u} B S hS Y.1 Y.2)) QY
  let Lpb := Stacks.DerivedModel.derivedFunctorOfExact (modulePullback B S hS f)
    (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2))
    (DerivedCategory.Q (C := Modules.{u, u} B S hS Y.1 Y.2))
  let LqcPB := Stacks.DerivedModel.derivedFunctorOfExact
    (quasicoherentPullback B S hS f hpull) QX QY
  let LincX := Stacks.DerivedModel.derivedFunctorOfExact (quasicoherentSheavesι B S hS X)
    (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)) QX
  let eIncY := Stacks.DerivedModel.derivedFunctorOfExactFac (quasicoherentSheavesι B S hS Y)
    (DerivedCategory.Q (C := Modules.{u, u} B S hS Y.1 Y.2)) QY
  let ePB := Stacks.DerivedModel.derivedFunctorOfExactFac (modulePullback B S hS f)
    (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2))
    (DerivedCategory.Q (C := Modules.{u, u} B S hS Y.1 Y.2))
  let eQcPB := Stacks.DerivedModel.derivedFunctorOfExactFac
    (quasicoherentPullback B S hS f hpull) QX QY
  let eIncX := Stacks.DerivedModel.derivedFunctorOfExactFac (quasicoherentSheavesι B S hS X)
    (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)) QX
  let L1 := LincY ⋙ Lpb
  let L2 := LqcPB ⋙ LincX
  let H1 := ((quasicoherentSheavesι B S hS Y).mapHomotopyCategory c ⋙
    (modulePullback B S hS f).mapHomotopyCategory c) ⋙ QtXall
  let H2 := ((quasicoherentPullback B S hS f hpull).mapHomotopyCategory c ⋙
    (quasicoherentSheavesι B S hS X).mapHomotopyCategory c) ⋙ QtXall
  let h1 : QtY ⋙ L1 ≅ H1 :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eIncY Lpb ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ePB ≪≫
      (Functor.associator _ _ _).symm
  let h2 : QtY ⋙ L2 ≅ H2 :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eQcPB LincX ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ eIncX ≪≫
      (Functor.associator _ _ _).symm
  let eBase : H2 ≅ H1 :=
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
      (ObjectProperty.liftCompιIso _ _ _) c) QtXall ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (quasicoherentSheavesι B S hS Y ⋙ modulePullback B S hS f)) c).symm QtXall
  let W := HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2) c
  letI : Localization.Lifting QtY W H1 L1 := ⟨h1⟩
  letI : Localization.Lifting QtY W H2 L2 := ⟨h2⟩
  let eLeft : L2 ≅ L1 := Localization.liftNatIso QtY W H2 H1 L2 L1 eBase
  exact (adjRQY.comp adjRf).rightAdjointUniq ((adjPhi.comp adjRQX).ofNatIsoLeft eLeft)

/-- **Stacks Project, Tag 08GZ, in the binders of the source statement.**  Let `f : X ⟶ Y` be a
quasi-compact, quasi-separated and flat morphism of algebraic spaces whose inverse image
preserves quasi-coherence.  With `Rf_*`, `RQ_X`, `RQ_Y` and `Φ` as above,
`Rf_* ⋙ RQ_Y ≅ RQ_X ⋙ Φ`.

Quasi-compactness and quasi-separatedness enter exactly where the source puts them: they are what
makes the direct image preserve quasi-coherence, by the reduction of Stacks 03M9 whose residual
affine-base case is `haffine`. -/
@[stacks 08GZ "in the binders of the source statement, granted the affine-base case of the \
preservation of quasi-coherence by the direct image, Stacks 03GA that the inverse image \
preserves quasi-coherence, Stacks 077V part (1) that QCoh(𝒪_X) is Grothendieck abelian, and \
flatness in the ringed-topos form of Stacks 04JC"]
noncomputable def flatPushforwardDerivedCoheratorIsoOfForallAffine
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (haffine : ∀ F : Modules.{u, u} B S hS X.1 X.2, F.IsQuasicoherentOnSite →
      ∀ V : SmallEtale B S hS Y.1,
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) →
        IsQuasiCompact B S hS (chartBaseChangeProjection B S hS f V).hom →
        IsQuasiSeparated B S hS (chartBaseChangeProjection B S hS f V).hom →
        ((chartLocalizedModulePushforward B S hS f V).obj
          ((moduleChartBaseChangeRestriction B S hS f V).obj F)).IsQuasicoherentOnSite)
    (Φ : DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2))
    (ΦUnit : (quasicoherentPushforward B S hS f
        (pushforwardPreservesQuasicoherence_of_forall_affine B S hS f hfqc hfqs
          haffine)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QY ⟶ QX ⋙ Φ)
    [Φ.IsRightDerivedFunctor ΦUnit (HomologicalComplex.quasiIso
      (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] :
    Rf ⋙ RQY ≅ RQX ⋙ Φ :=
  flatPushforwardDerivedCoheratorIso B S hS f hflat hpull QX QY CX adjX CY adjY Rf RfUnit
    RQX RQXUnit RQY RQYUnit _ Φ ΦUnit

end

end AlgebraicGeometry.Space

end
