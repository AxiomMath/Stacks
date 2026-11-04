module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonAffineBase

/-!
# Conclusion (b) of Tag 0EX3 over an affine base

`TensorComparisonAffineBase.lean` reads the two functors of conclusion (b) of
[Stacks, Tag 0EX3] as endofunctors of `ModuleCat Γ(Y', ⊤)` and verifies for each the three
hypotheses of the Eilenberg-Watts rigidity criterion.  This file supplies the two remaining
inputs and draws the conclusion.

What rigidity is applied to is **any** natural transformation of those two functors of the
module on the base: composing with the associated-module functor of the affine base and with
global sections gives a natural transformation of the two endofunctors above, and if it is
invertible at the structure sheaf of the base then it is invertible at the base ring, because
there the associated module *is* the structure sheaf.  Rigidity then makes it invertible at
every module, and since every quasi-coherent module on an affine scheme is an associated
module, it is invertible at every quasi-coherent module.

Conclusion (b) over an affine base is that statement at the canonical map
`higherDirectImageTensorNatTrans`, whose value at the structure sheaf is invertible
unconditionally (`isIso_higherDirectImageTensorMap_unitModule`).  The generality is what joins
the affine case to an arbitrary base: over an affine open of an arbitrary base the
transformation one has is not the canonical map of a situation but the restriction of the
canonical map of the ambient one, conjugated by the two squares of
`TensorComparisonRestrictSquares.lean` and descended along the restriction adjunction.

## Main definitions

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `baseTilde`: `M ↦ M~` on the affine base of a situation.
* `affineNatTrans`: a transformation of the two functors of conclusion (b), read on modules over
  the base ring.

## Main results

* `affineTargetIso`: the sections of `R^d f'_*(F' ⊗ (f')^* M~)` are the cohomology
  `H^d(X', F' ⊗ (f')^* M~)`, naturally in `M` — [Stacks, Tag 01XK] over the affine base.
* `baseTildeObjSelfIso`: the associated module of the base ring is the structure sheaf.
* `baseTildeObjIso`: every quasi-coherent module on the affine base is an associated module.
* `isIso_affineNatTrans_app`: **a transformation of the two functors of conclusion (b), read on
  modules over the base ring, is invertible at every module** as soon as it is invertible at the
  structure sheaf of the base — Eilenberg-Watts rigidity.
* `isIso_app_of_isAffine_base`: **the same, back on the modules of the affine base**: a
  transformation of the two functors invertible at the structure sheaf is invertible at every
  quasi-coherent module.
* `isIso_higherDirectImageTensorMap_of_isAffine_base`: **conclusion (b) of [Stacks, Tag 0EX3]
  over an affine base**, for the base-changed morphism of a situation in its degree `d`.

## Implementation notes

*Where the two indexings of the right derived functors meet.* [Stacks, Tag 01XK] is stated at
`CategoryTheory.Functor.rightDerivedPlus`, the `ℤ`-indexed model, which is the one the canonical
map of conclusion (b) is built at; the Eilenberg-Watts hypotheses are stated at
`CategoryTheory.Functor.rightDerived`, the `ℕ`-indexed one, which is the only indexing in which
`CategoryTheory.ShortComplex.map` is available.  `Stacks.DerivedIndexing.rightDerivedIso` crosses
them, as an isomorphism of functors and not objectwise, so it is whiskered into the comparison
rather than applied at a module.

*Why `StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineReconstruction` is not imported.* It
would supply `AlgebraicGeometry.affineQuasicoherentModulesEquiv`, which exhibits every
quasi-coherent module on an affine scheme as an associated module in one step.  Importing it
however brings a second instance of `CategoryTheory.HasDerivedCategory` for categories of
sheaves of modules into scope, and instance search then resolves the derived pushforward of this
file to a different functor from the one the canonical map of conclusion (b) is built at: the two
differ only by that instance, and reconciling them needs to unfold `Shrink`, whose definition the
module system does not expose.  So the comparison is assembled here from
`Stacks.Coherent.affineTilde` and the full faithfulness of global sections instead, which costs
two declarations and keeps the derived pushforward the one every other statement is about.

## Where the affineness of the base goes

`TensorComparisonBase.lean` removes it.  Invertibility of a morphism of quasi-coherent modules
is local on the base (`isIso_higherDirectImageTensorMap_of_isIso_restrict`,
`isIso_higherDirectImageTensorMap_of_bijective_app`), the affine opens cover any base, and a
situation restricts to one with affine base over an affine open
(`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.restrictBase` together with
`isAffine_restrictBase_Y'`).  What joins the two is that the two functors of conclusion (b)
**commute with restriction to an open of the base**, as natural isomorphisms

`G ↦ (R^d f'_* F' ⊗ G)|_V  ≅  G ↦ R^d (f' ∣_V)_* (F'|) ⊗ G|_V`

and

`G ↦ (R^d f'_*(F' ⊗ (f')^* G))|_V  ≅  G ↦ R^d (f' ∣_V)_*(F'| ⊗ (f' ∣_V)^* G|_V)`,

which are `sourceRestrictIso` and `targetRestrictIso` of
`TensorComparisonRestrictSquares.lean`; the cohomological half of each is
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictIso`
([Stacks, Tag 01E5]).

Conjugating the restricted canonical map by those two gives a transformation of the two functors
of the restricted situation precomposed with restriction, and
`CategoryTheory.Adjunction.descend` turns it into one of those functors themselves — restriction
is a left adjoint with invertible counit — with its component at `G|_V` the conjugated map at
`G` on the nose.  That descent is invertible at the structure sheaf of `V`, since the
restriction of the structure sheaf of the base is the structure sheaf of `V` and the canonical
map at the structure sheaf is invertible with no hypothesis at all.  So
`isIso_app_of_isAffine_base` above, which asks nothing of the transformation beyond that, inverts
it at every quasi-coherent module of `V`, `G|_V` included; locality finishes.  The result is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_higherDirectImageTensorMap`, which carries
`@[stacks 0EX3 "(b)"]`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Coherent
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable (S : TopDegreeBaseChangeSituation.{u}) [IsAffine S.Y'] (F' : S.X'.Modules)
  [F'.IsQuasicoherent]

/-! ### The associated-module functor of the affine base -/

/-- **`M ↦ M~` on the affine base of a situation**: the associated module on
`Spec Γ(Y', ⊤)`, pulled back along `Y' ≅ Spec Γ(Y', ⊤)`.  These are the two leading factors of
the geometric factor. -/
abbrev baseTilde : ModuleCat.{u} Γ(S.Y', ⊤) ⥤ S.Y'.Modules :=
  tildeFactor Γ(S.Y', ⊤) ⋙ pullbackFactor Γ(S.Y', ⊤) (baseOver S)

/-- **The associated module of the base ring is the structure sheaf of the base.** -/
def baseTildeObjSelfIso :
    (baseTilde S).obj (ModuleCat.of Γ(S.Y', ⊤) Γ(S.Y', ⊤)) ≅ Scheme.unitModule S.Y' :=
  (Scheme.Modules.pullback S.Y'.isoSpec.hom).mapIso
      (AlgebraicGeometry.tildeSelf (R := CommRingCat.of Γ(S.Y', ⊤))) ≪≫
    Scheme.Modules.pullbackUnitIso S.Y'.isoSpec.hom

/-- The two shapes of the associated-module functor of an affine scheme agree: restriction along
`Y' ≅ Spec Γ(Y', ⊤)` is inverse image along it. -/
def affineTildeIsoBaseTilde : affineTilde S.Y' ≅ baseTilde S :=
  Functor.isoWhiskerLeft (AlgebraicGeometry.tilde.functor (CommRingCat.of Γ(S.Y', ⊤)))
    (Scheme.Modules.restrictFunctorIsoPullback S.Y'.isoSpec.hom)

/-- **Every quasi-coherent module on the affine base is the associated module of its global
sections**, by [Stacks, Tag 01I7]: global sections is fully faithful on the quasi-coherent
modules, and the global sections of an associated module are the module one started from. -/
def affineTildeObjIso (G : S.Y'.Modules) [G.IsQuasicoherent] :
    (affineTilde S.Y').obj ((moduleGlobalSections S.Y').obj G) ≅ G :=
  (ObjectProperty.ι (SheafOfModules.isQuasicoherent S.Y'.ringCatSheaf)).mapIso
    ((affineQuasicoherentSectionsFullyFaithful S.Y').preimageIso
      (X := ⟨(affineTilde S.Y').obj ((moduleGlobalSections S.Y').obj G),
        affineTilde_quasicoherent S.Y' ((moduleGlobalSections S.Y').obj G)⟩)
      (Y := ⟨G, inferInstance⟩)
      (affineTildeSectionsIso S.Y' ((moduleGlobalSections S.Y').obj G)).symm)

/-- **Every quasi-coherent module on the affine base is an associated module**, in the shape the
Eilenberg-Watts hypotheses are stated at. -/
def baseTildeObjIso (G : S.Y'.Modules) [G.IsQuasicoherent] :
    (baseTilde S).obj ((moduleGlobalSections S.Y').obj G) ≅ G :=
  ((affineTildeIsoBaseTilde S).app ((moduleGlobalSections S.Y').obj G)).symm ≪≫
    affineTildeObjIso S G

/-! ### A transformation of the two functors, read on modules over the base ring -/

variable (τ : topDirectImageTensorLeftFunctor S.f' F' S.d ⟶
  topDirectImageTensorFunctor S.f' F' S.d)

/-- **A transformation of the two functors of conclusion (b) of [Stacks, Tag 0EX3], read on
modules over the ring of the affine base.**  Over an affine base every quasi-coherent module is
an associated module `M~`, so a transformation of the two functors of the conclusion restricts
along `M ↦ M~` and takes global sections to a transformation of endofunctors of
`Γ(Y', ⊤)`-modules; that is the shape the Eilenberg-Watts rigidity criterion consumes. -/
def affineNatTrans : affineSourceFunctor S F' ⟶
    baseTilde S ⋙ topDirectImageTensorFunctor S.f' F' S.d ⋙ moduleGlobalSections S.Y' :=
  Functor.whiskerRight (Functor.whiskerLeft (baseTilde S) τ) (moduleGlobalSections S.Y')

/-- The component of the transformation on modules over the base ring. -/
theorem affineNatTrans_app (M : ModuleCat.{u} Γ(S.Y', ⊤)) :
    (affineNatTrans S F' τ).app M =
      (moduleGlobalSections S.Y').map (τ.app ((baseTilde S).obj M)) := rfl

/-! ### The target, computed -/

/-- Pulling back along `Y' ≅ Spec Γ(Y', ⊤)` and then along `f'` is pulling back along the
composite, which is the structure morphism of `X'` over the spectrum of the base ring. -/
def baseTildePullbackIso :
    baseTilde S ⋙ Scheme.Modules.pullback S.f' ≅
      tildeFactor Γ(S.Y', ⊤) ⋙ pullbackFactor Γ(S.Y', ⊤) S.affineBaseOver :=
  Functor.isoWhiskerLeft (tildeFactor Γ(S.Y', ⊤))
    (Scheme.Modules.pullbackComp S.f' S.Y'.isoSpec.hom)

/-- **[Stacks, Tag 01XK] over the affine base, in the indexing conclusion (b) is stated at**: the
global sections of the degree-`d` higher direct image of a quasi-coherent module on `X'` are its
degree-`d` cohomology, with scalars restricted along `(f')^♯`. -/
def cohomologySectionsIso :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent S.X'.ringCatSheaf) ⋙
        (Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ) ⋙
          moduleGlobalSections S.Y' ≅
      qcohCohomology S.X' S.d ⋙ ModuleCat.restrictScalars S.f'.appTop.hom :=
  haveI := S.quasiCompact_f'
  haveI := S.quasiSeparated_f'
  (cohomologyIsoGlobalSectionsRightDerivedPushforward S.f' (S.d : ℤ)).symm ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent S.X'.ringCatSheaf))
      (Functor.isoWhiskerRight
        (Stacks.DerivedIndexing.rightDerivedIso (moduleGlobalSections S.X') S.d).symm
        (ModuleCat.restrictScalars S.f'.appTop.hom))

/-- **The target functor of conclusion (b), read on modules over the base ring, is the one whose
Eilenberg-Watts hypotheses are proved**: the sections of `R^d f'_*(F' ⊗ (f')^* M~)` are the
cohomology `H^d(X', F' ⊗ (f')^* M~)`. -/
def affineTargetIso :
    baseTilde S ⋙ topDirectImageTensorFunctor S.f' F' S.d ⋙ moduleGlobalSections S.Y' ≅
      affineTargetFunctor S F' :=
  Functor.isoWhiskerRight (baseTildePullbackIso S)
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨S.X'.toRingedSpace.presheaf, S.X'.toRingedSpace.IsSheaf⟩).obj F' ⋙
        (Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ) ⋙
          moduleGlobalSections S.Y') ≪≫
    Functor.isoWhiskerLeft
      (geometricFactor Γ(S.Y', ⊤) S.affineBaseOver (coefficientQcoh S F'))
      (cohomologySectionsIso S)

/-! ### Rigidity, and conclusion (b) over an affine base -/

omit [F'.IsQuasicoherent] in
/-- **A transformation invertible at the structure sheaf is invertible at the associated module
of the base ring**: there the associated module *is* the structure sheaf. -/
theorem isIso_app_baseTilde_self (hτ : IsIso (τ.app (Scheme.unitModule S.Y'))) :
    IsIso (τ.app ((baseTilde S).obj (ModuleCat.of Γ(S.Y', ⊤) Γ(S.Y', ⊤)))) :=
  CategoryTheory.NatTrans.isIso_app_of_iso τ (baseTildeObjSelfIso S).symm hτ

/-- **The transformation read on modules over the base ring is invertible at the base ring**,
as soon as the transformation itself is invertible at the structure sheaf of the base. -/
theorem isIso_affineNatTrans_app_self (hτ : IsIso (τ.app (Scheme.unitModule S.Y'))) :
    IsIso ((affineNatTrans S F' τ).app (ModuleCat.of Γ(S.Y', ⊤) Γ(S.Y', ⊤))) :=
  Iso.isIso_hom ((moduleGlobalSections S.Y').mapIso
    (@asIso _ _ _ _ (τ.app ((baseTilde S).obj (ModuleCat.of Γ(S.Y', ⊤) Γ(S.Y', ⊤))))
      (isIso_app_baseTilde_self S F' τ hτ)))

/-- **A transformation of the two functors of conclusion (b), read on modules over the ring of
the affine base, is invertible at every module as soon as it is invertible at the base ring.**
This is Eilenberg-Watts rigidity
`Stacks.EilenbergWatts.isIso_app_of_isIso_app_self_of_natIso`: both functors are naturally
isomorphic to additive right exact functors commuting with arbitrary direct sums. -/
theorem isIso_affineNatTrans_app (hτ : IsIso (τ.app (Scheme.unitModule S.Y')))
    (M : ModuleCat.{u} Γ(S.Y', ⊤)) : IsIso ((affineNatTrans S F' τ).app M) :=
  have := preservesFiniteColimits_affineTargetFunctor S F'
  have := fun J : Type u => preservesColimitsOfShape_discrete_affineSourceFunctor S F' J
  have := fun J : Type u => preservesColimitsOfShape_discrete_affineTargetFunctor S F' J
  Stacks.EilenbergWatts.isIso_app_of_isIso_app_self_of_natIso (Iso.refl _) (affineTargetIso S F')
    (affineNatTrans S F' τ) (isIso_affineNatTrans_app_self S F' τ hτ) M

/-- **A transformation of the two functors of conclusion (b) is invertible at every associated
module** as soon as it is invertible at the structure sheaf of the affine base. -/
theorem isIso_app_baseTilde (hτ : IsIso (τ.app (Scheme.unitModule S.Y')))
    (M : ModuleCat.{u} Γ(S.Y', ⊤)) : IsIso (τ.app ((baseTilde S).obj M)) := by
  have := S.quasiCompact_f'
  have := S.quasiSeparated_f'
  have : ((baseTilde S).obj M).IsQuasicoherent :=
    inferInstanceAs (((Scheme.Modules.pullback S.Y'.isoSpec.hom).obj
      ((AlgebraicGeometry.tilde.functor (CommRingCat.of Γ(S.Y', ⊤))).obj M)).IsQuasicoherent)
  refine isIso_of_bijective_app_top_of_tensorSource S.f' F' _ S.d _ ?_
  exact (ConcreteCategory.isIso_iff_bijective _).1 (isIso_affineNatTrans_app S F' τ hτ M)

/-- **Over an affine base, a transformation of the two functors of conclusion (b) of
[Stacks, Tag 0EX3] invertible at the structure sheaf is invertible at every quasi-coherent
module.**  Every quasi-coherent module on the affine base is the associated module of its global
sections, by [Stacks, Tag 01I7], and the transformation is natural. -/
theorem isIso_app_of_isAffine_base (hτ : IsIso (τ.app (Scheme.unitModule S.Y')))
    (G : S.Y'.Modules) [G.IsQuasicoherent] : IsIso (τ.app G) :=
  CategoryTheory.NatTrans.isIso_app_of_iso τ (baseTildeObjIso S G)
    (isIso_app_baseTilde S F' τ hτ ((moduleGlobalSections S.Y').obj G))

/-! **Conclusion (b) over an affine base is not stated here.**  The affine-base invertibility of
`higherDirectImageTensorMap` that this file's machinery yields is the special case
`[IsAffine S.Y']` of `…TopDegreeBaseChange.isIso_higherDirectImageTensorMap`
(`TensorComparisonBase.lean`), which carries `@[stacks 0EX3 "(b)"]` and assumes nothing of the
base.  Stating it again under the extra hypothesis would duplicate that theorem's statement, so
what this file contributes is `isIso_app_of_isAffine_base` above, which the unconditional proof
reaches through `…TopDegreeBaseChangeSituation.restrictBase` at each affine open of an arbitrary
base. -/

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
