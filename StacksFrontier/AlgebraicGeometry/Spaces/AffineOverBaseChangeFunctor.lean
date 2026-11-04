module

public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedDirectImageAlgebraFactorization

/-!
# Base change of the algebraic spaces affine over a base, as a functor

Let `g : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  `AlgebraicGeometry.Space.affineOverBaseChange` sends an algebraic space `Z` affine
over `X` to the base change `Y ×_X Z`, affine over `Y`, and
`AlgebraicGeometry.Space.affineOverBaseChangeProjection` is its projection to `Z`.  This file
makes that assignment a *functor* and proves that the projections are natural in `Z`.

## Main definitions

* `AlgebraicGeometry.Space.affineOverBaseChangeMap` is the base change of a morphism of
  algebraic spaces affine over `X`.
* `AlgebraicGeometry.Space.affineOverBaseChangeFunctor` is base change as a functor
  `AffineOver X ⥤ AffineOver Y`, agreeing with
  `AlgebraicGeometry.Space.affineOverBaseChange` on objects.

## Main results

* `AlgebraicGeometry.Space.affineOverBaseChangeMap_comp_projection`: **the projections of the
  geometric base change are natural in the affine algebraic space being base-changed.**

## Implementation notes

The two declarations here have exactly the types of the `affineBaseChange` and
`affineBaseChange_projection_naturality` fields of
`AlgebraicGeometry.Space.BaseChangeCompatibility`, read with `affineBaseChange_projection` as
`AlgebraicGeometry.Space.affineOverBaseChangeProjection`.  That structure carries them as data
because they had not been constructed:
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedDirectImageAlgebraFactorization` builds the
`affineBaseChange` field only *at an object*, which leaves the naturality field with no
`(affineBaseChange g).map` to speak of.  Nothing here hypothesises an anti-equivalence, so
nothing here is weakened by the size obstruction of
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`.

Every morphism into a base change is produced by the universal property of the one cartesian
square the development already has,
`AlgebraicGeometry.Space.affineOverBaseChange_isPullback`, rather than by `pullback.map` on the
underlying presheaves.  This keeps the construction at the spelling of
`AlgebraicGeometry.Space.affineOverBaseChangeProjection` and
`AlgebraicGeometry.Space.affineOverBaseChange`, so that the naturality statement is literally
`CategoryTheory.IsPullback.lift_fst` and needs no comparison between the fibre product of
algebraic spaces and the fibre product of their underlying presheaves.

**The two fields of `AlgebraicGeometry.Space.BaseChangeCompatibility` that remain open, and
why.**  Of its twelve fields, ten are now constructed with no anti-equivalence: the three of
`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback`, the two of
`StacksFrontier.AlgebraicGeometry.Spaces.PushforwardBaseChangeComparison`,
`affineBaseChange_projection` and `affineBaseChange_isPullback` of
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedDirectImageAlgebraFactorization`,
`affineBaseChange` and `affineBaseChange_projection_naturality` here, and
`algebraPullback_isQuasicoherent` as
`AlgebraicGeometry.Space.algebraPullback_isQuasicoherent` of
`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackQuasicoherent`.  `baseChangeIso` and
`baseChangeIso_canonical` mention `E.equivalence`, `E.pushforwardIso` and `E.pushforward_obj`,
so neither can be stated at all without an anti-equivalence; they are not merely unproved.

`algebraPullback_isQuasicoherent` *is* statable with no anti-equivalence — as
`AlgebraSheaf.IsQuasicoherent ((algebraPullback B S hS g).obj A)` for `A.IsQuasicoherent` — and
is now proved, in
`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackQuasicoherent`.  What it needs is *not*
Stacks 03GA for modules: that is available
unconditionally at an arbitrary morphism and an arbitrary quasi-coherent module, as
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`.  Since
`AlgebraicGeometry.Space.modulePullback` is by definition the inverse image followed by
extension of scalars along `g♯`, it is reached from the isomorphism

`AlgebraSheaf.underlyingModule ((algebraPullback B S hS g).obj A) ≅
  (modulePullback B S hS g).obj (AlgebraSheaf.underlyingModule A)`,

which is
`AlgebraicGeometry.Space.underlyingModuleAlgebraPullbackModulePullbackIso`, and that
isomorphism factors through two statements, both of which are now available.

*The extension-of-scalars half is proved.*  The notes of
`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback` say that the identification of the
module underlying the pushout with the tensor product "is not stated anywhere".  That is out of
date: `Stacks.SheafOfModules.AlgebraPushout.underlyingModulePushoutIso`, resting on the proved
`Stacks.SheafOfModules.AlgebraPushout.isIso_extendScalarsComparison`, is exactly that statement
on an arbitrary site, and
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule_eq_restrictScalars` says the module
underlying an algebra sheaf here is the same term that file's `underlyingModule` names.  What
blocks its use is a universe restriction and nothing conceptual: that file is stated for
`[SmallCategory C]` with the rings in the objects' universe, whereas the small étale site is
`AlgebraicGeometry.Space.smallEtaleRingedSite`, a `RingedSite.{u + 1, u, u}` — objects in
`Type (u + 1)`, morphisms in `Type u`, rings in `CommRingCat.{u}`.

*The inverse-image half is proved too.*
`AlgebraicGeometry.Space.underlyingModule_inverseImageAlgebra` identifies the module
underlying `g⁻¹A` with the inverse image of the module underlying `A`, modulo the interchange
of the inverse image with restriction of scalars.  All of it is definitional except the
comparison on morphisms,
`AlgebraicGeometry.Space.ringSheafMap_ringSheafPullback_map`, which forgetting commutativity
being fully faithful on sheaves supplies.  The scheme-level
`Stacks.AffineAlgebraEquivalence.algebraPullbackComparison` still names the gap as its own
remaining input, and the scheme-level theorem
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_obj` is proved without it, by
localizing to affine opens and transporting along the pseudofunctoriality of the scheme-level
algebra pullback, `Stacks.AffineAlgebraEquivalence.algebraPullbackComp`.  Imitating that route
here would need a composition comparison for `AlgebraicGeometry.Space.algebraPullback`, which
is also absent.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The base change `Y ×_X Z ⟶ Y ×_X Z'` of a morphism of algebraic spaces affine over `X`.**

It is the unique morphism whose composite with the projection to `Z'` is the projection to `Z`
followed by the given morphism and which lies over `Y`; both clauses come from the universal
property of `AlgebraicGeometry.Space.affineOverBaseChange_isPullback`. -/
def affineOverBaseChangeMap (g : Y ⟶ X) {Z Z' : AffineOver B S hS X} (φ : Z ⟶ Z') :
    affineOverBaseChange B S hS g Z ⟶ affineOverBaseChange B S hS g Z' :=
  ObjectProperty.homMk (Over.homMk
    ((affineOverBaseChange_isPullback B S hS g Z').lift
      (affineOverBaseChangeProjection B S hS g Z ≫ φ.hom.left)
      (affineOverBaseChange B S hS g Z).obj.hom
      (by rw [Category.assoc, Over.w φ.hom, (affineOverBaseChange_isPullback B S hS g Z).w]))
    ((affineOverBaseChange_isPullback B S hS g Z').lift_snd _ _ _))

/-- **The projections of the geometric base change are natural in the affine algebraic space
being base-changed.**

This has exactly the type of the `affineBaseChange_projection_naturality` field of
`AlgebraicGeometry.Space.BaseChangeCompatibility`, and is proved with no anti-equivalence and
no base-change compatibility: it is the defining property of
`AlgebraicGeometry.Space.affineOverBaseChangeMap`. -/
@[reassoc, stacks 081V "naturality of the projections of the geometric base change \
Y ×_X Z ⟶ Z in Z; the anti-equivalence of the tag and its compatibility with base change are \
not proved"]
theorem affineOverBaseChangeMap_comp_projection (g : Y ⟶ X) {Z Z' : AffineOver B S hS X}
    (φ : Z ⟶ Z') :
    (affineOverBaseChangeMap B S hS g φ).hom.left ≫
        affineOverBaseChangeProjection B S hS g Z' =
      affineOverBaseChangeProjection B S hS g Z ≫ φ.hom.left :=
  (affineOverBaseChange_isPullback B S hS g Z').lift_fst _ _ _

/-- **Base change of the algebraic spaces affine over `X`, as a functor
`AffineOver X ⥤ AffineOver Y`.**

On objects it is `AlgebraicGeometry.Space.affineOverBaseChange` and on morphisms
`AlgebraicGeometry.Space.affineOverBaseChangeMap`.  This has exactly the type of the
`affineBaseChange` field of `AlgebraicGeometry.Space.BaseChangeCompatibility`, of which
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedDirectImageAlgebraFactorization` constructs only
the action on objects. -/
@[stacks 081V "base change of the algebraic spaces affine over X as a functor; \
the anti-equivalence of the tag and its compatibility with base change are not proved"]
def affineOverBaseChangeFunctor (g : Y ⟶ X) :
    AffineOver B S hS X ⥤ AffineOver B S hS Y where
  obj Z := affineOverBaseChange B S hS g Z
  map φ := affineOverBaseChangeMap B S hS g φ
  map_id Z := ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    ((affineOverBaseChange_isPullback B S hS g Z).hom_ext
      (by rw [affineOverBaseChangeMap_comp_projection]; simp)
      ((Over.w _).trans (Over.w _).symm)))
  map_comp {Z Z' Z''} φ ψ := ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    ((affineOverBaseChange_isPullback B S hS g Z'').hom_ext
      (by
        rw [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left,
          affineOverBaseChangeMap_comp_projection, Category.assoc,
          affineOverBaseChangeMap_comp_projection,
          affineOverBaseChangeMap_comp_projection_assoc]
        simp)
      ((Over.w _).trans (Over.w _).symm)))

/-- Base change as a functor agrees on objects with
`AlgebraicGeometry.Space.affineOverBaseChange`. -/
@[simp]
theorem affineOverBaseChangeFunctor_obj (g : Y ⟶ X) (Z : AffineOver B S hS X) :
    (affineOverBaseChangeFunctor B S hS g).obj Z = affineOverBaseChange B S hS g Z :=
  rfl

/-- Base change as a functor agrees on morphisms with
`AlgebraicGeometry.Space.affineOverBaseChangeMap`. -/
@[simp]
theorem affineOverBaseChangeFunctor_map (g : Y ⟶ X) {Z Z' : AffineOver B S hS X} (φ : Z ⟶ Z') :
    (affineOverBaseChangeFunctor B S hS g).map φ = affineOverBaseChangeMap B S hS g φ :=
  rfl

end AlgebraicGeometry.Space

end
