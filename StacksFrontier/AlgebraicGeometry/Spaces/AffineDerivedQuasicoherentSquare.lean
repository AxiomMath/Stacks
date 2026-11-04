module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentPushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison

/-!
# The commuting square of Stacks 08GY for an affine morphism of algebraic spaces

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  The direct image of `𝒪`-modules preserves quasi-coherence, so it restricts to
`f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` (`AlgebraicGeometry.Space.quasicoherentPushforward`), and that
restriction is exact; an exact functor induces a functor of unbounded derived categories with no
derivation, so `f_*` induces `D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))`.  [Stacks, Tag 08GY] asserts that the
comparison functor of [Stacks, Tag 08F1] carries that induced functor to the derived direct
image `Rf_*`.  This file builds the square.

Everything here is derived-category bookkeeping.  The two geometric inputs are carried as
hypotheses:

* `hG9N`, the affine case of [Stacks, Tag 0G9N] on the algebraic-spaces side — that a complex of
  quasi-coherent `𝒪_X`-modules computes its own derived direct image, in the form that the
  derivation unit `α` of `Rf_*` is invertible at the homotopy class of such a complex;
* `hcolim`, right exactness of `f_*` on quasi-coherent modules, which is what makes the induced
  functor `D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))` exist at all.

Left exactness, additivity and the abelian structures are unconditional and are *not* hypotheses:
`AlgebraicGeometry.Space.preservesFiniteLimits_quasicoherentPushforward` (which
`StacksFrontier/AlgebraicGeometry/Spaces/AffineQuasicoherentPushforwardExact.lean` registers as an
instance, so the induced functors below need no binder for it),
`AlgebraicGeometry.Space.quasicoherentPushforward_additive` and
`AlgebraicGeometry.Space.abelian_quasicoherentSheaves_algebraicSpace`.  The other half of
[Stacks, Tag 08GY] — that the induced functor `D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))` *is* a total right
derived functor of `f_*` — is
`AlgebraicGeometry.Space.isRightDerivedFunctor_quasicoherentPushforward_mapDerivedCategory` in
that same file and is not restated here.

## Main definitions

* `AlgebraicGeometry.Space.mapDerivedCategoryQuasicoherentPushforwardCompιIso` — [Stacks,
  Tag 0G9N] for an affine morphism of algebraic spaces, as an isomorphism of functors
  `D(QCoh(𝒪_X)) ⥤ D(𝒪_Y)`.
* `AlgebraicGeometry.Space.derivedQuasicoherentComparisonSquare` — **the commuting square of
  [Stacks, Tag 08GY]**.

## Main results

* `AlgebraicGeometry.Space.isIso_whiskerLeft_derivedModulePushforwardUnit` — the comparison
  `f_* ⟶ Rf_*` is invertible on the whole image of `K(QCoh(𝒪_X))`.

## Implementation notes

**Where the square is stated, and why it is stated there.**  The square of [Stacks, Tag 08GY] is
a square of functors into `D_QCoh(𝒪_Y)`, and
`AlgebraicGeometry.Space.derivedQuasicoherentComparisonSquare` states it one step further on,
inside `D(𝒪_Y)`, which is where the library's statement of the tag states it.  That loses
nothing: the inclusion `ιQ : D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)` is fully faithful — it is
`CategoryTheory.ObjectProperty.ι` of the quasi-coherent-cohomology predicate, so
`CategoryTheory.ObjectProperty.fullyFaithfulι` applies — and composition with a fully faithful
functor reflects isomorphisms of functors, so the square stated here is *equivalent* to
commutativity of the square inside `D_QCoh(𝒪_Y)`.

The reason to state it after the inclusion is that the right edge of the square inside
`D_QCoh(𝒪_Y)` is the *restriction* of `Rf_*` to the complexes with quasi-coherent cohomology,
and the existence of that restriction is part (1) of [Stacks, Tag 08D5] — that `Rf_*` carries
quasi-coherent cohomology to quasi-coherent cohomology.  This development does not have that
statement on the algebraic-spaces side, and it is not an assertion of [Stacks, Tag 08GY]; naming
it as a further hypothesis would only move the open input around.  So `Rf_*` appears here as a
functor `D(𝒪_X) ⥤ D(𝒪_Y)` and the comparison functors are composed with `ιQ`.

**No `stacks` attribute here.**  `hG9N` and `hcolim` are open inputs of this file, each being
discharged in a sibling file; a separate file registers the [Stacks, Tag 08GY] attribute once
both are available.

**`Rf_*` is an arbitrary right derived functor.**  The right edge is a binder `Rf` together with
a derivation unit `α`, rather than a chosen `CategoryTheory.Functor.totalRightDerived`.  Such an
`Rf` exists for every morphism of algebraic spaces, by
`AlgebraicGeometry.Space.hasRightDerivedFunctor_modulePushforward`; stating the square against a
binder is what lets a caller use the derived direct image it already has.

**Two binders of the setting that the statements do not carry.**  The section variables include
`hf : IsAffineHom B S hS f.hom` and
`[Rf.IsRightDerivedFunctor α (HomotopyCategory.quasiIso …)]`, because that is the setting of
[Stacks, Tag 08GY], but no declaration below uses either, so Lean includes neither.  That is
deliberate rather than an oversight: affineness enters only through `hG9N` and `hcolim`, and all
that the proofs ask of `α` is the invertibility `hG9N` asserts.  The statements are therefore
proved for an arbitrary pair `(Rf, α)` subject to `hG9N`, which is strictly more general than —
and so applies to — the derived direct image with its derivation unit.  Carrying the two binders
would weaken the statements for nothing.

**Local priority raises.**  As in the neighbouring files on the small étale modules of an
algebraic space, `SheafOfModules.instAbelian` is raised and the two universe-pinned instances
`AlgebraicGeometry.Space.isGrothendieckAbelian_modules` and
`AlgebraicGeometry.Space.enoughInjectives_modules` are made local, so that the homological
instances on the modules are found at module universe `u`.  `HasDerivedCategory.standard` is
local for the reason it is in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedComparison.lean`, where the comparison
functor of [Stacks, Tag 08F1] is stated: a free `HasDerivedCategory` binder on the quasi-coherent
modules does not elaborate against the `Abelian` instance that is itself derived from the closure
properties.

## References

* [Stacks Project, Tag 08GY](https://stacks.math.columbia.edu/tag/08GY)
* [Stacks Project, Tag 08F1](https://stacks.math.columbia.edu/tag/08F1)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

attribute [local instance] isGrothendieckAbelian_modules
attribute [local instance] enoughInjectives_modules

section

variable (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (hG9N : ∀ K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ,
      (∀ n, (K.X n).IsQuasicoherentOnSite) →
        IsIso (α.app ((HomotopyCategory.quotient (Modules.{u, u} B S hS X.1 X.2)
          (ComplexShape.up ℤ)).obj K)))
    (hpush : PushforwardPreservesQuasicoherence B S hS f)
    (hcolim : PreservesFiniteColimits (quasicoherentPushforward B S hS f hpush))

omit [Rf.IsRightDerivedFunctor α
  (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] in
include hG9N in
/-- **The comparison `f_* ⟶ Rf_*` is invertible on the whole image of `K(QCoh(𝒪_X))`.**  An
object of `K(QCoh(𝒪_X))` is the homotopy class of a complex of quasi-coherent modules, and the
inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` carries it to a complex of quasi-coherent `𝒪_X`-modules, on
which the hypothesis `hG9N` — the affine case of [Stacks, Tag 0G9N] — applies.

Every object of `K(QCoh(𝒪_X))` is a homotopy class by
`CategoryTheory.HomotopyCategory.quotient_obj_surjective`, and the value of the derived inclusion
on such a class is transported to the class of the degreewise image by
`CategoryTheory.Functor.mapHomotopyCategoryFactors`. -/
theorem isIso_whiskerLeft_derivedModulePushforwardUnit :
    IsIso (Functor.whiskerLeft
      ((quasicoherentSheavesι B S hS X).mapHomotopyCategory (ComplexShape.up ℤ)) α) := by
  have hcomp : ∀ L, IsIso ((Functor.whiskerLeft
      ((quasicoherentSheavesι B S hS X).mapHomotopyCategory (ComplexShape.up ℤ)) α).app L) := by
    intro L
    obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    exact (NatTrans.isIso_app_iff_of_iso α
      (((quasicoherentSheavesι B S hS X).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app M)).2
      (hG9N (((quasicoherentSheavesι B S hS X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) fun n => (M.X n).2)
  exact NatIso.isIso_of_isIso_app _

/-- **[Stacks, Tag 0G9N] for an affine morphism of algebraic spaces, as an isomorphism of
functors on `D(QCoh(𝒪_X))`.**  Deriving the inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` of the
quasi-coherent modules and then taking the unbounded derived direct image is the same as taking
the derived functor of the direct image on quasi-coherent modules and then deriving the inclusion
`ι : QCoh(𝒪_Y) ⥤ Mod(𝒪_Y)`.

Both sides are functors `D(QCoh(𝒪_X)) ⥤ D(𝒪_Y)` lifting a functor on `K(QCoh(𝒪_X))` through the
localization `DerivedCategory.Qh`, so `CategoryTheory.Localization.liftNatIso` reduces the claim
to an isomorphism of the two lifted functors.  On `K(QCoh(𝒪_X))` the two differ exactly by the
comparison map `f_* ⟶ Rf_*`, which is invertible there by
`AlgebraicGeometry.Space.isIso_whiskerLeft_derivedModulePushforwardUnit`; the remaining steps are
the factorization of `CategoryTheory.Functor.mapDerivedCategory` through the homotopy category
and `AlgebraicGeometry.Space.quasicoherentPushforwardCompιIso` read on homotopy categories. -/
def mapDerivedCategoryQuasicoherentPushforwardCompιIso :
    letI := hcolim
    (quasicoherentPushforward B S hS f hpush).mapDerivedCategory ⋙
        (quasicoherentSheavesι B S hS Y).mapDerivedCategory ≅
      (quasicoherentSheavesι B S hS X).mapDerivedCategory ⋙ Rf :=
  letI := hcolim
  haveI := isIso_whiskerLeft_derivedModulePushforwardUnit B S hS f Rf α hG9N
  Localization.liftNatIso DerivedCategory.Qh
    (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
      (ComplexShape.up ℤ))
    (((quasicoherentPushforward B S hS f hpush).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙ (quasicoherentSheavesι B S hS Y).mapDerivedCategory)
    (((quasicoherentSheavesι B S hS X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙ Rf)
    _ _
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        ((quasicoherentPushforward B S hS f hpush).mapHomotopyCategory (ComplexShape.up ℤ))
        (quasicoherentSheavesι B S hS Y).mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (quasicoherentPushforward B S hS f hpush ⋙
              quasicoherentSheavesι B S hS Y)) (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomotopyCategoryCompIso
            (quasicoherentPushforwardCompιIso B S hS f hpush).symm (ComplexShape.up ℤ)).symm)
        DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      asIso (Functor.whiskerLeft
        ((quasicoherentSheavesι B S hS X).mapHomotopyCategory (ComplexShape.up ℤ)) α) ≪≫
      (Functor.associator _ _ _).symm)

/-- **The commuting square of [Stacks, Tag 08GY].**  For `f : X ⟶ Y` an affine morphism of
algebraic spaces the square

`D(QCoh(𝒪_X)) ⟶ D_QCoh(𝒪_X) ⟶^{Rf_*} D_QCoh(𝒪_Y)`,
`D(QCoh(𝒪_X)) ⟶^{f_*} D(QCoh(𝒪_Y)) ⟶ D_QCoh(𝒪_Y)`

commutes: the comparison functor of [Stacks, Tag 08F1] carries the derived functor of the direct
image on quasi-coherent modules to the derived direct image.

It is stated here after the fully faithful inclusion `ιQ : D_QCoh ⥤ D` on both corners of the
right-hand column, which is an equivalent assertion and is where the library's statement of the
tag states it; see the implementation notes for why.  Composed with that inclusion the comparison
functor becomes the derived inclusion, by
`AlgebraicGeometry.Space.quasicoherentDerivedComparisonCompιIso`, and the square becomes
`AlgebraicGeometry.Space.mapDerivedCategoryQuasicoherentPushforwardCompιIso`, which is
[Stacks, Tag 0G9N] for an affine morphism. -/
def derivedQuasicoherentComparisonSquare :
    letI := hcolim
    (quasicoherentPushforward B S hS f hpush).mapDerivedCategory ⋙
        quasicoherentDerivedComparisonSchemeUniverse B S hS Y.1 Y.2 ⋙
          (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).ι ≅
      quasicoherentDerivedComparisonSchemeUniverse B S hS X.1 X.2 ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⋙
          Rf :=
  letI := hcolim
  Functor.isoWhiskerLeft (quasicoherentPushforward B S hS f hpush).mapDerivedCategory
      (quasicoherentDerivedComparisonCompιIso B S hS Y.1 Y.2) ≪≫
    mapDerivedCategoryQuasicoherentPushforwardCompιIso B S hS f Rf α hG9N hpush hcolim ≪≫
    Functor.isoWhiskerRight
      (quasicoherentDerivedComparisonCompιIso B S hS X.1 X.2).symm Rf ≪≫
    Functor.associator _ _ _

end

end AlgebraicGeometry.Space

end
