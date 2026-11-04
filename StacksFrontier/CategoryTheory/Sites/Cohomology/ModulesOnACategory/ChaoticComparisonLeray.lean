module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonOnCartesianObjects
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactnessFreeModuleUniverse

/-!
# Restriction to a slice commutes with the derived pushforward of the chaotic comparison

Let `C` be a category carrying a Grothendieck topology `τ`, let `τ'` be the chaotic topology on
`C`, let `O` be a `τ`-sheaf of rings and let `ε : (C_τ, O_τ) ⟶ (C_τ', O_τ')` be the comparison
morphism of ringed sites, so that `ε_*` is the forgetful functor from `τ`-sheaves of `O`-modules
to presheaves of `O`-modules and `ε^*` is `τ`-sheafification.  Fix an object `U` of `C` and write
`-|_U` for restriction along the forgetful functor `C/U ⥤ C`, of presheaves of modules on the
chaotic side and of `τ`-sheaves of modules on the other.

The identity `(ε_*K)|_U = ε_{U*}(K|_U)` holds on the nose, both sides being the sections of the
underlying presheaf of `K` read on `C/U`.  Proved here is the derived form

`(Rε_*K)|_U = Rε_{U*}(K|_U)`,

and the computation of derived sections it gives:

`RΓ(U, Rε_*K) = RΓ(id_U, Rε_{U*}(K|_U))`.

That second identity is the Leray step of the proof of Stacks 0GZS, which the source invokes as
"by Leray": it is what turns a statement about `RΓ((C/U)_τ, -)` into a statement about
`RΓ(U, Rε_*(-))`, and so what connects hypothesis (2) of that tag, read on the localized site, to
the invertibility of the `ε`-unit on derived sections over the objects of `C` that
`Stacks.ModulesOnACategory.ChaoticComparison.cartesianEquivalenceOfSectionwise` takes.

## Main definitions

* `Stacks.ModulesOnACategory.ChaoticComparison.sheafRestriction`: restriction of `τ`-sheaves of
  modules to the localized site, with its target spelled as the modules on `overRingSheaf R U`.
* `Stacks.ModulesOnACategory.ChaoticComparison.lerayUnitLeft` and `lerayUnitRight`: the two
  comparisons exhibiting the two sides as right derived functors of the one underived composite.

## Main results

* `Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfExact`: the general brick, with the second
  functor exact instead of the first preserving K-injectivity.  It is the mirror of
  `derivedCompIso` and is not used below; the construction here is a single application of the
  uniqueness of right derived functors, which is what makes its defining compatibility available
  in one step.
* `Stacks.ModulesOnACategory.ChaoticComparison.derivedRestrictionPushforwardIso`:
  `(Rε_*K)|_U = Rε_{U*}(K|_U)`.
* `Stacks.ModulesOnACategory.ChaoticComparison.derivedRestrictionPushforwardIso_fac`: its
  defining compatibility — it carries `lerayUnitLeft` into `lerayUnitRight`.
* `Stacks.ModulesOnACategory.ChaoticComparison.derivedSectionsPushforwardIso`:
  `RΓ(U, Rε_*K) = RΓ(id_U, Rε_{U*}(K|_U))`.

## Implementation notes

Both sides of the first identity are right derived functors of the one functor
`ε_* ⋙ (-|_U) = (-|_U) ⋙ ε_{U*}`, which holds on the nose
(`epsilonPushforward_comp_restrictionFunctor`), so the identity is one application of
`CategoryTheory.Functor.rightDerivedNatIso`.  Each side is a composite of two derived functors
deriving the composite of the two underived ones, by
`Stacks.Cohomology.Localization.isRightDerivedFunctor_comp_of_kInjectives`, and the two reasons
differ.

On the left the second factor, restriction of presheaves of modules, is exact — it is both a left
and a right adjoint, `Stacks.ModulesOnACategory.MorphismsOverAnObject.restrictionIsLeftAdjoint`
and `restrictionIsRightAdjoint` — so its comparison `Functor.mapDerivedCategoryFactorsh.inv` is
invertible everywhere and no condition on `ε_*` is needed.

On the right the first factor, restriction of sheaves of modules, carries K-injective complexes to
K-injective complexes — Stacks 08FI, here at independent universes as
`Stacks.Cohomology.Localization.isKInjective_over_freeUniverses` — so the
comparison of `Rε_{U*}` is invertible there.  Its own exactness, needed to read the derived
restriction as the functor induced degreewise, is
`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits` and
`overFunctor_preservesFiniteColimits`.

**Why one application and not a composite of several.**  The isomorphism was first built as
`Rε_* ⋙ R(-|_U) ≅ R(ε_* ⋙ (-|_U)) = R((-|_U) ⋙ ε_{U*}) ≅ R(-|_U) ⋙ Rε_{U*}` with two further
isomorphisms identifying each total right derived restriction with the functor induced degreewise:
five layers, none of which exposes what the composite does to the comparison maps.  Built in one
step the compatibility is `Functor.rightDerivedNatTrans_app`, which is
`derivedRestrictionPushforwardIso_fac`; that is the handle on which any identification of this
isomorphism with something constructed differently has to run, and in particular the one needed to
identify it with the mate, along the two derived `ε`-adjunctions, of the derived sheafification
square of the sibling module.

The sections form is the first one whiskered with derived sections over the terminal object `id_U`
of `C/U`, after
`Stacks.ModulesOnACategory.MorphismsOverAnObject.derivedSectionsIso` has rewritten `RΓ(U, -)` on
the chaotic side as `RΓ(id_U, -|_U)`; on the chaotic side that identification needs no derived
correction, derived sections there being exact evaluation.

Stacks 0D6G is the same statement for a morphism of ringed *sites*, and is already proved as
`Stacks.Cohomology.Localization.derivedPushforwardOverFunctorIso`, which carries the tag.  It does
not apply here: `ε` is the identity functor read between two topologies, and the development of
this file presents neither `Rε_*` nor its derived pushforward as
`AlgebraicGeometry.RingedSite.Hom.toRingedToposSiteHom.pushforwardTopos`; the two presentations
would have to be glued, and the argument is shorter than the glue.

**Universes.** The objects and the morphisms of `C` and the section rings of `O` lie in three
independent universes `u`, `v` and `r`, and the module sections in `max u v r w` for a free `w`,
the universe at which the sheaves of modules on the site and on each slice form a Grothendieck
abelian category. Stacks 08FI is needed at those universes; the tagged
`Stacks.Cohomology.Localization.isKInjective_over` is stated with all of them identified, so it is
re-derived here as `Stacks.Cohomology.Localization.isKInjective_over_freeUniverses` from the
exactness of extension by zero at a free module universe.

Two spellings of one notion are pinned by `abbrev`s — `sheafRestriction` for restriction of
sheaves of modules and `sliceEpsilonPushforward`, `sliceDerivedEpsilonPushforward` and
`sliceDerivedEpsilonPushforwardUnit` for `ε_{U*}` and its derived functor — so that the sheaf of
rings on `C/U` is `overRingSheaf R U` and the presheaf of rings is `overRingPresheaf R.obj U`
everywhere.  Without them the composites below are rejected: the two spellings are equal by `rfl`,
but the defeq is blocked at the transparency at which instance search and the elaboration of `⋙`
operate, and `overRingSheaf` cannot be made an `abbrev` instead — reducible, it is unfolded by
instance search, which then fails to find the additivity of `ε_*` on the slice.

`lerayComparison`, the isomorphism between the two sources, has identity components; it is carried
through `derivedRestrictionPushforwardIso_fac` rather than cancelled, because cancelling it needs
a `rw` whose motive is not type-correct at `implicit` transparency.

## References

* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 0D6G](https://stacks.math.columbia.edu/tag/0D6G)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.LerayUnbounded

universe v w u₁ u₂ u₃ v₁ v₂ v₃

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [HasDerivedCategory.{v} A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [IsGrothendieckAbelian.{w} B] [HasDerivedCategory.{v} B] {E : Type u₃} [Category.{v₃} E]
  [Abelian E] [HasDerivedCategory.{v} E]

/-- If the second functor is exact then `RF ⋙ RG` is a right derived functor of the composite of
the two degreewise functors.  The comparison for `RF` is invertible on a K-injective complex, and
the one for `RG` is invertible everywhere, an exact functor needing no derivation. -/
theorem isRightDerivedFunctor_derivedCompUnit_of_exact (F : A ⥤ B) [F.Additive] (G : B ⥤ E)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (Stacks.DerivedFunctor.totalRightDerived F ⋙
        Stacks.DerivedFunctor.totalRightDerived G).IsRightDerivedFunctor (derivedCompUnit F G)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.isRightDerivedFunctor_comp_of_kInjectives F G _ _ _ _
    (fun I _ => Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ I)
    (fun _ _ => by
      have : IsIso ((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
            (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))) :=
        Stacks.Cohomology.Localization.isIso_of_isRightDerivedFunctor_of_exact G _ _
      infer_instance)

/-- **The brick, with the second functor exact.**  If `G` is exact and `e : F ⋙ G ≅ H`, then
`RF ⋙ RG ≅ RH`.  This is `Stacks.Cohomology.LerayUnbounded.derivedCompIso` with the hypothesis
on the second factor instead of the first: there `F` must preserve K-injectivity, here `G` must be
exact, and either makes the composite a right derived functor of the composite. -/
def derivedCompIsoOfExact (F : A ⥤ B) [F.Additive] (G : B ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (H : A ⥤ E) [H.Additive]
    (e : F ⋙ G ≅ H) :
    Stacks.DerivedFunctor.totalRightDerived F ⋙ Stacks.DerivedFunctor.totalRightDerived G ≅
      Stacks.DerivedFunctor.totalRightDerived H :=
  letI := isRightDerivedFunctor_derivedCompUnit_of_exact F G
  Functor.rightDerivedNatIso _ _ (derivedCompUnit F G)
    ((H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)) DerivedCategory.Qh)

end Stacks.Cohomology.LerayUnbounded

namespace Stacks.Cohomology.Localization

universe w u v r

/-- **Stacks 08FI at independent universes.** Restriction to the slice site over an object
preserves K-injective complexes of sheaves of modules, for a site whose objects, morphisms and
ring sections lie in three unrelated universes and whose modules lie in a universe containing all
three. Extension by zero is an exact left adjoint of the restriction at these universes
(`Stacks.Sites.ExtensionByZero.FreeModuleUniverse.extensionByZero_exact`), so the adjoint
criterion for K-injectivity applies, exactly as for the collapsed
`Stacks.Cohomology.Localization.isKInjective_over`, which carries the tag. -/
theorem isKInjective_over_freeUniverses {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{r}) (U : C)
    [HasSheafify J AddCommGrpCat.{max u v r w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
    (I : CochainComplex (SheafOfModules.{max u v r w} R) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((SheafOfModules.overFunctor.{max u v r w} R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  let F := SheafOfModules.overFunctor.{max u v r w} R U
  let G := SheafOfModules.pullback.{max u v r w} (F := Over.forget U)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
  let hG := (exactFunctor_iff G).mp
    (Stacks.Sites.ExtensionByZero.FreeModuleUniverse.extensionByZero_exact.{max u r w, r, v, u}
      J R U)
  let : F.Additive := inferInstanceAs (SheafOfModules.pushforward.{max u v r w}
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).Additive
  let : PreservesFiniteLimits G := hG.1
  let : PreservesFiniteColimits G := hG.2
  let : G.Additive := Functor.additive_of_preserves_binary_products G
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact F G
    (SheafOfModules.pullbackPushforwardAdjunction (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))) I

end Stacks.Cohomology.Localization

namespace Stacks.ModulesOnACategory.ChaoticComparison

open Stacks.Cohomology.LerayUnbounded (derivedCompIso derivedCompIsoOfExact)
open Stacks.ModulesOnACategory.MorphismsOverAnObject
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.Sites.OverModules (overRingPresheaf restrictionFunctor)

universe w u v r

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  (U : C) [HasSheafify (J.over U) AddCommGrpCat.{max u v r w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]

attribute [local instance] restrictionIsLeftAdjoint restrictionIsRightAdjoint

/-- Restriction of `τ`-sheaves of modules along the forgetful functor `C/U ⥤ C`, with its target
spelled as the modules on `overRingSheaf R U`.  This is Mathlib's `SheafOfModules.overFunctor`;
the two spellings of the sheaf of rings on `C/U` are definitionally equal, but instance search
does not see through the one `SheafOfModules.overFunctor` is stated at, so the functors it is
composed with here would not find their additivity. -/
abbrev sheafRestriction :
    SheafOfModules.{max u v r w} R ⥤ SheafOfModules.{max u v r w} (overRingSheaf R U) :=
  SheafOfModules.overFunctor.{max u v r w} R U

/-- Restriction of sheaves of modules to the localized site is additive. -/
instance sheafRestriction_additive : (sheafRestriction.{w} R U).Additive :=
  ⟨by intros; ext W; rfl⟩

/-- Restriction of sheaves of modules to the localized site preserves finite limits. -/
instance sheafRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (sheafRestriction.{w} R U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U

/-- Restriction of sheaves of modules to the localized site preserves finite colimits. -/
instance sheafRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (sheafRestriction.{w} R U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U

omit [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [HasSheafify (J.over U) AddCommGrpCat.{max u v r w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}] in
/-- The underived identity `(ε_*K)|_U = ε_{U*}(K|_U)`: both sides are the sections of the
underlying presheaf of `K` read on `C/U`, so this is an equality of functors. -/
theorem epsilonPushforward_comp_restrictionFunctor :
    epsilonPushforward.{w} R ⋙ restrictionFunctor.{v, u, r, max u v r w} R.obj U =
      sheafRestriction.{w} R U ⋙ epsilonPushforward.{w} (overRingSheaf R U) :=
  rfl

/-- `ε_{U*}` with its codomain spelled as the presheaves of modules on `overRingPresheaf R.obj U`,
which is the spelling restriction of presheaves of modules takes its values in. -/
abbrev sliceEpsilonPushforward :
    SheafOfModules.{max u v r w} (overRingSheaf R U) ⥤
      PresheafOfModules.{max u v r w} (overRingPresheaf R.obj U) :=
  epsilonPushforward.{w} (overRingSheaf R U)

/-- `ε_{U*}` is additive. -/
instance sliceEpsilonPushforward_additive : (sliceEpsilonPushforward.{w} R U).Additive :=
  epsilonPushforward_additive.{w} (overRingSheaf R U)

/-- `Rε_{U*}` with its codomain spelled as the derived category of presheaves of modules on
`overRingPresheaf R.obj U`. -/
abbrev sliceDerivedEpsilonPushforward :
    DerivedCategory (SheafOfModules.{max u v r w} (overRingSheaf R U)) ⥤
      DerivedCategory (PresheafOfModules.{max u v r w} (overRingPresheaf R.obj U)) :=
  derivedEpsilonPushforward.{w} (overRingSheaf R U)

/-- The comparison exhibiting `Rε_{U*}` as a right derived functor, at the pinned spelling. -/
abbrev sliceDerivedEpsilonPushforwardUnit :
    (sliceEpsilonPushforward.{w} R U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ sliceDerivedEpsilonPushforward.{w} R U :=
  derivedEpsilonPushforwardUnit.{w} (overRingSheaf R U)

/-- `Rε_{U*}` is a right derived functor of `ε_{U*}`, at the pinned spelling. -/
instance sliceDerivedEpsilonPushforward_isRightDerivedFunctor :
    (sliceDerivedEpsilonPushforward.{w} R U).IsRightDerivedFunctor
      (sliceDerivedEpsilonPushforwardUnit.{w} R U)
      (HomotopyCategory.quasiIso (SheafOfModules.{max u v r w} (overRingSheaf R U))
        (ComplexShape.up ℤ)) :=
  derivedEpsilonPushforward_isRightDerivedFunctor.{w} (overRingSheaf R U)

/-- The comparison exhibiting `Rε_* ⋙ (-|_U)` as a right derived functor of `ε_* ⋙ (-|_U)`. -/
abbrev lerayUnitLeft :
    (epsilonPushforward.{w} R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        ((restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙
        (derivedEpsilonPushforward.{w} R ⋙ derivedRestriction.{w} R.obj U) :=
  Functor.whiskerLeft ((epsilonPushforward.{w} R).mapHomotopyCategory (ComplexShape.up ℤ))
      (restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapDerivedCategoryFactorsh.inv ≫
    Functor.whiskerRight (derivedEpsilonPushforwardUnit.{w} R) (derivedRestriction.{w} R.obj U)

/-- The comparison exhibiting `(-|_U) ⋙ Rε_{U*}` as a right derived functor of
`(-|_U) ⋙ ε_{U*}`. -/
abbrev lerayUnitRight :
    (sheafRestriction.{w} R U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        ((sliceEpsilonPushforward.{w} R U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙
        ((sheafRestriction.{w} R U).mapDerivedCategory ⋙
          sliceDerivedEpsilonPushforward.{w} R U) :=
  Functor.whiskerLeft ((sheafRestriction.{w} R U).mapHomotopyCategory (ComplexShape.up ℤ))
      (sliceDerivedEpsilonPushforwardUnit.{w} R U) ≫
    Functor.whiskerRight (sheafRestriction.{w} R U).mapDerivedCategoryFactorsh.inv
      (sliceDerivedEpsilonPushforward.{w} R U)

/-- The two underived composites `ε_* ⋙ (-|_U)` and `(-|_U) ⋙ ε_{U*}` are one functor, so the
functors they induce on homotopy categories are isomorphic, by an isomorphism whose components
are identities. -/
def htpyComparison :
    (epsilonPushforward.{w} R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapHomotopyCategory
            (ComplexShape.up ℤ) ≅
      (sheafRestriction.{w} R U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (sliceEpsilonPushforward.{w} R U).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso
      (Iso.refl (epsilonPushforward.{w} R ⋙ restrictionFunctor.{v, u, r, max u v r w} R.obj U))
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (sheafRestriction.{w} R U ⋙ sliceEpsilonPushforward.{w} R U))
      (ComplexShape.up ℤ)).symm

/-- The comparison of the two sources of `lerayUnitLeft` and `lerayUnitRight`. -/
def lerayComparison :
    (epsilonPushforward.{w} R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        ((restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) ≅
      (sheafRestriction.{w} R U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        ((sliceEpsilonPushforward.{w} R U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) :=
  Functor.isoWhiskerRight (htpyComparison.{w} R U) DerivedCategory.Qh

/-- `Rε_* ⋙ (-|_U)` is a right derived functor of `ε_* ⋙ (-|_U)`: the comparison of `Rε_*` is
invertible on a K-injective complex, and that of restriction of presheaves of modules is
invertible everywhere, restriction being exact. -/
instance isRightDerivedFunctor_lerayLeft :
    (derivedEpsilonPushforward.{w} R ⋙ derivedRestriction.{w} R.obj U).IsRightDerivedFunctor
      (lerayUnitLeft.{w} R U)
      (HomotopyCategory.quasiIso (SheafOfModules.{max u v r w} R) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.isRightDerivedFunctor_comp_of_kInjectives
    (epsilonPushforward.{w} R) (restrictionFunctor.{v, u, r, max u v r w} R.obj U) _ _ _ _
    (fun I _ => Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ I)
    (fun _ _ => NatIso.isIso_app_of_isIso
      (restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapDerivedCategoryFactorsh.symm.hom _)

/-- `(-|_U) ⋙ Rε_{U*}` is a right derived functor of `(-|_U) ⋙ ε_{U*}`: the comparison of
restriction of sheaves of modules is invertible everywhere, restriction being exact, and that of
`Rε_{U*}` is invertible at the restriction of a K-injective complex, which is again K-injective by
Stacks 08FI. -/
instance isRightDerivedFunctor_lerayRight :
    ((sheafRestriction.{w} R U).mapDerivedCategory ⋙
        sliceDerivedEpsilonPushforward.{w} R U).IsRightDerivedFunctor
      (lerayUnitRight.{w} R U)
      (HomotopyCategory.quasiIso (SheafOfModules.{max u v r w} R) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.isRightDerivedFunctor_comp_of_kInjectives
    (sheafRestriction.{w} R U) (sliceEpsilonPushforward.{w} R U) _ _ _ _
    (fun _ _ => NatIso.isIso_app_of_isIso
      (sheafRestriction.{w} R U).mapDerivedCategoryFactorsh.symm.hom _)
    (fun I hI => by
      have : CochainComplex.IsKInjective
          (((sheafRestriction.{w} R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
        Stacks.Cohomology.Localization.isKInjective_over_freeUniverses.{w} J R U I
      exact Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _
        (((sheafRestriction.{w} R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))

/-- **Restriction to `C/U` commutes with the derived pushforward of the chaotic comparison:**
`(Rε_*K)|_U = Rε_{U*}(K|_U)`.  Both sides are right derived functors of the one functor
`ε_* ⋙ (-|_U) = (-|_U) ⋙ ε_{U*}`, so this is one application of the uniqueness of right derived
functors.

This is the statement of Stacks 0D6G for `ε`.  The tag itself sits on
`Stacks.Cohomology.Localization.derivedPushforwardOverFunctorIso`, which is the same statement for
a morphism of ringed sites; `ε` is the identity functor read between two topologies and is not
presented as one here. -/
def derivedRestrictionPushforwardIso :
    derivedEpsilonPushforward.{w} R ⋙ derivedRestriction.{w} R.obj U ≅
      (sheafRestriction.{w} R U).mapDerivedCategory ⋙
        sliceDerivedEpsilonPushforward.{w} R U :=
  Functor.rightDerivedNatIso _ _ (lerayUnitLeft.{w} R U) (lerayUnitRight.{w} R U)
    (HomotopyCategory.quasiIso (SheafOfModules.{max u v r w} R) (ComplexShape.up ℤ))
    (lerayComparison.{w} R U)

/-- **The defining compatibility of `derivedRestrictionPushforwardIso`:** it carries the one
comparison into the other.  This is what the isomorphism *is*, and it is the handle any
identification of it with something constructed differently has to run on — in particular with
the mate of the derived sheafification square, which is what Stacks 0GZS's hypothesis (2) has to
be fed through.

`lerayComparison` has identity components, both underived composites being one functor; it is
kept in the statement rather than cancelled because the two objects it joins are equal only by an
unfolding performed at a transparency at which the composite stops being type-correct. -/
theorem derivedRestrictionPushforwardIso_fac
    (X : HomotopyCategory (SheafOfModules.{max u v r w} R) (ComplexShape.up ℤ)) :
    (lerayUnitLeft.{w} R U).app X ≫
        (derivedRestrictionPushforwardIso.{w} R U).hom.app (DerivedCategory.Qh.obj X) =
      (lerayComparison.{w} R U).hom.app X ≫ (lerayUnitRight.{w} R U).app X :=
  Functor.rightDerivedNatTrans_app _ _ (lerayUnitLeft.{w} R U) (lerayUnitRight.{w} R U)
    (HomotopyCategory.quasiIso (SheafOfModules.{max u v r w} R) (ComplexShape.up ℤ))
    (lerayComparison.{w} R U).hom X

/-- **The Leray step of the proof of Stacks 0GZS:**
`RΓ(U, Rε_*K) = RΓ(id_U, Rε_{U*}(K|_U))`.  Derived sections over `U` of the derived pushforward of
`K` are the derived sections over the terminal object `id_U` of `C/U` of the derived pushforward on
the localized site of the restriction of `K`.

This is `derivedRestrictionPushforwardIso` whiskered with derived sections over `id_U`, after
`derivedSectionsIso` has rewritten `RΓ(U, -)` on the chaotic side as `RΓ(id_U, -|_U)`. -/
def derivedSectionsPushforwardIso :
    derivedEpsilonPushforward.{w} R ⋙ RGamma.{w} R.obj (Opposite.op U) ≅
      (sheafRestriction.{w} R U).mapDerivedCategory ⋙
        derivedEpsilonPushforward.{w} (overRingSheaf R U) ⋙
          RGamma.{w} (overRingPresheaf R.obj U) (Opposite.op (Over.mk (𝟙 U))) :=
  Functor.isoWhiskerLeft (derivedEpsilonPushforward.{w} R)
      (derivedSectionsIso.{w} R.obj U).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedRestrictionPushforwardIso.{w} R U)
      (RGamma.{w} (overRingPresheaf R.obj U) (Opposite.op (Over.mk (𝟙 U)))) ≪≫
    Functor.associator _ _ _

end Stacks.ModulesOnACategory.ChaoticComparison

end
