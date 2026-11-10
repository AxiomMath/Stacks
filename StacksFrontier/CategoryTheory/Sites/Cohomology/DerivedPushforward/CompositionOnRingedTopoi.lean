module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOfDirectImages
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-!
# Composition of derived pushforwards on ringed topoi

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` and `g : (Sh(D), 𝒪_D) ⟶ (Sh(E), 𝒪_E)` be morphisms of
ringed topoi.  Write `Rf_*`, `Rg_*` and `R(g ∘ f)_*` for right derived functors of the three
degreewise pushforwards of sheaves of modules followed by localization, each presented by a
functor on derived categories together with its canonical comparison and an
`IsRightDerivedFunctor` instance.  The underived pushforward-composition isomorphism
`AlgebraicGeometry.RingedToposSiteHom.pushforwardToposCompIso` and the universal property of
`R(g ∘ f)_*` produce a canonical comparison

`R(g ∘ f)_* ⟶ Rf_* ⋙ Rg_*`

and Stacks 0D6E is the assertion that it is invertible.

This file proves that the comparison is invertible **exactly when** degreewise `f_*` carries
K-injective complexes of `𝒪_C`-modules to complexes that compute `Rg_*`.  That is one
hypothesis, stated on `g`'s comparison alone, and the equivalence is unconditional, so no
argument can avoid it.

## Main definitions

* `Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.pushforwardToDerivedCategory` is
  degreewise pushforward on the homotopy
  category, followed by localization to the derived category.
* `Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.derivedPushforwardCompUnit` is the
  comparison from degreewise pushforward
  along `g ∘ f` to the composite of the two derived pushforwards.
* `Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.derivedPushforwardComparison` is the
  induced canonical comparison
  `R(g ∘ f)_* ⟶ Rf_* ⋙ Rg_*`.
* `Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.PushforwardComputesDerived` is the
  property that `g_*(f_* I) ⟶ Rg_*(f_* I)` is
  invertible for every K-injective complex `I` of `𝒪_C`-modules.

## Main results

* `Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.isRightDerivedFunctor_comp`: under
  `PushforwardComputesDerived`, the composite
  `Rf_* ⋙ Rg_*` together with `derivedPushforwardCompUnit` is a right derived functor of
  degreewise pushforward along `g ∘ f`.
* `Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.isIso_derivedPushforwardComparison`:
  under `PushforwardComputesDerived`, the
  canonical comparison is an isomorphism.
* `Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.derivedPushforwardCompIso`: the resulting
  `Rf_* ⋙ Rg_* ≅ R(g ∘ f)_*`.
* `Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.isIso_derivedPushforwardComparison_iff`:
  the converse too, so that
  `PushforwardComputesDerived` is *equivalent* to the composition formula and is therefore the
  exact remaining content, not a convenient weakening.
* `Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.pushforwardComputesDerived_of_isIso`,
  `pushforwardComputesDerived_of_isKInjective`: two sufficient conditions, which
  exhibit the hypothesis as satisfiable.

## Implementation notes

*Why the hypothesis is not discharged here.*  Both `R(g ∘ f)_*` and `Rf_* ⋙ Rg_*` are right
derived functors, of *different* functors on the homotopy category: the first of
`K(f_*) ⋙ K(g_*) ⋙ Q`, the second — by absoluteness of the derived pushforward — of
`K(f_*) ⋙ Q ⋙ Rg_*`.  The map between those two sources is `αg` whiskered with `K(f_*)`, and
`PushforwardComputesDerived` says precisely that this map is invertible at the K-injective
complexes.  The source's own proof of Stacks 0D6E gets that input from uniqueness of adjoints
applied to `Lf^* ⋙ Lg^* = L(g ∘ f)^*`, which is Stacks 0D6D, together with the adjunction
`Lf^* ⊣ Rf_*` of Stacks 07A6.  In this tree the 07A6 adjunction
(`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackPushforwardAdjunction`) is
  relative to a resolving datum whose
remaining input at the K-flat class is
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat` (Stacks 05VD),
and that input is now concluded, by
`AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlatUniv`; Stacks 0D6D is likewise
available, as `Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso`.  So
the adjunction route *is* available and the hypothesis carried below is dischargeable.  It is
nevertheless still carried here, because the discharge touches every statement in this cluster
and was deferred rather than taken; `isIso_derivedPushforwardComparison_iff` records that
nothing is lost by carrying it, since it *is* the statement.  The ringed-space analogue of the
whole package, where the corresponding pullback composition and adjunctions were already
available, has the same shape, so the discharge is a single application at each site.

*One spelling for the comparison at an object.*  `derivedPushforwardCompUnit_app` evaluates the
three-fold composite once and for all, in term mode, and every proof below works against that
single spelling.  The components of the whiskerings are `rfl`, but a tactic looking at the
unevaluated composite cannot see through the definition.

*The abbreviation must not be used in the application position.*  Passing
`pushforwardToDerivedCategory f` as the functor argument of
`Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective` or of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isRightDerivedFunctor_of_isIso_app_isKInjective`
  exhausts the heartbeat budget
in `whnf`, while `f.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
DerivedCategory.Qh` — the same term, reducibly — costs a few seconds.  Both applications below
are therefore written out; the abbreviation is kept only where it appears in a *statement*,
which is where it is readable and harmless.

*The universe narrowing is inherited, not chosen here.*  Stacks 0D6E's statement has three
independent pairs of site universes and three independent section universes.  The section
universe `w` is already shared by the three ringed topoi in
`AlgebraicGeometry.RingedToposSiteHom`, hence in `pushforwardToposCompIso`; and the site
universes are collapsed onto `w` as well because
  `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.exists_quasiIso_isKInjective`,
which supplies the K-injective resolutions this file runs on, is stated for
`AlgebraicGeometry.RingedTopos.{w, w, w}`.  That collapse is not a convenience of
Tag 07A6 either — `SheafOfModules.isGrothendieckAbelianU`, which is what makes the category of
modules Grothendieck abelian, requires `Category.{u, u} C` and forces the section universe to
dominate the site universe.  The three derived-category universes `dX`, `dY`, `dZ` are left
independent, as in the source statement.

*No sheafification instance is omitted.*  Every statement below references the
`HasSheafify _.J AddCommGrpCat.{w}` section variable of all three sites, so none of the three can
be dropped with `omit`.  Whether they are referenced depends on the import surface of
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction` and not on anything here: that file takes
Tag 06YS in its `ofSize` form and imports
`StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize`.  The dependency is carried
explicitly here rather than left to an instance arriving through an unrelated file.

## References

* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi

universe w dX dY dZ

section Defs

variable {X Y Z : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Z.J AddCommGrpCat.{w}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Degreewise pushforward of sheaves of modules on the unbounded homotopy category, followed
by localization to the derived category. -/
noncomputable abbrev pushforwardToDerivedCategory
    [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (f : RingedToposSiteHom X Y) :
    HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  f.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The comparison from degreewise pushforward along `g ∘ f` to the composite of the derived
pushforwards. -/
noncomputable def derivedPushforwardCompUnit
    [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    [HasDerivedCategory.{dZ} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))]
    (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)
    (Rf : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (Rg : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (αf : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
    (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg) :
    pushforwardToDerivedCategory (g.comp f) ⟶ DerivedCategory.Qh ⋙ (Rf ⋙ Rg) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (RingedToposSiteHom.pushforwardToposCompIso f g).symm (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    Functor.whiskerLeft
      (f.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)) αg ≫
    Functor.whiskerRight αf Rg

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The value of `derivedPushforwardCompUnit` at an object of the homotopy category, written out
as a composite of three maps.  Each whiskering contributes its component on the nose. -/
theorem derivedPushforwardCompUnit_app
    [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    [HasDerivedCategory.{dZ} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))]
    (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)
    (Rf : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (Rg : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (αf : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
    (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg)
    (K : HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) :
    (derivedPushforwardCompUnit f g Rf Rg αf αg).app K =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
            (RingedToposSiteHom.pushforwardToposCompIso f g).symm
              (ComplexShape.up ℤ)).inv.app K) ≫
        αg.app ((f.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        Rg.map (αf.app K) :=
  rfl

/-- The property that degreewise pushforward along `f` carries the K-injective complexes of
`𝒪_X`-modules to complexes computing the derived pushforward along `g`. -/
abbrev PushforwardComputesDerived
    [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    [HasDerivedCategory.{dZ} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))]
    (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)
    (Rg : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg) : Prop :=
  ∀ I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
    I.IsKInjective →
    IsIso (αg.app ((f.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj I)))

end Defs

section Main

variable {X Y Z : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Z.J AddCommGrpCat.{w}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dZ} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))]
  (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)
  (Rf : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  (Rg : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
  (Rh : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
  (αf : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
  (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg)
  (αh : pushforwardToDerivedCategory (g.comp f) ⟶ DerivedCategory.Qh ⋙ Rh)

/-- The canonical comparison from a derived pushforward along `g ∘ f` to the composite of
derived pushforwards along `f` and `g`, obtained from the universal property of the former. -/
noncomputable def derivedPushforwardComparison
    [Rh.IsRightDerivedFunctor αh
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))] :
    Rh ⟶ Rf ⋙ Rg :=
  Rh.rightDerivedDesc αh
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) _
    (derivedPushforwardCompUnit f g Rf Rg αf αg)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A K-injective complex computes any derived pushforward: the comparison of a right derived
functor of degreewise pushforward is invertible there. -/
theorem isIso_app_of_isKInjective
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hI : I.IsKInjective) :
    IsIso (αf.app ((HomotopyCategory.quotient
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      w, dY, dX, w + 1, w + 1, w + 1}
      (f.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.exists_quasiIso_isKInjective X)).2
    DerivedCategory.Qh Rf αf I hI

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- A derived pushforward along `g` whose comparison is already invertible imposes no condition
at all: every complex computes it.  This is the case of a `g` along which degreewise pushforward
is exact, and it exhibits `PushforwardComputesDerived` as a satisfiable hypothesis. -/
theorem pushforwardComputesDerived_of_isIso (h : IsIso αg) :
    PushforwardComputesDerived f g Rg αg :=
  have := h
  fun _ _ => NatIso.isIso_app_of_isIso αg _

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- If degreewise pushforward along `f` preserves K-injectivity, then it carries K-injective
complexes to complexes computing the derived pushforward along `g`. -/
theorem pushforwardComputesDerived_of_isKInjective
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))]
    (h : ∀ I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      I.IsKInjective →
      CochainComplex.IsKInjective
        ((f.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    PushforwardComputesDerived f g Rg αg :=
  fun I hI => isIso_app_of_isKInjective g Rg αg _ (h I hI)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The composite of two derived pushforwards is a derived pushforward along the composite.**
Under `PushforwardComputesDerived`, the composite `Rf_* ⋙ Rg_*`, with the comparison
`derivedPushforwardCompUnit`, is a right derived functor of degreewise pushforward along
`g ∘ f`. -/
theorem isRightDerivedFunctor_comp
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))]
    (h : PushforwardComputesDerived f g Rg αg) :
    (Rf ⋙ Rg).IsRightDerivedFunctor (derivedPushforwardCompUnit f g Rf Rg αf αg)
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)) := by
  refine
    isRightDerivedFunctor_of_isIso_app_isKInjective.{
      w, dZ, dX, w + 1, w + 1, w + 1}
    ((g.comp f).pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.exists_quasiIso_isKInjective X)
    DerivedCategory.Qh _ _ fun I hI => ?_
  rw [derivedPushforwardCompUnit_app]
  have h₂ := h I hI
  have h₃ := isIso_app_of_isKInjective f Rf αf I hI
  infer_instance

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Stacks 0D6E, the composition formula.**  Under `PushforwardComputesDerived`, the canonical
comparison from a derived pushforward along `g ∘ f` to the composite of derived pushforwards
along `f` and `g` is an isomorphism. -/
theorem isIso_derivedPushforwardComparison
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))]
    [Rh.IsRightDerivedFunctor αh
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))]
    (h : PushforwardComputesDerived f g Rg αg) :
    IsIso (derivedPushforwardComparison f g Rf Rg Rh αf αg αh) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc Rh αh
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))
      (Rf ⋙ Rg) (derivedPushforwardCompUnit f g Rf Rg αf αg)).1
    (isRightDerivedFunctor_comp f g Rf Rg αf αg h)

/-- The natural isomorphism `Rf_* ⋙ Rg_* ≅ R(g ∘ f)_*`. -/
noncomputable def derivedPushforwardCompIso
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))]
    [Rh.IsRightDerivedFunctor αh
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))]
    (h : PushforwardComputesDerived f g Rg αg) :
    Rf ⋙ Rg ≅ Rh :=
  haveI := isIso_derivedPushforwardComparison f g Rf Rg Rh αf αg αh h
  (asIso (derivedPushforwardComparison f g Rf Rg Rh αf αg αh)).symm

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The hypothesis is the whole content of the composition formula.**  The canonical comparison
is an isomorphism exactly when degreewise pushforward along `f` carries K-injective complexes to
complexes computing the derived pushforward along `g`. -/
theorem isIso_derivedPushforwardComparison_iff
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))]
    [Rh.IsRightDerivedFunctor αh
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))] :
    IsIso (derivedPushforwardComparison f g Rf Rg Rh αf αg αh) ↔
      PushforwardComputesDerived f g Rg αg := by
  refine ⟨fun hiso I hI => ?_, isIso_derivedPushforwardComparison f g Rf Rg Rh αf αg αh⟩
  have hh := isIso_app_of_isKInjective (g.comp f) Rh αh I hI
  have h₃ := isIso_app_of_isKInjective f Rf αf I hI
  have hfac := Functor.rightDerived_fac_app Rh αh
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    (Rf ⋙ Rg) (derivedPushforwardCompUnit f g Rf Rg αf αg)
    ((HomotopyCategory.quotient (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)).obj I)
  have hdesc : IsIso (Rh.rightDerivedDesc αh
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))
      (Rf ⋙ Rg) (derivedPushforwardCompUnit f g Rf Rg αf αg)) := hiso
  have hunit : IsIso ((derivedPushforwardCompUnit f g Rf Rg αf αg).app
      ((HomotopyCategory.quotient (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj I)) := by
    rw [← hfac]
    infer_instance
  rw [derivedPushforwardCompUnit_app] at hunit
  simpa using hunit

end Main

end Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi

end
