module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackAlongRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOfDirectImages
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of derived pullbacks along morphisms of ringed topoi

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` and `g : (Sh(D), 𝒪_D) ⟶ (Sh(E), 𝒪_E)` be morphisms of
ringed topoi.  Stacks 0D6D asserts that

`Lf^* ∘ Lg^* = L(g ∘ f)^*`

as functors `D(𝒪_E) ⟶ D(𝒪_C)`.  This file constructs the canonical comparison between the two
and proves it invertible, with no hypothesis beyond the two morphisms being morphisms of ringed
topoi — that is, beyond the morphism-of-sites property of the two underlying continuous functors.

## Main definitions

* `AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso` is the underived comparison
  `g^* ⋙ f^* ≅ (g ∘ f)^*`, obtained from the direct-image composition isomorphism of Stacks 0D6E
  by uniqueness of left adjoints.
* `pullbackOnHomotopyCompIso` is the same isomorphism on the unbounded homotopy categories.
* `derivedPullbackCompCounit` is the comparison from `Lg^* ⋙ Lf^*` to degreewise pullback along
  the composite.
* `derivedPullbackCompComparison` is the induced canonical comparison `Lg^* ⋙ Lf^* ⟶ L(g ∘ f)^*`.
* `derivedPullbackCompIso` is the resulting natural isomorphism.

## Main results

* `isKFlat_pullbackOnHomotopy`: degreewise pullback along `g` carries the class of K-flat
  complexes with flat terms on `E` into the same class on `D`.  This is Stacks 0G7E, read on the
  homotopy category.
* `isIso_derivedPullbackComparison_app_of_isKFlat`: the canonical comparison `Lf^* ⟶ f^*` is
  invertible at every K-flat complex with flat terms.
* `isLeftDerivedFunctor_derivedPullbackComp`: the composite `Lg^* ⋙ Lf^*`, with
  `derivedPullbackCompCounit`, is a left derived functor of degreewise pullback along `g ∘ f`.
* `isIso_derivedPullbackCompComparison`: **Stacks 0D6D**, the composition formula, and
  `derivedPullbackCompIso` the same as a natural isomorphism.
* `derivedPullbackCompComparison_comp_derivedPullbackComparison` and its evaluated form
  `derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app`: the comparison is
  the canonical one, being the unique map whose composite with the Stacks 06YY comparison for
  `g ∘ f` is `derivedPullbackCompCounit`.

## Implementation notes

*Why the composite is the derived pullback along the composite.*  The source argument is: choose
a K-flat complex with flat terms representing an object of `D(𝒪_E)`; its degreewise pullback
along `g` is again such a complex (Stacks 0G7E), so degreewise pullback computes both `Lg^*` on
the first and `Lf^*` on the second, and `f^*(g^*K) = (g ∘ f)^*K` on the nose.  Formally this
says that `Lg^* ⋙ Lf^*` is a left derived functor of `K((g ∘ f)^*) ⋙ Q` — which is what
`isLeftDerivedFunctor_derivedPullbackComp` proves, by
`CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions` at the
K-flat class — and the composition formula is then uniqueness of left derived functors.

*The morphism-of-sites hypotheses.*  `AlgebraicGeometry.RingedToposSiteHom` asks only that the
underlying functor be *continuous*; exactness of the inverse image is not a field of it, and it
is what makes the morphism a morphism of ringed *topoi*.  Stacks 0G7E is false without it, so
both `hmosf` and `hmosg` are carried, exactly as in the Stacks 06YY and 07A6 statements
of this chain.  The hypothesis for the composite is not a third assumption: it is
`CategoryTheory.Functor.IsMorphismOfSites.comp`, which is Stacks 03CC.

*Why nothing is parametrized over the derived functors.*  The ringed-space analogue
`Stacks.DerivedPullback.Composition` carries the three derived pullbacks and their comparisons
as parameters, because at the time it was written the derived pullback did not exist
unconditionally.  Here it does
(`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy`), so
the statements are about the canonical `derivedPullback` of Stacks 06YY.  The
`HasLeftDerivedFunctor` arguments are instance arguments of that functor, not residual
hypotheses: they are `Prop` classes, discharged for every morphism of ringed topoi, and by proof
irrelevance `derivedPullback f` is the same functor whichever witness is supplied.

*One spelling for the comparison at an object.*  `derivedPullbackCompCounit_app` evaluates the
threefold composite once, in term mode; the whiskerings contribute their components on the nose,
but a tactic looking at the unevaluated composite cannot see through them.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 03CC](https://stacks.math.columbia.edu/tag/03CC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace AlgebraicGeometry.RingedToposSiteHom

universe u

variable {X Y Z : RingedTopos.{u, u, u}}

/-- **Stacks 03CC** for the underlying continuous functors of two composable morphisms of ringed
topoi: the composite is again a morphism of sites, so a composite of morphisms of ringed topoi is
again a morphism of ringed topoi.  This is why the composition formula for derived pullback needs
no hypothesis on `g.comp f`. -/
theorem isMorphismOfSites_comp_u (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)
    (hmosf : f.u.IsMorphismOfSites Y.J X.J) (hmosg : g.u.IsMorphismOfSites Z.J Y.J) :
    (g.comp f).u.IsMorphismOfSites Z.J X.J :=
  hmosg.comp hmosf

variable
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The underived half of Stacks 0D6D.**  The inverse image of sheaves of modules along a
composite of morphisms of ringed topoi is canonically isomorphic to the composite of the two
inverse images.

Pullback of modules is defined as an abstract left adjoint, so there is no sectionwise formula
to compare: the isomorphism is produced from the direct-image composition isomorphism
`pushforwardToposCompIso` by uniqueness of left adjoints. -/
noncomputable def pullbackToposCompIso (f : RingedToposSiteHom X Y)
    (g : RingedToposSiteHom Y Z) :
    g.pullbackTopos ⋙ f.pullbackTopos ≅ (g.comp f).pullbackTopos :=
  Adjunction.leftAdjointCompIso g.pullbackPushforwardAdjunctionTopos
    f.pullbackPushforwardAdjunctionTopos (g.comp f).pullbackPushforwardAdjunctionTopos
    (pushforwardToposCompIso f g).symm

end AlgebraicGeometry.RingedToposSiteHom

namespace Stacks.Cohomology.DerivedPullbackCompositionOnTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)

/-- The pullback-composition isomorphism of Stacks 0D6D, read on the unbounded homotopy
categories of complexes of sheaves of modules. -/
def pullbackOnHomotopyCompIso :
    g.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        f.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (g.comp f).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (RingedToposSiteHom.pullbackToposCompIso f g)
    (ComplexShape.up ℤ)

section Counit

variable
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ))]

/-- The comparison from the composite of the derived pullbacks along `g` and `f` to degreewise
pullback along `g ∘ f`: the comparison for `Lg^*`, then the comparison for `Lf^*`, then the
pullback-composition isomorphism.

This is the datum through which the universal property of `L(g ∘ f)^*` produces the canonical
comparison of Stacks 0D6D. -/
def derivedPullbackCompCounit :
    DerivedCategory.Qh ⋙ (derivedPullback g ⋙ derivedPullback f) ⟶
      pullbackOnHomotopy (g.comp f) :=
  Functor.whiskerRight (derivedPullbackComparison g) (derivedPullback f) ≫
    Functor.whiskerLeft (g.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedPullbackComparison f) ≫
    Functor.whiskerRight (pullbackOnHomotopyCompIso f g).hom DerivedCategory.Qh

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The value of `derivedPullbackCompCounit` at a complex, written out as a composite of its
three factors.  Each whiskering contributes its component on the nose, so this holds by
definition; it is recorded once so that the three factors of the Stacks 0D6D comparison can be
reasoned about separately. -/
theorem derivedPullbackCompCounit_app
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ)) :
    (derivedPullbackCompCounit f g).app K =
      (derivedPullback f).map ((derivedPullbackComparison g).app K) ≫
        (derivedPullbackComparison f).app
          ((g.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso f g).hom.app K) :=
  rfl

end Counit

section KFlat

/-- **Stacks 0G7E on the homotopy category.**  Degreewise pullback along `g` carries the class of
K-flat complexes of `𝒪_E`-modules with flat terms into the same class for `𝒪_D`.

Nothing happens on passage to the homotopy category: the underlying complex of `K(g^*) K` is
`g^*` of the underlying complex of `K`.  The K-flatness clause is
`Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex`, whose three inputs —
Stacks 05VD, 0G6R and 0G7C — are all concluded in this tree; the flat-terms clause is Stacks
05VD alone. -/
theorem isKFlat_pullbackOnHomotopy (hmosg : g.u.IsMorphismOfSites Z.J Y.J)
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ))
    (hK : IsKFlat (Y := Z) K) :
    IsKFlat (Y := Y)
      ((g.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := by
  refine ⟨?_, ?_⟩
  · exact (Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O _).1
      (Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex g hmosg
        (RingedToposSiteHom.pullbackPreservesIsFlat g)
        (RingedToposSiteHom.pullbackPreservesShortExact g)
        (Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat Z) K.as
        ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Z.O K.as).2 hK.1) hK.2)
  · exact fun i => Stacks.Sheaves.DerivedPullback.KFlatPullback.isFlat_pullbackComplex_X g hmosg
      (RingedToposSiteHom.pullbackPreservesIsFlat g) K.as hK.2 i

variable
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

/-- The canonical comparison `Lf^* ⟶ f^*` of Stacks 06YY is invertible at every K-flat complex of
`𝒪_D`-modules with flat terms.

This is `CategoryTheory.LeftDerivedByResolutions.isIso_app_of_resolutions` at the resolving datum
of Stacks 06YS and Stacks 06YY, and it is the statement that such a complex computes `Lf^*`. -/
theorem isIso_derivedPullbackComparison_app_of_isKFlat (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (M : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))
    (hM : IsKFlat (Y := Y) M) :
    IsIso ((derivedPullbackComparison f).app M) :=
  LeftDerivedByResolutions.isIso_app_of_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))
    (IsKFlat (Y := Y))
    (hasResolutions_isKFlat (Y := Y))
    (pullbackOnHomotopy f)
    (fun s hs hK hM =>
      Stacks.Cohomology.DerivedPullbackOnRingedTopoi.pullbackInvertsQuasiIso_isKFlat f hmosf s hs
        hK hM)
    DerivedCategory.Qh (derivedPullback f) (derivedPullbackComparison f) M hM

end KFlat

section Main

variable
  (hmosf : f.u.IsMorphismOfSites Y.J X.J)
  (hmosg : g.u.IsMorphismOfSites Z.J Y.J)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ))]

omit [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (ComplexShape.up ℤ))] in
include hmosf hmosg in
/-- The comparison `derivedPullbackCompCounit` is invertible at a K-flat complex with flat terms.

Of its three factors the first is the image under `Lf^*` of the comparison for `Lg^*`, the second
is the comparison for `Lf^*` at the degreewise pullback along `g`, which is again K-flat with
flat terms by Stacks 0G7E, and the third is the image of an isomorphism. -/
theorem isIso_derivedPullbackCompCounit_app
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ))
    (hK : IsKFlat (Y := Z) K) :
    IsIso ((derivedPullbackCompCounit f g).app K) := by
  rw [derivedPullbackCompCounit_app]
  have h₁ := isIso_derivedPullbackComparison_app_of_isKFlat g hmosg K hK
  have h₂ := isIso_derivedPullbackComparison_app_of_isKFlat f hmosf _
    (isKFlat_pullbackOnHomotopy g hmosg K hK)
  infer_instance

omit [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (ComplexShape.up ℤ))] in
include hmosf hmosg in
/-- **The composite of two derived pullbacks is a derived pullback along the composite.**  The
composite `Lg^* ⋙ Lf^*`, with the comparison `derivedPullbackCompCounit`, is a left derived
functor of degreewise pullback along `g ∘ f` followed by localization.

A comparison invertible on a class that resolves every complex, and whose quasi-isomorphisms the
underived functor inverts, exhibits its functor as a left derived functor; the class is the
K-flat complexes with flat terms, resolving by Stacks 06YS and inverted by Stacks 06YY. -/
theorem isLeftDerivedFunctor_derivedPullbackComp :
    (derivedPullback g ⋙ derivedPullback f).IsLeftDerivedFunctor
      (derivedPullbackCompCounit f g)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
        (ComplexShape.up ℤ)) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ))
    (IsKFlat (Y := Z))
    (hasResolutions_isKFlat (Y := Z))
    (pullbackOnHomotopy (g.comp f))
    (fun s hs hK hM =>
      Stacks.Cohomology.DerivedPullbackOnRingedTopoi.pullbackInvertsQuasiIso_isKFlat (g.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg) s hs hK hM)
    DerivedCategory.Qh (derivedPullback g ⋙ derivedPullback f)
    (derivedPullbackCompCounit f g)
    (fun K hK => isIso_derivedPullbackCompCounit_app f g hmosf hmosg K hK)

/-- The canonical comparison `Lg^* ⋙ Lf^* ⟶ L(g ∘ f)^*` of Stacks 0D6D, obtained from the
universal property of the derived pullback along the composite.

It is characterized by `derivedPullbackCompComparison_comp_derivedPullbackComparison` below:
postcomposing it with the comparison of `L(g ∘ f)^*` returns `derivedPullbackCompCounit`. -/
def derivedPullbackCompComparison :
    derivedPullback g ⋙ derivedPullback f ⟶ derivedPullback (g.comp f) :=
  (derivedPullback (g.comp f)).leftDerivedLift (derivedPullbackComparison (g.comp f))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ)) _
    (derivedPullbackCompCounit f g)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The comparison of Stacks 0D6D is the canonical one.**  Postcomposing it with the
comparison `L(g ∘ f)^* ⟶ (g ∘ f)^*` of Stacks 06YY returns `derivedPullbackCompCounit`, and by
`CategoryTheory.Functor.leftDerived_ext` this determines it uniquely.

Nothing beyond the universal property of `L(g ∘ f)^*` is used, so this holds whether or not the
comparison is invertible. -/
@[reassoc]
theorem derivedPullbackCompComparison_comp_derivedPullbackComparison :
    Functor.whiskerLeft DerivedCategory.Qh (derivedPullbackCompComparison f g) ≫
        derivedPullbackComparison (g.comp f) =
      derivedPullbackCompCounit f g :=
  (derivedPullback (g.comp f)).leftDerived_fac (derivedPullbackComparison (g.comp f))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ)) _
    (derivedPullbackCompCounit f g)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The characterization of the Stacks 0D6D comparison at a complex, with the three factors of
`derivedPullbackCompCounit` written out.  This is the form a base-change computation consumes:
it says that on a complex, the comparison followed by the 06YY comparison for `g ∘ f` is the
06YY comparison for `g`, then the one for `f`, then the underived composition isomorphism. -/
theorem derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ)) :
    (derivedPullbackCompComparison f g).app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackComparison (g.comp f)).app K =
      (derivedPullback f).map ((derivedPullbackComparison g).app K) ≫
        (derivedPullbackComparison f).app
          ((g.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso f g).hom.app K) :=
  ((derivedPullback (g.comp f)).leftDerived_fac_app (derivedPullbackComparison (g.comp f))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
        (ComplexShape.up ℤ)) _
      (derivedPullbackCompCounit f g) K).trans
    (derivedPullbackCompCounit_app f g K)

include hmosf hmosg in
/-- **Stacks 0D6D.**  For composable morphisms of ringed topoi `f` and `g`, the canonical
comparison from the composite of the derived pullbacks to the derived pullback along `g ∘ f` is
an isomorphism, so `Lf^* ∘ Lg^* = L(g ∘ f)^*`.

Both functors are left derived functors of degreewise pullback along `g ∘ f`, and a map between
left derived functors induced by the universal property is invertible exactly then. -/
@[stacks 0D6D]
theorem isIso_derivedPullbackCompComparison :
    IsIso (derivedPullbackCompComparison f g) :=
  ((derivedPullback (g.comp f)).isLeftDerivedFunctor_iff_isIso_leftDerivedLift
      (derivedPullbackComparison (g.comp f))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
        (ComplexShape.up ℤ))
      (derivedPullback g ⋙ derivedPullback f) (derivedPullbackCompCounit f g)).1
    (isLeftDerivedFunctor_derivedPullbackComp f g hmosf hmosg)

include hmosf hmosg in
/-- **Stacks 0D6D as a natural isomorphism** `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*`, obtained by inverting
the canonical comparison. -/
@[stacks 0D6D "as a natural isomorphism"]
def derivedPullbackCompIso :
    derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (g.comp f) :=
  have := isIso_derivedPullbackCompComparison f g hmosf hmosg
  asIso (derivedPullbackCompComparison f g)

include hmosf hmosg in
/-- The underlying map of `derivedPullbackCompIso` is the canonical comparison of Stacks 0D6D,
so the characterization lemmas above apply to it. -/
@[simp]
theorem derivedPullbackCompIso_hom :
    (derivedPullbackCompIso f g hmosf hmosg).hom = derivedPullbackCompComparison f g :=
  rfl

end Main

end

end Stacks.Cohomology.DerivedPullbackCompositionOnTopoi

end
