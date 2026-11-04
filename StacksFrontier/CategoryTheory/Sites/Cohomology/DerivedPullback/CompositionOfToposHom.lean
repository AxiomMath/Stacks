module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of derived pullbacks along morphisms of ringed topoi

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` and `g : (Sh(D), 𝒪_D) ⟶ (Sh(E), 𝒪_E)` be morphisms of
ringed topoi in the sense of Stacks 01D3, part (2) — a morphism of the underlying topoi together
with a map `𝒪_E ⟶ g_*𝒪_D` — and let `g ∘ f` be their composite. Stacks 0D6D asserts that

`Lf^* ∘ Lg^* = L(g ∘ f)^*`

as functors `D(𝒪_E) ⟶ D(𝒪_C)`. This module constructs the canonical comparison between the two
and proves it invertible, with **no hypothesis whatsoever** beyond the two morphisms of ringed
topoi — in particular with no morphism-of-sites condition, which the ringed-site statement of
this chain carries and a `AlgebraicGeometry.RingedToposHom` cannot supply.

The argument is the one of the source. A K-flat complex of `𝒪_E`-modules with flat terms
computes `Lg^*`; its degreewise pullback along `g` is again such a complex (Stacks 0G7E), so it
computes `Lf^*`; and the two degreewise pullbacks compose up to the underived compositor of
Stacks 03D6. Hence `Lg^* ⋙ Lf^*`, with the comparison `derivedPullbackCompCounit`, is a left
derived functor of degreewise pullback along `g ∘ f`, and the comparison between two left
derived functors of one functor, induced by the universal property, is invertible exactly then.

## Main definitions

* `pullbackMapHomotopyCompIso` is the underived compositor `g^* ⋙ f^* ≅ (g ∘ f)^*` of
  Stacks 03D6, read on the unbounded homotopy categories.
* `derivedPullbackCompCounit` is the comparison from `Lg^* ⋙ Lf^*` to degreewise pullback along
  the composite.
* `derivedPullbackCompComparison` is the induced canonical comparison `Lg^* ⋙ Lf^* ⟶ L(g ∘ f)^*`.
* `derivedPullbackCompIso` is the resulting natural isomorphism.

## Main results

* `isIso_derivedPullbackComparison_app_isKFlat`: the canonical comparison `Lf^* ⟶ f^*` of
  Stacks 06YY is invertible at every K-flat complex with flat terms, i.e. such a complex
  computes `Lf^*`.
* `pullbackMapHomotopyCompIso`, `derivedPullbackCompCounit` and
  `derivedPullbackCompComparison` are stated for three ringed topoi at nine free universes;
  the invertibility results below are stated at `AlgebraicGeometry.RingedTopos.{u, u, u}`, for
  the reason recorded in the implementation notes.
* `isLeftDerivedFunctor_derivedPullbackComp`: the composite `Lg^* ⋙ Lf^*`, with
  `derivedPullbackCompCounit`, is a left derived functor of degreewise pullback along `g ∘ f`.
* `isIso_derivedPullbackCompComparison`: **Stacks 0D6D**, the composition formula, and
  `derivedPullbackCompIso` the same as a natural isomorphism.
* `derivedPullbackCompComparison_comp_derivedPullbackComparison` and its evaluated form
  `derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app`: the comparison is the
  canonical one, being the unique map whose composite with the Stacks 06YY comparison for
  `g ∘ f` is `derivedPullbackCompCounit`.

## Implementation notes

*Why this is not the ringed-site statement.* `Stacks.Cohomology.DerivedPullbackCompositionOnTopoi`
proves Stacks 0D6D for a `AlgebraicGeometry.RingedToposSiteHom` — a morphism of ringed topoi
whose geometric datum is a *continuous functor between the underlying sites* — and carries two
`CategoryTheory.Functor.IsMorphismOfSites` hypotheses on those functors, because the K-flatness
and exactness inputs it uses are stated for a morphism of sites. A
`AlgebraicGeometry.RingedToposHom` has no such functor, so that statement does not apply to one
and the passage is not a widening of universes. What makes the present file possible is that
both inputs are now available for an arbitrary morphism of ringed topoi and with no side
condition:
`Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy` for
Stacks 0G7E and `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat`
for the exactness clause of Stacks 06YY. Together with Stacks 06YS, which mentions no morphism
at all, they make the resolving datum unconditional, and with it the whole chain below.

*Why the two developments are not one.* The two pullback functors are genuinely different
constructions: the ringed-site one is `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`, an
abstract left adjoint of the pushforward along the continuous functor, while the present one is
`AlgebraicGeometry.RingedToposHom.pullbackModules`, the extension of scalars along the structure
map of an arbitrary morphism of topoi. So `derivedPullback` below is a different functor from
the one the ringed-site file derives, not the same one at greater generality, and the statements
cannot be merged by generalising a variable.

*The two sections and why they differ in universe generality.* Section `Comparison` builds the
underived compositor, the counit `derivedPullbackCompCounit` and the canonical comparison
`derivedPullbackCompComparison`, together with the two factorization lemmas that characterize
it, for three ringed topoi with **all nine of their universes free and unrelated**: the
construction uses only the universal property of a left derived functor and the compositor of
Stacks 03D6, both of which are available there. It carries the three existence instances of the
derived pullbacks, which at free universes are genuine hypotheses, exactly as in the
ringed-site file.

Section `Main` proves the invertibility, and is restricted to
`AlgebraicGeometry.RingedTopos.{u, u, u}`. The restriction comes from the two inputs and not
from the composition argument: it comes from **two** of the three inputs, Stacks 0G7E
(`Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy`) and the
exactness clause of Stacks 06YY
(`Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat`), which are
stated with the site and the module universes equal. The third, Stacks 06YS
(`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat`), is **no longer
narrowed**: it and the class it resolves are stated at independent universes and do reach a
target above the module universe. So a consumer whose ringed topoi are at unequal universes —
the small étale ringed topos of an algebraic space, which is
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`, is the case this chain meets — already has the
comparison and the resolutions, and still needs those two inputs above the module universe
before it has the invertibility. Nothing about the argument below changes when they arrive.

*Why nothing is parametrized over the derived functors in section `Main`.* At equal universes
the derived pullback exists along every morphism of ringed topoi
(`Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy`), so the
statements there are about the canonical `derivedPullback` of Stacks 06YY with no residual
hypothesis. That existence is a `Prop`-valued class, made available as a local instance; by
proof irrelevance `derivedPullback f` is the same functor whichever witness is supplied.

*The simplicial analogue.* `CategoryTheory.SimplicialSiteSituation.derivedTransitionCompIso`
proves the same formula for the transition morphisms of a simplicial-site situation. It is not
an instance of this file: there the transition of a composite simplex map is not the composite
of the two transitions, but agrees with it only up to the direct-image compositor of
Stacks 09WE, so the three-morphism form of the underived compositor is needed there. Here the
composite is `AlgebraicGeometry.RingedToposHom.comp` on the nose and the strict compositor
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso` of Stacks 03D6 applies.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)
open Stacks.Cohomology.DerivedPullbackOfToposHom

namespace Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe v u w v' u' w' v'' u'' w''

attribute [local instance] HasDerivedCategory.standard

noncomputable section

section Comparison

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)

/-- **The underived half of Stacks 0D6D**, read on the unbounded homotopy categories: the
compositor `g^* ⋙ f^* ≅ (g ∘ f)^*` of degreewise pullbacks of complexes of sheaves of modules
along a composite of morphisms of ringed topoi.

Nothing happens on passage to complexes: it is
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso`, the pseudo-functoriality of Stacks
03D6, applied degreewise. -/
def pullbackMapHomotopyCompIso :
    DerivedPushforward.pullbackMapHomotopy g ⋙ DerivedPushforward.pullbackMapHomotopy f ≅
      DerivedPushforward.pullbackMapHomotopy (g.comp f) :=
  Functor.mapHomotopyCategoryCompIso (RingedToposHom.pullbackModulesCompIso f g).symm
    (ComplexShape.up ℤ)

section Counit

variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor (quasiIsoTarget (Y := Y))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor (quasiIsoTarget (Y := Z))]

/-- The comparison from the composite of the derived pullbacks along `g` and `f` to degreewise
pullback along `g ∘ f`: the comparison for `Lg^*`, pushed forward by `Lf^*`; then the comparison
for `Lf^*` at the degreewise pullback along `g`; then the underived compositor.

This is the datum through which the universal property of `L(g ∘ f)^*` produces the canonical
comparison of Stacks 0D6D. -/
def derivedPullbackCompCounit :
    DerivedCategory.Qh ⋙ (derivedPullback g ⋙ derivedPullback f) ⟶
      pullbackOnHomotopy (g.comp f) :=
  Functor.whiskerRight (derivedPullbackComparison g) (derivedPullback f) ≫
    Functor.whiskerLeft (DerivedPushforward.pullbackMapHomotopy g) (derivedPullbackComparison f) ≫
    Functor.whiskerRight (pullbackMapHomotopyCompIso f g).hom DerivedCategory.Qh

/-- The value of `derivedPullbackCompCounit` at a complex, written out as a composite of its
three factors. Each whiskering contributes its component on the nose, so this holds by
definition; it is recorded once because a tactic looking at the unevaluated composite cannot
see through the whiskerings. -/
theorem derivedPullbackCompCounit_app
    (K : HomotopyCategory
      (SheafOfModules.{w''} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O))
      (ComplexShape.up ℤ)) :
    (derivedPullbackCompCounit f g).app K =
      (derivedPullback f).map ((derivedPullbackComparison g).app K) ≫
        (derivedPullbackComparison f).app ((DerivedPushforward.pullbackMapHomotopy g).obj K) ≫
        DerivedCategory.Qh.map ((pullbackMapHomotopyCompIso f g).hom.app K) :=
  rfl

section Lift

variable [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor (quasiIsoTarget (Y := Z))]

/-- The canonical comparison `Lg^* ⋙ Lf^* ⟶ L(g ∘ f)^*` of Stacks 0D6D, obtained from the
universal property of the derived pullback along the composite.

It is characterized by `derivedPullbackCompComparison_comp_derivedPullbackComparison` below:
postcomposing it with the comparison of `L(g ∘ f)^*` returns `derivedPullbackCompCounit`. -/
def derivedPullbackCompComparison :
    derivedPullback g ⋙ derivedPullback f ⟶ derivedPullback (g.comp f) :=
  (derivedPullback (g.comp f)).leftDerivedLift (derivedPullbackComparison (g.comp f))
    (quasiIsoTarget (Y := Z)) _ (derivedPullbackCompCounit f g)

/-- **The comparison of Stacks 0D6D is the canonical one.** Postcomposing it with the comparison
`L(g ∘ f)^* ⟶ (g ∘ f)^*` of Stacks 06YY returns `derivedPullbackCompCounit`, and by
`CategoryTheory.Functor.leftDerived_ext` this determines it uniquely.

Nothing beyond the universal property of `L(g ∘ f)^*` is used, so this holds whether or not the
comparison is invertible. -/
theorem derivedPullbackCompComparison_comp_derivedPullbackComparison :
    Functor.whiskerLeft DerivedCategory.Qh (derivedPullbackCompComparison f g) ≫
        derivedPullbackComparison (g.comp f) =
      derivedPullbackCompCounit f g :=
  (derivedPullback (g.comp f)).leftDerived_fac (derivedPullbackComparison (g.comp f))
    (quasiIsoTarget (Y := Z)) _ (derivedPullbackCompCounit f g)

/-- The characterization of the Stacks 0D6D comparison at a complex, with the three factors of
`derivedPullbackCompCounit` written out. This is the form a base-change computation consumes:
it says that on a complex, the comparison followed by the 06YY comparison for `g ∘ f` is the
06YY comparison for `g`, then the one for `f`, then the underived compositor. -/
theorem derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app
    (K : HomotopyCategory
      (SheafOfModules.{w''} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O))
      (ComplexShape.up ℤ)) :
    (derivedPullbackCompComparison f g).app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackComparison (g.comp f)).app K =
      (derivedPullback f).map ((derivedPullbackComparison g).app K) ≫
        (derivedPullbackComparison f).app ((DerivedPushforward.pullbackMapHomotopy g).obj K) ≫
        DerivedCategory.Qh.map ((pullbackMapHomotopyCompIso f g).hom.app K) :=
  ((derivedPullback (g.comp f)).leftDerived_fac_app (derivedPullbackComparison (g.comp f))
      (quasiIsoTarget (Y := Z)) _ (derivedPullbackCompCounit f g) K).trans
    (derivedPullbackCompCounit_app f g K)

end Lift

end Counit

end Comparison

section Main

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')] [HasSheafify Z.J (Type w'')]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

omit [Y.J.HasSheafCompose (forget RingCat.{w'})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify Y.J (Type w')] in
/-- The class of K-flat complexes with flat terms resolves every complex of sheaves of modules
on a ringed topos.

This is **Stacks 06YS**, in the spelling the resolving datum of this file consumes; the content
is `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat`, which
mentions no morphism at all. -/
theorem hasResolutions_isKFlat' :
    HasResolutions (Y := Y) (IsKFlat (Y := Y)) := fun N => by
  obtain ⟨K, hK, s, hs⟩ :=
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat (Y := Y) N
  exact ⟨K, hK, s, hs⟩

/-- The canonical comparison `Lf^* ⟶ f^*` of Stacks 06YY is invertible at every K-flat complex
of `𝒪_D`-modules with flat terms: such a complex computes the derived pullback.

This is the computation assertion of Stacks 06YY at the resolving datum of Stacks 06YS and the
exactness clause of Stacks 06YY, both unconditional for a morphism of ringed topoi. -/
theorem isIso_derivedPullbackComparison_app_isKFlat
    (M : HomotopyCategory
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
      (ComplexShape.up ℤ))
    (hM : IsKFlat (Y := Y) M) :
    IsIso ((derivedPullbackComparison f).app M) :=
  isIso_derivedPullbackComparison_app f (IsKFlat (Y := Y)) (hasResolutions_isKFlat' (Y := Y))
    (pullbackInvertsQuasiIso_isKFlat f) M hM

/-- The comparison `derivedPullbackCompCounit` is invertible at a K-flat complex with flat terms.

Of its three factors the first is the image under `Lf^*` of the comparison for `Lg^*`; the
second is the comparison for `Lf^*` at the degreewise pullback along `g`, which is again K-flat
with flat terms by Stacks 0G7E; and the third is the image of an isomorphism. -/
theorem isIso_derivedPullbackCompCounit_app
    (K : HomotopyCategory
      (SheafOfModules.{w''} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O))
      (ComplexShape.up ℤ))
    (hK : IsKFlat (Y := Z) K) :
    IsIso ((derivedPullbackCompCounit f g).app K) := by
  rw [derivedPullbackCompCounit_app]
  have h₁ := isIso_derivedPullbackComparison_app_isKFlat g K hK
  have h₂ := isIso_derivedPullbackComparison_app_isKFlat f _
    (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy g K hK)
  infer_instance

/-- **The composite of two derived pullbacks is a derived pullback along the composite.** The
composite `Lg^* ⋙ Lf^*`, with the comparison `derivedPullbackCompCounit`, is a left derived
functor of degreewise pullback along `g ∘ f` followed by localization.

A comparison invertible on a class that resolves every complex, and whose quasi-isomorphisms the
underived functor inverts, exhibits its functor as a left derived functor; the class is the
K-flat complexes with flat terms, resolving by Stacks 06YS and inverted by Stacks 06YY. -/
theorem isLeftDerivedFunctor_derivedPullbackComp :
    (derivedPullback g ⋙ derivedPullback f).IsLeftDerivedFunctor
      (derivedPullbackCompCounit f g) (quasiIsoTarget (Y := Z)) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (quasiIsoTarget (Y := Z)) (IsKFlat (Y := Z)) (hasResolutions_isKFlat' (Y := Z))
    (pullbackOnHomotopy (g.comp f)) (pullbackInvertsQuasiIso_isKFlat (g.comp f))
    DerivedCategory.Qh (derivedPullback g ⋙ derivedPullback f)
    (derivedPullbackCompCounit f g)
    (fun K hK => isIso_derivedPullbackCompCounit_app f g K hK)

/-- **Stacks 0D6D.** For composable morphisms of ringed topoi `f` and `g`, the canonical
comparison from the composite of the derived pullbacks to the derived pullback along `g ∘ f` is
an isomorphism, so `Lf^* ∘ Lg^* = L(g ∘ f)^*`.

There is no hypothesis: the geometric datum is the two-field morphism of ringed topoi of
Stacks 01D3, part (2), with no continuous functor between underlying sites and no
morphism-of-sites condition. Both functors are left derived functors of degreewise pullback
along `g ∘ f`, and a map between left derived functors induced by the universal property is
invertible exactly then. -/
@[stacks 0D6D "for a morphism of ringed topoi whose geometric datum is a morphism of the
underlying topoi rather than a continuous functor between the underlying sites, with no
morphism-of-sites hypothesis"]
theorem isIso_derivedPullbackCompComparison :
    IsIso (derivedPullbackCompComparison f g) :=
  ((derivedPullback (g.comp f)).isLeftDerivedFunctor_iff_isIso_leftDerivedLift
      (derivedPullbackComparison (g.comp f)) (quasiIsoTarget (Y := Z))
      (derivedPullback g ⋙ derivedPullback f) (derivedPullbackCompCounit f g)).1
    (isLeftDerivedFunctor_derivedPullbackComp f g)

/-- **Stacks 0D6D as a natural isomorphism** `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*`, for morphisms of
ringed topoi and with no hypothesis, obtained by inverting the canonical comparison. -/
@[stacks 0D6D "as a natural isomorphism, for a morphism of ringed topoi whose geometric datum
is a morphism of the underlying topoi rather than a continuous functor between the underlying
sites, with no morphism-of-sites hypothesis"]
def derivedPullbackCompIso :
    derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (g.comp f) :=
  have := isIso_derivedPullbackCompComparison f g
  asIso (derivedPullbackCompComparison f g)

/-- The underlying map of `derivedPullbackCompIso` is the canonical comparison of Stacks 0D6D,
so the characterization lemmas above apply to it. -/
@[simp]
theorem derivedPullbackCompIso_hom :
    (derivedPullbackCompIso f g).hom = derivedPullbackCompComparison f g :=
  rfl

end Main

end

end Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

end
