module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Defs
public import StacksFrontier.AlgebraicGeometry.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# Perfect objects along a directed limit of schemes

In the situation of Stacks 09RD — a directed inverse system `i ↦ S_i` of quasi-compact and
quasi-separated schemes with affine transition morphisms, with limit `S` — derived pullback
along the transition morphisms `f_{ji} : S_j ⟶ S_i` and along the projections `f_i : S ⟶ S_i`
carries perfect objects to perfect objects. It therefore induces functors
`D_perf(𝒪_{S_i}) ⥤ D_perf(𝒪_{S_j})` and `D_perf(𝒪_{S_i}) ⥤ D_perf(𝒪_S)` between the categories
of perfect objects, and the canonical composition isomorphisms of derived pullback make these
into a coherent cocone over the system.

Stacks 09RF states that this cocone exhibits `D_perf(𝒪_S)` as the *colimit* of the categories
`D_perf(𝒪_{S_i})`, that is, that the comparison functor out of the colimit is fully faithful and
essentially surjective. The results below are about the cocone itself; full faithfulness is
Stacks 09RE at the sheaf level, `AlgebraicGeometry.DescentSituation.isHomColimit` of
`StacksFrontier/AlgebraicGeometry/Perfect/LimitHomDescent.lean`.

## Main definitions

* `AlgebraicGeometry.DescentSituation.stage`, `limitScheme`, `transition` and `projection`: the
  schemes `S_i` and `S`, the transition morphisms `f_{ji}` and the projections `f_i`.
* `AlgebraicGeometry.DescentSituation.perfectTransition` and `perfectProjection`: derived
  pullback along `f_{ji}` and along `f_i`, read as functors between the categories of perfect
  objects.
* `AlgebraicGeometry.DescentSituation.pullbackProjectionIso` and `pullbackTransitionIso`: the
  canonical isomorphisms `Lf_{ji}^* ⋙ Lf_j^* ≅ Lf_i^*` and `Lf_{ji}^* ⋙ Lf_{kj}^* ≅ Lf_{ki}^*`
  on the ambient derived categories.
* `AlgebraicGeometry.DescentSituation.perfectComparison` and `perfectTransitionComp`: the same
  two isomorphisms read on the categories of perfect objects.

## Main results

* `AlgebraicGeometry.DescentSituation.isPerfect_transition` and `isPerfect_projection`: derived
  pullback along a transition morphism, respectively along a projection, of the situation carries
  a perfect object to a perfect object.
* `AlgebraicGeometry.DescentSituation.perfectComparison_coherence` and
  `perfectTransitionComp_coherence`: the cocycle identities satisfied by the comparison
  isomorphisms, so that the comparison functors form a coherent cocone of categories of perfect
  objects over the system.

## Implementation notes

*Why the perfect objects are a full subcategory of the derived category and not a separate
construction.* `Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory` is already the
category `D_perf(𝒪_X)` of Stacks 0F8I, the full subcategory of `DerivedCategory X.Modules` cut
out by `Stacks.Cohomology.PerfectComplexes.IsPerfect` at `X.toRingedSpace`; the functors below
are `ObjectProperty.lift` of derived pullback along it, so a morphism of perfect objects is a
morphism of the derived category and nothing has to be re-proved about it.

*The comparison isomorphisms come from a factorisation, not from a composite.* Derived pullback
is only pseudofunctorial, and `Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`
compares `Lg^* ⋙ Lf^*` with `L(f ≫ g)^*` for the literal composite `f ≫ g`. The morphisms of
the situation satisfy `f_j ≫ f_{ji} = f_i`, which is an equation and not a definitional
identity, so the comparison is taken from `Stacks.DerivedPullback.schemeFactorIso`, which
transports the canonical isomorphism along such an equation. Its cocycle identity
`Stacks.DerivedPullback.factorIso_assoc` is then the coherence of the cocone, with no further
transport.

*The coherence is stated on components rather than as an equality of natural isomorphisms.* An
equality of whiskered natural isomorphisms between functors into
`PerfectDerivedCategory D.limitScheme` would have to compare the associators as well; stating it
at an object reduces it to `ObjectProperty.hom_ext` applied to the ambient identity, and loses
nothing, the two sides being natural in that object.

## References

* [Stacks Project, Lemma 36.29.3 (Tag 09RF)](https://stacks.math.columbia.edu/tag/09RF)
* [Stacks Project, Situation 36.29.1 (Tag 09RD)](https://stacks.math.columbia.edu/tag/09RD)
* [Stacks Project, Lemma 36.29.2 (Tag 09RE)](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Lemma 36.27.2 (Tag 09UA)](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Lemma 36.5.1 (Tag 0D5S)](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (isPerfect_derivedPullback)

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace AlgebraicGeometry.DescentSituation

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation.{v, u} I)

/-- The scheme `S_i` at the stage `i`. -/
abbrev stage (i : I) : Scheme.{u} := D.system.obj (op i)

/-- The limiting scheme `S`. -/
abbrev limitScheme : Scheme.{u} := D.limitCone.pt

/-- The transition morphism `f_{ji} : S_j ⟶ S_i` of the system, for `i ≤ j`. -/
def transition {i j : I} (h : i ≤ j) : D.stage j ⟶ D.stage i :=
  D.system.map (homOfLE h).op

/-- The projection `f_i : S ⟶ S_i` from the limit to the stage `i`. -/
def projection (i : I) : D.limitScheme ⟶ D.stage i :=
  D.limitCone.π.app (op i)

/-- The projections are compatible with the transition morphisms: `f_j ≫ f_{ji} = f_i`. -/
theorem projection_comp_transition {i j : I} (h : i ≤ j) :
    D.projection j ≫ D.transition h = D.projection i :=
  D.limitCone.w (homOfLE h).op

/-- The transition morphisms compose: `f_{kj} ≫ f_{ji} = f_{ki}`. -/
theorem transition_comp_transition {i j k : I} (h : i ≤ j) (h' : j ≤ k) :
    D.transition h' ≫ D.transition h = D.transition (h.trans h') := by
  rw [transition, transition, transition, ← D.system.map_comp]
  congr 1

/-- The transition morphism attached to `i ≤ i` is the identity of `S_i`. -/
theorem transition_refl (i : I) : D.transition (le_refl i) = 𝟙 (D.stage i) :=
  Eq.trans
    (congrArg (fun f : op i ⟶ op i => D.system.map f)
      (show (homOfLE (le_refl i)).op = 𝟙 (op i) from rfl))
    (D.system.map_id (op i))

/-- **Derived pullback along a transition morphism of the situation preserves perfectness.**
This is Stacks 09UA at `f_{ji}`, and it is what makes the transition functor on the categories
of perfect objects defined. -/
@[stacks 09RF "derived pullback along the transition morphisms of the situation sends perfect \
objects to perfect objects, so the transition functors of the colimit statement are defined; the \
colimit property itself is not included"]
theorem isPerfect_transition {i j : I} (h : i ≤ j)
    (E : DerivedCategory (D.stage i).Modules) (hE : IsPerfect (X := (D.stage i).toRingedSpace) E) :
    IsPerfect (X := (D.stage j).toRingedSpace)
      ((derivedPullback (D.transition h).toLRSHom.toShHom).obj E) :=
  isPerfect_derivedPullback (D.transition h).toLRSHom.toShHom E hE

/-- **Derived pullback along a projection of the situation preserves perfectness.** This is
Stacks 09UA at `f_i`, and it is what makes the comparison functor from the stage `i` to the limit
defined. -/
@[stacks 09RF "derived pullback along the projections of the situation sends perfect objects to \
perfect objects, so the comparison functors of the colimit statement are defined; the colimit \
property itself is not included"]
theorem isPerfect_projection (i : I)
    (E : DerivedCategory (D.stage i).Modules) (hE : IsPerfect (X := (D.stage i).toRingedSpace) E) :
    IsPerfect (X := D.limitScheme.toRingedSpace)
      ((derivedPullback (D.projection i).toLRSHom.toShHom).obj E) :=
  isPerfect_derivedPullback (D.projection i).toLRSHom.toShHom E hE

/-- Derived pullback `Lf_{ji}^*` along a transition morphism, as a functor
`D_perf(𝒪_{S_i}) ⥤ D_perf(𝒪_{S_j})`. -/
def perfectTransition {i j : I} (h : i ≤ j) :
    PerfectDerivedCategory (D.stage i) ⥤ PerfectDerivedCategory (D.stage j) :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ derivedPullback (D.transition h).toLRSHom.toShHom)
    (fun E => D.isPerfect_transition h E.obj E.property)

/-- Derived pullback `Lf_i^*` along a projection, as a functor
`D_perf(𝒪_{S_i}) ⥤ D_perf(𝒪_S)`. -/
def perfectProjection (i : I) :
    PerfectDerivedCategory (D.stage i) ⥤ PerfectDerivedCategory D.limitScheme :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ derivedPullback (D.projection i).toLRSHom.toShHom)
    (fun E => D.isPerfect_projection i E.obj E.property)

/-- The canonical isomorphism `Lf_{ji}^* ⋙ Lf_j^* ≅ Lf_i^*` on the ambient derived categories,
obtained from the composition isomorphism of Stacks 0D5S along `f_j ≫ f_{ji} = f_i`. -/
def pullbackProjectionIso {i j : I} (h : i ≤ j) :
    derivedPullback (D.transition h).toLRSHom.toShHom ⋙
        derivedPullback (D.projection j).toLRSHom.toShHom ≅
      derivedPullback (D.projection i).toLRSHom.toShHom :=
  Stacks.DerivedPullback.schemeFactorIso (D.projection j) (D.transition h) (D.projection i)
    (D.projection_comp_transition h)

/-- The canonical isomorphism `Lf_{ji}^* ⋙ Lf_{kj}^* ≅ Lf_{ki}^*` on the ambient derived
categories, obtained from the composition isomorphism of Stacks 0D5S along
`f_{kj} ≫ f_{ji} = f_{ki}`. -/
def pullbackTransitionIso {i j k : I} (h : i ≤ j) (h' : j ≤ k) :
    derivedPullback (D.transition h).toLRSHom.toShHom ⋙
        derivedPullback (D.transition h').toLRSHom.toShHom ≅
      derivedPullback (D.transition (h.trans h')).toLRSHom.toShHom :=
  Stacks.DerivedPullback.schemeFactorIso (D.transition h') (D.transition h)
    (D.transition (h.trans h')) (D.transition_comp_transition h h')

/-- The comparison isomorphism of the cocone, on the categories of perfect objects: the
composite `D_perf(𝒪_{S_i}) ⥤ D_perf(𝒪_{S_j}) ⥤ D_perf(𝒪_S)` is isomorphic to the functor from
the stage `i`. -/
def perfectComparison {i j : I} (h : i ≤ j) :
    D.perfectTransition h ⋙ D.perfectProjection j ≅ D.perfectProjection i :=
  NatIso.ofComponents
    (fun E => ObjectProperty.isoMk _ ((D.pullbackProjectionIso h).app E.obj))
    (fun f => ObjectProperty.hom_ext _ ((D.pullbackProjectionIso h).hom.naturality f.hom))

/-- The composition isomorphism of the transition functors on the categories of perfect
objects. -/
def perfectTransitionComp {i j k : I} (h : i ≤ j) (h' : j ≤ k) :
    D.perfectTransition h ⋙ D.perfectTransition h' ≅ D.perfectTransition (h.trans h') :=
  NatIso.ofComponents
    (fun E => ObjectProperty.isoMk _ ((D.pullbackTransitionIso h h').app E.obj))
    (fun f => ObjectProperty.hom_ext _ ((D.pullbackTransitionIso h h').hom.naturality f.hom))

/-- The cocone cocycle identity on the ambient derived categories: for `i ≤ j ≤ k` the two ways
of identifying `Lf_{ji}^* ⋙ Lf_{kj}^* ⋙ Lf_k^*` with `Lf_i^*` agree. -/
theorem pullbackProjectionIso_assoc {i j k : I} (h : i ≤ j) (h' : j ≤ k)
    (M : DerivedCategory (D.stage i).Modules) :
    (D.pullbackProjectionIso h').hom.app
          ((derivedPullback (D.transition h).toLRSHom.toShHom).obj M) ≫
        (D.pullbackProjectionIso h).hom.app M =
      (derivedPullback (D.projection k).toLRSHom.toShHom).map
          ((D.pullbackTransitionIso h h').hom.app M) ≫
        (D.pullbackProjectionIso (h.trans h')).hom.app M := by
  have key := Stacks.DerivedPullback.factorIso_assoc
    (D.projection k).toLRSHom.toShHom (D.transition h').toLRSHom.toShHom
    (D.transition h).toLRSHom.toShHom (D.transition (h.trans h')).toLRSHom.toShHom
    (D.projection j).toLRSHom.toShHom (D.projection i).toLRSHom.toShHom
    (congrArg (fun m : D.stage k ⟶ D.stage i => m.toLRSHom.toShHom)
      (D.transition_comp_transition h h'))
    (congrArg (fun m : D.limitScheme ⟶ D.stage j => m.toLRSHom.toShHom)
      (D.projection_comp_transition h'))
    (congrArg (fun m : D.limitScheme ⟶ D.stage i => m.toLRSHom.toShHom)
      (D.projection_comp_transition h))
    (congrArg (fun m : D.limitScheme ⟶ D.stage i => m.toLRSHom.toShHom)
      (D.projection_comp_transition (h.trans h'))) M
  exact congrArg Iso.hom key

/-- **The cocone coherence on the categories of perfect objects.** For `i ≤ j ≤ k`, comparing
through the stage `j` and comparing after composing the two transitions give the same
isomorphism from the functor out of `D_perf(𝒪_{S_i})` through the stage `k` to the functor out
of `D_perf(𝒪_{S_i})` directly. Together with
`AlgebraicGeometry.DescentSituation.perfectTransitionComp_coherence` this is the statement that
the functors `AlgebraicGeometry.DescentSituation.perfectProjection` form a coherent cocone over
the system of categories of perfect objects. -/
@[stacks 09RF "the canonical cocone of the colimit statement: the functors between the \
categories of perfect objects induced by derived pullback along the projections, and their \
coherence with the transition functors. Neither full faithfulness nor essential surjectivity \
of the comparison out of the colimit is included"]
theorem perfectComparison_coherence {i j k : I} (h : i ≤ j) (h' : j ≤ k)
    (E : PerfectDerivedCategory (D.stage i)) :
    ((D.perfectComparison h').app ((D.perfectTransition h).obj E)).hom ≫
        ((D.perfectComparison h).app E).hom =
      (D.perfectProjection k).map ((D.perfectTransitionComp h h').app E).hom ≫
        ((D.perfectComparison (h.trans h')).app E).hom :=
  ObjectProperty.hom_ext _ (D.pullbackProjectionIso_assoc h h' E.obj)

/-- The cocycle identity for the transition comparison on the ambient derived categories: for
`i ≤ j ≤ k ≤ l` the two ways of identifying `Lf_{ji}^* ⋙ Lf_{kj}^* ⋙ Lf_{lk}^*` with `Lf_{li}^*`
agree. -/
theorem pullbackTransitionIso_assoc {i j k l : I} (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l)
    (M : DerivedCategory (D.stage i).Modules) :
    (D.pullbackTransitionIso h' h'').hom.app
          ((derivedPullback (D.transition h).toLRSHom.toShHom).obj M) ≫
        (D.pullbackTransitionIso h (h'.trans h'')).hom.app M =
      (derivedPullback (D.transition h'').toLRSHom.toShHom).map
          ((D.pullbackTransitionIso h h').hom.app M) ≫
        (D.pullbackTransitionIso (h.trans h') h'').hom.app M :=
  congrArg Iso.hom (Stacks.DerivedPullback.factorIso_assoc
    (D.transition h'').toLRSHom.toShHom (D.transition h').toLRSHom.toShHom
    (D.transition h).toLRSHom.toShHom (D.transition (h.trans h')).toLRSHom.toShHom
    (D.transition (h'.trans h'')).toLRSHom.toShHom
    (D.transition (h.trans (h'.trans h''))).toLRSHom.toShHom
    (congrArg (fun m : D.stage k ⟶ D.stage i => m.toLRSHom.toShHom)
      (D.transition_comp_transition h h'))
    (congrArg (fun m : D.stage l ⟶ D.stage j => m.toLRSHom.toShHom)
      (D.transition_comp_transition h' h''))
    (congrArg (fun m : D.stage l ⟶ D.stage i => m.toLRSHom.toShHom)
      (D.transition_comp_transition h (h'.trans h'')))
    (congrArg (fun m : D.stage l ⟶ D.stage i => m.toLRSHom.toShHom)
      (D.transition_comp_transition (h.trans h') h'')) M)

/-- **The system of transition functors on the categories of perfect objects is coherent.** For
`i ≤ j ≤ k ≤ l`, the two ways of composing the comparison isomorphisms of the three transitions
agree. -/
@[stacks 09RF "the system of categories of perfect objects along the transition morphisms: the \
transition functors, their composition isomorphisms and the cocycle identity those satisfy. \
Neither full faithfulness nor essential surjectivity of the comparison out of the colimit is \
included"]
theorem perfectTransitionComp_coherence {i j k l : I} (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l)
    (E : PerfectDerivedCategory (D.stage i)) :
    ((D.perfectTransitionComp h' h'').app ((D.perfectTransition h).obj E)).hom ≫
        ((D.perfectTransitionComp h (h'.trans h'')).app E).hom =
      (D.perfectTransition h'').map ((D.perfectTransitionComp h h').app E).hom ≫
        ((D.perfectTransitionComp (h.trans h') h'').app E).hom :=
  ObjectProperty.hom_ext _ (D.pullbackTransitionIso_assoc h h' h'' E.obj)

end AlgebraicGeometry.DescentSituation

end
