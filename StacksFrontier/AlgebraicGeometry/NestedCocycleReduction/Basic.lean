module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.RelativeProj

/-!
# Tag 01NO's pushed-forward twist comparison on sections

`StacksFrontier/AlgebraicGeometry/ChartTransNonNested/RelativeProj.lean` builds, for a nested
pair `W ⊆ U` of affine opens of the base of a quasi-coherent graded algebra, a morphism of
sheaves of modules on the relative projective spectrum
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested` from the direct image of the `n`-th
twist on the chart of `U` to the direct image of the `n`-th twist on the chart of `W`, and takes
care never to compute it on sections: everything there is proved at the level of morphisms or by
instantiating a definition in which every ingredient is a variable.

The nested cocycle
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle`, on the other hand, is an
equation between *values*, and the pointwise rigidity criterion
`Stacks.AlgebraicGeometry.ThetaMultiplicative.eq_id_of_fibreHom` consumes a description of the
comparison's action on an arbitrary section at an arbitrary point. This file supplies the
section-level vocabulary that description needs, and isolates the one step of it which is
**not reachable from outside the defining file** at this pin; see "What is not done", which
records the measurements.

## Main results, in increasing specificity

* `Stacks.AlgebraicGeometry.NestedCocycleReduction.pushforward_map_val_app`,
  `restrictAdjunction_unit_val_app`, `pushforwardComp_app_hom_val_app`,
  `pushforwardCongr_app_hom_val_app`, `pushforward_mapIso_hom_val_app` and `restrict_val_map`:
  the five structural factors of the comparison, read on sections, at the level of variables.
  Each is a restriction map or the identity; none of them is about `Proj`.
* `Stacks.AlgebraicGeometry.NestedCocycleReduction.map_comp_val` and `map_val_congr`: two
  successive restriction maps are one, and a restriction map does not depend on which inclusion
  of opens is used -- morphisms between opens are unique, so the composite inclusion need never
  be exhibited.
* `Stacks.AlgebraicGeometry.NestedCocycleReduction.comp_val_app_of`: one factor of a composite,
  read on a section, **with the composite given as a variable and identified by an equation of
  morphisms**. This is the shape that survives at the instance; see the implementation notes.
* `Stacks.AlgebraicGeometry.NestedCocycleReduction.tailGeneric_val_app`: the three tail factors
  of the comparison -- pseudofunctoriality of the pushforward, the chart congruence, and the
  functor image of the chart-level isomorphism -- composed and read on a section, at the level
  of variables. The chart congruence contributes a transport of opens and nothing else.
* `Stacks.AlgebraicGeometry.NestedCocycleReduction.chart_preimage_eq` and
  `image_preimage_le_preimage`: the two facts about opens the computation uses. The second holds
  for **every** open of the relative Proj, with no hypothesis relating it to the inverse image
  of `W`.
* `Stacks.AlgebraicGeometry.NestedCocycleReduction.pushNestedUnit_app_val`: **the unit factor of
  the comparison, computed on sections at the instance.** It is the restriction map of the twist
  on the chart of `U` from the preimage of the open to the image of its preimage in the chart of
  `W`.
* `Stacks.AlgebraicGeometry.NestedCocycleReduction.tailOf`: the tail at the instance, with the
  module and the chart-level comparison still variables and the inclusion of opens arbitrary.
* `Stacks.AlgebraicGeometry.NestedCocycleReduction.pushNested_app_val_of`: **the comparison on
  sections, conditional on the tail's action.** Given that the tail acts as the chart-level
  isomorphism on the restricted section -- the one step not reachable from here -- the
  whole comparison carries a section `s` over an open `V` to the chart-level isomorphism applied
  to the restriction of `s` to the image, in the chart of `U`, of the preimage of `V` in the
  chart of `W`. Nothing else about the comparison is then owed, and the cocycle becomes a
  statement about the chart-level isomorphisms alone.

## Why this is the reduction the pointwise route needs

`eq_id_of_fibreHom` asks for the value of the image of an arbitrary section at an arbitrary
point. For the comparison of a nested pair that means: strip the three layers that live on the
relative Proj -- the unit of the restriction adjunction, pseudofunctoriality of the pushforward
along the two charts, and the chart congruence -- and be left with the chart-level isomorphism
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.restrictTwistIso`, whose pointwise content is
Tag 01MY's fibre comparison through
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap_app_val`. Those three layers are
exactly what is computed here: each is a restriction map or an identity on sections, and the two
restriction maps compose into one by `map_comp_val`, which is why the conclusion of
`pushNested_app_val_of` mentions a single inclusion of opens.

What that leaves is a statement with no relative projective spectrum in it, about three
isomorphisms of sheaves of modules on the charts; and for those, the composition law of the
fibre comparisons `Stacks.AlgebraicGeometry.TwistBaseChange.fibreMap_comp` is already proved.

## Implementation notes: what is affordable at this instance

The defining file records that an `app` applied to a composite exhausts the recursion limit at
this instance. The facts below refine that, and they are the reason every statement here
has the shape it has.

* **An equation of morphisms, then `comp_val_app_of`, is affordable; the same identification
  made underneath an `app` is not.** Instantiating a factored form directly under an `app` --
  `(a ≫ b).val.app (op V) x` with `a` and `b` supplied -- reaches the recursion limit, while
  `comp_val_app_of` applied to an equation of morphisms does not. The two differ only in where
  the identification happens.
* **A general lemma must be instantiated with its structural arguments left as
  metavariables.** `pushNestedUnit_app_val` is proved by applying `pushforward_map_val_app` with
  the pushed-forward morphism a metavariable, which the unification against the body of the unit
  factor assigns; writing that morphism out instead and asking for the resulting equation of
  morphisms by `rfl` exceeds the **kernel's** deterministic timeout.
* **A `rfl` at the carrier of the sections is cheap; the carrier itself is not the problem.**
  Both `y = y` and the type of such a `y` -- which mentions the restriction of the twist along
  the transition morphism -- elaborate in seconds.
* The inclusion of opens is always a *variable*, identified with whatever the goal produces by
  `map_val_congr` or `map_comp_val`. Writing a transport of opens into a statement instead --
  `eqToHom` of the chart compatibility -- does not elaborate at all here, the same obstruction as
  for the twist index.

## What is not done, and why

**The action of `Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNestedTail` on sections is
not computed, and it is not reachable from outside the file that defines it.** The tail is an
isomorphism built as a threefold `CategoryTheory.Iso.trans`, and identifying it with its three
factors is what the comparison on sections needs. Eight spellings of that identification
all fail:

* as an equation of morphisms with the three factors written out, by `rfl`, and again after
  rewriting with the tail's own equation lemma and `CategoryTheory.Iso.trans_hom`: the
  elaborator succeeds in the second case and the **kernel** then exceeds its deterministic
  timeout;
* as an equation on sections with the three factors written out, by `rfl`: recursion limit, in
  the statement;
* by instantiating a general lemma whose left-hand side is the threefold `Iso.trans` -- with
  the schemes, the morphisms, the module and the comparison all metavariables; with the schemes
  and morphisms fixed and the module a metavariable; with the module taken from the type of the
  chart-level comparison; and in each case also after unfolding the tail first with `rw` or
  `simp only`: recursion limit every time.

The mechanism is visible in the last family: matching a metavariable's `CategoryTheory.Iso.hom`
projection against a composite is not a first-order problem, and the unifier does not come back.
So the identification has to be made **where the tail was elaborated**, and the shape it should
take is the hypothesis of `pushNested_app_val_of` -- which, once supplied, is the only thing
between the vocabulary here and a pointwise description of the comparison.

Consequently `Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle` is **not** proved
here, no `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` is constructed, and no Stacks
tag is attached to any declaration below.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartTransNonNested
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.NestedCocycleReduction

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u

/-! ### The structural factors on sections, at the level of variables -/

/-- The component of a pushed-forward morphism is the component at the preimage. -/
public theorem pushforward_map_val_app {X Y : Scheme.{u}} (g : Y ⟶ X) {M N : Y.Modules}
    (φ : M ⟶ N) (V : X.Opens)
    (s : ((Scheme.Modules.pushforward g).obj M).val.obj (op V)) :
    ((Scheme.Modules.pushforward g).map φ).val.app (op V) s = φ.val.app (op (g ⁻¹ᵁ V)) s :=
  rfl

/-- The unit of the restriction adjunction is, on sections, the restriction map from an open to
the image of its preimage. -/
public theorem restrictAdjunction_unit_val_app {X Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (M : X.Modules) (V : X.Opens) (s : M.val.obj (op V)) :
    ((Scheme.Modules.restrictAdjunction g).unit.app M).val.app (op V) s =
      M.val.map (homOfLE (g.image_preimage_le V)).op s :=
  rfl

/-- The pushforward of that unit, in one step. -/
public theorem push_restrictUnit_val_app {X Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsOpenImmersion g]
    (c : Z ⟶ X) (M : Z.Modules) (V : X.Opens) (s : M.val.obj (op (c ⁻¹ᵁ V))) :
    ((Scheme.Modules.pushforward c).map
        ((Scheme.Modules.restrictAdjunction g).unit.app M)).val.app (op V) s =
      M.val.map (homOfLE (g.image_preimage_le (c ⁻¹ᵁ V))).op s :=
  rfl

/-- Pseudofunctoriality of the pushforward is the identity on sections. -/
public theorem pushforwardComp_app_hom_val_app {X Y Z : Scheme.{u}} (g : Y ⟶ X) (g' : X ⟶ Z)
    (M : Y.Modules) (V : Z.Opens)
    (s : ((Scheme.Modules.pushforward g').obj ((Scheme.Modules.pushforward g).obj M)).val.obj
      (op V)) :
    ((Scheme.Modules.pushforwardComp g g').app M).hom.val.app (op V) s = s :=
  rfl

/-- The congruence isomorphism of two equal morphisms is, on sections, the transport of opens. -/
public theorem pushforwardCongr_app_hom_val_app {X Y : Scheme.{u}} {g g' : Y ⟶ X} (hg : g = g')
    (M : Y.Modules) (V : X.Opens)
    (s : ((Scheme.Modules.pushforward g).obj M).val.obj (op V)) :
    ((Scheme.Modules.pushforwardCongr hg).app M).hom.val.app (op V) s =
      M.val.map (eqToHom (show g' ⁻¹ᵁ V = g ⁻¹ᵁ V from hg ▸ rfl)).op s :=
  rfl

/-- The component of the functor image of an isomorphism under a pushforward. -/
public theorem pushforward_mapIso_hom_val_app {X Y : Scheme.{u}} (g : Y ⟶ X) {M N : Y.Modules}
    (e : M ≅ N) (V : X.Opens)
    (s : ((Scheme.Modules.pushforward g).obj M).val.obj (op V)) :
    ((Scheme.Modules.pushforward g).mapIso e).hom.val.app (op V) s =
      e.hom.val.app (op (g ⁻¹ᵁ V)) s :=
  rfl

/-- A restriction map of the restriction of a module along an open immersion is the restriction
map of the module along the image inclusion. -/
public theorem restrict_val_map {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (M : X.Modules) {T T' : Y.Opens} (i : T' ⟶ T)
    (s : ((Scheme.Modules.restrictFunctor g).obj M).val.obj (op T)) :
    ((Scheme.Modules.restrictFunctor g).obj M).val.map i.op s =
      M.val.map (g.opensFunctor.map i).op s :=
  rfl

/-- **Two successive restriction maps are one**, and the composite inclusion is supplied freely:
morphisms between opens are unique, so it never has to be exhibited as a composite. -/
public theorem map_comp_val {X : Scheme.{u}} (M : X.Modules) {T₁ T₂ T₃ : X.Opens}
    (i : T₃ ⟶ T₂) (j : T₂ ⟶ T₁) (k : T₃ ⟶ T₁) (s : M.val.obj (op T₁)) :
    M.val.map i.op (M.val.map j.op s) = M.val.map k.op s := by
  obtain rfl : k = i ≫ j := Subsingleton.elim _ _
  exact congrFun (congrArg (fun f => DFunLike.coe (ConcreteCategory.hom f))
    (M.val.map_comp j.op i.op).symm) s

/-- **A restriction map does not depend on the inclusion used.** -/
public theorem map_val_congr {X : Scheme.{u}} (M : X.Modules) {T T' : X.Opens} (i j : T' ⟶ T)
    (s : M.val.obj (op T)) : M.val.map i.op s = M.val.map j.op s := by
  obtain rfl : i = j := Subsingleton.elim _ _
  rfl

/-- **One factor of a composite, read on a section, with the composite given as a variable.**
The hypothesis `hφ` is an equation of *morphisms*, so the identification of the composite is
never requested underneath an `app`: at the instance below, supplying the factored form
directly under an `app` exhausts the recursion limit, while an equation of morphisms followed by
this lemma does not. -/
public theorem comp_val_app_of {X : Scheme.{u}} {M N P : X.Modules} {φ : M ⟶ P}
    (a : M ⟶ N) (b : N ⟶ P) (hφ : φ = a ≫ b) (V : X.Opens)
    {x : M.val.obj (op V)} {y : N.val.obj (op V)} (he : a.val.app (op V) x = y) :
    φ.val.app (op V) x = b.val.app (op V) y := by
  subst hφ
  exact congrArg (b.val.app (op V)) he

/-- **The three tail factors of the comparison on a section, at the level of variables.**
Pseudofunctoriality of the pushforward is the identity, the chart congruence is a transport of
opens, and the functor image of the chart-level isomorphism is that isomorphism read at the
preimage. -/
public theorem tailGeneric_val_app {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (c : Z ⟶ X) (d : Y ⟶ X)
    (hcd : g ≫ c = d) (R N : Y.Modules) (e : R ≅ N) (V : X.Opens)
    (y : ((Scheme.Modules.pushforward c).obj
      ((Scheme.Modules.pushforward g).obj R)).val.obj (op V)) :
    ((Scheme.Modules.pushforwardComp g c).app R ≪≫
        (Scheme.Modules.pushforwardCongr hcd).app R ≪≫
        (Scheme.Modules.pushforward d).mapIso e).hom.val.app (op V) y =
      e.hom.val.app (op (d ⁻¹ᵁ V))
        (R.val.map (eqToHom (show d ⁻¹ᵁ V = g ⁻¹ᵁ (c ⁻¹ᵁ V) from hcd ▸ rfl)).op y) :=
  rfl

/-! ### The comparison at the instance -/

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (W U : S.Opens) (h : W ≤ U)
  (hW : IsAffineOpen W) (hU : IsAffineOpen U) (n : ℤ)

/-- The preimage of an open of the relative Proj in the chart of the smaller affine open is the
preimage, under the transition morphism, of its preimage in the chart of the larger one. -/
public theorem chart_preimage_eq (V : (relativeProj A).scheme.Opens) :
    (relativeProj A).chart W hW ⁻¹ᵁ V =
      projInclusionMap A W U h hW hU ⁻¹ᵁ ((relativeProj A).chart U hU ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, (relativeProj A).chart_transition W U h hW hU]

/-- **The image in the chart of the larger affine open of the preimage of `V` in the chart of
the smaller one lies in the preimage of `V`.** No hypothesis relating `V` to the inverse image
of `W` is needed, in contrast with
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.image_preimage_chart`, where the two opens are
*equal* and the hypothesis is used. -/
public theorem image_preimage_le_preimage (V : (relativeProj A).scheme.Opens) :
    projInclusionMap A W U h hW hU ''ᵁ ((relativeProj A).chart W hW ⁻¹ᵁ V) ≤
      (relativeProj A).chart U hU ⁻¹ᵁ V := by
  rw [chart_preimage_eq A W U h hW hU V]
  exact Scheme.Hom.image_preimage_le _ _

/-- The comparison is the unit factor followed by the tail. An equation of morphisms, which is
the level at which the identification is affordable here. -/
public theorem pushNested_eq :
    pushNested A W U h hW hU n =
      pushNestedUnit A W U h hW hU n ≫ (pushNestedTail A W U h hW hU n).hom :=
  rfl

/-- **The unit factor of the comparison, on sections.** It is the restriction map of the twist
on the chart of `U`, from the preimage of the open to the image of its preimage in the chart of
`W`.

The pushed-forward morphism is left to unification rather than written out: writing it and
asking for the resulting equation of morphisms by `rfl` exceeds the kernel's deterministic
timeout at this instance. -/
public theorem pushNestedUnit_app_val (V : (relativeProj A).scheme.Opens)
    (s : (pushforwardVal ((relativeProj A).chart U hU)
      (twistingSheaf (A.grading U) n)).obj (op V)) :
    (pushNestedUnit A W U h hW hU n).val.app (op V) s =
      (twistingSheaf (A.grading U) n).val.map
        (homOfLE ((projInclusionMap A W U h hW hU).image_preimage_le
          ((relativeProj A).chart U hU ⁻¹ᵁ V))).op s :=
  push_restrictUnit_val_app (projInclusionMap A W U h hW hU) ((relativeProj A).chart U hU)
    (twistingSheaf (A.grading U) n) V s

/-- **The tail at the instance, with the module and the chart-level comparison still
variables.** Instantiating this at the tail of the comparison is the one step not
reachable from outside the defining file; see the module docstring. -/
public theorem tailOf (V : (relativeProj A).scheme.Opens)
    {R : (AlgebraicGeometry.Proj (A.grading W)).Modules}
    (e : R ≅ twistingSheaf (A.grading W) n)
    (i : (relativeProj A).chart W hW ⁻¹ᵁ V ⟶
      projInclusionMap A W U h hW hU ⁻¹ᵁ ((relativeProj A).chart U hU ⁻¹ᵁ V))
    (y : ((Scheme.Modules.pushforward ((relativeProj A).chart U hU)).obj
      ((Scheme.Modules.pushforward (projInclusionMap A W U h hW hU)).obj R)).val.obj (op V)) :
    ((Scheme.Modules.pushforwardComp (projInclusionMap A W U h hW hU)
          ((relativeProj A).chart U hU)).app R ≪≫
        (Scheme.Modules.pushforwardCongr
            ((relativeProj A).chart_transition W U h hW hU)).app R ≪≫
        (Scheme.Modules.pushforward ((relativeProj A).chart W hW)).mapIso e).hom.val.app
        (op V) y =
      e.hom.val.app (op ((relativeProj A).chart W hW ⁻¹ᵁ V)) (R.val.map i.op y) :=
  (tailGeneric_val_app _ _ _ _ _ _ _ V y).trans
    (congrArg (e.hom.val.app (op ((relativeProj A).chart W hW ⁻¹ᵁ V)))
      (map_val_congr R _ i y))

/-- **The comparison on sections, conditional on the tail's action.** The hypothesis is that the
tail carries a section to the chart-level isomorphism applied to its restriction along some
inclusion of opens -- the inclusion is a free argument, since morphisms between opens are
unique.

Granting it, the comparison carries a section `s` over an arbitrary open `V` of the relative
Proj to the chart-level isomorphism applied to the restriction of `s` to the image, in the chart
of `U`, of the preimage of `V` in the chart of `W`. The two restriction maps that the unit
factor and the chart congruence contribute are composed into the single one by `map_comp_val`.

This is the statement the pointwise rigidity criterion consumes: its right-hand side mentions no
construction on the relative projective spectrum, and the pointwise content of
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.restrictTwistIso` is Tag 01MY's fibre
comparison. -/
public theorem pushNested_app_val_of (V : (relativeProj A).scheme.Opens)
    (i : (relativeProj A).chart W hW ⁻¹ᵁ V ⟶
      projInclusionMap A W U h hW hU ⁻¹ᵁ ((relativeProj A).chart U hU ⁻¹ᵁ V))
    (htail : ∀ y : ((Scheme.Modules.pushforward ((relativeProj A).chart U hU)).obj
        ((Scheme.Modules.pushforward (projInclusionMap A W U h hW hU)).obj
          (restrictedTwist A W U h hW hU n))).val.obj (op V),
      (pushNestedTail A W U h hW hU n).hom.val.app (op V) y =
        (restrictTwistIso A W U h hW hU n).hom.val.app
            (op ((relativeProj A).chart W hW ⁻¹ᵁ V))
          ((restrictedTwist A W U h hW hU n).val.map i.op y))
    (s : (pushforwardVal ((relativeProj A).chart U hU)
      (twistingSheaf (A.grading U) n)).obj (op V)) :
    (pushNested A W U h hW hU n).val.app (op V) s =
      (restrictTwistIso A W U h hW hU n).hom.val.app
          (op ((relativeProj A).chart W hW ⁻¹ᵁ V))
        ((twistingSheaf (A.grading U) n).val.map
          (homOfLE (image_preimage_le_preimage A W U h hW hU V)).op s) := by
  refine Eq.trans (comp_val_app_of _ _ (pushNested_eq A W U h hW hU n) V
    (pushNestedUnit_app_val A W U h hW hU n V s)) ?_
  refine Eq.trans (htail _) ?_
  refine congrArg ((restrictTwistIso A W U h hW hU n).hom.val.app
    (op ((relativeProj A).chart W hW ⁻¹ᵁ V))) ?_
  refine Eq.trans (restrict_val_map (projInclusionMap A W U h hW hU)
    (twistingSheaf (A.grading U) n) _ _) ?_
  exact map_comp_val (X := AlgebraicGeometry.Proj (A.grading U))
    (twistingSheaf (A.grading U) n) _ _ _ s

end Stacks.AlgebraicGeometry.NestedCocycleReduction

end
