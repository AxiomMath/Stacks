module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSchemeStructureSharp
public import StacksFrontier.CategoryTheory.Sites.PushforwardContinuousCalculus

/-!
# The two chart comparisons of a representable direct image are the same map

For a representable morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` this development
carries **two** identifications of the sections of a direct image over an étale scheme chart `V`
of `Y` with the sections over the base-changed chart `X ×_Y V`, built in different ways and in
different categories:

* `AlgebraicGeometry.Space.chartProjectionSharpDirectImage`, a homomorphism of sheaves of rings,
  assembled from the projections `AlgebraicGeometry.Space.chartProjection` of the limit that
  computes the sections of the direct image, at the base-changed chart — which
  `AlgebraicGeometry.Space.chartBaseChangeArrowIsInitial` exhibits as an initial index.  It is
  the one Stacks 03G8, part (2) is stated for, by
  `AlgebraicGeometry.Space.fSharp_comp_chartProjectionSharpDirectImage`.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing`, an isomorphism of
  *functors* of sheaves of commutative rings, obtained by reflecting the geometric comparison
  `AlgebraicGeometry.Space.smallToposMorphismTypeU_comparison` of Stacks 03G2, part (1) along
  the comparison equivalence of Stacks 03G1 against the chart-base-change comparison
  `AlgebraicGeometry.Space.smallBaseChange_pushforward_comparisonTypeU` of Stacks 03G2,
  part (4).  It is the one `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` reads at a
  single chart.

**This file proves that they are the same map**, so that Stacks 03G8, part (2) is available for
the second one too.  Nothing related them before: the second was used only through its
invertibility (`AlgebraicGeometry.Space.isIso_fSharp_app_smallBaseChange`), and a square written
with it therefore had no computable edge along the structure map.

## Main results

* `AlgebraicGeometry.Space.directImageChartProjection_smallEtaleRingedToposHom_representable`:
  **the geometric comparison, read on the sections over a chart `V`, is the chart projection to
  the base-changed chart**, for an arbitrary sheaf of sets on the small étale site of `X`.  This
  is the identification, at the level the two constructions have in common.
* `AlgebraicGeometry.Space.sheafCompose_smallEtaleRingedToposHom_representableRing`: the same on
  sheaves of rings — forgetting commutativity in the comparison of Stacks 03G8 at the structure
  sheaf of `X` gives `AlgebraicGeometry.Space.chartProjectionSharpDirectImage` on the nose.
* `AlgebraicGeometry.Space.fSharp_comp_smallEtaleRingedToposHom_representableRing` is
  **Stacks 03G8, part (2) for the chart-base-change comparison**: the structure map `f♯` of the
  morphism of small étale ringed topoi, followed by that comparison, is pullback of regular
  functions along the cartesian projections `X ×_Y V ⟶ V`, as a homomorphism of sheaves of
  commutative rings.
* `AlgebraicGeometry.Space.fSharp_app_comp_pushforwardAlgebraSectionsIso` is that equality at a
  single chart: the structure map of a representable `Y ⟶ X` on the sections over `V`, followed
  by `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`, is pullback of regular functions
  along `Y ×_X V ⟶ V`.

## Implementation notes

The comparison of the second kind is a
`CategoryTheory.Functor.preimageIso` along whiskering by the comparison restriction of
Stacks 03G1, so its component at a *restricted* sheaf is the composite it was chosen over.
There the first factor is `AlgebraicGeometry.Space.smallToposMorphismTypeU_comparison`, whose
reading on charts is `AlgebraicGeometry.Space.directImageChartProjection_comparison`, and the
second factor is restriction along the chart comparison
`AlgebraicGeometry.Space.smallBaseChangeComparisonIso` of Stacks 03G2, part (4) — which is
exactly the morphism indexing the base-changed chart,
`AlgebraicGeometry.Space.chartBaseChangeArrow`.  That is
`AlgebraicGeometry.Space.smallBaseChange_pushforward_comparisonTypeU_inv_app_apply`, and it is
an equality by `rfl`: restriction along a composite of functors of sites is composition of
restrictions on the nose, by
`CategoryTheory.Functor.sheafPushforwardContinuousComp`, so only the middle factor of the
chart-base-change comparison survives, and that one is restriction along the comparison by
`CategoryTheory.Functor.sheafPushforwardContinuousIso_hom_app_hom_app`.  The passage to an
arbitrary sheaf is naturality of both sides in the sheaf, against the counit of the comparison
equivalence.

The ring-structured statements are then deduced, rather than proved again: the underlying map of
the comparison of sheaves of commutative rings is the one of sheaves of sets by
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing_forget`, and
`AlgebraicGeometry.Space.chartProjectionSharpDirectImage` is the chart projection on sections by
`rfl`; so the sheaf-of-rings identification is the sheaf-of-sets one read at the structure
sheaf, and the `CommRingCat` form follows from it by faithfulness of forgetting commutativity.
No `CategoryTheory.eqToHom` occurs anywhere: the objects on the two sides of each statement are
already the same.

**No `@[stacks]` attribute is placed.**  The identification itself is internal to this
development, and Stacks 03G8, part (2) is already registered on
`AlgebraicGeometry.Space.fSharp_comp_chartProjectionSharpDirectImage`, whose content
`AlgebraicGeometry.Space.fSharp_comp_smallEtaleRingedToposHom_representableRing` restates for
the other comparison; a second attribute would add no covered content.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1), the comparison of the
  two étale sites.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), parts (1) and (4), the
  direct image and the chart-base-change square.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map and
  its part (2).
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R), the structure map of a
  morphism of sites of schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback

universe u u₁ u₂ u₃ v₁ v₂ v₃

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- The component, at an object in the image, of an isomorphism of functors chosen along
whiskering by a functor on the left. -/
private lemma whiskeringLeft_preimageIso_hom_app {A : Type u₁} [Category.{v₁} A]
    {Bb : Type u₂} [Category.{v₂} Bb] {E : Type u₃} [Category.{v₃} E] (L : A ⥤ Bb)
    [Functor.Full ((Functor.whiskeringLeft A Bb E).obj L)]
    [Functor.Faithful ((Functor.whiskeringLeft A Bb E).obj L)]
    {F G : Bb ⥤ E} (e : L ⋙ F ≅ L ⋙ G) (Z : A) :
    (((Functor.whiskeringLeft A Bb E).obj L).preimageIso e).hom.app (L.obj Z) = e.hom.app Z := by
  rw [Functor.preimageIso_hom]
  exact congrArg (fun t : L ⋙ F ⟶ L ⋙ G => t.app Z)
    (Functor.map_preimage ((Functor.whiskeringLeft A Bb E).obj L) e.hom)

/-! ### The chart-base-change comparison, read on the sections over a chart -/

/-- **The chart-base-change comparison of Stacks 03G2, part (4), read on the sections of a
spaces-étale sheaf over an étale chart `V` of `Y`, is restriction along the comparison
`AlgebraicGeometry.Space.smallBaseChangeComparisonIso` of the two base changes of `V`.**

Restriction of sheaves along a composite of functors of sites is composition of restrictions on
the nose, so the two outer factors of
`AlgebraicGeometry.Space.smallBaseChange_pushforward_comparisonTypeU` contribute nothing, and
the middle one is restriction along the comparison of the chart base changes. -/
theorem smallBaseChange_pushforward_comparisonTypeU_inv_app_apply (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u)) (V : SmallEtale B S hS Y.1)
    (a : ((comparisonFunctor B S hS Y ⋙ (spacesBaseChange B S hS f).functor).op ⋙ H.obj).obj
      (op V)) :
    letI := isContinuous_smallBaseChange B S hS f hf
    ((smallBaseChange_pushforward_comparisonTypeU B S hS f hf).inv.app H).hom.app (op V) a =
      H.obj.map (smallBaseChangeComparisonIso B S hS f hf V).hom.op a :=
  rfl

/-! ### The two comparisons agree -/

/-- `AlgebraicGeometry.Space.directImageChartProjection_smallEtaleRingedToposHom_representable`
for a sheaf restricted from the spaces-étale site, where the comparison of Stacks 03G8 is the
composite it was chosen over: the geometric comparison of Stacks 03G2, part (1), followed by the
inverse of the chart-base-change comparison of Stacks 03G2, part (4). -/
private theorem representable_hom_app_restriction (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u)) (V : SmallEtale B S hS Y.1)
    (a : ((smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj
      ((smallEtaleComparisonRestriction B S hS X).obj H))) :
    letI := isContinuous_smallBaseChange B S hS f hf
    ((smallEtaleRingedToposHom_representable B S hS f hf).hom.app
        ((smallEtaleComparisonRestriction B S hS X).obj H)).hom.app (op V) a =
      (directImageChartProjection B S hS f V (chartBaseChangeArrow B S hS f hf V)).app
        ((smallEtaleComparisonRestriction B S hS X).obj H) a := by
  let := isContinuous_smallBaseChange B S hS f hf
  have h0 : ((smallEtaleRingedToposHom_representable B S hS f hf).hom.app
        ((smallEtaleComparisonRestriction B S hS X).obj H)) =
      (smallToposMorphismTypeU_comparison B S hS f ≪≫
        (smallBaseChange_pushforward_comparisonTypeU B S hS f hf).symm).hom.app H :=
    whiskeringLeft_preimageIso_hom_app _ _ H
  rw [directImageChartProjection_comparison B S hS f V (chartBaseChangeArrow B S hS f hf V) H a,
    h0]
  exact (smallBaseChange_pushforward_comparisonTypeU_inv_app_apply B S hS f hf H V _).symm

/-- **The two chart comparisons of a representable direct image are the same map.**

For a representable morphism `f : X ⟶ Y` of algebraic spaces, a sheaf of sets `F` on the small
étale site of `X` and an étale scheme chart `V` of `Y`, the comparison of Stacks 03G8 between the
direct image along `f` and base change of étale scheme charts,
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`, read on the sections over `V`,
is the projection `AlgebraicGeometry.Space.directImageChartProjection` of the limit computing
those sections to the base-changed chart `X ×_Y V`.

It is enough to prove this for a sheaf restricted from the spaces-étale site, where the
comparison is a composite of the geometric comparison of Stacks 03G2, part (1), whose chart
reading is `AlgebraicGeometry.Space.directImageChartProjection_comparison`, and restriction
along the comparison of the two base changes of `V`: both sides are natural in the sheaf, by
naturality of the comparison and by
`AlgebraicGeometry.Space.directImageChartProjection_map`, and every sheaf is isomorphic to a
restricted one. -/
theorem directImageChartProjection_smallEtaleRingedToposHom_representable (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1)
    (a : ((smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj F)) :
    letI := isContinuous_smallBaseChange B S hS f hf
    ((smallEtaleRingedToposHom_representable B S hS f hf).hom.app F).hom.app (op V) a =
      (directImageChartProjection B S hS f V (chartBaseChangeArrow B S hS f hf V)).app F a := by
  let := isContinuous_smallBaseChange B S hS f hf
  set H := (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj F
  set e : F ≅ (smallEtaleComparisonRestriction B S hS X).obj H :=
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.app F).symm
  refine Function.LeftInverse.injective
    (f := e.hom.hom.app (chartBaseChangeArrow B S hS f hf V).right)
    (g := e.inv.hom.app (chartBaseChangeArrow B S hS f hf V).right)
    (fun x => Sheaf.iso_inv_hom_app_apply e (chartBaseChangeArrow B S hS f hf V).right x) ?_
  rw [← directImageChartProjection_map B S hS f V (chartBaseChangeArrow B S hS f hf V) e.hom a,
    ← representable_hom_app_restriction B S hS f hf H V _]
  exact (Sheaf.hom_congr_app_apply
    ((smallEtaleRingedToposHom_representable B S hS f hf).hom.naturality e.hom) (op V) a).symm

/-- **The two chart comparisons agree on sheaves of rings.**  Forgetting commutativity in the
comparison of Stacks 03G8 between the direct image of sheaves of commutative rings and base
change of étale scheme charts, taken at the structure sheaf of `X`, gives
`AlgebraicGeometry.Space.chartProjectionSharpDirectImage`, the identification of the sections of
`f_*𝒪_X` over an étale chart `V` of `Y` with the regular functions on `X ×_Y V` assembled from
the projections of the limit.

The comparison of sheaves of commutative rings is the comparison of sheaves of sets on
underlying sheaves, by
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing_forget`, and
`AlgebraicGeometry.Space.chartProjectionSharpDirectImage` is the chart projection on sections;
so this is
`AlgebraicGeometry.Space.directImageChartProjection_smallEtaleRingedToposHom_representable` read
at the structure sheaf. -/
theorem sheafCompose_smallEtaleRingedToposHom_representableRing (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    (sheafCompose (SmallEtale.topology B S hS Y.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((smallEtaleRingedToposHom_representableRing B S hS f hf).hom.app
          (smallEtaleRingedTopos B S hS X).O) =
      chartProjectionSharpDirectImage B S hS f hf := by
  let := isContinuous_smallBaseChange B S hS f hf
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext Z
  refine RingCat.hom_ext (RingHom.ext fun z => ?_)
  exact (Sheaf.hom_congr_app_apply
    (smallEtaleRingedToposHom_representableRing_forget B S hS f hf
      (smallEtaleRingedTopos B S hS X).O) Z z).trans
    (directImageChartProjection_smallEtaleRingedToposHom_representable B S hS f hf
      (structureSetSheaf B S hS X) Z.unop z)

/-! ### Stacks 03G8, part (2) for the chart-base-change comparison -/

/-- **Stacks 03G8, part (2), for the chart-base-change comparison of a representable morphism.**
The structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of the morphism of small étale ringed topoi of
Stacks 03G8, followed by the comparison
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing` of the direct image with
base change of étale scheme charts, is pullback of regular functions along the cartesian
projections `X ×_Y V ⟶ V` — the structure map of Stacks 070R, part (2).

This is `AlgebraicGeometry.Space.fSharp_comp_chartProjectionSharpDirectImage`, the same
statement for the other comparison, carried across
`AlgebraicGeometry.Space.sheafCompose_smallEtaleRingedToposHom_representableRing`; forgetting
commutativity is faithful, so the equality of sheaves of commutative rings follows from the one
of sheaves of rings. -/
theorem fSharp_comp_smallEtaleRingedToposHom_representableRing (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    (smallEtaleRingedToposHom B S hS f).fSharp ≫
        (smallEtaleRingedToposHom_representableRing B S hS f hf).hom.app
          (smallEtaleRingedTopos B S hS X).O =
      cartesianProjectionSharpCommRing B S hS f hf := by
  let := isContinuous_smallBaseChange B S hS f hf
  have := (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
    (SmallEtale.topology B S hS Y.1)).faithful
  apply Functor.map_injective (sheafCompose (SmallEtale.topology B S hS Y.1)
    (forget₂ CommRingCat.{u} RingCat.{u}))
  rw [Functor.map_comp, sheafCompose_smallEtaleRingedToposHom_representableRing,
    forgetCommRingSheaf_map_fSharp, sheafCompose_cartesianProjectionSharpCommRing]
  exact structureSharp_comp_chartProjectionSharpDirectImage B S hS f hf

/-- **Stacks 03G8, part (2), at a single étale chart, for the sections of a direct-image
algebra.**  Let `Y` be an algebraic space over `X` with representable structure morphism and `V`
an étale scheme chart of `X`.  The structure map `𝒪_X ⟶ Y.hom_*𝒪_Y` on the sections over `V`,
followed by the identification `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` of those
sections with the regular functions on the scheme `Y ×_X V`, is pullback of regular functions
along the cartesian projection `Y ×_X V ⟶ V`.

This is the reading at `V` of
`AlgebraicGeometry.Space.fSharp_comp_smallEtaleRingedToposHom_representableRing`. -/
theorem fSharp_app_comp_pushforwardAlgebraSectionsIso {Xx : AlgebraicSpaces B S hS}
    (Yy : Over Xx) (hY : yoneda.relativelyRepresentable Yy.hom.hom)
    (V : SmallEtale B S hS Xx.1) :
    (smallEtaleRingedToposHom B S hS Yy.hom).fSharp.hom.app (op V) ≫
        (pushforwardAlgebraSectionsIso B S hS Yy hY V).hom =
      ((BigFppfOver.toScheme B S hS).map (hY.snd V.1.hom)).appTop := by
  let := isContinuous_smallBaseChange B S hS Yy.hom hY
  exact NatTrans.congr_app
    (congrArg (fun m : (smallEtaleRingedTopos B S hS Xx).O ⟶
        ((smallBaseChange B S hS Yy.hom hY).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS Xx.1)
          (SmallEtale.topology B S hS Yy.left.1)).obj
        (smallEtaleRingedTopos B S hS Yy.left).O => m.hom)
      (fSharp_comp_smallEtaleRingedToposHom_representableRing B S hS Yy.hom hY)) (op V)

end AlgebraicGeometry.Space

end
