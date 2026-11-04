module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp

/-!
# Composition of `f`-maps

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` contained in
a big fppf site `B`.  Stacks 03G3 attaches to a sheaf of sets on the small étale site of the
target and one on the small étale site of the source the set of *`f`-maps* between them,
`AlgebraicGeometry.Space.FMap`, and Stacks 03G4 — `AlgebraicGeometry.Space.chartCorrespondence`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartCorrespondence.lean`) — identifies them with the
homomorphisms into the direct image.  This file composes them:

`AlgebraicGeometry.Space.FMap.comp` takes a `g`-map from `R` to `Q` and an `f`-map from `Q` to
`P` to an `f ≫ g`-map from `R` to `P`.

Composition cannot be defined chart diagram by chart diagram.  A chart diagram over `f ≫ g` is
a commutative square built from an étale scheme chart `U` of `X` and an étale scheme chart `W`
of `Z`, and the morphism `U ⟶ W` it carries need not factor through any étale scheme chart of
`Y` at all: `U` is étale over `X` and `X ⟶ Y` is arbitrary, so `U` is not étale over `Y`.  What
is true is the *iterated-limit* identification: the sections of `g_*(f_*P)` over `W` are the
limit, over the étale scheme charts `V` of `Y` above `Y ×_Z W`, of the sections of `f_*P` over
`V`, which are in turn the limit over the étale scheme charts of `X` above `X ×_Y V`; and that
iterated limit is the single limit over the étale scheme charts of `X` above `X ×_Z W`, because
`X ×_Y (Y ×_Z W) ≅ X ×_Z W`.  That last isomorphism is
`AlgebraicGeometry.Space.spacesBaseChange_comp`, Stacks 03G2, part (2), and the composite of
direct images it induces is `AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU`.
So the composite `f`-map is *defined* by transporting the composite of the two homomorphisms
into the direct images back across the chart correspondence, and the chart formula
`AlgebraicGeometry.Space.FMap.comp_app` is a theorem.

The route is the one `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleStructureMapComp.lean`
takes for the structure map: transport the homomorphism to the spaces-étale site, where the
comparison of iterated direct images becomes restriction along
`AlgebraicGeometry.Space.spacesBaseChange_comp`, and read off chart projections there.  That
file does it for the structure sheaf only; the transport
`AlgebraicGeometry.Space.ranSpacesHom` below is the same construction for an arbitrary
homomorphism into the direct image, and
`AlgebraicGeometry.Space.structureSharpSpaces_eq_ranSpacesHom` records that it *is* the same
construction, by `rfl`.  That `rfl` is evidence that the two agree; it does not make the
structure-sheaf copy go away, and the implementation notes below say what paying that debt
would take.

## Main definitions

* `AlgebraicGeometry.Space.ranSpacesHom` is a homomorphism into the direct image of sheaves of
  sets, transported to the spaces-étale site of the target.  It is
  `AlgebraicGeometry.Space.structureSharpSpaces` for an arbitrary homomorphism in place of the
  structure map.
* `AlgebraicGeometry.Space.fmapRanComp` is the homomorphism from `R` into the direct image of
  `P` along `f ≫ g` built out of a `g`-map and an `f`-map: the homomorphism of the `g`-map,
  followed by the direct image of the homomorphism of the `f`-map read on the spaces-étale
  site, followed by the comparison of the iterated direct image with the direct image of the
  composite.
* `AlgebraicGeometry.Space.FMap.comp` is **the composite of two `f`-maps**: the `f`-map which
  the chart correspondence of Stacks 03G4 attaches to the composite of the two homomorphisms
  into the direct images, taken with the comparison of Stacks 03G2, part (3).  Only existing API
  enters the definition; `AlgebraicGeometry.Space.fmapRanComp` is proof machinery, identified
  with it by `AlgebraicGeometry.Space.fmapRan_comp`.
* `AlgebraicGeometry.Space.ChartDiagram.comp` is the chart diagram over `f ≫ g` obtained by
  composing the vertical scheme morphisms of a chart diagram over `f` and one over `g` sharing
  the middle chart.

The argument order is outer-first, `FMap.comp … ξ η` with `ξ` the `g`-map, matching
`CategoryTheory.MorphismOfTopoi.comp` and `AlgebraicGeometry.RingedToposHom.comp`.  The repo's
`f`-map composition for *topological* spaces,
`Stacks.Sheaves.StacksFMap.compPresheaf` (`StacksFrontier/Topology/Sheaves/Functors/FMap/Comp.lean`),
is inner-first; both conventions are in the repo and the topos one is followed here because the
definition is transport of composition of direct-image homomorphisms.

## Main results

* `AlgebraicGeometry.Space.FMap.comp_app`: **the chart formula for the composite.**  On a chart
  diagram over `f ≫ g` which *does* factor through an étale scheme chart of `Y`, the composite
  `f`-map is the composite of the two components.  This is the sense in which
  `AlgebraicGeometry.Space.FMap.comp` is composition of maps of sections.  It is *not* a
  characterization — see `AlgebraicGeometry.Space.FMap.comp_unique`.
* `AlgebraicGeometry.Space.fmapRan_comp`: **the composite `f`-map, read in the Kan-extension
  picture, is `AlgebraicGeometry.Space.fmapRanComp`.**  This is the substantive half of the
  compatibility of Stacks 03G4 with composition — the half the chart formula is computed from —
  the other half, `AlgebraicGeometry.Space.fmapDirectImageEquiv_comp`, being how the composite
  is defined.
* `AlgebraicGeometry.Space.FMap.comp_unique`: the composite is the *only* `f ≫ g`-map whose
  homomorphism into the direct image is that composite.  This, and not the chart formula, is
  what pins the composite down: the chart diagrams that factor through `Y` do not exhaust the
  index category, so `AlgebraicGeometry.Space.FMap.comp_app` determines only some of the chart
  projections.
* `AlgebraicGeometry.Space.ranSpacesHom_app_ranProj`: a chart projection of the transported
  homomorphism is the homomorphism read on the chart.  This is
  `AlgebraicGeometry.Space.structureSharpSpaces_app_chart` for an arbitrary homomorphism,
  composed with naturality.
* `AlgebraicGeometry.Space.ranProj_ranSpacesHom_comp`: the chart projection of the composite, at an
  étale scheme chart of `X` above `X ×_Z W` coming from a chart of `Y` above `Y ×_Z W`, is the
  iterated chart projection.  This is the iterated-limit identification in the form the chart
  formula needs.
* `AlgebraicGeometry.Space.chartLift_chartDiagram_comp`: the cartesian form of a composed chart
  diagram is the composite of the cartesian forms, through
  `AlgebraicGeometry.Space.chartBaseChangeComp`.  This is the chart-diagram counterpart of
  `AlgebraicGeometry.Space.chartBaseChangeMap_comp_chart`.

## Implementation notes

The pointwise-limit apparatus used here is the one of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleStructureMapComp.lean`
(`AlgebraicGeometry.Space.ranProj`, `ranProj_map`, `ranProj_app_apply`); no fourth copy is
made.  The `ranChartCone` copy of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartCorrespondence.lean` is unavoidable in two places,
both because the existing statements are phrased with it: `AlgebraicGeometry.Space.fmapRanApp_π`,
which is what computes a chart projection of the homomorphism of an `f`-map, and
`AlgebraicGeometry.Space.ranChartCone_π_congr`, which transports a chart projection along an
equality of indices and has no `ranProj` counterpart.  The two copies are interchanged by
`AlgebraicGeometry.Space.ranProj_app_apply`, and that is the only bridge used.

`AlgebraicGeometry.Space.ranSpacesHom_comp_formula` subsumes
`AlgebraicGeometry.Space.forgetRing_comp_structure_formula`, which is its case of the structure
map, exactly as `AlgebraicGeometry.Space.ranSpacesHom` subsumes
`AlgebraicGeometry.Space.structureSharpSpaces` (both checked by instantiating at the structure
map).  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleStructureMapComp.lean` is not edited
here, so the structure-sheaf copies coexist with these.

There is a cheaper way to pay that debt than generalizing by hand, and it is worth recording.
`AlgebraicGeometry.Space.ranSpacesHom` is
`AlgebraicGeometry.Space.presentationComparison`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartCorrespondence.lean`) composed with the direct image
of the Kan-extension comparison, *provided* that declaration's hypothesis `i : P ≅ …` is relaxed
to a plain homomorphism `i : P ⟶ …`; `ψ` already has that type on the nose, since
`AlgebraicGeometry.Space.smallEtaleDirectImage` is definitionally the conjugated spaces-étale
direct image.  The relaxation is free all the way down:
`AlgebraicGeometry.Space.counit_comp_presentation` and
`CategoryTheory.Equivalence.counit_comp_hom_eq_map_rightAdjointUniq` both go through unchanged,
because neither proof uses `i.inv` — the second consumes `i.hom` only, through
`e.counit.naturality i.hom`.  With that done, `AlgebraicGeometry.Space.ranSpacesHom` loses its
own proof apparatus (`AlgebraicGeometry.Space.restriction_map_ranSpacesHom` becomes a short
corollary of the relaxed `counit_comp_presentation`), and the six structure-sheaf declarations
of `SmallEtaleStructureMapComp.lean` between `structureSharpSpacesAux` and
`forgetRing_comp_structure_formula` can be retired in favour of the general ones.  That is a
cross-file refactor of two cited files and is deliberately not done here.

Two elaboration constraints shape the proofs.  First, the sections of the right
Kan extension have two spellings — `((comparisonFunctor B S hS X).op.ran.obj P.obj).obj (op A)`
and `((smallEtaleComparisonRan B S hS X).obj P).obj.obj (op A)` — which are definitionally
equal but *not* equal at `implicit` transparency, since `sheafPushforwardCocontinuous` is
semireducible.  A `rw` whose motive crosses that boundary fails with "the target expression is
not type-correct under the `implicit` transparency level", so every lemma below is stated in
one spelling throughout and the boundary is crossed only by term application or a closing
`rfl`.  Second, and for the same reason, a `congrArg`/`Eq.trans` chain crossing the boundary
sends the elaborator into a non-terminating `whnf`, while the *same* step written as a `rw` in
tactic mode succeeds immediately: `AlgebraicGeometry.Space.ranSpacesHom_app_ranProj` is an
instance of this, and it is why these proofs are tactic proofs where the structure-map file
uses term-mode chains.

What is *not* proved here is associativity of `AlgebraicGeometry.Space.FMap.comp`.  It reduces,
through `AlgebraicGeometry.Space.fmapDirectImageEquiv_comp`, to the associativity coherence of
the geometric comparison of Stacks 03G2, part (3), and that coherence **is** proved:
`AlgebraicGeometry.Space.smallToposMorphism_comp_assoc`
(`StacksFrontier/AlgebraicGeometry/Spaces/SpacesBaseChangeAssoc.lean`) carries
`@[stacks 03G2 "part (3), associativity of the composition isomorphism"]`.  What is missing is
only its transcription from `Type (u + 1)` to `Type u`, the universe at which a ringed topos
declares its underlying topos — the same transcription
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` is of
`AlgebraicGeometry.Space.smallToposMorphism_comp`, and which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRingedToposHom.lean` describe as "the proof is
the same, the sheaf universe playing no role in it".  So associativity is reachable and not
blocked.  (The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModuleCompIso.lean` say that coherence is
"not proved anywhere in this development"; it is in fact proved, as
`smallToposMorphism_comp_assoc`.)

No declaration here carries a `@[stacks]` attribute, and that is deliberate.  What Stacks 03G4
asserts is the two bijections together with their characterization on chart sections, and all
of that is proved in `StacksFrontier/AlgebraicGeometry/Spaces/ChartCorrespondence.lean`:
`AlgebraicGeometry.Space.chartCorrespondence` carries
`@[stacks 03G4 "f-maps are exactly maps into the direct image"]` and bundles the bijection with
`AlgebraicGeometry.Space.IsChartCorrespondence`, proved by
`AlgebraicGeometry.Space.fmapDirectImageEquiv_isChartCorrespondence`, and
`AlgebraicGeometry.Space.fmapInverseImageEquiv` carries
`@[stacks 03G4 "f-maps are exactly maps out of the inverse image"]`.  Composition of `f`-maps
is not among the assertions of that tag, and the composition law of Stacks 03G8 is separately
proved and tagged at `AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp`.  This file
is the infrastructure between the two, and what Stacks 03LU's composition fields consume.

## References

* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-! ### A homomorphism into the direct image, transported to the spaces-étale site -/

/-- A homomorphism `ψ : Q ⟶ f_*P` of sheaves of sets on the small étale site of `Y`, transported
to the spaces-étale site of `Y`: read through the quasi-inverse of the comparison equivalence of
Stacks 03G1, with the Kan-extension form of that quasi-inverse on both sides.

This is `AlgebraicGeometry.Space.structureSharpSpaces` with the structure map replaced by an
arbitrary homomorphism; `AlgebraicGeometry.Space.structureSharpSpaces_eq_ranSpacesHom` records that
it is the same construction. -/
noncomputable def ranSpacesHom (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (ψ : Q ⟶ (smallEtaleDirectImage B S hS f).obj P) :
    (smallEtaleComparisonRan B S hS Y).obj Q ⟶
      (spacesDirectImage B S hS f).obj ((smallEtaleComparisonRan B S hS X).obj P) :=
  ((smallEtaleComparisonRanIso B S hS Y).inv.app Q ≫
      (smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.map ψ ≫
      (smallEtaleComparisonRestriction B S hS Y).asEquivalence.unitIso.inv.app
        ((spacesDirectImage B S hS f).obj
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P))) ≫
    (spacesDirectImage B S hS f).map ((smallEtaleComparisonRanIso B S hS X).hom.app P)

/-- The structure map of `f` on the spaces-étale site is the transport of the structure map of
sheaves of sets: `AlgebraicGeometry.Space.ranSpacesHom` subsumes
`AlgebraicGeometry.Space.structureSharpSpaces`, on the nose. -/
theorem structureSharpSpaces_eq_ranSpacesHom (f : X ⟶ Y) :
    structureSharpSpaces B S hS f =
      ranSpacesHom B S hS f (structureSetSheaf B S hS X) (structureSetSheaf B S hS Y)
        (structureSharpSet B S hS f) := rfl

/-- Restricting the transported homomorphism along the comparison functor of Stacks 03G1 gives
back the homomorphism, read through the counit of the Kan-extension adjunction and the
Kan-extension form of the direct image.

This is `AlgebraicGeometry.Space.restriction_map_structureSharpSpaces` for an arbitrary
homomorphism; the two ingredients are
`AlgebraicGeometry.Space.restriction_map_unitIso_inv` and
`AlgebraicGeometry.Space.restriction_map_ranIso_inv_comp_counitIso`. -/
theorem restriction_map_ranSpacesHom (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (ψ : Q ⟶ (smallEtaleDirectImage B S hS f).obj P) :
    (smallEtaleComparisonRestriction B S hS Y).map (ranSpacesHom B S hS f P Q ψ) =
      (comparisonAdjunction B S hS Y).counit.app Q ≫
        ψ ≫ (smallEtaleDirectImageRanIso B S hS f).hom.app P := by
  have haux : (smallEtaleComparisonRestriction B S hS Y).map
        ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.map ψ ≫
          (smallEtaleComparisonRestriction B S hS Y).asEquivalence.unitIso.inv.app
            ((spacesDirectImage B S hS f).obj
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P))) =
      (smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.app Q ≫ ψ :=
    (CategoryTheory.Functor.map_comp _ _ _).trans
      ((congrArg (fun m ↦ (smallEtaleComparisonRestriction B S hS Y).map
          ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.map ψ) ≫ m)
        (restriction_map_unitIso_inv B S hS Y _)).trans
        ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.naturality ψ))
  have e2 := congrArg
    (fun m ↦ ((smallEtaleComparisonRestriction B S hS Y).map
          ((smallEtaleComparisonRanIso B S hS Y).inv.app Q) ≫ m) ≫
        (smallEtaleComparisonRestriction B S hS Y).map
          ((spacesDirectImage B S hS f).map
            ((smallEtaleComparisonRanIso B S hS X).hom.app P)))
    haux
  exact e2.trans (congrArg₂ (fun p q ↦ p ≫ q)
    (restriction_map_ranIso_inv_comp_counitIso B S hS Y Q)
    (rfl : ψ ≫ (smallEtaleDirectImageRanIso B S hS f).hom.app P =
      ψ ≫ (smallEtaleDirectImageRanIso B S hS f).hom.app P))

/-- On sections over an étale scheme chart of `Y`, the transported homomorphism is the
homomorphism itself, precomposed with the counit of the Kan-extension adjunction.

This is `AlgebraicGeometry.Space.structureSharpSpaces_app_chart` for an arbitrary
homomorphism. -/
theorem ranSpacesHom_app_chart (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (ψ : Q ⟶ (smallEtaleDirectImage B S hS f).obj P) (V : SmallEtale B S hS Y.1)
    (q : ((smallEtaleComparisonRan B S hS Y).obj Q).obj.obj
      (op ((comparisonFunctor B S hS Y).obj V))) :
    (ranSpacesHom B S hS f P Q ψ).hom.app (op ((comparisonFunctor B S hS Y).obj V)) q =
      (ψ ≫ (smallEtaleDirectImageRanIso B S hS f).hom.app P).hom.app (op V)
        (((comparisonAdjunction B S hS Y).counit.app Q).hom.app (op V) q) :=
  congrArg (fun m ↦ m.hom.app (op V) q) (restriction_map_ranSpacesHom B S hS f P Q ψ)

/-- Restricting a section of the right Kan extension to an étale scheme chart above its object
and applying the transported homomorphism there is applying the homomorphism to the chart
projection of the section.

This is `AlgebraicGeometry.Space.ranSpacesHom_app_chart` combined with naturality of the
transported homomorphism. -/
theorem ranSpacesHom_app_ranProj (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (ψ : Q ⟶ (smallEtaleDirectImage B S hS f).obj P) (A : SpacesEtale B S hS Y)
    (j : StructuredArrow (op A) (comparisonFunctor B S hS Y).op)
    (σ : ((smallEtaleComparisonRan B S hS Y).obj Q).obj.obj (op A)) :
    ((spacesDirectImage B S hS f).obj
          ((smallEtaleComparisonRan B S hS X).obj P)).obj.map j.hom
        ((ranSpacesHom B S hS f P Q ψ).hom.app (op A) σ) =
      (ψ ≫ (smallEtaleDirectImageRanIso B S hS f).hom.app P).hom.app (op j.right.unop)
        ((ranProj B S hS Y A j).app Q σ) := by
  rw [← NatTrans.naturality_apply (ranSpacesHom B S hS f P Q ψ).hom j.hom σ]
  exact ranSpacesHom_app_chart B S hS f P Q ψ j.right.unop
    (((smallEtaleComparisonRan B S hS Y).obj Q).obj.map j.hom σ)

/-- The homomorphism into the direct image of an `f`-map, read against the Kan-extension form of
the direct image. -/
theorem fmapDirectImageEquiv_comp_ranIso (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (η : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj) :
    fmapDirectImageEquiv B S hS f P Q η ≫
        (smallEtaleDirectImageRanIso B S hS f).hom.app P =
      fmapRan B S hS f P Q η := by
  change (fmapRan B S hS f P Q η ≫
    (smallEtaleDirectImageRanIso B S hS f).inv.app P) ≫ _ = _
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-! ### The composite homomorphism into the direct image -/

/-- The homomorphism from `R` into the direct image of `P` along `f ≫ g` attached to a `g`-map
from `R` to `Q` and an `f`-map from `Q` to `P`: the homomorphism of the `g`-map, followed by the
spaces-étale direct image along `g` of the transported homomorphism of the `f`-map, followed by
the comparison `AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU` of the iterated
cartesian direct image with the direct image of the composite. -/
noncomputable def fmapRanComp (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (R : Sheaf (SmallEtale.topology B S hS Z.1) (Type u))
    (ξ : FMap B S hS Y.1 Z.1 g.hom Q.obj R.obj)
    (η : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj) :
    R ⟶ (smallEtaleDirectImageRan B S hS (f ≫ g)).obj P :=
  fmapRan B S hS g Q R ξ ≫
    (smallEtaleComparisonRestriction B S hS Z).map
      ((spacesDirectImage B S hS g).map
          (ranSpacesHom B S hS f P Q (fmapDirectImageEquiv B S hS f P Q η)) ≫
        (spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app
          ((smallEtaleComparisonRan B S hS X).obj P))

/-- **The composite of a `g`-map and an `f`-map**: the `f ≫ g`-map which the chart
correspondence of Stacks 03G4 attaches to the composite

`R ⟶ g_*Q ⟶ g_*(f_*P) ⟶ (f ≫ g)_*P`

of the two homomorphisms into the direct images, the last arrow being the comparison of
Stacks 03G2, part (3).

It cannot be given chart diagram by chart diagram — the vertical morphism of a chart diagram
over `f ≫ g` need not factor through an étale scheme chart of `Y` — but on the chart diagrams
that do factor it is the composite of the components, which is
`AlgebraicGeometry.Space.FMap.comp_app`.

This carries no `@[stacks]` attribute: it is not one of the assertions of Stacks 03G4, which are
the two bijections and their characterization on chart sections, all proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartCorrespondence.lean`.  Nor does it on its own
discharge the composition fields of `AlgebraicGeometry.Space.ModuleImageData` (Stacks 03LU):
those want a `AlgebraicGeometry.Space.ModuleFMap`, whose additivity and semilinearity are
required at *every* chart diagram, while `AlgebraicGeometry.Space.FMap.comp_app` covers only the
ones that factor through `Y`.  This is the underlying map of sets of that composite. -/
noncomputable def FMap.comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (R : Sheaf (SmallEtale.topology B S hS Z.1) (Type u))
    (ξ : FMap B S hS Y.1 Z.1 g.hom Q.obj R.obj)
    (η : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj) :
    FMap B S hS X.1 Z.1 (f ≫ g).hom P.obj R.obj :=
  (fmapDirectImageEquiv B S hS (f ≫ g) P R).symm
    (fmapDirectImageEquiv B S hS g Q R ξ ≫
      (smallEtaleDirectImage B S hS g).map (fmapDirectImageEquiv B S hS f P Q η) ≫
      (smallToposMorphismTypeU_comp B S hS f g).hom.app P)

/-! ### The iterated-limit identification -/

/-- Cancelling the comparison of base changes inside the right Kan extension: the two
restrictions along the two directions of `AlgebraicGeometry.Space.spacesBaseChange_comp` undo
each other.  This is the elementwise form of `CategoryTheory.Iso.map_inv_hom_id`, of which
Mathlib has no `_apply` variant; the same cancellation appears inline in the proof of
`AlgebraicGeometry.Space.structureSharpRanSet_comp`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleStructureMapComp.lean`). -/
theorem ranMap_spacesBaseChange_comp_cancel (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (W : SmallEtale B S hS Z.1)
    (τ : ((comparisonFunctor B S hS X).op.ran.obj P.obj).obj
      (op ((spacesBaseChange B S hS f).functor.obj (chartBaseChange B S hS g W)))) :
    ((comparisonFunctor B S hS X).op.ran.obj P.obj).map
        ((spacesBaseChange_comp B S hS f g).hom.app
          ((comparisonFunctor B S hS Z).obj W)).op
        (((comparisonFunctor B S hS X).op.ran.obj P.obj).map
          ((spacesBaseChange_comp B S hS f g).inv.app
            ((comparisonFunctor B S hS Z).obj W)).op τ) = τ := by
  rw [← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id_app, op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- Restricting a section of the right Kan extension along
`AlgebraicGeometry.Space.chartBaseChangeComp` undoes the comparison of base changes: only the
cartesian direct image of the chart morphism of `Y` is left. -/
theorem ranMap_chartBaseChangeComp (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g W)) (comparisonFunctor B S hS Y).op)
    (τ : ((comparisonFunctor B S hS X).op.ran.obj P.obj).obj
      (op ((spacesBaseChange B S hS f).functor.obj (chartBaseChange B S hS g W)))) :
    ((comparisonFunctor B S hS X).op.ran.obj P.obj).map
        (chartBaseChangeComp B S hS f g W j).op
        (((comparisonFunctor B S hS X).op.ran.obj P.obj).map
          ((spacesBaseChange_comp B S hS f g).inv.app
            ((comparisonFunctor B S hS Z).obj W)).op τ) =
      ((comparisonFunctor B S hS X).op.ran.obj P.obj).map
        ((spacesBaseChange B S hS f).functor.map j.hom.unop).op τ := by
  rw [chartBaseChangeComp, op_comp, Functor.map_comp_apply, ranMap_spacesBaseChange_comp_cancel]

/-- The chart projection, at an étale scheme chart of `X` above `X ×_Z W` which comes from a
chart of `Y` above `Y ×_Z W` by `AlgebraicGeometry.Space.chartBaseChangeComp`, of a section
produced by the comparison of base changes is the iterated chart projection. -/
theorem ranProj_spacesBaseChange_comp_inv (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g W)) (comparisonFunctor B S hS Y).op)
    (k : StructuredArrow (op (chartBaseChange B S hS f j.right.unop))
      (comparisonFunctor B S hS X).op)
    (τ : ((comparisonFunctor B S hS X).op.ran.obj P.obj).obj
      (op ((spacesBaseChange B S hS f).functor.obj (chartBaseChange B S hS g W)))) :
    (ranProj B S hS X (chartBaseChange B S hS (f ≫ g) W)
          (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom))).app P
        (((comparisonFunctor B S hS X).op.ran.obj P.obj).map
          ((spacesBaseChange_comp B S hS f g).inv.app
            ((comparisonFunctor B S hS Z).obj W)).op τ) =
      (ranProj B S hS X (chartBaseChange B S hS f j.right.unop) k).app P
        (((comparisonFunctor B S hS X).op.ran.obj P.obj).map
          ((spacesBaseChange B S hS f).functor.map j.hom.unop).op τ) := by
  rw [← ranProj_map B S hS X (chartBaseChangeComp B S hS f g W j) P k,
    ranMap_chartBaseChangeComp]

/-- **The iterated limit is the single limit.** The chart projection of the transported
homomorphism, followed by the comparison of base changes, at an étale scheme chart of `X` above
`X ×_Z W` coming from a chart `j` of `Y` above `Y ×_Z W`, is the homomorphism applied to the
chart projection at `j`.

This is what replaces the identification of the iterated limit over the charts of `Y` and then
of `X` with the single limit over the charts of `X`: it needs no refinement of charts, only
`AlgebraicGeometry.Space.spacesBaseChange_comp`. -/
theorem ranProj_ranSpacesHom_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (ψ : Q ⟶ (smallEtaleDirectImage B S hS f).obj P) (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g W)) (comparisonFunctor B S hS Y).op)
    (k : StructuredArrow (op (chartBaseChange B S hS f j.right.unop))
      (comparisonFunctor B S hS X).op)
    (σ : ((smallEtaleComparisonRan B S hS Y).obj Q).obj.obj
      (op (chartBaseChange B S hS g W))) :
    (ranProj B S hS X (chartBaseChange B S hS (f ≫ g) W)
          (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom))).app P
        (((comparisonFunctor B S hS X).op.ran.obj P.obj).map
          ((spacesBaseChange_comp B S hS f g).inv.app
            ((comparisonFunctor B S hS Z).obj W)).op
          ((ranSpacesHom B S hS f P Q ψ).hom.app
            (op (chartBaseChange B S hS g W)) σ)) =
      (ranProj B S hS X (chartBaseChange B S hS f j.right.unop) k).app P
        ((ψ ≫ (smallEtaleDirectImageRanIso B S hS f).hom.app P).hom.app (op j.right.unop)
          ((ranProj B S hS Y (chartBaseChange B S hS g W) j).app Q σ)) := by
  rw [ranProj_spacesBaseChange_comp_inv B S hS f g P W j k
      ((ranSpacesHom B S hS f P Q ψ).hom.app (op (chartBaseChange B S hS g W)) σ),
    ← ranSpacesHom_app_ranProj B S hS f P Q ψ (chartBaseChange B S hS g W) j σ]
  rfl

/-- The chart projection of the section `fmapRanApp` of an `f`-map is the component of the
`f`-map at the chart diagram of the index. -/
private theorem ranProj_fmapRanApp (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (ξ : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (s : Q.obj.obj (op V)) :
    (ranProj B S hS X (chartBaseChange B S hS f V) j).app P (fmapRanApp B S hS f P Q ξ V s) =
      ξ.app (chartDiagramOfIndex B S hS f V j) s :=
  (ranProj_app_apply B S hS X (chartBaseChange B S hS f V) P j _).trans
    (fmapRanApp_π B S hS f P Q ξ V j s)

/-- The chart projection of `AlgebraicGeometry.Space.fmapRanComp`, at an étale scheme chart of
`X` above `X ×_Z W` coming from a chart `j` of `Y` above `Y ×_Z W`, is the component of the
`f`-map at the chart diagram of the first, applied to the component of the `g`-map at the chart
diagram of `j`. -/
theorem ranProj_fmapRanComp (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (R : Sheaf (SmallEtale.topology B S hS Z.1) (Type u))
    (ξ : FMap B S hS Y.1 Z.1 g.hom Q.obj R.obj)
    (η : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj) (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g W)) (comparisonFunctor B S hS Y).op)
    (k : StructuredArrow (op (chartBaseChange B S hS f j.right.unop))
      (comparisonFunctor B S hS X).op)
    (s : R.obj.obj (op W)) :
    (ranProj B S hS X (chartBaseChange B S hS (f ≫ g) W)
          (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom))).app P
        ((fmapRanComp B S hS f g P Q R ξ η).hom.app (op W) s) =
      η.app (chartDiagramOfIndex B S hS f j.right.unop k)
        (ξ.app (chartDiagramOfIndex B S hS g W j) s) := by
  refine (ranProj_ranSpacesHom_comp B S hS f g P Q (fmapDirectImageEquiv B S hS f P Q η) W j k
    (fmapRanApp B S hS g Q R ξ W s)).trans ?_
  rw [fmapDirectImageEquiv_comp_ranIso, ranProj_fmapRanApp B S hS g Q R ξ W j s]
  exact ranProj_fmapRanApp B S hS f P Q η j.right.unop k _

/-! ### The composite against the chart correspondence -/

/-- The composite of the two homomorphisms into the direct images, with the Kan-extension
comparisons absorbed, is `AlgebraicGeometry.Space.fmapRanComp`.

This is `AlgebraicGeometry.Space.forgetRing_comp_structure_formula` for an arbitrary
homomorphism in place of the structure map: naturality of the comparison
`AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU` and nothing else. -/
theorem ranSpacesHom_comp_formula (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (ψ : Q ⟶ (smallEtaleDirectImage B S hS f).obj P) :
    (smallEtaleDirectImageRanIso B S hS g).inv.app Q ≫
        (smallEtaleDirectImage B S hS g).map ψ ≫
        (smallToposMorphismTypeU_comp B S hS f g).hom.app P ≫
        (smallEtaleDirectImageRanIso B S hS (f ≫ g)).hom.app P =
      (smallEtaleComparisonRestriction B S hS Z).map
        ((spacesDirectImage B S hS g).map (ranSpacesHom B S hS f P Q ψ) ≫
          (spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app
            ((smallEtaleComparisonRan B S hS X).obj P)) :=
  congrArg (fun m ↦ (smallEtaleComparisonRestriction B S hS Z).map
      ((spacesDirectImage B S hS g).map
          ((smallEtaleComparisonRanIso B S hS Y).inv.app Q) ≫
        (spacesDirectImage B S hS g).map
          ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.map ψ) ≫
        (spacesDirectImage B S hS g).map
          ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.unitIso.inv.app
            ((spacesDirectImage B S hS f).obj
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P))) ≫ m))
    ((spacesBaseChange_pushforward_compTypeU B S hS f g).hom.naturality
      ((smallEtaleComparisonRanIso B S hS X).hom.app P)).symm

/-- **The chart correspondence of Stacks 03G4 is compatible with composition.** The
homomorphism into the direct image attached to the composite of a `g`-map and an `f`-map is the
composite of the two homomorphisms, followed by the comparison of Stacks 03G2, part (3), of the
iterated direct image with the direct image of the composite.

That comparison is `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`, which
`AlgebraicGeometry.Space.compToposPushforwardIso`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardComp.lean`) also names, and
which `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso_isCartesianComposition`
identifies as the one induced by cartesian composition.  This is how
`AlgebraicGeometry.Space.FMap.comp` is defined, so the content of composition sits in
`AlgebraicGeometry.Space.fmapRan_comp` and
`AlgebraicGeometry.Space.FMap.comp_app` instead. -/
theorem fmapDirectImageEquiv_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (R : Sheaf (SmallEtale.topology B S hS Z.1) (Type u))
    (ξ : FMap B S hS Y.1 Z.1 g.hom Q.obj R.obj)
    (η : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj) :
    fmapDirectImageEquiv B S hS (f ≫ g) P R (FMap.comp B S hS f g P Q R ξ η) =
      fmapDirectImageEquiv B S hS g Q R ξ ≫
        (smallEtaleDirectImage B S hS g).map (fmapDirectImageEquiv B S hS f P Q η) ≫
        (smallToposMorphismTypeU_comp B S hS f g).hom.app P :=
  (fmapDirectImageEquiv B S hS (f ≫ g) P R).apply_symm_apply _

/-- **The composite in the Kan-extension picture.** The homomorphism into the Kan-extension
form of the direct image attached to the composite `f`-map is
`AlgebraicGeometry.Space.fmapRanComp`: the homomorphism of the `g`-map, followed by the
spaces-étale direct image along `g` of the transported homomorphism of the `f`-map, followed by
the cartesian comparison.

This is where the passage between the two pictures happens, and it is what the chart formula
`AlgebraicGeometry.Space.FMap.comp_app` reads chart projections off. -/
theorem fmapRan_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (R : Sheaf (SmallEtale.topology B S hS Z.1) (Type u))
    (ξ : FMap B S hS Y.1 Z.1 g.hom Q.obj R.obj)
    (η : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj) :
    fmapRan B S hS (f ≫ g) P R (FMap.comp B S hS f g P Q R ξ η) =
      fmapRanComp B S hS f g P Q R ξ η := by
  refine Eq.trans (fmapDirectImageEquiv_comp_ranIso B S hS (f ≫ g) P R
    (FMap.comp B S hS f g P Q R ξ η)).symm ?_
  refine Eq.trans (congrArg
    (fun m ↦ m ≫ (smallEtaleDirectImageRanIso B S hS (f ≫ g)).hom.app P)
    (fmapDirectImageEquiv_comp B S hS f g P Q R ξ η)) ?_
  exact congrArg (fun m ↦ fmapRan B S hS g Q R ξ ≫ m)
    (ranSpacesHom_comp_formula B S hS f g P Q (fmapDirectImageEquiv B S hS f P Q η))

/-- `AlgebraicGeometry.Space.FMap.comp` is the `f`-map which
`AlgebraicGeometry.Space.ranFmap` attaches to `AlgebraicGeometry.Space.fmapRanComp`.  This is
`AlgebraicGeometry.Space.fmapRan_comp` read through the bijection, and it is what lets the chart
formula be computed from `AlgebraicGeometry.Space.ranProj_fmapRanComp`. -/
theorem FMap.comp_eq_ranFmap (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (R : Sheaf (SmallEtale.topology B S hS Z.1) (Type u))
    (ξ : FMap B S hS Y.1 Z.1 g.hom Q.obj R.obj)
    (η : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj) :
    FMap.comp B S hS f g P Q R ξ η =
      ranFmap B S hS (f ≫ g) P R (fmapRanComp B S hS f g P Q R ξ η) :=
  (fmapRanEquiv B S hS (f ≫ g) P R).injective
    ((fmapRan_comp B S hS f g P Q R ξ η).trans
      ((fmapRanEquiv B S hS (f ≫ g) P R).apply_symm_apply
        (fmapRanComp B S hS f g P Q R ξ η)).symm)

/-- `AlgebraicGeometry.Space.FMap.comp` is the *only* `f ≫ g`-map whose homomorphism into the
direct image is the composite of the two homomorphisms: the chart correspondence of Stacks 03G4
is a bijection, so this makes the composite a characterization rather than a choice. -/
theorem FMap.comp_unique (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (R : Sheaf (SmallEtale.topology B S hS Z.1) (Type u))
    (ξ : FMap B S hS Y.1 Z.1 g.hom Q.obj R.obj)
    (η : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj)
    (θ : FMap B S hS X.1 Z.1 (f ≫ g).hom P.obj R.obj)
    (h : fmapDirectImageEquiv B S hS (f ≫ g) P R θ =
      fmapDirectImageEquiv B S hS g Q R ξ ≫
        (smallEtaleDirectImage B S hS g).map (fmapDirectImageEquiv B S hS f P Q η) ≫
        (smallToposMorphismTypeU_comp B S hS f g).hom.app P) :
    θ = FMap.comp B S hS f g P Q R ξ η :=
  (fmapDirectImageEquiv B S hS (f ≫ g) P R).injective
    (h.trans (fmapDirectImageEquiv_comp B S hS f g P Q R ξ η).symm)

/-! ### The chart formula -/

section Factor

variable (f : X ⟶ Y) (g : Y ⟶ Z)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)

/-- The chart diagram over `f ≫ g` obtained by composing the vertical scheme morphisms of a
chart diagram over `f` and a chart diagram over `g` whose source chart is the target chart of
the first.

The two diagrams are given unbundled, by their charts and vertical morphisms, rather than as two
`AlgebraicGeometry.Space.ChartDiagram`s with an equality of middle charts: the bundled form would
force a transport, and `AlgebraicGeometry.Space.FMap.comp_app` consumes the unbundled form.  This
is chart-diagram API and belongs beside `AlgebraicGeometry.Space.ChartDiagram.ext`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartCorrespondence.lean`); it is here only because that
file is not edited. -/
def ChartDiagram.comp : ChartDiagram B S hS X.1 Z.1 (f ≫ g).hom where
  U := U
  V := W
  g := a ≫ b
  comm := by
    change U.1.hom ≫ f.hom ≫ g.hom = _
    rw [← Category.assoc, ha, Category.assoc, hb, CategoryTheory.Functor.map_comp,
      Category.assoc]

/-- **The cartesian form of a composed chart diagram.** It is the cartesian form of the chart
diagram over `f`, followed by the chart of `X` above `X ×_Z W` which the cartesian form of the
chart diagram over `g` determines.

This is the chart-diagram counterpart of
`AlgebraicGeometry.Space.chartBaseChangeMap_comp_chart`, and it is proved the same way: both
sides are morphisms to `X ×_Z W` over `X` whose composite with the cartesian projection is the
Yoneda morphism of the composed diagram, by
`AlgebraicGeometry.Space.spacesBaseChange_comp_projection` and the two
`AlgebraicGeometry.Space.chartLift_projection`s. -/
theorem chartLift_chartDiagram_comp :
    chartLift B S hS (f ≫ g) (ChartDiagram.comp B S hS f g a b ha hb) =
      chartLift B S hS f ⟨U, V, a, ha⟩ ≫
        chartBaseChangeComp B S hS f g W
          (indexOfChartDiagram B S hS g ⟨V, W, b, hb⟩) := by
  refine (chartLift_unique B S hS (f ≫ g) (ChartDiagram.comp B S hS f g a b ha hb) _ ?_).symm
  have hproj := spacesBaseChange_comp_projection B S hS f g ((comparisonFunctor B S hS Z).obj W)
  have hnat := (spacesBaseChange B S hS f).projection.naturality
    (chartLift B S hS g (⟨V, W, b, hb⟩ : ChartDiagram B S hS Y.1 Z.1 g.hom))
  have h1 := chartLift_projection B S hS f (⟨U, V, a, ha⟩ : ChartDiagram B S hS X.1 Y.1 f.hom)
  have h2 := chartLift_projection B S hS g (⟨V, W, b, hb⟩ : ChartDiagram B S hS Y.1 Z.1 g.hom)
  have key := (congrArg (fun m ↦ (SpacesEtale.toSpaces B S hS X).map
        (chartLift B S hS f (⟨U, V, a, ha⟩ : ChartDiagram B S hS X.1 Y.1 f.hom)) ≫
      (SpacesEtale.toSpaces B S hS X).map ((spacesBaseChange B S hS f).functor.map
        (chartLift B S hS g (⟨V, W, b, hb⟩ : ChartDiagram B S hS Y.1 Z.1 g.hom))) ≫ m)
      hproj).trans
    (congrArg (fun m ↦ (SpacesEtale.toSpaces B S hS X).map
        (chartLift B S hS f (⟨U, V, a, ha⟩ : ChartDiagram B S hS X.1 Y.1 f.hom)) ≫ m ≫
      (spacesBaseChange B S hS g).projection.app ((comparisonFunctor B S hS Z).obj W)) hnat)
  have key2 := congrArg₂ (fun p q ↦ p ≫ q) h1 h2
  have key3 : (SpacesEtale.toSpaces B S hS X).map
        (chartLift B S hS f (⟨U, V, a, ha⟩ : ChartDiagram B S hS X.1 Y.1 f.hom) ≫
          chartBaseChangeComp B S hS f g W
            (indexOfChartDiagram B S hS g ⟨V, W, b, hb⟩)) ≫
      (spacesBaseChange B S hS (f ≫ g)).projection.app
        ((comparisonFunctor B S hS Z).obj W) =
      chartDiagramSpaceMap B S hS f ⟨U, V, a, ha⟩ ≫
        chartDiagramSpaceMap B S hS g ⟨V, W, b, hb⟩ := key.trans key2
  exact (congrArg (fun q ↦ q.hom) key3).trans (yoneda.map_comp a b).symm

/-- The index of the limit cone named by a composed chart diagram is the composite index: the
chart of `X` above `X ×_Y V` named by the chart diagram over `f`, followed by the chart of `X`
above `X ×_Z W` which the chart diagram over `g` determines. -/
theorem indexOfChartDiagram_chartDiagram_comp :
    indexOfChartDiagram B S hS (f ≫ g) (ChartDiagram.comp B S hS f g a b ha hb) =
      StructuredArrow.mk ((chartBaseChangeComp B S hS f g W
            (indexOfChartDiagram B S hS g ⟨V, W, b, hb⟩)).op ≫
          (indexOfChartDiagram B S hS f ⟨U, V, a, ha⟩).hom) :=
  congrArg StructuredArrow.mk
    ((congrArg Quiver.Hom.op (chartLift_chartDiagram_comp B S hS f g a b ha hb)).trans
      op_comp)

/-- **The chart formula for the composite `f`-map.** On a chart diagram over `f ≫ g` whose
vertical scheme morphism factors through an étale scheme chart `V` of `Y`,
compatibly with the two structure morphisms, the composite `f`-map is the composite of the
component of the `f`-map at the lower diagram and the component of the `g`-map at the upper
one.

So `AlgebraicGeometry.Space.FMap.comp` is composition of maps of sections wherever composition
of maps of sections makes sense; on a chart diagram that does not factor it is still defined,
by the iterated-limit identification
`AlgebraicGeometry.Space.ranProj_ranSpacesHom_comp`. -/
theorem FMap.comp_app
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (R : Sheaf (SmallEtale.topology B S hS Z.1) (Type u))
    (ξ : FMap B S hS Y.1 Z.1 g.hom Q.obj R.obj)
    (η : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj) (s : R.obj.obj (op W)) :
    (FMap.comp B S hS f g P Q R ξ η).app (ChartDiagram.comp B S hS f g a b ha hb) s =
      η.app ⟨U, V, a, ha⟩ (ξ.app ⟨V, W, b, hb⟩ s) := by
  rw [FMap.comp_eq_ranFmap B S hS f g P Q R ξ η]
  refine Eq.trans (eq_of_heq (ranChartCone_π_congr B S hS X P.obj
    (chartBaseChange B S hS (f ≫ g) W)
    (indexOfChartDiagram_chartDiagram_comp B S hS f g a b ha hb)
    ((fmapRanComp B S hS f g P Q R ξ η).hom.app (op W) s))) ?_
  refine Eq.trans (ranProj_app_apply B S hS X (chartBaseChange B S hS (f ≫ g) W) P
    (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W
        (indexOfChartDiagram B S hS g ⟨V, W, b, hb⟩)).op ≫
      (indexOfChartDiagram B S hS f ⟨U, V, a, ha⟩).hom))
    ((fmapRanComp B S hS f g P Q R ξ η).hom.app (op W) s)).symm ?_
  refine Eq.trans (ranProj_fmapRanComp B S hS f g P Q R ξ η W
    (indexOfChartDiagram B S hS g ⟨V, W, b, hb⟩)
    (indexOfChartDiagram B S hS f ⟨U, V, a, ha⟩) s) ?_
  exact eq_of_heq (FMap.app_heq B S hS η
    (chartDiagramOfIndex_indexOfChartDiagram B S hS f ⟨U, V, a, ha⟩)
    (FMap.app_heq B S hS ξ
      (chartDiagramOfIndex_indexOfChartDiagram B S hS g ⟨V, W, b, hb⟩) HEq.rfl))

end Factor

end AlgebraicGeometry.Space

end
