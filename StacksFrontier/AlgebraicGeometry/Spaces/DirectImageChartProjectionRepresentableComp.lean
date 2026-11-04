module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftRefine

/-!
# The chart value of the composition comparison of direct images

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be representable morphisms of algebraic spaces over a scheme `S`
with `f ≫ g` representable, and let `W` be an étale scheme chart of `Z`.  Stacks 03G8 identifies
the sections of a direct image over `W` with the sections over the base-changed chart
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing`), and there are two ways to
carry a sheaf on `X` down to a chart over `W`: along `f ≫ g` in one step, or along `f` and then
along `g`.  The two readings of a section differ by restriction along
`AlgebraicGeometry.Space.smallBaseChangeComp`, the chart-level composition law of base change.
**This file proves that**, for the comparison of iterated direct images of Stacks 03G2, part (3).

## Main results

* `AlgebraicGeometry.Space.smallBaseChangeComp_smallEtaleRingedToposHom_representable`: for a
  sheaf of sets, the chart reading of `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`
  through the chart-base-change comparisons of `f ≫ g`, of `g` and of `f` is restriction along
  `AlgebraicGeometry.Space.smallBaseChangeComp`.
* `AlgebraicGeometry.Space.smallBaseChangeComp_smallEtaleRingedToposHom_compRingIso`: **the chart
  value of `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso`.**  The same statement
  for sheaves of commutative rings and the two composition-carrying comparisons of Stacks 01D3,
  part (3) and Stacks 03G2, part (3), as a homomorphism of the rings of sections over `W`.

## Implementation notes

The route is the one
`AlgebraicGeometry.Space.fSharp_comp_smallEtaleRingedToposHom_representableRing` takes: push the
sheaves of commutative rings down to sheaves of sets, where the comparisons forget on the nose —
`Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso_hom_forget` to the identity,
`Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom`
to `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` and
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing_forget` to
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable` — settle it there, and come back.
No `CategoryTheory.eqToHom` is needed anywhere: the objects on the two sides are already the same,
the comparison of the chart indices being carried by the restriction map.

On sheaves of sets the statement is three applications of
`AlgebraicGeometry.Space.directImageChartProjection_smallEtaleRingedToposHom_representable`, which
turns each chart-base-change comparison into the chart projection at the base-changed chart,
followed by `AlgebraicGeometry.Space.directImageChartProjection_smallToposMorphismTypeU_comp`,
which splits the projection of the one-step direct image at the index
`AlgebraicGeometry.Space.chartBaseChangeComp` attached to the pair of base-changed charts.  That
index is *not* the base-changed chart of `f ≫ g`; what identifies the two is the morphism of
indices `AlgebraicGeometry.Space.smallBaseChangeCompIndexHom`, whose underlying morphism of charts
is `AlgebraicGeometry.Space.smallBaseChangeComp` and which exists precisely because
`AlgebraicGeometry.Space.smallBaseChangeComp_comparison` says that
`AlgebraicGeometry.Space.smallBaseChangeComp` is compatible with the comparison isomorphisms
indexing the two charts.  The chart projections form a cone over the indices
(`AlgebraicGeometry.Space.directImageChartProjection_index_comp`), so that morphism of indices
acts as the restriction map in the statement.

**No `@[stacks]` attribute is placed.**  What is proved is a chart-level reading of comparisons
already registered elsewhere — Stacks 03G2, part (3) on
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc`, Stacks 03G2, part (4) on
`AlgebraicGeometry.Space.smallBaseChange` and
`AlgebraicGeometry.Space.smallBaseChange_comparison`, Stacks 03G8 on
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`, and Stacks 01D3, part (3) on
`AlgebraicGeometry.RingedToposHom.comp` — and not a statement of the Stacks project in its own
right.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3), part (3), the composition
  of morphisms of ringed topoi.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), parts (2), (3) and (4).
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- **The base-changed chart of a composite, as an index of the one-step limit attached to a pair
of base-changed charts.**  For representable `f : X ⟶ Y` and `g : Y ⟶ Z` with `f ≫ g`
representable and `W` an étale scheme chart of `Z`, the chart `X ×_Z W` receives from the chart
`X ×_Y (Y ×_Z W)` the morphism `AlgebraicGeometry.Space.smallBaseChangeComp`, and that morphism
is a morphism of charts above `X ×_Z W` because
`AlgebraicGeometry.Space.smallBaseChangeComp_comparison` identifies it with the composition
isomorphism of base change on the spaces-étale site. -/
def smallBaseChangeCompIndexHom (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) (W : SmallEtale B S hS Z.1) :
    chartBaseChangeArrow B S hS (f ≫ g) hfg W ⟶
      StructuredArrow.mk ((chartBaseChangeComp B S hS f g W
          (chartBaseChangeArrow B S hS g hg W)).op ≫
        (chartBaseChangeArrow B S hS f hf
          ((smallBaseChange B S hS g hg).obj W)).hom) :=
  StructuredArrow.homMk ((smallBaseChangeComp B S hS f g hf hg hfg).hom.app W).op
    (Quiver.Hom.unop_inj (smallBaseChangeComp_comparison B S hS f g hf hg hfg W))

/-- **The two chart readings of a section of an iterated direct image differ by restriction along
the chart-level composition law of base change.**

For representable `f : X ⟶ Y` and `g : Y ⟶ Z` with `f ≫ g` representable, a sheaf of sets `F` on
the small étale site of `X` and an étale scheme chart `W` of `Z`: a section of `g_*(f_*F)` over
`W` can be carried to a section of `F` over the chart `X ×_Z W` by transporting it across the
comparison of [Stacks Project, Tag 03G2], part (3), and then reading the chart-base-change
comparison of `f ≫ g`; or it can be read with the chart-base-change comparison of `g` and then
the one of `f`, landing on the chart `X ×_Y (Y ×_Z W)`.  The two agree after restriction along
`AlgebraicGeometry.Space.smallBaseChangeComp`. -/
theorem smallBaseChangeComp_smallEtaleRingedToposHom_representable (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (W : SmallEtale B S hS Z.1)
    (α : (smallEtaleDirectImage B S hS g ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Z.1) (op W)).obj
      ((smallEtaleDirectImage B S hS f).obj F)) :
    F.obj.map ((smallBaseChangeComp B S hS f g hf hg hfg).hom.app W).op
        (((smallEtaleRingedToposHom_representable B S hS (f ≫ g) hfg).hom.app F).hom.app
          (op W) (((smallToposMorphismTypeU_comp B S hS f g).hom.app F).hom.app (op W) α)) =
      ((smallEtaleRingedToposHom_representable B S hS f hf).hom.app F).hom.app
          (op ((smallBaseChange B S hS g hg).obj W))
        (((smallEtaleRingedToposHom_representable B S hS g hg).hom.app
          ((smallEtaleDirectImage B S hS f).obj F)).hom.app (op W) α) :=
  (congrArg (F.obj.map ((smallBaseChangeComp B S hS f g hf hg hfg).hom.app W).op)
      (directImageChartProjection_smallEtaleRingedToposHom_representable B S hS (f ≫ g) hfg F W
        (((smallToposMorphismTypeU_comp B S hS f g).hom.app F).hom.app (op W) α))).trans
    ((directImageChartProjection_index_comp B S hS (f ≫ g) W
          (smallBaseChangeCompIndexHom B S hS f g hf hg hfg W) F
          (((smallToposMorphismTypeU_comp B S hS f g).hom.app F).hom.app (op W) α)).trans
      ((directImageChartProjection_smallToposMorphismTypeU_comp B S hS f g W
            (chartBaseChangeArrow B S hS g hg W)
            (chartBaseChangeArrow B S hS f hf ((smallBaseChange B S hS g hg).obj W)) F α).trans
        ((directImageChartProjection_smallEtaleRingedToposHom_representable B S hS f hf F
              ((smallBaseChange B S hS g hg).obj W)
              ((directImageChartProjection B S hS g W
                (chartBaseChangeArrow B S hS g hg W)).app
                ((smallEtaleDirectImage B S hS f).obj F) α)).symm.trans
          (congrArg (((smallEtaleRingedToposHom_representable B S hS f hf).hom.app F).hom.app
              (op ((smallBaseChange B S hS g hg).obj W)))
            (directImageChartProjection_smallEtaleRingedToposHom_representable B S hS g hg
              ((smallEtaleDirectImage B S hS f).obj F) W α).symm))))

/-- **The chart value of `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso`.**

For representable `f : X ⟶ Y` and `g : Y ⟶ Z` with `f ≫ g` representable, a sheaf of commutative
rings `R` on the small étale site of `X` and an étale scheme chart `W` of `Z`: the two comparisons
that carry the composition — `Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso` of
[Stacks Project, Tag 01D3], part (3), and
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso` of [Stacks Project, Tag 03G2],
part (3) — followed by the chart-base-change comparison of Stacks 03G8 for `f ≫ g`, give the same
homomorphism on the sections over `W` as the chart-base-change comparisons of `g` and of `f` in
succession, after restriction along `AlgebraicGeometry.Space.smallBaseChangeComp`.

Both comparisons forget to the identity and to
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` on underlying sheaves of sets, and the
chart-base-change comparison forgets to
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`; so this is
`AlgebraicGeometry.Space.smallBaseChangeComp_smallEtaleRingedToposHom_representable` read at the
underlying sheaf of sets of `R`. -/
theorem smallBaseChangeComp_smallEtaleRingedToposHom_compRingIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom)
    (R : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (W : SmallEtale B S hS Z.1) :
    (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS f).toToposHom
            (smallEtaleRingedToposHom B S hS g).toToposHom R).hom.hom.app (op W) ≫
        ((smallEtaleRingedToposHom_compRingIso B S hS f g).hom.app R).hom.app (op W) ≫
        ((smallEtaleRingedToposHom_representableRing B S hS (f ≫ g) hfg).hom.app R).hom.app
          (op W) ≫
        R.obj.map ((smallBaseChangeComp B S hS f g hf hg hfg).hom.app W).op =
      ((smallEtaleRingedToposHom_representableRing B S hS g hg).hom.app
            ((pushforwardCommRingFunctor
              (smallEtaleRingedToposHom B S hS f).toToposHom).obj R)).hom.app (op W) ≫
        ((smallEtaleRingedToposHom_representableRing B S hS f hf).hom.app R).hom.app
          (op ((smallBaseChange B S hS g hg).obj W)) := by
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  have hcompIso : (smallEtaleRingedTopos B S hS Z).forgetRing.map
      (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS f).toToposHom
        (smallEtaleRingedToposHom B S hS g).toToposHom R).hom =
      𝟙 ((smallEtaleRingedToposHom B S hS g).toToposHom.pushforward.obj
        ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj
          ((smallEtaleRingedTopos B S hS X).forgetRing.obj R))) :=
    pushforwardCommRingCompIso_hom_forget (smallEtaleRingedToposHom B S hS f).toToposHom
      (smallEtaleRingedToposHom B S hS g).toToposHom R
  have hcomp : (smallEtaleRingedTopos B S hS Z).forgetRing.map
      ((smallEtaleRingedToposHom_compRingIso B S hS f g).hom.app R) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj R) :=
    underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
      (SmallEtale.topology B S hS Z.1) R (smallToposMorphismTypeU_comp B S hS f g)
  have e0 : (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS f).toToposHom
        (smallEtaleRingedToposHom B S hS g).toToposHom R).hom.hom.app (op W) a = a :=
    Sheaf.hom_congr_app_apply hcompIso (op W) a
  have e1 : ((smallEtaleRingedToposHom_compRingIso B S hS f g).hom.app R).hom.app (op W)
        ((pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS f).toToposHom
          (smallEtaleRingedToposHom B S hS g).toToposHom R).hom.hom.app (op W) a) =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj R)).hom.app (op W) a :=
    (Sheaf.hom_congr_app_apply hcomp (op W) _).trans
      (congrArg (((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj R)).hom.app (op W)) e0)
  have e2 := Sheaf.hom_congr_app_apply
    (smallEtaleRingedToposHom_representableRing_forget B S hS (f ≫ g) hfg R) (op W)
    (((smallEtaleRingedToposHom_compRingIso B S hS f g).hom.app R).hom.app (op W)
      ((pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS f).toToposHom
        (smallEtaleRingedToposHom B S hS g).toToposHom R).hom.hom.app (op W) a))
  have e3 := Sheaf.hom_congr_app_apply
    (smallEtaleRingedToposHom_representableRing_forget B S hS g hg
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj R))
    (op W) a
  have e4 := Sheaf.hom_congr_app_apply
    (smallEtaleRingedToposHom_representableRing_forget B S hS f hf R)
    (op ((smallBaseChange B S hS g hg).obj W))
    (((smallEtaleRingedToposHom_representableRing B S hS g hg).hom.app
      ((pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS f).toToposHom).obj R)).hom.app (op W) a)
  have hkey := smallBaseChangeComp_smallEtaleRingedToposHom_representable B S hS f g hf hg hfg
    ((smallEtaleRingedTopos B S hS X).forgetRing.obj R) W a
  refine (congrArg
    (((smallEtaleRingedTopos B S hS X).forgetRing.obj R).obj.map
      ((smallBaseChangeComp B S hS f g hf hg hfg).hom.app W).op)
    (e2.trans (congrArg
      (((smallEtaleRingedToposHom_representable B S hS (f ≫ g) hfg).hom.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj R)).hom.app (op W)) e1))).trans ?_
  exact hkey.trans (e4.trans (congrArg
    (((smallEtaleRingedToposHom_representable B S hS f hf).hom.app
      ((smallEtaleRingedTopos B S hS X).forgetRing.obj R)).hom.app
      (op ((smallBaseChange B S hS g hg).obj W))) e3)).symm

end AlgebraicGeometry.Space

end
