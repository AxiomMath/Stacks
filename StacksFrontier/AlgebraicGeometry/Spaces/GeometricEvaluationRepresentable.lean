module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleNeighborhoodBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange

/-!
# The triangle of geometric evaluations over a representable morphism

`AlgebraicGeometry.Space.geometricEval_isEtaleLocalRingMap_germ` says that the triangle of
evaluations at a geometric point over a morphism of algebraic spaces commutes on the germ of a
regular function, provided one commuting square of pointed étale charts over that germ's chart is
given.  For a *representable* morphism such a square is available over every chart of the target:
base change of pointed charts, `AlgebraicGeometry.Space.SmallEtaleNeighborhood.baseChange`,
produces one, with the cartesian projection as the morphism of charts.  Since the germs over all
charts of the target are the components of the colimit cocone defining the étale local ring, the
triangle then commutes on the whole étale local ring.

## Main results

* `AlgebraicGeometry.Space.geometricEval_comp_of_relativelyRepresentable`: for a representable
  morphism `f : X ⟶ Y` and any homomorphism of étale local rings induced by `f` at `x̄` in the
  sense of Stacks 04NG, evaluating at `f(x̄)` is evaluating its image at `x̄`.
* `AlgebraicGeometry.Space.geometricEval_comp_yoneda`: the same for a morphism of the big fppf
  site between two representable algebraic spaces, which is representable by
  `AlgebraicGeometry.Space.relativelyRepresentable_yoneda_map`.

## Implementation notes

The two evaluations are compared as morphisms of `CommRingCat` into the lifted field of the
geometric point, which is the target of
`AlgebraicGeometry.Space.geometricEvalCocone`: the étale local ring *is* the colimit of sections
over the pointed charts, so `CategoryTheory.Limits.colimit.hom_ext` reduces the comparison to the
germs, where `AlgebraicGeometry.Space.geometricEval_isEtaleLocalRingMap_germ` applies.  Comparing
the bare ring homomorphisms instead would require the germs to be jointly surjective, which they
are not.

The square over a chart `N` of the target is the base change `X ×_Y N`: its structure morphism is
`hf.fst` and the projection is `hf.snd`, so the "over" condition is the representability square
of `f` itself, and the compatibility of the lifts is
`AlgebraicGeometry.Space.smallBaseChangeFiberMap_smallBaseChangeFiberInv`, the statement that the
lift of `x̄` chosen on the base change projects to the given lift of `f(x̄)`.  No cofinality of the
base-changed charts is needed — one square over each chart of the target is enough, because the
comparison is already known to be a ring homomorphism out of the colimit.

## References

* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The triangle of geometric evaluations commutes, for a representable morphism.**  Let
`f : X ⟶ Y` be a representable morphism of algebraic spaces over `S`, let `x̄` be a geometric
point of `X` and let `φ` be a homomorphism of étale local rings induced by `f` at `x̄` in the sense
of Stacks 04NG.  Then evaluating a germ at `f(x̄)` is the same as evaluating its image under `φ`
at `x̄`.

Base change of pointed charts along `f` supplies, over every pointed chart of `Y`, a commuting
square of pointed charts, which is what
`AlgebraicGeometry.Space.geometricEval_isEtaleLocalRingMap_germ` asks for; the germs over all
charts of `Y` are the colimit cocone of the étale local ring of `Y` at `f(x̄)`, so agreement on
all of them is agreement. -/
theorem geometricEval_comp_of_relativelyRepresentable
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (x : GeometricPoint B S hS X.1)
    {φ : ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x)) →+*
      ↥(etaleLocalRing B S hS X.1 x)}
    (hφ : IsEtaleLocalRingMap f.hom x φ) :
    (geometricEval B S hS X.1 x).comp φ =
      geometricEval B S hS Y.1 (geometricPointMap f.hom x) := by
  -- the triangle on the germ over a pointed chart `N` of `Y`, through the base change `X ×_Y N`
  have key : ∀ (N : SmallEtaleNeighborhood (geometricPointMap f.hom x))
      (a : (structurePresheaf B S hS Y.1).obj (op N.chart)),
      geometricEval B S hS X.1 x
          (φ (etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x) (op N) a)) =
        geometricEval B S hS Y.1 (geometricPointMap f.hom x)
          (etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x) (op N) a) := by
    intro N a
    refine geometricEval_isEtaleLocalRingMap_germ B S hS X.1 f.hom x hφ
      ((SmallEtaleNeighborhood.baseChange B S hS f hf x).obj N) N
      (hf.snd N.chart.1.hom) (hf.w N.chart.1.hom) ?_ a
    exact congrArg Subtype.val (smallBaseChangeFiberMap_smallBaseChangeFiberInv B S hS f hf x
      N.chart ⟨N.point, N.point_comp⟩)
  -- the two evaluations as morphisms out of the colimit, compared on the cocone components
  have hmor : CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((geometricEval B S hS X.1 x).comp φ)) =
      colimit.desc _ (geometricEvalCocone B S hS Y.1 (geometricPointMap f.hom x)) := by
    refine colimit.hom_ext fun N => ?_
    refine Eq.trans ?_ (colimit.ι_desc
      (geometricEvalCocone B S hS Y.1 (geometricPointMap f.hom x)) N).symm
    refine CommRingCat.hom_ext (RingHom.ext fun z => ULift.ext ?_)
    show geometricEval B S hS X.1 x
        (φ (etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x) (op N.unop) z.down)) =
      geometricEvalApp B S hS Y.1 N.unop z.down
    exact (key N.unop z.down).trans
      (geometricEval_etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x) N.unop z.down)
  refine RingHom.ext fun t => ?_
  exact congrArg ULift.down (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmor) t)

/-- **The triangle of geometric evaluations commutes over a morphism of the site.**  For a
morphism `g : U ⟶ W` of the big fppf site of `S`, a geometric point `ū` of the algebraic space
`U` represents and any homomorphism of étale local rings induced by `g` at `ū` in the sense of
Stacks 04NG, evaluating a germ at the image of `ū` in `W` is the same as evaluating its image
at `ū`.

A morphism of representable algebraic spaces is representable, so this is
`AlgebraicGeometry.Space.geometricEval_comp_of_relativelyRepresentable`. -/
theorem geometricEval_comp_yoneda {U₀ W₀ : BigFppfOver B S hS} (g : U₀ ⟶ W₀)
    (ubar : GeometricPoint B S hS (yoneda.obj U₀))
    {φ : ↥(etaleLocalRing B S hS (yoneda.obj W₀) (geometricPointMap (yoneda.map g) ubar)) →+*
      ↥(etaleLocalRing B S hS (yoneda.obj U₀) ubar)}
    (hφ : IsEtaleLocalRingMap (yoneda.map g) ubar φ) :
    (geometricEval B S hS (yoneda.obj U₀) ubar).comp φ =
      geometricEval B S hS (yoneda.obj W₀) (geometricPointMap (yoneda.map g) ubar) :=
  geometricEval_comp_of_relativelyRepresentable B S hS
    (X := ⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩)
    (Y := ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩)
    (ObjectProperty.homMk (yoneda.map g)) (relativelyRepresentable_yoneda_map B S hS g) ubar hφ

end AlgebraicGeometry.Space

end
