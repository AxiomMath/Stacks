module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartLocalFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkPullback

/-!
# Base change of pointed étale charts along a closed immersion

Let `f : X ⟶ Y` be a closed immersion of algebraic spaces over a scheme `S` and let `x̄` be a
geometric point of `X`. Base change along `f` of étale scheme charts, which is
`AlgebraicGeometry.Space.smallBaseChange` of Stacks 03G2, part (4), carries a *pointed* chart
of `Y` to a pointed chart of `X`: the lift of `x̄` into `X ×_Y V` is read off the bijection
`AlgebraicGeometry.Space.smallBaseChangeFiberMap_bijective` between the lifts of `x̄` into
`X ×_Y V` and the lifts of `f(x̄)` into `V`. This file builds the resulting functor on small
étale neighbourhoods of Stacks 04JY and proves that it is **initial**.

Initiality is the cofinality statement which makes a colimit over the small étale
neighbourhoods of `f(x̄)` of sections over base-changed charts agree with the colimit over all
small étale neighbourhoods of `x̄`. It is the geometric input of Stacks 0EE3 for algebraic
spaces; `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionGeometricLength.lean` consumes it.

## Main definitions

* `AlgebraicGeometry.Space.smallBaseChangeFiberInv` is the inverse of the bijection
  `AlgebraicGeometry.Space.smallBaseChangeFiberMap` on lifts of a geometric point: it carries a
  lift of `f(x̄)` into an étale chart `V` of `Y` to the lift of `x̄` into `X ×_Y V`.
* `AlgebraicGeometry.Space.SmallEtaleNeighborhood.baseChange` is the induced functor from the
  small étale neighbourhoods of `f(x̄)` to those of `x̄`.

## Main results

* `AlgebraicGeometry.Space.SmallEtaleNeighborhood.exists_baseChange_hom`: every small étale
  neighbourhood of `x̄` is refined by a base-changed one. This is cover density of base change,
  Stacks 04E5, part (1), read at the point of the small étale site of Stacks 04K0.
* `AlgebraicGeometry.Space.SmallEtaleNeighborhood.exists_baseChange_factorization`: a morphism
  between two base-changed pointed neighbourhoods is, after a further refinement by a pointed
  neighbourhood of `f(x̄)`, the base change of a morphism of pointed neighbourhoods of `f(x̄)`.
  This is local fullness of base change, Stacks 04E5, part (1) again, in the sharp form
  Stacks 04FV gives it: the refining chart may be chosen with *invertible* base change, so the
  lift of `x̄` transports to it and no covering family has to be lifted through.
* `AlgebraicGeometry.Space.SmallEtaleNeighborhood.initial_baseChange`: the base-change functor
  on pointed neighbourhoods is initial.

## Implementation notes

The two hypotheses of `CategoryTheory.Functor.initial_of_exists_of_isCofiltered` are exactly
the two results above, in that order. For the second one, cofilteredness of the small étale
neighbourhoods of `x̄` first equalizes the two given morphisms by a neighbourhood of `x̄`, that
neighbourhood is then refined by a base-changed one, and the resulting morphism between two
base-changed charts is fed to Stacks 04FV. Without the invertibility clause of Stacks 04FV the
lift of `x̄` could not be moved onto the refining chart of `Y`, and the pointed statement would
need a covering family instead.

Pointedness is never constructed by hand. `AlgebraicGeometry.Space.smallBaseChangeFiberInv` is
the inverse of a bijection, its compatibility with a morphism of charts of `Y`
(`AlgebraicGeometry.Space.smallBaseChangeFiberInv_map`) is the naturality of
`AlgebraicGeometry.Space.smallBaseChangeFiberMap` together with its injectivity, and
`AlgebraicGeometry.Space.geometricFiber_map_smallBaseChangeFiberMap` converts a compatibility
of lifts *upstairs* into the compatibility of the corresponding lifts downstairs, which is what
a morphism of neighbourhoods of `f(x̄)` asks for.

Representability of `f` is all that the functor itself needs, so it is stated for a
`CategoryTheory.Functor.relativelyRepresentable` morphism; the closed-immersion hypothesis
enters only with cover density and local fullness.

## References

* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04FV](https://stacks.math.columbia.edu/tag/04FV)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- The lift of a geometric point `x̄` of `X` into the base change `X ×_Y V` of an étale chart
`V` of `Y` determined by a lift of `f(x̄)` into `V`: the inverse of the bijection
`AlgebraicGeometry.Space.smallBaseChangeFiberMap` on lifts. -/
noncomputable def smallBaseChangeFiberInv (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (x : GeometricPoint B S hS X.1)
    (V : SmallEtale B S hS Y.1)
    (q : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) V) :
    GeometricFiber B S hS X.1 x ((smallBaseChange B S hS f hf).obj V) :=
  (Equiv.ofBijective _ (smallBaseChangeFiberMap_bijective B S hS f hf x V)).symm q

/-- Composing the lift of `x̄` into `X ×_Y V` with the cartesian projection returns the given
lift of `f(x̄)` into `V`. -/
theorem smallBaseChangeFiberMap_smallBaseChangeFiberInv (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (x : GeometricPoint B S hS X.1)
    (V : SmallEtale B S hS Y.1)
    (q : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) V) :
    (smallBaseChangeFiberMap B S hS f hf x).app V
        (smallBaseChangeFiberInv B S hS f hf x V q) = q :=
  (Equiv.ofBijective _ (smallBaseChangeFiberMap_bijective B S hS f hf x V)).apply_symm_apply q

/-- The bijection on lifts of `x̄` is natural in the étale chart of `Y`. -/
private theorem geometricFiber_map_smallBaseChangeFiberMap_app (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (x : GeometricPoint B S hS X.1)
    {V W : SmallEtale B S hS Y.1} (k : V ⟶ W)
    (p : GeometricFiber B S hS X.1 x ((smallBaseChange B S hS f hf).obj V)) :
    (geometricFiber B S hS Y.1 (geometricPointMap f.hom x)).map k
        ((smallBaseChangeFiberMap B S hS f hf x).app V p) =
      (smallBaseChangeFiberMap B S hS f hf x).app W
        ((geometricFiber B S hS X.1 x).map ((smallBaseChange B S hS f hf).map k) p) :=
  (congrArg (fun φ => φ p) ((smallBaseChangeFiberMap B S hS f hf x).naturality k)).symm

/-- The lifts of `x̄` into the base-changed charts are compatible with morphisms of charts of
`Y`: the bijection on lifts is natural, and injective. -/
theorem smallBaseChangeFiberInv_map (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (x : GeometricPoint B S hS X.1)
    {V W : SmallEtale B S hS Y.1} (k : V ⟶ W)
    (q : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) V) :
    (geometricFiber B S hS X.1 x).map ((smallBaseChange B S hS f hf).map k)
        (smallBaseChangeFiberInv B S hS f hf x V q) =
      smallBaseChangeFiberInv B S hS f hf x W
        ((geometricFiber B S hS Y.1 (geometricPointMap f.hom x)).map k q) := by
  refine (smallBaseChangeFiberMap_bijective B S hS f hf x W).1
    ((geometricFiber_map_smallBaseChangeFiberMap_app B S hS f hf x k _).symm.trans ?_)
  rw [smallBaseChangeFiberMap_smallBaseChangeFiberInv]
  exact (smallBaseChangeFiberMap_smallBaseChangeFiberInv B S hS f hf x W _).symm

/-- **Base change of pointed étale charts.** For a representable morphism `f : X ⟶ Y` of
algebraic spaces and a geometric point `x̄` of `X`, the functor from the small étale
neighbourhoods of `f(x̄)` to those of `x̄` sending `V` to `X ×_Y V` with the lift of `x̄`
determined by the lift of `f(x̄)` carried by `V`. -/
noncomputable def SmallEtaleNeighborhood.baseChange (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (x : GeometricPoint B S hS X.1) :
    SmallEtaleNeighborhood (geometricPointMap f.hom x) ⥤ SmallEtaleNeighborhood x where
  obj V :=
    { chart := (smallBaseChange B S hS f hf).obj V.chart
      point := (smallBaseChangeFiberInv B S hS f hf x V.chart ⟨V.point, V.point_comp⟩).1
      point_comp :=
        (smallBaseChangeFiberInv B S hS f hf x V.chart ⟨V.point, V.point_comp⟩).2 }
  map {V W} k :=
    { hom := (smallBaseChange B S hS f hf).map k.hom
      point_comp := congrArg Subtype.val
        ((smallBaseChangeFiberInv_map B S hS f hf x k.hom ⟨V.point, V.point_comp⟩).trans
          (congrArg (smallBaseChangeFiberInv B S hS f hf x W.chart)
            (show (geometricFiber B S hS Y.1 (geometricPointMap f.hom x)).map k.hom
                ⟨V.point, V.point_comp⟩ = ⟨W.point, W.point_comp⟩ from
              Subtype.ext k.point_comp))) }
  map_id V := SmallEtaleNeighborhood.Hom.ext ((smallBaseChange B S hS f hf).map_id V.chart)
  map_comp k l := SmallEtaleNeighborhood.Hom.ext
    ((smallBaseChange B S hS f hf).map_comp k.hom l.hom)

/-- A lift of `x̄` into a base-changed chart `X ×_Y W` whose image in `X ×_Y V` is the lift
determined by a lift `q` of `f(x̄)` into `V` has image `q` under the cartesian projection: a
compatibility of lifts upstairs becomes a compatibility of lifts downstairs. -/
theorem geometricFiber_map_smallBaseChangeFiberMap (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (x : GeometricPoint B S hS X.1)
    {W V : SmallEtale B S hS Y.1} (a : W ⟶ V)
    (pW : GeometricFiber B S hS X.1 x ((smallBaseChange B S hS f hf).obj W))
    (qV : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) V)
    (h : (geometricFiber B S hS X.1 x).map ((smallBaseChange B S hS f hf).map a) pW =
      smallBaseChangeFiberInv B S hS f hf x V qV) :
    (geometricFiber B S hS Y.1 (geometricPointMap f.hom x)).map a
        ((smallBaseChangeFiberMap B S hS f hf x).app W pW) = qV := by
  refine (geometricFiber_map_smallBaseChangeFiberMap_app B S hS f hf x a pW).trans ?_
  rw [h, smallBaseChangeFiberMap_smallBaseChangeFiberInv]

/-- **Base-changed pointed charts refine every pointed chart.** For a closed immersion
`f : X ⟶ Y` of algebraic spaces, a geometric point `x̄` of `X` and a small étale neighbourhood
`U` of `x̄`, there is a small étale neighbourhood `V` of `f(x̄)` whose base change maps to `U`.

Base changes of étale charts of `Y` are cover dense among étale charts of `X` by Stacks 04E5,
part (1), and `AlgebraicGeometry.Space.exists_hom_of_isCoverDense` turns cover density into
cofinality among *pointed* charts; the lift of `x̄` it produces makes the chart of `Y` a
pointed chart through the bijection on lifts. -/
theorem SmallEtaleNeighborhood.exists_baseChange_hom (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (U : SmallEtaleNeighborhood x) :
    ∃ (V : SmallEtaleNeighborhood (geometricPointMap f.hom x)),
      Nonempty ((SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).obj V ⟶ U) := by
  have hbc : (smallBaseChange B S hS f hf.rep).IsCoverDense
      (SmallEtale.topology B S hS X.1) :=
    smallBaseChange_isCoverDense_of_isClosedImmersion B S hS f hf
  obtain ⟨Vc, p, g, hg⟩ :=
    exists_hom_of_isCoverDense (smallBaseChange B S hS f hf.rep) X.2 x U
  refine ⟨⟨Vc, ((smallBaseChangeFiberMap B S hS f hf.rep x).app Vc p).1,
    ((smallBaseChangeFiberMap B S hS f hf.rep x).app Vc p).2⟩, ⟨⟨g, ?_⟩⟩⟩
  have hp : smallBaseChangeFiberInv B S hS f hf.rep x Vc
      ((smallBaseChangeFiberMap B S hS f hf.rep x).app Vc p) = p :=
    (smallBaseChangeFiberMap_bijective B S hS f hf.rep x Vc).1
      (smallBaseChangeFiberMap_smallBaseChangeFiberInv B S hS f hf.rep x Vc _)
  exact Eq.trans (congrArg (fun z : GeometricFiber B S hS X.1 x
    ((smallBaseChange B S hS f hf.rep).obj Vc) =>
      z.1 ≫ (SmallEtale.toOver B S hS X.1).map g) hp) hg

/-- **Local fullness of base change on pointed charts.** Let `f : X ⟶ Y` be a closed immersion
of algebraic spaces, let `x̄` be a geometric point of `X` and let `φ` be a morphism between the
base changes of two small étale neighbourhoods `V`, `V'` of `f(x̄)`. Then there are a small
étale neighbourhood `W` of `f(x̄)` and morphisms `a : W ⟶ V`, `b : W ⟶ V'` with
`baseChange a ≫ φ = baseChange b`.

Stacks 04FV provides the chart `W` together with `a` and `b` on charts, *and* the fact that the
base change of `a` is an isomorphism. That is what carries the lift of `x̄` from `X ×_Y V` back
to `X ×_Y W`, making `W` a pointed chart with `a` and `b` morphisms of pointed charts, by
`AlgebraicGeometry.Space.geometricFiber_map_smallBaseChangeFiberMap`. -/
theorem SmallEtaleNeighborhood.exists_baseChange_factorization (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (V V' : SmallEtaleNeighborhood (geometricPointMap f.hom x))
    (φ : (SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).obj V ⟶
      (SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).obj V') :
    ∃ (W : SmallEtaleNeighborhood (geometricPointMap f.hom x)) (a : W ⟶ V) (b : W ⟶ V'),
      (SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).map a ≫ φ =
        (SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).map b := by
  obtain ⟨Wc, a, hiso, b, hab⟩ :=
    exists_isIso_smallBaseChange_map_of_isClosedImmersion B S hS f hf V.chart V'.chart φ.hom
  have := hiso
  have hbij : Function.Bijective ((geometricFiber B S hS X.1 x).map
      ((smallBaseChange B S hS f hf.rep).map a)) :=
    ConcreteCategory.bijective_of_isIso _
  obtain ⟨pW, hA⟩ := hbij.2
    (smallBaseChangeFiberInv B S hS f hf.rep x V.chart ⟨V.point, V.point_comp⟩)
  have hB : (geometricFiber B S hS X.1 x).map ((smallBaseChange B S hS f hf.rep).map b) pW =
      smallBaseChangeFiberInv B S hS f hf.rep x V'.chart ⟨V'.point, V'.point_comp⟩ :=
    (congrArg (fun z : (smallBaseChange B S hS f hf.rep).obj Wc ⟶
          (smallBaseChange B S hS f hf.rep).obj V'.chart =>
        (geometricFiber B S hS X.1 x).map z pW) hab).trans
      ((ConcreteCategory.congr_hom ((geometricFiber B S hS X.1 x).map_comp
          ((smallBaseChange B S hS f hf.rep).map a) φ.hom) pW).trans
        ((congrArg (fun z => (geometricFiber B S hS X.1 x).map φ.hom z) hA).trans
          (Subtype.ext φ.point_comp)))
  refine ⟨⟨Wc, ((smallBaseChangeFiberMap B S hS f hf.rep x).app Wc pW).1,
      ((smallBaseChangeFiberMap B S hS f hf.rep x).app Wc pW).2⟩,
    ⟨a, congrArg Subtype.val
      (geometricFiber_map_smallBaseChangeFiberMap B S hS f hf.rep x a pW _ hA)⟩,
    ⟨b, congrArg Subtype.val
      (geometricFiber_map_smallBaseChangeFiberMap B S hS f hf.rep x b pW _ hB)⟩, ?_⟩
  exact SmallEtaleNeighborhood.Hom.ext hab.symm

/-- **Base change on pointed étale charts is initial.** For a closed immersion `f : X ⟶ Y` of
algebraic spaces over `S` and a geometric point `x̄` of `X`, the functor
`AlgebraicGeometry.Space.SmallEtaleNeighborhood.baseChange` from the small étale neighbourhoods
of `f(x̄)` to those of `x̄` is initial.

The small étale neighbourhoods of `f(x̄)` are cofiltered, every neighbourhood of `x̄` is refined
by a base-changed one, and two morphisms out of a base-changed neighbourhood are equalized
after base-changing a further refinement: cofilteredness of the neighbourhoods of `x̄`
equalizes them by some neighbourhood, which is in turn refined by a base-changed one, and the
resulting morphism between base changes is the base change of a morphism of pointed charts of
`Y` by `AlgebraicGeometry.Space.SmallEtaleNeighborhood.exists_baseChange_factorization`. -/
theorem SmallEtaleNeighborhood.initial_baseChange (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1) :
    (SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).Initial := by
  let _ : IsCofiltered (SmallEtaleNeighborhood x) :=
    isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 x
  let _ : IsCofiltered (SmallEtaleNeighborhood (geometricPointMap f.hom x)) :=
    isCofiltered_smallEtaleNeighborhood B S hS Y.1 Y.2 (geometricPointMap f.hom x)
  refine Functor.initial_of_exists_of_isCofiltered _
    (fun U => SmallEtaleNeighborhood.exists_baseChange_hom B S hS f hf x U)
    (fun {U V} s s' => ?_)
  obtain ⟨W, e, he⟩ := IsCofilteredOrEmpty.cone_maps s s'
  obtain ⟨V₀, ⟨k⟩⟩ := SmallEtaleNeighborhood.exists_baseChange_hom B S hS f hf x W
  obtain ⟨W₁, a, b, hab⟩ :=
    SmallEtaleNeighborhood.exists_baseChange_factorization B S hS f hf x V₀ V (k ≫ e)
  refine ⟨W₁, b, ?_⟩
  rw [← hab]
  simp only [Category.assoc]
  rw [he]

end AlgebraicGeometry.Space

end
