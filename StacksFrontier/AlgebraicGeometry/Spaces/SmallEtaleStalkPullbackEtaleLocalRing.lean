module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkPullbackGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkPullbackRingMap
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalk-ring homomorphism of a pullback of modules is the map of étale local rings

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `x̄` be a geometric
point of `X`.  The morphism of small étale ringed topoi of Stacks 03G8 together with the points
of the two small étale sites determined by `x̄` and its image, and with the fibre comparison of
Stacks 04K2, part (4), is an instance of the matched pair of points for which Stacks 05V5
computes the stalk of a pullback of sheaves of modules.  The homomorphism of stalk rings along
which that computation extends scalars is `Stacks.Sheaves.StalkPullback.stalkRingMap`.

This file computes it on germs and concludes that, transported to the étale local rings of
Stacks 04KG by the comparison of Stacks 05VQ, it *is* the canonical homomorphism
`𝒪_{Y, f ∘ x̄} ⟶ 𝒪_{X, x̄}` of étale local rings of Stacks 04NG.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleStructureSetFiberMap`: the fibre comparison of Stacks 04K2,
  part (4) for sheaves of sets, followed by the fibre at `x̄` of the inverse-image form of the
  structure map, as a map of the fibres of the sheaves of sets underlying the two structure
  sheaves.
* `AlgebraicGeometry.Space.smallEtaleStalkPullbackRingMap`: the homomorphism of structure-sheaf
  stalks along which Stacks 05V5 extends scalars, for the small étale ringed topoi.
* `AlgebraicGeometry.Space.smallEtaleStalkPullbackEtaleLocalRingMap_eq`: the same homomorphism read
  on the étale local rings of Stacks 04KG.

## Main results

* `AlgebraicGeometry.Space.smallEtaleStructureSetFiberMap_toPresheafFiber` and
  `AlgebraicGeometry.Space.smallEtaleStalkPullbackRingMap_toPresheafFiber`: the germ formula —
  the germ at a lift of `f ∘ x̄` of a regular function on an étale chart `V` of `Y` goes to the
  germ at a compatible lift of `x̄` of its pullback along any commutative diagram of étale
  scheme charts over `f` with lower chart `V`.
* `AlgebraicGeometry.Space.isEtaleLocalRingMap_smallEtaleStalkPullbackRingMap`: the transported
  homomorphism pulls germs back in every compatible diagram of pointed étale scheme charts,
  that is, it satisfies `AlgebraicGeometry.Space.IsEtaleLocalRingMap`.
* `AlgebraicGeometry.Space.smallEtaleStalkPullbackEtaleLocalRingMap_eq`: consequently it is the
  canonical homomorphism of étale local rings of Stacks 04NG, by the uniqueness clause of that
  result.

## Implementation notes

The germ formula is proved on sheaves of sets first and then carried to the stalk rings.  On
sheaves of sets the fibre comparison is the transpose, across the skyscraper adjunction at the
image point, of a single map out of the structure sheaf of `Y`
(`AlgebraicGeometry.Space.fiberIso_comp_setFSharpInverseImage`), so germs are read off its
components by the skyscraper-adjunction lemma
`CategoryTheory.GrothendieckTopology.Point`'s
`toPresheafFiber_comp_skyscraperSheafAdjunction_homEquiv_symm`;
computing those components is the chartwise description of a morphism of sheaves over the
correspondence of Stacks 03G8, `AlgebraicGeometry.Space.chartCorrespondence_postcomp`, together
with the projections of the skyscraper comparison.  The passage to the stalk rings is
`Stacks.Sheaves.StalkPullback.stalkRingMap_toPresheafFiber`.

Every step of the computation on sheaves of sets is an identity of morphisms of `Type u`
evaluated at a section, and the evaluation is `CategoryTheory.types_congr_hom` rather than the
`CategoryTheory.ConcreteCategory.congr_hom` of the analogous computation over `CommRingCat` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleStalkStructureMap.lean`: the specialised lemma
has the two objects of `Type u` and the concrete structure on `Type u` already fixed in its
statement, whereas the general one leaves the concrete category to unification, where the
product indexed by a geometric fibre makes the problem diverge.

## References

* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.StalkPullback Stacks.Sheaves.StalkTransport

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The chartwise formula for a map out of the structure sheaf of `Y` on sheaves of sets.**
Pushing a map out of the sheaf of sets underlying the structure sheaf of `X` forward along the
canonical morphism of small étale topoi of Stacks 03G8 and restricting the result along a
diagram of étale scheme charts is pullback of regular functions along the diagram's morphism of
schemes, followed by the original map.

This is `AlgebraicGeometry.Space.chartCorrespondence_postcomp` for the structure sheaf, the
`f`-map it consumes being the one that the chart correspondence attaches to the structure map of
Stacks 03G8; that this `f`-map is pullback of regular functions is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_chart`, and the two forgetful readings of the
structure map agree by `AlgebraicGeometry.Space.setFSharp_eq_forgetRing_fSharp`. -/
theorem smallEtaleStructureSetHom_postcomp_chart
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (a : smallEtaleStructureSetSheaf B S hS X ⟶
      (smallEtaleComparisonRestriction B S hS X).obj H)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (h : (comparisonFunctor B S hS X).obj d.U ⟶ chartBaseChange B S hS f d.V)
    (hh : HEq (((SpacesEtale.toSpaces B S hS X).map h) ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj d.V)).hom
      (yoneda.map d.g))
    (s : (smallEtaleStructureSetSheaf B S hS Y).obj.obj (op d.V)) :
    H.obj.map h.op
        (((sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
            (smallEtaleRingedToposModulesHom B S hS f).fSharp ≫
          (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map a ≫
          (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H).hom.app (op d.V) s) =
      a.hom.app (op d.U) (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s) := by
  have hc := chartCorrespondence_postcomp B S hS f
    (smallEtaleStructureSetSheaf B S hS X) (smallEtaleStructureSetSheaf B S hS Y) H a
    ((fMapEquivPushforwardHom_ringUniverse B S hS f
        (smallEtaleStructureSetSheaf B S hS X) (smallEtaleStructureSetSheaf B S hS Y)).symm
      ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
        (smallEtaleRingedToposModulesHom B S hS f).fSharp))
    d h hh s
  have hd : ((fMapEquivPushforwardHom_ringUniverse B S hS f
        (smallEtaleStructureSetSheaf B S hS X) (smallEtaleStructureSetSheaf B S hS Y)).symm
      ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
        (smallEtaleRingedToposModulesHom B S hS f).fSharp)).app d s =
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s := by
    rw [setFSharp_eq_forgetRing_fSharp]
    exact smallEtaleRingedToposHom_chart B S hS f d s
  rw [hd] at hc
  have he : fMapEquivPushforwardHom_ringUniverse B S hS f
        (smallEtaleStructureSetSheaf B S hS X) (smallEtaleStructureSetSheaf B S hS Y)
      ((fMapEquivPushforwardHom_ringUniverse B S hS f
          (smallEtaleStructureSetSheaf B S hS X)
          (smallEtaleStructureSetSheaf B S hS Y)).symm
        ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
          (smallEtaleRingedToposModulesHom B S hS f).fSharp)) =
      (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
        (smallEtaleRingedToposModulesHom B S hS f).fSharp :=
    Equiv.apply_symm_apply _ _
  rw [he] at hc
  exact hc.symm

variable (x : GeometricPoint B S hS X.1)

/-- The fibre comparison of Stacks 04K2, part (4) for sheaves of sets, followed by the fibre at
`x̄` of the inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map of Stacks 03G8: a map from
the fibre at the image point of the sheaf of sets underlying `𝒪_Y` to the fibre at `x̄` of the
sheaf of sets underlying `𝒪_X`. -/
abbrev smallEtaleStructureSetFiberMap :
    ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).sheafFiber
        (A := Type u)).obj (smallEtaleStructureSetSheaf B S hS Y) ⟶
      smallEtaleStructureSetFiber B S hS x :=
  (smallEtaleInverseImageFiberIso B S hS f x).hom.app (smallEtaleStructureSetSheaf B S hS Y) ≫
    ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := Type u)).map
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
        (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage)

/-- **The germ formula on sheaves of sets.**  Given a commutative diagram of étale scheme charts
over `f` and compatible lifts of `x̄` and of its image into its two charts, the fibre comparison
followed by the fibre of the inverse-image structure map carries the germ of a regular function
on the lower chart to the germ of its pullback along the diagram's morphism of schemes. -/
theorem smallEtaleStructureSetFiberMap_toPresheafFiber
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (p : GeometricFiber B S hS X.1 x d.U)
    (q : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) d.V) (hpq : p.1 ≫ d.g = q.1)
    (s : (smallEtaleStructureSetSheaf B S hS Y).obj.obj (op d.V)) :
    smallEtaleStructureSetFiberMap B S hS f x
        ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).toPresheafFiber d.V q
          (smallEtaleStructureSetSheaf B S hS Y).obj s) =
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber d.U p
        (smallEtaleStructureSetSheaf B S hS X).obj
        (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s) := by
  have := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  have hgerm : (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).toPresheafFiber
        d.V q (smallEtaleStructureSetSheaf B S hS Y).obj ≫
        smallEtaleStructureSetFiberMap B S hS f x =
      (smallEtaleStructureSetSkyscraperHom B S hS f x).hom.app (op d.V) ≫
        Pi.π (fun _ : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) d.V =>
          smallEtaleStructureSetFiber B S hS x) q := by
    rw [smallEtaleStructureSetFiberMap, fiberIso_comp_setFSharpInverseImage]
    exact Point.toPresheafFiber_comp_skyscraperSheafAdjunction_homEquiv_symm
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
      (smallEtaleStructureSetSheaf B S hS Y) (smallEtaleStructureSetFiber B S hS x)
      (smallEtaleStructureSetSkyscraperHom B S hS f x) d.V q
  refine Eq.trans (types_congr_hom hgerm s) ?_
  refine Eq.trans (types_congr_hom (smallEtaleSkyscraperIso_hom_app_π B S hS f x
    (smallEtaleStructureSetFiber B S hS x) d.V q)
    (((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
        (smallEtaleStructureSetUnit B S hS x)).hom.app (op d.V)
      (((sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
        (smallEtaleRingedToposModulesHom B S hS f).fSharp).hom.app (op d.V) s))) ?_
  rw [spacesBaseChangeFiberIso_inv_app B S hS f x d p q hpq]
  refine Eq.trans (types_congr_hom (Point.skyscraperPresheaf_map_π
    (spacesEtaleSitePoint x) (baseChangeArrowOfChartDiagram B S hS f d)
    (smallEtaleStructureSetFiber B S hS x) p) _).symm ?_
  refine Eq.trans (congrArg (fun z =>
    Pi.π (fun _ : GeometricFiber B S hS X.1 x d.U =>
      smallEtaleStructureSetFiber B S hS x) p z)
    (smallEtaleStructureSetHom_postcomp_chart B S hS f
      ((spacesEtaleSitePoint x).skyscraperSheafFunctor.obj
        (smallEtaleStructureSetFiber B S hS x))
      (smallEtaleStructureSetUnit B S hS x) d (baseChangeArrowOfChartDiagram B S hS f d)
      (heq_of_eq (yoneda_map_baseChangeArrowOfChartDiagram B S hS f d)) s)) ?_
  exact types_congr_hom (Point.skyscraperSheafAdjunction_unit_π
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleStructureSetSheaf B S hS X) d.U p)
    (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s)

/-- **The homomorphism `(𝒪_Y)_{f ∘ x̄} ⟶ (𝒪_X)_{x̄}` of structure-sheaf stalks** along which
Stacks 05V5 extends scalars, for the morphism of small étale ringed topoi of Stacks 03G8 and the
matched pair of points determined by a geometric point `x̄` of `X`, the identification of stalk
functors being the fibre comparison of Stacks 04K2, part (4). -/
abbrev smallEtaleStalkPullbackRingMap :
    Stacks.ringFiber (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
        (smallEtaleRingedTopos B S hS Y).O.obj →+*
      Stacks.ringFiber (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O.obj :=
  stalkRingMap (smallEtaleRingedToposModulesHom B S hS f)
    (etaleSitePoint B S hS X.1 x X.2)
    (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
    (smallEtaleInverseImageFiberIso B S hS f x)

/-- **The germ formula for the homomorphism of structure-sheaf stalks.**  Given a commutative
diagram of étale scheme charts over `f` and compatible lifts of `x̄` and of its image into its
two charts, it carries the germ of a regular function on the lower chart to the germ of its
pullback along the diagram's morphism of schemes. -/
theorem smallEtaleStalkPullbackRingMap_toPresheafFiber
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (p : GeometricFiber B S hS X.1 x d.U)
    (q : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) d.V) (hpq : p.1 ≫ d.g = q.1)
    (s : (structurePresheaf B S hS Y.1).obj (op d.V)) :
    smallEtaleStalkPullbackRingMap B S hS f x
        ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).toPresheafFiber d.V q
          (smallEtaleRingedTopos B S hS Y).O.obj s) =
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber d.U p
        (smallEtaleRingedTopos B S hS X).O.obj
        (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s) := by
  refine Eq.trans (stalkRingMap_toPresheafFiber (smallEtaleRingedToposModulesHom B S hS f)
    (etaleSitePoint B S hS X.1 x X.2)
    (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
    (smallEtaleInverseImageFiberIso B S hS f x) d.V q s) ?_
  refine Eq.trans (congrArg (fun z => (Stacks.commRingPresheafFiberIso
      (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O.obj).hom.hom
    (ringStalkComparison (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleStructureRingSheaf B S hS X) z))
    (smallEtaleStructureSetFiberMap_toPresheafFiber B S hS f x d p q hpq s)) ?_
  refine Eq.trans (congrArg (Stacks.commRingPresheafFiberIso
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O.obj).hom.hom
    (ringStalkComparison_ringGerm (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleStructureRingSheaf B S hS X) d.U p
      (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s))) ?_
  exact Stacks.commRingPresheafFiberIso_hom_toPresheafFiber
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O.obj d.U p
    (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s)

/-- **The germ characterization of the homomorphism of stalk rings.**  Transported to the étale
local rings, the homomorphism along which Stacks 05V5 extends scalars pulls germs of regular
functions back in every commuting diagram of pointed étale scheme charts over `f`: it satisfies
`AlgebraicGeometry.Space.IsEtaleLocalRingMap`. -/
theorem isEtaleLocalRingMap_smallEtaleStalkPullbackRingMap :
    IsEtaleLocalRingMap f.hom x
      (((pointStalkRingEquiv B S hS X x).toRingHom.comp
          (smallEtaleStalkPullbackRingMap B S hS f x)).comp
        (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).symm.toRingHom) := by
  intro U V g hcomm hpoint
  refine RingHom.ext fun s => ?_
  have hX := pointStalkRingEquiv_germ_neighborhood B S hS X x U
    (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map g)) s)
  have hY := pointStalkRingEquiv_germ_neighborhood B S hS Y (geometricPointMap f.hom x) V s
  have hg := smallEtaleStalkPullbackRingMap_toPresheafFiber B S hS f x
    ⟨U.chart, V.chart, g, hcomm⟩
    (⟨U.point, U.point_comp⟩ : GeometricFiber B S hS X.1 x U.chart)
    (⟨V.point, V.point_comp⟩ :
      GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) V.chart) hpoint s
  have hY' : (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).symm
      (etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x) (op V) s) =
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).toPresheafFiber V.chart
        ⟨V.point, V.point_comp⟩ (smallEtaleRingedTopos B S hS Y).O.obj s := by
    rw [← hY]
    exact (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).symm_apply_apply _
  refine Eq.trans hX.symm (Eq.trans (congrArg (pointStalkRingEquiv B S hS X x) hg.symm) ?_)
  exact congrArg (fun z => pointStalkRingEquiv B S hS X x
    (smallEtaleStalkPullbackRingMap B S hS f x z)) hY'.symm

/-- **Stacks 04NG for the homomorphism of stalk rings of a pullback.**  The homomorphism of
structure-sheaf stalks along which Stacks 05V5 extends scalars is, after transport to the étale
local rings of Stacks 04KG, the canonical homomorphism of étale local rings of Stacks 04NG. -/
theorem smallEtaleStalkPullbackEtaleLocalRingMap_eq :
    (((pointStalkRingEquiv B S hS X x).toRingHom.comp
          (smallEtaleStalkPullbackRingMap B S hS f x)).comp
        (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).symm.toRingHom) =
      etaleLocalRingMap X.2 f.hom x :=
  (existsUnique_etaleLocalRingMap X.2 f.hom x).unique
    (isEtaleLocalRingMap_smallEtaleStalkPullbackRingMap B S hS f x)
    (etaleLocalRingMap_isEtaleLocalRingMap X.2 f.hom x)

end AlgebraicGeometry.Space

end

end
