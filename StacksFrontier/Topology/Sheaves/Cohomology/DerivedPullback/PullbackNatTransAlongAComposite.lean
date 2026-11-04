module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TotalTensorComplexAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional

/-!
# The comparison `Lf^*(QM) ⟶ Q(f^*M)` along a composite

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (Z, 𝒪_Z)` be morphisms of ringed spaces.
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` is the comparison

`Lf^*(QM) ⟶ Q(f^*M)`

of the derived pullback with the degreewise pullback, as a morphism of functors on cochain
complexes.  This file proves that it is compatible with composition: the comparison for `f ≫ g`,
read through the composition isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D5S, is the
comparison for `g` followed by the comparison for `f`, followed by the composition law for
degreewise pullback of complexes.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.pullbackOnHomotopyCompIso_hom_app_comp_factors`: on
  the image of a cochain complex, the pullback-composition isomorphism of homotopy categories
  agrees with the pullback-composition isomorphism of complexes, through Mathlib's
  `CategoryTheory.Functor.mapHomotopyCategoryFactors` for `f`, `g` and `f ≫ g`.
* `derivedPullbackCompIsoCanonical_hom_app_comp_derivedPullbackNatTrans`, in the same
  namespace: **the composition law for the comparison**, at the `DerivedCategory.Q` level.

## Implementation notes

*The homotopy-category level.*  `derivedPullbackCompIsoCanonical_hom_app_comp_comparison` of
`Stacks.Cohomology.DerivedPushforwardComposition` is the composition law for the comparison
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison`, whose source is
`Qh` rather than `Q`.
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` inserts the `Q` versus
`Qh ∘ quotient` bridge `DerivedCategory.quotientCompQhIso` at both ends and Mathlib's
`CategoryTheory.Functor.mapHomotopyCategoryFactors`; lifting the composition law therefore means
threading the bridge at three places and reconciling the three `mapHomotopyCategoryFactors`
against the two composition isomorphisms, which is the first result above.

*Why the chase is carried out abstractly.*  `comp_of_factors` states the diagram chase for
arbitrary categories, functors and transformations of the right shapes.  The concrete functors
are reducible abbreviations of derived functors on categories of sheaves of modules, where
`rw` has to unfold them to build a rewrite motive; at the abstract statement every term is small
and the same chase is six rewrites.  The concrete side is then one `exact` passing arguments.

*The two spellings of degreewise pullback.*
`Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex` is written at
`StacksDraft.KFlat.modulePullback`, which is `RingedSpaceModuleAdjunction.modulePullback`
retyped, and the local `implicit_reducible` attributes are what let the two meet during
unification.

*No new hypotheses.*  `M` is an arbitrary cochain complex of `𝒪_Z`-modules, with no boundedness,
flatness or quasi-coherence assumption, and `f`, `g` are arbitrary morphisms of ringed spaces.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

/-- **The diagram chase behind the composition law for the comparison `Lf^*(QM) ⟶ Q(f^*M)`.**

Three categories of complexes `CZ, CY, CX`, three homotopy categories `KZ, KY, KX` and three
localized categories `DZ, DY, DX`, with quotient functors `pZ, pY, pX`, localizations
`hZ, hY, hX` and the composites identified by `bZ, bY, bX`; degreewise functors `Kf, Kg, Kgf`
on the homotopy categories and `Cf, Cg, Cgf` on the complexes, identified on the image of the
quotient by `Ff, Fg, Fgf`; derived functors `Lf, Lg, Lgf` with comparisons `εf, εg, εgf`; and
composition isomorphisms `cK`, `cC`, `D` upstairs, downstairs and on the derived functors.

Given the composition law for the comparisons on the homotopy categories (`hfac`) and the
agreement of the two composition isomorphisms on the image of the quotient (`hcompat`), the
composition law holds for the transformations built from `b`, `ε` and `F`. -/
private lemma comp_of_factors
    {CZ CY CX KZ KY KX DZ DY DX : Type*}
    [Category CZ] [Category CY] [Category CX] [Category KZ] [Category KY] [Category KX]
    [Category DZ] [Category DY] [Category DX]
    {pZ : CZ ⥤ KZ} {pY : CY ⥤ KY} {pX : CX ⥤ KX}
    {hZ : KZ ⥤ DZ} {hY : KY ⥤ DY} {hX : KX ⥤ DX}
    {QZ : CZ ⥤ DZ} {QY : CY ⥤ DY} {QX : CX ⥤ DX}
    (bZ : pZ ⋙ hZ ≅ QZ) (bY : pY ⋙ hY ≅ QY) (bX : pX ⋙ hX ≅ QX)
    {Kf : KY ⥤ KX} {Kg : KZ ⥤ KY} {Kgf : KZ ⥤ KX}
    {Cf : CY ⥤ CX} {Cg : CZ ⥤ CY} {Cgf : CZ ⥤ CX}
    (Ff : pY ⋙ Kf ≅ Cf ⋙ pX) (Fg : pZ ⋙ Kg ≅ Cg ⋙ pY) (Fgf : pZ ⋙ Kgf ≅ Cgf ⋙ pX)
    {Lf : DY ⥤ DX} {Lg : DZ ⥤ DY} {Lgf : DZ ⥤ DX}
    (εf : hY ⋙ Lf ⟶ Kf ⋙ hX) (εg : hZ ⋙ Lg ⟶ Kg ⋙ hY) (εgf : hZ ⋙ Lgf ⟶ Kgf ⋙ hX)
    (cK : Kg ⋙ Kf ≅ Kgf) (cC : Cg ⋙ Cf ≅ Cgf) (D : Lg ⋙ Lf ≅ Lgf)
    (hfac : ∀ W : KZ, D.hom.app (hZ.obj W) ≫ εgf.app W =
      Lf.map (εg.app W) ≫ εf.app (Kg.obj W) ≫ hX.map (cK.hom.app W))
    (hcompat : ∀ M : CZ, cK.hom.app (pZ.obj M) ≫ Fgf.hom.app M =
      Kf.map (Fg.hom.app M) ≫ Ff.hom.app (Cg.obj M) ≫ pX.map (cC.hom.app M))
    (M : CZ) :
    D.hom.app (QZ.obj M) ≫ (Lgf.map (bZ.inv.app M) ≫ εgf.app (pZ.obj M) ≫
        hX.map (Fgf.hom.app M) ≫ bX.hom.app (Cgf.obj M)) =
      Lf.map (Lg.map (bZ.inv.app M) ≫ εg.app (pZ.obj M) ≫ hY.map (Fg.hom.app M) ≫
          bY.hom.app (Cg.obj M)) ≫
        (Lf.map (bY.inv.app (Cg.obj M)) ≫ εf.app (pY.obj (Cg.obj M)) ≫
          hX.map (Ff.hom.app (Cg.obj M)) ≫ bX.hom.app (Cf.obj (Cg.obj M))) ≫
        QX.map (cC.hom.app M) := by
  have hnat := D.hom.naturality (bZ.inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  have hb := bX.hom.naturality (cC.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hb
  have he := εf.naturality (Fg.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at he
  have hc : hX.map (cK.hom.app (pZ.obj M)) ≫ hX.map (Fgf.hom.app M) =
      hX.map (Kf.map (Fg.hom.app M)) ≫ hX.map (Ff.hom.app (Cg.obj M)) ≫
        hX.map (pX.map (cC.hom.app M)) := by
    rw [← hX.map_comp, hcompat M, hX.map_comp, hX.map_comp]
  have hcancel : Lf.map (bY.hom.app (Cg.obj M)) ≫ Lf.map (bY.inv.app (Cg.obj M)) = 𝟙 _ := by
    rw [← Lf.map_comp, Iso.hom_inv_id_app, Lf.map_id]
  simp only [Category.assoc]
  rw [← reassoc_of% hnat, reassoc_of% (hfac (pZ.obj M)), reassoc_of% hc, hb]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hcancel, reassoc_of% he]

/-- Cancelling three identities out of a composite: if `jy`, `ix` and `i'x` are identities and
`u = v`, then `u ≫ jy = ix ≫ i'x ≫ v`. -/
private lemma comp_id_eq_id_comp {C : Type*} [Category C] {x y : C}
    {u v : x ⟶ y} {jy : y ⟶ y} {ix i'x : x ⟶ x}
    (hj : jy = 𝟙 y) (hi : ix = 𝟙 x) (hi' : i'x = 𝟙 x) (huv : u = v) :
    u ≫ jy = ix ≫ i'x ≫ v := by
  rw [hj, hi, hi', Category.comp_id, Category.id_comp, Category.id_comp, huv]

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The two pullback-composition isomorphisms agree on the image of a cochain complex.**  On
the homotopy categories the isomorphism is
`Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso`, on complexes it is
`Stacks.PullbackTensorComposition.pullbackComplexCompIso`, and Mathlib's
`CategoryTheory.Functor.mapHomotopyCategoryFactors` identifies the two levels for `f`, `g` and
`f ≫ g`. -/
theorem pullbackOnHomotopyCompIso_hom_app_comp_factors
    (M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso f g).hom.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M) ≫
        ((RingedSpaceModuleAdjunction.modulePullback (f ≫ g)).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).hom.app M =
      ((RingedSpaceModuleAdjunction.modulePullback f).mapHomotopyCategory
            (ComplexShape.up ℤ)).map
          (((RingedSpaceModuleAdjunction.modulePullback g).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).hom.app M) ≫
        ((RingedSpaceModuleAdjunction.modulePullback f).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).hom.app ((pullbackComplex g).obj M) ≫
          (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            ((Stacks.PullbackTensorComposition.pullbackComplexCompIso f g).hom.app M) :=
  comp_id_eq_id_comp rfl
    (((RingedSpaceModuleAdjunction.modulePullback f).mapHomotopyCategory
      (ComplexShape.up ℤ)).map_id _) rfl rfl

/-- The value of `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` at a cochain
complex, written out as a composite of four maps; this holds by definition. -/
private lemma derivedPullbackNatTrans_app_eq {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (derivedPullbackNatTrans f).app M =
      (derivedPullback f).map ((DerivedCategory.quotientCompQhIso _).inv.app M) ≫
        (derivedPullbackComparison f).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M) ≫
          DerivedCategory.Qh.map
              (((RingedSpaceModuleAdjunction.modulePullback f).mapHomotopyCategoryFactors
                (ComplexShape.up ℤ)).hom.app M) ≫
            (DerivedCategory.quotientCompQhIso _).hom.app ((pullbackComplex f).obj M) :=
  rfl

open Stacks.Cohomology.DerivedPushforwardComposition in
/-- **The composition law for the comparison `Lf^*(QM) ⟶ Q(f^*M)`.**  For composable morphisms
of ringed spaces `f : X ⟶ Y`, `g : Y ⟶ Z` and an arbitrary cochain complex `M` of
`𝒪_Z`-modules, the composition isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D5S carries
the comparison for `f ≫ g` to the comparison for `g`, then the comparison for `f`, then the
composition law `f^*g^* ≅ (f ≫ g)^*` on complexes. -/
/- No `stacks` attribute: Stacks 0D5S is already covered, unclaused, by
`Stacks.DerivedPullback.Composition.isIso_derivedPullbackCompComparisonCanonical`. This is a
compatibility of that isomorphism with the comparison `Lf^*(QM) ⟶ Q(f^*M)` — a fact about the
construction, not a further clause of 0D5S's statement — so claiming coverage here would
contradict the bare attribute there. -/
theorem derivedPullbackCompIsoCanonical_hom_app_comp_derivedPullbackNatTrans
    (M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app
          (DerivedCategory.Q.obj M) ≫
        (derivedPullbackNatTrans (f ≫ g)).app M =
      (derivedPullback f).map ((derivedPullbackNatTrans g).app M) ≫
        (derivedPullbackNatTrans f).app ((pullbackComplex g).obj M) ≫
          DerivedCategory.Q.map
            ((Stacks.PullbackTensorComposition.pullbackComplexCompIso f g).hom.app M) := by
  simp only [derivedPullbackNatTrans_app_eq]
  exact comp_of_factors (DerivedCategory.quotientCompQhIso _)
    (DerivedCategory.quotientCompQhIso _) (DerivedCategory.quotientCompQhIso _)
    ((RingedSpaceModuleAdjunction.modulePullback f).mapHomotopyCategoryFactors _)
    ((RingedSpaceModuleAdjunction.modulePullback g).mapHomotopyCategoryFactors _)
    ((RingedSpaceModuleAdjunction.modulePullback (f ≫ g)).mapHomotopyCategoryFactors _)
    (derivedPullbackComparison f) (derivedPullbackComparison g)
    (derivedPullbackComparison (f ≫ g))
    (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso f g)
    (Stacks.PullbackTensorComposition.pullbackComplexCompIso f g)
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g)
    (derivedPullbackCompIsoCanonical_hom_app_comp_comparison f g)
    (pullbackOnHomotopyCompIso_hom_app_comp_factors f g) M

end Stacks.Cohomology.DerivedPullbackTensor

end
