module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs

/-!
# Base change of étale scheme charts along a representable morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose underlying morphism of
presheaves is representable. Then the fibre product of an étale scheme chart of `Y` with `X`
over `Y` is again an étale scheme chart, so base change along `f` is a functor between the small
étale sites. It is identified with base change on the spaces-étale sites through the comparison
functors, it is a morphism of small étale sites, and its induced morphism of topoi is
`AlgebraicGeometry.Space.smallToposMorphism`. We also prove that the composition isomorphisms of
`AlgebraicGeometry.Space.smallToposMorphism` are the transported spaces-étale ones and are
adjoint mates of each other.

## Main definitions

* `AlgebraicGeometry.Space.smallBaseChange` is base change on étale scheme charts.
* `AlgebraicGeometry.Space.smallBaseChange_projection` is its cartesian projection to the
  original chart, viewed as a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.smallBaseChange_comparison` is the canonical identification of
  small-chart base change with spaces-étale base change.
* `AlgebraicGeometry.Space.smallBaseChange_topos` identifies the direct image of
  `AlgebraicGeometry.Space.smallToposMorphism` with the one attached to small-chart base change.

## Main results

* `AlgebraicGeometry.Space.smallBaseChange_isPullback` and
  `AlgebraicGeometry.Space.smallBaseChange_comparison_projection`: the base-changed chart is a
  fibre product, and the comparison respects the cartesian projection.
* `AlgebraicGeometry.Space.smallBaseChange_isMorphismOfSites`: small-chart base change is a
  morphism of sites.
* `AlgebraicGeometry.Space.smallBaseChange_topos_comparison`: the identification of direct images
  is the transport of the spaces-étale one through the comparison square.
* `AlgebraicGeometry.Space.smallToposMorphism_comp_comparison` and
  `AlgebraicGeometry.Space.smallToposMorphism_comp_mate`: coherence of the composition
  isomorphisms of `AlgebraicGeometry.Space.smallToposMorphism`.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆ u

/-! ### Generalities -/

namespace CategoryTheory.Functor

/-- The component of a natural isomorphism obtained as the preimage under whiskering by an
equivalence, read off at an object in the image of that equivalence. -/
theorem preimageIso_whiskeringLeft_hom_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E] (i : C ⥤ D) [i.IsEquivalence]
    {F G : D ⥤ E} (e : i ⋙ F ≅ i ⋙ G) (Z : C) :
    (((whiskeringLeft _ _ _).obj i).preimageIso e).hom.app (i.obj Z) = e.hom.app Z :=
  congrArg (fun t => t.app Z) (((whiskeringLeft _ _ _).obj i).map_preimage e.hom)

end CategoryTheory.Functor

namespace MorphismOfTopoi

variable {E : Type u₁} [Category.{v₁} E] {F : Type u₂} [Category.{v₂} F]
  {G : Type u₃} [Category.{v₃} G] {E' : Type u₄} [Category.{v₄} E']
  {F' : Type u₅} [Category.{v₅} F'] {G' : Type u₆} [Category.{v₆} G']

/-- Transport along equivalences takes an identification of the composite direct image with the
direct image of a composite to the corresponding identification of the transported direct
images, coherently with `MorphismOfTopoi.transport_pushforward_comparison`. -/
theorem transport_comp_pushforward_comparison (φ : MorphismOfTopoi E F)
    (ψ : MorphismOfTopoi F G) (χ : MorphismOfTopoi E G)
    (π : φ.pushforward ⋙ ψ.pushforward ≅ χ.pushforward)
    (eE : E ≌ E') (eF : F ≌ F') (eG : G ≌ G') (W : E) :
    (ψ.transport eF eG).pushforward.map
        ((φ.transport_pushforward_comparison eE eF).hom.app W) ≫
      (ψ.transport_pushforward_comparison eF eG).hom.app (φ.pushforward.obj W) ≫
        eG.functor.map (π.hom.app W) =
      (transport_comp_pushforward φ ψ eE eF eG ≪≫
          Functor.isoWhiskerLeft eE.inverse
            (Functor.isoWhiskerRight π eG.functor)).hom.app (eE.functor.obj W) ≫
        (χ.transport_pushforward_comparison eE eG).hom.app W := by
  have hunit : eF.inverse.map (eF.functor.map (φ.pushforward.map (eE.unitIso.inv.app W))) ≫
        eF.unitIso.inv.app (φ.pushforward.obj W) =
      eF.unitIso.inv.app (φ.pushforward.obj (eE.inverse.obj (eE.functor.obj W))) ≫
        φ.pushforward.map (eE.unitIso.inv.app W) :=
    eF.unitIso.inv.naturality (φ.pushforward.map (eE.unitIso.inv.app W))
  have hnat : ψ.pushforward.map (φ.pushforward.map (eE.unitIso.inv.app W)) ≫ π.hom.app W =
      π.hom.app (eE.inverse.obj (eE.functor.obj W)) ≫
        χ.pushforward.map (eE.unitIso.inv.app W) :=
    π.hom.naturality (eE.unitIso.inv.app W)
  have key : ψ.pushforward.map (eF.inverse.map
          (eF.functor.map (φ.pushforward.map (eE.unitIso.inv.app W)))) ≫
        ψ.pushforward.map (eF.unitIso.inv.app (φ.pushforward.obj W)) ≫ π.hom.app W =
      ψ.pushforward.map (eF.unitIso.inv.app
          (φ.pushforward.obj (eE.inverse.obj (eE.functor.obj W)))) ≫
        π.hom.app (eE.inverse.obj (eE.functor.obj W)) ≫
          χ.pushforward.map (eE.unitIso.inv.app W) := by
    rw [← hnat]
    simp only [← Category.assoc, ← ψ.pushforward.map_comp, hunit]
  have hR : (transport_comp_pushforward φ ψ eE eF eG ≪≫
        Functor.isoWhiskerLeft eE.inverse
          (Functor.isoWhiskerRight π eG.functor)).hom.app (eE.functor.obj W) =
      eG.functor.map (ψ.pushforward.map (eF.unitIso.inv.app
          (φ.pushforward.obj (eE.inverse.obj (eE.functor.obj W))))) ≫
        eG.functor.map (π.hom.app (eE.inverse.obj (eE.functor.obj W))) := rfl
  have hL : (ψ.transport eF eG).pushforward.map
        ((φ.transport_pushforward_comparison eE eF).hom.app W) =
      eG.functor.map (ψ.pushforward.map (eF.inverse.map
        (eF.functor.map (φ.pushforward.map (eE.unitIso.inv.app W))))) :=
    congrArg (fun q => (ψ.transport eF eG).pushforward.map q) (Category.comp_id _)
  have hLg : (ψ.transport_pushforward_comparison eF eG).hom.app (φ.pushforward.obj W) =
      eG.functor.map (ψ.pushforward.map (eF.unitIso.inv.app (φ.pushforward.obj W))) :=
    Category.comp_id _
  have hX : (χ.transport_pushforward_comparison eE eG).hom.app W =
      eG.functor.map (χ.pushforward.map (eE.unitIso.inv.app W)) := Category.comp_id _
  have hmap3 : ∀ {A₁ A₂ A₃ A₄ : G} (x : A₁ ⟶ A₂) (y : A₂ ⟶ A₃) (z : A₃ ⟶ A₄),
      eG.functor.map x ≫ eG.functor.map y ≫ eG.functor.map z =
        eG.functor.map (x ≫ y ≫ z) := by
    intro A₁ A₂ A₃ A₄ x y z
    simp
  have hmap3' : ∀ {A₁ A₂ A₃ A₄ : G} (x : A₁ ⟶ A₂) (y : A₂ ⟶ A₃) (z : A₃ ⟶ A₄),
      (eG.functor.map x ≫ eG.functor.map y) ≫ eG.functor.map z =
        eG.functor.map (x ≫ y ≫ z) := by
    intro A₁ A₂ A₃ A₄ x y z
    simp
  rw [hR, hL, hLg, hX]
  exact (hmap3 _ _ _).trans
    ((congrArg (fun q => eG.functor.map q) key).trans (hmap3' _ _ _).symm)

end MorphismOfTopoi

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change of étale scheme charts -/

/-- A base change along a representable morphism of an étale chart is an étale chart. -/
theorem isEtaleChart_representablePullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    IsEtaleChart B S hS X.1 (CostructuredArrow.mk (hf.fst V.1.hom)) :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (hf.isPullback V.1.hom).flip V.property

/-- The compatibility making the base change of a morphism of étale charts well defined. -/
theorem representablePullback_lift_cond {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {V W : SmallEtale B S hS Y.1} (k : V ⟶ W) :
    hf.fst V.1.hom ≫ f.hom = yoneda.map (hf.snd V.1.hom ≫ k.hom.left) ≫ W.1.hom := by
  have hw : yoneda.map k.hom.left ≫ W.1.hom = V.1.hom := CostructuredArrow.w k.hom
  rw [hf.w V.1.hom, yoneda.map_comp, Category.assoc, hw]

/-- For a morphism `f` whose underlying morphism of presheaves is representable, base change along
`f` of étale scheme charts of `Y`, as a functor to étale scheme charts of `X`. -/
@[stacks 03G2 "part (4), base change on scheme charts"]
noncomputable def smallBaseChange {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    SmallEtale B S hS Y.1 ⥤ SmallEtale B S hS X.1 where
  obj V := ⟨CostructuredArrow.mk (hf.fst V.1.hom),
    isEtaleChart_representablePullback B S hS f hf V⟩
  map {V W} k := ObjectProperty.homMk (CostructuredArrow.homMk
    (hf.lift (hf.fst V.1.hom) (hf.snd V.1.hom ≫ k.hom.left)
      (representablePullback_lift_cond B S hS f hf k))
    (hf.lift_fst _ _ _))
  map_id V := by
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (hf.hom_ext ?_ ?_)) <;> simp
  map_comp {U V W} k l := by
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (hf.hom_ext ?_ ?_)) <;> simp

/-- The base change of a morphism of étale charts is compatible with the projections to the
charts of `Y`. -/
theorem smallBaseChange_map_snd {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {V W : SmallEtale B S hS Y.1} (k : V ⟶ W) :
    ((smallBaseChange B S hS f hf).map k).hom.left ≫ hf.snd W.1.hom =
      hf.snd V.1.hom ≫ k.hom.left :=
  hf.lift_snd _ _ _

/-- The cartesian projection from a pulled-back scheme chart to the original chart, viewed as a
morphism of algebraic spaces. -/
@[stacks 03G2 "part (4), projection of pulled-back scheme charts"]
noncomputable def smallBaseChange_projection {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    (smallBaseChange B S hS f hf ⋙ comparisonFunctor B S hS X) ⋙
        SpacesEtale.toSpaces B S hS X ⟶
      comparisonFunctor B S hS Y ⋙ SpacesEtale.toSpaces B S hS Y where
  app V := ObjectProperty.homMk (yoneda.map (hf.snd V.1.hom))
  naturality {V W} k := by
    refine ObjectProperty.hom_ext _ ?_
    change yoneda.map ((smallBaseChange B S hS f hf).map k).hom.left ≫
        yoneda.map (hf.snd W.1.hom) =
      yoneda.map (hf.snd V.1.hom) ≫ yoneda.map k.hom.left
    exact ((yoneda.map_comp _ _).symm.trans
      (congrArg (fun q => yoneda.map q)
        (smallBaseChange_map_snd B S hS f hf k))).trans (yoneda.map_comp _ _)

/-- The base change of an étale scheme chart is cartesian after passage to algebraic spaces. -/
@[stacks 03G2 "part (4), cartesian scheme-chart base change"]
theorem smallBaseChange_isPullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    IsPullback ((smallBaseChange_projection B S hS f hf).app V)
      ((smallBaseChange B S hS f hf ⋙ comparisonFunctor B S hS X).obj V).1.hom
      ((comparisonFunctor B S hS Y).obj V).1.hom f :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) (hf.isPullback V.1.hom).flip

/-- The comparison of the two base changes of a single étale chart: both are fibre products of
the chart along `f`, so they are canonically isomorphic over `X`. -/
noncomputable def smallBaseChangeComparisonIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    (smallBaseChange B S hS f hf ⋙ comparisonFunctor B S hS X).obj V ≅
      (comparisonFunctor B S hS Y ⋙ (spacesBaseChange B S hS f).functor).obj V :=
  (IsEtaleOver B S hS X).isoMk (Over.isoMk
    ((smallBaseChange_isPullback B S hS f hf V).isoIsPullback _ _
      ((spacesBaseChange B S hS f).isPullback ((comparisonFunctor B S hS Y).obj V)))
    ((smallBaseChange_isPullback B S hS f hf V).isoIsPullback_hom_snd _ _ _))

/-- `AlgebraicGeometry.Space.smallBaseChangeComparisonIso` is compatible with the cartesian
projections to the original chart. -/
theorem smallBaseChangeComparisonIso_hom_projection {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    (smallBaseChangeComparisonIso B S hS f hf V).hom.hom.left ≫
        (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V) =
      (smallBaseChange_projection B S hS f hf).app V :=
  (smallBaseChange_isPullback B S hS f hf V).isoIsPullback_hom_fst _ _ _

/-- `AlgebraicGeometry.Space.smallBaseChangeComparisonIso` is a morphism over `X`. -/
theorem smallBaseChangeComparisonIso_hom_hom {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    (smallBaseChangeComparisonIso B S hS f hf V).hom.hom.left ≫
        ((spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS Y).obj V)).1.hom =
      ((comparisonFunctor B S hS X).obj ((smallBaseChange B S hS f hf).obj V)).1.hom :=
  (smallBaseChange_isPullback B S hS f hf V).isoIsPullback_hom_snd _ _ _

/-- The square formed by small and spaces-étale base change and the comparison functors commutes
up to its canonical natural isomorphism. -/
@[stacks 03G2 "part (4), comparison square"]
noncomputable def smallBaseChange_comparison {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    smallBaseChange B S hS f hf ⋙ comparisonFunctor B S hS X ≅
      comparisonFunctor B S hS Y ⋙ (spacesBaseChange B S hS f).functor :=
  NatIso.ofComponents (smallBaseChangeComparisonIso B S hS f hf) (fun {V W} k => by
    have hp : ((comparisonFunctor B S hS Y ⋙ (spacesBaseChange B S hS f).functor).map
          k).hom.left ≫
          (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj W) =
        (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V) ≫
          (SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map k) :=
      (spacesBaseChange B S hS f).projection.naturality ((comparisonFunctor B S hS Y).map k)
    have hn : ((smallBaseChange B S hS f hf ⋙ comparisonFunctor B S hS X).map k).hom.left ≫
          (smallBaseChange_projection B S hS f hf).app W =
        (smallBaseChange_projection B S hS f hf).app V ≫
          (SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map k) :=
      (smallBaseChange_projection B S hS f hf).naturality k
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
    refine ((spacesBaseChange B S hS f).isPullback
      ((comparisonFunctor B S hS Y).obj W)).hom_ext ?_ ?_
    · rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
        Over.comp_left, Over.comp_left, Category.assoc,
        smallBaseChangeComparisonIso_hom_projection, hn, Category.assoc, hp, ← Category.assoc,
        smallBaseChangeComparisonIso_hom_projection]
    · have hA : ((smallBaseChange B S hS f hf ⋙ comparisonFunctor B S hS X).map k).hom.left ≫
            ((comparisonFunctor B S hS X).obj ((smallBaseChange B S hS f hf).obj W)).1.hom =
          ((comparisonFunctor B S hS X).obj ((smallBaseChange B S hS f hf).obj V)).1.hom :=
        Over.w _
      have hB : ((comparisonFunctor B S hS Y ⋙
              (spacesBaseChange B S hS f).functor).map k).hom.left ≫
            ((spacesBaseChange B S hS f).functor.obj
              ((comparisonFunctor B S hS Y).obj W)).1.hom =
          ((spacesBaseChange B S hS f).functor.obj
            ((comparisonFunctor B S hS Y).obj V)).1.hom :=
        Over.w _
      rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
        Over.comp_left, Over.comp_left, Category.assoc,
        smallBaseChangeComparisonIso_hom_hom, hA, Category.assoc, hB,
        smallBaseChangeComparisonIso_hom_hom])

/-- The comparison isomorphism `AlgebraicGeometry.Space.smallBaseChange_comparison` is compatible
with the cartesian projections to the original chart. -/
@[stacks 03G2 "part (4), comparison of cartesian projections"]
theorem smallBaseChange_comparison_projection {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    ((smallBaseChange_comparison B S hS f hf).hom.app V).hom.left ≫
        (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V) =
      (smallBaseChange_projection B S hS f hf).app V :=
  smallBaseChangeComparisonIso_hom_projection B S hS f hf V

/-- Base change of étale scheme charts is continuous. -/
theorem isContinuous_smallBaseChange {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    (smallBaseChange B S hS f hf).IsContinuous
      (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) := by
  have hcomp : (smallBaseChange B S hS f hf ⋙ comparisonFunctor B S hS X).IsContinuous
      (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS X) :=
    Functor.isContinuous_comp' (smallBaseChange_comparison B S hS f hf).symm
      (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)
      (SpacesEtale.topology B S hS X)
  refine ⟨fun G => ?_⟩
  have e := (sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))).mapIso
    (((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S hS X.1)
      (SpacesEtale.topology B S hS X)).objObjPreimageIso G)
  refine (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_of_iso_iff (J := SmallEtale.topology B S hS Y.1)
      (Functor.isoWhiskerLeft (smallBaseChange B S hS f hf).op e)).mp ?_)
  exact (smallBaseChange B S hS f hf ⋙ comparisonFunctor B S hS X).op_comp_isSheaf
    (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS X) _

/-- Direct-image comparison of the small and spaces-étale cartesian square, obtained by
applying sheaf pushforward to the canonical isomorphism of sites
`AlgebraicGeometry.Space.smallBaseChange_comparison`. -/
noncomputable def smallBaseChange_pushforward_comparison {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)) ⋙
      (smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) ≅
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⋙
      (comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) :=
  letI := isContinuous_smallBaseChange B S hS f hf
  letI := Functor.isContinuous_comp (smallBaseChange B S hS f hf) (comparisonFunctor B S hS X)
    (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X)
  letI := Functor.isContinuous_comp (comparisonFunctor B S hS Y)
    (spacesBaseChange B S hS f).functor (SmallEtale.topology B S hS Y.1)
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
  Functor.sheafPushforwardContinuousComp (smallBaseChange B S hS f hf)
      (comparisonFunctor B S hS X) (Type (u + 1)) (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) ≪≫
    Functor.sheafPushforwardContinuousIso (smallBaseChange_comparison B S hS f hf)
      (Type (u + 1)) (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS X) ≪≫
    (Functor.sheafPushforwardContinuousComp (comparisonFunctor B S hS Y)
      (spacesBaseChange B S hS f).functor (Type (u + 1)) (SmallEtale.topology B S hS Y.1)
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).symm

/-- Base change of étale scheme charts is a morphism of small étale sites. -/
@[stacks 03G2 "part (4), small-site morphism"]
theorem smallBaseChange_isMorphismOfSites {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    _root_.IsMorphismOfSites.{u + 1} (smallBaseChange B S hS f hf)
      (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) :=
  let := isContinuous_smallBaseChange B S hS f hf
  { toIsContinuous := isContinuous_smallBaseChange B S hS f hf
    hasExactLeftAdjoint :=
      ⟨(smallToposMorphism B S hS f).inverseImage,
        ⟨(smallToposMorphism B S hS f).adj.ofNatIsoRight
          (((Functor.whiskeringLeft _ _ _).obj
            ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type (u + 1))
              (SmallEtale.topology B S hS X.1)
              (SpacesEtale.topology B S hS X))).preimageIso
            (smallToposMorphism_comparison B S hS f ≪≫
              (smallBaseChange_pushforward_comparison B S hS f hf).symm))⟩,
        (smallToposMorphism B S hS f).preservesFiniteLimits⟩ }

/-- The direct image of `AlgebraicGeometry.Space.smallToposMorphism` is isomorphic to the direct
image along the morphism of small étale sites given by base change on scheme charts. -/
@[stacks 03G2 "part (4), induced morphism of topoi"]
noncomputable def smallBaseChange_topos {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
    (smallToposMorphism B S hS f).pushforward ≅
      (smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) :=
  letI := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
  ((Functor.whiskeringLeft _ _ _).obj
    ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X))).preimageIso
    (smallToposMorphism_comparison B S hS f ≪≫
      (smallBaseChange_pushforward_comparison B S hS f hf).symm)

/-- The isomorphism `AlgebraicGeometry.Space.smallBaseChange_topos`, composed with the comparison
`AlgebraicGeometry.Space.smallBaseChange_pushforward_comparison`, is
`AlgebraicGeometry.Space.smallToposMorphism_comparison`. -/
@[stacks 03G2 "part (4), canonical topos comparison coherence"]
theorem smallBaseChange_topos_comparison {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (F : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
    (smallBaseChange_topos B S hS f hf).hom.app
        (((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).obj F) ≫
      (smallBaseChange_pushforward_comparison B S hS f hf).hom.app F =
      (smallToposMorphism_comparison B S hS f).hom.app F := by
  dsimp only [smallBaseChange_topos]
  rw [Functor.preimageIso_whiskeringLeft_hom_app]
  simp

/-! ### Coherence of the composition isomorphisms -/

/-- The small-site composition isomorphism
`AlgebraicGeometry.Space.smallToposMorphism_comp` is precisely the transport of the cartesian
composition on the spaces-étale site through the comparison equivalences, on every sheaf. -/
@[stacks 03G2 "part (3), canonical composition coherence"]
theorem smallToposMorphism_comp_comparison {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (F : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))) :
    (smallToposMorphism B S hS g).pushforward.map
        ((smallToposMorphism_comparison B S hS f).hom.app F) ≫
      (smallToposMorphism_comparison B S hS g).hom.app
        (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj F) ≫
      ((comparisonFunctor B S hS Z).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z)).map
          ((spacesBaseChange_pushforward_comp B S hS f g).hom.app F) =
    (smallToposMorphism_comp B S hS f g).hom.app
        (((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).obj F) ≫
      (smallToposMorphism_comparison B S hS (f ≫ g)).hom.app F :=
  MorphismOfTopoi.transport_comp_pushforward_comparison
    (spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi
    (spacesBaseChange_isMorphismOfSites B S hS g).morphismOfTopoi
    (spacesBaseChange_isMorphismOfSites B S hS (f ≫ g)).morphismOfTopoi
    (spacesBaseChange_pushforward_comp B S hS f g)
    (smallEtaleToposEquiv B S hS X) (smallEtaleToposEquiv B S hS Y)
    (smallEtaleToposEquiv B S hS Z) F

/-- The inverse-image composition isomorphism
`AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage` is the adjoint mate of the
direct-image composition isomorphism `AlgebraicGeometry.Space.smallToposMorphism_comp`. -/
@[stacks 03G2 "part (3), composition mate coherence"]
theorem smallToposMorphism_comp_mate {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf (SmallEtale.topology B S hS Z.1) (Type (u + 1)))
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
    (h : ((MorphismOfTopoi.comp (smallToposMorphism B S hS g)
      (smallToposMorphism B S hS f)).inverseImage).obj F ⟶ G) :
    (smallToposMorphism B S hS (f ≫ g)).adj.homEquiv F G
        ((smallToposMorphism_comp_inverseImage B S hS f g).hom.app F ≫ h) =
      (MorphismOfTopoi.comp (smallToposMorphism B S hS g)
          (smallToposMorphism B S hS f)).adj.homEquiv F G h ≫
        (smallToposMorphism_comp B S hS f g).hom.app G :=
  (Adjunction.homEquiv_leftAdjointUniq_hom_app_comp _ _ h).trans
    (Adjunction.homEquiv_ofNatIsoRight_apply _ _ h)

end AlgebraicGeometry.Space

end
