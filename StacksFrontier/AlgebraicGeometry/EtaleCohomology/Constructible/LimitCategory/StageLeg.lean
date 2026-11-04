module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Coherence
public import StacksFrontier.CategoryTheory.Adjunction.UnitCharacterizedTransport

/-!
# The leg of sections along a composite of inverse images

For morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : X ⟶ Z` of a big étale site with `f ≫ g = h`
and a sheaf `G` on the small étale site of `Z`, the *leg* is the map of sheaves on `Y`

`g⁻¹G ⟶ f_* h⁻¹G`,

the unit of `f⁻¹ ⊣ f_*` at `g⁻¹G` followed by `f_*` of the comparison `f⁻¹g⁻¹G ≅ h⁻¹G`. On
sections over an étale `V ⟶ Y` it carries a section of `g⁻¹G` over `V` to a section of `h⁻¹G` over
`V ×_Y X`. When `X` is the limit of an inverse system and `Y`, `Z` are two of its stages, these are
the maps whose colimit is the degree zero case of Stacks 09YQ.

The leg is characterized by a unit equation, `η^g ≫ g_*(leg) = η^h ≫ c`, where `c : h_* ≅ g_* f_*`
is the comparison of direct images. This is what makes it comparable with legs built on other
presentations of the small étale site, through
`CategoryTheory.Adjunction.unitCharacterized_transport`.

## Main definitions

* `AlgebraicGeometry.smallEtalePushforwardCompHom` — the comparison `h_* ⟶ f_* ⋙ g_*` of direct
  images along a named composite.
* `AlgebraicGeometry.smallEtaleStageLeg` — the leg.

## Main results

* `AlgebraicGeometry.unit_comp_map_smallEtaleStageLeg` — its characterizing unit equation.
* `AlgebraicGeometry.smallEtaleStageLeg_naturality` — its naturality in the sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- Direct image of sheaves along a morphism of a big étale site. -/
public abbrev smallEtaleSheafPushforward {S T : B.Scheme} (f : T ⟶ S) :
    Sheaf (SmallEtale.topology B T.obj T.property) A ⥤
      Sheaf (SmallEtale.topology B S.obj S.property) A :=
  (smallEtaleBaseChange B f).sheafPushforwardContinuous A
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)

/-- The inverse image/direct image adjunction along a morphism of a big étale site. -/
public abbrev smallEtaleSheafAdjunction {S T : B.Scheme} (f : T ⟶ S) :
    smallEtaleSheafPullback B A f ⊣ smallEtaleSheafPushforward B A f :=
  (smallEtaleBaseChange B f).sheafAdjunctionContinuous A
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)

/-- **The comparison of direct images along a named composite.** For `f ≫ g = h`, direct image
along `h` is direct image along `f` followed by direct image along `g`, through the comparison
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso` of base changes. -/
public def smallEtalePushforwardCompHom {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e : f ≫ g = h) :
    smallEtaleSheafPushforward B A h ⟶
      smallEtaleSheafPushforward B A f ⋙ smallEtaleSheafPushforward B A g :=
  (Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChange_factoredCompIso B X Y Z f g h e)
    A _ _ _).inv

/-- The comparison of direct images along a named composite is an isomorphism. -/
public instance isIso_smallEtalePushforwardCompHom_app {X Y Z : B.Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : X ⟶ Z) (e : f ≫ g = h)
    (K : Sheaf (SmallEtale.topology B X.obj X.property) A) :
    IsIso ((smallEtalePushforwardCompHom B A f g h e).app K) := by
  unfold smallEtalePushforwardCompHom
  infer_instance

/-- **The leg along a named composite.** For `f ≫ g = h` and a sheaf `G` on `Z`, the unit of
`f⁻¹ ⊣ f_*` at `g⁻¹G` followed by `f_*` of the comparison `f⁻¹g⁻¹G ≅ h⁻¹G`. -/
public def smallEtaleStageLeg {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e : f ≫ g = h) (G : Sheaf (SmallEtale.topology B Z.obj Z.property) A) :
    (smallEtaleSheafPullback B A g).obj G ⟶
      (smallEtaleSheafPushforward B A f).obj ((smallEtaleSheafPullback B A h).obj G) :=
  (smallEtaleSheafAdjunction B A f).unit.app _ ≫
    (smallEtaleSheafPushforward B A f).map ((smallEtaleSheafPullbackCompIso' B A f g h e).hom.app G)

/-- **The unit equation characterizing the leg.** -/
public theorem unit_comp_map_smallEtaleStageLeg {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) (G : Sheaf (SmallEtale.topology B Z.obj Z.property) A) :
    (smallEtaleSheafAdjunction B A g).unit.app G ≫
        (smallEtaleSheafPushforward B A g).map (smallEtaleStageLeg B A f g h e G) =
      (smallEtaleSheafAdjunction B A h).unit.app G ≫
        (smallEtalePushforwardCompHom B A f g h e).app ((smallEtaleSheafPullback B A h).obj G) := by
  simp only [smallEtaleStageLeg, smallEtalePushforwardCompHom, smallEtaleSheafPullbackCompIso'_eq]
  exact Adjunction.unit_comp_map_leftAdjointCompIso_hom _ _ _ _ G

/-- The leg is natural in the sheaf. -/
public theorem smallEtaleStageLeg_naturality {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) {G G' : Sheaf (SmallEtale.topology B Z.obj Z.property) A}
    (a : G ⟶ G') :
    (smallEtaleSheafPullback B A g).map a ≫ smallEtaleStageLeg B A f g h e G' =
      smallEtaleStageLeg B A f g h e G ≫
        (smallEtaleSheafPushforward B A f).map ((smallEtaleSheafPullback B A h).map a) := by
  simp only [smallEtaleStageLeg, Category.assoc]
  rw [← (smallEtaleSheafAdjunction B A f).unit_naturality_assoc, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 2
  exact (smallEtaleSheafPullbackCompIso' B A f g h e).hom.naturality a

end AlgebraicGeometry
