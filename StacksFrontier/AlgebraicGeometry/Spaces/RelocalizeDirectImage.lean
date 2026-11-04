module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeSpacesEtaleRan

/-!
# Direct images of sheaves on algebraic spaces under relocalization

Let `g : T ⟶ S` be a morphism of a big fppf site and `f : X ⟶ Y` a morphism of algebraic spaces
over `T`, with lower-shriek extension `Λ f : Λ X ⟶ Λ Y` over `S`. Through the equivalences of
small étale sites `e_X`, `e_Y`, the direct image along `Λ f` of sheaves of sets is the direct
image along `f`: `e_Y^* ∘ (Λ f)_* ≅ f_* ∘ e_X^*`. No representability of `f` is needed; the direct
image is the one of Stacks 03G2 through the spaces-étale sites.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeSheafRestriction`: restriction of sheaves of sets along
  `e_X`.
* `AlgebraicGeometry.Space.relocalizeDirectImageRanIso`: the comparison of direct images, in the
  right Kan extension form `AlgebraicGeometry.Space.smallEtaleDirectImageRan`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS)

/-- Restriction of sheaves of sets on the small étale site of `Λ X` along the equivalence of
small étale sites `e_X`. -/
abbrev relocalizeSheafRestriction (X : AlgebraicSpaces B T hT) :
    Sheaf (SmallEtale.topology B S hS (relocalizeSpace B hT hS g X).1) (Type u) ⥤
      Sheaf (SmallEtale.topology B T hT X.1) (Type u) :=
  (SmallEtale.relocalize B hT hS g X.1 X.2).functor.sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B T hT X.1) (SmallEtale.topology B S hS _)

variable {X Y : AlgebraicSpaces B T hT} (f : X ⟶ Y)

/-- The base change along `Λ f` of the chart of `Λ Y` attached to a relocalized chart of `Y` is
`Λ` of the base change along `f` of the chart. -/
def relocalizeChartBaseChangeIso :
    (SmallEtale.relocalize B hT hS g Y.1 Y.2).functor ⋙
        comparisonFunctor B S hS (relocalizeSpace B hT hS g Y) ⋙
          (spacesBaseChange B S hS (relocalizeHom B hT hS g f)).functor ≅
      comparisonFunctor B T hT Y ⋙ (spacesBaseChange B T hT f).functor ⋙
        relocalizeSpacesEtale B hT hS g X :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (relocalizeComparisonIso B hT hS g Y) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (relocalizeSpacesEtaleBaseChangeIso B hT hS g f).symm

/-- The comparison of direct images on underlying presheaves, for one sheaf of sets. -/
def relocalizeDirectImageRanPresheafIso
    (G : Sheaf (SmallEtale.topology B S hS (relocalizeSpace B hT hS g X).1) (Type u)) :
    ((smallEtaleDirectImageRan B S hS (relocalizeHom B hT hS g f) ⋙
        relocalizeSheafRestriction B hT hS g Y).obj G).obj ≅
      ((relocalizeSheafRestriction B hT hS g X ⋙ smallEtaleDirectImageRan B T hT f).obj G).obj :=
  Functor.isoWhiskerRight (NatIso.op (relocalizeChartBaseChangeIso B hT hS g f)).symm
      ((comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ran.obj G.obj) ≪≫
    Functor.isoWhiskerLeft
      ((comparisonFunctor B T hT Y).op ⋙ (spacesBaseChange B T hT f).functor.op)
      (relocalizeRanIso B hT hS g X G.obj)

/-- **Direct images of sheaves of sets commute with relocalization**:
`e_Y^* ∘ (Λ f)_* ≅ f_* ∘ e_X^*`, in the right Kan extension form of the direct image, for an
arbitrary morphism `f` of algebraic spaces. -/
def relocalizeDirectImageRanIso :
    smallEtaleDirectImageRan B S hS (relocalizeHom B hT hS g f) ⋙
        relocalizeSheafRestriction B hT hS g Y ≅
      relocalizeSheafRestriction B hT hS g X ⋙ smallEtaleDirectImageRan B T hT f :=
  NatIso.ofComponents
    (fun G => (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (relocalizeDirectImageRanPresheafIso B hT hS g f G))
    (fun {G G'} φ => (fullyFaithfulSheafToPresheaf _ _).map_injective (by
      refine NatTrans.ext (funext fun V => ?_)
      have h := NatTrans.congr_app (relocalizeRanIso_hom_naturality B hT hS g X φ.hom)
        (op ((spacesBaseChange B T hT f).functor.obj ((comparisonFunctor B T hT Y).obj V.unop)))
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
      have key : ((comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ran.map φ.hom).app
            (op ((spacesBaseChange B S hS (relocalizeHom B hT hS g f)).functor.obj
              ((comparisonFunctor B S hS (relocalizeSpace B hT hS g Y)).obj
                ((SmallEtale.relocalize B hT hS g Y.1 Y.2).functor.obj V.unop)))) ≫
          ((comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ran.obj G'.obj).map
            ((NatIso.op (relocalizeChartBaseChangeIso B hT hS g f)).symm.hom.app V) ≫
          (relocalizeRanIso B hT hS g X G'.obj).hom.app
            (op ((spacesBaseChange B T hT f).functor.obj
              ((comparisonFunctor B T hT Y).obj V.unop))) =
        (((comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ran.obj G.obj).map
            ((NatIso.op (relocalizeChartBaseChangeIso B hT hS g f)).symm.hom.app V) ≫
          (relocalizeRanIso B hT hS g X G.obj).hom.app
            (op ((spacesBaseChange B T hT f).functor.obj
              ((comparisonFunctor B T hT Y).obj V.unop)))) ≫
          ((comparisonFunctor B T hT X).op.ran.map (Functor.whiskerLeft
            (SmallEtale.relocalize B hT hS g X.1 X.2).functor.op φ.hom)).app
            (op ((spacesBaseChange B T hT f).functor.obj
              ((comparisonFunctor B T hT Y).obj V.unop))) := by
        rw [← NatTrans.naturality_assoc, Category.assoc]
        exact congrArg (_ ≫ ·) h
      exact key))

end AlgebraicGeometry.Space

end
