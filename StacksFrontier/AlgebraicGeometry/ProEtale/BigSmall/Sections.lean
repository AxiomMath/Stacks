module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Limits
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallProjection
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallToBigTopos

/-!
# Sections of a pulled-back sheaf on the big pro-étale site

For a scheme `S` in a chosen big pro-étale site and a morphism `f : T ⟶ S`, the value at `T` of
the inverse image along the projection from the big pro-étale topos over `S` is the set of global
sections of the inverse image along the small pro-étale morphism induced by `f`.

## Main definitions

* `AlgebraicGeometry.ProEtale.smallProetale_inverseImageSectionsIso`: the global sections of the
  restriction to `T` of a sheaf on the big pro-étale site over `S` are its value at `f : T ⟶ S`.
* `AlgebraicGeometry.ProEtale.smallProetaleInverseImageFactorizationIso`: the inverse image along
  the small pro-étale morphism induced by `f` is the inverse image along the projection followed
  by the inverse image along the inclusion of the small site of `T`.
* `AlgebraicGeometry.ProEtale.bigProetaleInverseImageSectionsIso`: the value at `f` of the inverse
  image along the projection is the set of global sections of the inverse image along the small
  pro-étale morphism induced by `f`, naturally in the sheaf on the small pro-étale site of `S`.

## References

* [Stacks Project, Tag 0F65](https://stacks.math.columbia.edu/tag/0F65)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

/-- Restricting a big pro-étale sheaf to `T` and taking sections is evaluation
at the object `T ⟶ S`. -/
public noncomputable def smallProetale_inverseImageSectionsIso :
    (smallProetaleToBigProetaleMorphism B T S f).inverseImage ⋙
      Sheaf.Γ (SmallProetale.topology B T.obj T.property) (Type (u + 1)) ≅
    (sheafSections (BigProetaleOver.topology B S.obj S.property)
      (Type (u + 1))).obj (Opposite.op (Over.mk f)) := by
  let I := smallProetaleToBigProetaleMorphism B T S f
  let F := smallProetaleToBigProetaleFunctor B T S f
  let SiteT := SmallProetale B T.obj T.property
  let U : SiteT := smallIdentity B T.obj T.property
  let hU : IsTerminal U := smallIdentity_isTerminal B T.obj T.property
  let i := SmallProetale.inclusion B T.obj T.property
  let J := SmallProetale.topology B T.obj T.property
  let K := BigProetaleOver.topology B S.obj S.property
  let sectionsU := (sheafSections J (Type (u + 1))).obj (Opposite.op U)
  let sectionsf := (sheafSections K (Type (u + 1))).obj (Opposite.op (Over.mk f))
  have hiU : IsTerminal (i.obj U) := by
    change IsTerminal (Over.mk (𝟙 T))
    exact Over.mkIdTerminal
  have hFU : F.obj U ≅ Over.mk f := by
    change (Over.map f).obj (i.obj U) ≅ Over.mk f
    exact (Over.map f).mapIso (hiU.uniqueUpToIso Over.mkIdTerminal) ≪≫
      Over.isoMk (Iso.refl T)
  letI : F.IsContinuous J K :=
    smallProetaleToBigProetaleFunctor_isContinuous B T S f
  letI : F.IsCocontinuous J K :=
    smallProetaleToBigProetaleFunctor_isCocontinuous B T S f
  have hsections : I.inverseImage ⋙ sectionsU ≅ sectionsf := by
    have hEval : F.sheafPushforwardContinuous (Type (u + 1)) J K ⋙ sectionsU ≅
        sectionsf :=
      NatIso.ofComponents
        (fun G =>
          (eqToIso (by
            change ((F.sheafPushforwardContinuous (Type (u + 1)) J K).obj G).obj.obj
                (Opposite.op U) = G.obj.obj (Opposite.op (F.obj U))
            exact Functor.sheafPushforwardContinuous_obj_obj_obj F
              (Type (u + 1)) J K G (Opposite.op U))).trans
            (G.obj.mapIso hFU.symm.op))
        (by
          intro G G' α
          ext x
          dsimp [sectionsU, sectionsf, sheafSections]
          rw [Functor.sheafPushforwardContinuous_map_hom_app]
          let hobj := Functor.sheafPushforwardContinuous_obj_obj_obj F
            (Type (u + 1)) J K G (Opposite.op U)
          cases hobj
          exact congrArg (fun k => k x) (α.hom.naturality hFU.inv.op).symm)
    exact Functor.isoWhiskerRight
      (F.sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type (u + 1)) J K)
      sectionsU ≪≫ hEval
  exact Functor.isoWhiskerLeft I.inverseImage
      (Sheaf.ΓNatIsoSheafSections J (Type (u + 1)) hU) ≪≫ hsections

/-- The inverse image of the small morphism is the composite of the projection
and the inclusion morphisms. -/
public noncomputable def smallProetaleInverseImageFactorizationIso :
    (smallProetaleMorphism B T S f).inverseImage ≅
      (bigProetaleToSmallProetaleMorphism B S.obj S.property).inverseImage ⋙
        (smallProetaleToBigProetaleMorphism B T S f).inverseImage :=
  (Adjunction.leftAdjointUniq
    (((bigProetaleToSmallProetaleMorphism B S.obj S.property).comp
        (smallProetaleToBigProetaleMorphism B T S f)).adj.ofNatIsoRight
      (smallProetaleMorphismInclusionFactorizationIso B T S f).symm)
    (smallProetaleMorphism B T S f).adj).symm

/-- The value of `π_S⁻¹ F` at `f : T ⟶ S` is the space of global sections of
`f_small⁻¹ F` on the small pro-étale site of `T`, naturally in `F`. -/
@[stacks 0F65 "pullback_value"]
public noncomputable def bigProetaleInverseImageSectionsIso :
    (bigProetaleToSmallProetaleMorphism B S.obj S.property).inverseImage ⋙
      (sheafSections (BigProetaleOver.topology B S.obj S.property)
        (Type (u + 1))).obj (Opposite.op (Over.mk f)) ≅
    (smallProetaleMorphism B T S f).inverseImage ⋙
      Sheaf.Γ (SmallProetale.topology B T.obj T.property) (Type (u + 1)) :=
  Functor.isoWhiskerLeft (bigProetaleToSmallProetaleMorphism B S.obj S.property).inverseImage
      (smallProetale_inverseImageSectionsIso B T S f).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (smallProetaleInverseImageFactorizationIso B T S f).symm
      (Sheaf.Γ (SmallProetale.topology B T.obj T.property) (Type (u + 1)))

end AlgebraicGeometry.ProEtale

end
