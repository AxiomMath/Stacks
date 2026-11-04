module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.BaseChangeFull

/-!
# The glued algebraic space of a functor on the points of `T`, read on products of points

Let `G` be a functor over the site from the points of an algebraic space `T` to the families of
algebraic spaces with cartesian squares, as in Stacks 0E93, and let `X` be the algebraic space
glued from it (`AlgebraicGeometry.SpacesOverSpace.glueSpace`), with its maps `s_a : Z_a ⟶ X`
from the families `Z_a` of `G` at the points `a` of `T`. This file proves that the family of `G`
at the product point `a ×_T b` of two points is the fibre product `Z_a ×_X Z_b`, and that the
family at the atlas of `T` covers `X` étale (Stacks 041F). These are the shapes in which the
quasi-coherent module of Stacks 0E94 is descended along `Z_{a₀} ⟶ X`.

## Main definitions

* `AlgebraicGeometry.PolarizedOverSpace.prodPointLift`: the morphism into a product point given
  by two morphisms of points.

## Main results

* `AlgebraicGeometry.PolarizedOverSpace.isPullback_famMap_prodPoint`: `Z_{a ×_T b} = Z_a ×_X Z_b`.
* `AlgebraicGeometry.PolarizedOverSpace.isEtaleCovering_famToGlue_atlasPoint`: the family at the
  atlas of `T` is an étale covering of `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor schemeSpace
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat
  MorphismProperty

variable {B : BigFppfSite.{u}} {T : AlgebraicSpaces B integerBase (hZ B)}

section Lift

variable {x a b : (Points T).obj} (α : x ⟶ a) (β : x ⟶ b)

/-- For morphisms of points `α : x ⟶ a` and `β : x ⟶ b`, the composites `U_x ⟶ U_a ⟶ T` and
`U_x ⟶ U_b ⟶ T` agree. -/
theorem prodPointLift_condition :
    yoneda.map α.base ≫ (SpacesOverSpace.pointMap a).hom =
      yoneda.map β.base ≫ (SpacesOverSpace.pointMap b).hom :=
  (SpacesOverSpace.yoneda_map_comp_pointMap_hom α).trans
    (SpacesOverSpace.yoneda_map_comp_pointMap_hom β).symm

/-- The morphism of schemes into `U_a ×_T U_b` given by two morphisms of points. -/
def prodPointLiftBase : x.base ⟶ prodScheme a b :=
  (relativelyRepresentable_pointMap a).lift' α.base β.base (prodPointLift_condition α β)

/-- The first projection of `prodPointLiftBase α β` is the base of `α`. -/
theorem prodPointLiftBase_fst : prodPointLiftBase α β ≫ prodFst a b = α.base :=
  (relativelyRepresentable_pointMap a).lift'_fst _ _ _

/-- The second projection of `prodPointLiftBase α β` is the base of `β`. -/
theorem prodPointLiftBase_snd : prodPointLiftBase α β ≫ prodSnd a b = β.base :=
  (relativelyRepresentable_pointMap a).lift'_snd _ _ _

/-- The point `x` is the pullback of the product point `a ×_T b` along `prodPointLiftBase α β`. -/
theorem prodPointLift_fiber :
    x.fiber.as = T.obj.map (prodPointLiftBase α β).op (prodPoint a b).fiber.as := by
  refine Eq.trans ?_ (yonedaEquiv_comp_pointMap (prodPoint a b) (prodPointLiftBase α β)
    (c := (SpacesOverSpace.pointMap x).hom) ?_)
  · exact (Equiv.apply_symm_apply yonedaEquiv x.fiber.as).symm
  · rw [pointMap_pullPoint, ← Category.assoc, ← Functor.map_comp, prodPointLiftBase_snd]
    exact SpacesOverSpace.yoneda_map_comp_pointMap_hom β

/-- **The morphism into the product point `a ×_T b` given by two morphisms of points.** -/
def prodPointLift : x ⟶ prodPoint a b :=
  ⟨prodPointLiftBase α β, Discrete.eqToHom (prodPointLift_fiber α β)⟩

/-- The first projection of `prodPointLift α β` is `α`. -/
theorem prodPointLift_fst : prodPointLift α β ≫ prodPointFst a b = α :=
  SpacesOverSpace.hom_ext_base _ _ (prodPointLiftBase_fst α β)

/-- The second projection of `prodPointLift α β` is `β`. -/
theorem prodPointLift_snd : prodPointLift α β ≫ prodPointSnd a b = β :=
  SpacesOverSpace.hom_ext_base _ _ (prodPointLiftBase_snd α β)

end Lift

section Glue

variable {P : MorphismProperty (AlgebraicSpaces B integerBase (hZ B))}
  (G : Points T ⥤ᵇ BasedCategory.ofFunctor
    (SpacesOverSpace.cartesianProjection B integerBase (hZ B) P))

/-- **The family at the product point `a ×_T b` is the fibre product over the glued space of the
families at `a` and `b`.** -/
theorem isPullback_famMap_prodPoint (a b : (Points T).obj) :
    IsPullback (SpacesOverSpace.famMap G (prodPointFst a b))
      (SpacesOverSpace.famMap G (prodPointSnd a b)) (SpacesOverSpace.famToGlue G a)
      (SpacesOverSpace.famToGlue G b) := by
  have h₁ := SpacesOverSpace.isPullback_famMap G (prodPointFst a b)
  have big := h₁.paste_vert (isPullback_prod a b)
  have hs : SpacesOverSpace.famMap G (prodPointSnd a b) ≫ SpacesOverSpace.famHom G b =
      SpacesOverSpace.famHom G (prodPoint a b) ≫ yoneda.map (prodSnd a b) :=
    (SpacesOverSpace.isPullback_famMap G (prodPointSnd a b)).w
  have ha : SpacesOverSpace.famHom G a ≫ (SpacesOverSpace.pointMap a).hom =
      SpacesOverSpace.famToGlue G a ≫ SpacesOverSpace.glueToBase G :=
    (SpacesOverSpace.famToGlue_comp_glueToBase G a).symm
  rw [← hs, ha] at big
  refine IsPullback.of_bot big ?_ (SpacesOverSpace.isPullback_famToGlue G b).flip
  rw [SpacesOverSpace.famMap_comp_famToGlue, SpacesOverSpace.famMap_comp_famToGlue]

/-- **The family at the atlas of `T` is an étale covering of the glued space** (Stacks 041F). -/
theorem isEtaleCovering_famToGlue_atlasPoint :
    Space.IsEtaleCovering B integerBase (hZ B)
      (fun _ : Unit => (SpacesOverSpace.fam G (atlasPoint T)).left.obj)
      (fun _ => SpacesOverSpace.famToGlue G (atlasPoint T)) :=
  isEtaleCovering_fst_of_isPullback (SpacesOverSpace.isPullback_famToGlue G (atlasPoint T)).flip
    (SpacesOverSpace.isAlgebraicSpace_glue G) (isEtaleCovering_atlasPoint T)

end Glue

end AlgebraicGeometry.PolarizedOverSpace

end
