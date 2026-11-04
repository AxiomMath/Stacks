module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReduced

/-!
# Connectedness of the fibre over a field-valued point

This is a helper module of the proof of Stacks 0E0D. Its declarations are scoped to the
`AlgebraicGeometry.Space.ProperFlatStein` namespace and it records no tag.

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `p` be a
field-valued point of `Y`, defined over a field `k`. There are two ways to form the fibre of
`f` above `p`: the presheaf fibre product `X ×_Y Spec k` over the big fppf site of `S`, and the
fibre `AlgebraicGeometry.Space.fibreOverFieldValuedPoint`, formed over the big fppf site of
`Spec k` itself. The first is the lower-shriek extension of the second, so their point spaces
are homeomorphic and one is connected exactly when the other is.

## Main results

* `AlgebraicGeometry.Space.ProperFlatStein.fibreOverFieldValuedPointViewIso`: the lower-shriek
  extension of the fibre over a field-valued point is the presheaf fibre product of `f` with the
  morphism represented by the point.
* `AlgebraicGeometry.Space.ProperFlatStein.connectedPoints_fibreOverFieldValuedPoint_iff`: the
  fibre over a field-valued point has connected point space if and only if the presheaf fibre
  product does.

## Implementation notes

The presheaf fibre product `Q` comes with a morphism to the representable presheaf of `Spec k`,
so by the presheaf equivalence of Stacks 04SG (`AlgebraicGeometry.smallerBasePresheafEquivalence`)
it is the lower-shriek extension of a presheaf `F` over `Spec k`. By
`CategoryTheory.OverShriek.isPullback_relocalizeUnit` that presheaf is the fibre of the
restriction of `Q` above the tautological section, and pasting with the restriction of the
cartesian square of `Q` exhibits `F` as the fibre of the restriction of `f` above the restricted
section, which is the definition of the fibre over the point. The homeomorphism on points is
then Stacks 03BX for a change of base (`AlgebraicGeometry.Space.relocalizedPointsHomeomorph`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.ProperFlatStein

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The tautological section of the restriction along `g : T ⟶ S` of the representable
presheaf of `g`, followed by the restriction of the morphism represented by a section `v` of `Y`
over `g`, is the tautological section of the restriction of `Y` attached to `v`. -/
theorem restrictYonedaSelf_comp_relocalizeRestrict_map {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : Scheme.{u}} (hT : B.Contains T) (g : B.obj hT ⟶ B.obj hS)
    (v : Y.obj (op (Over.mk g))) :
    OverShriek.restrictYonedaSelf g ≫
        (OverShriek.relocalizeRestrict g).map (yonedaEquiv.symm v) =
      restrictedSection B S hS Y hT g v := by
  ext W h
  exact congrArg (fun t => Y.map (Quiver.Hom.op t) v) (Over.OverMorphism.ext rfl)

/-- The lower-shriek extension of the fibre of `f` over a field-valued point `p` of `Y`, formed
over the big fppf site of the field of `p`, is the presheaf fibre product of `f` with the
morphism represented by `p`. -/
noncomputable def fibreOverFieldValuedPointViewIso {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    (OverShriek.relocalizePresheafFunctor (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS)).obj
        (fibreOverFieldValuedPoint B S hS f p) ≅
      pullback f (yonedaEquiv.symm p.value) := by
  let g : B.obj p.contained ⟶ B.obj hS := ⟨p.toBase⟩
  let a : yoneda.obj (Over.mk g) ⟶ Y := yonedaEquiv.symm p.value
  let π : pullback f a ⟶ yoneda.obj (Over.mk g) := pullback.snd f a
  -- The fibre product is the lower-shriek extension of a presheaf `F` over the field.
  let E := smallerBasePresheafEquivalence B (Spec (.of p.carrier)) S p.contained hS g
  let Qπ : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := Over.mk π
  let F := E.inverse.obj Qπ
  let c := E.counitIso.app Qπ
  let e : (OverShriek.relocalizePresheafFunctor g).obj F ≅ pullback f a :=
    ((smallerBasePresheafForgetIso B (Spec (.of p.carrier)) S p.contained hS g).app F).symm ≪≫
      (Over.forget (yoneda.obj (Over.mk g))).mapIso c
  have he : e.hom ≫ π = OverShriek.viewStructureMap g F := by
    ext W s
    have hc := congrArg (fun t => t.app W
        (((smallerBasePresheafForgetIso B (Spec (.of p.carrier)) S p.contained hS g).inv.app
          F).app W s)) c.hom.w
    refine hc.trans ?_
    apply Over.OverMorphism.ext
    rfl
  -- `F` is the fibre of the restriction of the fibre product above the tautological section.
  letI : PreservesLimitsOfShape WalkingCospan
      (OverShriek.relocalizeRestrict g :
        ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤
          ((BigFppfOver B (Spec (.of p.carrier)) p.contained)ᵒᵖ ⥤ Type u)) :=
    ((OverShriek.relocalizeAdjunction g).rightAdjoint_preservesLimits).preservesLimitsOfShape
  have h₀ := OverShriek.isPullback_relocalizeUnit g F
  rw [← he, Functor.map_comp] at h₀
  have h₁ : IsPullback
      (OverShriek.relocalizeUnit g F ≫ (OverShriek.relocalizeRestrict g).map e.hom)
      (OverShriek.toYonedaMkId F) ((OverShriek.relocalizeRestrict g).map π)
      (OverShriek.restrictYonedaSelf g) :=
    h₀.of_iso (Iso.refl _) ((OverShriek.relocalizeRestrict g).mapIso e) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  have h₂ : IsPullback ((OverShriek.relocalizeRestrict g).map (pullback.fst f a))
      ((OverShriek.relocalizeRestrict g).map π) ((OverShriek.relocalizeRestrict g).map f)
      ((OverShriek.relocalizeRestrict g).map a) :=
    (IsPullback.of_hasPullback f a).map (OverShriek.relocalizeRestrict g)
  have h₃ := h₁.paste_horiz h₂
  rw [restrictYonedaSelf_comp_relocalizeRestrict_map B S hS p.contained g p.value] at h₃
  exact (OverShriek.relocalizePresheafFunctor g).mapIso h₃.isoPullback.symm ≪≫ e

/-- **Connectedness of the fibre over a field-valued point.** Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` and let `p` be a field-valued point of `Y` over a field `k`. The fibre
of `f` over `p`, an algebraic space over `Spec k`, has connected point space if and only if the
presheaf fibre product of `f` with the morphism represented by `p`, over the big fppf site of
`S`, does: the latter is the lower-shriek extension of the former, and the point space does not
depend on the base (Stacks 03BX for a change of base). -/
theorem connectedPoints_fibreOverFieldValuedPoint_iff
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    ConnectedPoints B (Spec (.of p.carrier)) p.contained
        (fibreOverFieldValuedPoint B S hS f p) ↔
      ConnectedPullback B S hS f (yonedaEquiv.symm p.value) :=
  (relocalizedPointsHomeomorph B (Spec (.of p.carrier)) S p.contained hS ⟨p.toBase⟩
      (fibreOverFieldValuedPoint B S hS f p)
      (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f hX hY p)).connectedSpace_iff.trans
    (pointsHomeomorphOfIso B S hS (fibreOverFieldValuedPointViewIso B S hS f p)).connectedSpace_iff

end AlgebraicGeometry.Space.ProperFlatStein

end
