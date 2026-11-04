module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.TargetSitePoint
public import StacksFrontier.CategoryTheory.Sites.Point.OfToposPointGerm

/-!
# The stalk ring map on underlying sets is the stalk of the structure map

Let `(f, f♯) : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi, let `Φ` be a point of
the source site and let `Ψ` be a point of the target site whose stalk functor on sheaves of sets
is identified with `f⁻¹` followed by the stalk functor of `Φ`.  The homomorphism
`𝒪'_Ψ ⟶ 𝒪_Φ` of stalk rings is built in two steps, through the isomorphism `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ`
and the stalk of the inverse-image form of the structure map.  This file reads the composite on
*underlying sets*: it is the identification of stalk functors followed by the stalk at `Φ` of
the inverse-image form of the structure map, which is the shape every element-level computation
with that homomorphism needs.

## Main results

* `Stacks.Sheaves.StalkPullback.commRingStalkEquiv_ringStalkComparison` — the isomorphism
  `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ` of stalk rings is, on underlying sets, the identification of stalk
  functors.
* `Stacks.Sheaves.StalkPullback.stalkRingMap_ringStalkComparison'` — the homomorphism
  `𝒪'_Ψ ⟶ 𝒪_Φ` of stalk rings is, on underlying sets, the identification of stalk functors
  followed by the stalk at `Φ` of `f⁻¹𝒪' ⟶ 𝒪`.
* `AlgebraicGeometry.RingedToposHom.targetStalkRingMap_ringStalkComparison` — the same statement
  at the reconstructed point `Ψ = AlgebraicGeometry.RingedToposHom.targetSitePoint`.

## References

* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

universe w v u v' u'

namespace Stacks.Sheaves.StalkPullback

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w}}
  [LocallySmall.{w} X.C] [LocallySmall.{w} Y.C]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y) (Φ : X.J.Point.{w}) (Ψ : Y.J.Point.{w})
  (e : Ψ.sheafFiber (A := Type w) ≅
    f.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type w))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The isomorphism `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ` of stalk rings is the identification of stalk functors
on underlying sets.**  Both sides are read through the comparison of the `CommRingCat`-valued
stalk of a presheaf of commutative rings with the stalk of its underlying sheaf of sets. -/
theorem commRingStalkEquiv_ringStalkComparison
    (x : (Ψ.sheafFiber (A := Type w)).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    commRingStalkEquiv f Φ Ψ e
        ((Stacks.commRingPresheafFiberIso Ψ Y.O.obj).ringCatIsoToRingEquiv
          (Stacks.Sheaves.StalkTransport.ringStalkComparison Ψ
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) x)) =
      (Stacks.commRingPresheafFiberIso Φ (inverseImageStructure f)).ringCatIsoToRingEquiv
        (Stacks.Sheaves.StalkTransport.ringStalkComparison Φ (inverseImageStructureRing f)
          (e.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) x)) := by
  rw [commRingStalkEquiv]
  refine Eq.trans (congrArg
    (fun z => (Stacks.commRingPresheafFiberIso Φ (inverseImageStructure f)).ringCatIsoToRingEquiv
      (Stacks.Sheaves.StalkInverseImage.stalkRingEquiv f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e z))
    ((Stacks.commRingPresheafFiberIso Ψ Y.O.obj).ringCatIsoToRingEquiv.symm_apply_apply
      (Stacks.Sheaves.StalkTransport.ringStalkComparison Ψ
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) x))) ?_
  exact congrArg (Stacks.commRingPresheafFiberIso Φ (inverseImageStructure f)).ringCatIsoToRingEquiv
    (Stacks.Sheaves.StalkInverseImage.stalkRingMap_ringStalkComparison f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e x)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The homomorphism `𝒪'_Ψ ⟶ 𝒪_Φ` of stalk rings, on underlying sets.**  It is the
identification of stalk functors on sheaves of sets followed by the stalk at `Φ` of the
inverse-image form `f⁻¹𝒪' ⟶ 𝒪` of the structure map.

This is the identification every element-level computation with the stalk homomorphism needs:
it turns a statement about `Stacks.Sheaves.StalkPullback.stalkRingMap` into a statement about
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage`, whose sections over a chart are
computable. -/
theorem stalkRingMap_ringStalkComparison'
    (x : (Ψ.sheafFiber (A := Type w)).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    stalkRingMap f Φ Ψ e
        ((Stacks.commRingPresheafFiberIso Ψ Y.O.obj).ringCatIsoToRingEquiv
          (Stacks.Sheaves.StalkTransport.ringStalkComparison Ψ
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) x)) =
      (Stacks.commRingPresheafFiberIso Φ X.O.obj).hom.hom
        (Stacks.Sheaves.StalkTransport.ringStalkComparison Φ
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          ((Φ.sheafFiber (A := Type w)).map
            ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage)
            (e.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) x))) :=
  (congrArg (fSharpStalk f Φ) (commRingStalkEquiv_ringStalkComparison f Φ Ψ e x)).trans
    (fSharpStalk_commRingPresheafFiberIso_ringStalkComparison f Φ
      (e.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) x))

end Stacks.Sheaves.StalkPullback

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [LocallySmall.{w} X.C] [LocallySmall.{w} Y.C]
  [EssentiallySmall.{w} Y.C] [HasSheafify Y.J (Type w)]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The homomorphism `𝒪'_Ψ ⟶ 𝒪_Φ` of stalk rings at the reconstructed point, on underlying
sets.**  It is the identification `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ` of stalk functors on sheaves of sets that
`AlgebraicGeometry.RingedToposHom.targetSitePointIso` provides, followed by the stalk at `Φ` of
the inverse-image form of the structure map of `f`. -/
theorem targetStalkRingMap_ringStalkComparison (f : RingedToposHom X Y) (Φ : X.J.Point.{w})
    (x : ((f.targetSitePoint Φ).sheafFiber (A := Type w)).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    f.targetStalkRingMap Φ
        ((Stacks.commRingPresheafFiberIso (f.targetSitePoint Φ) Y.O.obj).ringCatIsoToRingEquiv
          (Stacks.Sheaves.StalkTransport.ringStalkComparison (f.targetSitePoint Φ)
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) x)) =
      (Stacks.commRingPresheafFiberIso Φ X.O.obj).hom.hom
        (Stacks.Sheaves.StalkTransport.ringStalkComparison Φ
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          ((Φ.sheafFiber (A := Type w)).map
            ((sheafCompose X.J (forget RingCat.{w})).map
              f.toRingedToposModulesHom.fSharpInverseImage)
            ((f.targetSitePointIso Φ).hom.app
              (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) x))) :=
  Stacks.Sheaves.StalkPullback.stalkRingMap_ringStalkComparison'
    f.toRingedToposModulesHom Φ (f.targetSitePoint Φ) (f.targetSitePointIso Φ) x

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The identification `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ` of stalk functors, on a germ.**  A section `z` of a
sheaf of sets `F` on the target site over a chart `V` is named by a morphism of sheaves
`h_V^# ⟶ F`; the identification carries the germ of `z` at a point `y` of the reconstructed
target point lying over `V` to the image of `y` under `f⁻¹` followed by the stalk functor of `Φ`
applied to that naming morphism.

This is `CategoryTheory.PointOfTopos.sheafFiberIsoInverseImage_hom_app_toPresheafFiber_sheafHom`
at the point of the topos obtained by composing `Φ` with `f`, which is how
`AlgebraicGeometry.RingedToposHom.targetSitePointIso` is defined. -/
theorem targetSitePointIso_hom_app_toPresheafFiber (f : RingedToposHom X Y) (Φ : X.J.Point.{w})
    (F : Sheaf Y.J (Type w)) (V : Y.C) (y : (f.targetSitePoint Φ).fiber.obj V)
    (z : F.obj.obj (Opposite.op V)) :
    (f.targetSitePointIso Φ).hom.app F
        ((f.targetSitePoint Φ).toPresheafFiber V y F.obj z) =
      (f.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type w)).map
        ((presheafToSheaf Y.J (Type w)).map (shrinkYonedaEquiv.symm z) ≫
          (sheafificationAdjunction Y.J (Type w)).counit.app F) y :=
  (f.toposPointComp Φ).sheafFiberIsoInverseImage_hom_app_toPresheafFiber_sheafHom F V y z

end AlgebraicGeometry.RingedToposHom

end
