module

public import StacksFrontier.Deformation.Applications.TwoFibreProductInfRow
public import StacksFrontier.Deformation.Applications.TwoFibreProductSelfExact
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermFull.Keystone

/-!
# The six-term sequence of a 2-fibre product: the boundary quadruple and its class

Second of three parts of `StacksFrontier.Deformation.Applications.TwoFibreProductSixTermFull`.
It contains the conjugation relations the two outer legs satisfy, transported to the re-based
square-zero extension
(`Deformation.transportAut_comp_boundaryCompareFst`,
`Deformation.transportAut_comp_boundaryCompareSnd`), and the vanishing criterion for the class of
the quadruple the boundary map produces
(`Deformation.tangentClassAt_boundaryObject_eq_zero_iff`).

## References

* [Stacks Project, Tag 06L5](https://stacks.math.columbia.edu/tag/06L5)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

/-! ### The conjugation relations at the re-based square-zero extension -/

section CrossConj
open CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F]
  {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

attribute [local implicit_reducible] squareZeroCrossUnder

/-- Transporting a conjugation relation along `ψ` and `ψ'`: if `D` intertwines the pushforward
maps of `ψ` and `ψ'` and `A` is conjugate to `β` by `Dd`, then the transports of `A` and `β` are
conjugate by `D`. -/
private theorem transportAut_comp_of_conj {X : Type*} [Category X] (Φ : X ⥤ F) {y : X}
    {x : F} (Q : ChosenPushforwardsAt (Φ ⋙ pF) y) (P : ChosenPushforwardsAt pF x)
    {U V : Under (pF.obj x)} {U' V' : Under ((Φ ⋙ pF).obj y)} (ψ : U ⟶ V) (ψ' : U' ⟶ V')
    (A : Aut (P.obj U)) (β : Aut (Q.obj U'))
    {D : (P.obj V).1 ⟶ Φ.obj (Q.obj V').1} {Dd : (P.obj U).1 ⟶ Φ.obj (Q.obj U').1}
    (hD : P.map ψ ≫ D = Dd ≫ Φ.map (Q.map ψ')) (hl : pF.IsHomLift (𝟙 V.right) D)
    (hl' : pF.IsHomLift (𝟙 V.right) (Φ.map (Q.transportAut ψ' β).asIso.hom.val))
    (hc : A.asIso.hom.val ≫ Dd = Dd ≫ Φ.map β.asIso.hom.val) :
    (P.transportAut ψ A).asIso.hom.val ≫ D = D ≫ Φ.map (Q.transportAut ψ' β).asIso.hom.val := by
  refine conj_of_map P ψ (P.map_transportHom ψ A) hD hc ?_ ?_ ?_
  · exact (Φ.map_comp _ _).symm.trans
      ((congrArg Φ.map (Q.map_transportHom ψ' β)).trans (Φ.map_comp _ _))
  · have := (P.transportAut ψ A).asIso.hom.2
    infer_instance
  · infer_instance

/-- **The conjugation relation of the `ℋ`-leg, at the re-based square-zero extension.** If an
infinitesimal automorphism `A` of the chosen pushforward of `x₀ = f(y₀)` to the square-zero
extension read as an algebra under the base is conjugate, by the comparison `H₃` of Tag 07W6, to
the image under `f` of an automorphism `β` of the chosen pushforward of `y₀`, then the
transports of `A` and of `β` to the re-based extension are conjugate by the comparison `b'` of
the boundary map.

The transport of the comparison itself is `Deformation.map_cross_comp_boundaryCompareFst`, and
the transport of the conjugation is then `Deformation.conj_of_map`. -/
public theorem transportAut_comp_boundaryCompareFst (f : H ⥤ F) {y₀ : H}
    (QH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PF : ChosenPushforwardsAt pF (f.obj y₀))
    (hcofF : IsCofiberedInGroupoids pF) (M : FGModuleCat.{max v w} k)
    (H₃ : (PF.obj (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M)).1 ≅
      f.obj (QH.obj (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M)).1)
    (hi₃ : PF.inclusion (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M) ≫ H₃.hom =
      f.map (QH.inclusion (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M)))
    (hl₃ : pF.IsHomLift (𝟙 (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M).right) H₃.hom)
    (A : Aut (PF.obj (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M)))
    (β : Aut (QH.obj (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M)))
    (hc : A.asIso.hom.val ≫ H₃.hom = H₃.hom ≫ f.map β.asIso.hom.val) :
    (PF.transportAut
            (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom A).asIso.hom.val ≫
        (boundaryCompareFst.{u, v, w} f QH PF hcofF M).hom =
      (boundaryCompareFst.{u, v, w} f QH PF hcofF M).hom ≫
        f.map (QH.transportAut
          (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom β).asIso.hom.val :=
  transportAut_comp_of_conj f QH PF
    (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom
    (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom A β
    (map_cross_comp_boundaryCompareFst.{u, v, w} f QH PF hcofF M H₃ hi₃ hl₃)
    (isHomLift_boundaryCompareFst.{u, v, w} f QH PF hcofF M).1
    (isHomLift_map_of_comp f _ _ (QH.transportAut
      (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom β).asIso.hom.2) hc

/-- **The transport of the comparison `c'` across the two normalizations of the square-zero
extension.** Tag 06JV (2)'s comparison `Hε` between the chosen pushforwards of `f(y₀)` and of
`g(z₀)`, followed by the comparison of the two normalizations on the `ℋ`-side and then by `c'`,
is the comparison of the two normalizations on the `𝒢`-side followed by the `𝒢`-leg's own `b'`.

This is the third of the three transports exactness at `Inf(ℱ)` needs. Both sides lie over the
coordinate arrow of the `𝒢`-side comparison — `Hε` lies over the transport along the equality of
the two bases of `w₀`, which is where `Deformation.eqToHom_comp_squareZeroCross` is used — and
the chosen inclusion of `g(z₀)` is strongly cocartesian, so it is enough that they agree after
precomposition with it: there both become the image under `g` of the chosen inclusion of `z₀`,
the left-hand side by the comparison square of `Hε` and the defining property of `c'`. -/
public theorem map_cross_comp_boundaryCompareSnd (f : H ⥤ F) (g : G ⥤ F)
    {w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
    (QG : ChosenPushforwardsAt (g ⋙ pF) w₀.y)
    (PF : ChosenPushforwardsAt pF (f.obj w₀.x)) (PF' : ChosenPushforwardsAt pF (g.obj w₀.y))
    (hcofF : IsCofiberedInGroupoids pF) (M : FGModuleCat.{max v w} k)
    (Hε : (PF'.obj (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M)).1 ≅
      (PF.obj (squareZeroUnder.{u, v, w} (f ⋙ pF) w₀.x M)).1)
    (hiε : PF'.inclusion (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M) ≫ Hε.hom =
      w₀.iso.inv ≫ PF.inclusion (squareZeroUnder.{u, v, w} (f ⋙ pF) w₀.x M))
    (hlε : pF.IsHomLift (𝟙 (squareZeroUnder.{u, v, w} (f ⋙ pF) w₀.x M).right) Hε.hom) :
    Hε.hom ≫ PF.map (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom ≫
        (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
          (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).hom =
      PF'.map (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom ≫
        (boundaryCompareFst.{u, v, w} g QG PF' hcofF M).hom := by
  have hr : (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M).right =
      (squareZeroUnder.{u, v, w} (f ⋙ pF) w₀.x M).right :=
    congrArg (fun A : ArtinianLocalAlgCat.{u, max v w, w} Λ k =>
      ((squareZeroAlgFunctor.{u, v, w} A).obj M).right) (w₀.hy.trans w₀.hx.symm)
  have hlε' : pF.IsHomLift (eqToHom hr) Hε.hom := by
    let := hlε
    refine IsHomLift.of_fac' pF _ Hε.hom
      (PF'.obj (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M)).2
      (PF.obj (squareZeroUnder.{u, v, w} (f ⋙ pF) w₀.x M)).2 ?_
    rw [IsHomLift.fac' pF (𝟙 (squareZeroUnder.{u, v, w} (f ⋙ pF) w₀.x M).right) Hε.hom]
    simp only [Category.id_comp, eqToHom_trans]
  have hbase : eqToHom hr ≫
      (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom.right =
      (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom.right :=
    eqToHom_comp_squareZeroCross.{u, v, w} M hr
  have hSc : pF.IsHomLift
      (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom.right
      (PF.map (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom ≫
        (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
          (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).hom) :=
    @IsHomLift.comp_lift_id_right' _ _ _ _ pF _ _ _ _ _ _ _
      (PF.map_isHomLift (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom)
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M) _
      (isHomLift_boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
        (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).1
  have hL0 : pF.IsHomLift
      (eqToHom hr ≫ (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom.right)
      (Hε.hom ≫ PF.map (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom ≫
        (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
          (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).hom) :=
    @IsHomLift.comp _ _ _ _ pF _ _ _ _ _ _ _ _ _ _ hlε' hSc
  have hL := hbase ▸ hL0
  have hR : pF.IsHomLift
      (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom.right
      (PF'.map (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom ≫
        (boundaryCompareFst.{u, v, w} g QG PF' hcofF M).hom) :=
    @IsHomLift.comp_lift_id_right' _ _ _ _ pF _ _ _ _ _ _ _
      (PF'.map_isHomLift (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom)
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M) _
      (isHomLift_boundaryCompareFst.{u, v, w} g QG PF' hcofF M).1
  refine @Functor.IsStronglyCocartesian.ext _ _ _ _ pF _ _ _ _
    (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M).hom
    (PF'.inclusion (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M))
    (PF'.inclusion_cocartesian (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M)) _ _
    (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom.right _ _ hL hR ?_
  have hc := inclusion_comp_boundaryCompareSnd_hom.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
    (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M
  have hb := inclusion_comp_boundaryCompareFst_hom.{u, v, w} g QG PF' hcofF M
  calc PF'.inclusion (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M) ≫
        Hε.hom ≫ PF.map (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom ≫
          (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
            (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).hom
      = (PF'.inclusion (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M) ≫ Hε.hom) ≫
          PF.map (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom ≫
            (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
              (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).hom :=
        (Category.assoc _ _ _).symm
    _ = (w₀.iso.inv ≫ PF.inclusion (squareZeroUnder.{u, v, w} (f ⋙ pF) w₀.x M)) ≫
          PF.map (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom ≫
            (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
              (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).hom :=
        congrArg (· ≫ _) hiε
    _ = w₀.iso.inv ≫ (PF.inclusion (squareZeroUnder.{u, v, w} (f ⋙ pF) w₀.x M) ≫
          PF.map (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom) ≫
            (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
              (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).hom := by
        rw [Category.assoc, Category.assoc]
    _ = w₀.iso.inv ≫ PF.inclusion (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M) ≫
            (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
              (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).hom :=
        congrArg (fun z => w₀.iso.inv ≫ z ≫ _)
          (PF.inclusion_map (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom)
    _ = w₀.iso.inv ≫ w₀.iso.hom ≫
          g.map (QG.inclusion (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M)) :=
        congrArg (fun z => w₀.iso.inv ≫ z) hc
    _ = g.map (QG.inclusion (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M)) := by
        rw [Iso.inv_hom_id_assoc]
    _ = PF'.inclusion (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M) ≫
          (boundaryCompareFst.{u, v, w} g QG PF' hcofF M).hom := hb.symm
    _ = (PF'.inclusion (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M) ≫
          PF'.map (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom) ≫
            (boundaryCompareFst.{u, v, w} g QG PF' hcofF M).hom :=
        congrArg (· ≫ _)
          (PF'.inclusion_map (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom).symm
    _ = PF'.inclusion (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M) ≫
          PF'.map (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom ≫
            (boundaryCompareFst.{u, v, w} g QG PF' hcofF M).hom := Category.assoc _ _ _

/-- **The conjugation relation of the `𝒢`-leg, at the re-based square-zero extension.** If an
infinitesimal automorphism `A` of the chosen pushforward of `x₀ = f(y₀)` to the square-zero
extension read as an algebra under the base is conjugate, by `Hε` followed by the comparison
`H₄` of Tag 07W6, to the image under `g` of an automorphism `γ` of the chosen pushforward of
`z₀`, then the transports of `A` and of `γ` to the re-based extension are conjugate by the
comparison `c'` of the boundary map.

The transport of the comparison is `Deformation.map_cross_comp_boundaryCompareSnd` composed with
`Deformation.map_cross_comp_boundaryCompareFst` for the second leg, and the transport of the
conjugation is then `Deformation.conj_of_map`. -/
public theorem transportAut_comp_boundaryCompareSnd (f : H ⥤ F) (g : G ⥤ F)
    {w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
    (QG : ChosenPushforwardsAt (g ⋙ pF) w₀.y)
    (PF : ChosenPushforwardsAt pF (f.obj w₀.x)) (PF' : ChosenPushforwardsAt pF (g.obj w₀.y))
    (hcofF : IsCofiberedInGroupoids pF) (M : FGModuleCat.{max v w} k)
    (Hε : (PF'.obj (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M)).1 ≅
      (PF.obj (squareZeroUnder.{u, v, w} (f ⋙ pF) w₀.x M)).1)
    (hiε : PF'.inclusion (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M) ≫ Hε.hom =
      w₀.iso.inv ≫ PF.inclusion (squareZeroUnder.{u, v, w} (f ⋙ pF) w₀.x M))
    (hlε : pF.IsHomLift (𝟙 (squareZeroUnder.{u, v, w} (f ⋙ pF) w₀.x M).right) Hε.hom)
    (H₄ : (PF'.obj (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M)).1 ≅
      g.obj (QG.obj (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M)).1)
    (hi₄ : PF'.inclusion (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M) ≫ H₄.hom =
      g.map (QG.inclusion (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M)))
    (hl₄ : pF.IsHomLift (𝟙 (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M).right) H₄.hom)
    (A : Aut (PF.obj (squareZeroUnder.{u, v, w} (f ⋙ pF) w₀.x M)))
    (γ : Aut (QG.obj (squareZeroUnder.{u, v, w} (g ⋙ pF) w₀.y M)))
    (hc : A.asIso.hom.val ≫ Hε.inv ≫ H₄.hom = (Hε.inv ≫ H₄.hom) ≫ g.map γ.asIso.hom.val) :
    (PF.transportAut
            (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom A).asIso.hom.val ≫
        (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
          (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).hom =
      (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
          (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).hom ≫
        g.map (QG.transportAut
          (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom γ).asIso.hom.val := by
  have hthird := map_cross_comp_boundaryCompareSnd.{u, v, w} f g QG PF PF' hcofF M Hε hiε hlε
  have hb := map_cross_comp_boundaryCompareFst.{u, v, w} g QG PF' hcofF M H₄ hi₄ hl₄
  have hD : PF.map (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom ≫
        (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
          (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).hom =
      (Hε.inv ≫ H₄.hom) ≫
        g.map (QG.map (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom) := by
    rw [Category.assoc, ← hb, ← hthird, Iso.inv_hom_id_assoc]
    rfl
  exact transportAut_comp_of_conj g QG PF
    (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom
    (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom A γ hD
    (isHomLift_boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
      (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).1
    (isHomLift_map_of_comp g _ _ (QG.transportAut
      (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom γ).asIso.hom.2) hc

end CrossConj

/-! ### The vanishing of the class of the quadruple the boundary map produces -/

section BoundaryZero
open CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F]

attribute [local implicit_reducible] squareZeroCrossUnder

/-- **The quadruple the boundary map produces is the trivial deformation exactly when the
automorphism it twists by satisfies the boundary square.** The class in `T𝒲` of
`δ(α) = (k[M], y'₀, z'₀, c' ∘ α ∘ b')` vanishes exactly when there are automorphisms `β` of
`y'₀` and `γ` of `z'₀` with

`f(β) ≫ b'⁻¹ ≫ c' = b'⁻¹ ≫ α ≫ c' ≫ g(γ)`.

The zero of `T𝒲` is the class of the chosen pushforward of `w₀`
(`Deformation.tangentClassAt_pushforward_eq_zero`), two classes agree exactly when the objects
are isomorphic in the fibre (`Deformation.tangentClassAt_eq_iff`), and an isomorphism of the
`2`-fibre product is a pair of isomorphisms of the components satisfying the comparison square
(`CategoryTheory.TwoFibreProductOver.isoMkVertical`). Reading that pair through the comparisons
`Deformation.crossCompareFst` and `Deformation.crossCompareSnd` of the components of the chosen
pushforward of `w₀` with the chosen pushforwards of `y₀` and of `z₀`, and eliminating the
comparison isomorphism carried by that pushforward with
`Deformation.boundaryCompare_comp_crossCompare_eq`, turns the comparison square into the
displayed one. This is the source's "the isomorphism `w'₀ → δ(α)` produces a pair
`(β, γ)`". -/
public theorem tangentClassAt_boundaryObject_eq_zero_iff
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
    (PW : ChosenPushforwardsAt
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) w₀)
    (QH : ChosenPushforwardsAt (f ⋙ pF) w₀.x) (QG : ChosenPushforwardsAt (g ⋙ pF) w₀.y)
    (PF : ChosenPushforwardsAt pF (f.obj w₀.x)) (M : FGModuleCat.{max v w} k)
    (α : Aut (PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M))) :
    tangentClassAt.{u, v, w} (productBased.{u, v, w} pF f g)
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M
        ⟨boundaryObject.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
          (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QH QG PF
          hF.predeformation.cofibered M α, rfl⟩ = 0 ↔
      ∃ (β : Aut (QH.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M)))
        (γ : Aut (QG.obj (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M))),
        f.map β.asIso.hom.val ≫
            (boundaryCompareFst.{u, v, w} f QH PF hF.predeformation.cofibered M).inv ≫
              (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
                (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF
                hF.predeformation.cofibered M).hom =
          (boundaryCompareFst.{u, v, w} f QH PF hF.predeformation.cofibered M).inv ≫
            α.asIso.hom.val ≫
              (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
                (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF
                hF.predeformation.cofibered M).hom ≫ g.map γ.asIso.hom.val := by
  have hzero := tangentClassAt_pushforward_eq_zero.{u, v, w} (productBased.{u, v, w} pF f g)
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) w₀ PW M
  have hiso := tangentClassAt_eq_iff.{u, v, w} (productBased.{u, v, w} pF f g)
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M
    ⟨boundaryObject.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
      (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QH QG PF
      hF.predeformation.cofibered M α, rfl⟩
    (PW.obj (squareZeroCrossUnder.{u, v, w} w₀.base M))
  have hK := boundaryCompare_comp_crossCompare_eq.{u, v, w} f g PW QH QG PF M
    hF.predeformation.cofibered hH.predeformation.cofibered hG.predeformation.cofibered
  have hkey : f.map (crossCompareFst.{u, v, w} f g PW M QH hH.predeformation.cofibered).hom ≫
        (PW.obj (squareZeroCrossUnder.{u, v, w} w₀.base M)).1.iso.hom =
      (boundaryCompareFst.{u, v, w} f QH PF hF.predeformation.cofibered M).inv ≫
        (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
          (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF
          hF.predeformation.cofibered M).hom ≫
          g.map (crossCompareSnd.{u, v, w} f g PW M QG hG.predeformation.cofibered).hom := by
    rw [← hK, Iso.inv_hom_id_assoc]
  have hsqiff : ∀ (βv : (QH.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M)).1 ⟶
        (QH.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M)).1)
      (γv : (QG.obj (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M)).1 ⟶
        (QG.obj (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M)).1)
      (ai : (QH.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M)).1 ⟶
        (PW.obj (squareZeroCrossUnder.{u, v, w} w₀.base M)).1.x)
      (bi : (QG.obj (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M)).1 ⟶
        (PW.obj (squareZeroCrossUnder.{u, v, w} w₀.base M)).1.y),
      βv ≫ (crossCompareFst.{u, v, w} f g PW M QH hH.predeformation.cofibered).hom = ai →
      γv ≫ (crossCompareSnd.{u, v, w} f g PW M QG hG.predeformation.cofibered).hom = bi →
      ((f.map ai ≫
          (PW.obj (squareZeroCrossUnder.{u, v, w} w₀.base M)).1.iso.hom =
        ((boundaryCompareFst.{u, v, w} f QH PF hF.predeformation.cofibered M).inv ≫
            α.asIso.hom.val ≫
              (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
                (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF
                hF.predeformation.cofibered M).hom) ≫
          g.map bi) ↔
      (f.map βv ≫
          (boundaryCompareFst.{u, v, w} f QH PF hF.predeformation.cofibered M).inv ≫
            (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
              (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF
              hF.predeformation.cofibered M).hom =
        (boundaryCompareFst.{u, v, w} f QH PF hF.predeformation.cofibered M).inv ≫
          α.asIso.hom.val ≫
            (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
              (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF
              hF.predeformation.cofibered M).hom ≫ g.map γv)) := by
    rintro βv γv ai bi rfl rfl
    have eL : f.map (βv ≫ (crossCompareFst.{u, v, w} f g PW M QH
          hH.predeformation.cofibered).hom) ≫
          (PW.obj (squareZeroCrossUnder.{u, v, w} w₀.base M)).1.iso.hom =
        (f.map βv ≫
            (boundaryCompareFst.{u, v, w} f QH PF hF.predeformation.cofibered M).inv ≫
              (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
                (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF
                hF.predeformation.cofibered M).hom) ≫
          g.map (crossCompareSnd.{u, v, w} f g PW M QG hG.predeformation.cofibered).hom := by
      rw [f.map_comp, Category.assoc, hkey]
      simp only [Category.assoc]
    have eR : ((boundaryCompareFst.{u, v, w} f QH PF hF.predeformation.cofibered M).inv ≫
            α.asIso.hom.val ≫
              (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
                (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF
                hF.predeformation.cofibered M).hom) ≫
          g.map (γv ≫
            (crossCompareSnd.{u, v, w} f g PW M QG hG.predeformation.cofibered).hom) =
        ((boundaryCompareFst.{u, v, w} f QH PF hF.predeformation.cofibered M).inv ≫
            α.asIso.hom.val ≫
              (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
                (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF
                hF.predeformation.cofibered M).hom ≫ g.map γv) ≫
          g.map (crossCompareSnd.{u, v, w} f g PW M QG hG.predeformation.cofibered).hom := by
      rw [g.map_comp]
      simp only [Category.assoc]
    rw [eL, eR]
    exact Iso.cancel_iso_hom_right _ _
      (g.mapIso (crossCompareSnd.{u, v, w} f g PW M QG hG.predeformation.cofibered))
  rw [← hzero]
  refine Iff.trans hiso ?_
  constructor
  · rintro ⟨e⟩
    have hlift : (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g).IsHomLift
        (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)) e.hom.val := e.hom.2
    obtain ⟨eA, eB, hvA, hvB, hw0⟩ :
        ∃ (eA : (QH.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M)).1 ≅
              (PW.obj (squareZeroCrossUnder.{u, v, w} w₀.base M)).1.x)
          (eB : (QG.obj (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M)).1 ≅
              (PW.obj (squareZeroCrossUnder.{u, v, w} w₀.base M)).1.y),
          (f ⋙ pF).IsHomLift
              (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)) eA.hom ∧
            (g ⋙ pF).IsHomLift
              (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)) eB.hom ∧
            f.map eA.hom ≫ (PW.obj (squareZeroCrossUnder.{u, v, w} w₀.base M)).1.iso.hom =
              ((boundaryCompareFst.{u, v, w} f QH PF hF.predeformation.cofibered M).inv ≫
                  α.asIso.hom.val ≫
                    (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
                      (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF
                      hF.predeformation.cofibered M).hom) ≫ g.map eB.hom :=
      ⟨(TwoFibreProductOver.fst (f ⋙ pF) (g ⋙ pF) pF f g).mapIso
          (Functor.Fiber.fiberInclusion.mapIso e),
        (TwoFibreProductOver.snd (f ⋙ pF) (g ⋙ pF) pF f g).mapIso
          (Functor.Fiber.fiberInclusion.mapIso e),
        TwoFibreProductOver.isHomLift_a e.hom.val _ hlift,
        TwoFibreProductOver.isHomLift_b e.hom.val _ hlift, e.hom.val.w⟩
    have hβv : (f ⋙ pF).IsHomLift
        (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
        (eA.hom ≫
          (crossCompareFst.{u, v, w} f g PW M QH hH.predeformation.cofibered).inv) := by
      have := hvA
      have := isHomLift_crossCompareFst.{u, v, w} f g PW M QH hH.predeformation.cofibered
      infer_instance
    have hγv : (g ⋙ pF).IsHomLift
        (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
        (eB.hom ≫
          (crossCompareSnd.{u, v, w} f g PW M QG hG.predeformation.cofibered).inv) := by
      have := hvB
      have := isHomLift_crossCompareSnd.{u, v, w} f g PW M QG hG.predeformation.cofibered
      infer_instance
    have hsq' := (hsqiff
        (eA.hom ≫ (crossCompareFst.{u, v, w} f g PW M QH hH.predeformation.cofibered).inv)
        (eB.hom ≫ (crossCompareSnd.{u, v, w} f g PW M QG hG.predeformation.cofibered).inv)
        eA.hom eB.hom
        (by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id])
        (by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id])).mp hw0
    exact ⟨.of (fiberIsoOfVertical _ _
        (eA ≪≫ (crossCompareFst.{u, v, w} f g PW M QH hH.predeformation.cofibered).symm) hβv),
      .of (fiberIsoOfVertical _ _
        (eB ≪≫ (crossCompareSnd.{u, v, w} f g PW M QG hG.predeformation.cofibered).symm) hγv),
      hsq'⟩
  · rintro ⟨β, γ, hsq⟩
    have hβv : (f ⋙ pF).IsHomLift
        (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
        (β.asIso.hom.val ≫
          (crossCompareFst.{u, v, w} f g PW M QH hH.predeformation.cofibered).hom) := by
      have h1 : (f ⋙ pF).IsHomLift
          (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)) β.asIso.hom.val :=
        β.asIso.hom.2
      have h2 := isHomLift_crossCompareFst.{u, v, w} f g PW M QH hH.predeformation.cofibered
      exact @IsHomLift.comp_of_lift_id _ _ _ _ (f ⋙ pF) _ _ _ _ _ _ h1 h2
    have hγv : (g ⋙ pF).IsHomLift
        (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
        (γ.asIso.hom.val ≫
          (crossCompareSnd.{u, v, w} f g PW M QG hG.predeformation.cofibered).hom) := by
      have h1 : (g ⋙ pF).IsHomLift
          (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)) γ.asIso.hom.val :=
        γ.asIso.hom.2
      have h2 := isHomLift_crossCompareSnd.{u, v, w} f g PW M QG hG.predeformation.cofibered
      exact @IsHomLift.comp_of_lift_id _ _ _ _ (g ⋙ pF) _ _ _ _ _ _ h1 h2
    refine ⟨fiberIsoOfVertical _ _
      (TwoFibreProductOver.isoMkVertical
        (Functor.Fiber.fiberInclusion.mapIso β.asIso ≪≫
          crossCompareFst.{u, v, w} f g PW M QH hH.predeformation.cofibered)
        (Functor.Fiber.fiberInclusion.mapIso γ.asIso ≪≫
          crossCompareSnd.{u, v, w} f g PW M QG hG.predeformation.cofibered)
        hβv hγv ((hsqiff β.asIso.hom.val γ.asIso.hom.val _ _ rfl rfl).mpr hsq))
      (TwoFibreProductOver.structureFunctor_isHomLift _ _ hβv)⟩

end BoundaryZero

end Deformation

end
