module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.TwoIsoCoherenceOfToposHom

/-!
# Pasting of 2-isomorphisms on derived pullbacks

Consider morphisms of ringed topoi forming two commutative squares (Stacks 04IC)
```
  Sₙ --xφ--> Sₘ --xψ--> Sₗ
  |sₙ        |sₘ        |sₗ
  v          v          v
  Cₙ --tφ--> Cₘ --tψ--> Cₗ
```
with 2-isomorphisms `τφ : tφ ∘ sₙ ≅ sₘ ∘ xφ` and `τψ : tψ ∘ sₘ ≅ sₗ ∘ xψ`, together with morphisms
`tθ`, `xθ` and 2-isomorphisms `T : tψ ∘ tφ ≅ tθ`, `κ : xθ ≅ xψ ∘ xφ`, and a 2-isomorphism
`τθ : tθ ∘ sₙ ≅ sₗ ∘ xθ` that is the pasting of `τφ` and `τψ` through `T` and `κ`. Then on
derived pullbacks (Stacks 06YY) the square of `τθ` is the pasting of the squares of `τφ` and
`τψ` through the composition isomorphisms of Stacks 0D6D:
`Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.derivedPullbackTwoIsoSquare_pasting`.

The proof is a chase through the coherence of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/TwoIsoCoherenceOfToposHom.lean`:
the cocycle identity of Stacks 0D6D three times and the naturality of the composition
isomorphism in a 2-isomorphism four times.

Nothing here is registered.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.Cohomology.DerivedBaseChangeOfToposHom

universe v u w

attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

noncomputable section

namespace Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

variable {Sn Sm Sl Cn Cm Cl : RingedTopos.{v, u, w}}
  [Sn.J.HasSheafCompose (forget RingCat.{w})] [Sm.J.HasSheafCompose (forget RingCat.{w})]
  [Sl.J.HasSheafCompose (forget RingCat.{w})] [Cn.J.HasSheafCompose (forget RingCat.{w})]
  [Cm.J.HasSheafCompose (forget RingCat.{w})] [Cl.J.HasSheafCompose (forget RingCat.{w})]
  [Sn.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Sm.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Sl.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Cn.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Cm.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Cl.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Sn.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Sm.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Sl.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Cn.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Cm.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Cl.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify Sn.J AddCommGrpCat.{w}] [Sn.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Sm.J AddCommGrpCat.{w}] [Sm.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Sl.J AddCommGrpCat.{w}] [Sl.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Cn.J AddCommGrpCat.{w}] [Cn.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Cm.J AddCommGrpCat.{w}] [Cm.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Cl.J AddCommGrpCat.{w}] [Cl.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Sn.J (Type w)] [HasSheafify Sm.J (Type w)] [HasSheafify Sl.J (Type w)]
  [HasSheafify Cn.J (Type w)] [HasSheafify Cm.J (Type w)] [HasSheafify Cl.J (Type w)]
  (sn : RingedToposHom Sn Cn) (sm : RingedToposHom Sm Cm) (sl : RingedToposHom Sl Cl)
  (tφ : RingedToposHom Cn Cm) (tψ : RingedToposHom Cm Cl) (tθ : RingedToposHom Cn Cl)
  (xφ : RingedToposHom Sn Sm) (xψ : RingedToposHom Sm Sl) (xθ : RingedToposHom Sn Sl)

/-- The square of derived pullbacks of a 2-isomorphism `τ : t ∘ s ≅ s' ∘ x`:
`Lt^* ⋙ Ls^* ≅ Ls'^* ⋙ Lx^*`. -/
def derivedPullbackTwoIsoSquareIso {S S' C C' : RingedTopos.{v, u, w}}
    [S.J.HasSheafCompose (forget RingCat.{w})] [S'.J.HasSheafCompose (forget RingCat.{w})]
    [C.J.HasSheafCompose (forget RingCat.{w})] [C'.J.HasSheafCompose (forget RingCat.{w})]
    [S.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [S'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [C.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [C'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [S.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [C.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [C'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [HasSheafify S.J AddCommGrpCat.{w}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify S'.J AddCommGrpCat.{w}] [S'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify C.J AddCommGrpCat.{w}] [C.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify C'.J AddCommGrpCat.{w}] [C'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify S.J (Type w)] [HasSheafify S'.J (Type w)] [HasSheafify C.J (Type w)]
    [HasSheafify C'.J (Type w)]
    (s : RingedToposHom S C) (s' : RingedToposHom S' C') (t : RingedToposHom C C')
    (x : RingedToposHom S S') (τ : RingedToposHom.TwoIso (t.comp s) (s'.comp x)) :
    derivedPullback t ⋙ derivedPullback s ≅ derivedPullback s' ⋙ derivedPullback x :=
  derivedPullbackCompIso s t ≪≫ derivedPullbackIsoOfTwoIso τ ≪≫
    (derivedPullbackCompIso x s').symm

/-- **Pasting of squares of derived pullbacks.** If the 2-isomorphism `τθ` of the outer square is
the pasting of `τφ` and `τψ` through `T : tψ ∘ tφ ≅ tθ` and `κ : xθ ≅ xψ ∘ xφ`, then its square
of derived pullbacks, preceded by the composition isomorphism `Ltφ^* Ltψ^* ≅ L(tψ ∘ tφ)^*` and
`LT`, is the pasting of the squares of `τφ` and `τψ`, followed by the composition isomorphism
`Lxφ^* Lxψ^* ≅ L(xψ ∘ xφ)^*` and `Lκ⁻¹`. -/
theorem derivedPullbackTwoIsoSquare_pasting (τφ : RingedToposHom.TwoIso (tφ.comp sn) (sm.comp xφ))
    (τψ : RingedToposHom.TwoIso (tψ.comp sm) (sl.comp xψ))
    (τθ : RingedToposHom.TwoIso (tθ.comp sn) (sl.comp xθ))
    (T : RingedToposHom.TwoIso (tψ.comp tφ) tθ) (κ : RingedToposHom.TwoIso xθ (xψ.comp xφ))
    (hΓ : (RingedToposHom.TwoIso.associator sn tφ tψ).trans
        ((T.whiskerLeft sn).trans τθ) =
      (τφ.whiskerRight tψ).trans ((RingedToposHom.TwoIso.associator xφ sm tψ).trans
        ((τψ.whiskerLeft xφ).trans ((RingedToposHom.TwoIso.associator xφ xψ sl).symm.trans
          (κ.symm.whiskerRight sl)))))
    (Y : DerivedCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf Cl.O))) :
    (derivedPullback sn).map ((derivedPullbackCompIso tφ tψ).hom.app Y ≫
        (derivedPullbackIsoOfTwoIso T).hom.app Y) ≫
        (derivedPullbackTwoIsoSquareIso sn sl tθ xθ τθ).hom.app Y =
      (derivedPullbackTwoIsoSquareIso sn sm tφ xφ τφ).hom.app ((derivedPullback tψ).obj Y) ≫
        (derivedPullback xφ).map ((derivedPullbackTwoIsoSquareIso sm sl tψ xψ τψ).hom.app Y) ≫
        (derivedPullbackCompIso xφ xψ).hom.app ((derivedPullback sl).obj Y) ≫
        (derivedPullbackIsoOfTwoIso κ).inv.app ((derivedPullback sl).obj Y) := by
  have h1 : (derivedPullbackCompIso sn (tψ.comp tφ)).hom.app Y ≫
      (derivedPullbackIsoOfTwoIso (T.whiskerLeft sn)).hom.app Y =
        (derivedPullback sn).map ((derivedPullbackIsoOfTwoIso T).hom.app Y) ≫
          (derivedPullbackCompIso sn tθ).hom.app Y :=
    derivedPullbackCompComparison_whiskerLeft sn T Y
  have h2 : (derivedPullbackCompIso sn tφ).hom.app ((derivedPullback tψ).obj Y) ≫
      (derivedPullbackCompIso (tφ.comp sn) tψ).hom.app Y ≫
        (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator sn tφ tψ)).hom.app Y =
      (derivedPullback sn).map ((derivedPullbackCompIso tφ tψ).hom.app Y) ≫
        (derivedPullbackCompIso sn (tψ.comp tφ)).hom.app Y :=
    derivedPullbackCompComparison_assoc_associator sn tφ tψ Y
  have h3 : (derivedPullbackCompIso (tφ.comp sn) tψ).hom.app Y ≫
      (derivedPullbackIsoOfTwoIso (τφ.whiskerRight tψ)).hom.app Y =
        (derivedPullbackIsoOfTwoIso τφ).hom.app ((derivedPullback tψ).obj Y) ≫
          (derivedPullbackCompIso (sm.comp xφ) tψ).hom.app Y :=
    derivedPullbackCompComparison_whiskerRight τφ tψ Y
  have h4 : (derivedPullbackCompIso xφ sm).hom.app ((derivedPullback tψ).obj Y) ≫
      (derivedPullbackCompIso (sm.comp xφ) tψ).hom.app Y ≫
        (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator xφ sm tψ)).hom.app Y =
      (derivedPullback xφ).map ((derivedPullbackCompIso sm tψ).hom.app Y) ≫
        (derivedPullbackCompIso xφ (tψ.comp sm)).hom.app Y :=
    derivedPullbackCompComparison_assoc_associator xφ sm tψ Y
  have h5 : (derivedPullbackCompIso xφ (tψ.comp sm)).hom.app Y ≫
      (derivedPullbackIsoOfTwoIso (τψ.whiskerLeft xφ)).hom.app Y =
        (derivedPullback xφ).map ((derivedPullbackIsoOfTwoIso τψ).hom.app Y) ≫
          (derivedPullbackCompIso xφ (sl.comp xψ)).hom.app Y :=
    derivedPullbackCompComparison_whiskerLeft xφ τψ Y
  have h6 : (derivedPullbackCompIso xφ xψ).hom.app ((derivedPullback sl).obj Y) ≫
      (derivedPullbackCompIso (xψ.comp xφ) sl).hom.app Y ≫
        (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator xφ xψ sl)).hom.app Y =
      (derivedPullback xφ).map ((derivedPullbackCompIso xψ sl).hom.app Y) ≫
        (derivedPullbackCompIso xφ (sl.comp xψ)).hom.app Y :=
    derivedPullbackCompComparison_assoc_associator xφ xψ sl Y
  have h7 : (derivedPullbackCompIso (xψ.comp xφ) sl).hom.app Y ≫
      (derivedPullbackIsoOfTwoIso (κ.symm.whiskerRight sl)).hom.app Y =
        (derivedPullbackIsoOfTwoIso κ.symm).hom.app ((derivedPullback sl).obj Y) ≫
          (derivedPullbackCompIso xθ sl).hom.app Y :=
    derivedPullbackCompComparison_whiskerRight κ.symm sl Y
  have hΓ' := congrArg (fun s ↦ (derivedPullbackIsoOfTwoIso s).hom.app Y) hΓ
  simp only [derivedPullbackIsoOfTwoIso_trans, derivedPullbackIsoOfTwoIso_symm, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app] at hΓ'
  rw [derivedPullbackIsoOfTwoIso_symm] at h7
  simp only [derivedPullbackTwoIsoSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have h4' : (derivedPullbackCompIso (sm.comp xφ) tψ).hom.app Y ≫
      (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator xφ sm tψ)).hom.app Y =
        (derivedPullbackCompIso xφ sm).inv.app ((derivedPullback tψ).obj Y) ≫
          (derivedPullback xφ).map ((derivedPullbackCompIso sm tψ).hom.app Y) ≫
            (derivedPullbackCompIso xφ (tψ.comp sm)).hom.app Y := by
    rw [← h4, Iso.inv_hom_id_app_assoc]
  have h6' : (derivedPullbackCompIso xφ (sl.comp xψ)).hom.app Y ≫
      (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator xφ xψ sl)).inv.app Y =
        (derivedPullback xφ).map ((derivedPullbackCompIso xψ sl).inv.app Y) ≫
          (derivedPullbackCompIso xφ xψ).hom.app ((derivedPullback sl).obj Y) ≫
            (derivedPullbackCompIso (xψ.comp xφ) sl).hom.app Y := by
    rw [← cancel_epi ((derivedPullback xφ).map ((derivedPullbackCompIso xψ sl).hom.app Y)),
      ← reassoc_of% h6, Iso.hom_inv_id_app, Category.comp_id,
      ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [← reassoc_of% h1, ← reassoc_of% h2, reassoc_of% hΓ', reassoc_of% h3, reassoc_of% h4',
    reassoc_of% h5, reassoc_of% h6', reassoc_of% h7, Iso.hom_inv_id_app]
  simp only [Iso.symm_hom, CategoryTheory.Functor.comp_obj, Category.comp_id]

end Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

end
