module

public import Mathlib.CategoryTheory.Limits.Presheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical

/-!
# The stalk of a representable étale sheaf

Let `s` be a geometric point of a scheme `S`.  The stalk at `s` of the sheaf on the small
étale site of `S` represented by an étale `S`-scheme `X` is the set of lifts of `s` to `X`,
naturally in `X`, and the identification sends the germ at a pointed étale neighbourhood
`(U, p)` of a morphism `t : U ⟶ X` to the lift `p ≫ t`.  This is the computation at the heart
of [Stacks, Tag 03QT]: over a field `K` with separable closure `K^{sep}` it reads
`(h_X)_{\overline s} = Mor_K(Spec K^{sep}, X)`, so the stalk of a representable sheaf recovers
the Galois set of the represented étale `K`-scheme.

The stalk at `s` is a colimit over the category of elements of
`AlgebraicGeometry.geometricPointFiber`, the functor sending an object of the small étale
site to its set of lifts of `s`.  So the statement is an instance of the codensity theorem:
every functor to types is the colimit, over the opposite of its category of elements, of the
corepresentable functors its elements index.  That is Mathlib's
`CategoryTheory.Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso`, and no
geometry whatsoever enters.

## Main results

* `AlgebraicGeometry.yonedaCompEtaleStalkPresheafFunctorIso` — the presheaf-level statement:
  the étale stalk of a representable presheaf is the fibre of the geometric point.
* `AlgebraicGeometry.smallEtaleYonedaCompEtaleStalkFunctorIso` — its sheaf-level form, the
  stalk functor applied to `AlgebraicGeometry.smallEtaleYoneda`.
* `AlgebraicGeometry.smallEtaleYonedaCompEtaleStalkFunctorIso_hom_app_etaleStalkGerm` and
  `AlgebraicGeometry.smallEtaleYonedaCompEtaleStalkFunctorIso_hom_app_etaleStalkGerm_val` —
  the identification on germs, which pins the isomorphism down.

## References

* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- **The étale stalk of a representable presheaf.**  The stalk at a geometric point `s` of
the presheaf `Mor_S(-, X)` on the small étale site of `S` is the set of lifts of `s` to `X`,
naturally in `X`.  This is the codensity theorem for
`AlgebraicGeometry.geometricPointFiber`: the stalk is a colimit over the opposite of the
category of elements of that functor, and every functor to types is the colimit there of the
corepresentable functors its elements index. -/
noncomputable def yonedaCompEtaleStalkPresheafFunctorIso :
    yoneda (C := SmallEtale B S hS) ⋙ etaleStalkPresheafFunctor B S hS s (Type u) ≅
      geometricPointFiber B S hS s :=
  Functor.isoWhiskerRight (shrinkYonedaIsoYoneda (C := SmallEtale B S hS)).symm _ ≪≫
    Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso
      (geometricPointFiber B S hS s)

/-- The identification of the étale stalk of `Mor_S(-, X)` with the fibre of the geometric
point carries the germ at a pointed étale neighbourhood `(U, p)` of `t : U ⟶ X` to the lift
of `s` obtained by transporting `p` along `t`. -/
theorem colimit_ι_comp_yonedaCompEtaleStalkPresheafFunctorIso_hom (X : SmallEtale B S hS)
    (U : (geometricPointFiber B S hS s).Elements) :
    colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
        yoneda.obj X) (op U) ≫
      (yonedaCompEtaleStalkPresheafFunctorIso B S hS s).hom.app X =
      ↾ fun t ↦ (geometricPointFiber B S hS s).map t U.2 := by
  have key : colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
        yoneda.obj X) (op U) ≫
      (yonedaCompEtaleStalkPresheafFunctorIso B S hS s).hom.app X =
      (shrinkYonedaIsoYoneda.inv.app X).app (op U.1) ≫
        (Functor.Elements.coconeπOpCompShrinkYonedaObj (geometricPointFiber B S hS s) X).ι.app
          (op U) := by
    simp only [yonedaCompEtaleStalkPresheafFunctorIso,
      Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, etaleStalkPresheafFunctor,
      Functor.comp_map, Functor.whiskerRight_app, Functor.comp_obj, colim_map,
      Functor.whiskeringLeft_obj_map, Functor.whiskeringLeft_obj_obj]
    rw [ι_colimMap_assoc]
    congr 1
    exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
      (Functor.Elements.isColimitCoconeπOpCompShrinkYonedaObj
        (geometricPointFiber B S hS s) X) (op U)
  rw [key]
  ext t
  exact congrArg (fun r ↦ (geometricPointFiber B S hS s).map r U.2)
    (shrinkYonedaObjObjEquiv.apply_symm_apply t)

/-- **The étale stalk of a representable sheaf.**  The stalk at a geometric point `s` of the
sheaf on the small étale site of `S` represented by an étale `S`-scheme `X` is the set of
lifts of `s` to `X`, naturally in `X`. -/
noncomputable def smallEtaleYonedaCompEtaleStalkFunctorIso :
    smallEtaleYoneda B S hS ⋙ etaleStalkFunctor.{u, u} B S hS s ≅
      geometricPointFiber B S hS s :=
  yonedaCompEtaleStalkPresheafFunctorIso B S hS s

/-- The stalk of a representable sheaf is identified with the fibre of the geometric point by
sending the germ at a pointed étale neighbourhood `(U, p)` of a morphism `t : U ⟶ X` to the
lift of `s` obtained by transporting `p` along `t`. -/
theorem smallEtaleYonedaCompEtaleStalkFunctorIso_hom_app_etaleStalkGerm
    (X : SmallEtale B S hS) (U : (geometricPointFiber B S hS s).Elements) (t : U.1 ⟶ X) :
    (smallEtaleYonedaCompEtaleStalkFunctorIso B S hS s).hom.app X
        (etaleStalkGerm.{u, u} B S hS s ((smallEtaleYoneda B S hS).obj X) U t) =
      (geometricPointFiber B S hS s).map t U.2 :=
  ConcreteCategory.congr_hom
    (colimit_ι_comp_yonedaCompEtaleStalkPresheafFunctorIso_hom B S hS s X U) t

/-- The lift of the geometric point attached to the germ at `(U, p)` of `t : U ⟶ X` is the
composite `p ≫ t` of morphisms of schemes. -/
theorem smallEtaleYonedaCompEtaleStalkFunctorIso_hom_app_etaleStalkGerm_val
    (X : SmallEtale B S hS) (U : (geometricPointFiber B S hS s).Elements) (t : U.1 ⟶ X) :
    ((smallEtaleYonedaCompEtaleStalkFunctorIso B S hS s).hom.app X
        (etaleStalkGerm.{u, u} B S hS s ((smallEtaleYoneda B S hS).obj X) U t)).1 =
      U.2.1 ≫ (SmallEtale.toScheme B S hS).map t :=
  congrArg Subtype.val
    (smallEtaleYonedaCompEtaleStalkFunctorIso_hom_app_etaleStalkGerm B S hS s X U t)

end AlgebraicGeometry

end
