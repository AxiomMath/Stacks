module

public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Transitions of homotopy categories induced by a degreewise transition

Let `P : V ⥤ V'` and `Q : V ⥤ V''` be additive functors and `U : V' ⥤ V''` an additive functor.
A natural transformation `P ⋙ U ⟶ Q` induces one between the corresponding functors of homotopy
categories of complexes, and a cocycle condition for three such transformations — one for each
of two composable additive functors and one for their composite — is inherited by the induced
transformations.

## Main definitions

* `CategoryTheory.mapHomotopyCategoryTransition`: the transformation
  `P.mapHomotopyCategory c ⋙ U.mapHomotopyCategory c ⟶ Q.mapHomotopyCategory c` induced by a
  transformation `P ⋙ U ⟶ Q`.

## Main results

* `CategoryTheory.mapHomotopyCategoryCompIso_hom_app` and
  `CategoryTheory.mapHomotopyCategoryTransition_app`: both are the localization of the
  corresponding transformation of complexes at the representing complex of an object.
* `CategoryTheory.mapHomotopyCategoryTransition_cocycle`: the induced transformations satisfy
  the cocycle condition that the given ones satisfy degreewise.

## Implementation notes

`(P ⋙ U).mapHomotopyCategory c` and `P.mapHomotopyCategory c ⋙ U.mapHomotopyCategory c` are not
definitionally equal — the first is one quotient lift and the second a composite of two — so the
transformation induced by a map out of `P ⋙ U` has to be composed with the comparison
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` of the identity. That comparison is the
localization of an identity, hence an identity, which is what
`mapHomotopyCategoryTransition_app` records.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory

variable {ι : Type*} {Vt : Type*} [Category* Vt] [Preadditive Vt]
  {Vl : Type*} [Category* Vl] [Preadditive Vl]
  {Vm : Type*} [Category* Vm] [Preadditive Vm]
  {Vn : Type*} [Category* Vn] [Preadditive Vn]

/-- The comparison of homotopy categories attached to an isomorphism `F ⋙ G ≅ K` of additive
functors is, at an object, the localization of the corresponding map of complexes. -/
theorem mapHomotopyCategoryCompIso_hom_app {F : Vl ⥤ Vm} {G : Vm ⥤ Vn} {K : Vl ⥤ Vn}
    (e : F ⋙ G ≅ K) [F.Additive] [G.Additive] [K.Additive] (c : ComplexShape ι)
    (Y : HomotopyCategory Vl c) :
    (Functor.mapHomotopyCategoryCompIso e c).hom.app Y =
      (HomotopyCategory.quotient Vn c).map
        ((NatTrans.mapHomologicalComplex e.hom c).app Y.as) :=
  rfl

/-- The transformation of homotopy categories of complexes induced by a natural transformation
`t : P ⋙ U ⟶ Q` of additive functors: the comparison identifying the composite of the two
induced functors with the functor induced by the composite, followed by the transformation
induced by `t`. -/
def mapHomotopyCategoryTransition (c : ComplexShape ι) (P : Vt ⥤ Vl) (U : Vl ⥤ Vm)
    (Q : Vt ⥤ Vm) [P.Additive] [U.Additive] [Q.Additive] (t : P ⋙ U ⟶ Q) :
    P.mapHomotopyCategory c ⋙ U.mapHomotopyCategory c ⟶ Q.mapHomotopyCategory c :=
  (Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ U)) c).hom ≫
    NatTrans.mapHomotopyCategory t c

/-- The induced transformation is, at an object, the localization of the transformation of
complexes induced by `t`. -/
theorem mapHomotopyCategoryTransition_app (c : ComplexShape ι) (P : Vt ⥤ Vl) (U : Vl ⥤ Vm)
    (Q : Vt ⥤ Vm) [P.Additive] [U.Additive] [Q.Additive] (t : P ⋙ U ⟶ Q)
    (X : HomotopyCategory Vt c) :
    (mapHomotopyCategoryTransition c P U Q t).app X =
      (HomotopyCategory.quotient Vm c).map
        ((NatTrans.mapHomologicalComplex t c).app X.as) := by
  rw [mapHomotopyCategoryTransition, NatTrans.comp_app, mapHomotopyCategoryCompIso_hom_app,
    Iso.refl_hom, NatTrans.mapHomologicalComplex_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id]
  exact Category.id_comp _

/-- An invertible transformation of additive functors induces an invertible transformation of
the induced functors on homotopy categories. -/
instance isIso_natTrans_mapHomotopyCategory (c : ComplexShape ι) {P Q : Vt ⥤ Vl}
    [P.Additive] [Q.Additive] (t : P ⟶ Q) [IsIso t] :
    IsIso (NatTrans.mapHomotopyCategory t c) := by
  refine ⟨NatTrans.mapHomotopyCategory (inv t) c, ?_, ?_⟩
  · rw [← NatTrans.mapHomotopyCategory_comp, IsIso.hom_inv_id,
      NatTrans.mapHomotopyCategory_id]
  · rw [← NatTrans.mapHomotopyCategory_comp, IsIso.inv_hom_id,
      NatTrans.mapHomotopyCategory_id]

/-- An invertible degreewise transition induces an invertible transition of homotopy
categories. -/
instance isIso_mapHomotopyCategoryTransition (c : ComplexShape ι) (P : Vt ⥤ Vl) (U : Vl ⥤ Vm)
    (Q : Vt ⥤ Vm) [P.Additive] [U.Additive] [Q.Additive] (t : P ⋙ U ⟶ Q) [IsIso t] :
    IsIso (mapHomotopyCategoryTransition c P U Q t) := by
  rw [mapHomotopyCategoryTransition]
  infer_instance

/-- The cocycle condition passes from a degreewise family of transitions to the transitions of
homotopy categories it induces, the comparison of the two composable functors being replaced by
the comparison of homotopy categories it induces. -/
theorem mapHomotopyCategoryTransition_cocycle (c : ComplexShape ι)
    (Pl : Vt ⥤ Vl) (Pm : Vt ⥤ Vm) (Pn : Vt ⥤ Vn)
    [Pl.Additive] [Pm.Additive] [Pn.Additive]
    (Uψ : Vl ⥤ Vm) (Uφ : Vm ⥤ Vn) (Uχ : Vl ⥤ Vn)
    [Uψ.Additive] [Uφ.Additive] [Uχ.Additive] (e : Uψ ⋙ Uφ ≅ Uχ)
    (tψ : Pl ⋙ Uψ ⟶ Pm) (tφ : Pm ⋙ Uφ ⟶ Pn) (tχ : Pl ⋙ Uχ ⟶ Pn)
    (hdeg : ∀ M : Vt, e.hom.app (Pl.obj M) ≫ tχ.app M = Uφ.map (tψ.app M) ≫ tφ.app M)
    (X : HomotopyCategory Vt c) :
    (Functor.mapHomotopyCategoryCompIso e c).hom.app ((Pl.mapHomotopyCategory c).obj X) ≫
        (mapHomotopyCategoryTransition c Pl Uχ Pn tχ).app X =
      (Uφ.mapHomotopyCategory c).map
          ((mapHomotopyCategoryTransition c Pl Uψ Pm tψ).app X) ≫
        (mapHomotopyCategoryTransition c Pm Uφ Pn tφ).app X := by
  rw [mapHomotopyCategoryTransition_app, mapHomotopyCategoryTransition_app,
    mapHomotopyCategoryTransition_app, mapHomotopyCategoryCompIso_hom_app]
  refine ((HomotopyCategory.quotient Vn c).map_comp _ _).symm.trans
    (Eq.trans ?_ ((HomotopyCategory.quotient Vn c).map_comp _ _))
  exact congrArg (HomotopyCategory.quotient Vn c).map
    (HomologicalComplex.hom_ext _ _ fun i => hdeg (X.as.X i))

end CategoryTheory

end
