module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineTildeUnitSelf
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TildePullbackCrossing

/-!
# The Eilenberg-Watts unitor over an affine open is the pullback of `tildeSelf`

Let `f' : X' ⟶ Y'` be a morphism of schemes and `V` an affine open of `Y'`. The identification
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.pullbackTildeUnitIso` of the pullback of
`Γ(V, ⊤)~` along `(f' ∣_ V) ≫ V.isoSpec` with the structure sheaf of `f'⁻¹(V)` is the pullback
of `AlgebraicGeometry.tildeSelf` followed by `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`.
This is the unitor of the Eilenberg-Watts presentation of [Stacks, Tag 0EX3] (b) over `V`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.pullbackTildeUnitIso_hom_eq`: the two
  identifications agree.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- For a natural transformation `α : F ⟶ G` with `α.app B ≫ y = w`, the composite
`α.app A ≫ G.map t ≫ y` equals `F.map t ≫ w`. -/
theorem nat_comp_collapse {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α : F ⟶ G)
    {A B : C} (t : A ⟶ B) {E : D} (y : G.obj B ⟶ E) {w : F.obj B ⟶ E}
    (hw : α.app B ≫ y = w) :
    α.app A ≫ G.map t ≫ y = F.map t ≫ w := by
  rw [← hw, ← Category.assoc, ← α.naturality, Category.assoc]

/-- An isomorphism `ι` cancels against its inverse under a functor `P`:
`(a ≫ P.map ι.inv) ≫ P.map (ι.hom ≫ u) ≫ v = a ≫ P.map u ≫ v`. -/
theorem comp_map_cancel {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {A B E : C} (ι : A ≅ B) (u : B ⟶ E) {Z Z' : D} (a : Z ⟶ P.obj B) (v : P.obj E ⟶ Z') :
    (a ≫ P.map ι.inv) ≫ P.map (ι.hom ≫ u) ≫ v = a ≫ P.map u ≫ v := by
  rw [Category.assoc, ← P.map_comp_assoc, Iso.inv_hom_id_assoc]

/-- **The Eilenberg-Watts unitor over an affine open of the base is the pullback of
`AlgebraicGeometry.tildeSelf`.** For a morphism `f' : X' ⟶ Y'` and an affine open `V` of `Y'`, the
identification `…TopDegreeBaseChange.pullbackTildeUnitIso` of the pullback of `Γ(V, ⊤)~` along
`(f' ∣_ V) ≫ V.isoSpec` with the structure sheaf of `f'⁻¹(V)` is the pullback of `tildeSelf`
followed by `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`. -/
theorem pullbackTildeUnitIso_hom_eq {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') (V : Y'.Opens)
    [IsAffine (V : Scheme)] :
    (pullbackTildeUnitIso f' V).hom =
      (Scheme.Modules.pullback ((f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
          (AlgebraicGeometry.tildeSelf (R := CommRingCat.of Γ((V : Scheme), ⊤))).hom ≫
        (Scheme.Modules.pullbackUnitIso ((f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).hom := by
  have hcoh := affineTildeObjSectionsIso_unitModule (V : Scheme)
  have h1 : (pullbackTildeUnitIso f' V).hom =
      (pullbackIsoRestrictPullback f' V).hom.app
          ((AlgebraicGeometry.tilde.functor (CommRingCat.of Γ((V : Scheme), ⊤))).obj
            (ModuleCat.of Γ((V : Scheme), ⊤) Γ((V : Scheme), ⊤))) ≫
        (Scheme.Modules.pullback (f' ∣_ V)).map
            (Stacks.Coherent.affineTildeObjSectionsIso (V : Scheme)
              (Scheme.unitModule (V : Scheme)) inferInstance).hom ≫
          (Scheme.Modules.pullbackUnitIso (f' ∣_ V)).hom := rfl
  have h2 : (Stacks.Coherent.affineTildeObjSectionsIso (V : Scheme)
        (Scheme.unitModule (V : Scheme)) inferInstance).hom =
      (Scheme.Modules.restrictFunctor (V : Scheme).isoSpec.hom).map
          (AlgebraicGeometry.tildeSelf (R := CommRingCat.of Γ((V : Scheme), ⊤))).hom ≫
        ((Scheme.Modules.restrictFunctorIsoPullback (V : Scheme).isoSpec.hom).hom.app
            (_root_.SheafOfModules.unit (Spec (CommRingCat.of Γ((V : Scheme), ⊤))).ringCatSheaf) ≫
          (Scheme.Modules.pullbackUnitIso (V : Scheme).isoSpec.hom).hom) :=
    congrArg Iso.hom hcoh
  have hsplit : (Scheme.Modules.pullback (f' ∣_ V)).map
        (Stacks.Coherent.affineTildeObjSectionsIso (V : Scheme)
          (Scheme.unitModule (V : Scheme)) inferInstance).hom =
      (Scheme.Modules.pullback (f' ∣_ V)).map
          ((Scheme.Modules.restrictFunctor (V : Scheme).isoSpec.hom).map
            (AlgebraicGeometry.tildeSelf (R := CommRingCat.of Γ((V : Scheme), ⊤))).hom) ≫
        (Scheme.Modules.pullback (f' ∣_ V)).map
          (((Scheme.Modules.restrictFunctorIsoPullback (V : Scheme).isoSpec.hom).app
              (_root_.SheafOfModules.unit
                (Spec (CommRingCat.of Γ((V : Scheme), ⊤))).ringCatSheaf)).hom ≫
            (Scheme.Modules.pullbackUnitIso (V : Scheme).isoSpec.hom).hom) :=
    (congrArg (Scheme.Modules.pullback (f' ∣_ V)).map h2).trans
      ((Scheme.Modules.pullback (f' ∣_ V)).map_comp _ _)
  have hfinal : (pullbackIsoRestrictPullback f' V).hom.app
        (_root_.SheafOfModules.unit (Spec (CommRingCat.of Γ((V : Scheme), ⊤))).ringCatSheaf) ≫
      (Scheme.Modules.pullback (f' ∣_ V)).map
          (((Scheme.Modules.restrictFunctorIsoPullback (V : Scheme).isoSpec.hom).app
              (_root_.SheafOfModules.unit
                (Spec (CommRingCat.of Γ((V : Scheme), ⊤))).ringCatSheaf)).hom ≫
            (Scheme.Modules.pullbackUnitIso (V : Scheme).isoSpec.hom).hom) ≫
        (Scheme.Modules.pullbackUnitIso (f' ∣_ V)).hom =
      (Scheme.Modules.pullbackUnitIso ((f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).hom :=
    (comp_map_cancel (Scheme.Modules.pullback (f' ∣_ V))
        ((Scheme.Modules.restrictFunctorIsoPullback (V : Scheme).isoSpec.hom).app
          (_root_.SheafOfModules.unit (Spec (CommRingCat.of Γ((V : Scheme), ⊤))).ringCatSheaf))
        (Scheme.Modules.pullbackUnitIso (V : Scheme).isoSpec.hom).hom
        ((Scheme.Modules.pullbackComp (f' ∣_ V) (V : Scheme).isoSpec.hom).inv.app _)
        (Scheme.Modules.pullbackUnitIso (f' ∣_ V)).hom).trans
      (Scheme.Modules.pullbackUnitIso_comp (f' ∣_ V) (V : Scheme).isoSpec.hom)
  refine h1.trans (Eq.trans (congrArg (fun z : (Scheme.Modules.pullback (f' ∣_ V)).obj
        ((Scheme.Modules.restrictFunctor (V : Scheme).isoSpec.hom).obj
          ((AlgebraicGeometry.tilde.functor (CommRingCat.of Γ((V : Scheme), ⊤))).obj
            (ModuleCat.of Γ((V : Scheme), ⊤) Γ((V : Scheme), ⊤)))) ⟶
        Scheme.unitModule (f' ⁻¹ᵁ V : Scheme) =>
      (pullbackIsoRestrictPullback f' V).hom.app
        ((AlgebraicGeometry.tilde.functor (CommRingCat.of Γ((V : Scheme), ⊤))).obj
          (ModuleCat.of Γ((V : Scheme), ⊤) Γ((V : Scheme), ⊤))) ≫ z)
      ((congrArg (fun z => z ≫ (Scheme.Modules.pullbackUnitIso (f' ∣_ V)).hom)
        hsplit).trans (Category.assoc _ _ _))) ?_)
  exact nat_comp_collapse (pullbackIsoRestrictPullback f' V).hom
    (AlgebraicGeometry.tildeSelf (R := CommRingCat.of Γ((V : Scheme), ⊤))).hom _ hfinal

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
