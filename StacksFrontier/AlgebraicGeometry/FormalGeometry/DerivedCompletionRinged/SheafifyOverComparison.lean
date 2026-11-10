module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SectionwiseLocallyQuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceSheafification
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GlobalExtendedCech

/-!
# Sheafifying a complex of presheaves on a slice, against the restriction of a sheafification

Let `(𝒞, 𝒪)` be a ringed site, `U` an object, `P` a complex of presheaves of `𝒪`-modules and
`Q` a complex of presheaves of `𝒪_U`-modules, with a map `ψ : Q ⟶ P|_U` to the restriction of
`P` to the slice. This file builds the induced map

`Q^# ⟶ (P^#)|_U`

of complexes of sheaves of `𝒪_U`-modules — the sheafification of `ψ` followed by the comparison
of sheafification with restriction to a slice — and shows that it is a quasi-isomorphism as soon
as the maps of homology presheaves of `ψ` are locally bijective, and that it is compatible with
augmentations onto the structure sheaves.

## Main definitions

* `Stacks.SheafOfModules.SliceSheafification.sheafifyOverNatTrans`: the comparison
  `(P|_U)^# ⟶ (P^#)|_U`, natural in `P`.
* `AlgebraicGeometry.RingedSite.sheafifyAugmentation`: the augmentation `P^# ⟶ 𝒪` obtained by
  sheafifying an augmentation `P ⟶ 𝒪`.
* `AlgebraicGeometry.RingedSite.sheafifyOverMap`: the map `Q^# ⟶ (P^#)|_U` induced by
  `ψ : Q ⟶ P|_U`.

## Main results

* `Stacks.SheafOfModules.SliceSheafification.sheafifyOverHom_unit_comp_counit`: at the structure
  sheaf the comparison is compatible with the counits of the two sheafification adjunctions.
* `Stacks.SheafOfModules.SliceSheafification.sheafifyOverNatTrans_comp_augmentation`: the
  comparison, applied to a complex, is compatible with augmentations onto the structure sheaves.
* `AlgebraicGeometry.RingedSite.quasiIso_sheafifyOverMap`: `Q^# ⟶ (P^#)|_U` is a
  quasi-isomorphism when the homology maps of `ψ` are locally bijective.
* `AlgebraicGeometry.RingedSite.sheafifyOverMap_comp_restrictStructureSheafMap`: it is a map over
  `𝒪_U` when `ψ` is.

## Implementation notes

The two spellings of the structure sheaf of the slice, `(ringSheaf X).over U` (restriction along
`Over.forget U`) and `ringSheaf (X.over U)` (the slice ringed site), agree only after unfolding,
which `rw` does not do. The computations are therefore carried out for an arbitrary sheaf of
rings `R` in the first spelling, in the `Stacks.SheafOfModules.SliceSheafification` namespace,
and the ringed-site statements are obtained from them by a single term.

## References

* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w t v u

namespace Stacks.SheafOfModules.SliceSheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{t}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The restricted sheafification unit is natural in the presheaf of modules. -/
theorem restrictedUnit_naturality {P P' : PresheafOfModules.{w} R.obj} (f : P ⟶ P') :
    (presheafOverFunctor.{w} R U).map f ≫ restrictedUnit.{w} R U P' =
      restrictedUnit.{w} R U P ≫
        (SheafOfModules.forget (R.over U) ⋙ PresheafOfModules.restrictScalars
          (𝟙 (R.over U).obj)).map
          ((SheafOfModules.overFunctor R U).map
            ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).map f)) := by
  ext V : 1
  exact congrArg (fun m => m.app ((Over.forget U).op.obj V))
    ((PresheafOfModules.sheafificationAdjunction.{w} (𝟙 R.obj)).unit.naturality f)

/-- The comparison `sheafifyOverHom` corresponds under the adjunction to `restrictedUnit`. -/
private theorem homEquiv_sheafifyOverHom (P : PresheafOfModules.{w} R.obj) :
    (PresheafOfModules.sheafificationAdjunction.{w} (𝟙 (R.over U).obj)).homEquiv _ _
      (sheafifyOverHom.{w} R U P) = restrictedUnit.{w} R U P :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (R.over U).obj)).apply_symm_apply _

/-- The comparison `sheafifyOverHom` is natural in the presheaf of modules. -/
theorem sheafifyOverHom_naturality {P P' : PresheafOfModules.{w} R.obj} (f : P ⟶ P') :
    (PresheafOfModules.sheafification.{w} (𝟙 (R.over U).obj)).map
        ((presheafOverFunctor.{w} R U).map f) ≫ sheafifyOverHom.{w} R U P' =
      sheafifyOverHom.{w} R U P ≫ (SheafOfModules.overFunctor R U).map
        ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).map f) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{w} (𝟙 (R.over U).obj)
  apply (adj.homEquiv _ _).injective
  have h1 : adj.homEquiv _ _ ((PresheafOfModules.sheafification.{w} (𝟙 (R.over U).obj)).map
        ((presheafOverFunctor.{w} R U).map f) ≫ sheafifyOverHom.{w} R U P') =
      (presheafOverFunctor.{w} R U).map f ≫ adj.homEquiv _ _ (sheafifyOverHom.{w} R U P') :=
    adj.homEquiv_naturality_left _ _
  have h2 : adj.homEquiv _ _ (sheafifyOverHom.{w} R U P ≫ (SheafOfModules.overFunctor R U).map
        ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).map f)) =
      adj.homEquiv _ _ (sheafifyOverHom.{w} R U P) ≫
        (SheafOfModules.forget (R.over U) ⋙ PresheafOfModules.restrictScalars
          (𝟙 (R.over U).obj)).map ((SheafOfModules.overFunctor R U).map
            ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).map f)) :=
    adj.homEquiv_naturality_right _ _
  rw [h1, h2, homEquiv_sheafifyOverHom, homEquiv_sheafifyOverHom]
  exact restrictedUnit_naturality R U f

/-- **The comparison of sheafification with restriction to a slice, as a natural
transformation.** Its component at `P` is `sheafifyOverHom`. -/
def sheafifyOverNatTrans :
    presheafOverFunctor.{w} R U ⋙ PresheafOfModules.sheafification.{w} (𝟙 (R.over U).obj) ⟶
      PresheafOfModules.sheafification.{w} (𝟙 R.obj) ⋙ SheafOfModules.overFunctor R U where
  app P := sheafifyOverHom.{w} R U P
  naturality _ _ f := sheafifyOverHom_naturality R U f

/-- The comparison `sheafifyOverNatTrans` is a natural isomorphism. -/
instance isIso_sheafifyOverNatTrans : IsIso (sheafifyOverNatTrans.{w} R U) :=
  have : ∀ P, IsIso ((sheafifyOverNatTrans.{w} R U).app P) := fun P =>
    isIso_sheafifyOverHom.{w} R U P
  NatIso.isIso_of_isIso_app _

section Unit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{t}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{t}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- **The comparison of sheafification with restriction, at the structure sheaf, is compatible
with the counits**: at `P = 𝒪` the comparison `(𝒪|_U)^# ⟶ (𝒪^#)|_U` followed by the restricted
counit `(𝒪^#)|_U ⟶ 𝒪|_U` is the counit of the slice. -/
theorem sheafifyOverHom_unit_comp_counit :
    sheafifyOverHom.{t} R U (PresheafOfModules.unit R.obj) ≫
        (SheafOfModules.overFunctor R U).map
          ((PresheafOfModules.sheafificationAdjunction.{t} (𝟙 R.obj)).counit.app
            (SheafOfModules.unit R)) =
      (PresheafOfModules.sheafificationAdjunction.{t} (𝟙 (R.over U).obj)).counit.app
        (SheafOfModules.unit (R.over U)) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{t} (𝟙 (R.over U).obj)
  apply (adj.homEquiv _ _).injective
  have h1 : adj.homEquiv _ _ (sheafifyOverHom.{t} R U (PresheafOfModules.unit R.obj) ≫
        (SheafOfModules.overFunctor R U).map
          ((PresheafOfModules.sheafificationAdjunction.{t} (𝟙 R.obj)).counit.app
            (SheafOfModules.unit R))) =
      adj.homEquiv _ _ (sheafifyOverHom.{t} R U (PresheafOfModules.unit R.obj)) ≫
        (SheafOfModules.forget (R.over U) ⋙ PresheafOfModules.restrictScalars
          (𝟙 (R.over U).obj)).map ((SheafOfModules.overFunctor R U).map
            ((PresheafOfModules.sheafificationAdjunction.{t} (𝟙 R.obj)).counit.app
              (SheafOfModules.unit R))) :=
    adj.homEquiv_naturality_right _ _
  have h2 : adj.homEquiv _ _ (adj.counit.app (SheafOfModules.unit (R.over U))) = 𝟙 _ :=
    (adj.homEquiv_unit _ _ _).trans (adj.right_triangle_components _)
  rw [h1, homEquiv_sheafifyOverHom]
  refine Eq.trans ?_ h2.symm
  ext V : 1
  exact congrArg (fun m => m.app ((Over.forget U).op.obj V))
    ((PresheafOfModules.sheafificationAdjunction.{t} (𝟙 R.obj)).right_triangle_components
      (SheafOfModules.unit R))

end Unit

section Single

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction of presheaves of modules to the slice at `U` is an additive functor. -/
instance additive_presheafOverFunctor : (presheafOverFunctor.{u} R U).Additive :=
  ⟨by intros; ext; rfl⟩

/-- Restriction of sheaves of modules to the slice at `U` is an additive functor. -/
instance additive_overFunctor : (SheafOfModules.overFunctor.{u} R U).Additive :=
  ⟨by intros; ext; rfl⟩

/-- Sheafification of presheaves of modules is an additive functor. -/
instance additive_sheafification {C' : Type u} [Category.{u} C'] {J' : GrothendieckTopology C'}
    (R' : Sheaf J' RingCat.{u}) [HasWeakSheafify J' AddCommGrpCat.{u}]
    [J'.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (PresheafOfModules.sheafification.{u} (𝟙 R'.obj)).Additive :=
  (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R'.obj)).left_adjoint_additive

/-- **The comparison at the structure sheaf placed in degree zero is compatible with the
counits.** -/
theorem sheafifyOverNatTrans_single_unit :
    ((PresheafOfModules.sheafification.{u} (𝟙 (R.over U).obj)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (presheafOverFunctor.{u} R U)
          (ComplexShape.up ℤ) 0).inv.app (PresheafOfModules.unit R.obj)) ≫
      (NatTrans.mapHomologicalComplex (sheafifyOverNatTrans.{u} R U)
        (ComplexShape.up ℤ)).app ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (PresheafOfModules.unit R.obj)) ≫
      ((SheafOfModules.overFunctor R U).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (PresheafOfModules.sheafification.{u} (𝟙 R.obj)) (ComplexShape.up ℤ) 0).hom.app
            (PresheafOfModules.unit R.obj) ≫
          (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
            ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).counit.app
              (SheafOfModules.unit R))) ≫
      (HomologicalComplex.singleMapHomologicalComplex (SheafOfModules.overFunctor R U)
        (ComplexShape.up ℤ) 0).hom.app (SheafOfModules.unit R) =
      (HomologicalComplex.singleMapHomologicalComplex
          (PresheafOfModules.sheafification.{u} (𝟙 (R.over U).obj)) (ComplexShape.up ℤ) 0).hom.app
          (PresheafOfModules.unit (R.over U).obj) ≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (R.over U).obj)).counit.app
            (SheafOfModules.unit (R.over U))) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.map_comp, Category.assoc]
  have hn := (sheafifyOverNatTrans.{u} R U).naturality
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (PresheafOfModules.unit R.obj)).inv
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← Functor.map_comp_assoc (SheafOfModules.overFunctor R U),
    ← Functor.map_comp (PresheafOfModules.sheafification.{u} (𝟙 R.obj)), Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  let g := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).counit.app
    (SheafOfModules.unit R)
  let g' := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (R.over U).obj)).counit.app
    (SheafOfModules.unit (R.over U))
  let b := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
    ((PresheafOfModules.sheafification.{u} (𝟙 R.obj)).obj (PresheafOfModules.unit R.obj))
  let c := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) (SheafOfModules.unit R)
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
    ((PresheafOfModules.sheafification.{u} (𝟙 (R.over U).obj)).obj
      (PresheafOfModules.unit (R.over U).obj))
  let e' := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
    (SheafOfModules.unit (R.over U))
  change (PresheafOfModules.sheafification.{u} (𝟙 (R.over U).obj)).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (PresheafOfModules.unit (R.over U).obj)).hom ≫
      sheafifyOverHom.{u} R U (PresheafOfModules.unit R.obj) ≫
        (SheafOfModules.overFunctor R U).map b.inv ≫
          (SheafOfModules.overFunctor R U).map (b.hom ≫ g ≫ c.inv) ≫
            (SheafOfModules.overFunctor R U).map c.hom ≫ e'.inv =
    (PresheafOfModules.sheafification.{u} (𝟙 (R.over U).obj)).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (PresheafOfModules.unit (R.over U).obj)).hom ≫ e.inv ≫ e.hom ≫ g' ≫ e'.inv
  have hcancel : (SheafOfModules.overFunctor R U).map b.inv ≫
      (SheafOfModules.overFunctor R U).map (b.hom ≫ g ≫ c.inv) ≫
        (SheafOfModules.overFunctor R U).map c.hom ≫ e'.inv =
      (SheafOfModules.overFunctor R U).map g ≫ e'.inv := by
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]
    refine (Functor.map_comp_assoc _ _ _ _).symm.trans ?_
    exact congrArg (fun m => (SheafOfModules.overFunctor R U).map m ≫ e'.inv)
      ((Category.assoc _ _ _).trans ((congrArg (g ≫ ·) c.inv_hom_id).trans (Category.comp_id g)))
  rw [hcancel, Iso.inv_hom_id_assoc]
  exact congrArg (fun m => _ ≫ m)
    (((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ e'.inv) (sheafifyOverHom_unit_comp_counit R U))))

/-- **Sheafifying a map `ψ : Q ⟶ P|_U` into the restriction of a complex, then comparing with the
restriction of the sheafification, is compatible with augmentations onto the structure
sheaves**, as soon as `ψ` is compatible with the augmentations `P ⟶ R` and `Q ⟶ R|_U` of the
presheaf complexes. -/
theorem sheafifyOverNatTrans_comp_augmentation
    {P : CochainComplex (PresheafOfModules.{u} R.obj) ℤ}
    {Q : CochainComplex (PresheafOfModules.{u} (R.over U).obj) ℤ}
    (ψ : Q ⟶ ((presheafOverFunctor.{u} R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (aP : P ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (PresheafOfModules.unit R.obj))
    (aQ : Q ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (PresheafOfModules.unit (R.over U).obj))
    (h : ψ ≫ ((presheafOverFunctor.{u} R U).mapHomologicalComplex (ComplexShape.up ℤ)).map aP =
      aQ ≫ (HomologicalComplex.singleMapHomologicalComplex (presheafOverFunctor.{u} R U)
          (ComplexShape.up ℤ) 0).inv.app (PresheafOfModules.unit R.obj)) :
    (((PresheafOfModules.sheafification.{u} (𝟙 (R.over U).obj)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ψ ≫
      (NatTrans.mapHomologicalComplex (sheafifyOverNatTrans.{u} R U)
        (ComplexShape.up ℤ)).app P) ≫
      ((SheafOfModules.overFunctor R U).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((PresheafOfModules.sheafification.{u} (𝟙 R.obj)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map aP ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (PresheafOfModules.sheafification.{u} (𝟙 R.obj)) (ComplexShape.up ℤ) 0).hom.app
            (PresheafOfModules.unit R.obj) ≫
          (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
            ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).counit.app
              (SheafOfModules.unit R))) ≫
      (HomologicalComplex.singleMapHomologicalComplex (SheafOfModules.overFunctor R U)
        (ComplexShape.up ℤ) 0).hom.app (SheafOfModules.unit R) =
      ((PresheafOfModules.sheafification.{u} (𝟙 (R.over U).obj)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map aQ ≫
      (HomologicalComplex.singleMapHomologicalComplex
          (PresheafOfModules.sheafification.{u} (𝟙 (R.over U).obj)) (ComplexShape.up ℤ) 0).hom.app
          (PresheafOfModules.unit (R.over U).obj) ≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (R.over U).obj)).counit.app
            (SheafOfModules.unit (R.over U))) := by
  let S' := (PresheafOfModules.sheafification.{u} (𝟙 (R.over U).obj)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let O := (SheafOfModules.overFunctor R U).mapHomologicalComplex (ComplexShape.up ℤ)
  let Sm := (PresheafOfModules.sheafification.{u} (𝟙 R.obj)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let Pv := (presheafOverFunctor.{u} R U).mapHomologicalComplex (ComplexShape.up ℤ)
  let T := NatTrans.mapHomologicalComplex (sheafifyOverNatTrans.{u} R U) (ComplexShape.up ℤ)
  let Hs := (HomologicalComplex.singleMapHomologicalComplex
    (PresheafOfModules.sheafification.{u} (𝟙 R.obj)) (ComplexShape.up ℤ) 0).hom.app
      (PresheafOfModules.unit R.obj) ≫
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).counit.app
        (SheafOfModules.unit R))
  let Ho := (HomologicalComplex.singleMapHomologicalComplex (SheafOfModules.overFunctor R U)
    (ComplexShape.up ℤ) 0).hom.app (SheafOfModules.unit R)
  let PvInv := (HomologicalComplex.singleMapHomologicalComplex (presheafOverFunctor.{u} R U)
    (ComplexShape.up ℤ) 0).inv.app (PresheafOfModules.unit R.obj)
  have hn : T.app P ≫ O.map (Sm.map aP) = S'.map (Pv.map aP) ≫
      T.app ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (PresheafOfModules.unit R.obj)) :=
    (T.naturality aP).symm
  calc (S'.map ψ ≫ T.app P) ≫ O.map (Sm.map aP ≫ Hs) ≫ Ho
      = S'.map ψ ≫ (T.app P ≫ O.map (Sm.map aP)) ≫ O.map Hs ≫ Ho := by
        simp only [Functor.map_comp, Category.assoc]
    _ = S'.map ψ ≫ (S'.map (Pv.map aP) ≫ T.app ((HomologicalComplex.single _
          (ComplexShape.up ℤ) 0).obj (PresheafOfModules.unit R.obj))) ≫ O.map Hs ≫ Ho := by
        rw [hn]
    _ = S'.map (ψ ≫ Pv.map aP) ≫ T.app ((HomologicalComplex.single _
          (ComplexShape.up ℤ) 0).obj (PresheafOfModules.unit R.obj)) ≫ O.map Hs ≫ Ho := by
        rw [S'.map_comp ψ (Pv.map aP)]
        simp only [Category.assoc]
    _ = S'.map (aQ ≫ PvInv) ≫ T.app ((HomologicalComplex.single _
          (ComplexShape.up ℤ) 0).obj (PresheafOfModules.unit R.obj)) ≫ O.map Hs ≫ Ho :=
        congrArg (fun m => S'.map m ≫ _) h
    _ = S'.map aQ ≫ (S'.map PvInv ≫ T.app ((HomologicalComplex.single _
          (ComplexShape.up ℤ) 0).obj (PresheafOfModules.unit R.obj)) ≫ O.map Hs ≫ Ho) :=
        (congrArg (· ≫ _) (S'.map_comp aQ PvInv)).trans (Category.assoc _ _ _)
    _ = _ := congrArg (S'.map aQ ≫ ·) (sheafifyOverNatTrans_single_unit R U)

end Single

end Stacks.SheafOfModules.SliceSheafification

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

/-- **The augmentation of a sheafified complex of presheaves of modules**: the sheafification of
an augmentation `P ⟶ 𝒪` of presheaves, with the sheafification of `𝒪` read as `𝒪` through the
counit of the sheafification adjunction. -/
def sheafifyAugmentation
    {P : CochainComplex
      (PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) ℤ}
    (aP : P ⟶ (CochainComplex.singleFunctor _ 0).obj
      (PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)) :
    ((moduleSheafificationFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      structureSheafComplex X :=
  ((moduleSheafificationFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).map aP ≫
    ((moduleSheafificationFunctor X).mapCochainComplexSingleFunctor 0).hom.app
      (PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) ≫
    (CochainComplex.singleFunctor _ 0).map
      ((PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)).counit.app
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- The augmentation of the sheafified presheaf of Čech complexes is the sheafified
augmentation. -/
theorem sheafifiedCechAugmentation_eq_sheafifyAugmentation {r : ℕ}
    (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    sheafifiedCechAugmentation X f = sheafifyAugmentation X (cechPresheafAugmentation X f) :=
  rfl

variable (U : X.C)

/-- Restriction of presheaves of `𝒪`-modules to the slice at `U`. -/
abbrev presheafOver : PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj ⥤
    PresheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).obj :=
  Stacks.SheafOfModules.SliceSheafification.presheafOverFunctor.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U

attribute [local instance] additive_overFunctor

variable {X U}
  {P : CochainComplex (PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) ℤ}
  {Q : CochainComplex
    (PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).obj) ℤ}

/-- **The map `Q^# ⟶ (P^#)|_U` induced by `ψ : Q ⟶ P|_U`**: the sheafification of `ψ` on the
slice, followed by the comparison of sheafification with restriction to the slice. -/
def sheafifyOverMap
    (ψ : Q ⟶ ((presheafOver X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :
    ((moduleSheafificationFunctor (X.over U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q ⟶
      ((SheafOfModules.overFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((moduleSheafificationFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  ((moduleSheafificationFunctor (X.over U)).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ ≫
    (NatTrans.mapHomologicalComplex
      (Stacks.SheafOfModules.SliceSheafification.sheafifyOverNatTrans.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U)
      (ComplexShape.up ℤ)).app P

/-- **`Q^# ⟶ (P^#)|_U` is a quasi-isomorphism as soon as the maps of homology presheaves of
`ψ : Q ⟶ P|_U` are locally bijective**: sheafification turns `ψ` into a quasi-isomorphism by
`PresheafOfModules.quasiIso_sheafification_map_of_isLocallyBijective`, and the comparison of
sheafification with restriction is an isomorphism. -/
theorem quasiIso_sheafifyOverMap
    (ψ : Q ⟶ ((presheafOver X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (hinj : ∀ n : ℤ, Presheaf.IsLocallyInjective (X.J.over U)
      ((PresheafOfModules.toPresheaf.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).obj).map
        (HomologicalComplex.homologyMap ψ n)))
    (hsurj : ∀ n : ℤ, Presheaf.IsLocallySurjective (X.J.over U)
      ((PresheafOfModules.toPresheaf.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).obj).map
        (HomologicalComplex.homologyMap ψ n))) :
    QuasiIso (sheafifyOverMap ψ) := by
  have h1 : QuasiIso
      (((moduleSheafificationFunctor (X.over U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ψ) :=
    PresheafOfModules.quasiIso_sheafification_map_of_isLocallyBijective
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).obj) ψ hinj hsurj
  have h2 : IsIso ((NatTrans.mapHomologicalComplex
      (Stacks.SheafOfModules.SliceSheafification.sheafifyOverNatTrans.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U)
      (ComplexShape.up ℤ)).app P) :=
    have : ∀ n, IsIso (((NatTrans.mapHomologicalComplex
        (Stacks.SheafOfModules.SliceSheafification.sheafifyOverNatTrans.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U)
        (ComplexShape.up ℤ)).app P).f n) := fun n =>
      Stacks.SheafOfModules.SliceSheafification.isIso_sheafifyOverHom.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U (P.X n)
    HomologicalComplex.Hom.isIso_of_components _
  have h3 := quasiIso_of_isIso ((NatTrans.mapHomologicalComplex
      (Stacks.SheafOfModules.SliceSheafification.sheafifyOverNatTrans.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U)
      (ComplexShape.up ℤ)).app P)
  exact quasiIso_comp (hφ := h1) (hφ' := h3) _ _

/-- **`Q^# ⟶ (P^#)|_U` is a map over `𝒪_U`**, as soon as `ψ : Q ⟶ P|_U` is a map over `𝒪_U` of
the presheaf complexes: composed with the restriction of the augmentation `P^# ⟶ 𝒪` it is the
augmentation `Q^# ⟶ 𝒪_U`. -/
theorem sheafifyOverMap_comp_restrictStructureSheafMap
    (ψ : Q ⟶ ((presheafOver X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (aP : P ⟶ (CochainComplex.singleFunctor _ 0).obj
      (PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj))
    (aQ : Q ⟶ (CochainComplex.singleFunctor _ 0).obj
      (PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).obj))
    (h : ψ ≫ ((presheafOver X U).mapHomologicalComplex (ComplexShape.up ℤ)).map aP =
      aQ ≫ (HomologicalComplex.singleMapHomologicalComplex (presheafOver X U)
          (ComplexShape.up ℤ) 0).inv.app
            (PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)) :
    sheafifyOverMap ψ ≫ restrictStructureSheafMap X U (sheafifyAugmentation X aP) =
      sheafifyAugmentation (X.over U) aQ :=
  (Category.assoc _ _ _).symm.trans
    (Stacks.SheafOfModules.SliceSheafification.sheafifyOverNatTrans_comp_augmentation
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U ψ aP aQ h)

end AlgebraicGeometry.RingedSite

end
