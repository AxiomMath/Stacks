module

public import StacksFrontier.Deformation.ToposThickening.FlatThickeningComplexBaseIdealMaps

/-!
# The reduction `(f')^*𝒥 ⟶ i_*f^*𝒥`, transposed along `f'`

The transpose along `(f')^* ⊣ (f')_*` of the reduction `(f')^*𝒥 ⟶ i_*f^*𝒥` is the unit of
`t^*f^* ⊣ f_*t_*` at `𝒥` read through `t_*f_* = f'_*i_*`
(`Deformation.ToposThickening.unit_comp_map_basePullbackIdealReduction`), and the identification
`f^*𝒥 = I` of Situation 08VV, read on the base, is the structure map of `f'` on `𝒥`
(`Deformation.ToposThickening.unit_comp_map_comp_basePullbackIdealIsoIdeal_comp_incl`).

## References

* [Stacks Project, Tag 08VY](https://stacks.math.columbia.edu/tag/08VY)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe v u w v' u' vS uS wS vS' uS' wS'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  [HasSheafify X'.J AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S')
  (f : RingedToposHom X S) (f' : RingedToposHom X' S')
  (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)


/-- The inverse of an isomorphism transported along an equation of its target. -/
theorem iso_mpr_inv {C : Type*} [Category C] {ι : Sort*} (F : ι → C) {a b : ι} (h : a = b)
    {A : C} (e : A ≅ F a) (h' : (A ≅ F b) = (A ≅ F a)) :
    (h'.mpr e).inv = eqToHom (congrArg F h).symm ≫ e.inv := by
  subst h
  cases h'
  exact (Category.id_comp _).symm

include comm in
/-- The inverse of the comparison `f^*𝒥 = i^*(f')^*𝒥` of
`Deformation.ToposThickening.basePullbackIdealIsoPullback`. -/
theorem basePullbackIdealIsoPullback_inv :
    (basePullbackIdealIsoPullback i t f f' hi ht comm).inv =
      eqToHom (congrArg (fun φ => (pullbackModules φ).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom).symm ≫
      (eqToIso (basePullbackIdeal_eq_pullbackModules_toModulesHom t f ht) ≪≫
        ((MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).pullbackComparison.app
          ht.idealOfThickening.I).symm).inv :=
  iso_mpr_inv (fun φ => (pullbackModules φ).obj
    ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
    i.toModulesHom_eq_toRingedToposModulesHom
    (eqToIso (basePullbackIdeal_eq_pullbackModules_toModulesHom t f ht) ≪≫
        ((MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).pullbackComparison.app
          ht.idealOfThickening.I).symm)
    (congrArg (fun φ => basePullbackIdeal t f ht ≅ (pullbackModules φ).obj
      ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
      i.toModulesHom_eq_toRingedToposModulesHom.symm)

omit [X.J.HasSheafCompose (forget RingCat.{w})] in
/-- Two mutually inverse transports, followed by a morphism. -/
theorem eqToHom_comp_eqToHom_symm_comp {C : Type*} [Category C] {a b d : C} (p : a = b) (q : b = a)
    (x : a ⟶ d) : eqToHom p ≫ eqToHom q ≫ x = x := by
  simp

include comm in
/-- `Deformation.ToposThickening.basePullbackIdealIsoPullback_inv`, after the transport between
the two spellings of `i^*`. -/
theorem eqToHom_comp_basePullbackIdealIsoPullback_inv_eq :
    eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
      (basePullbackIdealIsoPullback i t f f' hi ht comm).inv =
    eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
      eqToHom (congrArg (fun φ => (pullbackModules φ).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom).symm ≫
      (eqToIso (basePullbackIdeal_eq_pullbackModules_toModulesHom t f ht) ≪≫
        ((MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).pullbackComparison.app
          ht.idealOfThickening.I).symm).inv :=
  congrArg (fun x => eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫ x)
    (basePullbackIdealIsoPullback_inv i t f f' hi ht comm)

include comm in
/-- The inverse of the comparison `f^*𝒥 = i^*(f')^*𝒥`, read from the pullback along the first
four-field reading of `i`. -/
theorem eqToHom_comp_basePullbackIdealIsoPullback_inv :
    eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
      (basePullbackIdealIsoPullback i t f f' hi ht comm).inv =
      (eqToIso (basePullbackIdeal_eq_pullbackModules_toModulesHom t f ht) ≪≫
        ((MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).pullbackComparison.app
          ht.idealOfThickening.I).symm).inv :=
  (eqToHom_comp_basePullbackIdealIsoPullback_inv_eq i t f f' hi ht comm).trans
    (eqToHom_comp_eqToHom_symm_comp _ _ _)

section GenericTranspose

variable {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒟]
  {Lt : 𝒜 ⥤ ℬ} {Rt : ℬ ⥤ 𝒜} {Lf : ℬ ⥤ 𝒞} {Rf : 𝒞 ⥤ ℬ}
  {Lg : 𝒜 ⥤ 𝒟} {Rg : 𝒟 ⥤ 𝒜} {Li : 𝒟 ⥤ 𝒞} {Ri : 𝒞 ⥤ 𝒟}
  (aTt : Lt ⊣ Rt) (aTf : Lf ⊣ Rf) (aTg : Lg ⊣ Rg) (aTi : Li ⊣ Ri)

omit [X.J.HasSheafCompose (forget RingCat.{w})] in
/-- **The transpose of a reduction along a comparison of iterated left adjoints**, stated
through units and through the two components of a comparison `τ` of iterated right adjoints
that it uses. -/
theorem unit_comp_map_unit_comp_map_inv_eqToIso_trans_of_components (c : Lg ⋙ Li ≅ Lt ⋙ Lf)
    (J : 𝒜) {E : 𝒞} (p : E = (Lt ⋙ Lf).obj J) (q : (Lt ⋙ Lf).obj J = E)
    (τJ : (Rf ⋙ Rt).obj ((Lt ⋙ Lf).obj J) ⟶ (Ri ⋙ Rg).obj ((Lt ⋙ Lf).obj J))
    (τE : (Rf ⋙ Rt).obj E ⟶ (Ri ⋙ Rg).obj E)
    (hnat : (Rf ⋙ Rt).map (eqToHom q) ≫ τE = τJ ≫ (Ri ⋙ Rg).map (eqToHom q))
    (hτ : (aTt.comp aTf).unit.app J ≫ τJ =
      (aTg.comp aTi).unit.app J ≫ (Ri ⋙ Rg).map (c.hom.app J)) :
    aTg.unit.app J ≫ Rg.map (aTi.unit.app (Lg.obj J) ≫ Ri.map ((eqToIso p ≪≫ (c.app J).symm).inv)) =
      (aTt.comp aTf).unit.app J ≫ (Rf ⋙ Rt).map (eqToHom q) ≫ τE := by
  have hcu : (aTg.comp aTi).unit.app J = aTg.unit.app J ≫ Rg.map (aTi.unit.app (Lg.obj J)) :=
    Adjunction.comp_unit_app _ _ _
  have hq : p.symm = q := rfl
  subst hq
  simp only [Functor.comp_map, Functor.comp_obj] at hτ hnat ⊢
  rw [hnat, Iso.trans_inv, Iso.symm_inv, eqToIso.inv, Iso.app_hom, Ri.map_comp, Rg.map_comp,
    Rg.map_comp, ← Category.assoc, ← hcu, ← Category.assoc, ← hτ, Category.assoc]

end GenericTranspose

include comm in
/-- The comparison of the two iterated pullbacks around the square `f' ∘ i = t ∘ f`, between the
left adjoints of the two composite adjunctions. -/
noncomputable def squarePullbackComparison :
    Functor.comp.{max uS' wS', max u' w, max u w, max (max uS' vS') (wS' + 1),
        max (max u' v') (w + 1), max (max u v) (w + 1)}
        (pullbackModules f'.toModulesHom) (pullbackModules i.toModulesHom) ≅
      Functor.comp.{max uS' wS', max uS wS, max u w, max (max uS' vS') (wS' + 1),
        max (max uS vS) (wS + 1), max (max u v) (w + 1)}
        (pullbackModules t.toModulesHom) (pullbackModules f.toModulesHom) :=
  (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).pullbackComparison

include comm in
/-- The comparison `t_*f_* = (t ∘ f)_* = (f' ∘ i)_* = f'_*i_*` of iterated direct images around
the square `f' ∘ i = t ∘ f`. -/
noncomputable def squarePushforwardComparison :
    Functor.comp.{max u w, max uS wS, max uS' wS', max (max u v) (w + 1),
        max (max uS vS) (wS + 1), max (max uS' vS') (wS' + 1)}
        (RingedToposHom.pushforwardModules f) (RingedToposHom.pushforwardModules t) ⟶
      Functor.comp.{max u w, max u' w, max uS' wS', max (max u v) (w + 1),
        max (max u' v') (w + 1), max (max uS' vS') (wS' + 1)}
        (RingedToposHom.pushforwardModules i) (RingedToposHom.pushforwardModules f') :=
  ((RingedToposHom.pushforwardModulesCompIso f t).inv ≫
      eqToHom (congrArg (fun m : RingedToposHom X S' => RingedToposHom.pushforwardModules m)
        comm.symm) ≫ (RingedToposHom.pushforwardModulesCompIso i f').hom)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The two spellings of `f^*t^*𝒥`, the second as a value of the composite left adjoint. -/
theorem basePullbackIdeal_eq_comp :
    basePullbackIdeal t f ht =
      (Functor.comp.{max uS' wS', max uS wS, max u w, max (max uS' vS') (wS' + 1),
        max (max uS vS) (wS + 1), max (max u v) (w + 1)}
        (pullbackModules t.toModulesHom) (pullbackModules f.toModulesHom)).obj
        ht.idealOfThickening.I :=
  (basePullbackIdeal_eq_pullbackModules_toModulesHom t f ht).trans (Functor.comp_obj _ _ _).symm

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The two spellings of `f^*t^*𝒥`, from the composite left adjoint. -/
theorem comp_obj_eq_basePullbackIdeal :
    (Functor.comp.{max uS' wS', max uS wS, max u w, max (max uS' vS') (wS' + 1),
        max (max uS vS) (wS + 1), max (max u v) (w + 1)}
        (pullbackModules t.toModulesHom) (pullbackModules f.toModulesHom)).obj
        ht.idealOfThickening.I = basePullbackIdeal t f ht :=
  (basePullbackIdeal_eq_comp t f ht).symm

include comm in
/-- The reduction `(f')^*𝒥 ⟶ i_*f^*𝒥` through the comparison of the two composite left
adjoints. -/
theorem eqToHom_comp_basePullbackIdealIsoPullback_inv_eq_squarePullbackComparison :
    eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
      (basePullbackIdealIsoPullback i t f f' hi ht comm).inv =
      (eqToIso (basePullbackIdeal_eq_comp t f ht) ≪≫
        ((squarePullbackComparison i t f f' hi ht comm).app ht.idealOfThickening.I).symm).inv :=
  eqToHom_comp_basePullbackIdealIsoPullback_inv i t f f' hi ht comm

omit [HasSheafify X'.J AddCommGrpCat.{w}] in
include comm in
/-- The conjugate of the comparison of the two composite left adjoints is the comparison
`t_*f_* = (t ∘ f)_* = (f' ∘ i)_* = f'_*i_*` of direct images. -/
theorem conjugateEquiv_squarePullbackComparison_hom :
    conjugateEquiv
        ((RingedToposHom.pullbackAdjPushforwardModules t).comp
          (RingedToposHom.pullbackAdjPushforwardModules f))
        ((RingedToposHom.pullbackAdjPushforwardModules f').comp
          (RingedToposHom.pullbackAdjPushforwardModules i))
        (squarePullbackComparison i t f f' hi ht comm).hom =
      (squarePushforwardComparison i t f f' comm) :=
  conjugateEquiv_pullbackComparison_hom
    (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm)

omit [HasSheafify X'.J AddCommGrpCat.{w}] in
include comm in
/-- The unit property of the comparison of direct images. -/
theorem unit_comp_pushforwardComparison_app :
    ((RingedToposHom.pullbackAdjPushforwardModules t).comp
        (RingedToposHom.pullbackAdjPushforwardModules f)).unit.app ht.idealOfThickening.I ≫
      (squarePushforwardComparison i t f f' comm).app
        ((Functor.comp.{max uS' wS', max uS wS, max u w, max (max uS' vS') (wS' + 1),
          max (max uS vS) (wS + 1), max (max u v) (w + 1)}
          (pullbackModules t.toModulesHom) (pullbackModules f.toModulesHom)).obj
          ht.idealOfThickening.I) =
      ((RingedToposHom.pullbackAdjPushforwardModules f').comp
          (RingedToposHom.pullbackAdjPushforwardModules i)).unit.app ht.idealOfThickening.I ≫
        (Functor.comp.{max u w, max u' w, max uS' wS', max (max u v) (w + 1),
          max (max u' v') (w + 1), max (max uS' vS') (wS' + 1)}
          (RingedToposHom.pushforwardModules i) (RingedToposHom.pushforwardModules f')).map
          ((squarePullbackComparison i t f f' hi ht comm).hom.app ht.idealOfThickening.I) := by
  rw [← conjugateEquiv_squarePullbackComparison_hom i t f f' hi ht comm]
  exact unit_conjugateEquiv
    ((RingedToposHom.pullbackAdjPushforwardModules t).comp
      (RingedToposHom.pullbackAdjPushforwardModules f))
    ((RingedToposHom.pullbackAdjPushforwardModules f').comp
      (RingedToposHom.pullbackAdjPushforwardModules i))
    (squarePullbackComparison i t f f' hi ht comm).hom ht.idealOfThickening.I

omit [HasSheafify X'.J AddCommGrpCat.{w}] in
include comm in
/-- **The transpose of the reduction `(f')^*𝒥 ⟶ i_*f^*𝒥` along `f'`** is the unit of
`t^*f^* ⊣ f_*t_*` at `𝒥`, read through `t_*f_* = (t ∘ f)_* = (f' ∘ i)_* = f'_*i_*`. -/
theorem unit_comp_map_basePullbackIdealReduction :
    (RingedToposHom.pullbackAdjPushforwardModules f').unit.app ht.idealOfThickening.I ≫
      (RingedToposHom.pushforwardModules f').map
        ((RingedToposHom.pullbackAdjPushforwardModules i).unit.app
            ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I) ≫
          (RingedToposHom.pushforwardModules i).map
          ((eqToIso (basePullbackIdeal_eq_comp t f ht) ≪≫
            ((squarePullbackComparison i t f f' hi ht comm).app
              ht.idealOfThickening.I).symm).inv)) =
      ((RingedToposHom.pullbackAdjPushforwardModules t).comp
          (RingedToposHom.pullbackAdjPushforwardModules f)).unit.app ht.idealOfThickening.I ≫
        (Functor.comp.{max u w, max uS wS, max uS' wS', max (max u v) (w + 1),
          max (max uS vS) (wS + 1), max (max uS' vS') (wS' + 1)}
          (RingedToposHom.pushforwardModules f) (RingedToposHom.pushforwardModules t)).map
          (eqToHom (comp_obj_eq_basePullbackIdeal t f ht)) ≫
        (squarePushforwardComparison i t f f' comm).app (basePullbackIdeal t f ht) :=
  unit_comp_map_unit_comp_map_inv_eqToIso_trans_of_components
    (RingedToposHom.pullbackAdjPushforwardModules t)
    (RingedToposHom.pullbackAdjPushforwardModules f)
    (RingedToposHom.pullbackAdjPushforwardModules f')
    (RingedToposHom.pullbackAdjPushforwardModules i)
    (squarePullbackComparison i t f f' hi ht comm) ht.idealOfThickening.I
    (basePullbackIdeal_eq_comp t f ht) (comp_obj_eq_basePullbackIdeal t f ht) _ _
    ((squarePushforwardComparison i t f f' comm).naturality
      (eqToHom (comp_obj_eq_basePullbackIdeal t f ht)))
    (unit_comp_pushforwardComparison_app i t f f' hi ht comm)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  [HasSheafify X'.J AddCommGrpCat.{w}] in
include comm in
/-- The induced map of defining ideals `(f')^*𝒥 ⟶ I` of Stacks 08M7, transposed along `f'`. -/
theorem homEquiv_ofFirstOrderThickenings_idealMap_comp_incl :
    (RingedToposHom.pullbackAdjPushforwardModules f').homEquiv ht.idealOfThickening.I
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
        ((MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap ≫
          hi.idealOfThickening.incl) =
      ht.idealOfThickening.incl ≫ RingedToposHom.unitStructureMap f' :=
  (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).homEquiv_idealMap_comp_incl

include comm in
/-- The reduction followed by the identification `f^*𝒥 = I` and the inclusion `I ⊂ O'`. -/
theorem basePullbackIdealReduction_comp_basePullbackIdealIsoIdeal_comp_incl (hf' : f'.IsFlat)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict) :
    (RingedToposHom.pullbackAdjPushforwardModules i).homEquiv _ _
        (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i t f f' hi ht comm).inv) ≫
        (SheafOfModules.restrictScalars (structureRingMap i)).map
          (basePullbackIdealIsoIdeal i t f f' hi ht comm hf' hstrict).hom ≫
          hi.idealOfThickening.incl =
      (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap ≫
        hi.idealOfThickening.incl :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ hi.idealOfThickening.incl)
    (basePullbackIdealReduction_comp_basePullbackIdealIsoIdeal i t f f' hi ht comm hf' hstrict))

include comm in
/-- **The identification `f^*𝒥 = I` of Situation 08VV, read on the base**: the composite unit of
`t^*f^* ⊣ f_*t_*` at `𝒥`, read through `t_*f_* = f'_*i_*`, followed by the direct image of the
identification and of the inclusion `I ⊂ O'`, is the structure map of `f'` on `𝒥 ⊂ O_{ℬ'}`. -/
theorem unit_comp_map_comp_basePullbackIdealIsoIdeal_comp_incl (hf' : f'.IsFlat)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict) :
    (((RingedToposHom.pullbackAdjPushforwardModules t).comp
          (RingedToposHom.pullbackAdjPushforwardModules f)).unit.app ht.idealOfThickening.I ≫
        (Functor.comp.{max u w, max uS wS, max uS' wS', max (max u v) (w + 1),
          max (max uS vS) (wS + 1), max (max uS' vS') (wS' + 1)}
          (RingedToposHom.pushforwardModules f) (RingedToposHom.pushforwardModules t)).map
          (eqToHom (comp_obj_eq_basePullbackIdeal t f ht)) ≫
        (squarePushforwardComparison i t f f' comm).app (basePullbackIdeal t f ht)) ≫
      (RingedToposHom.pushforwardModules f').map
        ((SheafOfModules.restrictScalars (structureRingMap i)).map
          (basePullbackIdealIsoIdeal i t f f' hi ht comm hf' hstrict).hom ≫
          hi.idealOfThickening.incl) =
      ht.idealOfThickening.incl ≫ RingedToposHom.unitStructureMap f' := by
  rw [← unit_comp_map_basePullbackIdealReduction i t f f' hi ht comm,
    ← eqToHom_comp_basePullbackIdealIsoPullback_inv_eq_squarePullbackComparison i t f f' hi ht comm,
    Category.assoc, ← Functor.map_comp, ← Adjunction.homEquiv_unit,
    basePullbackIdealReduction_comp_basePullbackIdealIsoIdeal_comp_incl i t f f' hi ht comm hf'
      hstrict]
  exact (Adjunction.homEquiv_unit _ _ _ _).symm.trans
    (homEquiv_ofFirstOrderThickenings_idealMap_comp_incl i t f f' hi ht comm)

end Deformation.ToposThickening
