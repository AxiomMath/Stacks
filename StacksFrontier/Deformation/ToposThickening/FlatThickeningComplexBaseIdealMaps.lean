module

public import StacksFrontier.Deformation.ToposThickening.FlatThickeningComplexSituation
public import StacksFrontier.Deformation.ToposThickening.FlatThickeningFlatLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge

/-!
# The identification `f^*𝒥 = I` of Situation 08VV, on the reduction

For a strict flat square `f' ∘ i = t ∘ f` of first order thickenings, the identification
`f^*𝒥 ≅ I` of `Deformation.ToposThickening.basePullbackIdealIsoIdeal`, precomposed with the
reduction `(f')^*𝒥 ⟶ i_*i^*(f')^*𝒥 = i_*f^*𝒥`, is the map of defining ideals of Stacks 08M7
(`Deformation.ToposThickening.basePullbackIdealReduction_comp_basePullbackIdealIsoIdeal`).

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

omit [X.J.HasSheafCompose (forget RingCat.{w})] in
/-- The conjugate of the left adjoint of a composite comparison is the comparison. -/
theorem conjugateEquiv_leftAdjointCompIso_hom {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁]
    [Category C₂] {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀) (e : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    conjugateEquiv adj₀₂ (adj₀₁.comp adj₁₂)
      (Adjunction.leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).hom = e.inv := by
  rw [Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans,
    Equiv.apply_symm_apply]

section Conjugate

variable {A : RingedTopos.{v, u, w}} {B : RingedTopos.{vS', uS', wS'}}
  [A.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{wS'})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [A.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify A.J AddCommGrpCat.{w}] [A.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [X.J.HasSheafCompose (forget RingCat.{w})] in
/-- Pullback functors along equal morphisms of ringed topoi are conjugate to the direct images. -/
theorem conjugateEquiv_eqToHom_pullbackModules (k₁ k₂ : RingedToposHom A B) (h : k₁ = k₂) :
    conjugateEquiv (RingedToposHom.pullbackAdjPushforwardModules k₂)
        (RingedToposHom.pullbackAdjPushforwardModules k₁)
        (eqToHom (congrArg (fun m : RingedToposHom A B => m.toModulesHom.pullbackModules) h)) =
      eqToHom (congrArg (fun m : RingedToposHom A B => RingedToposHom.pushforwardModules m)
        h.symm) := by
  subst h
  simp

omit [X.J.HasSheafCompose (forget RingCat.{w})] in
/-- Units of two adjunctions transported from equal four-field morphisms. -/
theorem unit_ofNatIsoRight_eq_of_eq (g₁ g₂ : Stacks.Sheaves.RingedToposModules.RingedToposHom A B)
    (h : g₁ = g₂) {R : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf A.O) ⥤
      SheafOfModules.{wS'} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)}
    (e₁ : Stacks.Sheaves.RingedToposModules.pushforwardModules g₁ ≅ R)
    (e₂ : Stacks.Sheaves.RingedToposModules.pushforwardModules g₂ ≅ R)
    (he : ∀ N, e₁.hom.app N = eqToHom (congrArg
      (fun g => (Stacks.Sheaves.RingedToposModules.pushforwardModules g).obj N) h) ≫ e₂.hom.app N)
    (M : SheafOfModules.{wS'} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)) :
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g₂).ofNatIsoRight
          e₂).unit.app M ≫
        R.map (eqToHom (congrArg (fun g => (pullbackModules g).obj M) h.symm)) =
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g₁).ofNatIsoRight
          e₁).unit.app M := by
  subst h
  have : e₁ = e₂ := Iso.ext (NatTrans.ext (funext fun N => (he N).trans (Category.id_comp _)))
  subst this
  simp

omit [X.J.HasSheafCompose (forget RingCat.{w})] [HasWeakSheafify A.J AddCommGrpCat.{w}]
  [A.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The two comparisons of direct images of sheaves of modules, from the two four-field readings
of a morphism of ringed topoi, agree: both are the identity on underlying sheaves of sets. -/
theorem toModulesPushforwardIso_hom_app_eq (k : RingedToposHom A B)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf A.O)) :
    k.toModulesPushforwardIso.hom.app M =
      eqToHom (congrArg (fun g => (Stacks.Sheaves.RingedToposModules.pushforwardModules g).obj M)
        k.toModulesHom_eq_toRingedToposModulesHom) ≫ k.pushforwardModulesIso.hom.app M := by
  apply Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
  have h1 : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf B.O)).map
      (k.toModulesPushforwardIso.hom.app M) =
        𝟙 (k.toToposHom.pushforward.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf A.O) M)) :=
    Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_ofSheafHom _ _ _
  rw [CategoryTheory.Functor.map_comp, eqToHom_map,
    RingedToposHom.moduleSheafFunctor_map_pushforwardModulesIso, h1]
  exact ((Category.comp_id _).trans (eqToHom_refl _ _)).symm

omit [X.J.HasSheafCompose (forget RingCat.{w})] in
/-- **The units of the two forms of Stacks 03D7 agree**, across the identification of the two
pullback functors. -/
theorem unit_viaComparison_comp_eqToHom (k : RingedToposHom A B)
    (M : SheafOfModules.{wS'} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)) :
    k.pullbackAdjPushforwardModulesViaComparison.unit.app M ≫
        k.pushforwardModules.map (eqToHom (congrArg (fun g => (pullbackModules g).obj M)
          k.toModulesHom_eq_toRingedToposModulesHom.symm)) =
      (RingedToposHom.pullbackAdjPushforwardModules k).unit.app M :=
  unit_ofNatIsoRight_eq_of_eq _ _ k.toModulesHom_eq_toRingedToposModulesHom _ _
    (toModulesPushforwardIso_hom_app_eq k) M

end Conjugate

section Generic

variable {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒟]
  {Lt : 𝒜 ⥤ ℬ} {Rt : ℬ ⥤ 𝒜} {Lf : ℬ ⥤ 𝒞} {Rf : 𝒞 ⥤ ℬ}
  {Lg : 𝒜 ⥤ 𝒟} {Rg : 𝒟 ⥤ 𝒜} {Li : 𝒟 ⥤ 𝒞} {Ri : 𝒞 ⥤ 𝒟}
  (aTt : Lt ⊣ Rt) (aTf : Lf ⊣ Rf) (aTg : Lg ⊣ Rg) (aTi : Li ⊣ Ri)

omit [X.J.HasSheafCompose (forget RingCat.{w})] in
/-- Reassociation through a composite. -/
theorem comp_comp_comp_eq_of_comp_eq {a b c d e : 𝒟} (u : a ⟶ b) (m₁ : b ⟶ c) (m₂ : c ⟶ d)
    (v : d ⟶ e) (M : b ⟶ d) (h : m₁ ≫ m₂ = M) : (u ≫ m₁) ≫ m₂ ≫ v = u ≫ M ≫ v := by
  rw [← h]
  simp

end Generic

omit [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- **The conjugate of the comparison of iterated pullbacks around a square** is the comparison
of iterated direct images, `t_*f_* = (t ∘ f)_* = (f' ∘ i)_* = f'_*i_*`. -/
theorem conjugateEquiv_pullbackComparison_hom (D : MorphismOfThickenings X X' S S') :
    conjugateEquiv ((RingedToposHom.pullbackAdjPushforwardModules D.t).comp
        (RingedToposHom.pullbackAdjPushforwardModules D.f))
      ((RingedToposHom.pullbackAdjPushforwardModules D.f').comp
        (RingedToposHom.pullbackAdjPushforwardModules D.i))
      D.pullbackComparison.hom =
    (RingedToposHom.pushforwardModulesCompIso D.f D.t).inv ≫
      eqToHom (congrArg (fun m : RingedToposHom X S' => RingedToposHom.pushforwardModules m)
        D.comm.symm) ≫ (RingedToposHom.pushforwardModulesCompIso D.i D.f').hom := by
  unfold MorphismOfThickenings.pullbackComparison
  rw [Iso.trans_hom, Iso.trans_hom, ← conjugateEquiv_comp _
    (RingedToposHom.pullbackAdjPushforwardModules (D.f'.comp D.i)), ← conjugateEquiv_comp _
    (RingedToposHom.pullbackAdjPushforwardModules (D.t.comp D.f)), Iso.symm_hom,
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv, eqToIso.hom,
    conjugateEquiv_eqToHom_pullbackModules _ _ D.comm, conjugateEquiv_leftAdjointCompIso_hom]
  exact Category.assoc _ _ _

omit [X.J.HasSheafCompose (forget RingCat.{w})] in
/-- Pullback along equal four-field morphisms, on a morphism. -/
theorem pullbackModules_map_eq_of_eq {A : RingedTopos.{v, u, w}} {B : RingedTopos.{v', u', w}}
    [A.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{w})]
    [A.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [B.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [A.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [B.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [HasWeakSheafify A.J AddCommGrpCat.{w}] [A.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (g₁ g₂ : Stacks.Sheaves.RingedToposModules.RingedToposHom A B) (h : g₁ = g₂)
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)} (φ : M ⟶ N) :
    (pullbackModules g₂).map φ =
      eqToHom (congrArg (fun g => (pullbackModules g).obj M) h.symm) ≫ (pullbackModules g₁).map φ ≫
        eqToHom (congrArg (fun g => (pullbackModules g).obj N) h.symm).symm := by
  subst h
  simp

omit [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- The bridge of the two units of `i^* ⊣ i_*` at the square-zero ideal. -/
theorem unit_viaComparison_comp_eqToHom_ideal :
    i.pullbackAdjPushforwardModulesViaComparison.unit.app hi.idealOfThickening.I ≫
        (RingedToposHom.pushforwardModules i).map (eqToHom (congrArg
          (fun g => (pullbackModules g).obj hi.idealOfThickening.I)
          i.toModulesHom_eq_toRingedToposModulesHom.symm)) =
      (RingedToposHom.pullbackAdjPushforwardModules i).unit.app hi.idealOfThickening.I :=
  unit_viaComparison_comp_eqToHom i _

omit [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] [HasWeakSheafify S.J AddCommGrpCat.{wS}]
  [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}] [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- The pullbacks along the two four-field readings of `i`, on a map into the ideal. -/
theorem pullbackModules_map_ideal
    (φ : (pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I ⟶ hi.idealOfThickening.I) :
    (pullbackModules i.toRingedToposModulesHom).map φ =
      eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom.symm) ≫
        (pullbackModules i.toModulesHom).map φ ≫
        eqToHom (congrArg (fun g => (pullbackModules g).obj hi.idealOfThickening.I)
          i.toModulesHom_eq_toRingedToposModulesHom.symm).symm :=
  pullbackModules_map_eq_of_eq _ _ i.toModulesHom_eq_toRingedToposModulesHom φ

omit [X.J.HasSheafCompose (forget RingCat.{w})] in
/-- A transpose followed by a map through the inverse isomorphism. -/
theorem homEquiv_comp_map_hom_comp {𝒞' 𝒟' : Type*} [Category 𝒞'] [Category 𝒟'] {L : 𝒟' ⥤ 𝒞'}
    {R : 𝒞' ⥤ 𝒟'} (aT : L ⊣ R) {P : 𝒟'} {E Q Z : 𝒞'} (e : L.obj P ⟶ Q) (A : E ≅ Q)
    (y : Q ⟶ Z) :
    aT.homEquiv P E (e ≫ A.inv) ≫ R.map (A.hom ≫ y) = aT.homEquiv P Z (e ≫ y) := by
  rw [← Adjunction.homEquiv_naturality_right, Category.assoc, Iso.inv_hom_id_assoc]

omit [HasSheafify X'.J AddCommGrpCat.{w}] in
include comm in
/-- The reduction followed by the direct image of a map out of `f^*𝒥 = i^*(f')^*𝒥`. -/
theorem basePullbackIdealReduction_comp_map {Z : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (y : (pullbackModules i.toRingedToposModulesHom).obj
      ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I) ⟶ Z) :
    (RingedToposHom.pullbackAdjPushforwardModules i).homEquiv _ _
        (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i t f f' hi ht comm).inv) ≫
        (RingedToposHom.pushforwardModules i).map
          ((basePullbackIdealIsoPullback i t f f' hi ht comm).hom ≫ y) =
      (RingedToposHom.pullbackAdjPushforwardModules i).homEquiv _ _
        (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫ y) :=
  homEquiv_comp_map_hom_comp _ _ _ _

omit [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] [HasWeakSheafify S.J AddCommGrpCat.{wS}]
  [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}] [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- The transpose of `i^*(f')^*𝒥 ⟶ i^*I` followed by the inverse of the unit at `I`. -/
theorem homEquiv_map_comp_inv_unit
    (φ : (pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I ⟶ hi.idealOfThickening.I) :
    (RingedToposHom.pullbackAdjPushforwardModules i).homEquiv _ _
        (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (pullbackModules i.toRingedToposModulesHom).map φ) ≫
        (@asIso _ _ _ _ _ (isIso_unit_app_ideal i hi)).inv = φ := by
  rw [Adjunction.homEquiv_unit, pullbackModules_map_ideal, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [Adjunction.unit_naturality_assoc,
    ← unit_viaComparison_comp_eqToHom_ideal, Category.assoc, ← Functor.map_comp_assoc,
    eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, asIso_inv,
    IsIso.hom_inv_id,
    Category.comp_id]

include comm in
/-- The identification `f^*𝒥 = I` read over `O'`: the direct image of `f^*𝒥 = i^*(f')^*𝒥 ⟶ i^*I`
followed by the inverse of the unit at `I`. -/
theorem restrictScalars_map_basePullbackIdealIsoIdeal_hom (hf' : f'.IsFlat)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict) :
    (SheafOfModules.restrictScalars (structureRingMap i)).map
        (basePullbackIdealIsoIdeal i t f f' hi ht comm hf' hstrict).hom =
      i.pushforwardModules.map ((basePullbackIdealIsoPullback i t f f' hi ht comm).hom ≫
        (pullbackModules i.toRingedToposModulesHom).map
          (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap) ≫
        (@asIso _ _ _ _ _ (isIso_unit_app_ideal i hi)).inv :=
  hi.restrictScalarsFullyFaithful.map_preimage _

include comm in
/-- **The identification `f^*𝒥 = I` of Situation 08VV is the map of defining ideals of
Stacks 08M7 on generators**: after the reduction `(f')^*𝒥 ⟶ i_*f^*𝒥` it is the canonical map
`(f')^*𝒥 ⟶ I`. -/
theorem basePullbackIdealReduction_comp_basePullbackIdealIsoIdeal (hf' : f'.IsFlat)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict) :
    (RingedToposHom.pullbackAdjPushforwardModules i).homEquiv _ _
        (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i t f f' hi ht comm).inv) ≫
        (SheafOfModules.restrictScalars (structureRingMap i)).map
          (basePullbackIdealIsoIdeal i t f f' hi ht comm hf' hstrict).hom =
      (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap := by
  rw [restrictScalars_map_basePullbackIdealIsoIdeal_hom]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (basePullbackIdealReduction_comp_map i t f f' hi ht comm _)).trans
      (homEquiv_map_comp_inv_unit (i := i) (f' := f') (hi := hi) (ht := ht)
        (φ := (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap)))

end Deformation.ToposThickening
