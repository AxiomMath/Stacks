module

public import StacksFrontier.AlgebraicGeometry.Descent.BigHVectFlatDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitDescentTransfer
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageComparison
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStagePseudococone
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPullbackComp
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleFibration
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectEssSurj
public import StacksFrontier.CategoryTheory.Sites.Descent.RestrictedBaseDescentData

/-!
# Condition (2) of Stacks 0EX9 for the stack of Stacks Tag 0EXE
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

example (U : BigHOver B S hS) :
    ((bigHVectPseudofunctor B S hS).obj (.mk (op U)) : Type _) =
      ((BigHOver.toScheme B S hS).obj U).Vect := rfl

example {U V : BigHOver B S hS} (g : V ⟶ U) :
    ((bigHVectPseudofunctor B S hS).map g.op.toLoc).toFunctor =
      Scheme.Vect.pullback ((BigHOver.toScheme B S hS).map g) := rfl

include hpS in
example {U V : BigHOver B S hS} (g : V ⟶ U) :
    ((frobeniusVectorBundlePseudofunctor B S hS p hpS).map g.op.toLoc).toFunctor =
      frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map g)
        (isInCharacteristic_bigHOver B S hS p hpS V)
        (isInCharacteristic_bigHOver B S hS p hpS U) := rfl

/-- The composition comparison of `U ↦ Vect(U)` at `g` and `h`, evaluated at a vector bundle,
is the inverse of the comparison `Scheme.Vect.pullbackComp` for the underlying morphisms. -/
lemma bigHVectPseudofunctor_mapComp_hom_app {U V W : BigHOver B S hS} (g : V ⟶ U) (h : W ⟶ V)
    (M : (bigHVectPseudofunctor B S hS).obj (.mk (op U))) :
    ((bigHVectPseudofunctor B S hS).mapComp g.op.toLoc h.op.toLoc).hom.toNatTrans.app M =
      ((Scheme.Vect.pullbackComp ((BigHOver.toScheme B S hS).map h)
        ((BigHOver.toScheme B S hS).map g)).inv.app M) :=
  ObjectProperty.hom_ext _ (Category.id_comp _)

/-- The identity comparison of `U ↦ Vect(U)` at `U`, evaluated at a vector bundle, is the
comparison `Scheme.Vect.pullbackId`. -/
lemma bigHVectPseudofunctor_mapId_hom_app (U : BigHOver B S hS)
    (M : (bigHVectPseudofunctor B S hS).obj (.mk (op U))) :
    ((bigHVectPseudofunctor B S hS).mapId (.mk (op U))).hom.toNatTrans.app M =
      (Scheme.Vect.pullbackId ((BigHOver.toScheme B S hS).obj U)).hom.app M :=
  ObjectProperty.hom_ext _ (Category.id_comp _)

/-- **The Frobenius comparison at the identity.** -/
lemma frobeniusModulesPullbackIso_id_hom_app (X : Scheme.{u}) (hX : IsInCharacteristic X p)
    (M : X.Modules) :
    (frobeniusModulesPullbackIso (𝟙 X) p hX hX).hom.app M =
      (Scheme.Modules.pullbackId X).hom.app _ ≫
        (Scheme.Modules.pullback (absoluteFrobenius X p hX)).map
          ((Scheme.Modules.pullbackId X).inv.app M) := by
  have h₁ := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality
    (absoluteFrobenius X p hX)) M
  have h₂ := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality
    (absoluteFrobenius X p hX)) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app, eqToHom_app] at h₁ h₂
  simp only [frobeniusModulesPullbackIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app]
  have k₁ := congrArg (fun t ↦ (Scheme.Modules.pullbackComp (𝟙 X)
    (absoluteFrobenius X p hX)).hom.app M ≫ t) h₁
  have k₂ := congrArg (fun t ↦ (Scheme.Modules.pullbackComp (absoluteFrobenius X p hX)
    (𝟙 X)).hom.app M ≫ t) h₂
  simp only [Iso.hom_inv_id_app_assoc] at k₁ k₂
  have k₁' := (Category.comp_id _).symm.trans k₁
  have h₂' := (congrArg (fun t ↦ (Scheme.Modules.pullbackComp (absoluteFrobenius X p hX)
    (𝟙 X)).inv.app M ≫ t) (Category.comp_id _)).symm.trans h₂
  rw [← cancel_mono ((Scheme.Modules.pullback (absoluteFrobenius X p hX)).map
      ((Scheme.Modules.pullbackId X).hom.app M))]
  simp only [Category.assoc]
  rw [h₂', ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, eqToHom_trans]
  exact (k₁'.symm.trans (Category.comp_id _).symm)

/-- **The Frobenius comparison at the identity**, in inverse form: the inverse of the comparison
for `𝟙 X` at `N`, followed by `pullbackId` at `F^* N`, is the Frobenius pullback of
`pullbackId` at `N`. -/
lemma frobeniusModulesPullbackIso_id_inv_comp (X : Scheme.{u}) (hX : IsInCharacteristic X p)
    (N : X.Modules) :
    (frobeniusModulesPullbackIso (𝟙 X) p hX hX).inv.app N ≫
        (Scheme.Modules.pullbackId X).hom.app
          ((Scheme.Modules.pullback (absoluteFrobenius X p hX)).obj N) =
      (Scheme.Modules.pullback (absoluteFrobenius X p hX)).map
        ((Scheme.Modules.pullbackId X).hom.app N) := by
  refine (Iso.inv_comp_eq ((frobeniusModulesPullbackIso (𝟙 X) p hX hX).app N)).2 ?_
  rw [Iso.app_hom, frobeniusModulesPullbackIso_id_hom_app]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

/-- **The Frobenius comparison of vector bundles at the identity.** -/
lemma frobeniusVectPullbackIso_id_inv_comp (X : Scheme.{u}) (hX : IsInCharacteristic X p)
    (M : X.Vect) :
    (frobeniusVectPullbackIso (𝟙 X) p hX hX).inv.app M ≫
        (Scheme.Vect.pullbackId X).hom.app ((frobeniusPullback X p hX).obj M) =
      (frobeniusPullback X p hX).map ((Scheme.Vect.pullbackId X).hom.app M) :=
  ObjectProperty.hom_ext _ (frobeniusModulesPullbackIso_id_inv_comp p X hX M.obj)

/-- **The Frobenius comparison of vector bundles is compatible with composition**, in the form of
inverses evaluated at an object. -/
lemma frobeniusVectPullbackIso_comp_inv_app {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (hZ : IsInCharacteristic Z p)
    (M : Z.Vect) :
    (frobeniusVectPullbackIso (g ≫ h) p hX hZ).inv.app M ≫
        (Scheme.Vect.pullbackComp g h).inv.app ((frobeniusPullback Z p hZ).obj M) =
      (frobeniusPullback X p hX).map ((Scheme.Vect.pullbackComp g h).inv.app M) ≫
        (frobeniusVectPullbackIso g p hX hY).inv.app ((Scheme.Vect.pullback h).obj M) ≫
        (Scheme.Vect.pullback g).map ((frobeniusVectPullbackIso h p hY hZ).inv.app M) := by
  simpa using NatTrans.congr_app (congrArg Iso.inv (frobeniusVectPullbackIso_comp p hX hY hZ g h)) M

include hpS in
/-- **The Frobenius pullback, as an endo-transformation of `U ↦ Vect(U)`.** -/
def bigHFrobeniusVectTrans : (bigHVectPseudofunctor B S hS).StrongTrans
    (bigHVectPseudofunctor B S hS) :=
  Pseudofunctor.catStrongTransOfIsLocallyDiscrete _ _
    (fun a ↦ frobeniusPullback ((BigHOver.toScheme B S hS).obj a.as.unop) p
      (isInCharacteristic_bigHOver B S hS p hpS a.as.unop))
    (fun {a b} f ↦ (frobeniusVectPullbackIso ((BigHOver.toScheme B S hS).map f.as.unop) p
      (isInCharacteristic_bigHOver B S hS p hpS b.as.unop)
      (isInCharacteristic_bigHOver B S hS p hpS a.as.unop)).symm)
    (fun a M ↦ by
      obtain ⟨⟨U⟩⟩ := a
      rw [bigHVectPseudofunctor_mapId_hom_app, bigHVectPseudofunctor_mapId_hom_app]
      exact frobeniusVectPullbackIso_id_inv_comp p _ _ M)
    (fun {a b c} f g M ↦ by
      obtain ⟨⟨U⟩⟩ := a
      obtain ⟨⟨V⟩⟩ := b
      obtain ⟨⟨W⟩⟩ := c
      obtain ⟨⟨f⟩⟩ := f
      obtain ⟨⟨g⟩⟩ := g
      have e₁ := bigHVectPseudofunctor_mapComp_hom_app B S hS (U := U) (V := V) (W := W) f g
        ((frobeniusPullback ((BigHOver.toScheme B S hS).obj U) p
          (isInCharacteristic_bigHOver B S hS p hpS U)).obj M)
      have e₂ := bigHVectPseudofunctor_mapComp_hom_app B S hS (U := U) (V := V) (W := W) f g M
      have key := frobeniusVectPullbackIso_comp_inv_app p ((BigHOver.toScheme B S hS).map g)
        ((BigHOver.toScheme B S hS).map f) (isInCharacteristic_bigHOver B S hS p hpS W)
        (isInCharacteristic_bigHOver B S hS p hpS V) (isInCharacteristic_bigHOver B S hS p hpS U) M
      exact (congrArg (fun t ↦ _ ≫ t) e₁).trans (key.trans
        (congrArg (fun t ↦ (frobeniusPullback _ p _).map t ≫ _) e₂).symm))


/-- **The two contractions through an identity of sheaves of rings, read at a site functor equal
to the identity**, compared with Mathlib's `CategoryTheory.SheafOfModules.pullbackId`.  All the
data is a parameter, so that the equations identifying the site functor and the two morphisms with
identities may be substituted. -/
lemma _root_.Stacks.SheafOfModules.pullbackComp_id_trans_eqToHom_trans_id_comp
    {C : Type*} [Category C] {J : GrothendieckTopology C} {S R : Sheaf J RingCat.{u}}
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : C ⥤ C) [Functor.IsContinuous F J J] [Functor.IsContinuous (F ⋙ F) J J]
    (hF : F = 𝟭 C)
    (ι : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J J).obj R)
    (c : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J J).obj R)
    (ρ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J J).obj S)
    {_ : (_root_.SheafOfModules.pushforward.{u} ι).IsRightAdjoint}
    {_ : (_root_.SheafOfModules.pushforward.{u} c).IsRightAdjoint}
    {_ : (_root_.SheafOfModules.pushforward.{u} ρ).IsRightAdjoint}
    (hc : HEq c (𝟙 R)) (hρ : HEq ρ (𝟙 S))
    (h : _root_.SheafOfModules.pullback.{u} (F := F ⋙ F)
        (ι ≫ (F.sheafPushforwardContinuous RingCat.{u} J J).map c) =
      _root_.SheafOfModules.pullback.{u} (F := F ⋙ F)
        (ρ ≫ (F.sheafPushforwardContinuous RingCat.{u} J J).map ι))
    (hcid : _root_.SheafOfModules.pullback.{u} c = _root_.SheafOfModules.pullback.{u} (F := 𝟭 C)
      (𝟙 R))
    (hρid : _root_.SheafOfModules.pullback.{u} ρ = _root_.SheafOfModules.pullback.{u} (F := 𝟭 C)
      (𝟙 S))
    (θc : _root_.SheafOfModules.pullback.{u} c ⟶ 𝟭 _)
    (hθc : θc = (eqToIso hcid ≪≫ _root_.SheafOfModules.pullbackId.{u} R).hom)
    (θρ : 𝟭 _ ⟶ _root_.SheafOfModules.pullback.{u} ρ)
    (hθρ : θρ = (eqToIso hρid ≪≫ _root_.SheafOfModules.pullbackId.{u} S).inv)
    (N : _root_.SheafOfModules.{u} S) :
    (_root_.SheafOfModules.pullbackComp.{u} ι c).hom.app N ≫ (eqToHom h).app N ≫
        (_root_.SheafOfModules.pullbackComp.{u} ρ ι).inv.app N =
      θc.app ((_root_.SheafOfModules.pullback.{u} ι).obj N) ≫
        (_root_.SheafOfModules.pullback.{u} ι).map (θρ.app N) := by
  subst hθc hθρ
  subst hF
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hρ
  have h₁ := NatTrans.congr_app (congrArg Iso.hom (_root_.SheafOfModules.pullback_comp_id.{u} ι)) N
  have h₂ := NatTrans.congr_app (congrArg Iso.inv (_root_.SheafOfModules.pullback_id_comp.{u} ι)) N
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.id_comp] at h₁ h₂
  have he : (eqToHom h).app N = 𝟙 _ := rfl
  have he₁ : (eqToIso hcid).hom = 𝟙 _ := rfl
  have he₂ : (eqToIso hρid).inv = 𝟙 _ := rfl
  rw [h₁, h₂, he, Iso.trans_hom, Iso.trans_inv, he₁, he₂]
  simp only [Category.comp_id, Category.id_comp]
  exact congrArg (_ ≫ ·) (Category.id_comp _)

/-- **The stage bridge at the identity.** -/
lemma frobeniusStageExtendScalarsPullbackIso_id_hom_app (X : Scheme.{u})
    (hX : IsInCharacteristic X p) (n : ℕ)
    (N : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    (frobeniusStageExtendScalarsPullbackIso p (𝟙 X) hX hX n).hom.app N =
      (frobeniusColimitPullbackId X p hX).hom.app ((frobeniusStageExtendScalars X p hX n).obj N) ≫
        (frobeniusStageExtendScalars X p hX n).map
          ((Scheme.Modules.pullbackId X).inv.app N) := by
  rw [frobeniusStageExtendScalarsPullbackIso_hom_app]
  exact Stacks.SheafOfModules.pullbackComp_id_trans_eqToHom_trans_id_comp
    (TopologicalSpace.Opens.map (𝟙 (X : TopCat))) rfl _ _ _
    (heq_of_eq (frobeniusColimitStructureSheafHom_id X p hX)) HEq.rfl
    (congrArg (fun φ => _root_.SheafOfModules.pullback.{u} φ)
      (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p (𝟙 X) hX hX n))
    (by rw [frobeniusColimitStructureSheafHom_id]; exact rfl) rfl
    _ rfl _ (by rw [Iso.trans_inv]; exact (Category.comp_id _).symm) N

/-- **The stage bridge of vector bundles at the identity**, in the form of the unit coherence of a
strong transformation. -/
lemma frobeniusStageFunctorPullbackIso_id_inv_comp (X : Scheme.{u}) (hX : IsInCharacteristic X p)
    (n : ℕ) (E : X.Vect) :
    (frobeniusStageFunctorPullbackIso p (𝟙 X) hX hX n).inv.app E ≫
        (frobeniusColimitVectorBundlesPullbackId X p hX).hom.app
          ((frobeniusStageFunctor X p hX n).obj E) =
      (frobeniusStageFunctor X p hX n).map ((Scheme.Vect.pullbackId X).hom.app E) := by
  rw [← cancel_epi ((frobeniusStageFunctorPullbackIso p (𝟙 X) hX hX n).hom.app E),
    Iso.hom_inv_id_app_assoc]
  apply ObjectProperty.hom_ext
  have key := frobeniusStageExtendScalarsPullbackIso_id_hom_app p X hX n E.obj
  rw [ObjectProperty.FullSubcategory.comp_hom]
  show _ = (frobeniusStageExtendScalarsPullbackIso p (𝟙 X) hX hX n).hom.app E.obj ≫
    (frobeniusStageExtendScalars X p hX n).map ((Scheme.Modules.pullbackId X).hom.app E.obj)
  rw [key, Category.assoc]
  exact (Category.comp_id _).symm.trans (congrArg (_ ≫ ·)
    (Iso.map_inv_hom_id ((Scheme.Modules.pullbackId X).app E.obj)
      (frobeniusStageExtendScalars X p hX n)).symm)

/-- **The stage bridge of vector bundles is compatible with composition**, in the form of inverses
evaluated at an object. -/
lemma frobeniusStageFunctorPullbackIso_comp_inv_app {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (hZ : IsInCharacteristic Z p)
    (n : ℕ) (E : Z.Vect) :
    (frobeniusStageFunctorPullbackIso p (g ≫ h) hX hZ n).inv.app E ≫
        (frobeniusColimitVectorBundlesPullbackComp p g h hX hY hZ).inv.app
          ((frobeniusStageFunctor Z p hZ n).obj E) =
      (frobeniusStageFunctor X p hX n).map ((Scheme.Vect.pullbackComp g h).inv.app E) ≫
        (frobeniusStageFunctorPullbackIso p g hX hY n).inv.app ((Scheme.Vect.pullback h).obj E) ≫
        (frobeniusColimitVectorBundlesPullback p g hX hY).map
          ((frobeniusStageFunctorPullbackIso p h hY hZ n).inv.app E) := by
  have key := frobeniusStageFunctorPullbackIso_comp p g h hX hY hZ n E
  rw [← cancel_epi ((frobeniusColimitVectorBundlesPullbackComp p g h hX hY hZ).hom.app
      ((frobeniusStageFunctor Z p hZ n).obj E) ≫
    (frobeniusStageFunctorPullbackIso p (g ≫ h) hX hZ n).hom.app E)]
  conv_rhs => rw [key]
  simp

include hpS in
/-- The identity comparison of the pseudofunctor of Stacks Tag 0EXE at `U`, evaluated at an
object, is `frobeniusColimitVectorBundlesPullbackId`. -/
lemma frobeniusVectorBundlePseudofunctor_mapId_hom_app (U : BigHOver B S hS)
    (M : (frobeniusVectorBundlePseudofunctor B S hS p hpS).obj (.mk (op U))) :
    ((frobeniusVectorBundlePseudofunctor B S hS p hpS).mapId (.mk (op U))).hom.toNatTrans.app M =
      (frobeniusColimitVectorBundlesPullbackId ((BigHOver.toScheme B S hS).obj U) p
        (isInCharacteristic_bigHOver B S hS p hpS U)).hom.app M := by
  apply ObjectProperty.hom_ext
  rfl

include hpS in
/-- The composition comparison of the pseudofunctor of Stacks Tag 0EXE at `g` and `h`, evaluated
at an object, is the inverse of `frobeniusColimitVectorBundlesPullbackComp`. -/
lemma frobeniusVectorBundlePseudofunctor_mapComp_hom_app {U V W : BigHOver B S hS} (g : V ⟶ U)
    (h : W ⟶ V) (M : (frobeniusVectorBundlePseudofunctor B S hS p hpS).obj (.mk (op U))) :
    ((frobeniusVectorBundlePseudofunctor B S hS p hpS).mapComp g.op.toLoc
        h.op.toLoc).hom.toNatTrans.app M =
      (frobeniusColimitVectorBundlesPullbackComp p ((BigHOver.toScheme B S hS).map h)
        ((BigHOver.toScheme B S hS).map g) (isInCharacteristic_bigHOver B S hS p hpS W)
        (isInCharacteristic_bigHOver B S hS p hpS V)
        (isInCharacteristic_bigHOver B S hS p hpS U)).inv.app M := by
  apply ObjectProperty.hom_ext
  rfl


include hpS in
/-- `frobeniusVectorBundlePseudofunctor_mapComp_hom_app` for arbitrary composable morphisms
`f`, `g` of `LocallyDiscrete (BigHOver B S hS)ᵒᵖ`. -/
lemma frobeniusVectorBundlePseudofunctor_mapComp_hom_app'
    {a b c : LocallyDiscrete (BigHOver B S hS)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
    (M : (frobeniusVectorBundlePseudofunctor B S hS p hpS).obj a) :
    ((frobeniusVectorBundlePseudofunctor B S hS p hpS).mapComp f g).hom.toNatTrans.app M =
      (frobeniusColimitVectorBundlesPullbackComp p ((BigHOver.toScheme B S hS).map g.as.unop)
        ((BigHOver.toScheme B S hS).map f.as.unop)
        (isInCharacteristic_bigHOver B S hS p hpS c.as.unop)
        (isInCharacteristic_bigHOver B S hS p hpS b.as.unop)
        (isInCharacteristic_bigHOver B S hS p hpS a.as.unop)).inv.app M := by
  apply ObjectProperty.hom_ext
  rfl

/-- `bigHVectPseudofunctor_mapComp_hom_app` for arbitrary composable morphisms `f`, `g` of
`LocallyDiscrete (BigHOver B S hS)ᵒᵖ`. -/
lemma bigHVectPseudofunctor_mapComp_hom_app'
    {a b c : LocallyDiscrete (BigHOver B S hS)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
    (M : (bigHVectPseudofunctor B S hS).obj a) :
    ((bigHVectPseudofunctor B S hS).mapComp f g).hom.toNatTrans.app M =
      ((Scheme.Vect.pullbackComp ((BigHOver.toScheme B S hS).map g.as.unop)
        ((BigHOver.toScheme B S hS).map f.as.unop)).inv.app M) :=
  ObjectProperty.hom_ext _ (Category.id_comp _)

include hpS in
/-- **The stage-`n` extension of scalars, as a strong transformation** from `U ↦ Vect(U)` to the
pseudofunctor of Stacks Tag 0EXE. -/
def bigHStageTrans (n : ℕ) : (bigHVectPseudofunctor B S hS).StrongTrans
    (frobeniusVectorBundlePseudofunctor B S hS p hpS) :=
  Pseudofunctor.catStrongTransOfIsLocallyDiscrete _ _
    (fun a ↦ frobeniusStageFunctor ((BigHOver.toScheme B S hS).obj a.as.unop) p
      (isInCharacteristic_bigHOver B S hS p hpS a.as.unop) n)
    (fun {a b} f ↦ (frobeniusStageFunctorPullbackIso p ((BigHOver.toScheme B S hS).map f.as.unop)
      (isInCharacteristic_bigHOver B S hS p hpS b.as.unop)
      (isInCharacteristic_bigHOver B S hS p hpS a.as.unop) n).symm)
    (fun a M ↦ by
      obtain ⟨⟨U⟩⟩ := a
      rw [bigHVectPseudofunctor_mapId_hom_app, frobeniusVectorBundlePseudofunctor_mapId_hom_app]
      exact frobeniusStageFunctorPullbackIso_id_inv_comp p _ _ n M)
    (fun {a b c} f g M ↦ by
      rw [frobeniusVectorBundlePseudofunctor_mapComp_hom_app',
        bigHVectPseudofunctor_mapComp_hom_app']
      exact frobeniusStageFunctorPullbackIso_comp_inv_app p _ _ _ _ _ n M)

end AlgebraicGeometry

end
