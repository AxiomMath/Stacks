module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer.SquareZeroDescent

/-!
# Fpqc coverings are universal effective epimorphisms

This file proves the forward implication through global sections over the charts `Spec`,
transfers the equalizer condition along affine base change, and proves Stacks 0EUA.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

open scoped ChangeOfRings TensorProduct

namespace SectionsEqualizer

open Stacks.Ample (unitModule)

private lemma pullback_isQuasicoherent_of_isIso {X Y : Scheme.{u}}
    (e : X ≅ Y) (F : Y.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback e.hom).obj F).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback e.hom).app F) inferInstance

private theorem pullbackComp_sectionsMap_injective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Modules) :
    Function.Injective (fun s : Γ((Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pullback g).obj F), ⊤) =>
      ((Scheme.Modules.pullbackComp f g).hom.app F).app ⊤ s) := by
  have h : IsIso ((Scheme.Modules.pullbackComp f g).hom.app F) := inferInstance
  have _ : IsIso (((Scheme.Modules.pullbackComp f g).hom.app F).app ⊤) :=
    (Scheme.Modules.Hom.isIso_iff_isIso_app.mp h) ⊤
  exact (ConcreteCategory.bijective_of_isIso _).1

-- This is the algebraic core of the square-zero argument in the first half of
-- Tag 0EUA.  A compatible family of module elements is embedded in the
-- square-zero extensions of the rings on the cover.  Ring descent produces an
-- element of the square-zero extension of the base; its scalar component
-- vanishes by separatedness of the base ring equalizer, and its module
-- component is the required descended section.
private theorem moduleElement_descends_of_squareZeroRingEqualizer
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    {I : Type w} (S : I → Type u) [∀ i, CommRing (S i)]
    (ρ : ∀ i, R →+* S i)
    (N : I → Type u) [∀ i, AddCommGroup (N i)] [∀ i, Module (S i) (N i)]
    [∀ i, Module (S i)ᵐᵒᵖ (N i)] [∀ i, IsCentralScalar (S i) (N i)]
    (η : ∀ i, M → N i)
    (θ : ∀ i, TrivSqZeroExt R M →+* TrivSqZeroExt (S i) (N i))
    (hθfst : ∀ i a, TrivSqZeroExt.fst (θ i a) = ρ i (TrivSqZeroExt.fst a))
    (hθinr : ∀ i m, θ i (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr (η i m))
    (hbase : ∀ r : R, (∀ i, ρ i r = 0) → r = 0)
    (T : I → I → Type u)
    [∀ i j, CommRing (T i j)]
    (α : ∀ i j, TrivSqZeroExt (S i) (N i) →+* T i j)
    (β : ∀ i j, TrivSqZeroExt (S j) (N j) →+* T i j)
    (heq : ∀ x : ∀ i, TrivSqZeroExt (S i) (N i),
      (∀ i j, α i j (x i) = β i j (x j)) →
      ∃! a : TrivSqZeroExt R M, ∀ i, θ i a = x i)
    (s : ∀ i, N i)
    (hs : ∀ i j,
      α i j (TrivSqZeroExt.inr (s i)) = β i j (TrivSqZeroExt.inr (s j))) :
    ∃! m : M, ∀ i, η i m = s i := by
  obtain ⟨a, ha, huniq⟩ := heq (fun i => TrivSqZeroExt.inr (s i)) hs
  have hfst : ∀ i, ρ i (TrivSqZeroExt.fst a) = 0 := by
    intro i
    have h := congrArg TrivSqZeroExt.fst (ha i)
    simpa [hθfst] using h
  have hfst_zero : TrivSqZeroExt.fst a = 0 := hbase _ hfst
  have ha_inr : a = TrivSqZeroExt.inr a.snd := by
    apply TrivSqZeroExt.ext
    · simp [hfst_zero]
    · rfl
  have hdesc : ∀ i, η i a.snd = s i := by
    intro i
    have h := congrArg TrivSqZeroExt.snd (ha i)
    rw [ha_inr, hθinr] at h
    simpa using h
  refine ⟨a.snd, hdesc, ?_⟩
  intro m hm
  have hm' : ∀ i, θ i (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr (s i) := by
    intro i
    rw [hθinr, hm i]
  have hma := huniq (TrivSqZeroExt.inr m) hm'
  have hma' : TrivSqZeroExt.inr m = TrivSqZeroExt.inr a.snd := hma.trans ha_inr
  exact congrArg TrivSqZeroExt.snd hma'

private theorem quasicoherentSections_unique_of_universalEffectiveEpiFamily
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (h : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f)
    (F : X.obj.Modules) [F.IsQuasicoherent]
    (a b : Γ(F, ⊤))
    (hab : ∀ i, pullbackGlobalSections (f i).hom F a =
      pullbackGlobalSections (f i).hom F b) : a = b := by
  let R := Γ(X.obj, ⊤)
  let eX := X.obj.isoSpec
  let F₀ := (Scheme.Modules.pullback eX.inv).obj F
  let : F₀.IsQuasicoherent := pullback_isQuasicoherent_of_isIso eX.symm F
  let M : ModuleCat R := moduleSpecΓFunctor.obj F₀
  let : Module Rᵐᵒᵖ M :=
    Module.compHom M (RingEquiv.toOpposite R).symm.toRingHom
  let : IsCentralScalar R M := ⟨by intro r x; rfl⟩
  let m : M := pullbackGlobalSections eX.inv F (a - b)
  have hm : ∀ i,
      (1 : Γ((U i).obj, ⊤)) ⊗ₜ[R, (f i).hom.appTop.hom] m = 0 := by
    intro i
    let q := Spec.map (f i).hom.appTop
    let eU := (U i).obj.isoSpec
    have hfi : pullbackGlobalSections (f i).hom F (a - b) = 0 := by
      rw [map_sub, hab i, sub_self]
    have hcomp : pullbackGlobalSections (eU.inv ≫ (f i).hom) F (a - b) = 0 := by
      rw [← pullbackGlobalSections_comp eU.inv (f i).hom F]
      simp [hfi]
    have hcomm : q ≫ eX.inv = eU.inv ≫ (f i).hom :=
      Scheme.isoSpec_inv_naturality (f i).hom
    have hq : pullbackGlobalSections q F₀ m = 0 := by
      apply pullbackComp_sectionsMap_injective q eX.inv F
      have hnat : ((Scheme.Modules.pullbackComp q eX.inv).hom.app F).app ⊤
          (pullbackGlobalSections q F₀ m) =
          pullbackGlobalSections (q ≫ eX.inv) F (a - b) := by
        simpa [m, F₀] using pullbackGlobalSections_comp q eX.inv F (a - b)
      change ((Scheme.Modules.pullbackComp q eX.inv).hom.app F).app ⊤
          (pullbackGlobalSections q F₀ m) =
        ((Scheme.Modules.pullbackComp q eX.inv).hom.app F).app ⊤ 0
      calc
        _ = pullbackGlobalSections (q ≫ eX.inv) F (a - b) := hnat
        _ = 0 := by rw [hcomm]; exact hcomp
        _ = _ := (map_zero _).symm
    have hunit := affinePullbackSectionsIso_unit R Γ((U i).obj, ⊤)
      (f i).hom.appTop F₀ m
    apply (ConcreteCategory.bijective_of_isIso
      (Stacks.Cech.affinePullbackSectionsIso R Γ((U i).obj, ⊤) (f i).hom.appTop F₀).hom).1
    exact hunit.trans (hq.trans (map_zero _).symm)
  have hmzero : m = 0 :=
    tensor_eq_zero_of_universalEffectiveEpiFamily_affine X U f h M m hm
  have habzero : a - b = 0 := by
    refine (pullbackGlobalSections_bijective_of_isIso eX.inv F).1 ?_
    have hz : pullbackGlobalSections eX.inv F (a - b) = 0 := hmzero
    rw [hz, map_zero]
  exact sub_eq_zero.mp habzero

private theorem equalizerCondition_of_equiv
    {I : Type w} {A B : Type u} {C D : I → Type u}
    {E H : I → I → Type u}
    (eA : A ≃ B) (eC : ∀ i, C i ≃ D i) (eE : ∀ i j, E i j ≃ H i j)
    (p : ∀ i, A → C i) (q : ∀ i, B → D i)
    (left : ∀ i j, C i → E i j) (right : ∀ i j, C j → E i j)
    (left' : ∀ i j, D i → H i j) (right' : ∀ i j, D j → H i j)
    (hp : ∀ i a, eC i (p i a) = q i (eA a))
    (hl : ∀ i j c, eE i j (left i j c) = left' i j (eC i c))
    (hr : ∀ i j c, eE i j (right i j c) = right' i j (eC j c))
    (h : ∀ d : ∀ i, D i,
      (∀ i j, left' i j (d i) = right' i j (d j)) →
      ∃! b : B, ∀ i, q i b = d i)
    (c : ∀ i, C i) (hc : ∀ i j, left i j (c i) = right i j (c j)) :
    ∃! a : A, ∀ i, p i a = c i := by
  have hd : ∀ i j, left' i j (eC i (c i)) = right' i j (eC j (c j)) := by
    intro i j
    rw [← hl, ← hr, hc]
  obtain ⟨b, hb, huniq⟩ := h (fun i => eC i (c i)) hd
  refine ⟨eA.symm b, ?_, ?_⟩
  · intro i
    apply (eC i).injective
    rw [hp, eA.apply_symm_apply]
    exact hb i
  · intro a ha
    apply eA.injective
    rw [eA.apply_symm_apply]
    apply huniq
    intro i
    rw [← hp, ha i]

private lemma specMap_tensor_left_comp
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] :
    let P := S ⊗[R] T
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := T))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [← Spec.map_comp]
  congr 1

private lemma specMap_tensor_right_comp
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] :
    let P := S ⊗[R] T
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R T)) =
      Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T)).commutes r


private noncomputable def moduleSectionsEquiv {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) : Γ(F, ⊤) ≃+ Γ(G, ⊤) where
  toFun := e.hom.app ⊤
  invFun := e.inv.app ⊤
  map_add' := map_add _
  left_inv s := by
    change (e.hom ≫ e.inv).app ⊤ s = s
    simp
  right_inv s := by
    change (e.inv ≫ e.hom).app ⊤ s = s
    simp

private noncomputable def isoPullbackSectionsEquiv {X Y : Scheme.{u}}
    (e : X ≅ Y) (F : Y.Modules) :
    Γ(F, ⊤) ≃+ Γ((Scheme.Modules.pullback e.hom).obj F, ⊤) :=
  AddEquiv.ofBijective (pullbackGlobalSections e.hom F).hom
    (pullbackGlobalSections_bijective_of_isIso e.hom F)

private lemma moduleSectionsEquiv_smul {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) (r : Γ(X, ⊤)) (s : Γ(F, ⊤)) :
    moduleSectionsEquiv e (r • s) = r • moduleSectionsEquiv e s :=
  moduleHom_app_smul e.hom r s

private lemma isoPullbackSectionsEquiv_smul {X Y : Scheme.{u}}
    (e : X ≅ Y) (F : Y.Modules) (r : Γ(Y, ⊤)) (s : Γ(F, ⊤)) :
    isoPullbackSectionsEquiv e F (r • s) =
      e.hom.appTop r • isoPullbackSectionsEquiv e F s :=
  pullbackGlobalSections_smul e.hom F r s

private lemma isoPullbackSectionsEquiv_symm_smul {X Y : Scheme.{u}}
    (e : X ≅ Y) (F : Y.Modules) (r : Γ(Y, ⊤))
    (s : Γ((Scheme.Modules.pullback e.hom).obj F, ⊤)) :
    (isoPullbackSectionsEquiv e F).symm (e.hom.appTop r • s) =
      r • (isoPullbackSectionsEquiv e F).symm s := by
  apply (isoPullbackSectionsEquiv e F).injective
  calc
    _ = e.hom.appTop r • s := (isoPullbackSectionsEquiv e F).apply_symm_apply _
    _ = e.hom.appTop r • isoPullbackSectionsEquiv e F
        ((isoPullbackSectionsEquiv e F).symm s) :=
      congrArg (fun z => e.hom.appTop r • z)
        ((isoPullbackSectionsEquiv e F).apply_symm_apply s).symm
    _ = _ := (isoPullbackSectionsEquiv_smul e F r _).symm

private noncomputable def chartPullbackSectionsEquiv
    {X Y X₀ Y₀ : Scheme.{u}} (eX : X₀ ≅ X) (eY : Y₀ ≅ Y)
    (f : Y ⟶ X) (q : Y₀ ⟶ X₀) (hq : q ≫ eX.hom = eY.hom ≫ f)
    (F : X.Modules) :
    Γ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback eX.hom).obj F), ⊤) ≃+
      Γ((Scheme.Modules.pullback f).obj F, ⊤) :=
  (moduleSectionsEquiv ((Scheme.Modules.pullbackComp q eX.hom).app F)).trans
    ((moduleSectionsEquiv ((Scheme.Modules.pullbackCongr hq).app F)).trans
      ((moduleSectionsEquiv ((Scheme.Modules.pullbackComp eY.hom f).symm.app F)).trans
        (isoPullbackSectionsEquiv eY ((Scheme.Modules.pullback f).obj F)).symm))

private lemma chartPullbackSectionsEquiv_global
    {X Y X₀ Y₀ : Scheme.{u}} (eX : X₀ ≅ X) (eY : Y₀ ≅ Y)
    (f : Y ⟶ X) (q : Y₀ ⟶ X₀) (hq : q ≫ eX.hom = eY.hom ≫ f)
    (F : X.Modules) (s : Γ(F, ⊤)) :
    chartPullbackSectionsEquiv eX eY f q hq F
      (pullbackGlobalSections q ((Scheme.Modules.pullback eX.hom).obj F)
        (pullbackGlobalSections eX.hom F s)) = pullbackGlobalSections f F s := by
  apply (isoPullbackSectionsEquiv eY ((Scheme.Modules.pullback f).obj F)).injective
  dsimp only [chartPullbackSectionsEquiv, AddEquiv.trans_apply]
  refine ((isoPullbackSectionsEquiv eY
    ((Scheme.Modules.pullback f).obj F)).apply_symm_apply _).trans ?_
  apply (moduleSectionsEquiv ((Scheme.Modules.pullbackComp eY.hom f).app F)).injective
  change (moduleSectionsEquiv ((Scheme.Modules.pullbackComp eY.hom f).app F))
    ((moduleSectionsEquiv ((Scheme.Modules.pullbackComp eY.hom f).app F)).symm _) = _
  refine ((moduleSectionsEquiv
    ((Scheme.Modules.pullbackComp eY.hom f).app F)).apply_symm_apply _).trans ?_
  change ((Scheme.Modules.pullbackCongr hq).hom.app F).app ⊤
    (((Scheme.Modules.pullbackComp q eX.hom).hom.app F).app ⊤ _) =
    ((Scheme.Modules.pullbackComp eY.hom f).hom.app F).app ⊤
      (pullbackGlobalSections eY.hom ((Scheme.Modules.pullback f).obj F)
        (pullbackGlobalSections f F s))
  exact (congrArg (fun z => ((Scheme.Modules.pullbackCongr hq).hom.app F).app ⊤ z)
    (pullbackGlobalSections_comp q eX.hom F s)).trans
      ((pullbackGlobalSections_congr hq F s).trans
        (pullbackGlobalSections_comp eY.hom f F s).symm)

private lemma chartPullbackSectionsEquiv_smul
    {X Y X₀ Y₀ : Scheme.{u}} (eX : X₀ ≅ X) (eY : Y₀ ≅ Y)
    (f : Y ⟶ X) (q : Y₀ ⟶ X₀) (hq : q ≫ eX.hom = eY.hom ≫ f)
    (F : X.Modules) (r : Γ(Y, ⊤))
    (s : Γ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback eX.hom).obj F), ⊤)) :
    chartPullbackSectionsEquiv eX eY f q hq F (eY.hom.appTop r • s) =
      r • chartPullbackSectionsEquiv eX eY f q hq F s := by
  let c₁ := moduleSectionsEquiv ((Scheme.Modules.pullbackComp q eX.hom).app F)
  let c₂ := moduleSectionsEquiv ((Scheme.Modules.pullbackCongr hq).app F)
  let c₃ := moduleSectionsEquiv ((Scheme.Modules.pullbackComp eY.hom f).symm.app F)
  let c₄ := isoPullbackSectionsEquiv eY ((Scheme.Modules.pullback f).obj F)
  change c₄.symm (c₃ (c₂ (c₁ (eY.hom.appTop r • s)))) =
    r • c₄.symm (c₃ (c₂ (c₁ s)))
  calc
    _ = c₄.symm (c₃ (c₂ (eY.hom.appTop r • c₁ s))) :=
      congrArg (fun z => c₄.symm (c₃ (c₂ z)))
        (moduleSectionsEquiv_smul ((Scheme.Modules.pullbackComp q eX.hom).app F) _ s)
    _ = c₄.symm (c₃ (eY.hom.appTop r • c₂ (c₁ s))) :=
      congrArg (fun z => c₄.symm (c₃ z))
        (moduleSectionsEquiv_smul ((Scheme.Modules.pullbackCongr hq).app F) _ (c₁ s))
    _ = c₄.symm (eY.hom.appTop r • c₃ (c₂ (c₁ s))) :=
      congrArg c₄.symm
        (moduleSectionsEquiv_smul ((Scheme.Modules.pullbackComp eY.hom f).symm.app F)
          _ (c₂ (c₁ s)))
    _ = _ := isoPullbackSectionsEquiv_symm_smul eY ((Scheme.Modules.pullback f).obj F) r _

private noncomputable def tensorChartSectionsEquiv
    {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
    (eX : Spec R ≅ X) (eY : Spec S ≅ Y) (f : Y ⟶ X)
    (ρ : R ⟶ S) (hρ : Spec.map ρ ≫ eX.hom = eY.hom ≫ f)
    (F : X.Modules) [((Scheme.Modules.pullback eX.hom).obj F).IsQuasicoherent] :
    (ModuleCat.extendScalars ρ.hom).obj
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback eX.hom).obj F)) ≃+
      Γ((Scheme.Modules.pullback f).obj F, ⊤) :=
  (AddEquiv.ofBijective (Stacks.Cech.affinePullbackSectionsIso R S ρ
      ((Scheme.Modules.pullback eX.hom).obj F)).hom.hom.toAddMonoidHom
    ((ConcreteCategory.isIso_iff_bijective _).mp (inferInstance :
      IsIso (Stacks.Cech.affinePullbackSectionsIso R S ρ
        ((Scheme.Modules.pullback eX.hom).obj F)).hom))).trans
    (chartPullbackSectionsEquiv eX eY f (Spec.map ρ) hρ F)

private lemma tensorChartSectionsEquiv_tmul
    {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
    (eX : Spec R ≅ X) (eY : Spec S ≅ Y) (f : Y ⟶ X)
    (ρ : R ⟶ S) (hρ : Spec.map ρ ≫ eX.hom = eY.hom ≫ f)
    (F : X.Modules) [((Scheme.Modules.pullback eX.hom).obj F).IsQuasicoherent]
    (s : S) (t : Γ(F, ⊤)) :
    tensorChartSectionsEquiv eX eY f ρ hρ F
      (s ⊗ₜ[R, ρ.hom] (pullbackGlobalSections eX.hom F t)) =
      eY.inv.appTop ((Scheme.ΓSpecIso S).inv s) • pullbackGlobalSections f F t := by
  dsimp only [tensorChartSectionsEquiv, AddEquiv.trans_apply, AddEquiv.ofBijective_apply]
  refine (congrArg (fun z => chartPullbackSectionsEquiv eX eY f (Spec.map ρ) hρ F z)
    (affinePullbackSectionsIso_tmul R S ρ ((Scheme.Modules.pullback eX.hom).obj F) s
      (pullbackGlobalSections eX.hom F t))).trans ?_
  change chartPullbackSectionsEquiv eX eY f (Spec.map ρ) hρ F
    ((Scheme.ΓSpecIso S).inv s • _) = _
  have he : eY.hom.appTop (eY.inv.appTop ((Scheme.ΓSpecIso S).inv s)) =
      (Scheme.ΓSpecIso S).inv s := by
    change (eY.hom ≫ eY.inv).appTop _ = _
    simp
  conv_lhs => rw [← he]
  rw [chartPullbackSectionsEquiv_smul, chartPullbackSectionsEquiv_global]

private lemma tensorChartSectionsEquiv_unit
    {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
    (eX : Spec R ≅ X) (eY : Spec S ≅ Y) (f : Y ⟶ X)
    (ρ : R ⟶ S) (hρ : Spec.map ρ ≫ eX.hom = eY.hom ≫ f)
    (F : X.Modules) [((Scheme.Modules.pullback eX.hom).obj F).IsQuasicoherent]
    (t : Γ(F, ⊤)) :
    tensorChartSectionsEquiv eX eY f ρ hρ F
      ((1 : S) ⊗ₜ[R, ρ.hom] (pullbackGlobalSections eX.hom F t)) =
      pullbackGlobalSections f F t := by
  rw [tensorChartSectionsEquiv_tmul]
  simp

private theorem affineSections_induction
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent]
    (P : Γ((Scheme.Modules.pullback f).obj F, ⊤) → Prop)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hgen : ∀ (s : Γ(Y, ⊤)) (m : Γ(F, ⊤)), P (s • pullbackGlobalSections f F m))
    (x : Γ((Scheme.Modules.pullback f).obj F, ⊤)) : P x := by
  let : ((Scheme.Modules.pullback X.isoSpec.symm.hom).obj F).IsQuasicoherent :=
    pullback_isQuasicoherent_of_isIso X.isoSpec.symm F
  let e := tensorChartSectionsEquiv X.isoSpec.symm Y.isoSpec.symm f f.appTop
    (Scheme.isoSpec_inv_naturality f) F
  obtain ⟨z, rfl⟩ := e.surjective x
  let := f.appTop.hom.toAlgebra
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => exact (congrArg P (map_add e a b)).mpr (hadd _ _ ha hb)
  | tmul s m =>
    obtain ⟨t, rfl⟩ := (pullbackGlobalSections_bijective_of_isIso X.isoSpec.inv F).2 m
    dsimp only [e]
    exact (congrArg P (tensorChartSectionsEquiv_tmul X.isoSpec.symm Y.isoSpec.symm f f.appTop
      (Scheme.isoSpec_inv_naturality f) F s t)).mpr (hgen _ _)

private lemma chartCoefficient_naturality
    {Y Z : Scheme.{u}} {S T : CommRingCat.{u}}
    (eY : Spec S ≅ Y) (eZ : Spec T ≅ Z) (a : Z ⟶ Y) (α : S ⟶ T)
    (ha : eZ.hom ≫ a = Spec.map α ≫ eY.hom) (s : S) :
    a.appTop (eY.inv.appTop ((Scheme.ΓSpecIso S).inv s)) =
      eZ.inv.appTop ((Scheme.ΓSpecIso T).inv (α s)) := by
  have hcomp : a ≫ eY.inv = eZ.inv ≫ Spec.map α := by
    rw [← cancel_epi eZ.hom]
    simp only [← Category.assoc, ha]
    simp
  change (a ≫ eY.inv).appTop ((Scheme.ΓSpecIso S).inv s) = _
  rw [hcomp, Scheme.Hom.comp_appTop]
  change eZ.inv.appTop ((Spec.map α).appTop ((Scheme.ΓSpecIso S).inv s)) = _
  rw [specMap_appTop_ΓSpecIso_inv]

private noncomputable def tensorExtendScalarsEquiv (R S : CommRingCat.{u}) [Algebra R S]
    (M : ModuleCat R) : S ⊗[R] M ≃+ (ModuleCat.extendScalars (algebraMap R S)).obj M := by
  let e : S ≃ₗ[R] (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) :=
    { toFun := fun s => s
      invFun := fun s => s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r s => Algebra.smul_def r s }
  exact (TensorProduct.congr e (LinearEquiv.refl R M)).toAddEquiv

private lemma tensorExtendScalarsEquiv_tmul (R S : CommRingCat.{u}) [Algebra R S]
    (M : ModuleCat R) (s : S) (m : M) :
    tensorExtendScalarsEquiv R S M (s ⊗ₜ[R] m) = s ⊗ₜ[R, algebraMap R S] m :=
  rfl

private noncomputable def tensorChartSectionsAlgEquiv
    {X Y : Scheme.{u}} {R S : CommRingCat.{u}} [Algebra R S]
    (eX : Spec R ≅ X) (eY : Spec S ≅ Y) (f : Y ⟶ X)
    (hρ : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ eX.hom = eY.hom ≫ f)
    (F : X.Modules) [((Scheme.Modules.pullback eX.hom).obj F).IsQuasicoherent] :
    S ⊗[R] (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback eX.hom).obj F)) ≃+
      Γ((Scheme.Modules.pullback f).obj F, ⊤) :=
  (tensorExtendScalarsEquiv R S _).trans
    (tensorChartSectionsEquiv eX eY f (CommRingCat.ofHom (algebraMap R S)) hρ F)

private lemma tensorChartSectionsAlgEquiv_tmul
    {X Y : Scheme.{u}} {R S : CommRingCat.{u}} [Algebra R S]
    (eX : Spec R ≅ X) (eY : Spec S ≅ Y) (f : Y ⟶ X)
    (hρ : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ eX.hom = eY.hom ≫ f)
    (F : X.Modules) [((Scheme.Modules.pullback eX.hom).obj F).IsQuasicoherent]
    (s : S) (t : Γ(F, ⊤)) :
    tensorChartSectionsAlgEquiv eX eY f hρ F
      (s ⊗ₜ[R] (pullbackGlobalSections eX.hom F t)) =
      eY.inv.appTop ((Scheme.ΓSpecIso S).inv s) • pullbackGlobalSections f F t :=
  tensorChartSectionsEquiv_tmul eX eY f (CommRingCat.ofHom (algebraMap R S)) hρ F s t

private lemma tensorChartSectionsAlgEquiv_unit
    {X Y : Scheme.{u}} {R S : CommRingCat.{u}} [Algebra R S]
    (eX : Spec R ≅ X) (eY : Spec S ≅ Y) (f : Y ⟶ X)
    (hρ : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ eX.hom = eY.hom ≫ f)
    (F : X.Modules) [((Scheme.Modules.pullback eX.hom).obj F).IsQuasicoherent]
    (t : Γ(F, ⊤)) :
    tensorChartSectionsAlgEquiv eX eY f hρ F
      ((1 : S) ⊗ₜ[R] (pullbackGlobalSections eX.hom F t)) =
      pullbackGlobalSections f F t := by
  rw [tensorChartSectionsAlgEquiv_tmul]
  simp

/-- Pullback of sections along a morphism of `Over` objects, applied to a scalar multiple of a
pulled-back global section. -/
private lemma pullbackSectionsMap_smul_global {S : Scheme.{u}} (F : S.Modules)
    {X Y : Over S} (g : X ⟶ Y) (r : Γ(Y.left, ⊤)) (t : Γ(F, ⊤)) :
    pullbackSectionsMap F g (r • pullbackGlobalSections Y.hom F t) =
      g.left.appTop r • pullbackGlobalSections X.hom F t := by
  rw [pullbackSectionsMap_smul, pullbackSectionsMap_global]

private lemma tensorChartSectionsEquiv_naturality
    {X : Scheme.{u}} {Y Z : Over X} (g : Z ⟶ Y)
    (R S T : CommRingCat.{u}) [Algebra R S] [Algebra R T]
    (eX : Spec R ≅ X) (eY : Spec S ≅ Y.left) (eZ : Spec T ≅ Z.left)
    (hY : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ eX.hom = eY.hom ≫ Y.hom)
    (hZ : Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ eX.hom = eZ.hom ≫ Z.hom)
    (α : S →ₐ[R] T) (hg : eZ.hom ≫ g.left = Spec.map (CommRingCat.ofHom α.toRingHom) ≫ eY.hom)
    (F : X.Modules) [((Scheme.Modules.pullback eX.hom).obj F).IsQuasicoherent]
    (z : S ⊗[R] (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback eX.hom).obj F))) :
    tensorChartSectionsAlgEquiv eX eZ Z.hom hZ F
      (TensorProduct.map α.toLinearMap LinearMap.id z) =
      pullbackSectionsMap F g
        (tensorChartSectionsAlgEquiv eX eY Y.hom hY F z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m =>
    obtain ⟨t, rfl⟩ := (pullbackGlobalSections_bijective_of_isIso eX.hom F).2 m
    have hmap : (TensorProduct.map α.toLinearMap LinearMap.id)
        (s ⊗ₜ[R] (pullbackGlobalSections eX.hom F t)) =
        (α s) ⊗ₜ[R] (pullbackGlobalSections eX.hom F t) :=
      TensorProduct.map_tmul α.toLinearMap LinearMap.id s _
    have hL := tensorChartSectionsAlgEquiv_tmul eX eZ Z.hom hZ F (α s) t
    have hR := tensorChartSectionsAlgEquiv_tmul eX eY Y.hom hY F s t
    have hsm := pullbackSectionsMap_smul_global F g
      (eY.inv.appTop ((Scheme.ΓSpecIso S).inv s)) t
    have hc := chartCoefficient_naturality eY eZ g.left
      (CommRingCat.ofHom α.toRingHom) hg s
    exact ((congrArg (fun y => tensorChartSectionsAlgEquiv eX eZ Z.hom hZ F y) hmap).trans
      hL).trans
      (((congrArg (fun y => pullbackSectionsMap F g y) hR).trans hsm).trans
        (congrArg (fun y => y • pullbackGlobalSections Z.hom F t) hc)).symm

/-- The chart identification of pullback sections carries the left inclusion of a tensor
product of coordinate rings to the pullback map along the corresponding projection. -/
private lemma tensorChartSectionsAlgEquiv_pairLeft
    {X : Scheme.{u}} {W Y : Over X} (a : W ⟶ Y)
    (R A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
    (eX : Spec R ≅ X) (eY : Spec A ≅ Y.left)
    (eW : Spec (CommRingCat.of (A ⊗[R] B)) ≅ W.left)
    (hY : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ eX.hom = eY.hom ≫ Y.hom)
    (hW : Spec.map (CommRingCat.ofHom
        (algebraMap R (CommRingCat.of (A ⊗[R] B)))) ≫ eX.hom = eW.hom ≫ W.hom)
    (hg : eW.hom ≫ a.left = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := B)).toRingHom) ≫
        eY.hom)
    (F : X.Modules) [((Scheme.Modules.pullback eX.hom).obj F).IsQuasicoherent]
    (z : A ⊗[R] (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback eX.hom).obj F))) :
    tensorChartSectionsAlgEquiv eX eW W.hom hW F
        (tensorPairLeft R A B
          (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback eX.hom).obj F)) z) =
      pullbackSectionsMap F a (tensorChartSectionsAlgEquiv eX eY Y.hom hY F z) :=
  tensorChartSectionsEquiv_naturality a R A (CommRingCat.of (A ⊗[R] B)) eX eY eW hY hW
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := B)) hg F z

/-- The chart identification of pullback sections carries the right inclusion of a tensor
product of coordinate rings to the pullback map along the corresponding projection. -/
private lemma tensorChartSectionsAlgEquiv_pairRight
    {X : Scheme.{u}} {W Y : Over X} (b : W ⟶ Y)
    (R A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
    (eX : Spec R ≅ X) (eY : Spec B ≅ Y.left)
    (eW : Spec (CommRingCat.of (A ⊗[R] B)) ≅ W.left)
    (hY : Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ eX.hom = eY.hom ≫ Y.hom)
    (hW : Spec.map (CommRingCat.ofHom
        (algebraMap R (CommRingCat.of (A ⊗[R] B)))) ≫ eX.hom = eW.hom ≫ W.hom)
    (hg : eW.hom ≫ b.left = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom) ≫ eY.hom)
    (F : X.Modules) [((Scheme.Modules.pullback eX.hom).obj F).IsQuasicoherent]
    (z : B ⊗[R] (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback eX.hom).obj F))) :
    tensorChartSectionsAlgEquiv eX eW W.hom hW F
        (tensorPairRight R A B
          (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback eX.hom).obj F)) z) =
      pullbackSectionsMap F b (tensorChartSectionsAlgEquiv eX eY Y.hom hY F z) :=
  tensorChartSectionsEquiv_naturality b R B (CommRingCat.of (A ⊗[R] B)) eX eY eW hY hW
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)) hg F z

/-- Two elements of the chart-level tensor products have the same image under the two
inclusions into the tensor product of the two coordinate rings as soon as their sections agree
after the two pullback maps. -/
private lemma tensorPair_eq_of_sections_eq
    {X : Scheme.{u}} {W Y Z : Over X} (a : W ⟶ Y) (b : W ⟶ Z)
    (R A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
    (eX : Spec R ≅ X) (eY : Spec A ≅ Y.left) (eZ : Spec B ≅ Z.left)
    (eW : Spec (CommRingCat.of (A ⊗[R] B)) ≅ W.left)
    (hY : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ eX.hom = eY.hom ≫ Y.hom)
    (hZ : Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ eX.hom = eZ.hom ≫ Z.hom)
    (hW : Spec.map (CommRingCat.ofHom
        (algebraMap R (CommRingCat.of (A ⊗[R] B)))) ≫ eX.hom = eW.hom ≫ W.hom)
    (F : X.Modules) [((Scheme.Modules.pullback eX.hom).obj F).IsQuasicoherent]
    (u : A ⊗[R] (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback eX.hom).obj F)) ≃+
      Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤))
    (v : B ⊗[R] (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback eX.hom).obj F)) ≃+
      Γ((Scheme.Modules.pullback Z.hom).obj F, ⊤))
    (hu : u = tensorChartSectionsAlgEquiv eX eY Y.hom hY F)
    (hv : v = tensorChartSectionsAlgEquiv eX eZ Z.hom hZ F)
    (x : A ⊗[R] (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback eX.hom).obj F)))
    (y : B ⊗[R] (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback eX.hom).obj F)))
    (sa : Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤))
    (sb : Γ((Scheme.Modules.pullback Z.hom).obj F, ⊤))
    (hsa : u x = sa) (hsb : v y = sb)
    (hga : eW.hom ≫ a.left = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := B)).toRingHom) ≫
        eY.hom)
    (hgb : eW.hom ≫ b.left = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom) ≫ eZ.hom)
    (hxy : pullbackSectionsMap F a sa = pullbackSectionsMap F b sb) :
    tensorPairLeft R A B
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback eX.hom).obj F)) x =
      tensorPairRight R A B
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback eX.hom).obj F)) y := by
  subst hu
  subst hv
  exact (tensorChartSectionsAlgEquiv eX eW W.hom hW F).injective
    ((tensorChartSectionsAlgEquiv_pairLeft a R A B eX eY eW hY hW hga F x).trans
      (((congrArg (fun v => pullbackSectionsMap F a v) hsa).trans
        (hxy.trans (congrArg (fun v => pullbackSectionsMap F b v) hsb).symm)).trans
          (tensorChartSectionsAlgEquiv_pairRight b R A B eX eZ eW hZ hW hgb F y).symm))

private lemma pullbackSectionsMap_comp_apply {X : Scheme.{u}} (F : X.Modules)
    {A B C : Over X} (f : A ⟶ B) (g : B ⟶ C)
    (s : Γ((Scheme.Modules.pullback C.hom).obj F, ⊤)) :
    pullbackSectionsMap F f (pullbackSectionsMap F g s) =
      pullbackSectionsMap F (f ≫ g) s := by
  have h := (quasiCoherentPresheafConstruction X F).functor.map_comp g.op f.op
  exact congrArg (fun k => k s) h.symm

private lemma compatibleSections_cone
    {I : Type w} {X : AffineScheme.{u}} {U : I → AffineScheme.{u}}
    {f : ∀ i, U i ⟶ X} (F : X.obj.Modules)
    (s : ∀ i, Γ((Scheme.Modules.pullback (affineOver X U f i).hom).obj F, ⊤))
    (hs : ∀ i j, pullbackSectionsMap F (pairwiseFst X U f i j) (s i) =
      pullbackSectionsMap F (pairwiseSnd X U f i j) (s j))
    (i j : I) (Z : Over X.obj) (a : Z ⟶ affineOver X U f i)
    (b : Z ⟶ affineOver X U f j) :
    pullbackSectionsMap F a (s i) = pullbackSectionsMap F b (s j) := by
  let l : Z ⟶ pairwiseOver X U f i j := Over.homMk
    (pullback.lift a.left b.left ((Over.w a).trans (Over.w b).symm))
    (by
      change (pullback.lift a.left b.left _) ≫ (pullback.fst _ _ ≫ (f i).hom) = Z.hom
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ (f i).hom)
          (pullback.lift_fst a.left b.left _))).trans (Over.w a))
  have ha : l ≫ pairwiseFst X U f i j = a := by
    ext
    exact pullback.lift_fst _ _ _
  have hb : l ≫ pairwiseSnd X U f i j = b := by
    ext
    exact pullback.lift_snd _ _ _
  exact ((congrArg (fun k => pullbackSectionsMap F k (s i)) ha).symm.trans
    ((pullbackSectionsMap_comp_apply F l (pairwiseFst X U f i j) (s i)).symm.trans
      ((congrArg (fun y => pullbackSectionsMap F l y) (hs i j)).trans
        (pullbackSectionsMap_comp_apply F l (pairwiseSnd X U f i j) (s j))))).trans
    (congrArg (fun k => pullbackSectionsMap F k (s j)) hb)

-- Comparing the canonical chart and base-change isomorphisms requires extra reduction.
private theorem quasicoherentSectionsEqualizer_of_isUniversalEffectiveEpiFamily
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (h : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f) :
    IsQuasicoherentSectionsEqualizer X U f := by
  intro F hF s hs
  let R := Γ(X.obj, ⊤)
  let S i := Γ((U i).obj, ⊤)
  let : ∀ i, Algebra R (S i) := fun i => (f i).hom.appTop.hom.toAlgebra
  let eX := X.obj.isoSpec.symm
  let F₀ := (Scheme.Modules.pullback eX.hom).obj F
  let : F₀.IsQuasicoherent := pullback_isQuasicoherent_of_isIso eX F
  let M := moduleSpecΓFunctor.obj F₀
  let : Module Rᵐᵒᵖ M := Module.compHom M (RingEquiv.toOpposite R).symm.toRingHom
  let : IsCentralScalar R M := ⟨by intro r x; rfl⟩
  have hchart : ∀ i, Spec.map (CommRingCat.ofHom (algebraMap R (S i))) ≫ eX.hom =
      ((U i).obj.isoSpec.symm).hom ≫ (affineOver X U f i).hom :=
    fun i => Scheme.isoSpec_inv_naturality (f i).hom
  let e i := tensorChartSectionsAlgEquiv eX (U i).obj.isoSpec.symm
    (affineOver X U f i).hom (hchart i) F
  let z (i) : S i ⊗[R] M := (e i).symm (s i)
  have hz : ∀ i j, tensorPairLeft R (S i) (S j) M (z i) =
      tensorPairRight R (S i) (S j) M (z j) := by
    intro i j
    let P := CommRingCat.of (S i ⊗[R] S j)
    let p : Spec P ⟶ X.obj :=
      Spec.map (CommRingCat.ofHom (algebraMap R P)) ≫ eX.hom
    let W : Over X.obj := Over.mk p
    let a : W ⟶ affineOver X U f i := Over.homMk
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := S i) (B := S j))) ≫ (U i).obj.isoSpec.inv)
      (by
        change (_ ≫ _) ≫ (f i).hom = p
        rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc]
        exact congrArg (fun k => k ≫ eX.hom) (specMap_tensor_left_comp R (S i) (S j)))
    let b : W ⟶ affineOver X U f j := Over.homMk
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := S i) (B := S j)).toRingHom) ≫ (U j).obj.isoSpec.inv)
      (by
        change (_ ≫ _) ≫ (f j).hom = p
        rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc]
        exact congrArg (fun k => k ≫ eX.hom) (specMap_tensor_right_comp R (S i) (S j)))
    have hP : Spec.map (CommRingCat.ofHom (algebraMap R P)) ≫ eX.hom =
        (Iso.refl (Spec P)).hom ≫ W.hom := by simp [W, p]
    exact tensorPair_eq_of_sections_eq a b R (S i) (S j) eX
      (U i).obj.isoSpec.symm (U j).obj.isoSpec.symm (Iso.refl _)
      (hchart i) (hchart j) hP F (e i) (e j) rfl rfl (z i) (z j) (s i) (s j)
      ((e i).apply_symm_apply (s i)) ((e j).apply_symm_apply (s j))
      (by dsimp [a]; simp only [Category.id_comp]; rfl)
      (by dsimp [b]; simp only [Category.id_comp]; rfl)
      (compatibleSections_cone F s hs i j W a b)
  obtain ⟨m, hm, _⟩ := tensorElements_descend_of_universalEffectiveEpiFamily_affine
    X U f h M z hz
  obtain ⟨t, ht⟩ := (pullbackGlobalSections_bijective_of_isIso eX.hom F).2 m
  have ht' : ∀ i, pullbackGlobalSections (f i).hom F t = s i := by
    intro i
    have hi := congrArg (e i) (hm i)
    rw [← ht] at hi
    exact (tensorChartSectionsAlgEquiv_unit eX (U i).obj.isoSpec.symm
      (affineOver X U f i).hom (hchart i) F t).symm.trans
        (hi.trans ((e i).apply_symm_apply (s i)))
  exact ⟨t, ht', fun t' ht'' =>
    quasicoherentSections_unique_of_universalEffectiveEpiFamily X U f h F t' t
      (fun i => (ht'' i).trans (ht' i).symm)⟩

private abbrev sectionsBaseChangeDiagram {X Y A B : Scheme.{u}}
    (p : Y ⟶ X) (F : Y.Modules) [F.IsQuasicoherent]
    (g : A ⟶ X) (q : B ⟶ Y) (r : B ⟶ A) (h : IsPullback q r p g) :
    AlgebraicGeometry.BaseChangeDiagram :=
  { X' := B, X := Y, S' := A, S := X, g' := q, f' := r, f := p, g := g,
    isPullback := h, F := F }

private lemma affineBaseChangeSectionsIso_naturality
    {X Y A₁ A₂ B₁ B₂ : Scheme.{u}} [IsAffine X] [IsAffine A₂]
    (p : Y ⟶ X) [IsAffineHom p] (F : Y.Modules) [F.IsQuasicoherent]
    (g₁ : A₁ ⟶ X) (g₂ : A₂ ⟶ X)
    (q₁ : B₁ ⟶ Y) (q₂ : B₂ ⟶ Y) (r₁ : B₁ ⟶ A₁) (r₂ : B₂ ⟶ A₂)
    (h₁ : IsPullback q₁ r₁ p g₁) (h₂ : IsPullback q₂ r₂ p g₂)
    (a : Over.mk g₁ ⟶ Over.mk g₂) (b : Over.mk q₁ ⟶ Over.mk q₂)
    (hr : b.left ≫ r₂ = r₁ ≫ a.left)
    (s : Γ((Scheme.Modules.pullback g₂).obj ((Scheme.Modules.pushforward p).obj F), ⊤)) :
    (affineBaseChangeSectionsIso (sectionsBaseChangeDiagram p F g₁ q₁ r₁ h₁)).hom
      (pullbackSectionsMap ((Scheme.Modules.pushforward p).obj F) a s) =
      pullbackSectionsMap F b
        ((affineBaseChangeSectionsIso (sectionsBaseChangeDiagram p F g₂ q₂ r₂ h₂)).hom s) := by
  let G := (Scheme.Modules.pushforward p).obj F
  let d₁ := sectionsBaseChangeDiagram p F g₁ q₁ r₁ h₁
  let d₂ := sectionsBaseChangeDiagram p F g₂ q₂ r₂ h₂
  let c₁ := (affineBaseChangeSectionsIso d₁).hom
  let c₂ := (affineBaseChangeSectionsIso d₂).hom
  let L := c₁.hom.comp (pullbackSectionsMap G a).hom
  let K := (pullbackSectionsMap F b).hom.comp c₂.hom
  change L s = K s
  apply affineSections_induction g₂ G (fun z => L z = K z) ?_ ?_ s
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro r t
    change c₁ (pullbackSectionsMap G a (r • pullbackGlobalSections g₂ G t)) =
      pullbackSectionsMap F b (c₂ (r • pullbackGlobalSections g₂ G t))
    calc
      _ = c₁ (a.left.appTop r • pullbackGlobalSections g₁ G t) :=
        congrArg c₁ (pullbackSectionsMap_smul_global G a r t)
      _ = r₁.appTop (a.left.appTop r) • pullbackGlobalSections q₁ F t :=
        affineBaseChangeSectionsIso_smul d₁ _ t
      _ = b.left.appTop (r₂.appTop r) • pullbackGlobalSections q₁ F t :=
        congrArg (fun k : B₁ ⟶ A₂ => k.appTop r • pullbackGlobalSections q₁ F t) hr.symm
      _ = pullbackSectionsMap F b (r₂.appTop r • pullbackGlobalSections q₂ F t) :=
        (pullbackSectionsMap_smul_global F b (r₂.appTop r) t).symm
      _ = _ := congrArg (fun z => pullbackSectionsMap F b z)
        (affineBaseChangeSectionsIso_smul d₂ r t).symm

-- The base-change half: along an affine morphism the global sections of a quasi-coherent
-- module are the global sections of its direct image, compatibly with pullback.
private theorem quasicoherentSectionsEqualizer_baseChange
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X) (h : IsQuasicoherentSectionsEqualizer X U f)
    (Y : AffineScheme.{u}) (p : Y ⟶ X) (V : I → AffineScheme.{u})
    (q : ∀ i, V i ⟶ Y) (r : ∀ i, V i ⟶ U i)
    (hp : ∀ i, IsPullback (q i) (r i) p (f i)) :
    IsQuasicoherentSectionsEqualizer Y V q := by
  intro F hF s hs
  have hp' (i) : IsPullback (q i).hom (r i).hom p.hom (f i).hom :=
    (hp i).map AffineScheme.forgetToScheme
  let F' := (Scheme.Modules.pushforward p.hom).obj F
  let d i := sectionsBaseChangeDiagram p.hom F (f i).hom (q i).hom (r i).hom (hp' i)
  let e i := affineBaseChangeSectionsIso (d i)
  let z (i) : Γ((Scheme.Modules.pullback (f i).hom).obj F', ⊤) := (e i).inv (s i)
  have he (i) : (e i).hom (z i) = s i := (e i).inv_hom_id_apply (s i)
  have hz : ∀ i j, pullbackSectionsMap F' (pairwiseFst X U f i j) (z i) =
      pullbackSectionsMap F' (pairwiseSnd X U f i j) (z j) := by
    intro i j
    let A := pairwiseOver X U f i j
    let B := pullback p.hom A.hom
    let l : B ⟶ Y.obj := pullback.fst p.hom A.hom
    let t : B ⟶ A.left := pullback.snd p.hom A.hom
    have hB : IsPullback l t p.hom A.hom := IsPullback.of_hasPullback _ _
    let dB := sectionsBaseChangeDiagram p.hom F A.hom l t hB
    let eB := affineBaseChangeSectionsIso dB
    let liftTo (n : I) (a : A ⟶ affineOver X U f n) :
        Over.mk l ⟶ affineOver Y V q n :=
      Over.homMk ((hp' n).lift l (t ≫ a.left)
        (hB.w.trans ((congrArg (fun k => t ≫ k) (Over.w a).symm).trans
          (Category.assoc t a.left (f n).hom).symm)))
        ((hp' n).lift_fst _ _ _)
    have hlift (n : I) (a : A ⟶ affineOver X U f n) :
        (liftTo n a).left ≫ (r n).hom = t ≫ a.left :=
      (hp' n).lift_snd _ _ _
    have hnat (n : I) (a : A ⟶ affineOver X U f n) :
        eB.hom (pullbackSectionsMap F' a (z n)) =
          pullbackSectionsMap F (liftTo n a) (s n) := by
      have hh := affineBaseChangeSectionsIso_naturality p.hom F
        A.hom (f n).hom l (q n).hom t (r n).hom hB (hp' n)
        a (liftTo n a) (hlift n a) (z n)
      exact hh.trans (congrArg (fun x => pullbackSectionsMap F (liftTo n a) x) (he n))
    apply (ConcreteCategory.bijective_of_isIso eB.hom).1
    rw [hnat i (pairwiseFst X U f i j), hnat j (pairwiseSnd X U f i j)]
    exact compatibleSections_cone F s hs i j (Over.mk l) _ _
  obtain ⟨t, ht, hu⟩ := h F' z hz
  have ht' : ∀ i, pullbackGlobalSections (q i).hom F t = s i := by
    intro i
    have hi := congrArg (fun x => (e i).hom x) (ht i)
    exact (affineBaseChangeSectionsIso_global (d i) t).symm.trans (hi.trans (he i))
  refine ⟨t, ht', ?_⟩
  intro t' ht''
  apply hu t'
  intro i
  apply (ConcreteCategory.bijective_of_isIso (e i).hom).1
  exact (affineBaseChangeSectionsIso_global (d i) t').trans ((ht'' i).trans (he i).symm)

end SectionsEqualizer

open SectionsEqualizer in
/-- **Stacks Project, Tag 0EUA.** A family of morphisms of affine schemes satisfies the
global-section equalizer condition for every quasi-coherent module if and only if it is a
universal effective epimorphic family in the category of affine schemes. -/
@[stacks 0EUA]
theorem quasicoherentSectionsEqualizer_iff_isUniversalEffectiveEpiFamily
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X) :
    IsQuasicoherentSectionsEqualizer X U f ↔
      StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f := by
  constructor
  · intro h
    refine ⟨fun i => inferInstance, ?_⟩
    intro Y p V q r hp
    exact isEffectiveEpiFamily_of_quasicoherentSectionsEqualizer Y V q
      (quasicoherentSectionsEqualizer_baseChange X U f h Y p V q r hp)
  · exact quasicoherentSectionsEqualizer_of_isUniversalEffectiveEpiFamily X U f

end AlgebraicGeometry
