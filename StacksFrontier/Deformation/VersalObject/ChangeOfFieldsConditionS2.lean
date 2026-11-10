module

public import StacksFrontier.Deformation.ResidueField.Comparison
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.SchlessingerConditions.SquareZeroExtension
public import StacksFrontier.Deformation.Terminal

/-!
# Conditions (S1), (S2) and (RS) after a change of residue field

Let `Λ → k → l` be a finite tower of a Noetherian base ring and two residue fields, and let
`p : F ⥤ 𝒞_{Λ,k}` be a functor. The projection `p_{l/k} : F_{l/k} ⥤ 𝒞_{Λ,l}` obtained by change of
residue field is the categorical pullback of `p` along the comparison functor `B ↦ B ×_l k`. If `p`
satisfies Schlessinger's condition (S1), or is cofibered in groupoids and satisfies (S2), or
satisfies the Rim-Schlessinger condition (RS), then so does `p_{l/k}`.

## Main results

* `Deformation.schlessingerConditionS1_changeOfFields`: condition (S1) passes from `p` to the
  projection obtained by change of residue field.
* `Deformation.schlessingerConditionS2_changeOfFields`: condition (S2) passes from `p` to the
  projection obtained by change of residue field.
* `Deformation.changeOfFieldsProjection_satisfiesRS`: condition (RS) passes from `p` to the
  projection obtained by change of residue field.

## References

* [Stacks Project, Tag 07WA](https://stacks.math.columbia.edu/tag/07WA)
-/

@[expose] public section

open CategoryTheory

universe u v w x y z

namespace Deformation

private noncomputable def pullbackCompletionChangeOfFields
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    {X₁ X₂ X : ChangeOfFieldsCategory S p}
    (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X)
    {A₁₂ : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (g₁ : A₁₂ ⟶ X₁.snd) (g₂ : A₁₂ ⟶ X₂.snd)
    (hpull : IsPullback g₂ g₁ f₂.snd f₁.snd)
    (H : PullbackCompletion p f₁.fst f₂.fst
      ((comparisonFunctor.{u, v, w, x} S).functor.map g₁ ≫ X₁.iso.inv)
      ((comparisonFunctor.{u, v, w, x} S).functor.map g₂ ≫ X₂.iso.inv)) :
    PullbackCompletion (changeOfFieldsProjection S p)
      f₁ f₂ g₁ g₂ := by
  let Fcmp := (comparisonFunctor.{u, v, w, x} S).functor
  let Z : ChangeOfFieldsCategory S p :=
    ⟨H.apex, A₁₂, eqToIso H.apex_eq⟩
  let mk : ∀ {Y : ChangeOfFieldsCategory S p} (g : A₁₂ ⟶ Y.snd) (h : H.apex ⟶ Y.fst),
      p.map h = eqToHom H.apex_eq ≫ (Fcmp.map g ≫ Y.iso.inv) → (Z ⟶ Y) :=
    fun g h hh => ⟨h, g, by simp [Z, Fcmp, hh]⟩
  refine ⟨Z, rfl, mk g₁ H.toFirst H.map_toFirst, mk g₂ H.toSecond H.map_toSecond, ?_, ?_, ?_⟩
  · apply CategoryTheory.Limits.CategoricalPullback.hom_ext
    · exact H.comm
    · exact hpull.w
  · rfl
  · rfl

private theorem comparisonFunctor_map_isPullback
    (S : ChangeOfFieldsSituation.{u, v, w})
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (f : A₁ ⟶ A) (g : A₂ ⟶ A)
    {P : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂)
    (h : IsPullback p₁ p₂ f g)
    (hg : Function.Surjective g.hom) :
    IsPullback
      ((comparisonFunctor.{u, v, w, x} S).functor.map p₁)
      ((comparisonFunctor.{u, v, w, x} S).functor.map p₂)
      ((comparisonFunctor.{u, v, w, x} S).functor.map f)
      ((comparisonFunctor.{u, v, w, x} S).functor.map g) := by
  let Fcmp := (comparisonFunctor.{u, v, w, x} S).functor
  let q := ArtinianLocalAlgCat.pullbackObj_of_surjective
    f g (Or.inr hg)
  let q₁ := ArtinianLocalAlgCat.pullbackFst_of_surjective
    f g (Or.inr hg)
  let q₂ := ArtinianLocalAlgCat.pullbackSnd_of_surjective
    f g (Or.inr hg)
  have hq : IsPullback q₁ q₂ f g :=
    ArtinianLocalAlgCat.isPullback_of_surjective f g (Or.inr hg)
  let i : P ≅ q := CategoryTheory.IsPullback.isoIsPullback A₁ A₂ h hq
  have hFg : Function.Surjective (Fcmp.map g).hom :=
    comparisonFunctor_map_surjective S g hg
  let q' := ArtinianLocalAlgCat.pullbackObj_of_surjective
    (Fcmp.map f) (Fcmp.map g) (Or.inr hFg)
  let q₁' := ArtinianLocalAlgCat.pullbackFst_of_surjective
    (Fcmp.map f) (Fcmp.map g) (Or.inr hFg)
  let q₂' := ArtinianLocalAlgCat.pullbackSnd_of_surjective
    (Fcmp.map f) (Fcmp.map g) (Or.inr hFg)
  have hq' : IsPullback q₁' q₂' (Fcmp.map f) (Fcmp.map g) :=
    ArtinianLocalAlgCat.isPullback_of_surjective
      (Fcmp.map f) (Fcmp.map g) (Or.inr hFg)
  have q₁_hom : q₁.hom = AlgHom.pullbackFst f.hom g.hom :=
    ArtinianLocalAlgCat.pullbackFst_of_surjective_hom
      f g (Or.inr hg)
  have q₂_hom : q₂.hom = AlgHom.pullbackSnd f.hom g.hom :=
    ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom
      f g (Or.inr hg)
  have q₁'_hom : q₁'.hom = AlgHom.pullbackFst (Fcmp.map f).hom (Fcmp.map g).hom :=
    ArtinianLocalAlgCat.pullbackFst_of_surjective_hom
      (Fcmp.map f) (Fcmp.map g) (Or.inr hFg)
  have q₂'_hom : q₂'.hom = AlgHom.pullbackSnd (Fcmp.map f).hom (Fcmp.map g).hom :=
    ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom
      (Fcmp.map f) (Fcmp.map g) (Or.inr hFg)
  have hres : residueMap S q =
      (residueMap S A₁).comp
        (RingHom.pullbackFst f.hom.toRingHom g.hom.toRingHom) := by
    have hcar : q.carrier = AlgHom.pullback f.hom g.hom :=
      ArtinianLocalAlgCat.pullbackObj_of_surjective_carrier f g (Or.inr hg)
    cases hcar
    ext a
    change q.residueEquiv (IsLocalRing.residue q a) =
      A₁.residueEquiv (IsLocalRing.residue A₁
        (RingHom.pullbackFst f.hom.toRingHom g.hom.toRingHom a))
    rw [ArtinianLocalAlgCat.pullbackObj_of_surjective_residueEquiv_residue
      f g (Or.inr hg)]
    change A.residueEquiv (IsLocalRing.residue A
      (f.hom (AlgHom.pullbackFst f.hom g.hom a))) =
        A₁.residueEquiv (IsLocalRing.residue A₁
          (AlgHom.pullbackFst f.hom g.hom a))
    exact f.residue_comm _
  let pullL := RingHom.pullback (residueMap S q)
    (algebraMap S.k S.l)
  let pullL' := RingHom.pullback
    ((residueMap S A₁).comp
      (RingHom.pullbackFst f.hom.toRingHom g.hom.toRingHom))
    (algebraMap S.k S.l)
  have hpullEq : pullL = pullL' := by
    dsimp only [pullL, pullL', q,
      ArtinianLocalAlgCat.pullbackObj_of_surjective,
      ArtinianLocalAlgCat.IsConcretePullback.obj]
    apply Subring.ext
    intro t
    change residueMap S q t.1 = algebraMap S.k S.l t.2 ↔
      ((residueMap S A₁).comp
        (RingHom.pullbackFst f.hom.toRingHom g.hom.toRingHom)) t.1 =
          algebraMap S.k S.l t.2
    rw [hres]
    exact Iff.rfl
  let eInner : pullL ≃+* pullL' := RingEquiv.subringCongr hpullEq
  let eRing : Fcmp.obj q ≃+*
      RingHom.pullback (Fcmp.map f).hom.toRingHom (Fcmp.map g).hom.toRingHom :=
    (comparisonFunctor.{u, v, w, x} S).pullbackEquiv q |>.trans
      (eInner.trans (comparisonFunctor_pullbackRingEquiv S f g))
  have eInner_val (b : pullL) : (eInner b).val = b.val := rfl
  have eRingFstAny (b : Fcmp.obj q) :
      ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₁
        (eRing b).val.1).val =
        (((comparisonFunctor.{u, v, w, x} S).pullbackEquiv q b).val.1.val.1,
          ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv q b).val.2) := by
    dsimp only [eRing]
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, comparisonFunctor_pullbackRingEquiv_fst,
      eInner_val]
  have eRingSndAny (b : Fcmp.obj q) :
      ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₂
        (eRing b).val.2).val =
        (((comparisonFunctor.{u, v, w, x} S).pullbackEquiv q b).val.1.val.2,
          ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv q b).val.2) := by
    dsimp only [eRing]
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, comparisonFunctor_pullbackRingEquiv_snd,
      eInner_val]
  let eRing' : Fcmp.obj q ≃+* q' := eRing
  have eRing'_apply (b : Fcmp.obj q) : eRing' b = (eRing b : q') := rfl
  have qAlgFst (a : S.Λ) :
      (algebraMap S.Λ q' a).val.1 = algebraMap S.Λ (Fcmp.obj A₁) a := rfl
  have qAlgSnd (a : S.Λ) :
      (algebraMap S.Λ q' a).val.2 = algebraMap S.Λ (Fcmp.obj A₂) a := rfl
  have algebraMap_eq : ∀ (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) (y z : Fcmp.obj B) (a : S.Λ),
      ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv B y).val =
        (algebraMap S.Λ B a, algebraMap S.Λ S.k a) → z = algebraMap S.Λ (Fcmp.obj B) a → y = z := by
    intro B y z a hy hz
    apply (comparisonFunctor.{u, v, w, x} S).pullbackEquiv B |>.injective
    apply Subtype.ext
    rw [hy, hz]
    exact Prod.ext ((comparisonFunctor.{u, v, w, x} S).algebraMap_fst B a).symm
      ((comparisonFunctor.{u, v, w, x} S).algebraMap_snd B a).symm
  let eAlg : Fcmp.obj q ≃ₐ[S.Λ] q' := AlgEquiv.ofRingEquiv (f := eRing') (by
    intro a
    apply Subtype.ext
    apply Prod.ext
    · apply algebraMap_eq A₁ _ _ a _ (qAlgFst a)
      rw [eRing'_apply, eRingFstAny, ComparisonFunctor.algebraMap_fst,
        ComparisonFunctor.algebraMap_snd]
      rfl
    · apply algebraMap_eq A₂ _ _ a _ (qAlgSnd a)
      rw [eRing'_apply, eRingSndAny, ComparisonFunctor.algebraMap_fst,
        ComparisonFunctor.algebraMap_snd]
      rfl)
  let eMor : Fcmp.obj q ⟶ q' :=
    { hom := eAlg.toAlgHom
      isLocal := ⟨fun b hb => by simpa using hb.map eAlg.symm.toRingHom⟩
      residue_comm := by
        intro b
        rw [ArtinianLocalAlgCat.pullbackObj_of_surjective_residueEquiv_residue
          (Fcmp.map f) (Fcmp.map g) (Or.inr hFg)]
        change (Fcmp.obj A).residueEquiv
            (IsLocalRing.residue (Fcmp.obj A)
              ((Fcmp.map f).hom
                (AlgHom.pullbackFst (Fcmp.map f).hom (Fcmp.map g).hom (eAlg b)))) = _
        calc
          (Fcmp.obj A).residueEquiv
              (IsLocalRing.residue (Fcmp.obj A)
                ((Fcmp.map f).hom
                  (AlgHom.pullbackFst (Fcmp.map f).hom (Fcmp.map g).hom (eAlg b)))) =
              (Fcmp.obj A₁).residueEquiv
                (IsLocalRing.residue (Fcmp.obj A₁)
                  (AlgHom.pullbackFst (Fcmp.map f).hom (Fcmp.map g).hom (eAlg b))) :=
                (Fcmp.map f).residue_comm _
          _ = ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₁
                (AlgHom.pullbackFst (Fcmp.map f).hom (Fcmp.map g).hom (eAlg b))).val.2 :=
                (comparisonFunctor.{u, v, w, x} S).residue_snd A₁ _
          _ = ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv q b).val.2 := by
                have hfst : AlgHom.pullbackFst (Fcmp.map f).hom (Fcmp.map g).hom (eAlg b) =
                    (eRing' b).val.1 := rfl
                rw [hfst, eRing'_apply, eRingFstAny]
          _ = (Fcmp.obj q).residueEquiv
                (IsLocalRing.residue (Fcmp.obj q) b) :=
                (comparisonFunctor.{u, v, w, x} S).residue_snd q b |>.symm }
  let eInv : q' ⟶ Fcmp.obj q :=
    { hom := eAlg.symm.toAlgHom
      isLocal := ⟨fun b hb => by simpa using hb.map eAlg.toRingHom⟩
      residue_comm := by
        intro b
        calc
          (Fcmp.obj q).residueEquiv
              (IsLocalRing.residue (Fcmp.obj q) (eAlg.symm b)) =
              q'.residueEquiv
                (IsLocalRing.residue q' (eAlg (eAlg.symm b))) :=
                  (eMor.residue_comm (eAlg.symm b)).symm
          _ = q'.residueEquiv (IsLocalRing.residue q' b) := by
                rw [eAlg.apply_symm_apply] }
  let eIso : Fcmp.obj q ≅ q' :=
    { hom := eMor
      inv := eInv
      hom_inv_id := by
        apply ArtinianLocalAlgCat.hom_ext
        ext b
        change eAlg.symm (eAlg b) = b
        exact eAlg.symm_apply_apply b
      inv_hom_id := by
        apply ArtinianLocalAlgCat.hom_ext
        ext b
        change eAlg (eAlg.symm b) = b
        exact eAlg.apply_symm_apply b }
  have eAlg_fst (b : Fcmp.obj q) :
      q₁'.hom (eAlg b) = (Fcmp.map q₁).hom b := by
    apply (comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₁ |>.injective
    apply Subtype.ext
    calc
      ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₁
          (q₁'.hom (eAlg b))).val =
        (((comparisonFunctor.{u, v, w, x} S).pullbackEquiv q b).val.1.val.1,
          ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv q b).val.2) := by
            rw [q₁'_hom]
            change ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₁
              ((eRing' b).val.1)).val = _
            rw [eRing'_apply, eRingFstAny]
      _ = ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₁
          ((Fcmp.map q₁).hom b)).val := by
            apply Prod.ext
            · rw [(comparisonFunctor.{u, v, w, x} S).map_fst, q₁_hom]
              rfl
            · exact ((comparisonFunctor.{u, v, w, x} S).map_snd q₁ b).symm
  have eAlg_snd (b : Fcmp.obj q) :
      q₂'.hom (eAlg b) = (Fcmp.map q₂).hom b := by
    apply (comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₂ |>.injective
    apply Subtype.ext
    calc
      ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₂
          (q₂'.hom (eAlg b))).val =
        (((comparisonFunctor.{u, v, w, x} S).pullbackEquiv q b).val.1.val.2,
          ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv q b).val.2) := by
            rw [q₂'_hom]
            change ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₂
              ((eRing' b).val.2)).val = _
            rw [eRing'_apply, eRingSndAny]
      _ = ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₂
          ((Fcmp.map q₂).hom b)).val := by
            apply Prod.ext
            · rw [(comparisonFunctor.{u, v, w, x} S).map_fst, q₂_hom]
              rfl
            · exact ((comparisonFunctor.{u, v, w, x} S).map_snd q₂ b).symm
  have heq₁ : eIso.hom ≫ q₁' = Fcmp.map q₁ := by
    apply ArtinianLocalAlgCat.hom_ext
    exact AlgHom.ext eAlg_fst
  have heq₂ : eIso.hom ≫ q₂' = Fcmp.map q₂ := by
    apply ArtinianLocalAlgCat.hom_ext
    exact AlgHom.ext eAlg_snd
  have hi₁ : Fcmp.map i.hom ≫ Fcmp.map q₁ = Fcmp.map p₁ := by
    rw [← Fcmp.map_comp]
    exact congrArg Fcmp.map
      (CategoryTheory.IsPullback.isoIsPullback_hom_fst A₁ A₂ h hq)
  have hi₂ : Fcmp.map i.hom ≫ Fcmp.map q₂ = Fcmp.map p₂ := by
    rw [← Fcmp.map_comp]
    exact congrArg Fcmp.map
      (CategoryTheory.IsPullback.isoIsPullback_hom_snd A₁ A₂ h hq)
  refine hq'.of_iso' (Functor.mapIso Fcmp i ≪≫ eIso) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by rfl) (by rfl)
  · simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, heq₁, hi₁,
      Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, heq₂, hi₂,
      Iso.refl_hom, Category.comp_id]
    rfl

private noncomputable def dualNumberMapEquiv
    {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]
    (σ : k ≃ₐ[Λ] k) : DualNumber k ≃ₐ[Λ] DualNumber k := by
  let f : DualNumber k ≃+* DualNumber k :=
    { toFun := fun x => (σ x.1, σ x.2)
      invFun := fun x => (σ.symm x.1, σ.symm x.2)
      left_inv := by
        intro x
        cases x with
        | mk a b => exact Prod.ext (σ.symm_apply_apply a) (σ.symm_apply_apply b)
      right_inv := by
        intro x
        cases x with
        | mk a b => exact Prod.ext (σ.apply_symm_apply a) (σ.apply_symm_apply b)
      map_mul' := by
        intro x y
        apply TrivSqZeroExt.ext
        · change σ (x.1 * y.1) = σ x.1 * σ y.1
          exact σ.map_mul _ _
        · change σ (x.1 * y.2 + x.2 * y.1) =
            σ x.1 * σ y.2 + σ x.2 * σ y.1
          simp only [map_add, map_mul]
      map_add' := by
        intro x y
        cases x with
        | mk a b => cases y with
          | mk c d => exact Prod.ext (σ.map_add _ _) (σ.map_add _ _) }
  exact AlgEquiv.ofRingEquiv (f := f) (by
    intro a
    apply TrivSqZeroExt.ext
    · exact σ.commutes a
    · change σ (0 : k) = 0
      exact map_zero σ.toRingHom)

private theorem comparisonFunctor_map_isSquareZeroProjection
    (S : ChangeOfFieldsSituation.{u, v, w})
    {Aε A₀ : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (e : Aε ⟶ A₀) (he : IsDualNumberProjection e) :
    IsSquareZeroProjection (V := S.l)
      ((comparisonFunctor.{u, v, w, x} S).functor.map e) := by
  let Fcmp := (comparisonFunctor.{u, v, w, x} S).functor
  rcases he with ⟨i₀, iε, hie⟩
  have hfield : IsField A₀ := MulEquiv.isField (Field.toIsField S.l) i₀.toMulEquiv
  have hbot : IsLocalRing.maximalIdeal A₀ = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
  let j₀ : A₀ ≃ₐ[S.Λ] S.l :=
    (ArtinianLocalAlgCat.residueAlgEquiv A₀ hbot).trans A₀.residueEquiv
  let σ : S.l ≃ₐ[S.Λ] S.l := i₀.symm.trans j₀
  let jε : Aε ≃ₐ[S.Λ] DualNumber S.l := iε.trans (dualNumberMapEquiv σ)
  have hjε_snd_algebraMap (a : S.Λ) :
      TrivSqZeroExt.snd (jε (algebraMap S.Λ Aε a)) = 0 := by
    rw [jε.commutes]
    rfl
  have hjε_fst (a : Aε) : (jε a).1 = residueMap S Aε a := by
    have heq : i₀ (e.hom a) = TrivSqZeroExt.fst (iε a) :=
      DFunLike.congr_fun hie a
    dsimp [jε, dualNumberMapEquiv, σ]
    change j₀ (i₀.symm (TrivSqZeroExt.fst (iε a))) = _
    rw [← heq, AlgEquiv.symm_apply_apply]
    simpa [j₀, residueMap] using e.residue_comm a
  let _ : Module S.kᵐᵒᵖ S.l := moduleMulOppositeOfSquareZeroVectorSpace S.k S.l
  let _ : IsCentralScalar S.k S.l := isCentralScalarOfSquareZeroVectorSpace S.k S.l
  let pull₀ := RingHom.pullback (residueMap S A₀) (algebraMap S.k S.l)
  let q₀ : pull₀ →+* S.k := RingHom.pullbackSnd _ _
  have hq₀ : Function.Bijective q₀ := by
    constructor
    · intro a b hab
      have hs : a.val.2 = b.val.2 := by simpa [q₀] using hab
      apply Subtype.ext
      apply Prod.ext
      · apply j₀.injective
        have ha := a.property
        have hb := b.property
        change residueMap S A₀ a.val.1 = algebraMap S.k S.l a.val.2 at ha
        change residueMap S A₀ b.val.1 = algebraMap S.k S.l b.val.2 at hb
        rw [hs] at ha
        exact ha.trans hb.symm
      · exact hs
    · intro a
      refine ⟨⟨(j₀.symm (algebraMap S.k S.l a), a), ?_⟩, rfl⟩
      change residueMap S A₀ (j₀.symm (algebraMap S.k S.l a)) = _
      exact j₀.apply_symm_apply (algebraMap S.k S.l a)
  let e₀Ring : Fcmp.obj A₀ ≃+* S.k :=
    ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₀).trans
      (RingEquiv.ofBijective q₀ hq₀)
  let e₀ : Fcmp.obj A₀ ≃ₐ[S.Λ] S.k := AlgEquiv.ofRingEquiv (f := e₀Ring) (by
    intro a
    change q₀ ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₀
      (algebraMap S.Λ (Fcmp.obj A₀) a)) = algebraMap S.Λ S.k a
    change ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₀
      (algebraMap S.Λ (Fcmp.obj A₀) a)).val.2 = algebraMap S.Λ S.k a
    exact (comparisonFunctor.{u, v, w, x} S).algebraMap_snd A₀ a)
  let pullε := RingHom.pullback (residueMap S Aε) (algebraMap S.k S.l)
  let eεRing : pullε ≃+* TrivSqZeroExt S.k S.l := by
    refine
      { toFun := fun z => (z.val.2, (jε z.val.1).2)
        invFun := fun z => ⟨(jε.symm (algebraMap S.k S.l z.1, z.2), z.1), ?_⟩
        left_inv := ?_
        right_inv := ?_
        map_mul' := ?_
        map_add' := ?_ }
    · change residueMap S Aε (jε.symm (algebraMap S.k S.l z.1, z.2)) = _
      calc
        _ = (jε (jε.symm (algebraMap S.k S.l z.1, z.2))).1 :=
          (hjε_fst _).symm
        _ = algebraMap S.k S.l z.1 :=
          congrArg TrivSqZeroExt.fst (jε.apply_symm_apply _)
    · intro z
      cases z with
      | mk q hq =>
        apply Subtype.ext
        apply Prod.ext
        · apply jε.injective
          apply TrivSqZeroExt.ext
          · calc
              (jε (jε.symm (algebraMap S.k S.l q.2, (jε q.1).2))).1 =
                  (algebraMap S.k S.l q.2, (jε q.1).2).1 :=
                    congrArg TrivSqZeroExt.fst (jε.apply_symm_apply _)
              _ = (jε q.1).1 := by
                    change algebraMap S.k S.l q.2 = (jε q.1).1
                    exact hq.symm.trans (hjε_fst q.1).symm
          · calc
              TrivSqZeroExt.snd (jε (jε.symm (algebraMap S.k S.l q.2, (jε q.1).2))) =
                  TrivSqZeroExt.snd (algebraMap S.k S.l q.2, (jε q.1).2) :=
                    congrArg TrivSqZeroExt.snd (jε.apply_symm_apply _)
              _ = TrivSqZeroExt.snd (jε q.1) := rfl
        · rfl
    · intro z
      apply Prod.ext
      · rfl
      · calc
          TrivSqZeroExt.snd (jε (jε.symm (algebraMap S.k S.l z.1, z.2))) =
              TrivSqZeroExt.snd (algebraMap S.k S.l z.1, z.2) :=
                congrArg TrivSqZeroExt.snd (jε.apply_symm_apply _)
          _ = z.2 := rfl
    · intro a b
      cases a with
      | mk qa hqa => cases b with
        | mk qb hqb =>
          rw [Subring.coe_mul]
          simp only [Prod.fst_mul, Prod.snd_mul]
          apply TrivSqZeroExt.ext
          · rfl
          · have hfa : (jε qa.1).1 = algebraMap S.k S.l qa.2 :=
              (hjε_fst qa.1).trans hqa
            have hfb : (jε qb.1).1 = algebraMap S.k S.l qb.2 :=
              (hjε_fst qb.1).trans hqb
            let x : TrivSqZeroExt S.k S.l := (qa.2, (jε qa.1).2)
            let y : TrivSqZeroExt S.k S.l := (qb.2, (jε qb.1).2)
            simp only [TrivSqZeroExt.snd]
            rw [map_mul]
            change TrivSqZeroExt.snd (jε qa.1 * jε qb.1) =
              TrivSqZeroExt.snd (x * y)
            rw [DualNumber.snd_mul, TrivSqZeroExt.snd_mul x y]
            have hfa' : TrivSqZeroExt.fst (jε qa.1) = algebraMap S.k S.l qa.2 := hfa
            have hfb' : TrivSqZeroExt.fst (jε qb.1) = algebraMap S.k S.l qb.2 := hfb
            rw [hfa', hfb']
            simp [x, y, Algebra.smul_def, IsCentralScalar.op_smul_eq_smul, mul_comm]
            rfl
    · intro a b
      cases a with
      | mk qa hqa => cases b with
        | mk qb hqb =>
          rw [Subring.coe_add]
          simp only [Prod.fst_add, Prod.snd_add]
          apply Prod.ext
          · rfl
          · calc
              (jε (qa.1 + qb.1)).2 = (jε qa.1).2 + (jε qb.1).2 :=
                congrArg Prod.snd (map_add jε qa.1 qb.1)
              _ = ((qa.2, (jε qa.1).2) + (qb.2, (jε qb.1).2)).2 := rfl
  let eε' : Fcmp.obj Aε ≃+* TrivSqZeroExt S.k S.l :=
    ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv Aε).trans eεRing
  let moduleΛl : Module S.Λ S.l := Module.compHom S.l (algebraMap S.Λ S.k)
  let _ : Module S.Λ S.l := moduleΛl
  let _ : SMul S.Λ S.l := moduleΛl.toSMul
  let _ : IsScalarTower S.Λ S.k S.l :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let eε : Fcmp.obj Aε ≃ₐ[S.Λ] TrivSqZeroExt S.k S.l :=
    AlgEquiv.ofRingEquiv (f := eε') (by
      intro a
      apply TrivSqZeroExt.ext
      · exact (comparisonFunctor.{u, v, w, x} S).algebraMap_snd Aε a
      · change TrivSqZeroExt.snd (jε
          ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv Aε
            (algebraMap S.Λ (Fcmp.obj Aε) a)).val.1) = 0
        rw [(comparisonFunctor.{u, v, w, x} S).algebraMap_fst]
        exact hjε_snd_algebraMap a)
  refine ⟨e₀, eε, ?_⟩
  apply AlgHom.ext
  intro a
  change q₀ ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv A₀
      ((Fcmp.map e).hom a)) =
    ((comparisonFunctor.{u, v, w, x} S).pullbackEquiv Aε a).val.2
  exact (comparisonFunctor.{u, v, w, x} S).map_snd e a

private noncomputable def artinianIsoAlgEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : ArtinianLocalAlgCat.{u, x, w} Λ k} (i : A ≅ B) : A ≃ₐ[Λ] B :=
  AlgEquiv.ofBijective i.hom.hom
    ⟨Function.LeftInverse.injective (g := i.inv.hom) fun a =>
        congrArg (fun f => f.hom a) i.hom_inv_id,
      fun b => ⟨i.inv.hom b, congrArg (fun f => f.hom b) i.inv_hom_id⟩⟩

private theorem changeOfFields_dualProjection_isSquareZeroProjection
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    {Xε X₀ : ChangeOfFieldsCategory S p}
    (e : Xε ⟶ X₀)
    (he : IsDualNumberProjection e.snd) :
    IsSquareZeroProjection (V := S.l)
      (p.map e.fst) := by
  let G := (comparisonFunctor.{u, v, w, x} S).functor
  let _ : Module S.kᵐᵒᵖ S.l := moduleMulOppositeOfSquareZeroVectorSpace S.k S.l
  let _ : IsCentralScalar S.k S.l := isCentralScalarOfSquareZeroVectorSpace S.k S.l
  let moduleΛl : Module S.Λ S.l := Module.compHom S.l (algebraMap S.Λ S.k)
  let _ : Module S.Λ S.l := moduleΛl
  let _ : SMul S.Λ S.l := moduleΛl.toSMul
  let _ : IsScalarTower S.Λ S.k S.l :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨j₀, jV, hj⟩ := comparisonFunctor_map_isSquareZeroProjection S e.snd he
  let i₀ := artinianIsoAlgEquiv X₀.iso
  let iε := artinianIsoAlgEquiv Xε.iso
  refine ⟨i₀.trans j₀, iε.trans jV, ?_⟩
  apply AlgHom.ext
  intro a
  have hw := congrArg (fun m => m.hom) e.w
  have hval := DFunLike.congr_fun hw a
  have hval' : X₀.iso.hom.hom ((p.map e.fst).hom a) =
      (G.map e.snd).hom (Xε.iso.hom.hom a) := by
    change X₀.iso.hom.hom ((p.map e.fst).hom a) =
      (G.map e.snd).hom (Xε.iso.hom.hom a) at hval
    exact hval
  have hcmp := DFunLike.congr_fun hj (Xε.iso.hom.hom a)
  change j₀ (X₀.iso.hom.hom ((p.map e.fst).hom a)) =
    TrivSqZeroExt.fst (jV (Xε.iso.hom.hom a))
  rw [hval']
  exact hcmp

private noncomputable def pullbackCompletionToOriginal
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    (hp : IsCofiberedInGroupoids p)
    {X Xε X₀ : ChangeOfFieldsCategory S p}
    (d : X ⟶ X₀) (e : Xε ⟶ X₀)
    {Aε : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (g : Aε ⟶ X.snd) (gε : Aε ⟶ Xε.snd)
    (P : PullbackCompletion
      (changeOfFieldsProjection S p) d e g gε) :
    PullbackCompletion p d.fst e.fst
      ((comparisonFunctor.{u, v, w, x} S).functor.map g ≫ X.iso.inv)
      ((comparisonFunctor.{u, v, w, x} S).functor.map gε ≫ Xε.iso.inv) := by
  let G := (comparisonFunctor.{u, v, w, x} S).functor
  let q := changeOfFieldsProjection S p
  let E := changeOfFieldsFiberEquivalence S p hp Aε
  let PF : q.Fiber Aε := ⟨P.apex, P.apex_eq⟩
  let PN : p.Fiber (G.obj Aε) := E.functor.obj PF
  let Iobj : q.Fiber Aε :=
    ⟨⟨PN.val, Aε, eqToIso PN.property⟩, rfl⟩
  let βP := E.unitIso.inv.app PF
  change Iobj ⟶ PF at βP
  have hβLift : q.IsHomLift (𝟙 Aε) βP.val := βP.property
  letI : q.IsHomLift (𝟙 Aε) βP.val := hβLift
  have hβBase := IsHomLift.fac' q (𝟙 Aε) βP.val
  have hβSnd : βP.val.snd = eqToHom P.apex_eq.symm := by
    change q.map βP.val = _ at hβBase
    change βP.val.snd = _ at hβBase
    exact hβBase
  have hβW : p.map βP.val.fst ≫ P.apex.iso.hom =
      eqToHom PN.property ≫ G.map βP.val.snd := by
    change p.map βP.val.fst ≫ P.apex.iso.hom =
      (eqToIso PN.property).hom ≫ G.map βP.val.snd
    exact βP.val.w
  have key : ∀ {Y : ChangeOfFieldsCategory S p} (k : P.apex ⟶ Y) (a : Aε ⟶ Y.snd),
      q.map k = eqToHom P.apex_eq ≫ a →
      p.map (βP.val.fst ≫ k.fst) ≫ Y.iso.hom = eqToHom PN.property ≫ G.map a := by
    intro Y k a hk
    have hBase : βP.val.snd ≫ k.snd = a := by
      change k.snd = _ at hk
      rw [hβSnd, hk]
      exact (by simp : eqToHom P.apex_eq.symm ≫ eqToHom P.apex_eq ≫ a = a)
    rw [Functor.map_comp, Category.assoc, k.w, ← Category.assoc, hβW, Category.assoc,
      ← G.map_comp, hBase]
  let Pold : PullbackCompletion p d.fst e.fst
      (G.map g ≫ X.iso.inv) (G.map gε ≫ Xε.iso.inv) := by
    refine ⟨PN.val, PN.property, βP.val.fst ≫ P.toFirst.fst,
      βP.val.fst ≫ P.toSecond.fst, ?_, ?_, ?_⟩
    · have hfst : P.toSecond.fst ≫ e.fst = P.toFirst.fst ≫ d.fst := by
        have hh := congrArg (fun m => m.fst) P.comm
        simpa using hh
      calc
        (βP.val.fst ≫ P.toSecond.fst) ≫ e.fst =
            βP.val.fst ≫ (P.toSecond.fst ≫ e.fst) := Category.assoc _ _ _
        _ = βP.val.fst ≫ (P.toFirst.fst ≫ d.fst) := congrArg _ hfst
        _ = (βP.val.fst ≫ P.toFirst.fst) ≫ d.fst := (Category.assoc _ _ _).symm
    · exact (cancel_mono X.iso.hom).mp ((key P.toFirst g P.map_toFirst).trans (by simp))
    · exact (cancel_mono Xε.iso.hom).mp ((key P.toSecond gε P.map_toSecond).trans (by simp))
  exact Pold

private alias dualNumberProjection_surjective := surjective_of_isDualNumberProjection

/-- A morphism of the changed category with surjective base component has surjective image
under `p`. -/
private theorem changeOfFields_surjective_fst
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    {X₂ X : ChangeOfFieldsCategory S p} (f : X₂ ⟶ X)
    (hf : Function.Surjective f.snd.hom) :
    Function.Surjective (p.map f.fst).hom := by
  let G := (comparisonFunctor.{u, v, w, x} S).functor
  have hG : Function.Surjective (G.map f.snd).hom :=
    comparisonFunctor_map_surjective S f.snd hf
  have hcomp : p.map f.fst = X₂.iso.hom ≫ G.map f.snd ≫ X.iso.inv := by
    apply (cancel_mono X.iso.hom).1
    calc
      p.map f.fst ≫ X.iso.hom = X₂.iso.hom ≫ G.map f.snd := f.w
      _ = (X₂.iso.hom ≫ G.map f.snd ≫ X.iso.inv) ≫ X.iso.hom := by simp
  rw [hcomp]
  exact (surjective_hom_of_isIso X.iso.inv).comp
    (hG.comp (surjective_hom_of_isIso X₂.iso.hom))

private theorem changeOfFields_isPullback
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    {X Xε X₀ : ChangeOfFieldsCategory S p}
    (d : X ⟶ X₀) (e : Xε ⟶ X₀)
    {Aε : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (g : Aε ⟶ X.snd) (gε : Aε ⟶ Xε.snd)
    (hpb : IsPullback gε g e.snd d.snd)
    (heSurj : Function.Surjective e.snd.hom) :
    IsPullback
      ((comparisonFunctor.{u, v, w, x} S).functor.map gε ≫ Xε.iso.inv)
      ((comparisonFunctor.{u, v, w, x} S).functor.map g ≫ X.iso.inv)
      (p.map e.fst) (p.map d.fst) := by
  let G := (comparisonFunctor.{u, v, w, x} S).functor
  have hcmp : IsPullback (G.map gε) (G.map g) (G.map e.snd) (G.map d.snd) :=
    (comparisonFunctor_map_isPullback S d.snd e.snd g gε hpb.flip heSurj).flip
  have heIso : G.map e.snd ≫ X₀.iso.inv = Xε.iso.inv ≫ p.map e.fst :=
    CategoryTheory.Limits.CategoricalPullback.Hom.w' e
  have hdIso : G.map d.snd ≫ X₀.iso.inv = X.iso.inv ≫ p.map d.fst :=
    CategoryTheory.Limits.CategoricalPullback.Hom.w' d
  let sqCmp : CategoryTheory.Square
      (ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k) :=
    { f₁₂ := G.map gε
      f₁₃ := G.map g
      f₂₄ := G.map e.snd
      f₃₄ := G.map d.snd
      fac := hcmp.w }
  let sqTarget : CategoryTheory.Square
      (ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k) :=
    { f₁₂ := G.map gε ≫ Xε.iso.inv
      f₁₃ := G.map g ≫ X.iso.inv
      f₂₄ := p.map e.fst
      f₃₄ := p.map d.fst
      fac := by
        calc
          (G.map gε ≫ Xε.iso.inv) ≫ p.map e.fst =
              G.map gε ≫ (G.map e.snd ≫ X₀.iso.inv) := by
                rw [Category.assoc, ← heIso]
          _ = G.map g ≫ (G.map d.snd ≫ X₀.iso.inv) := by
                rw [← Category.assoc, hcmp.w, Category.assoc]
          _ = (G.map g ≫ X.iso.inv) ≫ p.map d.fst := by
                rw [Category.assoc, ← hdIso, ← Category.assoc] }
  let eSq := CategoryTheory.Square.isoMk
    (sq₁ := sqCmp) (sq₂ := sqTarget) (Iso.refl _) Xε.iso.symm X.iso.symm X₀.iso.symm
    (by simp [sqCmp, sqTarget]) (by simp [sqCmp, sqTarget])
    heIso hdIso
  exact (CategoryTheory.Square.IsPullback.iff_of_iso eSq).mp hcmp

/-- A change of residue field preserves Schlessinger's condition (S1). -/
@[stacks 07WA "condition (S1)"]
public theorem schlessingerConditionS1_changeOfFields
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    (hS1 : SchlessingerConditionS1 p) :
    SchlessingerConditionS1
      (changeOfFieldsProjection S p) := by
  let G := (comparisonFunctor.{u, v, w, x} S).functor
  refine ⟨?_⟩
  intro X₁ X₂ X f₁ f₂ hf₂ A₁₂ g₁ g₂ hpb
  have hf₂snd : Function.Surjective f₂.snd.hom := hf₂
  rcases hS1.completion f₁.fst f₂.fst (changeOfFields_surjective_fst S p f₂ hf₂snd)
      (G.map g₁ ≫ X₁.iso.inv) (G.map g₂ ≫ X₂.iso.inv)
      (changeOfFields_isPullback S p f₁ f₂ g₁ g₂ hpb hf₂snd) with ⟨H⟩
  exact ⟨pullbackCompletionChangeOfFields S p f₁ f₂ g₁ g₂ hpb H⟩

/-- A change of residue field preserves Schlessinger's condition (S2) for a functor cofibered
in groupoids. -/
@[stacks 07WA "condition (S2)"]
public theorem schlessingerConditionS2_changeOfFields
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    (hp : IsCofiberedInGroupoids p)
    (hS2 : SchlessingerConditionS2 p) :
    SchlessingerConditionS2
      (changeOfFieldsProjection S p) := by
  let G := (comparisonFunctor.{u, v, w, x} S).functor
  let q := changeOfFieldsProjection S p
  have key : ∀ {X Xε X₀ : ChangeOfFieldsCategory S p} (d : X ⟶ X₀) (e : Xε ⟶ X₀)
      {Aε : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l} (g : Aε ⟶ X.snd) (gε : Aε ⟶ Xε.snd),
      IsPullback gε g e.snd d.snd → IsDualNumberProjection e.snd →
      IsSquareZeroProjection (V := S.l) (p.map e.fst) ∧
        IsPullback (G.map gε ≫ Xε.iso.inv) (G.map g ≫ X.iso.inv) (p.map e.fst) (p.map d.fst) := by
    intro X Xε X₀ d e Aε g gε hpb he
    exact ⟨changeOfFields_dualProjection_isSquareZeroProjection S p e he,
      changeOfFields_isPullback S p d e g gε hpb (dualNumberProjection_surjective e.snd he)⟩
  refine ⟨?_, ?_⟩
  · intro X Xε X₀ d e he Aε g gε hpb
    obtain ⟨heSq, hpb'⟩ := key d e g gε hpb he
    rcases schlessingerConditionS2_completion_squareZero p hp hS2
        d.fst e.fst heSq (G.map g ≫ X.iso.inv) (G.map gε ≫ Xε.iso.inv) hpb' with ⟨H⟩
    exact ⟨pullbackCompletionChangeOfFields S p d e g gε hpb H⟩
  · intro X Xε X₀ d e he Aε g gε hpb P Q
    obtain ⟨heSq, hpb'⟩ := key d e g gε hpb he
    let Pold := pullbackCompletionToOriginal S p hp d e g gε P
    let Qold := pullbackCompletionToOriginal S p hp d e g gε Q
    obtain ⟨b, hbFirst, hbBase⟩ :=
      schlessingerConditionS2_comparison_squareZero p hp hS2
        d.fst e.fst heSq (G.map g ≫ X.iso.inv) (G.map gε ≫ Xε.iso.inv) hpb' Pold Qold
    let EF := changeOfFieldsFiberEquivalence S p hp Aε
    let PF : q.Fiber Aε := ⟨P.apex, P.apex_eq⟩
    let QF : q.Fiber Aε := ⟨Q.apex, Q.apex_eq⟩
    let PN := EF.functor.obj PF
    let QN := EF.functor.obj QF
    let IP : q.Fiber Aε := ⟨⟨PN.val, Aε, eqToIso PN.property⟩, rfl⟩
    let IQ : q.Fiber Aε := ⟨⟨QN.val, Aε, eqToIso QN.property⟩, rfl⟩
    let ηP := EF.unitIso.app PF
    let ηQ := EF.unitIso.app QF
    let hηPdom : IP ⟶ PF := ηP.inv
    let hηQdom : IQ ⟶ QF := ηQ.inv
    change IP ⟶ PF at hηPdom
    change IQ ⟶ QF at hηQdom
    let incl := changeOfFieldsFiberInclusion S p Aε
    let bFiber : PN ⟶ QN := ⟨b, by
      apply IsHomLift.of_fac' p (𝟙 (G.obj Aε)) b PN.property QN.property
      simpa [Pold, Qold, pullbackCompletionToOriginal] using hbBase⟩
    let bI := incl.map bFiber
    let bChangedFiber : PF ⟶ QF := ηP.hom ≫ bI ≫ hηQdom
    let bChanged := bChangedFiber.val
    have hbase : q.map bChanged = eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm := by
      have := bChangedFiber.property
      exact IsHomLift.fac' q (𝟙 Aε) bChanged
    refine ⟨bChanged, ?_, hbase⟩
    apply CategoryTheory.Limits.CategoricalPullback.hom_ext
    · have hb : hηPdom.val.fst ≫ P.toFirst.fst =
          b ≫ hηQdom.val.fst ≫ Q.toFirst.fst := hbFirst
      have hunit : ηP.hom.val.fst ≫ hηPdom.val.fst = 𝟙 PF.val.fst :=
        congrArg (fun f : PF ⟶ PF => f.val.fst) ηP.hom_inv_id
      calc
        P.toFirst.fst = (ηP.hom.val.fst ≫ hηPdom.val.fst) ≫ P.toFirst.fst := by
          rw [hunit]
          simp
        _ = bChanged.fst ≫ Q.toFirst.fst := by
          exact (Category.assoc _ _ _).trans ((congrArg (ηP.hom.val.fst ≫ ·) hb).trans
            (((congrArg (ηP.hom.val.fst ≫ ·) (Category.assoc _ _ _).symm)).trans
              (Category.assoc _ _ _).symm))
    · change P.toFirst.snd = bChanged.snd ≫ Q.toFirst.snd
      rw [show P.toFirst.snd = _ from P.map_toFirst, show bChanged.snd = _ from hbase,
        show Q.toFirst.snd = _ from Q.map_toFirst]
      exact (by simp : eqToHom P.apex_eq ≫ g =
        (eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm) ≫ eqToHom Q.apex_eq ≫ g)

/-! ### Condition (RS) after a change of residue field -/

section

open CategoryTheory.Limits

universe uA vA uB vB uC vC uR vR wR

/-- A cospan in a categorical pullback has a fibre product whose image under the second
projection is again a fibre product, as soon as both component cospans have fibre products and
the image of the first one in the base category is a fibre product of the images. -/
private lemma categoricalPullback_pullback_of_componentPullbacks
    {A : Type uA} [Category.{vA} A] {D : Type uB} [Category.{vB} D]
    {E : Type uC} [Category.{vC} E]
    (p : E ⥤ A) (H : D ⥤ A)
    {X₁ X₂ X : CategoricalPullback p H}
    (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X)
    (c : PullbackCone f₁.fst f₂.fst) (hc : IsLimit c)
    (hcc : (p.map c.fst ≫ X₁.iso.hom) ≫ H.map f₁.snd =
      (p.map c.snd ≫ X₂.iso.hom) ≫ H.map f₂.snd)
    (hc' : IsLimit (PullbackCone.mk (p.map c.fst ≫ X₁.iso.hom)
      (p.map c.snd ≫ X₂.iso.hom) hcc))
    (d : PullbackCone f₁.snd f₂.snd) (hd : IsLimit d)
    (hd' : IsLimit (d.map H)) :
    ∃ t : PullbackCone f₁ f₂,
      Nonempty (IsLimit t) ∧ Nonempty (IsLimit (t.map (CategoricalPullback.π₂ p H))) := by
  let e : p.obj c.pt ≅ H.obj d.pt := hc'.conePointUniqueUpToIso hd'
  let Z : CategoricalPullback p H := ⟨c.pt, d.pt, e⟩
  let g₁ : Z ⟶ X₁ :=
    { fst := c.fst
      snd := d.fst
      w := by
        change p.map c.fst ≫ X₁.iso.hom = e.hom ≫ H.map d.fst
        have hh := hc'.conePointUniqueUpToIso_hom_comp hd' WalkingCospan.left
        change e.hom ≫ H.map d.fst = p.map c.fst ≫ X₁.iso.hom at hh
        exact hh.symm }
  let g₂ : Z ⟶ X₂ :=
    { fst := c.snd
      snd := d.snd
      w := by
        change p.map c.snd ≫ X₂.iso.hom = e.hom ≫ H.map d.snd
        have hh := hc'.conePointUniqueUpToIso_hom_comp hd' WalkingCospan.right
        change e.hom ≫ H.map d.snd = p.map c.snd ≫ X₂.iso.hom at hh
        exact hh.symm }
  let t : PullbackCone f₁ f₂ := PullbackCone.mk g₁ g₂ (by
    apply CategoricalPullback.hom_ext
    · simpa [g₁, g₂] using c.condition
    · simpa [g₁, g₂] using d.condition)
  have ht : IsLimit t := PullbackCone.isLimitAux' t (fun s => by
      have hF : s.fst.fst ≫ f₁.fst = s.snd.fst ≫ f₂.fst :=
        congrArg CategoricalPullback.Hom.fst s.condition
      have hD : s.fst.snd ≫ f₁.snd = s.snd.snd ≫ f₂.snd :=
        congrArg CategoricalPullback.Hom.snd s.condition
      let l₁ := PullbackCone.IsLimit.lift hc s.fst.fst s.snd.fst hF
      let l₂ := PullbackCone.IsLimit.lift hd s.fst.snd s.snd.snd hD
      have key : ∀ {Y : CategoricalPullback p H} (g : Z ⟶ Y) (s' : s.pt ⟶ Y),
          l₁ ≫ g.fst = s'.fst → l₂ ≫ g.snd = s'.snd →
          (p.map l₁ ≫ e.hom) ≫ H.map g.snd = (s.pt.iso.hom ≫ H.map l₂) ≫ H.map g.snd := by
        intro Y g s' h₁ h₂
        have hg : p.map g.fst ≫ Y.iso.hom = e.hom ≫ H.map g.snd := g.w
        rw [Category.assoc, ← hg, Category.assoc, ← H.map_comp, h₂, ← s'.w,
          ← Category.assoc, ← p.map_comp, h₁]
      have hw : p.map l₁ ≫ e.hom = s.pt.iso.hom ≫ H.map l₂ := by
        apply PullbackCone.IsLimit.hom_ext hd'
        · exact key g₁ s.fst (PullbackCone.IsLimit.lift_fst hc _ _ hF)
            (PullbackCone.IsLimit.lift_fst hd _ _ hD)
        · exact key g₂ s.snd (PullbackCone.IsLimit.lift_snd hc _ _ hF)
            (PullbackCone.IsLimit.lift_snd hd _ _ hD)
      refine ⟨⟨l₁, l₂, hw⟩, ?_, ?_, ?_⟩
      · apply CategoricalPullback.hom_ext
        · exact PullbackCone.IsLimit.lift_fst hc s.fst.fst s.snd.fst hF
        · exact PullbackCone.IsLimit.lift_fst hd s.fst.snd s.snd.snd hD
      · apply CategoricalPullback.hom_ext
        · exact PullbackCone.IsLimit.lift_snd hc s.fst.fst s.snd.fst hF
        · exact PullbackCone.IsLimit.lift_snd hd s.fst.snd s.snd.snd hD
      · intro m hm₁ hm₂
        have hm₁' : m ≫ g₁ = s.fst := by simpa [t] using hm₁
        have hm₂' : m ≫ g₂ = s.snd := by simpa [t] using hm₂
        apply CategoricalPullback.hom_ext
        · apply PullbackCone.IsLimit.hom_ext hc
          · exact (congrArg CategoricalPullback.Hom.fst hm₁').trans
              (PullbackCone.IsLimit.lift_fst hc _ _ hF).symm
          · exact (congrArg CategoricalPullback.Hom.fst hm₂').trans
              (PullbackCone.IsLimit.lift_snd hc _ _ hF).symm
        · apply PullbackCone.IsLimit.hom_ext hd
          · exact (congrArg CategoricalPullback.Hom.snd hm₁').trans
              (PullbackCone.IsLimit.lift_fst hd _ _ hD).symm
          · exact (congrArg CategoricalPullback.Hom.snd hm₂').trans
              (PullbackCone.IsLimit.lift_snd hd _ _ hD).symm)
  refine ⟨t, ⟨ht⟩, ⟨?_⟩⟩
  let iso : d ≅ t.map (CategoricalPullback.π₂ p H) :=
    PullbackCone.ext (Iso.refl _) (by
      change d.fst = (𝟙 d.pt) ≫ d.fst
      simp) (by
      change d.snd = (𝟙 d.pt) ≫ d.snd
      simp)
  exact IsLimit.ofIsoLimit hd iso

/-- A change of residue field preserves the Rim-Schlessinger condition (RS). -/
@[stacks 07WA "condition (RS)"]
public theorem changeOfFieldsProjection_satisfiesRS
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    (hp : SatisfiesRS p) :
    SatisfiesRS (changeOfFieldsProjection S p) := by
  constructor
  · exact changeOfFieldsProjection_isCofiberedInGroupoids S p hp.1
  · intro X₁ X₂ X f₁ f₂ hf₂
    let H := (comparisonFunctor.{u, v, w, x} S).functor
    have hf₂snd : Function.Surjective f₂.snd.hom := hf₂
    have hf₂' : Function.Surjective (p.map f₂.fst).hom :=
      changeOfFields_surjective_fst S p f₂ hf₂snd
    rcases hp.2 f₁.fst f₂.fst hf₂' with ⟨c, ⟨hc⟩, ⟨hcp⟩⟩
    let d₁ := ArtinianLocalAlgCat.pullbackFst_of_surjective f₁.snd f₂.snd (Or.inr hf₂snd)
    let d₂ := ArtinianLocalAlgCat.pullbackSnd_of_surjective f₁.snd f₂.snd (Or.inr hf₂snd)
    have hd : IsPullback d₁ d₂ f₁.snd f₂.snd :=
      ArtinianLocalAlgCat.isPullback_of_surjective f₁.snd f₂.snd (Or.inr hf₂snd)
    have hdp : IsPullback (H.map d₁) (H.map d₂) (H.map f₁.snd) (H.map f₂.snd) :=
      comparisonFunctor_map_isPullback S f₁.snd f₂.snd d₁ d₂ hd hf₂snd
    have hcc : (p.map c.fst ≫ X₁.iso.hom) ≫ H.map f₁.snd =
        (p.map c.snd ≫ X₂.iso.hom) ≫ H.map f₂.snd := by
      simp only [Category.assoc]
      rw [← f₁.w, ← f₂.w, ← p.map_comp_assoc, ← p.map_comp_assoc, c.condition]
    have hcp' : IsPullback (p.map c.fst) (p.map c.snd) (p.map f₁.fst) (p.map f₂.fst) :=
      IsPullback.of_isLimit hcp
    have hcIso : IsPullback (p.map c.fst ≫ X₁.iso.hom) (p.map c.snd ≫ X₂.iso.hom)
        (H.map f₁.snd) (H.map f₂.snd) :=
      hcp'.of_iso' (Iso.refl (p.obj c.pt)) X₁.iso.symm X₂.iso.symm X.iso.symm
        (by simp) (by simp)
        (CategoricalPullback.Hom.w' f₁).symm (CategoricalPullback.Hom.w' f₂).symm
    have hc' : IsLimit (PullbackCone.mk (p.map c.fst ≫ X₁.iso.hom)
        (p.map c.snd ≫ X₂.iso.hom) hcc) := hcIso.isLimit
    exact categoricalPullback_pullback_of_componentPullbacks
      p H f₁ f₂ c hc hcc hc' hd.cone hd.isLimit hdp.isLimit

end

end Deformation
