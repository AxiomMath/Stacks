module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.HenselianDatumSplitting
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.HenselianEndgame
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.Defs
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Basic

/-!
# Descent of the finite part over a henselian pair

Let `(A, I)` be a henselian pair, `S = Spec A`, `Z = Spec (A/I)` its closed fibre, and
`f : X ⟶ S` a finite morphism. Let `D` be a descent datum relative to `f` whose scheme `V` is
finite and étale over `X`. If the base change of `D` to `Z` is effective, with descended scheme
`U_Z` finite étale over `Z`, then `D` itself is effective with descended scheme finite étale over
`S`.

## Main results

* `Stacks.Etale.eq_of_pullbackFst_comp_eq`: two morphisms `M ⟶ U` over an étale `U ⟶ T` agree
  as soon as they agree on the closed fibre of `M`, when `M ⟶ Spec A` is closed and `I` lies in
  the Jacobson radical.
* `AlgebraicGeometry.DescentDatum.exists_descended_isFinite_etale_of_henselianPair`: a descent
  datum with finite étale scheme over a henselian pair is effective, with finite étale descended
  scheme, as soon as its closed fibre is.
* `AlgebraicGeometry.DescentDatum.exists_descended_restrictOpen_isFinite_etale_of_henselianPair`:
  the same for the restriction of a descent datum with étale scheme `V` to a transition-invariant
  open `W` finite over `S`, when the complementary open `W'` has empty closed fibre. The descended
  scheme of the closed fibre of `V` then also descends the closed fibre of `W`.

## References

* [Stacks, Tag 0BTP]
-/

@[expose] public section

noncomputable section

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- Let `I` be an ideal of `A` inside the Jacobson radical and `m : M ⟶ Spec A` a closed
morphism. Two morphisms `g₁ g₂ : M ⟶ U` over an étale `t : U ⟶ T` that agree on the closed fibre
`M ×_{Spec A} Spec (A/I)` are equal. -/
theorem eq_of_pullbackFst_comp_eq {A : Type u} [CommRing A] {I : Ideal A}
    (hI : I ≤ (⊥ : Ideal A).jacobson) {M U T : Scheme.{u}} (m : M ⟶ Spec (.of A))
    (hm : IsClosedMap m.base) (t : U ⟶ T) [Etale t] (g₁ g₂ : M ⟶ U)
    (hw : g₁ ≫ t = g₂ ≫ t)
    (h : pullback.fst m (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ g₁ =
      pullback.fst m (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ g₂) :
    g₁ = g₂ := by
  set k := pullback.fst m (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  have hfac : k ≫ pullback.lift g₁ g₂ hw = (k ≫ g₁) ≫ pullback.diagonal t := by
    apply pullback.hom_ext
    · simp
    · simp [h]
  have hopen : IsOpen ((pullback.lift g₁ g₂ hw).base ⁻¹'
      Set.range (pullback.diagonal t).base) :=
    (IsOpenImmersion.isOpen_range (pullback.diagonal t)).preimage
      (pullback.lift g₁ g₂ hw).base.hom.continuous
  have hsub : Set.range k.base ⊆
      (pullback.lift g₁ g₂ hw).base ⁻¹' Set.range (pullback.diagonal t).base := by
    rintro x ⟨y, rfl⟩
    exact ⟨(k ≫ g₁).base y, by simpa using (congrArg (fun q => q.base y) hfac).symm⟩
  have hall : Set.range (pullback.lift g₁ g₂ hw).base ⊆
      Set.range (pullback.diagonal t).base := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨x', hx', hspec⟩ := hm.exists_specializes_mem_preimage
      (fun y ↦ by
        obtain ⟨z, hz, hyz⟩ := PrimeSpectrum.exists_specializes_mem_zeroLocus_of_le_jacobson hI y
        exact ⟨z, mem_range_quotient_of_mem_zeroLocus I hz, hyz⟩) x
    refine hspec.mem_open hopen (hsub ?_)
    rwa [Scheme.Pullback.range_fst]
  obtain ⟨l, hl⟩ : ∃ l : M ⟶ U, l ≫ pullback.diagonal t = pullback.lift g₁ g₂ hw :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hall⟩
  have h1 : g₁ = l := by
    simpa [pullback.lift_fst] using (congrArg (· ≫ pullback.fst t t) hl).symm
  have h2 : g₂ = l := by
    simpa [pullback.lift_snd] using (congrArg (· ≫ pullback.snd t t) hl).symm
  rw [h1, h2]

end Stacks.Etale

namespace AlgebraicGeometry.DescentDatum

open CategoryTheory CategoryTheory.Limits

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of A)}

/-- Let `(A, I)` be a henselian pair and `f : X ⟶ Spec A` finite. A descent datum `D` relative to
`f`, whose scheme is finite and étale over `X`, is effective with finite étale descended scheme as
soon as its base change to the closed fibre `Spec (A/I)` is effective with finite étale descended
scheme. -/
theorem exists_descended_isFinite_etale_of_henselianPair (hI : HenselianPair A I)
    [IsFinite f] (D : DescentDatum f) [IsFinite D.over.hom] [Etale D.over.hom]
    (QZ : (D.changeDatum (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Descended)
    [IsFinite QZ.base.hom] [Etale QZ.base.hom] :
    ∃ Q : D.Descended, IsFinite Q.base.hom ∧ Etale Q.base.hom := by
  have h09ZS := finiteEtaleBaseChange_isEquivalence_of_henselianPair A I hI
  let QZobj : MorphismProperty.Over ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
      (Spec (CommRingCat.of (A ⧸ I))) :=
    MorphismProperty.Over.mk ⊤ QZ.base.hom ⟨inferInstance, inferInstance⟩
  obtain ⟨Uobj, ⟨eObj⟩⟩ := Functor.EssSurj.mem_essImage
    (MorphismProperty.Over.pullback ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) QZobj
  have : IsFinite Uobj.hom := Uobj.prop.1
  have : Etale Uobj.hom := Uobj.prop.2
  let e : pullback Uobj.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
      QZ.base.left :=
    (MorphismProperty.Over.forget _ ⊤ _ ⋙ CategoryTheory.Over.forget _).mapIso eObj
  have he : e.hom ≫ QZ.base.hom =
      pullback.snd Uobj.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    MorphismProperty.Over.w eObj.hom
  obtain ⟨L, hL1, hL2⟩ : ∃ L : pullback (pullback.snd Uobj.hom f)
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⟶
        pullback Uobj.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))),
      L ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst Uobj.hom f ∧
      L ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd f _ :=
    ⟨pullback.lift (pullback.fst _ _ ≫ pullback.fst Uobj.hom f)
      (pullback.snd _ _ ≫ pullback.snd f _) (by
        simp only [Category.assoc]
        rw [pullback.condition (f := Uobj.hom),
          pullback.condition_assoc (f := pullback.snd Uobj.hom f),
          pullback.condition (f := f)]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hG : IsPullback L (pullback.snd _ _) (pullback.snd Uobj.hom _)
      (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
    refine IsPullback.of_right ?_ hL2 (IsPullback.of_hasPullback _ _)
    rw [hL1, ← pullback.condition]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
  have hG' : IsPullback (pullback.snd _ _) (L ≫ e.hom)
      (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) QZ.base.hom := by
    have h2 : IsPullback e.hom (pullback.snd _ _) QZ.base.hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
    have := hG.paste_horiz h2
    rw [Category.comp_id] at this
    exact this.flip
  obtain ⟨θ, hθ1, hθ2⟩ : ∃ θ : (D.changeDatum (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk I)))).over.left ≅ pullback (pullback.snd Uobj.hom f)
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))),
      θ.hom ≫ pullback.snd _ _ = (D.changeDatum _).over.hom ∧ θ.hom ≫ L ≫ e.hom = QZ.proj :=
    ⟨QZ.isPullback.isoIsPullback _ _ hG', IsPullback.isoIsPullback_hom_fst _ _ _ _,
      IsPullback.isoIsPullback_hom_snd _ _ _ _⟩
  let E := (changePullbackFunctor f (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk I)))).objIso D
  have hEinv : E.inv.left ≫ (D.changeDatum _).over.hom =
      pullback.snd D.over.hom (pullback.fst f _) := Over.w E.inv
  have hEhi : E.hom.left ≫ E.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have hEih : E.inv.left ≫ E.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have : IsIso (E.inv.left ≫ θ.hom) := by
    have : IsIso E.inv.left := ⟨⟨E.hom.left, hEih, hEhi⟩⟩
    infer_instance
  obtain ⟨φ, hφiso, hφ, hφfac, -⟩ := Stacks.Etale.exists_isIso_of_isFinite_of_henselianPair hI f
    (pullback.fst f _) (pullback.snd f _) (IsPullback.of_hasPullback _ _) D.over.hom
    (pullback.snd Uobj.hom f) (E.inv.left ≫ θ.hom)
    (by rw [Category.assoc, hθ1, hEinv])
  have hkey : E.hom.left ≫ pullback.fst D.over.hom (pullback.fst f _) ≫ φ ≫
        pullback.fst Uobj.hom f =
      QZ.proj ≫ e.inv ≫ pullback.fst Uobj.hom _ := by
    rw [reassoc_of% hφfac]
    simp only [reassoc_of% hEhi]
    rw [← hL1, ← hθ2]
    simp
  have hpu : φ ≫ pullback.fst Uobj.hom f ≫ Uobj.hom = D.over.hom ≫ f := by
    rw [pullback.condition, reassoc_of% hφ]
  have hsq : IsPullback D.over.hom (φ ≫ pullback.fst Uobj.hom f) f (Over.mk Uobj.hom).hom :=
    (IsPullback.of_hasPullback Uobj.hom f).flip.of_iso (asIso φ).symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp [← hφ]) (by simp) (by simp) (by simp)
  refine ⟨DescentDatum.Descended.mk (Over.mk Uobj.hom) (φ ≫ pullback.fst Uobj.hom f) hsq ?_,
    ‹IsFinite Uobj.hom›, ‹Etale Uobj.hom›⟩
  · refine Stacks.Etale.eq_of_pullbackFst_comp_eq hI.le_jacobson
      (pullback.snd (D.over.hom ≫ f) f ≫ f) (Scheme.Hom.isClosedMap _) Uobj.hom _ _ ?_ ?_
    · simp only [Category.assoc]
      rw [hpu, reassoc_of% D.transitionPullbackIso_hom_comp_pullbackSnd]
      exact (pullback.condition (f := D.over.hom ≫ f) (g := f)).symm
    · obtain ⟨l₁, hl₁1, hl₁2⟩ : ∃ l : pullback (pullback.snd (D.over.hom ≫ f) f ≫ f)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶
            pullback D.over.hom (pullback.fst f _),
          l ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ f ∧
          l ≫ pullback.snd _ _ ≫ pullback.snd f _ = pullback.snd _ _ :=
        ⟨pullback.lift (pullback.fst _ _ ≫ pullback.fst _ f)
          (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ f ≫ D.over.hom)
            (pullback.snd _ _) (by
              simp only [Category.assoc]
              rw [pullback.condition (f := D.over.hom ≫ f)]
              exact pullback.condition))
          (by rw [pullback.lift_fst, Category.assoc]),
          pullback.lift_fst _ _ _, by rw [pullback.lift_snd_assoc, pullback.lift_snd]⟩
      obtain ⟨l₂, hl₂1, hl₂2⟩ : ∃ l : pullback (pullback.snd (D.over.hom ≫ f) f ≫ f)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶ pullback f _,
          l ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.snd _ f ∧
          l ≫ pullback.snd _ _ = pullback.snd _ _ :=
        ⟨pullback.lift (pullback.fst _ _ ≫ pullback.snd _ f) (pullback.snd _ _)
          (by rw [Category.assoc]; exact pullback.condition),
          pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
      obtain ⟨l, hl1, hl2⟩ : ∃ l : pullback (pullback.snd (D.over.hom ≫ f) f ≫ f)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶
            pullback ((D.changeDatum _).over.hom ≫ pullback.snd f _) (pullback.snd f _),
          l ≫ pullback.fst _ _ = l₁ ≫ E.inv.left ∧ l ≫ pullback.snd _ _ = l₂ :=
        ⟨pullback.lift (l₁ ≫ E.inv.left) l₂
          (by rw [Category.assoc, reassoc_of% hEinv, hl₁2, hl₂2]),
          pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
      have hl : l ≫ (changePullbackFunctor f _).sourceMap D = pullback.fst _ _ := by
        apply pullback.hom_ext
        · rw [Category.assoc, (changePullbackFunctor f _).sourceMap_fst D, reassoc_of% hl1]
          have h : E.inv.left ≫ E.hom.left ≫ pullback.fst D.over.hom
              (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) =
              pullback.fst D.over.hom _ := by
            rw [reassoc_of% hEih]
          exact (congrArg (l₁ ≫ ·) h).trans hl₁1
        · rw [Category.assoc, (changePullbackFunctor f _).sourceMap_snd D, reassoc_of% hl2,
            hl₂1]
      rw [← hl]
      simp only [Category.assoc]
      rw [← reassoc_of% ((changePullbackFunctor f _).gluing D),
        reassoc_of% ((changePullbackFunctor f _).targetMap_snd D), hkey,
        reassoc_of% QZ.proj_invariant, ← hkey,
        ← reassoc_of% ((changePullbackFunctor f _).sourceMap_fst D)]

section RestrictOpen

attribute [local implicit_reducible] restrictOpen

/-- Let `(A, I)` be a henselian pair, `f : X ⟶ Spec A` finite, and `D` a descent datum relative
to `f` with scheme `V` étale over `X`. Let `W` and `W'` be complementary opens of `V`, with `W`
transition-invariant and finite over `Spec A`, and `W'` with empty closed fibre. If the base
change of `D` to the closed fibre is effective with finite étale descended scheme, then the
restriction of `D` to `W` is effective with descended scheme finite étale over `Spec A`. -/
theorem exists_descended_restrictOpen_isFinite_etale_of_henselianPair (hI : HenselianPair A I)
    [IsFinite f] (D : DescentDatum f) [Etale D.over.hom] (W W' : D.over.left.Opens)
    (hWW' : IsCompl W W') (hW : D.IsTransitionInvariant W)
    (hfin : IsFinite ((W.ι ≫ D.over.hom) ≫ f))
    (hempty : IsEmpty (pullback ((W'.ι ≫ D.over.hom) ≫ f)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u}))
    (QZ : (D.changeDatum (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Descended)
    [IsFinite QZ.base.hom] [Etale QZ.base.hom] :
    ∃ Q : (D.restrictOpen W hW).Descended, IsFinite Q.base.hom ∧ Etale Q.base.hom := by
  have : Etale (D.restrictOpen W hW).over.hom := D.etale_restrictOpen_over_hom W hW
  have : IsFinite (D.restrictOpen W hW).over.hom :=
    MorphismProperty.of_postcomp @IsFinite (W' := @IsSeparated) (W.ι ≫ D.over.hom) f
      inferInstance hfin
  have hr : Set.range (pullback.fst D.over.hom
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) ⊆
      Set.range W.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    by_contra hv
    have hv' : pullback.fst D.over.hom _ p ∈ W' := by
      have : pullback.fst D.over.hom
          (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) p ∈
          (W : Set D.over.left) ∪ (W' : Set D.over.left) := by
        rw [union_coe_eq_univ_of_isCompl hWW']
        exact Set.mem_univ _
      exact this.resolve_left hv
    obtain ⟨w, hw⟩ : pullback.fst D.over.hom _ p ∈ Set.range W'.ι := by
      rwa [Scheme.Opens.range_ι]
    obtain ⟨t, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := (W'.ι ≫ D.over.hom) ≫ f) (g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      w (pullback.snd f _ (pullback.snd D.over.hom _ p)) (by
        simp only [Scheme.Hom.comp_apply, hw]
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
          ← Scheme.Hom.comp_apply, ← pullback.condition, ← Category.assoc,
          pullback.condition, Category.assoc])
    exact hempty.elim t
  let k := (D.restrictOpenHom W hW).hom ()
  let y := pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  have hm1 : ((Over.pullback y).map k).left ≫ pullback.fst D.over.hom y =
      pullback.fst (D.restrictOpen W hW).over.hom y ≫ W.ι :=
    pullback.lift_fst _ _ _
  have hm2 : ((Over.pullback y).map k).left ≫ pullback.snd D.over.hom y =
      pullback.snd (D.restrictOpen W hW).over.hom y := Over.w ((Over.pullback y).map k)
  let n : pullback D.over.hom y ⟶ pullback (D.restrictOpen W hW).over.hom y :=
    pullback.lift (IsOpenImmersion.lift W.ι (pullback.fst D.over.hom y) hr)
      (pullback.snd D.over.hom y) (by
        change IsOpenImmersion.lift W.ι (pullback.fst D.over.hom y) hr ≫ W.ι ≫ D.over.hom = _
        rw [IsOpenImmersion.lift_fac_assoc, pullback.condition])
  have hmiso : IsIso ((Over.pullback y).map k).left := by
    refine ⟨⟨n, ?_, ?_⟩⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← cancel_mono W.ι,
          Category.assoc, IsOpenImmersion.lift_fac, hm1]
      · rw [Category.assoc, pullback.lift_snd, Category.id_comp, hm2]
    · apply pullback.hom_ext
      · rw [Category.assoc, hm1, pullback.lift_fst_assoc, IsOpenImmersion.lift_fac,
          Category.id_comp]
      · rw [Category.assoc, hm2, pullback.lift_snd, Category.id_comp]
  let g := (changePullbackFunctor f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).functor.map (D.restrictOpenHom W hW)
  have : IsIso ((Over.pullback y).map k) := by
    have : IsIso ((Over.forget _).map ((Over.pullback y).map k)) := hmiso
    exact isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso (g.hom ()) := by
    have : g.hom () = ((changePullbackFunctor f _).objIso (D.restrictOpen W hW)).hom ≫
        (Over.pullback y).map k ≫ ((changePullbackFunctor f _).objIso D).inv := by
      rw [reassoc_of% ((changePullbackFunctor f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map (D.restrictOpenHom W hW)),
        Iso.hom_inv_id, Category.comp_id]
    rw [this]
    infer_instance
  have : IsIso (g.hom ()).left := inferInstanceAs (IsIso ((Over.forget _).map (g.hom ())))
  have hgw : (g.hom ()).left ≫ (D.changeDatum _).over.hom =
      ((D.restrictOpen W hW).changeDatum _).over.hom := Over.w (g.hom ())
  let QZ' : ((D.restrictOpen W hW).changeDatum
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Descended :=
    { base := QZ.base
      proj := (g.hom ()).left ≫ QZ.proj
      isPullback := QZ.isPullback.of_iso (asIso (g.hom ()).left).symm (Iso.refl _) (Iso.refl _)
        (Iso.refl _) (by rw [← hgw]; simp) (by simp) (by simp) (by simp)
      proj_invariant := Descended.comp_proj_invariant g QZ }
  have : IsFinite QZ'.base.hom := ‹IsFinite QZ.base.hom›
  have : Etale QZ'.base.hom := ‹Etale QZ.base.hom›
  exact exists_descended_isFinite_etale_of_henselianPair hI (D.restrictOpen W hW) QZ'

end RestrictOpen

end AlgebraicGeometry.DescentDatum

end
