module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductChartEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.General
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperFlatNoetherianModel
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange

/-!
# A datum of the derived Chow lemma whose `W` is a given affine étale chart

Let `X` be an algebraic space separated and of finite presentation over a ring `A` and
`b : U ⟶ X` an étale morphism from an affine scheme. The proof of Stacks 0CTT applies the
derived Chow lemma at the points of `U`; this file produces a datum `(n, Z, V, E)` of Stacks 0CTR
whose `W = c⁻¹(V)` is `U` over `X` and whose `V` is an affine scheme, flat and of finite
presentation over `A`, with `W ⟶ V` a closed immersion of affine schemes.

The chart `U` is first made a clopen part of a surjective affine étale atlas `U ⊔ W₁`, the atlas
descends to a Noetherian model over a ring of finite type over `ℤ`, the datum over that ring is
built at the model atlas and base changed back, and finally `V` is shrunk to the basic open of
`𝔸ᵐ_A` cutting `U` out of `U ⊔ W₁`.

## Main results

* `AlgebraicGeometry.Space.exists_derivedChowDatum_of_affine_chart`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard

open DerivedChow

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] (hA : B.Contains (Spec (.of A)))

/-- **A datum of the derived Chow lemma whose `W` is a given affine étale chart.** Let `X` be an
algebraic space separated and of finite presentation over `A` and `b : U₀ ⟶ X` an étale
morphism from an affine scheme with a point `u`. Then there is a datum of Stacks 0CTR on `X`
whose open `V` is an affine scheme `V₀`, flat and of finite presentation over `A`, and whose
`W = c⁻¹(V)` is `U₀` over `X`, with `W ⟶ V` a closed immersion `U₀ ⟶ V₀`. -/
theorem exists_derivedChowDatum_of_affine_chart (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (hsep : IsSeparated B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X).hom)
    (hfp : IsFinitePresentation B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X).hom)
    {U₀ : BigFppfOver B (Spec (.of A)) hA}
    (hU₀ : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U₀))
    (b : yoneda.obj U₀ ⟶ X.1)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf b)
    (u : points B (Spec (.of A)) hA (yoneda.obj U₀)) :
    ∃ (x : points B _ hA X.1) (D : DerivedChowDatum X x) (V₀ : BigFppfOver B (Spec (.of A)) hA)
      (_ : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj V₀))
      (eV : D.V ≅ schemeSpace V₀) (eW : schemeSpace U₀ ≅ overOpen D.i D.v)
      (g : U₀ ⟶ V₀),
      schemeSpaceMap g = eW.hom ≫ overOpenToOpen D.i D.v ≫ eV.hom ∧
      (eW.hom ≫ overOpenι D.i D.v ≫ D.i ≫ productFst X D.n D.contains).hom = b ∧
      Flat (B.inclusion.map V₀.hom) ∧ LocallyOfFinitePresentation (B.inclusion.map V₀.hom) ∧
      _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B (Spec (.of A)) hA).map g) := by
  let Q := BigFppfOver.toScheme B (Spec (.of A)) hA
  obtain ⟨W₁, c, hW₁, hcs, hce⟩ := exists_isAffine_isEtale_isSurjective_chart_of_isQuasiCompact
    B (Spec (.of A)) hA X.2 (toBase B (Spec (.of A)) hA X).hom hfp.2.1
  obtain ⟨T, cU, p, hT, hcUp, hpe, hps, hcU, s, hs⟩ := exists_isAffine_atlas_of_chart B _ hA X.2
    hU₀ hW₁ b c hb ((isEtale_iff_presheaf_of_yoneda B _ hA c).1 hce) hcs
  obtain ⟨A₀, _, _, _, hA₀, X₀', hX₀', f₀, hfp₀, hsep₀, W₀, q, hW₀, hqs, hqe, hcompat⟩ :=
    exists_finiteType_model_of_atlas B X.2 (toBase B (Spec (.of A)) hA X).hom hfp p hT hps hpe
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  let g : B.obj hA ⟶ B.obj hA₀ :=
    B.inclusion.preimage (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))
  obtain ⟨eX, φ, heX⟩ := hcompat g (B.inclusion.map_preimage _)
  let X₀ : AlgebraicSpaces B (Spec (.of A₀)) hA₀ := ⟨X₀', hX₀'⟩
  have hf₀ : (toBase B (Spec (.of A₀)) hA₀ X₀).hom = f₀ :=
    (isTerminal_yoneda_obj_base B (Spec (.of A₀)) hA₀).hom_ext _ _
  let x : points B _ hA X.1 := pointsMap B _ hA _ b u
  let x₀ := pointsMap B (Spec (.of A₀)) hA₀ _ (OverShriek.relocalizeRestrictCounit g X₀.1)
      (pointsRelocalize B (Spec (.of A)) (Spec (.of A₀)) hA hA₀ g _
        (pointsMap B (Spec (.of A)) hA X.1 eX.hom x))
  obtain ⟨a₀, ha₀⟩ := isSurjective_of_presheafSurjective B _ hA₀ q hqs x₀
  have hD₀ := exists_derivedChowDatum_of_chart B hA₀ X₀ (hf₀ ▸ hsep₀ hsep) (hf₀ ▸ hfp₀) q hW₀ hqe a₀
  rw [ha₀] at hD₀
  obtain ⟨D₀, hTor, eW₀, heW₀, AS, eV₀, jA, hAS, hASf, hASl, hjA, hjAc⟩ := hD₀
  let D := DerivedChowDatum.baseChange g D₀ eX hTor x rfl
  -- `W ≅ h_T` over `X`.
  let ιW : (overOpen (DerivedChowDatum.bcI g D₀ eX) (DerivedChowDatum.bcV g D₀)).1 ≅ yoneda.obj T :=
    DerivedChowDatum.bcOverOpenIso g D₀ eX ≪≫ (OverShriek.relocalizeRestrict g).mapIso eW₀.symm ≪≫
      (OverShriek.restrictYonedaIso g W₀).symm ≪≫ yoneda.mapIso φ
  have hp : yoneda.map φ.hom ≫ p = (OverShriek.restrictYonedaIso g W₀).hom ≫
      (OverShriek.relocalizeRestrict g).map q ≫ eX.inv := by
    rw [← cancel_mono eX.hom, Category.assoc, heX, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      yoneda.map_id, Category.id_comp]
  have hιW : ιW.hom ≫ p = (overOpenι (DerivedChowDatum.bcI g D₀ eX) (DerivedChowDatum.bcV g D₀) ≫
      DerivedChowDatum.bcI g D₀ eX ≫ productFst X D₀.n (DerivedChowDatum.bcContains D₀ g)).hom := by
    rw [DerivedChowDatum.bc_overOpen_comp_fst, ← heW₀]
    simp only [ιW, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc, hp, Iso.inv_hom_id_assoc, Functor.map_comp]
  -- `V ≅ h_{AS'}`.
  let eV₀' : D₀.V.1 ≅ yoneda.obj AS := (ObjectProperty.ι _).mapIso eV₀
  let AS' := (Over.pullback g).obj AS
  let ιV : (relocalizeRestrictSpace g D₀.V).1 ≅ yoneda.obj AS' :=
    (OverShriek.relocalizeRestrict g).mapIso eV₀' ≪≫ (OverShriek.restrictYonedaIso g AS).symm
  let jT : T ⟶ AS' := φ.inv ≫ (Over.pullback g).map jA
  have hjT : ιW.inv ≫ (overOpenToOpen (DerivedChowDatum.bcI g D₀ eX)
      (DerivedChowDatum.bcV g D₀)).hom ≫ ιV.hom = yoneda.map jT := by
    have h₁ : (DerivedChowDatum.bcOverOpenIso g D₀ eX).inv ≫ (overOpenToOpen
        (DerivedChowDatum.bcI g D₀ eX) (DerivedChowDatum.bcV g D₀)).hom =
        (OverShriek.relocalizeRestrict g).map (overOpenToOpen D₀.i D₀.v).hom := by
      rw [← DerivedChowDatum.bcOverOpenIso_hom_toOpen, Iso.inv_hom_id_assoc]
    have h₂ : eW₀.hom ≫ (overOpenToOpen D₀.i D₀.v).hom ≫ eV₀'.hom = yoneda.map jA := by
      show eW₀.hom ≫ (overOpenToOpen D₀.i D₀.v).hom ≫ eV₀.hom.hom = _
      rw [hjAc]
      exact Iso.hom_inv_id_assoc eW₀ (yoneda.map jA)
    have h₃ := OverShriek.restrictYonedaIso_naturality g jA
    simp only [ιW, ιV, jT, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc, Functor.map_comp]
    rw [reassoc_of% h₁, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      Category.assoc eW₀.hom, h₂, ← reassoc_of% h₃, Iso.hom_inv_id, Category.comp_id]
  -- `AS'` is affine, flat and of finite presentation over `A`, and `T ⟶ AS'` is a closed
  -- immersion.
  let _ : PreservesLimitsOfShape WalkingCospan B.inclusion := by infer_instance
  have hpbAS := (IsPullback.of_hasPullback AS.hom g).map B.inclusion
  have : IsAffine (B.inclusion.obj (B.obj hA₀)) := inferInstanceAs (IsAffine (Spec (.of A₀)))
  have : IsAffine (B.inclusion.obj (B.obj hA)) := inferInstanceAs (IsAffine (Spec (.of A)))
  have : IsAffine (B.inclusion.obj AS.left) := hAS
  have : _root_.AlgebraicGeometry.IsAffineHom (B.inclusion.map AS'.hom) :=
    MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsAffineHom) hpbAS inferInstance
  have hAS'a : IsAffine (Q.obj AS') :=
    _root_.AlgebraicGeometry.isAffine_of_isAffineHom (B.inclusion.map AS'.hom)
  have hAS'f : Flat (B.inclusion.map AS'.hom) :=
    MorphismProperty.of_isPullback (P := @Flat) hpbAS hASf
  have hAS'l : LocallyOfFinitePresentation (B.inclusion.map AS'.hom) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpbAS hASl
  have hpbj := (OverShriek.isPullback_pullback_map g jA).map B.inclusion
  have : _root_.AlgebraicGeometry.IsClosedImmersion (Q.map ((Over.pullback g).map jA)) :=
    MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsClosedImmersion)
      hpbj.flip hjA
  have : _root_.AlgebraicGeometry.IsClosedImmersion (Q.map jT) := by
    simp only [jT, Functor.map_comp]; infer_instance
  -- Shrink `AS'` to a basic open `V₀` with `T ×_{AS'} V₀ = U₀`.
  obtain ⟨V₀, o, gU, hV₀, ho, hgU, hsq⟩ :=
    exists_isPullback_basicOpen_of_isClosedImmersion B _ hA cU jT s hs
  let j : representedSpace V₀ ⟶ D.V := ObjectProperty.homMk (yoneda.map o ≫ ιV.inv)
  have hj : IsOpenImmersion B _ hA j.hom :=
    MorphismProperty.RespectsIso.postcomp _ ιV.inv (yoneda.map o)
      (isOpenImmersion_yoneda_map B _ hA o ho)
  have hB : IsPullback (yoneda.map cU ≫ ιW.inv) (yoneda.map gU)
      (overOpenToOpen (DerivedChowDatum.bcI g D₀ eX) (DerivedChowDatum.bcV g D₀)).hom j.hom := by
    refine (hsq.map yoneda).flip.of_iso (Iso.refl _) ιW.symm (Iso.refl _) ιV.symm (by simp)
      (by simp) ?_ (Category.id_comp _).symm
    rw [← hjT]
    simp
  have hA' := DerivedChowDatum.isPullback_restrictOpenMap D j
  obtain ⟨eWp, heWp₁, heWp₂⟩ : ∃ e : yoneda.obj U₀ ≅ (overOpen D.i (j ≫ D.v)).1,
      e.hom ≫ (DerivedChowDatum.restrictOpenMap D j).hom = yoneda.map cU ≫ ιW.inv ∧
        e.hom ≫ (overOpenToOpen D.i (j ≫ D.v)).hom = yoneda.map gU :=
    ⟨_, IsPullback.isoIsPullback_hom_fst _ _ hB hA', IsPullback.isoIsPullback_hom_snd _ _ hB hA'⟩
  let D' := D.restrictOpen j hj (pointsMap B _ hA _ eWp.hom u)
  refine ⟨_, D', V₀, hV₀, Iso.refl _, ObjectProperty.isoMk _ eWp, gU, ?_, ?_, ?_, ?_, hgU⟩
  · refine ObjectProperty.hom_ext _ ?_
    show yoneda.map gU = eWp.hom ≫ (overOpenToOpen D.i (j ≫ D.v)).hom ≫ 𝟙 _
    rw [Category.comp_id, heWp₂]
  · have h₁ : (overOpenι D.i (j ≫ D.v)).hom =
        (DerivedChowDatum.restrictOpenMap D j).hom ≫ (overOpenι D.i D.v).hom :=
      (pullback.lift_fst _ _ _).symm
    show eWp.hom ≫ (overOpenι D.i (j ≫ D.v)).hom ≫ (D.i ≫ productFst X D.n D.contains).hom = b
    rw [h₁, Category.assoc, reassoc_of% heWp₁]
    show yoneda.map cU ≫ ιW.inv ≫ (overOpenι (DerivedChowDatum.bcI g D₀ eX)
      (DerivedChowDatum.bcV g D₀) ≫ DerivedChowDatum.bcI g D₀ eX ≫
        productFst X D₀.n (DerivedChowDatum.bcContains D₀ g)).hom = b
    rw [← hιW, Iso.inv_hom_id_assoc, hcUp]
  all_goals rw [← BigFppfOver.toScheme_map_comp_hom o]; infer_instance

end AlgebraicGeometry.Space

end
