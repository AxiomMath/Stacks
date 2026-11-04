module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.EtaleCover.FiniteOpenUnion
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.EtaleCover.EtaleDecomposition

/-!
# The surjective étale chart of the finite part

The chart family over an étale decomposition, the reduction from algebraic spaces to the
representable and scheme cases, open representations of points of the finite part with values
in algebraically closed fields, and the main result
`AlgebraicGeometry.Space.exists_surjective_etale_chart_finiteOpenSubspacePresheaf` — Stacks
04QG.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FinitePartChart

attribute [local instance] Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
  Stacks.Morphisms.isFinite_respectsIso

attribute [local instance] schemeSizeBelow_isClosedUnderIsomorphisms
  schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan
  BigFppfSite.hasPullbacks_schemes
  Space.preservesLimitsOfShape_walkingCospan_toScheme

private theorem pairwise_disjoint_preimage_subtype {P Q : Scheme.{u}} (k : P ⟶ Q)
    {I : Type*} {D : I → Q.Opens} (hD : Pairwise (fun i j ↦ Disjoint (D i) (D j)))
    (J : Set I) : Pairwise (fun i j : J ↦ Disjoint (k ⁻¹ᵁ D i.1) (k ⁻¹ᵁ D j.1)) := by
  intro i j hij
  apply TopologicalSpace.Opens.coe_disjoint.mp
  have h := TopologicalSpace.Opens.coe_disjoint.mpr (hD (Subtype.coe_injective.ne hij))
  exact Set.disjoint_left.mpr fun x hx hy ↦ Set.disjoint_left.mp h hx hy

private theorem exists_site_chart_family_of_etale_decomposition
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    {U : Scheme.{u}}
    (a : U ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    [Etale a] (u : U)
    {I : Type u} [Finite I]
    (D : I → (pullback ((BigFppfOver.toScheme B S hS).map f) a).Opens)
    (hD : Pairwise (fun i j ↦ Disjoint (D i) (D j)))
    (hfin : ∀ i, IsFinite ((D i).ι ≫
      pullback.snd ((BigFppfOver.toScheme B S hS).map f) a)) :
    ∃ (V : BigFppfOver B S hS) (b : V ⟶ Y)
      (j : (BigFppfOver.toScheme B S hS).obj V ⟶ U)
      (v : (BigFppfOver.toScheme B S hS).obj V)
      (k : (BigFppfOver.toScheme B S hS).obj (pullback b f) ⟶
        pullback ((BigFppfOver.toScheme B S hS).map f) a),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsOpenImmersion j ∧ j v = u ∧
      j ≫ a = (BigFppfOver.toScheme B S hS).map b ∧
      Etale ((BigFppfOver.toScheme B S hS).map b) ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤
        ((BigFppfOver.toScheme B S hS).obj Y).size ∧
      k ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map f) a =
        (BigFppfOver.toScheme B S hS).map (pullback.snd b f) ∧
      k ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map f) a =
        (BigFppfOver.toScheme B S hS).map (pullback.fst b f) ≫ j ∧
      (∀ J : Set I, ∃ (W : BigFppfOver B S hS)
        (h : W ⟶ pullback b f)
        (z : Space.FiniteOpenSubspace B S hS (schemeSpaceMap f)
          (schemeSpace V))
        (p : yoneda.obj V ⟶
          (Space.finiteOpenSubspacePresheaf B S hS
            (schemeSpaceMap f)).toFunctor),
        z.toBase = schemeSpaceMap b ∧
        HEq z.subspace (Subfunctor.range
          (yoneda.map h ≫ ((IsPullback.of_hasPullback b f).map yoneda).isoPullback.hom)) ∧
        (Space.finiteOpenSubspacePresheaf B S hS
          (schemeSpaceMap f)).sections V (yonedaEquiv p) = z ∧
        p ≫ (Space.finiteOpenSubspacePresheaf B S hS
          (schemeSpaceMap f)).baseMap = yoneda.map b ∧
        (MorphismProperty.inverseImage (@Etale.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p ∧
        ∃ (e : (BigFppfOver.toScheme B S hS).obj W ≅
          ∐ fun i : J ↦ ((k ⁻¹ᵁ D i.1)).toScheme),
          e.hom ≫ Sigma.desc (fun i : J ↦ (k ⁻¹ᵁ D i.1).ι) =
            (BigFppfOver.toScheme B S hS).map h) := by
  let q := BigFppfOver.toScheme B S hS
  obtain ⟨V, b, j, v, k, hV, hj, hv, hb, hbe, hsize, hk, sq⟩ :=
    exists_site_pullback_neighborhood B S hS f a u
  refine ⟨V, b, j, v, k, hV, hj, hv, hb, hbe, hsize, hk, sq.w, ?_⟩
  intro J
  let E : J → (q.obj (pullback b f)).Opens := fun i ↦ k ⁻¹ᵁ D i.1
  have hE : Pairwise (fun i j ↦ Disjoint (E i) (E j)) :=
    pairwise_disjoint_preimage_subtype k hD J
  have hEfin (i : J) : IsFinite ((E i).ι ≫ q.map (pullback.fst b f)) :=
    isFinite_preimage_open_of_isPullback k (q.map (pullback.fst b f))
      (pullback.snd (q.map f) a) j sq (D i.1) (hfin i.1)
  obtain ⟨W, h, e, z, p, he, hz, hzsub, hsec, hp, hpetale⟩ :=
    exists_etale_chart_of_finite_open_union B S hS f b hbe E hE hEfin
  exact ⟨W, h, z, p, hz, hzsub, hsec, hp, hpetale, e, he⟩

private theorem presheaf_surjective_of_point_lifting
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : yoneda.relativelyRepresentable (diag F))
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ F)
    (hlift : ∀ (T : BigFppfOver B S hS) (a : yoneda.obj T ⟶ F)
      (t : (BigFppfOver.toScheme B S hS).obj T),
      ∃ (W : BigFppfOver B S hS) (b : W ⟶ T) (c : W ⟶ U)
        (w : (BigFppfOver.toScheme B S hS).obj W),
        (BigFppfOver.toScheme B S hS).map b w = t ∧
        yoneda.map c ≫ p = yoneda.map b ≫ a) :
    (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p := by
  let q := BigFppfOver.toScheme B S hS
  have := hasBinaryProducts_of_hasTerminal_and_pullbacks (BigFppfOver B S hS)
  refine ⟨Functor.relativelyRepresentable.diag_iff.mp hF p, ?_⟩
  intro T V a i b sq
  show Surjective (q.map b)
  refine ⟨fun t ↦ ?_⟩
  obtain ⟨W, b', c, w, hw, hcomm⟩ := hlift T a t
  let l : W ⟶ V := yoneda.preimage (sq.lift (yoneda.map c) (yoneda.map b') hcomm)
  have hl : l ≫ b = b' := by
    apply yoneda.map_injective
    simp only [Functor.map_comp, l, Functor.map_preimage, IsPullback.lift_snd]
  refine ⟨q.map l w, ?_⟩
  show (q.map l ≫ q.map b) w = t
  rwa [← q.map_comp, hl]

private theorem separated_and_locallyQuasiFinite_pullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf_sep : Space.IsSeparated B S hS f.hom)
    (hf_lqf : Space.IsLocallyQuasiFinite B S hS f.hom) :
    Space.IsSeparated B S hS (pullback.snd f.hom g.hom) ∧
      Space.IsLocallyQuasiFinite B S hS (pullback.snd f.hom g.hom) :=
  ⟨Space.isSeparated_pullback B S hS f.hom g.hom hf_sep,
    Space.IsLocallyQuasiFinite.of_isPullback B S hS
      (IsPullback.of_hasPullback f.hom g.hom).flip X.property Y.property hf_lqf⟩

private theorem schemeChart_pullback_isRepresentable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf_sep : Space.IsSeparated B S hS f.hom)
    (hf_lqf : Space.IsLocallyQuasiFinite B S hS f.hom)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1) :
    (pullback f.hom g).IsRepresentable := by
  let hV : IsAlgebraicSpace B S hS (yoneda.obj V) :=
    isAlgebraicSpace_yoneda B S hS V
  let hP : IsAlgebraicSpace B S hS (pullback f.hom g) :=
    isAlgebraicSpace_pullback B S hS f.hom g X.property hV Y.property
  let Vsp : AlgebraicSpaces B S hS := ⟨yoneda.obj V, hV⟩
  let gsp : Vsp ⟶ Y := ObjectProperty.homMk g
  have hprops := separated_and_locallyQuasiFinite_pullback B S hS f gsp
    hf_sep hf_lqf
  exact Space.isRepresentable_of_locallyQuasiFinite_separated B S hS
    (pullback f.hom g) (yoneda.obj V) hP hV (pullback.snd f.hom g)
    inferInstance hprops.2 hprops.1

private theorem exists_presheaf_cover_of_isPullback
    {C : Type*} [Category C] (P Q : MorphismProperty C)
    [P.IsStableUnderComposition] [Q.IsStableUnderComposition]
    {F' F Y' Y : Cᵒᵖ ⥤ Type _}
    {φ : F' ⟶ F} {b' : F' ⟶ Y'} {b : F ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback φ b' b g) (hgP : P.presheaf g) (hgQ : Q.presheaf g)
    (hc : ∃ (U : C) (p : yoneda.obj U ⟶ F'),
      P.presheaf (p ≫ b') ∧ Q.presheaf p ∧ P.presheaf p) :
    ∃ (U : C) (p : yoneda.obj U ⟶ F),
      P.presheaf (p ≫ b) ∧ Q.presheaf p ∧ P.presheaf p := by
  have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) P
  have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) Q
  obtain ⟨U, p, hpb, hpQ, hpP⟩ := hc
  refine ⟨U, p ≫ φ, ?_, ?_, ?_⟩
  · rw [Category.assoc, sq.w, ← Category.assoc]
    exact P.presheaf.comp_mem _ _ hpb hgP
  · exact Q.presheaf.comp_mem _ _ hpQ (Q.presheaf.of_isPullback sq.flip hgQ)
  · exact P.presheaf.comp_mem _ _ hpP (P.presheaf.of_isPullback sq.flip hgP)

private theorem exists_finitePart_cover_of_representable_case
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hc : ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
      X.obj.IsRepresentable → Y.obj.IsRepresentable →
      Space.IsSeparated B S hS f.hom →
      Space.IsLocallyQuasiFinite B S hS f.hom →
      ∃ (U : BigFppfOver B S hS)
        (p : yoneda.obj U ⟶ (Space.finiteOpenSubspacePresheaf B S hS f).toFunctor),
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf
          (p ≫ (Space.finiteOpenSubspacePresheaf B S hS f).baseMap) ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf_sep : Space.IsSeparated B S hS f.hom)
    (hf_lqf : Space.IsLocallyQuasiFinite B S hS f.hom) :
    ∃ (U : BigFppfOver B S hS)
      (p : yoneda.obj U ⟶ (Space.finiteOpenSubspacePresheaf B S hS f).toFunctor),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
        (p ≫ (Space.finiteOpenSubspacePresheaf B S hS f).baseMap) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p := by
  obtain ⟨V, g, hgSurj, hgEtale⟩ := Y.property.exists_atlas
  let Vsp := schemeSpace V
  let gsp : Vsp ⟶ Y := ObjectProperty.homMk g
  let P := AlgebraicSpaces.fiberProduct B S hS f gsp
  let fst : P ⟶ X := ObjectProperty.homMk (pullback.fst f.hom g)
  let snd : P ⟶ Vsp := ObjectProperty.homMk (pullback.snd f.hom g)
  obtain ⟨φ, sq⟩ := exists_isPullback_finitePart
    B S hS fst snd f gsp (AlgebraicSpaces.isPullback_fiberProduct B S hS f gsp)
  obtain ⟨hsep, hlqf⟩ := separated_and_locallyQuasiFinite_pullback
    B S hS f gsp hf_sep hf_lqf
  have hrep := schemeChart_pullback_isRepresentable B S hS f hf_sep hf_lqf V g
  have : MorphismProperty.IsStableUnderComposition (@Etale.{u}) :=
    ⟨fun a b (_ : Etale a) (_ : Etale b) ↦ Etale.etale_comp b (f := a)⟩
  have : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    ⟨fun a b ha hb ↦ @AlgebraicGeometry.instSurjectiveCompScheme _ _ _ a b ha hb⟩
  have := MorphismProperty.IsStableUnderComposition.inverseImage
    (P := @Etale.{u}) (BigFppfOver.toScheme B S hS)
  have := MorphismProperty.IsStableUnderComposition.inverseImage
    (P := @Surjective.{u}) (BigFppfOver.toScheme B S hS)
  exact exists_presheaf_cover_of_isPullback _ _ sq hgEtale hgSurj
    (hc snd hrep (inferInstanceAs (yoneda.obj V).IsRepresentable) hsep hlqf)

private theorem presheaf_etale_iso_hom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X₀ : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : yoneda.obj X₀ ≅ F) :
    (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf e.hom := by
  have hid := presheaf_yoneda_map B S hS (@Etale.{u}) (𝟙 X₀) (by
    rw [CategoryTheory.Functor.map_id]
    infer_instance)
  simpa using MorphismProperty.RespectsIso.postcomp
    ((MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf) e.hom _ hid

private theorem exists_finitePart_cover_of_scheme_case
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hc : ∀ {X Y : BigFppfOver B S hS} (f : X ⟶ Y),
      IsSeparated ((BigFppfOver.toScheme B S hS).map f) →
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map f) →
      LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map f) →
      ∃ (U : BigFppfOver B S hS)
        (p : yoneda.obj U ⟶ (Space.finiteOpenSubspacePresheaf B S hS
          (schemeSpaceMap f)).toFunctor),
        (MorphismProperty.inverseImage (@Etale.{u})
          (BigFppfOver.toScheme B S hS)).presheaf
          (p ≫ (Space.finiteOpenSubspacePresheaf B S hS
            (schemeSpaceMap f)).baseMap) ∧
        (MorphismProperty.inverseImage (@Surjective.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p ∧
        (MorphismProperty.inverseImage (@Etale.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf_sep : Space.IsSeparated B S hS f.hom)
    (hf_lqf : Space.IsLocallyQuasiFinite B S hS f.hom) :
    ∃ (U : BigFppfOver B S hS)
      (p : yoneda.obj U ⟶ (Space.finiteOpenSubspacePresheaf B S hS f).toFunctor),
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
        (p ≫ (Space.finiteOpenSubspacePresheaf B S hS f).baseMap) ∧
      (MorphismProperty.inverseImage (@Surjective.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p := by
  apply exists_finitePart_cover_of_representable_case B S hS ?_ f hf_sep hf_lqf
  intro X Y f hX hY hsep hlqf
  let q := BigFppfOver.toScheme B S hS
  let X₀ := X.obj.reprX
  let Y₀ := Y.obj.reprX
  let eX := X.obj.reprW
  let eY := Y.obj.reprW
  let f₀ : X₀ ⟶ Y₀ := yoneda.preimage (eX.hom ≫ f.hom ≫ eY.inv)
  have hf₀ : yoneda.map f₀ = eX.hom ≫ f.hom ≫ eY.inv := yoneda.map_preimage _
  let P := (MorphismProperty.inverseImage (@IsClosedImmersion.{u}) q).presheaf
  have hsep₀ : Space.IsSeparated B S hS (yoneda.map f₀) := by
    show P.diagonal (yoneda.map f₀)
    rw [hf₀, P.diagonal.cancel_left_of_respectsIso,
      P.diagonal.cancel_right_of_respectsIso]
    exact hsep
  have hprops := hlqf X₀ Y₀ eX.hom eY.hom f₀ (presheaf_etale_iso_hom B S hS eX)
    (presheaf_etale_iso_hom B S hS eY) (by rw [hf₀]; simp)
  obtain ⟨U, p, hpbase, hpsurj, hpetale⟩ := hc f₀
    ((Space.isSeparated_yoneda_map_iff B S hS f₀).mp hsep₀)
    hprops.1 hprops.2
  let eXsp : schemeSpace X₀ ≅ X := ObjectProperty.isoMk _ eX
  let eYsp : schemeSpace Y₀ ≅ Y := ObjectProperty.isoMk _ eY
  have sq : IsPullback eXsp.hom (schemeSpaceMap f₀) f eYsp.hom := by
    apply IsPullback.of_horiz_isIso
    constructor
    apply ObjectProperty.hom_ext
    show eX.hom ≫ f.hom = yoneda.map f₀ ≫ eY.hom
    rw [hf₀]
    simp
  obtain ⟨φ, hφ⟩ := exists_isPullback_finitePart B S hS
    eXsp.hom (schemeSpaceMap f₀) f eYsp.hom sq
  have : IsIso φ := hφ.isIso_fst_of_isIso
  refine ⟨U, p ≫ φ, ?_, ?_, ?_⟩
  · rw [Category.assoc, hφ.w, ← Category.assoc]
    exact MorphismProperty.RespectsIso.postcomp _ _ _ hpbase
  · exact MorphismProperty.RespectsIso.postcomp _ _ _ hpsurj
  · exact MorphismProperty.RespectsIso.postcomp _ _ _ hpetale

private theorem algebraicClosure_spec_mem
    (B : BigFppfSite.{u}) {X : Scheme.{u}}
    (hX : B.Contains X) (x : X) :
    B.Contains (Spec (.of (AlgebraicClosure (X.residueField x)))) := by
  let K := X.residueField x
  have hfield : Cardinal.mk K ≤ X.size := by
    have hs : (Spec (.of K)).size ≤ X.size :=
      Scheme.size_le_of_mono_quasiCompact (X.fromSpecResidueField x)
    rw [Scheme.size_Spec] at hs
    exact (le_max_right _ _).trans hs
  have hcard : Cardinal.mk (AlgebraicClosure K) ≤ X.size :=
    (Algebra.IsAlgebraic.cardinalMk_le_max K (AlgebraicClosure K)).trans
      (max_le hfield X.aleph0_le_size)
  exact Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (CommRingCat.of (AlgebraicClosure K)) hX
    (hcard.trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0))

/-- The two projections of a subfunctor of the fibre product of `yoneda.map b` and `yoneda.map f`
identified with `yoneda.obj W` via `j : W ⟶ pullback b f`. -/
private theorem iso_comp_subfunctor_ι_comp_projections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U W : BigFppfOver B S hS} (f : X ⟶ Y) (b : U ⟶ Y) (j : W ⟶ pullback b f)
    {Z : Subfunctor (pullback (yoneda.map b) (yoneda.map f))} (i : yoneda.obj W ≅ Z.toFunctor)
    (hi : yoneda.map j ≫ ((IsPullback.of_hasPullback b f).map yoneda).isoPullback.hom =
      i.hom ≫ Z.ι) :
    i.hom ≫ Z.ι ≫ pullback.fst (yoneda.map b) (yoneda.map f) =
        yoneda.map (j ≫ pullback.fst b f) ∧
      i.hom ≫ Z.ι ≫ pullback.snd (yoneda.map b) (yoneda.map f) =
        yoneda.map (j ≫ pullback.snd b f) := by
  rw [← Category.assoc, ← hi, ← Category.assoc, ← hi]
  simp

-- `AlgebraicGeometry.schemeSpaceMap` is a plain `def`, so the ambient fibre product of
-- the pair, which is formed over `(schemeSpaceMap b).hom`, is not recognised at `implicit`
-- transparency as the fibre product over `yoneda.map b` that the represented open lives in.
attribute [local implicit_reducible] AlgebraicGeometry.schemeSpaceMap
  AlgebraicGeometry.schemeSpace in
private theorem exists_open_representation_of_finite_part
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U : BigFppfOver B S hS} (f : X ⟶ Y) (b : U ⟶ Y)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (z : Space.FiniteOpenSubspace B S hS
      (schemeSpaceMap f) (schemeSpace U))
    (hz : z.toBase = schemeSpaceMap b) :
    ∃ (W : BigFppfOver B S hS) (j : W ⟶ pullback b f),
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      IsFinite ((BigFppfOver.toScheme B S hS).map
        (j ≫ pullback.fst b f)) ∧
      HEq z.subspace (Subfunctor.range
        (yoneda.map j ≫ ((IsPullback.of_hasPullback b f).map yoneda).isoPullback.hom)) := by
  rcases z with ⟨a, Z, hOpen, hFinite⟩
  dsimp only at hz
  cases hz
  let z : Space.FiniteOpenSubspace B S hS
      (schemeSpaceMap f) (schemeSpace U) :=
    ⟨schemeSpaceMap b, Z, hOpen, hFinite⟩
  let q := BigFppfOver.toScheme B S hS
  obtain ⟨W, p, e, _, hfinite, he, hopen⟩ :=
    exists_finite_representation_of_affine_base B S hS U hU z
  let i := ((IsPullback.of_hasPullback b f).map yoneda).isoPullback
  let j : W ⟶ pullback b f :=
    yoneda.preimage (e.hom ≫ z.subspace.ι ≫ i.inv)
  have hj : yoneda.map j ≫ i.hom = e.hom ≫ z.subspace.ι := by
    simp [j]
  have hjfst : j ≫ pullback.fst b f = p := by
    exact yoneda.map_injective
      ((iso_comp_subfunctor_ι_comp_projections B S hS f b j e hj).1.symm.trans he)
  have hjopen : IsOpenImmersion (q.map j) := by
    apply MorphismProperty.of_relative_map (F := yoneda)
      (P := MorphismProperty.inverseImage (@IsOpenImmersion.{u}) q)
    show (MorphismProperty.inverseImage (@IsOpenImmersion.{u}) q).presheaf
      (yoneda.map j)
    rw [← MorphismProperty.cancel_right_of_respectsIso
      (P := (MorphismProperty.inverseImage (@IsOpenImmersion.{u}) q).presheaf)
      (yoneda.map j) i.hom, hj]
    exact MorphismProperty.RespectsIso.precomp _ e.hom _ z.isOpen.2
  refine ⟨W, j, hjopen, ?_, ?_⟩
  · rwa [hjfst]
  · have hr : Subfunctor.range (e.hom ≫ z.subspace.ι) = z.subspace := by
      rw [Subfunctor.range_comp, Subfunctor.range_eq_top,
        Subfunctor.image_top, Subfunctor.range_ι]
    rw [hj]
    exact heq_of_eq hr.symm

private theorem isFinite_opensRange_projection
    {A B T : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j] (p : B ⟶ T)
    (h : IsFinite (j ≫ p)) : IsFinite (j.opensRange.ι ≫ p) := by
  have h' : IsFinite (j.isoOpensRange.inv ≫ (j ≫ p)) := inferInstance
  simpa only [← Category.assoc, j.isoOpensRange_inv_comp] using h'

private theorem opensRange_sigma_desc_opens
    {X : Scheme.{u}} {I : Type u} (D : I → X.Opens)
    [IsOpenImmersion (Sigma.desc fun i ↦ (D i).ι)] :
    (Sigma.desc fun i ↦ (D i).ι).opensRange = ⨆ i, D i := by
  ext
  simp [(sigmaMk _).symm.exists_congr_left, ← Scheme.Hom.comp_apply,
    Scheme.Opens.exists_toScheme]

private theorem exists_iso_subfunctor_of_range
    {C : Type*} [Category C] {F G : Cᵒᵖ ⥤ Type u}
    (j : F ⟶ G) [Mono j] (Z : Subfunctor G) (hZ : Z = Subfunctor.range j) :
    ∃ e : F ≅ Z.toFunctor, e.hom ≫ Z.ι = j := by
  subst Z
  exact ⟨asIso (Subfunctor.toRange j), Subfunctor.toRange_ι j⟩

/-- A morphism of underlying schemes compatible with maps to a common object of
`BigFppfOver B S hS` lifts to a morphism of `BigFppfOver B S hS`. -/
private def overHomOfCompEq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P W W' : BigFppfOver B S hS} (j : W ⟶ P) (j' : W' ⟶ P)
    (m₀ : (BigFppfOver.toScheme B S hS).obj W' ⟶ (BigFppfOver.toScheme B S hS).obj W)
    (hm : m₀ ≫ (BigFppfOver.toScheme B S hS).map j = (BigFppfOver.toScheme B S hS).map j') :
    W' ⟶ W :=
  Over.homMk (ObjectProperty.homMk m₀) (by
    apply ObjectProperty.hom_ext
    change m₀ ≫ W.hom.hom = W'.hom.hom
    have hjS := congrArg (fun m ↦ m.hom) j.w
    have hj'S := congrArg (fun m ↦ m.hom) j'.w
    change (BigFppfOver.toScheme B S hS).map j ≫ P.hom.hom = W.hom.hom at hjS
    change (BigFppfOver.toScheme B S hS).map j' ≫ P.hom.hom = W'.hom.hom at hj'S
    rw [← hjS, ← Category.assoc, hm, hj'S])

private theorem exists_isPullback_of_preimage_opensRange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P P' W W' : BigFppfOver B S hS}
    (L : P' ⟶ P) (j : W ⟶ P) (j' : W' ⟶ P')
    (hj : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
    (hj' : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j'))
    (hr : (BigFppfOver.toScheme B S hS).map L ⁻¹ᵁ
      ((BigFppfOver.toScheme B S hS).map j).opensRange =
      ((BigFppfOver.toScheme B S hS).map j').opensRange) :
    ∃ m : W' ⟶ W, IsPullback m j' j L := by
  let q := BigFppfOver.toScheme B S hS
  have hrange : Set.range (q.map (j' ≫ L)) ⊆ Set.range (q.map j) := by
    rintro _ ⟨x, rfl⟩
    have hx : q.map j' x ∈ q.map L ⁻¹ᵁ (q.map j).opensRange := by
      rw [hr]
      exact ⟨x, rfl⟩
    exact hx
  let m₀ := IsOpenImmersion.lift (q.map j) (q.map (j' ≫ L)) hrange
  have hm₀ : m₀ ≫ q.map j = q.map (j' ≫ L) :=
    IsOpenImmersion.lift_fac _ _ _
  let m : W' ⟶ W := overHomOfCompEq B S hS j (j' ≫ L) m₀ hm₀
  refine ⟨m, ?_⟩
  apply IsPullback.of_map q
  · exact q.map_injective hm₀
  exact IsOpenImmersion.isPullback (q.map m) (q.map j') (q.map j) (q.map L)
    (by
      show q.map j' ≫ q.map L = m₀ ≫ q.map j
      simpa only [Functor.map_comp] using hm₀.symm) hr

attribute [local implicit_reducible] AlgebraicGeometry.schemeSpaceMap
  AlgebraicGeometry.schemeSpace in
private theorem isBaseChange_of_represented_open_pullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U U' W W' : BigFppfOver B S hS}
    (f : X ⟶ Y) (b : U ⟶ Y) (b' : U' ⟶ Y) (l : U' ⟶ U)
    (hl : l ≫ b = b')
    (L : pullback b' f ⟶ pullback b f)
    (hLfst : L ≫ pullback.fst b f = pullback.fst b' f ≫ l)
    (hLsnd : L ≫ pullback.snd b f = pullback.snd b' f)
    (j : W ⟶ pullback b f) (j' : W' ⟶ pullback b' f)
    [Mono j] [Mono j'] (m : W' ⟶ W) (sq : IsPullback m j' j L)
    (z : Space.FiniteOpenSubspace B S hS
      (schemeSpaceMap f)
      (schemeSpace U))
    (z' : Space.FiniteOpenSubspace B S hS
      (schemeSpaceMap f)
      (schemeSpace U'))
    (hz : z.toBase = schemeSpaceMap b)
    (hz' : z'.toBase = schemeSpaceMap b')
    (hr : HEq z.subspace (Subfunctor.range
      (yoneda.map j ≫ ((IsPullback.of_hasPullback b f).map yoneda).isoPullback.hom)))
    (hr' : HEq z'.subspace (Subfunctor.range
      (yoneda.map j' ≫ ((IsPullback.of_hasPullback b' f).map yoneda).isoPullback.hom))) :
    Space.FiniteOpenSubspace.IsBaseChange B S hS
      (schemeSpaceMap f) l z z' := by
  rcases z with ⟨a, Z, hopen, hfinite⟩
  rcases z' with ⟨a', Z', hopen', hfinite'⟩
  dsimp only at hz hz'
  cases hz
  cases hz'
  let e := ((IsPullback.of_hasPullback b f).map yoneda).isoPullback
  let e' := ((IsPullback.of_hasPullback b' f).map yoneda).isoPullback
  obtain ⟨i, hi⟩ := exists_iso_subfunctor_of_range (yoneda.map j ≫ e.hom) Z
    (eq_of_heq hr)
  obtain ⟨i', hi'⟩ := exists_iso_subfunctor_of_range (yoneda.map j' ≫ e'.hom) Z'
    (eq_of_heq hr')
  let n := i'.inv ≫ yoneda.map m ≫ i.hom
  have hnf : i'.hom ≫ n = yoneda.map m ≫ i.hom := by simp [n]
  obtain ⟨hip, hip₂⟩ := iso_comp_subfunctor_ι_comp_projections B S hS f b j i hi.symm
  obtain ⟨hi'p, hi'p₂⟩ := iso_comp_subfunctor_ι_comp_projections B S hS f b' j' i' hi'.symm
  have sqL : IsPullback L (pullback.fst b' f) (pullback.fst b f) l := by
    apply IsPullback.of_right _ hLfst (IsPullback.of_hasPullback b f).flip
    rw [hLsnd, hl]
    exact (IsPullback.of_hasPullback b' f).flip
  refine ⟨?_, n, ?_, ?_⟩
  · show yoneda.map b' = yoneda.map l ≫ yoneda.map b
    rw [← yoneda.map_comp, hl]
  · show IsPullback
      (Z'.ι ≫ pullback.fst (yoneda.map b') (yoneda.map f)) n
      (yoneda.map l) (Z.ι ≫ pullback.fst (yoneda.map b) (yoneda.map f))
    exact ((sq.flip.paste_horiz sqL.flip).map yoneda).of_iso i'
      (Iso.refl _) i (Iso.refl _) (by simpa using hi'p.symm)
      (by simpa using hnf.symm) (by simp) (by simpa using hip.symm)
  · show n ≫ Z.ι ≫ pullback.snd (yoneda.map b) (yoneda.map f) =
      Z'.ι ≫ pullback.snd (yoneda.map b') (yoneda.map f)
    apply (cancel_epi i'.hom).1
    rw [← Category.assoc, hnf, Category.assoc, hip₂, hi'p₂, ← yoneda.map_comp,
      ← Category.assoc, sq.w, Category.assoc, hLsnd]

private theorem exists_chart_of_site_coproduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    {I : Type u} (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (ι : ∀ i, U i ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj V ≅
      ∐ fun i ↦ (BigFppfOver.toScheme B S hS).obj (U i))
    (he : ∀ i, (BigFppfOver.toScheme B S hS).map (ι i) ≫ e.hom =
      Sigma.ι (fun i ↦ (BigFppfOver.toScheme B S hS).obj (U i)) i)
    (b : ∀ i, U i ⟶ Y) (hb : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (b i)))
    (p : ∀ i, yoneda.obj (U i) ⟶
      (Space.finiteOpenSubspacePresheaf B S hS (schemeSpaceMap f)).toFunctor)
    (hp : ∀ i, p i ≫ (Space.finiteOpenSubspacePresheaf B S hS (schemeSpaceMap f)).baseMap =
      yoneda.map (b i)) :
    ∃ pV : yoneda.obj V ⟶
        (Space.finiteOpenSubspacePresheaf B S hS (schemeSpaceMap f)).toFunctor,
      (∀ i, yoneda.map (ι i) ≫ pV = p i) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
          (pV ≫ (Space.finiteOpenSubspacePresheaf B S hS (schemeSpaceMap f)).baseMap) := by
  obtain ⟨s, hs⟩ := exists_sections_of_site_coproduct B S hS _
    (Space.isSheaf_finiteOpenSubspacePresheaf B S hS (schemeSpaceMap f)) U V ι e he
    (fun i ↦ yonedaEquiv (p i))
  let pV : yoneda.obj V ⟶
      (Space.finiteOpenSubspacePresheaf B S hS (schemeSpaceMap f)).toFunctor :=
    yonedaEquiv.symm s
  have hpV (i : I) : yoneda.map (ι i) ≫ pV = p i := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact hs i
  let bV : V ⟶ Y := yoneda.preimage
    (pV ≫ (Space.finiteOpenSubspacePresheaf B S hS (schemeSpaceMap f)).baseMap)
  have hbV (i : I) : ι i ≫ bV = b i := by
    apply yoneda.map_injective
    rw [Functor.map_comp, yoneda.map_preimage]
    show (yoneda.map (ι i) ≫ pV) ≫
      (Space.finiteOpenSubspacePresheaf B S hS (schemeSpaceMap f)).baseMap = yoneda.map (b i)
    rw [hpV]
    exact hp i
  have hbV_eq : pV ≫ (Space.finiteOpenSubspacePresheaf B S hS (schemeSpaceMap f)).baseMap =
      yoneda.map bV :=
    (yoneda.map_preimage _).symm
  refine ⟨pV, hpV, ?_⟩
  rw [hbV_eq]
  exact presheaf_yoneda_map B S hS (@Etale.{u} : MorphismProperty Scheme.{u}) bV
    (etale_map_of_site_coproduct B S hS U ι e he bV fun i ↦ hbV i ▸ hb i)

private theorem isFinite_preimage_isoPullback_inv_opensRange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U W : BigFppfOver B S hS} (f : X ⟶ Y) (b : U ⟶ Y) (j : W ⟶ pullback b f)
    [IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (hj : IsFinite ((BigFppfOver.toScheme B S hS).map (j ≫ pullback.fst b f))) :
    IsFinite ((((IsPullback.of_hasPullback b f).map
      (BigFppfOver.toScheme B S hS)).isoPullback.inv ⁻¹ᵁ
        ((BigFppfOver.toScheme B S hS).map j).opensRange).ι ≫
      pullback.fst ((BigFppfOver.toScheme B S hS).map b)
        ((BigFppfOver.toScheme B S hS).map f)) := by
  let q := BigFppfOver.toScheme B S hS
  have hsq : IsPullback ((IsPullback.of_hasPullback b f).map q).isoPullback.inv
      (pullback.fst (q.map b) (q.map f)) (q.map (pullback.fst b f)) (𝟙 (q.obj U)) := by
    apply IsPullback.of_horiz_isIso
    constructor
    simp only [Category.comp_id]
    exact ((IsPullback.of_hasPullback b f).map q).isoPullback_inv_fst
  exact isFinite_preimage_open_of_isPullback _ _ _ _ hsq _
    (isFinite_opensRange_projection (q.map j) (q.map (pullback.fst b f)) hj)

private theorem exists_pullback_map_of_lift
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y V R : BigFppfOver B S hS} {E : Scheme.{u}} (f : X ⟶ Y) (b : V ⟶ Y) (b' : R ⟶ Y)
    (a : E ⟶ (BigFppfOver.toScheme B S hS).obj Y) (lV : R ⟶ V) (hlV : lV ≫ b = b')
    (j : (BigFppfOver.toScheme B S hS).obj V ⟶ E)
    (l : (BigFppfOver.toScheme B S hS).obj R ⟶ E)
    (hl : (BigFppfOver.toScheme B S hS).map lV ≫ j = l)
    (k : (BigFppfOver.toScheme B S hS).obj (pullback b f) ⟶
      pullback ((BigFppfOver.toScheme B S hS).map f) a)
    (hk : k ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map f) a =
      (BigFppfOver.toScheme B S hS).map (pullback.snd b f))
    (hksnd : k ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map f) a =
      (BigFppfOver.toScheme B S hS).map (pullback.fst b f) ≫ j)
    (k' : pullback ((BigFppfOver.toScheme B S hS).map b')
      ((BigFppfOver.toScheme B S hS).map f) ⟶
        pullback ((BigFppfOver.toScheme B S hS).map f) a)
    (hk' : k' ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map f) a =
      pullback.snd ((BigFppfOver.toScheme B S hS).map b')
        ((BigFppfOver.toScheme B S hS).map f))
    (hk'snd : k' ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map f) a =
      pullback.fst ((BigFppfOver.toScheme B S hS).map b')
        ((BigFppfOver.toScheme B S hS).map f) ≫ l) :
    ∃ L : pullback b' f ⟶ pullback b f,
      L ≫ pullback.fst b f = pullback.fst b' f ≫ lV ∧
      L ≫ pullback.snd b f = pullback.snd b' f ∧
      (BigFppfOver.toScheme B S hS).map L ≫ k =
        ((IsPullback.of_hasPullback b' f).map
          (BigFppfOver.toScheme B S hS)).isoPullback.hom ≫ k' := by
  refine ⟨pullback.lift (pullback.fst b' f ≫ lV) (pullback.snd b' f)
    (by rw [Category.assoc, hlV, pullback.condition]), pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _, ?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [hk, hk', ← Functor.map_comp, pullback.lift_snd]
    exact ((IsPullback.of_hasPullback b' f).map
      (BigFppfOver.toScheme B S hS)).isoPullback_hom_snd.symm
  · simp only [Category.assoc]
    rw [hksnd, hk'snd, ← Category.assoc, ← Functor.map_comp, pullback.lift_fst,
      Functor.map_comp, Category.assoc, hl, ← Category.assoc,
      ((IsPullback.of_hasPullback b' f).map (BigFppfOver.toScheme B S hS)).isoPullback_hom_fst]

private theorem isOpenImmersion_of_iso_sigma_opens {X Y : Scheme.{u}} {I : Type u}
    (D : I → Y.Opens) (hD : Pairwise (fun i j ↦ Disjoint (D i) (D j))) (φ : X ⟶ Y)
    (e : X ≅ ∐ fun i ↦ (D i).toScheme) (he : e.hom ≫ Sigma.desc (fun i ↦ (D i).ι) = φ) :
    IsOpenImmersion φ := by
  have := isOpenImmersion_sigmaDesc_opens D hD
  subst he
  exact IsOpenImmersion.comp e.hom _

private theorem opensRange_of_iso_sigma_opens {X Y : Scheme.{u}} {I : Type u}
    (D : I → Y.Opens) (hD : Pairwise (fun i j ↦ Disjoint (D i) (D j))) (φ : X ⟶ Y)
    [IsOpenImmersion φ] (e : X ≅ ∐ fun i ↦ (D i).toScheme)
    (he : e.hom ≫ Sigma.desc (fun i ↦ (D i).ι) = φ) :
    φ.opensRange = ⨆ i, D i := by
  have := isOpenImmersion_sigmaDesc_opens D hD
  subst he
  exact (e.hom.opensRange_comp_of_isIso _).trans (opensRange_sigma_desc_opens D)

private theorem preimage_iSup_preimage_of_comp_eq {P P' Q R : Scheme.{u}}
    (L : P' ⟶ P) (k : P ⟶ Q) (e : P' ⟶ R) (k' : R ⟶ Q) (h : L ≫ k = e ≫ k')
    {I : Type*} (D : I → Q.Opens) (J : Set I) :
    L ⁻¹ᵁ (⨆ i : J, k ⁻¹ᵁ D i.1) = e ⁻¹ᵁ (⨆ i ∈ J, k' ⁻¹ᵁ D i) := by
  simp only [Scheme.Hom.preimage_iSup, iSup_subtype]
  congr 1
  funext i
  congr 1
  funext hi
  show L ⁻¹ᵁ (k ⁻¹ᵁ D i) = e ⁻¹ᵁ (k' ⁻¹ᵁ D i)
  rw [← Scheme.Hom.comp_preimage, h, Scheme.Hom.comp_preimage]

/-- The finite-part sheaf of a separated, locally quasi-finite morphism of
algebraic spaces has a surjective étale scheme cover that is étale over the
target. -/
@[stacks 04QG]
theorem _root_.AlgebraicGeometry.Space.exists_surjective_etale_chart_finiteOpenSubspacePresheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf_sep : Space.IsSeparated B S hS f.hom)
    (hf_lqf : Space.IsLocallyQuasiFinite B S hS f.hom) :
    ∃ (U : BigFppfOver B S hS)
      (p : yoneda.obj U ⟶
        (Space.finiteOpenSubspacePresheaf B S hS f).toFunctor),
      (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
          (p ≫ (Space.finiteOpenSubspacePresheaf B S hS f).baseMap) ∧
      (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p := by
  apply exists_finitePart_cover_of_scheme_case B S hS ?_ f hf_sep hf_lqf
  intro X' Y' f' hsep hft hlqf
  classical
  let q := BigFppfOver.toScheme B S hS
  let g : q.obj X' ⟶ q.obj Y' := q.map f'
  have : IsSeparated g := hsep
  have : LocallyOfFiniteType g := hft
  have : LocallyQuasiFinite g := hlqf
  let A := Σ y : q.obj Y', Finset (g.fiber y)
  obtain ⟨κ, hκ, hκB, hA, hYsize⟩ :=
    exists_uniform_bound_finite_fiber_subsets B g X'.left.property Y'.left.property
  choose E I hI Wrem D hdisj hcover hfin hW using
    fun a : A ↦ exists_etale_decomposition_of_locallyQuasiFinite g a.1 a.2
  let (a : A) : Finite (I a) := hI a
  have hfamily (a : A) := exists_site_chart_family_of_etale_decomposition
    B S hS f' (E a).toBase (E a).point (D a)
    (hdisj a) (fun i ↦ (hfin a i).choose_spec.1)
  choose V b j v k hV hj hv hb hbe hsize hk hksnd hchart using hfamily
  let C := Σ a : A, Set (I a)
  have hC : Cardinal.mk C ≤ κ :=
    cardinal_mk_finite_piece_choices_le A I κ hκ hA
  have hVsize (c : C) : (q.obj (V c.1)).size ≤ κ :=
    (hsize c.1).trans hYsize
  obtain ⟨T, ι, eT, heT, _⟩ :=
    exists_site_coproduct_of_uniform_bound B S hS (fun c : C ↦ V c.1)
      κ hκ hκB hC hVsize
  have hcharts (c : C) := hchart c.1 c.2
  choose W h z p hz hzsub hsec hp hpetale ep he using hcharts
  let F := (Space.finiteOpenSubspacePresheaf B S hS
    (schemeSpaceMap f')).toFunctor
  obtain ⟨pT, hpT, hbase⟩ := exists_chart_of_site_coproduct B S hS f'
    (fun c : C ↦ V c.1) T ι eT heT (fun c ↦ b c.1) (fun c ↦ hbe c.1) p hp
  refine ⟨T, pT, hbase, ?_,
    Space.isEtale_of_isEtale_comp_baseMap B S hS (schemeSpaceMap f') T pT hbase⟩
  apply presheaf_surjective_of_point_lifting B S hS
    (Space.relativelyRepresentable_diag_finiteOpenSubspacePresheaf B S hS
      (schemeSpaceMap f')) T pT
  intro R a t
  let K := (q.obj R).residueField t
  let Ω := AlgebraicClosure K
  let : Field Ω := inferInstance
  have : IsAlgClosed Ω := AlgebraicClosure.isAlgClosed K
  have hΩ : B.Contains (Spec (.of Ω)) :=
    algebraicClosure_spec_mem B R.left.property t
  let r₀ : Spec (.of Ω) ⟶ q.obj R :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
      (q.obj R).fromSpecResidueField t
  let RΩ : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (r₀ ≫ R.hom.hom) : B.obj hΩ ⟶ B.obj hS)
  let ρ : RΩ ⟶ R := Over.homMk (ObjectProperty.homMk r₀) (by rfl)
  let aΩ := yoneda.map ρ ≫ a
  let zΩ := (Space.finiteOpenSubspacePresheaf B S hS
    (schemeSpaceMap f')).sections RΩ (yonedaEquiv aΩ)
  have hr₀ : r₀ default = t := by
    show (q.obj R).fromSpecResidueField t
      ((Spec.map (CommRingCat.ofHom (algebraMap K Ω))) default) = t
    exact Scheme.fromSpecResidueField_apply t _
  let bΩ : RΩ ⟶ Y' := yoneda.preimage zΩ.toBase.hom
  have hbΩ : zΩ.toBase = schemeSpaceMap bΩ :=
    ObjectProperty.hom_ext _ (yoneda.map_preimage _).symm
  obtain ⟨WΩ, jΩ, hjΩopen, hjΩfinite, hjΩsub⟩ :=
    exists_open_representation_of_finite_part B S hS f' bΩ
      (inferInstanceAs (IsAffine (Spec (.of Ω)))) zΩ hbΩ
  let ZΩ := (q.map jΩ).opensRange
  let eΩ := ((IsPullback.of_hasPullback bΩ f').map q).isoPullback
  let Z' := eΩ.inv ⁻¹ᵁ ZΩ
  have hZ'finite : IsFinite (Z'.ι ≫ pullback.fst (q.map bΩ) g) :=
    isFinite_preimage_isoPullback_inv_opensRange B S hS f' bΩ jΩ hjΩfinite
  have : Subsingleton (q.obj RΩ) := inferInstanceAs (Subsingleton (Spec (.of Ω)))
  obtain ⟨sΩ, hsΩ⟩ := exists_finset_fiber_containing_finite_open
    g (q.map bΩ) (default : Spec (.of Ω)) Z' hZ'finite
  let a₀ : A := ⟨q.map bΩ (default : Spec (.of Ω)), sΩ⟩
  obtain ⟨l, kΩ, J, hl, hlu, hkΩfst, hkΩsnd, hJ⟩ :=
    exists_subset_of_etale_decomposition g a₀.1 a₀.2 (E a₀) (Wrem a₀) (D a₀)
      (hcover a₀) (fun i ↦ ⟨(hfin a₀ i).choose,
        (hfin a₀ i).choose_spec.2⟩) (hW a₀) (q.map bΩ) rfl Z' hsΩ
  have : IsOpenImmersion (j a₀) := hj a₀
  obtain ⟨lV, hlV, _⟩ := exists_lift_of_subsingleton_of_mem_range
    l (j a₀) default (v a₀) ((hv a₀).trans hlu.symm)
  have hlVb : lV ≫ q.map (b a₀) = q.map bΩ := by
    rw [← hb a₀, ← Category.assoc, hlV, hl]
  let lV' : RΩ ⟶ V a₀ := overHomOfCompEq B S hS (b a₀) bΩ lV hlVb
  have hlV'b : lV' ≫ b a₀ = bΩ := q.map_injective hlVb
  obtain ⟨L, hLfst, hLsnd, hLk⟩ := exists_pullback_map_of_lift B S hS f' (b a₀) bΩ
    (E a₀).toBase lV' hlV'b (j a₀) l hlV (k a₀) (hk a₀) (hksnd a₀) kΩ hkΩfst hkΩsnd
  let c : C := ⟨a₀, J⟩
  let Dc : J → (q.obj (pullback (b a₀) f')).Opens :=
    fun i ↦ k a₀ ⁻¹ᵁ D a₀ i.1
  have hDc : Pairwise (fun i j ↦ Disjoint (Dc i) (Dc j)) :=
    pairwise_disjoint_preimage_subtype (k a₀) (hdisj a₀) J
  have hcOpen : IsOpenImmersion (q.map (h c)) :=
    isOpenImmersion_of_iso_sigma_opens Dc hDc _ (ep c) (he c)
  have hpreimage : q.map L ⁻¹ᵁ (q.map (h c)).opensRange = (q.map jΩ).opensRange := by
    rw [opensRange_of_iso_sigma_opens Dc hDc _ (ep c) (he c)]
    refine (preimage_iSup_preimage_of_comp_eq _ _ _ _ hLk (D a₀) J).trans ?_
    rw [← hJ]
    show eΩ.hom ⁻¹ᵁ (eΩ.inv ⁻¹ᵁ ZΩ) = ZΩ
    rw [← Scheme.Hom.comp_preimage, eΩ.hom_inv_id]
    rfl
  obtain ⟨m, sqm⟩ := exists_isPullback_of_preimage_opensRange
    B S hS L (h c) jΩ hcOpen hjΩopen hpreimage
  have : Mono (h c) := q.mono_of_mono_map inferInstance
  have : Mono jΩ := q.mono_of_mono_map inferInstance
  have hbc := isBaseChange_of_represented_open_pullback B S hS
    f' (b a₀) bΩ lV' hlV'b L hLfst hLsnd (h c) jΩ m sqm
    (z c) zΩ (hz c) hbΩ (hzsub c) hjΩsub
  have hsections : F.map lV'.op (yonedaEquiv (p c)) = yonedaEquiv aΩ := by
    apply (Space.finiteOpenSubspacePresheaf B S hS
      (schemeSpaceMap f')).sections RΩ |>.injective
    apply finitePart_map_sections_eq_of_isBaseChange
    rwa [hsec c]
  refine ⟨RΩ, ρ, lV' ≫ ι c, (default : Spec (.of Ω)), hr₀, ?_⟩
  rw [Functor.map_comp, Category.assoc, hpT]
  apply yonedaEquiv.injective
  show yonedaEquiv (yoneda.map lV' ≫ p c) = yonedaEquiv aΩ
  rw [← yonedaEquiv_naturality]
  exact hsections

end AlgebraicGeometry.FinitePartChart

end
