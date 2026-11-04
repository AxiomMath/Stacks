module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteOverDenseOpenSubspace.QuasiCompactAndSeparatedCases

/-!
# Finiteness over a dense open subspace: étale charts and atlases

The quasi-compact case is applied on an affine étale chart of the source. A morphism from an
algebraic space to an affine scheme which is locally of finite type is finite as soon as its
composite with a surjective étale morphism from an affine scheme is finite, together with the
corresponding relation. Finiteness of fibre products of schemes is then transported to the
representable presheaves on the big fppf site, open subschemes of an object of the site being
seen as objects of the site again. These are auxiliary results for **Stacks 0BBC**.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology
attribute [local instance] CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange

private theorem finite_fiber_of_finiteType_of_codimensionZero
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsFiniteType B S hS f)
    (y : points B S hS Y)
    (hy : localRingDimension B S hS y = 0)
    (hfiber : ∀ x : points B S hS X,
      pointsMap B S hS X f x = y →
        localRingDimension B S hS x = 0) :
    Set.Finite {x : points B S hS X |
      pointsMap B S hS X f x = y} := by
  have hqf := ((quasiFiniteAt_over_codimensionZeroPoint_tfae
    B S hS hX hY f hf.1 y hy).out 1 2).mp hfiber
  exact (finite_setOf_mapsTo_and_isQuasiFiniteAt
    B S hS hX hY f hf y).subset fun x hx => ⟨hx, hqf x hx⟩

theorem exists_dense_open_isFinite_etale_chart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hYdecent : IsDecentSpace B S hS Y)
    (hYzero : Set.Finite {y : points B S hS Y |
      localRingDimension B S hS y = 0})
    (hzero : ∀ x : points B S hS X,
      localRingDimension B S hS (pointsMap B S hS X f x) = 0 →
        localRingDimension B S hS x = 0)
    (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (a : yoneda.obj U ⟶ X) (ha : IsEtale B S hS a) :
    letI := pointTopology B S hS Y
    ∃ V : Subfunctor Y, IsOpenSubspace B S hS V ∧
      Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)) ∧
      IsFinite B S hS (pullback.snd (a ≫ f) V.ι) := by
  have hUalg := isAlgebraicSpace_yoneda B S hS U
  have hUqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal (yoneda.obj U) := by
    apply isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme
      B S hS B.contains_terminal (X := yoneda.obj U)
    refine ⟨U, ?_, ⟨Functor.representableByEquiv.symm (Iso.refl _)⟩⟩
    let := hU
    infer_instance
  have hUqc : IsQuasiCompactSpace B S hS (yoneda.obj U) :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS U hU
  have hlfta : IsLocallyOfFiniteType B S hS a := by
    have hlqf := isLocallyQuasiFinite_of_isEtale B S hS hX ha
    intro V W b c g hb hc hcomm
    exact (hlqf V W b c g hb hc hcomm).1
  have hft : IsFiniteType B S hS (a ≫ f) :=
    ⟨isLocallyOfFiniteType_comp B S hS hUalg hX hY a f hlfta hf,
      isQuasiCompact_of_isQuasiCompactSpace
        B S hS B.contains_terminal hY hYqs hUqc (a ≫ f)⟩
  have hqs := isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source
    B S hS B.contains_terminal hUalg hUqs (a ≫ f)
  apply exists_dense_open_isFinite_of_quasiSeparated_finiteType
    B S hS hUalg hY (a ≫ f) hqs hft hYdecent hYzero
  intro y hy
  apply finite_fiber_of_finiteType_of_codimensionZero B S hS hUalg hY (a ≫ f) hft y hy
  intro u hu
  apply (localRingDimension_zero_iff_of_isEtale B S hS hUalg hX a ha u).2
  apply hzero
  have hmap : pointsMap B S hS X f
      (pointsMap B S hS (yoneda.obj U) a u) = y := by
    simpa only [pointsMap_comp, Function.comp_apply] using hu
  exact hmap.symm ▸ hy


/-- A morphism of representables is finite exactly when its image in schemes is finite. -/
private theorem isFinite_yoneda_map_iff {A C : BigFppfOver B S hS} (m : A ⟶ C) :
    IsFinite B S hS (yoneda.map m) ↔
      _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map m) := by
  let P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
    (BigFppfOver.toScheme B S hS)
  let : P.IsStableUnderBaseChange := inverseImage_stableUnderBaseChange B S hS _
  rw [isFinite_iff_representable B S hS _ (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_yoneda B S hS _)]
  exact ⟨fun h ↦ (MorphismProperty.relative_map_iff (F := yoneda) (P := P)).mp h.2,
    fun h ↦ have hp := (MorphismProperty.relative_map_iff (F := yoneda) (P := P)).mpr h
      ⟨hp.1, hp⟩⟩

private theorem finite_of_finite_surjective_affine_atlas
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (U V : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (g : yoneda.obj U ⟶ X) (f : X ⟶ yoneda.obj V)
    (hgfin : IsFinite B S hS g)
    (hgsurj : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hget : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hcomp : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (g ≫ f)))) :
    IsFinite B S hS f := by
  let : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    inverseImage_stableUnderBaseChange B S hS _
  let : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    inverseImage_stableUnderBaseChange B S hS _
  let : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    inverseImage_stableUnderBaseChange B S hS _
  let T := BigFppfOver.toScheme B S hS
  let : IsAffine (T.obj U) := hU
  have hgrel := (isFinite_iff_representable B S hS g
    (isAlgebraicSpace_yoneda B S hS U) hX).mp hgfin
  have hflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      T).presheaf g := by
    refine ⟨hget.1, fun a b ξ fst snd hpb ↦ ?_⟩
    have h1 : _root_.AlgebraicGeometry.IsFinite (T.map snd) := hgrel.2.2 ξ fst snd hpb
    have h2 : Etale (T.map snd) := hget.2 ξ fst snd hpb
    exact (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (T.map snd)).mpr ⟨h1, inferInstance, inferInstance⟩
  have hrepX : X.IsRepresentable :=
    isRepresentable_of_surjectiveEtale_finiteLocallyFree_of_isImmersion B S hS
      (Z := U) (𝟙 ((BigFppfOver.toScheme B S hS).obj U)) hX g hflf hgsurj hget
  obtain ⟨W, ⟨e⟩⟩ : ∃ W : BigFppfOver B S hS, Nonempty (X ≅ yoneda.obj W) :=
    ⟨hrepX.has_representation.choose, ⟨Functor.representableByEquiv
      hrepX.has_representation.choose_spec.some |>.symm⟩⟩
  let k : U ⟶ W := yoneda.preimage (g ≫ e.hom)
  let l : W ⟶ V := yoneda.preimage (e.inv ≫ f)
  have hk : yoneda.map k = g ≫ e.hom := yoneda.map_preimage _
  have hl : yoneda.map l = e.inv ≫ f := yoneda.map_preimage _
  have hkl : k ≫ l = yoneda.preimage (g ≫ f) := by
    apply yoneda.map_injective
    simp [Functor.map_comp, hk, hl]
  have hksurj : Surjective (T.map k) := by
    apply (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage (@Surjective.{u}) T)).mp
    rw [hk]
    exact MorphismProperty.RespectsIso.postcomp _ e.hom g hgsurj
  have hkfin : _root_.AlgebraicGeometry.IsFinite (T.map k) := by
    apply (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsFinite.{u}) T)).mp
    rw [hk]
    exact MorphismProperty.RespectsIso.postcomp _ e.hom g hgrel.2
  have : _root_.AlgebraicGeometry.IsFinite (T.map k) := hkfin
  have : Surjective (T.map k) := hksurj
  have hW : IsAffine (T.obj W) :=
    Stacks.AffineFromFiniteSurjective.isAffine_of_finite_surjective (T.map k)
  have hle : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf e.inv := by
    simpa using MorphismProperty.RespectsIso.postcomp _ e.inv (𝟙 _)
      (presheaf_etale_id B S hS W)
  have hlft : LocallyOfFiniteType (T.map l) := by
    apply hft W V e.inv (𝟙 _) l hle (presheaf_etale_id B S hS V)
    simpa using hl
  have hklfin : _root_.AlgebraicGeometry.IsFinite (T.map k ≫ T.map l) := by
    rw [← Functor.map_comp, hkl]
    exact hcomp
  let : IsAffine (T.obj W) := hW
  let : IsAffine (T.obj V) := hV
  let : Surjective (T.map k) := hksurj
  let : LocallyOfFiniteType (T.map l) := hlft
  let : _root_.AlgebraicGeometry.IsFinite (T.map k ≫ T.map l) := hklfin
  let : _root_.AlgebraicGeometry.UniversallyClosed (T.map l) :=
    _root_.AlgebraicGeometry.UniversallyClosed.of_comp_surjective (T.map k) (T.map l)
  let : _root_.AlgebraicGeometry.IsProper (T.map l) := ⟨⟩
  have hlfin : _root_.AlgebraicGeometry.IsFinite (T.map l) :=
    _root_.AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom.mpr
      ⟨inferInstance, inferInstance⟩
  exact isFinite_of_arrowIso B S hS _ _ e.symm (Iso.refl _) (by simp [hl])
    ((isFinite_yoneda_map_iff B S hS l).mpr hlfin)

theorem finite_of_finite_atlas_and_relation
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (U T : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (a : yoneda.obj U ⟶ X) (b : X ⟶ yoneda.obj T)
    (hasurj : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haet : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : IsLocallyOfFiniteType B S hS b)
    (hcomp : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (a ≫ b))))
    (hrel : IsFinite B S hS
      (pullback.snd a a ≫ a ≫ b)) :
    IsFinite B S hS b := by
  let F := BigFppfOver.toScheme B S hS
  let k : U ⟶ T := yoneda.preimage (a ≫ b)
  let r := haet.1.snd a
  have sq := haet.1.isPullback a
  have hmap : yoneda.map (r ≫ k) = yoneda.map r ≫ a ≫ b := by
    simp [k, Functor.map_comp]
  have hrel' : IsFinite B S hS (yoneda.map (r ≫ k)) := by
    apply isFinite_of_arrowIso B S hS _ _ sq.isoPullback.symm (Iso.refl _) ?_ hrel
    simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, hmap]
    rw [← sq.isoPullback_inv_snd]
    rfl
  have hfinite : _root_.AlgebraicGeometry.IsFinite (F.map (r ≫ k)) :=
    (isFinite_yoneda_map_iff B S hS _).mp hrel'
  have hr : _root_.AlgebraicGeometry.IsFinite (F.map r) := by
    let : _root_.AlgebraicGeometry.IsFinite (F.map k) := hcomp
    have : _root_.AlgebraicGeometry.IsFinite (F.map r ≫ F.map k) := by
      rw [← Functor.map_comp]
      exact hfinite
    exact _root_.AlgebraicGeometry.IsFinite.of_comp (F.map r) (F.map k)
  exact finite_of_finite_surjective_affine_atlas B S hS hX U T hU hT a b
    (finite_of_finite_etale_kernelPair B S hS hX U a hasurj haet hr)
    hasurj haet hb hcomp

lemma finite_selfPullback_fiber_of_isFinite_restrict
    {U T : Scheme.{u}} (k : U ⟶ T) (V : T.Opens) (η : T)
    (hηV : η ∈ V) (hfin : _root_.AlgebraicGeometry.IsFinite (k ∣_ V)) :
    ((pullback.snd k k ≫ k) ⁻¹' {η}).Finite := by
  let A := k ⁻¹ᵁ V
  let O : (pullback k k).Opens :=
    (pullback.fst k k ⁻¹ᵁ A) ⊓ (pullback.snd k k ⁻¹ᵁ A)
  have sq := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback k k)
    (US := V) (UT := A) (UX := A) le_rfl le_rfl (UY := O) rfl
  let b := (pullback.snd k k).resLE A O (by intro x hx; exact hx.2)
  have hb : _root_.AlgebraicGeometry.IsFinite b := by
    apply MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsFinite) sq
    simpa only [A, Scheme.Hom.resLE_eq_morphismRestrict] using hfin
  let := hb
  let : _root_.AlgebraicGeometry.IsFinite (k ∣_ V) := hfin
  have hf := (b ≫ (k ∣_ V)).finite_preimage_singleton ⟨η, hηV⟩
  apply (hf.image O.ι).subset
  intro x hx
  have hx' : k (pullback.snd k k x) = η := hx
  have hfst : k (pullback.fst k k x) = η := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact hx'
  have hxO : x ∈ O := ⟨by change k (pullback.fst k k x) ∈ V; rwa [hfst],
    by change k (pullback.snd k k x) ∈ V; rwa [hx']⟩
  refine ⟨⟨x, hxO⟩, ?_, rfl⟩
  apply Subtype.ext
  show ((b ≫ (k ∣_ V)) ≫ V.ι) ⟨x, hxO⟩ = η
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
  show (((pullback.snd k k).resLE A O _ ≫ A.ι) ≫ k) ⟨x, hxO⟩ = η
  rw [Scheme.Hom.resLE_comp_ι]
  exact hx'

lemma kernelPair_baseChange {C : Type*} [Category C] [HasPullbacks C]
    {U U' X X' : C}
    {a : U ⟶ X} {a' : U' ⟶ X'} {i : U' ⟶ U} {p : X' ⟶ X}
    (h : IsPullback i a' a p) :
    IsPullback (pullback.map a' a' a a i i p h.w.symm h.w.symm)
      (pullback.snd a' a') (pullback.snd a a) i := by
  let d := pullback.map a' a' a a i i p h.w.symm h.w.symm
  have hw : pullback.snd a' a' ≫ i = d ≫ pullback.snd a a := by
    simp only [d, pullback.map, pullback.lift_snd]
  have hs := (IsPullback.of_hasPullback a' a').paste_horiz h
  have hs' : IsPullback (d ≫ pullback.fst a a) (pullback.snd a' a')
      a (i ≫ a) := by
    simpa only [d, pullback.map, pullback.lift_fst, h.w] using hs
  exact hs'.of_right hw.symm (IsPullback.of_hasPullback a a)

lemma finite_pullback_of_range_subset_open
    {R T A : Scheme.{u}} (l : R ⟶ T) (c : A ⟶ T) (D : T.Opens)
    (hfin : _root_.AlgebraicGeometry.IsFinite (l ∣_ D))
    (hc : Set.range c.base ⊆ Set.range D.ι.base) :
    _root_.AlgebraicGeometry.IsFinite (pullback.snd l c) := by
  let b := AlgebraicGeometry.IsOpenImmersion.lift D.ι c hc
  have hb : b ≫ D.ι = c := AlgebraicGeometry.IsOpenImmersion.lift_fac D.ι c hc
  have sq := (IsPullback.of_hasPullback (l ∣_ D) b).paste_horiz
    (isPullback_morphismRestrict l D).flip
  have sq' : IsPullback (pullback.fst (l ∣_ D) b ≫ (l ⁻¹ᵁ D).ι)
      (pullback.snd (l ∣_ D) b) l c := by simpa only [hb] using sq
  let := hfin
  have hf : _root_.AlgebraicGeometry.IsFinite (sq'.isoPullback.hom ≫ pullback.snd l c) := by
    rw [sq'.isoPullback_hom_snd]
    infer_instance
  let := hf
  have hh : _root_.AlgebraicGeometry.IsFinite
      (sq'.isoPullback.inv ≫ (sq'.isoPullback.hom ≫ pullback.snd l c)) :=
    inferInstance
  simpa only [Iso.inv_hom_id_assoc] using hh

noncomputable def openSubschemeSiteObject
    (U : BigFppfOver B S hS)
    (D : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    BigFppfOver B S hS :=
  let hD : B.Contains D.toScheme := (Scheme.size_coe_opens_le _ D).trans_lt U.left.2
  let j : B.obj hD ⟶ U.left := B.inclusion.preimage D.ι
  Over.mk (j ≫ U.hom)

noncomputable def openSubschemeSiteι
    (U : BigFppfOver B S hS)
    (D : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    openSubschemeSiteObject B S hS U D ⟶ U :=
  Over.homMk (B.inclusion.preimage D.ι)

theorem map_openSubschemeSiteι
    (U : BigFppfOver B S hS)
    (D : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (BigFppfOver.toScheme B S hS).map
      (openSubschemeSiteι B S hS U D) = D.ι := B.inclusion.map_preimage _

theorem finite_pullback_yoneda_of_scheme
    {R T A : BigFppfOver B S hS} (l : R ⟶ T) (c : A ⟶ T)
    (hfin : _root_.AlgebraicGeometry.IsFinite (pullback.snd
      ((BigFppfOver.toScheme B S hS).map l)
      ((BigFppfOver.toScheme B S hS).map c))) :
    IsFinite B S hS
      (pullback.snd (yoneda.map l) (yoneda.map c)) := by
  let F := BigFppfOver.toScheme B S hS
  have sq := (IsPullback.of_hasPullback l c).map F
  have hs : _root_.AlgebraicGeometry.IsFinite (F.map (pullback.snd l c)) := by
    rw [← sq.isoPullback_hom_snd]
    let := hfin
    infer_instance
  have hf := (isFinite_yoneda_map_iff B S hS _).mpr hs
  have sqY := (IsPullback.of_hasPullback l c).map yoneda
  apply isFinite_of_arrowIso B S hS _ _ sqY.isoPullback (Iso.refl _) ?_ hf
  simpa only [Iso.refl_hom, Category.comp_id] using sqY.isoPullback_hom_snd

end AlgebraicGeometry.Space

end
