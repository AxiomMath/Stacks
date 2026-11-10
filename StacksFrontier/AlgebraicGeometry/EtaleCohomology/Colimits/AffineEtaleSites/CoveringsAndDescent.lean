module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.BaseChange
-- Not a `public import`: the survivor is named only inside a private proof below.
import StacksFrontier.AlgebraicGeometry.Limits.Descending.ConstructibleImage
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.BaseChange

/-!
# Coverings of the small affine étale site and affine étale models over a limit

The characterisation `Stacks.EtaleCohomology.mem_smallAffineEtale_precoverage_iff` of the
coverings of the small affine étale site as the finite jointly surjective étale families,
comparison of sites through equivalences of sheaf categories, and the descent of étaleness of a
base change to a finite stage (Stacks 0EYL).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)

universe u₁ v₁ u₂ v₂ w₁

/-- Any natural family of chosen pullbacks agrees with the slice pullback functor. -/
private noncomputable def overPullbackComparison {C : Type*} [Category* C] [HasPullbacks C]
    {M : Type*} [Category* M] {S T : C} (f : T ⟶ S)
    (F : M ⥤ Over S) (G : M ⥤ Over T)
    (p : G ⋙ Over.forget T ⟶ F ⋙ Over.forget S)
    (hp : ∀ A, IsPullback (p.app A) (G.obj A).hom (F.obj A).hom f) :
    G ≅ F ⋙ Over.pullback f := by
  refine NatIso.ofComponents (fun A => Over.isoMk (hp A).isoPullback
    (hp A).isoPullback_hom_snd) ?_
  intro A A' g
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, CategoryTheory.Functor.comp_map, Over.isoMk_hom_left,
      Over.pullback_map_left, Category.assoc, IsPullback.isoPullback_hom_fst,
      pullback.lift_fst]
    rw [← Category.assoc, IsPullback.isoPullback_hom_fst]
    exact p.naturality g
  · simp only [Over.comp_left, CategoryTheory.Functor.comp_map, Over.isoMk_hom_left,
      Over.pullback_map_left, Category.assoc, IsPullback.isoPullback_hom_snd,
      pullback.lift_snd]
    exact Over.w (G.map g)

private lemma chosen_baseChange_map_isPullback
    {C : Type*} [Category* C] [HasPullbacks C]
    {M : Type*} [Category* M] {S T : C} (f : T ⟶ S)
    (F : M ⥤ Over S) (G : M ⥤ Over T)
    (p : G ⋙ Over.forget T ⟶ F ⋙ Over.forget S)
    (hp : ∀ A, IsPullback (p.app A) (G.obj A).hom (F.obj A).hom f)
    {A B : M} (g : A ⟶ B) :
    IsPullback (G.map g).left (p.app A) (p.app B) (F.map g).left := by
  apply IsPullback.of_right (t := (hp B).flip)
    (p := p.naturality g)
  change IsPullback ((G.map g).left ≫ (G.obj B).hom) (p.app A) f
    ((F.map g).left ≫ (F.obj B).hom)
  rw [Over.w, Over.w]
  exact (hp A).flip

private lemma mem_range_of_isPullback {P A B C : Scheme.{u}}
    {f : P ⟶ B} {p : P ⟶ A} {q : B ⟶ C} {g : A ⟶ C}
    (h : IsPullback f p q g) (b : B) :
    b ∈ Set.range f ↔ q b ∈ Set.range g := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨p a, (congrArg (fun t => t a) h.w).symm⟩
  · rintro ⟨a, ha⟩
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback b a ha.symm
    exact ⟨h.isoPullback.inv z, (congrArg (fun t => t z) h.isoPullback_inv_fst).trans hz⟩

/-- Pulling the stage diagram of an affine-transition limit back along a map from an affine
scheme gives a limit diagram of affine schemes with affine transition maps. -/
private lemma isLimit_pullback_stage_affine {J : Type u} [Category.{u} J] [IsCofiltered J]
    (F : J ⥤ Scheme.{u}) (d : Cone F) (hd : IsLimit d)
    [∀ {i j : J} (a : i ⟶ j), IsAffineHom (F.map a)]
    (i : J) {U : Scheme.{u}} [IsAffine U] (q : U ⟶ F.obj i) :
    let G := (Over.post F ⋙ Over.pullback q) ⋙ Over.forget U
    Nonempty (IsLimit ((Over.forget U).mapCone
      ((Over.pullback q).mapCone (overStageCone F d i)))) ∧
      (∀ j : Over i, IsAffine (G.obj j)) ∧ ∀ {j k : Over i} (a : j ⟶ k), IsAffineHom (G.map a) := by
  intro G
  refine ⟨⟨isLimitOfPreserves _
    (isLimitOfPreserves (Over.pullback q) (isLimitOverStageCone F d hd i))⟩, fun j => ?_,
    fun {j k} a => ?_⟩
  · have : IsAffineHom (pullback.snd (F.map j.hom) q) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) inferInstance
    change IsAffine (pullback (F.map j.hom) q)
    exact isAffine_of_isAffineHom (pullback.snd (F.map j.hom) q)
  · exact MorphismProperty.of_isPullback
      (isPullback_pullback_map q ((Over.post F).map a)).flip
      (show IsAffineHom (F.map a.left) from inferInstance)

/-- A constructible subset containing every limit fibre contains every fibre at a later stage. -/
private lemma exists_stage_range_subset {J : Type u} [Category.{u} J] [IsCofiltered J]
    (F : J ⥤ Scheme.{u}) (d : Cone F) (hd : IsLimit d)
    [∀ {i j : J} (a : i ⟶ j), IsAffineHom (F.map a)]
    (i : J) {Y : Scheme.{u}} [IsAffine Y] (q : Y ⟶ F.obj i)
    (E : Set Y) (hE : Topology.IsConstructible E)
    (hlim : ∀ (p : d.pt) (y : Y), (d.π.app i) p = q y → y ∈ E) :
    ∃ (j : J) (a : j ⟶ i), ∀ (p : F.obj j) (y : Y), F.map a p = q y → y ∈ E := by
  classical
  obtain ⟨T, hT, hTc, t, ht⟩ := exists_affine_scheme_with_range hE.compl
  have : IsAffine T := hT
  let q' := t ≫ q
  let G := (Over.post F ⋙ Over.pullback q') ⋙ Over.forget T
  let d' := (Over.forget T).mapCone ((Over.pullback q').mapCone (overStageCone F d i))
  obtain ⟨⟨hd'⟩, hG, hG'⟩ := isLimit_pullback_stage_affine F d hd i q'
  have := hG
  have {j k : Over i} (a : j ⟶ k) : IsAffineHom (G.map a) := hG' a
  by_contra hn
  push Not at hn
  have (j : Over i) : Nonempty (G.obj j) := by
    obtain ⟨p, y, hp, hy⟩ := hn j.left j.hom
    obtain ⟨z, hz⟩ := ht ▸ (show y ∈ Eᶜ from hy)
    have hpz : F.map j.hom p = q' z := by
      change F.map j.hom p = q (t z)
      rw [hz]
      exact hp
    obtain ⟨w, _, _⟩ := Scheme.Pullback.exists_preimage_pullback p z hpz
    exact ⟨w⟩
  obtain ⟨z⟩ := Scheme.nonempty_of_isLimit G d' hd'
  let p := (pullback.fst (d.π.app i) q') z
  let w := (pullback.snd (d.π.app i) q') z
  have hpw : (d.π.app i) p = q (t w) :=
    congrArg (fun f => f z) (pullback.condition (f := d.π.app i) (g := q'))
  have hmem : t w ∈ Eᶜ := by
    rw [← ht]
    exact ⟨w, rfl⟩
  exact hmem (hlim p (t w) hpw)

private abbrev affineEtaleToBigScheme (B : AlgebraicGeometry.BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :=
  AlgebraicGeometry.SmallAffineEtale.inclusion B S hS ⋙
    AlgebraicGeometry.SmallEtale.inclusion B S hS ⋙ Over.forget (B.obj S hS)

/-- An arrow to a fixed étale object determines its source's structure map. -/
private lemma affineEtaleToBigScheme_arrow_injective
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicGeometry.SmallAffineEtale B S hS) :
    Function.Injective (fun p : Σ Y : AlgebraicGeometry.SmallAffineEtale B S hS, Y ⟶ X =>
      (⟨(affineEtaleToBigScheme B S hS).obj p.1,
        (affineEtaleToBigScheme B S hS).map p.2⟩ :
        Σ Y : B.Scheme, Y ⟶ (affineEtaleToBigScheme B S hS).obj X)) := by
  rintro ⟨⟨⟨A, hA⟩, ha⟩, f⟩ ⟨⟨⟨A', hA'⟩, ha'⟩, f'⟩ h
  obtain ⟨Y, k, rfl⟩ := Over.mk_surjective A
  obtain ⟨Y', k', rfl⟩ := Over.mk_surjective A'
  have hY : Y = Y' := congrArg Sigma.fst h
  cases hY
  have hf : f.hom.hom.left = f'.hom.hom.left := eq_of_heq (Sigma.mk.inj h).2
  have hk : k = k' :=
    (Over.w f.hom.hom).symm.trans
      ((congrArg (fun z => z ≫ X.obj.obj.hom) hf).trans (Over.w f'.hom.hom))
  cases hk
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact Over.OverMorphism.ext hf

/-- **A presieve of the small affine etale site is a covering family exactly when it is finite
and its image is a jointly surjective family of etale morphisms of schemes.**

The point of this characterisation is what it does *not* mention. Membership in
`AlgebraicGeometry.SmallAffineEtale.precoverage` unfolds to
`AlgebraicGeometry.SmallAffineEtale.IsCovering`, hence to `B.IsCovering`, hence to
`CovBounded IsEtaleCovering B.coveringBound`, whose second conjunct is the cardinality bound
`#I₀ ≤ B.coveringBound`. A `BigEtaleSite` carries no axiom bounding `coveringBound` from below, so
that conjunct is not discharged by finiteness: the only entry is the field
`AlgebraicGeometry.BigEtaleSite.exists_covering_rep`, which replaces an etale covering by a
combinatorially equivalent *selected* one that is bounded, after which the index type has to be
cut down again. The `mpr` direction below performs exactly that — `exists_covering_rep`, then
`deduplicateFamily`, then `Cardinal.mk_le_of_injective` along an injection of the deduplicated
index types, then `deduplicateFamily_card_le` — and it is the only place in this development where
the bound is discharged. Everything downstream should go through this iff rather than repeat the
dance. The refinement lemmas that do repeat it are each a partial reimplementation of it:
`AlgebraicGeometry.finite_standard_refinement` in
`StacksFrontier/AlgebraicGeometry/ProEtale/Site/AffineDense.lean`, which is the canonical one and
the only one bearing that name; and two private siblings that are *not* copies of it, because
each is stated over a different site and so cannot be replaced by it —
`AlgebraicGeometry.bigZariskiSite_finite_standard_refinement` in
`StacksFrontier/AlgebraicGeometry/Topologies/BigSites/AffineZariskiDenseSubsite.lean`, over a
`BigZariskiSite` and concluding in addition that every member is a `basicOpen` of the target;
and `AlgebraicGeometry.Space.finite_affine_etaleCovering_refinement` in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineEtaleDenseSubsite.lean`, over the étale coverings
of a `BigFppfSite`. -/
public lemma mem_smallAffineEtale_precoverage_iff
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicGeometry.SmallAffineEtale B S hS) (R : Presieve X) :
    R ∈ AlgebraicGeometry.SmallAffineEtale.precoverage B S hS X ↔
      R ∈ Precoverage.finite _ X ∧
        R.map (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS) ∈
          Scheme.etalePrecoverage ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj X) := by
  constructor
  · rintro ⟨E, rfl, hE⟩
    have : Finite E.I₀ := hE.2
    refine ⟨Precoverage.ofArrows_mem_finite _ _, ?_⟩
    rw [← PreZeroHypercover.presieve₀_map]
    exact hE.1.1
  · rintro ⟨hfin, hcov⟩
    let F := affineEtaleToBigScheme B S hS
    let E := R.preZeroHypercover
    have : Finite E.I₀ := Set.Finite.to_subtype hfin
    have he : AlgebraicGeometry.IsEtaleCovering ⟨F.obj X, E.map F⟩ := by
      change (E.map (F ⋙ B.inclusion)).presieve₀ ∈ Scheme.etalePrecoverage _
      rw [PreZeroHypercover.presieve₀_map, Presieve.presieve₀_preZeroHypercover]
      exact hcov
    obtain ⟨⟨T, Q⟩, hQ, hcomb⟩ := B.exists_covering_rep ⟨F.obj X, E.map F⟩ he
    obtain ⟨ht, hcomb⟩ := hcomb
    cases ht
    have hinj := affineEtaleToBigScheme_arrow_injective B S hS X
    let m : (deduplicateFamily E).I₀ → (deduplicateFamily (E.map F)).I₀ := fun z =>
      ⟨⟨F.obj z.1.1, F.map z.1.2⟩, by
        obtain ⟨k, hk⟩ := z.2
        exact ⟨k, congrArg (fun p : Σ Y, Y ⟶ X =>
          (⟨F.obj p.1, F.map p.2⟩ : Σ Y, Y ⟶ F.obj X)) hk⟩⟩
    have hm : Function.Injective m := fun _ _ hz => Subtype.ext (hinj (congrArg Subtype.val hz))
    have hbound : Cardinal.mk (deduplicateFamily E).I₀ ≤ B.coveringBound :=
      (Cardinal.mk_le_of_injective hm).trans
        ((deduplicateFamily_card_le hcomb).trans hQ.2)
    refine ⟨deduplicateFamily E, ?_, ?_, deduplicateFamily_finite E⟩
    · rw [deduplicateFamily_presieve₀, Presieve.presieve₀_preZeroHypercover]
    · refine ⟨?_, hbound⟩
      change ((deduplicateFamily E).map (F ⋙ B.inclusion)).presieve₀ ∈ Scheme.etalePrecoverage _
      rw [PreZeroHypercover.presieve₀_map, deduplicateFamily_presieve₀,
        Presieve.presieve₀_preZeroHypercover]
      exact hcov

private lemma affineEtale_precoverage_eq
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    AlgebraicGeometry.SmallAffineEtale.precoverage B S hS = Precoverage.finite _ ⊓
      Scheme.etalePrecoverage.comap (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS) := by
  ext X R
  exact mem_smallAffineEtale_precoverage_iff B S hS X R

private lemma affineEtaleToScheme_coverPreserving
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    CoverPreserving (AlgebraicGeometry.SmallAffineEtale.topology B S hS) Scheme.etaleTopology
      (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS) := by
  have hbc : (MorphismProperty.precoverage (@Etale.{u})).IsStableUnderBaseChange :=
    MorphismProperty.instIsStableUnderBaseChangePrecoverageOfIsStableUnderBaseChange
  have hbc' : (Scheme.precoverage (@Etale.{u})).IsStableUnderBaseChange :=
    inferInstanceAs (Precoverage.IsStableUnderBaseChange
      (Scheme.jointlySurjectivePrecoverage ⊓ MorphismProperty.precoverage (@Etale.{u})))
  have : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).IsContinuous
      ((Scheme.precoverage @Etale).comap
        (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS)).toGrothendieck
      Scheme.etaleTopology :=
    Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
      (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS)
      ((Scheme.precoverage @Etale).comap
        (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS))
      (Scheme.precoverage @Etale) le_rfl
  have hle : AlgebraicGeometry.SmallAffineEtale.topology B S hS ≤
      ((Scheme.precoverage @Etale).comap
        (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS)).toGrothendieck :=
    Precoverage.toGrothendieck_monotone (by
      intro X R hR
      exact ((mem_smallAffineEtale_precoverage_iff B S hS X R).mp hR).2)
  exact ⟨fun hR => (CoverPreserving.of_isContinuous
    (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS)
    ((Scheme.precoverage @Etale).comap
      (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS)).toGrothendieck
    Scheme.etaleTopology).cover_preserve (hle _ hR)⟩

private lemma etale_cover_of_generate {X : Scheme.{u}} (R : Presieve X)
    (hR : Sieve.generate R ∈ Scheme.etaleTopology X)
    (het : ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Etale f) : R ∈ Scheme.etalePrecoverage X := by
  obtain ⟨𝒰, h𝒰⟩ := Scheme.mem_grothendieckTopology_iff.mp hR
  refine ⟨?_, ?_⟩
  · rw [Scheme.jointlySurjectivePrecoverage,
      Presieve.mem_comap_jointlySurjectivePrecoverage_iff]
    intro x
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    obtain ⟨Y, g, f, hf, hw⟩ := h𝒰 _ _ (Presieve.ofArrows.mk i)
    exact ⟨Y, f, hf, g y, congrArg (fun t => t y) hw⟩
  · exact het

private lemma affineEtale_hom_etale
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.SmallAffineEtale B S hS} (f : X ⟶ Y) :
    Etale ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map f) := by
  let q := B.inclusion.map Y.obj.obj.hom
  have : Etale q := Y.obj.property
  have : Etale ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map f ≫ q) := by
    change Etale (B.inclusion.map f.hom.hom.left ≫ B.inclusion.map Y.obj.obj.hom)
    have hw := congrArg B.inclusion.map (Over.w f.hom.hom)
    rw [Functor.map_comp] at hw
    rw [hw]
    exact X.obj.property
  exact Etale.of_comp _ q

private lemma affineEtale_topology_finite_cover
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicGeometry.SmallAffineEtale B S hS) (R : Presieve X)
    (hfin : R ∈ Precoverage.finite _ X)
    (hR : R ∈ (AlgebraicGeometry.SmallAffineEtale.topology B S hS).toPrecoverage X) :
    R ∈ AlgebraicGeometry.SmallAffineEtale.precoverage B S hS X := by
  apply (mem_smallAffineEtale_precoverage_iff B S hS X R).mpr
  refine ⟨hfin, etale_cover_of_generate _ ?_ ?_⟩
  · rw [Sieve.generate_map_eq_functorPushforward]
    exact (affineEtaleToScheme_coverPreserving B S hS).cover_preserve hR
  · intro Y f hf
    cases hf with
    | of hf => exact affineEtale_hom_etale B S hS _

private abbrev smallEtaleToOver (B : AlgebraicGeometry.BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :=
  AlgebraicGeometry.SmallEtale.inclusion B S hS ⋙ Over.post B.inclusion

private noncomputable def smallEtaleBaseChangeToOverIso
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) :
    AlgebraicGeometry.smallEtaleBaseChange B f ⋙
        smallEtaleToOver B T.obj T.property ≅
      smallEtaleToOver B S.obj S.property ⋙ Over.pullback (B.inclusion.map f) := by
  let F := AlgebraicGeometry.smallEtaleBaseChange B f
  refine overPullbackComparison (B.inclusion.map f)
    (smallEtaleToOver B S.obj S.property)
    (F ⋙ smallEtaleToOver B T.obj T.property) ?_ ?_
  · refine { app := fun A => B.inclusion.map (pullback.fst A.obj.hom f), naturality := ?_ }
    intro A A' g
    change B.inclusion.map ((Over.pullback f).map g.hom).left ≫
        B.inclusion.map (pullback.fst A'.obj.hom f) =
      B.inclusion.map (pullback.fst A.obj.hom f) ≫ B.inclusion.map g.hom.left
    rw [← B.inclusion.map_comp, ← B.inclusion.map_comp]
    apply congrArg B.inclusion.map
    exact pullback.lift_fst _ _ _
  · intro A
    exact (IsPullback.of_hasPullback A.obj.hom f).map B.inclusion


private lemma continuous_of_sheaf_comparison
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {C' D' : Type*} [Category* C'] [Category* D']
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
    (F : C ⥤ D) (p : C ⥤ C') (q : D ⥤ D') (G : C' ⥤ D')
    (e : F ⋙ q ≅ p ⋙ G)
    [p.IsContinuous J J'] [q.IsContinuous K K'] [G.IsContinuous J' K']
    [(q.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂)) K K').EssSurj] :
    F.IsContinuous J K := by
  have : (p ⋙ G).IsContinuous J K' := Functor.isContinuous_comp p G J J' K'
  have : (F ⋙ q).IsContinuous J K' := Functor.isContinuous_of_iso e.symm J K'
  constructor
  intro H
  obtain ⟨H', ⟨h⟩⟩ := Functor.EssSurj.mem_essImage
    (q.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂)) K K') H
  have hh := (F ⋙ q).op_comp_isSheaf_of_isSheaf J K' H'.obj H'.property
  apply (isSheaf_iff_isSheaf_of_type _ _).mp
  exact (Presheaf.isSheaf_of_iso_iff
    (Functor.isoWhiskerLeft F.op ((sheafToPresheaf K _).mapIso h))).mp hh

/-- Transport a morphism of sites through equivalences on categories of sheaves. -/
private lemma morphismOfSites_of_sheaf_comparison
    {C D : Type u₁} [SmallCategory C] [SmallCategory D]
    {C' D' : Type u₁} [Category.{v₁} C'] [Category.{v₂} D']
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
    (F : C ⥤ D) (p : C ⥤ C') (q : D ⥤ D') (G : C' ⥤ D')
    (e : F ⋙ q ≅ p ⋙ G)
    [p.IsContinuous J J'] [q.IsContinuous K K']
    [(p.sheafPushforwardContinuous (Type u₁) J J').IsEquivalence]
    [(q.sheafPushforwardContinuous (Type u₁) K K').IsEquivalence]
    (hG : _root_.IsMorphismOfSites.{u₁} G J' K') :
    F.IsMorphismOfSites J K := by
  have := hG.toIsContinuous
  let P := p.sheafPushforwardContinuous (Type u₁) J J'
  let Q := q.sheafPushforwardContinuous (Type u₁) K K'
  let R := G.sheafPushforwardContinuous (Type u₁) J' K'
  have : (p ⋙ G).IsContinuous J K' := Functor.isContinuous_comp p G J J' K'
  have : (F ⋙ q).IsContinuous J K' := Functor.isContinuous_of_iso e.symm J K'
  have : F.IsContinuous J K := continuous_of_sheaf_comparison J K J' K' F p q G e
  let F' := F.sheafPushforwardContinuous (Type u₁) J K
  let e' : Q ⋙ F' ≅ R ⋙ P :=
    Functor.sheafPushforwardContinuousComp F q (Type u₁) J K K' ≪≫
      Functor.sheafPushforwardContinuousIso e (Type u₁) J K' ≪≫
      (Functor.sheafPushforwardContinuousComp p G (Type u₁) J J' K').symm
  let er : Q.inv ⋙ R ⋙ P ≅ F' :=
    Functor.isoWhiskerLeft Q.inv e'.symm ≪≫
      (Functor.associator Q.inv Q F').symm ≪≫
      Functor.isoWhiskerRight Q.asEquivalence.counitIso F' ≪≫ Functor.leftUnitor F'
  obtain ⟨L, ⟨adj⟩, hL⟩ := hG.hasExactLeftAdjoint
  let adj' : (P.inv ⋙ L ⋙ Q) ⊣ F' :=
    ((P.asEquivalence.symm.toAdjunction.comp adj).comp
      Q.asEquivalence.toAdjunction).ofNatIsoRight er
  have : PreservesFiniteLimits L := hL
  have : PreservesFiniteLimits (P.inv ⋙ L ⋙ Q) := inferInstance
  refine ⟨inferInstance, ?_, Functor.preservesFiniteColimits_sheafPullback F J K⟩
  exact preservesFiniteLimits_of_natIso
    (adj'.leftAdjointUniq (F.sheafAdjunctionContinuous (Type u₁) J K))

/-- Étaleness of a structure morphism transfers along an isomorphism in the slice category. -/
private lemma etale_of_overIso {S : Scheme.{u}} {A A' : Over S}
    (e : A ≅ A') [Etale A.hom] : Etale A'.hom := by
  have : IsIso (Over.Hom.left e.inv) :=
    ⟨Over.Hom.left e.hom, congrArg Over.Hom.left e.inv_hom_id,
      congrArg Over.Hom.left e.hom_inv_id⟩
  have : Etale (Over.Hom.left e.inv) := inferInstance
  rw [← Over.w e.inv]
  exact Etale.etale_comp _ _

/-- Étaleness of a base change persists under further base change. -/
private lemma etale_baseChange_comp {S T U : Scheme.{u}} (f : U ⟶ T) (g : T ⟶ S)
    (A : Over S) [Etale ((Over.pullback g).obj A).hom] :
    Etale ((Over.pullback (f ≫ g)).obj A).hom := by
  have : Etale (pullback.snd ((Over.pullback g).obj A).hom f) := inferInstance
  have : Etale ((Over.pullback g ⋙ Over.pullback f).obj A).hom := this
  exact etale_of_overIso ((Over.pullbackComp f g).app A).symm

/-- Finitely many local étaleness assertions can be realized at one common stage. -/
private lemma exists_etale_baseChange_of_finite_cover {J : Type*} [Category* J]
    [IsCofiltered J] (F : J ⥤ Scheme.{u}) (i : J) (A : Over (F.obj i))
    (𝒰 : A.left.OpenCover) [Finite 𝒰.I₀]
    (h𝒰 : ∀ k, ∃ (j : J) (a : j ⟶ i),
      Etale (pullback.snd (𝒰.f k ≫ A.hom) (F.map a))) :
    ∃ (j : J) (a : j ⟶ i), Etale ((Over.pullback (F.map a)).obj A).hom := by
  choose j a ha using h𝒰
  obtain ⟨k, b, t, ht⟩ := IsCofiltered.wideCospan a
  have he (l : 𝒰.I₀) : Etale (pullback.snd (𝒰.f l ≫ A.hom) (F.map b)) := by
    rw [← ht l, F.map_comp]
    let : Etale ((Over.pullback (F.map (a l))).obj
      (Over.mk (𝒰.f l ≫ A.hom))).hom := ha l
    exact etale_baseChange_comp (F.map (t l)) (F.map (a l))
      (Over.mk (𝒰.f l ≫ A.hom))
  refine ⟨k, b, ?_⟩
  let V := 𝒰.pullback₁ (pullback.fst A.hom (F.map b))
  apply (MorphismProperty.iff_of_zeroHypercover_source (P := @Etale) V).mpr
  intro l
  have hsq := (IsPullback.of_hasPullback (pullback.fst A.hom (F.map b))
    (𝒰.f l)).flip.paste_vert (IsPullback.of_hasPullback A.hom (F.map b))
  change Etale (pullback.fst (pullback.fst A.hom (F.map b)) (𝒰.f l) ≫
    pullback.snd A.hom (F.map b))
  rw [← hsq.isoPullback_hom_snd]
  let := he l
  infer_instance

/-- Étaleness can be tested after factoring the base through an étale morphism. -/
private lemma etale_pullback_factor_iff {S T U : Scheme.{u}} (a : T ⟶ S)
    (q : U ⟶ S) [Etale q] (W : Over U) :
    Etale (pullback.snd (W.hom ≫ q) a) ↔
      Etale (pullback.snd W.hom (pullback.snd a q)) := by
  let h := (IsPullback.of_hasPullback W.hom (pullback.snd a q)).paste_vert
    (IsPullback.of_hasPullback a q).flip
  constructor
  · intro he
    have : Etale (pullback.snd W.hom (pullback.snd a q) ≫ pullback.fst a q) := by
      rw [← h.isoPullback_hom_snd]
      infer_instance
    exact Etale.of_comp _ (pullback.fst a q)
  · intro he
    rw [← h.isoPullback_inv_snd]
    infer_instance

/-- A chart with affine target satisfies the étaleness descent criterion. -/
private lemma exists_etale_baseChange_chart {J : Type u} [Category.{u} J] [IsCofiltered J]
    (F : J ⥤ Scheme.{u}) (d : Cone F) (hd : IsLimit d)
    [∀ {i j : J} (a : i ⟶ j), IsAffineHom (F.map a)]
    (i : J) {U : Scheme.{u}} [IsAffine U] (q : U ⟶ F.obj i) [Etale q]
    (W : Over U) [IsAffine W.left] [LocallyOfFinitePresentation W.hom]
    [Etale (pullback.snd (W.hom ≫ q) (d.π.app i))] :
    ∃ j : Over i, Etale (pullback.snd (W.hom ≫ q) (F.map j.hom)) := by
  let E : Over i ⥤ Over U := Over.post F ⋙ Over.pullback q
  let e : Cone E := (Over.pullback q).mapCone (overStageCone F d i)
  let F' := E ⋙ Over.forget U
  let d' := (Over.forget U).mapCone e
  obtain ⟨⟨hd'⟩, hF, hF'⟩ := isLimit_pullback_stage_affine F d hd i q
  have := hF
  have {j k : Over i} (a : j ⟶ k) : IsAffineHom (F'.map a) := hF' a
  let i₀ : Over i := Over.mk (𝟙 i)
  let p₀ := (E.obj i₀).hom
  have : IsAffineHom p₀ :=
    show IsAffineHom (pullback.snd (F.map i₀.hom) q) from inferInstance
  let W₀ := (Over.pullback p₀).obj W
  have : IsAffine W₀.left := by
    change IsAffine (pullback W.hom p₀)
    exact isAffine_of_isAffineHom (pullback.fst W.hom p₀)
  have : LocallyOfFinitePresentation W₀.hom := by
    change LocallyOfFinitePresentation (pullback.snd W.hom p₀)
    infer_instance
  have hlim : Etale ((Over.pullback e.pt.hom).obj W).hom :=
    (etale_pullback_factor_iff (d.π.app i) q W).mp inferInstance
  have : Etale ((Over.pullback (d'.π.app i₀)).obj W₀).hom := by
    let : Etale ((Over.pullback (d'.π.app i₀ ≫ p₀)).obj W).hom := by
      have hw : d'.π.app i₀ ≫ p₀ = e.pt.hom := Over.w (e.π.app i₀)
      rw [hw]
      exact hlim
    exact etale_of_overIso ((Over.pullbackComp (d'.π.app i₀) p₀).app W)
  obtain ⟨j, hj⟩ := exists_etale_baseChange F' d' hd' i₀ W₀
  refine ⟨j.left, (etale_pullback_factor_iff (F.map j.left.hom) q W).mpr ?_⟩
  have hw : F'.map j.hom ≫ p₀ = (E.obj j.left).hom := Over.w (E.map j.hom)
  have : Etale ((Over.pullback p₀ ⋙ Over.pullback (F'.map j.hom)).obj W).hom := hj
  have ht := etale_of_overIso ((Over.pullbackComp (F'.map j.hom) p₀).app W).symm
  exact (congrArg (fun t => Etale (pullback.snd W.hom t)) hw).mp ht


/-- Restricting the source to an étale chart preserves étaleness after base change. -/
private lemma etale_baseChange_precomp {S T U V : Scheme.{u}} (a : T ⟶ S)
    (g : U ⟶ S) (h : V ⟶ U) [Etale h] [Etale (pullback.snd g a)] :
    Etale (pullback.snd (h ≫ g) a) := by
  let f : Over.mk (h ≫ g) ⟶ Over.mk g := Over.homMk h rfl
  have : Etale ((Over.pullback a).map f).left :=
    MorphismProperty.of_isPullback (isPullback_pullback_map a f).flip
      (show Etale f.left from ‹Etale h›)
  have hw : ((Over.pullback a).map f).left ≫ pullback.snd g a =
      pullback.snd (h ≫ g) a := Over.w ((Over.pullback a).map f)
  rw [← hw]
  infer_instance

/-- Quasi-compact sources allow étaleness to descend without compactness assumptions on the
base. -/
private lemma exists_etale_baseChange_of_compact_source {J : Type u} [Category.{u} J]
    [IsCofiltered J] (F : J ⥤ Scheme.{u}) (d : Cone F) (hd : IsLimit d)
    [∀ {i j : J} (a : i ⟶ j), IsAffineHom (F.map a)]
    (i : J) (A : Over (F.obj i)) [CompactSpace A.left]
    [LocallyOfFinitePresentation A.hom]
    [Etale ((Over.pullback (d.π.app i)).obj A).hom] :
    ∃ j : Over i, Etale ((Over.pullback (F.map j.hom)).obj A).hom := by
  have hcharts (x : A.left) : ∃ (U : A.left.affineOpens) (V : (F.obj i).affineOpens),
      x ∈ U.1 ∧ U.1 ≤ A.hom ⁻¹ᵁ V.1 := by
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := F.obj i) (x := A.hom.base x) (U := ⊤) trivial
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (X := A.left) (x := x) (U := A.hom ⁻¹ᵁ V) hxV
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxU, hUV⟩
  choose U V hxU hUV using hcharts
  let 𝒰 : A.left.OpenCover := {
    I₀ := A.left
    X := fun x => (U x).1
    f := fun x => (U x).1.ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x => ⟨x, ⟨x, hxU x⟩, rfl⟩, inferInstance⟩ }
  obtain ⟨j, a, ha⟩ := exists_etale_baseChange_of_finite_cover F i A 𝒰.finiteSubcover (by
    intro k
    let l := 𝒰.idx k.val
    let W : Over (V l).1.toScheme := Over.mk (A.hom.resLE (V l).1 (U l).1 (hUV l))
    have : IsAffine (V l).1.toScheme := (V l).2
    have : IsAffine W.left := (U l).2
    have : LocallyOfFinitePresentation W.hom :=
      IsZariskiLocalAtSource.resLE (P := @LocallyOfFinitePresentation)
        (hUV l) (show LocallyOfFinitePresentation A.hom from inferInstance)
    have hw : W.hom ≫ (V l).1.ι = (U l).1.ι ≫ A.hom :=
      Scheme.Hom.resLE_comp_ι A.hom (hUV l)
    have : Etale (pullback.snd A.hom (d.π.app i)) :=
      ‹Etale ((Over.pullback (d.π.app i)).obj A).hom›
    have : Etale (pullback.snd (W.hom ≫ (V l).1.ι) (d.π.app i)) := by
      rw [hw]
      exact etale_baseChange_precomp (d.π.app i) A.hom (U l).1.ι
    obtain ⟨j, hj⟩ := exists_etale_baseChange_chart F d hd i (V l).1.ι W
    refine ⟨j.left, j.hom, ?_⟩
    change Etale (pullback.snd ((U l).1.ι ≫ A.hom) (F.map j.hom))
    rwa [hw] at hj)
  exact ⟨Over.mk a, ha⟩

end Stacks.EtaleCohomology

end
