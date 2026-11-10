module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineSourceEtaleDescent

/-!
# Refining a surjective étale map so that it factors through affine pieces of a target

Over an affine object `a` of the big fppf site, a surjective étale `q : c ⟶ a` together with an
arbitrary morphism `k : c ⟶ U` is refined by a surjective étale map from an affine `c'` which
factors, over `k`, through an affine `W` étale over `U`. Both `c'` and `W` are finite
coproducts of affine opens: of `c` contained in the preimage of an affine open of `U`, and of
those affine opens of `U`.

This is the shape in which the lifting step for algebraic spaces consumes an étale atlas `U` of
the space: the pieces of `W` are affine opens of the atlas, so `W` is again étale over the space,
and it is affine, so it is a chart by a single ring.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_affine_surjective_etale_refinement_factor`.
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of the site from an open piece `V` of `c` into an open piece `O` of `U`, lifting
`k : c ⟶ U` when the image of `V` lands in that of `O`. -/
theorem BigFppfOver.exists_restrict_hom {c U V O : BigFppfOver B S hS} (k : c ⟶ U)
    (uc : V ⟶ c) (uU : O ⟶ U) (huU : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map uU))
    (hsub : Set.range ((BigFppfOver.toScheme B S hS).map (uc ≫ k)) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map uU)) :
    ∃ g : V ⟶ O, g ≫ uU = uc ≫ k := by
  let g₀ := IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map uU)
    ((BigFppfOver.toScheme B S hS).map (uc ≫ k)) hsub
  have hg₀ : g₀ ≫ (BigFppfOver.toScheme B S hS).map uU =
      (BigFppfOver.toScheme B S hS).map (uc ≫ k) := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk (B.inclusion.preimage (X := V.left) (Y := O.left) g₀) ?_, ?_⟩
  · apply B.inclusion.map_injective
    rw [Functor.map_comp, B.inclusion.map_preimage]
    have hw : ∀ {X : BigFppfOver B S hS} (f : X ⟶ U), B.inclusion.map X.hom =
        (BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map U.hom := fun f => by
      rw [← Over.w f, Functor.map_comp]
      rfl
    rw [hw uU, hw (uc ≫ k), ← Category.assoc, hg₀]
  · apply Functor.map_injective (F := BigFppfOver.toScheme B S hS)
    rw [Functor.map_comp]
    change B.inclusion.map (B.inclusion.preimage _) ≫ (BigFppfOver.toScheme B S hS).map uU = _
    rw [B.inclusion.map_preimage]
    exact hg₀

/-- A property of morphisms of schemes that respects isomorphisms holds for the image of `f`
out of a coproduct `T` of pieces `T' j` as soon as it holds for the induced map on the coproduct
of the images of the restrictions `p j` of `f`. -/
private theorem BigFppfOver.map_of_sigmaDesc {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {σ : Type u} {T' : σ → BigFppfOver B S hS} {T M : BigFppfOver B S hS} (c : ∀ j, T' j ⟶ T)
    (e : (∐ fun j ↦ (BigFppfOver.toScheme B S hS).obj (T' j)) ≅
      (BigFppfOver.toScheme B S hS).obj T)
    (he : ∀ j, Sigma.ι (fun j ↦ (BigFppfOver.toScheme B S hS).obj (T' j)) j ≫ e.hom =
      (BigFppfOver.toScheme B S hS).map (c j))
    (f : T ⟶ M) (p : ∀ j, T' j ⟶ M) (hp : ∀ j, c j ≫ f = p j)
    (h : P (Sigma.desc fun j ↦ (BigFppfOver.toScheme B S hS).map (p j))) :
    P ((BigFppfOver.toScheme B S hS).map f) := by
  have key : e.hom ≫ (BigFppfOver.toScheme B S hS).map f =
      Sigma.desc fun j ↦ (BigFppfOver.toScheme B S hS).map (p j) := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [← Category.assoc, he j, Sigma.ι_comp_desc, ← Functor.map_comp, hp j]
  rw [← key] at h
  exact (MorphismProperty.cancel_left_of_respectsIso P e.hom _).mp h

/-- **A surjective étale refinement factoring through affine pieces.** Over an affine base `a`,
a surjective étale `q : c ⟶ a` and a morphism `k : c ⟶ U` admit an affine `c'` with `r : c' ⟶ c`
such that `r ≫ q` is surjective and étale, and an affine `W` étale over `U` by `s` through which
`r ≫ k` factors. -/
theorem BigFppfOver.exists_affine_surjective_etale_refinement_factor
    {a c U : BigFppfOver B S hS} (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (q : c ⟶ a) (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q)) (k : c ⟶ U) :
    ∃ (c' W : BigFppfOver B S hS) (r : c' ⟶ c) (s : W ⟶ U) (m : c' ⟶ W),
      IsAffine ((BigFppfOver.toScheme B S hS).obj c') ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map (r ≫ q)) ∧
      Etale ((BigFppfOver.toScheme B S hS).map (r ≫ q)) ∧
      Etale ((BigFppfOver.toScheme B S hS).map s) ∧ m ≫ s = r ≫ k := by
  classical
  have _ := ha
  have _ := hqe
  set Q := (BigFppfOver.toScheme B S hS).map q
  set K := (BigFppfOver.toScheme B S hS).map k
  choose Vc uc huc hucrange hVcaff using fun V =>
    BigFppfOver.exists_affineOpen_restrict B S hS c V
  choose VU uU huU huUrange hVUaff using fun O =>
    BigFppfOver.exists_affineOpen_restrict B S hS U O
  -- the good pairs: an affine open of `c` inside the preimage of an affine open of `U`
  let J := {p : ((BigFppfOver.toScheme B S hS).obj c).affineOpens ×
      ((BigFppfOver.toScheme B S hS).obj U).affineOpens //
    (p.1.1 : Set ((BigFppfOver.toScheme B S hS).obj c)) ⊆ K.base ⁻¹' (p.2.1 : Set _)}
  have hrest : ∀ j : J, ∃ g : Vc j.1.1 ⟶ VU j.1.2, g ≫ uU j.1.2 = uc j.1.1 ≫ k := by
    intro j
    refine BigFppfOver.exists_restrict_hom k (uc j.1.1) (uU j.1.2) (huU j.1.2) ?_
    rintro _ ⟨z, rfl⟩
    rw [huUrange j.1.2, Functor.map_comp, Scheme.Hom.comp_apply]
    exact j.2 (hucrange j.1.1 ▸ ⟨z, rfl⟩)
  choose g hg using hrest
  have hopen : ∀ j : J,
      IsOpen (Q.base '' (j.1.1.1 : Set ((BigFppfOver.toScheme B S hS).obj c))) :=
    fun j => Q.isOpenMap _ j.1.1.1.2
  have hsub : (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj a)) ⊆
      ⋃ j : J, Q.base '' (j.1.1.1 : Set ((BigFppfOver.toScheme B S hS).obj c)) := by
    intro x _
    obtain ⟨y, hy⟩ := Surjective.surj (f := Q) x
    have hy' : K.base y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hy'
    obtain ⟨O, hO⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
    obtain ⟨V, hV, hyV, hVsub⟩ := exists_isAffineOpen_mem_and_subset (U := K ⁻¹ᵁ O.1) hO
    exact Set.mem_iUnion.2 ⟨⟨(⟨V, hV⟩, O), hVsub⟩, ⟨y, hyV, hy⟩⟩
  obtain ⟨t, ht⟩ := (CompactSpace.isCompact_univ
    (X := ((BigFppfOver.toScheme B S hS).obj a))).elim_finite_subcover _ hopen hsub
  have _ : ∀ j : {j // j ∈ t}, IsAffine ((BigFppfOver.toScheme B S hS).obj (Vc j.1.1.1)) :=
    fun j => hVcaff j.1.1.1
  have _ : ∀ j : {j // j ∈ t}, IsAffine ((BigFppfOver.toScheme B S hS).obj (VU j.1.1.2)) :=
    fun j => hVUaff j.1.1.2
  have _ : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  obtain ⟨c', inj, e, he, hdesc⟩ :=
    BigFppfOver.exists_coproduct_of_mk_le_aleph0 (σ := {j // j ∈ t})
      (Cardinal.mk_le_aleph0) (fun j => Vc j.1.1.1)
  obtain ⟨W, injW, eW, heW, hdescW⟩ :=
    BigFppfOver.exists_coproduct_of_mk_le_aleph0 (σ := {j // j ∈ t})
      (Cardinal.mk_le_aleph0) (fun j => VU j.1.1.2)
  obtain ⟨r, hr⟩ := hdesc (fun j => uc j.1.1.1)
  obtain ⟨s, hs⟩ := hdescW (fun j => uU j.1.1.2)
  obtain ⟨m, hm⟩ := hdesc (fun j => g j.1 ≫ injW j)
  -- maps out of `c'` and `W` are determined on the pieces
  have hext : ∀ {M : BigFppfOver B S hS} (d₁ d₂ : c' ⟶ M), (∀ j, inj j ≫ d₁ = inj j ≫ d₂) →
      d₁ = d₂ := by
    intro M d₁ d₂ h
    apply BigFppfOver.map_toScheme_injective B S hS
    dsimp only
    rw [← cancel_epi e.hom]
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [← Category.assoc, ← Category.assoc, he j, ← Functor.map_comp, ← Functor.map_comp, h j]
  refine ⟨c', W, r, s, m, IsAffine.of_isIso e.inv, IsAffine.of_isIso eW.inv, ?_, ?_, ?_, ?_⟩
  · refine BigFppfOver.map_of_sigmaDesc (P := @Surjective.{u}) inj e he (r ≫ q)
      (fun j => uc j.1.1.1 ≫ q) (fun j => by rw [← Category.assoc, hr j]) ?_
    simp only [Functor.map_comp]
    refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_univ_subset ?_)
    refine ht.trans (Set.iUnion₂_subset fun j hj => ?_)
    refine Set.subset_iUnion_of_subset ⟨j, hj⟩ ?_
    rintro _ ⟨y, hyU, rfl⟩
    obtain ⟨z, hz⟩ : y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (uc j.1.1)) := by
      rwa [hucrange j.1.1]
    exact ⟨z, by rw [Scheme.Hom.comp_apply, hz]⟩
  · refine BigFppfOver.map_of_sigmaDesc (P := @Etale.{u}) inj e he (r ≫ q)
      (fun j => uc j.1.1.1 ≫ q) (fun j => by rw [← Category.assoc, hr j]) ?_
    refine IsZariskiLocalAtSource.sigmaDesc fun j => ?_
    have _ := huc j.1.1.1
    rw [Functor.map_comp]
    infer_instance
  · refine BigFppfOver.map_of_sigmaDesc (P := @Etale.{u}) injW eW heW s
      (fun j => uU j.1.1.2) hs ?_
    refine IsZariskiLocalAtSource.sigmaDesc fun j => ?_
    have _ := huU j.1.1.2
    infer_instance
  · refine hext _ _ fun j => ?_
    rw [← Category.assoc, hm j, Category.assoc, hs j, ← Category.assoc, hr j, hg j.1]

end AlgebraicGeometry

end
