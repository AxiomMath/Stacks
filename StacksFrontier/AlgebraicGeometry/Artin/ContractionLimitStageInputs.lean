module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageSystemLimit

/-!
# The inputs of the lifting argument along the descended system

This file proves, for the systems `k ↦ A_k^∧` and `k ↦ C_k^∧` of a stage witness
(`AlgebraicGeometry.Artin.LimitStages`), the hypotheses of
`AlgebraicGeometry.Artin.StageLift.exists_stage_continuous_ringHom` which concern only these
systems: the colimit statements `Ker(A → C) = colim Ker(A_k → C_k)` and
`Coker(A → C) = colim Coker(A_k → C_k)` in the form the lifting argument uses them, the
vanishing of elements of `Ker(A_k^∧ → C_k^∧)` dying in `A^∧` at a later stage, and the Artin–Rees
estimate for `A_k^∧ ⟶ A^∧ × C_k^∧` (the "more algebra arguments" of the proof of Stacks 0GI5).

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Artin.LimitStages

open Space FormalSpace FormalDictionary FormalRing ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance]
  AlgebraicGeometry.Artin.FormalDictionary.instTopologicalSpaceAdicCompletion

variable {c : ContractionSituation B S hS} {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ LocallyNoetherianOver B S hS} {κ : Cone D} {ξ : Triple c κ.pt.obj}
  {w : CompatibilityWitness c κ.pt.obj ξ.Z ξ.u ξ.xhat} {k₀ : I}
  (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
  [hD : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj)]

section Generic

/-- An element of a Noetherian ring killed by a power of `J` and vanishing in the `J`-adic
completion is zero (Artin–Rees for the submodule it generates). -/
theorem eq_zero_of_pow_mul_eq_zero_of_algebraMap_eq_zero {R : Type u} [CommRing R]
    [IsNoetherianRing R] (J : Ideal R) {a : R} {N : ℕ} (h : ∀ x ∈ J ^ N, x * a = 0)
    (ha : algebraMap R (AdicCompletion J R) a = 0) : a = 0 := by
  have hmem : ∀ n, a ∈ (J ^ n • ⊤ : Submodule R R) := fun n => by
    have h1 := congrArg (AdicCompletion.eval J R n) ha
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.eval_of, Algebra.algebraMap_self,
      RingHom.id_apply, map_zero] at h1
    exact (Submodule.Quotient.mk_eq_zero _).1 h1
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul J (Submodule.span R {a})
  have h2 : a ∈ (J ^ (N + k) • ⊤ : Submodule R R) ⊓ Submodule.span R {a} :=
    ⟨hmem (N + k), Submodule.mem_span_singleton_self a⟩
  rw [hk (N + k) (Nat.le_add_left k N), Nat.add_sub_cancel] at h2
  have h3 : J ^ N • ((J ^ k • ⊤ : Submodule R R) ⊓ Submodule.span R {a}) ≤ ⊥ := by
    refine Submodule.smul_le.2 fun r hr m hm => ?_
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hm.2
    rw [Submodule.mem_bot, smul_eq_mul, smul_eq_mul, mul_left_comm, h r hr, mul_zero]
  exact (Submodule.mem_bot R).1 (h3 h2)

/-- The completion of a ring map `f` with `J.map f ≤ J'` sends the `m`-th power of the extension
of `J` to `A^∧` into the `m`-th power of the extension of `J'` to `A'^∧`. -/
theorem completionRingHom_mem_map_pow {A A' : Type u} [CommRing A] [CommRing A'] {f : A →+* A'}
    {J : Ideal A} {J' : Ideal A'} (h : J.map f ≤ J') {m : ℕ} {x : AdicCompletion J A}
    (hx : x ∈ (J.map (algebraMap A (AdicCompletion J A))) ^ m) :
    completionRingHom f h x ∈ (J'.map (algebraMap A' (AdicCompletion J' A'))) ^ m := by
  rw [← Ideal.map_pow] at hx ⊢
  have hle : ((J ^ m).map (algebraMap A (AdicCompletion J A))).map (completionRingHom f h) ≤
      (J' ^ m).map (algebraMap A' (AdicCompletion J' A')) := by
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.comp_apply, completionRingHom_algebraMap]
    refine Ideal.mem_map_of_mem _ (Ideal.pow_right_mono h m ?_)
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hb
  exact hle (Ideal.mem_map_of_mem _ hx)

/-- An ideal of `ULift R`. -/
def uliftIdeal {R : Type u} [CommRing R] (J : Ideal R) : Ideal (ULift.{u + 1} R) :=
  J.map (ULift.ringEquiv : ULift.{u + 1} R ≃+* R).symm

/-- An element `x` lies in `uliftIdeal J` if and only if `x.down` lies in `J`. -/
theorem mem_uliftIdeal {R : Type u} [CommRing R] (J : Ideal R) (x : ULift.{u + 1} R) :
    x ∈ uliftIdeal J ↔ x.down ∈ J := by
  rw [uliftIdeal, Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x.down, hx, rfl⟩

/-- `uliftIdeal` commutes with powers. -/
theorem uliftIdeal_pow {R : Type u} [CommRing R] (J : Ideal R) (n : ℕ) :
    uliftIdeal J ^ n = uliftIdeal (J ^ n) :=
  (Ideal.map_pow _ J n).symm

/-- **A common later stage** for finitely many properties stable under passing to later
stages. -/
theorem exists_forall_finset {C : Type*} [Category C] [IsCofiltered C] {k : C} {α : Type*}
    (P : α → ∀ {k' : C}, (k' ⟶ k) → Prop)
    (hP : ∀ (a : α) {k' k'' : C} (f : k' ⟶ k) (h : k'' ⟶ k'), P a f → P a (h ≫ f))
    (G : Finset α) (hG : ∀ a ∈ G, ∃ (k' : C) (f : k' ⟶ k), P a f) :
    ∃ (k' : C) (f : k' ⟶ k), ∀ a ∈ G, P a f := by
  classical
  induction G using Finset.induction_on with
  | empty => exact ⟨k, 𝟙 k, by simp⟩
  | insert b G _ ih =>
    obtain ⟨k₁, f₁, h₁⟩ := ih fun a ha => hG a (Finset.mem_insert_of_mem ha)
    obtain ⟨k₂, f₂, h₂⟩ := hG b (Finset.mem_insert_self b G)
    let m := IsCofiltered.min k₁ k₂
    obtain ⟨m', e, he⟩ := IsCofilteredOrEmpty.cone_maps (IsCofiltered.minToLeft k₁ k₂ ≫ f₁)
      (IsCofiltered.minToRight k₁ k₂ ≫ f₂)
    refine ⟨m', e ≫ IsCofiltered.minToLeft k₁ k₂ ≫ f₁, fun a ha => ?_⟩
    rcases Finset.mem_insert.1 ha with rfl | ha
    · rw [he, ← Category.assoc]
      exact hP _ _ _ h₂
    · rw [← Category.assoc]
      exact hP _ _ _ (h₁ a ha)

/-- Adic completion of ring maps turns a composite `g ∘ f = k` into the composite of the
completions. -/
private theorem completionRingHom_comp_eq {A A' A'' : Type u} [CommRing A] [CommRing A']
    [CommRing A''] {f : A →+* A'} {g : A' →+* A''} {k : A →+* A''} {J : Ideal A} {J' : Ideal A'}
    {J'' : Ideal A''} (e : g.comp f = k) (hf : J.map f ≤ J') (hg : J'.map g ≤ J'')
    (hk : J.map k ≤ J'') :
    (completionRingHom g hg).comp (completionRingHom f hf) = completionRingHom k hk := by
  subst e
  exact completionRingHom_comp f hf g hg hk

end Generic

section Colimit

include hκ in
/-- **`Γ(V, 𝒪) = colim Γ(V_k, 𝒪)`, surjectivity**, over the stages below `k₀`. -/
theorem exists_stage_appTop_eq (a : Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)) :
    ∃ (k : Over k₀) (t : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)),
      ((BigFppfOver.toScheme B S hS).map (limitMap κ k)).appTop.hom t = a := by
  have : ∀ i, IsAffine ((D ⋙ LocallyNoetherianOver.toScheme B S hS).obj i) := hD
  obtain ⟨i, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit
    (D ⋙ LocallyNoetherianOver.toScheme B S hS) _ hκ a
  let j := IsCofiltered.min i k₀
  refine ⟨Over.mk (IsCofiltered.minToRight i k₀),
    ((BigFppfOver.toScheme B S hS).map (D.map (IsCofiltered.minToLeft i k₀)).hom).appTop.hom t, ?_⟩
  rw [← ht, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
    ← Functor.map_comp]
  change ((BigFppfOver.toScheme B S hS).map ((κ.π.app j).hom ≫
    (D.map (IsCofiltered.minToLeft i k₀)).hom)).appTop.hom t = _
  rw [cone_π_hom_comp]
  rfl

include hκ in
/-- **`Γ(V, 𝒪) = colim Γ(V_k, 𝒪)`, injectivity.** -/
theorem exists_stage_appTop_eq_zero {k : Over k₀}
    (t : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))
    (ht : ((BigFppfOver.toScheme B S hS).map (limitMap κ k)).appTop.hom t = 0) :
    ∃ (k' : Over k₀) (f : k' ⟶ k),
      ((BigFppfOver.toScheme B S hS).map (D.map f.left).hom).appTop.hom t = 0 := by
  have : ∀ i, IsAffine ((D ⋙ LocallyNoetherianOver.toScheme B S hS).obj i) := hD
  obtain ⟨j, g, hg⟩ := exists_appTop_map_eq_zero_of_isAffine_of_isLimit
    (D ⋙ LocallyNoetherianOver.toScheme B S hS) _ hκ k.left t ht
  exact ⟨Over.mk (g ≫ k.hom), Over.homMk g, hg⟩

variable (W : StageWitness c κ ξ w k₀)

include hκ in
/-- **`Γ(V', 𝒪) = colim Γ(V'_k, 𝒪)`, injectivity**, along the system `k ↦ V'_k`. -/
theorem exists_stage_restrict_eq_zero {k : Over k₀}
    (s : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B S hS (stageSpace W k).1 (stageSpace W k).2).O)))
    (hs : globalSectionsRingHomSite B S hS
      (ObjectProperty.homMk (stageA W k) : limitSpace w ⟶ stageSpace W k) s = 0) :
    ∃ (k' : Over k₀) (f : k' ⟶ k), globalSectionsRingHomSite B S hS
      (ObjectProperty.homMk (stageHom W f) : stageSpace W k' ⟶ stageSpace W k) s = 0 := by
  obtain ⟨j, g, hg⟩ := (W.baseChange k.hom).toStageModel.exists_restrict_eq_zero hκ
    (fun i => hD i) s hs
  let M := (W.baseChange k.hom).toStageModel
  let f : Over.mk (g ≫ k.hom) ⟶ k := Over.homMk g
  let φ : (stageSpace W (Over.mk (g ≫ k.hom))).1 ⟶ (M.baseChange g).Y :=
    pullback.lift (stageQ W (Over.mk (g ≫ k.hom))) (stageHom W f) (stageHom_q W f).symm
  have hφ : φ ≫ M.baseChangeHom g = stageHom W f := pullback.lift_snd _ _ _
  refine ⟨Over.mk (g ≫ k.hom), f, ?_⟩
  have e : (ObjectProperty.homMk (stageHom W f) : stageSpace W (Over.mk (g ≫ k.hom)) ⟶
      stageSpace W k) = (ObjectProperty.homMk φ : stageSpace W (Over.mk (g ≫ k.hom)) ⟶
        ⟨(M.baseChange g).Y, (M.baseChange g).isAlgebraicSpace_Y⟩) ≫
      (ObjectProperty.homMk (M.baseChangeHom g) :
        (⟨(M.baseChange g).Y, (M.baseChange g).isAlgebraicSpace_Y⟩ : AlgebraicSpaces B S hS) ⟶
          stageSpace W k) :=
    ObjectProperty.hom_ext _ hφ.symm
  rw [e, globalSectionsRingHomSite_comp, RingHom.comp_apply]
  exact (congrArg (globalSectionsRingHomSite B S hS (ObjectProperty.homMk φ :
    stageSpace W (Over.mk (g ≫ k.hom)) ⟶ ⟨(M.baseChange g).Y, (M.baseChange g).isAlgebraicSpace_Y⟩))
      hg).trans (map_zero _)

end Colimit

section Restrictions

variable (I₀ : Ideal Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤))

/-- `A_k ⟶ A_{k'}`. -/
abbrev res (D : I ⥤ LocallyNoetherianOver B S hS) {k k' : Over k₀} (f : k' ⟶ k) :
    Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤) →+*
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤) :=
  ((BigFppfOver.toScheme B S hS).map (D.map f.left).hom).appTop.hom

/-- `A_k ⟶ A`. -/
abbrev resL (κ : Cone D) (k : Over k₀) :
    Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤) →+*
      Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤) :=
  ((BigFppfOver.toScheme B S hS).map (limitMap κ k)).appTop.hom

omit [IsCofiltered I] hD in
/-- The restriction `A_k ⟶ A` factors as `A_k ⟶ A_{k'} ⟶ A`. -/
theorem resL_comp_res {k k' : Over k₀} (f : k' ⟶ k) :
    (resL κ k').comp (res D f) = resL κ k := by
  rw [res, resL, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ← Functor.map_comp]
  change ((BigFppfOver.toScheme B S hS).map
    ((κ.π.app k'.left).hom ≫ (D.map f.left).hom)).appTop.hom = _
  rw [cone_π_hom_comp]

omit [IsCofiltered I] hD in
/-- The restriction `A_k ⟶ A` factors as `A_k ⟶ A_{k'} ⟶ A`, elementwise. -/
theorem resL_res {k k' : Over k₀} (f : k' ⟶ k) (a) : resL κ k' (res D f a) = resL κ k a :=
  congrArg (fun φ => φ a) (resL_comp_res (κ := κ) f)

omit [IsCofiltered I] hD in
/-- The restrictions `A_k ⟶ A_{k'} ⟶ A_{k''}` compose to the restriction along `h ≫ f`. -/
theorem res_comp_res {k k' k'' : Over k₀} (f : k' ⟶ k) (h : k'' ⟶ k') :
    (res D h).comp (res D f) = res D (h ≫ f) :=
  (appTop_map_comp_eq f h).symm

omit [IsCofiltered I] hD in
/-- The restrictions `A_k ⟶ A_{k'} ⟶ A_{k''}` compose to the restriction along `h ≫ f`,
elementwise. -/
theorem res_res {k k' k'' : Over k₀} (f : k' ⟶ k) (h : k'' ⟶ k') (a) :
    res D h (res D f a) = res D (h ≫ f) a :=
  congrArg (fun φ => φ a) (res_comp_res f h)

omit [IsCofiltered I] hD in
/-- The extension of `stageIdeal I₀ k` along `A_k ⟶ A` is `limitIdeal I₀`. -/
theorem stageIdeal_map_resL (k : Over k₀) :
    (stageIdeal I₀ k).map (resL κ k) = limitIdeal (κ := κ) I₀ :=
  stageIdeal_map_limit I₀ k

/-- `A_k^∧ ⟶ A_{k'}^∧`. -/
abbrev cres {k k' : Over k₀} (f : k' ⟶ k) :
    AdicCompletion (stageIdeal I₀ k) Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤) →+*
      AdicCompletion (stageIdeal I₀ k')
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤) :=
  completionRingHom (res D f) (stageIdeal_map_le I₀ f)

/-- `A_k^∧ ⟶ A^∧`. -/
abbrev cresL (κ : Cone D) (k : Over k₀) :
    AdicCompletion (stageIdeal I₀ k) Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤) →+*
      AdicCompletion (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤) :=
  completionRingHom (resL κ k) (stageIdeal_map_limit I₀ k).le

omit [IsCofiltered I] hD in
/-- The map `A_k^∧ ⟶ A^∧` factors as `A_k^∧ ⟶ A_{k'}^∧ ⟶ A^∧`. -/
theorem cresL_comp_cres {k k' : Over k₀} (f : k' ⟶ k) :
    (cresL I₀ κ k').comp (cres I₀ f) = cresL I₀ κ k :=
  completionRingHom_comp_eq (resL_comp_res (κ := κ) f) _ _ _

omit [IsCofiltered I] hD in
/-- The maps `A_k^∧ ⟶ A_{k'}^∧ ⟶ A_{k''}^∧` compose to the map along `h ≫ f`. -/
theorem cres_comp_cres {k k' k'' : Over k₀} (f : k' ⟶ k) (h : k'' ⟶ k') :
    (cres I₀ h).comp (cres I₀ f) = cres I₀ (h ≫ f) :=
  completionRingHom_comp_eq (res_comp_res f h) _ _ _

omit [IsCofiltered I] hD in
/-- The maps `A_k^∧ ⟶ A_{k'}^∧ ⟶ A_{k''}^∧` compose to the map along `h ≫ f`, elementwise. -/
theorem cres_cres {k k' k'' : Over k₀} (f : k' ⟶ k) (h : k'' ⟶ k') (x) :
    cres I₀ h (cres I₀ f x) = cres I₀ (h ≫ f) x :=
  congrArg (fun φ => φ x) (cres_comp_cres I₀ f h)

omit [IsCofiltered I] hD in
/-- The map `A_k^∧ ⟶ A^∧` factors as `A_k^∧ ⟶ A_{k'}^∧ ⟶ A^∧`, elementwise. -/
theorem cresL_cres {k k' : Over k₀} (f : k' ⟶ k) (x) :
    cresL I₀ κ k' (cres I₀ f x) = cresL I₀ κ k x :=
  congrArg (fun φ => φ x) (cresL_comp_cres (κ := κ) I₀ f)

end Restrictions

section Inputs

variable (W : StageWitness c κ ξ w k₀) [hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj κ.pt.obj)]
  {I₀ : Ideal Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤)}
  (hZI₀ : ∀ x, x ∈ W.Z ↔ Space.pointsToScheme B S hS (D.obj k₀).obj x ∈
    ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj).zeroLocus
      (I₀ : Set Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤)))

omit [IsCofiltered I] hD hpt in
/-- The second projection of the pullback of `w.p` along the open subspace complementary to
`ξ.Z` is an isomorphism. -/
theorem isIso_limit_pullback_snd :
    IsIso (pullback.snd w.p (Space.openSubspaceOfPoints B S hS (yoneda.obj κ.pt.obj) ξ.Zᶜ).ι) := by
  have e : w.isPullback_j.flip.isoPullback.hom ≫ pullback.snd w.p
      (Space.openSubspaceOfPoints B S hS (yoneda.obj κ.pt.obj) ξ.Zᶜ).ι = 𝟙 _ :=
    w.isPullback_j.flip.isoPullback_hom_snd
  have e' : pullback.snd w.p (Space.openSubspaceOfPoints B S hS (yoneda.obj κ.pt.obj) ξ.Zᶜ).ι =
      w.isPullback_j.flip.isoPullback.inv := by
    rw [← Iso.inv_hom_id_assoc w.isPullback_j.flip.isoPullback
      (pullback.snd w.p (Space.openSubspaceOfPoints B S hS (yoneda.obj κ.pt.obj) ξ.Zᶜ).ι), e,
      Category.comp_id]
  rw [e']
  infer_instance

include hZI₀ in
omit [IsCofiltered I] hD in
/-- **The kernel and the cokernel of `Γ(V, 𝒪) ⟶ Γ(V', 𝒪)` are killed by a power of `I`.** -/
theorem limit_torsion :
    ∃ N : ℕ, (∀ a, pullbackRingHom B κ.pt.obj (spaceHom κ.pt.obj (limitP w)) a = 0 →
        ∀ x ∈ limitIdeal (κ := κ) I₀ ^ N, x * a = 0) ∧
      ∀ s : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Space.smallEtaleRingedSite B S hS (limitSpace w).1 (limitSpace w).2).O)),
        ∀ x ∈ limitIdeal (κ := κ) I₀ ^ N,
          pullbackRingHom B κ.pt.obj (spaceHom κ.pt.obj (limitP w)) x * s ∈
            (pullbackRingHom B κ.pt.obj (spaceHom κ.pt.obj (limitP w))).range :=
  StageRings.exists_pow_smul_ker_coker κ.pt.obj (f := spaceHom κ.pt.obj (limitP w))
    (limit_hZI hZI₀) (isIso_limit_pullback_snd (w := w)) w.isProper_p

include hZI₀ in
omit [IsCofiltered I] hpt in
/-- **The kernel and the cokernel of `Γ(V_k, 𝒪) ⟶ Γ(V'_k, 𝒪)` are killed by a power of `I_k`.** -/
theorem stage_torsion (k : Over k₀) :
    ∃ N : ℕ, (∀ a, pullbackRingHom B (D.obj k.left).obj (spaceHom _ (stageQ W k)) a = 0 →
        ∀ x ∈ stageIdeal I₀ k ^ N, x * a = 0) ∧
      ∀ s : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Space.smallEtaleRingedSite B S hS (stageSpace W k).1 (stageSpace W k).2).O)),
        ∀ x ∈ stageIdeal I₀ k ^ N,
          pullbackRingHom B (D.obj k.left).obj (spaceHom _ (stageQ W k)) x * s ∈
            (pullbackRingHom B (D.obj k.left).obj (spaceHom _ (stageQ W k))).range :=
  (W.baseChange k.hom).exists_pow_smul_ker_coker (fun i => hD i) (stage_hZI hZI₀ k)

omit [IsCofiltered I] hD in
/-- Every fibre space of `spaceHom κ.pt.obj (limitP w)` along `limitIdeal I₀` is
quasi-compact. -/
theorem limit_hqc (n : ℕ) :
    IsQuasiCompactSpace B S hS (fibreSpace κ.pt.obj (limitIdeal (κ := κ) I₀)
      (spaceHom κ.pt.obj (limitP w)) n).1 :=
  isQuasiCompactSpace_fibreSpace _ _ _ w.isProper_p n


omit [IsCofiltered I] hpt in
/-- Every fibre space of `spaceHom _ (stageQ W k)` along `stageIdeal I₀ k` is quasi-compact. -/
theorem stage_hqc (k : Over k₀) (n : ℕ) :
    IsQuasiCompactSpace B S hS (fibreSpace (D.obj k.left).obj (stageIdeal I₀ k)
      (spaceHom _ (stageQ W k)) n).1 :=
  isQuasiCompactSpace_fibreSpace _ _ _ (isProper_stageQ W k) n

include hκ hZI₀ in
/-- **`Ker(A^∧ → C^∧) = colim Ker(A_k^∧ → C_k^∧)`**: every element of `Ker(A^∧ → C^∧)` is the
image of an element of `Ker(A_k^∧ → C_k^∧)` for some stage `k`. -/
theorem exists_stage_of_limitAlpha_eq_zero
    (y : AdicCompletion (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤))
    (hy : limitAlpha W hZI₀ y = 0) :
    ∃ (k : Over k₀) (z : AdicCompletion (stageIdeal I₀ k)
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)),
      stageAlpha W hZI₀ k z = 0 ∧ cresL I₀ κ k z = y := by
  obtain ⟨N, hK, -⟩ := limit_torsion W hZI₀
  obtain ⟨a, ha, hya⟩ := exists_algebraMap_eq_of_alpha_eq_zero (limitP w) w.isProper_p
    (limit_hZI hZI₀) (limit_hqc (I₀ := I₀) (w := w)) hK hy
  obtain ⟨k, t, ht⟩ := exists_stage_appTop_eq hκ a
  have hs : globalSectionsRingHomSite B S hS
      (ObjectProperty.homMk (stageA W k) : limitSpace w ⟶ stageSpace W k)
        (pullbackRingHom B _ (spaceHom _ (stageQ W k)) t) = 0 :=
    (globalSectionsRingHomSite_pullbackRingHom (stageQ W k) (limitMap κ k) (limitP w)
      (stageA W k) (stageA_q W k) t).trans ((congrArg _ ht).trans ha)
  obtain ⟨k', f, hf⟩ := exists_stage_restrict_eq_zero hκ W
    (pullbackRingHom B _ (spaceHom _ (stageQ W k)) t) hs
  refine ⟨k', algebraMap _ _ (res D f t), ?_, ?_⟩
  · have e₁ := alpha_algebraMap (stageQ W k') (stage_hZI hZI₀ k') (stage_hqc W k') (res D f t)
    have e₂ := (globalSectionsRingHomSite_pullbackRingHom (stageQ W k) (D.map f.left).hom
      (stageQ W k') (stageHom W f) (stageHom_q W f) t).symm
    exact e₁.trans ((congrArg (towerOf (stageIdeal I₀ k') (stageQ W k')) (e₂.trans hf)).trans
      (map_zero _))
  · have e₁ := completionRingHom_algebraMap (resL κ k') (stageIdeal_map_limit I₀ k').le (res D f t)
    exact e₁.trans ((congrArg (algebraMap _ _) ((resL_res f t).trans ht)).trans hya)

omit [IsCofiltered I] hD in
/-- The restriction `A_k ⟶ A_{k''}` along `h ≫ f` is the composite of the restrictions along `f`
and `h`, elementwise. -/
theorem appTop_map_comp_apply {k k' k'' : Over k₀} (f : k' ⟶ k) (h : k'' ⟶ k')
    (a : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)) :
    res D (h ≫ f) a = res D h (res D f a) :=
  (res_res f h a).symm

include hκ hZI₀ in
/-- **An element of `Ker(A_k^∧ → C_k^∧)` dying in `A^∧` dies at a later stage**: there is a
stage `k' ⟶ k` such that every `x` in `Ker(A_k^∧ → C_k^∧)` with image zero in `A^∧` has image
zero in `A_{k'}^∧`. -/
theorem exists_stage_cres_eq_zero (k : Over k₀) :
    ∃ (k' : Over k₀) (g : k' ⟶ k), ∀ x : AdicCompletion (stageIdeal I₀ k)
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤),
      stageAlpha W hZI₀ k x = 0 → cresL I₀ κ k x = 0 → cres I₀ g x = 0 := by
  obtain ⟨N, hK, -⟩ := stage_torsion W hZI₀ k
  let L : Ideal Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤) :=
    RingHom.ker (pullbackRingHom B (D.obj k.left).obj (spaceHom _ (stageQ W k))) ⊓
      RingHom.ker (resL κ k)
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian L : L.FG)
  obtain ⟨k', f, hf⟩ := exists_forall_finset (k := k)
    (fun (a : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)) {k'} (f : k' ⟶ k) =>
      res D f a = 0)
    (fun a _ _ f h hf => (appTop_map_comp_apply f h a).trans ((congrArg (res D h) hf).trans
      (map_zero _))) G
    (fun a ha => exists_stage_appTop_eq_zero hκ a
      (Ideal.mem_inf.1 (hG ▸ Submodule.subset_span ha : a ∈ L)).2)
  refine ⟨k', f, fun x hx hxl => ?_⟩
  obtain ⟨a, ha, hxa⟩ := exists_algebraMap_eq_of_alpha_eq_zero (stageQ W k) (isProper_stageQ W k)
    (stage_hZI hZI₀ k) (stage_hqc W k) hK hx
  have hφa : resL κ k a = 0 := by
    refine eq_zero_of_pow_mul_eq_zero_of_algebraMap_eq_zero (limitIdeal (κ := κ) I₀) (N := N)
      (fun y hy => ?_) ?_
    · rw [← stageIdeal_map_resL I₀ k, ← Ideal.map_pow] at hy
      have hle : (stageIdeal I₀ k ^ N).map (resL κ k) ≤ (⊥ : Ideal _).colon {resL κ k a} := by
        rw [Ideal.map_le_iff_le_comap]
        intro z hz
        rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul, hK a ha z hz,
          map_zero]
        exact Submodule.zero_mem _
      have h2 := Submodule.mem_colon_singleton.1 (hle hy)
      rwa [smul_eq_mul, Submodule.mem_bot] at h2
    · rw [← hxa] at hxl
      exact (completionRingHom_algebraMap (resL κ k) (stageIdeal_map_limit I₀ k).le
        a).symm.trans hxl
  have haL : a ∈ L := Ideal.mem_inf.2 ⟨ha, hφa⟩
  have hspan : L ≤ RingHom.ker (res D f) := by
    rw [← hG, Ideal.span_le]
    intro b hb
    exact hf b hb
  rw [← hxa]
  exact (completionRingHom_algebraMap (res D f) (stageIdeal_map_le I₀ f) a).trans
    ((congrArg (algebraMap _ _) (RingHom.mem_ker.1 (hspan haL))).trans (map_zero _))

end Inputs

end AlgebraicGeometry.Artin.LimitStages

end
