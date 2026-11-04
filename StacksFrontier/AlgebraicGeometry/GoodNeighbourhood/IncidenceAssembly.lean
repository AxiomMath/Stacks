module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.IncidenceGraph
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.ReducedEtaleSupport
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.PointwiseAssembly
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.ProjectiveDivisorReduction
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineSpaceBundleSmooth
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Elementary fibrations from good sections: the incidence construction

This file proves `AlgebraicGeometry.GoodNeighbourhood.IncidenceFromGoodSections k` for `k`
algebraically closed (SGA 4, Exposé XI, Proposition 3.3, the construction): given good sections
`v₁, …, v_{d-1}, w₀` of an invertible module on the integral projective `X̄` through the closed
point `x` of the smooth open `W`, some open neighbourhood of `x` in `W` is an elementary fibration.
It is cut out of the incidence family `X̃ = V(vⱼ - tⱼ w₀) ⊆ X̄ × 𝔸^{d-1}_k` with its projection
`π` to `T = 𝔸^{d-1}_k`.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.etaleAt_of_mem_smoothLocus_of_fiberDimensionAt_eq_zero`:
  a morphism smooth at a point, with fibre of dimension `0` there, is étale there.
* `AlgebraicGeometry.GoodNeighbourhood.incidenceFromGoodSections`:
  `AlgebraicGeometry.GoodNeighbourhood.IncidenceFromGoodSections k` for `k` algebraically closed.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

attribute [local instance] Stacks.ChernCap42.isInvertible_sheafObj_modulePullback

/-- **Smooth with fibre of dimension `0` is étale.** -/
theorem etaleAt_of_mem_smoothLocus_of_fiberDimensionAt_eq_zero {Y S : Scheme.{u}} (f : Y ⟶ S)
    [LocallyOfFinitePresentation f] (y : Y) (h₁ : y ∈ f.smoothLocus)
    (h₂ : topologicalKrullDimAt (f.fiber (f y)) (f.asFiber y) = ((0 : ℕ) : WithBot ℕ∞)) :
    EtaleAt f y := by
  let G₀ : Y.Opens := ⟨{x | x ∈ f.smoothLocus ∧
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = ((0 : ℕ) : WithBot ℕ∞)},
    isOpen_setOf_mem_smoothLocus_fiberDimensionAt_eq f 0⟩
  have : Smooth (G₀.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact eq_top_iff.2 fun x _ => x.2.1
  have : SmoothOfRelativeDimension 0 (G₀.ι ≫ f) :=
    Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq _ 0 fun x => by
      rw [fiberDimensionAt_comp_openImmersion]
      exact x.2.2
  have : Etale (G₀.ι ≫ f) := (Etale.iff_smoothOfRelativeDimension_zero _).2 inferInstance
  exact Stacks.FundamentalGroup.ExtendedEtaleFold.etaleAt_of_etaleAt_isOpenImmersion_comp G₀.ι f
    ⟨y, h₁, h₂⟩ ((etale_iff_forall_etaleAt _).1 inferInstance _)

/-- Every point of `P` over `s` comes from the fibre, for any presentation of the fibre by a
cartesian square. -/
theorem exists_eq_of_isPullback_fromSpecResidueField {F P S : Scheme.{u}} {s : S}
    {ι : F ⟶ P} {q : F ⟶ Spec (S.residueField s)} {f : P ⟶ S}
    (hF : IsPullback ι q f (S.fromSpecResidueField s)) (z : P) (hz : f z = s) :
    ∃ x : F, ι x = z := by
  obtain ⟨t⟩ : Nonempty (Spec (S.residueField s)) := inferInstance
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback z t
    (by rw [hz, Scheme.fromSpecResidueField_apply])
  refine ⟨hF.isoPullback.inv w, ?_⟩
  rw [← Scheme.Hom.comp_apply, hF.isoPullback_inv_fst, hw]

/-- A section of an invertible module pulls back to `0` on a reduced scheme mapping into its
zero locus. -/
theorem pullbackGlobalSections_eq_zero_of_range_subset {Y X : Scheme.{u}} [IsReduced Y]
    (g : Y ⟶ X) (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (σ : Γ(L, ⊤)) (h : Set.range g.base ⊆ ((zeroScheme X L σ).support : Set X)) :
    pullbackGlobalSections g L σ = 0 := by
  obtain ⟨m, hm⟩ :=
    (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support _ g).2 h
  refine (Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker _ _ _).2 ?_
  calc zeroScheme X L σ = (zeroScheme X L σ).subschemeι.ker :=
        (Scheme.IdealSheafData.ker_subschemeι _).symm
    _ ≤ (m ≫ (zeroScheme X L σ).subschemeι).ker := Scheme.Hom.le_ker_comp _ _
    _ = g.ker := by rw [hm]

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- The fibre over the origin as a cartesian square over `Spec κ(0)`. -/
theorem isPullback_originSection_fromSpecResidueField (c : ℕ)
    {s : 𝔸(ULift.{u} (Fin c); Spec (.of k))}
    (α : Spec (.of k) ≅ Spec ((𝔸(ULift.{u} (Fin c); Spec (.of k))).residueField s))
    (hα : α.hom ≫ (𝔸(ULift.{u} (Fin c); Spec (.of k))).fromSpecResidueField s = origin c) :
    IsPullback (originSection p c) (p ≫ α.hom)
      (pullback.snd p (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k)))
      ((𝔸(ULift.{u} (Fin c); Spec (.of k))).fromSpecResidueField s) :=
  (isPullback_originSection p c).of_iso (Iso.refl _) (Iso.refl _) α (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp [hα])

variable (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [LocallyOfFiniteType p]

/-- **The tower for the incidence family.** Let `I₀` be a closed subscheme of `X ×_k 𝔸^c_k`
restricting to `Y₀` on the fibre over the origin and flat near `(x', 0)`. If every
`Y₀ ∩ V(v₁, …, v_m)` is smooth of relative dimension `n - m` at `x'`, then
`I₀ ∩ V(G₁, …, G_c)` is flat over `𝔸^c_k` near `(x', 0)`. -/
theorem exists_flat_sup_incidence {c : ℕ} (v : Fin c → Γ(L, ⊤)) (w₀ : Γ(L, ⊤))
    {s : 𝔸(ULift.{u} (Fin c); Spec (.of k))}
    (α : Spec (.of k) ≅ Spec ((𝔸(ULift.{u} (Fin c); Spec (.of k))).residueField s))
    (hα : α.hom ≫ (𝔸(ULift.{u} (Fin c); Spec (.of k))).fromSpecResidueField s = origin c)
    (I₀ : (pullback p (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k))).IdealSheafData)
    (Y₀ : X.IdealSheafData) (hI₀ : I₀.comap (originSection p c) = Y₀) (x' : X) (n : ℕ)
    (hcn : c ≤ n)
    (h₀ : ∃ (Q : Scheme.{u}) (o : Q ⟶ I₀.subscheme), IsOpenImmersion o ∧
      originSection p c x' ∈ Set.range (o ≫ I₀.subschemeι).base ∧
      Flat (o ≫ I₀.subschemeι ≫ pullback.snd _ _))
    (hfib : ∀ m ≤ c, SubschemeSmoothAt p (Y₀ ⊔ partialIdeal L v m) (n - m) x') :
    ∃ (Q : Scheme.{u})
      (o : Q ⟶ (I₀ ⊔ partialIdeal _ (incidenceSection p L v w₀) c).subscheme),
      IsOpenImmersion o ∧ originSection p c x' ∈
        Set.range (o ≫ (I₀ ⊔ partialIdeal _ (incidenceSection p L v w₀) c).subschemeι).base ∧
      Flat (o ≫ (I₀ ⊔ partialIdeal _ (incidenceSection p L v w₀) c).subschemeι ≫
        pullback.snd _ _) := by
  have : IsLocallyNoetherian (pullback p (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k)) ≫ p)
  refine exists_flat_sup_partialIdeal_of_isPullback _ _ I₀ (incidenceSection p L v w₀) s
    (originSection p c) (p ≫ α.hom) (isPullback_originSection_fromSpecResidueField p c α hα)
    x' n hcn h₀ (fun m hm => ?_) c le_rfl
  rw [(Scheme.IdealSheafData.map_gc _).l_sup, hI₀,
    comap_partialIdeal_incidenceSection_originSection]
  exact (hfib m hm).comp_isIso _ _

/-- **Elementary fibrations from good sections** (SGA 4, Exposé XI, Proposition 3.3, the
construction): `AlgebraicGeometry.GoodNeighbourhood.IncidenceFromGoodSections k` holds for `k`
algebraically closed. -/
theorem incidenceFromGoodSections (k : Type u) [Field k] [IsAlgClosed k] :
    IncidenceFromGoodSections k := by
  intro X p d hp hX W hW hd x hxW hx L _ v w₀ hgood
  obtain ⟨hxC, hxw, h2, h3, h4, h5⟩ := hgood
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  let T := 𝔸(ULift.{u} (Fin (d - 1)); Spec (.of k))
  let τ : T ⟶ Spec (.of k) := T ↘ Spec (.of k)
  have : SmoothOfRelativeDimension (d - 1) τ :=
    Stacks.Chow.smoothOfRelativeDimension_affineSpaceOver _ _
  have : Smooth τ := SmoothOfRelativeDimension.smooth (d - 1) τ
  have : IsNormal T := isNormal_of_smooth_over_field τ
  let pr₁ := pullback.fst p τ
  let pr₂ := pullback.snd p τ
  have : IsLocallyNoetherian (pullback p τ) := LocallyOfFiniteType.isLocallyNoetherian (pr₁ ≫ p)
  let I := partialIdeal _ (incidenceSection p L v w₀) (d - 1)
  let π : I.subscheme ⟶ T := I.subschemeι ≫ pr₂
  have hπ : IsProjectiveMorphism π :=
    Stacks.SectionsVanishingOnSubscheme.isProjectiveMorphism_comp_of_isClosedImmersion _
      (hp.baseChange τ)
  obtain ⟨s, α, hα⟩ := exists_iso_fromSpecResidueField_of_comp_eq_id k τ (origin (d - 1))
    (AffineSpace.homOfVector_over _ _)
  have hF := isPullback_originSection_fromSpecResidueField p (d - 1) α hα
  let ι := originSection p (d - 1)
  have hιs : ∀ x' : X, pr₂ (ι x') = s := fun x' => by
    have e : ι ≫ pr₂ = p ≫ α.hom ≫ T.fromSpecResidueField s := by
      rw [hα]; exact originSection_snd p (d - 1)
    rw [← Scheme.Hom.comp_apply, e]
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have hιfst : ∀ x' : X, pr₁ (ι x') = x' := fun x' => by
    rw [← Scheme.Hom.comp_apply, originSection_fst]; rfl
  have hCι : ∀ x' : X, ι x' ∈ (I.support : Set _) ↔
      x' ∈ ((partialIdeal L v (d - 1)).support : Set X) := fun x' => by
    rw [← comap_partialIdeal_incidenceSection_originSection p L v w₀ (d - 1),
      Scheme.IdealSheafData.support_comap]
    rfl
  have hmemI : ∀ (y : I.subscheme) (x' : X), ι x' = I.subschemeι y →
      x' ∈ ((partialIdeal L v (d - 1)).support : Set X) := fun y x' h => by
    rw [← hCι, h, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  have hflatI : ∀ x' ∈ ((partialIdeal L v (d - 1)).support : Set X),
      ∃ (Q : Scheme.{u}) (o : Q ⟶ I.subscheme), IsOpenImmersion o ∧
        ι x' ∈ Set.range (o ≫ I.subschemeι).base ∧ Flat (o ≫ I.subschemeι ≫ pr₂) := by
    intro x' hx'
    have key : ∀ J : (pullback p τ).IdealSheafData, J = ⊥ ⊔ I →
        ∃ (Q : Scheme.{u}) (o : Q ⟶ J.subscheme), IsOpenImmersion o ∧
          ι x' ∈ Set.range (o ≫ J.subschemeι).base ∧ Flat (o ≫ J.subschemeι ≫ pr₂) := by
      intro J hJ
      subst hJ
      refine exists_flat_sup_incidence p L v w₀ α hα ⊥ ⊥
        (Scheme.IdealSheafData.map_gc _).l_bot x' d (by omega) ?_ ?_
      · have : IsIso (⊥ : (pullback p τ).IdealSheafData).subschemeι :=
          (Scheme.isIso_subschemeι_iff_eq_bot _).2 rfl
        refine ⟨(⊥ : (pullback p τ).IdealSheafData).subscheme, 𝟙 _, inferInstance, ?_, ?_⟩
        · rw [Category.id_comp, Scheme.IdealSheafData.range_subschemeι,
            Scheme.IdealSheafData.support_bot]
          trivial
        · rw [Category.id_comp]
          infer_instance
      · intro m hm
        rw [bot_sup_eq]
        exact h2 x' hx' m hm
    exact key I (bot_sup_eq _).symm
  have hIsm : ∀ x' ∈ ((partialIdeal L v (d - 1)).support : Set X),
      SubschemeSmoothAt (p ≫ α.hom) (I.comap ι) 1 x' := fun x' hx'C => by
    have h1 : d - (d - 1) = 1 := by omega
    rw [comap_partialIdeal_incidenceSection_originSection]
    simpa only [h1] using (h2 x' hx'C (d - 1) le_rfl).comp_isIso _ _
  have hsm : ∀ y : I.subscheme, π y = s → y ∈ π.smoothLocus ∧
      topologicalKrullDimAt (π.fiber (π y)) (π.asFiber y) = ((1 : ℕ) : WithBot ℕ∞) := by
    intro y hy
    obtain ⟨x', hx'⟩ := exists_eq_of_isPullback_fromSpecResidueField hF (I.subschemeι y) hy
    have hx'C := hmemI y x' hx'
    obtain ⟨Q, o, ho, hyo, hfl⟩ := hflatI x' hx'C
    have := ho
    have := hfl
    obtain ⟨z, hz, hzs, hzd⟩ :=
      exists_mem_smoothLocus_of_isPullback pr₂ I s ι (p ≫ α.hom) hF x' _ o hyo (hIsm x' hx'C)
    have hzy : z = y := I.subschemeι.isClosedEmbedding.injective (hz.trans hx')
    subst hzy
    exact ⟨hzs, hzd⟩
  let N : X.Opens := ⟨((zeroScheme X L w₀).support : Set X)ᶜ,
    (zeroScheme X L w₀).support.isClosed.isOpen_compl⟩
  let V : X.Opens := W ⊓ N
  have hxV : x ∈ V := ⟨hxW, hxw⟩
  obtain ⟨j, hjo, hj1, hjr⟩ := exists_isOpenImmersion_incidence p L v w₀ V (fun y hy => hy.2)
  have := hjo
  have hnotj : ∀ y : I.subscheme, y ∉ Set.range j.base ↔ pr₁ (I.subschemeι y) ∉ (V : Set X) := by
    intro y
    rw [hjr]
    rfl
  let A : TopologicalSpace.Closeds I.subscheme :=
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let Zi := Scheme.IdealSheafData.vanishingIdeal A
  let i := Zi.subschemeι
  have hZ : Set.range i.base = (Set.range j.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hrange : ∀ q, q ∈ Set.range (i ≫ I.subschemeι).base ↔
      q ∈ (I.support : Set _) ∧ pr₁ q ∉ (V : Set X) := by
    intro q
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨i z, rfl⟩, ?_⟩
      have h : i z ∈ Set.range i.base := ⟨z, rfl⟩
      rw [hZ] at h
      exact (hnotj _).1 h
    · rintro ⟨hq, hqV⟩
      rw [← Scheme.IdealSheafData.range_subschemeι] at hq
      obtain ⟨y, rfl⟩ := hq
      have h : y ∈ Set.range i.base := by rw [hZ]; exact (hnotj y).2 hqV
      obtain ⟨z, rfl⟩ := h
      exact ⟨z, rfl⟩
  have het : ∀ z : Zi.subscheme, π (i z) = s → EtaleAt (i ≫ π) z := by
    intro z hz
    obtain ⟨x', hx'⟩ := exists_eq_of_isPullback_fromSpecResidueField hF (I.subschemeι (i z)) hz
    have hx'C := hmemI (i z) x' hx'
    have hx'V : x' ∉ (V : Set X) := by
      have h := ((hrange (ι x')).1 (by rw [hx']; exact ⟨z, rfl⟩)).2
      rwa [hιfst] at h
    show EtaleAt (i ≫ I.subschemeι ≫ pr₂) z
    rw [← Category.assoc]
    by_cases hxw' : x' ∈ ((zeroScheme X L w₀).support : Set X)
    · obtain ⟨hxW', hsm0⟩ := h4 x' hx'C hxw'
      obtain ⟨Q, o, ho, hyo, hfl⟩ := hflatI x' hx'C
      have := ho
      have := hfl
      have h₂ : SubschemeSmoothAt (p ≫ α.hom)
          ((I ⊔ zeroScheme _ _ (pullbackGlobalSections pr₁ L w₀)).comap ι) 0 x' := by
        rw [(Scheme.IdealSheafData.map_gc _).l_sup,
          comap_partialIdeal_incidenceSection_originSection,
          comap_zeroScheme_pullback_fst_originSection]
        exact hsm0.comp_isIso _ _
      obtain ⟨Q', o', ho', hyo', hfl'⟩ := exists_flat_sup_zeroScheme_of_isPullback pr₂ _ I
        (pullbackGlobalSections pr₁ L w₀) s 0 ι (p ≫ α.hom) hF x' o hyo (hIsm x' hx'C) h₂
      have := ho'
      have := hfl'
      obtain ⟨z', hz', hz's, hz'd⟩ :=
        exists_mem_smoothLocus_of_isPullback pr₂ _ s ι (p ≫ α.hom) hF x' 0 o' hyo' h₂
      have hsupp : ∀ q, q ∈ ((zeroScheme _ _ (pullbackGlobalSections pr₁ L w₀)).support : Set _) ↔
          pr₁ q ∈ ((zeroScheme X L w₀).support : Set X) := by
        intro q
        have hzp : zeroScheme _ _ (pullbackGlobalSections pr₁ L w₀) =
            (zeroScheme X L w₀).comap pr₁ := Stacks.Divisors.zeroScheme_pullback _ _ _
        rw [hzp, Scheme.IdealSheafData.support_comap]
        rfl
      refine etaleAt_of_inter_eq_support pr₂ (i ≫ I.subschemeι) _ (pr₁ ⁻¹ᵁ W) ?_ z ?_ z'
        (hz'.trans hx') (etaleAt_of_mem_smoothLocus_of_fiberDimensionAt_eq_zero _ z' hz's hz'd)
      · ext q
        simp only [Set.mem_inter_iff, hrange, Scheme.IdealSheafData.support_sup,
          TopologicalSpace.Closeds.coe_inf, hsupp]
        constructor
        · rintro ⟨⟨hq, hqV⟩, hqW⟩
          refine ⟨⟨hq, ?_⟩, hqW⟩
          by_contra hc
          exact hqV ⟨hqW, hc⟩
        · rintro ⟨⟨hq, hqs⟩, hqW⟩
          exact ⟨⟨hq, fun hV => hV.2 hqs⟩, hqW⟩
      · show pr₁ (I.subschemeι (i z)) ∈ W
        rw [← hx', hιfst]
        exact hxW'
    · have hx'W : x' ∉ (W : Set X) := fun h => hx'V ⟨h, hxw'⟩
      have h3' := h3 x' hx'C hx'W
      let Yv := Scheme.IdealSheafData.vanishingIdeal
        (⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩ : TopologicalSpace.Closeds X)
      let I₀ := Yv.comap pr₁
      have hI₀ : I₀.comap ι = Yv := by
        rw [← Scheme.IdealSheafData.comap_comp, originSection_fst, Scheme.IdealSheafData.comap_id]
      have hYsupp : ∀ q, q ∈ (I₀.support : Set _) ↔ pr₁ q ∉ (W : Set X) := by
        intro q
        rw [Scheme.IdealSheafData.support_comap]
        show pr₁ q ∈ (Yv.support : Set X) ↔ _
        rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
        rfl
      have h₀ : ∃ (Q : Scheme.{u}) (o : Q ⟶ I₀.subscheme), IsOpenImmersion o ∧
          ι x' ∈ Set.range (o ≫ I₀.subschemeι).base ∧ Flat (o ≫ I₀.subschemeι ≫ pr₂) := by
        refine ⟨I₀.subscheme, 𝟙 _, inferInstance, ?_, ?_⟩
        · rw [Category.id_comp, Scheme.IdealSheafData.range_subschemeι, hYsupp, hιfst]
          exact hx'W
        · rw [Category.id_comp]
          have hsq : IsPullback ((Yv.comapIso pr₁).hom ≫ pullback.snd _ _) (I₀.subschemeι ≫ pr₂)
              (Yv.subschemeι ≫ p) τ :=
            (isPullback_comap_subschemeι Yv pr₁).flip.paste_vert (IsPullback.of_hasPullback p τ)
          exact MorphismProperty.of_isPullback (P := @Flat) hsq inferInstance
      obtain ⟨Q, o, ho, hyo, hfl⟩ :=
        exists_flat_sup_incidence p L v w₀ α hα I₀ Yv hI₀ x' (d - 1) le_rfl h₀ h3'
      have := ho
      have := hfl
      have hfib0 : SubschemeSmoothAt (p ≫ α.hom) ((I₀ ⊔ I).comap ι) (d - 1 - (d - 1)) x' := by
        rw [(Scheme.IdealSheafData.map_gc _).l_sup, hI₀,
          comap_partialIdeal_incidenceSection_originSection]
        exact (h3' (d - 1) le_rfl).comp_isIso _ _
      obtain ⟨z', hz', hz's, hz'd⟩ :=
        exists_mem_smoothLocus_of_isPullback pr₂ (I₀ ⊔ I) s ι (p ≫ α.hom) hF x' _ o hyo hfib0
      rw [Nat.sub_self] at hz'd
      refine etaleAt_of_inter_eq_support pr₂ (i ≫ I.subschemeι) (I₀ ⊔ I) (pr₁ ⁻¹ᵁ N) ?_ z ?_ z'
        (hz'.trans hx') (etaleAt_of_mem_smoothLocus_of_fiberDimensionAt_eq_zero _ z' hz's hz'd)
      · ext q
        simp only [Set.mem_inter_iff, hrange, Scheme.IdealSheafData.support_sup,
          TopologicalSpace.Closeds.coe_inf, hYsupp]
        constructor
        · rintro ⟨⟨hq, hqV⟩, hqN⟩
          exact ⟨⟨fun hW' => hqV ⟨hW', hqN⟩, hq⟩, hqN⟩
        · rintro ⟨⟨hqW, hq⟩, hqN⟩
          exact ⟨⟨hq, fun hV => hqW hV.1⟩, hqN⟩
      · show pr₁ (I.subschemeι (i z)) ∈ N
        rw [← hx', hιfst]
        exact hxw'
  obtain ⟨e₁, he₁C, he₁w⟩ := h5
  have hne : ∃ z : Zi.subscheme, π (i z) = s := by
    obtain ⟨z, hz⟩ := (hrange (ι e₁)).2 ⟨(hCι e₁).2 he₁C, by
      rw [hιfst]; exact fun h => h.2 he₁w⟩
    refine ⟨z, ?_⟩
    show pr₂ ((i ≫ I.subschemeι) z) = s
    rw [hz]
    exact hιs e₁
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨e, ⟨heC, hew⟩, hecl⟩ := IsClosed.exists_closed_singleton
    ((partialIdeal L v (d - 1)).support.isClosed.inter (zeroScheme X L w₀).support.isClosed)
    ⟨e₁, he₁C, he₁w⟩
  let σ₀ : Spec (.of k) ⟶ X := pointOfClosedPoint p e hecl
  have hσ₀ : σ₀ ≫ p = 𝟙 _ := pointOfClosedPoint_comp p e hecl
  have hσ₀r : Set.range σ₀.base ⊆ {e} := by
    rintro _ ⟨a, rfl⟩
    exact pointOfClosedPoint_apply p e hecl a
  let σ : T ⟶ pullback p τ := pullback.lift (τ ≫ σ₀) (𝟙 T)
    (by rw [Category.assoc, hσ₀, Category.comp_id, Category.id_comp])
  have hσ₁ : σ ≫ pr₁ = τ ≫ σ₀ := pullback.lift_fst _ _ _
  have hσ₂ : σ ≫ pr₂ = 𝟙 T := pullback.lift_snd _ _ _
  have hσ₀z : ∀ t : Γ(L, ⊤), e ∈ ((zeroScheme X L t).support : Set X) →
      pullbackGlobalSections σ _ (pullbackGlobalSections pr₁ L t) = 0 := by
    intro t ht
    rw [← Stacks.Divisors.pullbackGlobalSections_comp_eq_zero_iff,
      Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker, hσ₁,
      ← Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker]
    apply Stacks.Divisors.pullbackGlobalSections_comp_eq_zero
    exact pullbackGlobalSections_eq_zero_of_range_subset σ₀ L t
      (hσ₀r.trans (Set.singleton_subset_iff.2 ht))
  have hσker : I ≤ σ.ker := by
    refine iSup₂_le fun j _ => ?_
    refine (Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker _ _ _).1 ?_
    have hej : e ∈ ((zeroScheme X L (v j)).support : Set X) :=
      Scheme.IdealSheafData.support_antitone
        (le_iSup₂_of_le (f := fun (j : Fin (d - 1)) (_ : j.val < d - 1) => zeroScheme X L (v j))
          j j.2 le_rfl) heC
    rw [incidenceSection, map_sub, SectionsEqualizer.pullbackGlobalSections_smul, hσ₀z _ hej,
      hσ₀z _ hew, smul_zero, sub_zero]
  let σ' : T ⟶ I.subscheme :=
    IsClosedImmersion.lift I.subschemeι σ (by rw [I.ker_subschemeι]; exact hσker)
  have hσ' : σ' ≫ π = 𝟙 T := by
    show σ' ≫ I.subschemeι ≫ pr₂ = 𝟙 T
    rw [← Category.assoc, IsClosedImmersion.lift_fac, hσ₂]
  have hjx : π (j ⟨x, hxV⟩) = s := by
    obtain ⟨y, hy⟩ : ι x ∈ Set.range I.subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact (hCι x).2 hxC
    have hyj : y ∉ (Set.range j.base)ᶜ := by
      rw [Set.mem_compl_iff, not_not, hjr]
      show pr₁ (I.subschemeι y) ∈ V
      rw [hy, hιfst]
      exact hxV
    obtain ⟨u, hu⟩ := not_not.mp hyj
    have hux : u = ⟨x, hxV⟩ := by
      apply V.ι.isOpenEmbedding.injective
      have h := congrArg (fun g : V.toScheme ⟶ X => g.base u) hj1
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at h
      rw [← h, hu, hy, hιfst]
      rfl
    rw [← hux]
    show pr₂ (I.subschemeι (j u)) = s
    rw [hu, hy]
    exact hιs x
  have hjτ : j ≫ π ≫ τ = V.ι ≫ p := by
    calc j ≫ (I.subschemeι ≫ pr₂) ≫ τ = (j ≫ I.subschemeι ≫ pr₁) ≫ p := by
          simp only [Category.assoc, pr₁, pr₂, pullback.condition]
      _ = V.ι ≫ p := by rw [hj1]
  have : Nonempty V.toScheme := ⟨⟨x, hxV⟩⟩
  have : IrreducibleSpace V.toScheme := V.ι.isOpenEmbedding.irreducibleSpace
  obtain ⟨S₀, U₀, e₀, f₀, hS₀, hsS₀, he₀, hf₀, hcomm, hrange'⟩ :=
    exists_isElementaryFibration_of_closedFibre k τ π hπ σ' hσ' j i hZ s hsm het hne
      ⟨⟨x, hxV⟩, hjx⟩
  have : IsOpenImmersion e₀ := he₀
  let φ := (e₀ ≫ V.ι).isoOpensRange
  have : IsAffine S₀.toScheme := hS₀
  have : Nonempty S₀ := ⟨⟨_, hsS₀⟩⟩
  have : IsIntegral S₀.toScheme := isIntegral_of_isOpenImmersion S₀.ι
  have hq : SmoothOfRelativeDimension (d - 1) (S₀.ι ≫ τ) := by
    have h : SmoothOfRelativeDimension (0 + (d - 1)) (S₀.ι ≫ τ) := inferInstance
    rwa [zero_add] at h
  refine ⟨(e₀ ≫ V.ι).opensRange, S₀.toScheme, S₀.ι ≫ τ, φ.inv ≫ f₀, ?_, ?_,
    hf₀.precomp_iso φ.symm, hq, inferInstance, inferInstance, ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact (e₀ u).2.1
  · have hv : (⟨x, hxV⟩ : V.toScheme) ∈ Set.range e₀.base := by
      rw [hrange']
      show π (j ⟨x, hxV⟩) ∈ (S₀ : Set T)
      rw [hjx]
      exact hsS₀
    obtain ⟨u₀, hu₀⟩ := hv
    exact ⟨u₀, by rw [Scheme.Hom.comp_apply, hu₀]; rfl⟩
  · calc (φ.inv ≫ f₀) ≫ S₀.ι ≫ τ = φ.inv ≫ (f₀ ≫ S₀.ι) ≫ τ := by
          simp only [Category.assoc]
      _ = φ.inv ≫ e₀ ≫ j ≫ π ≫ τ := by rw [hcomm]; simp only [Category.assoc]
      _ = φ.inv ≫ (e₀ ≫ V.ι) ≫ p := by rw [hjτ, Category.assoc]
      _ = (e₀ ≫ V.ι).opensRange.ι ≫ p := by
          have h := Scheme.Hom.isoOpensRange_hom_ι (e₀ ≫ V.ι)
          calc φ.inv ≫ (e₀ ≫ V.ι) ≫ p
              = φ.inv ≫ ((e₀ ≫ V.ι).isoOpensRange.hom ≫ (e₀ ≫ V.ι).opensRange.ι) ≫ p := by
                rw [h]
            _ = (e₀ ≫ V.ι).opensRange.ι ≫ p := by
                rw [Category.assoc, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.GoodNeighbourhood

end
