module

public import StacksFrontier.AlgebraicGeometry.Spaces.GluedEtaleQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# The kernel pair of an étale atlas which is an isomorphism off an open subspace

Let `f : V ⟶ X` be an étale morphism from an object of the site to an algebraic space, let
`U ⊆ X` be an open subspace over whose closed complement `f` is an isomorphism, and let
`W = f⁻¹(U)`, an open subscheme of `V`. Then the kernel pair `V ×_X V` is glued from the
diagonal copy of `V` and from `W ×_U W` along the diagonal copy of `W`: these two charts are
open, they meet along `W`, and they cover `V ×_X V` because a point of `V ×_X V` lying over the
complement of `U` lies on the diagonal. This is the identification of the limit relation
`R = lim R_i` with `V ×_X V` in the proof of absolute Noetherian approximation.

## Main results

* `AlgebraicGeometry.Space.GluedKernelDatum.isPushout`: the kernel pair is the pushout of the
  two charts.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.hasPullbacks_bigFppfOver
  AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The data of an étale morphism which is an isomorphism off an open subspace, with the inverse
image of the open subspace, and the kernel pairs of the morphism and of its restriction. -/
structure GluedKernelDatum where
  /-- The algebraic space. -/
  X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  isAlgebraicSpace_X : IsAlgebraicSpace B S hS X
  /-- The open subspace. -/
  Uo : Subfunctor X
  isOpenSubspace : IsOpenSubspace B S hS Uo
  /-- The scheme. -/
  V : BigFppfOver B S hS
  /-- The étale morphism. -/
  f : yoneda.obj V ⟶ X
  isEtale_f : IsEtale B S hS f
  /-- The inverse image of the open subspace. -/
  W : BigFppfOver B S hS
  /-- Its open immersion into `V`. -/
  jW : W ⟶ V
  [isOpenImmersion_jW :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jW)]
  /-- Its morphism to the open subspace. -/
  wU : yoneda.obj W ⟶ Uo.toFunctor
  isPullback_W : IsPullback (yoneda.map jW) wU f Uo.ι
  /-- The kernel pair of `f`. -/
  K : BigFppfOver B S hS
  /-- The first projection of the kernel pair of `f`. -/
  k₁ : K ⟶ V
  /-- The second projection of the kernel pair of `f`. -/
  k₂ : K ⟶ V
  isPullback_K : IsPullback (yoneda.map k₁) (yoneda.map k₂) f f
  /-- The kernel pair of the restriction of `f`. -/
  Q : BigFppfOver B S hS
  /-- The first projection of the kernel pair of the restriction of `f`. -/
  q₁ : Q ⟶ W
  /-- The second projection of the kernel pair of the restriction of `f`. -/
  q₂ : Q ⟶ W
  isPullback_Q : IsPullback (yoneda.map q₁) (yoneda.map q₂) wU wU

namespace GluedKernelDatum

attribute [instance] isOpenImmersion_jW

variable {B S hS} (D : GluedKernelDatum B S hS)

local notation "𝕋" => BigFppfOver.toScheme B S hS

/-- The open immersion `W ⟶ V` is a monomorphism. -/
theorem jW_mono : Mono D.jW :=
  ⟨fun x y h => (𝕋).map_injective ((cancel_mono ((𝕋).map D.jW)).1
    (by rw [← Functor.map_comp, ← Functor.map_comp, h]))⟩

/-- Two morphisms to the kernel pair of `f` agree if their compositions with both projections
agree. -/
theorem K_hom_ext {T : BigFppfOver B S hS} {x y : T ⟶ D.K} (h₁ : x ≫ D.k₁ = y ≫ D.k₁)
    (h₂ : x ≫ D.k₂ = y ≫ D.k₂) : x = y :=
  yoneda.map_injective (D.isPullback_K.hom_ext (by simpa using congrArg yoneda.map h₁)
    (by simpa using congrArg yoneda.map h₂))

/-- Two morphisms to the kernel pair of the restriction of `f` agree if their compositions with
both projections agree. -/
theorem Q_hom_ext {T : BigFppfOver B S hS} {x y : T ⟶ D.Q} (h₁ : x ≫ D.q₁ = y ≫ D.q₁)
    (h₂ : x ≫ D.q₂ = y ≫ D.q₂) : x = y :=
  yoneda.map_injective (D.isPullback_Q.hom_ext (by simpa using congrArg yoneda.map h₁)
    (by simpa using congrArg yoneda.map h₂))

/-- The diagonal of the kernel pair of `f`. -/
noncomputable def Δ : D.V ⟶ D.K := yoneda.preimage (D.isPullback_K.lift (𝟙 _) (𝟙 _) rfl)

/-- The diagonal followed by the first projection is the identity. -/
@[reassoc (attr := simp)]
theorem Δ_k₁ : D.Δ ≫ D.k₁ = 𝟙 _ := yoneda.map_injective (by simp [Δ])

/-- The diagonal followed by the second projection is the identity. -/
@[reassoc (attr := simp)]
theorem Δ_k₂ : D.Δ ≫ D.k₂ = 𝟙 _ := yoneda.map_injective (by simp [Δ])

/-- The diagonal of the kernel pair of the restriction of `f`. -/
noncomputable def d : D.W ⟶ D.Q := yoneda.preimage (D.isPullback_Q.lift (𝟙 _) (𝟙 _) rfl)

/-- The diagonal of `W ×_U W` followed by the first projection is the identity. -/
@[reassoc (attr := simp)]
theorem d_q₁ : D.d ≫ D.q₁ = 𝟙 _ := yoneda.map_injective (by simp [d])

/-- The diagonal of `W ×_U W` followed by the second projection is the identity. -/
@[reassoc (attr := simp)]
theorem d_q₂ : D.d ≫ D.q₂ = 𝟙 _ := yoneda.map_injective (by simp [d])

/-- The two composites `W ×_U W ⟶ W ⟶ V ⟶ X` agree. -/
theorem w_f : yoneda.map (D.q₁ ≫ D.jW) ≫ D.f = yoneda.map (D.q₂ ≫ D.jW) ≫ D.f := by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, D.isPullback_W.w,
    ← Category.assoc, ← Category.assoc, D.isPullback_Q.w]

/-- The chart `W ×_U W` of the kernel pair of `f`. -/
noncomputable def ι : D.Q ⟶ D.K :=
  yoneda.preimage (D.isPullback_K.lift (yoneda.map (D.q₁ ≫ D.jW)) (yoneda.map (D.q₂ ≫ D.jW)) D.w_f)

/-- The chart `W ×_U W ⟶ V ×_X V` followed by the first projection is the first projection
followed by `W ⟶ V`. -/
@[reassoc (attr := simp)]
theorem ι_k₁ : D.ι ≫ D.k₁ = D.q₁ ≫ D.jW := yoneda.map_injective (by simp [ι])

/-- The chart `W ×_U W ⟶ V ×_X V` followed by the second projection is the second projection
followed by `W ⟶ V`. -/
@[reassoc (attr := simp)]
theorem ι_k₂ : D.ι ≫ D.k₂ = D.q₂ ≫ D.jW := yoneda.map_injective (by simp [ι])

/-- The diagonal restricted to `W` factors through the chart `W ×_U W` via its diagonal. -/
theorem jW_Δ : D.jW ≫ D.Δ = D.d ≫ D.ι := D.K_hom_ext (by simp) (by simp)

/-- **The two charts meet along `W`.** -/
theorem isPullback_charts : IsPullback D.jW D.d D.Δ D.ι := by
  have := D.jW_mono
  have key : ∀ s : PullbackCone D.Δ D.ι,
      s.fst = s.snd ≫ D.q₁ ≫ D.jW ∧ s.fst = s.snd ≫ D.q₂ ≫ D.jW := fun s =>
    ⟨by simpa using congrArg (· ≫ D.k₁) s.condition,
      by simpa using congrArg (· ≫ D.k₂) s.condition⟩
  refine IsPullback.of_isLimit' ⟨D.jW_Δ⟩ (PullbackCone.IsLimit.mk _
    (fun s => s.snd ≫ D.q₁) (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · simpa using (key s).1.symm
  · have h : s.snd ≫ D.q₁ = s.snd ≫ D.q₂ :=
      (cancel_mono D.jW).1 (by simp only [Category.assoc, ← (key s).1, ← (key s).2])
    exact D.Q_hom_ext (by simp) (by simp [h])
  · simp [← hm₂]

/-- **The chart `W ×_U W` is the inverse image of `W` under the first projection**: a point of
`V ×_X V` whose first projection lies over `U` has its second projection over `U` too. -/
theorem isPullback_ι : IsPullback D.ι D.q₁ D.k₁ D.jW := by
  have := D.jW_mono
  have hW : ∀ (s : PullbackCone D.k₁ D.jW),
      yoneda.map (s.fst ≫ D.k₂) ≫ D.f = (yoneda.map s.snd ≫ D.wU) ≫ D.Uo.ι := fun s => by
    rw [Functor.map_comp, Category.assoc, ← D.isPullback_K.w, ← Category.assoc,
      ← Functor.map_comp, s.condition, Functor.map_comp, Category.assoc, Category.assoc,
      D.isPullback_W.w]
  let L : ∀ (s : PullbackCone D.k₁ D.jW), yoneda.obj s.pt ⟶ yoneda.obj D.Q := fun s =>
    D.isPullback_Q.lift (yoneda.map s.snd) (D.isPullback_W.lift _ _ (hW s))
      (by rw [IsPullback.lift_snd])
  have hL₁ : ∀ s, yoneda.preimage (L s) ≫ D.q₁ = s.snd := fun s =>
    yoneda.map_injective (by simpa using IsPullback.lift_fst _ _ _ _)
  have hL₂ : ∀ s, yoneda.preimage (L s) ≫ D.q₂ ≫ D.jW = s.fst ≫ D.k₂ := fun s =>
    yoneda.map_injective (by
      simpa using (by rw [← Category.assoc, IsPullback.lift_snd, IsPullback.lift_fst] :
        L s ≫ yoneda.map D.q₂ ≫ yoneda.map D.jW = yoneda.map (s.fst ≫ D.k₂)))
  refine IsPullback.of_isLimit' ⟨D.ι_k₁⟩ (PullbackCone.IsLimit.mk _ (fun s => yoneda.preimage (L s))
    (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · exact D.K_hom_ext (by simp [reassoc_of% (hL₁ s), s.condition]) (by simp [hL₂])
  · exact hL₁ s
  · refine D.Q_hom_ext (by simp [← hm₂, hL₁]) ((cancel_mono D.jW).1 ?_)
    rw [Category.assoc, Category.assoc, hL₂, ← ι_k₂, ← hm₁, Category.assoc]

/-- The first projection of the kernel pair of `f` is étale. -/
theorem etale_k₁ : Etale ((𝕋).map D.k₁) :=
  (presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance _).mp
    (presheaf_of_isPullback B S hS D.isPullback_K.flip
      ((isEtale_iff_presheaf_of_yoneda B S hS D.f).mp D.isEtale_f))

/-- The diagonal `V ⟶ V ×_X V` is an open immersion. -/
instance isOpenImmersion_Δ : _root_.AlgebraicGeometry.IsOpenImmersion ((𝕋).map D.Δ) := by
  have := D.etale_k₁
  exact isOpenImmersion_of_section_of_etale ((𝕋).map D.k₁) ((𝕋).map D.Δ)
    (by rw [← Functor.map_comp, Δ_k₁, CategoryTheory.Functor.map_id])

/-- The chart `W ×_U W ⟶ V ×_X V` is an open immersion. -/
instance isOpenImmersion_ι : _root_.AlgebraicGeometry.IsOpenImmersion ((𝕋).map D.ι) :=
  MorphismProperty.of_isPullback (D.isPullback_ι.map (𝕋)).flip inferInstance

/-- The diagonal `W ⟶ W ×_U W` is an open immersion. -/
instance isOpenImmersion_d : _root_.AlgebraicGeometry.IsOpenImmersion ((𝕋).map D.d) :=
  MorphismProperty.of_isPullback (D.isPullback_charts.map (𝕋)) inferInstance

section Cover

variable (Tc : Subfunctor D.X)
  (hT : ∀ x, x ∉ Set.range (pointsMap B S hS D.Uo.toFunctor D.Uo.ι) →
    x ∈ Set.range (pointsMap B S hS Tc.toFunctor Tc.ι))
  (hiso : IsIso (pullback.fst Tc.ι D.f))

include hT hiso in
/-- **The two charts cover the kernel pair**: a point of `V ×_X V` lying over the complement of
`U` lies on the diagonal, because `f` is an isomorphism over the complement. -/
theorem mem_range_Δ_or_ι (κ : (𝕋).obj D.K) :
    κ ∈ Set.range ((𝕋).map D.Δ).base ∨ κ ∈ Set.range ((𝕋).map D.ι).base := by
  obtain ⟨p, rfl⟩ := surjective_pointsToScheme B S hS D.K κ
  set x := pointsMap B S hS (yoneda.obj D.K) (yoneda.map D.k₁ ≫ D.f) p
  by_cases hx : x ∈ Set.range (pointsMap B S hS D.Uo.toFunctor D.Uo.ι)
  · obtain ⟨z, hz⟩ := hx
    have hsq : IsPullback (yoneda.map D.ι) (yoneda.map D.q₁ ≫ D.wU) (yoneda.map D.k₁ ≫ D.f)
        D.Uo.ι := (D.isPullback_ι.map yoneda).paste_vert D.isPullback_W
    obtain ⟨t, ht, -⟩ := exists_points_of_isPullback B S hS hsq p z hz.symm
    refine Or.inr ⟨pointsToScheme B S hS D.Q t, ?_⟩
    rw [← pointsToScheme_pointsMap_yoneda, ht]
  · obtain ⟨d₀, hd₀⟩ := hT x hx
    obtain ⟨t₀, ht₀, ht₀'⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback Tc.ι (yoneda.map D.k₁ ≫ D.f)) d₀ p hd₀
    let sD : pullback Tc.ι (yoneda.map D.k₁ ≫ D.f) ⟶ Tc.toFunctor := pullback.fst _ _
    let sR : pullback Tc.ι (yoneda.map D.k₁ ≫ D.f) ⟶ yoneda.obj D.K := pullback.snd _ _
    have h₁ : sD ≫ Tc.ι = (sR ≫ yoneda.map D.k₁) ≫ D.f := by
      rw [Category.assoc]
      exact pullback.condition
    have h₂ : sD ≫ Tc.ι = (sR ≫ yoneda.map D.k₂) ≫ D.f := by
      refine h₁.trans ?_
      rw [Category.assoc, Category.assoc]
      exact congrArg (sR ≫ ·) D.isPullback_K.w
    have hl : pullback.lift sD (sR ≫ yoneda.map D.k₁) h₁ =
        pullback.lift sD (sR ≫ yoneda.map D.k₂) h₂ := by
      refine (cancel_mono (pullback.fst Tc.ι D.f)).1 ?_
      rw [pullback.lift_fst, pullback.lift_fst]
    have ha : sR ≫ yoneda.map D.k₁ = sR ≫ yoneda.map D.k₂ := by
      have := congrArg (· ≫ pullback.snd Tc.ι D.f) hl
      rwa [pullback.lift_snd, pullback.lift_snd] at this
    have hdiag : sR = (sR ≫ yoneda.map D.k₁) ≫ yoneda.map D.Δ := by
      refine D.isPullback_K.hom_ext ?_ ?_
      · rw [Category.assoc, ← Functor.map_comp, Δ_k₁, CategoryTheory.Functor.map_id,
          Category.comp_id]
      · rw [Category.assoc, ← Functor.map_comp, Δ_k₂, CategoryTheory.Functor.map_id,
          Category.comp_id, ha]
    refine Or.inl ⟨pointsToScheme B S hS D.V
      (pointsMap B S hS _ (sR ≫ yoneda.map D.k₁) t₀), ?_⟩
    rw [← pointsToScheme_pointsMap_yoneda, ← pointsMap_comp_apply, ← hdiag]
    exact congrArg (pointsToScheme B S hS D.K) ht₀'

include hT hiso in
/-- **The kernel pair of `f` is glued from the diagonal copy of `V` and from `W ×_U W` along
the diagonal copy of `W`.** -/
theorem isPushout : IsPushout ((𝕋).map D.jW) ((𝕋).map D.d) ((𝕋).map D.Δ) ((𝕋).map D.ι) :=
  isPushout_of_isPullback_of_jointly_surjective (D.isPullback_charts.map (𝕋))
    (D.mem_range_Δ_or_ι Tc hT hiso)

end Cover

end GluedKernelDatum

end AlgebraicGeometry.Space

end
