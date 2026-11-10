module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSpaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SiteObjectBase
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFiniteAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# Properness descends to a stage of a limit of affine objects

Let `V = lim V_i` be a cofiltered limit of affine objects of the big fppf site and let
`Y_k ⟶ V_k` be a separated morphism of finite type from an algebraic space whose base change
to `V` is proper. Then its base change to some later stage is proper.

This is the step "after increasing `λ` we may assume `V'_λ ⟶ V_λ` is proper" of the proof of
Stacks 0GI5, for algebraic spaces and an index category of any size. As in the source it goes
through Chow's lemma (Stacks 089J, over a base object of the site): a proper surjection
`h_{X'} ⟶ Y_k` from a scheme `X'` of finite type over `V_k`; the scheme `X' ⟶ V_k` becomes
proper at a stage (Stacks 081F for schemes), and properness passes to the image (Stacks 08AJ).

## Main results

* `AlgebraicGeometry.Space.exists_chowSchemeCover_of_isAffine`: Chow's lemma over an affine object.
* `AlgebraicGeometry.Space.exists_stage_isProper_of_isLimit`: the descent of properness.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Chow's lemma over an affine object of the site** (Stacks 089J): a separated algebraic space
of finite type over an affine object `V` is the target of a proper surjection from a scheme of
the site over `V` whose structure morphism is quasi-compact. -/
theorem exists_chowSchemeCover_of_isAffine {V : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ yoneda.obj V) (hsep : IsSeparated B S hS g) (hft : IsFiniteType B S hS g) :
    ∃ (X' : BigFppfOver B S hS) (ψ : X' ⟶ V) (p : yoneda.obj X' ⟶ X),
      IsProper B S hS p ∧ IsSurjective B S hS p ∧ p ≫ g = yoneda.map ψ ∧
        QuasiCompact ((BigFppfOver.toScheme B S hS).map ψ) := by
  let T := BigFppfOver.toScheme B S hS
  have := hV
  let A : CommRingCat.{u} := CommRingCat.of Γ(T.obj V, ⊤)
  have hA : B.Contains (Spec A) :=
    contains_spec_of_isAffine B S hS (V := V) Γ(T.obj V, ⊤) (RingEquiv.refl _) Γ(T.obj V, ⊤)
  let e₀ : B.obj hA ≅ V.left := B.inclusion.preimageIso (T.obj V).isoSpec.symm
  let e : (Over.mk (e₀.hom ≫ V.hom) : BigFppfOver B S hS) ≅ V := Over.isoMk e₀ rfl
  have hsep' : IsSeparated B S hS (g ≫ yoneda.map e.inv) :=
    isSeparated_of_arrowIso B S hS g (g ≫ yoneda.map e.inv) (𝟙 _) (yoneda.map e.inv)
      (by simp) hsep
  have hft' : IsFiniteType B S hS (g ≫ yoneda.map e.inv) :=
    isFiniteType_of_arrowIso B S hS g (g ≫ yoneda.map e.inv) (𝟙 _) (yoneda.map e.inv)
      (by simp) hft
  obtain ⟨X', ψ, p, hp, hps, hpg, hq⟩ :=
    exists_chowSchemeCover_over_base B S hS A hA (e₀.hom ≫ V.hom) hX _ hsep' hft'
  refine ⟨X', ψ ≫ e.hom, p, hp, hps, ?_, ?_⟩
  · rw [Functor.map_comp, ← reassoc_of% hpg, ← Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  · have := quasiCompact_of_isHQuasiProjective hq
    rw [Functor.map_comp]
    infer_instance

section BaseChange

variable {X' W V : BigFppfOver B S hS} {Yk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {ψ : X' ⟶ V} {π : yoneda.obj X' ⟶ Yk} {pk : Yk ⟶ yoneda.obj V} (hπ : π ≫ pk = yoneda.map ψ)
  (φ : W ⟶ V)

/-- The comparison `h_{X' ×_V W} ⟶ Y_k ×_V h_W` induced by `π : h_{X'} ⟶ Y_k` over `V`. -/
noncomputable def chowBaseChangeMap : yoneda.obj (pullback ψ φ) ⟶ pullback pk (yoneda.map φ) :=
  pullback.lift (yoneda.map (pullback.fst ψ φ) ≫ π) (yoneda.map (pullback.snd ψ φ)) (by
    rw [Category.assoc, hπ, ← Functor.map_comp, pullback.condition, Functor.map_comp])

/-- The comparison `chowBaseChangeMap` followed by the projection `Y_k ×_V h_W ⟶ h_W` is the
image under the Yoneda embedding of the projection `X' ×_V W ⟶ W`. -/
theorem chowBaseChangeMap_snd :
    chowBaseChangeMap hπ φ ≫ pullback.snd pk (yoneda.map φ) = yoneda.map (pullback.snd ψ φ) :=
  pullback.lift_snd _ _ _

/-- The square formed by `h_{X' ×_V W} ⟶ h_{X'}`, the comparison `chowBaseChangeMap`,
`π : h_{X'} ⟶ Y_k` and the projection `Y_k ×_V h_W ⟶ Y_k` is a pullback square. -/
theorem isPullback_chowBaseChangeMap :
    IsPullback (yoneda.map (pullback.fst ψ φ)) (chowBaseChangeMap hπ φ) π
      (pullback.fst pk (yoneda.map φ)) := by
  have big : IsPullback (yoneda.map (pullback.fst ψ φ))
      (chowBaseChangeMap hπ φ ≫ pullback.snd pk (yoneda.map φ)) (π ≫ pk) (yoneda.map φ) := by
    rw [chowBaseChangeMap_snd, hπ]
    exact (IsPullback.of_hasPullback ψ φ).map yoneda
  exact IsPullback.of_bot big (pullback.lift_fst _ _ _).symm
    (IsPullback.of_hasPullback pk (yoneda.map φ))

end BaseChange

/-- The base change of a morphism from an algebraic space to a represented presheaf along a
represented morphism is an algebraic space. -/
private theorem isAlgebraicSpace_pullback_yoneda_map {Yk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hYk : IsAlgebraicSpace B S hS Yk) {V W : BigFppfOver B S hS} (pk : Yk ⟶ yoneda.obj V)
    (φ : W ⟶ V) : IsAlgebraicSpace B S hS (pullback pk (yoneda.map φ)) :=
  isAlgebraicSpace_pullback B S hS _ _ hYk (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_yoneda B S hS _)

/-- **Properness descends to a stage of a limit of affine objects.** Let `V = lim V_i` be a
cofiltered limit of affine objects of the site (any `u`-small index), `p_k : Y_k ⟶ V_k` a
separated morphism of finite type from an algebraic space, and `p : Y ⟶ V` its base change. If
`p` is proper, then the base change of `p_k` to some later stage is proper. -/
theorem exists_stage_isProper_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ BigFppfOver B S hS} {c : Cone E}
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hE : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    {k : I} {Yk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hYk : IsAlgebraicSpace B S hS Yk)
    (pk : Yk ⟶ yoneda.obj (E.obj k)) (hsep : IsSeparated B S hS pk)
    (hft : IsFiniteType B S hS pk) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (p : Y ⟶ yoneda.obj c.pt) (a : Y ⟶ Yk)
    (hpb : IsPullback p a (yoneda.map (c.π.app k)) pk) (hp : IsProper B S hS p) :
    ∃ (k' : I) (f : k' ⟶ k), IsProper B S hS (pullback.snd pk (yoneda.map (E.map f))) := by
  let T := BigFppfOver.toScheme B S hS
  have : PreservesLimitsOfShape WalkingCospan T := comp_preservesLimitsOfShape _ _
  let D := E ⋙ T
  let c' := T.mapCone c
  have : EssentiallySmall.{u} I := essentiallySmallSelf.{u} I
  have : ∀ i, IsAffine (D.obj i) := hE
  have : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map f) :=
    fun f => isAffineHom_of_isAffine _
  have : IsAffine (T.obj (E.obj k)) := hE k
  -- Chow's lemma over the affine stage
  obtain ⟨X', ψ, π, hπp, hπs, hπ, hψqc⟩ := exists_chowSchemeCover_of_isAffine (hE k) hYk pk hsep hft
  have hX' : IsAlgebraicSpace B S hS (yoneda.obj X') := isAlgebraicSpace_yoneda B S hS X'
  have hVk : IsAlgebraicSpace B S hS (yoneda.obj (E.obj k)) := isAlgebraicSpace_yoneda B S hS _
  have hψsep : AlgebraicGeometry.IsSeparated (T.map ψ) := by
    rw [← isSeparated_yoneda_map_iff, ← hπ]
    exact isSeparated_comp B S hS π pk hπp.1 hsep
  have hψlft : LocallyOfFiniteType (T.map ψ) := by
    rw [← isLocallyOfFiniteType_yoneda_map_iff, ← hπ]
    exact (isFiniteType_comp B S hS hX' hYk hVk π pk hπp.2.1 hft).1
  -- the base change of a represented morphism along the cone is the pullback in the site
  have key : ∀ {W : BigFppfOver B S hS} (φ : W ⟶ E.obj k),
      IsProper B S hS (yoneda.map (pullback.snd ψ φ)) ↔
        _root_.AlgebraicGeometry.IsProper (pullback.snd (T.map ψ) (T.map φ)) := by
    intro W φ
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @AlgebraicGeometry.IsProper)
      (PreservesPullback.iso T ψ φ).hom, PreservesPullback.iso_hom_snd]
    exact ⟨isProper_toScheme_map_of_isProper_yoneda_map B S hS _,
      isProper_yoneda_map B S hS _⟩
  let X₀ : Over (D.obj k) := Over.mk (T.map ψ)
  let Y₀ : Over (D.obj k) := Over.mk (𝟙 (D.obj k))
  let f₀ : X₀ ⟶ Y₀ := Over.homMk (T.map ψ) (Category.comp_id _)
  have hf₀ : ∀ {Z : Scheme.{u}} (g : Z ⟶ D.obj k),
      ((Over.pullback g).map f₀).left ≫ pullback.snd (𝟙 (D.obj k)) g =
        pullback.snd (T.map ψ) g := fun g =>
    Over.w ((Over.pullback g).map f₀)
  have hiso : ∀ {Z : Scheme.{u}} (g : Z ⟶ D.obj k), IsIso (pullback.snd (𝟙 (D.obj k)) g) :=
    fun g => inferInstance
  have hprop : ∀ {Z : Scheme.{u}} (g : Z ⟶ D.obj k),
      _root_.AlgebraicGeometry.IsProper ((Over.pullback g).map f₀).left ↔
        _root_.AlgebraicGeometry.IsProper (pullback.snd (T.map ψ) g) := by
    intro Z g
    rw [← hf₀ g, MorphismProperty.cancel_right_of_respectsIso (P := @AlgebraicGeometry.IsProper)]
  -- properness at the limit
  have hlim : _root_.AlgebraicGeometry.IsProper ((Over.pullback (c'.π.app k)).map f₀).left := by
    rw [hprop]
    change _root_.AlgebraicGeometry.IsProper (pullback.snd (T.map ψ) (T.map (c.π.app k)))
    rw [← key, ← chowBaseChangeMap_snd hπ (c.π.app k)]
    have hP := isAlgebraicSpace_pullback_yoneda_map hYk pk (c.π.app k)
    refine isProper_comp B S hS (isAlgebraicSpace_yoneda B S hS _) hP
      (isAlgebraicSpace_yoneda B S hS _) _ _
      (isProper_of_isPullback B S hS (isAlgebraicSpace_yoneda B S hS _) hX' hP hYk
        (isPullback_chowBaseChangeMap hπ (c.π.app k)) hπp) ?_
    rw [← hpb.flip.isoPullback_inv_snd]
    exact isProper_comp B S hS hP hY (isAlgebraicSpace_yoneda B S hS _) _ _
      (isProper_of_isIso B S hS _) hp
  -- properness at a stage (Stacks 081F for schemes)
  have : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace (T.map ψ)
  have : QuasiSeparatedSpace X₀.left := quasiSeparatedSpace_of_quasiSeparated (T.map ψ)
  have : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj k))
  have : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj k))
  have : LocallyOfFiniteType f₀.left := hψlft
  have := hlim
  obtain ⟨k', f, hk'⟩ := exists_isProper_baseChange_of_isLimit D c' k hc X₀ Y₀ f₀
  refine ⟨k', f, ?_⟩
  rw [hprop] at hk'
  have hYk' := isAlgebraicSpace_pullback_yoneda_map hYk pk (E.map f)
  have hW : IsAlgebraicSpace B S hS (yoneda.obj (E.obj k')) := isAlgebraicSpace_yoneda B S hS _
  have hcomp : IsProper B S hS (chowBaseChangeMap hπ (E.map f) ≫
      pullback.snd pk (yoneda.map (E.map f))) := by
    rwa [chowBaseChangeMap_snd, key]
  have hsurj : IsSurjective B S hS (chowBaseChangeMap hπ (E.map f)) := by
    have sq := isPullback_chowBaseChangeMap hπ (E.map f)
    exact isSurjective_of_isPullback B S hS
      (W := ⟨_, isAlgebraicSpace_yoneda B S hS _⟩) (Z := ⟨_, hX'⟩) (X := ⟨_, hYk'⟩) (Y := ⟨_, hYk⟩)
      (p := ObjectProperty.homMk (yoneda.map (pullback.fst ψ (E.map f))))
      (q := ObjectProperty.homMk (chowBaseChangeMap hπ (E.map f)))
      (g := ObjectProperty.homMk π) (f := ObjectProperty.homMk (pullback.fst pk _))
      (IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) sq) hπs
  exact isProper_of_isSurjective_comp B S hS (isAlgebraicSpace_yoneda B S hS _) hYk' hW _ _
    hcomp.2.2 hsurj (isSeparated_pullback B S hS pk _ hsep)
    (IsFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback pk (yoneda.map (E.map f))).flip
      hYk hVk hft)

/-- **A proper algebraic space of finite presentation over a limit of affine objects descends to a
proper algebraic space over a stage** (any `u`-small cofiltered index). -/
theorem exists_stage_isProper_model
    {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ BigFppfOver B S hS} {c : Cone E}
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hE : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (p : Y ⟶ yoneda.obj c.pt) (hp : IsProper B S hS p)
    (hqc : IsQuasiCompactSpace B S hS Y) (hlfp : IsLocallyOfFinitePresentation B S hS p) :
    ∃ (k : I) (Yk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Yk)
      (pk : Yk ⟶ yoneda.obj (E.obj k)) (a : Y ⟶ Yk),
      IsPullback p a (yoneda.map (c.π.app k)) pk ∧ IsProper B S hS pk := by
  obtain ⟨k, Yk, hYk, pk, a, hpb, hsep, hft⟩ :=
    exists_stage_model_of_isSeparated hc hE hpt hY p hp.1 hqc hlfp
  obtain ⟨k', f, hk'⟩ := exists_stage_isProper_of_isLimit hc hE hYk pk hsep hft hY p a hpb hp
  have hw : yoneda.map (c.π.app k') ≫ yoneda.map (E.map f) = yoneda.map (c.π.app k) := by
    rw [← Functor.map_comp, c.w]
  let a' : Y ⟶ pullback pk (yoneda.map (E.map f)) :=
    pullback.lift a (p ≫ yoneda.map (c.π.app k')) (by rw [Category.assoc, hw, hpb.w])
  refine ⟨k', _, isAlgebraicSpace_pullback_yoneda_map hYk pk (E.map f), _, a', ?_, hk'⟩
  have big : IsPullback p (a' ≫ pullback.fst pk (yoneda.map (E.map f)))
      (yoneda.map (c.π.app k') ≫ yoneda.map (E.map f)) pk := by
    rwa [hw, pullback.lift_fst]
  exact IsPullback.of_bot big (pullback.lift_snd _ _ _).symm
    (IsPullback.of_hasPullback pk (yoneda.map (E.map f))).flip

end AlgebraicGeometry.Space

end
