module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.DenseAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.NoetherianInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.Permanence
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianOfFiniteTypeOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOpenEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionIntoQuotientStackSubspace

/-!
# Nagata's compactification theorem over a base of finite type over `Spec ℤ`

Let `Y` be an algebraic space over `S` which is quasi-compact, quasi-separated and of finite
type over `Spec ℤ`, and let `f : X ⟶ Y` be separated and of finite type. Then `X` has a
compactification over `Y`.

`X` is Noetherian, so it has a dense open affine subspace, which has a compactification over
`Y`. By Noetherian induction there is a maximal open subspace `U ⊆ X` containing it which has a
compactification over `Y`; `U` is dense. If `U ≠ X`, Stacks 0F4C gives a strictly larger open
`U ⊂ W ⊆ X` and an elementary distinguished square `(U ⊆ W, V ⟶ W)` with `V` affine and
`U ×_W V ⟶ U` of dense image. The affine `V` has a compactification over `Y`, so Stacks 0F4B
gives one of `W`, contradicting maximality. Hence `U = X`.

## Main results

* `AlgebraicGeometry.Space.hasCompactification_of_isFiniteType_viewOverIntegers`: the theorem.

## Implementation notes

Stacks 0F4B is the explicit hypothesis `h0F4B`, supplied by
`AlgebraicGeometry.Space.hasCompactification_of_isElementaryDistinguishedSquare`. It is stated
as in the source, for an elementary distinguished square `(U₂ ⊆ U, f : U₁ ⟶ U)` in the sense of
`AlgebraicGeometry.Space.IsElementaryDistinguishedSquare`, over a base which is quasi-compact,
quasi-separated and of finite type over `Spec ℤ`; quasi-compactness and quasi-separatedness are
the standing assumptions under which the source defines compactifications.

## References

* [Stacks Project, Tag 0F4D](https://stacks.math.columbia.edu/tag/0F4D)
* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
* [Stacks Project, Tag 0F4C](https://stacks.math.columbia.edu/tag/0F4C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- A dense range composed into an open embedding: if `g ∘ k` has dense range and `g` is an open
embedding, then `k` has dense range. -/
private theorem denseRange_of_comp_isOpenEmbedding {α β γ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [TopologicalSpace γ] {k : α → β} {g : β → γ}
    (hg : Topology.IsOpenEmbedding g) (h : DenseRange (g ∘ k)) : DenseRange k := by
  have hd := h.preimage hg.isOpenMap
  rwa [Set.range_comp, Set.preimage_image_eq _ hg.injective] at hd

/-- **Nagata's compactification theorem over a base of finite type over `Spec ℤ`.** Let `Y` be a
quasi-compact and quasi-separated algebraic space of finite type over `Spec ℤ`, and let
`f : X ⟶ Y` be separated and of finite type. Then `f` has a compactification.

Stacks 0F4B is the hypothesis `h0F4B`. -/
theorem hasCompactification_of_isFiniteType_viewOverIntegers (hZ : B.Contains (⊤_ Scheme.{u}))
    (h0F4B : ∀ {U Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U),
      IsAlgebraicSpace B S hS Y → IsQuasiCompactSpace B S hS Y →
      IsAbsolutelyQuasiSeparated B S hS hZ Y →
      IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from (viewOverIntegers B S hS hZ Y)) →
      ∀ p : U ⟶ Y, IsSeparated B S hS p → IsFiniteType B S hS p →
      ∀ (U₂ : Subfunctor U) {U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f₁ : U₁ ⟶ U),
        IsElementaryDistinguishedSquare B S hS hU U₂ f₁ →
        HasCompactification B S hS (f₁ ≫ p) → HasCompactification B S hS (U₂.ι ≫ p) →
        (letI := pointTopology B S hS U
         DenseRange (pointsMap B S hS (pullback f₁ U₂.ι) (pullback.fst f₁ U₂.ι ≫ f₁))) →
        HasCompactification B S hS p)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hYft : IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from (viewOverIntegers B S hS hZ Y)))
    (f : X ⟶ Y) (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) :
    HasCompactification B S hS f := by
  classical
  have hXN : IsNoetherian B S hS hZ X :=
    isNoetherian_of_isFiniteType_of_isQuasiSeparated hZ hX hY f hft
      (isQuasiSeparated_of_isSeparated B S hS hsep)
      (isNoetherian_of_isFiniteType_viewOverIntegers B S hS hZ _ hY hYqs hYft)
  -- A dense open affine with a compactification.
  obtain ⟨D, u, -, hu, hdense, hDc⟩ := exists_dense_affine_openImmersion_hasCompactification hZ
    hX hXN hY hYqc hYqs hYft f hft.1
  have : Mono u := mono_of_isOpenImmersion B S hS u hu
  let U₀ := Subfunctor.range u
  have hU₀ : IsOpenSubspace B S hS U₀ :=
    isOpenSubspace_range_of_isOpenImmersion_of_isAlgebraicSpace B S hS u
      (isAlgebraicSpace_yoneda B S hS D) hu
  have hU₀c : HasCompactification B S hS (U₀.ι ≫ f) := by
    have e : (asIso (Subfunctor.toRange u)).inv ≫ u = U₀.ι :=
      (Iso.inv_comp_eq _).2 (Subfunctor.toRange_ι _).symm
    rw [← e, Category.assoc]
    exact HasCompactification.isIso_comp _ hDc
  -- A maximal compactifiable open subspace.
  obtain ⟨U, hU, hU₀U, hUc, hmax⟩ :=
    exists_maximal_isOpenSubspace_hasCompactification hZ hX hXN f U₀ hU₀ hU₀c
  by_cases htop : U = ⊤
  · subst htop
    have h := HasCompactification.isIso_comp (inv (⊤ : Subfunctor X).ι) hUc
    rwa [IsIso.inv_hom_id_assoc] at h
  exfalso
  have hUdense : DenseRange (pointsMap B S hS U.toFunctor U.ι) := by
    have hfac : (Subfunctor.toRange u ≫ Subfunctor.homOfLe hU₀U) ≫ U.ι = u := by
      rw [Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι]
    refine hdense.mono ?_
    rintro _ ⟨x, rfl⟩
    rw [← hfac, pointsMap_comp]
    exact ⟨_, rfl⟩
  -- Stacks 0F4C.
  obtain ⟨V, W, hW, hUW, f', hV, hét, -, hEDS, hdense'⟩ :=
    exists_affine_etale_isElementaryDistinguishedSquare B S hS hZ X hX hXN U hU htop hUdense
  refine hmax W hW hUW ?_
  let k : U.toFunctor ⟶ W.toFunctor := Subfunctor.homOfLe hUW.le
  have hk : k ≫ W.ι = U.ι := Subfunctor.homOfLe_ι _
  have : Mono k := mono_of_mono_fac hk
  let U₂ := Subfunctor.range k
  have hWlft : IsLocallyOfFiniteType B S hS W.ι :=
    isLocallyOfFiniteType_of_isImmersion B S hS W.ι (isImmersion_of_isOpenImmersion B S hS hW.2)
  have hpsep : IsSeparated B S hS (W.ι ≫ f) :=
    isSeparated_comp B S hS _ _
      (isSeparated_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hW.2)) hsep
  have hpft : IsFiniteType B S hS (W.ι ≫ f) :=
    isFiniteType_comp' B S hS W.ι f hX hY
      ⟨hWlft, isQuasiCompact_ι_of_isNoetherian B S hS hZ hX hXN hW⟩ hft
  refine h0F4B hW.1 hY hYqc hYqs hYft (W.ι ≫ f) hpsep hpft U₂ f' hEDS ?_ ?_ ?_
  · -- The affine étale chart is compactifiable over `Y`.
    have hlft : IsLocallyOfFiniteType B S hS ((f' ≫ W.ι) ≫ f) :=
      isLocallyOfFiniteType_comp' B S hS _ f hX hY (isLocallyOfFiniteType_of_isEtale' B S hS _ hét)
        hft.1
    rw [Category.assoc] at hlft
    exact hasCompactification_yoneda_of_isLocallyOfFiniteType hZ hY hYqc hYqs hYft V hV
      _ hlft
  · -- The open `U` is compactifiable over `Y`.
    have e : (asIso (Subfunctor.toRange k)).inv ≫ k = U₂.ι :=
      (Iso.inv_comp_eq _).2 (Subfunctor.toRange_ι _).symm
    rw [← e, Category.assoc, ← Category.assoc k, hk]
    exact HasCompactification.isIso_comp _ hUc
  · -- The overlap has dense image in `W`.
    have hcond : pullback.snd U.ι (f' ≫ W.ι) ≫ f' =
        (pullback.fst U.ι (f' ≫ W.ι) ≫ Subfunctor.toRange k) ≫ U₂.ι := by
      rw [Category.assoc, Subfunctor.toRange_ι]
      apply (cancel_mono W.ι).1
      rw [Category.assoc, Category.assoc, hk, pullback.condition]
    let φ : pullback U.ι (f' ≫ W.ι) ⟶ pullback f' U₂.ι :=
      pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ Subfunctor.toRange k) hcond
    have hφ : φ ≫ pullback.fst f' U₂.ι ≫ f' = pullback.fst U.ι (f' ≫ W.ι) ≫ k := by
      rw [pullback.condition, ← Category.assoc, pullback.lift_snd, Category.assoc,
        Subfunctor.toRange_ι]
    have hkdense : DenseRange (pointsMap B S hS U.toFunctor k) := by
      refine denseRange_of_comp_isOpenEmbedding (isOpenEmbedding_pointsMap B S hS W.ι hW.2) ?_
      rwa [← pointsMap_comp, hk]
    have hcomp : DenseRange (pointsMap B S hS _ (pullback.fst U.ι (f' ≫ W.ι) ≫ k)) := by
      rw [pointsMap_comp]
      exact hkdense.comp hdense' (continuous_pointsMap B S hS k)
    refine hcomp.mono ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨pointsMap B S hS _ φ x, ?_⟩
    rw [← hφ, pointsMap_comp B S hS _ φ]
    rfl

end AlgebraicGeometry.Space

end
