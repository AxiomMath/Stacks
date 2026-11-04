module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.CharacterTorsorStagePoint
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleStageDescent

/-!
# The `μ_n`-torsor of a character over the geometric base, and its rigidity

Let `T_χ ⟶ Y` be the torsor cover of a character `χ : V → ℤ/n` of an open subgroup of
`π₁(X, x)` (`AlgebraicGeometry.CharacterTorsorData`). Its base change to any `S ⟶ Y` over a field
`K` containing a primitive `n`-th root of unity is a `ℤ/n`-torsor scheme over `S`, hence a torsor
under `μ_n` on `S_ét` (`Stacks.Kummer.schemeTorsor`). For `S = Y_K`, `K/k'` an algebraic
extension of the field of definition `k'` of `Y`, two characters with isomorphic torsors agree on
every element of `V` in the geometric fundamental group: the isomorphism gives an equivariant
morphism of the base changes to `Y_K`, which descends to a finite stage `Y_E`
(`AlgebraicGeometry.exists_stage_hom_of_baseChange`), and rigidity at a point of `Y_E` fixed by
the geometric fundamental group concludes.

## Main definitions

* `AlgebraicGeometry.CharacterTorsorData.baseTorsor`: the `μ_n`-torsor over `S`.

## Main results

* `AlgebraicGeometry.CharacterTorsorData.eq_of_baseTorsor_eq`: the rigidity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Kummer Stacks.Cohomology.Torsors

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [ConnectedSpace X] {x : GeometricPoint X} {n : ℕ} [NeZero n]
  {V : Subgroup (EtaleFundamentalGroup X x)} {Y : FiniteEtaleOver X}
  {eY : (finiteEtaleFiberFunctor x).obj Y ≃ EtaleFundamentalGroup X x ⧸ V}
  {χ : V → ZMod n} {hadd : ∀ a b, χ (a * b) = χ a + χ b}

namespace CharacterTorsorData

variable (D : CharacterTorsorData x χ hadd Y eY)

/-- The torsor cover as a finite étale cover of `Y`. -/
abbrev overY : FiniteEtaleOver Y.left :=
  MorphismProperty.Over.mk ⊤ D.q.left (finiteEtale_left_of_hom D.q)

/-- The translations as morphisms of finite étale covers of `Y`. -/
abbrev τY (a : ZMod n) : D.overY ⟶ D.overY :=
  MorphismProperty.Over.homMk (D.τ a).left (translation_left_comp D.q D.τ D.τ_q a)

omit [NeZero n] in
/-- The base change along `g : Z ⟶ Y` of the translation `D.τY a` is the translation `D.τZ g a`
of `T_χ ×_Y Z`. -/
theorem baseChange_map_τY_left {Z : Scheme.{u}} (g : Z ⟶ Y.left) (a : ZMod n) :
    ((finiteEtaleBaseChange g).map (D.τY a)).left = D.τZ g a := by
  apply pullback.hom_ext
  · exact (finiteEtaleBaseChange_map_left_fst g (D.τY a)).trans
      (baseChangeTranslation_fst D.q.left g (fun a => (D.τ a).left)
        (translation_left_comp D.q D.τ D.τ_q) a).symm
  · exact (MorphismProperty.Over.w ((finiteEtaleBaseChange g).map (D.τY a))).trans
      (baseChangeTranslation_snd D.q.left g (fun a => (D.τ a).left)
        (translation_left_comp D.q D.τ D.τ_q) a).symm

omit [NeZero n] in
/-- The translation by `0` of `T_χ ×_Y Z` is the identity. -/
theorem τZ_zero {Z : Scheme.{u}} (g : Z ⟶ Y.left) : D.τZ g 0 = 𝟙 _ :=
  baseChangeTranslation_zero _ _ _ _ (by rw [D.τ_zero]; rfl)

omit [NeZero n] in
/-- The translation by `a + b` of `T_χ ×_Y Z` is the composite of the translations by `a` and by
`b`. -/
theorem τZ_add {Z : Scheme.{u}} (g : Z ⟶ Y.left) (a b : ZMod n) :
    D.τZ g (a + b) = D.τZ g a ≫ D.τZ g b :=
  baseChangeTranslation_add _ _ _ _ (fun a b => by
    rw [D.τ_add, MorphismProperty.Comma.comp_left]) a b

/-- The translations of `T_χ ×_Y Z` form a free action of `ℤ/n`. -/
theorem isFreeTranslation_τZ {Z : Scheme.{u}} (g : Z ⟶ Y.left) : IsFreeTranslation (D.τZ g) :=
  isFreeTranslation_baseChange _ _ _ _
    (isFreeTranslation_of_isIso _ _ D.isIso_torsorComparison)

/-- The translations of `T_χ ×_Y Z` act locally transitively on the fibres of the projection
`T_χ ×_Y Z ⟶ Z`. -/
theorem isLocallyTransitive_τZ {Z : Scheme.{u}} (g : Z ⟶ Y.left) :
    IsLocallyTransitive (D.τZ g) (pullback.snd D.q.left g) :=
  isLocallyTransitive_baseChange _ _ _ _
    (isLocallyTransitive_of_isIso _ _ D.isIso_torsorComparison)

/-- The projection `T_χ ×_Y Z ⟶ Z` is étale. -/
instance etale_snd {Z : Scheme.{u}} (g : Z ⟶ Y.left) : Etale (pullback.snd D.q.left g) :=
  haveI : Etale D.q.left := (finiteEtale_left_of_hom D.q).2
  inferInstance

omit [NeZero n] in
/-- For `Y` connected, the projection `T_χ ×_Y Z ⟶ Z` is surjective. -/
theorem surjective_snd [ConnectedSpace Y.left] {Z : Scheme.{u}} (g : Z ⟶ Y.left) :
    Surjective (pullback.snd D.q.left g) :=
  have : Surjective D.q.left := ⟨D.surjective_q⟩
  inferInstance

variable {K : Type u} [Field K] [DecidableEq K] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
  {S : Scheme.{u}} (fS : S ⟶ Spec (.of K)) (π : S ⟶ Y.left) [ConnectedSpace Y.left]

/-- **The `μ_n`-torsor over `S` of the torsor cover of a character**: the sheaf of sections of the
base change `T_χ ×_Y S`. -/
def baseTorsor : AbelianTorsor (rootsOfUnitySheaf.{u, 0} S n) :=
  haveI := D.surjective_snd π
  schemeTorsor fS hζ (pullback.snd D.q.left π) (D.τZ π)
    (fun a => baseChangeTranslation_snd _ _ _ _ a) (D.τZ_zero π) (D.τZ_add π)
    (D.isFreeTranslation_τZ π) (D.isLocallyTransitive_τZ π)

end CharacterTorsorData

open CharacterTorsorData

variable {k : Type u} [Field k] [Fintype k] (f : X ⟶ Spec (.of k))
  (heY : ∀ (σ : EtaleFundamentalGroup X x) y, eY (σ • y) = σ • eY y)
  {K₀ : Type u} [Field K₀] [Algebra k K₀] [Module.Finite k K₀] (r : Y.left ⟶ Spec (.of K₀))
  (hr : r ≫ Spec.map (CommRingCat.ofHom (algebraMap k K₀)) = Y.hom ≫ f)
  {K : Type u} [Field K] [DecidableEq K] [Algebra K₀ K] [Algebra.IsAlgebraic K₀ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ n)
  [ConnectedSpace Y.left] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]

include heY hr in
/-- **Characters with isomorphic torsors over the geometric base agree on the geometric
fundamental group.** -/
theorem CharacterTorsorData.eq_of_baseTorsor_eq {χ₁ χ₂ : V → ZMod n}
    {hadd₁ : ∀ a b, χ₁ (a * b) = χ₁ a + χ₁ b} {hadd₂ : ∀ a b, χ₂ (a * b) = χ₂ a + χ₂ b}
    (D₁ : CharacterTorsorData x χ₁ hadd₁ Y eY) (D₂ : CharacterTorsorData x χ₂ hadd₂ Y eY)
    (h : Quotient.mk (torsorSetoid (rootsOfUnitySheaf.{u, 0} _ n))
        (D₁.baseTorsor hζ (pullback.snd r (spectrumMap K₀ K)) (pullback.fst r (spectrumMap K₀ K))) =
      Quotient.mk (torsorSetoid (rootsOfUnitySheaf.{u, 0} _ n))
        (D₂.baseTorsor hζ (pullback.snd r (spectrumMap K₀ K)) (pullback.fst r (spectrumMap K₀ K))))
    (v : V) (hv : etaleFundamentalGroupMap f x (v : EtaleFundamentalGroup X x) = 1) :
    χ₁ v = χ₂ v := by
  set π := pullback.fst r (spectrumMap K₀ K)
  have := D₁.surjective_snd π
  have := D₂.surjective_snd π
  obtain ⟨φ, hφ, hφτ⟩ := exists_hom_of_schemeTorsor_eq (pullback.snd r (spectrumMap K₀ K)) hζ
    (pullback.snd D₁.q.left π) (pullback.snd D₂.q.left π) (D₁.τZ π) (D₂.τZ π)
    (fun a => baseChangeTranslation_snd _ _ _ _ a) (fun a => baseChangeTranslation_snd _ _ _ _ a)
    (D₁.τZ_zero π) (D₂.τZ_zero π) (D₁.τZ_add π) (D₂.τZ_add π) (D₁.isFreeTranslation_τZ π)
    (D₂.isFreeTranslation_τZ π) (D₁.isLocallyTransitive_τZ π) (D₂.isLocallyTransitive_τZ π) h
  let Φ : (finiteEtaleBaseChange π).obj D₁.overY ⟶ (finiteEtaleBaseChange π).obj D₂.overY :=
    MorphismProperty.Over.homMk φ hφ
  have hΦ : ∀ a, (finiteEtaleBaseChange π).map (D₁.τY a) ≫ Φ =
      Φ ≫ (finiteEtaleBaseChange π).map (D₂.τY a) := fun a => by
    apply MorphismProperty.Over.Hom.ext
    rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
      baseChange_map_τY_left, baseChange_map_τY_left]
    exact hφτ a
  obtain ⟨E, hE, Ψ, hΨ⟩ := exists_stage_hom_of_baseChange K₀ K r D₁.overY D₂.overY D₁.τY D₂.τY Φ hΦ
  obtain ⟨hg, e, he, hfix⟩ := exists_stagePoint f heY r hr (K := K) E
  refine D₁.eq_of_hom_baseChange D₂ _ hg Ψ.left (MorphismProperty.Over.w Ψ) (fun a => ?_) e he v
    (hfix v hv)
  have := congrArg (fun φ => φ.left) (hΨ a)
  simp only [MorphismProperty.Comma.comp_left, baseChange_map_τY_left] at this
  exact this

end AlgebraicGeometry
