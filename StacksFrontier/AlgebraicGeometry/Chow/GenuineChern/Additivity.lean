module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernBasic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts

/-!
# Additivity of the first Chern class in short exact sequences

For a short exact sequence `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of finite locally free modules of constant
ranks `a`, `a + c`, `c` on `X`, [Stacks, Tag 02UI] gives `c(ℰ) = c(ℰ₁) c(ℰ₂)`, whose degree one
part is

  `c₁(ℰ) ∩ α = c₁(ℰ₁) ∩ α + c₁(ℰ₂) ∩ α`.

This file proves that identity by the source's induction on `a`. For `a ≤ 1` it is the case of an
invertible subsheaf (Stacks 02UH, the input `Stacks.Chow.GenuineChern.SubAdditive`) or an
isomorphism. For `a ≥ 2` one passes to the projective bundle `π : P(ℰ₁) ⟶ X`, where
`π^*ℰ₁ ⟶ 𝒪(1)` is onto with kernel `ℱ` of rank `a - 1`; with `𝒬 = π^*ℰ/ℱ` there are short exact
sequences `0 ⟶ ℱ ⟶ π^*ℰ ⟶ 𝒬 ⟶ 0` and `0 ⟶ 𝒪(1) ⟶ 𝒬 ⟶ π^*ℰ₂ ⟶ 0`, so the induction
hypothesis and the invertible case give the identity on `P(ℰ₁)` at `π^*α`; it descends because
`π^*` commutes with the first Chern class (`Stacks.Chow.GenuineChern.FlatCompat`) and is
injective (`Stacks.Chow.GenuineChern.TopHalf`).

The two module-theoretic inputs — an extension of finite locally free modules of ranks `a` and `c`
is finite locally free of rank `a + c`, and the two sequences above — are
`Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact` and
`Stacks.Chow.GenuineChern.exists_shortExact_pair`.

## References

* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-- **The first Chern class along an invertible subsheaf** (Stacks 02UH, degree one), for every
short exact sequence `0 ⟶ ℳ ⟶ 𝒢 ⟶ 𝒬 ⟶ 0` with `ℳ` invertible and `𝒬` of positive rank. -/
def SubAdditive : Prop :=
  ∀ ⦃X : Scheme.{u}⦄ (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (S : ShortComplex X.Modules)
    (_ : S.ShortExact) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ 1]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (r + 1 + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ (r + 1)]
    (k : ℤ) (α : chowGroup C sX k),
    firstChern S.X₂ C sX (r + 1 + 1) k α =
      firstChern S.X₃ C sX (r + 1) k α + firstChern S.X₁ C sX 1 k α

variable {C}

/-- Transport of a rank along an isomorphism of modules and an equality of ranks. -/
theorem rank_of_iso {X : Scheme.{u}} {E E' : X.Modules} {r r' : ℕ} (e : E ≅ E') (h : r = r')
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r' :=
  by subst h; exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e hE

/-- `firstChern` evaluated at two rank instances of two isomorphic modules. -/
theorem firstChern_iso (HF : FlatCompat C) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {E E' : X.Modules} {r r' : ℕ} (e : E' ≅ E) (h : r' = r)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r)
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r') (k : ℤ)
    (α : chowGroup C sX k) :
    @firstChern _ E' C sX _ r' hE' k α = @firstChern _ E C sX _ r hE k α := by
  subst h
  exact firstChern_congr sX HF r' e k α

/-- **Additivity of the first Chern class** (Stacks 02UI, degree one): for a short exact sequence
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of finite locally free modules of ranks `a`, `a + c`, `c`,
`c₁(ℰ) ∩ α = c₁(ℰ₁) ∩ α + c₁(ℰ₂) ∩ α`. -/
theorem firstChern_add_of_shortExact (H : TopHalf C) (HF : FlatCompat C) (HS : SubAdditive C)
    (a : ℕ) : ∀ ⦃X : Scheme.{u}⦄ (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (S : ShortComplex X.Modules) (_ : S.ShortExact) (c : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ a]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (a + c)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ c]
    (k : ℤ) (α : chowGroup C sX k),
    firstChern S.X₂ C sX (a + c) k α = firstChern S.X₁ C sX a k α + firstChern S.X₃ C sX c k α := by
  induction a with
  | zero =>
    intro X sX _ S hS c h₁ h₂ h₃ k α
    have hz : IsZero S.X₁ := Stacks.WeilCohomology.isZero_of_isFiniteLocallyFreeOfRank_zero _ h₁
    have : IsIso S.g := hS.isIso_g_iff.2 hz
    have h0 : firstChern S.X₁ C sX 0 k α = 0 := rfl
    rw [h0, zero_add (firstChern S.X₃ C sX c k α)]
    exact firstChern_iso HF sX (asIso S.g) (by omega) h₃ h₂ k α
  | succ a ih =>
    intro X sX _ S hS c h₁ h₂ h₃ k α
    rcases c with _ | c
    · -- the quotient vanishes and `ℰ₁ ⟶ ℰ` is an isomorphism
      have hz : IsZero S.X₃ := Stacks.WeilCohomology.isZero_of_isFiniteLocallyFreeOfRank_zero _ h₃
      have : IsIso S.f := hS.isIso_f_iff.2 hz
      have h0 : firstChern S.X₃ C sX 0 k α = 0 := rfl
      rw [h0, add_zero (firstChern S.X₁ C sX (a + 1) k α)]
      exact firstChern_iso HF sX (asIso S.f).symm (by omega) h₁ h₂ k α
    rcases a with _ | m
    · -- an invertible subsheaf: Stacks 02UH
      have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂
          (c + 1 + 1) := rank_of_iso (Iso.refl _) (by omega) h₂
      have := firstChern_rank_congr sX S.X₂ (show 0 + 1 + (c + 1) = c + 1 + 1 by omega) k
      rw [this, HS sX S hS c k α, add_comm (firstChern S.X₃ C sX (c + 1) k α)]
    · -- the splitting step on the projective bundle of `ℰ₁`
      have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁ :=
        isFiniteLocallyFree_of_rank S.X₁ (m + 1 + 1)
      have := flat_bundleProj S.X₁ (m + 1)
      have := locallyOfFiniteType_bundleProj S.X₁ (m + 1)
      have : S.X₁.IsQuasicoherent :=
        Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree S.X₁
      have hd := relativeDimension_bundleProj S.X₁ (m + 1)
      -- the tautological sequence `0 ⟶ ℱ ⟶ π^*ℰ₁ ⟶ 𝒪(1) ⟶ 0`
      let τ : (Scheme.Modules.pullback (bundleProj S.X₁)).obj S.X₁ ⟶ bundleTwist S.X₁ :=
        Stacks.ProjectiveBundleSplitting.tautologicalMap S.X₁ (bundlePieces S.X₁)
      have hτ : Epi τ :=
        Stacks.ProjectiveBundleSplitting.epi_tautologicalMap S.X₁ (bundlePieces S.X₁)
      have hL : AlgebraicGeometry.SheafOfModules.IsInvertible (bundle S.X₁).presheaf
          (bundle S.X₁).ringCatSheaf.2 (bundleTwist S.X₁) := isInvertible_bundleTwist S.X₁
      have hπ : ∀ (E : X.Modules) (r : ℕ)
          [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r],
          AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((Scheme.Modules.pullback (bundleProj S.X₁)).obj E) r :=
        fun E r _ => isFiniteLocallyFreeOfRank_pullback _ E r
      have hπA := hπ S.X₁ (m + 1 + 1)
      have hK : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (kernel τ) (m + 1) :=
        Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
          τ hτ hL (m + 1) hπA
      have hO : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (bundleTwist S.X₁) 1 := by
        have : AlgebraicGeometry.SheafOfModules.IsInvertible (bundle S.X₁).sheaf.obj
            (bundle S.X₁).ringCatSheaf.property (bundleTwist S.X₁) := hL
        exact isFiniteLocallyFreeOfRank_one_of_isInvertible _
      let T1 : ShortComplex (bundle S.X₁).Modules :=
        ShortComplex.mk (kernel.ι τ) τ (kernel.condition τ)
      have hT1 : T1.ShortExact := { exact := ShortComplex.exact_kernel τ }
      -- the pulled-back sequence and the two sequences of the step
      have hS' : (S.map (Scheme.Modules.pullback (bundleProj S.X₁))).ShortExact :=
        shortExact_map_pullback _ S hS
      obtain ⟨T2, T3, hT2, hT3, ⟨e21⟩, ⟨e22⟩, ⟨e23⟩, ⟨e31⟩, ⟨e33⟩⟩ :=
        exists_shortExact_pair T1 _ hT1 hS' (Iso.refl _)
      have hπB := hπ S.X₂ (m + 1 + 1 + (c + 1))
      have hπC := hπ S.X₃ (c + 1)
      have e22' : T2.X₂ ≅ (Scheme.Modules.pullback (bundleProj S.X₁)).obj S.X₂ := e22
      have e33' : T3.X₃ ≅ (Scheme.Modules.pullback (bundleProj S.X₁)).obj S.X₃ := e33
      have e21' : T2.X₁ ≅ kernel τ := e21
      have e31' : T3.X₁ ≅ bundleTwist S.X₁ := e31
      have r21 := rank_of_iso e21.symm rfl hK
      have r22 := rank_of_iso e22.symm (show m + 1 + 1 + (c + 1) = m + 1 + (1 + (c + 1)) by omega)
        hπB
      have r31 := rank_of_iso e31.symm rfl hO
      have r33 := rank_of_iso e33.symm rfl hπC
      have r32 := isFiniteLocallyFreeOfRank_of_shortExact T3 hT3 1 (c + 1) r31 r33
      have r32' := rank_of_iso (Iso.refl T3.X₂) (show 1 + (c + 1) = c + 1 + 1 by omega) r32
      have r23 := rank_of_iso e23.symm rfl r32
      -- the identity on the bundle, at `β = π^*α`
      set β := flatPullbackChow C (bundleProj S.X₁ ≫ sX) sX (bundleProj S.X₁) rfl (m + 1 + 1 - 1) hd
        k (flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ hd k) α with hβ
      have e1 := @ih _ (bundleProj S.X₁ ≫ sX) _ T2 hT2 (1 + (c + 1)) r21 r22 r23 _ β
      have e2 := @HS _ (bundleProj S.X₁ ≫ sX) _ T3 hT3 c r31 r32' r33 _ β
      have e3 := @ih _ (bundleProj S.X₁ ≫ sX) _ T1 hT1 1 hK hπA hO _ β
      rw [firstChern_iso HF _ e22' (by omega) hπB r22, firstChern_iso HF _ e21' rfl hK r21,
        firstChern_iso HF _ e23 (show 1 + (c + 1) = c + 1 + 1 by omega) r32' r23, e2,
        firstChern_iso HF _ e31' rfl hO r31, firstChern_iso HF _ e33' rfl hπC r33] at e1
      have hbundle : firstChern ((Scheme.Modules.pullback (bundleProj S.X₁)).obj S.X₂) C
            (bundleProj S.X₁ ≫ sX) (m + 1 + 1 + (c + 1)) _ β =
          firstChern ((Scheme.Modules.pullback (bundleProj S.X₁)).obj S.X₁) C
              (bundleProj S.X₁ ≫ sX) (m + 1 + 1) _ β +
            firstChern ((Scheme.Modules.pullback (bundleProj S.X₁)).obj S.X₃) C
              (bundleProj S.X₁ ≫ sX) (c + 1) _ β := by
        rw [e1, e3]; abel
      -- descend along the injective pullback
      have hpull := fun (E : X.Modules) (r : ℕ)
          [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] =>
        have := hπ E r
        firstChern_flatPullback_heq sX HF (bundleProj S.X₁ ≫ sX) (bundleProj S.X₁) rfl
          (m + 1 + 1 - 1) hd E r ((Scheme.Modules.pullback (bundleProj S.X₁)).obj E) (Iso.refl _)
          k α
      have hadd : ∀ {d₁ d₂ : ℤ} (_ : d₁ = d₂) {x y : chowGroup C (bundleProj S.X₁ ≫ sX) d₁}
          {x' y' : chowGroup C (bundleProj S.X₁ ≫ sX) d₂}, x ≍ x' → y ≍ y' → x + y ≍ x' + y' := by
        intro d₁ d₂ h x y x' y' hx hy
        subst h; cases hx; cases hy; rfl
      refine pullback_injective sX S.X₁ H (m + 1) (k - 1) ?_
      simp only [projectiveBundlePullback, map_add]
      refine chowGroup_eq_of_heq C _ ((hpull S.X₂ (m + 1 + 1 + (c + 1))).symm.trans ?_)
      rw [hbundle]
      exact hadd (by omega) (hpull S.X₁ (m + 1 + 1)) (hpull S.X₃ (c + 1))

end Stacks.Chow.GenuineChern

end
