module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Compat
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bridge
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InvertibleCap

/-!
# Pushing a family of Chern class cap products forward along a proper morphism

Let `π₁ : P₁ ⟶ W` and `π₂ : P₂ ⟶ X` be flat of relative dimension `n`, with invertible modules
`L₁` on `P₁` and `L₂` on `P₂`, and let `i : W ⟶ X` and `i' : P₁ ⟶ P₂` be proper morphisms with
`i' ≫ π₂ = π₁ ≫ i` and `L₁ ≅ i'^* L₂`. If `i'_* π₁^* = π₂^* i_*` on Chow groups
([Stacks, Tag 02RG]) then the summands `c₁(L)^j ∩ π^*(-)` of the relation of [Stacks, Tag 02U6]
commute with pushforward ([Stacks, Tag 02SU]), so a family of Chern class cap products over `W`
pushes forward to one over `X`. Two instances are recorded: an isomorphism `P₁ ≅ P₂` over the same
base, and the inverse image `π^{-1}(W) ⟶ P` of a closed subscheme `W ⊆ X`.

## Main results

* `Stacks.Chow.GenuineChern.chernTermsCompatibleWithPushforward_of_isProper` — the
  compatibility of the summands, in the form `Stacks.Chow.properPushforward_isChernCapFamily`
  consumes.
* `Stacks.Chow.GenuineChern.properChowPushforward_bundlePullback_of_isIso` — the input for an
  isomorphism of bundles over the same base.

## References

* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-- Powers of the cap of two isomorphic invertible modules agree. -/
theorem capPow_invCap_congr {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    {L N : P.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property N]
    (e : L ≅ N) (s : ℕ) (a m : ℤ) (h : a = m + s) (x : chowGroup C sP a) :
    capPow C sP (invCap C sP L) s a m h x = capPow C sP (invCap C sP N) s a m h x :=
  (capPow_comm C sP (invCap C sP N) sP (invCap C sP L) (fun d ↦ AddMonoidHom.id _)
    (fun d y ↦ by
      obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
      simp only [AddMonoidHom.id_apply, invCap_capOnChow_mk]
      exact firstChernClassCapOfInvertible_congr C sP d L N e α) s a m h x)

variable {W X P₁ P₂ : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sP₁ : P₁ ⟶ C.S) [LocallyOfFiniteType sP₁] (sP₂ : P₂ ⟶ C.S)
  [LocallyOfFiniteType sP₂] (π₁ : P₁ ⟶ W) [LocallyOfFiniteType π₁] [Flat π₁]
  (hs₁ : π₁ ≫ sW = sP₁) (π₂ : P₂ ⟶ X) [LocallyOfFiniteType π₂] [Flat π₂] (hs₂ : π₂ ≫ sX = sP₂)
  (n : ℕ) (hπ₁ : AlgebraicGeometry.RelativeDimension π₁ n)
  (hπ₂ : AlgebraicGeometry.RelativeDimension π₂ n)
  (hfac₁ : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP₁ sW π₁ hs₁ (n + 1 - 1) hπ₁ k)
  (hfac₂ : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP₂ sX π₂ hs₂ (n + 1 - 1) hπ₂ k)
  (i : W ⟶ X) [IsProper i] (hi : i ≫ sX = sW)
  (i' : P₁ ⟶ P₂) [IsProper i'] (hi' : i' ≫ sP₂ = sP₁)
  (L₁ : P₁.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible P₁.sheaf.obj P₁.ringCatSheaf.property L₁]
  (L₂ : P₂.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible P₂.sheaf.obj P₂.ringCatSheaf.property L₂]

/-- **The summands of the relation of Stacks 02U6 commute with pushforward along a proper
morphism of bundles**, granted Stacks 02RG for the square, `i'_* π₁^* = π₂^* i_*`, and the
compatibility `L₁ ≅ i'^* L₂` of the twists (Stacks 02SU). -/
theorem chernTermsCompatibleWithPushforward_of_isProper
    (eL : L₁ ≅ (Scheme.Modules.pullback i').obj L₂)
    (hPB : ∀ (k : ℤ) (y : chowGroup C sW k),
      properChowPushforward C sP₁ sP₂ i' hi' (k + n)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP₁ sP₂ i' hi' _)
          (bundlePullback C sW sP₁ π₁ hs₁ n hπ₁ k y) =
        bundlePullback C sX sP₂ π₂ hs₂ n hπ₂ k
          (properChowPushforward C sW sX i hi k
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sW sX i hi k) y)) :
    ChernTermsCompatibleWithPushforward C sW sX sP₁ sP₂ π₁ hs₁ π₂ hs₂ (n + 1) hπ₁ hπ₂ hfac₁ hfac₂
      (invCap C sP₁ L₁) (invCap C sP₂ L₂) i hi i' hi' := by
  have := isInvertible_presheaf_modulePullback L₂ i'
  intro k j hj x
  rw [projectiveBundleChernTerm_eq_bundleTerm, projectiveBundleChernTerm_eq_bundleTerm,
    ← properChowPushforward_chowGroupCast]
  congr 1
  simp only [bundleTerm, AddMonoidHom.comp_apply]
  rw [capPow_invCap_congr C sP₁ eL, properChowPushforward_capPow, hPB,
    properChowPushforward_chowGroupCast]

/-- **Stacks 02RG for an isomorphism of bundles over the same base, on Chow groups.** If
`ψ : P₁ ⟶ P₂` is an isomorphism with `ψ ≫ π₂ = π₁`, then `ψ_* π₁^* = π₂^*`. -/
theorem properChowPushforward_bundlePullback_of_isIso {Q₁ Q₂ : Scheme.{u}} (sQ₁ : Q₁ ⟶ C.S)
    [LocallyOfFiniteType sQ₁] (sQ₂ : Q₂ ⟶ C.S) [LocallyOfFiniteType sQ₂] (ρ₁ : Q₁ ⟶ W)
    [LocallyOfFiniteType ρ₁] [Flat ρ₁] (hr₁ : ρ₁ ≫ sW = sQ₁) (ρ₂ : Q₂ ⟶ W)
    [LocallyOfFiniteType ρ₂] [Flat ρ₂] (hr₂ : ρ₂ ≫ sW = sQ₂) (m : ℕ)
    (hρ₁ : AlgebraicGeometry.RelativeDimension ρ₁ m)
    (hρ₂ : AlgebraicGeometry.RelativeDimension ρ₂ m) (ψ : Q₁ ⟶ Q₂) [IsIso ψ]
    (hψ : ψ ≫ ρ₂ = ρ₁) (hψs : ψ ≫ sQ₂ = sQ₁) (k : ℤ) (y : chowGroup C sW k) :
    properChowPushforward C sQ₁ sQ₂ ψ hψs (k + m)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sQ₁ sQ₂ ψ hψs _)
        (bundlePullback C sW sQ₁ ρ₁ hr₁ m hρ₁ k y) =
      bundlePullback C sW sQ₂ ρ₂ hr₂ m hρ₂ k y := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
  rw [bundlePullback_mk, properChowPushforward_mk, bundlePullback_mk]
  have h := flatPullback_properPushforward_of_isIso C sW sQ₁ sW sQ₂ (𝟙 W) (Category.id_comp sW)
    ψ hψs ρ₁ hr₁ ρ₂ hr₂ (by rw [Category.comp_id, hψ]) m hρ₁ hρ₂ k z
  rw [properPushforward_id] at h
  exact congrArg _ h.symm

end Stacks.Chow.GenuineChern

end
