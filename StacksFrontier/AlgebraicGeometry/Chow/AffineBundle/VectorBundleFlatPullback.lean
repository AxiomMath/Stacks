module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Completion.Divisor
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PushforwardShiftsSummandsOfDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.ChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.LocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleChowBijective

/-!
# Flat pullback along a vector bundle is an isomorphism on Chow groups

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `ℰ` be a finite locally free `𝒪_X`-module of rank `r` and let
`p : E = Spec_X(Sym(ℰ)) ⟶ X` be its vector bundle. This file proves [Stacks, Tag 02TY]:

  `p^* : A_k(X) ⟶ A_{k+r}(E)`

is an isomorphism for every `k`.

The bijectivity is `Stacks.Chow.flatPullbackChow_bijective_vectorBundleToBase`; this file
restates it for `Stacks.Chow.flatPullbackChow`, and identifies the restriction to an open of the
zeroth summand of the projective space bundle map with a flat pullback (Stacks 02RD).

## Main results

* `Stacks.Chow.chowGroupOpensRestrictOfIsOpenImmersion_completionPullbackTerm`: the restriction to
  an open `V ⊆ P` of the zeroth summand of the projective space bundle map is the flat pullback
  along `V ⟶ X`.
* `Stacks.Chow.flatPullbackChow_bijective_vectorBundleToBase_factorsGeneral`: flat pullback along a
  vector bundle of any rank is bijective on Chow groups.

## References

* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.ProjectiveCompletion

universe u

namespace Stacks.Chow

/-! ### The zeroth summand restricted to an open is a flat pullback -/

/-- **The restriction of `π^*` to an open is the flat pullback along the open.** For `π : P ⟶ X`
flat of relative dimension `r` and an open `V ⊆ P` on which `π` has relative dimension `r`, the
zeroth summand `Stacks.Chow.completionPullbackTerm` of the projective space bundle map of `P`,
followed by the restriction to `V`, is the flat pullback along `V ⟶ X`: this is Stacks 02RD for
`V ⟶ P ⟶ X`. -/
theorem chowGroupOpensRestrictOfIsOpenImmersion_completionPullbackTerm (C : ChowSituation.{u})
    {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sX = sP)
    (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r + 1 - 1))
    (hfac : ∀ k : ℤ,
      FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r + 1 - 1) hπ k)
    (twist : ChernCapOperator C sP) (V : P.Opens) (hbase : (V.ι ≫ π) ≫ sX = V.ι ≫ sP)
    (hV : AlgebraicGeometry.RelativeDimension (V.ι ≫ π) r) (k : ℤ)
    (hfacV : FlatPullbackFactorsThroughRationalEquivalence C (V.ι ≫ sP) sX (V.ι ≫ π) hbase r hV
      k)
    (α : chowGroup C sX k) :
    chowGroupOpensRestrictOfIsOpenImmersion C sP V (k + ((r : ℕ) : ℤ))
        (completionPullbackTerm C sX sP π hsP r hπ hfac twist (k + ((r + 1 : ℕ) : ℤ))
          (k + ((r : ℕ) : ℤ)) k (by omega) (by simp) α) =
      flatPullbackChow C (V.ι ≫ sP) sX (V.ι ≫ π) hbase r hV k hfacV α := by
  apply eq_of_heq
  have hres : ∀ {a b : ℤ} (_ : a = b) {x : chowGroup C sP a} {y : chowGroup C sP b}, x ≍ y →
      chowGroupOpensRestrictOfIsOpenImmersion C sP V a x ≍
        chowGroupOpensRestrictOfIsOpenImmersion C sP V b y := by
    rintro a _ rfl x _ hxy
    rw [eq_of_heq hxy]
  have hk : k = k + ((r + 1 : ℕ) : ℤ) - ((r + 1 - 0 : ℕ) : ℤ) := by omega
  -- the zeroth summand is the flat pullback along `π`
  have h1 : completionPullbackTerm C sX sP π hsP r hπ hfac twist (k + ((r + 1 : ℕ) : ℤ))
        (k + ((r : ℕ) : ℤ)) k (by omega) (by simp) α ≍
      flatPullbackChow C sP sX π hsP (r + 1 - 1) hπ _ (hfac _) (chowGroupCast C sX hk α) := by
    simp only [completionPullbackTerm, completionTerm, AddMonoidHom.coe_comp,
      Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
    exact (chowGroupCast_heq C sP _ _).trans <|
      (heq_of_eq (projectiveBundleChernTerm_zero C sX sP π hsP (r + 1) hπ hfac twist
        (k + ((r + 1 : ℕ) : ℤ)) (Nat.zero_le _) _)).trans (chowGroupCast_heq C sP _ _)
  -- restriction to an open of a flat pullback along `π` is the flat pullback along `V ⟶ X`
  have h3 : ∀ (m : ℤ) (β : chowGroup C sX m),
      chowGroupOpensRestrictOfIsOpenImmersion C sP V (m + ((r + 1 - 1 : ℕ) : ℤ))
          (flatPullbackChow C sP sX π hsP (r + 1 - 1) hπ m (hfac m) β) =
        flatPullbackChow C (V.ι ≫ sP) sX (V.ι ≫ π) hbase (r + 1 - 1) hV m
          (flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ hbase _ hV m) β := by
    intro m β
    have heq : ∀ x, chowGroupOpensRestrictOfIsOpenImmersion C sP V
        (m + ((r + 1 - 1 : ℕ) : ℤ)) x = chowGroupRestrict C sP (V.ι ≫ sP) V.ι rfl _ x := by
      intro x
      obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
      rfl
    exact (heq _).trans (chowGroupRestrict_bundlePullback C sX sP π hsP (r + 1 - 1) hπ V hV m β)
  refine (hres (by omega) h1).trans ?_
  refine (heq_of_eq (h3 _ _)).trans ?_
  exact flatPullbackChow_heq_congr C _ sX _ _ hbase hbase rfl (by omega) hV hV hk.symm _ _ _ _
    (chowGroupCast_heq C sX hk α)

/-! ### Stacks 02TY -/

/-- **Stacks 02TY.** Let `X` be locally of finite type over the base of chapter 42, let `ℰ` be a
finite locally free `𝒪_X`-module of rank `r` and let `p : Spec_X(Sym(ℰ)) ⟶ X` be its vector
bundle. Then flat pullback `p^* : A_k(X) ⟶ A_{k+r}(Spec_X(Sym(ℰ)))` is bijective for every `k`.

This is `Stacks.Chow.flatPullbackChow_bijective_vectorBundleToBase`, stated with the flat
pullback `Stacks.Chow.flatPullbackChow` and without the instance `[E.IsQuasicoherent]`, which a
finite locally free module satisfies
(`Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree`). -/
@[stacks 02TY]
theorem flatPullbackChow_bijective_vectorBundleToBase_factorsGeneral (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
    letI _ := locallyOfFiniteType_vectorBundleToBase E r
    letI _ := flat_vectorBundleToBase E r
    Function.Bijective (flatPullbackChow C
      (Scheme.Modules.vectorBundleToBase X E ≫ sX) sX
      (Scheme.Modules.vectorBundleToBase X E) rfl r
      (relativeDimension_vectorBundleToBase E r) k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl r _ k)) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  exact flatPullbackChow_bijective_vectorBundleToBase C sX E r k

end Stacks.Chow

end
