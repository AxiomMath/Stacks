module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundlePullbackIsoPositiveRank
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerChow
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bridge
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProperPushforward

/-!
# The pushforward from a divisor cut out by the twist shifts the summands

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `π : P ⟶ X` be flat
of relative dimension `r`, let `L` be an invertible module on `P` and let `s` be a global section
of `L` whose zero scheme `i : D ⟶ P` is an effective Cartier divisor, with `π_D = π ∘ i` flat of
relative dimension `r - 1`. Write `ξ = c₁(L) ∩ -` on `P` and `ξ_D = c₁(i^*L) ∩ -` on `D`. Then for
every class `α` on `X` and every `j < r`,

  `i_*(ξ_D^j ∩ π_D^* α) = ξ^{j+1} ∩ π^* α`.

This is the compatibility used in the proof of Stacks 02TY, where `P = P(ℰ ⊕ 𝒪_X)`,
`L = 𝒪_P(1)` and `D = Z(s) = P(ℰ)` is the divisor at infinity: it is the statement
`Stacks.Chow.PushforwardShiftsSummands` that the engine
`Stacks.Chow.bijective_chowGroupOpensRestrict_comp_completionPullbackTerm` consumes. The proof is
the one of the source. The case `j = 0` is Stacks 02TR, `c₁(L) ∩ π^* α = i_*(π_D^* α)`, which
applies because `D`, being an effective Cartier divisor flat over `X`, is a relative effective
Cartier divisor on `P/X`; the remaining `j` caps are moved across `i_*` by Stacks 02SU. Both are
`Stacks.Chow.properChowPushforward_bundleTerm`, stated for the summands `Stacks.Chow.bundleTerm`
of the projective space bundle map; what is done here is the passage to the summands
`Stacks.Chow.infinityTerm` and `Stacks.Chow.completionTerm`, which differ from those by
transport along equalities of degrees (`Stacks.Chow.projectiveBundleChernTerm_eq_bundleTerm`).

## Main results

* `Stacks.Chow.pushforwardShiftsSummands_zeroScheme` — `Stacks.Chow.PushforwardShiftsSummands`
  for the zero scheme of a section of `L` that is an effective Cartier divisor, flat over `X` of
  relative dimension `r - 1`, with the twists `c₁(L)` and `c₁(i^*L)`.

## Implementation notes

The zero scheme of `s` is an effective Cartier divisor exactly when `s` is a regular section
(Stacks 02OR, `Stacks.Divisors.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection`), so the
hypothesis on `s` is that it is regular.

`Stacks.Chow.PushforwardShiftsSummands` is parametrized by proofs that the two flat pullbacks
factor through rational equivalence. These are Stacks 02S1, and the statement below supplies them
from `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` rather than taking them
as hypotheses; being proofs, any other choice gives the same proposition.

## References

* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **The pushforward from the zero scheme of a section of the twist shifts the summands.** Let
`π : P ⟶ X` be flat of relative dimension `r`, let `s` be a global section of an invertible
module `L` on `P` whose zero scheme `i : D ⟶ P` is an effective Cartier divisor, and let
`π_D = π ∘ i` be flat of relative dimension `r - 1`. Then

  `i_*(c₁(i^*L)^j ∩ π_D^* α) = c₁(L)^{j+1} ∩ π^* α`

for every `j < r` and every class `α` on `X`, in the normalized degrees of
`Stacks.Chow.infinityTerm` and `Stacks.Chow.completionTerm`. By Stacks 02TR and Stacks 02SU. -/
theorem pushforwardShiftsSummands_zeroScheme (C : ChowSituation.{u}) {X P : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sX = sP) (r : ℕ)
    (hπ : AlgebraicGeometry.RelativeDimension π r) (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (hs : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme P L s))
    [Flat ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π)]
    (hπD : AlgebraicGeometry.RelativeDimension
      ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π) (r - 1))
    (n d : ℤ) (hdP : n + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) = d)
    (hdD : n + ((r - 1 : ℕ) : ℤ) - (r : ℤ) = d) :
    PushforwardShiftsSummands C sX sP ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ sP) π hsP
      ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π) (by rw [Category.assoc, hsP]) r hπ
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C sP sX π hsP _ hπ k)
      (invCap C sP L) hπD
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ _ _ hπD k)
      (invCap C _ ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme P L s).subschemeι).obj L))
      (Stacks.Divisors.zeroScheme P L s).subschemeι rfl n d hdP hdD := by
  intro j α
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by have := j.pos; omega⟩
  have hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor π
      (Stacks.Divisors.zeroScheme P L s) := ⟨hs, inferInstance⟩
  have hπ' : AlgebraicGeometry.RelativeDimension π (m + 1) := hπ
  have hq : AlgebraicGeometry.RelativeDimension
      ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π) m := hπD
  simp only [infinityTerm, completionTerm, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [projectiveBundleChernTerm_eq_bundleTerm C sX _ _ _ m hq _ _ n j.val _ α,
    projectiveBundleChernTerm_eq_bundleTerm C sX sP π hsP (m + 1) hπ' _ _ n j.succ.val _ _]
  simp only [chowGroupCast_chowGroupCast]
  set i := (Stacks.Divisors.zeroScheme P L s).subschemeι with hi
  let : AlgebraicGeometry.SheafOfModules.IsInvertible _ _
      ((Scheme.Modules.pullback i).obj L) := isInvertible_presheaf_modulePullback L i
  have key : ∀ (A B e : ℤ) (hAB : A = B + 1) {a : ℤ} (x : chowGroup C sX a)
      (e2 : a = A + (j : ℕ)) (e4 : a = B + ((j : ℕ) + 1 : ℕ)) (e1 : A + (m : ℤ) = e)
      (e3 : B + ((m + 1 : ℕ) : ℤ) = e),
      chowPushforwardOfIsClosedImmersion C (i ≫ sP) sP i rfl e
          (chowGroupCast C _ e1 (bundleTerm C sX (i ≫ sP) (i ≫ π) (by rw [Category.assoc, hsP]) m
            hq (invCap C _ ((Scheme.Modules.pullback i).obj L)) A j (chowGroupCast C sX e2 x))) =
        chowGroupCast C sP e3 (bundleTerm C sX sP π hsP (m + 1) hπ' (invCap C sP L) B
          ((j : ℕ) + 1) (chowGroupCast C sX e4 x)) := by
    intro A B e hAB a x e2 e4 e1 e3
    subst hAB e1
    have h := properChowPushforward_bundleTerm C sX sP π hsP m hπ' L s hD hq B j
      (chowGroupCast C sX e2 x)
    rw [chowGroupCast_chowGroupCast] at h
    rw [← h, properChowPushforward_chowGroupCast, chowGroupCast_chowGroupCast]
    rfl
  exact key _ _ d (by push_cast; ring) α _ _ _ _

end Stacks.Chow

end
