module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyFunctoriality
public import StacksCore.Tactic.StacksAttribute

/-!
# The base change compatibility of the constant-rank Chern classes

Let `(S, δ)` be as in [Stacks, Tag 02QL], let `X` be a scheme locally of finite type over `S` and
let `f : X' ⟶ X` be a morphism. For a finite locally free module `ℰ` on `X` of globally constant
rank `r` whose pullbacks all have rank `r`, and for `j ≤ r`, the restriction map of
[Stacks, Tag 0B7F] carries the degree-`j` Chern class of `ℰ` to that of `f^*ℰ`,

  `f^*(c_j(ℰ)) = c_j(f^*ℰ)`,

provided the two total Chern class data use the same Chern cap rule and that rule takes equal
values at isomorphic modules.

## Main definitions

* `Stacks.Chow.HigherChernCapRule.RespectsIso`: the Chern cap rule takes equal values at
  isomorphic modules of the same rank.

## Main results

* `Stacks.Chow.pullbackPreservesRank_pullback`: rank preservation ([Stacks, Tag 02U9]) passes to
  the pullback module.
* `Stacks.Chow.chowCohomologyRestriction_ch_eq`: `f^*(c_j(ℰ)) = c_j(f^*ℰ)` for `j ≤ r`, on a
  module of globally constant rank `r`.
* `Stacks.Chow.chowCohomologyRestriction_one_zero`: `f^*(1) = 1` in degree `0`.

## Implementation notes

`Stacks.Chow.HigherChernCapRule` is a family of homomorphisms indexed by a module, with no
naturality in the module, and `AlgebraicGeometry.Scheme.Modules.pullbackComp` identifies
`t^*(f^*ℰ)` with `(t ≫ f)^*ℰ` only up to isomorphism. The hypothesis
`Stacks.Chow.HigherChernCapRule.RespectsIso` relates the values of the rule at these two modules.
Its statement involves no transport: the value of the rule is a homomorphism
`A_k(T) ⟶ A_{k-j}(T)` whose type does not mention the module.

## References

* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Iso-invariance of the Chern cap rule -/

/-- **The Chern cap rule takes equal values at isomorphic modules**: for isomorphic finite locally
free modules `F ≅ F'` of rank `r` on a scheme `T` locally of finite type over `S`, the values of
`cap` at `F` and at `F'` agree in every degree. -/
def HigherChernCapRule.RespectsIso (C : ChowSituation.{u}) (r : ℕ)
    (cap : HigherChernCapRule C r) : Prop :=
  ∀ {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (F F' : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r],
    (F ≅ F') → ∀ (k : ℤ) (j : Fin (r + 1)), cap q F k j = cap q F' k j

/-! ### Rank preservation passes to a pullback -/

section Rank

variable {X X' : Scheme.{u}} (f : X' ⟶ X)

/-- If every pullback of `ℰ` has rank `r`, then so does every pullback of `f^*ℰ`. -/
theorem pullbackPreservesRank_pullback {E : X.Modules} {r : ℕ}
    (hrank : PullbackPreservesRank E r) :
    PullbackPreservesRank ((Scheme.Modules.pullback f).obj E) r := fun {_T} t =>
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Scheme.Modules.pullbackComp t f).app E).symm (hrank (t ≫ f))

end Rank

/-! ### The base change compatibility in the constant-rank range -/

section Restriction

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : X' ⟶ X) [LocallyOfFiniteType f]
  (hgys : G.IsNaturalUnderBaseChangeIso)
  {R : ChowCohomologySeriesRing C G sX} {R' : ChowCohomologySeriesRing C G (f ≫ sX)}

/-- **The base change compatibility of the total Chern class in degrees at most the rank.** For a
module `ℰ` on `X` of globally constant rank `r` whose pullbacks all have rank `r`, and for a
degree `j ≤ r`, the restriction map `f^* : A^j(X) ⟶ A^j(X')` of Stacks 0B7F carries the
degree-`j` component of the total Chern class of `ℰ` to that of `f^*ℰ`:

  `f^*(c_j(ℰ)) = c_j(f^*ℰ)`,

provided the two data use the same Chern cap rule (`hcap`) and that rule takes equal values at
isomorphic modules (`hiso`). -/
theorem chowCohomologyRestriction_ch_eq (D : TotalChernClassSeries C G sX R)
    (D' : TotalChernClassSeries C G (f ≫ sX) R') (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (hrank : PullbackPreservesRank E r)
    (hcap : (D.cap r : HigherChernCapRule C r) = (D'.cap r : HigherChernCapRule C r))
    (hiso : HigherChernCapRule.RespectsIso C r (D'.cap r : HigherChernCapRule C r))
    (j : Fin (r + 1)) :
    chowCohomologyRestriction C G sX f ((j : ℕ) : ℤ) hgys (D.ch E (j : ℕ)) =
      D'.ch ((Scheme.Modules.pullback f).obj E) (j : ℕ) := by
  have hrank' : PullbackPreservesRank ((Scheme.Modules.pullback f).obj E) r :=
    pullbackPreservesRank_pullback f hrank
  have := @hrank
  have := @hrank'
  refine eq_of_isChernClassBivariant C (f ≫ sX) ((Scheme.Modules.pullback f).obj E) r G
    (D'.cap r) hrank' j ?_
    (D'.ch_isChernClass ((Scheme.Modules.pullback f).obj E) r hrank' j)
  intro T t _ k α
  refine (chowCohomologyRestriction_cap C G sX f ((j : ℕ) : ℤ) hgys (D.ch E (j : ℕ))
    t k α).trans ?_
  refine (D.ch_isChernClass E r hrank j (T := T) (t ≫ f) k
    (chowGroupCongr C (Category.assoc t f sX).symm k α)).trans ?_
  rw [hcap]
  exact DFunLike.congr_fun
    (hiso (t ≫ (f ≫ sX)) ((Scheme.Modules.pullback (t ≫ f)).obj E)
      ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback f).obj E))
      ((Scheme.Modules.pullbackComp t f).app E).symm k j) _

/-- The restriction map of Stacks 0B7F carries the constant term of the unit series of `A^*(X)^∧`
to that of `A^*(X')^∧`:

  `f^*(1) = 1`  in degree `0`,

given a module `E` of globally constant rank whose pullbacks all have that rank and the hypotheses
`hcap` and `hiso` of `Stacks.Chow.chowCohomologyRestriction_ch_eq`. -/
theorem chowCohomologyRestriction_one_zero (D : TotalChernClassSeries C G sX R)
    (D' : TotalChernClassSeries C G (f ≫ sX) R') (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (hrank : PullbackPreservesRank E r)
    (hcap : (D.cap r : HigherChernCapRule C r) = (D'.cap r : HigherChernCapRule C r))
    (hiso : HigherChernCapRule.RespectsIso C r (D'.cap r : HigherChernCapRule C r)) :
    chowCohomologyRestriction C G sX f ((0 : ℕ) : ℤ) hgys (R.one 0) = R'.one 0 := by
  have h := chowCohomologyRestriction_ch_eq C G sX f hgys D D' E r hrank hcap hiso 0
  rw [Fin.val_zero, D.ch_apply_zero E,
    D'.ch_apply_zero ((Scheme.Modules.pullback f).obj E)] at h
  exact h

end Restriction

end Stacks.Chow

end
