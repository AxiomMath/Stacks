module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.RankLocusChernClass

/-!
# The rank-locus assembly on a module of globally constant rank

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `ℰ` be a finite locally free `O_X`-module whose rank is
globally constant and equal to `r₀`. The rank decomposition `X = X_0 ⊔ X_1 ⊔ X_2 ⊔ …` of
Stacks 0ESW then has a single nonempty piece, `X_{r₀} = X`, by
`Stacks.Chow.rankLocus_eq_top`, so the product decomposition

  `A^p(X) = ∏_{r ≥ 0} A^p(X_r)`

of Stacks 0FDZ degenerates to the single identification `A^p(X) = A^p(X_{r₀})`.

This file builds that identification and reads the Chern classes through it: the class
`c_n(ℰ) ∈ A^n(X)` assembled from the rank loci by `Stacks.Chow.chernClassArbitraryRank` is the
constant-rank Chern class `Stacks.Chow.chernClass` of Stacks 0B7H, granted that the latter
restricts on `X_{r₀}` to the `n`-th Chern class of `ℰ|_{X_{r₀}}`. See the implementation notes
for why that one comparison is a hypothesis.

## Main definitions

* `Stacks.Chow.constRankLocusFamily` — the rank decomposition of a module of globally constant
  rank, presented as the one-piece decomposition `X = X_{r₀}`.
* `Stacks.Chow.rankLocusRestrictionEquivOfConstantRank` — **Stacks 0FDZ** at that decomposition:
  restriction to the rank-`r₀` locus is an isomorphism `A^p(X) ≅ A^p(X_{r₀})`.

## Main results

* `Stacks.Chow.eq_of_rankLocusRestriction_eq_of_constantRank` — a Chow cohomology class on `X` is
  determined by its restriction to the single nonempty rank locus.
* `Stacks.Chow.chernClassArbitraryRank_eq_chernClass` — **Stacks 0ESW on a module of globally
  constant rank**: the rank-locus assembly is the constant-rank Chern class of Stacks 0B7H.
* `Stacks.Chow.chernClassArbitraryRank_eq_chernClass_of_isChernClassBivariant` — the same, with
  the restriction comparison read through the characterization of Stacks 0B7H rather than through
  the assembled family.

## Implementation notes

### The one-piece decomposition

The decomposition used here is the constant family `fun _ ↦ X_{r₀}` on a one-point index type,
not the family `Stacks.Chow.rankLociFamily` of all rank loci: the latter is a decomposition only
because its other members are empty, and Stacks 0FDZ applied to it produces a product over all of
`ℕ`. The two restriction maps to the piece `X_{r₀}` agree, both being
`Stacks.Chow.bivariantPieceRestriction`, which depends on the decomposition only through the piece
it restricts to; so the inverse supplied by Stacks 0FDZ for the one-piece decomposition is an
inverse of `Stacks.Chow.rankLocusRestriction` read at `r₀`.

### The comparison that is a hypothesis

`Stacks.Chow.HigherChernCapRule`, the cap operation of Stacks 0B7G as it is used here, is a bare
family of homomorphisms of Chow groups indexed by a test scheme and a module on it; it carries no
naturality, and in particular nothing relates its value at a module to its value at an isomorphic
module. The two classes compared here are pinned, through Stacks 0B7H, by that rule at two
different modules: at a test scheme `g : T ⟶ X` the assembled class is pinned by the rule at
`g^*(ℰ|_{X_{r₀}})` and the constant-rank class by the rule at `(g ≫ ι)^*ℰ`, where `ι` is the
inclusion of the locus. These are modules on the same scheme `T` identified only by
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, so their two cap operations are unrelated data
and the comparison does not follow from what is carried here. It is therefore assumed, in exactly
the form in which it is used: that the constant-rank Chern class of `ℰ` restricts on `X_{r₀}` to
the `n`-th Chern class of `ℰ|_{X_{r₀}}`. For a cap operation that is functorial in the module,
as the cap product of Stacks 0B7G is, the comparison holds.

## References

* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (E : X.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r₀ : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r₀]

/-! ### The rank decomposition of a module of globally constant rank -/

/-- The rank decomposition of a module whose rank is globally constant and equal to `r₀`,
presented as the one-piece decomposition `X = X_{r₀}` indexed by a one-point type. -/
def constRankLocusFamily : PUnit.{u + 1} → X.Opens := fun _ ↦ rankLocus E r₀

/-- The one-piece family is a decomposition of `X` into open and closed subschemes: its single
member is the whole scheme, by `Stacks.Chow.rankLocus_eq_top`. -/
theorem isClopenDecomposition_constRankLocusFamily :
    IsClopenDecomposition (constRankLocusFamily E r₀) where
  disjoint i j hij := absurd (Subsingleton.elim i j) hij
  iSup_eq_top := by simp [constRankLocusFamily, rankLocus_eq_top E r₀]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r₀] in
/-- The single piece lies in its own preimage under the identity. -/
theorem constRankLocusFamily_le_preimage (i : PUnit.{u + 1}) :
    constRankLocusFamily E r₀ i ≤ (𝟙 X) ⁻¹ᵁ constRankLocusFamily E r₀ i := by simp

/-! ### Chow cohomology of a module of globally constant rank -/

variable (hgysO : G.IsNaturalUnderOpenImmersion) (hgysR : G.IsNaturalUnderOpensRestriction)
  (hgysC : G.IsNaturalUnderPullbackComp) (p : ℤ)

/-- **Stacks 0FDZ at the one-piece rank decomposition.** On a module whose rank is globally
constant and equal to `r₀`, restriction to the rank-`r₀` locus is an isomorphism
`A^p(X) ≅ A^p(X_{r₀})`. -/
def rankLocusRestrictionEquivOfConstantRank :
    chowCohomologyComponent C G sX p ≃+
      chowCohomologyComponent C G ((rankLocus E r₀).ι ≫ sX) p :=
  (bivariantPieceEquiv C G sX sX (𝟙 X) (Category.id_comp sX) (constRankLocusFamily E r₀)
      (constRankLocusFamily E r₀) id (constRankLocusFamily_le_preimage E r₀)
      (isClopenDecomposition_constRankLocusFamily E r₀) p hgysO hgysR hgysC).trans
    ((AddEquiv.piUnique _).trans
      (pieceIdentityCongr C G sX (constRankLocusFamily E r₀)
        (constRankLocusFamily_le_preimage E r₀) p default _))

/-- The isomorphism of Stacks 0FDZ at the one-piece rank decomposition is restriction to the
rank-`r₀` locus. -/
@[simp]
theorem rankLocusRestrictionEquivOfConstantRank_apply (c : chowCohomologyComponent C G sX p) :
    rankLocusRestrictionEquivOfConstantRank C G sX E r₀ hgysO hgysR hgysC p c =
      rankLocusRestriction C G sX E hgysO p c r₀ :=
  rfl

include hgysR hgysC in
/-- On a module whose rank is globally constant and equal to `r₀`, a Chow cohomology class on `X`
is determined by its restriction to the rank-`r₀` locus. -/
theorem eq_of_rankLocusRestriction_eq_of_constantRank
    {c d : chowCohomologyComponent C G sX p}
    (h : rankLocusRestriction C G sX E hgysO p c r₀ =
      rankLocusRestriction C G sX E hgysO p d r₀) : c = d :=
  (rankLocusRestrictionEquivOfConstantRank C G sX E r₀ hgysO hgysR hgysC
    p).injective h

/-! ### The Chern classes of a module of globally constant rank -/

variable (caps : ∀ r : ℕ, HigherChernCapRule C r)
  (hrank : ∀ r : ℕ,
    PullbackPreservesRank ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r)
  (cc : ∀ (r : ℕ) (j : Fin (r + 1)),
    chowCohomologyComponent C G ((rankLocus E r).ι ≫ sX) (j : ℤ))
  (hproper : ∀ i : Fin (r₀ + 1), IdentityCapRule.ProperNaturality C sX (i : ℤ)
    (chernIdentityCapRuleOfRank C sX E r₀ (caps r₀) i))
  (hflat : ∀ i : Fin (r₀ + 1), IdentityCapRule.FlatNaturality C sX (i : ℤ)
    (chernIdentityCapRuleOfRank C sX E r₀ (caps r₀) i))
  (hgysin : ∀ i : Fin (r₀ + 1), IdentityCapRule.GysinNaturality C sX (i : ℤ)
    (chernIdentityCapRuleOfRank C sX E r₀ (caps r₀) i) G)
  (hiso : G.IsNaturalUnderInverseIso)

/-- **Stacks 0ESW on a module of globally constant rank.** The rank-locus assembly `c_n(ℰ)` is
the constant-rank Chern class of Stacks 0B7H, granted that the latter restricts on the rank-`r₀`
locus to the `n`-th member of the assembled family. -/
theorem chernClassArbitraryRank_eq_chernClass (n : ℕ) (h : n ≤ r₀)
    (hres : rankLocusRestriction C G sX E hgysO (n : ℤ)
        (chernClass C sX E r₀ G (caps r₀) hproper hflat hgysin hiso
          ⟨n, Nat.lt_succ_of_le h⟩) r₀ = cc r₀ ⟨n, Nat.lt_succ_of_le h⟩) :
    chernClassArbitraryRank C G sX E hgysO hgysR hgysC cc n =
      chernClass C sX E r₀ G (caps r₀) hproper hflat hgysin hiso ⟨n, Nat.lt_succ_of_le h⟩ :=
  eq_of_rankLocusRestriction_eq_of_constantRank C G sX E r₀ hgysO hgysR hgysC (n : ℤ)
    (((rankLocusRestriction_chernClassArbitraryRank C G sX E hgysO hgysR hgysC cc
      n r₀).trans (rankLocusChernFamily_of_le C G sX E cc n r₀ h)).trans hres.symm)

/-- **Stacks 0ESW on a module of globally constant rank**, with the restriction comparison read
through the characterization of Stacks 0B7H: if the constant-rank Chern class restricts on the
rank-`r₀` locus to a class which is an `n`-th Chern class of `ℰ|_{X_{r₀}}` there, then the
rank-locus assembly is that constant-rank Chern class. -/
theorem chernClassArbitraryRank_eq_chernClass_of_isChernClassBivariant
    (hcc : ∀ (r : ℕ) (j : Fin (r + 1)),
      IsChernClassBivariant C ((rankLocus E r).ι ≫ sX)
        ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r G (caps r) (hrank r) j (cc r j))
    (n : ℕ) (h : n ≤ r₀)
    (hres : IsChernClassBivariant C ((rankLocus E r₀).ι ≫ sX)
      ((Scheme.Modules.pullback (rankLocus E r₀).ι).obj E) r₀ G (caps r₀) (hrank r₀)
      ⟨n, Nat.lt_succ_of_le h⟩
      (rankLocusRestriction C G sX E hgysO (n : ℤ)
        (chernClass C sX E r₀ G (caps r₀) hproper hflat hgysin hiso
          ⟨n, Nat.lt_succ_of_le h⟩) r₀)) :
    chernClassArbitraryRank C G sX E hgysO hgysR hgysC cc n =
      chernClass C sX E r₀ G (caps r₀) hproper hflat hgysin hiso ⟨n, Nat.lt_succ_of_le h⟩ :=
  chernClassArbitraryRank_eq_chernClass C G sX E r₀ hgysO hgysR hgysC caps cc hproper
    hflat hgysin hiso n h
    (eq_of_isChernClassBivariant C ((rankLocus E r₀).ι ≫ sX)
      ((Scheme.Modules.pullback (rankLocus E r₀).ι).obj E) r₀ G (caps r₀) (hrank r₀)
      ⟨n, Nat.lt_succ_of_le h⟩ hres (hcc r₀ ⟨n, Nat.lt_succ_of_le h⟩))

end Stacks.Chow

end
