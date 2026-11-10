module

public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.ArbitraryRank
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ChernClassDual

/-!
# The Chern classes of the dual of a finite locally free module: Stacks 0FA5

Let `X` be locally of finite type over the base of chapter 42 and let `ℰ` be a finite locally
free `𝒪_X`-module, of rank not necessarily constant, with dual `ℰ^∨`. [Stacks, Tag 0FA5] is

  `c_i(ℰ^∨) = (-1)^i c_i(ℰ)`  in `A^i(X)`,

for every `i ≥ 0`, where `c_i` is the Chern class of [Stacks, Tag 0ESW]: the class of `A^i(X)`
whose component on the rank-`r` locus `X_r` is the class `c_i(ℰ|_{X_r})` of [Stacks, Tag 0B7H],
zero when `i > r`.

## The proof

The rank loci of `ℰ` and of `ℰ^∨` coincide: on `X_r` the restriction of `ℰ^∨` is the dual of
`ℰ|_{X_r}` by the base-change isomorphism `Stacks.Chow.pullbackDualMap_isIso`, hence has rank
`r` (Tag 0FA7, `Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf`).
By Tag 0FDZ a class of `A^i(X)` is determined by its restrictions to the rank loci of `ℰ`
(`Stacks.Chow.eq_of_rankLocusRestriction_eq`). On `X_r` the left side restricts to
`c_i((ℰ^∨)|_{X_r}) = c_i((ℰ|_{X_r})^∨)` and the right side to `(-1)^i c_i(ℰ|_{X_r})`, which agree
by the constant-rank case `Stacks.Chow.GenuineChern.chernClass_dualSheaf`; for `i > r` both
restrictions vanish.

## Main results

* `Stacks.Chow.GenuineChern.chernClass_congr` — the Chern class of Tag 0B7H depends only on the
  isomorphism class of the module.
* `Stacks.Chow.SectionZeroScheme.rankLocus_dualSheaf` — `ℰ` and `ℰ^∨` have the same rank loci.
* `Stacks.Chow.SectionZeroScheme.chernClassOfLocallyFree_dualSheaf` — **Stacks 0FA5**.

## References

* [Stacks Project, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf isFiniteLocallyFree_dualSheaf
  isFiniteLocallyFreeOfRank_dualSheaf)

universe u

namespace Stacks.Chow.GenuineChern

/-- **The Chern classes of Stacks 0B7H depend only on the isomorphism class of the module.** Both
classes cap by `c_j(g^*ℰ) ∩ - = c_j(g^*ℰ') ∩ -` on every test scheme `g`, so they agree by the
uniqueness in the characterization of Stacks 0B7H. -/
theorem chernClass_congr (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {F F' : X.Modules} (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r]
    (e : F ≅ F') (j : Fin (r + 1)) :
    chernClass C sX F r j = chernClass C sX F' r j := by
  refine eq_of_isChernClassBivariant C sX F r (gysinSystemOfInvertible C) (chernCap C r)
    (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) j
    (isChernClassBivariant_chernClass C sX F r j) ?_
  intro T g _ k α
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F' r g
  rw [isChernClassBivariant_chernClass C sX F' r j g k α]
  exact chernCap_congr C (g ≫ sX) r ((Scheme.Modules.pullback g).mapIso e.symm) k j α

end Stacks.Chow.GenuineChern

namespace Stacks.Chow.SectionZeroScheme

variable {X : Scheme.{u}} (E : X.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The base-change isomorphism `(ℰ^∨)|_{X_r} ≅ (ℰ|_{X_r})^∨` on the rank-`r` locus. -/
private def pullbackRankLocusDualIso (r : ℕ) :
    (Scheme.Modules.pullback (rankLocus E r).ι).obj (dualSheaf E) ≅
      dualSheaf ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) :=
  @asIso _ _ _ _ (pullbackDualMap (rankLocus E r).ι E)
    (pullbackDualMap_isIso (rankLocus E r).ι E hE)

/-- On the rank-`r` locus of `ℰ`, the restriction of `ℰ^∨` has rank `r`: it is the dual of the
restriction of `ℰ`, by the base-change isomorphism of the dual. -/
theorem isFiniteLocallyFreeOfRank_pullback_rankLocus_dualSheaf (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLocus E r).ι).obj (dualSheaf E)) r := by
  have := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (pullbackRankLocusDualIso E r).symm (isFiniteLocallyFreeOfRank_dualSheaf _ r this)

/-- **A finite locally free module and its dual have the same rank at every point.** -/
theorem moduleRank_dualSheaf (x : X) :
    haveI := isFiniteLocallyFree_dualSheaf E hE
    moduleRank (dualSheaf E) x = moduleRank E x := by
  have := isFiniteLocallyFree_dualSheaf E hE
  have := isFiniteLocallyFreeOfRank_pullback_rankLocus_dualSheaf E (moduleRank E x)
  have hx : x ∈ rankLocus E (moduleRank E x) := (mem_rankLocus E).2 rfl
  exact (mem_rankLocus (dualSheaf E)).1
    (mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback (dualSheaf E)
      (rankLocus E (moduleRank E x)).ι (moduleRank E x) ⟨x, hx⟩)

/-- **A finite locally free module and its dual have the same rank loci.** -/
theorem rankLocus_dualSheaf (r : ℕ) :
    haveI := isFiniteLocallyFree_dualSheaf E hE
    rankLocus (dualSheaf E) r = rankLocus E r := by
  have := isFiniteLocallyFree_dualSheaf E hE
  ext x
  change moduleRank (dualSheaf E) x = r ↔ moduleRank E x = r
  rw [moduleRank_dualSheaf E x]

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The restriction of `c_i(ℰ)` to the rank-`r` locus** (Stacks 0ESW), read on an open `W`
equal to that locus: it is `c_i(ℰ|_W)` of Stacks 0B7H for `i ≤ r`, and zero for `i > r`. -/
theorem chowCohomologyRestriction_chernClassOfLocallyFree (r i : ℕ) (W : X.Opens)
    (hW : W = rankLocus E r)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback W.ι).obj E) r] :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sX W.ι (i : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (chernClassOfLocallyFree E C sX i) =
      if h : i ≤ r then
        GenuineChern.chernClass C (W.ι ≫ sX) ((Scheme.Modules.pullback W.ι).obj E) r
          ⟨i, Nat.lt_succ_of_le h⟩
      else 0 := by
  subst hW
  exact (chowCohomologyRestriction_eq_pieceIdentityCongr (rankLociFamily E)
    (chernClassOfLocallyFree E C sX i) (ULift.up r)).trans
    (rankLocusRestriction_chernClassArbitraryRank C (gysinSystemOfInvertible C) sX E _ _ _ _ i r)

/-- **Stacks 0FA5.** For a finite locally free `𝒪_X`-module `ℰ` on a scheme `X` locally of finite
type over the base, of rank not necessarily constant, and every `i ≥ 0`,

  `c_i(ℰ^∨) = (-1)^i c_i(ℰ)`

in `A^i(X)`, for the Chern classes `Stacks.Chow.SectionZeroScheme.chernClassOfLocallyFree` of
Stacks 0ESW, built from the bivariant Chern classes of Stacks 0B7H on the rank loci.

Both sides are compared on the rank loci of `ℰ`, which are those of `ℰ^∨`
(`Stacks.Chow.SectionZeroScheme.rankLocus_dualSheaf`); on `X_r` the identity is the constant-rank
case `Stacks.Chow.GenuineChern.chernClass_dualSheaf` together with `(ℰ^∨)|_{X_r} ≅ (ℰ|_{X_r})^∨`,
and for `i > r` both sides restrict to zero. -/
@[stacks 0FA5 "c_i(E^dual) = (-1)^i c_i(E) in A^i(X) for every finite locally free E (rank not \
necessarily constant) and every i >= 0, at the Chern classes of Tag 0ESW built from those of \
Tag 0B7H"]
theorem chernClassOfLocallyFree_dualSheaf (i : ℕ) :
    haveI := isFiniteLocallyFree_dualSheaf E hE
    chernClassOfLocallyFree (dualSheaf E) C sX i =
      ((-1 : ℤ) ^ i) • chernClassOfLocallyFree E C sX i := by
  have := isFiniteLocallyFree_dualSheaf E hE
  refine eq_of_rankLocusRestriction_eq C (gysinSystemOfInvertible C) sX E
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) (i : ℤ) fun r ↦ ?_
  have hEr := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
  have hEDr := isFiniteLocallyFreeOfRank_pullback_rankLocus_dualSheaf E r
  have hres : ∀ c, rankLocusRestriction C (gysinSystemOfInvertible C) sX E
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) (i : ℤ) c r =
      chowCohomologyRestriction C (gysinSystemOfInvertible C) sX (rankLocus E r).ι (i : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c := fun c ↦
    (chowCohomologyRestriction_eq_pieceIdentityCongr (rankLociFamily E) c (ULift.up r)).symm
  rw [hres, hres, map_zsmul,
    chowCohomologyRestriction_chernClassOfLocallyFree (dualSheaf E) C sX r i _
      (rankLocus_dualSheaf E r).symm,
    chowCohomologyRestriction_chernClassOfLocallyFree E C sX r i _ rfl]
  split_ifs with h
  · have := isFiniteLocallyFreeOfRank_dualSheaf _ r hEr
    rw [GenuineChern.chernClass_congr C _ r (pullbackRankLocusDualIso E r)]
    exact GenuineChern.chernClass_dualSheaf C _ _ r ⟨i, Nat.lt_succ_of_le h⟩
  · rw [smul_zero]

end Stacks.Chow.SectionZeroScheme

end
