module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantPowerSumShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DualComplexChern
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.ArbitraryRankDual
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree

/-!
# The Chern character of the dual of a finite locally free module: Stacks 0FAB

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let `ℰ` be a
finite locally free `𝒪_X`-module, of no assumed rank, with dual `ℰ^∨ = SheafHom(ℰ, 𝒪_X)`.
[Stacks, Tag 0FAB] is the sign rule

  `ch_i(ℰ^∨) = (-1)^i ch_i(ℰ)`  in  `A^i(X) ⊗ 𝐐`.

Here `ch_i(ℰ) = P_i(ℰ)/i!` is `Stacks.Chow.moduleChernCharacterComponent`, where `P_i(ℰ)` is the
power sum of Stacks 0F9B, Newton's recursion applied to the bivariant Chern classes
`Stacks.Chow.GenuineChern.chernClass` of Stacks 0B7H on each rank locus of `ℰ`, assembled over
the rank loci by Stacks 0FDZ.

## The proof

As in the source, the sign rule follows from the one for Chern classes, Stacks 0FA5. Let
`σ` be the ring endomorphism `Stacks.Chow.TotalChowClass.signScale` of
`A^*(X) = ∏_{q ≥ 0} A^q(X)` multiplying `A^q(X)` by `(-1)^q`.

* For `ℰ` of constant rank `r`, Stacks 0FA5 says `c(ℰ^∨) = σ(c(ℰ))`
  (`Stacks.Chow.totalChern_dualSheaf`). Since `σ` is a ring homomorphism commuting with taking
  homogeneous components and fixing the rank term `r · 1`, it commutes with Newton's recursion,
  so `P(ℰ^∨) = σ(P(ℰ))` (`Stacks.Chow.modulePowerSum_dualSheaf`).
* For arbitrary rank, both sides are compared on the rank loci `X_r` of `ℰ`, using that `σ`
  commutes with restriction and that the restriction of `ℰ^∨` to `X_r` is the dual of the
  restriction of `ℰ` (the dual base-change isomorphism of a finite locally free module; the
  rank of the restriction of `ℰ^∨` is
  `Stacks.Chow.SectionZeroScheme.isFiniteLocallyFreeOfRank_pullback_rankLocus_dualSheaf`)
  (`Stacks.Chow.modulePowerSumArbitraryRank_dualSheaf`).
* Reading the degree-`i` component and dividing by `i!` gives Stacks 0FAB
  (`Stacks.Chow.moduleChernCharacterComponent_dualSheaf`).

## References

* [Stacks Project, Tag 0FAB](https://stacks.math.columbia.edu/tag/0FAB)
* [Stacks Project, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The power sums of the dual of a module of constant rank.** For `ℰ` finite locally free of
rank `r`, `P_p(ℰ^∨)` is the `(-1)^q`-scaling of `P_p(ℰ)` in `A^*(X)`: the scaling is a ring
endomorphism carrying `c(ℰ)` to `c(ℰ^∨)` (Stacks 0FA5) and fixing the rank term, so it commutes
with Newton's recursion. -/
theorem modulePowerSum_dualSheaf (F : X.Modules) (r : ℕ)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r) (p : ℕ) :
    modulePowerSum C sX (dualSheaf F) r
        (Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf F r hF) p =
      TotalChowClass.signScale (modulePowerSum C sX F r hF p) := by
  let := hF
  rw [modulePowerSum, modulePowerSum, ← TotalChowClass.signScaleRingHom_apply,
    map_newtonPowerSum, TotalChowClass.signScaleRingHom_apply,
    TotalChowClass.signScale_zsmul_one]
  congr 1
  funext i
  rw [TotalChowClass.signScaleRingHom_apply, ← TotalChowClass.homComponent_signScale,
    totalChern_dualSheaf]

variable (E : X.Modules) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The power sums of the dual of a module of arbitrary rank.** For `ℰ` finite locally free,
`P_p(ℰ^∨)` is the `(-1)^q`-scaling of `P_p(ℰ)` in `A^*(X)`. Both sides are compared on the rank
loci of `ℰ`, where the restriction of `ℰ^∨` is the dual of the restriction of `ℰ`. -/
theorem modulePowerSumArbitraryRank_dualSheaf (p : ℕ) :
    haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf E hE
    modulePowerSumArbitraryRank C sX (dualSheaf E) p =
      TotalChowClass.signScale (modulePowerSumArbitraryRank C sX E p) := by
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf E hE
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily E) fun r ↦ ?_
  set ι := (rankLociFamily E r).ι
  have hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback ι).obj E) r.down :=
    isFiniteLocallyFreeOfRank_pullback_rankLociFamily E r
  have hr' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback ι).obj (dualSheaf E)) r.down :=
    SectionZeroScheme.isFiniteLocallyFreeOfRank_pullback_rankLocus_dualSheaf E r.down
  rw [res_modulePowerSumArbitraryRank_of_constantRank C sX (dualSheaf E) ι rfl r.down hr' p,
    TotalChowClass.res_signScale, res_modulePowerSumArbitraryRank_rankLociFamily,
    ← modulePowerSum_dualSheaf C (ι ≫ sX) _ r.down hr p]
  exact modulePowerSum_congr C _
    (Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf _ _ hr) hr'
    (@asIso _ _ _ _ (pullbackDualMap ι E) (pullbackDualMap_isIso ι E hE)) rfl p

/-- **Stacks 0FAB.** Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over
`S` and let `ℰ` be a finite locally free `𝒪_X`-module with dual `ℰ^∨`. Then

  `ch_i(ℰ^∨) = (-1)^i ch_i(ℰ)`  in  `A^i(X) ⊗ 𝐐`

for every `i ≥ 0`. -/
@[stacks 0FAB "ch_i(E^dual) = (-1)^i ch_i(E) in A^i(X) tensor Q for every i >= 0, X locally of \
finite type over the base of Situation 02QL and E a finite locally free O_X-module of arbitrary \
(not necessarily constant) rank, E^dual = SheafHom(E, O_X). ch_i(E) = P_i(E)/i! is \
Stacks.Chow.moduleChernCharacterComponent, built from the bivariant Chern classes of Tag 0B7H; \
the proof is Tag 0FA5 (Stacks.Chow.GenuineChern.chernClass_dualSheaf) on each rank locus. \
Nothing is carried."]
theorem moduleChernCharacterComponent_dualSheaf (i : ℕ) :
    haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf E hE
    moduleChernCharacterComponent C sX (dualSheaf E) i =
      ((-1 : ℤ) ^ i) • moduleChernCharacterComponent C sX E i := by
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf E hE
  rw [moduleChernCharacterComponent, moduleChernCharacterComponent,
    modulePowerSumComponentArbitraryRank, modulePowerSumComponentArbitraryRank,
    modulePowerSumArbitraryRank_dualSheaf, TotalChowClass.signScale_apply,
    TensorProduct.tmul_smul]

end Stacks.Chow

end
