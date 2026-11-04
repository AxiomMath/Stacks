module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.HigherRankIrreducibleCriterion
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericIdealPushforward

/-!
# The dévissage of coherent sheaves on a Noetherian scheme

On a Noetherian scheme, a property of coherent modules which holds for the zero module, is
closed under extensions, descends from a nonempty finite direct sum, and for every integral
closed subscheme admits a coherent module supported exactly there whose generic stalk is
annihilated by the maximal ideal and which has a generic-equality subsheaf inside every ideal
multiple, holds for every coherent module.

## Main results

* `Stacks.AlgebraicGeometry.NoetherianDevissage.hasGenericStalkIdealCoproductSub` and
  `Stacks.AlgebraicGeometry.NoetherianDevissage.hasIrreducibleHigherRankCriterion`: the two
  predicates that the dévissage consumes, discharged from [Stacks Project, Tag 01YE] and
  [Stacks Project, Tag 01YL].
* `Stacks.AlgebraicGeometry.NoetherianDevissage.property_higher_rank`:
  [Stacks Project, Tag 01YM].

## Implementation notes

The vanishing of the property on the zero module is an added hypothesis. The source's condition
(1) concludes only about the middle term of a short exact sequence, and condition (2) descends
along a direct sum, so neither yields the property for the zero module; on an empty scheme the
zero module is the only coherent module and nothing else could. The attribute records this.

The two predicates differ from the library statements they are discharged from only in bundling:
`Stacks.AlgebraicGeometry.Tag01YEStalkBridge.IsMaximalIdealAnnihilated` and
`Stacks.ClosedImmersion.StalkKilledByMaximalIdeal` are the same definition in two namespaces, so
the first transfers by `exact`; and the generic subsheaf is asked for coherent here and used
quasi-coherent there, which is [Stacks Project, Tag 01BW].

## References

* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YL](https://stacks.math.columbia.edu/tag/01YL)
* [Stacks Project, Tag 01YM](https://stacks.math.columbia.edu/tag/01YM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NoetherianDevissage

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-! ### The two inputs of the dévissage -/

/-- **[Stacks, Tag 01YE] in the form the dévissage consumes.** The annihilation hypothesis is
the same definition under two names, so it transfers unchanged. -/
theorem hasGenericStalkIdealCoproductSub [IsNoetherian X] :
    Tag01YEStalkBridge.HasGenericStalkIdealCoproductSub X := by
  intro W i hi hW ξ hξ F hF hann
  have := hi
  have := hW
  have := hF
  exact Stacks.ClosedImmersion.exists_idealCoproduct_pushforward_mono_isIso_near_genericPoint
    i ξ hξ F hann

/-- **[Stacks, Tag 01YL] in the form the dévissage consumes.** The generic subsheaf is asked for
coherent and used quasi-coherent, which is [Stacks, Tag 01BW]. -/
alias hasIrreducibleHigherRankCriterion :=
  Stacks.AlgebraicGeometry.HigherRankIrreducibleDevissage.hasIrreducibleHigherRankCriterion

/-! ### The dévissage -/

/-- **The dévissage of coherent sheaves on a Noetherian scheme.** A property closed under
extensions, descending from a nonempty finite direct sum, and holding for a suitable coherent
module at every integral closed subscheme, holds for every coherent module. -/
@[stacks 01YM "plus P on the zero sheaf, which conditions (1) and (2) do not give"]
theorem property_higher_rank [IsNoetherian X] (P : X.Modules → Prop)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hsum : ∀ F : X.Modules, F.IsCoherent →
      (∃ n : ℕ, P (∏ᶜ fun _ : Fin (n + 1) => F)) → P F)
    (hgeneric : ∀ (I : X.IdealSheafData) [IsIntegral I.subscheme],
      ∃ G : X.Modules, G.IsCoherent ∧
        (∀ x : X, x ∈ I.support ↔ Nontrivial (G.presheaf.stalk x)) ∧
        Tag01YEStalkBridge.IsMaximalIdealAnnihilated G
          (I.subschemeι (genericPoint I.subscheme)) ∧
        (∀ J : X.IdealSheafData,
          I.subschemeι (genericPoint I.subscheme) ∉ J.support →
          ∃ G' : G.Submodule,
            G'.toSheafOfModules.IsCoherent ∧
            (∀ (U : X.affineOpens) (s : Γ(G'.toSheafOfModules, U.1)),
              (Scheme.Modules.Hom.app G'.ι U.1 s : Γ(G, U.1)) ∈
                J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1))) ∧
            Function.Surjective
              (((TopCat.Presheaf.stalkFunctor Ab
                (I.subschemeι (genericPoint I.subscheme))).map
                  (Scheme.Modules.Hom.mapPresheaf G'.ι)).hom) ∧
            P G'.toSheafOfModules)) :
    ∀ F : X.Modules, F.IsCoherent → P F :=
  Tag01YMHigherRank.property_higher_rank_of_criteria X
    (hasGenericStalkIdealCoproductSub X) (hasIrreducibleHigherRankCriterion X)
    P hzero hext hsum hgeneric

end Stacks.AlgebraicGeometry.NoetherianDevissage

end
