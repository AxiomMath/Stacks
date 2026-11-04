module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ChowCohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.SplittingProjective

/-!
# The splitting principle, for the Chow cohomology ring of the repository

**Stacks 02UL.** Let `(S, δ)` be as in Situation 02QL, `X` locally of finite type over `S` and
`ℰ_i` (`i ∈ I`, finite) finite locally free `𝒪_X`-modules of ranks `r_i`. There is a projective
flat morphism `π : P ⟶ X` of relative dimension `d = ∑_i binom(r_i, 2)` such that

1. for every morphism `f : Y ⟶ X` the flat pullback `π_Y^* : CH_k(Y) ⟶ CH_{k+d}(Y ×_X P)` is
   injective, and
2. each `π^*ℰ_i` has a filtration whose successive quotients are invertible `𝒪_P`-modules;

and, since (1) holds, the restriction map `res : A^*(X) ⟶ A^*(P)` of Stacks 0B7F is injective.

Here `A^*` is the Chow cohomology ring of Stacks 0B7E at the Gysin system of the first Chern class
rule, `Stacks.Chow.gysinSystemOfInvertible`, and `res` is the ring map
`Stacks.Chow.chowCohomologyTotalRestrictionRingOfInvertible` of Stacks 0B7F, both built with no
hypothesis: the naturality of that Gysin system under base-change isomorphisms is a theorem,
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso`.

## Main results

* `Stacks.Chow.chowCohomologyTotalRestrictionRingOfInvertible_injective`: the last assertion of
  Stacks 02UL for any flat morphism of fixed relative dimension satisfying clause (1).
* `Stacks.Chow.exists_splittingMorphism_isProjective_ofInvertible`: **Stacks 02UL.**

## References

* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **The last assertion of Stacks 02UL.** Let `π : P ⟶ X` be flat of relative dimension `d`
such that flat pullback along every base change of `π` is injective on Chow groups (clause (1) of
Stacks 02UL). Then the restriction map `res : A^*(X) ⟶ A^*(P)` of Stacks 0B7F is injective. -/
theorem chowCohomologyTotalRestrictionRingOfInvertible_injective (C : ChowSituation.{u})
    {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (π : P ⟶ X)
    [LocallyOfFiniteType π] [Flat π] (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension π d)
    (hπ : UniversallyChowInjective C π d hd) :
    Function.Injective (chowCohomologyTotalRestrictionRingOfInvertible C sX π) :=
  (DirectSum.map_injective _).mpr fun p ↦
    chowCohomologyRestriction_injective C (gysinSystemOfInvertible C) sX π p d hd hπ
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)

attribute [local instance] SplittingMorphism.locallyOfFiniteType_π SplittingMorphism.flat_π

/-- **Stacks 02UL (the splitting principle).** Let `(S, δ)` be as in Situation 02QL, `X` locally
of finite type over `S` and `ℰ_i` (`i ∈ I`, `I` finite) finite locally free `𝒪_X`-modules of
ranks `r_i`. There is a morphism `π : P ⟶ X` which is

* projective (Stacks 01W8), flat, and of relative dimension `d = ∑_i binom(r_i, 2)`,

such that

1. for every morphism `f : Y ⟶ X` with `Y` locally of finite type over `S`, the flat pullback
   `π_Y^* : CH_k(Y) ⟶ CH_{k+d}(Y ×_X P)` along the base change of `π` is injective for every
   `k` (`Stacks.Chow.UniversallyChowInjective`), and
2. each `π^*ℰ_i` has a filtration whose successive quotients `ℒ_{i,1}, …, ℒ_{i,r_i}` are
   invertible `𝒪_P`-modules;

moreover the restriction map `res : A^*(X) ⟶ A^*(P)` of Stacks 0B7F,
`Stacks.Chow.chowCohomologyTotalRestrictionRingOfInvertible`, is injective. Nothing is assumed
beyond the hypotheses of the tag. -/
@[stacks 02UL]
theorem exists_splittingMorphism_isProjective_ofInvertible (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type) [Fintype I]
    (E : I → X.Modules) (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) :
    ∃ T : SplittingMorphism C sX (∑ i, (r i).choose 2),
      IsProjective T.π ∧ Flat T.π ∧
      AlgebraicGeometry.RelativeDimension T.π (∑ i, (r i).choose 2) ∧
      UniversallyChowInjective C T.π (∑ i, (r i).choose 2) T.relDim ∧
      (∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
        ((Scheme.Modules.pullback T.π).obj (E i)) (r i)) ∧
      Function.Injective (chowCohomologyTotalRestrictionRingOfInvertible C sX T.π) := by
  obtain ⟨T, hproj, hflat, hdim, hinj, hfilt, -⟩ :=
    exists_splittingMorphism_isProjective C sX I E r hE
  exact ⟨T, hproj, hflat, hdim, hinj, hfilt,
    chowCohomologyTotalRestrictionRingOfInvertible_injective C sX T.π _ T.relDim hinj⟩

end Stacks.Chow

end
