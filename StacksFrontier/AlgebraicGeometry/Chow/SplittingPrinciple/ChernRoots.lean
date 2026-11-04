module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorPowerSums
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.Unconditional

/-!
# Identities between total classes may be checked on split modules

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `ℰ_i`, `i ∈ I` finite, be finite locally free `𝒪_X`-modules of
ranks `r_i`. The splitting principle (Stacks 02UL) is used in chapter 42 in the following form:
to prove an identity between bivariant classes on `X` — typically one built from the Chern
classes of the `ℰ_i` — it suffices to prove it after restriction along every morphism
`h : T ⟶ X` along which each `h^*ℰ_i` has a filtration with invertible successive quotients.
On such a `T` the Whitney sum formula (Stacks 02UI) writes the total Chern class of each `h^*ℰ_i`
as the product `∏_j (1 + c₁(ℒ_j))` of its Chern roots.

This file proves that reduction for the total Chow cohomology classes
`Stacks.Chow.TotalChowClass` at the Gysin system of the first Chern class of an invertible
module. A total class is determined by its operations on the test schemes `g : T ⟶ X`
(Stacks 0B76); over each of them the splitting morphism `π : P ⟶ T` of the modules `g^*ℰ_i`
(`Stacks.Chow.exists_splittingMorphism_universal`) has injective flat pullback on Chow groups,
a bivariant class commutes with flat pullback, and `(g ∘ π)^*ℰ_i ≅ π^*g^*ℰ_i` is filtered with
invertible quotients.

## Main results

* `Stacks.Chow.TotalChowClass.eq_of_res_eq_of_hasInvertibleFiltration` — **the Chern roots
  principle**: two total classes on `X` agree if their restrictions agree along every
  `h : T ⟶ X` that splits the `ℰ_i`.

## References

* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.TotalChowClass

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- **The Chern roots principle.** Let `ℰ_i`, `i ∈ I` finite, be finite locally free
`𝒪_X`-modules of ranks `r_i`. Two total Chow cohomology classes `c`, `d` on `X` are equal as soon
as their restrictions agree along every morphism `h : T ⟶ X`, with `T` locally of finite type
over `S`, such that each `h^*ℰ_i` has a filtration of length `r_i` with invertible successive
quotients.

Over a test scheme `g : T ⟶ X` the splitting morphism `π : P ⟶ T` of the modules `g^*ℰ_i`
(Stacks 02UL, `Stacks.Chow.exists_splittingMorphism_universal`) has injective flat pullback, and
`(π ≫ g)^*ℰ_i ≅ π^*g^*ℰ_i` is filtered; so the hypothesis applies to `h = π ≫ g`, and
`Stacks.Chow.TotalChowClass.eq_of_res_eq_of_flat` concludes. -/
theorem eq_of_res_eq_of_hasInvertibleFiltration {I : Type} [Fintype I] (E : I → X.Modules)
    (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i))
    {c d : TotalChowClass C sX}
    (h : ∀ {T : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (h : T ⟶ X)
      [LocallyOfFiniteType h] (hs : h ≫ sX = sT),
      (∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T
        ((Scheme.Modules.pullback h).obj (E i)) (r i)) → res h hs c = res h hs d) :
    c = d := by
  refine eq_of_res_eq_of_flat fun {T} g _ ↦ ?_
  obtain ⟨S, -, hS⟩ := exists_splittingMorphism_universal C (g ≫ sX) I
    (fun i ↦ (Scheme.Modules.pullback g).obj (E i)) r
    fun i ↦ @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ g (E i) (r i) (hE i)
  obtain ⟨P, sP, π, hsP, relDim, hfac, hinj⟩ := S
  subst hsP
  exact ⟨P, π, inferInstance, inferInstance, _, relDim, hinj,
    h _ (π ≫ g) (Category.assoc π g sX) fun i ↦
      (hS i).of_iso ((Scheme.Modules.pullbackComp π g).app (E i))⟩

end Stacks.Chow.TotalChowClass

end
