module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentSupportDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.IntersectionProductCycle

/-!
# The delta-dimension bound on the supports of the Tor sheaves

`AlgebraicGeometry.TorFormula.intersectionProductCycle` forms the alternating sum
`∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(ℱ, 𝒢)]_k` from a bound on the delta-dimension of the support of each
`Tor` sheaf, the bound that `Stacks.Chow.coherentSheafCycle` needs in order for the cycle of a
coherent sheaf to be well formed. This file proves that bound from the source's own hypothesis
on the two sheaves: a bound on the relative dimension at the points of `Supp ℱ ∩ Supp 𝒢`.

The two statements are connected by the support clause of Tag 0AZT: every `Torᵢ^{𝒪_X}(ℱ, 𝒢)` is
supported inside `Supp ℱ ∩ Supp 𝒢`, so a dimension bound on that intersection is inherited by
each `Tor` sheaf. For `ℱ = 𝒪_W` and `𝒢 = 𝒪_V` the structure sheaves of two closed subvarieties
of dimensions `s` and `r` which intersect properly, the hypothesis is the source's
`dim(Supp ℱ ∩ Supp 𝒢) ≤ r + s - dim X` and the conclusion is the bound at `k = r + s - dim X`.

## Main results

* `AlgebraicGeometry.TorFormula.torSheafDeltaDimension_le_of_forall_mem_inter` — a relative
  dimension bound at the points of `Supp ℱ ∩ Supp 𝒢` bounds the delta-dimension of the support
  of every `Tor` sheaf.

## References

* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry.TorFormula

/-- **The source's hypothesis on the intersection of the two supports supplies the bound the
alternating sum needs.** If every point of `Supp ℱ ∩ Supp 𝒢` has relative dimension at most `n`,
then the support of each `Tor` sheaf has delta-dimension at most `n`, because every `Tor` sheaf
is supported inside that intersection (Tag 0AZT). This is how
`dim(Supp ℱ ∩ Supp 𝒢) ≤ r + s - dim X` enters the formation of
`AlgebraicGeometry.TorFormula.intersectionProductCycle`. -/
theorem torSheafDeltaDimension_le_of_forall_mem_inter (C : Stacks.Chow.ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (hX : IsRegular X) (F G : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (hG : SheafOfModules.IsCoherent G) (n : ℤ)
    (hn : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp G,
      Stacks.Chow.relativeDimension C.dimensionFunction f w ≤ n) (i : ℕ) :
    haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
    Stacks.Chow.schemeDeltaDimension C
      ((Stacks.Chow.reducedSupport (torSheaf X F G i)).subschemeι ≫ f) ≤ WithBotTop.coe n := by
  have := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
  exact Stacks.Chow.schemeDeltaDimension_reducedSupport_le C f (torSheaf X F G i)
    fun w hw => hn w (supp_torSheaf_subset_inter X F G i hw)

end AlgebraicGeometry.TorFormula

end
