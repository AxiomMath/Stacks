module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergenceUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Convergence of the truncation tower under a degree-dependent bound, with nothing assumed

Let `(C, O)` be a ringed site and let `E` be an object of the derived category of `O`-modules.
Suppose a subset `B` of the objects of `C` covers every object, and that there is a function
`p : ℤ → ℤ` with `H^p(V, H^{m - p}(E)) = 0` for every `V ∈ B` and all `p > p(m)`.  Then the
canonical map from `E` to the derived limit of its truncation tower `n ↦ τ_{≥ -n} E` is an
isomorphism.  This is [Stacks, Tag 08U3].

The source assumes nothing else.  The module universe is taken to be `max u v r w` -- still
arbitrary, since `w` is -- so that sheafification of abelian presheaves, enough injectives for
sheaves of `O`-modules and the countable product of the truncation tower in the derived category
are all theorems rather than hypotheses; the discharges are the ones made for [Stacks, Tag 0D6M]
in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergenceUnconditional`.
The deduction from [Stacks, Tag 0D6M] is the proof of the source: take `p(V, m) = p(m)`, and for
the cofinal system of coverings of `V ∈ B` take all coverings whose members lie in `B`.

## Main results

* `Stacks.Cohomology.DegreeBound.isIso_to_isDerivedLimit_truncGETower_of_degreeBound` --
  **[Stacks, Tag 08U3]**, with the site's own category structure as its only class hypothesis.

## Implementation notes

The system of all `B`-coverings of `V` is cofinal because an arbitrary covering is refined by
binding it with `B`-coverings of its own members, whose generated sieve covers by transitivity of
the topology.

A covering family is represented by a `PreZeroHypercover`, which is a covering exactly when the
sieve it generates lies in the topology, and the truncation tower is
`Stacks.DerivedLimit.truncGETower`, both as in [Stacks, Tag 0D6M].  Because the predicate "`L` is
a derived limit" does not remember the first arrow of its distinguished triangle, the statement
is given for a presentation of that triangle together with a map whose composites with all
product projections are the canonical truncation maps; this pins down the canonical map of the
source rather than an arbitrary map to a derived limit.

Cohomology over an object is `Stacks.Cohomology.moduleCohomology`, applied through `@` to the
discharged instances `Stacks.Cohomology.hasSheafifyMax`,
`Stacks.Cohomology.wEqualsLocallyBijectiveMax` and
`Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives`, as in [Stacks, Tag 0D6M].  The
product of the truncation tower is
`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`, made a local
instance here so that `∏ᶜ` elaborates in the statement with no hypothesis.

## References

* [Stacks Project, Tag 08U3](https://stacks.math.columbia.edu/tag/08U3)
* [Stacks Project, Tag 0D6M](https://stacks.math.columbia.edu/tag/0D6M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v r w

namespace Stacks.Cohomology.DegreeBound

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules

variable {C : Type u} [instC : Category.{v} C] {J : GrothendieckTopology C}

/-- **Stacks Project, Tag 08U3.** Let `O` be a sheaf of rings on a site `C` and let `E` be an
object of the derived category of sheaves of `O`-modules.  Suppose there are a function
`p(-) : ℤ → ℤ` and a set `B` of objects of `C` such that every object of `C` has a covering whose
members are elements of `B`, and such that `H^p(V, H^{m - p}(E)) = 0` for all `p > p(m)` and all
`V ∈ B`.  Then the canonical map `E ⟶ R lim τ_{≥ -n} E` is an isomorphism.

Nothing else is assumed: sheafification, enough injectives and the countable products presenting
the derived limit are all theorems at this module universe. -/
@[stacks 08U3]
theorem isIso_to_isDerivedLimit_truncGETower_of_degreeBound
    (O : Sheaf J RingCat.{r})
    (E : DerivedCategory (SheafOfModules.{max u v r w} O))
    (degreeBound : ℤ → ℤ) (B : Set C)
    (basisCover : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U,
      𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    (vanishing : ∀ (V : C), B V → ∀ (p : ℕ) (m : ℤ), degreeBound m < (p : ℤ) →
      IsZero (@moduleCohomology C instC J O hasSheafifyMax.{u, v, r, w}
        wEqualsLocallyBijectiveMax.{u, v, r, w}
        (SiteModules.moduleSheavesEnoughInjectives.{u, v, r, w} O) V p
        ((DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w} O)
          (m - (p : ℤ))).obj E)))
    (L : DerivedCategory (SheafOfModules.{max u v r w} O))
    (c : E ⟶ L)
    (q : L ⟶ ∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{max u v r w} O) E).obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{max u v r w} O) E).obj ⟨n⟩) ⟶
          L⟦(1 : ℤ)⟧,
      Triangle.mk q (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{max u v r w} O) E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{max u v r w} O) E).obj ⟨n⟩)
              (n + 1) ≫
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{max u v r w} O) E).map
              (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{max u v r w} O)))
    (hc : ∀ n : ℕ, c ≫ q ≫
      Pi.π (fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{max u v r w} O) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c := by
  classical
  obtain ⟨δ, hL⟩ := hL
  refine isIso_to_isDerivedLimit_truncGETower_of_vanishing O E B basisCover
    (fun _ _ => degreeBound)
    (fun V _ => {𝒰 | 𝒰.sieve₀ ∈ J V ∧ ∀ i, B (𝒰.X i)})
    (by intro V hV 𝒰 h𝒰; exact h𝒰.1) ?_
    (by intro V hV 𝒰 h𝒰 i p m hm; exact vanishing _ (h𝒰.2 i) p m hm)
    L c q δ hL hc
  intro V hV 𝒰 h𝒰
  choose F hF using fun i : 𝒰.I₀ => basisCover (𝒰.X i)
  refine ⟨𝒰.bind F, ⟨?_, fun ij => (hF ij.1).2 ij.2⟩,
    ⟨fun ij => ij.1, fun ij => (F ij.1).f ij.2, fun ij => rfl⟩⟩
  have hbind : Sieve.generate
      (Presieve.bindOfArrows 𝒰.X 𝒰.f (fun i => (F i).presieve₀)) ∈ J V :=
    J.bindOfArrows h𝒰 (fun i => by
      simpa [PreZeroHypercover.presieve₀] using (hF i).1)
  simpa [PreZeroHypercover.bind, PreZeroHypercover.sieve₀,
    Presieve.bindOfArrows_ofArrows] using hbind

end Stacks.Cohomology.DegreeBound

end
