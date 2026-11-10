module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Convergence of the truncation tower on a ringed site, with nothing assumed

[Stacks, Tag 0D6M] is proved in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedLimit/TruncationTowerConvergence.lean` with
the module universe `wModule` left entirely free, and therefore with four class hypotheses that
the free universe makes unavailable: sheafification of abelian presheaves, that sheafification
inverts exactly the locally bijective maps, that sheaves of `O`-modules have enough injectives,
and that the truncation tower has a product in the derived category.

None of these is a hypothesis of the source.  Each of them is a *theorem* once the module
universe is large enough to contain the site and the structure rings, which is the only case in
which the category of sheaves of modules is the one the source is talking about.  This file
takes the module universe to be `max u v r w` -- still an arbitrary universe, since `w` is
arbitrary -- and discharges all four, so that the tag is available with no class hypothesis at
all beyond the model of the derived category.

## Main results

* `Stacks.Cohomology.hasSheafifyMax`, `Stacks.Cohomology.wEqualsLocallyBijectiveMax` -- the
  first two of the four facts, at the module universe `max u v r w`.  The other two are
  instances, listed in the implementation notes.
* `Stacks.Cohomology.isIso_to_isDerivedLimit_truncGETower_of_vanishing` -- **[Stacks, Tag
  0D6M]**, with the site's own category structure as its only class hypothesis.

## Implementation notes

The four facts come from, in order:

* `Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp`,
* `Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp`,
* `Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives` (through
  `Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck`: a Grothendieck abelian category
  has enough injectives),
* `Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`.

The last one is the one that is not formal.  `SheafOfModules O` does not satisfy AB4\*, so the
countable products of its derived category cannot be obtained from [Stacks, Tag 07KC]; they come
instead from termwise products of K-injective complexes, [Stacks, Tag 0BK6].

The first two are *not* registered as instances, and are instead applied by hand through `@` in
the statement below.  Their types mention the ring universe `r` and the extra module universe
`w` only inside the coefficient universe `max u v r w`, so instance search meets them with those
two universes undetermined and the resulting level constraints are the ones Lean reports as
`stuck at solving universe constraint`.  The other two name the structure sheaf, which pins `r`,
and have a four-element `max` chain that matches the goal's structurally, so they are usable as
instances; `hasProductsOfShape_derivedCategory_sheafOfModules` is made a local one here, and
`moduleSheavesEnoughInjectives` already is a global one.

## References

* [Stacks Project, Tag 0D6M](https://stacks.math.columbia.edu/tag/0D6M)
* [Stacks Project, Tag 0D6N](https://stacks.math.columbia.edu/tag/0D6N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v r w

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules

section Unconditional

variable {C : Type u} [instC : Category.{v} C] {J : GrothendieckTopology C}

set_option linter.checkUnivs false in
/-- Sheafification of abelian presheaves on an arbitrary site, in the module universe
`max u v r w` of the statement below. -/
theorem hasSheafifyMax : HasSheafify J AddCommGrpCat.{max u v r w} :=
  SiteModules.site_hasSheafify_addCommGrp.{u, v, max r w}

set_option linter.checkUnivs false in
/-- Sheafification of abelian presheaves inverts exactly the locally bijective maps, in the
module universe `max u v r w` of the statement below. -/
theorem wEqualsLocallyBijectiveMax :
    J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w} :=
  SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w}

/-- **Stacks Project, Tag 0D6M.** Let `O` be a sheaf of rings on a site `C`, let `E` be an
object of the derived category of sheaves of `O`-modules, and let `B` be a set of objects of
`C` large enough that every object is covered by members of `B`.  Suppose each `V ∈ B` carries
a degree bound `p(V, -) : ℤ → ℤ` and a cofinal system of coverings of `V` on whose members
`Hᵖ(Vᵢ, H^{m - p}(E)) = 0` whenever `p > p(V, m)`.  Then the canonical map from `E` to the
derived limit of the truncation tower `n ↦ τ_{≥ -n} E` is an isomorphism.

Nothing is assumed: sheafification, enough injectives and the countable products presenting the
derived limit are all theorems at this module universe, and are supplied as instances above. -/
@[stacks 0D6M,
  stacks 0D6N "the constant-bound case, by taking the degree bound at V to be max d_V m"]
theorem isIso_to_isDerivedLimit_truncGETower_of_vanishing
    (O : Sheaf J RingCat.{r})
    (E : DerivedCategory (SheafOfModules.{max u v r w} O))
    (B : Set C)
    (basisCover : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U,
      𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    (degreeBound : ∀ V : C, B V → ℤ → ℤ)
    (Cov : ∀ V : C, B V → Set (PreZeroHypercover.{max u v} V))
    (Cov_isCover : ∀ (V : C) (hV : B V) (𝒰 : PreZeroHypercover.{max u v} V),
      Cov V hV 𝒰 → 𝒰.sieve₀ ∈ J V)
    (Cov_cofinal : ∀ (V : C) (hV : B V) (𝒰 : PreZeroHypercover.{max u v} V),
      𝒰.sieve₀ ∈ J V →
        ∃ 𝒱 : PreZeroHypercover.{max u v} V, Cov V hV 𝒱 ∧ Nonempty (𝒱.Hom 𝒰))
    (vanishing : ∀ (V : C) (hV : B V) (𝒰 : PreZeroHypercover.{max u v} V),
      Cov V hV 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ) (m : ℤ),
        degreeBound V hV m < (p : ℤ) →
          IsZero (@moduleCohomology C instC J O hasSheafifyMax.{u, v, r, w}
            wEqualsLocallyBijectiveMax.{u, v, r, w}
            (SiteModules.moduleSheavesEnoughInjectives.{u, v, r, w} O)
            (𝒰.X i) p
            ((DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w} O)
              (m - (p : ℤ))).obj E)))
    (L : DerivedCategory (SheafOfModules.{max u v r w} O))
    (c : E ⟶ L)
    (q : L ⟶ ∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{max u v r w} O) E).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{max u v r w} O) E).obj ⟨n⟩) ⟶
        L⟦(1 : ℤ)⟧)
    (hL : Triangle.mk q (Pi.lift fun n : ℕ ↦
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
    IsIso c :=
  @isIso_to_isDerivedLimit_truncationGETower C instC J O hasSheafifyMax.{u, v, r, w}
    wEqualsLocallyBijectiveMax.{u, v, r, w}
    (SiteModules.moduleSheavesEnoughInjectives.{u, v, r, w} O) E B basisCover degreeBound Cov
    Cov_isCover Cov_cofinal vanishing inferInstance L c q δ hL hc

end Unconditional

end Stacks.Cohomology

end
