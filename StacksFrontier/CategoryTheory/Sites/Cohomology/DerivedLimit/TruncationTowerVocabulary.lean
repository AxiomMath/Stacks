module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGETower
public import StacksCore.Tactic.StacksAttribute

/-!
# Convergence of the truncation tower on a ringed site (Stacks 0D6M): the vocabulary

Stacks 0D6M says that if a ringed site is locally covered by objects carrying cofinal systems
of coverings on whose members the cohomology of the cohomology sheaves of `E ∈ D(O)` vanishes
above an object- and degree-dependent bound, then the canonical map from `E` to the derived
limit of its truncations `τ_{≥ -n} E` is an isomorphism.

Two pieces of vocabulary are needed even to *state* it, and this file supplies them: the
truncation tower itself, which is `truncGETower` of
`StacksFrontier.Algebra.Homology.DerivedCategory.TruncGETower` (a neutral file, so that the
ringed-space statement Stacks 0D62 and this one speak about the same tower), and the cohomology
of a sheaf of modules over an object of the site, which is `siteModuleCohomology` below.

## Main definitions

* `Stacks.Cohomology.SiteModuleCohomology.siteModuleCohomology`: `Hᵖ(U, F)` for a sheaf of modules
  `F` on a ringed site
  and an object `U` of the site, as a module over the sections of the structure sheaf over `U`
  (Stacks 071G).

## Implementation notes

**The tag is not proved here.**  With `truncGETower` and `siteModuleCohomology` in place the
statement of Stacks 0D6M elaborates verbatim; what is missing is its proof, namely

```
theorem isIso_to_isDerivedLimit_truncationGETower
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [EnoughInjectives (SheafOfModules.{wModule} O)]
    (E : DerivedCategory (SheafOfModules.{wModule} O))
    (B : Set C)
    (basisCover : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U,
      𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    (degreeBound : ∀ V : C, B V → ℤ → ℤ)
    (Cov : ∀ V : C, B V → Set (PreZeroHypercover.{max u v} V))
    (Cov_isCover : ...) (Cov_cofinal : ...) (vanishing : ...)
    [HasProduct fun n : ℕ ↦ (truncGETower _ E).obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{wModule} O)) (c : E ⟶ L) (q : L ⟶ ∏ᶜ …)
    (δ : (∏ᶜ …) ⟶ L⟦(1 : ℤ)⟧) (hL : Triangle.mk q … δ ∈ distTriang …)
    (hc : ∀ n : ℕ, c ≫ q ≫ Pi.π … n = (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c
```

the body of which is the argument of the source: fix `m`, set
`n(V) = 1 + max {-m, p(V, m-1) - m, -1 + p(V, m) - m, -2 + p(V, m+1) - m}`, and deduce from the
distinguished triangles `Hⁿ⁻¹(E)[n+1] ⟶ K_{n+1} ⟶ K_n ⟶ Hⁿ⁻¹(E)[n+2]` of the truncations that
`Hᵐ⁻¹(V_i, K_{n+1}) ⟶ Hᵐ⁻¹(V_i, K_n)` and `Hᵐ(V_i, K_{n+1}) ⟶ Hᵐ(V_i, K_n)` are isomorphisms
for `n ≥ n(V)`; Stacks 0D6L then gives the injectivity of `Hᵐ(K)(V) ⟶ Hᵐ(K_{n(V)})(V)` that
forces `Hᵐ(E) ⟶ Hᵐ(K)` to be an isomorphism.  Stacks 0D6L is itself a gap.

## References

* [Stacks Project, Tag 0D6M](https://stacks.math.columbia.edu/tag/0D6M)
* [Stacks Project, Tag 071G](https://stacks.math.columbia.edu/tag/071G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u wRing wModule

namespace Stacks.Cohomology.SiteModuleCohomology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Evaluation of a sheaf of modules at an object of the site is additive. -/
local instance evaluation_additive (O : Sheaf J RingCat.{wRing}) (U : Cᵒᵖ) :
    (SheafOfModules.evaluation.{wModule} O U).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

/-- **Cohomology of a sheaf of modules over an object of a ringed site (Stacks 071G).**  The
`p`-th cohomology `Hᵖ(U, F)` is the `p`-th right derived functor of the sections functor
`Γ(U, -) = SheafOfModules.evaluation O (op U)`, evaluated at `F`; it is a module over the ring
`O(U)` of sections of the structure sheaf over `U`. -/
@[stacks 071G "the right derived functors of `Γ(U, -)`, computed from an injective resolution"]
def siteModuleCohomology (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [EnoughInjectives (SheafOfModules.{wModule} O)]
    (U : C) (p : ℕ) (F : SheafOfModules.{wModule} O) :
    ModuleCat.{wModule} (O.obj.obj (op U)) :=
  ((SheafOfModules.evaluation.{wModule} O (op U)).rightDerived p).obj F

end Stacks.Cohomology.SiteModuleCohomology

end
