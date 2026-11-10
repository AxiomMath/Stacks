module

public import
StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergenceUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Convergence of the truncation tower under a uniform cohomological bound

Let `(C, O)` be a ringed site and let `E` be an object of the derived category of `O`-modules.
Suppose a subset `B` of the objects of `C` covers every object, and that there is a single
integer `d ≥ 0` with `H^p(V, H^q(E)) = 0` for every `V ∈ B`, every `p > d` and every `q < 0`.
Then the canonical map from `E` to the derived limit of its truncation tower `n ↦ τ_{≥ -n} E` is
an isomorphism.

The module universe is `max u v r w`, at which sheafification of abelian presheaves, the
inversion of exactly the locally bijective maps by sheafification, enough injectives for sheaves
of `O`-modules and the product of the truncation tower in the derived category are all theorems,
so the only class hypothesis is the site's own category structure.

## Main results

* `Stacks.Cohomology.UniformBound.isIso_to_isDerivedLimit_truncGETower_of_vanishing_uniform`:
  under a uniform cohomological bound on a covering family of objects, `E` is the derived limit
  of its truncation tower.

## References

* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
* [Stacks Project, Tag 0D6M](https://stacks.math.columbia.edu/tag/0D6M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v r w

namespace Stacks.Cohomology.UniformBound

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules

variable {C : Type u} [instC : Category.{v} C] {J : GrothendieckTopology C}

/-- Let `O` be a sheaf of rings on a site `C` and let `E` be an object of the derived category of
sheaves of `O`-modules.  Suppose there are an integer `d ≥ 0` and a set `B` of objects of `C`
such that every object of `C` has a covering whose members are elements of `B`, and such that
`H^p(V, H^q(E)) = 0` for all `p > d`, all `q < 0` and all `V ∈ B`.  Then the canonical map
`E ⟶ R lim τ_{≥ -n} E` is an isomorphism.

Here `R lim τ_{≥ -n} E` is an object `L` with a distinguished triangle
`L ⟶ ∏ τ_{≥ -n} E ⟶ ∏ τ_{≥ -n} E ⟶ L[1]`, and `c : E ⟶ L` is the map whose composites with
the product projections are the truncation maps `E ⟶ τ_{≥ -n} E`. -/
@[stacks 0D6P]
theorem isIso_to_isDerivedLimit_truncGETower_of_vanishing_uniform
    (O : Sheaf J RingCat.{r})
    (E : DerivedCategory (SheafOfModules.{max u v r w} O))
    (d : ℤ) (hd : 0 ≤ d) (B : Set C)
    (basisCover : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U,
      𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    (vanishing : ∀ (V : C), B V → ∀ (p : ℕ), d < (p : ℤ) → ∀ (q : ℤ), q < 0 →
      IsZero (@moduleCohomology C instC J O hasSheafifyMax.{u, v, r, w}
        wEqualsLocallyBijectiveMax.{u, v, r, w}
        (SiteModules.moduleSheavesEnoughInjectives.{u, v, r, w} O) V p
        ((DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w} O) q).obj E)))
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
    (fun _ _ m ↦ d + max 0 m)
    (fun V _ ↦ {𝒰 | 𝒰.sieve₀ ∈ J V ∧ ∀ i, B (𝒰.X i)})
    (fun _ _ _ h𝒰 ↦ h𝒰.1) ?_
    (fun _ _ _ h𝒰 i p m hm ↦ vanishing _ (h𝒰.2 i) p (by omega) _ (by omega))
    L c q δ hL hc
  intro V hV 𝒰 h𝒰
  choose F hF using fun i : 𝒰.I₀ ↦ basisCover (𝒰.X i)
  refine ⟨𝒰.bind F, ⟨?_, fun ij ↦ (hF ij.1).2 ij.2⟩,
    ⟨fun ij ↦ ij.1, fun ij ↦ (F ij.1).f ij.2, fun ij ↦ rfl⟩⟩
  have hbind : Sieve.generate
      (Presieve.bindOfArrows 𝒰.X 𝒰.f (fun i ↦ (F i).presieve₀)) ∈ J V :=
    J.bindOfArrows h𝒰 (fun i ↦ by
      simpa [PreZeroHypercover.presieve₀] using (hF i).1)
  simpa [PreZeroHypercover.bind, PreZeroHypercover.sieve₀,
    Presieve.bindOfArrows_ofArrows] using hbind

end Stacks.Cohomology.UniformBound

end
