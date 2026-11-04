module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleDirectImageAffineVanishing

/-!
# Higher direct images along a 1-morphism of stacks represented by affine schemes

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks which are representable by affine schemes.
For a locally quasi-coherent module `F` on `𝒳_étale` the higher direct images `Rⁱf_*F`, `i > 0`,
computed in the étale topology, vanish. This is the vanishing half of clause (4) of
**Stacks 076Z** in the proofs of **Stacks 075Z** and **Stacks 0765**, which in the source is
read off **Stacks 075P** and the vanishing of higher cohomology of quasi-coherent modules on
affine schemes.

## Main results

* `AlgebraicGeometry.Stack.isZero_stackModuleHigherDirectImage_of_isAffineRepresentable`.

## References

* [Stacks Project, Tag 075P](https://stacks.math.columbia.edu/tag/075P)
* [Stacks Project, Tag 075Z](https://stacks.math.columbia.edu/tag/075Z)
* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **The higher direct images along a 1-morphism of algebraic stacks represented by affine
schemes vanish on locally quasi-coherent modules.** For `f : 𝒳 ⟶ 𝒴` with `𝒳` and `𝒴`
representable by affine schemes and `F` a locally quasi-coherent module on `𝒳_étale`
(**Stacks 06WJ**), `Rⁱf_*F = 0` for `i > 0`, the higher direct images computed in the étale
topology at the universe of the schemes. -/
theorem isZero_stackModuleHigherDirectImage_of_isAffineRepresentable
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒳)
    (h𝒴 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒴)
    (F : StackModules B S hS .etale 𝒳)
    (hF : IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val)
    (i : ℕ) (hi : 0 < i) :
    IsZero ((stackModuleHigherDirectImage B S hS f .etale i).obj F) := by
  choose t ht hx₀ using fun y : 𝒴.val.val.obj =>
    AlgebraicStacks.exists_isTerminal_costructuredArrow_of_isAffineRepresentable B S hS f h𝒳 h𝒴 y
  exact isZero_stackModuleHigherDirectImage_etale_of_isTerminal B S hS f (fun y _ => t y)
    (fun y _ => (ht y).some) hx₀ F
    (FibredSite.isCartesianAlongEtaleAffines_of_isLocallyQuasicoherent B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids E h F hF) i hi

end AlgebraicGeometry.Stack
