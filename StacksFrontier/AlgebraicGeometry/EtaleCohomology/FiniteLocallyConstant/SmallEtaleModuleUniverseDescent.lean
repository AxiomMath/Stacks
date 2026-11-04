module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ModuleUniverseDescent

/-!
# The coefficient universe of a finite type locally constant sheaf of modules on a small étale site

Mathlib's small étale site of a scheme `S : Scheme.{u}` has objects in `Type (u + 1)` and
morphisms in `Type u`, so the smallest module universe in which its sheaves of `Λ`-modules carry
sheafification is `u + 1`, while a statement whose coefficients are modules presented in an
unrelated universe `v` has to place them in `ModuleCat.{max (u + 1) v} Λ`. On finite type locally
constant sheaves the two presentations agree, as soon as `Λ` itself is `(u + 1)`-small: such a
sheaf with sections in `ModuleCat.{max (u + 1) v} Λ` is the pointwise universe lift of one with
sections in `ModuleCat.{u + 1} Λ`.

This is `Stacks.ConstantSheaf.exists_isFiniteTypeLocallyConstantModuleSheaf_uliftFunctor_iso` at
the small étale site, and the module-coefficient companion of
`AlgebraicGeometry.exists_isFiniteLocallyConstant_smallEtale_uliftFunctor_iso`.

## Main results

* `AlgebraicGeometry.exists_isFiniteTypeLocallyConstantModuleSheaf_smallEtale_uliftFunctor_iso`:
  the universe descent, from `ModuleCat.{max (u + 1) v} Λ` to `ModuleCat.{u + 1} Λ`, of a finite
  type locally constant sheaf of `Λ`-modules on the small étale site of a scheme.

## References

* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v u r

namespace AlgebraicGeometry

/-- **A finite type locally constant sheaf of `Λ`-modules on the small étale site of a scheme
`S : Scheme.{u}` with sections in `ModuleCat.{max (u + 1) v} Λ` is the pointwise universe lift of
one with sections in `ModuleCat.{u + 1} Λ`**, which is again finite type locally constant. The
coefficient ring is assumed `(u + 1)`-small, which is what bounds the size of a finitely
generated module over it. -/
theorem exists_isFiniteTypeLocallyConstantModuleSheaf_smallEtale_uliftFunctor_iso
    (S : Scheme.{u}) (Λ : Type r) [Ring Λ] [Small.{u + 1} Λ]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{max (u + 1) v} Λ))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, v, r}
      S.smallEtaleTopology Λ F) :
    ∃ F₀ : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u, r}
          S.smallEtaleTopology Λ F₀ ∧
        Nonempty ((sheafCompose S.smallEtaleTopology
          (ModuleCat.uliftFunctor.{v, u + 1} Λ)).obj F₀ ≅ F) :=
  Stacks.ConstantSheaf.exists_isFiniteTypeLocallyConstantModuleSheaf_uliftFunctor_iso.{v, u,
    u + 1, r} S.smallEtaleTopology Λ F hF

end AlgebraicGeometry

end
