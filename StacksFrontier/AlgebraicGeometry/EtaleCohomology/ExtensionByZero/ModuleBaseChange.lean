module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage

/-!
# Extension by zero of sheaves of modules commutes with inverse image

For an étale morphism `j : U ⟶ X` and an arbitrary morphism `f : Y ⟶ X`, with projections
`f' : U ×_X Y ⟶ U` and `j' : U ×_X Y ⟶ Y`, extension by zero of étale sheaves of `Λ`-modules on
Mathlib's small étale sites satisfies `j'_! ∘ (f')^{-1} ≅ f^{-1} ∘ j_!` ([Stacks, Tag 03S6]). The
proof is that of the abelian case, `Stacks.EtaleCohomology.extensionByZeroBaseChangeIso`: both
sides are left adjoints, of `(f')_* ∘ (j')^{-1}` and of `j^{-1} ∘ f_*`, and those right adjoints
agree for sheaves valued in any category
(`Stacks.EtaleCohomology.smallEtaleRestrictionPushforwardBaseChangeIso`).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroBaseChangeIso`: the isomorphism
  `j'_! ∘ (f')^{-1} ≅ f^{-1} ∘ j_!` of functors on étale sheaves of `Λ`-modules, natural in the
  sheaf.

## References

* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u r

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
  AlgebraicGeometry.Etale.instIsMultiplicativeScheme

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {U X Y : Scheme.{u}} (j : U ⟶ X) [Etale j] (f : Y ⟶ X)

/-- **Stacks 03S6 for sheaves of modules on Mathlib's small étale sites.** Extension by zero
commutes with inverse image: `j'_! ∘ (f')^{-1} ≅ f^{-1} ∘ j_!`, naturally in the sheaf, for the
projections `f' : U ×_X Y ⟶ U` and `j' : U ×_X Y ⟶ Y`. -/
def etaleModuleExtensionByZeroBaseChangeIso :
    etaleModuleInverseImage.{u, r} Λ (pullback.fst j f) ⋙
        etaleModuleExtensionByZero.{u, r} Λ (pullback.snd j f) ≅
      etaleModuleExtensionByZero.{u, r} Λ j ⋙ etaleModuleInverseImage.{u, r} Λ f :=
  Adjunction.leftAdjointCompIso
    (etaleModuleInverseImageAdj.{u, r} Λ (pullback.fst j f))
    (etaleModuleExtensionByZeroAdj.{u, r} Λ (pullback.snd j f))
    ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).comp (etaleModuleInverseImageAdj.{u, r} Λ f))
    (smallEtaleRestrictionPushforwardBaseChangeIso.{u, _, _} j f
      (ModuleCat.{max (u + 1) r} Λ))

end Stacks.EtaleCohomology

end
