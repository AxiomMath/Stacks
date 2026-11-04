module

public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.Deformation.Examples.Spaces

/-!
# The action of the residue field on the modules of an algebraic space over it

In the situation of Stacks 0E3Z, an algebraic space `X` over the residue field `k` comes with its
structure morphism `toK : X ⟶ Spec k`, a morphism to an object of the big fppf site.  Pulling the
functions on `Spec k` back along `toK` gives a ring homomorphism `k ⟶ Γ(X, 𝒪_X)`, through which
`k` acts on every `𝒪_X`-module, and so on the `Ext` groups out of the naive cotangent complex of
Stacks 0E41 and 0E42.

## Main definitions

* `Deformation.Examples.spaceResidueFieldRingHom`: the ring homomorphism `k →+* Γ(X, 𝒪_X)`.

## References

* [Stacks Project, Tag 0E3Z](https://stacks.math.columbia.edu/tag/0E3Z)
* [Stacks Project, Tag 0E42](https://stacks.math.columbia.edu/tag/0E42)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Cohomology.SiteModules

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))

/-- **The residue field acting on the modules of an algebraic space over it.**  For an algebraic
space `X` over `Spec k` with structure morphism `toK`, the ring homomorphism `k →+* Γ(X, 𝒪_X)`
which sends `c` to the pullback along `toK` of the function `c` on `Spec k`. -/
def spaceResidueFieldRingHom (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
    (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))) :
    k →+* GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.structureSheaf B (Spec (.of Λ)) hΛ X hX)) :=
  (Space.pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ ⟨X, hX⟩
      (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)) (ObjectProperty.homMk toK)).comp
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

end Deformation.Examples
