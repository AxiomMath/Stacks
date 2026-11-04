module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceSurjectiveSectionIso

/-!
# The deformation of an algebraic space over `k[ε]` realizing an extension

In the situation of `Deformation.Examples.spaceSurjToDual`, let `X ⊂ X'` be the thickening
realizing an extension `P` of `f⁻¹𝒪_{Spec k}`-algebras of `𝒪_X` by `𝒪_X ⊗_k k`, with its
morphism `X' ⟶ Spec k[ε]`. When `X' ⟶ Spec k[ε]` is flat and `X = X' ×_{Spec k[ε]} Spec k`,
the pair `(X' ⟶ Spec k[ε], X ⟶ X')` is an object of the deformation category of `X` lying over
the dual numbers. This is the deformation of the surjectivity step of the second display of
[Stacks Project, Tag 0E41].

## Main definitions

* `Deformation.Examples.spaceDualResidue`: the residue map `k[ε] ⟶ k`.
* `Deformation.Examples.spaceSurjFamily`: the flat family `X' ⟶ Spec k[ε]`.
* `Deformation.Examples.spaceSurjPoint`: the point of the fibre over `k[ε]`.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 0E3Z](https://stacks.math.columbia.edu/tag/0E3Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space Deformation.Artin

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

variable (Λ k) in
/-- **The residue map `k[ε] ⟶ k`**, as a morphism of `𝒞_Λ`. -/
abbrev spaceDualResidue : spaceDualNumbers (Λ := Λ) (k := k) ⟶ residueFieldBase Λ k :=
  isTerminal_residueFieldBase.from _

/-- **The closed immersion `Spec k ⟶ Spec k[ε]`.** -/
abbrev spaceDualImmersion :
    spaceBaseOver B hΛ hSpec (residueFieldBase Λ k) ⟶
      spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k)) :=
  spaceBaseOverMap B hΛ hSpec (spaceDualResidue Λ k)

variable (P : AlgebraExtension (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
  (inverseImageBaseMap B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK))
  (spaceRankOneCoefficient B hΛ hSpec X hX toK))

/-- **The flat family `X' ⟶ Spec k[ε]`**, for a flat `X' ⟶ Spec k[ε]`. -/
def spaceSurjFamily
    (hflat : Space.IsFlat B (Spec (.of Λ)) hΛ (spaceSurjToDual B hΛ hSpec X hX toK P).hom) :
    FlatAlgebraicSpaceFamily B hΛ hSpec where
  base := spaceDualNumbers (Λ := Λ) (k := k)
  space := (spaceSurjAmbient B hΛ hSpec X hX toK P).1
  algebraic := (spaceSurjAmbient B hΛ hSpec X hX toK P).2
  toBase := (spaceSurjToDual B hΛ hSpec X hX toK P).hom
  flat := hflat

/-- **The deformation of `X` over `k[ε]` realizing `P`**: the flat family `X' ⟶ Spec k[ε]` with
`X ⟶ X'`, when `X = X' ×_{Spec k[ε]} Spec k`. -/
def spaceSurjPoint
    (hflat : Space.IsFlat B (Spec (.of Λ)) hΛ (spaceSurjToDual B hΛ hSpec X hX toK P).hom)
    (hcart : IsPullback (spaceSurjImmersion B hΛ hSpec X hX toK P).hom toK
      (spaceSurjToDual B hΛ hSpec X hX toK P).hom
      (yoneda.map (spaceDualImmersion B hΛ hSpec))) :
    (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      ((squareZeroExtensionArtinian Λ k).obj (FGModuleCat.of k k)) :=
  ⟨Over.mk (X := spaceSpecialFiber B hΛ hSpec X hX toK)
    (Y := spaceSurjFamily B hΛ hSpec X hX toK P hflat)
    { base := spaceDualResidue Λ k
      map := (spaceSurjImmersion B hΛ hSpec X hX toK P).hom
      cartesian := hcart }, rfl⟩

end Deformation.Examples

end
