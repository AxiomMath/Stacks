module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequenceSquare
public import StacksFrontier.Topology.Sheaves.Modules.ConormalSequenceStalkExtension

/-!
# The stalk of the conormal map of a square of sheaves of rings

This file is the square-level analogue of the `Comparison` section of
`StacksFrontier.Topology.Sheaves.Modules.ConormalSequenceStalkExtension`: there the base sheaf `R`
and the target sheaf `B` are fixed and only the polynomial presentation varies, which is what
Stacks 08TL needs; here both may vary, which is what Stacks 08TX needs.

## Main definitions

* `Stacks.Sites.Conormal.stalkExtensionHomOfSquare`: the morphism of stalk extensions induced by
  a commutative square.

## Main results

* `Stacks.Sites.Conormal.stalkExtensionHomOfSquare_toRingHom`: its underlying ring homomorphism
  is the stalk of `ψ`.

## References

* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

namespace Stacks.Sites.Conormal

open Stacks.RelativeDifferentialStalk (algebraStalk)

section Square

variable {X : TopCat.{u}}
  (R₁ R₂ A₁ A₂ B₁ B₂ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a₁ : R₁ ⟶ A₁) (a₂ : R₂ ⟶ A₂) (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂)
  (c₁ : R₁ ⟶ B₁) (c₂ : R₂ ⟶ B₂) (ρ : R₁ ⟶ R₂) (ψ : A₁ ⟶ A₂) (β : B₁ ⟶ B₂)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₂.hom] (x : X)

/-- **A commutative square induces a morphism of the stalk extensions.**  For a square

```
B₁ ──β──▸ B₂
▲          ▲
φ₁         φ₂
│          │
A₁ ──ψ──▸ A₂
▲          ▲
a₁         a₂
│          │
R₁ ──ρ──▸ R₂
```

of sheaves of commutative rings, the stalk of `ψ` at `x` is a morphism of the extension of
`B₁ₓ` over `R₁ₓ` presented by `φ₁` into the extension of `B₂ₓ` over `R₂ₓ` presented by `φ₂`,
over the algebra structures that `ρ` and `β` induce on the stalks.

This is `Stacks.Sites.Conormal.stalkExtensionHom` with the base and the target allowed to vary;
that one is the case `ρ = 𝟙` and `β = 𝟙`. -/
def stalkExtensionHomOfSquare (hc₁ : a₁ ≫ φ₁ = c₁) (hc₂ : a₂ ≫ φ₂ = c₂)
    (ha : ρ ≫ a₂ = a₁ ≫ ψ) (hsq : ψ ≫ φ₂ = φ₁ ≫ β) :
    letI := stalkAlgebraBase R₁ B₁ c₁ x
    letI := stalkAlgebraBase R₂ B₂ c₂ x
    letI := algebraStalk ρ.hom x
    letI := algebraStalk β.hom x
    (stalkExtension R₁ A₁ B₁ a₁ φ₁ c₁ x hc₁).Hom
      (stalkExtension R₂ A₂ B₂ a₂ φ₂ c₂ x hc₂) :=
  letI := stalkAlgebraBase R₁ B₁ c₁ x
  letI := stalkAlgebraBase R₂ B₂ c₂ x
  letI := algebraStalk ρ.hom x
  letI := algebraStalk β.hom x
  { toRingHom := ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map ψ.hom).hom
    toRingHom_algebraMap := fun r =>
      (stalkFunctor_map_comp_apply a₁ ψ (a₁ ≫ ψ) rfl x r).trans
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).congr_map
            (Sheaf.hom_ext_iff.mp ha.symm)).symm ▸
          (stalkFunctor_map_comp_apply ρ a₂ (ρ ≫ a₂) rfl x r).symm)
    algebraMap_toRingHom := fun z =>
      (stalkFunctor_map_comp_apply ψ φ₂ (ψ ≫ φ₂) rfl x z).trans
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).congr_map
            (Sheaf.hom_ext_iff.mp hsq)).symm ▸
          (stalkFunctor_map_comp_apply φ₁ β (φ₁ ≫ β) rfl x z).symm) }

/-- The underlying ring homomorphism of the induced morphism of extensions is the stalk of
`ψ`. -/
theorem stalkExtensionHomOfSquare_toRingHom (hc₁ : a₁ ≫ φ₁ = c₁) (hc₂ : a₂ ≫ φ₂ = c₂)
    (ha : ρ ≫ a₂ = a₁ ≫ ψ) (hsq : ψ ≫ φ₂ = φ₁ ≫ β) :
    letI := stalkAlgebraBase R₁ B₁ c₁ x
    letI := stalkAlgebraBase R₂ B₂ c₂ x
    letI := algebraStalk ρ.hom x
    letI := algebraStalk β.hom x
    (stalkExtensionHomOfSquare R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ c₁ c₂ ρ ψ β x
        hc₁ hc₂ ha hsq).toRingHom =
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map ψ.hom).hom := rfl

end Square

end Stacks.Sites.Conormal

end

end
