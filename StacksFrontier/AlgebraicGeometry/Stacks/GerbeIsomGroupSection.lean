module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Gerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# A section of a gerbe is surjective

Let `π : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` making `𝒳` a gerbe over `𝒴` in the
sense of Stacks 06QC, and let `x : 𝒴 ⟶ 𝒳` be a *section* of `π`, that is a 1-morphism together
with a 2-isomorphism `x ≫ π ≅ 𝟙 𝒴`. Then `x` is surjective in the sense of Stacks 04ZS.

## Main results

* `AlgebraicGeometry.Stack.isSurjectiveOnObjects_of_section_of_isGerbeOver`: a section of a
  gerbe is surjective on objects in the sense of Stacks 06D4.
* `AlgebraicGeometry.Stack.isSurjective_of_section_of_isGerbeOver`: a section of a gerbe is
  surjective.

## References

* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
* [Stacks Project, Tag 06P1](https://stacks.math.columbia.edu/tag/06P1)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- A section of a gerbe is surjective on objects: every object of `𝒳` over the spectrum of a
field becomes isomorphic, after a field extension, to the image under `x` of a point of `𝒴`. -/
theorem isSurjectiveOnObjects_of_section_of_isGerbeOver
    (π : 𝒳 ⟶ 𝒴) (x : 𝒴 ⟶ 𝒳) (hx : x ≫ π ≅ 𝟙 𝒴)
    (hπ : AlgebraicStacks.IsGerbeOver B S hS π) :
    IsSurjectiveOnObjects B S hS 𝒴.val.val.p 𝒳.val.val.p x.hom.hom.toFunctor := by
  intro T hT ξ hξ
  have hTy : 𝒴.val.val.p.obj (π.hom.hom.toFunctor.obj ξ) = T :=
    (BasedFunctor.w_obj π.hom.hom ξ).trans hξ
  subst hTy
  have hb := hx.hom.hom.hom.isHomLift' (π.hom.hom.toFunctor.obj ξ)
  obtain ⟨R, hR, hcov⟩ := hπ.locally_full _ hb
  obtain ⟨V, g, hV, hgR⟩ := exists_isFieldObject_arrow_of_mem_topology B S hS hT hR
  obtain ⟨a₁, a₁', e₁, e₁', a, h₁, h₂, h₃, -⟩ := hcov g hgR
  rw [CatFiberedInGroupoids.homFunctor_comp_p π.hom] at h₁ h₂ h₃
  obtain ⟨u, φ, hφ⟩ :=
    𝒴.val.isFiberedInGroupoids.exists_lift g (π.hom.hom.toFunctor.obj ξ) rfl
  have := 𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift g e₁
  refine ⟨V, hV, g, u, IsHomLift.domain_eq 𝒴.val.val.p g φ,
    Functor.IsStronglyCartesian.map 𝒳.val.val.p g e₁ (Category.id_comp g).symm
      (x.hom.hom.toFunctor.map φ) ≫ a ≫ e₁', inferInstance⟩

/-- Let `π : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` making `𝒳` a gerbe over `𝒴`,
and let `x : 𝒴 ⟶ 𝒳` be a section of `π`, i.e. a 1-morphism with a 2-isomorphism
`x ≫ π ≅ 𝟙 𝒴`. Then `x` is surjective. -/
@[stacks 06QG "part (3): surjectivity of the section"]
theorem isSurjective_of_section_of_isGerbeOver
    (π : 𝒳 ⟶ 𝒴) (x : 𝒴 ⟶ 𝒳) (hx : x ≫ π ≅ 𝟙 𝒴)
    (hπ : AlgebraicStacks.IsGerbeOver B S hS π) :
    IsSurjective B S hS x :=
  pointsMap_surjective_of_isSurjectiveOnObjects B S hS x
    (isSurjectiveOnObjects_of_section_of_isGerbeOver B S hS π x hx hπ)

end AlgebraicGeometry.Stack

end
