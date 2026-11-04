module

public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethQcqs
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact

/-!
# The cokernel of a map of modules, read on the spectrum

The functor `M ↦ M^~` from modules to quasi-coherent modules on `Spec R` is a left adjoint, so
it preserves cokernels. A morphism of quasi-coherent modules on `Spec R` which is a map of
`R`-modules read through two isomorphisms therefore has the sheaf attached to the cokernel of
that map of modules as its cokernel, and its cokernel vanishes exactly when the map of modules
is surjective.

This is what a stage of a complete dévissage built out of algebraic data needs: the module
dévissed by the next stage is the cokernel of the stage's map of sheaves, while the algebraic
dévissage carries the quotient `M ⧸ range α`.

## Main definitions

* `AlgebraicGeometry.cokernelTildeIso`: **the cokernel of a map of sheaves conjugated to `α^~` is
  the sheaf attached to `M ⧸ range α`.**

## Main results

* `AlgebraicGeometry.tildeFunctor_preservesCokernel`: the functor `M ↦ M^~` preserves the
  cokernel of a map.
* `AlgebraicGeometry.isZero_cokernel_of_surjective_of_tilde_comm`: the cokernel of a map of
  sheaves conjugated to `α^~` vanishes when `α` is surjective.

## Implementation notes

Additivity of `AlgebraicGeometry.tilde.functor` is passed explicitly as
`AlgebraicGeometry.KunnethQcqs.tilde_additive`. Preservation of finite colimits is
`Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor`.

The hypothesis relating the two maps is a commuting square of the map of sheaves with `α^~`, with
isomorphisms on the two sides; `CategoryTheory.Limits.cokernel.mapIso` turns it into an
isomorphism of cokernels. The final identification of the cokernel in `ModuleCat` with the
quotient by the range is `ModuleCat.cokernelIsoRangeQuotient`.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- **The functor `M ↦ M^~` takes the cokernel of a map of modules to the cokernel of the
induced map of sheaves.** -/
public def tildeFunctor_preservesCokernel {M P : ModuleCat.{u} R} (φ : M ⟶ P) :
    cokernel ((tilde.functor R).map φ) ≅ (tilde.functor R).obj (cokernel φ) :=
  haveI := Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor R
  haveI := KunnethQcqs.tilde_additive R
  (PreservesCokernel.iso (tilde.functor R) φ).symm

/-- **The cokernel of a map of sheaves conjugated to `α^~` is the sheaf attached to the quotient
of the target of `α` by its range.** -/
public def cokernelTildeIso {G₁ G₂ : (Spec R).Modules} (β : G₁ ⟶ G₂) {M P : ModuleCat.{u} R}
    (e₁ : G₁ ≅ (tilde.functor R).obj M) (e₂ : G₂ ≅ (tilde.functor R).obj P) (φ : M ⟶ P)
    (hcomm : β ≫ e₂.hom = e₁.hom ≫ (tilde.functor R).map φ) :
    cokernel β ≅ (tilde.functor R).obj (ModuleCat.of R (P ⧸ LinearMap.range φ.hom)) :=
  (cokernel.mapIso β ((tilde.functor R).map φ) e₁ e₂ hcomm).trans
    ((tildeFunctor_preservesCokernel φ).trans
      ((tilde.functor R).mapIso (ModuleCat.cokernelIsoRangeQuotient φ)))

/-- **The cokernel of a map of sheaves conjugated to `α^~` vanishes when `α` is surjective.**
A left adjoint preserves epimorphisms, and the cokernel of an epimorphism is zero. -/
public theorem isZero_cokernel_of_surjective_of_tilde_comm {G₁ G₂ : (Spec R).Modules}
    (β : G₁ ⟶ G₂) {M P : ModuleCat.{u} R} (e₁ : G₁ ≅ (tilde.functor R).obj M)
    (e₂ : G₂ ≅ (tilde.functor R).obj P) (φ : M ⟶ P)
    (hcomm : β ≫ e₂.hom = e₁.hom ≫ (tilde.functor R).map φ)
    (hsurj : Function.Surjective φ.hom) : IsZero (cokernel β) := by
  have : Epi φ := ConcreteCategory.epi_of_surjective _ hsurj
  have := Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor R
  have : Epi ((tilde.functor R).map φ) := (tilde.functor R).map_epi φ
  have : Epi β := by
    have h : β = e₁.hom ≫ (tilde.functor R).map φ ≫ e₂.inv := by
      rw [← Category.assoc, ← hcomm, Category.assoc, e₂.hom_inv_id, Category.comp_id]
    rw [h]
    infer_instance
  exact isZero_cokernel_of_epi β

end AlgebraicGeometry

end
