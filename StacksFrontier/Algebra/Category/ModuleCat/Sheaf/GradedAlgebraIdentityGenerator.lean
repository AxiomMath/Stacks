module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison

/-!
# The exterior-algebra universal property at the identity generator

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of graded `R`-algebras. The
statement that `A` is the exterior algebra **of its own degree-one piece**, on the identity
generator

`IsExteriorAlgebra A (𝟙 (A.piece 1))`,

is the form in which the universal property is both proved and consumed whenever no generating
sheaf of modules is chosen in advance: the degree-one piece *is* the generating module, and the
comparison homomorphism out of a chosen exterior algebra is the `desc` at that generator.

This file supplies the transport of that statement along a homomorphism of sheaves of graded
algebras which is an isomorphism in every degree. There is no new mathematics here: the content
is `SheafOfModules.GradedAlgebra.IsUniversal.ofDegreewiseIso`, which moves a universal property
along such a homomorphism, followed by
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.comp_iso`, which moves the generating sheaf of
modules back. What the file removes is the need to perform that two-step dance by hand at each
link of a chain of such homomorphisms.

## Main results

* `SheafOfModules.GradedAlgebra.UnitalHom.isIso_inverse_app`: the degreewise inverse of a
  degreewise invertible homomorphism is itself degreewise invertible, as an instance. This is
  what makes a transport usable in **either** direction.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.ofDegreewiseIso`: a sheaf of graded algebras
  receiving a degreewise invertible homomorphism from an exterior algebra of `M` is an exterior
  algebra of `M`, on the image of the generator.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_ofDegreewiseIso`: **the transport at the
  identity generator.** If `A` is the exterior algebra of its own degree-one piece and
  `φ : A ⟶ B` is an isomorphism in every degree, then `B` is the exterior algebra of *its* own
  degree-one piece. Neither the source nor the target module is mentioned, so a chain of such
  homomorphisms composes with no bookkeeping about generators at all.

## Implementation notes

**Why the identity-generator form is not an instance of the plain one.**
`IsUniversal.ofDegreewiseIso` lands on the generator `𝟙 (A.piece 1) ≫ φ.app 1`, whose
*source* is `A.piece 1`, while the conclusion asked for has source `B.piece 1`. The two are
isomorphic — by `φ.app 1` itself — and `IsExteriorAlgebra.comp_iso` precomposes with the
inverse, after which `inv (φ.app 1) ≫ 𝟙 ≫ φ.app 1` is the identity of `B.piece 1`. It is this
rewriting step, and the `IsIso` instance for the degreewise inverse that the backwards direction
needs, that were being re-derived at every use site.

**No `@[stacks]` attribute.** Nothing here is a clause of a tag: this is the transport primitive
that a local-to-global argument through a chain of presentations of one graded algebra consumes.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u w a

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {A B : GradedAlgebra.{w, a} R}

/-- **The degreewise inverse of a degreewise invertible homomorphism of sheaves of graded
algebras is itself degreewise invertible.** Each component of
`SheafOfModules.GradedAlgebra.UnitalHom.inverse` is by definition the inverse of the
corresponding component of `φ`, so this is `CategoryTheory.IsIso.inv_isIso` read through that
definition. As an instance it is what makes a transport along `φ` usable in both directions. -/
instance UnitalHom.isIso_inverse_app (φ : UnitalHom A B) [∀ n, IsIso (φ.app n)] (n : ℤ) :
    IsIso (φ.inverse.app n) :=
  inferInstanceAs (IsIso (inv (φ.app n)))

variable {M : SheafOfModules.{a} R}

/-- **An exterior-algebra universal property transports along a degreewise invertible
homomorphism of sheaves of graded algebras.** If `A` with the degree-one generator `ι` is the
exterior algebra of `M` and `φ : A ⟶ B` is an isomorphism in every degree, then `B` with the
generator `ι ≫ φ.app 1` is the exterior algebra of `M`.

This is `SheafOfModules.GradedAlgebra.IsUniversal.ofDegreewiseIso` at `P = SquareZero`, whose
side condition is free: the square of the image of a local section is the image of its square
(`SheafOfModules.GradedAlgebra.SquareZero.compUnitalHom`). -/
theorem IsExteriorAlgebra.ofDegreewiseIso {ι : M ⟶ A.piece 1} (h : IsExteriorAlgebra A ι)
    (φ : UnitalHom A B) [∀ n, IsIso (φ.app n)] : IsExteriorAlgebra B (ι ≫ φ.app 1) :=
  h.isUniversal.ofDegreewiseIso φ (h.1.compUnitalHom φ)

/-- **The transport of the exterior-algebra universal property at the identity generator.** If
`A` is the exterior algebra of its own degree-one piece and `φ : A ⟶ B` is an isomorphism in
every degree, then `B` is the exterior algebra of its own degree-one piece.

The generating sheaf of modules is not a parameter on either side, so a chain of degreewise
invertible homomorphisms transports the statement with no bookkeeping: each link is one
application of this lemma, in either direction by
`SheafOfModules.GradedAlgebra.UnitalHom.isIso_inverse_app`.

`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.ofDegreewiseIso` lands on the generator
`𝟙 (A.piece 1) ≫ φ.app 1`, out of `A.piece 1`;
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.comp_iso` moves the generating module to
`B.piece 1` along the inverse of `φ.app 1`, and the composite generator is then the identity. -/
theorem IsExteriorAlgebra.id_ofDegreewiseIso (h : IsExteriorAlgebra A (𝟙 (A.piece 1)))
    (φ : UnitalHom A B) [∀ n, IsIso (φ.app n)] : IsExteriorAlgebra B (𝟙 (B.piece 1)) := by
  have hcomp := (h.ofDegreewiseIso φ).comp_iso (inv (φ.app 1)) inferInstance
  rwa [Category.id_comp, IsIso.inv_hom_id] at hcomp

/-- **The transport at the identity generator, backwards.** The direction a local-to-global
argument uses when the universal property is established on the presentation a local computation
produces and is needed on the presentation the comparison map is built in. -/
theorem IsExteriorAlgebra.id_of_degreewiseIso (h : IsExteriorAlgebra B (𝟙 (B.piece 1)))
    (φ : UnitalHom A B) [∀ n, IsIso (φ.app n)] : IsExteriorAlgebra A (𝟙 (A.piece 1)) :=
  h.id_ofDegreewiseIso φ.inverse

end SheafOfModules.GradedAlgebra

end
