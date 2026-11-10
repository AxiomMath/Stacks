module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AlgebraTransport

/-!
# The transport of a quadruple along a homomorphism of graded algebras is functorial

`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.algebraTransport` reads a quadruple for
`ℬ` as a quadruple for `𝒜` along a unital homomorphism `Φ : 𝒜 ⟶ ℬ` whose components are
isomorphisms, and
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.algebraTransport` does the same for the
map `ψ` alone.  Both were introduced with their compatibility with the pullback along a morphism
of test schemes, but with no law describing how they compose.

This file supplies the two missing laws: transporting along the identity homomorphism changes
nothing, and transporting along `Φ` after transporting along `Ψ` is transporting along the
composite `Φ ∘ Ψ`.  In other words `algebraTransport` is a functor in the homomorphism, which is
what `Twisting.algebraTransport_pullback` is for the test scheme.

## Why these are needed

They are what lets a coherence *between* comparison homomorphisms be turned into a statement
about the transported quadruples.  The restriction datum of Stacks 084A — see
`AlgebraicGeometry.Space.GradedAlgebraRestriction` — carries its identity coherence and its
cocycle condition as equations of unital homomorphisms, stated against
`Stacks.Conormal.gradedPullbackId` and
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraCompHomOf`.  Those equations say
nothing about quadruples until one knows that transporting along the two sides of such an
equation gives the same quadruple, and that is exactly `algebraTransport_id` and
`algebraTransport_comp` below.  Without them the coherences cannot be consumed at all.

## Main statements

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.algebraTransport_id` and
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.algebraTransport_comp`: the two laws
  for the map `ψ`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.algebraTransport_id` and
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.algebraTransport_comp`: the two laws
  for a quadruple.

## Implementation notes

Both laws are degreewise and hold for the stated reason at once: the component of
`Twisting.algebraTransport Φ χ` in degree `i` is the inverse image of `Φ` in degree `i d`
followed by the component of `χ`, so the identity homomorphism contributes the inverse image of
an identity and the composite contributes the inverse image of a composite.  Only
`CategoryTheory.Functor.map_id` and `CategoryTheory.Functor.map_comp` are used.

The quadruple laws take the invertibility hypothesis of each factor *and* of the composite as
separate arguments.  This costs nothing, `CategoryTheory.IsIso` being a proposition, and it keeps
the statements usable without the caller having to produce the composite's hypothesis in a
particular form; the instance
`SheafOfModules.GradedAlgebra.UnitalHom.isIso_comp_app` discharges it by `inferInstance`.

No invertibility is needed for the `Twisting` laws, matching
`Twisting.algebraTransport` itself, which asks for none.
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {T X : Scheme.{u}}

/-! ### The two laws for the map `ψ` -/

namespace Twisting

variable {A B C : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)}
    {d : ℤ} {f : T ⟶ X} {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **Transporting the map `ψ` along the identity homomorphism changes nothing.** In degree `i`
the transport prefixes the inverse image of the identity of the degree-`i d` piece, which is the
identity. -/
theorem algebraTransport_id (χ : Twisting f A d L) :
    algebraTransport (SheafOfModules.GradedAlgebra.UnitalHom.id A) χ = χ :=
  Twisting.ext fun i => by
    change (pullbackFunctor (ringedSpaceHom f)).map (𝟙 (A.piece (i * d))) ≫ χ.app i = χ.app i
    rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Transporting the map `ψ` along a composite is transporting along the two factors in
turn.** In degree `i` both sides are the inverse image of `Φ ∘ Ψ` in degree `i d` followed by the
component of `χ`, the inverse image being a functor. -/
theorem algebraTransport_comp (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (Ψ : SheafOfModules.GradedAlgebra.UnitalHom B C) (χ : Twisting f C d L) :
    algebraTransport Φ (algebraTransport Ψ χ) = algebraTransport (Φ.comp Ψ) χ :=
  Twisting.ext fun i => by
    change (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * d)) ≫
        (pullbackFunctor (ringedSpaceHom f)).map (Ψ.app (i * d)) ≫ χ.app i =
      (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * d) ≫ Ψ.app (i * d)) ≫ χ.app i
    rw [CategoryTheory.Functor.map_comp, Category.assoc]

end Twisting

/-! ### The two laws for a quadruple -/

namespace Quadruple

variable {A B C : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)}
    {d : ℤ} {f : T ⟶ X}

/-- **Transporting a quadruple along the identity homomorphism changes nothing.** The invertible
module and the two propositional fields are untouched, and the map `ψ` is unchanged by
`Twisting.algebraTransport_id`. -/
theorem algebraTransport_id
    (h : ∀ n : ℤ, IsIso ((SheafOfModules.GradedAlgebra.UnitalHom.id A).app n))
    (P : Quadruple f A d) :
    algebraTransport (SheafOfModules.GradedAlgebra.UnitalHom.id A) h P = P :=
  Quadruple.ext rfl fun i =>
    heq_of_eq (congrArg (Twisting.app · i) (Twisting.algebraTransport_id P.twisting))

/-- **Transporting a quadruple along a composite is transporting along the two factors in
turn.** The invertible module is the same throughout, so the two quadruples are compared by
`Twisting.algebraTransport_comp` on the map `ψ` alone.

This is the law that lets the cocycle condition of a restriction datum — an equation of unital
homomorphisms — be read as an equation of restricted quadruples. -/
theorem algebraTransport_comp (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (Ψ : SheafOfModules.GradedAlgebra.UnitalHom B C) (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
    (hΨ : ∀ n : ℤ, IsIso (Ψ.app n)) (hΦΨ : ∀ n : ℤ, IsIso ((Φ.comp Ψ).app n))
    (P : Quadruple f C d) :
    algebraTransport Φ hΦ (algebraTransport Ψ hΨ P) = algebraTransport (Φ.comp Ψ) hΦΨ P :=
  Quadruple.ext rfl fun i =>
    heq_of_eq (congrArg (Twisting.app · i) (Twisting.algebraTransport_comp Φ Ψ P.twisting))

/-- **Transporting a quadruple along a degreewise invertible homomorphism and then along its
inverse changes nothing**, the two composites of a degreewise invertible unital homomorphism with
its inverse being the identity. -/
theorem algebraTransport_inverse_comp (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    [inst : ∀ n : ℤ, IsIso (Φ.app n)]
    (hinv : ∀ n : ℤ, IsIso (Φ.inverse.app n)) (hc : ∀ n : ℤ, IsIso ((Φ.inverse.comp Φ).app n))
    (P : Quadruple f B d) :
    algebraTransport Φ.inverse hinv (algebraTransport Φ inst P) =
      algebraTransport (SheafOfModules.GradedAlgebra.UnitalHom.id B)
        (fun n => by
          rw [Φ.inverse_comp] at hc
          exact hc n) P := by
  rw [algebraTransport_comp Φ.inverse Φ hinv inst hc]
  congr 1
  exact Φ.inverse_comp

end Quadruple

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
