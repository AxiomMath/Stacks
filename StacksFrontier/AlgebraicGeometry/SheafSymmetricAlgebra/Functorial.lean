module

public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.HomBridge
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Scheme
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafFunctorial

/-!
# Functoriality of the symmetric algebra of a module on a scheme, at relative Proj

A morphism `u : E₁ ⟶ E₂` of `𝒪_X`-modules induces a homomorphism `Sym(E₁) ⟶ Sym(E₂)` of graded
`𝒪_X`-algebras, and hence — contravariantly — a morphism of projective bundles
`𝐏(E₂) ⟶ 𝐏(E₁)`. This file constructs the homomorphism, as a
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom` between the two
`Stacks.SymGraded.schemeSheafGradedAlgebra`s: the input from which
`Stacks.AlgebraicGeometry.ProjBundleSurjection.bundleMap` builds the morphism of projective
bundles, and to which the eventual-isomorphism and eventual-surjection theorems of Tags 07ZI and
07ZJ apply.

## The symmetric algebra in question

`Sym(E)` here is `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X E`, the degreewise
sheafification of the sectionwise symmetric algebra, whose laws
`StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Scheme` reads off. So the functoriality
already proved for it — `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraUnitalHom`, together
with its identity and composition laws — is the functoriality wanted, and the only step left is
the bridge of `StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.HomBridge`.

## Main definitions

* `Stacks.SymGraded.symUnitalHom`: the unital homomorphism `Sym(E₁) ⟶ Sym(E₂)` of sheaves of
  graded algebras induced by `u : E₁ ⟶ E₂`.
* `Stacks.SymGraded.symSheafGradedAlgebraHom`: the induced `SheafGradedAlgebraHom` of the two
  relative-Proj inputs.

## Main results

* `Stacks.SymGraded.symUnitalHom_id` and `Stacks.SymGraded.symUnitalHom_comp`: `Sym` is
  functorial.
* `Stacks.SymGraded.gen_comp_symUnitalHom_app_one`: the induced homomorphism extends `u` on the
  degree-one generators, which is what characterizes it.
* `Stacks.SymGraded.isIso_symSheafGradedAlgebraHom_app`: **for an isomorphism of modules the
  induced homomorphism is an isomorphism in every degree**, so it satisfies the eventual
  hypotheses of Tags 07ZI and 07ZJ.

## Implementation notes

**Why the universal property is not used.** `symUnitalHom` is
`symmetricAlgebraUnitalHom` rather than
`SheafOfModules.GradedAlgebra.IsUniversal.descComp` of
`AlgebraicGeometry.Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra`, even though the two are
equal by
`SheafOfModules.GradedAlgebra.IsUniversal.descComp_unique`. Reusing the existing definition
brings its identity and composition laws with it;
re-deriving them from the universal property would prove the same two theorems a second time.

**The quasi-coherence hypotheses stay hypotheses.** `symSheafGradedAlgebraHom` takes an
`IsQuasicoherentPieces` for each of the two modules, exactly as
`Stacks.SymGraded.schemeSheafGradedAlgebra` does, so that it applies to the conditional bundle of
an arbitrary module as well as to the unconditional bundle of a quasi-coherent one — where
`Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent` discharges it.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

namespace Stacks.SymGraded

universe u

variable {X : Scheme.{u}}

/-! ### Functoriality of the graded algebra -/

variable {E₁ E₂ E₃ : X.Modules}

/-- **The unital homomorphism `Sym(E₁) ⟶ Sym(E₂)` induced by `u : E₁ ⟶ E₂`**: the unique one
extending `u` followed by the degree-one generator of `Sym(E₂)`. -/
public def symUnitalHom (u : E₁ ⟶ E₂) :
    SheafOfModules.GradedAlgebra.UnitalHom (Scheme.Modules.symmetricAlgebra X E₁)
      (Scheme.Modules.symmetricAlgebra X E₂) :=
  Scheme.Modules.symmetricAlgebraUnitalHom X u

/-- The induced homomorphism extends `u`: in degree one it carries the generator of `Sym(E₁)` to
the image under `u` of the generator of `Sym(E₂)`. This characterizes it, by
`AlgebraicGeometry.Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra`. -/
public theorem gen_comp_symUnitalHom_app_one (u : E₁ ⟶ E₂) :
    Scheme.Modules.symmetricAlgebraGen X E₁ ≫ (symUnitalHom u).app 1 =
      u ≫ Scheme.Modules.symmetricAlgebraGen X E₂ :=
  Scheme.Modules.symmetricAlgebraGen_comp_symmetricAlgebraUnitalHom X u

/-- **`Sym` is functorial**: the identity induces the identity. -/
public theorem symUnitalHom_id :
    symUnitalHom (𝟙 E₁) =
      SheafOfModules.GradedAlgebra.UnitalHom.id (Scheme.Modules.symmetricAlgebra X E₁) :=
  Scheme.Modules.symmetricAlgebraUnitalHom_id X

/-- **`Sym` is functorial**: a composite induces the composite. -/
public theorem symUnitalHom_comp (u : E₁ ⟶ E₂) (v : E₂ ⟶ E₃) :
    symUnitalHom (u ≫ v) = (symUnitalHom u).comp (symUnitalHom v) :=
  Scheme.Modules.symmetricAlgebraUnitalHom_comp X u v

/-! ### The homomorphism of relative-Proj inputs -/

variable (hqc₁ : IsQuasicoherentPieces E₁) (hqc₂ : IsQuasicoherentPieces E₂)

/-- **The homomorphism of sheaf-level graded algebra data induced by a morphism of modules.**
A morphism `u : E₁ ⟶ E₂` of `𝒪_X`-modules induces a homomorphism, in the sense of Tag 07ZG, of
the two Situation 01NN inputs `Sym(E₁)` and `Sym(E₂)` of the relative Proj construction.

It is the input from which the morphism `r_ψ` of Tag 07ZG is built. -/
public def symSheafGradedAlgebraHom (u : E₁ ⟶ E₂) :
    SheafGradedAlgebraHom (schemeSheafGradedAlgebra E₁ hqc₁)
      (schemeSheafGradedAlgebra E₂ hqc₂) :=
  toSheafGradedAlgebraHom (isCommutative_symmetricAlgebra E₁)
    (vanishesInNegativeDegrees_symmetricAlgebra E₁) hqc₁
    (isCommutative_symmetricAlgebra E₂)
    (vanishesInNegativeDegrees_symmetricAlgebra E₂) hqc₂ (symUnitalHom u)

/-- The degree-`n` morphism of the induced homomorphism is the degree-`n` morphism of
`Stacks.SymGraded.symUnitalHom`. -/
public theorem symSheafGradedAlgebraHom_app (u : E₁ ⟶ E₂) (n : ℤ) :
    (symSheafGradedAlgebraHom hqc₁ hqc₂ u).app n = (symUnitalHom u).app n := rfl

/-- **For an isomorphism of modules the induced homomorphism is an isomorphism in every
degree.** The two composites are the homomorphisms induced by the two composites of the
isomorphism, which are the identities by functoriality.

This discharges the hypotheses of Tags 07ZI and 07ZJ, which ask only for all sufficiently large
degrees. -/
public theorem isIso_symSheafGradedAlgebraHom_app (e : E₁ ≅ E₂) (n : ℤ) :
    IsIso ((symSheafGradedAlgebraHom hqc₁ hqc₂ e.hom).app n) := by
  have key : ∀ {A B : X.Modules} (f : A ⟶ B) (g : B ⟶ A), f ≫ g = 𝟙 A →
      (symUnitalHom f).app n ≫ (symUnitalHom g).app n = 𝟙 _ := fun f g h => by
    rw [← SheafOfModules.GradedAlgebra.UnitalHom.comp_app, ← symUnitalHom_comp, h, symUnitalHom_id]
    rfl
  exact ⟨(symUnitalHom e.inv).app n, key _ _ e.hom_inv_id, key _ _ e.inv_hom_id⟩

end Stacks.SymGraded

end
