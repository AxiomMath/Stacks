module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Bridge
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Hom

/-!
# Morphisms, across the bridge to the input of relative Proj

`StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Bridge` converts a sheaf of graded
`𝒪_S`-algebras, `SheafOfModules.GradedAlgebra S.ringCatSheaf`, into the data the relative Proj
construction of this repository consumes,
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra S`. It carries the *objects*
across and says in its own `Not done here` that it carries no morphisms, because at the time it
was written `SheafGradedAlgebra` had none.

It has them now:
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom` is the homomorphism
Tag 07ZG starts from. **This file carries a morphism across the same bridge**, which was the only
missing step between the two vocabularies.

## Main definitions

* `Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebraHom`: **the conversion of a
  unital homomorphism of sheaves of graded algebras into a `SheafGradedAlgebraHom`.**

## Main results

* `Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebraHom_app`: the degreewise
  morphism is carried across unchanged. It is `rfl`, so a statement about the converted
  homomorphism in a given degree is a statement about the given one.

## Implementation notes

**Every field is the given field read at `op U`.** This is the same phenomenon the implementation
notes of `Bridge.lean` record for the object conversion: `Γ(M, U)` is
`(Scheme.Modules.presheaf M).obj (op U)`, an object of `Ab`, while the graded-algebra structure
speaks of `M.val.obj (op U)`, an object of `ModuleCat Γ(S, U)`, and these are different objects of
different categories with the same carrier and the same additive structure. The morphisms agree
for the same reason, so `app` is `SheafOfModules.GradedAlgebra.UnitalHom.app` with no coercion
written, and the two laws are `map_mul` and `map_one` at `op U`.

The degree bookkeeping needs no transfer here. `SheafGradedAlgebraHom.app_mul` and
`UnitalHom.map_mul` are both stated in the `ℤ` spelling `i + j`; it is `sectionPieceHom_mul` in
`RelativeProjMapDomain/Hom.lean` that re-reads it in the `ℕ` spelling the graded ring of sections
uses, and that is already done there.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)

## Not done here

No tag is claimed, for the reason `Bridge.lean` gives for the object conversion: the sheaf-level
graded algebra data of Tag 01NN is carried by `SheafGradedAlgebra`, the graded algebras and their
unital homomorphisms of Tag 0FQW by `SheafOfModules.GradedAlgebra` and its `UnitalHom`, and the
homomorphism Tag 07ZG starts from by `SheafGradedAlgebraHom`. This file asserts nothing that any
of the three does not.

Nothing is said about identities or composites. `SheafGradedAlgebraHom` has no extensionality
lemma — it is not the hom of a category — so the laws would have to be stated degreewise, and no
consumer needs them in that form; the degreewise statements are
`toSheafGradedAlgebraHom_app` composed with
`SheafOfModules.GradedAlgebra.UnitalHom.id_app` and `comp_app`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

namespace Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

universe u

variable {S : Scheme.{u}} {A B : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf}
  (hcommA : IsCommutative A) (hnegA : VanishesInNegativeDegrees A)
  (hqcA : ∀ n : ℤ, ((A.piece n : S.Modules)).IsQuasicoherent)
  (hcommB : IsCommutative B) (hnegB : VanishesInNegativeDegrees B)
  (hqcB : ∀ n : ℤ, ((B.piece n : S.Modules)).IsQuasicoherent)

/-- **The conversion of a morphism.** A unital homomorphism of sheaves of graded `𝒪_S`-algebras
is a homomorphism of the sheaf-level graded algebra data of Situation 01NN that the two algebras
convert to, in the sense of Tag 07ZG.

The data is carried across unchanged: the degree-`n` morphism of the result *is* the given
degree-`n` morphism, and the two laws are the given ones read at `op U`. -/
public def toSheafGradedAlgebraHom (ψ : SheafOfModules.GradedAlgebra.UnitalHom A B) :
    SheafGradedAlgebraHom (toSheafGradedAlgebra A hcommA hnegA hqcA)
      (toSheafGradedAlgebra B hcommB hnegB hqcB) where
  app n := ψ.app n
  app_mul i j U a b := ψ.map_mul i j (op U) a b
  app_one U := ψ.map_one (op U)

/-- The degreewise morphism is carried across unchanged. -/
public theorem toSheafGradedAlgebraHom_app (ψ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (n : ℤ) :
    (toSheafGradedAlgebraHom hcommA hnegA hqcA hcommB hnegB hqcB ψ).app n = ψ.app n := rfl

end Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

end
