module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The symmetric algebra of a module sheaf is functorial

Let `X` be a scheme. `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X F` is the symmetric
algebra of an `𝒪_X`-module `F`, and
`AlgebraicGeometry.Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra` says it is universal: it
receives a unique unital homomorphism of sheaves of graded algebras from any degree-one generator
whose local sections commute pairwise. **This file reads that universal property as
functoriality**: a morphism `q : F ⟶ G` induces

`Sym(q) : Sym(F) ⟶ Sym(G)`

with `Sym(𝟙) = 𝟙` and `Sym(q ≫ r) = Sym(q) ≫ Sym(r)`.

The commuting hypothesis is free: the target is always a symmetric algebra, whose homogeneous
multiplication is commutative by
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra_mul_comm`, so a map into its degree-one piece
commutes pairwise whatever it is.

## Why this is wanted

For Tag 0B3V, a surjection `q : 𝓔 ⟶ 𝓛` onto an invertible module induces the graded algebra map
`Sym(𝓔) ⟶ Sym(𝓛)` whose degree-`n` part is `Symⁿ(q)`; since `Symⁿ 𝓛 ≅ 𝓛^{⊗ n}` for an invertible
`𝓛`, that is the map `Sym(𝓔) ⟶ ⨁ₙ 𝓛^{⊗ n}` the universal property of `𝐏(𝓔) = Proj_X(Sym 𝓔)`
consumes. Nothing here is local on `X`: the universal property of `symmetricAlgebra` holds over
an arbitrary scheme with no quasi-coherence and no affineness, so the graded map exists globally
and only its *trivialization* has to be done over a cover.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraMap`: **`Sym(q)`**, for `q : F ⟶ G`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pairwiseCommutes_comp_symmetricAlgebraGen`: the commuting
  hypothesis of the universal property is automatic for a map into a symmetric algebra.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGen_comp_symmetricAlgebraMap`: **the
  characterizing square** `gen_F ≫ Sym(q)₁ = q ≫ gen_G`, so `Sym(q)` extends `q` in degree one.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraMap_unique`: it is the only unital
  homomorphism doing so, so `Sym(q)` is canonical rather than merely some extension.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraMap_id` and
  `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraMap_comp`: **the functor laws.**

## Implementation notes

**`symmetricAlgebra_mul_comm` is stated with `HEq`** because in general
`piece (i + j)` and `piece (j + i)` are different sheaves of modules indexed by equal integers.
`PairwiseCommutes` only ever uses degrees `(1, 1)`, where the two sides already have the same
type, so `eq_of_heq` applies and no transport along an equality of degrees appears.

Both functor laws are proved from `symmetricAlgebraMap_unique` rather than by computing with the
construction: `Sym(q)` is characterized by one square, and each law is the statement that the
competing homomorphism satisfies the same square.

No `@[stacks]` attribute is attached. Tag 01CG asserts the existence of the symmetric algebra of
a module sheaf with its universal property, which is `isSymmetricAlgebra_symmetricAlgebra` and is
registered where it is proved; functoriality is a consequence of a universal property and is not
a separate assertion of that tag.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.GradedAlgebra (PairwiseCommutes UnitalHom)

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F G H : SheafOfModules.{u} X.ringCatSheaf}

/-- **The commuting hypothesis of the symmetric algebra's universal property is automatic for a
map into a symmetric algebra.** Homogeneous multiplication in `Sym(G)` is commutative, so any
`F ⟶ (Sym G).piece 1` has pairwise-commuting image. -/
theorem pairwiseCommutes_comp_symmetricAlgebraGen (q : F ⟶ G) :
    PairwiseCommutes (A := symmetricAlgebra X G) (q ≫ symmetricAlgebraGen X G) :=
  fun U _ _ => eq_of_heq (symmetricAlgebra_mul_comm X G 1 1 U _ _)

/-- **`Sym(q) : Sym(F) ⟶ Sym(G)`**, the unital homomorphism of sheaves of graded algebras that a
morphism `q : F ⟶ G` induces, by the universal property of `Sym(F)` applied to the degree-one
generator `q ≫ gen_G`. -/
@[ega "II 4.1.2" "more general"]
def symmetricAlgebraMap (q : F ⟶ G) :
    UnitalHom (symmetricAlgebra X F) (symmetricAlgebra X G) :=
  (isSymmetricAlgebra_symmetricAlgebra X F).isUniversal.desc (symmetricAlgebra X G)
    (q ≫ symmetricAlgebraGen X G) (pairwiseCommutes_comp_symmetricAlgebraGen q)

/-- **The characterizing square.** In degree one `Sym(q)` is `q`, read through the two
generators. -/
theorem symmetricAlgebraGen_comp_symmetricAlgebraMap (q : F ⟶ G) :
    symmetricAlgebraGen X F ≫ (symmetricAlgebraMap q).app 1 = q ≫ symmetricAlgebraGen X G :=
  (isSymmetricAlgebra_symmetricAlgebra X F).isUniversal.desc_extends _ _ _

/-- **`Sym(q)` is the only unital homomorphism extending `q` in degree one**, so it is canonical.
-/
theorem symmetricAlgebraMap_unique (q : F ⟶ G)
    {g : UnitalHom (symmetricAlgebra X F) (symmetricAlgebra X G)}
    (hg : symmetricAlgebraGen X F ≫ g.app 1 = q ≫ symmetricAlgebraGen X G) :
    g = symmetricAlgebraMap q :=
  (isSymmetricAlgebra_symmetricAlgebra X F).isUniversal.desc_unique _ _ _ hg

/-- **`Sym` preserves the identity.** -/
theorem symmetricAlgebraMap_id :
    symmetricAlgebraMap (𝟙 F) = UnitalHom.id (symmetricAlgebra X F) :=
  ((isSymmetricAlgebra_symmetricAlgebra X F).isUniversal.eq_id
    (by rw [symmetricAlgebraGen_comp_symmetricAlgebraMap, Category.id_comp])).symm ▸ rfl

/-- **`Sym` preserves composition.** -/
theorem symmetricAlgebraMap_comp (q : F ⟶ G) (r : G ⟶ H) :
    symmetricAlgebraMap (q ≫ r) =
      (symmetricAlgebraMap q).comp (symmetricAlgebraMap r) :=
  (symmetricAlgebraMap_unique (q ≫ r) (by
    rw [UnitalHom.comp_app, ← Category.assoc, symmetricAlgebraGen_comp_symmetricAlgebraMap,
      Category.assoc, symmetricAlgebraGen_comp_symmetricAlgebraMap, Category.assoc])).symm

end AlgebraicGeometry.Scheme.Modules

end
