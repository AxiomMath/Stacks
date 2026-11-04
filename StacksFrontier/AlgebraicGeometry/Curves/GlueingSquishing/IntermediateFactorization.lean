module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic

/-!
# Intermediate factorizations and quasi-coherent subalgebras

Let `f : X' ⟶ X` be a morphism of schemes. This file sets up the two halves of the dictionary
used in [Stacks, Tag 0C1L]:

* a quasi-coherent sheaf of `𝒪_X`-algebras `A` together with a morphism `ψ : A ⟶ f_* 𝒪_{X'}` of
  `𝒪_X`-algebras determines a factorization `X' ⟶ Spec_X(A) ⟶ X` of `f` whose second half is
  affine;
* conversely a factorization `X' ⟶ Y ⟶ X` of `f` whose second half `g : Y ⟶ X` is affine is of
  that form: `Y` is `Spec_X(g_* 𝒪_Y)` over `X`, the algebra map is the canonical
  `g_* 𝒪_Y ⟶ f_* 𝒪_{X'}`, and the first half of the factorization is carried to the morphism
  produced by the first half of the dictionary.

Together these say that the intermediate factorizations of `f` with affine second half are the
`𝒪_X`-algebras between `𝒪_X` and `f_* 𝒪_{X'}`, which is the correspondence the proof of
[Stacks, Tag 0C1L] uses to pass from a subalgebra of `f_* 𝒪_{X'}` to a proper intermediate
factorization and back.

## Main definitions

* `Stacks.GlueSquishFactor.toIntermediateOver` and `Stacks.GlueSquishFactor.toIntermediate` are
  the morphism `X' ⟶ Spec_X(A)` attached to `ψ : A ⟶ f_* 𝒪_{X'}`, over `X` and as a morphism of
  schemes.
* `Stacks.GlueSquishFactor.factorizationAlgebraHom` is the morphism `g_* 𝒪_Y ⟶ f_* 𝒪_{X'}` of
  `𝒪_X`-algebras attached to a factorization `f = u ≫ g`.
* `Stacks.GlueSquishFactor.isoRelativeSpecOfAffine` is the isomorphism `Y ≅ Spec_X(g_* 𝒪_Y)` of
  schemes over `X`, for `g : Y ⟶ X` affine.

## Main results

* `Stacks.GlueSquishFactor.toIntermediate_comp_relativeSpecToBase` — the factorization
  identity: the morphism attached to `ψ` followed by the structure morphism of `Spec_X(A)`
  is `f`.
* `Stacks.GlueSquishFactor.pushforwardAlgebraMap_toIntermediateOver` — the defining property of
  that morphism: the algebra map it induces is `ψ`, read through the identification
  `(Spec_X(A) ⟶ X)_* 𝒪 ≅ A` of [Stacks, Tag 01SA].
* `Stacks.GlueSquishFactor.toIntermediateOver_factorizationAlgebraHom` and
  `Stacks.GlueSquishFactor.toIntermediate_factorizationAlgebraHom` — every intermediate
  factorization with affine second half is the one attached to its own algebra: the comparison
  isomorphism `Y ≅ Spec_X(g_* 𝒪_Y)` carries `u` to the morphism attached to
  `factorizationAlgebraHom`.
* `Stacks.GlueSquishFactor.factorizationAlgebraHom_toIntermediate` — the other roundtrip: the
  algebra map of the factorization attached to `ψ` is `ψ`, so the two directions are mutually
  inverse.
* `Stacks.GlueSquishFactor.mono_hom_pushforwardAlgebra_of_factorization` — if
  `𝒪_X ⟶ f_* 𝒪_{X'}` is a monomorphism then so is `𝒪_X ⟶ g_* 𝒪_Y`, which is the inclusion
  `𝒪_X ⊂ g_* 𝒪_Y` of the source.
* `Stacks.GlueSquishFactor.exists_affine_factorization_over` — the first half of the dictionary
  in the shape a factorization argument over a fixed base consumes: a subalgebra produces an
  object `Z` over the base with `f = p ≫ q` and `q` affine.

## Implementation notes

Both halves are obtained from a single bijection, the universal property
`Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom` of the relative spectrum: for `Z`
affine over `X` and `W` an arbitrary scheme over `X`,
`Hom_X(W, Z) ≃ Hom_{𝒪_X-alg}(Z.hom _* 𝒪_Z, W.hom _* 𝒪_W)`. Applying it with
`Z = Spec_X(A)` and `W = X'`, and composing with the isomorphism
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso` of [Stacks, Tag 01SA], turns `ψ` into a
morphism `X' ⟶ Spec_X(A)` over `X`; the triangle over `X` is then carried by the morphism
itself, as `CategoryTheory.Over.w`.

Because the bijection is natural and injective, the converse direction is bookkeeping: the
comparison `Y ≅ Spec_X(g_* 𝒪_Y)` is the preimage of `pushforwardAlgebraIso (g_* 𝒪_Y)` and the
two identities making it an isomorphism are checked after applying `pushforwardAlgebraMap`,
where they are `CategoryTheory.Iso.hom_inv_id` and `CategoryTheory.Iso.inv_hom_id`; the same
injectivity identifies `u` composed with that isomorphism with the morphism attached to
`factorizationAlgebraHom`. This is why the morphism `X' ⟶ Spec_X(A)` is defined here through the
universal property rather than as the composite of the canonical morphism
`Stacks.RelativeSpec.toRelativeSpec` with
`Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom`: that composite is the same morphism, but
reading its induced algebra map off the chartwise description would be a separate computation,
and nothing below needs it.

No finiteness or quasi-coherence hypothesis on `f` is used: only `A` has to be quasi-coherent,
to form `Spec_X(A)` at all, and only the second half `g` of a factorization has to be affine.
The hypotheses of [Stacks, Tag 0C1L] on `f` are therefore not required for the dictionary, and
quasi-coherence of `A` is taken as a hypothesis rather than derived — for a subalgebra of
`f_* 𝒪_{X'}` it is an extra condition.

The instance `Stacks.GlueSquishFactor.isAffineHom_hom_mk` is needed because the affineness
hypothesis of `overHomEquivAlgebraHom` is stated for the structure morphism of a bundled object
of `CategoryTheory.Over X`, and instance search does not unfold `CategoryTheory.Over.mk`.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01LY](https://stacks.math.columbia.edu/tag/01LY)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.GlueSquishFactor

/-- The structure morphism of `CategoryTheory.Over.mk h` is affine when `h` is. -/
instance isAffineHom_hom_mk {S T : Scheme.{u}} (h : T ⟶ S) [IsAffineHom h] :
    IsAffineHom (Over.mk h).hom :=
  inferInstanceAs (IsAffineHom h)

/-- For an affine morphism `h : T ⟶ S`, the sheaf of `𝒪_S`-algebras `h_* 𝒪_T` is
quasi-coherent. -/
instance isQuasicoherent_pushforwardAlgebra_of_isAffineHom {S T : Scheme.{u}} (h : T ⟶ S)
    [IsAffineHom h] : AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra h) :=
  Stacks.AffineAlgebraEquivalence.isQuasicoherent_pushforwardAlgebra h

/-- The canonical map of the morphism over `S` attached to an algebra map `φ` is `φ`. -/
private theorem pushforwardAlgebraMap_symm_overHomEquivAlgebraHom {S : Scheme.{u}} {W Z : Over S}
    [IsAffineHom Z.hom] (φ : pushforwardAlgebra Z.hom ⟶ pushforwardAlgebra W.hom) :
    pushforwardAlgebraMap ((overHomEquivAlgebraHom W Z).symm φ) = φ :=
  (overHomEquivAlgebraHom_apply _).symm.trans ((overHomEquivAlgebraHom W Z).apply_symm_apply φ)

/-! ### From a quasi-coherent algebra to an intermediate factorization -/

section Subalgebra

variable {X' X : Scheme.{u}} (f : X' ⟶ X) (A : AlgebraSheaf X)
  [AlgebraSheaf.IsQuasicoherent A] (ψ : A ⟶ pushforwardAlgebra f)

/-- **The morphism `X' ⟶ Spec_X(A)` over `X` attached to a morphism `ψ : A ⟶ f_* 𝒪_{X'}` of
`𝒪_X`-algebras.** It is the morphism corresponding to `ψ` under the universal property of the
relative spectrum, read through the identification `(Spec_X(A) ⟶ X)_* 𝒪 ≅ A`. -/
@[stacks 0C1L "the intermediate factorization attached to a subalgebra"]
def toIntermediateOver : Over.mk f ⟶ Over.mk (relativeSpecToBase A) :=
  (overHomEquivAlgebraHom (Over.mk f) (Over.mk (relativeSpecToBase A))).symm
    ((pushforwardAlgebraIso A).hom ≫ ψ)

/-- The morphism `X' ⟶ Spec_X(A)` attached to `ψ : A ⟶ f_* 𝒪_{X'}`, as a morphism of schemes. -/
def toIntermediate : X' ⟶ relativeSpec A :=
  (toIntermediateOver f A ψ).left

/-- **The defining property of `Stacks.GlueSquishFactor.toIntermediateOver`.** The morphism of
pushed-forward structure sheaves it induces is `ψ`, read through the identification
`(Spec_X(A) ⟶ X)_* 𝒪 ≅ A` of [Stacks, Tag 01SA]. -/
theorem pushforwardAlgebraMap_toIntermediateOver :
    pushforwardAlgebraMap (toIntermediateOver f A ψ) = (pushforwardAlgebraIso A).hom ≫ ψ :=
  pushforwardAlgebraMap_symm_overHomEquivAlgebraHom _

/-- **The factorization of `f` attached to a morphism `ψ : A ⟶ f_* 𝒪_{X'}`.** The morphism
`X' ⟶ Spec_X(A)` of `Stacks.GlueSquishFactor.toIntermediate`, followed by the structure morphism
of the relative spectrum, is `f`. -/
@[stacks 0C1L "the intermediate factorization attached to a subalgebra"]
theorem toIntermediate_comp_relativeSpecToBase :
    toIntermediate f A ψ ≫ relativeSpecToBase A = f :=
  Over.w (toIntermediateOver f A ψ)

end Subalgebra

/-! ### From an intermediate factorization to a quasi-coherent algebra -/

section Factorization

variable {X' X Y : Scheme.{u}} (f : X' ⟶ X) (u : X' ⟶ Y) (g : Y ⟶ X) [IsAffineHom g]
  (hu : u ≫ g = f)

/-- **The morphism of `𝒪_X`-algebras `g_* 𝒪_Y ⟶ f_* 𝒪_{X'}` attached to a factorization
`f = u ≫ g`.** It is the canonical contravariant map on pushed-forward structure sheaves of the
morphism `u`, viewed as a morphism of schemes over `X`. -/
def factorizationAlgebraHom : pushforwardAlgebra g ⟶ pushforwardAlgebra f :=
  pushforwardAlgebraMap (Over.homMk u hu : Over.mk f ⟶ Over.mk g)

omit [IsAffineHom g] in
/-- The algebra map attached to a factorization is a morphism of `𝒪_X`-algebras: pushing a
section of `𝒪_X` into `g_* 𝒪_Y` and then into `f_* 𝒪_{X'}` is pushing it into `f_* 𝒪_{X'}`.
This is the chain of inclusions `𝒪_X ⊂ g_* 𝒪_Y ⊂ f_* 𝒪_{X'}` of [Stacks, Tag 0C1L]. -/
theorem hom_comp_factorizationAlgebraHom :
    (pushforwardAlgebra g).hom ≫ (factorizationAlgebraHom f u g hu).right =
      (pushforwardAlgebra f).hom :=
  Under.w (factorizationAlgebraHom f u g hu)

omit [IsAffineHom g] in
include hu in
/-- If `𝒪_X ⟶ f_* 𝒪_{X'}` is a monomorphism then so is `𝒪_X ⟶ g_* 𝒪_Y` for any factorization
`f = u ≫ g`: this is the inclusion `𝒪_X ⊂ g_* 𝒪_Y` of [Stacks, Tag 0C1L]. -/
theorem mono_hom_pushforwardAlgebra_of_factorization [Mono (pushforwardAlgebra f).hom] :
    Mono (pushforwardAlgebra g).hom :=
  mono_of_mono_fac (hom_comp_factorizationAlgebraHom f u g hu)

/-- The comparison morphism `Y ⟶ Spec_X(g_* 𝒪_Y)` over `X`, for `g : Y ⟶ X` affine: the
morphism corresponding to the identification `(Spec_X(g_* 𝒪_Y) ⟶ X)_* 𝒪 ≅ g_* 𝒪_Y` of
[Stacks, Tag 01SA] under the universal property of the relative spectrum. -/
def toRelativeSpecOfAffine :
    Over.mk g ⟶ Over.mk (relativeSpecToBase (pushforwardAlgebra g)) :=
  (overHomEquivAlgebraHom (Over.mk g) (Over.mk (relativeSpecToBase (pushforwardAlgebra g)))).symm
    (pushforwardAlgebraIso (pushforwardAlgebra g)).hom

/-- The comparison morphism `Spec_X(g_* 𝒪_Y) ⟶ Y` over `X`, for `g : Y ⟶ X` affine: the
morphism corresponding to the inverse of the identification of [Stacks, Tag 01SA]. -/
def fromRelativeSpecOfAffine :
    Over.mk (relativeSpecToBase (pushforwardAlgebra g)) ⟶ Over.mk g :=
  (overHomEquivAlgebraHom (Over.mk (relativeSpecToBase (pushforwardAlgebra g))) (Over.mk g)).symm
    (pushforwardAlgebraIso (pushforwardAlgebra g)).inv

/-- The morphism of pushed-forward structure sheaves induced by
`Stacks.GlueSquishFactor.toRelativeSpecOfAffine` is the identification of [Stacks, Tag 01SA]. -/
theorem pushforwardAlgebraMap_toRelativeSpecOfAffine :
    pushforwardAlgebraMap (toRelativeSpecOfAffine g) =
      (pushforwardAlgebraIso (pushforwardAlgebra g)).hom :=
  pushforwardAlgebraMap_symm_overHomEquivAlgebraHom _

/-- The morphism of pushed-forward structure sheaves induced by
`Stacks.GlueSquishFactor.fromRelativeSpecOfAffine` is the inverse of the identification of
[Stacks, Tag 01SA]. -/
theorem pushforwardAlgebraMap_fromRelativeSpecOfAffine :
    pushforwardAlgebraMap (fromRelativeSpecOfAffine g) =
      (pushforwardAlgebraIso (pushforwardAlgebra g)).inv :=
  pushforwardAlgebraMap_symm_overHomEquivAlgebraHom _

/-- **A scheme affine over `X` is the relative spectrum of its algebra of functions over `X`.**
For `g : Y ⟶ X` affine, the comparison morphism `Y ⟶ Spec_X(g_* 𝒪_Y)` is an isomorphism of
schemes over `X`. This is [Stacks, Tag 01SA] in the form used by [Stacks, Tag 0C1L]: an
intermediate factorization with affine second half is a relative spectrum. -/
@[stacks 0C1L "every affine intermediate factorization comes from a subalgebra"]
def isoRelativeSpecOfAffine :
    Over.mk g ≅ Over.mk (relativeSpecToBase (pushforwardAlgebra g)) where
  hom := toRelativeSpecOfAffine g
  inv := fromRelativeSpecOfAffine g
  hom_inv_id := eq_of_pushforwardAlgebraMap_eq (by
    rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_id,
      pushforwardAlgebraMap_toRelativeSpecOfAffine,
      pushforwardAlgebraMap_fromRelativeSpecOfAffine, Iso.inv_hom_id])
  inv_hom_id := eq_of_pushforwardAlgebraMap_eq (by
    rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_id,
      pushforwardAlgebraMap_toRelativeSpecOfAffine,
      pushforwardAlgebraMap_fromRelativeSpecOfAffine, Iso.hom_inv_id])

/-- **Every intermediate factorization with affine second half comes from an algebra.** For a
factorization `f = u ≫ g` with `g` affine, the comparison isomorphism
`Y ≅ Spec_X(g_* 𝒪_Y)` carries `u` to the morphism attached by
`Stacks.GlueSquishFactor.toIntermediateOver` to the algebra map `g_* 𝒪_Y ⟶ f_* 𝒪_{X'}` of the
factorization. -/
@[stacks 0C1L "every affine intermediate factorization comes from a subalgebra"]
theorem toIntermediateOver_factorizationAlgebraHom :
    toIntermediateOver f (pushforwardAlgebra g) (factorizationAlgebraHom f u g hu) =
      (Over.homMk u hu : Over.mk f ⟶ Over.mk g) ≫ toRelativeSpecOfAffine g :=
  eq_of_pushforwardAlgebraMap_eq (by
    rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_toRelativeSpecOfAffine,
      pushforwardAlgebraMap_toIntermediateOver]
    rfl)

/-- The statement of `Stacks.GlueSquishFactor.toIntermediateOver_factorizationAlgebraHom` on the
underlying morphisms of schemes: `u` followed by the comparison isomorphism
`Y ≅ Spec_X(g_* 𝒪_Y)` is the morphism attached to the algebra map of the factorization. -/
theorem toIntermediate_factorizationAlgebraHom :
    u ≫ (toRelativeSpecOfAffine g).left =
      toIntermediate f (pushforwardAlgebra g) (factorizationAlgebraHom f u g hu) :=
  congrArg (fun t ↦ t.left) (toIntermediateOver_factorizationAlgebraHom f u g hu).symm

end Factorization

/-! ### The two directions are mutually inverse -/

section Roundtrip

variable {X' X : Scheme.{u}} (f : X' ⟶ X) (A : AlgebraSheaf X)
  [AlgebraSheaf.IsQuasicoherent A] (ψ : A ⟶ pushforwardAlgebra f)

/-- **Passing from `ψ : A ⟶ f_* 𝒪_{X'}` to its intermediate factorization and back returns
`ψ`.** The algebra map of the factorization `X' ⟶ Spec_X(A) ⟶ X` attached to `ψ` is `ψ` itself,
read through the identification `(Spec_X(A) ⟶ X)_* 𝒪 ≅ A` of [Stacks, Tag 01SA]. -/
theorem factorizationAlgebraHom_toIntermediate :
    factorizationAlgebraHom f (toIntermediate f A ψ) (relativeSpecToBase A)
        (toIntermediate_comp_relativeSpecToBase f A ψ) =
      (pushforwardAlgebraIso A).hom ≫ ψ :=
  pushforwardAlgebraMap_toIntermediateOver f A ψ

end Roundtrip

/-! ### The factorization as a splitting over a fixed base -/

/-- **The intermediate factorization attached to a subalgebra, over a fixed base.** For a
morphism `f` of schemes over a base `S` and a morphism `ψ : A ⟶ f_* 𝒪` from a quasi-coherent
sheaf of algebras on the target, `f` factors over `S` through a scheme affine over its target.

This supplies the factorization itself, and affineness of its second half. It is not the full
splitting hypothesis of the induction of [Stacks, Tag 0C1L], which additionally requires both
halves to be almost isomorphisms and to drop a measure; neither is proved here. -/
theorem exists_affine_factorization_over {S : Scheme.{u}} {W' W : Over S} (f : W' ⟶ W)
    (A : AlgebraSheaf W.left) [AlgebraSheaf.IsQuasicoherent A]
    (ψ : A ⟶ pushforwardAlgebra f.left) :
    ∃ (Z : Over S) (p : W' ⟶ Z) (q : Z ⟶ W), p ≫ q = f ∧ IsAffineHom q.left := by
  refine ⟨Over.mk (relativeSpecToBase A ≫ W.hom),
    Over.homMk (toIntermediate f.left A ψ) ?_, Over.homMk (relativeSpecToBase A) rfl,
    Over.OverMorphism.ext ?_, inferInstanceAs (IsAffineHom (relativeSpecToBase A))⟩
  · show toIntermediate f.left A ψ ≫ relativeSpecToBase A ≫ W.hom = W'.hom
    rw [← Category.assoc, toIntermediate_comp_relativeSpecToBase, Over.w]
  · show toIntermediate f.left A ψ ≫ relativeSpecToBase A = f.left
    exact toIntermediate_comp_relativeSpecToBase f.left A ψ

end Stacks.GlueSquishFactor

end
