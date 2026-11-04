module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Faithful
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Full
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over

/-!
# Affine morphisms are the relative spectra of quasi-coherent algebras

A morphism of schemes `f : X ⟶ S` is affine exactly when it is, over `S`, the structure
morphism of the relative spectrum of a quasi-coherent sheaf of `𝒪_S`-algebras. For an affine
morphism that algebra can be taken to be the pushforward `f_* 𝒪_X` of the structure sheaf, and
the resulting comparison `X ⟶ Spec_S(f_* 𝒪_X)` is an isomorphism over `S`.

## Main definitions

* `AlgebraicGeometry.affineOverOfIsAffineHom`: the source of an affine morphism, as a scheme
  affine over the target.
* `AlgebraicGeometry.toRelativeSpecOfAlgebraIso` and
  `AlgebraicGeometry.fromRelativeSpecOfAlgebraIso`: the two comparison morphisms between the
  source of an affine morphism and the relative spectrum of an algebra sheaf identified with
  `f_* 𝒪_X`, and `AlgebraicGeometry.relativeSpecOverIsoOfAlgebraIso` the isomorphism they form.
* `AlgebraicGeometry.relativeSpecMapOfAlgebraHom`: **the morphism `Spec_S(B) ⟶ Spec_S(A)` over
  `S` induced by a morphism `A ⟶ B` of quasi-coherent algebra sheaves**, the relative spectrum
  being contravariant in the algebra.
* `AlgebraicGeometry.affineOverIso`: the identification of `affineOverOfIsAffineHom f` with the
  relative spectrum of the pushforward of the structure sheaf.
* `AlgebraicGeometry.relativeSpecPushforwardAlgebraIso`: for an affine morphism `f : X ⟶ S`, the
  isomorphism `X ≅ Spec_S(f_* 𝒪_X)` over `S`.

## Main results

* `AlgebraicGeometry.pushforwardAlgebraMap_toRelativeSpecOfAlgebraIso` and
  `AlgebraicGeometry.pushforwardAlgebraMap_fromRelativeSpecOfAlgebraIso`: the algebra maps the
  two comparison morphisms induce are the ones they were built from.
* `AlgebraicGeometry.pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom`: likewise for the
  morphism of relative spectra attached to a morphism of algebras.
* `AlgebraicGeometry.relativeSpecPushforwardAlgebraIso_hom` and
  `AlgebraicGeometry.relativeSpecPushforwardAlgebraIso_inv`: the comparison isomorphism is
  exactly the pair of comparison morphisms.
* `AlgebraicGeometry.isAffineHom_iff_exists_relativeSpecIso`: a morphism is affine if and only
  if it is a relative spectrum.

## Implementation notes

The relative spectrum of a quasi-coherent algebra sheaf `A` is
`Stacks.AffineAlgebraEquivalence.relativeSpec A`, with structure morphism
`Stacks.AffineAlgebraEquivalence.relativeSpecToBase A`; quasi-coherence of `A` is a typeclass
argument of both, so it is bound before the relative spectrum is named in the statements below.

**The comparison morphism is exhibited, not chosen.** It is
`Stacks.AffineAlgebraEquivalence.overHomOfAlgebraHom` of the algebra map
`(Spec_S A ⟶ S)_* 𝒪 ≅ A ≅ f_* 𝒪_X`, which glues the morphisms of affine schemes that algebra
map gives over the affine opens of `S`; its inverse is the same construction applied to the
inverse algebra map. Fullness of the pushforward functor on the schemes affine over `S` would
also produce a comparison morphism, but only through `CategoryTheory.Functor.preimage`, which
is `Exists.choose` of the surjectivity of `CategoryTheory.Functor.map`: that route proves the
comparison exists without naming it, so the isomorphism of a diagram built from it would be
data defined by `Classical.choice`. The two morphisms are mutually inverse because the algebra
maps they induce are, together with faithfulness
(`Stacks.AffineAlgebraEquivalence.eq_of_pushforwardAlgebraMap_eq`), and
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso` is the identification of the
pushed-forward structure sheaf of a relative spectrum with the algebra it is built from.

## References

* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A scheme affine over `S` is sent by the pushforward functor to the pushforward of its
structure sheaf. -/
theorem affinePushforwardAlgebraFunctor_obj (Y : AffineOver S) :
    (affinePushforwardAlgebraFunctor S).obj (op Y) = pushforwardAlgebra Y.obj.hom := rfl

section

variable (f : X ⟶ S) [IsAffineHom f] [AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f)]

/-- The source of an affine morphism, as a scheme affine over the target. -/
def affineOverOfIsAffineHom : AffineOver S := ⟨Over.mk f, ‹IsAffineHom f›⟩

end

/-! ### The comparison morphisms, exhibited -/

section Comparison

variable (f : X ⟶ S) [IsAffineHom f] (A : AlgebraSheaf S) [AlgebraSheaf.IsQuasicoherent A]
  (e : pushforwardAlgebra f ≅ A)

/-- The structure morphism of `CategoryTheory.Over.mk h` is affine when `h` is. Instance search
does not unfold `CategoryTheory.Over.mk`, so the two constructions below could not otherwise
name `Stacks.AffineAlgebraEquivalence.overHomOfAlgebraHom`. -/
instance isAffineHom_over_mk_hom {T : Scheme.{u}} (h : T ⟶ S) [IsAffineHom h] :
    IsAffineHom (Over.mk h).hom :=
  inferInstanceAs (IsAffineHom h)

/-- **The comparison morphism `X ⟶ Spec_S(A)` over `S`** attached to an identification
`e : f_* 𝒪_X ≅ A` of the pushforward of the structure sheaf with a quasi-coherent algebra sheaf:
the morphism obtained by gluing, over the affine opens of `S`, the maps of affine schemes that
the algebra map `(Spec_S A ⟶ S)_* 𝒪 ≅ A ≅ f_* 𝒪_X` gives on sections. -/
@[ega "II 5.1.6"]
def toRelativeSpecOfAlgebraIso : Over.mk f ⟶ Over.mk (relativeSpecToBase A) :=
  overHomOfAlgebraHom ((pushforwardAlgebraIso A).hom ≫ e.inv)

/-- **The comparison morphism `Spec_S(A) ⟶ X` over `S`** attached to an identification
`e : f_* 𝒪_X ≅ A`: the morphism glued from the inverse algebra map
`f_* 𝒪_X ≅ A ≅ (Spec_S A ⟶ S)_* 𝒪`. -/
def fromRelativeSpecOfAlgebraIso : Over.mk (relativeSpecToBase A) ⟶ Over.mk f :=
  overHomOfAlgebraHom (e.hom ≫ (pushforwardAlgebraIso A).inv)

omit [IsAffineHom f] in
/-- The defining property of `AlgebraicGeometry.toRelativeSpecOfAlgebraIso`: the canonical map
it induces on pushed-forward structure sheaves is the given algebra map. -/
theorem pushforwardAlgebraMap_toRelativeSpecOfAlgebraIso :
    pushforwardAlgebraMap (toRelativeSpecOfAlgebraIso f A e) =
      (pushforwardAlgebraIso A).hom ≫ e.inv :=
  pushforwardAlgebraMap_overHomOfAlgebraHom _

/-- The defining property of `AlgebraicGeometry.fromRelativeSpecOfAlgebraIso`: the canonical map
it induces on pushed-forward structure sheaves is the inverse algebra map. -/
theorem pushforwardAlgebraMap_fromRelativeSpecOfAlgebraIso :
    pushforwardAlgebraMap (fromRelativeSpecOfAlgebraIso f A e) =
      e.hom ≫ (pushforwardAlgebraIso A).inv :=
  pushforwardAlgebraMap_overHomOfAlgebraHom _

/-- **The source of an affine morphism `f : X ⟶ S` is, over `S`, the relative spectrum of any
quasi-coherent sheaf of `𝒪_S`-algebras identified with `f_* 𝒪_X`**, by the two comparison
morphisms above: they are mutually inverse because the algebra maps they induce are, and a
morphism over `S` into a scheme affine over `S` is determined by that algebra map. -/
@[sga "3 III 0.1.7" "(a)"]
def relativeSpecOverIsoOfAlgebraIso : Over.mk f ≅ Over.mk (relativeSpecToBase A) where
  hom := toRelativeSpecOfAlgebraIso f A e
  inv := fromRelativeSpecOfAlgebraIso f A e
  hom_inv_id := eq_of_pushforwardAlgebraMap_eq (by
    rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_id,
      pushforwardAlgebraMap_toRelativeSpecOfAlgebraIso,
      pushforwardAlgebraMap_fromRelativeSpecOfAlgebraIso, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id])
  inv_hom_id := eq_of_pushforwardAlgebraMap_eq (by
    rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_id,
      pushforwardAlgebraMap_toRelativeSpecOfAlgebraIso,
      pushforwardAlgebraMap_fromRelativeSpecOfAlgebraIso, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id])

end Comparison

/-! ### Contravariant functoriality of the relative spectrum in the algebra -/

section AlgebraFunctoriality

variable (A B : AlgebraSheaf S) [AlgebraSheaf.IsQuasicoherent A]
  [AlgebraSheaf.IsQuasicoherent B] (φ : A ⟶ B)

/-- **The morphism of relative spectra `Spec_S(B) ⟶ Spec_S(A)` over `S` induced by a morphism
`φ : A ⟶ B` of quasi-coherent `𝒪_S`-algebras.** The relative spectrum is contravariant in the
algebra: the morphism is glued, over the affine opens of `S`, out of the algebra map
`(Spec_S A ⟶ S)_* 𝒪 ≅ A ⟶ B ≅ (Spec_S B ⟶ S)_* 𝒪`, so it is exhibited and not chosen. -/
@[ega "II 8.5.1" "special case"]
def relativeSpecMapOfAlgebraHom : Over.mk (relativeSpecToBase B) ⟶ Over.mk (relativeSpecToBase A) :=
  overHomOfAlgebraHom ((pushforwardAlgebraIso A).hom ≫ φ ≫ (pushforwardAlgebraIso B).inv)

/-- The defining property of `AlgebraicGeometry.relativeSpecMapOfAlgebraHom`: the canonical map
it induces on pushed-forward structure sheaves is the given algebra map, read through the two
identifications of `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`. -/
theorem pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom :
    pushforwardAlgebraMap (relativeSpecMapOfAlgebraHom A B φ) =
      (pushforwardAlgebraIso A).hom ≫ φ ≫ (pushforwardAlgebraIso B).inv :=
  pushforwardAlgebraMap_overHomOfAlgebraHom _

end AlgebraFunctoriality

section

variable (f : X ⟶ S) [IsAffineHom f] [AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f)]

/-- The identification, over `S`, of the source of an affine morphism with the relative
spectrum of the pushforward of its structure sheaf. -/
def affineOverIso :
    affineOverOfIsAffineHom f ≅ relativeSpecAffineOver (pushforwardAlgebra f) :=
  ObjectProperty.isoMk (IsAffineHomOver S)
    (relativeSpecOverIsoOfAlgebraIso f (pushforwardAlgebra f) (Iso.refl _))

end

/-- For an affine morphism `f : X ⟶ S`, the source is, over `S`, the relative spectrum of the
pushforward `f_* 𝒪_X` of its structure sheaf, which is a quasi-coherent sheaf of
`𝒪_S`-algebras. -/
@[stacks 01S8 "the source is the relative spectrum of the pushforward algebra", ega "II 1.3.2"]
def relativeSpecPushforwardAlgebraIso (f : X ⟶ S) [IsAffineHom f] :
    Over.mk f ≅ Over.mk (@relativeSpecToBase S (pushforwardAlgebra f)
      (isQuasicoherent_pushforwardAlgebra f)) :=
  haveI := isQuasicoherent_pushforwardAlgebra f
  (IsAffineHomOver S).ι.mapIso (affineOverIso f)

/-- The comparison isomorphism of [Stacks, Tag 01S8] is the glued comparison morphism: its
forward map is exhibited, not merely shown to exist. -/
theorem relativeSpecPushforwardAlgebraIso_hom (f : X ⟶ S) [IsAffineHom f] :
    (relativeSpecPushforwardAlgebraIso f).hom =
      haveI := isQuasicoherent_pushforwardAlgebra f
      toRelativeSpecOfAlgebraIso f (pushforwardAlgebra f) (Iso.refl _) :=
  rfl

/-- The inverse of the comparison isomorphism of [Stacks, Tag 01S8] is likewise the glued
comparison morphism in the other direction. -/
theorem relativeSpecPushforwardAlgebraIso_inv (f : X ⟶ S) [IsAffineHom f] :
    (relativeSpecPushforwardAlgebraIso f).inv =
      haveI := isQuasicoherent_pushforwardAlgebra f
      fromRelativeSpecOfAlgebraIso f (pushforwardAlgebra f) (Iso.refl _) :=
  rfl

/-- **Stacks Project, Tag 01S8, equivalence of (1) and (3).** A morphism of schemes is affine if
and only if it is isomorphic, as an object over its target, to the structure morphism of the
relative spectrum of a quasi-coherent sheaf of algebras on the target. -/
@[stacks 01S8 "equivalence of (1) and (3)", ega "II 1.3.1" "partial", sga "3 I 4.2" "partial"]
theorem isAffineHom_iff_exists_relativeSpecIso (f : X ⟶ S) :
    IsAffineHom f ↔
      ∃ (A : AlgebraSheaf S) (hA : AlgebraSheaf.IsQuasicoherent A),
        Nonempty (Over.mk f ≅ Over.mk (@relativeSpecToBase S A hA)) := by
  refine ⟨fun hf => ?_, ?_⟩
  · have := hf
    exact ⟨pushforwardAlgebra f, isQuasicoherent_pushforwardAlgebra f,
      ⟨relativeSpecPushforwardAlgebraIso f⟩⟩
  · rintro ⟨A, hA, ⟨e⟩⟩
    have := hA
    have hiso : IsIso e.hom.left := by
      have h : IsIso ((Over.forget S).map e.hom) := inferInstance
      rwa [Over.forget_map] at h
    have hw : e.hom.left ≫ relativeSpecToBase A = f := Over.w e.hom
    rw [← hw]
    infer_instance

end AlgebraicGeometry
