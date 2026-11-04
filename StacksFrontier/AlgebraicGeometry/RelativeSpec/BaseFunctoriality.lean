module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecCriterion
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Adjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative spectrum over a varying base

`Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom` is the universal property of the
relative spectrum over a *fixed* base: for `A` a quasi-coherent `𝒪_S`-algebra and `X` a scheme
over `S`, a morphism `X ⟶ \underline{Spec}_S(A)` of schemes over `S` is the same thing as a
morphism `A ⟶ X.hom _* 𝒪_X` of `𝒪_S`-algebras.  This file states the universal property over a
*varying* base: for `g : T ⟶ S`, `A` a quasi-coherent `𝒪_S`-algebra and `A'` a quasi-coherent
`𝒪_T`-algebra, a morphism

`\underline{Spec}_T(A') ⟶ \underline{Spec}_S(A)` lying over `g`

is the same thing as a morphism `A ⟶ g_* A'` of `𝒪_S`-algebras.

Both directions are needed.  From algebras to schemes it produces the morphisms of relative
spectra that a gluing datum calls for: a family of quasi-coherent algebras on the members of a
cover, with transition maps, has a family of relative spectra with transition morphisms over
the maps of the cover.  From schemes to algebras it says that such a morphism over `g` is
*determined* by its algebra map, which is what makes the compatibilities of such a family —
functoriality in `g`, and the cocycle condition — checkable on algebras, where they are
statements about sections.

## Main definitions

* `Stacks.AffineAlgebraEquivalence.relativeSpecPushforwardIsoOverBase` identifies the
  pushed-forward structure sheaf of `\underline{Spec}_T(A')`, read over `S`, with `g_* A'`.
* `Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseAlgebraHom` reads an algebra map
  `A ⟶ g_* A'` as a map of the pushed-forward structure sheaves of the two relative spectra.
* `Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseHom` is the morphism of schemes over `S`
  attached to an algebra map `A ⟶ g_* A'`, and
  `Stacks.AffineAlgebraEquivalence.relativeSpecMapOverBase` is the underlying morphism of
  schemes `\underline{Spec}_T(A') ⟶ \underline{Spec}_S(A)`.
* `Stacks.AffineAlgebraEquivalence.algebraHomEquivRelativeSpecOverBaseHom`: **the universal
  property of the relative spectrum over a varying base.**  The morphisms of relative spectra
  lying over `g : T ⟶ S`, read in `CategoryTheory.Over S`, are in bijection with the morphisms
  `A ⟶ g_* A'` of `𝒪_S`-algebras.

## Main results

* `Stacks.AffineAlgebraEquivalence.relativeSpecMapOverBase_comp_toBase`: the morphism lies over
  `g`, that is, the square with the two structure morphisms commutes.
* `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_relativeSpecOverBaseHom`: the canonical
  map on pushed-forward structure sheaves of `relativeSpecOverBaseHom` is the given algebra map,
  read through the two identifications of
  `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`.
* `Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseHom_ext`: two morphisms of schemes over
  `S` between the two relative spectra with the same canonical map on pushed-forward structure
  sheaves are equal.
* `Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseHom_eq_of_pushforwardAlgebraMap` and
  `Stacks.AffineAlgebraEquivalence.relativeSpecMapOverBase_eq_of_pushforwardAlgebraMap`: a
  morphism over `g` inducing the algebra map attached to `φ` *is* the one attached to `φ`.
* `Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseHom_pushforwardAlgebraMap` and
  `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_relativeSpecOverBaseHom_conj`: the two
  round trips, which are the two halves of the bijection.

## Implementation notes

The bijection is `Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom` at the two objects
`Over.mk (relativeSpecToBase A' ≫ g)` and `Over.mk (relativeSpecToBase A)` of
`CategoryTheory.Over S`, conjugated by two isomorphisms.  Its hypothesis is on the target
alone, and the target's structure morphism is affine by
`Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase` together with
`AlgebraicGeometry.isAffineHom_over_mk_hom`; the source is an arbitrary scheme over `S`, so no
affineness of `g` is used and none is assumed.

What makes the statement about `g_* A'` rather than about `(relativeSpecToBase A' ≫ g)_* 𝒪` is
`Stacks.AffineAlgebraEquivalence.algebraPushforward_pushforwardAlgebra`, which holds by `rfl`:
the direct image along `g` of the pushed-forward structure sheaf of a scheme over `T` is the
pushed-forward structure sheaf of the same scheme read over `S`.  So the middle type of the
bijection *is* `pushforwardAlgebra (relativeSpecToBase A) ⟶ (algebraPushforward g).obj
(pushforwardAlgebra (relativeSpecToBase A'))`, and the two isomorphisms conjugating it are
`pushforwardAlgebraIso A` on the left and the direct image of `pushforwardAlgebraIso A'` on the
right.  Nothing is chosen: both are the universal maps of the relative spectra.

**Where the two spellings of the middle object have to be kept apart.**  The one real obstacle
here is that `pushforwardAlgebra (relativeSpecToBase A' ≫ g)` and
`(algebraPushforward g).obj (pushforwardAlgebra (relativeSpecToBase A'))` are definitionally
equal but not syntactically equal, and `simp` matches syntactically: with both spellings loose
in one composite, `CategoryTheory.Category.assoc` does not fire and the two round trips cannot
be closed at all.  `Stacks.AffineAlgebraEquivalence.relativeSpecPushforwardIsoOverBase` exists
to absorb the passage once, at a single declaration whose stated type uses the first spelling;
every later composite is then in one spelling and the cancellations are `simp`.  For the same
reason `Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseAlgebraHom_conj_self` is stated for
a *variable* map of the pushed-forward structure sheaves and applied with its argument left to
unification: writing `pushforwardAlgebraMap u` there instead forces the defeq as an explicit
type ascription, and that exhausts the heartbeat budget at `whnf`.

`Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseHom` is
`Stacks.AffineAlgebraEquivalence.overHomOfAlgebraHom` applied directly, and the bijection is
written out with its two round trips and its inverse identified with it afterwards.  Defining
the morphism as the inverse of a bijection assembled from `CategoryTheory.Iso.homCongr` and
`Equiv.trans` loses its defining property: reaching
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_overHomOfAlgebraHom` then has to unfold
`Equiv.symm` through `CategoryTheory.Iso.homCongr` while solving for the implicit algebra map,
and that exhausts the heartbeat budget at `whnf`.

No `stacks` attribute is carried.  Stacks 01LP and 01S4 state the universal property of the
relative spectrum over a fixed base, which is
`Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom`; the version over a varying base is an
unnamed consequence of it, and Stacks 01LQ — the base change of a relative spectrum — is a
different statement, about `g^{-1}A ⊗ 𝒪_T` rather than about an arbitrary `𝒪_T`-algebra
receiving a map from `A`.  What this adds over
`AlgebraicGeometry.relativeSpecMapOfAlgebraHom`, which is the same construction for `g` the
identity, is the varying base and nothing else.

## References

* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01S4](https://stacks.math.columbia.edu/tag/01S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

variable {T S : Scheme.{u}} (g : T ⟶ S)
    (A : Stacks.RelativeSpec.AlgebraSheaf S)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]
    (A' : Stacks.RelativeSpec.AlgebraSheaf T)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A']

/-- The pushed-forward structure sheaf of `\underline{Spec}_T(A')`, read over `S`, is the direct
image along `g` of `A'`.

This is `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso` at `A'` pushed forward along
`g`, with its source written as the pushed-forward structure sheaf of the composite structure
morphism: the two spellings are definitionally equal by
`Stacks.AffineAlgebraEquivalence.algebraPushforward_pushforwardAlgebra`, and naming the
isomorphism at this one absorbs the passage between them once and for all. -/
@[ega "II 1.3.6" "special case"]
def relativeSpecPushforwardIsoOverBase :
    pushforwardAlgebra (relativeSpecToBase A' ≫ g) ≅ (algebraPushforward g).obj A' :=
  (algebraPushforward g).mapIso (pushforwardAlgebraIso A')

/-- The algebra map `(\underline{Spec}_S A ⟶ S)_* 𝒪 ⟶ (\underline{Spec}_T A' ⟶ S)_* 𝒪` which
an algebra map `φ : A ⟶ g_* A'` becomes when both relative spectra are read through the
universal isomorphisms of their relative spectra. -/
def relativeSpecOverBaseAlgebraHom (φ : A ⟶ (algebraPushforward g).obj A') :
    pushforwardAlgebra (relativeSpecToBase A) ⟶
      pushforwardAlgebra (relativeSpecToBase A' ≫ g) :=
  (pushforwardAlgebraIso A).hom ≫ φ ≫ (relativeSpecPushforwardIsoOverBase g A').inv

/-- `Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseAlgebraHom` is the given algebra map
conjugated by the two universal isomorphisms. -/
theorem relativeSpecOverBaseAlgebraHom_eq (φ : A ⟶ (algebraPushforward g).obj A') :
    relativeSpecOverBaseAlgebraHom g A A' φ =
      (pushforwardAlgebraIso A).hom ≫ φ ≫ (relativeSpecPushforwardIsoOverBase g A').inv :=
  rfl

/-- **The morphism of relative spectra over `g : T ⟶ S` attached to an algebra map
`φ : A ⟶ g_* A'`,** read in `CategoryTheory.Over S`.  It is exhibited, not chosen: it is the
glued morphism of the universal property of the relative spectrum of `A`, applied to the
reading `Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseAlgebraHom` of `φ`. -/
def relativeSpecOverBaseHom (φ : A ⟶ (algebraPushforward g).obj A') :
    Over.mk (relativeSpecToBase A' ≫ g) ⟶ Over.mk (relativeSpecToBase A) :=
  overHomOfAlgebraHom (relativeSpecOverBaseAlgebraHom g A A' φ)

/-- **The morphism of schemes `\underline{Spec}_T(A') ⟶ \underline{Spec}_S(A)` attached to an
algebra map `φ : A ⟶ g_* A'`.** -/
def relativeSpecMapOverBase (φ : A ⟶ (algebraPushforward g).obj A') :
    relativeSpec A' ⟶ relativeSpec A :=
  (relativeSpecOverBaseHom g A A' φ).left

/-- The defining property of `Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseHom`: the
canonical map it induces on pushed-forward structure sheaves is the given algebra map, read
through the two universal isomorphisms. -/
theorem pushforwardAlgebraMap_relativeSpecOverBaseHom
    (φ : A ⟶ (algebraPushforward g).obj A') :
    pushforwardAlgebraMap (relativeSpecOverBaseHom g A A' φ) =
      relativeSpecOverBaseAlgebraHom g A A' φ :=
  pushforwardAlgebraMap_overHomOfAlgebraHom _

/-- The morphism of relative spectra attached to `φ : A ⟶ g_* A'` lies over `g`. -/
@[reassoc]
theorem relativeSpecMapOverBase_comp_toBase (φ : A ⟶ (algebraPushforward g).obj A') :
    relativeSpecMapOverBase g A A' φ ≫ relativeSpecToBase A = relativeSpecToBase A' ≫ g :=
  Over.w (relativeSpecOverBaseHom g A A' φ)

/-- **Rigidity.**  Two morphisms of schemes over `S` between the two relative spectra with the
same canonical map on pushed-forward structure sheaves are equal.  This is what makes the
compatibilities of a family of relative spectra checkable on algebras. -/
theorem relativeSpecOverBaseHom_ext
    {u v : Over.mk (relativeSpecToBase A' ≫ g) ⟶ Over.mk (relativeSpecToBase A)}
    (h : pushforwardAlgebraMap u = pushforwardAlgebraMap v) : u = v :=
  eq_of_pushforwardAlgebraMap_eq h

/-- A morphism of schemes over `S` between the two relative spectra whose canonical map on
pushed-forward structure sheaves is the one attached to `φ` is `relativeSpecOverBaseHom φ`: a
morphism of relative spectra lying over `g` is determined by its algebra map. -/
theorem relativeSpecOverBaseHom_eq_of_pushforwardAlgebraMap
    (φ : A ⟶ (algebraPushforward g).obj A')
    (u : Over.mk (relativeSpecToBase A' ≫ g) ⟶ Over.mk (relativeSpecToBase A))
    (hu : pushforwardAlgebraMap u = relativeSpecOverBaseAlgebraHom g A A' φ) :
    u = relativeSpecOverBaseHom g A A' φ :=
  relativeSpecOverBaseHom_ext g A A'
    (hu.trans (pushforwardAlgebraMap_relativeSpecOverBaseHom g A A' φ).symm)

/-- The underlying morphism of schemes of a morphism over `S` between the two relative spectra
whose canonical map on pushed-forward structure sheaves is the one attached to `φ` is
`relativeSpecMapOverBase φ`. -/
theorem relativeSpecMapOverBase_eq_of_pushforwardAlgebraMap
    (φ : A ⟶ (algebraPushforward g).obj A')
    (u : Over.mk (relativeSpecToBase A' ≫ g) ⟶ Over.mk (relativeSpecToBase A))
    (hu : pushforwardAlgebraMap u = relativeSpecOverBaseAlgebraHom g A A' φ) :
    u.left = relativeSpecMapOverBase g A A' φ :=
  congrArg CategoryTheory.Over.Hom.left
    (relativeSpecOverBaseHom_eq_of_pushforwardAlgebraMap g A A' φ u hu)

/-- Conjugating by the two universal isomorphisms and conjugating back is the identity on maps
of the pushed-forward structure sheaves. -/
theorem relativeSpecOverBaseAlgebraHom_conj_self
    (k : pushforwardAlgebra (relativeSpecToBase A) ⟶
      pushforwardAlgebra (relativeSpecToBase A' ≫ g)) :
    (pushforwardAlgebraIso A).hom ≫
        ((pushforwardAlgebraIso A).inv ≫ k ≫ (relativeSpecPushforwardIsoOverBase g A').hom) ≫
      (relativeSpecPushforwardIsoOverBase g A').inv = k := by
  simp

/-- The canonical map induced by `relativeSpecOverBaseHom φ` is `φ` conjugated by the two
universal isomorphisms. -/
private theorem pushforwardAlgebraMap_relativeSpecOverBaseHom_eq_conj
    (φ : A ⟶ (algebraPushforward g).obj A') :
    pushforwardAlgebraMap (relativeSpecOverBaseHom g A A' φ) =
      (pushforwardAlgebraIso A).hom ≫ φ ≫ (relativeSpecPushforwardIsoOverBase g A').inv :=
  pushforwardAlgebraMap_overHomOfAlgebraHom _

/-- The morphism of relative spectra attached to the algebra map which a morphism `u` over `g`
induces is `u` itself. -/
theorem relativeSpecOverBaseHom_pushforwardAlgebraMap
    (u : Over.mk (relativeSpecToBase A' ≫ g) ⟶ Over.mk (relativeSpecToBase A)) :
    relativeSpecOverBaseHom g A A'
        ((pushforwardAlgebraIso A).inv ≫ pushforwardAlgebraMap u ≫
          (relativeSpecPushforwardIsoOverBase g A').hom) = u :=
  relativeSpecOverBaseHom_ext g A A'
    (by rw [pushforwardAlgebraMap_relativeSpecOverBaseHom_eq_conj]; simp)

/-- The algebra map induced by the morphism of relative spectra attached to `φ` is `φ`
itself. -/
theorem pushforwardAlgebraMap_relativeSpecOverBaseHom_conj
    (φ : A ⟶ (algebraPushforward g).obj A') :
    (pushforwardAlgebraIso A).inv ≫ pushforwardAlgebraMap (relativeSpecOverBaseHom g A A' φ) ≫
        (relativeSpecPushforwardIsoOverBase g A').hom = φ := by
  rw [pushforwardAlgebraMap_relativeSpecOverBaseHom_eq_conj]
  simp

/-- **The universal property of the relative spectrum over a varying base.**  For `g : T ⟶ S`,
a quasi-coherent `𝒪_S`-algebra `A` and a quasi-coherent `𝒪_T`-algebra `A'`, the morphisms
`\underline{Spec}_T(A') ⟶ \underline{Spec}_S(A)` of schemes over `S` — equivalently, the
morphisms of schemes lying over `g` — are in bijection with the morphisms `A ⟶ g_* A'` of
`𝒪_S`-algebras. -/
@[sga "3 I 4.2" "Hom_S(Spec A'", sga "3 III 0.1.7" "0.1.7(a)"]
def algebraHomEquivRelativeSpecOverBaseHom :
    (Over.mk (relativeSpecToBase A' ≫ g) ⟶ Over.mk (relativeSpecToBase A)) ≃
      (A ⟶ (algebraPushforward g).obj A') where
  toFun u := (pushforwardAlgebraIso A).inv ≫ pushforwardAlgebraMap u ≫
    (relativeSpecPushforwardIsoOverBase g A').hom
  invFun φ := relativeSpecOverBaseHom g A A' φ
  left_inv u := relativeSpecOverBaseHom_pushforwardAlgebraMap g A A' u
  right_inv φ := pushforwardAlgebraMap_relativeSpecOverBaseHom_conj g A A' φ

/-- The bijection of the universal property over a varying base carries a morphism over `g` to
the canonical map it induces on pushed-forward structure sheaves, read through the two universal
isomorphisms. -/
theorem algebraHomEquivRelativeSpecOverBaseHom_apply
    (u : Over.mk (relativeSpecToBase A' ≫ g) ⟶ Over.mk (relativeSpecToBase A)) :
    algebraHomEquivRelativeSpecOverBaseHom g A A' u =
      (pushforwardAlgebraIso A).inv ≫ pushforwardAlgebraMap u ≫
        (relativeSpecPushforwardIsoOverBase g A').hom :=
  congrFun (Equiv.coe_fn_mk _ _ _ _) u

/-- The inverse of the bijection of the universal property over a varying base is
`Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseHom`. -/
theorem algebraHomEquivRelativeSpecOverBaseHom_symm_apply
    (φ : A ⟶ (algebraPushforward g).obj A') :
    (algebraHomEquivRelativeSpecOverBaseHom g A A').symm φ =
      relativeSpecOverBaseHom g A A' φ :=
  congrFun (Equiv.coe_fn_symm_mk _ _ _ _) φ

end Stacks.AffineAlgebraEquivalence

end
