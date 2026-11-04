module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafEquivalence

/-!
# The comparison of two direct images is compatible with postcomposition

Let `G ⊂ X'` be a thickening of algebraic spaces with inclusion `i : X ⟶ X'`, and let
`a', b' : X' ⟶ Y'` be two morphisms with `i ≫ a' = i ≫ b'`.  The comparison of the two direct
images `AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq` of [Stacks Project,
Tag 05ZM] is built from the agreement of the two morphisms on the closed subspace: it is
`CategoryTheory.Equivalence.cancelCompLeft` of the comparison *after precomposition with* `i_*`,
which is functoriality of the direct image together with the hypothesis.

This file supplies the companion statement for **postcomposition**.  If in addition
`q : Y' ⟶ Bb` is a morphism with `a' ≫ q = b' ≫ q` — the two morphisms being morphisms over
`Bb`, which is a hypothesis about the morphisms themselves and not about their restrictions —
then the comparison read through `q_*` is the comparison that the equality `a' ≫ q = b' ≫ q`
induces, again by functoriality of the direct image.

That is the compatibility which the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftPairActionSection` record as owed by the
hypothesis `hφ` of [Stacks Project, Tag 0618]: with it, the comparison of the two inverse
images may be computed on a sheaf pulled back from `Bb`, which is what says that the difference
of the two structure maps kills `q^{-1}𝒪_{Bb}` and is therefore a `Bb`-derivation.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleCompPushforwardIsoOfCompEq`: the comparison of
  `a'_* ⋙ q_*` with `b'_* ⋙ q_*` induced by `a' ≫ q = b' ≫ q`, built exactly as
  `AlgebraicGeometry.Space.smallEtaleCompPushforwardIsoOfRestrictEq` is built from
  `i ≫ a' = i ≫ b'` — two composition isomorphisms of [Stacks Project, Tag 03G2] part (3) with
  the transport along the hypothesis between them.

## Main results

* `AlgebraicGeometry.Space.map_eqToIso_comp_smallToposMorphismTypeU_comp` and
  `AlgebraicGeometry.Space.eqToIso_comp_smallToposMorphismTypeU_comp`: the two bookkeeping
  lemmas which move a transport along an equality of morphisms across a composition
  isomorphism, in each of its two slots.
* `AlgebraicGeometry.Space.map_eqToIso_comp_smallToposMorphismTypeU_comp_assoc` and
  `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc_comp_eqToIso`: the first two steps
  of the cocycle chase which compares the two comparisons on a direct image `i_*F`.

## Where the chase is completed

The chase **is** completed, in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEqPostcompose`, as
`AlgebraicGeometry.Space.whiskerRight_smallEtalePushforwardIsoOfRestrictEq_comp` and its
pointwise form `AlgebraicGeometry.Space.map_smallEtalePushforwardIsoOfRestrictEq_hom_app`.

Joining them naively does not work: composing the two steps above
with the second slot's bookkeeping lemma forces the kernel to identify
`(i ≫ a') ≫ q = (i ≫ b') ≫ q` with `i ≫ (a' ≫ q) = i ≫ (b' ≫ q)` inside an `eqToHom`, and
dies with `(kernel) deterministic timeout`.  The cure is not a respelling of the *bracketing*:
the bracketing is free and the **level** is not:

* `(i ≫ a') ≫ q = i ≫ a' ≫ q` is `rfl` in `AlgebraicGeometry.AlgebraicSpaces`, cheaply;
* so are the two bracketings of a transport taken between the two direct images of one sheaf;
* the two bracketings of a transport taken between the two direct image *functors* and then
  read at a sheaf are what the kernel cannot afford, proof irrelevance inside an `eqToHom`
  reducing to the equality of its types and those types mentioning
  `(smallToposMorphismTypeU B S hS _).pushforward`.

So the remedy is to take every transport at the level of objects, which is what the two lemmas
`AlgebraicGeometry.Space.map_eqToHom_comp_smallToposMorphismTypeU_comp` and
`AlgebraicGeometry.Space.eqToHom_comp_smallToposMorphismTypeU_comp` of that file do, converting
once with `AlgebraicGeometry.Space.eqToIso_pushforward_hom_app` where a definition hands in a
functor-level transport.  Neither the functor-level bookkeeping lemmas below nor
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc` had to change.

## Implementation notes

Each bookkeeping lemma has the equality of morphisms as a variable, so that `subst` applies and
at an instantiation neither has to be restated.  They are what the associativity cocycle
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc` has to be composed with in order to
compare the two comparisons on a direct image `i_*F`: on such a sheaf the comparison of
[Stacks Project, Tag 05ZM] *is* the precomposition one
(`AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq_hom_app_pushforward`), and since
`i_*` is an equivalence `CategoryTheory.NatTrans.ext_of_essSurj`
(`StacksFrontier/CategoryTheory/Shift/DetectingCommShift.lean`) carries an identity proved there to
every sheaf.

Two measurements from building this file.  `CategoryTheory.Functor.map_id` does not fire as a
`simp` lemma here and has to be `rw`-ritten with **both** arguments explicit; and it must be
written `CategoryTheory.Functor.map_id`, since the bare `Functor.map_id` resolves to the monadic
one.  `Category.id_comp` likewise needs its morphism supplied, because the identity it cancels
sits at `(MorphismOfTopoi.comp _ _).pushforward.obj F` while the goal spells that object as an
iterated `Functor.obj` — the two are definitionally equal but not syntactically, so no keyed
matching finds it.

No `@[stacks]` attribute is claimed: this is a compatibility between two instances of the
comparison of [Stacks Project, Tag 05ZM], and the tag stays where
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafEquivalence` has it.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Moving a transport across a composition isomorphism -/

section Transport

variable {U V W : AlgebraicSpaces B S hS}

/-- **A transport along an equality of the first morphism crosses the composition isomorphism.**
For `k₁ = k₂ : U ⟶ V` and `q : V ⟶ W`, the direct image along `q` of the transport from `(k₁)_*`
to `(k₂)_*`, followed by the composition isomorphism at `(k₂, q)`, is the composition
isomorphism at `(k₁, q)` followed by the transport along `k₁ ≫ q = k₂ ≫ q`. -/
theorem map_eqToIso_comp_smallToposMorphismTypeU_comp {k₁ k₂ : U ⟶ V} (e : k₁ = k₂) (q : V ⟶ W)
    (e' : k₁ ≫ q = k₂ ≫ q) (F : Sheaf (SmallEtale.topology B S hS U.1) (Type u)) :
    (smallToposMorphismTypeU B S hS q).pushforward.map
          ((eqToIso (congrArg
            (fun k => (smallToposMorphismTypeU B S hS k).pushforward) e)).hom.app F) ≫
        (smallToposMorphismTypeU_comp B S hS k₂ q).hom.app F =
      (smallToposMorphismTypeU_comp B S hS k₁ q).hom.app F ≫
        (eqToIso (congrArg
          (fun k => (smallToposMorphismTypeU B S hS k).pushforward) e')).hom.app F := by
  subst e
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  rw [CategoryTheory.Functor.map_id (smallToposMorphismTypeU B S hS q).pushforward
    ((smallToposMorphismTypeU B S hS k₁).pushforward.obj F)]
  exact Category.id_comp ((smallToposMorphismTypeU_comp B S hS k₁ q).hom.app F)

/-- **A transport along an equality of the second morphism crosses the composition isomorphism.**
For `i : U ⟶ V` and `g₁ = g₂ : V ⟶ W`, the transport from `(g₁)_*` to `(g₂)_*` read at `i_*F`,
followed by the composition isomorphism at `(i, g₂)`, is the composition isomorphism at
`(i, g₁)` followed by the transport along `i ≫ g₁ = i ≫ g₂`. -/
theorem eqToIso_comp_smallToposMorphismTypeU_comp (i : U ⟶ V) {g₁ g₂ : V ⟶ W} (e : g₁ = g₂)
    (e' : i ≫ g₁ = i ≫ g₂) (F : Sheaf (SmallEtale.topology B S hS U.1) (Type u)) :
    (eqToIso (congrArg (fun k => (smallToposMorphismTypeU B S hS k).pushforward) e)).hom.app
          ((smallToposMorphismTypeU B S hS i).pushforward.obj F) ≫
        (smallToposMorphismTypeU_comp B S hS i g₂).hom.app F =
      (smallToposMorphismTypeU_comp B S hS i g₁).hom.app F ≫
        (eqToIso (congrArg
          (fun k => (smallToposMorphismTypeU B S hS k).pushforward) e')).hom.app F := by
  subst e
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  exact Category.id_comp ((smallToposMorphismTypeU_comp B S hS i g₁).hom.app F)

/-- **The first step of the cocycle chase**: the bookkeeping lemma for the first slot,
reassociated so that the transport along `(i ≫ a') ≫ q = (i ≫ b') ≫ q` stands at the right of
the composite.  It is a declaration of its own because the kernel budget for checking the whole
chase in one declaration is not enough and each step alone fits. -/
theorem map_eqToIso_comp_smallToposMorphismTypeU_comp_assoc
    {U V W Z : AlgebraicSpaces B S hS} (i : U ⟶ V) (a' b' : V ⟶ W)
    (q : W ⟶ Z) (h : i ≫ a' = i ≫ b') (h' : (i ≫ a') ≫ q = (i ≫ b') ≫ q)
    (F : Sheaf (SmallEtale.topology B S hS U.1) (Type u)) :
    (smallToposMorphismTypeU B S hS q).pushforward.map
          ((smallToposMorphismTypeU_comp B S hS i a').hom.app F) ≫
        (smallToposMorphismTypeU B S hS q).pushforward.map
          ((eqToIso (congrArg
            (fun k => (smallToposMorphismTypeU B S hS k).pushforward) h)).hom.app F) ≫
        (smallToposMorphismTypeU_comp B S hS (i ≫ b') q).hom.app F =
      ((smallToposMorphismTypeU B S hS q).pushforward.map
            ((smallToposMorphismTypeU_comp B S hS i a').hom.app F) ≫
          (smallToposMorphismTypeU_comp B S hS (i ≫ a') q).hom.app F) ≫
        (eqToIso (congrArg
          (fun k => (smallToposMorphismTypeU B S hS k).pushforward) h')).hom.app F :=
  (congrArg (fun m => _ ≫ m)
      (map_eqToIso_comp_smallToposMorphismTypeU_comp B S hS h q h' F)).trans
    (Category.assoc _ _ _).symm

/-- **The second step of the cocycle chase**: the associativity cocycle
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc` of [Stacks Project, Tag 03G2]
part (3), applied under the transport along `(i ≫ a') ≫ q = (i ≫ b') ≫ q`. -/
theorem smallToposMorphismTypeU_comp_assoc_comp_eqToIso
    {U V W Z : AlgebraicSpaces B S hS} (i : U ⟶ V) (a' b' : V ⟶ W)
    (q : W ⟶ Z) (h' : (i ≫ a') ≫ q = (i ≫ b') ≫ q)
    (F : Sheaf (SmallEtale.topology B S hS U.1) (Type u)) :
    ((smallToposMorphismTypeU B S hS q).pushforward.map
            ((smallToposMorphismTypeU_comp B S hS i a').hom.app F) ≫
          (smallToposMorphismTypeU_comp B S hS (i ≫ a') q).hom.app F) ≫
        (eqToIso (congrArg
          (fun k => (smallToposMorphismTypeU B S hS k).pushforward) h')).hom.app F =
      ((smallToposMorphismTypeU_comp B S hS a' q).hom.app
            ((smallToposMorphismTypeU B S hS i).pushforward.obj F) ≫
          (smallToposMorphismTypeU_comp B S hS i (a' ≫ q)).hom.app F) ≫
        (eqToIso (congrArg
          (fun k => (smallToposMorphismTypeU B S hS k).pushforward) h')).hom.app F :=
  congrArg (fun m => m ≫ _) (smallToposMorphismTypeU_comp_assoc B S hS i a' q F)

end Transport

/-! ### The comparison induced by an equality of the composites -/

section Restrict

variable {X' Y' Bb : AlgebraicSpaces B S hS} {G : Subfunctor X'.1}
  (hG : IsThickening B S hS X' G) (a' b' : X' ⟶ Y')

/-- **The comparison of the two direct images induced by an equality of the composites with a
third morphism.**  For `a' ≫ q = b' ≫ q` the two composites `a'_* ⋙ q_*` and `b'_* ⋙ q_*` are
isomorphic, by functoriality of the direct image ([Stacks Project, Tag 03G2] part (3)) and the
hypothesis.

This is built exactly as `AlgebraicGeometry.Space.smallEtaleCompPushforwardIsoOfRestrictEq` is,
with precomposition by the inclusion replaced by postcomposition by `q`; no thickening is
involved. -/
def smallEtaleCompPushforwardIsoOfCompEq (q : Y' ⟶ Bb) (hq : a' ≫ q = b' ≫ q) :
    (smallToposMorphismTypeU B S hS a').pushforward ⋙
        (smallToposMorphismTypeU B S hS q).pushforward ≅
      (smallToposMorphismTypeU B S hS b').pushforward ⋙
        (smallToposMorphismTypeU B S hS q).pushforward :=
  smallToposMorphismTypeU_comp B S hS a' q ≪≫
    eqToIso (congrArg (fun k => (smallToposMorphismTypeU B S hS k).pushforward) hq) ≪≫
    (smallToposMorphismTypeU_comp B S hS b' q).symm

end Restrict

end AlgebraicGeometry.Space

end
