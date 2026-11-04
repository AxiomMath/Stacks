module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.Slice
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.Situation

/-!
# Weakly contractible objects that stay weakly contractible on the slices

`Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation` fixes a covering collection `B`
of objects of a site over which locally surjective morphisms of sheaves of sets valued in an
independent universe `t` are surjective on sections. The derived-completeness results consume
that collection twice: on the site itself, and on each slice site `C/U`, because derived
completeness of a complex of sheaves of modules is a condition on its restriction to every
slice. This file bundles the two.

The slice condition is a separate field rather than a consequence of the first one. Transporting
weak contractibility to a slice goes through the equivalence between sheaves on `C/U` and
sheaves on `C` over the sheafified representable `h_U^#`
(`Stacks.WeaklyContractible.weaklyContractible_over`), which is available only at the morphism
universe of the site, and the transfer from that universe to `t` needs the site to be `Type v`
small — the hypothesis the situation bundle exists in order to avoid. A site that is `Type v`
small does supply the field, which is `Stacks.WeaklyContractible.SlicedObjectsSituation.of`.

## Main definitions

* `Stacks.WeaklyContractible.SlicedObjectsSituation`: the bundle, a
  `WeaklyContractibleObjectsSituation` together with the same statement on every slice site.
* `Stacks.WeaklyContractible.SlicedObjectsSituation.over`: the situation it induces on a slice.
* `Stacks.WeaklyContractible.SlicedObjectsSituation.of`: the bundle supplied by a weakly
  contractible testing family on a `Type v`-small site.

## Main results

* `Stacks.WeaklyContractible.hasEnoughObjects_over`: a covering collection of objects of a site
  covers every object of every slice site, through the arrows whose source it contains.

## References

* [Stacks Project, Tag 0945](https://stacks.math.columbia.edu/tag/0945)
* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
-/

@[expose] public section

open CategoryTheory Opposite

universe t w w' v u

namespace Stacks.WeaklyContractible

/-- The sheaf of rings of a situation may be replaced by any other sheaf of rings on the same
site: it is data attached to the collection of objects, not a constraint on it. -/
def WeaklyContractibleObjectsSituation.withRing {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (h : WeaklyContractibleObjectsSituation.{w, v, u, t} C J)
    (O : Sheaf J RingCat.{w'}) : WeaklyContractibleObjectsSituation.{w', v, u, t} C J where
  B := h.B
  isWeaklyContractible := h.isWeaklyContractible
  hasEnoughObjects := h.hasEnoughObjects
  O := O

/-- A collection of objects of a site which is covering, whose members test surjectivity of
morphisms of sheaves of sets valued in `Type t`, and which continues to test it on every slice
site, through the arrows whose source belongs to the collection. -/
structure SlicedObjectsSituation.{w₀, v₀, u₀, t₀}
    (C : Type u₀) [Category.{v₀} C] (J : GrothendieckTopology C) extends
    WeaklyContractibleObjectsSituation.{w₀, v₀, u₀, t₀} C J where
  /-- An arrow of the site whose source belongs to the collection is a testing object of the
  slice site over its target. -/
  isWeaklyContractibleOver : ∀ (U : C) ⦃Z : Over U⦄, B Z.left →
    ∀ (F G : Sheaf (J.over U) (Type t₀)) (φ : F ⟶ G),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op Z))

/-- A covering collection of objects of a site covers every object of every slice site: an
object `W` of `C/U` is covered by the arrows `V i ⟶ W` coming from a covering `{V i ⟶ W.left}`
of its source by members of the collection. -/
theorem hasEnoughObjects_over {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {B : ObjectProperty C} (hB : J.HasEnoughObjects B) (U : C) :
    (J.over U).HasEnoughObjects (fun Z : Over U ↦ B Z.left) := by
  intro W
  obtain ⟨I, V, f, hf, hV⟩ := hB W.left
  refine ⟨I, fun i ↦ Over.mk (f i ≫ W.hom), fun i ↦ Over.homMk (f i), ?_, hV⟩
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact hf

/-- The situation a sliced bundle induces on the slice site over an object, with a chosen sheaf
of rings there. -/
def SlicedObjectsSituation.over {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (h : SlicedObjectsSituation.{w, v, u, t} C J) (U : C)
    (O : Sheaf (J.over U) RingCat.{w'}) :
    WeaklyContractibleObjectsSituation.{w', v, max u v, t} (Over U) (J.over U) where
  B Z := h.B Z.left
  isWeaklyContractible := h.isWeaklyContractibleOver U
  hasEnoughObjects := hasEnoughObjects_over h.hasEnoughObjects U
  O := O

/-- On a `Type v`-small site a weakly contractible testing family is a sliced bundle, at the
value universe `max u v` of the sheaves of modules on it.

Both surjectivity statements come from the universe transfer
`Stacks.WeaklyContractible.surjective_sections_of_isWeaklyContractible`, applied on the site
itself and on the slice site, where weak contractibility of the arrows with source in the
family is `Stacks.WeaklyContractible.weaklyContractible_over`. -/
def SlicedObjectsSituation.of {C : Type u} [Category.{v} C] [Small.{v} C]
    {J : GrothendieckTopology C} [HasSheafify J (Type v)]
    (h : WeaklyContractibleTestingFamily C J) (O : Sheaf J RingCat.{w}) :
    SlicedObjectsSituation.{w, v, u, max u v} C J where
  B := h.B
  isWeaklyContractible _ hU :=
    surjective_sections_of_isWeaklyContractible.{max u v} J _ (h.isWeaklyContractible hU)
  hasEnoughObjects := h.hasEnoughObjects
  O := O
  isWeaklyContractibleOver U _ hZ := by
    let : Small.{v} (Over U) := smallOverOfSmall U
    let : J.WEqualsLocallyBijective (Type v) := wEqualsLocallyBijective_types J
    let : HasSheafify (J.over U) (Type v) :=
      CategoryTheory.hasSheafifyEssentiallySmallSite (J.over U) (Type v)
    exact surjective_sections_of_isWeaklyContractible.{max u v} (J.over U) _
      (weaklyContractible_over J _ (h.isWeaklyContractible hZ))

end Stacks.WeaklyContractible

end
