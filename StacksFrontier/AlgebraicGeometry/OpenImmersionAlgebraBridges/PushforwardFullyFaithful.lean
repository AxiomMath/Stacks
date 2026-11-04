module

public import Mathlib.Topology.Sheaves.Functors

/-!
# Sheaf pushforward along a topological embedding is fully faithful

Let `f : X ⟶ Y` be a continuous map of topological spaces which is *inducing*, i.e. which
gives `X` the subspace topology from its image, and let `A` be any category. Then

  `TopCat.Sheaf.pushforward A f : Sh(X, A) ⥤ Sh(Y, A)`

is full and faithful. The reason is that `Opens.map f : Opens Y ⥤ Opens X` is then
**surjective on objects** — for an inducing map every open of `X` is the preimage of an open
of `Y`, and `Topology.IsInducing.functorObj` picks one out — so `Opens.map f` is cover-dense,
and Mathlib's dense-subsite machinery
(`CategoryTheory.Functor.IsCoverDense.full_sheafPushforwardContinuous`) does the rest.

## Main results

* `Stacks.SheafPushforwardInducing.isCoverDense_opensMap`: `Opens.map f` is cover-dense for an
  inducing `f`.
* `Stacks.SheafPushforwardInducing.fullyFaithful_pushforward_of_isInducing`: the pushforward
  functor is fully faithful, for an arbitrary target category.

## What this generalises, and why it had to be restated

`Stacks.full_and_faithful_pushforward_subsetInclusion`
(`StacksFrontier/Topology/Sheaves/ClosedImmersion/PushforwardAlgStruct.lean`, Stacks Tag 00AH
part 1) is the same statement for the *specific* morphism `Stacks.subsetInclusion X Z :
TopCat.of Z ⟶ X` attached to a subset `Z ⊆ X`. That theorem is already stated for an
**arbitrary** subset — its file is named `ClosedImmersion/` but its own docstring records that
closedness is used only for the essential-image half — so nothing about closed sets was ever in
the way. What *is* in the way is that `Stacks.subsetInclusion X Z` is one particular morphism of
`TopCat`, not a variable: the underlying map `j.base` of a scheme open immersion `j : U ⟶ X` is
not an instance of it (`U` is an abstract scheme, its carrier is not `TopCat.of Z`), so the
theorem cannot be *applied*, only reproved. The reproof is the one below, and generalising the
binder from a subset inclusion to an arbitrary inducing map costs exactly one line: the
surjectivity of `Opens.map` on objects, which `Topology.IsInducing.map_functorObj` supplies.

Two hypotheses of that statement are also unnecessary here. It asks for
`S : AlgebraicStructureType` with `HasColimits S.C`; Mathlib's full and faithful instances for
`Functor.sheafPushforwardContinuous` are stated over a bare `A : Type*` with `[Category A]`, so
the target category needs no forgetful functor, no limits and no colimits. And its hand-built
`CoverPreserving`/`IsContinuous` step for `Opens.map` duplicates the global Mathlib instance
`(Opens.map f).IsContinuous` of `Mathlib/Topology/Sheaves/SheafCondition/Sites.lean`.

Pinned Mathlib itself states no fullness or faithfulness of `TopCat.Sheaf.pushforward` under
`Topology.IsOpenEmbedding`: `Mathlib/Topology/Sheaves/Functors.lean` builds the naive pullback
`Topology.IsOpenEmbedding.sheafPullback` and its comparison with `TopCat.Sheaf.pullback`, and
stops there.

## References

* [Stacks Project, Tag 00AH](https://stacks.math.columbia.edu/tag/00AH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat

universe u v w

namespace Stacks.SheafPushforwardInducing

variable {X Y : TopCat.{u}} {f : X ⟶ Y}

/-- For an inducing map `f : X ⟶ Y`, every open of `X` is the preimage of an open of `Y`:
`Topology.IsInducing.functorObj` is a right inverse of `Opens.map f` on objects. -/
public theorem opensMap_surjective (hf : Topology.IsInducing f) :
    Function.Surjective (Opens.map f).obj :=
  fun V => ⟨hf.functorObj V, hf.map_functorObj V⟩

/-- `Opens.map f` is cover-dense for an inducing `f`: every open of `X` is literally in the
image of the functor, so the identity sieve on it is covered by images. -/
public theorem isCoverDense_opensMap (hf : Topology.IsInducing f) :
    (Opens.map f).IsCoverDense (Opens.grothendieckTopology X) := by
  constructor
  intro V x hx
  obtain ⟨W, hW⟩ := opensMap_surjective hf V
  exact ⟨V, 𝟙 V, ⟨⟨W, eqToHom hW.symm, eqToHom hW, by simp⟩⟩, hx⟩

/-- `Opens.map f` is locally full for any continuous `f`: an inclusion `f⁻¹U ≤ f⁻¹V` of
preimages is witnessed on the cover of `f⁻¹U` by `f⁻¹(U ⊓ V)`. No hypothesis on `f` is used —
morphisms between opens are unique, so the image sieve is already large. -/
public instance isLocallyFull_opensMap :
    (Opens.map f).IsLocallyFull (Opens.grothendieckTopology X) := by
  constructor
  intro U V g x hx
  exact ⟨(Opens.map f).obj (U ⊓ V), (Opens.map f).map (homOfLE inf_le_left),
    ⟨U ⊓ V, homOfLE inf_le_left, 𝟙 _, ⟨homOfLE inf_le_right, Subsingleton.elim _ _⟩, by simp⟩,
    hx, leOfHom g hx⟩

/-- `Opens.map f` is locally faithful for any continuous `f`: two parallel morphisms of opens
are equal, so their equalizer sieve is the top sieve. -/
public instance isLocallyFaithful_opensMap :
    (Opens.map f).IsLocallyFaithful (Opens.grothendieckTopology X) := by
  constructor
  intro U V g₁ g₂ _
  obtain rfl : g₁ = g₂ := Subsingleton.elim _ _
  rw [Sieve.equalizer_self, Sieve.functorPushforward_top]
  exact (Opens.grothendieckTopology _).top_mem _

/-- **Sheaf pushforward along an embedding is fully faithful.** For an inducing continuous map
`f : X ⟶ Y` and an arbitrary category `A`, the direct image `f_* : Sh(X, A) ⥤ Sh(Y, A)` is
fully faithful. This is Stacks Tag 00AH part (1) with the subset inclusion replaced by a
variable morphism and with no hypothesis on the target category. -/
public noncomputable def fullyFaithful_pushforward_of_isInducing (hf : Topology.IsInducing f)
    (A : Type v)
    [Category.{w} A] : (TopCat.Sheaf.pushforward A f).FullyFaithful :=
  letI := isCoverDense_opensMap hf
  letI : (TopCat.Sheaf.pushforward A f).Full :=
    Functor.IsCoverDense.full_sheafPushforwardContinuous _ _ _
  letI : (TopCat.Sheaf.pushforward A f).Faithful :=
    Functor.IsCoverDense.faithful_sheafPushforwardContinuous _ _ _
  Functor.FullyFaithful.ofFullyFaithful _

/-- The pushforward along an inducing map is full. -/
public theorem full_pushforward_of_isInducing (hf : Topology.IsInducing f) (A : Type v)
    [Category.{w} A] : (TopCat.Sheaf.pushforward A f).Full :=
  (fullyFaithful_pushforward_of_isInducing hf A).full

/-- The pushforward along an inducing map is faithful. -/
public theorem faithful_pushforward_of_isInducing (hf : Topology.IsInducing f) (A : Type v)
    [Category.{w} A] : (TopCat.Sheaf.pushforward A f).Faithful :=
  (fullyFaithful_pushforward_of_isInducing hf A).faithful

end Stacks.SheafPushforwardInducing
