module

public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Zero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 00AG — pushforward along a closed embedding (sheaves of abelian groups)

Let `i : Z ⟶ X` be a closed embedding of topological spaces. Stacks 00AG states that the
pushforward `i_* : Ab(Z) → Ab(X)` on sheaves of abelian groups is fully faithful, with essential
image the sheaves whose stalks vanish at every point outside the range of `i`.

Two parts of the tag are proved, both by specialising the general statements of
`StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward`, which are proved for an
arbitrary value category:

* `closedInclusion_pushforward_faithful` and `closedInclusion_pushforward_full`: `i_*` is fully
  faithful, by `ClosedImmersionSheaves.sheafPushforwardFullyFaithful`. Only inducingness is used:
  every open `V ⊆ Z` is the preimage of an open of `X`, so a morphism of sheaves on `Z` is already
  determined by — and reconstructible from — the components of its pushforward.
* `closedInclusion_pushforward_essImage_stalk_isZero`: the forward direction of the
  essential-image description. It rests on
  `closedInclusion_pushforward_stalk_isZero_of_not_mem_range`, the vanishing of `(i_* 𝒜)_x` for
  `x` outside the range of `i`, which is
  `ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange` — the stalk there is a terminal
  object — combined with the fact that a terminal object of `AddCommGrpCat` is a zero object.

The reverse direction of the essential-image description is **not** proved here. It requires
infrastructure beyond Mathlib's present sheaf API for closed embeddings — the pullback along a
closed embedding, and the stalkwise behaviour of the counit of the resulting adjunction.
-/

@[expose] public section

open TopologicalSpace CategoryTheory TopCat Opposite Limits

universe u

/-- The pushforward functor on sheaves of abelian groups along a (closed) inclusion
`i : Z ⟶ X` of topological spaces. -/
def closedInclusionPushforward (Z X : TopCat.{u}) (i : Z ⟶ X) :
    TopCat.Sheaf AddCommGrpCat.{u} Z ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  TopCat.Sheaf.pushforward AddCommGrpCat i

/-! ### Full faithfulness via the inducing-map functor

For an inducing map `i : Z ⟶ X`, `Topology.IsInducing.functor` provides a right adjoint to
`Opens.map i` whose counit is invertible, so every open `V` of `Z` is the preimage of an open of
`X`; that is what makes `i_*` fully faithful. -/

/-- `i_* : Ab(Z) → Ab(X)` is fully faithful, by the general statement
`ClosedImmersionSheaves.sheafPushforwardFullyFaithful` for an inducing map. -/
noncomputable def closedInclusionPushforwardFullyFaithful
    (Z X : TopCat.{u}) (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom) :
    (closedInclusionPushforward Z X i).FullyFaithful :=
  ClosedImmersionSheaves.sheafPushforwardFullyFaithful (C := AddCommGrpCat.{u}) hi.isInducing

/-- **Stacks 00AG, faithfulness.** The pushforward of sheaves of abelian groups along a closed
embedding is a faithful functor. -/
@[stacks 00AG]
theorem closedInclusion_pushforward_faithful
    (Z X : TopCat.{u}) (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom) :
    (closedInclusionPushforward Z X i).Faithful :=
  (closedInclusionPushforwardFullyFaithful Z X i hi).faithful

/-- **Stacks 00AG, fullness.** The pushforward of sheaves of abelian groups along a closed
embedding is a full functor: every morphism `i_* 𝒜 ⟶ i_* ℬ` is `i_*` of a morphism `𝒜 ⟶ ℬ`. -/
@[stacks 00AG]
theorem closedInclusion_pushforward_full
    (Z X : TopCat.{u}) (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom) :
    (closedInclusionPushforward Z X i).Full :=
  (closedInclusionPushforwardFullyFaithful Z X i hi).full

/-! ### Pushforward stalks vanish off the range -/

/-- For a sheaf `𝒜` on `Z` and a point `x : X` outside the image of the closed embedding `i`,
the stalk of the pushforward `i_* 𝒜` at `x` is a zero object in `AddCommGrpCat`: it is a terminal
object, and a terminal object of `AddCommGrpCat` is isomorphic to `0`. -/
@[ega "0 3.4.6" "(F)",
  ega "0 4.2.5" "Ψ_*M is zero outside X",
  ega "IV 21.9.1" "special case",
  sga "6 IX 1.1" "Support clause"]
lemma closedInclusion_pushforward_stalk_isZero_of_not_mem_range
    (Z X : TopCat.{u}) (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom)
    (𝒜 : TopCat.Sheaf AddCommGrpCat.{u} Z) (x : X)
    (hx : x ∉ Set.range i.hom) :
    IsZero (Presheaf.stalk ((closedInclusionPushforward Z X i).obj 𝒜).1 x) :=
  IsZero.of_iso (isZero_zero AddCommGrpCat.{u})
    ((ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange i 𝒜.property hi x
      hx).uniqueUpToIso HasZeroObject.zeroIsTerminal)

/-- An isomorphism of sheaves of abelian groups on `X` induces an isomorphism of the stalks at
any fixed point of `X`. -/
noncomputable def stalk_iso_of_sheaf_iso
    (X : TopCat.{u}) {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (e : F ≅ G) (x : X) :
    Presheaf.stalk F.obj x ≅ Presheaf.stalk G.obj x :=
  (Presheaf.stalkFunctor _ x).mapIso
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).mapIso e)

/-! ### Essential image: forward direction (members have vanishing stalks off range) -/

/-- **Stacks 00AG, essential image, forward direction.** If a sheaf `G` of abelian groups on
`X` lies in the essential image of the pushforward along a closed embedding `i`, then the stalk
of `G` vanishes at every point outside the range of `i`. -/
@[stacks 00AG,
  ega "0 3.4.6" "(F)",
  ega "0 4.2.5" "Ψ_*M is zero outside X",
  ega "IV 21.9.1" "special case", sga "6 IX 1.1" "Support clause"]
theorem closedInclusion_pushforward_essImage_stalk_isZero
    (Z X : TopCat.{u}) (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom)
    (G : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hG : (closedInclusionPushforward Z X i).essImage G) :
    ∀ x : X, x ∉ Set.range i.hom → IsZero (Presheaf.stalk G.obj x) := by
  obtain ⟨𝒜, ⟨e⟩⟩ := hG
  intro x hx
  have h := closedInclusion_pushforward_stalk_isZero_of_not_mem_range Z X i hi 𝒜 x hx
  exact h.of_iso (stalk_iso_of_sheaf_iso X e x).symm
