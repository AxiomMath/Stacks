module

public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Embeddings of topoi

## Main definitions

* `MorphismOfTopoi.IsEmbedding`: a morphism of topoi is an *embedding* when its pushforward
  `f_*` is fully faithful (Stacks 08LU).

## Main results

* `MorphismOfTopoi.isEmbedding_iff_isIso_counit_app`: a morphism of topoi is an embedding
  precisely when the adjunction map `f⁻¹ f_* G ⟶ G` is an isomorphism for every `G`. This is
  the remark following Stacks 08LU, which the Stacks Project deduces from Lemma 04D6.

Tags covered: 08LU.
-/

@[expose] public section

open CategoryTheory

universe v u v' u'

namespace MorphismOfTopoi

variable {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]

/-- **Stacks Project, Definition 7.43.1 (tag 08LU).**

A morphism of topoi `f : E → F` is an *embedding* if its pushforward `f_*` is fully faithful. -/
@[stacks 08LU, sga "4 IV 9.1.1" "a)", sga "4 IV 9.1" "embedding def"]
def IsEmbedding (f : MorphismOfTopoi E F) : Prop :=
  f.pushforward.Full ∧ f.pushforward.Faithful

namespace IsEmbedding

variable {f : MorphismOfTopoi E F}

/-- The pushforward of an embedding of topoi is full. -/
lemma full (hf : f.IsEmbedding) : f.pushforward.Full := hf.1

/-- The pushforward of an embedding of topoi is faithful. -/
lemma faithful (hf : f.IsEmbedding) : f.pushforward.Faithful := hf.2

/-- The fully faithful structure on the pushforward of an embedding of topoi. -/
noncomputable def fullyFaithful (hf : f.IsEmbedding) : f.pushforward.FullyFaithful :=
  have := hf.full
  have := hf.faithful
  .ofFullyFaithful _

end IsEmbedding

/-- A morphism of topoi is an embedding if and only if the adjunction map
`f⁻¹ f_* G ⟶ G` is an isomorphism for every object `G` of the source topos.

This is the remark following Stacks Project Definition 7.43.1 (tag 08LU); the Stacks Project
obtains it from Lemma 04D6, and it is here the equivalence between a right adjoint being fully
faithful and the counit of the adjunction being invertible. -/
@[sga "4 IV 9.1.1" "more general"]
theorem isEmbedding_iff_isIso_counit_app (f : MorphismOfTopoi E F) :
    f.IsEmbedding ↔ ∀ G : E, IsIso (f.adj.counit.app G) := by
  refine ⟨fun hf G => ?_, fun h => ?_⟩
  · have := hf.full
    have := hf.faithful
    infer_instance
  · have : IsIso f.adj.counit := NatIso.isIso_of_isIso_app _
    have hff := f.adj.fullyFaithfulROfIsIsoCounit
    exact ⟨hff.full, hff.faithful⟩

end MorphismOfTopoi
