module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.Topology.Sets.OpenCover
public import StacksCore.Tactic.StacksAttribute

/-!
# Gluing morphisms along an arbitrary family of opens covering a scheme

Let `T` be a scheme and `W : s → T.Opens` a family of open subschemes covering it. A family of
morphisms `g a : W a ⟶ Z` which agree on the overlaps `W a ⊓ W b` is the family of restrictions
of a unique morphism `T ⟶ Z`.

`AlgebraicGeometry.Scheme.hom_ext_of_forall` is the uniqueness half of this, and is all the
library had: the existence half is `AlgebraicGeometry.Scheme.Cover.glueMorphisms`, whose
compatibility hypothesis is stated on the *chosen fibre product* of two members of the cover
rather than on their intersection as opens. For a family of opens the two presentations are
identified by `AlgebraicGeometry.isPullback_opens_inf`, and that is the whole content of this
file.

`AlgebraicGeometry.Scheme.existsUnique_hom_of_compatible` is a different statement: it asks for
the family to be indexed by a preorder which is inclusion of the members and to be a *basis* of
the topology, which makes the cover locally directed and lets compatibility be checked against
the inclusions `W a ≤ W b` alone. An open covering is not a basis, so that version does not
apply to one.

## Main results

* `AlgebraicGeometry.Scheme.existsUnique_hom_of_opens_cover`: **a family of morphisms out of the
  members of an open covering of `T` agreeing on the pairwise intersections comes from a unique
  morphism out of `T`.**

## References

* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- **Morphisms out of a scheme glue along an open covering.** A family of morphisms `g a` out of
the members of a family of opens covering `T` which agree on the intersections `W a ⊓ W b` is the
family of restrictions of a unique morphism `T ⟶ Z`.

The existence is `AlgebraicGeometry.Scheme.Cover.glueMorphisms`, after
`AlgebraicGeometry.isPullback_opens_inf` has rewritten the agreement on the intersection of two
opens as agreement on the chosen fibre product of their inclusions; the uniqueness is
`AlgebraicGeometry.Scheme.Cover.hom_ext`. -/
theorem existsUnique_hom_of_opens_cover {T Z : Scheme.{u}} {s : Type*} (W : s → T.Opens)
    (hW : ∀ x : T, ∃ a, x ∈ W a) (g : ∀ a, (W a).toScheme ⟶ Z)
    (hg : ∀ a b, T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a) ≫ g a =
      T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b) ≫ g b) :
    ∃! f : T ⟶ Z, ∀ a, (W a).ι ≫ f = g a := by
  have hcov : IsOpenCover W :=
    top_le_iff.mp fun x _ => Opens.mem_iSup.mpr (hW x)
  let 𝒰 : T.OpenCover := T.openCoverOfIsOpenCover W hcov
  refine ⟨𝒰.glueMorphisms g ?_, fun a => 𝒰.ι_glueMorphisms g _ a,
    fun f' hf' => 𝒰.hom_ext _ _ fun a => (hf' a).trans (𝒰.ι_glueMorphisms g _ a).symm⟩
  intro a b
  change pullback.fst (W a).ι (W b).ι ≫ g a = pullback.snd (W a).ι (W b).ι ≫ g b
  rw [← cancel_epi (isPullback_opens_inf (W a) (W b)).isoPullback.hom, ← Category.assoc,
    ← Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]
  exact hg a b

end AlgebraicGeometry.Scheme

end
