module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications

/-!
# Interior-preserving morphisms of compactifications

Let `X` be a scheme over `S` and let `j : X ⟶ j.space` and `k : X ⟶ k.space` be two
compactifications of `X` over `S`.  A morphism `g : j ⟶ k` of compactifications preserves the
interior when the inverse image under `g` of the interior `k(X) ⊆ k.space` is exactly the
interior `j(X) ⊆ j.space`.  This is the condition under which the two exceptional inverse image
functors attached to `j` and `k` are compared by the adjunction, and it is *not* automatic for
the notion of compactification used here.

The main result is that a morphism out of a compactification with dense interior always preserves
the interior.  This is [Stacks, Tag 0ATU] part (c), already available in this library as
`AlgebraicGeometry.preimage_range_immersion_eq`; the content here is that the bundled standing
data `AlgebraicGeometry.CategoryOfCompactifications` that lemma asks for can be manufactured from
a Noetherian base alone, so the hypothesis is just `IsNoetherian S`.

Also recorded is the purely formal step by which a coherent family of isomorphisms indexed by the
compactifications of `X` is computed from any common refinement
(`CategoryTheory.Iso.eq_symm_trans_of_trans`): once the comparison isomorphisms of
[Stacks, Tag 0AA0] exist and compose, the dense-refinement formula for them is this lemma.

## Main definitions

* `AlgebraicGeometry.CompactificationOf.PreservesInterior` — a morphism of compactifications
  whose inverse image of the target interior is the source interior.

## Main results

* `AlgebraicGeometry.CompactificationOf.compactSpace` and
  `AlgebraicGeometry.CompactificationOf.quasiSeparatedSpace` — the ambient scheme of a
  compactification inherits quasi-compactness and quasi-separatedness from the base.
* `AlgebraicGeometry.CompactificationOf.preservesInterior_of_denseRange` — a morphism out of a
  compactification with dense interior preserves the interior.
* `CategoryTheory.Iso.eq_symm_trans_of_trans` — a transitive family of isomorphisms is computed
  from any common refinement.

## References

* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe v u

namespace CategoryTheory.Iso

/-- A family of isomorphisms that composes transitively is determined by its values out of any
single object: `e i j = (e r i)⁻¹ ≫ e r j` for every `r`.  Together with the existence of such a
family this is the whole content of the dense-refinement formula for the comparison isomorphisms
of [Stacks, Tag 0AA0]. -/
theorem eq_symm_trans_of_trans {C : Type u} [Category.{v} C] {ι : Type*} {F : ι → C}
    (e : ∀ i j, F i ≅ F j) (htrans : ∀ i j k, e i j ≪≫ e j k = e i k) (i j r : ι) :
    e i j = (e r i).symm ≪≫ e r j := by
  rw [← htrans r i j, Iso.symm_self_id_assoc]

end CategoryTheory.Iso

namespace AlgebraicGeometry.CompactificationOf

variable {S : Scheme.{u}} {X : Over S}

/-- The ambient scheme of a compactification of a scheme over a quasi-compact base is
quasi-compact: it is proper, hence quasi-compact, over the base. -/
instance compactSpace [CompactSpace S] (j : CompactificationOf X) : CompactSpace j.space :=
  QuasiCompact.compactSpace_of_compactSpace j.toBase

/-- The ambient scheme of a compactification of a scheme over a quasi-separated base is
quasi-separated: it is separated, hence quasi-separated, over the base. -/
instance quasiSeparatedSpace [QuasiSeparatedSpace S] (j : CompactificationOf X) :
    QuasiSeparatedSpace j.space :=
  quasiSeparatedSpace_of_quasiSeparated j.toBase

/-- A morphism of compactifications **preserves the interior** when the inverse image of the
interior of the target is exactly the interior of the source.  With the notion of
compactification used here this may fail, and it is exactly the hypothesis under which the
exceptional inverse images attached to the two compactifications are compared by the
adjunction. -/
def PreservesInterior {j k : CompactificationOf X} (g : j ⟶ k) : Prop :=
  (CompactificationOf.Hom.map g).base ⁻¹' Set.range k.immersion.base =
    Set.range j.immersion.base

/-- **A morphism out of a compactification with dense interior preserves the interior.**  Over a
Noetherian base the ambient scheme of a compactification is Noetherian, because it is locally of
finite type over the base and quasi-compact; hence the interior is a Noetherian space and its
open immersion is quasi-compact.  That exhibits the standing data
`AlgebraicGeometry.CategoryOfCompactifications` required by [Stacks, Tag 0ATU] part (c), which is
the statement. -/
theorem preservesInterior_of_denseRange [IsNoetherian S] {j k : CompactificationOf X}
    (g : j ⟶ k) (hj : DenseRange j.immersion.base) : PreservesInterior g := by
  have : IsNoetherian j.space :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian j.toBase }
  have : NoetherianSpace X.left :=
    j.immersion.isOpenEmbedding.isInducing.noetherianSpace
  exact preimage_range_immersion_eq
    { S := S, X := X, isQuasiCompact := inferInstance, isQuasiSeparated := inferInstance,
      exists_quasiCompact_compactification := ⟨j, inferInstance⟩ } j k g hj

end AlgebraicGeometry.CompactificationOf

end
