module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sober
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedLocallyClosed

/-!
# The reduced induced scheme on an irreducible locally closed subset

A locally closed subset `T` of a scheme `X` carries the reduced induced scheme structure
`Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedScheme`: a closed
subscheme of the open subscheme `coborder T`, with a canonical morphism to `X`. This file
identifies its underlying topological space with `T` and deduces that the reduced induced scheme
on an *irreducible* locally closed subset is an irreducible space whose generic point is the
generic point of `T`.

Both halves of the construction contribute to the homeomorphism. The closed immersion of the
subscheme into `coborder T` is a topological embedding with image the preimage of `T`, and the
open immersion of `coborder T` into `X` is an embedding with image `coborder T`; the composite is
therefore an embedding with image `coborder T ∩ closure T = T`.

## Main results

* `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.range_inclusion`,
  `.isEmbedding_reducedInducedInclusion` and `.reducedInducedHomeomorph`: the canonical morphism
  of the reduced induced scheme on a locally closed subset has image that subset, is a
  topological embedding, and is therefore a homeomorphism onto that subset.
* `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.irreducibleSpace_reducedInducedScheme`:
  the reduced induced scheme on an irreducible locally closed subset is irreducible.
* `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.genericPoint_mem`: the generic point of
  an irreducible locally closed subset of a scheme lies in that subset.
* `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedInclusion_genericPoint`:
  the generic point of the reduced induced scheme maps to the generic point of the subset.

## Implementation notes

`irreducibleSpace_reducedInducedScheme` cannot be an instance: it depends on the hypothesis that
`T` is irreducible, which is not a class. Accordingly
`reducedInducedInclusion_genericPoint` takes the resulting `IrreducibleSpace` as an
instance argument — it is needed for `genericPoint` to be defined at all — and a caller supplies
it with `haveI := irreducibleSpace_reducedInducedScheme T hT hirr`.

`range_inclusion` restates `AlgebraicGeometry.range_reducedInducedInclusion`, proved here
directly so that the topology of the reduced induced structure does not depend on the theory of
affine morphisms.

## References

* [Stacks Project, Tag 0F2L](https://stacks.math.columbia.edu/tag/0F2L)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace

namespace Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u

variable {X : Scheme.{u}} (T : Set X) (hT : IsLocallyClosed T)

/-- The canonical morphism of the reduced induced scheme on a locally closed subset has image
that subset. -/
theorem range_inclusion : Set.range (reducedInducedInclusion T hT) = T := by
  have hcomp : Set.range (reducedInducedInclusion T hT) =
      (reducedInducedOpen T hT).ι '' Set.range (reducedInducedIdealSheaf T hT).subschemeι := by
    rw [← Set.range_comp]
    rfl
  have hsupp : (reducedInducedIdealSheaf T hT).support = reducedInducedClosed T hT :=
    Closeds.ext_iff.mpr rfl
  have hpre : (reducedInducedClosed T hT : Set (reducedInducedOpen T hT).toScheme) =
      (reducedInducedOpen T hT).ι ⁻¹' T := rfl
  rw [hcomp, Scheme.IdealSheafData.range_subschemeι, hsupp, hpre,
    Set.image_preimage_eq_inter_range, (reducedInducedOpen T hT).range_ι]
  exact Set.inter_eq_left.mpr subset_coborder

/-- The canonical morphism of the reduced induced scheme on a locally closed subset is a
topological embedding: it is a closed immersion into the complement of the boundary followed by
the open immersion of that complement. -/
theorem isEmbedding_reducedInducedInclusion :
    IsEmbedding (reducedInducedInclusion T hT) :=
  have : IsPreimmersion (reducedInducedInclusion T hT) :=
    inferInstanceAs (IsPreimmersion
      ((reducedInducedIdealSheaf T hT).subschemeι ≫ (reducedInducedOpen T hT).ι))
  (reducedInducedInclusion T hT).isEmbedding

/-- **The underlying space of the reduced induced scheme on a locally closed subset is that
subset.** The canonical morphism is a homeomorphism onto its image. -/
noncomputable def reducedInducedHomeomorph : reducedInducedScheme T hT ≃ₜ T :=
  (isEmbedding_reducedInducedInclusion T hT).toHomeomorph.trans
    (Homeomorph.setCongr (range_inclusion T hT))

/-- The homeomorphism `reducedInducedHomeomorph` sends a point to its image under the canonical
morphism `reducedInducedInclusion`. -/
@[simp]
theorem coe_reducedInducedHomeomorph (x : reducedInducedScheme T hT) :
    (reducedInducedHomeomorph T hT x : X) = reducedInducedInclusion T hT x := rfl

/-- **The reduced induced scheme on an irreducible locally closed subset is irreducible.** -/
theorem irreducibleSpace_reducedInducedScheme (hirr : IsIrreducible T) :
    IrreducibleSpace (reducedInducedScheme T hT) :=
  have : IrreducibleSpace T := Subtype.irreducibleSpace hirr
  { toPreirreducibleSpace :=
      (reducedInducedHomeomorph T hT).isOpenEmbedding.preirreducibleSpace
    toNonempty := Nonempty.map (reducedInducedHomeomorph T hT).symm inferInstance }

include hT in
/-- The generic point of an irreducible locally closed subset of a sober space lies in the
subset. -/
theorem genericPoint_mem (hirr : IsIrreducible T) : hirr.genericPoint ∈ T := by
  by_contra hmem
  have hcl : IsClosed (closure T \ T) := by
    have h := hT.isOpen_coborder
    rwa [coborder, isOpen_compl_iff] at h
  have hsub : closure ({hirr.genericPoint} : Set X) ⊆ closure T \ T :=
    closure_minimal (Set.singleton_subset_iff.mpr
      ⟨hirr.isGenericPoint_genericPoint_closure.mem, hmem⟩) hcl
  rw [hirr.genericPoint_closure_eq] at hsub
  obtain ⟨y, hy⟩ := hirr.nonempty
  exact (hsub (subset_closure hy)).2 hy

/-- The image of a point whose singleton is dense in the reduced induced scheme on a locally
closed subset `T` is a generic point of `closure T`. -/
theorem isGenericPoint_reducedInducedInclusion {x : reducedInducedScheme T hT}
    (hx : closure ({x} : Set (reducedInducedScheme T hT)) = Set.univ) :
    IsGenericPoint (reducedInducedInclusion T hT x) (closure T) := by
  have hmemT : reducedInducedInclusion T hT x ∈ T :=
    (range_inclusion T hT).subset (Set.mem_range_self x)
  refine isGenericPoint_def.mpr (Set.Subset.antisymm ?_ ?_)
  · exact closure_mono (Set.singleton_subset_iff.mpr hmemT)
  · refine closure_minimal ?_ isClosed_closure
    calc T = reducedInducedInclusion T hT '' closure ({x} : Set (reducedInducedScheme T hT)) := by
          rw [hx, Set.image_univ, range_inclusion]
      _ ⊆ closure (reducedInducedInclusion T hT '' {x}) :=
          image_closure_subset_closure_image (reducedInducedInclusion T hT).continuous
      _ = closure {reducedInducedInclusion T hT x} := by rw [Set.image_singleton]

/-- **The generic point of the reduced induced scheme on an irreducible locally closed subset is
the generic point of that subset.** -/
theorem reducedInducedInclusion_genericPoint (hirr : IsIrreducible T)
    [IrreducibleSpace (reducedInducedScheme T hT)] :
    reducedInducedInclusion T hT (genericPoint (reducedInducedScheme T hT)) =
      hirr.genericPoint :=
  (isGenericPoint_reducedInducedInclusion T hT (genericPoint_spec _)).eq
    hirr.isGenericPoint_genericPoint_closure

end Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

end
