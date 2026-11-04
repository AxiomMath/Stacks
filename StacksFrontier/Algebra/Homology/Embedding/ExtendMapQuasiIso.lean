module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap

/-!
# A functor applied to an extended morphism is a quasi-isomorphism exactly when it was one

Let `e : c.Embedding c'` be an embedding of complex shapes, let `F : C ⥤ D` be an additive functor
between abelian categories and let `f : K ⟶ L` be a morphism of complexes over `c`. Extending `f`
along `e` inserts zero maps between zero objects in the degrees outside the image of `e`, and `F`
carries zero objects to zero objects, so applying `F` degreewise to the extension of `f` is, up to
the comparison isomorphism `HomologicalComplex.mapHomologicalComplexExtendIso`, the extension of
`F` applied degreewise to `f`. Since `HomologicalComplex.quasiIso_extendMap_iff` says that
extending along `e` neither creates nor destroys a quasi-isomorphism, the two statements

`QuasiIso ((F.mapHomologicalComplex c').map (HomologicalComplex.extendMap f e))` and
`QuasiIso ((F.mapHomologicalComplex c).map f)`

are equivalent.

This is the step that transfers a quasi-isomorphism of complexes indexed by one shape to the
shape the consumer uses. Its use in this development is at `e = ComplexShape.embeddingDownNat`:
the resolutions of [Stacks, Tag 01GE] and [Stacks, Tag 0D78] are augmentations of
`ℕ`-indexed chain complexes, while the cone of the augmentation whose acyclicity the
cohomological descent of a hypercovering needs is formed in `ℤ`-indexed cochain complexes, and the
functor is applied after the extension.

## Main results

* `HomologicalComplex.quasiIso_mapHomologicalComplex_map_extendMap_iff`: the equivalence above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] (e : c.Embedding c') [e.IsRelIff]
  {K L : HomologicalComplex C c} (f : K ⟶ L)

omit [e.IsRelIff] in
/-- **An additive functor applied degreewise to the extension of a morphism along an embedding of
complex shapes is a quasi-isomorphism exactly when the functor applied degreewise to the morphism
itself is one.** Extension inserts zero objects, which the functor preserves, so the two
morphisms agree up to `HomologicalComplex.mapHomologicalComplexExtendIso`; extension then neither
creates nor destroys a quasi-isomorphism by `HomologicalComplex.quasiIso_extendMap_iff`. -/
theorem quasiIso_mapHomologicalComplex_map_extendMap_iff :
    QuasiIso ((F.mapHomologicalComplex c').map (extendMap f e)) ↔
      QuasiIso ((F.mapHomologicalComplex c).map f) :=
  (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (mapHomologicalComplexExtendIso F K e).symm
      (mapHomologicalComplexExtendIso F L e).symm
      (mapHomologicalComplexExtendIso_inv_naturality F K f e).symm)).trans
    (quasiIso_extendMap_iff _ _)

end HomologicalComplex

end
