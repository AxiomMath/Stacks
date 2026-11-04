module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.DiagonalUniqueness

/-!
# Composition of compactly supported direct images

Let `Rg_! : 𝒞 ⥤ Pro-𝒟` be a functor whose values are pro-objects with countable index, and let
`M = (M_n)` be an inverse sequence in `𝒞`, as produced by a first compactly supported direct
image `Rf_!`. Applying `Rg_!` termwise gives an inverse system in `Pro-𝒟`, and there is an inverse
sequence `N = (N_k)` in `𝒟`, unique up to pro-isomorphism, with
`Hom(N, L) = colim_n Hom(Rg_! M_n, L)` naturally in `L`. This is the composition `Rg_! ∘ Rf_!`.

## Main definitions

* `CategoryTheory.Pro.CompositionRepresentation` packages such an inverse sequence `N` together
  with the natural identification of its functor of points.

## Main results

* `CategoryTheory.Pro.exists_compositionRepresentation` constructs the composition.
* `CategoryTheory.Pro.CompositionRepresentation.homColimitIso` is the displayed colimit formula.
* `CategoryTheory.Pro.compositionRepresentation_uniqueUpToIso` gives uniqueness up to
  pro-isomorphism.

## Implementation notes

A pro-object is used through its functor of points `N ↦ colim_k Hom(N_k, N)`, which is
`CategoryTheory.Pro.coyonedaColim`; this embedding is contravariant, so a functor with values in
pro-objects of `𝒟` appears as a functor `𝒞ᵒᵖ ⥤ 𝒟 ⥤ Type v`, and the inverse system `(M_n)`
becomes the direct system `M.rightOp ⋙ G` of such functors. The comparison is an isomorphism of
functors, hence natural in the test object `L`. Functoriality in the first argument is not
asserted: the source defers it to Tag 0G55.

## References

* [Stacks Project, Tag 0G54](https://stacks.math.columbia.edu/tag/0G54)
* [Stacks Project, Tag 0G53](https://stacks.math.columbia.edu/tag/0G53)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v v' u u'

namespace CategoryTheory.Pro

/-- An inverse sequence in `𝒟` representing the termwise image of an inverse sequence `M` in `𝒞`
under a functor `G` with values in pro-objects of `𝒟`. The comparison isomorphism says that maps
out of `system` are the colimit over `n` of the maps out of `G (M n)`, naturally in the target. -/
public structure CompositionRepresentation {C : Type u'} [Category.{v'} C] {D : Type u}
    [Category.{v} D] (G : Cᵒᵖ ⥤ D ⥤ Type v) (M : ℕᵒᵖ ⥤ C) where
  /-- The resulting inverse sequence in `𝒟`. -/
  system : ℕᵒᵖ ⥤ D
  /-- Naturally in the target, maps out of `system` are the colimit of the maps out of
  `G (M n)`. -/
  comparison : colimit (M.rightOp ⋙ G) ≅ Pro.coyonedaColim (liftedInverseSequence system)

/-- The composition of two compactly supported direct images: the termwise image under `G` of an
inverse sequence `M` is represented by an inverse sequence in the target category. -/
@[stacks 0G54 "the composition, for pro-object-valued functors with countable-index \
  representations supplied as data"]
public theorem exists_compositionRepresentation {C : Type u'} [Category.{v'} C] {D : Type u}
    [Category.{v} D] (G : Cᵒᵖ ⥤ D ⥤ Type v) (S : C → ℕᵒᵖ ⥤ D)
    (e : ∀ L : C, G.obj (op L) ≅ Pro.coyonedaColim (liftedInverseSequence (S L)))
    (M : ℕᵒᵖ ⥤ C) : Nonempty (CompositionRepresentation G M) := by
  obtain ⟨r⟩ := exists_diagonalRepresentation (M.rightOp ⋙ G)
    (fun n => S (M.obj (op n))) (fun n => e (M.obj (op n)))
  exact ⟨⟨r.system, r.comparison⟩⟩

/-- **Stacks Project, Tag 0G54**, the displayed formula: for every object `L`, the colimit over
`n` of `Hom(G (M n), L)` is the colimit over `k` of `Hom(system_k, L)`. -/
@[stacks 0G54 "the Hom-colimit formula, for pro-object-valued functors with \
  countable-index representations supplied as data"]
public noncomputable def CompositionRepresentation.homColimitIso {C : Type u'} [Category.{v'} C]
    {D : Type u} [Category.{v} D] {G : Cᵒᵖ ⥤ D ⥤ Type v} {M : ℕᵒᵖ ⥤ C}
    (r : CompositionRepresentation G M) (L : D) :
    colimit ((M.rightOp ⋙ G) ⋙ (evaluation D (Type v)).obj L) ≅
      colimit ((liftedInverseSequence r.system).op ⋙ coyoneda ⋙
        (evaluation D (Type v)).obj L) :=
  (colimitObjIsoColimitCompEvaluation (M.rightOp ⋙ G) L).symm ≪≫ r.comparison.app L ≪≫
    coyonedaColimObjIso (liftedInverseSequence r.system) L

/-- **Stacks Project, Tag 0G54**, uniqueness: two inverse sequences representing the termwise
image of `M` under `G` are uniquely pro-isomorphic over their comparison isomorphisms. The
pro-morphism and its inverse are expressed through Stacks 0G2X. -/
@[stacks 0G54 "uniqueness up to pro-isomorphism, for pro-object-valued functors with \
  countable-index representations supplied as data"]
public theorem compositionRepresentation_uniqueUpToIso {C : Type u'} [Category.{v'} C]
    {D : Type u} [Category.{v} D] (G : Cᵒᵖ ⥤ D ⥤ Type v) (M : ℕᵒᵖ ⥤ C)
    (r r' : CompositionRepresentation G M) :
    ∃! φ : Pro.Hom (liftedInverseSequence r.system) (liftedInverseSequence r'.system),
      (∃ ψ : Pro.Hom (liftedInverseSequence r'.system) (liftedInverseSequence r.system),
        (Pro.homEquiv (liftedInverseSequence r'.system)
              (liftedInverseSequence r.system)).symm ψ ≫
            (Pro.homEquiv (liftedInverseSequence r.system)
              (liftedInverseSequence r'.system)).symm φ =
          𝟙 (Pro.coyonedaColim (liftedInverseSequence r.system)) ∧
        (Pro.homEquiv (liftedInverseSequence r.system)
              (liftedInverseSequence r'.system)).symm φ ≫
            (Pro.homEquiv (liftedInverseSequence r'.system)
              (liftedInverseSequence r.system)).symm ψ =
          𝟙 (Pro.coyonedaColim (liftedInverseSequence r'.system))) ∧
      r'.comparison.hom ≫ (Pro.homEquiv (liftedInverseSequence r.system)
          (liftedInverseSequence r'.system)).symm φ = r.comparison.hom := by
  refine ⟨Pro.homEquiv _ _ (r'.comparison.inv ≫ r.comparison.hom), ?_, ?_⟩
  · refine ⟨⟨Pro.homEquiv _ _ (r.comparison.inv ≫ r'.comparison.hom), ?_, ?_⟩, ?_⟩ <;>
      simp [Category.assoc]
  · rintro φ' ⟨_, h⟩; apply (Pro.homEquiv _ _).symm.injective
    simpa [Category.assoc] using congrArg (r'.comparison.inv ≫ ·) h

end CategoryTheory.Pro
