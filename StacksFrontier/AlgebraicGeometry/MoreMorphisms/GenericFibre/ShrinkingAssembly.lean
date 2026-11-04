module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.DenseFibreShrinking
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FibreOfOpenRestriction

/-!
# Assembling the shrinking step of Stacks Tag 0559

Steps E and F of the first proof of Stacks Tag 0559 are joined here. The situation produced by
the earlier steps is: a finite type morphism `f : X ⟶ Y` onto an irreducible base, a finite type
morphism `f' : X' ⟶ Y` which is already known to be geometrically irreducible — the standard
hypersurface model of step F — and opens `U ⊆ X`, `U' ⊆ X'` which are `Y`-isomorphic and dense in
the fibres over the generic point.

Geometric irreducibility then travels from `X'` to `X` over every point of a nonempty open of
`Y`: it restricts from `X'_y` to the dense open `U'_y`, crosses the isomorphism to `U_y`, and
extends from the dense open `U_y` to `X_y`. The two shrinkings — one making `U_y` dense in `X_y`,
one making `U'_y` dense in `X'_y` — are intersected, which is nonempty because `Y` is irreducible.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_fiber_iso_iff`: geometric irreducibility of a fibre
  is invariant under an isomorphism of the source over the base.
* `AlgebraicGeometry.geometricallyIrreducible_morphismRestrict_of_forall`: a morphism restricted
  over an open of the base is geometrically irreducible as soon as its fibres over the points of
  that open are.
* `AlgebraicGeometry.exists_open_geometricallyIrreducible_of_denseOpenIso`: steps E and F of
  Stacks Tag 0559 assembled.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An isomorphism of the sources of two morphisms with the same target identifies their fibres
over any point of the target, hence transports geometric irreducibility of a fibre. -/
public theorem geometricallyIrreducible_fiber_iso_iff {U U' Y : Scheme.{u}} {g : U ⟶ Y}
    {g' : U' ⟶ Y} (e : U ≅ U') (he : e.hom ≫ g' = g) (y : Y) :
    GeometricallyIrreducible (g.fiberToSpecResidueField y) ↔
      GeometricallyIrreducible (g'.fiberToSpecResidueField y) := by
  subst he
  have hiso : IsPullback e.inv g' (e.hom ≫ g') (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have hsq : IsPullback (g'.fiberι y ≫ e.inv) (g'.fiberToSpecResidueField y) (e.hom ≫ g')
      (Y.fromSpecResidueField y) := by
    simpa using (isPullback_fiberι_fiberToSpecResidueField g' y).paste_horiz hiso
  have : MorphismProperty.RespectsIso @GeometricallyIrreducible.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have key := MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIrreducible)
    hsq.isoPullback.hom (pullback.snd (e.hom ≫ g') (Y.fromSpecResidueField y))
  rw [hsq.isoPullback_hom_snd] at key
  exact key.symm

/-- A morphism restricted over an open subscheme of its target is geometrically irreducible as
soon as all its fibres over points of that open are. -/
public theorem geometricallyIrreducible_morphismRestrict_of_forall {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens)
    (h : ∀ v : V, GeometricallyIrreducible (f.fiberToSpecResidueField (V.ι v))) :
    GeometricallyIrreducible (f ∣_ V) :=
  (GeometricallyIrreducible.iff_geometricallyIrreducible_fiber _).mpr fun v ↦
    MorphismProperty.of_isPullback
      (isPullback_fiberToSpecResidueField_of_isPullback
        (isPullback_morphismRestrict f V).flip v) (h v)

/-- **Steps E and F of Stacks Tag 0559.** Let `f : X ⟶ Y` and `f' : X' ⟶ Y` be finite type
morphisms onto an irreducible base with generic point `η`, with `f'` geometrically irreducible.
Let `U ⊆ X` and `U' ⊆ X'` be opens which are isomorphic over `Y` and whose traces on the fibres
over `η` are dense. Then `f` has geometrically irreducible fibres over a nonempty open subscheme
of `Y`. -/
public theorem exists_open_geometricallyIrreducible_of_denseOpenIso {X X' Y : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y) [IrreducibleSpace Y] [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType f'] [QuasiCompact f'] [GeometricallyIrreducible f']
    (U : X.Opens) (U' : X'.Opens) (e : U.toScheme ≅ U'.toScheme)
    (he : e.hom ≫ (U'.ι ≫ f') = U.ι ≫ f) (η : Y) (hη : IsGenericPoint η Set.univ)
    (hU : Dense ((f.fiberι η ⁻¹ᵁ U : (f.fiber η).Opens) : Set ↥(f.fiber η)))
    (hU' : Dense ((f'.fiberι η ⁻¹ᵁ U' : (f'.fiber η).Opens) : Set ↥(f'.fiber η))) :
    ∃ V : Y.Opens, Nonempty V ∧ GeometricallyIrreducible (f ∣_ V) := by
  obtain ⟨V₁, hV₁o, hV₁ne, hV₁⟩ := exists_open_dense_fiber_preimage f U η hη hU
  obtain ⟨V₂, hV₂o, hV₂ne, hV₂⟩ := exists_open_dense_fiber_preimage f' U' η hη hU'
  have hinter : (V₁ ∩ V₂).Nonempty := by
    have := (IrreducibleSpace.isIrreducible_univ Y).2 V₁ V₂ hV₁o hV₂o
      (by simpa using hV₁ne) (by simpa using hV₂ne)
    simpa using this
  refine ⟨⟨V₁, hV₁o⟩ ⊓ ⟨V₂, hV₂o⟩, Set.nonempty_coe_sort.mpr hinter, ?_⟩
  refine geometricallyIrreducible_morphismRestrict_of_forall f _ fun v ↦ ?_
  obtain ⟨hv₁, hv₂⟩ : (v : Y) ∈ V₁ ∧ (v : Y) ∈ V₂ := v.2
  rw [Scheme.Opens.ι_apply]
  refine geometricallyIrreducible_fiberToSpecResidueField_of_dense_opens_comp f _ U
    (hV₁ _ hv₁) ?_
  rw [geometricallyIrreducible_fiber_iso_iff e he, ← geometricallyIrreducible_opens_fiber_iff,
    geometricallyIrreducible_dense_open_comp_iff _ _ (hV₂ _ hv₂)]
  infer_instance

end AlgebraicGeometry

end
