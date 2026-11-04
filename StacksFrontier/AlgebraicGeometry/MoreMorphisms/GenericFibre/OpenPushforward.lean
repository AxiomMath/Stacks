module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.BaseRestriction

/-!
# Pushing the shrunken base of Stacks Tag 0559 forward along an open immersion

The last move of the first proof of Stacks Tag 0559 over a domain base. Steps D, E and F run
over the spectrum of the localization `A` of the base ring `R` away from a single element, that
is over a principal open `W ⊆ Spec R`, and produce a nonempty open `V ⊆ Spec A` over which the
fibres of the restricted morphism are geometrically irreducible. This module carries that `V`
back to a nonempty open of `Spec R`.

## Relation to `AlgebraicGeometry.exists_open_geometricallyIrreducible_of_opensIsoSpec`

That theorem performs the same push-forward, but it transports the *hypotheses* of Tag 0559 to
`Spec A` as well and therefore asks for the conclusion of Tag 0559 over `Spec A` for **every**
morphism to `Spec A`. That universally quantified form cannot be supplied by the model: the
affine model is built from the generic residue field of the one morphism at hand, and over a
general base its existence is exactly what Tag 0559 is about, so instantiating it would be
circular. What the model does supply is the conclusion for the single morphism
`f ∣_ W ≫ e.hom`, and that is what this module consumes; in exchange it needs no hypothesis on
`f` at all, the two fibrewise hypotheses and the finiteness properties being irrelevant to a
push-forward.

## Main results

* `AlgebraicGeometry.Scheme.Γevaluation_residueFieldCongr_inv`: evaluation on global sections at
  a point, read at an equal point.
* `AlgebraicGeometry.exists_open_geometricallyIrreducible_of_restrictIsoSpec`: **the
  push-forward**, the statement above.

## Implementation notes

`MorphismProperty.RespectsIso @GeometricallyIrreducible` is not found by instance search even
though `MorphismProperty.IsStableUnderBaseChange @GeometricallyIrreducible` is, so it is supplied
by hand, as in `AlgebraicGeometry.geometricallyIrreducible_morphismRestrict_iff_forall`.

No Stacks tag is attached: the push-forward is not itself a tag of the source.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Steps E and F of the
  first proof
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Evaluating a global section in the residue field at a point is unchanged when the point is
presented as an equal point. -/
theorem Scheme.Γevaluation_residueFieldCongr_inv {X : Scheme.{u}} {x y : X} (h : x = y) :
    X.Γevaluation y ≫ (X.residueFieldCongr h).inv = X.Γevaluation x := by
  subst h
  simp

/-- **The push-forward of the shrunken base of Stacks Tag 0559.** Let `f : X ⟶ Spec R`, let `W`
be an open subscheme of `Spec R` presented as the spectrum of a ring `A` by an isomorphism
`e : W ≅ Spec A`, and suppose the fibres of `f ∣_ W ≫ e.hom` are geometrically irreducible over
a nonempty open `V ⊆ Spec A`. Then the fibres of `f` are geometrically irreducible over a
nonempty open subscheme of `Spec R`, namely the image of `e.hom ⁻¹' V` under the inclusion of
`W`. -/
theorem exists_open_geometricallyIrreducible_of_restrictIsoSpec {R : CommRingCat.{u}}
    {X : Scheme.{u}} (f : X ⟶ Spec R) {W : (Spec R).Opens} {A : CommRingCat.{u}}
    (e : W.toScheme ≅ Spec A) {V : (Spec A).Opens} (hVne : Nonempty V)
    (hV : GeometricallyIrreducible ((f ∣_ W ≫ e.hom) ∣_ V)) :
    ∃ V' : (Spec R).Opens, Nonempty V' ∧ GeometricallyIrreducible (f ∣_ V') := by
  have hri : MorphismProperty.RespectsIso @GeometricallyIrreducible.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  -- The fibres of `f` over the points of `W` that `e.hom` sends into `V`.
  have key : ∀ y : W.toScheme, e.hom y ∈ V →
      GeometricallyIrreducible (f.fiberToSpecResidueField (W.ι y)) := by
    intro y hy
    refine (prop_fiberToSpecResidueField_of_morphismRestrict
      (P := @GeometricallyIrreducible) f W y).mp
      ((prop_fiberToSpecResidueField_comp_iso_iff (P := @GeometricallyIrreducible)
        (f ∣_ W) e y).mp ?_)
    simpa using (geometricallyIrreducible_morphismRestrict_iff_forall _ V).mp hV ⟨e.hom y, hy⟩
  have hsur : Set.range e.hom = Set.univ := e.hom.homeomorph.surjective.range_eq
  obtain ⟨v⟩ := hVne
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : W.toScheme, e.hom y₀ = V.ι v := by
    rw [← Set.mem_range, hsur]; trivial
  refine ⟨⟨W.ι '' (e.hom ⁻¹' (V : Set (Spec A))),
    W.ι.isOpenEmbedding.isOpenMap _ (V.isOpen.preimage e.hom.continuous)⟩,
    ⟨⟨W.ι y₀, y₀, ?_, rfl⟩⟩, ?_⟩
  · rw [Set.mem_preimage, hy₀]
    exact v.2
  · rw [geometricallyIrreducible_morphismRestrict_iff_forall]
    intro w
    obtain ⟨y, hy, hyeq⟩ : ∃ y : W.toScheme, e.hom y ∈ V ∧ W.ι y = w.1 := w.2
    have hkey := key y hy
    rw [hyeq] at hkey
    exact hkey

end AlgebraicGeometry

end
