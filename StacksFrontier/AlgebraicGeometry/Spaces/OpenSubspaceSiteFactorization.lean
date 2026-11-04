module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# An open subspace of a scheme of the site is an open immersion of the site

Let `T` be a scheme of the big fppf site of `S` and `W` a subfunctor of its functor of points
whose inclusion is an open immersion of algebraic spaces. Being an open immersion is
representability by open immersions of schemes, so base-changing the inclusion along the
identity of `yoneda.obj T` presents `W` as the functor of points of a scheme `V` of the site
through a morphism `s : V ⟶ T` which is an open immersion of schemes. Consequently a morphism
`T' ⟶ T` of the site factors through `s` exactly when its functor of points factors through `W`.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenImmersion_iso_of_isOpenImmersion_ι`: the open subspace is
  the functor of points of a scheme of the site, over `T` and through an open immersion.
* `AlgebraicGeometry.Space.exists_isOpenImmersion_forall_factorsThrough_iff`: factoring through
  that open immersion in the site is factoring through the open subspace.

## Implementation notes

The conclusions are existentials: the scheme of the site is the one chosen by
`CategoryTheory.Functor.relativelyRepresentable`.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A subfunctor of a scheme of the site whose inclusion is an open immersion is a scheme of the
site.** Base-changing the inclusion along the identity presents the subfunctor as the functor of
points of a scheme `V` of the site, through a morphism `V ⟶ T` which is an open immersion of
schemes. -/
theorem exists_isOpenImmersion_iso_of_isOpenImmersion_ι {T : BigFppfOver B S hS}
    (W : Subfunctor (yoneda.obj T)) (hW : IsOpenImmersion B S hS W.ι) :
    ∃ (V : BigFppfOver B S hS) (s : V ⟶ T),
      MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
          (BigFppfOver.toScheme B S hS) s ∧
        ∃ e : yoneda.obj V ≅ W.toFunctor, e.hom ≫ W.ι = yoneda.map s := by
  have hpb := hW.rep.isPullback (𝟙 (yoneda.obj T))
  have _ : IsIso (hW.rep.fst (𝟙 (yoneda.obj T))) := hpb.isIso_fst_of_isIso
  refine ⟨hW.rep.pullback (𝟙 (yoneda.obj T)), hW.rep.snd (𝟙 (yoneda.obj T)),
    hW.property_snd (𝟙 (yoneda.obj T)), asIso (hW.rep.fst (𝟙 (yoneda.obj T))), ?_⟩
  simpa using hpb.w

/-- **An open subspace of a scheme of the site is a locus on the schemes of the site.** A morphism
`T' ⟶ T` of the site factors through the open immersion presenting the subfunctor exactly when its
functor of points factors through the subfunctor. -/
theorem exists_isOpenImmersion_forall_factorsThrough_iff {T : BigFppfOver B S hS}
    (W : Subfunctor (yoneda.obj T)) (hW : IsOpenImmersion B S hS W.ι) :
    ∃ (V : BigFppfOver B S hS) (s : V ⟶ T),
      MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
          (BigFppfOver.toScheme B S hS) s ∧
        ∀ (T' : BigFppfOver B S hS) (h : T' ⟶ T),
          (∃ t : T' ⟶ V, t ≫ s = h) ↔
            ∃ r : yoneda.obj T' ⟶ W.toFunctor, r ≫ W.ι = yoneda.map h := by
  obtain ⟨V, s, hs, e, he⟩ := exists_isOpenImmersion_iso_of_isOpenImmersion_ι B S hS W hW
  refine ⟨V, s, hs, fun T' h => ⟨?_, ?_⟩⟩
  · rintro ⟨t, rfl⟩
    exact ⟨yoneda.map t ≫ e.hom, by rw [Category.assoc, he, ← Functor.map_comp]⟩
  · rintro ⟨r, hr⟩
    refine ⟨yoneda.preimage (r ≫ e.inv), yoneda.map_injective ?_⟩
    rwa [Functor.map_comp, Functor.map_preimage, ← he, Category.assoc, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Space

end
