module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# An open subspace of a representable algebraic space is an open subscheme

An open subspace of an algebraic space over `S` is a subfunctor whose inclusion is an open
immersion, which by definition means that the inclusion is representable and that every
represented base change of it is an open immersion of schemes.  If the ambient presheaf is
*itself* represented by an object of the big fppf site, then the base change along the
representing isomorphism is the inclusion itself: so the subfunctor is represented by an object
of the site, and the inclusion is the Yoneda image of an open immersion of schemes.

No hypothesis on the site beyond containing the ambient scheme is needed: representability of
the subfunctor is a consequence of `AlgebraicGeometry.Space.IsOpenImmersion`.  This is
Stacks 03KC for the open immersion property.

## Main results

* `AlgebraicGeometry.Space.exists_siteOpenImmersion_of_isOpenImmersion`: an open subspace of a
  presheaf identified with a represented one is the presheaf represented by an object of the
  site, by an open immersion of schemes into the representing scheme.
* `AlgebraicGeometry.Space.exists_factor_of_mem_subfunctor`: a morphism of the site into the
  representing object whose corresponding section lies in the subfunctor factors through that
  open immersion.
* `AlgebraicGeometry.Space.mem_range_of_mem_subfunctor`: consequently every point of its source
  is carried into the range of the open immersion.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03KC](https://stacks.math.columbia.edu/tag/03KC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) {S : Scheme.{u}} (hS : C.Contains S)
  {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (W : Subfunctor F)

/-- **An open subspace of a represented presheaf is represented by an object of the site, by an
open immersion of schemes.** -/
theorem exists_siteOpenImmersion_of_isOpenImmersion (hW : IsOpenImmersion C S hS W.ι)
    {T : BigFppfOver C S hS} (i : F ≅ yoneda.obj T) :
    ∃ (A : BigFppfOver C S hS) (j : A ⟶ T) (e : yoneda.obj A ≅ W.toFunctor),
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme C S hS).map j) ∧
        e.hom ≫ W.ι ≫ i.hom = yoneda.map j := by
  obtain ⟨A, j, fst, hpb⟩ := hW.rep i.inv
  have hiso := hpb.isIso_fst_of_isIso
  refine ⟨A, j, asIso fst, hW.property i.inv fst j hpb, ?_⟩
  change fst ≫ W.ι ≫ i.hom = yoneda.map j
  rw [← Category.assoc, hpb.w, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **A morphism of the site whose section lies in an open subspace factors through the open
immersion de-realizing it.** -/
theorem exists_factor_of_mem_subfunctor {T : BigFppfOver C S hS} (i : F ≅ yoneda.obj T)
    {A : BigFppfOver C S hS} (j : A ⟶ T) (e : yoneda.obj A ≅ W.toFunctor)
    (hj : e.hom ≫ W.ι ≫ i.hom = yoneda.map j) {Z : BigFppfOver C S hS} (f : Z ⟶ T)
    (w : W.toFunctor.obj (Opposite.op Z))
    (hw : W.ι.app (Opposite.op Z) w = yonedaEquiv (yoneda.map f ≫ i.inv)) :
    ∃ m : Z ⟶ A, m ≫ j = f := by
  obtain ⟨g, hk⟩ : ∃ g : yoneda.obj Z ⟶ W.toFunctor, g ≫ W.ι = yoneda.map f ≫ i.inv :=
    ⟨yonedaEquiv.symm w, by rw [yonedaEquiv_symm_naturality_right, hw, Equiv.symm_apply_apply]⟩
  refine ⟨yoneda.preimage (g ≫ e.inv), yoneda.map_injective ?_⟩
  rw [yoneda.map_comp, yoneda.map_preimage, Category.assoc, ← hj, Iso.inv_hom_id_assoc,
    ← Category.assoc, hk, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Every point of the source of such a morphism lies in the range of the open immersion.** -/
theorem mem_range_of_mem_subfunctor {T : BigFppfOver C S hS} (i : F ≅ yoneda.obj T)
    {A : BigFppfOver C S hS} (j : A ⟶ T) (e : yoneda.obj A ≅ W.toFunctor)
    (hj : e.hom ≫ W.ι ≫ i.hom = yoneda.map j) {Z : BigFppfOver C S hS} (f : Z ⟶ T)
    (w : W.toFunctor.obj (Opposite.op Z))
    (hw : W.ι.app (Opposite.op Z) w = yonedaEquiv (yoneda.map f ≫ i.inv))
    (z : (BigFppfOver.toScheme C S hS).obj Z) :
    ((BigFppfOver.toScheme C S hS).map f).base z ∈
      Set.range ((BigFppfOver.toScheme C S hS).map j).base := by
  obtain ⟨m, hm⟩ := exists_factor_of_mem_subfunctor C hS W i j e hj f w hw
  refine ⟨((BigFppfOver.toScheme C S hS).map m).base z, ?_⟩
  rw [← hm, Functor.map_comp]
  rfl

end AlgebraicGeometry.Space

end
