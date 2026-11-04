module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproductSpace

/-!
# A representable coproduct of sheaves is a clopen decomposition of its representing object

Let `F i` be a family of sheaves of sets on the big fppf site of a scheme `S`, indexed by an
arbitrary type, and let `G` be a sheaf coproduct of the family. If `G` is isomorphic to the
sheaf of points of an object `U` of the site, then each summand `F i` is itself isomorphic to
the sheaf of points of an object `U i` of the site, and the induced morphisms `U i ⟶ U` are
simultaneously open and closed immersions of schemes.

This is the first half of the conclusion of **Stacks 02WO**. The second half, that the `U i`
exhibit `U` as a *coproduct of schemes*, is not stated here. The statement is read off
**Stacks 0F15** in the form `AlgebraicGeometry.coproductIncl_pullback_rep`, and no smallness
hypothesis is imposed on the index type.

## Main results

* `AlgebraicGeometry.exists_clopen_decomposition_of_representable_coproduct`: the clopen
  decomposition of the representing object of a coproduct of sheaves.

## References

* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
* [Stacks Project, Tag 0F15](https://stacks.math.columbia.edu/tag/0F15)
* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- **The clopen decomposition half of Stacks 02WO.** Let `G` be a coproduct of a family of
sheaves `F i` on the big fppf site of `S`, indexed by an arbitrary type, and suppose `G` is
isomorphic to the sheaf of points of an object `U` of the site. Then each summand is
isomorphic to the sheaf of points of an object `Uᵢ i` of the site, whose morphism to `U` is
both an open and a closed immersion of schemes, compatibly with the coproduct inclusions. -/
theorem exists_clopen_decomposition_of_representable_coproduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, Fi i ⟶ G)
    (hc : IsColimit (Cofan.mk G ι))
    (U : BigFppfOver B S hS) (e : G.obj ≅ yoneda.obj U) :
    ∃ (Uᵢ : I → BigFppfOver B S hS) (j : ∀ i, Uᵢ i ⟶ U)
      (eᵢ : ∀ i, (Fi i).obj ≅ yoneda.obj (Uᵢ i)),
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i))) ∧
        (∀ i, IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (j i))) ∧
        ∀ i, (eᵢ i).hom ≫ yoneda.map (j i) = (ι i).hom ≫ e.hom := by
  choose Uᵢ j f hpb hopen hclosed using fun i =>
    coproductIncl_pullback_rep B S hS ι hc i (A := U) e.inv
  have hiso : ∀ i, IsIso (f i) := fun i => (hpb i).isIso_fst_of_isIso
  refine ⟨Uᵢ, j, fun i => (asIso (f i)).symm, hopen, hclosed, fun i => ?_⟩
  have hw : f i ≫ (ι i).hom ≫ e.hom = yoneda.map (j i) := by
    rw [← Category.assoc, (hpb i).w, Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [← hw, Iso.symm_hom, asIso_inv, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

end AlgebraicGeometry

end
