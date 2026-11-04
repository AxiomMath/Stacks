module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits

/-!
# Inverse image on the small étale site

Let `f : X ⟶ Y` be a morphism of schemes. Base change
`Stacks.EtaleCohomology.smallEtaleBaseChange f : Y.Etale ⥤ X.Etale` is a continuous functor of
small étale sites, so the direct image `f_*` it induces on étale sheaves admits a left adjoint:
the inverse image, or pullback, `f⁻¹`. There is one such functor on sheaves of sets and one on
sheaves of abelian groups, and each is characterised by its adjunction
`Hom(f⁻¹ G, F) = Hom(G, f_* F)`, functorial in `F` on `X_étale` and `G` on `Y_étale`.

Such an adjoint is not formal, but it exists for every continuous functor of sites that
preserves the final object and fibre products, and then the direct image is computed by
`f_* F (V) = F (u V)`. For the small étale sites the construction is explicit: `f⁻¹ G` is the
sheafification of the presheaf sending an étale `X`-scheme `U` to the colimit of the sets `G(V)`
over the category of pairs `(V, φ : U ⟶ X ×_Y V)` with `V` étale over `Y`. That presheaf is the
left Kan extension of `G` along the opposite of base change, and the colimit computing its
sections over `U` is indexed by `CostructuredArrow (smallEtaleBaseChange f).op (op U)`, whose
objects are exactly those pairs.

## Main results

* `Stacks.EtaleCohomology.smallEtaleInverseImagePresheafObjIsoColimit` — the sections over `U` of
  the presheaf whose sheafification is `f⁻¹ G` are the colimit of `G(V)` over the pairs
  `(V, φ : U ⟶ X ×_Y V)`.
* `Stacks.EtaleCohomology.smallEtaleInverseImage_obj` — `f⁻¹ G` is the sheaf associated to that
  presheaf.

## References

* [Stacks Project, Tag 03Q0](https://stacks.math.columbia.edu/tag/03Q0)
* [Stacks Project, Tag 03Q2](https://stacks.math.columbia.edu/tag/03Q2)
* [Stacks Project, Tag 04I3](https://stacks.math.columbia.edu/tag/04I3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-! ### The inverse image functors and their characterising adjunctions -/

add_to_stacks 03Q0 "the inverse image `f⁻¹` on sheaves of sets"
  Stacks.EtaleCohomology.smallEtaleInverseImage

add_to_stacks 03Q0 "`f⁻¹` on sheaves of sets is characterised by its adjunction
  `Hom(f⁻¹ G, F) = Hom(G, f_* F)`"
  Stacks.EtaleCohomology.smallEtaleInverseImageAdjunction

add_to_stacks 03Q0 "the inverse image `f⁻¹` on sheaves of abelian groups"
  Stacks.EtaleCohomology.smallEtalePullbackAb

add_to_stacks 03Q0 "`f⁻¹` on sheaves of abelian groups is characterised by its adjunction
  `Hom(f⁻¹ G, F) = Hom(G, f_* F)`"
  Stacks.EtaleCohomology.smallEtaleAdjunctionAb

/-! ### The explicit formula for the inverse image -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The sections over an étale `X`-scheme `U` of the presheaf whose sheafification is `f⁻¹ G`:
the colimit of the sets `G(V)` over the category of pairs `(V, φ : U ⟶ X ×_Y V)` with `V` étale
over `Y`, which is the comma category `CostructuredArrow (smallEtaleBaseChange f).op (op U)`.
The presheaf is the left Kan extension of `G` along the opposite of base change, and a left Kan
extension along a functor between small categories is computed pointwise by this colimit. -/
@[stacks 04I3 "the displayed presheaf: its sections over `U` are the colimit of `G(V)` over the
  pairs `(V, φ : U ⟶ X ×_Y V)`"]
def smallEtaleInverseImagePresheafObjIsoColimit
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) (U : X.Etale) :
    ((smallEtaleBaseChange f).op.lan.obj G.obj).obj (op U) ≅
      colimit (CostructuredArrow.proj (smallEtaleBaseChange f).op (op U) ⋙ G.obj) :=
  Functor.leftKanExtensionObjIsoColimit _ _ _

/-- The inverse image `f⁻¹ G` of a sheaf of sets on the small étale site of `Y` is the sheaf
associated to the presheaf of `smallEtaleInverseImagePresheafObjIsoColimit`, that is, to the
left Kan extension of `G` along the opposite of base change. -/
@[stacks 04I3 "`f⁻¹ G` is the sheaf associated to the displayed presheaf"]
theorem smallEtaleInverseImage_obj
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) :
    (smallEtaleInverseImage.{u, v} f).obj G =
      (presheafToSheaf (smallEtaleTopology X) (Type (max (u + 1) v))).obj
        ((smallEtaleBaseChange f).op.lan.obj G.obj) :=
  rfl

/-! ### The construction for an arbitrary site

For sites `C₁` and `C₂` with final objects and fibre products and a functor `u : C₂ ⥤ C₁` which
is continuous and commutes with finite limits, the direct image
`f_* : Sh(C₁) ⥤ Sh(C₂)` is given by `f_* F (V) = F (u V)` and admits an exact left adjoint
`f⁻¹`. The two halves are Mathlib's formula for the sections of the direct image and the
criterion for `u` to define a morphism of sites. -/

add_to_stacks 03Q2 "for a continuous functor `u : C₂ ⥤ C₁` the direct image on sheaves is given
  by `f_* F (V) = F (u V)`"
  CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj

add_to_stacks 03Q2 "a continuous `u` carrying a final object to a final object and preserving
  fibre products has an exact left adjoint `f⁻¹` of `f_*`"
  CategoryTheory.Functor.isMorphismOfSites_of_isTerminal

end Stacks.EtaleCohomology

end
