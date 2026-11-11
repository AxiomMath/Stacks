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

* `Stacks.EtaleCohomology.inverseImageIsoSheafifyColimitPresheaf` — for any left adjoint `f⁻¹`
  of `f_*`, `f⁻¹ G` is the sheaf associated to the presheaf
  `U ↦ colim_{(V, φ : U ⟶ X ×_Y V)} G(V)` (Stacks 04I3).
* `Stacks.EtaleCohomology.smallEtaleInverseImagePresheafObjIsoColimit` — the sections over `U` of
  the left Kan extension of `G` along the opposite of base change are that colimit.

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

/-- The sections over an étale `X`-scheme `U` of the left Kan extension of `G` along the opposite
of base change, `(smallEtaleBaseChange f).op.lan.obj G.obj`, are the colimit of the sets `G(V)`
over the category of pairs `(V, φ : U ⟶ X ×_Y V)` with `V` étale over `Y`, which is the comma
category `CostructuredArrow (smallEtaleBaseChange f).op (op U)`: a left Kan extension along a
functor between small categories is computed pointwise by this colimit. This is only the
presheaf-level half of Stacks 04I3; the statement about `f⁻¹` is
`Stacks.EtaleCohomology.inverseImageIsoSheafifyColimitPresheaf`. -/
def smallEtaleInverseImagePresheafObjIsoColimit
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) (U : X.Etale) :
    ((smallEtaleBaseChange f).op.lan.obj G.obj).obj (op U) ≅
      colimit (CostructuredArrow.proj (smallEtaleBaseChange f).op (op U) ⋙ G.obj) :=
  Functor.leftKanExtensionObjIsoColimit _ _ _

/-- The library's inverse image `smallEtaleInverseImage f` is, by construction, the
sheafification of the left Kan extension of `G` along the opposite of base change. This is a
definitional unfolding; the statement of Stacks 04I3, for any left adjoint of `f_*`, is
`Stacks.EtaleCohomology.inverseImageIsoSheafifyColimitPresheaf`. -/
theorem smallEtaleInverseImage_obj
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) :
    (smallEtaleInverseImage.{u, v} f).obj G =
      (presheafToSheaf (smallEtaleTopology X) (Type (max (u + 1) v))).obj
        ((smallEtaleBaseChange f).op.lan.obj G.obj) :=
  rfl

/-- The presheaf on `X_étale` of Stacks 04I3: its sections over an étale `X`-scheme `U` are, by
definition, the colimit `colim G(V)` over the category of pairs `(V, φ : U ⟶ X ×_Y V)` with `V`
étale over `Y` (the comma category `CostructuredArrow (smallEtaleBaseChange f).op (op U)`), and
its restriction maps are induced by composing `φ`. It is Mathlib's pointwise left Kan extension
of `G` along the opposite of base change. -/
abbrev smallEtaleColimitPresheaf (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) :
    X.Etaleᵒᵖ ⥤ Type (max (u + 1) v) :=
  (smallEtaleBaseChange f).op.pointwiseLeftKanExtension G.obj

/-- The sections of `smallEtaleColimitPresheaf f G` over `U` are the colimit of `G(V)` over the
pairs `(V, φ : U ⟶ X ×_Y V)`. -/
theorem smallEtaleColimitPresheaf_obj
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) (U : X.Etale) :
    (smallEtaleColimitPresheaf.{u, v} f G).obj (op U) =
      colimit (CostructuredArrow.proj (smallEtaleBaseChange f).op (op U) ⋙ G.obj) :=
  rfl

/-- **Stacks 04I3.** Let `f : X ⟶ Y` be a morphism of schemes and let `f⁻¹` be any left adjoint
of the direct image `f_*` on sheaves of sets of the small étale sites (Stacks 03Q0). Then for
every sheaf `G` on `Y_étale`, `f⁻¹ G` is the sheaf associated to the presheaf
`U ↦ colim_{(V, φ : U ⟶ X ×_Y V)} G(V)`, namely `smallEtaleColimitPresheaf f G`. The isomorphism
is natural, being the composite of the uniqueness of left adjoints with the uniqueness of left
Kan extensions. -/
@[stacks 04I3 "for any left adjoint `f⁻¹` of `f_*` on sheaves of sets of the small étale sites,
  `f⁻¹ G` is the sheafification of `U ↦ colim G(V)` over the pairs `(V, U ⟶ X ×_Y V)`"]
def inverseImageIsoSheafifyColimitPresheaf
    {L : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v)) ⥤
      Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))}
    (adj : L ⊣ (smallEtaleBaseChange f).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (smallEtaleTopology Y) (smallEtaleTopology X))
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) :
    L.obj G ≅
      (presheafToSheaf (smallEtaleTopology X) (Type (max (u + 1) v))).obj
        (smallEtaleColimitPresheaf.{u, v} f G) :=
  (adj.leftAdjointUniq (smallEtaleInverseImageAdjunction.{u, v} f)).app G ≪≫
    (presheafToSheaf (smallEtaleTopology X) (Type (max (u + 1) v))).mapIso
      (Functor.leftKanExtensionUnique _ ((smallEtaleBaseChange f).op.lanUnit.app G.obj) _
        ((smallEtaleBaseChange f).op.pointwiseLeftKanExtensionUnit G.obj))

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
