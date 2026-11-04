module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf

/-!
# Representation of a quotient sheaf, before and after lifting the universe

A quotient sheaf of a pre-relation on schemes over `S` can be formed in two ways on a site
whose objects live one universe above its morphisms. Either the quotient presheaf is
sheafified in `Type u`, the universe of the morphisms of `Over S`, which needs
`CategoryTheory.HasSheafify` for that universe; or its values are lifted to `Type (u + 1)`
first and sheafified there, where the ordinary plus construction is available. Representation
of the quotient by a scheme is then expressed in two shapes which are not the same statement:
an isomorphism of *sheaves* of `Type u` out of the sheafification of the quotient presheaf, or
an isomorphism of *presheaves* of `Type (u + 1)` out of the sheafification of the lifted quotient
presheaf. On an essentially small site the second follows from the first, because `ULift`
commutes with sheafification there.

## Main results

* `Stacks.Groupoids.exists_iso_sheafifyUlift_quotientPresheaf`: from an isomorphism of sheaves
  of `Type u` identifying the quotient sheaf of a pre-relation with the functor of points of a
  scheme `M`, compatibly with a given map `U ⟶ M`, one obtains an isomorphism out of the
  sheafification of the lifted quotient presheaf onto the lifted functor of points of `M`,
  compatible with the same map.

## References

* [Stacks Project, Tag 02VG](https://stacks.math.columbia.edu/tag/02VG)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace Stacks.Groupoids

/-- **Sheafifying the lifted quotient presheaf represents the same quotient.** Let `j` be a
pre-relation on schemes over `S`, let `f : U ⟶ M` be a map out of its object scheme, and
suppose the quotient sheaf of `j` for a topology `J` on an essentially small site is
isomorphic, as a sheaf of `Type u`, to the restricted functor of points of `M`, by an
isomorphism which carries the canonical projection to `f`. Then the sheafification of the
quotient presheaf of `j` with values lifted to `Type (u + 1)` is isomorphic to the lifted
restricted functor of points of `M`, again compatibly with `f`. -/
theorem exists_iso_sheafifyUlift_quotientPresheaf {S : Scheme.{u}} {C : Type (u + 1)}
    [Category.{u} C] [EssentiallySmall.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] [HasSheafify J (Type (u + 1))] (F : C ⥤ Over S)
    {R U M : Over S} (j : PreRelation R U) (f : U ⟶ M)
    (hM : Presheaf.IsSheaf J (points F M))
    (q : quotientSheaf (S := S) J F j ⟶ (⟨points F M, hM⟩ : Sheaf J (Type u))) (hq : IsIso q)
    (hfac : toQuotientSheaf J F j ≫ q.hom = F.op.whiskerLeft (yoneda.map f)) :
    ∃ e : sheafify J (quotientPresheaf F j ⋙ uliftFunctor.{u + 1}) ≅
        points F M ⋙ uliftFunctor.{u + 1},
      Functor.whiskerRight (toQuotientPresheaf F j) uliftFunctor.{u + 1} ≫
          toSheafify J (quotientPresheaf F j ⋙ uliftFunctor.{u + 1}) ≫ e.hom =
        Functor.whiskerRight (F.op.whiskerLeft (yoneda.map f)) uliftFunctor.{u + 1} := by
  let _ : ((equivSmallModel.{u} C).inverse.inducedTopology J).PreservesSheafification
      uliftFunctor.{u + 1, u} :=
    GrothendieckTopology.instPreservesSheafification _ _
  let _ : J.PreservesSheafification uliftFunctor.{u + 1, u} :=
    GrothendieckTopology.PreservesSheafification.transport J
      ((equivSmallModel.{u} C).inverse.inducedTopology J) (equivSmallModel.{u} C).inverse
      (Type (u + 1)) uliftFunctor.{u + 1, u}
  have hqh : IsIso q.hom := inferInstanceAs (IsIso ((sheafToPresheaf J (Type u)).map q))
  refine ⟨sheafifyComposeIso J uliftFunctor.{u + 1} (quotientPresheaf F j) ≪≫
    Functor.isoWhiskerRight (asIso q.hom) uliftFunctor.{u + 1}, ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, ← Category.assoc, Category.assoc
    (Functor.whiskerRight (toQuotientPresheaf F j) uliftFunctor.{u + 1}),
    sheafComposeIso_hom_fac]
  simp only [Functor.isoWhiskerRight_hom, asIso_hom, ← Functor.whiskerRight_comp, hfac]

end Stacks.Groupoids

end

end
