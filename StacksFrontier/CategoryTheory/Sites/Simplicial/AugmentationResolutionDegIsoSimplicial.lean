module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechTermMate

/-!
# The simplicial compatibility of the degreewise identification, untransposed

Let `S` be a simplicial-site situation, `a` an augmentation of `S` towards a site `(D, K)` and
`G` an abelian sheaf on `(D, K)`. The degree-`n` value of the resolving simplicial object
`barSimplicial'` of `(totalInverseImageAb S D K a).obj G` is identified with the term
`g_{n!}(a_n^{-1}G)` by `degIso'`.

This file proves `degIso_inv_comp_barSimplicial_map_comp_degIso_hom`, an equation between two
morphisms `g_{n!}(a_n^{-1}G) ⟶ g_{m!}(a_m^{-1}G)` of abelian sheaves on the total site: the
simplex map of the resolution at `φ : ⦋m⦌ ⟶ ⦋n⦌`, conjugated by the degreewise identifications,
is the lower shriek image of an explicit morphism on the component of degree `n`, followed by the
counit of `g_{n!} ⊣ g_n^{-1}`. That explicit morphism is the restriction comparison
`componentRestrictionAbInverseImageIso'`, followed by the `φ`-labelled summand
`componentSheafSummand'` and the degree-`m` identification restricted to the component of degree
`n`. Its transpose along `g_{n!} ⊣ g_n^{-1}` is `homEquiv_degIso_inv_comp_barSimplicial_map'`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.degIso_inv_comp_barSimplicial_map_comp_degIso_hom`: the untransposed simplicial
  compatibility of `degIso'`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.map_degIso_inv_comp_barSimplicial_map_comp_degIso_hom`: its image under an arbitrary functor
  out of the abelian sheaves on the total site.

## References

* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WM](https://stacks.math.columbia.edu/tag/09WM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe v w u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K) (G : Sheaf K Ab.{u}) [HasSheafify K Ab.{u}]

omit [HasSheafify K Ab.{u}] in
/-- **The untransposed simplicial compatibility of the degreewise identification of the
resolution.** The simplex map of the resolution at `φ : ⦋m⦌ ⟶ ⦋n⦌`, conjugated by the degreewise
identifications of its terms, is the lower shriek image of the restriction comparison
`componentRestrictionAbInverseImageIso'`, followed by the `φ`-labelled summand
`componentSheafSummand'` and the degree-`m` identification, and then the counit of
`g_{n!} ⊣ g_n^{-1}`. -/
theorem degIso_inv_comp_barSimplicial_map_comp_degIso_hom {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    (degIso' S D K a G n).inv ≫
        ((barSimplicial' S).obj ((totalInverseImageAb S D K a).obj G)).map φ.op ≫
          (degIso' S D K a G m).hom =
      (componentLowerShriekAb S ⦋n⦌).map
          ((componentRestrictionAbInverseImageIso' S D K a G ⦋n⦌).inv ≫
            componentSheafSummand' S ((totalInverseImageAb S D K a).obj G) φ ≫
              (S.restrictAb ⦋n⦌).map (degIso' S D K a G m).hom) ≫
        (S.componentLowerShriekAbAdjunction' ⦋n⦌).counit.app (resolutionTerm S D K a G m) := by
  refine Eq.trans (((S.componentLowerShriekAbAdjunction' ⦋n⦌).homEquiv
    ((componentInverseImageAb S D K a ⦋n⦌).obj G)
    (resolutionTerm S D K a G m)).eq_symm_apply.mpr
      (homEquiv_degIso_inv_comp_barSimplicial_map' S D K a G φ)) ?_
  exact (S.componentLowerShriekAbAdjunction' ⦋n⦌).homEquiv_counit _ _ _

omit [HasSheafify K Ab.{u}] in
/-- **The untransposed simplicial compatibility, pushed forward along a functor.** The image under
`Φ` of the simplex map of the resolution at `φ : ⦋m⦌ ⟶ ⦋n⦌`, conjugated by the degreewise
identifications, is the image of the explicit morphism of
`degIso_inv_comp_barSimplicial_map_comp_degIso_hom`. -/
theorem map_degIso_inv_comp_barSimplicial_map_comp_degIso_hom
    {A : Type w} [Category.{v, w} A] (Φ : Sheaf S.totalTopology Ab.{u} ⥤ A) {m n : ℕ}
    (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    Φ.map (degIso' S D K a G n).inv ≫
        Φ.map (((barSimplicial' S).obj ((totalInverseImageAb S D K a).obj G)).map φ.op) ≫
          Φ.map (degIso' S D K a G m).hom =
      Φ.map ((componentLowerShriekAb S ⦋n⦌).map
            ((componentRestrictionAbInverseImageIso' S D K a G ⦋n⦌).inv ≫
              componentSheafSummand' S ((totalInverseImageAb S D K a).obj G) φ ≫
                (S.restrictAb ⦋n⦌).map (degIso' S D K a G m).hom)) ≫
        Φ.map ((S.componentLowerShriekAbAdjunction' ⦋n⦌).counit.app
          (resolutionTerm S D K a G m)) := by
  refine Eq.trans (congrArg (fun g => Φ.map (degIso' S D K a G n).inv ≫ g)
    (Φ.map_comp (((barSimplicial' S).obj ((totalInverseImageAb S D K a).obj G)).map φ.op)
      (degIso' S D K a G m).hom).symm) ?_
  refine Eq.trans (Φ.map_comp _ _).symm ?_
  refine Eq.trans (congrArg Φ.map
    (degIso_inv_comp_barSimplicial_map_comp_degIso_hom S D K a G φ)) ?_
  exact Φ.map_comp _ _

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
