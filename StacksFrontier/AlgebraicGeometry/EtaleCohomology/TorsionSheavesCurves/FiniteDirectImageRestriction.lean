module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteDirectImageEdge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.RestrictionComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition

/-!
# Restriction maps across a finite direct image

Consider a commutative square of schemes
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
and an abelian sheaf `G` on `X_étale`. Restriction along `g` of a class on `Y` with coefficients
in `f_* G`, followed by the base change comparison `g⁻¹ f_* G ⟶ f'_* g'⁻¹ G` and the edge map of
`f'`, is the edge map of `f` followed by restriction along `g'`. This is the compatibility of the
identification `H^q(X, G) = H^q(Y, f_* G)` of Tag 0A5D with base change.

When `f` and `f'` are integral, so that both edge maps are bijective, and the base change
comparison is an isomorphism at `G` (Tag 0959 for `f` finite and the square cartesian),
restriction along `g` is bijective (resp. surjective) for `f_* G` exactly when restriction along
`g'` is for `G`.

## Main results

* `Stacks.EtaleCohomology.edgeMap_restriction`: the compatibility.
* `Stacks.EtaleCohomology.bijective_restriction_directImage_iff`,
  `Stacks.EtaleCohomology.surjective_restriction_directImage_iff`: the transfer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (hyp : g' ≫ f = f' ≫ g)
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})]

omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- The sheaf-level identity behind `edgeMap_restriction`: the base change comparison followed by
the counit of `f'` is the counit of `f` pulled back along `g'`, up to the identifications of the
inverse images along the diagonal of the square. -/
theorem baseChange_comp_counit (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleAbelianInverseImageCompIso'.{u, u + 1} f' g (g' ≫ f) hyp).hom.app
          ((etaleAbelianDirectImage.{u, u + 1} f).obj G) ≫
        (etaleAbelianInverseImage.{u, u + 1} f').map
          ((etaleAbelianBaseChange.{u, u + 1} f g g' f' hyp).app G) ≫
        (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f').counit.app
          ((etaleAbelianInverseImage.{u, u + 1} g').obj G) =
      (etaleAbelianInverseImageCompIso'.{u, u + 1} g' f (g' ≫ f) rfl).hom.app
          ((etaleAbelianDirectImage.{u, u + 1} f).obj G) ≫
        (etaleAbelianInverseImage.{u, u + 1} g').map
          ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f).counit.app G) := by
  have hm := mateEquiv_counit (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f)
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f')
    (TwoSquare.mk _ _ _ _
      ((etaleAbelianInverseImageCompIso'.{u, u + 1} f' g (g' ≫ f) hyp).inv ≫
        (etaleAbelianInverseImageCompIso'.{u, u + 1} g' f (g' ≫ f) rfl).hom)) G
  rw [← etaleAbelianBaseChange_eq_mateEquiv.{u, u + 1} f g g' f' hyp (g' ≫ f) rfl hyp] at hm
  rw [hm]
  simp

/-- **Restriction commutes with the edge map**, across the base change comparison. -/
theorem edgeMap_restriction (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, u + 1} f).obj G) q) :
    edgeMap f' ((etaleAbelianInverseImage.{u, u + 1} g').obj G) q
        ((etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g
          ((etaleAbelianDirectImage.{u, u + 1} f).obj G) q x).comp
          (Ext.mk₀ ((etaleAbelianBaseChange.{u, u + 1} f g g' f' hyp).app G)) (add_zero q)) =
      etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g' G q (edgeMap f G q x) := by
  rw [edgeMap_apply, edgeMap_apply, etaleCohomologyRestrictionMap_comp_mk₀.{u, u + 1, u + 1},
    etaleCohomologyRestrictionMap_comp_mk₀.{u, u + 1, u + 1},
    etaleCohomologyRestrictionMap_comp_eq_comp_mk₀.{u, u + 1, u + 1} g f' (g' ≫ f) hyp,
    etaleCohomologyRestrictionMap_comp_eq_comp_mk₀.{u, u + 1, u + 1} f g' (g' ≫ f) rfl]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc]
  rw [baseChange_comp_counit f g g' f' hyp G]

/-- Restriction along `g` for `f_* G` and along `g'` for `G` are conjugate by bijections, when the
edge maps are bijective and the base change comparison is an isomorphism at `G`. -/
theorem restriction_directImage_conj [IsIntegralHom f] [IsIntegralHom f']
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [IsIso ((etaleAbelianBaseChange.{u, u + 1} f g g' f' hyp).app G)] (q : ℕ) :
    ∃ (e₁ : Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, u + 1} f).obj G) q →
        Sheaf.H.{u + 1} G q)
      (e₂ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, u + 1} g).obj
        ((etaleAbelianDirectImage.{u, u + 1} f).obj G)) q →
        Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, u + 1} g').obj G) q),
      Function.Bijective e₁ ∧ Function.Bijective e₂ ∧
        e₂ ∘ etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g
            ((etaleAbelianDirectImage.{u, u + 1} f).obj G) q =
          etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g' G q ∘ e₁ := by
  refine ⟨edgeMap f G q, (edgeMap f' ((etaleAbelianInverseImage.{u, u + 1} g').obj G) q) ∘
    (fun y => y.comp (Ext.mk₀ ((etaleAbelianBaseChange.{u, u + 1} f g g' f' hyp).app G))
      (add_zero q)), bijective_edgeMap f q G, ?_, ?_⟩
  · exact (bijective_edgeMap f' q _).comp (bijective_comp_mk₀_of_isIso _ q)
  · funext x
    exact edgeMap_restriction f g g' f' hyp G q x

/-- **Bijectivity of restriction transfers across a finite direct image.** -/
theorem bijective_restriction_directImage_iff [IsIntegralHom f] [IsIntegralHom f']
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [IsIso ((etaleAbelianBaseChange.{u, u + 1} f g g' f' hyp).app G)] (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g
        ((etaleAbelianDirectImage.{u, u + 1} f).obj G) q) ↔
      Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g' G q) := by
  obtain ⟨e₁, e₂, h₁, h₂, hc⟩ := restriction_directImage_conj f g g' f' hyp G q
  rw [← Function.Bijective.of_comp_iff' h₂, hc, Function.Bijective.of_comp_iff _ h₁]

/-- **Surjectivity of restriction transfers across a finite direct image.** -/
theorem surjective_restriction_directImage_iff [IsIntegralHom f] [IsIntegralHom f']
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [IsIso ((etaleAbelianBaseChange.{u, u + 1} f g g' f' hyp).app G)] (q : ℕ) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g
        ((etaleAbelianDirectImage.{u, u + 1} f).obj G) q) ↔
      Function.Surjective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g' G q) := by
  obtain ⟨e₁, e₂, h₁, h₂, hc⟩ := restriction_directImage_conj f g g' f' hyp G q
  rw [← Function.Surjective.of_comp_iff' h₂, hc, Function.Surjective.of_comp_iff _ h₁.2]

end Stacks.EtaleCohomology

end
