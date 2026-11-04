module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DirectImageCohomology
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionBaseChange

/-!
# Restriction maps on the cohomology of a direct image along an integral morphism

Consider a commutative square of schemes

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

with `f` and `f'` integral, and an abelian sheaf `F` on `X_étale` for which the base change
comparison `g^{-1} f_* F ⟶ f'_* (g')^{-1} F` is an isomorphism (Tag 0959 when `f` is finite and
the square cartesian). Then restriction along `g` on the cohomology of `f_* F` is bijective
(resp. surjective) in a degree exactly when restriction along `g'` on the cohomology of `F` is.
This is the step of Lemma 0A5D that moves statements (6), (7) and (8) of Situation 0A52 from `F`
to `f_* F`.

## Main results

* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_directImage_iff`
* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_directImage_iff`

## Implementation notes

Both restriction maps are maps on `Ext` out of a constant sheaf induced by an exact inverse-image
functor, and the cohomology of a direct image is identified with that of the sheaf by the
adjunction map of `Stacks.ExtAdjunction.extMap`. The base change comparison is by construction
the mate of the comparison of the two composite inverse images, which is exactly the compatibility
`Stacks.ExtAdjunction.extMap_mapExactFunctor_comp_mk₀` asks for.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

section

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- Restriction along `g` is the map on `Ext` induced by the inverse image, followed by the
constant-sheaf comparison; so it is bijective exactly when the map on `Ext` is. -/
theorem bijective_etaleCohomologyRestrictionMap_iff_mapExtAddHom
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} g G q) ↔
      Function.Bijective ((etaleAbelianInverseImage.{u, v} g).mapExtAddHom
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
          (AddCommGrpCat.of (ULift ℤ))) G q) :=
  Function.Bijective.of_comp_iff' (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ q) _

/-- The surjective form of `bijective_etaleCohomologyRestrictionMap_iff_mapExtAddHom`. -/
theorem surjective_etaleCohomologyRestrictionMap_iff_mapExtAddHom
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} g G q) ↔
      Function.Surjective ((etaleAbelianInverseImage.{u, v} g).mapExtAddHom
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
          (AddCommGrpCat.of (ULift ℤ))) G q) :=
  Function.Surjective.of_comp_iff' (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ q) _

end

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] in
/-- The base change comparison is, by definition, the base change morphism
`Stacks.CategoryTheory.BaseChange.twoSquare` of the square of inverse-image/direct-image
adjunctions. -/
theorem etaleAbelianBaseChange_eq_twoSquare :
    etaleAbelianBaseChange.{u, v} f g g' f' h =
      Stacks.CategoryTheory.BaseChange.twoSquare
        (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
        (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
        (etaleAbelianInverseImageCompIso.{u, v} f' g).symm
        ((etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
          eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k) h)) := by
  rw [etaleAbelianBaseChange]

variable [IsIntegralHom f] [IsIntegralHom f']

include h in
/-- **Restriction on the cohomology of a direct image, bijectivity.** For a commutative square
with `f`, `f'` integral and an abelian sheaf `F` whose base change comparison is invertible,
restriction along `g` is bijective on `H^q(Y, f_* F)` if and only if restriction along `g'` is
bijective on `H^q(X, F)`. -/
theorem bijective_etaleCohomologyRestrictionMap_directImage_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    [IsIso ((etaleAbelianBaseChange.{u, v} f g g' f' h).app F)] (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} g
        ((etaleAbelianDirectImage.{u, v} f).obj F) q) ↔
      Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} g' F q) := by
  have : PreservesFiniteColimits (etaleAbelianDirectImage.{u, v} f) :=
    preservesFiniteColimits_etaleAbelianDirectImage_of_isIntegralHom.{u, v} f
  have : PreservesFiniteColimits (etaleAbelianDirectImage.{u, v} f') :=
    preservesFiniteColimits_etaleAbelianDirectImage_of_isIntegralHom.{u, v} f'
  let ZY := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
    (AddCommGrpCat.of (ULift ℤ))
  let e := ((etaleAbelianInverseImageConstantIso.{u, v} f).app (AddCommGrpCat.of (ULift ℤ))).inv
  have : IsIso ((Stacks.CategoryTheory.BaseChange.twoSquare
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
      (etaleAbelianInverseImageCompIso.{u, v} f' g).symm
      ((etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
        eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k) h))).app F) :=
    by rw [← etaleAbelianBaseChange_eq_twoSquare]; infer_instance
  rw [bijective_etaleCohomologyRestrictionMap_iff_mapExtAddHom,
    bijective_etaleCohomologyRestrictionMap_iff_mapExtAddHom,
    Stacks.ExtAdjunction.bijective_mapExtAddHom_iff_of_twoSquare
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
      (etaleAbelianInverseImageCompIso.{u, v} f' g).symm
      ((etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
        eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k) h))
      ZY F q]
  refine Stacks.ExtAdjunction.bijective_iff_of_comp_eq
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso
      ((etaleAbelianInverseImage.{u, v} g').map e) q) Function.bijective_id
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso e q) (fun x ↦ ?_)
  simp only [Functor.mapExtAddHom_apply, Stacks.ExtAdjunction.precomp_apply, id,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]


include h in
/-- **Restriction on the cohomology of a direct image, surjectivity**, under the hypotheses of
`bijective_etaleCohomologyRestrictionMap_directImage_iff`. -/
theorem surjective_etaleCohomologyRestrictionMap_directImage_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    [IsIso ((etaleAbelianBaseChange.{u, v} f g g' f' h).app F)] (q : ℕ) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} g
        ((etaleAbelianDirectImage.{u, v} f).obj F) q) ↔
      Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} g' F q) := by
  have : PreservesFiniteColimits (etaleAbelianDirectImage.{u, v} f) :=
    preservesFiniteColimits_etaleAbelianDirectImage_of_isIntegralHom.{u, v} f
  have : PreservesFiniteColimits (etaleAbelianDirectImage.{u, v} f') :=
    preservesFiniteColimits_etaleAbelianDirectImage_of_isIntegralHom.{u, v} f'
  let ZY := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
    (AddCommGrpCat.of (ULift ℤ))
  let e := ((etaleAbelianInverseImageConstantIso.{u, v} f).app (AddCommGrpCat.of (ULift ℤ))).inv
  have : IsIso ((Stacks.CategoryTheory.BaseChange.twoSquare
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
      (etaleAbelianInverseImageCompIso.{u, v} f' g).symm
      ((etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
        eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k) h))).app F) :=
    by rw [← etaleAbelianBaseChange_eq_twoSquare]; infer_instance
  rw [surjective_etaleCohomologyRestrictionMap_iff_mapExtAddHom,
    surjective_etaleCohomologyRestrictionMap_iff_mapExtAddHom,
    Stacks.ExtAdjunction.surjective_mapExtAddHom_iff_of_twoSquare
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
      (etaleAbelianInverseImageCompIso.{u, v} f' g).symm
      ((etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
        eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k) h))
      ZY F q]
  refine Stacks.ExtAdjunction.surjective_iff_of_comp_eq
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso
      ((etaleAbelianInverseImage.{u, v} g').map e) q) Function.bijective_id
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso e q) (fun x ↦ ?_)
  simp only [Functor.mapExtAddHom_apply, Stacks.ExtAdjunction.precomp_apply, id,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

end Stacks.EtaleCohomology

end

