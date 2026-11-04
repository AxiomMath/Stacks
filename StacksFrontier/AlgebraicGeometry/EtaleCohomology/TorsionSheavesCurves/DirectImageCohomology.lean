module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralDirectImageAcyclic
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction

/-!
# Étale cohomology of the direct image along an integral morphism

For a morphism of schemes `f : X ⟶ Y` and an abelian sheaf `F` on `X_étale` there is a canonical
map `H^q(Y, f_* F) → H^q(X, F)`: restrict a class along `f` to `H^q(X, f^{-1} f_* F)` and push it
forward along the counit `f^{-1} f_* F → F`. When `f` is integral — a finite morphism, for
instance — this map is an isomorphism.

## Main definitions

* `Stacks.EtaleCohomology.etaleCohomologyDirectImageMap f F q : H^q(Y, f_* F) →+ H^q(X, F)`.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyDirectImageMap_bijective`: for integral `f` the map is
  bijective in every degree.

## References

* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 0A5D](https://stacks.math.columbia.edu/tag/0A5D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- The canonical map `H^q(Y, f_* F) → H^q(X, F)`: restriction along `f`, followed by the
counit `f^{-1} f_* F → F` of the inverse-image/direct-image adjunction. -/
def etaleCohomologyDirectImageMap (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (q : ℕ) :
    Sheaf.H.{w} ((etaleAbelianDirectImage.{u, v} f).obj F) q →+ Sheaf.H.{w} F q :=
  ((Ext.mk₀ ((etaleAbelianInverseImageDirectImageAdj.{u, v} f).counit.app F)).postcomp _
      (add_zero q)).comp
    (etaleCohomologyRestrictionMap.{u, v, w} f ((etaleAbelianDirectImage.{u, v} f).obj F) q)

/-- The defining formula of `etaleCohomologyDirectImageMap`. -/
theorem etaleCohomologyDirectImageMap_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (x : Sheaf.H.{w} ((etaleAbelianDirectImage.{u, v} f).obj F) q) :
    etaleCohomologyDirectImageMap.{u, v, w} f F q x =
      (etaleCohomologyRestrictionMap.{u, v, w} f ((etaleAbelianDirectImage.{u, v} f).obj F) q
        x).comp (Ext.mk₀ ((etaleAbelianInverseImageDirectImageAdj.{u, v} f).counit.app F))
        (add_zero q) :=
  rfl

/-- For `f : X ⟶ Y` integral — finite, for instance — and every abelian sheaf `F` on `X_étale`,
the canonical map `H^q(Y, f_* F) → H^q(X, F)` is bijective in every degree. -/
theorem etaleCohomologyDirectImageMap_bijective [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Bijective (etaleCohomologyDirectImageMap.{u, v, w} f F q) := by
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, v} f
  have : PreservesFiniteColimits (etaleAbelianDirectImage.{u, v} f) :=
    preservesFiniteColimits_etaleAbelianDirectImage_of_isIntegralHom.{u, v} f
  let Z := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
    (AddCommGrpCat.of (ULift ℤ))
  have heq : ⇑(etaleCohomologyDirectImageMap.{u, v, w} f F q) =
      ((Ext.mk₀ (((etaleAbelianInverseImageConstantIso.{u, v} f).app
        (AddCommGrpCat.of (ULift ℤ))).inv) : Ext.{w} _ _ 0).precomp F (zero_add q)) ∘
        (Stacks.ExtAdjunction.extMap adj Z F q :
          Ext.{w} Z ((etaleAbelianDirectImage.{u, v} f).obj F) q →+
            Ext.{w} ((etaleAbelianInverseImage.{u, v} f).obj Z) F q) := by
    funext x
    rw [Function.comp_apply, etaleCohomologyDirectImageMap_apply,
      Stacks.ExtAdjunction.extMap_apply, Stacks.ExtAdjunction.precomp_apply,
      etaleCohomologyRestrictionMap_apply]
    apply Ext.comp_assoc_of_third_deg_zero
  rw [heq]
  exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ q).comp
    (Stacks.ExtAdjunction.extMap_bijective adj Z F q)

end Stacks.EtaleCohomology

end
