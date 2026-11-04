module

public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage

/-!
# Endomorphisms of étale cohomology induced by a self-map of a scheme

A self-map `g : X ⟶ X` and an identification `c : g^{-1} G ⟶ G` of the coefficients give an
endomorphism of the étale cohomology `H^n(X, G)`: restrict along `g`, then apply `c`.  Two such
endomorphisms are mutually inverse as soon as their data are: if a natural transformation `w`
from the composite of the two inverse-image functors to the identity functor is compatible both
with the two constant-sheaf comparisons and with the two coefficient identifications, then the
composite of the two endomorphisms is the identity.

Everything here is the abstract `Ext` statement `Stacks.ExtFunctorial.extEndo_extEndo`
transported along `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`, which is `Ext` of the
exact inverse-image functor read through the constant-sheaf comparison.

## Main definitions

* `Stacks.EtaleCohomology.etaleCohomologyEndo` — the endomorphism attached to `(g, c)`.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyEndo_comp` — the two endomorphisms are mutually
  inverse.
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry

namespace Stacks.EtaleCohomology

section Endo

variable {X : Scheme.{u}}
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- The constant sheaf on `ℤ`, out of which étale cohomology is the `Ext` groups. -/
public abbrev etaleConstantIntSheaf (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
    (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))

/-- **The endomorphism of étale cohomology induced by a self-map and a coefficient
identification.** For `g : X ⟶ X` and `c : g^{-1} G ⟶ G`, restriction along `g` followed by
`c`. -/
public def etaleCohomologyEndo (g : X ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (c : (etaleAbelianInverseImage.{u, v} g).obj G ⟶ G) (n : ℕ) :
    Sheaf.H.{w} G n →+ Sheaf.H.{w} G n :=
  (Sheaf.H.map c n).comp (etaleCohomologyRestrictionMap.{u, v, w} g G n)

/-- The endomorphism is the abstract `Ext` endomorphism of the exact inverse-image functor, with
the constant-sheaf comparison on the source and `c` on the target. -/
public theorem etaleCohomologyEndo_apply (g : X ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (c : (etaleAbelianInverseImage.{u, v} g).obj G ⟶ G) (n : ℕ) (x : Sheaf.H.{w} G n) :
    etaleCohomologyEndo.{u, v, w} g G c n x =
      Stacks.ExtFunctorial.extEndo (etaleAbelianInverseImage.{u, v} g)
        ((etaleAbelianInverseImageConstantIso.{u, v} g).app
          (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))).inv c n x := by
  have h : etaleCohomologyEndo.{u, v, w} g G c n x =
      Sheaf.H.map c n (etaleCohomologyRestrictionMap.{u, v, w} g G n x) := rfl
  rw [h, Sheaf.H.map_apply, etaleCohomologyRestrictionMap_apply]
  rfl

/-- **Two endomorphisms of étale cohomology are mutually inverse as soon as their data are.**
If a natural transformation `w` from the composite of the two inverse-image functors to the
identity functor is compatible with the two constant-sheaf comparisons and with the two
coefficient identifications, then applying the first endomorphism after the second is the
identity of `H^n(X, G)`. -/
public theorem etaleCohomologyEndo_comp
    (gα gβ : X ⟶ X)
    (w : etaleAbelianInverseImage.{u, v} gβ ⋙ etaleAbelianInverseImage.{u, v} gα ⟶
      𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (cα : (etaleAbelianInverseImage.{u, v} gα).obj G ⟶ G)
    (cβ : (etaleAbelianInverseImage.{u, v} gβ).obj G ⟶ G)
    (hz : ((etaleAbelianInverseImageConstantIso.{u, v} gα).app
            (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))).inv ≫
          (etaleAbelianInverseImage.{u, v} gα).map
              ((etaleAbelianInverseImageConstantIso.{u, v} gβ).app
                (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))).inv ≫
            w.app (etaleConstantIntSheaf.{u, v} X) = 𝟙 (etaleConstantIntSheaf.{u, v} X))
    (hc : (etaleAbelianInverseImage.{u, v} gα).map cβ ≫ cα = w.app G) (n : ℕ) :
    (etaleCohomologyEndo.{u, v, w} gα G cα n).comp
        (etaleCohomologyEndo.{u, v, w} gβ G cβ n) =
      AddMonoidHom.id (Sheaf.H.{w} G n) := by
  refine AddMonoidHom.ext fun x ↦ ?_
  rw [AddMonoidHom.comp_apply, etaleCohomologyEndo_apply, etaleCohomologyEndo_apply,
    AddMonoidHom.id_apply]
  exact Stacks.ExtFunctorial.extEndo_extEndo _ _ w _ _ cα cβ hz hc n x

end Endo

end Stacks.EtaleCohomology

end
