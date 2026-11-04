module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Restriction of sections along an inclusion of affine opens

The restriction map on sections of the structure sheaf induced by a morphism of the small affine
Zariski site, as a ring homomorphism, together with its functoriality.  This is what a diagram
of rings indexed by the affine Zariski site is built from.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

open Scheme.AffineZariskiSite

/-- Restriction of sections of the structure sheaf along an inclusion of affine opens. -/
def restrictionRingMap (X : Scheme.{u})
    {U V : X.AffineZariskiSite} (i : U ⟶ V) : Γ(X, V.1) →+* Γ(X, U.1) :=
  (X.presheaf.map (homOfLE (toOpens_mono i.le)).op).hom

/-- Restricting along the identity is the identity. -/
theorem restrictionRingMap_id (X : Scheme.{u}) (U : X.AffineZariskiSite) :
    restrictionRingMap X (CategoryTheory.CategoryStruct.id U) = RingHom.id _ := by
  ext x
  simp [restrictionRingMap]

/-- Restriction maps compose. -/
theorem restrictionRingMap_comp (X : Scheme.{u})
    {U V W : X.AffineZariskiSite} (i : U ⟶ V) (j : V ⟶ W) :
    restrictionRingMap X (i ≫ j) =
      (restrictionRingMap X i).comp (restrictionRingMap X j) := by
  have hcat :
      X.presheaf.map (homOfLE (toOpens_mono j.le)).op ≫
        X.presheaf.map (homOfLE (toOpens_mono i.le)).op =
      X.presheaf.map (homOfLE (toOpens_mono (i ≫ j).le)).op := by
    rw [← X.presheaf.map_comp]
    congr 1
  simpa [restrictionRingMap, ← CommRingCat.comp_apply] using
    (congrArg CommRingCat.Hom.hom hcat).symm

end AlgebraicGeometry

end
