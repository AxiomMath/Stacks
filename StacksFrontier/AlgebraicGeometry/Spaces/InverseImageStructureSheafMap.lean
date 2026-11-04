module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageCompAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# The map `(u ≫ h)⁻¹𝒪_Y ⟶ u⁻¹𝒪_X` of inverse images of structure sheaves

For morphisms of algebraic spaces `u : W ⟶ X` and `h : X ⟶ Y`, the inverse image along `u` of the
structure map `h^♯ : h⁻¹𝒪_Y ⟶ 𝒪_X`, read through the composition law
`u⁻¹h⁻¹ ≅ (u ≫ h)⁻¹` of Stacks 03G8, is a homomorphism of sheaves of rings on the small étale
site of `W`
`(u ≫ h)⁻¹𝒪_Y ⟶ u⁻¹𝒪_X`
compatible with the structure maps to `𝒪_W`. For `u` the inclusion of a closed subspace this is
the algebra structure of the extension of a thickening; for `u` the map `X₀ ⟶ X'` of a
deformation and `h` a morphism of deformations it is the comparison of the extensions of two
deformations used in the proof of [Stacks Project, Tag 0D1K].

## Main definitions

* `AlgebraicGeometry.Space.inverseImageStructureSheafMap`: the map `(u ≫ h)⁻¹𝒪_Y ⟶ u⁻¹𝒪_X`.
* `AlgebraicGeometry.Space.inverseImageStructureSheafMapOfEq`: the same for `u' = u ≫ h`.

## Main results

* `AlgebraicGeometry.Space.inverseImageStructureSheafMap_comp_structureSharpInverseImage`:
  followed by `u^♯` it is `(u ≫ h)^♯`.
* `AlgebraicGeometry.Space.inverseImageStructureSheafMap_comp`,
  `AlgebraicGeometry.Space.inverseImageStructureSheafMapOfEq_comp`: the maps compose along
  `h` and `g` to the map along `h ≫ g` (from the associativity of the composition law of 03G8).

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W X Y Z : AlgebraicSpaces B S hS}

/-- **The map `(u ≫ h)⁻¹𝒪_Y ⟶ u⁻¹𝒪_X`**: the inverse image along `u` of `h^♯`, read through
the composition law `u⁻¹h⁻¹ ≅ (u ≫ h)⁻¹` of Stacks 03G8. -/
def inverseImageStructureSheafMap (u : W ⟶ X) (h : X ⟶ Y) :
    inverseImageStructureSheaf B S hS (u ≫ h) ⟶ inverseImageStructureSheaf B S hS u :=
  (smallEtaleRingedToposHom_compInverseImageRingIso B S hS u h).inv.app _ ≫
    (smallEtaleInverseImageRing B S hS u).map (smallEtaleRingedToposHom B S hS h).fSharpInverseImage

/-- **The map `(u ≫ h)⁻¹𝒪_Y ⟶ u⁻¹𝒪_X` is compatible with the structure maps**: followed by
`u^♯ : u⁻¹𝒪_X ⟶ 𝒪_W` it is `(u ≫ h)^♯`. -/
theorem inverseImageStructureSheafMap_comp_structureSharpInverseImage (u : W ⟶ X) (h : X ⟶ Y) :
    inverseImageStructureSheafMap B S hS u h ≫ structureSharpInverseImage B S hS u =
      structureSharpInverseImage B S hS (u ≫ h) := by
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg (_ ≫ ·)
    (smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS u h).symm) ?_
  exact Iso.inv_hom_id_app_assoc _ _ _

/-- The map `u'⁻¹𝒪_Y ⟶ u⁻¹𝒪_X` for `u' = u ≫ h`. -/
def inverseImageStructureSheafMapOfEq {u' : W ⟶ Y} (u : W ⟶ X) (h : X ⟶ Y) (e : u ≫ h = u') :
    inverseImageStructureSheaf B S hS u' ⟶ inverseImageStructureSheaf B S hS u :=
  eqToHom (congrArg (inverseImageStructureSheaf B S hS) e.symm) ≫
    inverseImageStructureSheafMap B S hS u h

/-- For `u₁ = u₂`, the identification `u₁⁻¹𝒪_Y ⟶ u₂⁻¹𝒪_Y` followed by `u₂^♯` is `u₁^♯`. -/
theorem structureSharpInverseImage_eqToHom {u₁ u₂ : W ⟶ Y} (e : u₁ = u₂) :
    eqToHom (congrArg (inverseImageStructureSheaf B S hS) e) ≫
        structureSharpInverseImage B S hS u₂ = structureSharpInverseImage B S hS u₁ := by
  cases e
  exact Category.id_comp _

/-- The map `u'⁻¹𝒪_Y ⟶ u⁻¹𝒪_X` for `u' = u ≫ h` is compatible with the structure maps. -/
theorem inverseImageStructureSheafMapOfEq_comp_structureSharpInverseImage {u' : W ⟶ Y}
    (u : W ⟶ X) (h : X ⟶ Y) (e : u ≫ h = u') :
    inverseImageStructureSheafMapOfEq B S hS u h e ≫ structureSharpInverseImage B S hS u =
      structureSharpInverseImage B S hS u' := by
  refine (Category.assoc _ _ _).trans ?_
  rw [inverseImageStructureSheafMap_comp_structureSharpInverseImage]
  exact structureSharpInverseImage_eqToHom B S hS e.symm

/-- Associativity of the composition law of 03G8, followed by an arbitrary morphism `k`. -/
private theorem compInverseImageRingIso_inv_app_assoc_comp (u : W ⟶ X) (h : X ⟶ Y)
    (g : Y ⟶ Z) (A : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}) {T}
    (k : (smallEtaleInverseImageRing B S hS u).obj ((smallEtaleInverseImageRing B S hS h).obj
      ((smallEtaleInverseImageRing B S hS g).obj A)) ⟶ T) :
    (smallEtaleRingedToposHom_compInverseImageRingIso B S hS (u ≫ h) g).inv.app A ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS u h).inv.app
          ((smallEtaleInverseImageRing B S hS g).obj A) ≫ k =
      (smallEtaleRingedToposHom_compInverseImageRingIso B S hS u (h ≫ g)).inv.app A ≫
        (smallEtaleInverseImageRing B S hS u).map
          ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS h g).inv.app A) ≫ k := by
  simp only [← Category.assoc,
    smallEtaleRingedToposHom_compInverseImageRingIso_inv_assoc B S hS u h g A]

/-- **The maps `(u ≫ h)⁻¹𝒪_Y ⟶ u⁻¹𝒪_X` compose**: along `h` and then `g`, read on `u` and on
`u ≫ h`, they compose to the map along `h ≫ g`. This is the associativity of the composition law
of Stacks 03G8
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso_inv_assoc`) together
with its compatibility with the structure maps. -/
theorem inverseImageStructureSheafMap_comp (u : W ⟶ X) (h : X ⟶ Y) (g : Y ⟶ Z) :
    inverseImageStructureSheafMap B S hS (u ≫ h) g ≫ inverseImageStructureSheafMap B S hS u h =
      inverseImageStructureSheafMap B S hS u (h ≫ g) := by
  have hn := (smallEtaleRingedToposHom_compInverseImageRingIso B S hS u h).inv.naturality
    (smallEtaleRingedToposHom B S hS g).fSharpInverseImage
  have hs := inverseImageStructureSheafMap_comp_structureSharpInverseImage B S hS h g
  unfold inverseImageStructureSheafMap at hs ⊢
  calc _ = (smallEtaleRingedToposHom_compInverseImageRingIso B S hS (u ≫ h) g).inv.app _ ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS u h).inv.app _ ≫
        (smallEtaleInverseImageRing B S hS u).map
          ((smallEtaleInverseImageRing B S hS h).map
            (smallEtaleRingedToposHom B S hS g).fSharpInverseImage) ≫
        (smallEtaleInverseImageRing B S hS u).map
          (smallEtaleRingedToposHom B S hS h).fSharpInverseImage := by
        simp only
        exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) hn).trans (Category.assoc _ _ _)))
    _ = (smallEtaleRingedToposHom_compInverseImageRingIso B S hS u (h ≫ g)).inv.app _ ≫
        (smallEtaleInverseImageRing B S hS u).map
          ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS h g).inv.app _) ≫
        (smallEtaleInverseImageRing B S hS u).map
          ((smallEtaleInverseImageRing B S hS h).map
            (smallEtaleRingedToposHom B S hS g).fSharpInverseImage) ≫
        (smallEtaleInverseImageRing B S hS u).map
          (smallEtaleRingedToposHom B S hS h).fSharpInverseImage :=
        compInverseImageRingIso_inv_app_assoc_comp B S hS u h g _ _
    _ = _ := by
        simp only [← Functor.map_comp]
        exact congrArg (fun k => _ ≫ (smallEtaleInverseImageRing B S hS u).map k)
          ((Category.assoc _ _ _).symm.trans hs)

/-- The maps `u'⁻¹𝒪_Y ⟶ u⁻¹𝒪_X` for `u' = u ≫ h` compose along `h` and `g` to the map along
`h ≫ g`. -/
theorem inverseImageStructureSheafMapOfEq_comp {u' : W ⟶ Y} {u'' : W ⟶ Z} (u : W ⟶ X)
    (h : X ⟶ Y) (g : Y ⟶ Z) (e₁ : u ≫ h = u') (e₂ : u' ≫ g = u'') :
    inverseImageStructureSheafMapOfEq B S hS u' g e₂ ≫
        inverseImageStructureSheafMapOfEq B S hS u h e₁ =
      inverseImageStructureSheafMapOfEq B S hS u (h ≫ g)
        (by rw [← Category.assoc, e₁, e₂]) := by
  subst e₁ e₂
  simpa [inverseImageStructureSheafMapOfEq] using inverseImageStructureSheafMap_comp B S hS u h g

/-- **The inverse image along `u` of the map `(h ≫ g)⁻¹𝒪_Z ⟶ h⁻¹𝒪_Y` is the map along `g` on
`u ≫ h`**, read through the composition law `u⁻¹h⁻¹ ≅ (u ≫ h)⁻¹` of Stacks 03G8. -/
theorem inverseImageStructureSheafMap_inverseImage (u : W ⟶ X) (h : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleRingedToposHom_compInverseImageRingIso B S hS u (h ≫ g)).inv.app
          (smallEtaleRingedTopos B S hS Z).O ≫
        (smallEtaleInverseImageRing B S hS u).map (inverseImageStructureSheafMap B S hS h g) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS u h).hom.app
          (smallEtaleRingedTopos B S hS Y).O =
      inverseImageStructureSheafMap B S hS (u ≫ h) g := by
  have hn := (smallEtaleRingedToposHom_compInverseImageRingIso B S hS u h).hom.naturality
    (smallEtaleRingedToposHom B S hS g).fSharpInverseImage
  unfold inverseImageStructureSheafMap
  calc _ = (smallEtaleRingedToposHom_compInverseImageRingIso B S hS u (h ≫ g)).inv.app _ ≫
        (smallEtaleInverseImageRing B S hS u).map
          ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS h g).inv.app _) ≫
        (smallEtaleInverseImageRing B S hS u).map
          ((smallEtaleInverseImageRing B S hS h).map
            (smallEtaleRingedToposHom B S hS g).fSharpInverseImage) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS u h).hom.app _ :=
        congrArg (_ ≫ ·) ((congrArg (· ≫ _)
          ((smallEtaleInverseImageRing B S hS u).map_comp _ _)).trans (Category.assoc _ _ _))
    _ = (smallEtaleRingedToposHom_compInverseImageRingIso B S hS (u ≫ h) g).inv.app _ ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS u h).inv.app _ ≫
        (smallEtaleInverseImageRing B S hS u).map
          ((smallEtaleInverseImageRing B S hS h).map
            (smallEtaleRingedToposHom B S hS g).fSharpInverseImage) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS u h).hom.app _ :=
        (compInverseImageRingIso_inv_app_assoc_comp B S hS u h g _ _).symm
    _ = _ := by
        refine congrArg (_ ≫ ·) ?_
        refine (congrArg (_ ≫ ·) hn).trans ?_
        exact Iso.inv_hom_id_app_assoc _ _ _

end AlgebraicGeometry.Space

end
