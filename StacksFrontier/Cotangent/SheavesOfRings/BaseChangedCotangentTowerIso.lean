module

public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.TargetModulesTransport
public import StacksFrontier.Deformation.ToposThickening.TrivializedThickeningComparison

/-!
# The first vertex of the fundamental triangle under an isomorphism of towers

Let `A ⟶ B ⟶ D` and `A' ⟶ B' ⟶ D` be two towers of homomorphisms of sheaves of commutative rings
on a site with the same top, and let `α : A ⟶ A'` and `β : B ⟶ B'` be isomorphisms making the
two squares commute. Then the degreewise base changes `L_{B/A} ⊗_B D` and `L_{B'/A'} ⊗_{B'} D`,
the first vertices `CategoryTheory.Sheaf.baseChangedCotangentComplex` of the fundamental
triangles of the two towers, are isomorphic.

## Main definitions

* `CategoryTheory.Sheaf.squareRestrictExtendScalarsIso`: for `b = β ≫ b'` with `β` an
  isomorphism, restricting scalars along `β` and then extending them along `b` is extending them
  along `b'`.
* `CategoryTheory.Sheaf.baseChangedCotangentComplexIsoOfTower`: the isomorphism of first
  vertices.

## Implementation notes

The cotangent simplicial modules of `A ⟶ B` and `A' ⟶ B'` are identified, after restriction of
scalars along `β`, by square functoriality
(`CategoryTheory.Sheaf.isIso_squareCotangentSimplicialMap`); extension of scalars along `b` of
that restriction is extension along `b'`, the two functors being left adjoint to the same
restriction of scalars.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section Extend

variable {B B' D : Sheaf J CommRingCat.{max u v w}} (β : B ⟶ B') [IsIso β] (b : B ⟶ D)
  (b' : B' ⟶ D)

/-- Restricting scalars along `b` and then along `β⁻¹` is restricting them along `b'`, when
`β ≫ b' = b`. -/
def squareRestrictCompIso (hb : β ≫ b' = b) :
    squareRestrict.{u, v, w} J b ⋙ squareRestrict.{u, v, w} J (CategoryTheory.inv β) ≅
      squareRestrict.{u, v, w} J b' :=
  NatIso.ofComponents
    (fun M => (Stacks.SheafOfModules.restrictScalarsCompIso
      (squareTargetRing.{u, v, w} J (CategoryTheory.inv β)) (squareTargetRing.{u, v, w} J b)
      (squareTargetRing.{u, v, w} J b')
      (by
        subst hb
        exact ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).congr_map
          (IsIso.inv_hom_id_assoc β b').symm).trans
          ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).map_comp _ _))
      M).symm)
    (fun _ => by
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      ext x
      rfl)

/-- **Extension of scalars along `b = β ≫ b'`, precomposed with restriction along the
isomorphism `β`, is extension of scalars along `b'`**: both are left adjoint to restriction of
scalars along `b'`. -/
def squareRestrictExtendScalarsIso (hb : β ≫ b' = b) :
    squareRestrict.{u, v, w} J β ⋙ towerExtendScalars.{u, v, w} J b ≅
      towerExtendScalars.{u, v, w} J b' :=
  Adjunction.leftAdjointUniq
    (((targetModulesTransport.{u, v, w} J (asIso β)).symm.toAdjunction.comp
      (towerExtendRestrictAdjunction.{u, v, w} J b)).ofNatIsoRight
        (squareRestrictCompIso.{u, v, w} J β b b' hb))
    (towerExtendRestrictAdjunction.{u, v, w} J b')

end Extend

variable {J} {A B A' B' D : Sheaf J CommRingCat.{max u v w}} {a : A ⟶ B} {b : B ⟶ D}
  {a' : A' ⟶ B'} {b' : B' ⟶ D} (α : A ≅ A') (β : B ≅ B')
  (ha : a ≫ β.hom = α.hom ≫ a') (hb : β.hom ≫ b' = b)

/-- The degreewise base changes of the cotangent simplicial modules of two isomorphic towers
with the same top are isomorphic. -/
def baseChangedCotangentSimplicialModuleIsoOfTower :
    baseChangedCotangentSimplicialModule.{u, v, w} J a b ≅
      baseChangedCotangentSimplicialModule.{u, v, w} J a' b' :=
  haveI := isIso_squareCotangentSimplicialMap (resolutionSquareMap.{u, v, w} J α.hom β.hom ha)
    (fun _ => inferInstance)
  ((SimplicialObject.whiskering _ _).obj (towerExtendScalars.{u, v, w} J b)).mapIso
      (asIso (squareCotangentSimplicialMap (resolutionSquareMap.{u, v, w} J α.hom β.hom ha))) ≪≫
    ((SimplicialObject.whiskering _ _).mapIso
      (squareRestrictExtendScalarsIso.{u, v, w} J β.hom b b' hb)).app
        (cotangentSimplicialModule.{u, v, w} J a').object

/-- **The first vertex of the fundamental triangle is invariant under an isomorphism of
towers.** For isomorphisms `α : A ≅ A'` and `β : B ≅ B'` with `a ≫ β = α ≫ a'` and
`β ≫ b' = b`, the degreewise base changes `L_{B/A} ⊗_B D` and `L_{B'/A'} ⊗_{B'} D` are
isomorphic. -/
def baseChangedCotangentComplexIsoOfTower :
    baseChangedCotangentComplex.{u, v, w} J a b ≅ baseChangedCotangentComplex.{u, v, w} J a' b' :=
  ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor (targetModules.{u, v, w} J D)).mapIso
    ((alternatingFaceMapComplex (targetModules.{u, v, w} J D)).mapIso
      (baseChangedCotangentSimplicialModuleIsoOfTower α β ha hb))

end CategoryTheory.Sheaf

end
