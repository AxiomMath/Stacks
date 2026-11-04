module

public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierPullbackCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleDivisorDifference
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation

/-!
# The inverse image of `𝒪_X(D - D')` along a flat morphism

Let `j : X ⟶ Y` be a flat morphism of algebraic spaces and let `D, D' ⊆ Y` be effective
Cartier divisors.  Then `j^*𝒪_Y(D - D') ≅ 𝒪_X(j⁻¹D - j⁻¹D')`.  Flatness makes the canonical
map `j^*𝓘_D ⟶ 𝓘_{j⁻¹D}` an isomorphism (Stacks 04CQ); the inverse image is monoidal
(Stacks 03EL) and preserves the structure sheaf, so `j^*𝒪_Y(D)` is a tensor inverse of
`𝓘_{j⁻¹D}`, as is `𝒪_X(j⁻¹D)`, and tensor inverses are unique up to isomorphism.  Together with
`𝒪(-D') ≅ 𝓘_{D'}` this identifies both tensor factors of `𝒪_Y(D - D') = 𝒪_Y(D) ⊗ 𝒪_Y(-D')`.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackStructureSheafTensorIso`: the inverse image of modules on
  algebraic spaces commutes with `Stacks.SheafOfModules.Tensor.sheafTensor`.

## Main results

* `AlgebraicGeometry.Space.isInvertibleModule_differenceDivisorSheaf`: `𝒪_X(D - D')` is
  invertible.
* `AlgebraicGeometry.Space.isInvertible_of_isInvertibleModule`: the two invertibility
  predicates for modules on an algebraic space agree.
* `AlgebraicGeometry.Space.nonempty_modulePullback_differenceDivisorSheaf_iso`:
  `j^*𝒪_Y(D - D') ≅ 𝒪_X(j⁻¹D - j⁻¹D')` for flat `j`.

## References

* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.SheafOfModules.Invertible

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section PullbackSheafTensor

attribute [local instance] modulesMonoidalCategory

/-- The inverse image along a morphism of algebraic spaces commutes with the tensor product
sheaf: `f^*(G ⊗ G') ≅ f^*G ⊗ f^*G'`, in the spelling
`Stacks.SheafOfModules.Tensor.sheafTensor` of the tensor product. -/
def modulePullbackStructureSheafTensorIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (G G' : SheafOfModules.{u} (structureRingSheaf B S hS Y)) :
    (modulePullback B S hS f).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          ⟨structureCommRings B S hS Y, Presheaf.isSheaf_of_isSheaf_comp _
            (structureCommRings B S hS Y) (forget₂ CommRingCat RingCat)
            (structureRingSheaf B S hS Y).property⟩).obj G).obj G') ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          ⟨structureCommRings B S hS X, Presheaf.isSheaf_of_isSheaf_comp _
            (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
            (structureRingSheaf B S hS X).property⟩).obj
          ((modulePullback B S hS f).obj G)).obj ((modulePullback B S hS f).obj G') :=
  (modulePullback B S hS f).mapIso (modulesTensorObjIso B S hS Y.1 Y.2 G G').symm ≪≫
    modulePullbackTensorIso B S hS f G G' ≪≫
    modulesTensorObjIso B S hS X.1 X.2 _ _

end PullbackSheafTensor

/-- The sheaf `𝒪_X(D - D')` is an invertible module. -/
theorem isInvertibleModule_differenceDivisorSheaf (X : AlgebraicSpaces B S hS)
    (D D' : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D)
    (hD' : IsEffectiveCartierDivisor B S hS X D') :
    IsInvertibleModule X (differenceDivisorSheaf B S hS X D D' hD hD') := by
  have hN : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (negativeDivisorSheaf B S hS X D' hD') := by
    have := associatedInvertibleSheaf_isInvertible B S hS X D' hD'
    exact Stacks.SheafOfModules.Invertible.tensorPower_isInvertible _ _ _ (-1)
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry.{u, u + 1, u} _ _ _
    (associatedInvertibleSheaf_isInvertible B S hS X D hD)
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry.{u, u + 1, u} _ _ _ hN
  exact Stacks.SheafOfModules.isInvertible_tensorSheaf.{u, u + 1, u}
    (structureCommRings B S hS X) (structureRingSheaf B S hS X).property _ _

/-- An invertible module in the sense of the Picard functor is invertible in the sense of the
divisor calculus. -/
theorem isInvertible_of_isInvertibleModule (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule X L) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry.{u, u + 1, u} _ _ _ hL

/-- The inverse image of `𝒪_Y(D - D')` along a flat morphism `j : X ⟶ Y` is
`𝒪_X(j⁻¹D - j⁻¹D')`. -/
theorem nonempty_modulePullback_differenceDivisorSheaf_iso {X Y : AlgebraicSpaces B S hS}
    (j : X ⟶ Y) (hj : IsFlat B S hS j.hom)
    (D D' : ClosedSubspaces B S hS Y.1) (hD : IsEffectiveCartierDivisor B S hS Y D)
    (hD' : IsEffectiveCartierDivisor B S hS Y D') :
    Nonempty ((modulePullback B S hS j).obj (differenceDivisorSheaf B S hS Y D D' hD hD') ≅
      differenceDivisorSheaf B S hS X
        ⟨D.1.preimage j.hom, isClosedSubspace_preimage B S hS j.hom D.1 Y.2 X.2 D.2⟩
        ⟨D'.1.preimage j.hom, isClosedSubspace_preimage B S hS j.hom D'.1 Y.2 X.2 D'.2⟩
        (isPullbackDefined_of_isFlat B S hS j D hD hj)
        (isPullbackDefined_of_isFlat B S hS j D' hD' hj)) := by
  have hflat : (smallEtaleRingedToposHom B S hS j).IsFlat :=
    (isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS j).mp hj
  set D₁ := preimageSubspace B S hS j D with hD₁def
  set D₁' := preimageSubspace B S hS j D' with hD₁'def
  have hE := isPullbackDefined_of_isFlat B S hS j D hD hj
  have hE' := isPullbackDefined_of_isFlat B S hS j D' hD' hj
  have hI : ∀ Z : ClosedSubspaces B S hS Y.1,
      Nonempty ((modulePullback B S hS j).obj (idealSheafOfModules B S hS Y Z) ≅
        idealSheafOfModules B S hS X (preimageSubspace B S hS j Z)) := fun Z => by
    have := isIso_idealSheafMap_of_isFlat B S hS j Z hflat
    exact ⟨asIso (idealSheafMap B S hS (preimageSubspace B S hS j Z) Z j
      (preimageProjection B S hS j Z) (conormalEtaleRestrictionSquare B S hS j Z))⟩
  obtain ⟨eI⟩ := hI D
  obtain ⟨eI'⟩ := hI D'
  let eA : (modulePullback B S hS j).obj (associatedInvertibleSheaf B S hS Y D hD) ≅
      associatedInvertibleSheaf B S hS X D₁ hE :=
    have : Stacks.SheafOfModules.IsInvertible (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property (idealSheafOfModules B S hS X D₁) :=
      Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry.{u, u + 1, u} _ _ _ hE
    Stacks.SheafOfModules.isoOfTensorIsoUnit (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property _ _ _
      (tensorProductIso (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (Iso.refl _) eI.symm ≪≫
        (modulePullbackStructureSheafTensorIso B S hS j _ _).symm ≪≫
        (modulePullback B S hS j).mapIso (associatedInvertibleSheafEvaluation B S hS Y D hD) ≪≫
        modulePullbackUnitIso B S hS j)
      (associatedInvertibleSheafEvaluation B S hS X D₁ hE)
  let eN : (modulePullback B S hS j).obj (negativeDivisorSheaf B S hS Y D' hD') ≅
      negativeDivisorSheaf B S hS X D₁' hE' :=
    (modulePullback B S hS j).mapIso (negativeDivisorSheafIso B S hS Y D' hD') ≪≫ eI' ≪≫
      (negativeDivisorSheafIso B S hS X D₁' hE').symm
  exact ⟨modulePullbackStructureSheafTensorIso B S hS j _ _ ≪≫
    tensorProductIso (structureCommRings B S hS X) (structureRingSheaf B S hS X).property eA eN⟩

end AlgebraicGeometry.Space
