module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPullbackGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMap

/-!
# The map of Equation 0DKF built from the derived pullback-stalk comparison

For a commutative square of algebraic spaces, a geometric point `x̄'` of `X'`, objects `K` of
`D(𝒪_X)` and `K'` of `D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`, Equation 0DKF is the map
`H^n(K_x̄ ⊗ᴸ_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'}) ⊗ 𝒪_{X',x̄'} ⟶ H^n(K'_x̄')`.  Here it is built from the derived
pullback-stalk comparison `AlgebraicGeometry.Space.derivedPullbackGeometricStalkMap`.

## Main definitions

* `AlgebraicGeometry.Space.canonicalGeometricStalkBaseChangeCohomologyMap`: the map of
  Equation 0DKF.
* `AlgebraicGeometry.Space.GeometricPointwiseBaseChange`: condition (1) of Stacks 0DKG, the map
  of Equation 0DKF is an isomorphism at every geometric point and in every degree.

## References

* [Stacks Project, Equation 0DKF](https://stacks.math.columbia.edu/tag/0DKF)
* [Stacks Project, Tag 0DKG](https://stacks.math.columbia.edu/tag/0DKG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingTheory.TorIndependence
open scoped TensorProduct
open scoped ChangeOfRings

namespace AlgebraicGeometry.Space

universe u

/- A module imported here brings the global instance
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` into scope; it gives `Abelian` for these
categories of modules at a universe join that is never the one used here. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The commutative square of geometric stalks -/

variable {X X' Y Y' : AlgebraicSpaces B S hS}

/-- **Stacks Project, Equation 0DKF.** The canonical map

`H^n(K_x̄ ⊗ᴸ_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'}) ⊗_{(𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'})} 𝒪_{X',x̄'} ⟶ H^n(K'_x̄')`

of `𝒪_{X',x̄'}`-modules attached to a commutative square of algebraic spaces, a geometric point
`x̄'` of `X'`, objects `K` of `D(𝒪_X)` and `K'` of `D(𝒪_{X'})` and a morphism
`φ : L(g')^*K ⟶ K'`.  No cartesianness, Tor independence or quasi-coherence is required.

It is built, not chosen: the `𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'}`-module structure on the source is
`RingTheory.TorIndependence.baseChangeCohomologyModule` and the map is
`RingTheory.TorIndependence.ringBaseChangeCohomologyMap`, the adjoint of the Stacks 065Z
comparison, precomposed with the derived pullback-stalk comparison
`K_x̄ ⊗ᴸ_{𝒪_{X,x̄}} 𝒪_{X',x̄'} ⟶ (L(g')^*K)_x̄'` and followed by `φ`. -/
@[stacks 0DKF]
def canonicalGeometricStalkBaseChangeCohomologyMap
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    (x' : GeometricPoint B S hS X'.1)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (n : ℤ) :=
  let R := geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x'))
  let A := geometricStalkRing B S hS (geometricPointMap g'.hom x')
  let R' := geometricStalkRing B S hS (geometricPointMap f'.hom x')
  let A' := geometricStalkRing B S hS x'
  let a := (stalkStructureMap B S hS f (geometricPointMap g'.hom x')).hom
  let b := (geometricBaseStalkMap B S hS f g f' g' w x').hom
  let c := (stalkStructureMap B S hS g' x').hom
  let e := (stalkStructureMap B S hS f' x').hom
  letI : Algebra R A := a.toAlgebra
  letI : Algebra R R' := b.toAlgebra
  letI : Algebra R A' := (c.comp a).toAlgebra
  letI : Algebra A A' := c.toAlgebra
  letI : Algebra R' A' := e.toAlgebra
  letI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R R' A' :=
    IsScalarTower.of_algebraMap_eq' (stalkStructureMap_square B S hS f g f' g' w x')
  ringBaseChangeCohomologyMap (R := R) (A := A) (R' := R') (A' := A')
    ((geometricDerivedStalk B S hS (geometricPointMap g'.hom x')).obj K)
    ((geometricDerivedStalk B S hS x').obj K')
    ((derivedPullbackGeometricStalkMap g' x').app K ≫ (geometricDerivedStalk B S hS x').map φ) n

/-- **Condition (1) of Stacks 0DKG.** For every geometric point `x̄'` of `X'` and every `n ∈ ℤ`
the map of Equation 0DKF attached to `φ : L(g')^*K ⟶ K'` is an isomorphism. -/
def GeometricPointwiseBaseChange
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') : Prop :=
  ∀ (x' : GeometricPoint B S hS X'.1) (n : ℤ),
    IsIso (canonicalGeometricStalkBaseChangeCohomologyMap B S hS f g f' g' w x' K K' φ n)

end AlgebraicGeometry.Space

end
