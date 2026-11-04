module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffinePointwiseRingChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapIso
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapCanonical

/-!
# Invariance of the map of Equation 0DKF under isomorphisms of the data

For a commutative square of algebraic spaces, a geometric point `x̄'` of `X'` and data
`(K, K', φ : L(g')^*K ⟶ K')`, the map of Equation 0DKF
(`AlgebraicGeometry.Space.canonicalGeometricStalkBaseChangeCohomologyMap`) is invertible or not
independently of the representatives: isomorphisms `K ≅ K₁` and `K' ≅ K₁'` carrying `φ` to `φ₁`
make the two maps invertible together.

## Main results

* `AlgebraicGeometry.Space.isIso_geometricStalkBaseChangeCohomologyMap_iff_of_iso`
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
attribute [-instance] Stacks.SheafOfModules.coefficientSheafification

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingTheory.TorIndependence

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X X' Y Y' : AlgebraicSpaces B S hS}

/-- The input of Equation 0DKF, the derived pullback-stalk comparison followed by the stalk of
`φ`, carries compatible isomorphisms of the data to a commutative square. -/
theorem derivedPullbackGeometricStalkMap_app_comp_map_of_iso (g' : X' ⟶ X)
    (x' : GeometricPoint B S hS X'.1)
    {K K₁ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    {K' K₁' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))}
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (φ₁ : (smallEtaleDerivedModulePullback B S hS g').obj K₁ ⟶ K₁')
    (e : K ⟶ K₁) (e' : K' ⟶ K₁')
    (h : (smallEtaleDerivedModulePullback B S hS g').map e ≫ φ₁ = φ ≫ e') :
    ((derivedPullbackGeometricStalkMap g' x').app K ≫ (geometricDerivedStalk B S hS x').map φ) ≫
        (geometricDerivedStalk B S hS x').map e' =
      (geometricStalkDerivedExtension g' x').functor.map
          ((geometricDerivedStalk B S hS (geometricPointMap g'.hom x')).map e) ≫
        (derivedPullbackGeometricStalkMap g' x').app K₁ ≫
          (geometricDerivedStalk B S hS x').map φ₁ := by
  have hn := (derivedPullbackGeometricStalkMap g' x').naturality e
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, h]

/-- **The map of Equation 0DKF is invariant under isomorphisms of the data.** Isomorphisms
`e : K ≅ K₁` and `e' : K' ≅ K₁'` with `L(g')^*e ≫ φ₁ = φ ≫ e'` make the map of Equation 0DKF for
`(K, K', φ)` at `x̄'` in degree `n` invertible exactly when the one for `(K₁, K₁', φ₁)` is. -/
theorem isIso_geometricStalkBaseChangeCohomologyMap_iff_of_iso
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    (x' : GeometricPoint B S hS X'.1)
    {K K₁ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    {K' K₁' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))}
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (φ₁ : (smallEtaleDerivedModulePullback B S hS g').obj K₁ ⟶ K₁')
    (e : K ≅ K₁) (e' : K' ≅ K₁')
    (h : (smallEtaleDerivedModulePullback B S hS g').map e.hom ≫ φ₁ = φ ≫ e'.hom) (n : ℤ) :
    IsIso (canonicalGeometricStalkBaseChangeCohomologyMap B S hS f g f' g' w x' K K' φ n) ↔
      IsIso (canonicalGeometricStalkBaseChangeCohomologyMap B S hS f g f' g' w x' K₁ K₁' φ₁ n) := by
  let R := geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x'))
  let A := geometricStalkRing B S hS (geometricPointMap g'.hom x')
  let R' := geometricStalkRing B S hS (geometricPointMap f'.hom x')
  let A' := geometricStalkRing B S hS x'
  let a := (stalkStructureMap B S hS f (geometricPointMap g'.hom x')).hom
  let b := (geometricBaseStalkMap B S hS f g f' g' w x').hom
  let c := (stalkStructureMap B S hS g' x').hom
  let e₀ := (stalkStructureMap B S hS f' x').hom
  let : Algebra R A := a.toAlgebra
  let : Algebra R R' := b.toAlgebra
  let : Algebra R A' := (c.comp a).toAlgebra
  let : Algebra A A' := c.toAlgebra
  let : Algebra R' A' := e₀.toAlgebra
  let : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R R' A' :=
    IsScalarTower.of_algebraMap_eq' (stalkStructureMap_square B S hS f g f' g' w x')
  exact isIso_ringBaseChangeCohomologyMap_iff_of_iso (R := R) (A := A) (R' := R') (A' := A')
    ((geometricDerivedStalk B S hS (geometricPointMap g'.hom x')).mapIso e)
    ((geometricDerivedStalk B S hS x').mapIso e') _ _
    (derivedPullbackGeometricStalkMap_app_comp_map_of_iso B S hS g' x' φ φ₁ e.hom e'.hom h).symm n

end AlgebraicGeometry.Space

end
