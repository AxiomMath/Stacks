module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkStructureMapComp
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapSquareIso

/-!
# The map of Equation 0DKF along étale morphisms of squares

For a commutative square of algebraic spaces and a second commutative square mapping to it by
étale morphisms, the stalk rings of the two squares at corresponding geometric points are
identified by the bijective homomorphisms of geometric stalk rings of the étale maps (Stacks
04KF), and the map of Equation 0DKF of the first square is invertible exactly when the ring-level
map of Stacks 0DJ7 of the second square of stalk rings, at the base changes of the data, is.

## Main results

* `AlgebraicGeometry.Space.stalkStructureMap_cube`
* `AlgebraicGeometry.Space.isIso_geometricStalkBaseChangeCohomologyMap_iff_of_isEtale_square`
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

@[expose] public noncomputable section

open CategoryTheory
open RingTheory.TorIndependence

universe u

/- A module imported on the base (`Stacks.Cohomology.SiteModules.moduleSheavesAbelian`, through
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TorIndependentDerivedPullback`) gives `Abelian` for
these categories of modules at a universe join that is never the one used here. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Cube

variable {X X' Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- **The square of geometric stalk rings of a commutative square, with transported points.**
For a commutative square and geometric points `p`, `q`, `y` equal to the images of `x̄'`, going
round by `X` and going round by `Y'` give the same homomorphism `𝒪_{Y,y} ⟶ 𝒪_{X',x̄'}`. -/
theorem stalkStructureMap_cube (w : g' ≫ f = f' ≫ g) (x' : GeometricPoint B S hS X'.1)
    (p : GeometricPoint B S hS X.1) (hp : p = geometricPointMap g'.hom x')
    (q : GeometricPoint B S hS Y'.1) (hq : q = geometricPointMap f'.hom x')
    (y : GeometricPoint B S hS Y.1) (hy₁ : y = geometricPointMap f.hom p)
    (hy₂ : y = geometricPointMap g.hom q) :
    (eqToHom (congrArg (fun z => geometricStalkRing B S hS (X := X) z) hp) ≫
        stalkStructureMap B S hS g' x').hom.comp
      (eqToHom (congrArg (fun z => geometricStalkRing B S hS (X := Y) z) hy₁) ≫
        stalkStructureMap B S hS f p).hom =
    (eqToHom (congrArg (fun z => geometricStalkRing B S hS (X := Y') z) hq) ≫
        stalkStructureMap B S hS f' x').hom.comp
      (eqToHom (congrArg (fun z => geometricStalkRing B S hS (X := Y) z) hy₂) ≫
        stalkStructureMap B S hS g q).hom := by
  subst hp hq hy₁
  simp only [eqToHom_refl, Category.id_comp]
  exact stalkStructureMap_square B S hS f g f' g' w x'

/-- `AlgebraicGeometry.Space.stalkStructureMap_cube` when only the first leg carries a transport
of points. -/
theorem stalkStructureMap_cube_left (w : g' ≫ f = f' ≫ g) (x' : GeometricPoint B S hS X'.1)
    (p : GeometricPoint B S hS X.1) (hp : p = geometricPointMap g'.hom x')
    (hy : geometricPointMap f.hom p = geometricPointMap g.hom (geometricPointMap f'.hom x')) :
    (eqToHom (congrArg (fun z => geometricStalkRing B S hS (X := X) z) hp) ≫
        stalkStructureMap B S hS g' x').hom.comp (stalkStructureMap B S hS f p).hom =
    (stalkStructureMap B S hS f' x').hom.comp
      (eqToHom (congrArg (fun z => geometricStalkRing B S hS (X := Y) z) hy) ≫
        stalkStructureMap B S hS g (geometricPointMap f'.hom x')).hom := by
  subst hp
  simp only [eqToHom_refl, Category.id_comp]
  exact stalkStructureMap_square B S hS f g f' g' w x'

end Cube

/-- The homomorphism of geometric stalk rings of an étale morphism, after a transport of the
point, is bijective. -/
theorem bijective_eqToHom_comp_stalkStructureMap {X X' : AlgebraicSpaces B S hS} (φ : X' ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (y : GeometricPoint B S hS X'.1) (p : GeometricPoint B S hS X.1)
    (h : p = geometricPointMap φ.hom y) :
    Function.Bijective (eqToHom (congrArg (fun z => geometricStalkRing B S hS (X := X) z) h) ≫
      stalkStructureMap B S hS φ y).hom := by
  subst h
  simpa only [eqToHom_refl, Category.id_comp] using
    bijective_stalkStructureMap_of_isEtale B S hS φ hφ y

section Square

variable {X X' Y Y' X₁ X₁' Y₁ Y₁' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {f' : X' ⟶ Y'} {g' : X' ⟶ X} {f₁ : X₁ ⟶ Y₁} {g₁ : Y₁' ⟶ Y₁} {f₁' : X₁' ⟶ Y₁'}
  {g₁' : X₁' ⟶ X₁} {a : X₁ ⟶ X} {b : Y₁ ⟶ Y} {c : Y₁' ⟶ Y'} {a' : X₁' ⟶ X'}

/-- **The map of Equation 0DKF along an étale morphism of squares, ring-level half.** For a
commutative square of algebraic spaces and a second one mapping to it by étale morphisms
`a, b, c, a'`, the map of Equation 0DKF of the first square at `a'(x̄)` is invertible exactly when
the ring-level map of Stacks 0DJ7 of the square of geometric stalks of the second square at
`x̄`, at the base changes of the stalks of `K`, `K'` and the induced morphism, is. -/
theorem isIso_geometricStalkBaseChangeCohomologyMap_iff_of_isEtale_square
    (w : g' ≫ f = f' ≫ g) (w₁ : g₁' ≫ f₁ = f₁' ≫ g₁)
    (hfa : f₁ ≫ b = a ≫ f) (hgb : g₁ ≫ b = c ≫ g) (hfc : f₁' ≫ c = a' ≫ f')
    (ha' : g₁' ≫ a = a' ≫ g') (hae : IsEtale B S hS a.hom) (hbe : IsEtale B S hS b.hom)
    (hce : IsEtale B S hS c.hom) (hae' : IsEtale B S hS a'.hom)
    (x : GeometricPoint B S hS X₁'.1)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') (n : ℤ) :
    letI : Algebra
      (geometricStalkRing B S hS
        (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
      (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x))) :=
      (stalkStructureMap B S hS f
          (geometricPointMap g'.hom (geometricPointMap a'.hom x))).hom.toAlgebra
    letI : Algebra
      (geometricStalkRing B S hS
        (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
      (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x))) :=
      (geometricBaseStalkMap B S hS f g f' g' w (geometricPointMap a'.hom x)).hom.toAlgebra
    letI : Algebra
      (geometricStalkRing B S hS
        (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
      (geometricStalkRing B S hS (geometricPointMap a'.hom x)) :=
      ((stalkStructureMap B S hS g' (geometricPointMap a'.hom x)).hom.comp
          (stalkStructureMap B S hS f
            (geometricPointMap g'.hom (geometricPointMap a'.hom x))).hom).toAlgebra
    letI : Algebra
      (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap a'.hom x)) :=
      (stalkStructureMap B S hS g' (geometricPointMap a'.hom x)).hom.toAlgebra
    letI : Algebra
      (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap a'.hom x)) :=
      (stalkStructureMap B S hS f' (geometricPointMap a'.hom x)).hom.toAlgebra
    haveI : IsScalarTower
      (geometricStalkRing B S hS
        (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
      (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap a'.hom x)) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower
      (geometricStalkRing B S hS
        (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
      (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap a'.hom x)) :=
      IsScalarTower.of_algebraMap_eq'
        (stalkStructureMap_square B S hS f g f' g' w (geometricPointMap a'.hom x))
    letI : Algebra
      (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)) :=
      (stalkStructureMap B S hS f₁ (geometricPointMap g₁'.hom x)).hom.toAlgebra
    letI : Algebra
      (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap f₁'.hom x)) :=
      (geometricBaseStalkMap B S hS f₁ g₁ f₁' g₁' w₁ x).hom.toAlgebra
    letI : Algebra
      (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
      (geometricStalkRing B S hS x) :=
      ((stalkStructureMap B S hS g₁' x).hom.comp
          (stalkStructureMap B S hS f₁ (geometricPointMap g₁'.hom x)).hom).toAlgebra
    letI : Algebra (geometricStalkRing B S hS (geometricPointMap g₁'.hom x))
      (geometricStalkRing B S hS x) := (stalkStructureMap B S hS g₁' x).hom.toAlgebra
    letI : Algebra (geometricStalkRing B S hS (geometricPointMap f₁'.hom x))
      (geometricStalkRing B S hS x) := (stalkStructureMap B S hS f₁' x).hom.toAlgebra
    haveI : IsScalarTower
      (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)) (geometricStalkRing B S hS x) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower
      (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap f₁'.hom x)) (geometricStalkRing B S hS x) :=
      IsScalarTower.of_algebraMap_eq' (stalkStructureMap_square B S hS f₁ g₁ f₁' g₁' w₁ x)
    letI : Algebra
      (geometricStalkRing B S hS
        (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
      (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x))) :=
      (eqToHom (congrArg (fun z => geometricStalkRing B S hS (X := Y) z)
            ((congrArg (geometricPointMap f.hom)
                (congrArg (fun m : X₁' ⟶ X => geometricPointMap m.hom x) ha').symm).trans
              (congrArg
                (fun m : X₁ ⟶ Y => geometricPointMap m.hom (geometricPointMap g₁'.hom x))
                hfa).symm)) ≫ stalkStructureMap B S hS b
          (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x))).hom.toAlgebra
    letI : Algebra
      (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)) :=
      (eqToHom (congrArg (fun z => geometricStalkRing B S hS (X := X) z)
            (congrArg (fun m : X₁' ⟶ X => geometricPointMap m.hom x) ha').symm) ≫
          stalkStructureMap B S hS a (geometricPointMap g₁'.hom x)).hom.toAlgebra
    letI : Algebra
      (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap f₁'.hom x)) :=
      (eqToHom (congrArg (fun z => geometricStalkRing B S hS (X := Y') z)
            (congrArg (fun m : X₁' ⟶ Y' => geometricPointMap m.hom x) hfc).symm) ≫
          stalkStructureMap B S hS c (geometricPointMap f₁'.hom x)).hom.toAlgebra
    letI : Algebra (geometricStalkRing B S hS (geometricPointMap a'.hom x))
      (geometricStalkRing B S hS x) := (stalkStructureMap B S hS a' x).hom.toAlgebra
    letI : Algebra
      (geometricStalkRing B S hS
        (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
      (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)) :=
      ((eqToHom
            (congrArg (fun z => geometricStalkRing B S hS (X := X) z)
              (congrArg (fun m : X₁' ⟶ X => geometricPointMap m.hom x) ha').symm) ≫
            stalkStructureMap B S hS a (geometricPointMap g₁'.hom x)).hom.comp
          (stalkStructureMap B S hS f
            (geometricPointMap g'.hom (geometricPointMap a'.hom x))).hom).toAlgebra
    haveI : IsScalarTower
      (geometricStalkRing B S hS
        (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
      (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower
      (geometricStalkRing B S hS
        (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
      (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)) := IsScalarTower.of_algebraMap_eq'
      (stalkStructureMap_cube_left B S hS f b f₁ a hfa.symm (geometricPointMap g₁'.hom x)
          (geometricPointMap g'.hom (geometricPointMap a'.hom x))
          (congrArg (fun m : X₁' ⟶ X => geometricPointMap m.hom x) ha').symm
          ((congrArg (geometricPointMap f.hom)
              (congrArg (fun m : X₁' ⟶ X => geometricPointMap m.hom x) ha').symm).trans
            (congrArg
              (fun m : X₁ ⟶ Y => geometricPointMap m.hom (geometricPointMap g₁'.hom x)) hfa).symm))
    letI : Algebra
      (geometricStalkRing B S hS
        (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
      (geometricStalkRing B S hS (geometricPointMap f₁'.hom x)) :=
      ((eqToHom
            (congrArg (fun z => geometricStalkRing B S hS (X := Y') z)
              (congrArg (fun m : X₁' ⟶ Y' => geometricPointMap m.hom x) hfc).symm) ≫
            stalkStructureMap B S hS c (geometricPointMap f₁'.hom x)).hom.comp
          (geometricBaseStalkMap B S hS f g f' g' w (geometricPointMap a'.hom x)).hom).toAlgebra
    haveI : IsScalarTower
      (geometricStalkRing B S hS
        (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
      (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap f₁'.hom x)) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower
      (geometricStalkRing B S hS
        (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
      (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap f₁'.hom x)) := IsScalarTower.of_algebraMap_eq'
      (stalkStructureMap_cube B S hS g b g₁ c hgb.symm (geometricPointMap f₁'.hom x)
          (geometricPointMap f'.hom (geometricPointMap a'.hom x))
          (congrArg (fun m : X₁' ⟶ Y' => geometricPointMap m.hom x) hfc).symm
        (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x))
          (geometricPointMap_square B S hS f₁ g₁ f₁' g₁' w₁ x)
        (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
          (geometricPointMap_square B S hS f g f' g' w (geometricPointMap a'.hom x))
          ((congrArg (geometricPointMap f.hom)
              (congrArg (fun m : X₁' ⟶ X => geometricPointMap m.hom x) ha').symm).trans
            (congrArg
              (fun m : X₁ ⟶ Y => geometricPointMap m.hom (geometricPointMap g₁'.hom x)) hfa).symm))
    letI : Algebra
      (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
      (geometricStalkRing B S hS x) :=
      ((stalkStructureMap B S hS a' x).hom.comp
          (stalkStructureMap B S hS g' (geometricPointMap a'.hom x)).hom).toAlgebra
    haveI : IsScalarTower
      (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap a'.hom x)) (geometricStalkRing B S hS x) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower
      (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)) (geometricStalkRing B S hS x) :=
      IsScalarTower.of_algebraMap_eq'
      (stalkStructureMap_square B S hS g' a g₁' a' ha'.symm x)
    letI : Algebra
      (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
      (geometricStalkRing B S hS x) :=
      ((stalkStructureMap B S hS a' x).hom.comp
          (stalkStructureMap B S hS f' (geometricPointMap a'.hom x)).hom).toAlgebra
    haveI : IsScalarTower
      (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap a'.hom x)) (geometricStalkRing B S hS x) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower
      (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
      (geometricStalkRing B S hS (geometricPointMap f₁'.hom x)) (geometricStalkRing B S hS x) :=
      IsScalarTower.of_algebraMap_eq'
      (stalkStructureMap_square B S hS f' c f₁' a' hfc.symm x)
    IsIso (canonicalGeometricStalkBaseChangeCohomologyMap B S hS f g f' g' w
        (geometricPointMap a'.hom x) K K' φ n) ↔
      IsIso (ringBaseChangeCohomologyMap
          (R := geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
          (A := geometricStalkRing B S hS (geometricPointMap g₁'.hom x))
          (R' := geometricStalkRing B S hS (geometricPointMap f₁'.hom x))
          (A' := geometricStalkRing B S hS x)
        ((dext (algebraMap
                (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
                (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)))).obj
            ((geometricDerivedStalk B S hS
                (geometricPointMap g'.hom (geometricPointMap a'.hom x))).obj K))
        ((dext (algebraMap (geometricStalkRing B S hS (geometricPointMap a'.hom x))
                (geometricStalkRing B S hS x))).obj
            ((geometricDerivedStalk B S hS (geometricPointMap a'.hom x)).obj K'))
        (extendScalarsBaseChangeHom
            (A := geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
            (A' := geometricStalkRing B S hS (geometricPointMap a'.hom x))
            (A₁ := geometricStalkRing B S hS (geometricPointMap g₁'.hom x))
            (A₁' := geometricStalkRing B S hS x)
          ((geometricDerivedStalk B S hS
                (geometricPointMap g'.hom (geometricPointMap a'.hom x))).obj K)
            ((geometricDerivedStalk B S hS (geometricPointMap a'.hom x)).obj K')
          ((derivedPullbackGeometricStalkMap g' (geometricPointMap a'.hom x)).app K ≫
            (geometricDerivedStalk B S hS (geometricPointMap a'.hom x)).map φ)) n) := by
  have hA := (congrArg (fun m : X₁' ⟶ X => geometricPointMap m.hom x) ha').symm
  have hC := (congrArg (fun m : X₁' ⟶ Y' => geometricPointMap m.hom x) hfc).symm
  have hB := (congrArg (geometricPointMap f.hom) hA).trans
    (congrArg (fun m : X₁ ⟶ Y => geometricPointMap m.hom (geometricPointMap g₁'.hom x)) hfa).symm
  let : Algebra
    (geometricStalkRing B S hS
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
    (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x))) :=
    (stalkStructureMap B S hS f
        (geometricPointMap g'.hom (geometricPointMap a'.hom x))).hom.toAlgebra
  let : Algebra
    (geometricStalkRing B S hS
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
    (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x))) :=
    (geometricBaseStalkMap B S hS f g f' g' w (geometricPointMap a'.hom x)).hom.toAlgebra
  let : Algebra
    (geometricStalkRing B S hS
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
    (geometricStalkRing B S hS (geometricPointMap a'.hom x)) :=
    ((stalkStructureMap B S hS g' (geometricPointMap a'.hom x)).hom.comp
        (stalkStructureMap B S hS f
          (geometricPointMap g'.hom (geometricPointMap a'.hom x))).hom).toAlgebra
  let : Algebra (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap a'.hom x)) :=
    (stalkStructureMap B S hS g' (geometricPointMap a'.hom x)).hom.toAlgebra
  let : Algebra (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap a'.hom x)) :=
    (stalkStructureMap B S hS f' (geometricPointMap a'.hom x)).hom.toAlgebra
  have : IsScalarTower
    (geometricStalkRing B S hS
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
    (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap a'.hom x)) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower
    (geometricStalkRing B S hS
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
    (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap a'.hom x)) :=
    IsScalarTower.of_algebraMap_eq'
      (stalkStructureMap_square B S hS f g f' g' w (geometricPointMap a'.hom x))
  let : Algebra (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)) :=
    (stalkStructureMap B S hS f₁ (geometricPointMap g₁'.hom x)).hom.toAlgebra
  let : Algebra (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap f₁'.hom x)) :=
    (geometricBaseStalkMap B S hS f₁ g₁ f₁' g₁' w₁ x).hom.toAlgebra
  let : Algebra (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
    (geometricStalkRing B S hS x) :=
    ((stalkStructureMap B S hS g₁' x).hom.comp
        (stalkStructureMap B S hS f₁ (geometricPointMap g₁'.hom x)).hom).toAlgebra
  let : Algebra (geometricStalkRing B S hS (geometricPointMap g₁'.hom x))
    (geometricStalkRing B S hS x) := (stalkStructureMap B S hS g₁' x).hom.toAlgebra
  let : Algebra (geometricStalkRing B S hS (geometricPointMap f₁'.hom x))
    (geometricStalkRing B S hS x) := (stalkStructureMap B S hS f₁' x).hom.toAlgebra
  have : IsScalarTower
    (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)) (geometricStalkRing B S hS x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower
    (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap f₁'.hom x)) (geometricStalkRing B S hS x) :=
    IsScalarTower.of_algebraMap_eq' (stalkStructureMap_square B S hS f₁ g₁ f₁' g₁' w₁ x)
  let : Algebra
    (geometricStalkRing B S hS
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
    (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x))) :=
    (eqToHom (congrArg (fun z => geometricStalkRing B S hS (X := Y) z)
          hB) ≫ stalkStructureMap B S hS b
        (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x))).hom.toAlgebra
  let : Algebra (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)) :=
    (eqToHom (congrArg (fun z => geometricStalkRing B S hS (X := X) z)
          hA) ≫
        stalkStructureMap B S hS a (geometricPointMap g₁'.hom x)).hom.toAlgebra
  let : Algebra (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap f₁'.hom x)) :=
    (eqToHom (congrArg (fun z => geometricStalkRing B S hS (X := Y') z)
          hC) ≫
        stalkStructureMap B S hS c (geometricPointMap f₁'.hom x)).hom.toAlgebra
  let : Algebra (geometricStalkRing B S hS (geometricPointMap a'.hom x))
    (geometricStalkRing B S hS x) := (stalkStructureMap B S hS a' x).hom.toAlgebra
  let : Algebra
    (geometricStalkRing B S hS
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
    (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)) :=
    ((eqToHom
          (congrArg (fun z => geometricStalkRing B S hS (X := X) z)
            hA) ≫
          stalkStructureMap B S hS a (geometricPointMap g₁'.hom x)).hom.comp
        (stalkStructureMap B S hS f
          (geometricPointMap g'.hom (geometricPointMap a'.hom x))).hom).toAlgebra
  have : IsScalarTower
    (geometricStalkRing B S hS
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
    (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower
    (geometricStalkRing B S hS
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
    (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)) := IsScalarTower.of_algebraMap_eq'
    (stalkStructureMap_cube_left B S hS f b f₁ a hfa.symm (geometricPointMap g₁'.hom x)
        (geometricPointMap g'.hom (geometricPointMap a'.hom x))
        hA
        hB)
  let : Algebra
    (geometricStalkRing B S hS
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
    (geometricStalkRing B S hS (geometricPointMap f₁'.hom x)) :=
    ((eqToHom
          (congrArg (fun z => geometricStalkRing B S hS (X := Y') z)
            hC) ≫
          stalkStructureMap B S hS c (geometricPointMap f₁'.hom x)).hom.comp
        (geometricBaseStalkMap B S hS f g f' g' w (geometricPointMap a'.hom x)).hom).toAlgebra
  have : IsScalarTower
    (geometricStalkRing B S hS
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
    (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap f₁'.hom x)) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower
    (geometricStalkRing B S hS
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
    (geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap f₁'.hom x)) := IsScalarTower.of_algebraMap_eq'
    (stalkStructureMap_cube B S hS g b g₁ c hgb.symm (geometricPointMap f₁'.hom x)
        (geometricPointMap f'.hom (geometricPointMap a'.hom x))
        hC
      (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x))
        (geometricPointMap_square B S hS f₁ g₁ f₁' g₁' w₁ x)
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
        (geometricPointMap_square B S hS f g f' g' w (geometricPointMap a'.hom x))
        hB)
  let : Algebra (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
    (geometricStalkRing B S hS x) :=
    ((stalkStructureMap B S hS a' x).hom.comp
        (stalkStructureMap B S hS g' (geometricPointMap a'.hom x)).hom).toAlgebra
  have : IsScalarTower
    (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap a'.hom x)) (geometricStalkRing B S hS x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower
    (geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap g₁'.hom x)) (geometricStalkRing B S hS x) :=
    IsScalarTower.of_algebraMap_eq'
    (stalkStructureMap_square B S hS g' a g₁' a' ha'.symm x)
  let : Algebra (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
    (geometricStalkRing B S hS x) :=
    ((stalkStructureMap B S hS a' x).hom.comp
        (stalkStructureMap B S hS f' (geometricPointMap a'.hom x)).hom).toAlgebra
  have : IsScalarTower
    (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap a'.hom x)) (geometricStalkRing B S hS x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower
    (geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
    (geometricStalkRing B S hS (geometricPointMap f₁'.hom x)) (geometricStalkRing B S hS x) :=
    IsScalarTower.of_algebraMap_eq'
    (stalkStructureMap_square B S hS f' c f₁' a' hfc.symm x)
  exact isIso_ringBaseChangeCohomologyMap_iff_of_bijective
    (R := geometricStalkRing B S hS
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x))))
    (A := geometricStalkRing B S hS (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
    (R' := geometricStalkRing B S hS (geometricPointMap f'.hom (geometricPointMap a'.hom x)))
    (A' := geometricStalkRing B S hS (geometricPointMap a'.hom x))
      (R₁ := geometricStalkRing B S hS (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x)))
      (A₁ := geometricStalkRing B S hS (geometricPointMap g₁'.hom x))
      (R₁' := geometricStalkRing B S hS (geometricPointMap f₁'.hom x))
      (A₁' := geometricStalkRing B S hS x)
    (bijective_eqToHom_comp_stalkStructureMap B S hS b hbe
        (geometricPointMap f₁.hom (geometricPointMap g₁'.hom x))
      (geometricPointMap f.hom (geometricPointMap g'.hom (geometricPointMap a'.hom x)))
        hB)
    (bijective_eqToHom_comp_stalkStructureMap B S hS a hae (geometricPointMap g₁'.hom x)
        (geometricPointMap g'.hom (geometricPointMap a'.hom x))
      hA)
    (bijective_eqToHom_comp_stalkStructureMap B S hS c hce (geometricPointMap f₁'.hom x)
      (geometricPointMap f'.hom (geometricPointMap a'.hom x))
        hC)
    (bijective_stalkStructureMap_of_isEtale B S hS a' hae' x) _ _ _ n

end Square

end AlgebraicGeometry.Space

end
