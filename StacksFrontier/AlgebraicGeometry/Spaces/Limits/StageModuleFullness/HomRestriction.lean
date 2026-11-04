module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleHomRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence

/-!
# Restriction of morphisms of inverse images as conjugation by the comparison triangle

The restriction `AlgebraicGeometry.Space.moduleHomRestrict` of a morphism `p^*M ⟶ p^*N` along
`g : Q ⟶ P` is conjugation by the comparison `AlgebraicGeometry.Space.modulePullbackTriangle`.

## Main results

* `AlgebraicGeometry.Space.StageFullness.moduleHomRestrict_eq_triangle`: the restriction is
  conjugation by the comparison.
* `AlgebraicGeometry.Space.StageFullness.moduleHomRestrict_eq_of_map_eq`: a morphism whose inverse
  image is the conjugate of `φ` by the comparison restricts to `φ`.
* `AlgebraicGeometry.Space.StageFullness.map_eq_of_moduleHomRestrict_eq`: a morphism which
  restricts to `φ` has as inverse image the conjugate of `φ` by the comparison.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.StageFullness

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {Z : AlgebraicSpaces B S hS} {M N : Modules.{u, u} B S hS Z.1 Z.2}

/-- **The restriction is conjugation by the comparison
`AlgebraicGeometry.Space.modulePullbackTriangle`.** -/
theorem moduleHomRestrict_eq_triangle {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z)
    (q : Q ⟶ Z) (h : g ≫ p = q)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    moduleHomRestrict M N g p q h x =
      (modulePullbackTriangle B S hS h).hom.app M ≫ (modulePullback B S hS g).map x ≫
        (modulePullbackTriangle B S hS h).inv.app N := by
  subst h
  rw [moduleHomRestrict_rfl, modulePullbackTriangle_rfl]
  rfl

/-- A morphism whose inverse image is the conjugate of `φ` by
`AlgebraicGeometry.Space.modulePullbackTriangle` restricts to `φ`. -/
theorem moduleHomRestrict_eq_of_map_eq {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z)
    (q : Q ⟶ Z) (h : g ≫ p = q)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N)
    (φ : (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS q).obj N)
    (hx : (modulePullback B S hS g).map x =
      (modulePullbackTriangle B S hS h).inv.app M ≫ φ ≫
        (modulePullbackTriangle B S hS h).hom.app N) :
    moduleHomRestrict M N g p q h x = φ := by
  rw [moduleHomRestrict_eq_triangle, hx]
  simp

/-- A morphism which restricts to `φ` has as inverse image the conjugate of `φ` by
`AlgebraicGeometry.Space.modulePullbackTriangle`. -/
theorem map_eq_of_moduleHomRestrict_eq {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z)
    (q : Q ⟶ Z) (h : g ≫ p = q)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N)
    (φ : (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS q).obj N)
    (hx : moduleHomRestrict M N g p q h x = φ) :
    (modulePullback B S hS g).map x =
      (modulePullbackTriangle B S hS h).inv.app M ≫ φ ≫
        (modulePullbackTriangle B S hS h).hom.app N := by
  rw [← hx, moduleHomRestrict_eq_triangle]
  simp

end AlgebraicGeometry.Space.StageFullness

end
