module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Ring.ULift
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections of a scheme over an affine base, as an algebra

A morphism of schemes `g : X ⟶ Spec R` makes the sections of `𝒪_X` over every open an
`R`-algebra: the ring map is the global-sections comparison `R ≅ Γ(Spec R, ⊤)` followed by
`g.appLE ⊤ U`. If `R` is itself an algebra over a ring `k`, composing gives `Γ(X, U)` the
structure of a `k`-algebra; the case `k = ℚ` gives the sections of a scheme over a rational base
the structure of a `ℚ`-algebra.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.sectionsRingMap`: the ring map `R ⟶ Γ(X, U)` attached to
  `g : X ⟶ Spec R` and an open `U`.
* `AlgebraicGeometry.Scheme.Hom.sectionsAlgebraOfBase`: `Γ(X, U)` as a `k`-algebra, for `k` a
  base ring of `R`; and `sectionsRatAlgebra`, the case `k = ℚ`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.sectionsRingMap_comp_map`: the ring map is compatible with
  restriction to a smaller open.
* `AlgebraicGeometry.Scheme.Hom.sectionsRingMap_comp`: the ring map of a composite
  `X ⟶ Y ⟶ Spec R` is the ring map of `Y ⟶ Spec R` followed by the comparison of sections.

## Implementation notes

`Algebra k ↥Γ(X, U)` is produced by a `def` rather than an `instance`: a scheme can map to
several affine schemes, so an instance would make the algebra structure on `Γ(X, U)` ambiguous.

## References

* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1) — morphisms to an affine
  scheme are ring maps on global sections.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} {R : CommRingCat.{u}}

/-- **The ring map `R ⟶ Γ(X, U)` attached to a morphism `g : X ⟶ Spec R` and an open `U`**: the
inverse of the global-sections comparison of `Spec R`, followed by `g` on sections from `⊤` down
to `U`. -/
def sectionsRingMap (g : X ⟶ Spec R) (U : X.Opens) : R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso R).inv ≫ g.appLE ⊤ U (by simp)

/-- **The ring map on sections is compatible with restriction.** Restricting the image of `r : R`
over `U` to a smaller open `V` gives the image of `r` over `V`. -/
@[reassoc]
theorem sectionsRingMap_comp_map (g : X ⟶ Spec R) {U V : X.Opens} (i : op U ⟶ op V) :
    sectionsRingMap g U ≫ X.presheaf.map i = sectionsRingMap g V := by
  rw [sectionsRingMap, sectionsRingMap, Category.assoc, appLE_map]

/-- The ring map on sections, read on an element, is compatible with restriction. -/
theorem sectionsRingMap_map_apply (g : X ⟶ Spec R) {U V : X.Opens} (i : op U ⟶ op V) (r : ↥R) :
    (X.presheaf.map i).hom ((sectionsRingMap g U).hom r) = (sectionsRingMap g V).hom r :=
  congrArg (fun k : R ⟶ Γ(X, V) ↦ k.hom r) (sectionsRingMap_comp_map g i)

/-- **The ring map of a composite.** For `f : X ⟶ Y` and `g : Y ⟶ Spec R`, the structure `X`
inherits over `U` is the one `Y` carries over an open containing the image, transported by `f` on
sections. -/
theorem sectionsRingMap_comp (f : X ⟶ Y) (g : Y ⟶ Spec R) {V : Y.Opens} {U : X.Opens}
    (e : U ≤ f ⁻¹ᵁ V) :
    sectionsRingMap g V ≫ f.appLE V U e = sectionsRingMap (f ≫ g) U := by
  rw [sectionsRingMap, sectionsRingMap, Category.assoc, appLE_comp_appLE]

/-- **The sections of `X` over `U` as a `k`-algebra**, for a morphism `X ⟶ Spec R` and a base
ring `k` of `R`. -/
@[instance_reducible]
def sectionsAlgebraOfBase (k : Type v) [CommRing k] [Algebra k ↥R] (g : X ⟶ Spec R)
    (U : X.Opens) : Algebra k ↥Γ(X, U) :=
  ((sectionsRingMap g U).hom.comp (algebraMap k ↥R)).toAlgebra

/-- **The sections of a scheme over a rational base are a `ℚ`-algebra, over every open.**

`ℚ` is taken in universe `0` and `R` in universe `u`, so a rational base is a morphism to
`Spec` of a `CommRingCat.{u}` which is a `ℚ`-algebra; `CommRingCat.of (ULift.{u} ℚ)` is one. -/
@[instance_reducible]
def sectionsRatAlgebra [Algebra ℚ ↥R] (g : X ⟶ Spec R) (U : X.Opens) :
    Algebra ℚ ↥Γ(X, U) :=
  sectionsAlgebraOfBase ℚ g U

/-- The `ℚ`-algebra structure on sections over a rational base, read on the algebra map: it is
the ring map on sections applied to the image of a rational number in `R`. -/
theorem algebraMap_sectionsRatAlgebra [Algebra ℚ ↥R] (g : X ⟶ Spec R) (U : X.Opens) (q : ℚ) :
    letI := sectionsRatAlgebra g U
    algebraMap ℚ ↥Γ(X, U) q = (sectionsRingMap g U).hom (algebraMap ℚ ↥R q) :=
  rfl

end AlgebraicGeometry.Scheme.Hom

end
