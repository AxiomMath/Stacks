module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The higher direct images of a morphism of `R`-schemes are `R`-linear

A sheaf of modules on a scheme `Z` over `Spec R` carries an action of `R` on each of its modules
of sections, pulled back from the base, and this makes the category of sheaves of modules on `Z`
an `R`-linear category: that is `AlgebraicGeometry.modulesLinear`. Pushforward along a morphism
of `R`-schemes is `R`-linear for that structure
(`AlgebraicGeometry.over_pushforward_linear`), and the right derived functors of an `R`-linear
functor are `R`-linear (`CategoryTheory.Functor.linear_rightDerived`). This file composes those
two facts and transports the result to the `ℤ`-indexed derived functors
`CategoryTheory.Functor.rightDerivedPlus`, in which the statements about higher direct images in
this directory are phrased.

What the conclusion says concretely is that `R^n f_*` carries multiplication by `f^♯ r` on a
module on `X` to multiplication by `r` on its `n`-th higher direct image. That is exactly the
`𝒪`-linearity of a right derived functor which the implementation notes of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/TensorComparisonZero.lean` record as the
second input needed to build the canonical tensor map of [Stacks, Tag 0EX3] (b) out of a
bilinear family on sections: `Stacks.BilinearMap` asks for linearity in each variable, and
linearity in the section of the module on the base is this statement.

## Main results

All of the following live in the namespace
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage`.

* `linear_rightDerived_pushforward` and `linear_rightDerivedPlus_pushforward`: **the right
  derived functors of the pushforward along a morphism of `R`-schemes are `R`-linear**, for
  Mathlib's `ℕ`-indexed and `ℤ`-indexed derived functors respectively.
* `rightDerivedPlus_pushforward_map_baseScalar`: **the higher direct image of multiplication by
  a base scalar is multiplication by that scalar**, with no linear structure appearing in the
  statement.
* `baseRingToSections_toSpecΓ` and `baseRingToSections_comp_toSpecΓ`: over the spectrum of its
  own global sections, the scalar by which a scheme's canonical `R`-structure multiplies is the
  global section itself, and along a morphism it is its pullback.
* `rightDerivedPlus_pushforward_map_baseScalar_toSpecΓ`: the same statement for an arbitrary
  morphism of schemes and `r` a global section of the structure sheaf of the target, which is
  the form a bilinear family on sections consumes.

## Implementation notes

The linear structure is not an instance and cannot be: `AlgebraicGeometry.modulesLinear`
depends on a chosen morphism to `Spec R`, and a scheme can lie over `Spec R` in many ways. So it
is introduced with `letI` inside each proof, exactly as `AlgebraicGeometry.over_pushforward_linear`
does, and the statements that are meant to be used elsewhere —
`rightDerivedPlus_pushforward_map_baseScalar` and its specialisation — mention
`AlgebraicGeometry.baseScalar` rather than a scalar action, so that no instance has to be in
scope to read them.

For the specialisation the base is `Spec Γ(Y, ⊤)` and the structure morphism is
`AlgebraicGeometry.Scheme.toSpecΓ`. `AlgebraicGeometry.Scheme.toSpecΓ_appTop` identifies its
value on global sections with `AlgebraicGeometry.Scheme.ΓSpecIso`, which is what makes the base
scalar attached to `Z.toSpecΓ` the global section itself rather than some transport of it.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.SchemeHigherDirectImage

attribute [local instance] HasDerivedCategory.standard

noncomputable section

section Over

variable (R : Type u) [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

/-- **The right derived functors of the pushforward along a morphism of `R`-schemes are
`R`-linear.** The pushforward itself is `R`-linear by
`AlgebraicGeometry.over_pushforward_linear`, and
`CategoryTheory.Functor.linear_rightDerived` promotes that to its right derived functors. -/
theorem linear_rightDerived_pushforward (n : ℕ) :
    letI := AlgebraicGeometry.modulesLinear R X
    letI := AlgebraicGeometry.modulesLinear R Y
    ((Scheme.Modules.pushforward f.left).rightDerived n).Linear R := by
  let := AlgebraicGeometry.modulesLinear R X
  let := AlgebraicGeometry.modulesLinear R Y
  let : (Scheme.Modules.pushforward f.left).Linear R :=
    AlgebraicGeometry.over_pushforward_linear R f
  infer_instance

/-- **The `ℤ`-indexed right derived functors of the pushforward along a morphism of `R`-schemes
are `R`-linear.** The comparison `Stacks.DerivedIndexing.rightDerivedIso` of the two indexings is
an isomorphism of functors in each non-negative degree, and linearity transports along an
isomorphism of functors. -/
theorem linear_rightDerivedPlus_pushforward (n : ℕ) :
    letI := AlgebraicGeometry.modulesLinear R X
    letI := AlgebraicGeometry.modulesLinear R Y
    ((Scheme.Modules.pushforward f.left).rightDerivedPlus (n : ℤ)).Linear R := by
  let := AlgebraicGeometry.modulesLinear R X
  let := AlgebraicGeometry.modulesLinear R Y
  let := linear_rightDerived_pushforward R f n
  exact Functor.linear_of_iso R
    (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f.left) n)

/-- **The higher direct image of multiplication by a base scalar is multiplication by that
scalar.** For a morphism `f` of `R`-schemes, a module `M` on the source and `r : R`, the `n`-th
higher direct image of the endomorphism "multiply by `r`" of `M` is the endomorphism "multiply by
`r`" of `R^n f_* M`.

No linear structure appears in the statement: `AlgebraicGeometry.baseScalar` is the
multiplication operator itself, so this is readable and usable without the `R`-linear structure
on either category being in scope. -/
theorem rightDerivedPlus_pushforward_map_baseScalar (n : ℕ) (r : R) (M : X.left.Modules) :
    ((Scheme.Modules.pushforward f.left).rightDerivedPlus (n : ℤ)).map
        ((AlgebraicGeometry.baseScalar R X r).app M) =
      (AlgebraicGeometry.baseScalar R Y r).app
        (((Scheme.Modules.pushforward f.left).rightDerivedPlus (n : ℤ)).obj M) := by
  let := AlgebraicGeometry.modulesLinear R X
  let := AlgebraicGeometry.modulesLinear R Y
  let := linear_rightDerivedPlus_pushforward R f n
  have hX : (AlgebraicGeometry.baseScalar R X r).app M = r • 𝟙 M := (Category.comp_id _).symm
  have hY : (AlgebraicGeometry.baseScalar R Y r).app
      (((Scheme.Modules.pushforward f.left).rightDerivedPlus (n : ℤ)).obj M) =
      r • 𝟙 (((Scheme.Modules.pushforward f.left).rightDerivedPlus (n : ℤ)).obj M) :=
    (Category.comp_id _).symm
  rw [hX, hY]
  exact (Functor.linear_iff R
    ((Scheme.Modules.pushforward f.left).rightDerivedPlus (n : ℤ))).mp inferInstance M r

end Over

section Global

/-- The inverse of `ΓSpecIso` followed by the global sections map of `Z.toSpecΓ` is the identity. -/
private theorem ΓSpecIso_inv_comp_toSpecΓ_appTop (Z : Scheme.{u}) :
    (Scheme.ΓSpecIso (CommRingCat.of ↑Γ(Z, ⊤))).inv ≫ Z.toSpecΓ.appTop = 𝟙 _ := by
  rw [Scheme.toSpecΓ_appTop Z]
  exact Iso.inv_hom_id _

/-- **The base scalar of a scheme over the spectrum of its own global sections is the global
section itself.** `AlgebraicGeometry.Scheme.toSpecΓ_appTop` cancels the comparison
`AlgebraicGeometry.Scheme.ΓSpecIso` against its inverse, so no transport is left. -/
theorem baseRingToSections_toSpecΓ (Z : Scheme.{u}) (U : Z.Opensᵒᵖ) (r : Γ(Z, ⊤)) :
    AlgebraicGeometry.baseRingToSections ↑Γ(Z, ⊤)
        (Over.mk Z.toSpecΓ : Over (Spec (CommRingCat.of ↑Γ(Z, ⊤)))) U r =
      (Z.presheaf.map U.unop.leTop.op).hom r := by
  have h := ΓSpecIso_inv_comp_toSpecΓ_appTop Z
  simp only [AlgebraicGeometry.baseRingToSections, Over.mk_hom, h,
    CategoryTheory.Functor.map_id]
  rfl

/-- **Along a morphism, the base scalar of the global sections of the target is the pullback of
the global section.** This is `baseRingToSections_toSpecΓ` for the composite structure morphism
`f ≫ Y.toSpecΓ`. -/
theorem baseRingToSections_comp_toSpecΓ {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opensᵒᵖ)
    (r : Γ(Y, ⊤)) :
    AlgebraicGeometry.baseRingToSections ↑Γ(Y, ⊤)
        (Over.mk (f ≫ Y.toSpecΓ) : Over (Spec (CommRingCat.of ↑Γ(Y, ⊤)))) U r =
      (X.presheaf.map U.unop.leTop.op).hom (f.appTop r) := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of ↑Γ(Y, ⊤))).inv ≫ (f ≫ Y.toSpecΓ).appTop =
      f.appTop := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ΓSpecIso_inv_comp_toSpecΓ_appTop,
      Category.id_comp]
  simp only [AlgebraicGeometry.baseRingToSections, Over.mk_hom, h]
  rfl

/-- **The `n`-th higher direct image carries multiplication by `f^♯ r` to multiplication by
`r`**, for an arbitrary morphism of schemes `f : X ⟶ Y` and `r` a global section of the
structure sheaf of `Y`. The two multiplication operators are
`AlgebraicGeometry.baseScalar` for the canonical structure morphisms to
`Spec Γ(Y, ⊤)`, whose values on sections are computed by `baseRingToSections_comp_toSpecΓ` and
`baseRingToSections_toSpecΓ`.

This is the `𝒪`-linearity of a right derived functor: it is what makes a family of morphisms
`x ↦ R^n f_*(- ⊗ f^* s)` linear in the section `s`, hence a bilinear family on sections. -/
theorem rightDerivedPlus_pushforward_map_baseScalar_toSpecΓ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (r : Γ(Y, ⊤)) (M : X.Modules) :
    ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).map
        ((AlgebraicGeometry.baseScalar ↑Γ(Y, ⊤)
          (Over.mk (f ≫ Y.toSpecΓ) : Over (Spec (CommRingCat.of ↑Γ(Y, ⊤)))) r).app M) =
      (AlgebraicGeometry.baseScalar ↑Γ(Y, ⊤)
          (Over.mk Y.toSpecΓ : Over (Spec (CommRingCat.of ↑Γ(Y, ⊤)))) r).app
        (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj M) :=
  rightDerivedPlus_pushforward_map_baseScalar ↑Γ(Y, ⊤)
    (Over.homMk f : (Over.mk (f ≫ Y.toSpecΓ) : Over (Spec (CommRingCat.of ↑Γ(Y, ⊤)))) ⟶
      Over.mk Y.toSpecΓ) n r M

end Global

end

end Stacks.AlgebraicGeometry.SchemeHigherDirectImage

end
