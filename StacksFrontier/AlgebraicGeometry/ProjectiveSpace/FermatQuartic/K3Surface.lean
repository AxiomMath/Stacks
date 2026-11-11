module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.FermatQuartic.Canonical
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.FermatQuartic.Cohomology
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.FermatQuartic.Differentials
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.FermatQuartic.Geometry
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.FermatQuartic.Smooth
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.FermatQuartic.Tangent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SmoothEquidimensionalOverField

/-!
# The Fermat quartic is a K3 surface

Let `k` be a field in which `2 ≠ 0` and let `X = V(x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴) ⊆ 𝐏³_k` be the Fermat
quartic. This file assembles the facts proved in the other files of this folder into the
unconditional statements that make `X` a K3 surface:

* `X` is smooth and projective over `k`, of relative dimension two, integral and nonempty;
* `H¹(X, 𝒪_X) = 0` (`AlgebraicGeometry.FermatQuartic.isZero_cohomology_one_unit`, which needs no
  hypothesis on `k`);
* `ω_X ≅ 𝒪_X`;
* `H⁰(X, Ω_{X/k}) = 0`;
* `H²(X, T_X) = Ext²(Ω_{X/k}, 𝒪_X) = 0`, and likewise `Ext²(Ω_{X/k}, ω_X) = 0`.

## Main results

* `AlgebraicGeometry.FermatQuartic.smoothOfRelativeDimension_toSpec`: `X ⟶ Spec k` is smooth of
  relative dimension two.
* `AlgebraicGeometry.FermatQuartic.isIntegral_fermatQuartic`: `X` is integral.
* `AlgebraicGeometry.FermatQuartic.nonempty_dualizingModule_iso_unit`: `ω_X ≅ 𝒪_X`.
* `AlgebraicGeometry.FermatQuartic.subsingleton_unit_hom_relativeDifferentials`:
  `H⁰(X, Ω_{X/k}) = 0`.
* `AlgebraicGeometry.FermatQuartic.subsingleton_ext_relativeDifferentials_unit` and
  `AlgebraicGeometry.FermatQuartic.subsingleton_ext_relativeDifferentials_dualizingModule`:
  `Ext²(Ω_{X/k}, 𝒪_X) = 0` and `Ext²(Ω_{X/k}, ω_X) = 0`.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u

namespace AlgebraicGeometry.FermatQuartic

variable (k : Type u) [Field k] [NeZero (2 : k)]

/-- **The Fermat quartic is smooth of relative dimension two over `k`**: it is smooth, and it is
equidimensional of dimension two. -/
instance smoothOfRelativeDimension_toSpec : SmoothOfRelativeDimension 2 (toSpec k) :=
  smoothOfRelativeDimension_of_equidimensional k (toSpec k) (equidimensional_fermatQuartic k) 2
    (topologicalKrullDim_fermatQuartic k)

/-- **The Fermat quartic is integral**: it is connected and smooth over `k`. -/
instance isIntegral_fermatQuartic : IsIntegral (fermatQuartic k) :=
  isIntegral_fermatQuartic_of_smooth k inferInstance

/-- **`ω_X ≅ 𝒪_X`**: the dualizing module of the Fermat quartic is trivial. -/
theorem nonempty_dualizingModule_iso_unit :
    Nonempty (Stacks.Duality.dualizingModule (toSpec k) ≅
      SheafOfModules.unit (fermatQuartic k).ringCatSheaf) :=
  nonempty_dualizingModule_iso_unit_of_smooth k

/-- **`H⁰(X, Ω_{X/k}) = 0`**: every morphism `𝒪_X ⟶ Ω_{X/k}` is zero. -/
theorem subsingleton_unit_hom_relativeDifferentials :
    Subsingleton (SheafOfModules.unit (fermatQuartic k).ringCatSheaf ⟶
      Scheme.Hom.relativeDifferentials (toSpec k)) :=
  subsingleton_unit_hom_relativeDifferentials_of_smooth k inferInstance

/-- **`Ext²(Ω_{X/k}, ω_X) = 0`** for the Fermat quartic. -/
theorem subsingleton_ext_relativeDifferentials_dualizingModule :
    Subsingleton (Ext.{u} (Scheme.Hom.relativeDifferentials (toSpec k))
      (Stacks.Duality.dualizingModule (toSpec k)) 2) :=
  subsingleton_ext_relativeDifferentials_dualizingModule_of_vanishing k
    (equidimensional_fermatQuartic k) (topologicalKrullDim_fermatQuartic k)
    (subsingleton_unit_hom_relativeDifferentials k)

/-- **`H²(X, T_X) = Ext²(Ω_{X/k}, 𝒪_X) = 0`** for the Fermat quartic. -/
theorem subsingleton_ext_relativeDifferentials_unit :
    Subsingleton (Ext.{u} (Scheme.Hom.relativeDifferentials (toSpec k))
      (SheafOfModules.unit (fermatQuartic k).ringCatSheaf) 2) :=
  subsingleton_ext_relativeDifferentials_unit_of_vanishing k
    (equidimensional_fermatQuartic k) (topologicalKrullDim_fermatQuartic k)
    (subsingleton_unit_hom_relativeDifferentials k) (nonempty_dualizingModule_iso_unit k)

end AlgebraicGeometry.FermatQuartic

end
