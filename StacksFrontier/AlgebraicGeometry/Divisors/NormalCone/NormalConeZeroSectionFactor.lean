module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ZeroSectionFactor
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeFunctorial
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeZeroSection

/-!
# Factoring a morphism into a normal cone through its zero section

Let `D ⊆ X` be an effective Cartier divisor, so that the normal cone `C_DX` is a line bundle over
`D` with zero section `o : D ⟶ C_DX` (`Stacks.Conormal.normalConeZeroSection`). A step of
[Stacks, Tag 0FEB] asks for a morphism `m : T ⟶ C_DX` to factor through `o`, over a prescribed
morphism `g : T ⟶ D`.

This file reduces that factorization to a single equation between morphisms of
`𝒪_D`-modules. The reduction is an *equivalence*, so nothing is lost by passing to it.

## Main results

* `Stacks.Conormal.totalSpaceIsoNormalCone_inv_comp_totalSpaceToBase`: the inverse of the
  identification of the total space with the normal cone lies over `D`.
* `Stacks.Conormal.eq_comp_normalConeZeroSection_iff`: **a morphism `m : T ⟶ C_DX` lying over
  `g : T ⟶ D` equals `g ≫ o` if and only if the module component of the pair attached to `m` by
  the functor of points of the total space vanishes.**

## Why this shape

Both `m` and `g ≫ o` are morphisms into the relative spectrum `C_DX` of the conormal graded
algebra, so [Stacks, Tag 01LV] turns their equality into an equality of relative-spectrum pairs
(`Stacks.RelativeSpec.pairToHom_injective`). A pair is a dependent sum — a morphism to the base
together with a map of algebra sheaves *whose type mentions that morphism* — and here the two
first components are equal but not syntactically so, which is why that comparison is not a
rewrite.

Routing instead through `Stacks.LineBundle.Situation.factorsThrough_zeroSection_iff`, the
criterion on the *total space* of the line bundle, removes the dependency: the right-hand side
below is an equation `φ = 0` between two morphisms of a single fixed module, and the morphism to
the base is pinned afterwards, by the plain composition identity `hbase` and the fact that `o`
splits the projection. So the remaining obligation carries no transport.

## References

* [Stacks Project, Tag 0FEB](https://stacks.math.columbia.edu/tag/0FEB)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Conormal

variable {X : Scheme.{u}} (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D]
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (normalBundleAlgebra D.subschemeι)]
  [(conormalAlgebraSheaf D.subschemeι).IsQuasicoherent]

/-- **The inverse of the identification of the total space of the conormal line bundle with the
normal cone lies over `D`**: it carries the projection of the total space to the projection
`C_DX ⟶ D` of the cone. This is
`Stacks.Conormal.totalSpaceIsoNormalCone_hom_comp_normalConeToBase` read through the inverse. -/
theorem totalSpaceIsoNormalCone_inv_comp_totalSpaceToBase :
    (totalSpaceIsoNormalCone D).inv ≫ (conormalSituation D).totalSpaceToBase =
      normalConeToBase D.subschemeι :=
  (Iso.inv_comp_eq _).mpr (totalSpaceIsoNormalCone_hom_comp_normalConeToBase D).symm

/-- **The zero section of the normal cone, read back on the total space of the conormal line
bundle, is the zero section of that line bundle.** -/
theorem normalConeZeroSection_comp_totalSpaceIsoNormalCone_inv :
    normalConeZeroSection D ≫ (totalSpaceIsoNormalCone D).inv = conormalZeroSection D :=
  (Category.assoc _ _ _).trans
    ((congrArg (conormalZeroSection D ≫ ·) (totalSpaceIsoNormalCone D).hom_inv_id).trans
      (Category.comp_id _))

/-- **A morphism into the normal cone of an effective Cartier divisor factors through the zero
section exactly when the module component of its pair vanishes.**

More precisely, let `m : T ⟶ C_DX` lie over `g : T ⟶ D`. Then `m = g ≫ o` if and only if the
morphism of `𝒪_D`-modules `𝒞_{D/X,1} ⟶ (m ≫ π)_* 𝒪_T` attached to `m` by the functor of points of
the total space of the conormal line bundle (`Stacks.LineBundle.Situation.totalSpaceHomEquiv`,
read through `Stacks.Conormal.totalSpaceIsoNormalCone`) is zero.

The right-hand side is an equation between two morphisms of one fixed module, so unlike the
comparison of the two relative-spectrum pairs it involves no dependent type. -/
theorem eq_comp_normalConeZeroSection_iff {T : Scheme.{u}} (m : T ⟶ normalCone D.subschemeι)
    (g : T ⟶ D.subscheme) (hbase : m ≫ normalConeToBase D.subschemeι = g) :
    m = g ≫ normalConeZeroSection D ↔
      ((conormalSituation D).totalSpaceHomEquiv T
        (m ≫ (totalSpaceIsoNormalCone D).inv)).2 = 0 := by
  rw [← (cancel_mono (totalSpaceIsoNormalCone D).inv), Category.assoc,
    normalConeZeroSection_comp_totalSpaceIsoNormalCone_inv,
    ← (conormalSituation D).factorsThrough_zeroSection_iff]
  refine ⟨fun hm => ⟨g, hm.symm⟩, fun ⟨g', hg'⟩ => ?_⟩
  have hgg : g' = g := by
    have := congrArg (· ≫ (conormalSituation D).totalSpaceToBase) hg'
    simp only [Category.assoc, (conormalSituation D).zeroSection_comp_totalSpaceToBase,
      totalSpaceIsoNormalCone_inv_comp_totalSpaceToBase, Category.comp_id] at this
    exact this.trans hbase
  exact hgg ▸ hg'.symm

/-! ### The instance a nested pair of divisors needs -/

section Nested

variable {X : Scheme.{u}} (DY : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor DY]
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (normalBundleAlgebra DY.subschemeι)]
  [(conormalAlgebraSheaf DY.subschemeι).IsQuasicoherent]
  {Z : Scheme.{u}} (iZ : Z ⟶ X) [IsClosedImmersion iZ]
  [(conormalAlgebraSheaf iZ).IsQuasicoherent]
  (f : Z ⟶ DY.subscheme) [IsClosedImmersion f]
  [(conormalAlgebraSheaf f).IsQuasicoherent] (hf : f ≫ DY.subschemeι = iZ)

omit [Stacks.Divisors.IsEffectiveCartierDivisor DY]
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (normalBundleAlgebra DY.subschemeι)] in
/-- **The composite `C_ZY ⟶ C_ZX ⟶ C_YX` of a nested pair `Z ⊆ Y ⊆ X` lies over `Z ⟶ Y`**: its
composite with the projection `C_YX ⟶ Y` is the projection `C_ZY ⟶ Z` followed by `Z ⟶ Y`. Both
factors lie over their base morphisms, by
`Stacks.Conormal.normalConeMapOfSquare_toBase` and
`Stacks.Conormal.normalConeMapOfFactorization_toBase`. -/
theorem normalConeNested_comp_normalConeToBase :
    (normalConeMapOfSquare f iZ (𝟙 Z) DY.subschemeι ((Category.id_comp iZ).trans hf.symm) ≫
          normalConeMapOfFactorization iZ DY.subschemeι f hf) ≫
        normalConeToBase DY.subschemeι =
      normalConeToBase f ≫ f := by
  rw [Category.assoc, normalConeMapOfFactorization_toBase, ← Category.assoc,
    normalConeMapOfSquare_toBase, Category.comp_id]

/-- **The factorization of `C_ZY ⟶ C_ZX ⟶ C_YX` through the zero section `o : Y ⟶ C_YX` is
equivalent to the vanishing of one morphism of `𝒪_Y`-modules.**

This is the fact about schemes that `Stacks.Chow.normalConeToZeroFibre` is built from — proved in
`StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeNestedZeroSection` as
`Stacks.Conormal.normalConeNested_eq_comp_normalConeZeroSection` — reduced by
`Stacks.Conormal.eq_comp_normalConeZeroSection_iff` to the vanishing of the module component of
the pair that the functor of points of the total space of the conormal line bundle attaches to
that composite. The reduction is an equivalence, so it is not a weakening; and the right-hand
side mentions no dependent type. -/
theorem normalConeNested_eq_comp_normalConeZeroSection_iff :
    normalConeMapOfSquare f iZ (𝟙 Z) DY.subschemeι ((Category.id_comp iZ).trans hf.symm) ≫
          normalConeMapOfFactorization iZ DY.subschemeι f hf =
        normalConeToBase f ≫ f ≫ normalConeZeroSection DY ↔
      ((conormalSituation DY).totalSpaceHomEquiv (normalCone f)
          ((normalConeMapOfSquare f iZ (𝟙 Z) DY.subschemeι
                ((Category.id_comp iZ).trans hf.symm) ≫
              normalConeMapOfFactorization iZ DY.subschemeι f hf) ≫
            (totalSpaceIsoNormalCone DY).inv)).2 = 0 := by
  rw [← Category.assoc (normalConeToBase f) f (normalConeZeroSection DY)]
  exact eq_comp_normalConeZeroSection_iff DY _ _
    (normalConeNested_comp_normalConeToBase DY iZ f hf)

end Nested

end Stacks.Conormal

end
