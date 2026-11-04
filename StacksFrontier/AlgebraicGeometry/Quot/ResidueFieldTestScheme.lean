module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafMatrices
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# The residue field of a point of a scheme of the site as a test scheme

For a point `x` of the underlying scheme of an object `c` of the big fppf site, the spectrum of
the residue field `κ(x)` is an object of the site over `c`, whose ring of global functions is
`κ(x)`, the restriction of global functions of `c` being evaluation at `x`.

## Main results

* `AlgebraicGeometry.Scheme.fromSpecResidueField_appTop_ΓSpecIso_hom`: the global functions of
  `X` restrict to `Spec κ(x)` by evaluation at `x`.
* `AlgebraicGeometry.Space.exists_residueField_test`: the residue field test scheme.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The global functions of a scheme restrict to the spectrum of a residue field by evaluation
at the point.** -/
theorem Scheme.fromSpecResidueField_appTop_ΓSpecIso_hom (X : Scheme.{u}) (x : X) :
    (X.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso (X.residueField x)).hom =
      X.evaluation ⊤ x trivial := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.fromSpecStalk_appTop]
  simp [Scheme.evaluation]

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The residue field of a point as a test scheme.**  For a point `x` of the underlying scheme
of `c` there are an object `T` of the site with a morphism `f : T ⟶ c` and a ring isomorphism
`Γ(T) ≃ κ(x)` through which the restriction of global functions along `f` is evaluation at
`x`. -/
theorem exists_residueField_test (c : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj c) :
    ∃ (T : BigFppfOver B S hS) (f : T ⟶ c)
      (ι : Gam T ≃+* ((BigFppfOver.toScheme B S hS).obj c).residueField x),
      ∀ a : Gam c, ι (((BigFppfOver.toScheme B S hS).map f).appTop.hom a) =
        (((BigFppfOver.toScheme B S hS).obj c).evaluation ⊤ x trivial).hom a := by
  let X := (BigFppfOver.toScheme B S hS).obj c
  have hV : B.Contains (Spec (.of (X.residueField x))) :=
    B.residueField_spec_contains c.left.property x
  obtain ⟨T, f, e, hf⟩ := exists_siteObject_toScheme_map_eq B S hS hV (X.fromSpecResidueField x)
  let ι₀ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) ≅ X.residueField x :=
    Scheme.Γ.mapIso e.symm.op ≪≫ Scheme.ΓSpecIso (X.residueField x)
  refine ⟨T, f, ι₀.commRingCatIsoToRingEquiv, fun a => ?_⟩
  have h1 : ((BigFppfOver.toScheme B S hS).map f).appTop ≫ ι₀.hom = X.evaluation ⊤ x trivial := by
    show ((BigFppfOver.toScheme B S hS).map f).appTop ≫ e.inv.appTop ≫
      (Scheme.ΓSpecIso (X.residueField x)).hom = _
    rw [hf, Scheme.Hom.comp_appTop, Category.assoc, ← Category.assoc e.hom.appTop,
      ← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop, Category.id_comp,
      Scheme.fromSpecResidueField_appTop_ΓSpecIso_hom]
  exact congrArg (fun φ => φ.hom a) h1

end Space

end AlgebraicGeometry

end
