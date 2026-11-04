module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic

/-!
# Global sections of a proper variety over an algebraically closed field

Let `k` be an algebraically closed field and let `X` be a proper variety over `k`. The structural
ring map `k →+* Γ(X, ⊤)` is bijective: a proper variety over an algebraically closed field has no
global functions beyond the constants. Indeed `Γ(X, ⊤)` is a domain because `X` is integral, it is
integral over `k` because the structure morphism is universally closed, and an integral domain
integral over an algebraically closed subfield equals that subfield.

## Main results

* `Stacks.AlgebraicGeometry.UnitsNormalProper.bijective_structMap`: the structural ring map
  `k →+* Γ(X, ⊤)` of a proper variety over an algebraically closed field is bijective.

## References

* [Stacks Project, Tag 04L2](https://stacks.math.columbia.edu/tag/04L2)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.UnitsNormalProper

variable (k : Type u) [Field k] {X : Scheme.{u}}

/-- The structural ring map `k →+* Γ(X, ⊤)` of a scheme over `Spec k`. -/
noncomputable abbrev structMap (f : X ⟶ Spec (.of k)) : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

/-- The ring of global sections of an integral scheme is a domain. -/
theorem isDomain_globalSections [IsIntegral X] : IsDomain Γ(X, ⊤) :=
  have : Nonempty (⊤ : X.Opens) :=
    ⟨⟨(inferInstance : IrreducibleSpace X).toNonempty.some, trivial⟩⟩
  AlgebraicGeometry.IsIntegral.component_integral ⊤

/-- For a proper variety over an algebraically closed field, the structural ring map from the
field to the global sections is bijective: the only global functions are the constants. -/
theorem bijective_structMap [IsAlgClosed k] (f : X ⟶ Spec (.of k))
    [AlgebraicGeometry.IsProperVariety k f] : Function.Bijective (structMap k f) := by
  have : IsDomain Γ(X, ⊤) := isDomain_globalSections
  let _ : Algebra k Γ(X, ⊤) := (structMap k f).toAlgebra
  have : Algebra.IsIntegral k Γ(X, ⊤) :=
    ⟨Stacks.AlgebraicGeometry.ProperGeomConnected.isIntegral_toSpecΓ_algebraMap f⟩
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

end Stacks.AlgebraicGeometry.UnitsNormalProper
