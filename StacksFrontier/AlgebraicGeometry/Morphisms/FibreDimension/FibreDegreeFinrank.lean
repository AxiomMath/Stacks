module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBounded

/-!
# The degree of a fibre is the dimension of its global sections

A fibre of a locally quasi-finite quasi-compact morphism of schemes is an Artinian scheme and the
morphism from it to the spectrum of the residue field is finite. Over a field, being finite
locally free of rank `r` is the same as having `r`-dimensional global sections, so the degree of
such a fibre *is* the dimension of its ring of global sections. A bound on the degrees of the
fibres of a morphism is therefore a bound on those dimensions, and nothing else has to be checked
to produce one.

## Main results

* `AlgebraicGeometry.module_finite_globalSections_of_isFinite`: the global sections of the source
  of a finite morphism to the spectrum of a ring form a finite module over that ring.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_iff_finrank_eq`: a finite morphism to the spectrum
  of a field is finite locally free of rank `r` exactly when its global sections have
  dimension `r`.
* `AlgebraicGeometry.boundsFiberDegrees_iff_finrank_fiber_le`: an integer bounds the degrees of
  the fibres of a locally quasi-finite quasi-compact morphism exactly when it bounds the
  dimension of the global sections of every fibre over the corresponding residue field.

## Implementation notes

The fibre `f.fiber y` of a locally quasi-finite quasi-compact morphism is an Artinian scheme and
`f.fiberToSpecResidueField y` is finite; both are Mathlib instances, so the only content left in
a fibre-degree bound is the linear algebra. In particular no affineness or flatness of the fibre
has to be produced by hand: an Artinian scheme is finite and discrete, hence affine.

The algebra structure on the global sections of the source is the one transported along
`(Scheme.ΓSpecIso _).inv ≫ p.appTop`, which is the convention used by
`Stacks.Morphisms.sheafOfModules_isFiniteLocallyFreeOfRank_iff_module`; it appears as a `let` in
the statements for that reason.

## References

* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
* [Stacks Project, Tag 01SL](https://stacks.math.columbia.edu/tag/01SL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The global sections of the source of a finite morphism to the spectrum of a ring form a
finite module over that ring. -/
public theorem module_finite_globalSections_of_isFinite {R : CommRingCat.{u}} {Z : Scheme.{u}}
    (p : Z ⟶ Spec R) [IsFinite p] :
    letI := ((Scheme.ΓSpecIso R).inv ≫ p.appTop).hom.toAlgebra
    Module.Finite ↑R ↑Γ(Z, ⊤) :=
  p.finite_appTop.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2)

/-- A finite morphism to the spectrum of a field is finite locally free of rank `r` exactly when
its ring of global sections has dimension `r` over that field. -/
public theorem isFiniteLocallyFreeOfRank_iff_finrank_eq {K : Type u} [Field K]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of K)) [IsFinite p] (r : ℕ) :
    letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r ↔ Module.finrank K ↑Γ(Z, ⊤) = r := by
  let _ : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
  have _ : Module.Finite K ↑Γ(Z, ⊤) := module_finite_globalSections_of_isFinite p
  rw [Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff,
    and_iff_right (inferInstance : IsAffineHom p),
    Stacks.Morphisms.sheafOfModules_isFiniteLocallyFreeOfRank_iff_module p r]
  exact ⟨fun h ↦ (Module.IsFiniteLocallyFreeOfRank.finite_and_finrank_eq h).2,
    Module.isFiniteLocallyFreeOfRank_of_finrank_eq⟩

/-- An integer bounds the degrees of the fibres of a locally quasi-finite quasi-compact morphism
of schemes exactly when it bounds the dimension of the ring of global sections of every fibre
over the residue field of the corresponding point. -/
public theorem boundsFiberDegrees_iff_finrank_fiber_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [QuasiCompact f] (n : ℤ) :
    BoundsFiberDegrees f n ↔ ∀ y : Y,
      letI := ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
        (f.fiberToSpecResidueField y).appTop).hom.toAlgebra
      (Module.finrank ↑(Y.residueField y) ↑Γ(f.fiber y, ⊤) : ℤ) ≤ n := by
  constructor
  · intro h y
    obtain ⟨r, hr, hrank⟩ := h y
    rwa [(isFiniteLocallyFreeOfRank_iff_finrank_eq (K := ↑(Y.residueField y))
      (f.fiberToSpecResidueField y) r).mp hrank]
  · intro h y
    let _ : Algebra ↑(Y.residueField y) ↑Γ(f.fiber y, ⊤) :=
      ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
        (f.fiberToSpecResidueField y).appTop).hom.toAlgebra
    exact ⟨Module.finrank ↑(Y.residueField y) ↑Γ(f.fiber y, ⊤), h y,
      (isFiniteLocallyFreeOfRank_iff_finrank_eq (K := ↑(Y.residueField y))
        (f.fiberToSpecResidueField y) _).mpr rfl⟩

end AlgebraicGeometry

end
