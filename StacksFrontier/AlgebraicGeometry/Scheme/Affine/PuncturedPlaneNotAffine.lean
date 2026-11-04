module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.PuncturedPlaneSections

/-!
# The punctured affine plane is not affine

The complement of the origin in the affine plane over a field is not an affine scheme. This is
the standard example of a scheme that is not affine, and of an open subscheme of an affine scheme
that is not affine.

## Main results

* `AlgebraicGeometry.not_isAffine_puncturedScheme`: the punctured affine plane is not affine.

## Implementation notes

The global sections of the punctured plane are still `k[x, y]`, and the canonical map realizing
that is the one induced by the open immersion. Were the punctured plane affine, that map would be
an isomorphism of affine schemes, because taking global sections is an equivalence between affine
schemes and rings; the open immersion would then be an isomorphism, so its open image would be
everything, and the origin would lie in the punctured plane.

## References

* [Stacks Project, Tag 01IL](https://stacks.math.columbia.edu/tag/01IL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The affine plane with its origin removed is not affine. -/
@[stacks 01IL "punctured_plane_not_affine"]
theorem not_isAffine_puncturedScheme (S : PuncturedAffinePlane.{u}) :
    ¬ IsAffine S.puncturedScheme := by
  intro hU
  let j : S.puncturedScheme ⟶ S.X := S.openImmersion
  let f : AffineScheme.of S.puncturedScheme ⟶ AffineScheme.of S.X := AffineScheme.ofHom j
  have hΓ : IsIso ((Scheme.ΓSpecIso (.of S.R)).inv ≫ j.appTop) :=
    isIso_coordinateRingToGlobalSections S
  have hf : IsIso f := (isIso_op_iff f).mp
    ((isIso_iff_of_reflects_iso f.op AffineScheme.Γ).mp
      (show IsIso (AffineScheme.Γ.map f.op) from
        IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of S.R)).inv j.appTop))
  have hUtop : S.U = ⊤ := by
    have hj : IsIso j := Functor.map_isIso AffineScheme.forgetToScheme f
    simpa [j, PuncturedAffinePlane.openImmersion, Scheme.Opens.opensRange_ι] using
      Scheme.Hom.opensRange_of_isIso j
  have hmem : affinePlaneOrigin S.k ∈ (S.U : Set (affinePlane S.k)) :=
    hUtop.symm ▸ Set.mem_univ _
  rw [S.carrier_U] at hmem
  exact hmem rfl

end AlgebraicGeometry

end
