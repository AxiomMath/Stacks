module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInFiniteOfProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperConnectedGeometricFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationNoetherianQcqs

/-!
# Stacks 0A1B, clause (1): `f'` is proper with connected geometric fibres

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with `Y` locally Noetherian,
and let `X ⟶ Y' ⟶ Y` be its factorization `f = π ∘ f'` through the normalization `Y'` of `Y` in
`X` (Stacks 0822).  Clause (1) of Stacks 0A1B asserts that `f'` is proper with connected
geometric fibres.

Properness is `AlgebraicGeometry.Space.isProper_toNormalizationInQcqs`.  For the geometric
fibres: `f'` is surjective and `f'_* 𝒪_X = 𝒪_{Y'}` (Stacks 0A19, clauses (1) and (3)), and `Y'`
is locally Noetherian, being finite over `Y` (clause (2),
`AlgebraicGeometry.Space.isFinite_normalizationInQcqsHom_of_isProper`); so
`AlgebraicGeometry.Space.connectedPullback_of_isProper_of_isIso_fSharp` applies.  The source's
proof goes through the theorem on formal functions (Stacks 08B1); the proof here replaces it by
an étale-local spreading of a splitting of the fibre (see
`StacksFrontier.AlgebraicGeometry.Spaces.ProperConnectedFibresOverAffine`).

## Main results

* `AlgebraicGeometry.Space.isProper_and_connectedPullback_toNormalizationInQcqs`: clause (1).

## References

* [Stacks Project, Tag 0A1B](https://stacks.math.columbia.edu/tag/0A1B)
* [Stacks Project, Tag 0A19](https://stacks.math.columbia.edu/tag/0A19)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0A1B, clause (1).**  Let `f : X ⟶ Y` be a proper morphism of algebraic spaces with
`Y` locally Noetherian.  The morphism `f' : X ⟶ Y'` to the normalization of `Y` in `X`
(Stacks 0822), through which `f` factors as `f = π ∘ f'`, is proper, and its geometric fibres are
connected: for every geometric point `ȳ` of `Y'` the fibre `X ×_{Y'} ȳ` has connected point
space. -/
@[stacks 0A1B "part (1): for f proper with Y locally Noetherian, the morphism f' : X -> Y' to \
the normalization of Y in X (Stacks 0822), with f = pi o f', is proper and its geometric fibres \
are connected"]
theorem isProper_and_connectedPullback_toNormalizationInQcqs (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    IsProper B S hS
        (toNormalizationInQcqs f hf.2.1.2 (isQuasiSeparated_of_isSeparated B S hS hf.1)).hom ∧
      ∀ y : GeometricPoint B S hS (normalizationInQcqs B S hS f hf.2.1.2
          (isQuasiSeparated_of_isSeparated B S hS hf.1)).1,
        ConnectedPullback B S hS
          (toNormalizationInQcqs f hf.2.1.2 (isQuasiSeparated_of_isSeparated B S hS hf.1)).hom
          (yonedaEquiv.symm y.val.value) := by
  have hfqs := isQuasiSeparated_of_isSeparated B S hS hf.1
  have hproper := isProper_toNormalizationInQcqs B S hS f hf.2.1.2 hfqs hf
  refine ⟨hproper, fun y => ?_⟩
  have := isIso_fSharp_toNormalizationInQcqs f hf.2.1.2 hfqs hf.2.2
  have hπ := isFinite_normalizationInQcqsHom_of_isProper B S hS f hf hY
  have hπp := ((isFinite_iff_isAffineHom_and_isProper B S hS
    (normalizationInQcqs B S hS f hf.2.1.2 hfqs).2 Y.2 _).1 hπ).2
  have hY' := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS
    (normalizationInQcqs B S hS f hf.2.1.2 hfqs).2 Y.2 _ hπp.2.1.1 hY
  exact connectedPullback_of_isProper_of_isIso_fSharp _ hproper
    (isSurjective_toNormalizationInQcqs B S hS f hf.2.1.2 hfqs hf.2.2) hY' y

end AlgebraicGeometry.Space

end
