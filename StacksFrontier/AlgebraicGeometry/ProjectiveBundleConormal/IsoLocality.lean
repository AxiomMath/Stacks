module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.IsoReduction

/-!
# Invertibility of a morphism of modules from a neighbourhood of each point

`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict` says that invertibility of a
morphism of sheaves of modules on a scheme is local: it suffices that the restriction to each
member of an *indexed open cover* be invertible. An argument that produces its open by shrinking
around a point — which is the shape every statement in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SplittingCover` has — holds the
hypothesis in the pointwise form instead, and this file records that form.

The two are of course the same statement: index the cover by the points of `X` and choose, for
each, the open the hypothesis supplies. Having it written down means a local argument can be
spelled "around every point there is an open on which the map is invertible" and never has to
construct a cover.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_forall_exists_isIso_restrict`: **the
  pointwise form of the locality criterion.**
* `Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_forall_exists_isIso_restrict`:
  that criterion at the canonical map of [Stacks, Tag 0B3V] clause 3, which together with
  `Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_isIso_pullback_idealSheafLift`
  is the shape in which the clause's isomorphism assertion is reduced to a computation on one
  affine open.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChange

/-- **Invertibility of a morphism of sheaves of modules is local, in pointwise form.** If every
point of `X` has *some* open neighbourhood to which the restriction of `φ` is invertible, then
`φ` is invertible.

This is `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict` with the cover
indexed by the points of `X`: the chosen neighbourhoods cover `X` because each contains its own
point. -/
theorem isIso_of_forall_exists_isIso_restrict {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)) :
    IsIso φ := by
  choose U hmem hiso using h
  refine isIso_of_isIso_restrict φ U ?_ hiso
  refine IsOpenCover.mk (eq_top_iff.mpr fun x _ => ?_)
  exact Opens.mem_iSup.mpr ⟨x, hmem x⟩

end Stacks.AlgebraicGeometry.AffineBaseChange

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
  [IsImmersion σ]

include hσ e hqe in
/-- **The isomorphism assertion of [Stacks, Tag 0B3V] clause 3 is local on `X`.** If every point
of `X` has an open neighbourhood to which the restriction of the canonical map is invertible, the
canonical map is invertible.

This is the companion of
`Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_isIso_pullback_idealSheafLift`:
that one strips the two outer isomorphisms off the canonical map, this one reduces the remaining
assertion to one affine open. The open is supplied by
`Stacks.ProjectiveBundleConormal.exists_affine_open_chartLinearForm`, on which the source becomes
`ker(q)|_U` by `Stacks.ProjectiveBundleConormal.restrictSourceIso` and the chart of the bundle
becomes the affine bundle on `Γ(ker q, U)` by
`Stacks.ProjectiveBundleConormal.splitChartMap`. -/
theorem isIso_conormalCanonicalMap_of_forall_exists_isIso_restrict
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map (conormalCanonicalMap E Q hσ e hqe))) :
    IsIso (conormalCanonicalMap E Q hσ e hqe) :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_forall_exists_isIso_restrict _ h

end Stacks.ProjectiveBundleConormal

end
