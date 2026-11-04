module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportZeroVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldBaseChangeGeometry
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology of `ℱ_ρ` on a geometric curve in degrees zero

Let `X` be a geometrically connected smooth curve over a field `k`, let `K` be an algebraic
extension of `k` (in the source, `k̄` or `k^{sep}`), let `Λ` be a finite ring and let `ℱ_ρ` be the
sheaf on `X_étale` attached to a finite `Λ`-module `M` with a continuous action `ρ` of the
fundamental group. Remark 03VL of the Trace Formula chapter computes the cohomology of `ℱ_ρ` on
`X_K` in the two extreme degrees. This file proves its two degree-zero assertions:

* `H⁰(X_K, ℱ_ρ) = M^{π₁(X_K, η̄)}`, functorially in `ρ`;
* `H⁰_c(X_K, ℱ_ρ) = 0` if `X` is not projective over `k`.

## Main results

* `AlgebraicGeometry.curveGlobalSectionsIsoInvariants` — the first.
* `AlgebraicGeometry.isZero_curveCompactlySupportedCohomologyZero_of_not_isProjective` — the
  second, for compactly supported cohomology in the sense of Tag 0GJZ.

## Implementation notes

The sheaf `ℱ_ρ` is `AlgebraicGeometry.representationSheaf`, built through Tag 0DV5 on a big
étale site `B` containing `X`, and its restriction to `X_K` is
`AlgebraicGeometry.geometricRepresentationSheaf`. The base change `X_K` lies in `B` as soon as `X`
does (`AlgebraicGeometry.contains_fieldBaseChange`), because `K` is algebraic over `k`, so no
further condition on `B` is imposed. The geometric fundamental group `π₁(X_K, η̄)` acts on `M`
through the homomorphism `π₁(X_K, η̄) ⟶ π₁(X, η̄)` induced by the projection, for a geometric point
`η̄` of `X_K` and its image in `X`.

A curve is projective over `k` exactly when it is proper (Tag 0A26), and properness descends
along `K / k` (Tag 02L1), so a curve which is not projective has a base change `X_K` which is
integral and not proper over `K`; that is what the vanishing of `H⁰_c` uses.

## References

* [Stacks Project, Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
* [Stacks Project, Tag 0GJZ](https://stacks.math.columbia.edu/tag/0GJZ)
* [Stacks Project, Tag 0GK1](https://stacks.math.columbia.edu/tag/0GK1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.Frobenius
open Stacks.EtaleCohomology

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f]
  (K : Type u) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] (Λ : Type r) [Ring Λ] [Finite Λ]

omit [Smooth f] [GeometricallyConnected f] in
include f in
/-- A curve is connected, being integral. -/
theorem connectedSpace_of_isCurve : ConnectedSpace X.1 :=
  have : IsIntegral X.1 := (inferInstance : IsCurve k f).toIsIntegral
  inferInstance

omit [Smooth f] [GeometricallyConnected f] in
include f in
/-- A curve is nonempty, being integral. -/
theorem nonempty_of_isCurve : Nonempty X.1 :=
  have : IsIntegral X.1 := (inferInstance : IsCurve k f).toIsIntegral
  inferInstance

omit [Smooth f] [GeometricallyConnected f] in
/-- The base change `X_K` of a curve to an algebraic extension lies in every big étale site
containing the curve. -/
theorem contains_fieldBaseChange_of_isCurve : B.Contains (fieldBaseChange (Over.mk f) K) :=
  have := nonempty_of_isCurve B X f
  contains_fieldBaseChange f K B X.2

/-- **Stacks Project, Tag 03VL, first identification: `H⁰(X_K, ℱ_ρ) = M^{π₁(X_K, η̄)}`,
functorially in `ρ`.** For a geometrically connected smooth curve `X` over `k`, an algebraic
extension `K` of `k`, a finite ring `Λ` and a geometric point `η̄` of `X_K`, the global sections
on `X_K` of the restriction of the sheaf `ℱ_ρ` attached to a finite `Λ`-module `M` with a
continuous action `ρ` of `π₁(X, η̄)` are the invariants of `M` under `π₁(X_K, η̄)`, acting through
`π₁(X_K, η̄) ⟶ π₁(X, η̄)`. This is an isomorphism of functors of `(M, ρ)`, with values in
`Λ`-modules (the invariants lifted to the coefficient universe of `ℱ_ρ`). The source states it for
`X` projective and `K = k̄`; neither projectivity nor `#Λ ∈ k^*` is used. -/
def curveGlobalSectionsIsoInvariants (y : GeometricPoint (fieldBaseChange (Over.mk f) K)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    geometricRepresentationSheaf B X
          (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
          Λ f K ⋙
        etaleModuleGlobalSections.{u, r} Λ (fieldBaseChange (Over.mk f) K) ≅
      finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
          (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom y) ⋙
        finiteTypeContinuousModuleInvariants Λ
          (EtaleFundamentalGroup (fieldBaseChange (Over.mk f) K) y) ⋙
        ModuleCat.uliftFunctor.{r, u + 1} Λ :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  geometricGlobalSectionsIsoInvariants B X Λ f K (contains_fieldBaseChange_of_isCurve B X f K) y

omit [Smooth f] [GeometricallyConnected f] [Algebra.IsAlgebraic k K] in
/-- **A curve which is not projective has a base change which is not proper.** A proper curve
is H-projective (Tag 0A26), hence projective, and properness descends along `K / k`
(Tag 02L1). -/
theorem not_isProper_fieldBaseChange_of_not_isProjective (hnp : ¬ IsProjective f) :
    ¬ IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k K)) := by
  intro hK
  have hf : IsProper f := isProper_of_isProper_fieldBaseChange f K hK
  refine hnp ?_
  have hdim : topologicalKrullDim (X.1 : Type u) ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  open Stacks.HQuasiProjectiveDimensionOne in
  exact (isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one f hdim).isProjective

attribute [local instance] HasDerivedCategory.standard in
/-- **Stacks Project, Tag 03VL, last assertion: `H⁰_c(X_K, ℱ_ρ) = 0` if `X` is not
projective.** For a geometrically connected smooth curve `X` over `k` which is not projective,
an algebraic extension `K` of `k`, a finite ring `Λ` and a finite `Λ`-module `M` with a continuous
action `ρ` of `π₁(X, η̄)`, the zeroth compactly supported cohomology module, in the sense of
Tag 0GJZ, of the restriction of `ℱ_ρ` to `X_K` vanishes, through any compactification of `X_K`
over `K`. -/
@[stacks 03VL "H⁰_c(X_k̄, ℱ_ρ) = 0 if X is not projective, H_c in the sense of Tag 0GJZ, for every \
algebraic extension K of k in place of k̄", sga "5 VII 7.1.1" "b), special case"]
theorem isZero_curveCompactlySupportedCohomologyZero_of_not_isProjective
    (hnp : ¬ IsProjective f)
    (jbar : CompactificationOf (Over.mk (pullback.snd (Over.mk f).hom (specAlgebraMap k K))))
    (y : GeometricPoint (fieldBaseChange (Over.mk f) K))
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{r, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    IsZero ((compactlySupportedCohomologyGroup.{u, r} K
        (pullback.snd (Over.mk f).hom (specAlgebraMap k K)) jbar Λ 0).obj
      ((DerivedCategory.Plus.singleFunctor
        (EtaleModules.{u, r} Λ (fieldBaseChange (Over.mk f) K)) 0).obj
          ((geometricRepresentationSheaf B X
            (y.map (fieldBaseChangeObjProj B X f K
              (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f K).obj M))) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f K
  have := isIntegral_fieldBaseChange f K
  have : LocallyOfFiniteType (Over.mk f).hom := inferInstanceAs (LocallyOfFiniteType f)
  have : QuasiCompact (Over.mk f).hom := inferInstanceAs (QuasiCompact f)
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  let : ConnectedSpace (fieldBaseChangeObj B X f K
      (contains_fieldBaseChange_of_isCurve B X f K)).1 :=
    connectedSpace_fieldBaseChange f K
  have e : (geometricRepresentationSheaf B X (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f K).obj M ≅
      (sheafCompose (fieldBaseChange (Over.mk f) K).smallEtaleTopology
        (ModuleCat.uliftFunctor.{r, u + 1} Λ)).obj
        ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B
          (fieldBaseChangeObj B X f K (contains_fieldBaseChange_of_isCurve B X f K))
            y Λ).inverse.obj
          ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
            (fieldBaseChangeObjProj B X f K
              (contains_fieldBaseChange_of_isCurve B X f K)).hom y)).obj M)).obj :=
    (representationSheafPullbackIso B (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)) Λ y).app M ≪≫
      (representationSheafIsoEtaleSite B (fieldBaseChangeObj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)) y Λ).app _
  have h := isZero_compactlySupportedCohomologyGroup_zero_of_not_isProper Λ
    (Y := fieldBaseChange (Over.mk f) K) K (pullback.snd (Over.mk f).hom (specAlgebraMap k K))
    (not_isProper_fieldBaseChange_of_not_isProjective B X f K hnp) jbar _
    ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B
      (fieldBaseChangeObj B X f K (contains_fieldBaseChange_of_isCurve B X f K)) y Λ).inverse.obj
      ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom y)).obj M)).property
  exact h.of_iso ((compactlySupportedCohomologyGroup.{u, r} K _ jbar Λ 0).mapIso
    ((DerivedCategory.Plus.singleFunctor _ 0).mapIso e))

end AlgebraicGeometry
