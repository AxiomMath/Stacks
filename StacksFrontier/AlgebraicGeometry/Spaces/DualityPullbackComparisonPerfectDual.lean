module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparisonPerfectCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedDualExactPairing
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0E5Q: the map of Stacks 0E5P at a perfect object

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated algebraic spaces and `a` the
right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. For `K` perfect, the map
`Lf^*K ⊗^L a(L) ⟶ a(K ⊗^L L)` is an isomorphism for every `L ∈ D_QCoh(𝒪_Y)`, and so is the map
`Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)` of Stacks 0E5P: a perfect object has a dual in `D_QCoh(𝒪_Y)`
(`AlgebraicGeometry.Space.quasicoherentDerivedDualExactPairing`, Stacks 08JJ), and the map is
invertible at a dualizable object
(`AlgebraicGeometry.Space.isIso_quasicoherentDerivedCompareWithPullbackTensor_of_exactPairing'`).

## Main results

* `AlgebraicGeometry.Space.isIso_quasicoherentDerivedCompareWithPullbackTensor_of_isPerfect`
* `AlgebraicGeometry.Space.isIso_quasicoherentDerivedCompareWithPullback_app_of_isPerfect`

## References

* [Stacks Project, Tag 0E5Q](https://stacks.math.columbia.edu/tag/0E5Q)
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)

/-- **Stacks 0E5Q.** Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated algebraic
spaces and `a` the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. For `K, L ∈ D_QCoh(𝒪_Y)`
with `K` perfect, the map `Lf^*K ⊗^L a(L) ⟶ a(K ⊗^L L)` is an isomorphism. -/
@[stacks 0E5Q "the map Lf^*K ⊗ a(L) → a(K ⊗ L) is an isomorphism for K perfect"]
theorem isIso_quasicoherentDerivedCompareWithPullbackTensor_of_isPerfect
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K.obj)
    (L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    IsIso (quasicoherentDerivedCompareWithPullbackTensor hZ f hXqc hXqs hYqs K L) :=
  isIso_quasicoherentDerivedCompareWithPullbackTensor_of_exactPairing' hZ f hXqc hXqs hYqs K
    (quasicoherentDerivedDual Y K hK) (quasicoherentDerivedDualExactPairing Y K hK) L

/-- **Stacks 0E5Q, in particular.** For `K ∈ D_QCoh(𝒪_Y)` perfect, the map
`Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)` of Stacks 0E5P is an isomorphism. -/
@[stacks 0E5Q "in particular, the map (0E5P) Lf^*K ⊗ a(O_Y) → a(K) is an isomorphism for K \
  perfect"]
theorem isIso_quasicoherentDerivedCompareWithPullback_app_of_isPerfect
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K.obj) :
    IsIso ((quasicoherentDerivedCompareWithPullback hZ f hXqc hXqs hYqs).app K) := by
  have := isIso_quasicoherentDerivedCompareWithPullbackTensor_of_isPerfect hZ f hXqc hXqs hYqs K hK
    (derivedStructureSheaf B S hS Y.1 Y.2)
  rw [quasicoherentDerivedCompareWithPullback_app]
  infer_instance

end AlgebraicGeometry.Space

end
