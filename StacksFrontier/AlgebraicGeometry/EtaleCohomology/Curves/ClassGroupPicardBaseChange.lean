module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClassGroupPicard
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionClosedPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionSmoothCurve
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyBaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierPullbackCorollaries
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced

/-!
# The class of a closed point under scalar extension

Let `X` be a smooth curve over an algebraically closed field `k`, `k'/k` a field extension and
`p : X_{k'} ⟶ X` the projection. Over a closed point `x` of `X` lies a single point `x'` of
`X_{k'}` (`Stacks.EtaleCohomology.scalarExtensionClosedPoint`), and the fibre is reduced: it is
`Spec(κ(x) ⊗_k k') = Spec k'`. So the pullback of the effective Cartier divisor `x` is the
effective Cartier divisor `x'`, and the pullback of `𝒪_X(x)` is `𝒪_{X_{k'}}(x')` (Tag 0C4U).

## Main results

* `Stacks.EtaleCohomology.comap_vanishingIdeal_closedPoint_scalarExtensionFst`:
  `p⁻¹(x) = x'` as closed subschemes.
* `Stacks.EtaleCohomology.schemePullbackClass_picardClass_closedPoint`: `p^*[𝒪(x)] = [𝒪(x')]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isCurve_scalarExtension smooth_scalarExtension

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] (k' : Type u) [Field k'] [Algebra k k']

omit [IsCurve k g] in
/-- The fibre of `X_{k'} ⟶ X` over a closed point `x` is the closed point `x'` over it. -/
theorem preimage_closedPoint_scalarExtensionFst (x : closedPoints X) :
    (scalarExtensionFst k k' g).base ⁻¹' {x.1} = {(scalarExtensionClosedPoint g k' x).1} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact ⟨eq_scalarExtensionClosedPoint g k' x, fun h => h ▸
    scalarExtensionFst_scalarExtensionClosedPoint g k' x⟩

omit [IsCurve k g] in
/-- **The pullback of a closed point to `X_{k'}` is the closed point over it, with its reduced
structure.** The pulled back subscheme is `x ×_k k'`, which is reduced because `x` is reduced and
`k` is perfect, and its support is the single point `x'`. -/
theorem comap_vanishingIdeal_closedPoint_scalarExtensionFst (x : closedPoints X) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X))).comap
        (scalarExtensionFst k k' g) =
      Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({(scalarExtensionClosedPoint g k' x).1} :
          Set (scalarExtension k k' g))) := by
  set D := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X))
  have : AlgebraicGeometry.IsIntegral D.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x.1
  have hP := (isPullback_comap_subschemeι D (scalarExtensionFst k k' g)).paste_vert
    (IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
  have : GeometricallyReduced (D.subschemeι ≫ g) := geometricallyReduced_of_isReduced _
  have : IsReduced (pullback (D.subschemeι ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
    inferInstance
  have : IsReduced (D.comap (scalarExtensionFst k k' g)).subscheme :=
    isReduced_of_isOpenImmersion hP.isoPullback.hom
  refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
  ext y
  rw [Scheme.IdealSheafData.support_comap]
  show y ∈ (scalarExtensionFst k k' g).base ⁻¹' (D.support : Set X) ↔ _
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    (x.2 : IsClosed ({x.1} : Set X)).closure_eq, preimage_closedPoint_scalarExtensionFst,
    Closeds.coe_closure,
    ((scalarExtensionClosedPoint g k' x).2 : IsClosed ({(scalarExtensionClosedPoint g k' x).1} :
      Set (scalarExtension k k' g))).closure_eq]

include g in
/-- The pullback of the effective Cartier divisor of a closed point to `X_{k'}` is defined: the
projection is a dominant morphism of integral schemes (Tag 02OO (2)). -/
theorem isPullbackDefined_scalarExtensionFst_closedPoint (x : closedPoints X) :
    Stacks.Divisors.IsPullbackDefined (scalarExtensionFst k k' g)
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X))) := by
  have : AlgebraicGeometry.IsIntegral (scalarExtension k k' g) := isIntegral_scalarExtension k k' g
  have : Surjective (scalarExtensionFst k k' g) := surjective_scalarExtensionFst g k'
  exact Stacks.Divisors.isPullbackDefined_of_isDominant _ _
    (isEffectiveCartierDivisor_closedPoint g x)

/-- The class of `𝒪_X(D)` in the model `Stacks.Picard.ofScheme` of `Pic(X)` is carried by the
comparison of the two models to the class `AlgebraicGeometry.divisorSchemePicardClass`. -/
theorem picardModelAddEquiv_picardClass {Y : Scheme.{u}} (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    Stacks.GluePicard.picardModelAddEquiv Y.toRingedSpace (Stacks.Divisors.picardClass D) =
      divisorSchemePicardClass D :=
  Stacks.GluePicard.picardModelAddEquiv_classOf Y.toRingedSpace _ _

/-- **The pullback of `𝒪_X(x)` to `X_{k'}` is `𝒪_{X_{k'}}(x')`**, for `x'` the closed point over
`x`, in the model `AlgebraicGeometry.schemePicard` of the Picard group (Tag 0C4U). -/
theorem picardModelAddEquiv_schemePullbackClass_closedPoint (x : closedPoints X) :
    haveI := isEffectiveCartierDivisor_closedPoint g x
    haveI := isEffectiveCartierDivisor_closedPoint (scalarExtensionSnd k k' g)
      (scalarExtensionClosedPoint g k' x)
    Stacks.GluePicard.picardModelAddEquiv (scalarExtension k k' g).toRingedSpace
        (Stacks.Picard.schemePullbackClass (scalarExtensionFst k k' g)
          ((Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).symm
            (divisorSchemePicardClass
              (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X)))))) =
      divisorSchemePicardClass (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({(scalarExtensionClosedPoint g k' x).1} :
          Set (scalarExtension k k' g)))) := by
  have := isEffectiveCartierDivisor_closedPoint g x
  have := isEffectiveCartierDivisor_closedPoint (scalarExtensionSnd k k' g)
    (scalarExtensionClosedPoint g k' x)
  have := isPullbackDefined_scalarExtensionFst_closedPoint g k' x
  rw [← picardModelAddEquiv_picardClass, AddEquiv.symm_apply_apply,
    Stacks.Divisors.schemePullbackClass_picardClass, ← picardModelAddEquiv_picardClass]
  exact congrArg _ (Stacks.Divisors.picardClass_congr
    (comap_vanishingIdeal_closedPoint_scalarExtensionFst g k' x))

end Stacks.EtaleCohomology

end
