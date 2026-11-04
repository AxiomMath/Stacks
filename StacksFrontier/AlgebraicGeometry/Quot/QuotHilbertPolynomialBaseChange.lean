/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotSubfunctorBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerFibreSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyOverRing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackTensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedModulePushforward

/-!
# Base change of `Quot^P_{F/X/B}`

Let `F/X/B` be a Quot situation (Stacks 09TR), `L` an invertible `𝒪_X`-module, `P : ℤ → ℤ`,
`p : B' ⟶ B` a morphism of algebraic spaces and `F'/X'/B'` the base-changed situation of
Stacks 08IT, with `L'` the pullback of `L` to `X' = X ×_B B'`.  For a scheme `T` over `B'` and a
point `t ∈ T` the fibre `X'_t` is `X_t` (`T` read over `B` through `B' ⟶ B`), the fibre of a
quotient of `F'_T` is the inverse image of the fibre of the matching quotient of `F_T`, and
`L'_t` is `L_t`; so the twisted Euler characteristics agree and

`Quot^{P, L'}_{F'/X'/B'} = Quot^{P, L}_{F/X/B} ×_B B'`

as subfunctors of the Quot presheaf of `F'/X'/B'`.  This is the base change step in the proofs of
Stacks 0DPB and 0DPC: being an algebraic space proper over the base is checked after base change
to affine schemes
(`AlgebraicGeometry.Space.QuotSituation.isProperAlgebraicSpaceOver_of_represented`).

## Main results

* `AlgebraicGeometry.Space.eulerCharacteristicAlong_modulePullback_of_iso`: the Euler
  characteristic of a quasi-coherent module is unchanged by the inverse image along an
  isomorphism of algebraic spaces.
* `AlgebraicGeometry.Space.QuotSituation.twistedEuler_ofCanonicalBaseChanged`: a quotient of
  `F'/X'/B'` and the quotient of `F/X/B` it is read as have the same twisted Euler
  characteristics, with respect to `L'` and `L`.
* `AlgebraicGeometry.Space.QuotSituation.baseChangeSubfunctor_hilbertPolynomialQuot`:
  `Quot^{P, L}_{F/X/B} ×_B B' = Quot^{P, L'}_{F'/X'/B'}`.

## References

* [Stacks Project, Tag 08IT](https://stacks.math.columbia.edu/tag/08IT)
* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 0DPC](https://stacks.math.columbia.edu/tag/0DPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The Euler characteristic is unchanged by the inverse image along an isomorphism.**  For an
isomorphism `e : X ≅ Y` of algebraic spaces, a field `k` with ring maps to the global functions
of `X` and `Y` compatible with `e`, and a quasi-coherent `𝒪_Y`-module `M`,
`χ(X, e^*M) = χ(Y, M)`: `e^*M` is the direct image of `M` along the affine morphism `e⁻¹`. -/
theorem eulerCharacteristicAlong_modulePullback_of_iso {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y)
    (k : Type u) [Field k]
    (ψX : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
    (ψY : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
    (h : GlobalSectionRingHomsCompatible B S hS e.inv
      (relativelyRepresentable_of_isAffineHom B S hS e.inv (isAffineHom_of_isIso e.inv.hom))
      ψX ψY)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite) :
    eulerCharacteristicAlong B S hS X.1 X.2 k ψX ((modulePullback B S hS e.hom).obj M) =
      eulerCharacteristicAlong B S hS Y.1 Y.2 k ψY M :=
  ((eulerCharacteristicAlong_modulePushforward_of_isAffineHom B S hS e.inv _ k ψX ψY
    (isAffineHom_of_isIso e.inv.hom) h M hM).trans
    (eulerCharacteristicAlong_congr B S hS X.1 X.2 k ψX
      ((modulePushforwardInvIsoModulePullback B S hS e).app M))).symm

namespace QuotSituation

variable (D : QuotSituation B S hS) {Y' : AlgebraicSpaces B S hS} (p : Y' ⟶ D.Y)
  (L : Modules.{u, u} B S hS D.X.1 D.X.2)
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]

/-- **The twisted Euler characteristics are unchanged by base change** (Stacks 08IT).  A quotient
of `F'_T` in the Quot presheaf of the base-changed situation `F'/X'/B'` has, at every point `t`
of `T`, the same twisted Euler characteristics with respect to the pullback `L'` of `L` to
`X' = X ×_B B'` as the quotient of `F_T` it is read as, with respect to `L`.

Under the identification `X'_t ≅ X_t` of the two fibres the fibre of the quotient of `F'_T` is
the inverse image of the fibre of the quotient of `F_T`, and `(L'^{⊗ n})_t` is the inverse image
of `(L^{⊗ n})_t`; the inverse image along an isomorphism does not change the Euler
characteristic (`AlgebraicGeometry.Space.eulerCharacteristicAlong_modulePullback_of_iso`). -/
theorem twistedEuler_ofCanonicalBaseChanged {T : BigFppfOver B S hS}
    (y : QuotFamilyOver (D.canonicalBaseChanged p) T) (t : y.cohObject.testScheme) (n : ℤ) :
    @CoherentObject.twistedEuler B S hS (D.canonicalBaseChanged p).toCoherentSituation
        ((modulePullback B S hS (D.baseChangedSourceProjection p)).obj L)
        (isInvertible_modulePullback B S hS (D.baseChangedSourceProjection p) L) y.cohObject t n =
      @CoherentObject.twistedEuler B S hS D.toCoherentSituation L hL
        y.ofCanonicalBaseChanged.cohObject t n := by
  let D' := D.canonicalBaseChanged p
  let A' := y.cohObject
  let A := y.ofCanonicalBaseChanged.cohObject
  let T₀ : SchemesOver Y' := CostructuredArrow.mk y.toBase
  let Tt' := A'.pointTest t
  let e := D.canonicalBaseChangeFiberIso p Tt'
  let eT := D.canonicalBaseChangeFiberIso p T₀
  let Q := D.quotientModule ((CostructuredArrow.map p).obj T₀)
    ((D.canonicalBaseChangeSubobjectEquiv p T₀).symm y.subobject)
  let Qo := D.quotientModule ((CostructuredArrow.map p).obj T₀) y.ofCanonicalBaseChanged.subobject
  let jQ : Q ≅ Qo := eqToIso (congrArg (D.quotientModule ((CostructuredArrow.map p).obj T₀))
    (QuotFamilyOver.ofCanonicalBaseChanged_subobject y).symm)
  -- the three compatibilities of `X'_t ≅ X_t`, read on the side of `A`
  have sq : e.hom ≫ D.toCoherentSituation.relativeMap (A.pointTestHom t) =
      D'.relativeMap (A'.pointTestHom t) ≫ eT.hom :=
    D.toQuotientSituation.baseChangeFiberIso_hom_comp_relativeMap p _ (A'.pointTestHom t)
  have sqX : e.hom ≫ baseChangeProjection D.toCoherentSituation.f (A.pointTest t) =
      D'.sourceProjection Tt' ≫ D.baseChangedSourceProjection p :=
    D.toQuotientSituation.baseChangeFiberIso_hom_comp_sourceProjection p _ Tt'
  have sqT : e.hom ≫ D.toCoherentSituation.projection (A.pointTest t) = D'.projection Tt' :=
    D.toQuotientSituation.baseChangeFiberIso_hom_comp_projection p _ Tt'
  -- the fibre of the quotient of `F'_T` is the inverse image of the fibre of the quotient of `F_T`
  let i1 := (modulePullback B S hS (D'.relativeMap (A'.pointTestHom t))).mapIso
      (D.canonicalBaseChangedQuotientModuleIsoSymm p T₀ y.subobject) ≪≫
    (modulePullback B S hS (D'.relativeMap (A'.pointTestHom t))).mapIso
      ((modulePullback B S hS eT.hom).mapIso jQ) ≪≫
    (modulePullbackSquare B S hS rfl sq).app Qo
  -- `(L'^{⊗ n})_t` is the inverse image of `(L^{⊗ n})_t`
  let i2 := (modulePullback B S hS (D'.sourceProjection Tt')).mapIso
      (modulePullbackInvertibleTensorPowerIso B S hS (D.baseChangedSourceProjection p) L n).symm ≪≫
    (modulePullbackSquare B S hS rfl sqX).app (invertibleTensorPower B S hS D.X.1 D.X.2 L n)
  let Ft := (modulePullback B S hS (D.toCoherentSituation.relativeMap (A.pointTestHom t))).obj Qo
  let Lt := (modulePullback B S hS
    (baseChangeProjection D.toCoherentSituation.f (A.pointTest t))).obj
      (invertibleTensorPower B S hS D.X.1 D.X.2 L n)
  let N := ((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).obj Ft).obj Lt
  let i3 := ((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS (D'.space Tt').1 (D'.space Tt').2).O).mapIso i1).app _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS (D'.space Tt').1 (D'.space Tt').2).O).obj _).mapIso i2 ≪≫
    (modulePullbackSheafTensorIso B S hS e.hom Ft Lt).symm
  -- the ring maps from `κ(t)` are compatible with `e`
  let α := (Scheme.ΓSpecIso (.of (A'.testScheme.residueField t))).inv.hom
  have hc : GlobalSectionRingHomsCompatible B S hS e.inv
      (relativelyRepresentable_of_isAffineHom B S hS e.inv (isAffineHom_of_isIso e.inv.hom))
      ((globalSectionsRingHom B S hS _ _ (D'.projection Tt').hom).comp α)
      ((globalSectionsRingHom B S hS _ _
        (D.toCoherentSituation.projection (A.pointTest t)).hom).comp α) := by
    rw [← (Iso.inv_comp_eq e).mpr sqT.symm]
    exact globalSectionRingHomsCompatible_globalSectionsRingHom B S hS e.inv _
      (D'.projection Tt').hom α
  exact (eulerCharacteristicAlong_congr _ _ _ _ _ _ _ i3).trans
    (eulerCharacteristicAlong_modulePullback_of_iso e _ _ _ hc N
      (@CoherentObject.isQuasicoherentOnSite_fibreTwistedModule _ _ _ _ A t _
        (isInvertible_invertibleTensorPower B S hS D.X.1 D.X.2 L n)))

/-- **`Quot^P` commutes with base change** (Stacks 08IT, at the Hilbert polynomial condition of
Stacks 0DP6): the subfunctor `Quot^{P, L}_{F/X/B} ×_B B'` of the Quot presheaf of the
base-changed situation `F'/X'/B'` is `Quot^{P, L'}_{F'/X'/B'}`, for `L'` the pullback of `L` to
`X' = X ×_B B'`. -/
theorem baseChangeSubfunctor_hilbertPolynomialQuot (P : ℤ → ℤ) :
    D.baseChangeSubfunctor p (D.hilbertPolynomialQuot L P) =
      @hilbertPolynomialQuot B S hS (D.canonicalBaseChanged p)
        ((modulePullback B S hS (D.baseChangedSourceProjection p)).obj L)
        (isInvertible_modulePullback B S hS (D.baseChangedSourceProjection p) L) P := by
  refine Subfunctor.ext (funext fun T => Set.ext fun y => ?_)
  show (∀ t n, P n = @CoherentObject.twistedEuler B S hS D.toCoherentSituation L hL
      y.ofCanonicalBaseChanged.cohObject t n) ↔
    ∀ t n, P n = @CoherentObject.twistedEuler B S hS (D.canonicalBaseChanged p).toCoherentSituation
      ((modulePullback B S hS (D.baseChangedSourceProjection p)).obj L)
      (isInvertible_modulePullback B S hS (D.baseChangedSourceProjection p) L) y.cohObject t n
  simp only [D.twistedEuler_ofCanonicalBaseChanged p L y]
  exact Iff.rfl

end QuotSituation

end AlgebraicGeometry.Space

end
