module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericRestriction

/-!
# Reading `s_ξ|_Z` on an étale chart of the prime divisor

Let `X`, `Z ⊂ X`, `(U, u)`, `ℒ` and `s_ξ` be as in
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/KeyFormula/GenericRestriction.lean`.  This file
evaluates the value at the generic point of `Z` — and hence `s_ξ|_Z` — on an étale chart `W` of
`Z` receiving `ρ_Z : Spec κ(u) → Z`.  A section `m` of `ℒ|_Z` over `W` has an image in the fibre
`ρ_Z^*(ℒ|_Z)` over `Spec κ(u)`, which is a multiple `(m / s_ξ)(ξ) · s_ξ|_Z` of the image of
`s_ξ`; and if a meromorphic section `σ` of `ℒ|_Z` is `a ⊗ m` over `W`, its value at the generic
point is the pullback `a(ξ)` of `a` to `Spec κ(u)` times `(m / s_ξ)(ξ)`.  In particular, if
`s_ξ|_Z = a ⊗ m` over `W` then `a(ξ) = (s_ξ / m)(ξ)`: reading `s_ξ|_Z` (Section 0EQU) against `m`
at the generic point of `Z` gives the ratio of `s_ξ` to `m` there.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.genericFibreCoefficient`: the coefficient
  `(m / s_ξ)(ξ) ∈ κ(u)` of the image of a section `m` of `ℒ|_Z` over a chart receiving `ρ_Z`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldValue_eq_of_eval_eq_tmul`: the value at the
  generic point of `a ⊗ m` is `a(ξ) · (m / s_ξ)(ξ)`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericRestriction_chart`: if `s_ξ|_Z = a ⊗ m` over `W`,
  then `a(ξ) · (m / s_ξ)(ξ) = 1`.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X)
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (V : SmallEtale B S hS Z.subspace.toFunctor)
    (g : Z.genericFieldSpec B S hS hX hdec ⟶ V.obj.left)
    (hg : yoneda.map g ≫ V.1.hom =
      fieldMorphism B S hS Z.subspace.toFunctor (Z.genericFieldPoint B S hS hX hdec))

/-- **The coefficient `(m / s_ξ)(ξ)`** of a section `m` of `ℒ|_Z` over an étale chart `V` of `Z`
receiving `ρ_Z` by `g`: the element of `κ(u)` by which the image of `s_ξ` in the fibre must be
multiplied to give the image of `m`. -/
def PrimeDivisor.genericFibreCoefficient
    (m : (Z.restrictModule B S hS hX L).val.obj (op V)) :
    Z.genericResidueField B S hS hX hdec :=
  (Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).hom.hom
    ((Equiv.ofBijective _ (Z.bijective_smul_genericFieldGenerator B S hS hX hdec L hL
      (Z.genericFieldChart B S hS hX hdec) (𝟙 _))).symm
      ((modulePullbackChartFMap B S hS (Z.genericFieldMorphism B S hS hX hdec)
        (Z.restrictModule B S hS hX L)).app (genericFieldPointChartDiagram B S hS _ V g hg) m))

/-- **The defining property of `(m / s_ξ)(ξ)`**: the image of `m` in the fibre is `(m / s_ξ)(ξ)`
times the image of `s_ξ`. -/
theorem PrimeDivisor.modulePullbackChartFMap_eq_genericFibreCoefficient_smul
    (m : (Z.restrictModule B S hS hX L).val.obj (op V)) :
    (modulePullbackChartFMap B S hS (Z.genericFieldMorphism B S hS hX hdec)
        (Z.restrictModule B S hS hX L)).app (genericFieldPointChartDiagram B S hS _ V g hg) m =
      (show chartRing B S hS (Z.genericFieldSpace B S hS hX hdec).1
          (Z.genericFieldSpace B S hS hX hdec).2 (Z.genericFieldChart B S hS hX hdec) from
        (Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).inv.hom
          (Z.genericFibreCoefficient B S hS hX hdec L hL V g hg m)) •
        Z.genericFibreGenerator B S hS hX hdec L hL := by
  refine ((Equiv.ofBijective _ (Z.bijective_smul_genericFieldGenerator B S hS hX hdec L hL
      (Z.genericFieldChart B S hS hX hdec) (𝟙 _))).apply_symm_apply _).symm.trans ?_
  exact congrArg₂ (fun (r : chartRing B S hS (Z.genericFieldSpace B S hS hX hdec).1
      (Z.genericFieldSpace B S hS hX hdec).2 (Z.genericFieldChart B S hS hX hdec)) y => r • y)
    (CommRingCat.inv_hom_apply _ _).symm (Z.genericFieldGenerator_id B S hS hX hdec L hL)

/-- **The value at the generic point, read on an étale chart**: if a meromorphic section `σ` of
`ℒ|_Z` is `a ⊗ m` over an étale chart `V` receiving `ρ_Z`, its value at the generic point of `Z`
is the pullback of `a` to `Spec κ(u)`, read in `κ(u)`, times `(m / s_ξ)(ξ)`. -/
theorem PrimeDivisor.genericFieldValue_eq_of_eval_eq_tmul
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L))
    (a : (meromorphicChartSheaf B S hS Z.subspace.toFunctor Z.closed.1).obj.obj (op V))
    (m : (Z.restrictModule B S hS hX L).val.obj (op V))
    (hσ : σ.eval (op V) =
      toMeromorphicSectionSheaf B S hS Z.subspace.toFunctor Z.closed.1
        (Z.restrictModule B S hS hX L) V
        (a ⊗ₜ[chartRing B S hS Z.subspace.toFunctor Z.closed.1 V] m)) :
    Z.genericFieldValue B S hS hX hdec L hL σ =
      (Z.genericFieldMeromorphicEquiv B S hS hX hdec).symm
          (chartMeromorphicPullbackHom B S hS (Z.genericFieldMorphism B S hS hX hdec)
            (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
            (genericFieldPointChartDiagram B S hS _ V g hg) a) *
        Z.genericFibreCoefficient B S hS hX hdec L hL V g hg m := by
  rw [Z.genericFieldValue_eq_iff B S hS hX hdec L hL]
  refine (pullbackMeromorphicSection_eval_chartDiagram B S hS
    (Z.genericFieldMorphism B S hS hX hdec) (Z.restrictModule B S hS hX L)
    (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec) σ
    (genericFieldPointChartDiagram B S hS _ V g hg) _ hσ).trans ?_
  refine congrArg _ ((chartPullbackMeromorphicSectionsSheaf_tmul B S hS
    (Z.genericFieldMorphism B S hS hX hdec) (Z.restrictModule B S hS hX L)
    (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
    (genericFieldPointChartDiagram B S hS _ V g hg) a m).trans ?_)
  set x := chartMeromorphicPullbackHom B S hS (Z.genericFieldMorphism B S hS hX hdec)
      (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
      (genericFieldPointChartDiagram B S hS _ V g hg) a
  have hc := (Z.genericFieldMeromorphicEquiv B S hS hX hdec).apply_symm_apply x
  rw [Z.modulePullbackChartFMap_eq_genericFibreCoefficient_smul B S hS hX hdec L hL V g hg m,
    map_mul, hc, Z.genericFieldGenerator_id B S hS hX hdec L hL]
  set r : chartRing B S hS (Z.genericFieldSpace B S hS hX hdec).1
      (Z.genericFieldSpace B S hS hX hdec).2 (Z.genericFieldChart B S hS hX hdec) :=
    (Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).inv.hom
      (Z.genericFibreCoefficient B S hS hX hdec L hL V g hg m)
  have h := meromorphicSectionModule_smul_tmul B S hS (Z.genericFieldSpace B S hS hX hdec).1
    (Z.genericFieldSpace B S hS hX hdec).2
    ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
      (Z.restrictModule B S hS hX L)) (Z.genericFieldChart B S hS hX hdec)
    (pureMeromorphicSection B S hS _ _ _ _ (r • Z.genericFibreGenerator B S hS hX hdec L hL)) x
  refine Eq.trans ?_ ((h 1 _ rfl).symm.trans
    (h _ _ (pureMeromorphicSection_smul_eq_algebraMap_tmul B S hS _ _ _ _ r _)))
  congr 1
  exact (mul_one x).symm

/-- **`s_ξ|_Z` read on an étale chart**: if `s_ξ|_Z` is `a ⊗ m` over an étale chart `V` of `Z`
receiving `ρ_Z`, then the pullback of `a` to the generic point, times `(m / s_ξ)(ξ)`, is `1`; so
`a` at the generic point of `Z` is the ratio `(s_ξ / m)(ξ)`. -/
theorem PrimeDivisor.genericRestriction_chart
    (a : (meromorphicChartSheaf B S hS Z.subspace.toFunctor Z.closed.1).obj.obj (op V))
    (m : (Z.restrictModule B S hS hX L).val.obj (op V))
    (hσ : (Z.genericRestriction B S hS hX hdec hN L hL).eval (op V) =
      toMeromorphicSectionSheaf B S hS Z.subspace.toFunctor Z.closed.1
        (Z.restrictModule B S hS hX L) V
        (a ⊗ₜ[chartRing B S hS Z.subspace.toFunctor Z.closed.1 V] m)) :
    (Z.genericFieldMeromorphicEquiv B S hS hX hdec).symm
          (chartMeromorphicPullbackHom B S hS (Z.genericFieldMorphism B S hS hX hdec)
            (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
            (genericFieldPointChartDiagram B S hS _ V g hg) a) *
        Z.genericFibreCoefficient B S hS hX hdec L hL V g hg m = 1 := by
  rw [← Z.genericFieldValue_eq_of_eval_eq_tmul B S hS hX hdec L hL V g hg _ a m hσ]
  exact Z.genericFieldValue_genericRestriction B S hS hX hdec hN L hL

end AlgebraicGeometry.Space

end
