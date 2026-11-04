module

public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen

/-!
# The smooth compactification of a connected finite étale cover of a smooth curve

Let `X` be a smooth curve over a perfect field `k` and `Y ⟶ X` a connected finite étale cover.
Then `Y` is a smooth curve over `k`. Its smooth projective compactification `Ȳ`
([Stacks, Tag 0H1F]) is a smooth projective curve over `k`, and over its constant field `k₀`
(a finite extension of `k`) it is smooth, proper and geometrically irreducible. The open
immersion `Y ⟶ Ȳ` has finite complement. For a proper `X`,
`AlgebraicGeometry.exists_constantField_of_finiteEtale` gives the same without compactifying.

## Main results

* `AlgebraicGeometry.isCurve_finiteEtale_comp`: `Y` is a curve over `k`.
* `AlgebraicGeometry.exists_compactification_constantField_of_finiteEtale`: the compactification
  and its constant field.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- **A connected finite étale cover of a smooth curve is a smooth curve.** -/
theorem isCurve_finiteEtale_comp (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Smooth f] [IsCurve k f] [ConnectedSpace X] (Y : FiniteEtaleOver X) [ConnectedSpace Y.left] :
    IsCurve k (Y.hom ≫ f) := by
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  have : Nonempty Y.left := ConnectedSpace.toNonempty
  have : ConnectedSpace ((𝟭 Scheme).obj Y.left) := ‹ConnectedSpace Y.left›
  have : Smooth (Y.hom ≫ f) := inferInstance
  have : IsIntegral ((𝟭 Scheme).obj Y.left) :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (Y.hom ≫ f)
  have : Nonempty ((𝟭 Scheme).obj Y.left) := ‹Nonempty Y.left›
  have : IsSeparated f := (IsCurve.toIsVariety (k := k) (f := f)).toIsSeparated
  have : QuasiCompact f := (IsCurve.toIsVariety (k := k) (f := f)).toQuasiCompact
  have : IsSeparated Y.hom := inferInstance
  have : IsSeparated (Y.hom ≫ f) := inferInstance
  have : QuasiCompact (Y.hom ≫ f) := inferInstance
  have : LocallyOfFiniteType (Y.hom ≫ f) := inferInstance
  have hdimX : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one f
  have hle : topologicalKrullDim Y.left ≤ 1 := hdimX ▸ topologicalKrullDim_le_of_etale Y.hom
  have hge : 1 ≤ topologicalKrullDim Y.left := hdimX ▸
    topologicalKrullDim_le_of_surjective_of_isClosedMap Y.hom (surjective_of_finiteEtale Y)
      Y.hom.isClosedMap
  exact { topologicalKrullDim_eq_one := le_antisymm hle hge }

/-- **The compactification of a connected finite étale cover of a smooth curve, over its constant
field.** For `X` a smooth curve over a perfect field `k` and `Y ⟶ X` a connected finite étale
cover, there are a finite extension `k₀` of `k`, a smooth proper geometrically irreducible curve
`Ȳ` over `k₀` and an open immersion `j : Y ⟶ Ȳ` with finite complement, compatible with the
structure morphisms to `Spec k`. -/
theorem exists_compactification_constantField_of_finiteEtale (k : Type u) [Field k]
    [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsCurve k f]
    [ConnectedSpace X] (Y : FiniteEtaleOver X) [ConnectedSpace Y.left] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Module.Finite k K) (Ybar : Scheme.{u})
      (j : Y.left ⟶ Ybar) (_ : IsOpenImmersion j) (r : Ybar ⟶ Spec (.of K)),
      (j ≫ r) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) = Y.hom ≫ f ∧ IsProper r ∧
        Smooth r ∧ GeometricallyIrreducible r ∧ IsCurve K r ∧
        ((Set.range j.base)ᶜ).Finite := by
  have := isCurve_finiteEtale_comp k f Y
  have : Etale Y.hom := Y.prop.2
  have hreg : IsRegular Y.left := isRegular_of_smooth_over_field (Y.hom ≫ f)
  obtain ⟨-, Ybar, q, j, hj, hjq, hcurve, hproj, -, hsm, hfin, -⟩ :=
    exists_smooth_isProjectiveMorphism_compactification_of_perfectField k (Y.hom ≫ f) hreg
  have : IsProper q := isProper_of_isProjectiveMorphism q hproj
  have hdimeq : topologicalKrullDim Ybar = 1 := IsCurve.topologicalKrullDim_eq_one (f := q)
  obtain ⟨K, _, _, _, _, r, hr, hrs, hrproj, hgi, -⟩ :=
    exists_isSeparable_smooth_isProjectiveMorphism_geometricallyIrreducible k q hdimeq.le
  have : IsProper r := isProper_of_isProjectiveMorphism r hrproj
  refine ⟨K, inferInstance, inferInstance, inferInstance, Ybar, j, hj, r, ?_, inferInstance, hrs,
    hgi, { topologicalKrullDim_eq_one := hdimeq }, hfin⟩
  rw [Category.assoc, hr, hjq]
end AlgebraicGeometry
