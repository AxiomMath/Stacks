module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicDenseChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicGenericPointValue

/-!
# The meromorphic value of a section of a module trivialised at the codimension-zero points

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B` satisfying conditions (a),
(b) and (c) of Stacks 0ENA, let `P` be a presentation of its schematic locus at the
codimension-zero points, and let `M` be a sheaf of `𝒪_X`-modules together with a trivialisation
`τ_η : j_η^*M ≅ 𝒪_{Spec(𝒪_{X, η})}` at every point `η` of codimension `0` — the choice of
generators `s_η ∈ M_η` that the proof of Stacks 0EPQ makes.

The first conclusion of Stacks 0ENA says that the canonical comparison identifies the
meromorphic functions over an étale chart `U` with the product over `η ∈ X⁰` of the regular
functions on `U ×_X Spec(𝒪_{X, η})`.  So the family of the **values at the codimension-zero
points** of a section of `M` over `U`, which is
`AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointValue`, is the comparison image
of a unique meromorphic function on `U`: the **meromorphic value** of the section.

The value map is `𝒪_X`-linear and natural, so it is a morphism of `𝒪_X`-modules
`M ⟶ 𝒦_X`; each of the three properties is checked by applying the comparison and using the
corresponding property of the values at the points, the comparisons being morphisms of sheaves of
rings.  And the meromorphic value of a free generator **multiplies injectively**, because each of
its values at the points does.

## Main definitions

* `AlgebraicGeometry.Space.CodimensionZeroPresentation.meromorphicValue` is the meromorphic value
  of a section.
* `…meromorphicValueHom` is the resulting morphism of presheaves of `𝒪_X`-modules `M ⟶ 𝒦_X`.

## Main results

* `…genericPointComparison_meromorphicValue`: the defining property, that the comparison at `η`
  carries the meromorphic value to the value at `η`.
* `…injective_mul_meromorphicValue`: **multiplication by the meromorphic value of a free
  generator is injective** on the meromorphic functions over every chart over the chart of the
  generator.

## Implementation notes

The target of `…meromorphicValueHom` is `𝒦_X` read as a presheaf of `𝒪_X`-modules by restriction
of scalars along `𝒪_X ⟶ 𝒦_X`, which is the form the change-of-rings adjunction of Stacks 03CU
consumes: the morphism of `𝒦_X`-modules `𝒦_X(M) ⟶ 𝒦_X` that the existence of a regular
meromorphic section is read off from is its adjoint transpose.

Bijectivity of the comparison over *every* chart, not only over the affine ones, is
`…bijective_pi_genericPointComparison_app_of_isIso`; over an affine chart it is the
affine-chart computation of the first conclusion of Stacks 0ENA, and over an arbitrary chart it
follows because the comparison of sheaves is then an isomorphism.  This is the only place where
conditions (a) and (b) of Stacks 0ENA are used.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

namespace CodimensionZeroPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (P : CodimensionZeroPresentation B S hS X.1) (M : Modules.{u, u} B S hS X.1 X.2)
    (τ : (η : CodimensionZeroPoints B S hS X.1) → P.genericPointPullback η.2 M ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (P.specStalkSpace η.2).1 (P.specStalkSpace η.2).2).O))
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)

/-! ### The meromorphic value -/

/-- The comparison of the first conclusion of Stacks 0ENA over a chart, as a bijection of the
meromorphic functions with the product of the regular functions at the codimension-zero points. -/
noncomputable def genericPointComparisonEquiv (U : SmallEtale B S hS X.1) :
    (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) ≃
      ∀ η : CodimensionZeroPoints B S hS X.1,
        (P.genericPointStructureSheaf η.2).obj.obj (op U) :=
  Equiv.ofBijective _ (P.bijective_pi_genericPointComparison_app_of_isIso hwa hfin U)

/-- The bijection `genericPointComparisonEquiv` sends a meromorphic function to the family of its
comparison images at the codimension-zero points. -/
@[simp]
theorem genericPointComparisonEquiv_apply (U : SmallEtale B S hS X.1)
    (s : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U))
    (η : CodimensionZeroPoints B S hS X.1) :
    P.genericPointComparisonEquiv hwa hfin U s η =
      ((P.genericPointComparison η.2).hom.app (op U)).hom s :=
  rfl

/-- **The meromorphic value of a section of `M` over an étale chart**: the unique meromorphic
function whose comparison image at each codimension-zero point `η` is the value of the section
at `η`. -/
noncomputable def meromorphicValue (U : SmallEtale B S hS X.1) (s : M.val.obj (op U)) :
    (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) :=
  (P.genericPointComparisonEquiv hwa hfin U).symm
    fun η => P.genericPointValue η.2 M (τ η).hom U s

/-- **The defining property of the meromorphic value**: its comparison image at `η` is the value
at `η`. -/
theorem genericPointComparison_meromorphicValue (U : SmallEtale B S hS X.1)
    (s : M.val.obj (op U)) (η : CodimensionZeroPoints B S hS X.1) :
    ((P.genericPointComparison η.2).hom.app (op U)).hom
        (P.meromorphicValue M τ hwa hfin U s) =
      P.genericPointValue η.2 M (τ η).hom U s :=
  congrFun ((P.genericPointComparisonEquiv hwa hfin U).apply_symm_apply
    fun η => P.genericPointValue η.2 M (τ η).hom U s) η

include hwa hfin in
/-- Two meromorphic functions with the same comparison image at every codimension-zero point are
equal. -/
theorem eq_of_genericPointComparison_eq (U : SmallEtale B S hS X.1)
    {a b : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)}
    (h : ∀ η : CodimensionZeroPoints B S hS X.1,
      ((P.genericPointComparison η.2).hom.app (op U)).hom a =
        ((P.genericPointComparison η.2).hom.app (op U)).hom b) :
    a = b :=
  (P.bijective_pi_genericPointComparison_app_of_isIso hwa hfin U).injective (funext h)

/-- The meromorphic value is additive. -/
theorem meromorphicValue_add (U : SmallEtale B S hS X.1) (s s' : M.val.obj (op U)) :
    P.meromorphicValue M τ hwa hfin U (s + s') =
      P.meromorphicValue M τ hwa hfin U s + P.meromorphicValue M τ hwa hfin U s' := by
  refine P.eq_of_genericPointComparison_eq hwa hfin U fun η => ?_
  rw [P.genericPointComparison_meromorphicValue M τ hwa hfin U (s + s') η,
    map_add, P.genericPointComparison_meromorphicValue M τ hwa hfin U s η,
    P.genericPointComparison_meromorphicValue M τ hwa hfin U s' η]
  exact P.genericPointValue_add η.2 M (τ η).hom U s s'

/-- The meromorphic value is `𝒪_X`-linear: the value of `r • s` is the image of `r` in `𝒦_X`
times the value of `s`. -/
theorem meromorphicValue_smul (U : SmallEtale B S hS X.1)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj (op U))
    (s : M.val.obj (op U)) :
    P.meromorphicValue M τ hwa hfin U (r • s) =
      ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom r *
        P.meromorphicValue M τ hwa hfin U s := by
  refine P.eq_of_genericPointComparison_eq hwa hfin U fun η => ?_
  rw [P.genericPointComparison_meromorphicValue M τ hwa hfin U (r • s) η,
    map_mul, P.genericPointComparison_meromorphicValue M τ hwa hfin U s η,
    P.genericPointComparison_app_toMeromorphicFunctionSheaf η.2 U r]
  exact P.genericPointValue_smul η.2 M (τ η).hom U r s

/-- The meromorphic value is natural in the chart. -/
theorem meromorphicValue_map {U V : SmallEtale B S hS X.1} (k : U ⟶ V)
    (s : M.val.obj (op V)) :
    P.meromorphicValue M τ hwa hfin U ((M.val.map k.op).hom s) =
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map k.op).hom
        (P.meromorphicValue M τ hwa hfin V s) := by
  refine P.eq_of_genericPointComparison_eq hwa hfin U fun η => ?_
  rw [P.genericPointComparison_meromorphicValue M τ hwa hfin U ((M.val.map k.op).hom s) η,
    P.genericPointValue_map η.2 M (τ η).hom k s,
    ← P.genericPointComparison_meromorphicValue M τ hwa hfin V s η]
  exact (ConcreteCategory.congr_hom ((P.genericPointComparison η.2).hom.naturality k.op) _).symm

/-! ### The morphism of modules, and injectivity at a free generator -/

/-- **The meromorphic value as a morphism of presheaves of `𝒪_X`-modules `M ⟶ 𝒦_X`**, the target
read by restriction of scalars along `𝒪_X ⟶ 𝒦_X`. -/
noncomputable def meromorphicValueHom :
    M.val ⟶ (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars
        (toMeromorphicFunctionSheaf B S hS X.1 X.2).hom).obj
      (PresheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O).obj) :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun s => P.meromorphicValue M τ hwa hfin U.unop s)
          fun s s' => P.meromorphicValue_add M τ hwa hfin U.unop s s')
      naturality := fun U V f => by
        ext s
        exact P.meromorphicValue_map M τ hwa hfin f.unop s }
    fun U r m => P.meromorphicValue_smul M τ hwa hfin U.unop r m

/-- The component of `meromorphicValueHom` over a chart `U` sends a section `s` to its
meromorphic value. -/
@[simp]
theorem meromorphicValueHom_app (U : SmallEtale B S hS X.1) (s : M.val.obj (op U)) :
    ((P.meromorphicValueHom M τ hwa hfin).app (op U)).hom s =
      P.meromorphicValue M τ hwa hfin U s :=
  rfl

include hwa hfin in
/-- **Multiplication by the meromorphic value of a free generator is injective**: if `e` is a
compatible family of free generators of `M` over the charts over `V`, then multiplication by the
meromorphic value of `e U k` is injective on the meromorphic functions over `U`.

Each of its values at the codimension-zero points multiplies injectively, by
`…injective_mul_genericPointValue`, and the comparisons of the first conclusion of Stacks 0ENA
are jointly injective. -/
theorem injective_mul_meromorphicValue
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property M)
    (V : SmallEtale B S hS X.1)
    (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → M.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (M.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hbij : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)
    (U : SmallEtale B S hS X.1) (k : U ⟶ V) :
    Function.Injective fun z : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) ↦
      z * P.meromorphicValue M τ hwa hfin U (e U k) := by
  intro z z' hz
  refine P.eq_of_genericPointComparison_eq hwa hfin U fun η => ?_
  refine P.injective_mul_genericPointValue η.2 M (τ η).hom inferInstance hM V e hcompat hbij
    U k ?_
  have h := congrArg ((P.genericPointComparison η.2).hom.app (op U)).hom hz
  simpa only [map_mul, P.genericPointComparison_meromorphicValue M τ hwa hfin U (e U k) η] using h

end CodimensionZeroPresentation

end AlgebraicGeometry.Space

end
