module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GaloisFixedComponentDescent
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.ConjugateComponents
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Galois action on geometric irreducible components and change of ground field

Let `k` be a field with separable algebraic closure `ksep`, and let `X` be a scheme over `k`.
The group `ksep ≃ₐ[k] ksep` acts, through its opposite, on the irreducible components of
`X_{ksep}` (`AlgebraicGeometry.galoisActionOnGeometricIrreducibleComponents`). This file
assembles the two properties of that action asserted by Tag 038J: its fixed points are the base
changes of the geometrically irreducible components of `X`, and for an extension `k'/k` with
separable algebraic closure `ksep'` containing `ksep`, the bijection between the irreducible
components of `X_{ksep'}` and of `X_{ksep}` intertwines the two actions through restriction of
automorphisms.

## Main definitions

* `AlgebraicGeometry.irreducibleComponentsBaseChangeComparisonEquiv`: for a separably closed
  field `ksep` and an extension `ksep'/ksep`, the bijection from the irreducible components of
  `X_{ksep'}` to those of `X_{ksep}` given by taking images along the comparison map.

## Main results

* `AlgebraicGeometry.galoisActionOnGeometricIrreducibleComponents_fixed_iff_and_compatible`:
  Tag 038J, both properties of the canonical action, with no hypothesis beyond those of the
  source.

## Implementation notes

The bijection is Tag 038H in the form `AlgebraicGeometry.bijOn_image_baseChangeComparison`: a
separably closed field is separably closed in each of its extensions, so its separable closure in
`ksep'` is trivial. A chosen embedding of `ksep` into `ksep'` over `k` is represented by an
algebra structure with the scalar tower condition, and the restriction map
`ksep' ≃ₐ[k'] ksep' → ksep ≃ₐ[k] ksep` is `AlgEquiv.restrictNormalHom` after restricting scalars
to `k`. The base change `X_{ksep'}` is the fibre product over `Spec k`, on which
`ksep' ≃ₐ[k'] ksep'` acts through its image in `ksep' ≃ₐ[k] ksep'`.

## References

* [Stacks Project, Tag 038H](https://stacks.math.columbia.edu/tag/038H)
* [Stacks Project, Tag 038J](https://stacks.math.columbia.edu/tag/038J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- For a tower `k → ksep → ksep'` of fields with `ksep` separably closed, taking images along
the comparison map `X_{ksep'} ⟶ X_{ksep}` is a bijection between the irreducible components of
the two base changes (Tag 038H). -/
@[ega "IV 4.4.6" "irreducible clause"]
public noncomputable def irreducibleComponentsBaseChangeComparisonEquiv
    (k ksep ksep' : Type u) [Field k] [Field ksep] [Field ksep']
    [Algebra k ksep] [Algebra ksep ksep'] [Algebra k ksep'] [IsScalarTower k ksep ksep']
    [hsep : IsSepClosed ksep] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    irreducibleComponents
        (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap k ksep')))) ≃
      irreducibleComponents
        (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap k ksep)))) :=
  (bijOn_image_baseChangeComparison k ksep ksep'
    (IntermediateField.eq_bot_of_isSepClosed_of_isSeparable _) X f).equiv _

/-- The bijection on irreducible components sends a component to its image under the comparison
map. -/
@[simp, ega "IV 4.4.6" "irreducible clause"]
public theorem irreducibleComponentsBaseChangeComparisonEquiv_apply_coe
    (k ksep ksep' : Type u) [Field k] [Field ksep] [Field ksep']
    [Algebra k ksep] [Algebra ksep ksep'] [Algebra k ksep'] [IsScalarTower k ksep ksep']
    [IsSepClosed ksep] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (Z : irreducibleComponents
      (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap k ksep'))))) :
    (irreducibleComponentsBaseChangeComparisonEquiv k ksep ksep' X f Z : Set _) =
      (baseChangeComparison k ksep ksep' X f).base '' (Z : Set _) :=
  rfl

/-- **Stacks Project, Tag 038J.** Let `k` be a field with separable algebraic closure `ksep` and
let `X` be a scheme over `k`. The canonical action of `Gal(ksep/k)ᵐᵒᵖ` on the irreducible
components of `X_{ksep}` has the following properties.

1. A component `Tbar` is fixed by the action if and only if there is an irreducible component
   `T` of `X`, geometrically irreducible over `k`, with `T_{ksep} = Tbar`.
2. For every field extension `k'/k` with separable algebraic closure `ksep'`, and every embedding
   `ksep → ksep'` over `k`, taking images along `X_{ksep'} ⟶ X_{ksep}` is a bijection on
   irreducible components (Tag 038H), and it intertwines the action of `Gal(ksep'/k')` with
   the action of `Gal(ksep/k)` through restriction of automorphisms.

Geometric irreducibility of `T` is that of its reduced induced closed subscheme over `k`, and
`T_{ksep}` is the inverse image of `T` in `X_{ksep}`. -/
@[stacks 038J, ega "IV 4.5.21" "more general"]
public theorem galoisActionOnGeometricIrreducibleComponents_fixed_iff_and_compatible
    (k ksep : Type u) [Field k] [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    (∀ Tbar : (galoisActionOnGeometricIrreducibleComponents k ksep (Over.mk f)).V,
      (∀ σ : MulOpposite (ksep ≃ₐ[k] ksep),
        ConcreteCategory.hom
          ((galoisActionOnGeometricIrreducibleComponents k ksep (Over.mk f)).ρ σ) Tbar = Tbar) ↔
        ∃ T : irreducibleComponents X,
          GeometricallyIrreducible
            ((Scheme.IdealSheafData.vanishingIdeal
                ⟨(T : Set X), isClosed_of_mem_irreducibleComponents T.1 T.2⟩).subschemeι ≫ f) ∧
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k ksep)))).base ⁻¹'
            (T : Set X) = Tbar.1) ∧
    ∀ (k' ksep' : Type u) [Field k'] [Field ksep']
      [Algebra k k'] [Algebra k' ksep'] [Algebra k ksep'] [Algebra ksep ksep']
      [IsScalarTower k k' ksep'] [IsScalarTower k ksep ksep'] [IsSepClosure k' ksep'],
      Set.BijOn (fun Z ↦ (baseChangeComparison k ksep ksep' X f).base '' Z)
          (irreducibleComponents
            (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap k ksep')))))
          (irreducibleComponents
            (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap k ksep))))) ∧
        ∀ (σ : MulOpposite (ksep' ≃ₐ[k'] ksep'))
          (Z : (galoisActionOnGeometricIrreducibleComponents k ksep' (Over.mk f)).V),
          irreducibleComponentsBaseChangeComparisonEquiv k ksep ksep' (hsep :=
              IsSepClosure.sep_closed k) X f
            (ConcreteCategory.hom
              ((galoisActionOnGeometricIrreducibleComponents k ksep' (Over.mk f)).ρ
                (MulOpposite.op (AlgEquiv.restrictScalars k σ.unop))) Z) =
          ConcreteCategory.hom
            ((galoisActionOnGeometricIrreducibleComponents k ksep (Over.mk f)).ρ
              (MulOpposite.op
                ((AlgEquiv.restrictNormalHom ksep) (AlgEquiv.restrictScalars k σ.unop))))
            (irreducibleComponentsBaseChangeComparisonEquiv k ksep ksep' (hsep :=
              IsSepClosure.sep_closed k) X f Z) := by
  have : IsSepClosed ksep := IsSepClosure.sep_closed k
  refine ⟨fixed_geometricComponent_iff_exists_geometricallyIrreducible_component k ksep X f,
    fun k' ksep' _ _ _ _ _ _ _ _ _ ↦ ⟨bijOn_image_baseChangeComparison k ksep ksep'
      (IntermediateField.eq_bot_of_isSepClosed_of_isSeparable _) X f, fun σ Z ↦ ?_⟩⟩
  exact galoisActionOnGeometricIrreducibleComponents_equivariant k k' ksep ksep' X f
    (irreducibleComponentsBaseChangeComparisonEquiv k ksep ksep' X f) (fun _ ↦ rfl) σ Z

end AlgebraicGeometry

end
