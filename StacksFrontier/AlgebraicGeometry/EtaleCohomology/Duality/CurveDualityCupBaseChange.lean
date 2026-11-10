module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperCurveCupDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.InverseImageBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.FiniteCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupPairingBaseChange
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# The pairing of a relative curve, carried to a base change

Let `f : X ⟶ S` be a proper morphism of schemes, `ℓ ≥ 1`, `Λ = ℤ/ℓ`, and let
```
X' --g'--> X
|f'        |f
v          v
S' --g---> S
```
be a cartesian square (for instance the geometric fibre of `f` at a geometric point
`g : Spec Ω ⟶ S`). Write `E = f⁻¹Λ_S`, `K = Rf_* E` and `E'`, `K'` for the same objects of `f'`
(`Stacks.EtaleCohomology.curveDualityUnit`, `Stacks.EtaleCohomology.curveDualityComplex`). This
file carries the pairing `K ⊗^L K ⟶ Λ_S[-2]`, `(a, b) ↦ t(w_*(b ∪ a))`, from which the duality
map `Stacks.EtaleCohomology.curveDualityMap` is built, to the base change:

* `g⁻¹K ≅ K'` (`curveDualityComplexBaseChangeIso`), by proper base change, together with
  `g'⁻¹E ≅ E'` and `g⁻¹(Λ_S[0]) ≅ Λ_{S'}[0]`;
* for a multiplication `w : E ⊗^L E ⟶ E`, the multiplication `w'` on `E'` it induces
  (`curveDualityBaseChangeMultiplication`), invertible when `w` is;
* for a trace `t : K ⟶ Λ_S[-2]`, the trace `t' : K' ⟶ Λ_{S'}[-2]` it induces
  (`curveDualityBaseChangeTrace`), with `H²(t')` invertible when `H²(t)` is;
* **the pairing of `(w', t')` on `K'` is `g⁻¹` of the pairing of `(w, t)` on `K`**, read through
  the comparison of [Stacks, Tag 07A4] and `g⁻¹K ≅ K'` (`curveDualityPairing_baseChange`).

The proof is the abstract
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupPairing_baseChange`, fed with
[Stacks, Tag 0H9A] on `D(-_étale, Λ)` (`etaleModuleDerivedSquareBaseChange_adjunctionCupProduct`)
and the braiding of the comparison of [Stacks, Tag 07A4]
(`etaleDerivedInverseImageTensorIso_braiding`). No unit coherence of the comparison of Tag 07A4
enters: the multiplication `w'` is whatever `g'⁻¹ w` becomes.

The derived categories are in the standard model `HasDerivedCategory.standard`, the one of
`Stacks.EtaleCohomology.curveDualityMap`.

## Main definitions

* `Stacks.EtaleCohomology.etaleUnitSheafInverseImageIso`,
  `Stacks.EtaleCohomology.curveDualitySingleUnitInverseImageIso`,
  `Stacks.EtaleCohomology.curveDualityUnitBaseChangeIso`,
  `Stacks.EtaleCohomology.curveDualityComplexBaseChangeIso`.
* `Stacks.EtaleCohomology.curveDualityBaseChangeMultiplication`,
  `Stacks.EtaleCohomology.curveDualityBaseChangeTrace`.

## Main results

* `Stacks.EtaleCohomology.isIso_curveDualityBaseChangeMultiplication`.
* `Stacks.EtaleCohomology.isIso_homologyFunctor_map_curveDualityBaseChangeTrace`.
* `Stacks.EtaleCohomology.curveDualityPairing_baseChange`.

## References

* [Stacks Project, Tag 0H9A](https://stacks.math.columbia.edu/tag/0H9A)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0F0C](https://stacks.math.columbia.edu/tag/0F0C)
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Prod

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

open Stacks.EtaleCohomology.ExtensionTorsor

section Unit

variable (ℓ : ℕ) {S S' : Scheme.{u}} (g : S' ⟶ S)

/-- `g⁻¹ ℤ/ℓ_S ≅ ℤ/ℓ_{S'}`: the inverse image of a constant sheaf is constant. -/
def etaleUnitSheafInverseImageIso :
    (etaleModuleInverseImage.{u, 0} (ZMod ℓ) g).obj (unitSheaf (X := S) ℓ) ≅
      unitSheaf (X := S') ℓ :=
  (TorsionModules.etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) g).app
    (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))

/-- `g⁻¹(Λ_S[0]) ≅ Λ_{S'}[0]` in the derived categories. -/
def curveDualitySingleUnitInverseImageIso :
    (etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).obj
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S') ℓ) :=
  ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) g).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (etaleUnitSheafInverseImageIso ℓ g)

/-- `g⁻¹(Λ_S[0][n]) ≅ Λ_{S'}[0][n]`: the commutation of `g⁻¹` with the shift, followed by
`g⁻¹(Λ_S[0]) ≅ Λ_{S'}[0]`. -/
def curveDualityShiftedUnitInverseImageIso (n : ℤ) :
    (etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).obj
        (((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦n⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S') ℓ))⟦n⟧ :=
  ((etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).commShiftIso n).app _ ≪≫
    (shiftFunctor _ n).mapIso (curveDualitySingleUnitInverseImageIso ℓ g)

end Unit

section Square

variable (ℓ : ℕ) {S X S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S')
  (g' : X' ⟶ X)

/-- `g'⁻¹E ≅ E'` for `E = f⁻¹Λ_S` and `E' = f'⁻¹Λ_{S'}`: the two composite inverse images around
the square agree (`etaleModuleDerivedInverseImageSquareIso`) and `g⁻¹Λ_S ≅ Λ_{S'}`. -/
def curveDualityUnitBaseChangeIso (w : g' ≫ f = f' ≫ g) :
    (etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g').obj (curveDualityUnit ℓ f) ≅
      curveDualityUnit ℓ f' :=
  ((etaleModuleDerivedInverseImageSquareIso (ZMod ℓ) f g f' g' w).app _).symm ≪≫
    (etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) f').mapIso
      (curveDualitySingleUnitInverseImageIso ℓ g)

variable [NeZero ℓ]

/-- `ℤ/ℓ`, `ℓ ≥ 1`, is a torsion ring. -/
theorem isTorsion_zmod : IsAddTorsion (ZMod ℓ) :=
  fun x => isOfFinAddOrder_of_finite x

/-- **`g⁻¹K ≅ K'` by proper base change**: the base change map at `E`
(`etaleModuleDerivedSquareBaseChange`, invertible for `f` proper and the square cartesian),
followed by `Rf'_*` of `g'⁻¹E ≅ E'`. -/
def curveDualityComplexBaseChangeIso [IsProper f] (sq : IsPullback g' f' f g) :
    (etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).obj (curveDualityComplex ℓ f) ≅
      curveDualityComplex ℓ f' :=
  haveI := isIso_etaleModuleDerivedSquareBaseChange_of_isProper (ZMod ℓ) f g f' g'
    (isTorsion_zmod ℓ) sq (curveDualityUnit ℓ f)
  asIso (etaleModuleDerivedSquareBaseChange (ZMod ℓ) f g f' g' sq.w (curveDualityUnit ℓ f)) ≪≫
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f').mapIso
      (curveDualityUnitBaseChangeIso ℓ f g f' g' sq.w)

/-- **The multiplication induced on the base change**: for `m : E ⊗^L E ⟶ E`, the multiplication
`E' ⊗^L E' ⟶ E'` that `g'⁻¹ m` becomes through `g'⁻¹E ≅ E'` and the comparison of
[Stacks, Tag 07A4] along `g'`. -/
def curveDualityBaseChangeMultiplication (w : g' ≫ f = f' ≫ g)
    (m : ((etaleDerivedTensor.{u, 0} (ZMod ℓ) X).obj (curveDualityUnit ℓ f)).obj
      (curveDualityUnit ℓ f) ⟶ curveDualityUnit ℓ f) :
    ((etaleDerivedTensor.{u, 0} (ZMod ℓ) X').obj (curveDualityUnit ℓ f')).obj
      (curveDualityUnit ℓ f') ⟶ curveDualityUnit ℓ f' :=
  (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} (ZMod ℓ) X')).map
      ((curveDualityUnitBaseChangeIso ℓ f g f' g' w).inv ×ₘ
        (curveDualityUnitBaseChangeIso ℓ f g f' g' w).inv) ≫
    (etaleDerivedInverseImageTensorIso.{u, 0} (ZMod ℓ) g').inv.app
      (curveDualityUnit ℓ f, curveDualityUnit ℓ f) ≫
    (etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g').map m ≫
    (curveDualityUnitBaseChangeIso ℓ f g f' g' w).hom

omit [NeZero ℓ] in
/-- The induced multiplication is invertible when the original one is. -/
theorem isIso_curveDualityBaseChangeMultiplication (w : g' ≫ f = f' ≫ g)
    (m : ((etaleDerivedTensor.{u, 0} (ZMod ℓ) X).obj (curveDualityUnit ℓ f)).obj
      (curveDualityUnit ℓ f) ⟶ curveDualityUnit ℓ f) [IsIso m] :
    IsIso (curveDualityBaseChangeMultiplication ℓ f g f' g' w m) := by
  have : IsIso ((curveDualityUnitBaseChangeIso ℓ f g f' g' w).inv ×ₘ
      (curveDualityUnitBaseChangeIso ℓ f g f' g' w).inv) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  unfold curveDualityBaseChangeMultiplication
  infer_instance

/-- **The trace induced on the base change**: for `t : K ⟶ Λ_S[-2]`, the trace
`K' ⟶ Λ_{S'}[-2]` that `g⁻¹ t` becomes through `g⁻¹K ≅ K'` and `g⁻¹(Λ_S[-2]) ≅ Λ_{S'}[-2]`. -/
def curveDualityBaseChangeTrace [IsProper f] (sq : IsPullback g' f' f g)
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2)) :
    ShiftedHom (curveDualityComplex ℓ f')
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S') ℓ)) (-2) :=
  (curveDualityComplexBaseChangeIso ℓ f g f' g' sq).inv ≫
    (etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).map t ≫
      (curveDualityShiftedUnitInverseImageIso ℓ g (-2)).hom

/-- **The induced trace is a top-degree trace when the original one is**: `H²` of it is
invertible when `H²(t)` is, because `g⁻¹` is exact and so commutes with `H²`. -/
theorem isIso_homologyFunctor_map_curveDualityBaseChangeTrace [IsProper f]
    (sq : IsPullback g' f' f g)
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (ht : IsIso ((DerivedCategory.homologyFunctor _ 2).map t)) :
    IsIso ((DerivedCategory.homologyFunctor _ 2).map
      (curveDualityBaseChangeTrace ℓ f g f' g' sq t)) := by
  have h : IsIso ((DerivedCategory.homologyFunctor _ 2).map
      ((etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).map t)) :=
    (NatIso.isIso_map_iff (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (etaleModuleInverseImage.{u, 0} (ZMod ℓ) g) 2) t).2
      (Functor.map_isIso (etaleModuleInverseImage.{u, 0} (ZMod ℓ) g) _)
  unfold curveDualityBaseChangeTrace
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **The pairing of a relative curve is carried to the pairing of its base change.** For `f`
proper and a cartesian square, a multiplication `m : E ⊗^L E ⟶ E` and a trace
`t : K ⟶ Λ_S[-2]`, the comparison of [Stacks, Tag 07A4] along `g` at `(K, K)`, followed by
`g⁻¹K ≅ K'` in both factors and by the pairing `(a, b) ↦ t'(m'_*(b ∪ a))` of the base change,
is `g⁻¹` of the pairing `(a, b) ↦ t(m_*(b ∪ a))` followed by `g⁻¹(Λ_S[-2]) ≅ Λ_{S'}[-2]`. Here
`m'` and `t'` are `curveDualityBaseChangeMultiplication` and `curveDualityBaseChangeTrace`, and
the pairings are the ones whose adjoints are `curveDualityMap`. -/
theorem curveDualityPairing_baseChange [IsProper f] (sq : IsPullback g' f' f g)
    (m : ((etaleDerivedTensor.{u, 0} (ZMod ℓ) X).obj (curveDualityUnit ℓ f)).obj
      (curveDualityUnit ℓ f) ⟶ curveDualityUnit ℓ f)
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2)) :
    (etaleDerivedInverseImageTensorIso.{u, 0} (ZMod ℓ) g).hom.app
        (curveDualityComplex ℓ f, curveDualityComplex ℓ f) ≫
      (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} (ZMod ℓ) S')).map
          ((curveDualityComplexBaseChangeIso ℓ f g f' g' sq).hom ×ₘ
            (curveDualityComplexBaseChangeIso ℓ f g f' g' sq).hom) ≫
        (etaleDerivedTensorBraidingIso.{u, 0} (ZMod ℓ) S' _ _).inv ≫ curveDualityCup ℓ f' ≫
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f').map
              (curveDualityBaseChangeMultiplication ℓ f g f' g' sq.w m) ≫
            curveDualityBaseChangeTrace ℓ f g f' g' sq t =
      (etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).map
          ((etaleDerivedTensorBraidingIso.{u, 0} (ZMod ℓ) S _ _).inv ≫ curveDualityCup ℓ f ≫
            (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).map m ≫ t) ≫
        (curveDualityShiftedUnitInverseImageIso ℓ g (-2)).hom :=
  Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupPairing_baseChange
    (adjf := etaleModuleDerivedInverseImageAdj.{u, 0} (ZMod ℓ) f)
    (adjf' := etaleModuleDerivedInverseImageAdj.{u, 0} (ZMod ℓ) f')
    (A := Functor.uncurry.obj (etaleDerivedTensor.{u, 0} (ZMod ℓ) S))
    (A' := Functor.uncurry.obj (etaleDerivedTensor.{u, 0} (ZMod ℓ) S'))
    (B := Functor.uncurry.obj (etaleDerivedTensor.{u, 0} (ZMod ℓ) X))
    (B' := Functor.uncurry.obj (etaleDerivedTensor.{u, 0} (ZMod ℓ) X'))
    (αf := (etaleDerivedInverseImageTensorIso.{u, 0} (ZMod ℓ) f).hom)
    (αf' := (etaleDerivedInverseImageTensorIso.{u, 0} (ZMod ℓ) f').hom)
    (αg := (etaleDerivedInverseImageTensorIso.{u, 0} (ZMod ℓ) g).hom)
    (αg' := etaleDerivedInverseImageTensorIso.{u, 0} (ZMod ℓ) g')
    (bc := Stacks.CategoryTheory.BaseChange.twoSquare
      (etaleModuleDerivedInverseImageAdj.{u, 0} (ZMod ℓ) f)
      (etaleModuleDerivedInverseImageAdj.{u, 0} (ZMod ℓ) f')
      (etaleModuleDerivedInverseImageSquareIso (ZMod ℓ) f g f' g' sq.w) (Iso.refl _))
    (E := curveDualityUnit ℓ f) (u := curveDualityUnitBaseChangeIso ℓ f g f' g' sq.w) (w := m)
    (t := t) (ψ := (curveDualityShiftedUnitInverseImageIso ℓ g (-2)).hom)
    (κ := curveDualityComplexBaseChangeIso ℓ f g f' g' sq) (hκ := rfl)
    (hcup := etaleModuleDerivedSquareBaseChange_adjunctionCupProduct (ZMod ℓ) f g f' g' sq.w
      (curveDualityUnit ℓ f) (curveDualityUnit ℓ f))
    (β := etaleDerivedTensorBraidingIso.{u, 0} (ZMod ℓ) S _ _)
    (β₁ := etaleDerivedTensorBraidingIso.{u, 0} (ZMod ℓ) S' _ _)
    (β₂ := etaleDerivedTensorBraidingIso.{u, 0} (ZMod ℓ) S' _ _)
    (hβ := etaleDerivedInverseImageTensorIso_braiding (ZMod ℓ) g _ _)
    (hβ' := open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi in
      TensorHomAdjunction.uncurry_transportTensor_map_braiding
        (etaleDerivedEquivalence.{u, 0} (ZMod ℓ) S') _
        (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
          (etaleRingedSite.{u, 0} (ZMod ℓ) S') _).hom _ _)

end Square

end Stacks.EtaleCohomology

end
