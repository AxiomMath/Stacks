module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartPerfectComplexNoetherian
public import StacksFrontier.Homology.Tor.DerivedTensorDirectSum
public import StacksFrontier.Homology.TensorComplex.SingleTensor

/-!
# The obstruction functor of a proper flat space over a field

Over a field `k`, the functors `V ↦ H^n(K ⊗ᴸ_k V)` attached to an object `K` of `D(k)` vanish on
every vector space as soon as they vanish on `k` itself: every vector space is a direct sum of
copies of `k`, and `H^n(K ⊗ᴸ_k −)` commutes with direct sums. Applied to the perfect complex of
Situation 07YX at a chart, this says that the obstruction functor `T²` (and the tangent functor
`T¹`) of a flat, proper, finitely presented algebraic space over `k` vanishes on every
`k`-vector space once it vanishes on `k`.

## Main definitions

* `Deformation.Artin.tensorComplexLeft` — the functor `M ↦ M ⊗ P` for a fixed complex `P`,
  tensoring termwise on the left.

## Main results

* `Deformation.Artin.tensorComplexLeft_preservesColimitsOfShape` — it preserves coproducts.
* `Deformation.Artin.subsingleton_derivedCohomology_obj_of_subsingleton_self` — over a field,
  `H^n(K ⊗ᴸ_k V) = 0` for every vector space `V` once `H^n(K ⊗ᴸ_k k) = 0`.
* `AlgebraicGeometry.Space.ProperFlatLift.subsingleton_cotangentExtTwo_obj_of_subsingleton_self`
  — the same for the obstruction functor `T²` of a proper flat space over `k`, and
  `subsingleton_cotangentExtOne_obj_of_subsingleton_self` for `T¹`.

## Implementation notes

The derived tensor product `CochainComplex.DerivedTensor.derivedTensorProduct K` is computed on
a K-flat representative `P` of `K` by
`CochainComplex.DerivedTensor.derivedTensorProduct_iso_lift_of_kFlat_resolution`, so that
`H^n(K ⊗ᴸ_k M) ≅ H^n(M[0] ⊗ P) ≅ H^n(M ⊗ P)` for every module `M`. The functor
`M ↦ H^n(M ⊗ P)` commutes with coproducts because tensoring does and because coproducts of
modules are exact. No perfectness of `K` is needed.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe t u

namespace Deformation.Artin

attribute [local instance 10000] HasDerivedCategory.standard

section TensorComplexLeft

variable (A : Type u) [CommRing A]

/-- The termwise tensor product `M ⊗ P` of a module `M` with a fixed cochain complex `P`, as a
functor of `M`. -/
def tensorComplexLeft (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    ModuleCat.{u} A ⥤ CochainComplex (ModuleCat.{u} A) ℤ where
  obj M := ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  map {_ _} f :=
    { f := fun n => f ▷ P.X n
      comm' := fun n m _ => by simpa using (whisker_exchange f (P.d n m)).symm }
  map_id _ := by ext n; simp
  map_comp _ _ := by ext n; simp

/-- Tensoring a fixed complex termwise on the left with a module preserves coproducts. -/
theorem tensorComplexLeft_preservesColimitsOfShape (J : Type u)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    PreservesColimitsOfShape (Discrete J) (tensorComplexLeft A P) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun n => by
    change PreservesColimitsOfShape (Discrete J) (tensorRight (P.X n))
    exact preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (P.X n)))

end TensorComplexLeft

/-- **Over a field, `H^n(K ⊗ᴸ −)` vanishes on every vector space once it vanishes on `k`.**
Every vector space is a direct sum of copies of `k`, and `H^n(K ⊗ᴸ −)` commutes with direct
sums. -/
theorem subsingleton_derivedCohomology_obj_of_subsingleton_self {k : Type u} [Field k]
    (K : DerivedCategory (ModuleCat.{u} k)) (n : ℤ)
    (h : Subsingleton ((derivedCohomology k K n).obj (ModuleCat.of k k)))
    (V : ModuleCat.{u} k) :
    Subsingleton ((derivedCohomology k K n).obj V) := by
  classical
  obtain ⟨P, hP, ⟨κ⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative K
  obtain ⟨α⟩ := (CochainComplex.DerivedTensor.derivedTensorProduct_iso_lift_of_kFlat_resolution
      K P P (𝟙 P) hP
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} k)).app P ≪≫ κ)).1
  let X (M : ModuleCat.{u} k) : CochainComplex (ModuleCat.{u} k) ℤ :=
    (HomologicalComplex.single (ModuleCat.{u} k) (ComplexShape.up ℤ) 0).obj M
  have hiso : ∀ M : ModuleCat.{u} k, (derivedCohomology k K n).obj M ≅
      ((tensorComplexLeft k P).obj M).homology n := fun M =>
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).mapIso
        ((CochainComplex.DerivedTensor.derivedTensorProduct K).mapIso
            ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} k) 0).app M ≪≫
              ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} k)).app (X M)).symm) ≪≫
          α.app ((HomotopyCategory.quotient (ModuleCat.{u} k) (ComplexShape.up ℤ)).obj (X M)) ≪≫
          (DerivedCategory.quotientCompQhIso (ModuleCat.{u} k)).app
            ((TleftCochain (X M)).obj P)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).app _ ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ) n).mapIso
        (TotalTensorComplex.SingleTensor.singleTensorIso M P)
  let ι := Module.Free.ChooseBasisIndex k V
  let b := Module.Free.chooseBasis k V
  let E : ι → ModuleCat.{u} k := fun _ => ModuleCat.of k k
  let eV : V ≅ ∐ E :=
    (b.repr.trans (finsuppLEquivDirectSum k k ι)).toModuleIso ≪≫
      (ModuleCat.coprodIsoDirectSum E).symm
  have hk : IsZero (((tensorComplexLeft k P).obj (ModuleCat.of k k)).homology n) :=
    IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.mpr h) (hiso _).symm
  have h1 := tensorComplexLeft_preservesColimitsOfShape k ι P
  have h2 := Stacks.DerivedTensor.homologyFunctor_preservesColimitsOfShape
    (𝒜 := ModuleCat.{u} k) (J := Discrete ι) (ComplexShape.up ℤ) n
  let G := tensorComplexLeft k P ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ) n
  have hcop : IsZero (G.obj (∐ E)) :=
    IsZero.of_iso (Stacks.DerivedTensor.isZero_colimit_of_isZero _ (fun _ => hk))
      (preservesColimitIso G (Discrete.functor E))
  exact ModuleCat.isZero_iff_subsingleton.mp
    (IsZero.of_iso hcop (hiso V ≪≫ G.mapIso eV))

end Deformation.Artin

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {k : Type u} [Field k] {toS : Spec (.of k) ⟶ S} {hk : B.Contains (Spec (.of k))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver k B S hS toS hk)
  [HasDerivedCategory.{t} (modelModules x.obj.obj.left)]

/-- **The obstruction functor over a field.** For `x` a flat, proper, finitely presented
algebraic space over a field `k`, the obstruction functor `T² = Ext²(L_{X/k}, 𝒪_X ⊗_k −)`
vanishes on every `k`-vector space once it vanishes on `k`. -/
theorem subsingleton_cotangentExtTwo_obj_of_subsingleton_self
    (h : Subsingleton ((cotangentExtTwo (chartStructureMap x hx) (chartBaseRingHom x hx)).obj
      (ModuleCat.of k k)))
    (V : ModuleCat.{u} k) :
    Subsingleton ((cotangentExtTwo (chartStructureMap x hx) (chartBaseRingHom x hx)).obj V) := by
  obtain ⟨K, -, e₂, -, -⟩ :=
    exists_isPerfect_iso_cotangentExt_boundaryMap_of_isNoetherianRing x hx
  have h' : Subsingleton ((derivedCohomology k K 2).obj (ModuleCat.of k k)) :=
    (e₂.app (ModuleCat.of k k)).toLinearEquiv.toEquiv.subsingleton
  have := subsingleton_derivedCohomology_obj_of_subsingleton_self K 2 h' V
  exact (e₂.app V).symm.toLinearEquiv.toEquiv.subsingleton

/-- **The tangent functor over a field.** For `x` a flat, proper, finitely presented
algebraic space over a field `k`, the functor `T¹ = Ext¹(L_{X/k}, 𝒪_X ⊗_k −)` vanishes on
every `k`-vector space once it vanishes on `k`. -/
theorem subsingleton_cotangentExtOne_obj_of_subsingleton_self
    (h : Subsingleton ((cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx)).obj
      (ModuleCat.of k k)))
    (V : ModuleCat.{u} k) :
    Subsingleton ((cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx)).obj V) := by
  obtain ⟨K, e₁, -, -, -⟩ :=
    exists_isPerfect_iso_cotangentExt_boundaryMap_of_isNoetherianRing x hx
  have h' : Subsingleton ((derivedCohomology k K 1).obj (ModuleCat.of k k)) :=
    (e₁.app (ModuleCat.of k k)).toLinearEquiv.toEquiv.subsingleton
  have := subsingleton_derivedCohomology_obj_of_subsingleton_self K 1 h' V
  exact (e₁.app V).symm.toLinearEquiv.toEquiv.subsingleton

end AlgebraicGeometry.Space.ProperFlatLift

end
