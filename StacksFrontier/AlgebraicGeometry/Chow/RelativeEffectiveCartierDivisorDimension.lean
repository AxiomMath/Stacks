module

public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.BaseChangeDivisor
public import StacksFrontier.AlgebraicGeometry.FibreDimension.AffineComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenaryExamples
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeEffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Dimension.Equidimensional
public import StacksCore.Tactic.StacksAttribute

/-!
# The relative dimension of a relative effective Cartier divisor

Let `p : X ⟶ Y` be flat and locally of finite type of relative dimension `r + 1` and let
`i : D ⟶ X` be a relative effective Cartier divisor on `X/Y` (Stacks 062T). Then
`p|_D : D ⟶ Y` has relative dimension `r`.

The fibre of `p|_D` over `s ∈ Y` is the restriction of `D` to the fibre `X_s`, an effective
Cartier divisor there (Stacks 056Q). Its dimension is given by the **dimension drop** of an
effective Cartier divisor: on an equidimensional scheme of dimension `n` locally of finite type
over a field, every irreducible component of a nonempty effective Cartier divisor has dimension
`n - 1`.

## Main results

* `Stacks.Chow.topologicalKrullDim_eq_iSup_irreducibleComponents` — the dimension of a space is
  the supremum of the dimensions of its irreducible components.
* `Stacks.Chow.topologicalKrullDim_irreducibleComponents_of_isEffectiveCartierDivisor` — the
  dimension drop, over a base situation whose dimension function vanishes at closed points: every
  irreducible component of a nonempty effective Cartier divisor on an equidimensional scheme of
  dimension `n` has dimension `n - 1`, and so does the divisor.
* `AlgebraicGeometry.relativeDimension_of_isRelativeEffectiveCartierDivisor` — **the relative
  dimension of a relative effective Cartier divisor**: if `p` has relative dimension `r + 1` then
  `p|_D` has relative dimension `r`.

## References

* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
* [Stacks Project, Tag 056Q](https://stacks.math.columbia.edu/tag/056Q)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 02IA](https://stacks.math.columbia.edu/tag/02IA)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The dimension of a space through its irreducible components -/

/-- The dimension of a space is the supremum of the dimensions of its irreducible components. -/
@[ega "0 14.1.4" "(ii), special case", ega "IV 14.2.4" "more general"]
theorem topologicalKrullDim_eq_iSup_irreducibleComponents (T : Type*) [TopologicalSpace T] :
    topologicalKrullDim T =
      ⨆ W : Set T, ⨆ (_ : W ∈ irreducibleComponents T), topologicalKrullDim W := by
  refine le_antisymm ?_ (iSup_le fun W ↦ iSup_le fun _ ↦ topologicalKrullDim_subspace_le T W)
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun Z ↦ ?_
  obtain ⟨W, hW, hZW⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (Z : Set T) Z.isIrreducible
  refine le_iSup_of_le W (le_iSup_of_le hW ?_)
  calc
    (Order.height Z : WithBot ℕ∞) ≤
        (Order.height (⟨W, hW.1, isClosed_of_mem_irreducibleComponents W hW⟩ :
          IrreducibleCloseds T) : WithBot ℕ∞) := by
      exact_mod_cast Order.height_mono (show Z ≤ _ from hZW)
    _ ≤ topologicalKrullDim W := height_le_topologicalKrullDim _

/-- On an equidimensional space the dimension is the dimension of any irreducible component. -/
@[ega "0 14.1.3" "finite dimension"]
private theorem topologicalKrullDim_eq_of_equidimensional {T : Type u}
    [TopologicalSpace T] (hT : Equidimensional T) {W : Set T} (hW : W ∈ irreducibleComponents T) :
    topologicalKrullDim T = topologicalKrullDim W := by
  rw [topologicalKrullDim_eq_iSup_irreducibleComponents T]
  exact le_antisymm (iSup_le fun W' ↦ iSup_le fun hW' ↦ (hT W' hW' W hW).le)
    (le_iSup_of_le W (le_iSup_of_le hW le_rfl))

/-- Equidimensionality is a topological property, so it transfers along a homeomorphism. -/
private theorem equidimensional_of_homeomorph {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (hB : TopologicalSpace.Equidimensional B) :
    TopologicalSpace.Equidimensional A := by
  intro Z hZ W hW
  calc topologicalKrullDim Z = topologicalKrullDim (e '' Z) :=
        (e.image Z).isHomeomorph.topologicalKrullDim_eq
    _ = topologicalKrullDim (e '' W) :=
        hB _ (e.image_mem_irreducibleComponents hZ) _ (e.image_mem_irreducibleComponents hW)
    _ = topologicalKrullDim W := (e.image W).isHomeomorph.topologicalKrullDim_eq.symm

/-! ### The dimension of an irreducible component as a closed subscheme -/

/-- The reduced induced structure on the closure of a point has, as a topological space, the
dimension of that closure. -/
private lemma topologicalKrullDim_integralComponentAt {A : Scheme.{u}} (x : A) :
    topologicalKrullDim (integralComponentAt x).subscheme =
      topologicalKrullDim (closure ({x} : Set A)) := by
  have hrange : Set.range (integralComponentAt x).subschemeι.base = closure ({x} : Set A) := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
  calc topologicalKrullDim (integralComponentAt x).subscheme
      = topologicalKrullDim (Set.univ : Set (integralComponentAt x).subscheme) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).symm
    _ = topologicalKrullDim (Set.range (integralComponentAt x).subschemeι.base) := by
        rw [← Set.image_univ]
        exact ((integralComponentAt x).subschemeι.isClosedEmbedding.homeomorphImage
          Set.univ).isHomeomorph.topologicalKrullDim_eq
    _ = topologicalKrullDim (closure ({x} : Set A)) := by rw [hrange]

/-- The relative dimension of a point of a scheme locally of finite type over the base equals,
after truncation, the dimension of the closure of that point. -/
private lemma topologicalKrullDim_closure_eq_relativeDimension_toNat (C : ChowSituation.{u})
    [JacobsonSpace C.S]
    (hδ : ∀ t : C.S, IsClosed ({t} : Set C.S) → C.dimensionFunction t = 0)
    {A : Scheme.{u}} (g : A ⟶ C.S) [LocallyOfFiniteType g] (x : A) :
    topologicalKrullDim (closure ({x} : Set A)) =
      ((relativeDimension C.dimensionFunction g x).toNat : WithBot ℕ∞) := by
  let := isIntegral_integralComponentAt x
  have hgen : (integralComponentAt x).subschemeι.base
      (genericPoint (integralComponentAt x).subscheme) = x :=
    genericPointOf_integralComponentAt x
  have h := topologicalKrullDim_eq_relativeDimension_toNat C hδ g
    (integralComponentAt x).subschemeι (genericPoint (integralComponentAt x).subscheme)
    (genericPoint_spec (integralComponentAt x).subscheme)
  rw [← topologicalKrullDim_integralComponentAt x, h, hgen]

/-! ### The dimension drop of an effective Cartier divisor -/

/-- **The dimension drop of an effective Cartier divisor.** Let `X` be equidimensional of
dimension `n` and locally of finite type over the base scheme of a situation whose dimension
function vanishes at closed points, and let `D ⊆ X` be a nonempty effective Cartier divisor.
Then every irreducible component of `D` has dimension `n - 1`, and so does `D`. -/
theorem topologicalKrullDim_irreducibleComponents_of_isEffectiveCartierDivisor
    (C : ChowSituation.{u}) [JacobsonSpace C.S]
    (hδ : ∀ t : C.S, IsClosed ({t} : Set C.S) → C.dimensionFunction t = 0)
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (n : ℕ)
    (hX : Equidimensional X) (hXdim : topologicalKrullDim X = (n : WithBot ℕ∞))
    (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDne : Nonempty D.subscheme) :
    (∀ W : Set D.subscheme, W ∈ irreducibleComponents D.subscheme →
        topologicalKrullDim W = ((n - 1 : ℕ) : WithBot ℕ∞)) ∧
      topologicalKrullDim D.subscheme = ((n - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨dX, hdX⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
    C.dimensionFunction f
  have hdDim : IsDimensionFunctionForCatenary (relativeDimension C.dimensionFunction f) := by
    constructor
    · intro x z h hne
      rw [← hdX x, ← hdX z]
      exact dX.strictAnti_specializes h hne
    · intro x z h
      rw [← hdX x, ← hdX z]
      exact dX.step_immediate h
  have hSober : StacksSober X := stacksSober_iff_t0_and_quasiSober.2 ⟨inferInstance, inferInstance⟩
  have hcomponents : ∀ W : Set D.subscheme, W ∈ irreducibleComponents D.subscheme →
      topologicalKrullDim W = ((n - 1 : ℕ) : WithBot ℕ∞) := by
    intro W hW
    set ξ : D.subscheme := (genericPoints.ofComponent ⟨W, hW⟩).1 with hξdef
    have hξ : IsGenericPoint ξ W := genericPoints.isGenericPoint_ofComponent ⟨W, hW⟩
    set y : X := D.subschemeι.base ξ with hydef
    have hcoheight : Order.coheight y = (1 : ℕ∞) := by
      have hcartier := AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor
        D hD ξ ⟨⟨W, hW⟩, hξ⟩
      rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at hcartier
      exact_mod_cast hcartier
    obtain ⟨A, hA, hyA⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({y} : Set X)) isIrreducible_singleton.closure
    set η : X := (genericPoints.ofComponent ⟨A, hA⟩).1 with hηdef
    have hηA : IsGenericPoint η A := genericPoints.isGenericPoint_ofComponent ⟨A, hA⟩
    have hηy : η ⤳ y := hηA.specializes (hyA (subset_closure rfl))
    set T : IrreducibleCloseds X :=
      ⟨A, hA.1, isClosed_of_mem_irreducibleComponents A hA⟩ with hTdef
    have hTeq : IrreducibleCloseds.closureSingleton η = T := IrreducibleCloseds.ext hηA
    have hcoheightV : Order.coheight (IrreducibleCloseds.closureSingleton y) = (1 : ℕ∞) := by
      have hV : (irreducibleSetEquivPoints (α := X)).symm y =
          IrreducibleCloseds.closureSingleton y := IrreducibleCloseds.ext rfl
      calc Order.coheight (IrreducibleCloseds.closureSingleton y)
          = Order.coheight ((irreducibleSetEquivPoints (α := X)).symm y) :=
            congrArg Order.coheight hV.symm
        _ = Order.coheight y :=
            Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm y
        _ = 1 := hcoheight
    have hVT : IrreducibleCloseds.closureSingleton y ≤ T := hyA
    have hTmax : IsMax T := fun Z hZ ↦ hA.2 Z.isIrreducible hZ
    have hVTne : IrreducibleCloseds.closureSingleton y ≠ T := by
      intro heq
      rw [heq, Order.coheight_eq_zero.mpr hTmax] at hcoheightV
      norm_num at hcoheightV
    have htopcod : IrreducibleClosedsCodim.topCodim
        (IrreducibleCloseds.closureSingleton y) T = 1 := by
      refine le_antisymm ?_ (one_le_topCodim_of_lt _ _ (lt_of_le_of_ne hVT hVTne))
      rw [IrreducibleClosedsCodim.topCodim_le_iff]
      intro q hhead _
      have hlen : (q.length : ℕ∞) ≤
          Order.coheight (IrreducibleCloseds.closureSingleton y) := by
        rw [← hhead]
        exact Order.length_le_coheight_head
      simpa [hcoheightV] using hlen
    have hformula := (isCatenarySpace_and_topCodim_eq_of_isDimensionFunction X hSober
      (relativeDimension C.dimensionFunction f) hdDim).2 η y hηy
    rw [hTeq] at hformula
    have hnot : η ≠ y := by
      intro heq
      rw [← hTeq, heq, topCodim_self_eq_zero] at htopcod
      norm_num at htopcod
    have hdiff : relativeDimension C.dimensionFunction f η -
        relativeDimension C.dimensionFunction f y = 1 := by
      have hnat : (((relativeDimension C.dimensionFunction f η -
          relativeDimension C.dimensionFunction f y).toNat : ℕ) : ℤ) = 1 := by
        exact_mod_cast (hformula.symm.trans htopcod)
      have hlt : relativeDimension C.dimensionFunction f y <
          relativeDimension C.dimensionFunction f η := hdDim.strict_spec hηy hnot
      omega
    have hdη : relativeDimension C.dimensionFunction f η = (n : ℤ) := by
      have h := topologicalKrullDim_closure_eq_relativeDimension_toNat C hδ f η
      rw [hηA, ← topologicalKrullDim_eq_of_equidimensional hX hA, hXdim] at h
      have hnonneg : 0 ≤ relativeDimension C.dimensionFunction f η :=
        relativeDimension_nonneg C hδ f η
      have hcast : (n : ℕ) = (relativeDimension C.dimensionFunction f η).toNat := by
        exact_mod_cast h
      omega
    have hdy : relativeDimension C.dimensionFunction f y = (n : ℤ) - 1 := by omega
    have hrelξ : relativeDimension C.dimensionFunction (D.subschemeι ≫ f) ξ =
        relativeDimension C.dimensionFunction f y := by
      rw [relativeDimension_comp_closedImmersion]
    have hnonnegξ : 0 ≤ relativeDimension C.dimensionFunction (D.subschemeι ≫ f) ξ :=
      relativeDimension_nonneg C hδ (D.subschemeι ≫ f) ξ
    have hn : 1 ≤ n := by
      rw [hrelξ, hdy] at hnonnegξ
      omega
    have h := topologicalKrullDim_closure_eq_relativeDimension_toNat C hδ
      (D.subschemeι ≫ f) ξ
    rw [hξ, hrelξ, hdy] at h
    rw [h]
    congr 1
    omega
  refine ⟨hcomponents, ?_⟩
  obtain ⟨x⟩ := hDne
  obtain ⟨W, hW, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x} : Set D.subscheme)) isIrreducible_singleton.closure
  exact (topologicalKrullDim_eq_of_equidimensional
    (fun V hV W' hW' ↦ by rw [hcomponents V hV, hcomponents W' hW']) hW).trans
    (hcomponents W hW)

/-! ### The fibre of the divisor -/

/-- The closed subscheme cut out by the inverse image of an ideal sheaf `I` on `X` in the fibre
of `p : X ⟶ Y` over `s` is homeomorphic to the fibre over `s` of `I.subscheme ⟶ X ⟶ Y`. -/
private def comapFiberHomeo {X Y : Scheme.{u}} (p : X ⟶ Y) (I : X.IdealSheafData) (s : Y) :
    (I.comap (p.fiberι s)).subscheme ≃ₜ (I.subschemeι ≫ p).fiber s :=
  (Scheme.IdealSheafData.comapIso I (p.fiberι s) ≪≫
    pullbackSymmetry (p.fiberι s) I.subschemeι ≪≫
      pullbackRightPullbackFstIso p (Y.fromSpecResidueField s) I.subschemeι).hom.homeomorph

/-- The restriction of a relative effective Cartier divisor on `X/Y` to a fibre of `p` is an
effective Cartier divisor there. -/
private theorem isEffectiveCartierDivisor_comap_fiberι {X Y : Scheme.{u}} (p : X ⟶ Y)
    (D : X.IdealSheafData) [Flat (D.subschemeι ≫ p)]
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (s : Y) :
    Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (p.fiberι s)) := by
  have hsnd : Stacks.Divisors.IsEffectiveCartierDivisor
      (D.comap (pullback.snd (Y.fromSpecResidueField s) p)) :=
    AlgebraicGeometry.isEffectiveCartierDivisor_comap_pullback p
      (Y.fromSpecResidueField s) D hD
  have hrw : D.comap (p.fiberι s) =
      (D.comap (pullback.snd (Y.fromSpecResidueField s) p)).comap
        (pullbackSymmetry p (Y.fromSpecResidueField s)).hom := by
    rw [← Scheme.IdealSheafData.comap_comp, pullbackSymmetry_hom_comp_snd]
    rfl
  rw [hrw]
  exact Stacks.Divisors.isPullbackDefined_of_flat
    (pullbackSymmetry p (Y.fromSpecResidueField s)).hom _ hsnd

end Stacks.Chow

namespace AlgebraicGeometry

/-- **The relative dimension of a relative effective Cartier divisor.** If `p : X ⟶ Y` is
locally of finite type of relative dimension `r + 1` and `D ⊆ X` is a relative effective Cartier
divisor on `X/Y` (Stacks 062T), then `p|_D : D ⟶ Y` has relative dimension `r`. -/
theorem relativeDimension_of_isRelativeEffectiveCartierDivisor {X Y : Scheme.{u}} (p : X ⟶ Y)
    [LocallyOfFiniteType p] (r : ℕ) (hp : RelativeDimension p (r + 1)) (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p D) :
    RelativeDimension (D.subschemeι ≫ p) r := by
  classical
  have : Flat (D.subschemeι ≫ p) := hD.2
  rw [relativeDimension_iff]
  intro s hs
  let E := Stacks.Chow.comapFiberHomeo p D s
  have hDne : Nonempty (D.comap (p.fiberι s)).subscheme := ⟨E.symm hs.some⟩
  have hXne : Nonempty (p.fiber s) := ⟨(D.comap (p.fiberι s)).subschemeι.base (E.symm hs.some)⟩
  obtain ⟨hXequi, hXdim⟩ := hp s hXne
  have hDfib : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (p.fiberι s)) :=
    Stacks.Chow.isEffectiveCartierDivisor_comap_fiberι p D hD.1 s
  have : JacobsonSpace (Stacks.Chow.fieldChowSituation ↥(Y.residueField s)).S :=
    inferInstanceAs (JacobsonSpace (Spec (.of ↥(Y.residueField s))))
  have : LocallyOfFiniteType (p.fiberToSpecResidueField s) := by
    show LocallyOfFiniteType (pullback.snd p (Y.fromSpecResidueField s))
    infer_instance
  have hdrop := Stacks.Chow.topologicalKrullDim_irreducibleComponents_of_isEffectiveCartierDivisor
    (Stacks.Chow.fieldChowSituation ↥(Y.residueField s))
    (fun t _ ↦ Stacks.Chow.fieldChowSituation_dimensionFunction ↥(Y.residueField s) t)
    (p.fiberToSpecResidueField s) (r + 1) hXequi hXdim (D.comap (p.fiberι s)) hDfib hDne
  have hequi : TopologicalSpace.Equidimensional (D.comap (p.fiberι s)).subscheme :=
    fun V hV W hW ↦ by rw [hdrop.1 V hV, hdrop.1 W hW]
  refine ⟨Stacks.Chow.equidimensional_of_homeomorph E.symm hequi, ?_⟩
  rw [E.symm.isHomeomorph.topologicalKrullDim_eq, hdrop.2]
  norm_num

end AlgebraicGeometry

end
