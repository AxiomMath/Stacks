module

public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.BaseChangeDivisor
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeEffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.Equidimensional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative dimension of a relative effective Cartier divisor

Let `p : X ⟶ Y` be locally of finite type and of relative dimension `r + 1`, and let `D ⊆ X` be a
relative effective Cartier divisor on `X/Y` (Stacks 062T). Then `D ⟶ Y` has relative dimension
`r`: for `y ∈ Y` the fibre `D_y` is an effective Cartier divisor on the fibre `X_y`
(Stacks 056Q), which is equidimensional of dimension `r + 1`, and every irreducible component of
an effective Cartier divisor on an equidimensional scheme locally of finite type over a field has
codimension one, hence dimension `r`. In relative dimension zero the same argument shows that `D`
is empty.

## Main results

* `Stacks.Divisors.relativeDimension_subschemeι_comp_of_isRelativeEffectiveCartierDivisor` —
  `D ⟶ Y` has relative dimension `r` when `p` has relative dimension `r + 1`.
* `Stacks.Divisors.isEmpty_subscheme_of_isRelativeEffectiveCartierDivisor_of_relativeDimension_zero`
  — `D` is empty when `p` has relative dimension `0`.

## Implementation notes

The dimension count on a fibre is done in the Chow situation `Stacks.Chow.fieldChowSituation` of
the residue field: there the relative dimension of Stacks 02JW is a dimension function on the
fibre, vanishing at closed points, so Stacks 02IA turns the codimension-one statement for the
generic points of the components of the divisor (Stacks 02RK, via the stalk computation
`AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor`) into a drop of the
dimension function by exactly one.

## References

* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
* [Stacks Project, Tag 056Q](https://stacks.math.columbia.edu/tag/056Q)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open IrreducibleClosedsCodim

universe u

namespace Stacks.Divisors

/-- An irreducible component of a space whose components all have dimension `n` has dimension
`n`. -/
@[ega "0 14.1.3" "finite dimension"]
private theorem topologicalKrullDim_component_of_equidimensional
    {X : Type u} [TopologicalSpace X] (hX : Equidimensional X)
    (n : ℕ) (hXdim : topologicalKrullDim X = (n : WithBot ℕ∞))
    (W : Set X) (hW : W ∈ irreducibleComponents X) :
    topologicalKrullDim W = (n : WithBot ℕ∞) := by
  have hsupi :
      (⨆ W' : Set X, ⨆ (_ : W' ∈ irreducibleComponents X), topologicalKrullDim W') =
        topologicalKrullDim W := by
    apply le_antisymm
    · exact iSup_le fun W' => iSup_le fun hW' => (hX W' hW' W hW).le
    · exact le_iSup_of_le W (le_iSup_of_le hW le_rfl)
  rw [← hsupi, ← AlgebraicGeometry.topologicalKrullDim_eq_iSup_irreducibleComponents, hXdim]

/-- The reduced closed subscheme on an irreducible component is integral. -/
private theorem isIntegral_vanishingIdeal_component {X : Scheme.{u}} (W : Set X)
    (hW : W ∈ irreducibleComponents X) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      ⟨W, isClosed_of_mem_irreducibleComponents W hW⟩).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨W, isClosed_of_mem_irreducibleComponents W hW⟩ : Closeds X)
  have hsupp : (I.support : Set X) = W := by
    simp [I, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have : IrreducibleSpace I.subscheme :=
    Stacks.Chow.irreducibleSpace_subscheme_of_isIrreducible I (by rw [hsupp]; exact hW.1)
  exact isIntegral_of_irreducibleSpace_of_isReduced I.subscheme

/-- The generic point of the reduced closed subscheme on an irreducible component is the generic
point of that component. -/
private theorem subschemeι_genericPoint_vanishingIdeal_component {X : Scheme.{u}} (W : Set X)
    (hW : W ∈ irreducibleComponents X) :
    haveI := isIntegral_vanishingIdeal_component W hW
    (Scheme.IdealSheafData.vanishingIdeal
        ⟨W, isClosed_of_mem_irreducibleComponents W hW⟩).subschemeι
      (genericPoint (Scheme.IdealSheafData.vanishingIdeal
        ⟨W, isClosed_of_mem_irreducibleComponents W hW⟩).subscheme) =
      (genericPoints.ofComponent ⟨W, hW⟩).1 := by
  have := isIntegral_vanishingIdeal_component W hW
  set I := Scheme.IdealSheafData.vanishingIdeal
    (⟨W, isClosed_of_mem_irreducibleComponents W hW⟩ : Closeds X) with hI
  have hsupp : (I.support : Set X) = W := by
    simp [I, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hclosure :
      closure ({I.subschemeι (genericPoint I.subscheme)} : Set X) = W := by
    rw [← Set.image_singleton, I.subschemeι.isClosedEmbedding.closure_image_eq,
      genericPoint_closure, Set.image_univ, I.range_subschemeι, hsupp]
  have hη : IsGenericPoint ((genericPoints.ofComponent ⟨W, hW⟩).1) W :=
    genericPoints.isGenericPoint_ofComponent ⟨W, hW⟩
  have hξ : IsGenericPoint (I.subschemeι (genericPoint I.subscheme)) W := by
    rw [← hclosure]
    exact isGenericPoint_closure
  exact (hη.eq hξ).symm

/-- The dimension of the reduced closed subscheme on a closed subset is that of the subset. -/
private theorem topologicalKrullDim_vanishingIdeal_subscheme {X : Scheme.{u}} (W : Closeds X) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal W).subscheme =
      topologicalKrullDim (W : Set X) := by
  set I := Scheme.IdealSheafData.vanishingIdeal W
  have hrange : Set.range I.subschemeι = (W : Set X) := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  calc
    topologicalKrullDim I.subscheme = topologicalKrullDim (Set.univ : Set I.subscheme) :=
      (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ I.subscheme).isHomeomorph).symm
    _ = topologicalKrullDim (Set.range I.subschemeι) := by
      rw [← Set.image_univ]
      exact (I.subschemeι.isClosedEmbedding.homeomorphImage Set.univ).isHomeomorph
        |>.topologicalKrullDim_eq
    _ = topologicalKrullDim (W : Set X) := by rw [hrange]

/-- The generic point of a component of an effective Cartier divisor has coheight one in the
ambient scheme. -/
private theorem coheight_subschemeι_genericPoint_component {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D) (W : Set D.subscheme)
    (hW : W ∈ irreducibleComponents D.subscheme) :
    (Order.coheight (D.subschemeι (genericPoints.ofComponent ⟨W, hW⟩).1) : WithBot ℕ∞) = 1 := by
  rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
  exact AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor D hD _
    ⟨⟨W, hW⟩, genericPoints.isGenericPoint_ofComponent ⟨W, hW⟩⟩

/-- **An effective Cartier divisor on an equidimensional scheme is equidimensional of one less
dimension.** Let `X` be locally of finite type over a Jacobson base whose dimension function
vanishes at closed points, equidimensional of dimension `n`, and let `D ⊆ X` be a nonempty
effective Cartier divisor. Then every irreducible component of `D` has dimension `n - 1`, and so
does `D`. -/
private theorem topologicalKrullDim_components_of_isEffectiveCartierDivisor
    (C : Stacks.Chow.ChowSituation.{u}) [JacobsonSpace C.S]
    (hzero : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (n : ℕ) (hX : Equidimensional X) (hXdim : topologicalKrullDim X = (n : WithBot ℕ∞))
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D) (hDne : Nonempty D.subscheme) :
    (∀ W : Set D.subscheme, W ∈ irreducibleComponents D.subscheme →
      topologicalKrullDim W = ((n - 1 : ℕ) : WithBot ℕ∞)) ∧
    topologicalKrullDim D.subscheme = ((n - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set d : X → ℤ := Stacks.Chow.relativeDimension C.dimensionFunction f with hd
  obtain ⟨dX, hdX⟩ := Stacks.Chow.relativeDimension_isDimensionFunction
    C.isUniversallyCatenary C.dimensionFunction f
  have hdDim : IsDimensionFunctionForCatenary d := by
    constructor
    · intro a b hab hne
      rw [hd, ← hdX b, ← hdX a]
      exact dX.strictAnti_specializes hab hne
    · intro a b hab
      rw [hd, ← hdX a, ← hdX b]
      exact dX.step_immediate hab
  have hSober : StacksSober X :=
    stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩
  have hcomponents : ∀ W : Set D.subscheme,
      W ∈ irreducibleComponents D.subscheme →
      topologicalKrullDim W = ((n - 1 : ℕ) : WithBot ℕ∞) := by
    intro W hW
    set ξD := (genericPoints.ofComponent ⟨W, hW⟩).1 with hξD
    set y : X := D.subschemeι ξD with hy
    set I := Scheme.IdealSheafData.vanishingIdeal
      (⟨W, isClosed_of_mem_irreducibleComponents W hW⟩ : Closeds D.subscheme) with hI
    have : IsIntegral I.subscheme := isIntegral_vanishingIdeal_component W hW
    set ξI : I.subscheme := genericPoint I.subscheme with hξIdef
    have hξI : IsGenericPoint ξI (Set.univ : Set I.subscheme) := genericPoint_spec I.subscheme
    have hcoheight : (Order.coheight y : WithBot ℕ∞) = 1 :=
      coheight_subschemeι_genericPoint_component D hD W hW
    have hcoheight' : Order.coheight y = (1 : ℕ∞) := by exact_mod_cast hcoheight
    set V : IrreducibleCloseds X := IrreducibleCloseds.closureSingleton y with hV
    have hcoheightV : Order.coheight V = 1 := by
      have heV : (irreducibleSetEquivPoints (α := X)).symm y = V := IrreducibleCloseds.ext rfl
      rwa [← heV, Order.coheight_orderIso]
    obtain ⟨A, hA, hyA⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({y} : Set X)) isIrreducible_singleton.closure
    set η := (genericPoints.ofComponent ⟨A, hA⟩).1 with hηdef
    have hηgen : IsGenericPoint η A := genericPoints.isGenericPoint_ofComponent ⟨A, hA⟩
    have hηy : η ⤳ y := hηgen.specializes (hyA (subset_closure rfl))
    set T : IrreducibleCloseds X := ⟨A, hA.1, isClosed_of_mem_irreducibleComponents A hA⟩
      with hT
    have hVT : V ≤ T := by
      show closure ({y} : Set X) ⊆ A
      exact hyA
    have hTmax : IsMax T := fun Z hTZ ↦ hA.2 Z.isIrreducible hTZ
    have hVTne : V ≠ T := by
      intro heq
      have hz : Order.coheight T = 0 := Order.coheight_eq_zero.mpr hTmax
      rw [heq, hz] at hcoheightV
      norm_num at hcoheightV
    have htopcod : topCodim V T = 1 := by
      apply le_antisymm
      · rw [topCodim_le_iff]
        intro q hh _
        have hlen : (q.length : ℕ∞) ≤ Order.coheight V := by
          rw [← hh]
          exact Order.length_le_coheight_head
        simpa [hcoheightV] using hlen
      · exact one_le_topCodim_of_lt V T (lt_of_le_of_ne hVT hVTne)
    have hTη : T = IrreducibleCloseds.closureSingleton η :=
      IrreducibleCloseds.ext hηgen.def.symm
    have hnot : η ≠ y := by
      intro heq
      rw [hTη, heq, ← hV, topCodim_self_eq_zero] at htopcod
      norm_num at htopcod
    have hformula : topCodim V T = ((d η - d y).toNat : ℕ∞) := by
      rw [hTη, hV]
      exact (isCatenarySpace_and_topCodim_eq_of_isDimensionFunction X hSober d hdDim).2 η y hηy
    have hdiff : d η - d y = 1 := by
      have hnat : ((d η - d y).toNat : ℤ) = 1 := by
        exact_mod_cast (hformula.symm.trans htopcod)
      have hlt : d y < d η := by
        rw [hd, ← hdX y, ← hdX η]
        exact dX.strictAnti_specializes hηy hnot
      rwa [Int.toNat_of_nonneg (by omega)] at hnat
    set IA := Scheme.IdealSheafData.vanishingIdeal
      (⟨A, isClosed_of_mem_irreducibleComponents A hA⟩ : Closeds X) with hIA
    have : IsIntegral IA.subscheme := isIntegral_vanishingIdeal_component A hA
    have hIAgeneric : IsGenericPoint (genericPoint IA.subscheme)
        (Set.univ : Set IA.subscheme) := genericPoint_spec _
    have hgenA : IA.subschemeι (genericPoint IA.subscheme) = η :=
      subschemeι_genericPoint_vanishingIdeal_component A hA
    have hdη : d η = (n : ℤ) := by
      have hdimA := Stacks.Chow.topologicalKrullDim_eq_relativeDimension_toNat
        C hzero f IA.subschemeι (genericPoint IA.subscheme) hIAgeneric
      rw [topologicalKrullDim_vanishingIdeal_subscheme] at hdimA
      change topologicalKrullDim A = _ at hdimA
      rw [topologicalKrullDim_component_of_equidimensional hX n hXdim A hA, hgenA] at hdimA
      have hrel : (d η).toNat = n := by exact_mod_cast hdimA.symm
      have hnneg : 0 ≤ d η := Stacks.Chow.relativeDimension_nonneg C hzero f η
      omega
    have hdy : d y = (n : ℤ) - 1 := by omega
    have hrel : Stacks.Chow.relativeDimension C.dimensionFunction (D.subschemeι ≫ f) ξD = d y :=
      Stacks.Chow.relativeDimension_comp_closedImmersion C.dimensionFunction D.subschemeι f ξD
    have hpoint : I.subschemeι ξI = ξD := subschemeι_genericPoint_vanishingIdeal_component W hW
    have hdimI := Stacks.Chow.topologicalKrullDim_eq_relativeDimension_toNat
      C hzero (D.subschemeι ≫ f) I.subschemeι ξI hξI
    have hnonnegD := Stacks.Chow.relativeDimension_nonneg C hzero (D.subschemeι ≫ f) ξD
    rw [hrel, hdy] at hnonnegD
    rw [topologicalKrullDim_vanishingIdeal_subscheme] at hdimI
    show topologicalKrullDim W = _
    rw [show (W : Set D.subscheme) =
      ((⟨W, isClosed_of_mem_irreducibleComponents W hW⟩ : Closeds D.subscheme) :
        Set D.subscheme) from rfl, hdimI, hpoint, hrel, hdy,
      show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by omega]
    simp
  refine ⟨hcomponents, ?_⟩
  rw [AlgebraicGeometry.topologicalKrullDim_eq_iSup_irreducibleComponents]
  obtain ⟨x⟩ := hDne
  obtain ⟨W, hW, _⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x} : Set D.subscheme)) isIrreducible_singleton.closure
  apply le_antisymm
  · exact iSup_le fun W' => iSup_le fun hW' => (hcomponents W' hW').le
  · rw [← hcomponents W hW]
    exact le_iSup_of_le W (le_iSup_of_le hW le_rfl)

/-- The fibre of `D ⟶ Y` over `s` is the divisor that `D` cuts on the fibre of `X ⟶ Y`, in the
presentation `D.comap (pullback.snd g p)` along `g = Spec κ(s) ⟶ Y`. -/
private def comapFiberIso {X Y : Scheme.{u}} (p : X ⟶ Y) (D : X.IdealSheafData) (s : Y) :
    (D.comap (pullback.snd (Y.fromSpecResidueField s) p)).subscheme ≅
      (D.subschemeι ≫ p).fiber s := by
  set g := Y.fromSpecResidueField s
  let eZ := pullbackSymmetry g p
  let m := pullback.map D.subschemeι (pullback.snd g p) D.subschemeι (pullback.fst p g)
    (𝟙 _) eZ.hom (𝟙 _) (by simp) (by simp [eZ])
  haveI : IsIso m := by
    dsimp only [m]
    infer_instance
  exact D.comapIso (pullback.snd g p) ≪≫
    pullbackSymmetry (pullback.snd g p) D.subschemeι ≪≫ asIso m ≪≫
    pullbackRightPullbackFstIso p g D.subschemeι

/-- **A relative effective Cartier divisor drops the relative dimension by one.** Let
`p : X ⟶ Y` be locally of finite type and of relative dimension `r + 1`, and let `D` be a
relative effective Cartier divisor on `X/Y` (Stacks 062T). Then `D ⟶ Y` has relative dimension
`r`. -/
theorem relativeDimension_subschemeι_comp_of_isRelativeEffectiveCartierDivisor
    {X Y : Scheme.{u}} (p : X ⟶ Y) [LocallyOfFiniteType p] (r : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (D : X.IdealSheafData)
    (hD : IsRelativeEffectiveCartierDivisor p D) :
    AlgebraicGeometry.RelativeDimension (D.subschemeι ≫ p) r := by
  classical
  rw [AlgebraicGeometry.relativeDimension_iff]
  intro s hs
  set g := Y.fromSpecResidueField s
  set Z := pullback g p
  set fZ := pullback.fst g p
  set D' := D.comap (pullback.snd g p)
  have : Flat (D.subschemeι ≫ p) := hD.2
  have hD' : IsEffectiveCartierDivisor D' :=
    AlgebraicGeometry.isEffectiveCartierDivisor_comap_pullback p g D hD.1
  let E : D'.subscheme ≅ (D.subschemeι ≫ p).fiber s := comapFiberIso p D s
  have hD'ne : Nonempty D'.subscheme := by
    obtain ⟨w⟩ := hs
    exact ⟨E.inv w⟩
  let eX : Z ≃ₜ p.fiber s := (pullbackSymmetry g p).hom.homeomorph
  have hpFiber := hp s (by
    obtain ⟨w⟩ := hD'ne
    exact ⟨eX (D'.subschemeι w)⟩)
  let C := Stacks.Chow.fieldChowSituation (Y.residueField s)
  have : JacobsonSpace C.S := by
    show JacobsonSpace (Spec (.of (Y.residueField s)))
    infer_instance
  have hzero : ∀ t : C.S, IsClosed ({t} : Set C.S) → C.dimensionFunction t = 0 :=
    fun t _ ↦ Stacks.Chow.fieldChowSituation_dimensionFunction _ t
  have hX : Equidimensional Z := Equidimensional.of_homeomorph eX hpFiber.1
  have hXdim : topologicalKrullDim Z = ((r + 1 : ℕ) : WithBot ℕ∞) :=
    (IsHomeomorph.topologicalKrullDim_eq _ eX.isHomeomorph).trans hpFiber.2
  have hcomponents := topologicalKrullDim_components_of_isEffectiveCartierDivisor C hzero
    (X := Z) fZ (r + 1) hX hXdim D' hD' hD'ne
  have hD'equi : Equidimensional D'.subscheme := by
    intro V hV W hW
    rw [hcomponents.1 V hV, hcomponents.1 W hW]
  refine ⟨Equidimensional.of_homeomorph E.hom.homeomorph.symm hD'equi, ?_⟩
  exact (IsHomeomorph.topologicalKrullDim_eq _ E.hom.homeomorph.isHomeomorph).symm.trans
    hcomponents.2

/-- **In relative dimension zero a relative effective Cartier divisor is empty.** If `p` is
locally of finite type and of relative dimension `0`, every relative effective Cartier divisor on
`X/Y` is empty. -/
theorem isEmpty_subscheme_of_isRelativeEffectiveCartierDivisor_of_relativeDimension_zero
    {X Y : Scheme.{u}} (p : X ⟶ Y) [LocallyOfFiniteType p]
    (hp : AlgebraicGeometry.RelativeDimension p 0) (D : X.IdealSheafData)
    (hD : IsRelativeEffectiveCartierDivisor p D) :
    IsEmpty D.subscheme := by
  classical
  refine isEmpty_iff.mpr fun d ↦ ?_
  set s : Y := p (D.subschemeι d)
  set g := Y.fromSpecResidueField s
  set Z := pullback g p
  set D' := D.comap (pullback.snd g p)
  have : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst g p)
  have : Flat (D.subschemeι ≫ p) := hD.2
  have hD' : IsEffectiveCartierDivisor D' :=
    AlgebraicGeometry.isEffectiveCartierDivisor_comap_pullback p g D hD.1
  let E : D'.subscheme ≅ (D.subschemeι ≫ p).fiber s := comapFiberIso p D s
  let w' : D'.subscheme := E.inv ((D.subschemeι ≫ p).asFiber d)
  obtain ⟨K, hK, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({w'} : Set D'.subscheme)) isIrreducible_singleton.closure
  set ξ : D'.subscheme := (genericPoints.ofComponent ⟨K, hK⟩).1
  have hcoheight : (Order.coheight (D'.subschemeι ξ) : WithBot ℕ∞) = 1 :=
    coheight_subschemeι_genericPoint_component D' hD' K hK
  have hle : (Order.coheight (D'.subschemeι ξ) : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
    have h := Order.coheight_le_krullDim
      ((irreducibleSetEquivPoints (α := Z)).symm (D'.subschemeι ξ))
    rwa [Order.coheight_orderIso] at h
  have hdimZ : topologicalKrullDim Z = 0 := by
    have e : Z ≃ₜ p.fiber s := (pullbackSymmetry g p).hom.homeomorph
    exact (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).trans
      (hp s ⟨p.asFiber (D.subschemeι d)⟩).2
  rw [hdimZ, hcoheight] at hle
  norm_num at hle

end Stacks.Divisors

end
