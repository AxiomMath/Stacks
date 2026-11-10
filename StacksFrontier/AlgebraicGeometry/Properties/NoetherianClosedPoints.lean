module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.RingTheory.Spectrum.Prime.DimensionTwoOpens

/-!
# Closed points of locally Noetherian schemes

Every nonempty locally Noetherian scheme has a closed point. More generally, every nonempty
closed subset of such a scheme contains a point that is closed in the ambient scheme, and
equivalently every point specializes to a closed point.

## Main results

* `AlgebraicGeometry.closedPoints_nonempty`: a nonempty locally Noetherian scheme has a closed
  point.
* `AlgebraicGeometry.nonempty_inter_closedPoints_of_isClosed`: a nonempty closed subset contains
  a point closed in the ambient scheme.
* `AlgebraicGeometry.exists_specializes_closedPoint`: every point specializes to a closed point.

## Implementation notes

Closed points are `TopologicalSpace.closedPoints`, and specialization is `Specializes`. The three
results are the three formulations of the statement of Tag 02IL.

## References

* [Stacks Project, Tag 02IL](https://stacks.math.columbia.edu/tag/02IL)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On an integral, locally Noetherian scheme, if a point `x` specializing to `y` is itself an
open point, then the local ring at `y` has Krull dimension less than two. -/
private theorem local_stalk_dim_lt_two_of_open_singleton {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsIntegral Y] (x y : Y) (hxy : x ⤳ y) (U : Set Y)
    (hU : U = {x}) (hUopen : IsOpen U) :
    ringKrullDim (Y.presheaf.stalk y) < 2 := by
  let R := Y.presheaf.stalk y
  let f := Y.fromSpecStalk y
  let V : Set (PrimeSpectrum R) := f ⁻¹' U
  have hVopen : IsOpen V := hUopen.preimage f.continuous
  have hxrange : x ∈ Set.range f := by
    rw [Scheme.range_fromSpecStalk]
    exact hxy
  obtain ⟨p, hp⟩ := hxrange
  have hpV : p ∈ V := by
    change f p ∈ U
    rw [hp, hU]
    simp
  have hf_inj : Function.Injective f := f.isEmbedding.injective
  have hV : V = {p} := by
    ext q
    constructor
    · intro hq
      apply Set.mem_singleton_iff.mpr
      apply hf_inj
      have hq' : f q ∈ ({x} : Set Y) := by
        change f q ∈ U at hq
        rw [hU] at hq
        exact hq
      exact (Set.mem_singleton_iff.mp hq').trans hp.symm
    · rintro rfl
      exact hpV
  have hnot : ¬ 2 ≤ ringKrullDim R := by
    intro hdim
    have hinf := PrimeSpectrum.infinite_of_two_le_ringKrullDim R hdim V hVopen
      ⟨p, hpV⟩
    exact hinf (hV ▸ Set.finite_singleton p)
  exact lt_of_not_ge hnot

/-- The range of the inclusion of the reduced induced subscheme on a closed set `Z` is `Z`. -/
private theorem range_subschemeι_vanishingIdeal {X : Scheme.{u}} (Z : Closeds X) :
    Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = Z := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- If `{x}` is not closed, then its closure contains a point other than `x`. -/
private theorem exists_mem_closure_singleton_ne {X : Type*} [TopologicalSpace X] {x : X}
    (hx : ¬ IsClosed ({x} : Set X)) : ∃ y ∈ closure ({x} : Set X), y ≠ x := by
  by_contra! h
  exact hx (closure_subset_iff_isClosed.mp fun y hy => h y hy)

/-- Every nonempty locally Noetherian scheme has a closed point. -/
@[stacks 02IL "nonempty scheme"]
theorem closedPoints_nonempty (X : Scheme.{u}) [IsLocallyNoetherian X] [Nonempty X] :
    (closedPoints X).Nonempty := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x₀)).opensRange
  have hUaff : IsAffineOpen U :=
    isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x₀))
  let : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hUaff⟩
  let : NoetherianSpace {y : X // y ∈ U.1} :=
    noetherianSpace_of_isAffineOpen U hUaff
  let : CompactSpace {y : X // y ∈ U.1} :=
    TopologicalSpace.NoetherianSpace.compactSpace _
  have hx₀U : x₀ ∈ U.1 := by
    simpa [U] using X.affineCover.covers x₀
  let : Nonempty {y : X // y ∈ U.1} := ⟨⟨x₀, hx₀U⟩⟩
  obtain ⟨xU, -, hxUclosed⟩ :=
    IsClosed.exists_closed_singleton (X := {y : X // y ∈ U.1}) isClosed_univ
      Set.univ_nonempty
  let x : X := xU.1
  have hxU : x ∈ U.1 := xU.2
  have hpre : (Subtype.val : {y : X // y ∈ U.1} → X) ⁻¹'
      closure ({x} : Set X) = closure ({xU} : Set {y : X // y ∈ U.1}) := by
    calc
      (Subtype.val : {y : X // y ∈ U.1} → X) ⁻¹' closure ({x} : Set X) =
          closure ((Subtype.val : {y : X // y ∈ U.1} → X) ⁻¹' ({x} : Set X)) :=
        U.2.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
          continuous_subtype_val _
      _ = closure ({xU} : Set {y : X // y ∈ U.1}) := by
        congr 1
        ext y
        change y.1 = xU.1 ↔ y = xU
        exact Subtype.ext_iff.symm
  have hclosureInter : closure ({x} : Set X) ∩ U.1 = {x} := by
    ext y
    constructor
    · rintro ⟨hyc, hyU⟩
      have hy' : (⟨y, hyU⟩ : {y : X // y ∈ U.1}) ∈
          closure ({xU} : Set {y : X // y ∈ U.1}) := by
        have : (⟨y, hyU⟩ : {y : X // y ∈ U.1}) ∈
            (Subtype.val : {y : X // y ∈ U.1} → X) ⁻¹'
            closure ({x} : Set X) := by
          change (⟨y, hyU⟩ : {y : X // y ∈ U.1}).1 ∈ closure ({x} : Set X)
          exact hyc
        exact hpre.symm ▸ this
      have hy'' : (⟨y, hyU⟩ : {y : X // y ∈ U.1}) ∈
          ({xU} : Set {y : X // y ∈ U.1}) := by
        have heqClosure : closure ({xU} : Set {y : X // y ∈ U.1}) =
            ({xU} : Set {y : X // y ∈ U.1}) :=
          hxUclosed.closure_eq
        simpa only [heqClosure] using hy'
      have : (⟨y, hyU⟩ : U) = xU := Set.mem_singleton_iff.mp hy''
      simpa [x] using congrArg Subtype.val this
    · intro hy
      have : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact ⟨subset_closure (Set.mem_singleton x), hxU⟩
  let C : Closeds X := ⟨closure ({x} : Set X), isClosed_closure⟩
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal C
  let Y : Scheme := I.subscheme
  let i : Y ⟶ X := I.subschemeι
  have hrange : Set.range i = closure ({x} : Set X) := range_subschemeι_vanishingIdeal C
  have hmem_range (y : X) (hxy : x ⤳ y) : y ∈ Set.range i := by
    rw [hrange]
    exact hxy.mem_closure
  obtain ⟨xY, hixY⟩ := hmem_range x specializes_rfl
  let : IsClosedImmersion i := inferInstance
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian i
  let : IsReduced Y := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal C
  have hsupportIrred : IsIrreducible (closure ({x} : Set X)) :=
    isIrreducible_iff_closure.mpr isIrreducible_singleton
  have hpreSupport : i ⁻¹' closure ({x} : Set X) = (Set.univ : Set Y) := by
    rw [← hrange, Set.preimage_range]
  let e : Y ≃ₜ closure ({x} : Set X) :=
    (Homeomorph.Set.univ Y).symm.trans <| (Homeomorph.setCongr hpreSupport.symm).trans <|
      i.isEmbedding.homeomorphOfSubsetRange (by rw [hrange])
  let : IrreducibleSpace Y := (e.irreducibleSpace_iff).mpr
    ((isIrreducible_iff_irreducibleSpace).mp hsupportIrred)
  let : IsIntegral Y :=
    (isIntegral_iff_irreducibleSpace_and_isReduced Y).mpr ⟨inferInstance, inferInstance⟩
  let UY : Set Y := i ⁻¹' U.1
  have hUYopen : IsOpen UY := U.2.preimage i.continuous
  have hUY : UY = {xY} := by
    ext y
    constructor
    · intro hy
      apply Set.mem_singleton_iff.mpr
      apply i.isEmbedding.injective
      have hycl : i y ∈ closure ({x} : Set X) := hrange ▸ ⟨y, rfl⟩
      have hyx : i y = x := by
        have : i y ∈ closure ({x} : Set X) ∩ U.1 := ⟨hycl, hy⟩
        have hmem : i y ∈ ({x} : Set X) :=
          (congrArg (fun s : Set X => i y ∈ s) hclosureInter).mp this
        exact Set.mem_singleton_iff.mp hmem
      exact hyx.trans hixY.symm
    · intro hy
      have hy' : y = xY := Set.mem_singleton_iff.mp hy
      subst y
      change i xY ∈ U.1
      rw [hixY]
      exact hxU
  have hclosedSpecialization (y : X) (hxy : x ⤳ y) (hyx : y ≠ x) :
      IsClosed ({y} : Set X) := by
    obtain ⟨yY, hiyY⟩ := hmem_range y hxy
    have hxyY : xY ⤳ yY :=
      i.isEmbedding.isInducing.specializes_iff.mp (by simpa [hixY, hiyY] using hxy)
    by_contra hyclosed
    obtain ⟨z, hzyC, hzy⟩ := exists_mem_closure_singleton_ne hyclosed
    have hyz : y ⤳ z := specializes_iff_mem_closure.mpr hzyC
    have hxz : x ⤳ z := hxy.trans hyz
    have hzneqx : z ≠ x := fun hzx =>
      hyx (inseparable_iff_eq.mp (hxy.antisymm (by simpa [hzx] using hyz))).symm
    obtain ⟨zY, hizY⟩ := hmem_range z hxz
    have hdimZ : ringKrullDim (Y.presheaf.stalk zY) < 2 := by
      have hxzY : xY ⤳ zY :=
        i.isEmbedding.isInducing.specializes_iff.mp (by simpa [hixY, hizY] using hxz)
      exact local_stalk_dim_lt_two_of_open_singleton xY zY hxzY UY hUY hUYopen
    let : PartialOrder Y := specializationOrder Y
    have hyz' : zY < yY := by
      apply lt_of_le_of_ne
      · change yY ⤳ zY
        exact i.isEmbedding.isInducing.specializes_iff.mp (by simpa [hiyY, hizY] using hyz)
      · intro heq
        apply hzy
        have := congrArg i heq
        simpa [hizY, hiyY] using this
    have hyx' : yY < xY := by
      apply lt_of_le_of_ne
      · exact hxyY
      · intro heq
        apply hyx
        have := congrArg i heq
        simpa [hixY, hiyY] using this
    have hcy : 1 ≤ Order.coheight yY := by
      have h := Order.coheight_add_one_le hyx'
      exact (show (1 : ℕ∞) ≤ Order.coheight xY + 1 by simp).trans h
    have hcw : 2 ≤ Order.coheight zY := by
      have h := Order.coheight_add_one_le hyz'
      have h' : (2 : ℕ∞) ≤ Order.coheight yY + 1 := by
        calc
          (2 : ℕ∞) = 1 + 1 := by norm_num
          _ ≤ Order.coheight yY + 1 := add_le_add_left hcy 1
      exact h'.trans h
    have hdimlow : (2 : WithBot ℕ∞) ≤ ringKrullDim (Y.presheaf.stalk zY) := by
      rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
      exact WithBot.coe_le_coe.mpr hcw
    exact (not_lt_of_ge hdimlow) hdimZ
  by_cases hxclosed : IsClosed ({x} : Set X)
  · exact ⟨x, mem_closedPoints_iff.mpr hxclosed⟩
  · obtain ⟨y, hyC, hyx⟩ := exists_mem_closure_singleton_ne hxclosed
    have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hyC
    exact ⟨y, mem_closedPoints_iff.mpr (hclosedSpecialization y hxy hyx)⟩

/-- Every nonempty closed subset of a locally Noetherian scheme contains a point that is
closed in the ambient scheme. -/
@[stacks 02IL "nonempty closed subset", ega "IV 5.1.11"]
theorem nonempty_inter_closedPoints_of_isClosed (X : Scheme.{u}) [IsLocallyNoetherian X]
    {Z : Set X} (hZ : Z.Nonempty) (hZ' : IsClosed Z) :
    (Z ∩ closedPoints X).Nonempty := by
  classical
  let T : Closeds X := ⟨Z, hZ'⟩
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal T
  let Y : Scheme := I.subscheme
  let i : Y ⟶ X := I.subschemeι
  have hrange : Set.range i = Z := range_subschemeι_vanishingIdeal T
  have hYnonempty : Nonempty Y := by
    obtain ⟨z, hz⟩ := hZ
    obtain ⟨y, -⟩ : z ∈ Set.range i := by simpa [hrange] using hz
    exact ⟨y⟩
  let : IsClosedImmersion i := inferInstance
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian i
  obtain ⟨y, hyclosed⟩ := closedPoints_nonempty Y
  refine ⟨i y, ?_, ?_⟩
  · simp [← hrange]
  · change y ∈ i ⁻¹' closedPoints X
    rw [i.isClosedEmbedding.preimage_closedPoints]
    exact hyclosed

/-- Every point of a locally Noetherian scheme specializes to a closed point. -/
@[stacks 02IL "closed specialization"]
theorem exists_specializes_closedPoint (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    ∃ y ∈ closedPoints X, Specializes x y := by
  obtain ⟨y, ⟨hyclosure, hyclosed⟩⟩ := nonempty_inter_closedPoints_of_isClosed X
    ⟨x, subset_closure (Set.mem_singleton x)⟩ isClosed_closure
  exact ⟨y, hyclosed, specializes_iff_mem_closure.mpr hyclosure⟩


end AlgebraicGeometry
