module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ClosedSubschemeZeroCycle
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ProductOfPuncturedSchemes
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestrictionLocal
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSectionCycle
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinZeroSectionDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeRegularSection
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Triviality
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence

/-!
# Zero schemes of functions

For a scheme `Y` and a global function `g ∈ Γ(Y, 𝒪_Y)`, the zero scheme of `g` read as a section
of the structure sheaf `𝒪_Y` regarded as an invertible module over itself. This file records the
facts the action of a relative cycle on principal divisors needs: the zero scheme of a
pulled-back function is the inverse image of the zero scheme, the restriction of `𝒪_Y` to any
closed subscheme is trivial, on an integral scheme the cycle of the zero scheme of a nonzero
function has the orders of vanishing of that function as coefficients, and the Gysin map on
cycles of a function, on a cycle none of whose components lies in its zero scheme, is the sum of
the principal divisors of its restrictions to the components.

## Main results

* `Stacks.Chow.zeroScheme_unitModule_appTop` — `Z(f^♯ g) = f⁻¹ Z(g)`.
* `Stacks.Chow.isTrivial_pullback_unitModule` — `𝒪_Y` restricts trivially along any morphism.
* `Stacks.Chow.cycleAssociatedToZeroScheme_unitModule_apply` — `[Z(g)]_{n-1} = div(g)`,
  coefficientwise.
* `Stacks.Chow.gysinCycleMapPushforward_unitModule_apply` — `i_* i^* β = ∑_w β_w div(g|_{Z_w})`
  for a cycle `β` meeting `Z(g)` properly.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Chow

/-- `𝒪_Y` is an invertible `𝒪_Y`-module, in the spelling of the zero scheme of Stacks 02OQ. -/
instance isInvertible_sheafObj_unitModule (Y : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      (Scheme.unitModule Y) :=
  Stacks.Ample.isInvertibleModule_unit Y

/-- **The zero scheme of a pulled-back function is the inverse image of the zero scheme.** -/
theorem zeroScheme_unitModule_appTop {Y' Y : Scheme.{u}} (f : Y' ⟶ Y) (g : Γ(Y, ⊤)) :
    Stacks.Divisors.zeroScheme Y' (Scheme.unitModule Y') (f.appTop g) =
      (Stacks.Divisors.zeroScheme Y (Scheme.unitModule Y) g).comap f := by
  rw [← Stacks.Divisors.zeroScheme_pullback f (Scheme.unitModule Y) g]
  exact (AlgebraicGeometry.zeroScheme_eq_of_iso (Scheme.Modules.pullbackUnitIso f)
    (AlgebraicGeometry.SectionsEqualizer.pullbackUnitIso_unit f g)).symm

/-- **`𝒪_Y` restricts trivially along any morphism.** -/
theorem isTrivial_pullback_unitModule {Z Y : Scheme.{u}} (i : Z ⟶ Y) :
    AlgebraicGeometry.SheafOfModules.IsTrivial Z.sheaf.obj Z.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj (Scheme.unitModule Y)) :=
  ⟨Scheme.Modules.pullbackUnitIso i⟩

/-- **`[Z(g)]_{n-1} = div(g)`, coefficientwise.** On an integral scheme of delta-dimension `n`,
the cycle of the zero scheme of a nonzero function `g` has the order of vanishing of `g` as its
coefficient at every point. -/
theorem cycleAssociatedToZeroScheme_unitModule_apply (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (p : Y ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral Y] [IsLocallyNoetherian Y] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) (g : Γ(Y, ⊤)) (hg : g ≠ 0) (y : Y) :
    haveI : Nonempty (⊤ : Y.Opens) := ⟨⟨y, trivial⟩⟩
    (cycleAssociatedToClosedSubscheme C p
        (Stacks.Divisors.zeroScheme Y (Scheme.unitModule Y) g).subschemeι (n - 1)).1 y =
      Y.ord (Y.germToFunctionField ⊤ g) y := by
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨y, trivial⟩⟩
  by_cases hco : Order.coheight y = 1
  · obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y)
      (U := ⊤) trivial
    have : Nonempty (U : Y.Opens) := ⟨⟨y, hyU⟩⟩
    have h := Stacks.ChernCap42.cycleAssociatedToZeroScheme_apply_eq_ord C p hn
      (Scheme.unitModule Y) g hg hco (U := ⟨U, hU⟩) (Iso.refl _) hyU
    refine h.trans ?_
    congr 1
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hco]
    by_contra hne
    exact hco ((relativeDimension_eq_sub_one_iff_coheight_eq_one C p hn y).mp
      ((mem_cyclesOfDimension_iff_forall_point C p (n - 1) _).mp
        (cycleAssociatedToClosedSubscheme C p
          (Stacks.Divisors.zeroScheme Y (Scheme.unitModule Y) g).subschemeι (n - 1)).2 y hne))

/-- The restriction of a function to an integral closed subscheme not contained in its zero
scheme is nonzero. -/
theorem appTop_subschemeι_ne_zero {Y : Scheme.{u}} (g : Γ(Y, ⊤)) (Z : Y.IdealSheafData)
    (hnot : ¬ Stacks.Divisors.zeroScheme Y (Scheme.unitModule Y) g ≤ Z) :
    Z.subschemeι.appTop g ≠ 0 := by
  refine fun h0 ↦ hnot ?_
  rw [← Stacks.Divisors.comap_eq_bot_iff_le, ← zeroScheme_unitModule_appTop, h0]
  exact Stacks.Divisors.zeroScheme_zero_eq_bot _

/-- **The component of the Gysin map of a function, as a principal divisor.** For an integral
closed subscheme `Z ⊆ Y` of delta-dimension `k + 1` not contained in the zero scheme `D` of a
function `g`, the cycle `[Z ∩ D]_k`, pushed into `Y`, is the pushforward of the principal divisor
of `g|_Z`. -/
theorem properPushforward_gysinCycleMapComponent_unitModule (C : ChowSituation.{u})
    {Y : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (g : Γ(Y, ⊤))
    (Z : Y.IdealSheafData) (hZ : IsIntegral Z.subscheme)
    (hDim : schemeDeltaDimension C (Z.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hnot : ¬ Stacks.Divisors.zeroScheme Y (Scheme.unitModule Y) g ≤ Z) (y : Y) :
    letI := hZ
    haveI : Nonempty (⊤ : Z.subscheme.Opens) :=
      ⟨⟨genericPoint Z.subscheme, trivial⟩⟩
    (properPushforward C ((Stacks.Divisors.zeroScheme Y (Scheme.unitModule Y) g).subschemeι ≫ p)
        p (Stacks.Divisors.zeroScheme Y (Scheme.unitModule Y) g).subschemeι rfl k
        (gysinCycleMapComponent C p k (Scheme.unitModule Y) g Z hZ hDim)).1 y =
      (properPushforward C (Z.subschemeι ≫ p) p Z.subschemeι rfl ((k + 1) - 1)
        (principalDivisorCycle C (Z.subschemeι ≫ p) hDim
          (Z.subscheme.germToFunctionField ⊤ (Z.subschemeι.appTop g)))).1 y := by
  let := hZ
  have : Nonempty (⊤ : Z.subscheme.Opens) := ⟨⟨genericPoint Z.subscheme, trivial⟩⟩
  have : IsLocallyNoetherian Z.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Z.subschemeι ≫ p)
  set D := Stacks.Divisors.zeroScheme Y (Scheme.unitModule Y) g with hD
  rw [gysinCycleMapComponent_of_not_le C p k (Scheme.unitModule Y) g Z hZ hDim hnot,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
  -- the principal divisor on `Z` is the cycle of the zero scheme of `g|_Z`
  have hprin : (principalDivisorCycle C (Z.subschemeι ≫ p) hDim
        (Z.subscheme.germToFunctionField ⊤ (Z.subschemeι.appTop g)) :
          CycleGroup C (Z.subschemeι ≫ p) ((k + 1) - 1)) =
      cycleAssociatedToClosedSubscheme C (Z.subschemeι ≫ p)
        (Stacks.Divisors.zeroScheme Z.subscheme (Scheme.unitModule Z.subscheme)
          (Z.subschemeι.appTop g)).subschemeι ((k + 1) - 1) := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    rw [principalDivisorCycle_apply]
    exact (cycleAssociatedToZeroScheme_unitModule_apply C (Z.subschemeι ≫ p) hDim _
      (appTop_subschemeι_ne_zero g Z hnot) z).symm
  rw [hprin, properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
  have hE : Stacks.Divisors.zeroScheme Z.subscheme (Scheme.unitModule Z.subscheme)
      (Z.subschemeι.appTop g) = D.comap Z.subschemeι := zeroScheme_unitModule_appTop _ g
  rw [show ((k + 1) - 1 : ℤ) = k by ring]
  obtain ⟨e₁, he₁⟩ := Stacks.ChernCap42.exists_iso_comap_sup Z D Z.subschemeι (Iso.refl _)
    (Category.id_comp _)
  obtain ⟨e₂, he₂⟩ := Stacks.ChernCap42.exists_iso_comap_sup D Z D.subschemeι (Iso.refl _)
    (Category.id_comp _)
  have h₁ := cycleAssociatedToClosedSubscheme_eq_of_iso C p _ _ e₁ he₁ k
  have h₂ := cycleAssociatedToClosedSubscheme_eq_of_iso C p _ _ e₂ he₂ k
  rw [sup_comm] at h₂
  rw [← hE] at h₁
  rw [h₁, ← h₂]

/-- **The Gysin map of a function on a cycle meeting its zero scheme properly.** Let `β` be a
`(k+1)`-cycle on `Y` none of whose components lies in the zero scheme of the function `g`. Then
`i_* i^* β = ∑_w β_w (Z_w ⟶ Y)_* div(g|_{Z_w})`, coefficientwise, the sum running over the points
`w` carrying a nonzero coefficient of `β` and `Z_w` being the closure of `w`. -/
theorem gysinCycleMapPushforward_unitModule_apply (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (p : Y ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (g : Γ(Y, ⊤)) (β : CycleGroup C p (k + 1))
    (hβ : ∀ w : cycleSupportIndex β,
      ¬ Stacks.Divisors.zeroScheme Y (Scheme.unitModule Y) g ≤ integralComponentAt w.1)
    (y : Y) :
    (gysinCycleMapPushforward C p k (Scheme.unitModule Y) g
        (isTrivial_pullback_unitModule _) β).1 y =
      ∑ᶠ w : cycleSupportIndex β, β.1 w.1 *
        (letI := isIntegral_integralComponentAt w.1
         haveI : Nonempty (⊤ : (integralComponentAt w.1).subscheme.Opens) :=
           ⟨⟨genericPoint _, trivial⟩⟩
         (properPushforward C ((integralComponentAt w.1).subschemeι ≫ p) p
          (integralComponentAt w.1).subschemeι rfl ((k + 1) - 1)
          (principalDivisorCycle C ((integralComponentAt w.1).subschemeι ≫ p)
            (schemeDeltaDimension_cycleSupportIndex β w)
            ((integralComponentAt w.1).subscheme.germToFunctionField ⊤
              ((integralComponentAt w.1).subschemeι.appTop g)))).1 y) := by
  set D := Stacks.Divisors.zeroScheme Y (Scheme.unitModule Y) g with hD
  have hterm : ∀ w : cycleSupportIndex β,
      (let := isIntegral_integralComponentAt w.1
       have : Nonempty (⊤ : (integralComponentAt w.1).subscheme.Opens) :=
         ⟨⟨genericPoint _, trivial⟩⟩
       (properPushforward C ((integralComponentAt w.1).subschemeι ≫ p) p
        (integralComponentAt w.1).subschemeι rfl ((k + 1) - 1)
        (principalDivisorCycle C ((integralComponentAt w.1).subschemeι ≫ p)
          (schemeDeltaDimension_cycleSupportIndex β w)
          ((integralComponentAt w.1).subscheme.germToFunctionField ⊤
            ((integralComponentAt w.1).subschemeι.appTop g)))).1 y) =
        (properPushforward C (D.subschemeι ≫ p) p D.subschemeι rfl k
          (gysinCycleMapComponent C p k (Scheme.unitModule Y) g (integralComponentAt w.1)
            (isIntegral_integralComponentAt w.1)
            (schemeDeltaDimension_cycleSupportIndex β w))).1 y := fun w ↦
    (properPushforward_gysinCycleMapComponent_unitModule C p k g (integralComponentAt w.1)
      (isIntegral_integralComponentAt w.1) (schemeDeltaDimension_cycleSupportIndex β w)
      (hβ w) y).symm
  simp only [hterm]
  have hL : (gysinCycleMapPushforward C p k (Scheme.unitModule Y) g
        (isTrivial_pullback_unitModule _) β).1 y =
      (properPushforward C (D.subschemeι ≫ p) p D.subschemeι rfl k
        (gysinCycleMap C p k (Scheme.unitModule Y) g (isTrivial_pullback_unitModule _) β)).1 y :=
    rfl
  rw [hL]
  by_cases hy : y ∈ Set.range D.subschemeι.base
  · obtain ⟨d, rfl⟩ := hy
    simp only [properPushforward_apply_image_of_isClosedImmersion]
    exact isGysinCycleMap_gysinCycleMap C p k (Scheme.unitModule Y) g
      (isTrivial_pullback_unitModule _)
      (fun x : cycleSupportIndex β ↦ integralComponentAt x.1)
      (fun x ↦ isIntegral_integralComponentAt x.1)
      (fun x ↦ schemeDeltaDimension_cycleSupportIndex β x)
      (locallyFinite_support_integralComponentAt β) (fun x ↦ β.1 x.1) β
      (cycle_eq_finsum_primeCycles β) d
  · simp only [properPushforward_apply_eq_zero_of_notMem_range C _ p _ rfl k _ y hy, mul_zero,
      finsum_zero]

end Stacks.Chow

end
