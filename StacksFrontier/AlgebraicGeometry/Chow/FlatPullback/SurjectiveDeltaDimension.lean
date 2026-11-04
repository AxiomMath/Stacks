module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components

/-!
# Delta-dimension along a surjection with equidimensional fibres

Let `f : X ⟶ Y` be locally of finite type, surjective, with every nonempty fibre equidimensional
of dimension `r` (`AlgebraicGeometry.RelativeDimension f r`). Over each point `y` of `Y` the
generic point `x` of an irreducible component of the fibre has residue transcendence degree `r`
over `κ(y)` (the dimension formula of Stacks 02FX), so `δ(x) = δ(y) + r`. Hence

  `dim_δ X ≤ n`   implies   `dim_δ Y ≤ n - r`.

## Main results

* `Stacks.Chow.exists_toNat_residueTrdeg_eq_of_relativeDimension`.
* `Stacks.Chow.schemeDeltaDimension_le_sub_of_surjective_of_relativeDimension`.

## References

* [Stacks Project, Tag 02FX](https://stacks.math.columbia.edu/tag/02FX)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- **Over every point of the image, a morphism with fibres equidimensional of dimension `r` has
a point of residue transcendence degree `r`**: the generic point of an irreducible component of
the fibre. -/
theorem exists_toNat_residueTrdeg_eq_of_relativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (r : ℕ) (hrel : AlgebraicGeometry.RelativeDimension f r) (y : Y)
    (hy : ∃ x : X, f.base x = y) :
    ∃ x : X, f.base x = y ∧ Cardinal.toNat (residueTrdeg f x) = r := by
  obtain ⟨x₀, hx₀⟩ := hy
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({f.asFiber x₀} : Set (f.fiber (f.base x₀))))
    isIrreducible_singleton.closure
  set ζ := hW.1.genericPoint with hζ
  have hζW : IsGenericPoint ζ W :=
    hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
  set x := f.fiberι (f.base x₀) ζ with hxdef
  have hι : ∀ (y : Y) (z : f.fiber y), f.base (f.fiberι y z) = y :=
    fun y z => (f.range_fiberι y).le ⟨z, rfl⟩
  have hfx : f.base x = f.base x₀ := hι _ ζ
  refine ⟨x, hfx.trans hx₀, ?_⟩
  -- a point of the fibre of `x` generalizing `x` is `x`
  have hmaxX : ∀ x' : X, f.base x' = f.base x → x' ⤳ x → x' = x := by
    intro x' hx'f hx'
    have hmem : x' ∈ Set.range (f.fiberι (f.base x₀)).base :=
      (f.range_fiberι _).ge (hx'f.trans hfx)
    obtain ⟨ζ', rfl⟩ := hmem
    have hsp : ζ' ⤳ ζ := (f.fiberι (f.base x₀)).isEmbedding.specializes_iff.mp hx'
    have hsub' : W ⊆ closure ({ζ'} : Set (f.fiber (f.base x₀))) := by
      rw [← hζW]
      exact closure_minimal (Set.singleton_subset_iff.mpr hsp.mem_closure) isClosed_closure
    have hgen : IsGenericPoint ζ' W :=
      Set.Subset.antisymm (hW.2 isIrreducible_singleton.closure hsub') hsub'
    rw [hgen.eq hζW]
  have hmax : IsMax (f.asFiber x) := by
    intro z hz
    have hspec : (f.fiberι (f.base x)).base z ⤳ x := by
      have h' : z ⤳ f.asFiber x := hz
      simpa using h'.map (f.fiberι (f.base x)).continuous
    refine le_of_eq ((f.fiberι (f.base x)).isEmbedding.injective ?_)
    rw [hmaxX _ (hι _ z) hspec]
    exact (Scheme.Hom.fiberι_asFiber f x).symm
  have hzero : ringKrullDim ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x)) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact_mod_cast Order.coheight_eq_zero.mpr hmax
  have hq : LocallyOfFiniteType (f.fiberToSpecResidueField (f.base x)) := by
    show LocallyOfFiniteType (Limits.pullback.snd f (Y.fromSpecResidueField (f.base x)))
    infer_instance
  have hrelx := hrel (f.base x) ⟨f.asFiber x⟩
  have hAt := @topologicalKrullDimAt_eq_of_equidimensional _ _ (f.fiber (f.base x))
    (f.fiberToSpecResidueField (f.base x)) hq r hrelx.1 hrelx.2 (f.asFiber x)
  have hfor := topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg f x
  change topologicalKrullDimAt (f.fiber (f.base x)) (f.asFiber x) =
    ringKrullDim ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x)) +
      (Cardinal.toENat (residueTrdeg f x) : WithBot ℕ∞) at hfor
  rw [hAt, hzero, zero_add] at hfor
  have hENat : Cardinal.toENat (residueTrdeg f x) = r := (WithBot.coe_eq_coe.mp hfor).symm
  simpa [Cardinal.toNat_toENat] using congrArg ENat.toNat hENat

/-- **Delta-dimension drops by `r` along a surjection with fibres equidimensional of dimension
`r`.** If `f : X ⟶ Y` over the base is locally of finite type and surjective, with every fibre
equidimensional of dimension `r`, and `dim_δ X ≤ n`, then `dim_δ Y ≤ n - r`. -/
theorem schemeDeltaDimension_le_sub_of_surjective_of_relativeDimension (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hbase : f ≫ sY = sX)
    (hsurj : Function.Surjective f.base) (r : ℕ) (hrel : AlgebraicGeometry.RelativeDimension f r)
    {n : ℤ} (hX : schemeDeltaDimension C sX ≤ (n : EInt)) :
    schemeDeltaDimension C sY ≤ ((n - r : ℤ) : EInt) := by
  have congr : ∀ {Z : Scheme.{u}} (a b : Z ⟶ C.S) [LocallyOfFiniteType a]
      [LocallyOfFiniteType b], a = b → schemeDeltaDimension C a = schemeDeltaDimension C b := by
    rintro Z a b _ _ rfl; rfl
  have hX' : schemeDeltaDimension C (𝟙 X ≫ sX) ≤ (n : EInt) :=
    (congr _ _ (Category.id_comp sX)).trans_le hX
  have hY := schemeDeltaDimension_le_of_forall_relativeDimension_le C sY (𝟙 Y) (k := n - r)
    fun y => by
      obtain ⟨x, hx, htr⟩ := exists_toNat_residueTrdeg_eq_of_relativeDimension f r hrel y
        (hsurj y)
      have hstep := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY f x
      rw [hbase, htr, hx] at hstep
      have hle := relativeDimension_le_of_schemeDeltaDimension_le C sX (𝟙 X) hX' x
      change relativeDimension C.dimensionFunction sX x ≤ n at hle
      show relativeDimension C.dimensionFunction sY y ≤ n - r
      omega
  exact (congr _ _ (Category.id_comp sY)).symm.trans_le hY

end Stacks.Chow

end
