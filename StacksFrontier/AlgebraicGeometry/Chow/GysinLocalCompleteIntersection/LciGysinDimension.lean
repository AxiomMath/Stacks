module

public import StacksFrontier.AlgebraicGeometry.Chow.RegularImmersionCodimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmoothInputs.FibreDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SmoothConnectedComponents
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.RegularOpenIndependence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.ClosedComposition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.Spreading
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularNormalRank
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.Components
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.RegularImmersionGysinComposition

/-!
# δ-dimensions in the factorization of a local complete intersection morphism

Let `g : U ⟶ Y` be locally of finite type, with `U` and `Y` locally of finite type over the base of
Situation 02QL. At a generic point `η` of an irreducible component of `U`,

  `δ_U(η) = δ_Y(g(η)) + d`,

`d` the dimension at `η` of the fibre of `g` through `η`: the transcendence degree of `κ(η)` over
`κ(g(η))` is the dimension of the fibre at its generic point `η` (Stacks 02JW, Stacks 00OS). When
`g` is flat, `g(η)` is a generic point of an irreducible component of `Y`.

## Main results

* `AlgebraicGeometry.coheight_eq_zero_map_of_flat`: for `g` flat, `g(η)` is a generic point.
* `AlgebraicGeometry.exists_coheight_eq_zero_specializes`: every point is a specialization of a
  generic point of an irreducible component.
* `Stacks.Chow.relativeDimension_eq_add_of_coheight_eq_zero`: `δ_U(η) = δ_Y(g(η)) + d`.
* `Stacks.Chow.relativeDimension_eq_of_closedImmersion_of_smooth`: for a closed immersion
  `i : X ⟶ U` and `g` smooth, `δ_X(ξ) = m + d - r` at a generic point `ξ` of `X`, with `r` the
  dimension of the local ring of `U` at `i(ξ)`.
* `Stacks.Chow.coheight_eq_componentRank_ofIsRegularImmersion`: for a regular closed immersion,
  that dimension is the rank of the normal sheaf at `ξ`.

## References

* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 00OS](https://stacks.math.columbia.edu/tag/00OS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace AlgebraicGeometry

/-- A flat morphism carries a generic point of an irreducible component (a point of coheight zero)
to a generic point of an irreducible component. -/
theorem coheight_eq_zero_map_of_flat {U Y : Scheme.{u}} (g : U ⟶ Y) [Flat g] {η : U}
    (hη : coheight η = 0) : coheight (g η) = 0 := by
  rw [Order.coheight_eq_zero] at hη ⊢
  intro y hy
  obtain ⟨η', hη', rfl⟩ := Flat.generalizingMap g hy
  exact (hη (show η ≤ η' from hη')).map g.continuous

/-- Every point of a scheme is a specialization of a point of coheight zero, the generic point of
an irreducible component containing it. -/
theorem exists_coheight_eq_zero_specializes {U : Scheme.{u}} (x : U) :
    ∃ η : U, coheight η = 0 ∧ η ⤳ x := by
  obtain ⟨W, hW, hxW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x} : Set U)) isIrreducible_singleton.closure
  have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
  have hgen := hW.1.isGenericPoint_genericPoint hWc
  refine ⟨hW.1.genericPoint, ?_, ?_⟩
  · rw [Order.coheight_eq_zero]
    intro y hy
    have hsp : y ⤳ hW.1.genericPoint := hy
    have hyW : closure ({y} : Set U) = W := by
      have h1 : W ⊆ closure ({y} : Set U) := by
        rw [← hgen.def]; exact closure_minimal (Set.singleton_subset_iff.2
          (specializes_iff_mem_closure.1 hsp)) isClosed_closure
      exact (hW.2 isIrreducible_singleton.closure h1).antisymm h1
    have : IsGenericPoint y W := by rw [IsGenericPoint, hyW]
    exact (this.eq hgen ▸ specializes_refl _)
  · exact (hgen.specializes (hxW (subset_closure rfl)))

end AlgebraicGeometry

namespace Stacks.Chow

/-- **`δ_U(η) = δ_Y(g(η)) + d` at a generic point `η` of `U`**, for `g` locally of finite type and
`d` the dimension at `η` of the fibre of `g` through `η`. -/
theorem relativeDimension_eq_add_of_coheight_eq_zero (C : ChowSituation.{u}) {U Y : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (g : U ⟶ Y) [LocallyOfFiniteType g] {η : U}
    (hη : coheight η = 0) (d : ℕ)
    (hd : topologicalKrullDimAt (g.fiber (g η)) (g.asFiber η) = (d : WithBot ℕ∞)) :
    relativeDimension C.dimensionFunction (g ≫ sY) η =
      relativeDimension C.dimensionFunction sY (g η) + d := by
  rw [relativeDimension_comp_eq_add_trdeg]
  congr 2
  have hf := topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk_add_trdeg g η
  have h0 : coheight (g.asFiber η) = 0 := by
    rw [Order.coheight_eq_zero] at hη ⊢
    intro y hy
    have hsp : g.fiberι _ y ⤳ g.fiberι _ (g.asFiber η) := hy.map (g.fiberι _).continuous
    rw [Scheme.Hom.fiberι_asFiber] at hsp
    have h2 : η ⤳ g.fiberι _ y := hη (show η ≤ g.fiberι _ y from hsp)
    have h3 : g.fiberι _ y = g.fiberι _ (g.asFiber η) := by
      rw [Scheme.Hom.fiberι_asFiber]; exact (hsp.antisymm h2).eq
    rw [(g.fiberι _).isEmbedding.injective h3]
  rw [ringKrullDim_stalk_eq_coheight, h0, hd] at hf
  have h4 : Cardinal.toENat (residueTrdeg g η) = d := by
    have := hf.symm
    simp only [WithBot.coe_zero, zero_add] at this
    exact_mod_cast this
  rw [← Cardinal.toNat_toENat, h4]
  rfl

/-- **The δ-dimension of a generic point of a regularly embedded closed subscheme of a scheme
smooth over `Y`**: if `i : X ⟶ U` is a closed immersion, `g : U ⟶ Y` is smooth with fibre dimension
`d` at `i(ξ)`, the local ring of `U` at `i(ξ)` has dimension `r`, and the generic points of the
irreducible components of `Y` through `g(i(ξ))` have δ-dimension `m`, then a generic point `ξ` of
an irreducible component of `X` has `δ_X(ξ) = m + d - r`. -/
theorem relativeDimension_eq_of_closedImmersion_of_smooth (C : ChowSituation.{u})
    {X U Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (i : X ⟶ U)
    [IsClosedImmersion i] (g : U ⟶ Y) [Smooth g] [LocallyOfFiniteType g] {ξ : X}
    {r : ℕ} (hr : coheight (i ξ) = r) (m : ℤ)
    (hY : ∀ y : Y, coheight y = 0 → y ⤳ g (i ξ) → relativeDimension C.dimensionFunction sY y = m)
    (d : ℕ) (hd : topologicalKrullDimAt (g.fiber (g (i ξ))) (g.asFiber (i ξ)) = (d : WithBot ℕ∞)) :
    relativeDimension C.dimensionFunction (i ≫ g ≫ sY) ξ = m + d - r := by
  rw [relativeDimension_comp_closedImmersion]
  have hloc := isLocallyConstant_fiberDimensionAt_of_smooth g
  have hdim : ∀ η : U, coheight η = 0 → η ⤳ i ξ →
      relativeDimension C.dimensionFunction (g ≫ sY) η = m + d := by
    intro η hη hsp
    have hdη : topologicalKrullDimAt (g.fiber (g η)) (g.asFiber η) = (d : WithBot ℕ∞) := by
      rw [← hd]
      obtain ⟨V, hVo, hxV, hV⟩ := (IsLocallyConstant.iff_exists_open _).1 hloc (i ξ)
      exact hV η ((specializes_iff_forall_open.1 hsp) V hVo hxV)
    rw [relativeDimension_eq_add_of_coheight_eq_zero C sY g hη d hdη,
      hY _ (coheight_eq_zero_map_of_flat g hη) (hsp.map g.continuous)]
  obtain ⟨η, hη, hsp⟩ := exists_coheight_eq_zero_specializes (i ξ)
  refine relativeDimension_eq_sub_of_coheight C (g ≫ sY) (i ξ) (m + d) (fun z hz => ?_) hsp
    (hdim η hη hsp) hr
  obtain ⟨η', hη', hsp'⟩ := exists_coheight_eq_zero_specializes z
  exact (relativeDimension_le_of_specializes C (g ≫ sY) hsp').trans
    (hdim η' hη' (hsp'.trans hz)).le

open Stacks.AlgebraicGeometry.RegularIdealSheaf in
/-- **The local ring of the ambient scheme at a generic point of a regularly embedded closed
subscheme has dimension the rank of the normal sheaf there**. -/
theorem coheight_eq_componentRank_ofIsRegularImmersion {X U : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian U] (i : X ⟶ U) [IsClosedImmersion i] (hi : IsRegularImmersion i) {ξ : X}
    (hξ : coheight ξ = 0) :
    coheight (i ξ) = (VirtualNormalBundle.ofIsRegularImmersion i hi).componentRank
      (ConnectedComponents.mk ξ) := by
  have hreg : IsRegularIdealSheaf U.toRingedSpace (definingIdealOfHom i) := by
    have hfac : i.liftCoborder ≫ i.coborderRange.ι = i := i.liftCoborder_ι
    have hci : IsClosedImmersion (i.liftCoborder ≫ i.coborderRange.ι) := by
      rw [hfac]; infer_instance
    have h2 := (Stacks.AlgebraicGeometry.isRegularIdealSheaf_comp_open_iff i.liftCoborder
      i.coborderRange.ι).mpr hi
    rwa [hfac] at h2
  obtain ⟨V, hzV, r, f, hw, hker⟩ :=
    Stacks.AlgebraicGeometry.exists_affine_isWeaklyRegular_generators i hreg ξ
  rw [coheight_eq_of_isWeaklyRegular_ker i ξ hξ hzV f hw hker]
  have hq := Stacks.AlgebraicGeometry.isQuasiRegular_of_isWeaklyRegular _ hw
  have hC := isFiniteLocallyFree_conormalModule i hi
  have h1 := (VirtualNormalBundle.ofIsRegularImmersion i hi).fiberRank_eq_componentRank
    (ConnectedComponents.mk ξ) ξ rfl
  rw [← h1]
  change ((r : ℕ) : ℕ∞) = (Scheme.Modules.fiberRank
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf (conormalModule i)) ξ : ℕ∞)
  rw [AlgebraicGeometry.Scheme.Modules.fiberRank_dualSheaf _ hC ξ]
  exact_mod_cast (Stacks.Conormal.fiberRank_conormalSheaf_eq_of_isQuasiRegular i V.2
    (by rw [Stacks.Conormal.coborderRange_eq_top i]; exact le_top) f hq hker hzV).symm

end Stacks.Chow

end
