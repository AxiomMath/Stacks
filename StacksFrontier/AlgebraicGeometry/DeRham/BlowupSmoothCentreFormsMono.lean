module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsDerived
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsChartMono
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal

/-!
# The first canonical map of a smooth blowup is a monomorphism

Let `f : X ⟶ S` be smooth, `i : Z ⟶ X` a closed immersion of a scheme smooth over `S`, and
`b : X' ⟶ X` the blowing up of `X` along `Z`.  The first canonical map of [Stacks, Tag 0G5G],
`b^*Ω^a_{X/S} ⟶ Ω^a_{X'/S}`, is a monomorphism.  This is step (E2) of the existence half of
[Stacks, Tag 0G5J].  Monomorphy is local on `X'`.  Over an étale chart of [Stacks, Tag 0FUE] the
map is, up to isomorphisms, the pullback along the flat chart map of the coordinate one, which is a
monomorphism (`Stacks.DeRham.mono_blowupFormsPullbackMap`).  Off the centre the blowup is an
isomorphism, and the map is invertible.

## Main results

* `Stacks.DeRham.mono_of_mono_pullback_ι`: monomorphy of a map of modules is local.
* `Stacks.DeRham.isIso_pullback_ι_blowupFormsMap_of_etale`: the map restricted to an open along
  which `b` is étale is invertible.
* `Stacks.DeRham.BlowupEtaleChart.mono_pullback_ι_blowupFormsMap`: the map is a monomorphism over
  a chart.
* `Stacks.DeRham.mono_blowupFormsPullbackMap_blowUpToBase`: the map is a monomorphism.

## References

* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
* [Stacks Project, Tag 0G5J](https://stacks.math.columbia.edu/tag/0G5J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom

universe u

namespace Stacks.DeRham

/-- **Monomorphy of a map of modules is local on an open cover.** -/
theorem mono_of_mono_pullback_ι {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {ι : Type*}
    (V : ι → X.Opens) (hV : iSup V = ⊤) (h : ∀ k, Mono ((Scheme.Modules.pullback (V k).ι).map φ)) :
    Mono φ := by
  refine Preadditive.mono_of_isZero_kernel _ ?_
  refine Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_restrict_cover V hV _
    fun k => ?_
  have : PreservesFiniteLimits (Scheme.Modules.pullback (V k).ι) :=
    preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback (V k).ι)
  have := h k
  refine IsZero.of_iso ?_ ((Scheme.Modules.restrictFunctorIsoPullback (V k).ι).app _ ≪≫
    PreservesKernel.iso (Scheme.Modules.pullback (V k).ι) φ)
  exact isZero_kernel_of_mono _

variable {S X Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}

/-- The first canonical map `b^*Ω^a_{X/S} ⟶ Ω^a_{X'/S}` of a blowup, restricted to an open of
`X'` along which the blowup is étale, is an isomorphism. -/
theorem isIso_pullback_ι_blowupFormsMap_of_etale {Y : Scheme.{u}} (b : Y ⟶ X) (V : Y.Opens)
    [Etale (V.ι ≫ b)] (a : ℤ) :
    IsIso ((Scheme.Modules.pullback V.ι).map
      (relativeDifferentialFormsMap b f (b ≫ f) (𝟙 S) (by simp) a)) := by
  have h := relativeDifferentialFormsMap_comp b V.ι f (b ≫ f) (V.ι ≫ b ≫ f) (𝟙 S) (𝟙 S) (𝟙 S)
    (by simp) (by simp) (by simp) a
  have h1 : IsIso (relativeDifferentialFormsMap (V.ι ≫ b) f (V.ι ≫ b ≫ f) (𝟙 S) (by simp) a) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  have h2 : IsIso (relativeDifferentialFormsMap V.ι (b ≫ f) (V.ι ≫ b ≫ f) (𝟙 S) (by simp) a) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  rw [h, isIso_comp_left_iff, isIso_comp_right_iff] at h1
  exact h1

namespace BlowupEtaleChart

variable (c : BlowupEtaleChart f i)

/-- **The first canonical map is a monomorphism over a chart.** -/
theorem mono_pullback_ι_blowupFormsMap (a : ℕ) :
    Mono ((Scheme.Modules.pullback (blowUpToBase i.ker ⁻¹ᵁ c.U).ι).map
      (relativeDifferentialFormsMap (blowUpToBase i.ker) f (blowUpToBase i.ker ≫ f) (𝟙 S)
        (by simp) (a : ℤ))) := by
  let := c.commRing
  have : PreservesFiniteLimits (Scheme.Modules.pullback c.blowupMap) :=
    Stacks.AlgebraicGeometry.FlatBaseChangeDerived.preservesFiniteLimits_pullback c.blowupMap
  have hL := mono_blowupFormsPullbackMap c.R c.m c.n a
  have hC : Mono ((Scheme.Modules.pullback c.blowupMap).map (blowupFormsPullbackMap c.R c.m c.n a)
      ≫ c.blowupFormsChart (a : ℤ)) := mono_comp _ _
  rw [blowupFormsPullbackMap, c.chart_blowupFormsMap] at hC
  have hM : Mono (c.chartFormsMap (a : ℤ)) := by
    simp only [← Category.assoc] at hC
    exact (mono_comp_iff_of_isIso _ _).1 hC
  have hR : Mono ((Scheme.Modules.pullback (blowUpToBase i.ker ⁻¹ᵁ c.U).ι).map
      (relativeDifferentialFormsMap (blowUpToBase i.ker) f (blowUpToBase i.ker ≫ f) (𝟙 S)
        (by simp) (a : ℤ)) ≫ c.blowupFormsRestrict (a : ℤ)) := by
    rw [c.restrict_blowupFormsMap]
    exact mono_comp _ _
  exact mono_of_mono _ (c.blowupFormsRestrict (a : ℤ))

end BlowupEtaleChart

/-- **(E2) The first canonical map of [Stacks, Tag 0G5G] is a monomorphism** for the blowing up of
a smooth centre: `b^*Ω^a_{X/S} ⟶ Ω^a_{X'/S}` is injective.  No hypothesis on the interior of the
centre is needed. -/
theorem mono_blowupFormsPullbackMap_blowUpToBase [IsClosedImmersion i] [Smooth f]
    [Smooth (i ≫ f)] (a : ℕ) :
    Mono (relativeDifferentialFormsMap (blowUpToBase i.ker) f (blowUpToBase i.ker ≫ f) (𝟙 S)
      (by simp) (a : ℤ)) := by
  classical
  have hloc : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Mono ((Scheme.Modules.pullback (blowUpToBase i.ker ⁻¹ᵁ V).ι).map
        (relativeDifferentialFormsMap (blowUpToBase i.ker) f (blowUpToBase i.ker ≫ f) (𝟙 S)
          (by simp) (a : ℤ))) := by
    intro x
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨c, hzc, -⟩ := exists_blowupEtaleChart f i z ⊤ trivial
      exact ⟨c.U, hzc, c.mono_pullback_ι_blowupFormsMap a⟩
    · let W : X.Opens :=
        ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
      have := isIso_blowUpToBase_restrict_compl_range (i := i)
      have : Etale ((blowUpToBase i.ker ⁻¹ᵁ W).ι ≫ blowUpToBase i.ker) := by
        rw [← morphismRestrict_ι]; infer_instance
      have := isIso_pullback_ι_blowupFormsMap_of_etale (f := f) (blowUpToBase i.ker)
        (blowUpToBase i.ker ⁻¹ᵁ W) (a : ℤ)
      exact ⟨W, hx, inferInstance⟩
  choose V hxV hV using hloc
  refine mono_of_mono_pullback_ι _ (fun x => blowUpToBase i.ker ⁻¹ᵁ V x) ?_ hV
  refine top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨blowUpToBase i.ker y, ?_⟩
  exact hxV _

end Stacks.DeRham
