module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsMono
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsPoleBound
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealAnnihilation
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupTwistDivisor

/-!
# The pole bound for the blowing up of a smooth centre

Let `f : X ⟶ S` be smooth, `i : Z ⟶ X` a closed immersion of a scheme smooth over `S`, and
`b : X' ⟶ X` the blowing up of `X` along `Z`.  This file proves step (E3) of the existence half
of [Stacks, Tag 0G5J]: for an ideal sheaf `𝒟` on `X'` which over every étale chart of
[Stacks, Tag 0FUE] is the inverse image of the ideal of `(n-1)E` of the coordinate model, the
action of `ℐ_𝒟` on `Ω^a_{X'/S}` dies modulo `b^*Ω^a_{X/S}`.  This is the pole bound of
[Stacks, Tag 0G5G], globalized.

The pole bound is stated as the vanishing of `idealAction 𝒟 Ω^a ≫ cokernel.π φ`.  It is proved in
annihilator form (`Stacks.Divisors.IsAnnihilatedBy`):

* the coordinate cokernel is killed by `(n-1)E`, by `Stacks.DeRham.exceptionalPoleBound`;
* annihilation passes to inverse images (`Stacks.Divisors.IsAnnihilatedBy.pullback`);
* over a chart, the restricted cokernel is the inverse image of the coordinate one, since both
  first canonical maps are, up to isomorphisms, the common model `chartFormsMap`;
* off the centre the first canonical map is invertible, so the cokernel vanishes;
* annihilation is local (`Stacks.Divisors.isAnnihilatedBy_of_cover`).

## Main results

* `Stacks.DeRham.BlowupEtaleChart.isAnnihilatedBy_cokernel_restrict`: the pole bound over a chart.
* `Stacks.DeRham.poleBound_of_comap_eq`: the pole bound, for every ideal sheaf with the local
  form of `Σ (c - 1)E_c`.

## References

* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
* [Stacks Project, Tag 0G5J](https://stacks.math.columbia.edu/tag/0G5J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom

universe u

namespace Stacks.DeRham

/-- The cokernel of the first canonical map of the coordinate blowup is killed by the ideal of
`(n-1)E`. -/
theorem isAnnihilatedBy_cokernel_blowupFormsPullbackMap (R : Type u) [CommRing R] (m n a : ℕ) :
    Stacks.Divisors.IsAnnihilatedBy (coordinateExceptional R m n ^ (n - 1))
      (cokernel (blowupFormsPullbackMap R m n a)) :=
  Stacks.Divisors.isAnnihilatedBy_cokernel_of_sections _ _
    (cokernelπ_app_smul_idealSheafSection_eq_zero R m n a)

/-- The cokernel of an arrow is unchanged by pre- and post-composition with isomorphisms. -/
def cokernelIsoOfCompIso {C : Type*} [Category C] [Abelian C] {A B A' B' : C} (u : A ⟶ B)
    (v : A' ⟶ B') (e₁ : A ≅ A') (e₂ : B ≅ B') (w : u ≫ e₂.hom = e₁.hom ≫ v) :
    cokernel u ≅ cokernel v :=
  cokernel.mapIso u v e₁ e₂ w

/-- Restricting the cokernel of `φ` to an open is the cokernel of the restriction of `φ`. -/
private def restrictCokernelIso {Y : Scheme.{u}} (U : Y.Opens) {F G : Y.Modules} (φ : F ⟶ G) :
    (cokernel φ).restrict U.ι ≅ cokernel ((Scheme.Modules.pullback U.ι).map φ) :=
  ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _) ≪≫
    PreservesCokernel.iso (Scheme.Modules.pullback U.ι) _

variable {S X Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}

namespace BlowupEtaleChart

variable (c : BlowupEtaleChart f i)

/-- Over a chart, the cokernel of the restricted first canonical map is that of the common model
`chartFormsMap`. -/
def cokernelRestrictIsoChart (a : ℕ) :
    cokernel ((Scheme.Modules.pullback (blowUpToBase i.ker ⁻¹ᵁ c.U).ι).map
      (relativeDifferentialFormsMap (blowUpToBase i.ker) f (blowUpToBase i.ker ≫ f) (𝟙 S)
        (by simp) (a : ℤ))) ≅ cokernel (c.chartFormsMap (a : ℤ)) :=
  cokernelIsoOfCompIso _ _
    ((Scheme.Modules.pullbackComp (blowUpToBase i.ker ⁻¹ᵁ c.U).ι (blowUpToBase i.ker)).app _ ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι (blowUpToBase i.ker) c.U).symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp (blowUpToBase i.ker ∣_ c.U) c.U.ι).app _).symm ≪≫
      (Scheme.Modules.pullback (blowUpToBase i.ker ∣_ c.U)).mapIso
        (asIso (c.ambientFormsRestrict (a : ℤ))))
    (asIso (c.blowupFormsRestrict (a : ℤ)))
    (by simpa [Category.assoc] using c.restrict_blowupFormsMap (a : ℤ))

/-- Over a chart, the cokernel of the pulled-back coordinate first canonical map is that of the
common model `chartFormsMap`. -/
def cokernelChartIsoChart (a : ℕ) :
    cokernel ((Scheme.Modules.pullback c.blowupMap).map
      (blowupFormsPullbackMap c.R c.m c.n a)) ≅ cokernel (c.chartFormsMap (a : ℤ)) :=
  cokernelIsoOfCompIso _ _
    ((Scheme.Modules.pullbackComp c.blowupMap (coordinateBlowupToAmbient c.R c.m c.n)).app _ ≪≫
      (Scheme.Modules.pullbackCongr c.blowupMap_comm.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp (blowUpToBase i.ker ∣_ c.U) c.g).app _).symm ≪≫
      (Scheme.Modules.pullback (blowUpToBase i.ker ∣_ c.U)).mapIso
        (asIso (c.ambientFormsChart (a : ℤ))))
    (asIso (c.blowupFormsChart (a : ℤ)))
    (by simpa [Category.assoc, blowupFormsPullbackMap] using c.chart_blowupFormsMap (a : ℤ))

/-- **The pole bound over a chart, in annihilator form.**  Over a chart, the cokernel of the first
canonical map is killed by the inverse image of the ideal of `(n-1)E` of the coordinate model. -/
theorem isAnnihilatedBy_cokernel_restrict (a : ℕ) :
    Stacks.Divisors.IsAnnihilatedBy
      ((coordinateExceptional c.R c.m c.n ^ (c.n - 1)).comap c.blowupMap)
      ((cokernel (relativeDifferentialFormsMap (blowUpToBase i.ker) f (blowUpToBase i.ker ≫ f)
        (𝟙 S) (by simp) (a : ℤ))).restrict (blowUpToBase i.ker ⁻¹ᵁ c.U).ι) := by
  let := c.commRing
  have hF := Scheme.Hom.isQuasicoherent_relativeDifferentialForms
    (coordinateAmbientToBase c.R c.m c.n) a
  have hF' : ((Scheme.Modules.pullback (coordinateBlowupToAmbient c.R c.m c.n)).obj
      (relativeDifferentialForms (coordinateAmbientToBase c.R c.m c.n) (a : ℤ))).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _
  have hG := Scheme.Hom.isQuasicoherent_relativeDifferentialForms
    (coordinateBlowupToBase c.R c.m c.n) a
  have h1 := (isAnnihilatedBy_cokernel_blowupFormsPullbackMap c.R c.m c.n a).pullback c.blowupMap
  refine h1.of_iso ?_
  exact PreservesCokernel.iso (Scheme.Modules.pullback c.blowupMap) _ ≪≫
    c.cokernelChartIsoChart a ≪≫ (c.cokernelRestrictIsoChart a).symm ≪≫
    (restrictCokernelIso _ _).symm

end BlowupEtaleChart

/-- **The pole bound, for any ideal sheaf with the local form of `Σ (c - 1)E_c`.**  Let `𝒟` be an
ideal sheaf on the blowup whose restriction over every chart is the inverse image of the ideal of
`(n-1)E` of the coordinate model.  Then `ℐ_𝒟 · Ω^a_{X'/S} ⊆ b^*Ω^a_{X/S}`. -/
theorem poleBound_of_comap_eq [IsClosedImmersion i] [Smooth f] [Smooth (i ≫ f)]
    (D : (blowUp i.ker).IdealSheafData)
    (hD : ∀ c : BlowupEtaleChart f i, D.comap (blowUpToBase i.ker ⁻¹ᵁ c.U).ι =
      (coordinateExceptional c.R c.m c.n ^ (c.n - 1)).comap c.blowupMap) (a : ℕ) :
    Stacks.Divisors.idealAction D (relativeDifferentialForms (blowUpToBase i.ker ≫ f) a) ≫
      cokernel.π (relativeDifferentialFormsMap (blowUpToBase i.ker) f (blowUpToBase i.ker ≫ f)
        (𝟙 S) (by simp) (a : ℤ)) = 0 := by
  classical
  refine Stacks.Divisors.idealAction_comp_cokernelπ_eq_zero _ _ ?_
  have hloc : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Stacks.Divisors.IsAnnihilatedBy (D.comap (blowUpToBase i.ker ⁻¹ᵁ V).ι)
        ((cokernel (relativeDifferentialFormsMap (blowUpToBase i.ker) f
          (blowUpToBase i.ker ≫ f) (𝟙 S) (by simp) (a : ℤ))).restrict
          (blowUpToBase i.ker ⁻¹ᵁ V).ι) := by
    intro x
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨c, hzc, -⟩ := exists_blowupEtaleChart f i z ⊤ trivial
      refine ⟨c.U, hzc, ?_⟩
      rw [hD c]
      exact c.isAnnihilatedBy_cokernel_restrict a
    · let W : X.Opens :=
        ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
      have := isIso_blowUpToBase_restrict_compl_range (i := i)
      have : Etale ((blowUpToBase i.ker ⁻¹ᵁ W).ι ≫ blowUpToBase i.ker) := by
        rw [← morphismRestrict_ι]; infer_instance
      have := isIso_pullback_ι_blowupFormsMap_of_etale (f := f) (blowUpToBase i.ker)
        (blowUpToBase i.ker ⁻¹ᵁ W) (a : ℤ)
      refine ⟨W, hx, Stacks.Divisors.isAnnihilatedBy_of_isZero _ ?_⟩
      exact (isZero_cokernel_of_epi _).of_iso (restrictCokernelIso _ _)
  choose V hxV hV using hloc
  refine Stacks.Divisors.isAnnihilatedBy_of_cover D _
    (fun y => blowUpToBase i.ker ⁻¹ᵁ V (blowUpToBase i.ker y)) ?_ fun y => hV _
  exact top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxV _⟩

/-- **(E3) The pole bound for the twisting divisor `𝒟 = Σ (c - 1)E_c`** of the blowing up of a
smooth centre: `ℐ_𝒟 · Ω^a_{X'/S} ⊆ b^*Ω^a_{X/S}`, stated as the vanishing of the action of `ℐ_𝒟`
modulo the first canonical map.  No hypothesis on the interior of the centre is needed. -/
theorem blowupTwistDivisor_poleBound [IsClosedImmersion i] [Smooth f] [Smooth (i ≫ f)] (a : ℕ) :
    Stacks.Divisors.idealAction (blowupTwistDivisor f i)
        (relativeDifferentialForms (blowUpToBase i.ker ≫ f) a) ≫
      cokernel.π (relativeDifferentialFormsMap (blowUpToBase i.ker) f (blowUpToBase i.ker ≫ f)
        (𝟙 S) (by simp) (a : ℤ)) = 0 :=
  poleBound_of_comap_eq _ (fun c => c.comap_blowupTwistDivisor) a

end Stacks.DeRham
