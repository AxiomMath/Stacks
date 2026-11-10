module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.Section
public import StacksFrontier.RingTheory.Smooth.ConormalSectionCompletion

/-!
# The power series chart of a smooth morphism along a section

Let `f : X ⟶ S` be smooth with `S` locally Noetherian, `σ` a section of `f` and `s ∈ S`. Near
`σ(s)` the completion of `X` along `σ` is a power series ring over the base: there are an affine
open `U ∋ s` of `S`, an integer `d` and a flat morphism `φ : Spec Γ(S, U)[[t_1, …, t_d]] ⟶ X`
lying over `U` under which the zero section `t = 0` is the section `σ`.

## Main results

* `AlgebraicGeometry.exists_flat_powerSeries_chart_of_section` — the chart.

## References

* [Stacks Project, Tag 00MB](https://stacks.math.columbia.edu/tag/00MB)
* [Stacks Project, Tag 05D5](https://stacks.math.columbia.edu/tag/05D5)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The power series chart along a section.** Let `f : X ⟶ S` be smooth with `S` locally
Noetherian, `σ` a section of `f` and `s ∈ S`. There are an affine open `U ∋ s`, an integer `d`
and a flat morphism `φ : Spec Γ(S, U)[[t_1, …, t_d]] ⟶ X` with `f ∘ φ` the structure map to
`U ⊆ S`, and with `φ` restricted to the zero section `t = 0` equal to `σ` on `U`. -/
theorem exists_flat_powerSeries_chart_of_section {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    [IsLocallyNoetherian S] (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (s : S) :
    ∃ (U : S.Opens) (hU : IsAffineOpen U) (_ : s ∈ U) (d : ℕ)
      (φ : Spec (.of (MvPowerSeries (Fin d) Γ(S, U))) ⟶ X),
      Flat φ ∧ φ ≫ f = Spec.map (CommRingCat.ofHom MvPowerSeries.C) ≫ hU.fromSpec ∧
        Spec.map (CommRingCat.ofHom MvPowerSeries.constantCoeff) ≫ φ = hU.fromSpec ≫ σ := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨U, V, hU, hV, hsU, -, hVU, hUV, sectionHom, hsec, hfree, -⟩ :=
    exists_affineOpens_free_conormal_powerSeries f σ hσ s
      (InfinitesimalLifting.smoothAt_of_smooth f _)
  let : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  have hsm : Algebra.Smooth Γ(S, U) Γ(X, V) := RingHom.smooth_algebraMap.mp
    (HasRingHomProperty.appLE (P := @Smooth) f inferInstance ⟨U, hU⟩ ⟨V, hV⟩ hVU)
  let : Algebra Γ(X, V) Γ(S, U) := sectionHom.toAlgebra
  obtain ⟨eAdic, heAdic⟩ :=
    exists_adicCompletion_algEquiv_mvPowerSeries_constantCoeff sectionHom hsm hfree
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hflat : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, V) (AdicCompletion (RingHom.ker sectionHom) Γ(X, V))))) := by
    refine Flat.SpecMap_iff.mpr ?_
    rw [CommRingCat.hom_ofHom]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hC : f.appLE U V hVU ≫ CommRingCat.ofHom
      (algebraMap Γ(X, V) (AdicCompletion (RingHom.ker sectionHom) Γ(X, V))) ≫
        eAdic.toRingEquiv.toCommRingCatIso.hom = CommRingCat.ofHom MvPowerSeries.C := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    change eAdic (algebraMap Γ(S, U) (AdicCompletion (RingHom.ker sectionHom) Γ(X, V)) a) = _
    rw [AlgEquiv.commutes, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    rfl
  have hcc : CommRingCat.ofHom
      (algebraMap Γ(X, V) (AdicCompletion (RingHom.ker sectionHom) Γ(X, V))) ≫
        eAdic.toRingEquiv.toCommRingCatIso.hom ≫
          CommRingCat.ofHom MvPowerSeries.constantCoeff = σ.appLE V U hUV := by
    refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    change MvPowerSeries.constantCoeff
      (eAdic (algebraMap Γ(X, V) (AdicCompletion (RingHom.ker sectionHom) Γ(X, V)) b)) = _
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, heAdic,
      ← hsec]
    rfl
  refine ⟨U, hU, hsU, _, Spec.map eAdic.toRingEquiv.toCommRingCatIso.hom ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, V) (AdicCompletion (RingHom.ker sectionHom) Γ(X, V)))) ≫ hV.fromSpec,
    inferInstance, ?_, ?_⟩
  · rw [← hC, Category.assoc, Category.assoc,
      ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU]
    simp only [Spec.map_comp, Category.assoc]
  · rw [← IsAffineOpen.SpecMap_appLE_fromSpec σ hV hU hUV, ← hcc]
    simp only [Spec.map_comp, Category.assoc]

end AlgebraicGeometry

end
