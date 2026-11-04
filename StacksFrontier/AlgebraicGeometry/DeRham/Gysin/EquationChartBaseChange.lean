module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ChartDataComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartRestriction
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.BaseChange
public import StacksFrontier.AlgebraicGeometry.QuasiRegular.StalkGenerators

/-!
# Pulled-back equation charts

Let

```
Z' --h--> Z
|i'       |i
v         v
X' --g--> X
```

be a cartesian square of schemes with `i` a closed immersion. An equation chart
`Stacks.Gysin.EquationChart i c` of `i` — an open `W` of `X` with `c` sections generating the ideal
of `Z` over `W` — pulls back to an equation chart of `i'` with ambient open `g⁻¹W` and equations
the pulled-back sections `g^♯(f₁), …, g^♯(f_c)`. No hypothesis is placed on `g`.

## Main results

* `Stacks.Gysin.isGeneratedByOn_of_forall_exists_isGeneratedByOn`: generation of an ideal sheaf on
  an open is local on that open.
* `Stacks.Gysin.isGeneratedByOn_definingIdealOfHom_of_isPullback`: sections generating the ideal of
  `i` over `W` pull back to sections generating the ideal of `i'` over `g⁻¹W`.
* `Stacks.Gysin.EquationChart.ofIsPullback`: the pulled-back equation chart.
* `Stacks.Gysin.restrictEquations_preimage`: the pulled-back equations read on `g⁻¹W` are the
  equations read on `W` pulled back along `g ∣_ W`.

## References

* [Stacks Project, Tag 0G89](https://stacks.math.columbia.edu/tag/0G89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RingedSpace

universe u

namespace Stacks.Gysin

/-- Generation of an ideal sheaf on an open is local on that open: if every point of `V` has a
neighbourhood `W ≤ V` on which the restrictions of `f` generate `J`, then `f` generates `J` on
`V`. -/
theorem isGeneratedByOn_of_forall_exists_isGeneratedByOn {X : Scheme.{u}}
    (J : (structureSheafModule X.toRingedSpace).Submodule) {V : X.Opens} {r : ℕ}
    (f : Fin r → Γ(X, V))
    (h : ∀ y ∈ V, ∃ (W : X.Opens) (hWV : W ≤ V), y ∈ W ∧
      IsGeneratedByOn X.toRingedSpace J W (fun k => X.presheaf.map (homOfLE hWV).op (f k))) :
    IsGeneratedByOn X.toRingedSpace J V f := by
  refine isGeneratedByOn_of_forall_stalkIdeal_eq (X := X.toLocallyRingedSpace) J f
    fun y hy => ?_
  obtain ⟨W, hWV, hyW, hW⟩ := h y hy
  rw [stalkIdeal_eq_jid_of_isGeneratedByOn (X := X.toLocallyRingedSpace) J _ hW y hyW,
    germFamily_res V W hWV f y hyW]

variable {Z X Z' X' : Scheme.{u}} {h : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {g : X' ⟶ X}

/-- Generators of the ideal of a closed immersion pull back to generators of the ideal of its base
change: for a cartesian square `h ≫ i = i' ≫ g` with `i` a closed immersion, if
`e₁, …, e_c ∈ Γ(X, W)` generate the defining ideal of `i` over `W`, then
`g^♯(e₁), …, g^♯(e_c) ∈ Γ(X', g⁻¹W)` generate the defining ideal of `i'` over `g⁻¹W`. -/
theorem isGeneratedByOn_definingIdealOfHom_of_isPullback (hcart : IsPullback h i' i g)
    [IsClosedImmersion i] {W : X.Opens} {c : ℕ} (e : Fin c → Γ(X, W))
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W e) :
    IsGeneratedByOn X'.toRingedSpace (definingIdealOfHom i') (g ⁻¹ᵁ W)
      (fun k => (g.app W).hom (e k)) := by
  have _ : IsClosedImmersion i' := MorphismProperty.of_isPullback hcart inferInstance
  refine isGeneratedByOn_of_forall_exists_isGeneratedByOn _ _ fun y' hy' => ?_
  obtain ⟨U, hU, hyU, hUW⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show g y' ∈ W from hy')
  obtain ⟨U', hU', hyU', hU'U⟩ := Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
    (show y' ∈ g ⁻¹ᵁ U from hyU)
  have hU'W : U' ≤ g ⁻¹ᵁ W := hU'U.trans (g.preimage_mono hUW)
  refine ⟨U', hU'W, hyU', ?_⟩
  set s : Fin c → Γ(X, U) := fun k => X.presheaf.map (homOfLE hUW).op (e k) with hs
  have hgenU : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) U s :=
    isGeneratedByOn_of_le W e hgen U hUW
  have hkerU : RingHom.ker (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom = Ideal.span (Set.range s) := by
    rw [Scheme.Hom.appLE_eq_app]
    exact Stacks.AlgebraicGeometry.ker_app_eq_span_range i hU s hgenU
  have hsurj : Function.Surjective (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact i.app_surjective U hU
  have hTU' : i' ⁻¹ᵁ U' ≤ h ⁻¹ᵁ (i ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, hcart.w, Scheme.Hom.comp_preimage]
    exact i'.preimage_mono hU'U
  have hPZ := Stacks.AlgebraicGeometry.isPushout_appLE_of_isPullback_affineOpens hcart hU
    (hU.preimage i) hU' le_rfl hU'U (Q := i' ⁻¹ᵁ U') (inf_eq_right.mpr hTU').symm
  have hkerU' : RingHom.ker (i'.app U').hom =
      Ideal.span (Set.range fun k => (g.appLE U U' hU'U).hom (s k)) := by
    have hk := Stacks.Flatness.ker_inl_of_isPushout hPZ.flip hsurj
    rw [Scheme.Hom.appLE_eq_app (f := i') (U := U')] at hk
    rw [hk, hkerU, Ideal.map_span, ← Set.range_comp]
    rfl
  have hfam : (fun k => X'.presheaf.map (homOfLE hU'W).op ((g.app W).hom (e k))) =
      fun k => (g.appLE U U' hU'U).hom (s k) := by
    funext k
    rw [hs]
    show (g.app W ≫ X'.presheaf.map (homOfLE hU'W).op).hom (e k) =
      (X.presheaf.map (homOfLE hUW).op ≫ g.appLE U U' hU'U).hom (e k)
    rw [Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  rw [hfam]
  exact Stacks.AlgebraicGeometry.isGeneratedByOn_definingIdealOfHom_of_ker_app_eq_span i' hU' _
    hkerU'

/-- For `g : X' ⟶ X`, an open `W` of `X` and sections `f : I → Γ(X, W)`, the equations `g^♯(fₖ)`
read as global sections of `g⁻¹W` are the images under `(g ∣_ W)^♯` of the `fₖ` read as global
sections of `W`. -/
theorem restrictEquations_preimage (g : X' ⟶ X) (W : X.Opens) {I : Type*}
    (f : I → Γ(X, W)) :
    restrictEquations (g ⁻¹ᵁ W) (fun k => (g.app W).hom (f k)) =
      fun k => (g ∣_ W).appTop (restrictEquations W f k) := by
  funext k
  rw [restrictEquations_apply, restrictEquations_apply, morphismRestrict_appTop,
    ← ConcreteCategory.comp_apply]
  have key : g.app W ≫ X'.presheaf.map (eqToHom (g ⁻¹ᵁ W).ι_image_top).op =
      X.presheaf.map (eqToHom W.ι_image_top).op ≫ g.app (W.ι ''ᵁ ⊤) ≫
        X'.presheaf.map (eqToHom (image_morphismRestrict_preimage g W ⊤)).op := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map,
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
    simp only [Scheme.Hom.preimage_top]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (f k)) key

/-- The pulled-back equation chart: for a cartesian square `h ≫ i = i' ≫ g` with `i` a closed
immersion, an equation chart of `i` with ambient open `W` and equations `f₁, …, f_c` gives the
equation chart of `i'` with ambient open `g⁻¹W` and equations `g^♯(f₁), …, g^♯(f_c)`. -/
def EquationChart.ofIsPullback (hcart : IsPullback h i' i g) [IsClosedImmersion i] {c : ℕ}
    (a : EquationChart i c) : EquationChart i' c where
  ambient := g ⁻¹ᵁ a.ambient
  equations k := (g.app a.ambient).hom (a.equations k)
  gen := isGeneratedByOn_definingIdealOfHom_of_isPullback hcart a.equations a.gen
  vanish V hV k := by
    have hmem : (g.app a.ambient).hom (a.equations k) ∈
        (definingIdealOfHom i').obj (op (g ⁻¹ᵁ a.ambient)) := by
      rw [isGeneratedByOn_definingIdealOfHom_of_isPullback hcart a.equations a.gen _ le_rfl]
      exact mem_generatedIdealOn X'.toRingedSpace _ _ k
    exact (definingIdealOfHom i').toSubmodule.map_mem (homOfLE hV).op hmem

end Stacks.Gysin

end
