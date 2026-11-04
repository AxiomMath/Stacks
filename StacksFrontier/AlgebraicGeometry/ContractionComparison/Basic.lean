module

public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaMap.Consequence
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.Defs

/-!
# Comparing two contractions through an ample invertible module

Let `d : X ⟶ Y₀` and `c : X ⟶ Y` be surjective morphisms with `𝒪_{Y₀} = d_*𝒪_X` and
`𝒪_Y = c_*𝒪_X` and reduced separated targets, and let `L₀`, `L` be ample invertible modules on
`Y₀`, `Y` with `d^*L₀ ≅ c^*L`. Then `Y₀ ≅ Y` under `X`. This is the last step of the uniqueness
in [Stacks, Tag 0E7Q], where the source identifies both targets with `Proj` of the common section
ring; here the identification is made chart by chart instead, without `Proj`.

The charts: for an affine nonvanishing locus `Y_s` of a section `s` of `L^{⊗ n}`, the section
`c^*s` of `(c^*L)^{⊗ n} ≅ (d^*L₀)^{⊗ n}` descends to a section `s₀` of `L₀^{⊗ n}`, because the unit
`L₀^{⊗ n} ⟶ d_*d^*L₀^{⊗ n}` is an isomorphism (projection formula), and
`d⁻¹(Y₀)_{s₀} = c⁻¹Y_s`. On such a pair of opens the ring map
`Γ(Y, Y_s) ⟶ Γ(X, c⁻¹Y_s) = Γ(X, d⁻¹(Y₀)_{s₀}) ≅ Γ(Y₀, (Y₀)_{s₀})` gives a morphism
`(Y₀)_{s₀} ⟶ Y`, and these glue, the overlaps being compared after the surjection `d`.

## Main results

* `Stacks.ContractionComparison.exists_comp_eq`: `c` factors through `d` given opens
  `V₀ i ⊆ Y₀` covering `Y₀` and affine opens `V i ⊆ Y` with `d⁻¹V₀ i ⊆ c⁻¹V i`.
* `Stacks.ContractionComparison.exists_modulePullbackSection_eq`: global sections of `d^*N`
  descend along `d` for an invertible `N`, when `𝒪_{Y₀} = d_*𝒪_X`.
* `Stacks.ContractionComparison.exists_preimage_nonvanishingOpen_eq`.
* `Stacks.ContractionComparison.exists_iso_comp_eq_of_isAmple`: the comparison `Y₀ ≅ Y`.

## References

* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.ContractionComparison

/-! ### Comparing two contractions chart by chart -/

section Core

variable {X Y₀ Y : Scheme.{u}} (d : X ⟶ Y₀) (c : X ⟶ Y)

/-- **The chart map** `V₀ ⟶ Y` attached to opens `V₀ ⊆ Y₀`, `V ⊆ Y` with `V` affine,
`d⁻¹V₀ ⊆ c⁻¹V` and `Γ(Y₀, V₀) ≅ Γ(X, d⁻¹V₀)`: it corresponds to the ring map
`Γ(Y, V) ⟶ Γ(X, d⁻¹V₀) ≅ Γ(Y₀, V₀)`. -/
def chartHom {V₀ : Y₀.Opens} {V : Y.Opens} (hV : IsAffineOpen V) (hle : d ⁻¹ᵁ V₀ ≤ c ⁻¹ᵁ V)
    [IsIso (d.app V₀)] : V₀.toScheme ⟶ Y :=
  V₀.toSpecΓ ≫ Spec.map (c.appLE V (d ⁻¹ᵁ V₀) hle ≫ inv (d.app V₀)) ≫ hV.fromSpec

variable {d c} {V₀ : Y₀.Opens} {V : Y.Opens} (hV : IsAffineOpen V) (hle : d ⁻¹ᵁ V₀ ≤ c ⁻¹ᵁ V)
  [IsIso (d.app V₀)]

/-- The chart map recovers `c` on `d⁻¹V₀`. -/
@[reassoc]
theorem resLE_chartHom :
    d.resLE V₀ (d ⁻¹ᵁ V₀) le_rfl ≫ chartHom d c hV hle = (d ⁻¹ᵁ V₀).ι ≫ c := by
  rw [chartHom, ← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, ← Spec.map_comp_assoc,
    Category.assoc, ← Scheme.Hom.app_eq_appLE, IsIso.inv_hom_id, Category.comp_id,
    Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec,
    Scheme.Hom.resLE_comp_ι]

/-- **The chart relation**: if `t₀ : T ⟶ V₀` and `t : T ⟶ X` agree in `Y₀` through `d`, then
they agree in `Y` through the chart map and `c`. -/
theorem comp_chartHom {T : Scheme.{u}} (t : T ⟶ X) (t₀ : T ⟶ V₀.toScheme)
    (h : t₀ ≫ V₀.ι = t ≫ d) : t₀ ≫ chartHom d c hV hle = t ≫ c := by
  have hr : Set.range t ⊆ Set.range (d ⁻¹ᵁ V₀).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    show d (t x) ∈ V₀
    rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
    exact (t₀ x).2
  have hw : IsOpenImmersion.lift (d ⁻¹ᵁ V₀).ι t hr ≫ (d ⁻¹ᵁ V₀).ι = t :=
    IsOpenImmersion.lift_fac _ _ _
  have ht₀ : t₀ = IsOpenImmersion.lift (d ⁻¹ᵁ V₀).ι t hr ≫ d.resLE V₀ (d ⁻¹ᵁ V₀) le_rfl := by
    rw [← cancel_mono V₀.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, reassoc_of% hw, h]
  rw [ht₀, Category.assoc, resLE_chartHom, reassoc_of% hw]

variable (d c) in
/-- **A contraction factors through another one, chart by chart**: let `d : X ⟶ Y₀` be
surjective with `Y₀` reduced, `c : X ⟶ Y` with `Y` separated, and let `V₀ i` cover `Y₀` with
`Γ(Y₀, V₀ i) ≅ Γ(X, d⁻¹V₀ i)` and `d⁻¹V₀ i ⊆ c⁻¹V i` for affine opens `V i ⊆ Y`. Then `c`
factors through `d`. -/
theorem exists_comp_eq [Surjective d] [IsReduced Y₀] [Y.IsSeparated] {ι : Type*}
    (V₀ : ι → Y₀.Opens) (V : ι → Y.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (hle : ∀ i, d ⁻¹ᵁ V₀ i ≤ c ⁻¹ᵁ V i) (hd : ∀ i, IsIso (d.app (V₀ i)))
    (hcov : IsOpenCover V₀) : ∃ e : Y₀ ⟶ Y, d ≫ e = c := by
  let 𝒰 := Y₀.openCoverOfIsOpenCover V₀ hcov
  let g : ∀ i, 𝒰.X i ⟶ Y := fun i => have := hd i; chartHom d c (hV i) (hle i)
  have hg : ∀ i j : ι,
      pullback.fst (V₀ i).ι (V₀ j).ι ≫ g i = pullback.snd (V₀ i).ι (V₀ j).ι ≫ g j := by
    intro i j
    have := hd i
    have := hd j
    have : IsReduced (pullback (V₀ i).ι (V₀ j).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst (V₀ i).ι (V₀ j).ι ≫ (V₀ i).ι)
    let q := pullback.fst (pullback.fst (V₀ i).ι (V₀ j).ι ≫ (V₀ i).ι) d
    let t := pullback.snd (pullback.fst (V₀ i).ι (V₀ j).ι ≫ (V₀ i).ι) d
    have hq : (q ≫ pullback.fst (V₀ i).ι (V₀ j).ι) ≫ (V₀ i).ι = t ≫ d := by
      rw [Category.assoc]
      exact pullback.condition (f := pullback.fst (V₀ i).ι (V₀ j).ι ≫ (V₀ i).ι) (g := d)
    have hq' : (q ≫ pullback.snd (V₀ i).ι (V₀ j).ι) ≫ (V₀ j).ι = t ≫ d := by
      rw [Category.assoc, ← pullback.condition (f := (V₀ i).ι) (g := (V₀ j).ι), ← Category.assoc]
      exact hq
    refine ext_of_isDominant q ?_
    rw [← Category.assoc, ← Category.assoc]
    exact (comp_chartHom (hV i) (hle i) t _ hq).trans (comp_chartHom (hV j) (hle j) t _ hq').symm
  refine ⟨𝒰.glueMorphisms g hg, ?_⟩
  refine (X.openCoverOfIsOpenCover (fun i => d ⁻¹ᵁ V₀ i) ?_).hom_ext _ _ fun (i : ι) => ?_
  · exact IsOpenCover.mk (by
      rw [← Scheme.Hom.preimage_iSup, hcov.iSup_eq_top, Scheme.Hom.preimage_top])
  · have := hd i
    have h1 : (V₀ i).ι ≫ 𝒰.glueMorphisms g hg = g i := 𝒰.ι_glueMorphisms g hg i
    show (d ⁻¹ᵁ V₀ i).ι ≫ d ≫ _ = (d ⁻¹ᵁ V₀ i).ι ≫ c
    rw [← Scheme.Hom.resLE_comp_ι_assoc d (le_refl (d ⁻¹ᵁ V₀ i)), h1]
    exact resLE_chartHom (hV i) (hle i)

end Core

/-! ### Descending a section of the pullback of an invertible module -/

section Descent

open Stacks.RingedSpace RingedSpaceModuleAdjunction Opposite

variable {X Y₀ : Scheme.{u}} (d : X ⟶ Y₀)

/-- **Sections of `d^*N` descend when `𝒪_{Y₀} = d_*𝒪_X`**, for an invertible `N`: the unit
`N ⟶ d_*d^*N` is an isomorphism (projection formula), so every global section of `d^*N` is the
pullback of a global section of `N`. -/
theorem exists_modulePullbackSection_eq
    (hd : IsIso (SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom)) (N : Y₀.Modules)
    [Stacks.SheafOfModules.IsInvertible Y₀.sheaf.obj
      (structureRingSheaf Y₀.toRingedSpace).property N]
    (v : ((modulePullback d.toLRSHom.toShHom).obj N).sections) :
    ∃ s : N.sections, Stacks.SheafOfModules.modulePullbackSection d.toLRSHom N s = v := by
  have hu : IsIso ((pullbackAdjunction d.toLRSHom.toShHom).unit.app N) :=
    Stacks.ProjectionFormula.isIso_unit_app_of_isIso _ N hd
      (Stacks.ProjectionFormula.isIso_projectionFormulaMap _ _ N)
  let e := asIso ((pullbackAdjunction d.toLRSHom.toShHom).unit.app N)
  refine ⟨Stacks.SheafOfModules.sectionsOfTop N (e.inv.val.app (op ⊤) (v.eval (op ⊤))), ?_⟩
  refine Stacks.SheafOfModules.sections_ext_of_eval_top _ ?_
  refine (Stacks.SheafOfModules.modulePullbackSection_eval_top _ _ _).trans ?_
  show e.hom.val.app (op ⊤) ((Stacks.SheafOfModules.sectionsOfTop N
    (e.inv.val.app (op ⊤) (v.eval (op ⊤)))).eval (op ⊤)) = _
  refine (congrArg (fun z => e.hom.val.app (op ⊤) z)
    (Stacks.SheafOfModules.sectionsOfTop_eval_top N _)).trans ?_
  show (e.inv ≫ e.hom).val.app (op ⊤) (v.eval (op ⊤)) = _
  rw [e.inv_hom_id]
  rfl

open Stacks.SheafOfModules.Invertible (tensorPower tensorPowerCongr) in
/-- **Nonvanishing loci transport across `d^*L₀ ≅ c^*L`**: for a section `s₀` of `L₀^{⊗ n}` on
`Y₀` there is a section `s` of `L^{⊗ n}` on `Y` with `d⁻¹(Y₀)_{s₀} = c⁻¹Y_s`, when
`𝒪_Y = c_*𝒪_X`. The pullback of `s₀`, carried across `(d^*L₀)^{⊗ n} ≅ (c^*L)^{⊗ n}`, descends
along `c` (`exists_modulePullbackSection_eq`), and none of these steps moves a nonvanishing
locus. -/
theorem exists_preimage_nonvanishingOpen_eq {Y : Scheme.{u}} (c : X ⟶ Y)
    (hc : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (L₀ : Y₀.Modules) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y₀.toRingedSpace.presheaf
      (structureSheafRing Y₀.toRingedSpace).property L₀]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback d).obj L₀)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback c).obj L)]
    (φ : (Scheme.Modules.pullback d).obj L₀ ≅ (Scheme.Modules.pullback c).obj L) (n : ℕ)
    (s₀ : (tensorPower Y₀.toRingedSpace.presheaf (structureSheafRing Y₀.toRingedSpace).property
      L₀ (n : ℤ)).sections) :
    ∃ s : (tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property
        L (n : ℤ)).sections,
      d ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen (X := Y₀.toRingedSpace) _ s₀ =
        c ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen (X := Y.toRingedSpace) _ s := by
  let t₀ := SheafOfModules.sectionsMap (Scheme.Modules.pullbackTensorPowerIso d L₀ n).hom
    (Stacks.SheafOfModules.modulePullbackSection d.toLRSHom _ s₀)
  let ψ := tensorPowerCongr X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
    _ _ φ n
  let t := SheafOfModules.sectionsMap ψ.hom t₀
  let v := SheafOfModules.sectionsMap (Scheme.Modules.pullbackTensorPowerIso c L n).inv t
  have : Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (structureRingSheaf Y.toRingedSpace).property
      (tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property
        L (n : ℤ)) :=
    Scheme.Modules.isInvertible_tensorPower Y L n
  obtain ⟨s, hs⟩ := exists_modulePullbackSection_eq c hc _ v
  refine ⟨s, ?_⟩
  have h₁ := Scheme.Modules.nonvanishingOpen_pullbackTensorPowerIso d L₀ n s₀
  have h₂ := Scheme.Modules.nonvanishingOpen_pullbackTensorPowerIso c L n s
  have hψ : Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) _ t =
      Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) _ t₀ :=
    Opens.ext (Stacks.SheafOfModules.nonvanishingLocus_sectionsMap X.toRingedSpace ψ t₀)
  have hv : SheafOfModules.sectionsMap (Scheme.Modules.pullbackTensorPowerIso c L n).hom
      (Stacks.SheafOfModules.modulePullbackSection c.toLRSHom _ s) = t := by
    rw [hs]
    exact (SheafOfModules.sectionsMap_comp (Scheme.Modules.pullbackTensorPowerIso c L n).inv
      (Scheme.Modules.pullbackTensorPowerIso c L n).hom t).symm.trans
      ((congrArg (fun g => SheafOfModules.sectionsMap g t) (Iso.inv_hom_id _)).trans
        (SheafOfModules.sectionsMap_id t))
  exact h₁.symm.trans (hψ.symm.trans ((congrArg
    (Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) _) hv).symm.trans h₂))

end Descent

/-! ### Two contractions identifying ample modules -/

section Ample

open Stacks.SheafOfModules.Invertible (tensorPower)
open Opposite

variable {X Y₀ Y : Scheme.{u}} (d : X ⟶ Y₀) (c : X ⟶ Y)

/-- **A contraction factors through another one identifying ample modules**: let `d : X ⟶ Y₀`
be surjective with `𝒪_{Y₀} = d_*𝒪_X` and `Y₀` reduced, `c : X ⟶ Y` with `𝒪_Y = c_*𝒪_X` and `Y`
separated, and let `L₀`, `L` be invertible on `Y₀`, `Y` with `L` ample and `d^*L₀ ≅ c^*L`. Then
`c` factors through `d`: each affine `Y_s`, `s ∈ Γ(Y, L^{⊗ n})`, has `c⁻¹Y_s = d⁻¹(Y₀)_{s₀}`
for some `s₀`, and these charts glue (`exists_comp_eq`). -/
theorem exists_comp_eq_of_isAmple [Surjective d] [IsReduced Y₀] [Y.IsSeparated]
    (hd : IsIso (SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom))
    (hc : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (L₀ : Y₀.Modules) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y₀.toRingedSpace.presheaf
      (structureSheafRing Y₀.toRingedSpace).property L₀]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L]
    (φ : (Scheme.Modules.pullback d).obj L₀ ≅ (Scheme.Modules.pullback c).obj L)
    (hL : Scheme.Modules.IsAmple Y L) : ∃ e : Y₀ ⟶ Y, d ≫ e = c := by
  have key := fun (n : ℕ) (s : (tensorPower Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L (n : ℤ)).sections) =>
    exists_preimage_nonvanishingOpen_eq c d hd L L₀ φ.symm n s
  let ι := Σ n : ℕ, {s : (tensorPower Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L (n : ℤ)).sections //
    IsAffineOpen (Stacks.SheafOfModules.nonvanishingOpen (X := Y.toRingedSpace) _ s)}
  let V : ι → Y.Opens := fun i =>
    Stacks.SheafOfModules.nonvanishingOpen (X := Y.toRingedSpace) _ i.2.1
  let V₀ : ι → Y₀.Opens := fun i =>
    Stacks.SheafOfModules.nonvanishingOpen (X := Y₀.toRingedSpace) _ (key i.1 i.2.1).choose
  have hV₀ : ∀ i, d ⁻¹ᵁ V₀ i = c ⁻¹ᵁ V i := fun i => (key i.1 i.2.1).choose_spec.symm
  refine exists_comp_eq d c V₀ V (fun i => i.2.2) (fun i => (hV₀ i).le) (fun i => ?_) ?_
  · have hO : IsIso (C := Y₀.Modules)
        (SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom) := hd
    let e := ((Scheme.Modules.toPresheaf Y₀).mapIso (@asIso _ _ _ _ _ hO)).app (op (V₀ i))
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (ConcreteCategory.bijective_of_isIso e.hom)
  · refine IsOpenCover.mk (eq_top_iff.2 fun y₀ _ => ?_)
    obtain ⟨x, rfl⟩ := d.surjective y₀
    obtain ⟨n, -, s, hxs, haff⟩ := hL.exists_affine_nonvanishingLocus (c x)
    refine Opens.mem_iSup.2 ⟨⟨n, s, haff⟩, ?_⟩
    show x ∈ d ⁻¹ᵁ V₀ ⟨n, s, haff⟩
    rwa [hV₀]

/-- **Two contractions identifying ample modules are isomorphic under the source**: let
`d : X ⟶ Y₀` and `c : X ⟶ Y` be surjective with `𝒪_{Y₀} = d_*𝒪_X`, `𝒪_Y = c_*𝒪_X` and reduced
separated targets, and let `L₀`, `L` be ample invertible modules on `Y₀`, `Y` with
`d^*L₀ ≅ c^*L`. Then `Y₀ ≅ Y` under `X`. -/
theorem exists_iso_comp_eq_of_isAmple [Surjective d] [Surjective c] [IsReduced Y₀]
    [IsReduced Y] [Y₀.IsSeparated] [Y.IsSeparated]
    (hd : IsIso (SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom))
    (hc : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (L₀ : Y₀.Modules) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y₀.toRingedSpace.presheaf
      (structureSheafRing Y₀.toRingedSpace).property L₀]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L]
    (φ : (Scheme.Modules.pullback d).obj L₀ ≅ (Scheme.Modules.pullback c).obj L)
    (hL₀ : Scheme.Modules.IsAmple Y₀ L₀) (hL : Scheme.Modules.IsAmple Y L) :
    ∃ e : Y₀ ≅ Y, d ≫ e.hom = c := by
  obtain ⟨e, he⟩ := exists_comp_eq_of_isAmple d c hd hc L₀ L φ hL
  obtain ⟨e', he'⟩ := exists_comp_eq_of_isAmple c d hc hd L L₀ φ.symm hL₀
  refine ⟨⟨e, e', ext_of_isDominant d ?_, ext_of_isDominant c ?_⟩, he⟩
  · rw [reassoc_of% he, he', Category.comp_id]
  · rw [reassoc_of% he', he, Category.comp_id]

end Ample

end Stacks.ContractionComparison
