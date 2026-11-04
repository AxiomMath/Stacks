module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogResidue
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogExteriorPower
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.EquationDivision
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.IdealTrivializationCover
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.DeRhamComplexLogPoles
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.PullbackCup
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge

/-!
# Wedging a form vanishing on a divisor with a form with logarithmic poles

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor, cut out by
`I`, for which the de Rham complex of log poles is defined (Tag 0FMV). Let `𝒦^p ⊆ Ω^p_{X/S}` be
the `p`-forms vanishing on `Y`. For `k ∈ 𝒦^p` and a form `ψ` with logarithmic poles along `Y`,
the wedge product `k ∧ ψ` has no pole: on a chart with local equation `t`, `k = t · (t⁻¹ k)` with
`t⁻¹ k` a form with logarithmic poles, so `k ∧ ψ = t · (t⁻¹ k ∧ ψ)`, and a form with logarithmic
poles times a local section of the ideal sheaf has no pole. This file constructs the resulting
pairing `𝒦^p × Ω^1_{X/S}(log Y) ⟶ Ω^{p+1}_{X/S}` sectionwise: `k ∧ ψ` is the unique form `ω`
with `ι(ω) = ι(k) ∧ ψ`, `ι` the inclusion of the forms with no pole.

It is the pairing along which the vanishing of `c₁^{Hodge}(𝒪_X(-Y))` in
`H¹(X, Ω¹_{X/S}(log Y))` kills `a ∪ c₁^{Hodge}(𝒪_X(-Y))` for a class `a` restricting to zero on
`Y`, in the proof of axiom (A4) for Hodge cohomology (Remark 0FWE).

## Main results

* `Stacks.HodgeWeil.injective_logPolesFormsInclusion_app`: the inclusion of the forms with no
  pole is injective on sections.
* `Stacks.HodgeWeil.exists_logPolesFormsInclusion_eq_logFormsWedge`: `ι(k) ∧ ψ` has no pole.
* `Stacks.HodgeWeil.kernelLogWedge`: the pairing `k ∧ ψ`, and
  `Stacks.HodgeWeil.kernelLogWedge_logPolesFormsInclusion`: `k ∧ ι(η)` is the wedge product of
  forms.

## References

* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV)
* [Stacks Project, Tag 0FUP](https://stacks.math.columbia.edu/tag/0FUP)
* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry AlgebraicGeometry.Scheme.Hom

universe u

namespace Stacks.HodgeWeil

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData}
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

include hI hlog in
/-- **The inclusion of the forms with no pole into the forms with logarithmic poles is injective
on sections**: a form killed by `ι` vanishes near every point, by the local equation being a
nonzerodivisor on the forms (Tag 0FMV). -/
theorem injective_logPolesFormsInclusion_app (n : ℕ) (W : X.Opens) :
    Function.Injective ((logPolesFormsInclusion f I n).val.app (op W)) := by
  rw [injective_iff_map_eq_zero]
  intro ω hω
  refine TopCat.Presheaf.section_ext
    ⟨(relativeDifferentialForms f (n : ℤ)).val.presheaf,
      (relativeDifferentialForms f (n : ℤ)).isSheaf⟩ W ω 0 fun x hx => ?_
  obtain ⟨V, hVW, hxV, hV⟩ := exists_map_eq_zero_of_logPolesFormsInclusion_eq_zero hI hlog ω hω x hx
  have h1 := congrArg (TopCat.Presheaf.germ (relativeDifferentialForms f (n : ℤ)).val.presheaf
    V x hxV) hV
  exact (TopCat.Presheaf.germ_res_apply (relativeDifferentialForms f (n : ℤ)).val.presheaf
    (homOfLE hVW) x hxV ω).symm.trans (h1.trans
      (((TopCat.Presheaf.germ (relativeDifferentialForms f (n : ℤ)).val.presheaf V x
        hxV).hom.map_zero).trans ((TopCat.Presheaf.germ
          (relativeDifferentialForms f (n : ℤ)).val.presheaf W x hx).hom.map_zero).symm))


/-- Restricting the inclusion of the forms with no pole. -/
theorem logPolesFormsInclusion_map {n : ℕ} {W W' : X.Opens} (h : W' ≤ W)
    (ω : Γ(relativeDifferentialForms f (n : ℤ), W)) :
    (logPolesForms f I n).val.map (homOfLE h).op
        ((logPolesFormsInclusion f I n).val.app (op W) ω) =
      (logPolesFormsInclusion f I n).val.app (op W')
        ((relativeDifferentialForms f (n : ℤ)).presheaf.map (homOfLE h).op ω) :=
  (PresheafOfModules.naturality_apply (logPolesFormsInclusion f I n).val (homOfLE h).op ω).symm

/-- The value of `t⁻¹ z` at the basis element is `z`. -/
theorem logEval_logOfCoord_basisLE {U : X.Opens} (e : Stacks.Divisors.IdealTrivialization I U)
    {p : ℕ} {W : X.Opens} (hW : W ≤ U) (z : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hz : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) z = 0) :
    logEval f I (e.logOfCoord hW z hz) (le_refl W) (e.basisLE hW) = z := by
  rw [Stacks.Divisors.IdealTrivialization.logEval_logOfCoord, e.coordLE_basisLE]
  refine (one_smul _ _).trans ?_
  exact ConcreteCategory.congr_hom
    ((relativeDifferentialForms f (p : ℤ)).presheaf.map_id (op W)) z

/-- Restricting `ι(k) ∧ ψ` is wedging the restrictions. -/
private theorem logFormsWedge_logPolesFormsInclusion_map {p : ℕ} {W W' : X.Opens} (h : W' ≤ W)
    (k : Γ(relativeDifferentialForms f (p : ℤ), W)) (ψ : (logPolesForms f I 1).val.obj (op W)) :
    logFormsWedge hI hlog ((logPolesFormsInclusion f I p).val.app (op W')
        ((relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op k))
        ((logPolesForms f I 1).val.map (homOfLE h).op ψ) =
      (logPolesForms f I (p + 1)).val.map (homOfLE h).op
        (logFormsWedge hI hlog ((logPolesFormsInclusion f I p).val.app (op W) k) ψ) :=
  (congrArg (fun z => logFormsWedge hI hlog z ((logPolesForms f I 1).val.map (homOfLE h).op ψ))
    (logPolesFormsInclusion_map h k).symm).trans (logFormsWedge_res hI hlog _ _ h)

/-- A restriction of a form vanishing on `Y` vanishes on `Y`. -/
private theorem formRestriction_map_eq_zero {p : ℕ} {U V : (X.Opens)ᵒᵖ} (g : U ⟶ V)
    {k : (relativeDifferentialForms f (p : ℤ)).val.obj U}
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app U k = 0) :
    (formRestriction I.subschemeι f (p : ℤ)).val.app V
      ((relativeDifferentialForms f (p : ℤ)).val.map g k) = 0 :=
  (PresheafOfModules.naturality_apply (formRestriction I.subschemeι f (p : ℤ)).val g _).trans
    ((congrArg _ hk).trans (map_zero _))

include hI hlog in
/-- **On a chart, `ι(k) ∧ ψ` has no pole**, for a form `k` vanishing on `Y`: with `t` the local
equation, `ι(k) = t · t⁻¹k`, so `ι(k) ∧ ψ = t · (t⁻¹k ∧ ψ)` is `ι` of the value of `t⁻¹k ∧ ψ`
at the basis element. -/
theorem logPolesFormsInclusion_logEval_logFormsWedge_logOfCoord {U : X.Opens}
    (e : Stacks.Divisors.IdealTrivialization I U) {p : ℕ} {W : X.Opens} (hW : W ≤ U)
    (k : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) k = 0)
    (ψ : (logPolesForms f I 1).val.obj (op W)) :
    (logPolesFormsInclusion f I (p + 1)).val.app (op W)
        (logEval f I (logFormsWedge hI hlog (e.logOfCoord hW k hk) ψ) (le_refl W)
          (e.basisLE hW)) =
      logFormsWedge hI hlog ((logPolesFormsInclusion f I p).val.app (op W) k) ψ := by
  rw [← e.equationAt_smul_eq_logPolesFormsInclusion hW,
    ← logFormsWedge_smul_left hI hlog, e.equationAt_smul_eq_logPolesFormsInclusion hW,
    logEval_logOfCoord_basisLE]

include hI hlog in
/-- **`ι(k) ∧ ψ` has no pole**, for a form `k` vanishing on `Y` and a form `ψ` with logarithmic
poles: there is a form `ω` with `ι(ω) = ι(k) ∧ ψ`. The local solutions of the charts glue, being
unique by the injectivity of `ι`. -/
theorem exists_logPolesFormsInclusion_eq_logFormsWedge {p : ℕ} {W : X.Opens}
    (k : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) k = 0)
    (ψ : (logPolesForms f I 1).val.obj (op W)) :
    ∃ ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W),
      (logPolesFormsInclusion f I (p + 1)).val.app (op W) ω =
        logFormsWedge hI hlog ((logPolesFormsInclusion f I p).val.app (op W) k) ψ := by
  let Q : ∀ W' : X.Opens, Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W') → Prop :=
    fun W' s => ∀ h : W' ≤ W, (logPolesFormsInclusion f I (p + 1)).val.app (op W') s =
      logFormsWedge hI hlog ((logPolesFormsInclusion f I p).val.app (op W')
        ((relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op k))
        ((logPolesForms f I 1).val.map (homOfLE h).op ψ)
  have hres : ∀ {W₁ W₂ : X.Opens} (h : W₂ ≤ W₁) (s : Γ(relativeDifferentialForms f
      ((p + 1 : ℕ) : ℤ), W₁)), W₁ ≤ W → Q W₁ s →
      Q W₂ ((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).val.resLE h s) := by
    intro W₁ W₂ h s hW₁ hs h₂
    refine ((logPolesFormsInclusion_map (I := I) h s).symm.trans (congrArg _ (hs hW₁))).trans
      ((logFormsWedge_logPolesFormsInclusion_map hI hlog h _ _).symm.trans ?_)
    rw [forms_map_map, logPolesForms_map_map]
  have huniq : ∀ {W₁ : X.Opens} (s s' : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W₁)),
      W₁ ≤ W → Q W₁ s → Q W₁ s' → s = s' := fun s s' hW₁ hs hs' =>
    injective_logPolesFormsInclusion_app hI hlog (p + 1) _ ((hs hW₁).trans (hs' hW₁).symm)
  have hex : ∀ x ∈ W, ∃ W₁ : X.Opens, W₁ ≤ W ∧ x ∈ W₁ ∧ ∃ s, Q W₁ s := by
    intro x hx
    obtain ⟨U, hxU, ⟨e⟩⟩ := Stacks.Divisors.IdealTrivialization.exists_mem_nonempty hI x
    have hk' := formRestriction_map_eq_zero (homOfLE (inf_le_left (b := U))).op hk
    exact ⟨W ⊓ U, inf_le_left, ⟨hx, hxU⟩, logEval f I (logFormsWedge hI hlog
      (e.logOfCoord inf_le_right _ hk') ((logPolesForms f I 1).val.map
        (homOfLE inf_le_left).op ψ)) (le_refl _) (e.basisLE inf_le_right), fun h =>
      logPolesFormsInclusion_logEval_logFormsWedge_logOfCoord hI hlog e inf_le_right _ hk' _⟩
  obtain ⟨s, hs⟩ := TopCat.Sheaf.exists_of_local
    (relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).isSheaf W Q hres huniq hex
  refine ⟨s, logPolesForms_ext_of_local fun x hx => ?_⟩
  obtain ⟨W₁, hW₁, hx₁, hQ⟩ := hs x hx
  refine ⟨W₁, hW₁, hx₁, ?_⟩
  exact ((logPolesFormsInclusion_map (I := I) hW₁ s).trans (hQ hW₁)).trans
    (logFormsWedge_logPolesFormsInclusion_map hI hlog hW₁ k ψ)


/-- **The wedge product `k ∧ ψ ∈ Ω^{p+1}_{X/S}(W)`** of a form `k` vanishing on `Y` with a form
`ψ` with logarithmic poles: the unique form with `ι(k ∧ ψ) = ι(k) ∧ ψ`. -/
def kernelLogWedgeSection {p : ℕ} {W : X.Opens} (k : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) k = 0)
    (ψ : (logPolesForms f I 1).val.obj (op W)) :
    Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W) :=
  (exists_logPolesFormsInclusion_eq_logFormsWedge hI hlog k hk ψ).choose

/-- The image of `k ∧ ψ` under the inclusion of forms with logarithmic poles is `ι(k) ∧ ψ`. -/
theorem logPolesFormsInclusion_kernelLogWedgeSection {p : ℕ} {W : X.Opens}
    (k : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) k = 0)
    (ψ : (logPolesForms f I 1).val.obj (op W)) :
    (logPolesFormsInclusion f I (p + 1)).val.app (op W) (kernelLogWedgeSection hI hlog k hk ψ) =
      logFormsWedge hI hlog ((logPolesFormsInclusion f I p).val.app (op W) k) ψ :=
  (exists_logPolesFormsInclusion_eq_logFormsWedge hI hlog k hk ψ).choose_spec

/-- `k ∧ ψ` is characterised by `ι(k ∧ ψ) = ι(k) ∧ ψ`. -/
theorem kernelLogWedgeSection_eq {p : ℕ} {W : X.Opens}
    (k : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) k = 0)
    (ψ : (logPolesForms f I 1).val.obj (op W))
    (ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (hω : (logPolesFormsInclusion f I (p + 1)).val.app (op W) ω =
      logFormsWedge hI hlog ((logPolesFormsInclusion f I p).val.app (op W) k) ψ) :
    kernelLogWedgeSection hI hlog k hk ψ = ω :=
  injective_logPolesFormsInclusion_app hI hlog (p + 1) W
    ((logPolesFormsInclusion_kernelLogWedgeSection hI hlog k hk ψ).trans hω.symm)

/-- `k ∧ ψ` depends only on the form `k`. -/
theorem kernelLogWedgeSection_congr {p : ℕ} {W : X.Opens}
    {k k' : Γ(relativeDifferentialForms f (p : ℤ), W)} (e : k = k')
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) k = 0)
    (hk' : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) k' = 0)
    (ψ : (logPolesForms f I 1).val.obj (op W)) :
    kernelLogWedgeSection hI hlog k hk ψ = kernelLogWedgeSection hI hlog k' hk' ψ := by
  subst e
  rfl

/-- **`k ∧ ι(η)` is the wedge product of forms** `k ∧ η`. -/
theorem kernelLogWedgeSection_logPolesFormsInclusion {p : ℕ} {W : X.Opens}
    (k : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) k = 0)
    (η : Γ(relativeDifferentialForms f (1 : ℤ), W)) :
    kernelLogWedgeSection hI hlog k hk ((logPolesFormsInclusion f I 1).val.app (op W) η) =
      formWedge f p 1 W k η :=
  kernelLogWedgeSection_eq hI hlog k hk _ _
    (logFormsWedge_logPolesFormsInclusion hI hlog k η).symm

/-- `k ∧ ψ` is additive in the form `k`: `(k + k') ∧ ψ = k ∧ ψ + k' ∧ ψ`. -/
theorem kernelLogWedgeSection_add_left {p : ℕ} {W : X.Opens}
    (k k' : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) k = 0)
    (hk' : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) k' = 0)
    (hkk : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) (k + k') = 0)
    (ψ : (logPolesForms f I 1).val.obj (op W)) :
    kernelLogWedgeSection hI hlog (k + k') hkk ψ =
      kernelLogWedgeSection hI hlog k hk ψ + kernelLogWedgeSection hI hlog k' hk' ψ := by
  refine kernelLogWedgeSection_eq hI hlog _ _ _ _ ?_
  refine (((logPolesFormsInclusion f I (p + 1)).val.app (op W)).hom.map_add _ _).trans ?_
  rw [logPolesFormsInclusion_kernelLogWedgeSection, logPolesFormsInclusion_kernelLogWedgeSection]
  refine (logFormsWedge_add_left hI hlog _ _ ψ).symm.trans ?_
  exact congrArg (fun z => logFormsWedge hI hlog z ψ)
    (((logPolesFormsInclusion f I p).val.app (op W)).hom.map_add k k').symm

/-- `k ∧ ψ` is additive in the form `ψ`: `k ∧ (ψ + ψ') = k ∧ ψ + k ∧ ψ'`. -/
theorem kernelLogWedgeSection_add_right {p : ℕ} {W : X.Opens}
    (k : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) k = 0)
    (ψ ψ' : (logPolesForms f I 1).val.obj (op W)) :
    kernelLogWedgeSection hI hlog k hk (ψ + ψ') =
      kernelLogWedgeSection hI hlog k hk ψ + kernelLogWedgeSection hI hlog k hk ψ' := by
  refine kernelLogWedgeSection_eq hI hlog _ _ _ _ ?_
  refine (((logPolesFormsInclusion f I (p + 1)).val.app (op W)).hom.map_add _ _).trans ?_
  rw [logPolesFormsInclusion_kernelLogWedgeSection, logPolesFormsInclusion_kernelLogWedgeSection]
  exact (logFormsWedge_add_right hI hlog _ ψ ψ').symm

/-- `k ∧ ψ` is linear in the form `k`: `(r • k) ∧ ψ = r • (k ∧ ψ)`. -/
theorem kernelLogWedgeSection_smul_left {p : ℕ} {W : X.Opens} (r : Γ(X, W))
    (k : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) k = 0)
    (hrk : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) (r • k) = 0)
    (ψ : (logPolesForms f I 1).val.obj (op W)) :
    kernelLogWedgeSection hI hlog (r • k) hrk ψ = r • kernelLogWedgeSection hI hlog k hk ψ := by
  refine kernelLogWedgeSection_eq hI hlog _ _ _ _ ?_
  refine (((logPolesFormsInclusion f I (p + 1)).val.app (op W)).hom.map_smul _ _).trans ?_
  rw [logPolesFormsInclusion_kernelLogWedgeSection]
  refine (logFormsWedge_smul_left hI hlog _ ψ r).symm.trans ?_
  exact congrArg (fun z => logFormsWedge hI hlog z ψ)
    (((logPolesFormsInclusion f I p).val.app (op W)).hom.map_smul r k).symm

/-- `k ∧ ψ` is linear in the form `ψ`: `k ∧ (r • ψ) = r • (k ∧ ψ)`. -/
theorem kernelLogWedgeSection_smul_right {p : ℕ} {W : X.Opens} (r : Γ(X, W))
    (k : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) k = 0)
    (ψ : (logPolesForms f I 1).val.obj (op W)) :
    kernelLogWedgeSection hI hlog k hk
        ((show X.ringCatSheaf.obj.obj (op W) from r) • ψ) =
      r • kernelLogWedgeSection hI hlog k hk ψ := by
  refine kernelLogWedgeSection_eq hI hlog _ _ _ _ ?_
  refine (((logPolesFormsInclusion f I (p + 1)).val.app (op W)).hom.map_smul _ _).trans ?_
  rw [logPolesFormsInclusion_kernelLogWedgeSection]
  exact (logFormsWedge_smul_right hI hlog _ ψ r).symm

/-- `k ∧ ψ` commutes with restriction. -/
theorem kernelLogWedgeSection_map {p : ℕ} {W W' : X.Opens} (h : W' ≤ W)
    (k : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) k = 0)
    (hk' : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W')
      ((relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op k) = 0)
    (ψ : (logPolesForms f I 1).val.obj (op W)) :
    kernelLogWedgeSection hI hlog ((relativeDifferentialForms f (p : ℤ)).presheaf.map
        (homOfLE h).op k) hk' ((logPolesForms f I 1).val.map (homOfLE h).op ψ) =
      (relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE h).op
        (kernelLogWedgeSection hI hlog k hk ψ) := by
  refine kernelLogWedgeSection_eq hI hlog _ _ _ _ ?_
  exact ((logPolesFormsInclusion_map (I := I) h _).symm.trans
    (congrArg _ (logPolesFormsInclusion_kernelLogWedgeSection hI hlog k hk ψ))).trans
    (logFormsWedge_logPolesFormsInclusion_map hI hlog h k ψ).symm


/-! ### The pairing as a morphism of sheaves of `f⁻¹𝒪_S`-modules -/

section Sheaf

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance] AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable (f I)

/-- The sheaf `𝒦^p` of `p`-forms vanishing on `Y`, as a sheaf of `f⁻¹𝒪_S`-modules. -/
abbrev kernelFormsBase (p : ℕ) :
    _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) :=
  (_root_.SheafOfModules.restrictScalars (baseRingHom f)).obj (formRestrictionKernelSheaf f I p)

/-- The inclusion `𝒦^p ⟶ Ω^p_{X/S}`, of sheaves of `f⁻¹𝒪_S`-modules. -/
abbrev kernelFormsBaseInclusion (p : ℕ) :
    kernelFormsBase f I p ⟶ AlgebraicGeometry.SheafOfModules.deRhamTerm (formsAlgebras f) p :=
  (_root_.SheafOfModules.restrictScalars (baseRingHom f)).map (formRestrictionKernel f I p).ι

/-- The inclusion `Ω^p_{X/S} ⟶ Ω^p_{X/S}(log Y)`, of sheaves of `f⁻¹𝒪_S`-modules. -/
abbrev logPolesFormsBaseInclusion (p : ℕ) :
    AlgebraicGeometry.SheafOfModules.deRhamTerm (formsAlgebras f) p ⟶ logPolesFormsBase f I p :=
  (_root_.SheafOfModules.restrictScalars (baseRingHom f)).map (logPolesFormsInclusion f I p)

variable {f I}

/-- A local section of `𝒦^p` vanishes on `Y`. -/
theorem formRestriction_kernelFormsBase {p : ℕ} {W : X.Opens}
    (k : (kernelFormsBase f I p).val.obj (op W)) :
    (formRestriction I.subschemeι f (p : ℤ)).val.app (op W)
      ((formRestrictionKernel f I p).ι.val.app (op W) k) = 0 :=
  (mem_formRestrictionKernel f I p (op W) _).1 k.2

/-- A local section of `𝒦^p`, as an element of the submodule, vanishes on `Y`. -/
theorem formRestriction_formRestrictionKernelSheaf {p : ℕ} {U : (X.Opens)ᵒᵖ}
    (k : (formRestrictionKernelSheaf f I p).val.obj U) :
    (formRestriction I.subschemeι f (p : ℤ)).val.app U
      ((formRestrictionKernel f I p).ι.val.app U k) = 0 :=
  (mem_formRestrictionKernel f I p U _).1 k.2

/-- A sum of forms vanishing on `Y` vanishes on `Y`. -/
theorem formRestriction_add_eq_zero {p : ℕ} {U : (X.Opens)ᵒᵖ}
    {k k' : (relativeDifferentialForms f (p : ℤ)).val.obj U}
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app U k = 0)
    (hk' : (formRestriction I.subschemeι f (p : ℤ)).val.app U k' = 0) :
    (formRestriction I.subschemeι f (p : ℤ)).val.app U (k + k') = 0 := by
  refine (((formRestriction I.subschemeι f (p : ℤ)).val.app U).hom.map_add k k').trans ?_
  rw [hk, hk', add_zero]

/-- A multiple of a form vanishing on `Y` vanishes on `Y`. -/
theorem formRestriction_smul_eq_zero {p : ℕ} {U : (X.Opens)ᵒᵖ} (r : X.ringCatSheaf.obj.obj U)
    {k : (relativeDifferentialForms f (p : ℤ)).val.obj U}
    (hk : (formRestriction I.subschemeι f (p : ℤ)).val.app U k = 0) :
    (formRestriction I.subschemeι f (p : ℤ)).val.app U (r • k) = 0 := by
  refine (((formRestriction I.subschemeι f (p : ℤ)).val.app U).hom.map_smul r k).trans ?_
  rw [hk, smul_zero]

/-- `k ∧ ψ` commutes with the restriction maps of the sheaves, for an arbitrary morphism of
opens. -/
theorem kernelLogWedgeSection_restrict_naturality {p : ℕ} {U V : (X.Opens)ᵒᵖ} (g : U ⟶ V)
    (k : (formRestrictionKernelSheaf f I p).val.obj U) (ψ : (logPolesForms f I 1).val.obj U) :
    (relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).val.map g
        (kernelLogWedgeSection hI hlog (W := U.unop)
          ((formRestrictionKernel f I p).ι.val.app U k)
          (formRestriction_formRestrictionKernelSheaf k) ψ) =
      kernelLogWedgeSection hI hlog (W := V.unop)
        ((formRestrictionKernel f I p).ι.val.app V ((formRestrictionKernelSheaf f I p).val.map g k))
        (formRestriction_formRestrictionKernelSheaf _) ((logPolesForms f I 1).val.map g ψ) := by
  have hk' := formRestriction_map_eq_zero g (formRestriction_formRestrictionKernelSheaf k)
  obtain ⟨U⟩ := U
  obtain ⟨V⟩ := V
  exact (kernelLogWedgeSection_map hI hlog (leOfHom g.unop) _
    (formRestriction_formRestrictionKernelSheaf k) hk' ψ).symm.trans
    (kernelLogWedgeSection_congr hI hlog
      (PresheafOfModules.naturality_apply (formRestrictionKernel f I p).ι.val
        (homOfLE (leOfHom g.unop)).op k) (formRestriction_formRestrictionKernelSheaf _) hk' _).symm

include hI hlog in
/-- **The pairing `𝒦^p × Ω¹_{X/S}(log Y) ⟶ Ω^{p+1}_{X/S}`, `(k, ψ) ↦ k ∧ ψ`**, as an
`𝒪_X`-bilinear map of sheaves. -/
def kernelLogWedgeBilinear (p : ℕ) :
    _root_.SheafOfModules.BilinearMap (formRestrictionKernelSheaf f I p) (logPolesForms f I 1)
      (relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)) where
  app U := AddMonoidHom.mk' (fun k => AddMonoidHom.mk'
    (fun ψ => kernelLogWedgeSection hI hlog (W := U.unop)
      ((formRestrictionKernel f I p).ι.val.app U k)
      (formRestriction_formRestrictionKernelSheaf k) ψ)
    (fun ψ ψ' => kernelLogWedgeSection_add_right hI hlog (W := U.unop)
      ((formRestrictionKernel f I p).ι.val.app U k)
      (formRestriction_formRestrictionKernelSheaf k) ψ ψ')) fun k k' => AddMonoidHom.ext fun ψ =>
      (kernelLogWedgeSection_congr hI hlog
        (((formRestrictionKernel f I p).ι.val.app U).hom.map_add k k')
        (formRestriction_formRestrictionKernelSheaf (k + k'))
        (formRestriction_add_eq_zero (formRestriction_formRestrictionKernelSheaf k)
          (formRestriction_formRestrictionKernelSheaf k')) ψ).trans
      (kernelLogWedgeSection_add_left hI hlog _ _
        (formRestriction_formRestrictionKernelSheaf k)
        (formRestriction_formRestrictionKernelSheaf k') _ ψ)
  map_smul_left U r k ψ :=
    (kernelLogWedgeSection_congr hI hlog
      (((formRestrictionKernel f I p).ι.val.app U).hom.map_smul r k)
      (formRestriction_formRestrictionKernelSheaf (r • k))
      (formRestriction_smul_eq_zero r (formRestriction_formRestrictionKernelSheaf k)) ψ).trans
    (kernelLogWedgeSection_smul_left hI hlog (W := U.unop) r _
      (formRestriction_formRestrictionKernelSheaf k) _ ψ)
  map_smul_right U r k ψ := kernelLogWedgeSection_smul_right hI hlog (W := U.unop) r
    ((formRestrictionKernel f I p).ι.val.app U k) (formRestriction_formRestrictionKernelSheaf k) ψ
  naturality g k ψ := kernelLogWedgeSection_restrict_naturality hI hlog g k ψ

include hI hlog in
/-- **The pairing `𝒦^p ⊗ Ω¹_{X/S}(log Y) ⟶ Ω^{p+1}_{X/S}`, `k ⊗ ψ ↦ k ∧ ψ`**, on the
underlying presheaves of `f⁻¹𝒪_S`-modules. -/
def kernelLogWedgePresheafMap (p : ℕ) :
    PresheafOfModules.tensorObj (O := ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
        S.sheaf).obj) (kernelFormsBase f I p).val (logPolesFormsBase f I 1).val ⟶
      (PresheafOfModules.restrictScalars (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj)).obj
        (AlgebraicGeometry.SheafOfModules.deRhamTerm (formsAlgebras f) (p + 1)).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun k ψ => (kernelLogWedgeBilinear hI hlog p).app U k ψ)
    (fun k k' ψ => by
      exact congrArg (fun φ : _ →+ _ => φ ψ)
        (((kernelLogWedgeBilinear hI hlog p).app U).map_add k k'))
    (fun r k ψ => (kernelLogWedgeBilinear hI hlog p).map_smul_left U (baseFn f r) k ψ)
    (fun k ψ ψ' => ((kernelLogWedgeBilinear hI hlog p).app U k).map_add ψ ψ')
    (fun r k ψ => (kernelLogWedgeBilinear hI hlog p).map_smul_right U (baseFn f r) k ψ)
  naturality {U V} g := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun k ψ => ?_
    exact ((kernelLogWedgeBilinear hI hlog p).naturality g k ψ).symm

include hI hlog in
/-- **The pairing `𝒦^p ⊗_{f⁻¹𝒪_S} Ω¹_{X/S}(log Y) ⟶ Ω^{p+1}_{X/S}`, `k ⊗ ψ ↦ k ∧ ψ`**, a
morphism of sheaves of `f⁻¹𝒪_S`-modules. -/
def kernelLogWedge (p : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj
        (kernelFormsBase f I p)).obj (logPolesFormsBase f I 1) ⟶
      AlgebraicGeometry.SheafOfModules.deRhamTerm (formsAlgebras f) (p + 1) :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj)).symm
    (kernelLogWedgePresheafMap hI hlog p)


/-- The value of `kernelLogWedge` on the class of a local pure tensor is `k ∧ ψ`. -/
theorem kernelLogWedge_val_app_tensorSheafUnit (p : ℕ) (U : (X.Opens)ᵒᵖ)
    (k : (kernelFormsBase f I p).val.obj U) (ψ : (logPolesFormsBase f I 1).val.obj U) :
    (kernelLogWedge hI hlog p).val.app U
        ((PresheafOfModules.tensorSheafUnit (kernelFormsBase f I p)
          (logPolesFormsBase f I 1)).app U (k ⊗ₜ ψ)) =
      kernelLogWedgeSection hI hlog (W := U.unop) ((formRestrictionKernel f I p).ι.val.app U k)
        (formRestriction_formRestrictionKernelSheaf k) ψ := by
  have e := (PresheafOfModules.sheafificationHomEquiv
      (P := PresheafOfModules.tensorObj (kernelFormsBase f I p).val (logPolesFormsBase f I 1).val)
      (F := AlgebraicGeometry.SheafOfModules.deRhamTerm (formsAlgebras f) (p + 1))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj)).apply_symm_apply
      (kernelLogWedgePresheafMap hI hlog p)
  exact (PresheafOfModules.tensorSheafificationHomEquiv_app_apply
    (Osharp := (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)
    (kernelLogWedge hI hlog p) U (k ⊗ₜ ψ)).symm.trans
    (congrArg (fun φ => PresheafOfModules.Hom.app φ U (k ⊗ₜ ψ)) e)

/-- **The pairing extends the wedge product**: on `𝒦^p ⊗ Ω¹_{X/S}`, the wedge product
`Ω^p ⊗ Ω¹ ⟶ Ω^{p+1}` restricted along `𝒦^p ⟶ Ω^p` is `kernelLogWedge` restricted along
`Ω¹_{X/S} ⟶ Ω¹_{X/S}(log Y)`. -/
theorem kernelLogWedge_comp_eq (p : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).map
        (kernelFormsBaseInclusion f I p)).app
        (AlgebraicGeometry.SheafOfModules.deRhamTerm (formsAlgebras f) 1) ≫
      AlgebraicGeometry.SheafOfModules.exteriorProductComponent (formsAlgebras f) p 1 =
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj
        (kernelFormsBase f I p)).map (logPolesFormsBaseInclusion f I 1) ≫
      kernelLogWedge hI hlog p := by
  refine PresheafOfModules.tensorSheaf_hom_ext
    (Osharp := (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)
    (F := kernelFormsBase f I p)
    (G := AlgebraicGeometry.SheafOfModules.deRhamTerm (formsAlgebras f) 1)
    (Q := AlgebraicGeometry.SheafOfModules.deRhamTerm (formsAlgebras f) (p + 1))
    fun U k η => ?_
  refine Eq.trans (congrArg ((AlgebraicGeometry.SheafOfModules.exteriorProductComponent
    (formsAlgebras f) p 1).val.app U)
    (AlgebraicGeometry.SheafOfModules.tensorFunctor_map_unit_apply
      (kernelFormsBaseInclusion f I p) U k η)) ?_
  refine Eq.trans (AlgebraicGeometry.SheafOfModules.exteriorProductComponent_unit_apply
    (formsAlgebras f) p 1 U _ η) ?_
  refine Eq.symm (Eq.trans (congrArg ((kernelLogWedge hI hlog p).val.app U)
    (AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_map_unit_apply
      (logPolesFormsBaseInclusion f I 1) U k η)) ?_)
  refine (kernelLogWedge_val_app_tensorSheafUnit hI hlog p U k _).trans ?_
  exact kernelLogWedgeSection_logPolesFormsInclusion hI hlog _ _ η

end Sheaf

end Stacks.HodgeWeil

end
