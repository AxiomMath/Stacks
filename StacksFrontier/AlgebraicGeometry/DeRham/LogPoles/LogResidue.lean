module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartLift

/-!
# The residue of a form with logarithmic poles

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor, cut out by
`I`, for which the de Rham complex of log poles is defined ([Stacks, Tag 0FMV]). This file
constructs the residue `Res : Ω^{p+1}_{X/S}(log Y) ⟶ i_*Ω^p_{Y/S}` of [Stacks, Tag 0FMW].

On an open where the ideal sheaf is trivialized, with basis element `b` and local equation `t`, a
form `φ` with logarithmic poles has `φ(b) = t α + dt ∧ β` locally, i.e. `φ = α + dlog t ∧ β`, and
its residue is `β|_Y` (`AlgebraicGeometry.Scheme.Hom.IsResidueDecomp`). This does not depend on
the decomposition nor on the trivialization
(`Stacks.Divisors.IdealTrivialization.formRes_eq_of_isResidueDecomp`), by the second condition of
Tag 0FMV, and so glues.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Divisors.IdealTrivialization

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : IdealTrivialization I U)

/-- The coordinate of `r • a` with respect to the basis element over `W ≤ U` is `r` times the
coordinate of `a`. -/
theorem coordLE_smul {W : X.Opens} (h : W ≤ U) (r : Γ(X, W))
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op W)) :
    e.coordLE h (toIdealScalar r • a) = r * e.coordLE h a :=
  map_smul _ r a

/-- **A residue decomposition** of a form `φ` with logarithmic poles over an open `V ≤ U`:
`φ(b) = t α + dt ∧ β` for the basis element `b` and the local equation `t`, i.e.
`φ = α + dlog t ∧ β` on `V`. -/
def IsResidueDecomp {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I (p + 1)).val.obj (op W))
    {V : X.Opens} (hVW : V ≤ W) (hVU : V ≤ U)
    (α : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) : Prop :=
  logEval f I φ hVW (e.basisLE hVU) = e.equationAt hVU • α + exactWedge f p V (e.equationAt hVU) β

/-- Residue decompositions restrict to smaller opens. -/
theorem IsResidueDecomp.res {p : ℕ} {W : X.Opens} {φ : (logPolesForms f I (p + 1)).val.obj (op W)}
    {V : X.Opens} {hVW : V ≤ W} {hVU : V ≤ U}
    {α : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V)}
    {β : Γ(relativeDifferentialForms f (p : ℤ), V)} (hd : e.IsResidueDecomp φ hVW hVU α β)
    {V' : X.Opens} (h : V' ≤ V) :
    e.IsResidueDecomp φ (h.trans hVW) (h.trans hVU)
      ((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE h).op α)
      ((relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op β) := by
  unfold IsResidueDecomp at hd ⊢
  rw [e.logEval_basisLE_res φ hVW hVU h, hd, map_add, forms_map_smul, exactWedge_res,
    e.equationAt_res hVU h]

/-- Residue decompositions exist near every point. -/
theorem exists_isResidueDecomp {p : ℕ} {W : X.Opens}
    (φ : (logPolesForms f I (p + 1)).val.obj (op W)) {W' : X.Opens} (hW'W : W' ≤ W)
    (hW'U : W' ≤ U) (x : X) (hx : x ∈ W') :
    ∃ (V : X.Opens) (hV : V ≤ W'), x ∈ V ∧ ∃ α β,
      e.IsResidueDecomp φ (hV.trans hW'W) (hV.trans hW'U) α β := by
  obtain ⟨V, hV, hxV, α, β, hαβ⟩ := e.exists_local_eq_smul_add_exactWedge hW'U p
    (logEval f I φ hW'W (e.basisLE hW'U)) (formRestriction_logEval φ _ _) x hx
  refine ⟨V, hV, hxV, α, β, ?_⟩
  unfold IsResidueDecomp
  rw [e.logEval_basisLE_res φ hW'W hW'U hV]
  exact hαβ

/-- **The residue does not depend on the decomposition nor on the trivialization.** -/
theorem formRes_eq_of_isResidueDecomp (hlog : f.HasLogPolesDeRhamComplex I) {U' : X.Opens}
    (e' : IdealTrivialization I U') {p : ℕ} {W : X.Opens}
    {φ : (logPolesForms f I (p + 1)).val.obj (op W)} {V : X.Opens} {hVW : V ≤ W} {hVU : V ≤ U}
    {hVU' : V ≤ U'} {α α' : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V)}
    {β β' : Γ(relativeDifferentialForms f (p : ℤ), V)} (hd : e.IsResidueDecomp φ hVW hVU α β)
    (hd' : e'.IsResidueDecomp φ hVW hVU' α' β') :
    formRes I.subschemeι (p : ℤ) V β = formRes I.subschemeι (p : ℤ) V β' := by
  set t := e.equationAt hVU
  set c := e.coordLE hVU (e'.basisLE hVU')
  set c' := e'.coordLE hVU' (e.basisLE hVU)
  have hcc : c' * c = 1 := by
    have h1 := congrArg (e.coordLE hVU) (e'.eq_coord_smul_basisLE hVU' (e.basisLE hVU))
    rw [e.coordLE_basisLE, e.coordLE_smul] at h1
    exact h1.symm
  have ht' : e'.equationAt hVU' = c * t := by
    have := e.idealFn_eq_mul hVU (e'.basisLE hVU')
    exact this
  have hκ' : logEval f I φ hVW (e'.basisLE hVU') = c • logEval f I φ hVW (e.basisLE hVU) :=
    e.logEval_eq_coord_smul φ hVW hVU _
  unfold IsResidueDecomp at hd hd'
  rw [hκ', hd, ht', exactWedge_mul_left] at hd'
  have hrel : t • (α - α' - c' • exactWedge f p V c β') +
      exactWedge f p V t (β - β') = 0 := by
    have h2 := congrArg (fun z => c' • z) hd'
    simp only [smul_add, smul_smul] at h2
    rw [exactWedge_sub_right]
    have hc1 : c' * (c * t) = t := by rw [← mul_assoc, hcc, one_mul]
    have hc2 : c' * c = 1 := hcc
    rw [hc1, hc2, one_smul, one_smul] at h2
    linear_combination (norm := module) h2
  exact sub_eq_zero.mp (((formRes_sub _ _ _ _ _).symm).trans
    (e.formRestriction_eq_zero_of_smul_add_exactWedge_eq_zero hlog hVU p _ _ hrel))

end Stacks.Divisors.IdealTrivialization

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData}

variable (f I) in
/-- The direct image `i_*Ω^p_{Y/S}` of the relative `p`-forms of the divisor. -/
abbrev divisorForms (p : ℕ) : X.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj
    (relativeDifferentialForms (I.subschemeι ≫ f) (p : ℤ))

/-- Restricting a section of `i_*Ω^p_{Y/S}` from `V` to `V'` and then to `V''` is restricting it
from `V` to `V''`. -/
theorem divisorForms_map_map {p : ℕ} {V V' V'' : X.Opens} (h : V' ≤ V) (h' : V'' ≤ V')
    (ρ : Γ(divisorForms f I p, V)) :
    (divisorForms f I p).presheaf.map (homOfLE h').op
        ((divisorForms f I p).presheaf.map (homOfLE h).op ρ) =
      (divisorForms f I p).presheaf.map (homOfLE (h'.trans h)).op ρ := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- **`ρ` is the residue of `φ` over `V`**: for every trivialization of the ideal sheaf and every
residue decomposition `φ = α + dlog t ∧ β` over an open inside `V`, `ρ` restricts to `β|_Y`. -/
def IsResidueOf {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I (p + 1)).val.obj (op W))
    (V : X.Opens) (ρ : Γ(divisorForms f I p, V)) : Prop :=
  ∃ hVW : V ≤ W, ∀ (U' : X.Opens) (e' : Stacks.Divisors.IdealTrivialization I U') (V' : X.Opens)
    (h : V' ≤ V) (hU : V' ≤ U') (α : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V'))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V')),
    e'.IsResidueDecomp φ (h.trans hVW) hU α β →
      (divisorForms f I p).presheaf.map (homOfLE h).op ρ = formRes I.subschemeι (p : ℤ) V' β

/-- If `ρ` is the residue of `φ` over `V`, then its restriction to `V₂ ≤ V` is the residue of `φ`
over `V₂`. -/
theorem IsResidueOf.res {p : ℕ} {W : X.Opens} {φ : (logPolesForms f I (p + 1)).val.obj (op W)}
    {V : X.Opens} {ρ : Γ(divisorForms f I p, V)} (hρ : IsResidueOf φ V ρ) {V₂ : X.Opens}
    (h₂ : V₂ ≤ V) : IsResidueOf φ V₂ ((divisorForms f I p).presheaf.map (homOfLE h₂).op ρ) := by
  obtain ⟨hVW, hρ⟩ := hρ
  refine ⟨h₂.trans hVW, fun U' e' V' h hU α β hd => ?_⟩
  rw [divisorForms_map_map]
  exact hρ U' e' V' (h.trans h₂) hU α β hd

/-- For an effective Cartier divisor, the residue of `φ` over `V` is unique. -/
theorem IsResidueOf.unique (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) {p : ℕ}
    {W : X.Opens} {φ : (logPolesForms f I (p + 1)).val.obj (op W)} {V : X.Opens}
    {ρ ρ' : Γ(divisorForms f I p, V)} (hρ : IsResidueOf φ V ρ) (hρ' : IsResidueOf φ V ρ') :
    ρ = ρ' := by
  obtain ⟨hVW, hρ⟩ := hρ
  obtain ⟨_, hρ'⟩ := hρ'
  refine TopCat.Presheaf.IsSheaf.section_ext (Scheme.Modules.isSheaf _) fun x hx => ?_
  obtain ⟨Ux, hxU, ⟨e⟩⟩ := Stacks.Divisors.IdealTrivialization.exists_mem_nonempty hI x
  obtain ⟨V', hV', hxV', α, β, hd⟩ :=
    e.exists_isResidueDecomp φ (inf_le_left.trans hVW) (inf_le_right : V ⊓ Ux ≤ Ux) x ⟨hx, hxU⟩
  refine ⟨V', hV'.trans inf_le_left, hxV', ?_⟩
  exact (hρ Ux e V' (hV'.trans inf_le_left) _ α β hd).trans
    (hρ' Ux e V' (hV'.trans inf_le_left) _ α β hd).symm

/-- The residue property is local. -/
theorem IsResidueOf.of_local {p : ℕ} {W : X.Opens}
    {φ : (logPolesForms f I (p + 1)).val.obj (op W)} {V : X.Opens} (hVW : V ≤ W)
    {ρ : Γ(divisorForms f I p, V)}
    (hloc : ∀ x ∈ V, ∃ (V₁ : X.Opens) (h₁ : V₁ ≤ V), x ∈ V₁ ∧
      IsResidueOf φ V₁ ((divisorForms f I p).presheaf.map (homOfLE h₁).op ρ)) :
    IsResidueOf φ V ρ := by
  refine ⟨hVW, fun U' e' V' h hU α β hd => ?_⟩
  refine TopCat.Presheaf.IsSheaf.section_ext (Scheme.Modules.isSheaf _) fun x hx => ?_
  obtain ⟨V₁, h₁, hx₁, _, hρ₁⟩ := hloc x (h hx)
  refine ⟨V' ⊓ V₁, inf_le_left, ⟨hx, hx₁⟩, ?_⟩
  rw [divisorForms_map_map, ← formRes_map]
  have key := hρ₁ U' e' (V' ⊓ V₁) inf_le_right (inf_le_left.trans hU) _ _
    (Stacks.Divisors.IdealTrivialization.IsResidueDecomp.res e' hd inf_le_left)
  rw [divisorForms_map_map] at key
  exact key

/-- Near every point of `W`, a form with logarithmic poles has a residue decomposition for some
trivialization of the ideal sheaf. -/
private theorem exists_isResidueDecomp_near (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I (p + 1)).val.obj (op W)) (x : X) (hx : x ∈ W) :
    ∃ (U : X.Opens) (e : Stacks.Divisors.IdealTrivialization I U) (V : X.Opens) (hVW : V ≤ W)
      (hVU : V ≤ U) (α : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V))
      (β : Γ(relativeDifferentialForms f (p : ℤ), V)), x ∈ V ∧ e.IsResidueDecomp φ hVW hVU α β := by
  obtain ⟨Ux, hxU, ⟨e⟩⟩ := Stacks.Divisors.IdealTrivialization.exists_mem_nonempty hI x
  obtain ⟨V, hV, hxV, α, β, hd⟩ := e.exists_isResidueDecomp φ (inf_le_left : W ⊓ Ux ≤ W)
    (inf_le_right : W ⊓ Ux ≤ Ux) x ⟨hx, hxU⟩
  exact ⟨Ux, e, V, hV.trans inf_le_left, hV.trans inf_le_right, α, β, hxV, hd⟩

/-- Restricting the residue candidate `β|_Y` of one residue decomposition agrees with `β'|_Y` for
any other residue decomposition on a smaller open. -/
private theorem map_formRes_eq_of_isResidueDecomp (hlog : f.HasLogPolesDeRhamComplex I)
    {U : X.Opens} (e : Stacks.Divisors.IdealTrivialization I U) {p : ℕ} {W : X.Opens}
    {φ : (logPolesForms f I (p + 1)).val.obj (op W)} {V : X.Opens} {hVW : V ≤ W} {hVU : V ≤ U}
    {α : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V)}
    {β : Γ(relativeDifferentialForms f (p : ℤ), V)} (hd : e.IsResidueDecomp φ hVW hVU α β)
    {U' : X.Opens} (e' : Stacks.Divisors.IdealTrivialization I U') {V' : X.Opens} (h : V' ≤ V)
    (hU : V' ≤ U') (α' : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V'))
    (β' : Γ(relativeDifferentialForms f (p : ℤ), V'))
    (hd' : e'.IsResidueDecomp φ (h.trans hVW) hU α' β') :
    (divisorForms f I p).presheaf.map (homOfLE h).op (formRes I.subschemeι (p : ℤ) V β) =
      formRes I.subschemeι (p : ℤ) V' β' := by
  rw [← formRes_map]
  exact Stacks.Divisors.IdealTrivialization.formRes_eq_of_isResidueDecomp e hlog e'
    (Stacks.Divisors.IdealTrivialization.IsResidueDecomp.res e hd h) hd'

/-- **The residue exists**. -/
theorem exists_isResidueOf (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hlog : f.HasLogPolesDeRhamComplex I) {p : ℕ} {W : X.Opens}
    (φ : (logPolesForms f I (p + 1)).val.obj (op W)) :
    ∃ ρ : Γ(divisorForms f I p, W), IsResidueOf φ W ρ := by
  obtain ⟨ρ, hρ⟩ := TopCat.Sheaf.exists_of_local (N := (divisorForms f I p).val)
    (divisorForms f I p).isSheaf W (fun V ρ => IsResidueOf φ V ρ)
    (fun {V₁ V₂} h ρ _ hρ => by
      rw [PresheafOfModules.resLE_apply]
      exact hρ.res h)
    (fun {V} ρ ρ' _ hρ hρ' => IsResidueOf.unique hI hρ hρ')
    (fun x hx => by
      obtain ⟨Ux, e, V, hVW, hVU, α, β, hxV, hd⟩ := exists_isResidueDecomp_near hI φ x hx
      exact ⟨V, hVW, hxV, formRes I.subschemeι (p : ℤ) V β, hVW,
        fun _ e' _ h hU α' β' hd' =>
          map_formRes_eq_of_isResidueDecomp hlog e hd e' h hU α' β' hd'⟩)
  refine ⟨ρ, IsResidueOf.of_local le_rfl fun x hx => ?_⟩
  obtain ⟨V, hV, hxV, hρV⟩ := hρ x hx
  rw [PresheafOfModules.resLE_apply] at hρV
  exact ⟨V, hV, hxV, hρV⟩

/-- A single residue decomposition computes the residue. -/
theorem isResidueOf_of_isResidueDecomp (hlog : f.HasLogPolesDeRhamComplex I) {U : X.Opens}
    (e : Stacks.Divisors.IdealTrivialization I U) {p : ℕ} {W : X.Opens}
    {φ : (logPolesForms f I (p + 1)).val.obj (op W)} {V : X.Opens} {hVW : V ≤ W} {hVU : V ≤ U}
    {α : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V)}
    {β : Γ(relativeDifferentialForms f (p : ℤ), V)} (hd : e.IsResidueDecomp φ hVW hVU α β) :
    IsResidueOf φ V (formRes I.subschemeι (p : ℤ) V β) :=
  ⟨hVW, fun _ e' _ h hU α' β' hd' =>
    map_formRes_eq_of_isResidueDecomp hlog e hd e' h hU α' β' hd'⟩

variable (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- **The residue of a form with logarithmic poles.** -/
def logRes {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I (p + 1)).val.obj (op W)) :
    Γ(divisorForms f I p, W) :=
  (exists_isResidueOf hI hlog φ).choose

/-- `logRes hI hlog φ` is the residue of `φ` over `W`. -/
theorem isResidueOf_logRes {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I (p + 1)).val.obj (op W)) :
    IsResidueOf φ W (logRes hI hlog φ) :=
  (exists_isResidueOf hI hlog φ).choose_spec

/-- Any residue `ρ` of `φ` over `W` is `logRes hI hlog φ`. -/
theorem logRes_eq {p : ℕ} {W : X.Opens} {φ : (logPolesForms f I (p + 1)).val.obj (op W)}
    {ρ : Γ(divisorForms f I p, W)} (hρ : IsResidueOf φ W ρ) : logRes hI hlog φ = ρ :=
  IsResidueOf.unique hI (isResidueOf_logRes hI hlog φ) hρ

/-- The residue, computed by a residue decomposition. -/
theorem logRes_map_eq {U : X.Opens} (e : Stacks.Divisors.IdealTrivialization I U) {p : ℕ}
    {W : X.Opens} (φ : (logPolesForms f I (p + 1)).val.obj (op W)) {V : X.Opens} (hVW : V ≤ W)
    (hVU : V ≤ U) {α : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V)}
    {β : Γ(relativeDifferentialForms f (p : ℤ), V)} (hd : e.IsResidueDecomp φ hVW hVU α β) :
    (divisorForms f I p).presheaf.map (homOfLE hVW).op (logRes hI hlog φ) =
      formRes I.subschemeι (p : ℤ) V β :=
  IsResidueOf.unique hI ((isResidueOf_logRes hI hlog φ).res hVW)
    (isResidueOf_of_isResidueDecomp hlog e hd)

/-- The residue is computed locally by residue decompositions; a section of `i_*Ω^p_{Y/S}`
agreeing with `β|_Y` on a neighbourhood of every point, for some decomposition there, is the
residue. -/
theorem logRes_eq_of_local {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I (p + 1)).val.obj (op W))
    (ρ : Γ(divisorForms f I p, W))
    (hloc : ∀ x ∈ W, ∃ (U : X.Opens) (e : Stacks.Divisors.IdealTrivialization I U) (V : X.Opens)
      (hVW : V ≤ W) (hVU : V ≤ U) (α : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V))
      (β : Γ(relativeDifferentialForms f (p : ℤ), V)), x ∈ V ∧
        e.IsResidueDecomp φ hVW hVU α β ∧
        (divisorForms f I p).presheaf.map (homOfLE hVW).op ρ = formRes I.subschemeι (p : ℤ) V β) :
    logRes hI hlog φ = ρ :=
  logRes_eq hI hlog (IsResidueOf.of_local le_rfl fun x hx => by
    obtain ⟨U, e, V, hVW, hVU, α, β, hxV, hd, hρ⟩ := hloc x hx
    exact ⟨V, hVW, hxV, hρ ▸ isResidueOf_of_isResidueDecomp hlog e hd⟩)

/-- The residue is additive. -/
theorem logRes_add {p : ℕ} {W : X.Opens} (φ φ' : (logPolesForms f I (p + 1)).val.obj (op W)) :
    logRes hI hlog (φ + φ') = logRes hI hlog φ + logRes hI hlog φ' := by
  refine logRes_eq_of_local hI hlog _ _ fun x hx => ?_
  obtain ⟨Ux, e, V, hVW, hVU, α, β, hxV, hd⟩ := exists_isResidueDecomp_near hI φ x hx
  obtain ⟨V', hV', hxV', α', β', hd'⟩ := e.exists_isResidueDecomp φ' hVW hVU x hxV
  have hd₁ := Stacks.Divisors.IdealTrivialization.IsResidueDecomp.res e hd hV'
  refine ⟨Ux, e, V', hV'.trans hVW, hV'.trans hVU,
    (relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hV').op α + α',
    (relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE hV').op β + β', hxV', ?_, ?_⟩
  · unfold Stacks.Divisors.IdealTrivialization.IsResidueDecomp at hd₁ hd' ⊢
    rw [logEval_add, hd₁, hd', exactWedge_add_right, smul_add]
    abel
  · rw [map_add, logRes_map_eq hI hlog e φ _ _ hd₁, logRes_map_eq hI hlog e φ' _ _ hd',
      formRes_add]
    rfl

/-- The residue commutes with restriction to smaller opens. -/
theorem logRes_res {p : ℕ} {W W₁ : X.Opens} (h₁ : W₁ ≤ W)
    (φ : (logPolesForms f I (p + 1)).val.obj (op W)) :
    logRes hI hlog ((logPolesForms f I (p + 1)).val.map (homOfLE h₁).op φ) =
      (divisorForms f I p).presheaf.map (homOfLE h₁).op (logRes hI hlog φ) :=
  logRes_eq hI hlog
    (by
      obtain ⟨_, hρ⟩ := (isResidueOf_logRes hI hlog φ).res h₁
      exact ⟨le_rfl, fun U' e' V' h hU α β hd => hρ U' e' V' h hU α β hd⟩)

/-- **The residue vanishes on forms with no pole.** -/
theorem logRes_logPolesFormsInclusion {p : ℕ} {W : X.Opens}
    (ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W)) :
    logRes hI hlog ((logPolesFormsInclusion f I (p + 1)).val.app (op W) ω) = 0 := by
  refine logRes_eq_of_local hI hlog _ _ fun x hx => ?_
  obtain ⟨Ux, hxU, ⟨e⟩⟩ := Stacks.Divisors.IdealTrivialization.exists_mem_nonempty hI x
  refine ⟨Ux, e, W ⊓ Ux, inf_le_left, inf_le_right,
    (relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE inf_le_left).op ω, 0,
    ⟨hx, hxU⟩, ?_, ?_⟩
  · unfold Stacks.Divisors.IdealTrivialization.IsResidueDecomp
    rw [logEval_logPolesFormsInclusion, exactWedge_zero_right, add_zero]
    rfl
  · rw [map_zero, formRes_zero]
    rfl

/-- The residue is `𝒪_X`-linear. -/
theorem logRes_smul {p : ℕ} {W : X.Opens} (r : Γ(X, W))
    (φ : (logPolesForms f I (p + 1)).val.obj (op W)) :
    logRes hI hlog ((show X.ringCatSheaf.obj.obj (op W) from r) • φ) = r • logRes hI hlog φ := by
  refine logRes_eq_of_local hI hlog _ _ fun x hx => ?_
  obtain ⟨Ux, e, V, hVW, hVU, α, β, hxV, hd⟩ := exists_isResidueDecomp_near hI φ x hx
  refine ⟨Ux, e, V, hVW, hVU, X.presheaf.map (homOfLE hVW).op r • α,
    X.presheaf.map (homOfLE hVW).op r • β, hxV, ?_, ?_⟩
  · unfold Stacks.Divisors.IdealTrivialization.IsResidueDecomp at hd ⊢
    rw [logEval_smul_left, hd, exactWedge_smul_right, smul_add, smul_comm]
  · rw [Scheme.Modules.map_smul, logRes_map_eq hI hlog e φ _ _ hd, formRes_smul]
    rfl

/-- The de Rham differential of the divisor commutes with restriction of sections of
`i_*Ω^•_{Y/S}`. -/
theorem divisorForms_map_deRhamD {p : ℕ} {W V : X.Opens} (h : V ≤ W)
    (ρ : Γ(divisorForms f I p, W)) :
    (divisorForms f I (p + 1)).presheaf.map (homOfLE h).op
        (deRhamD (I.subschemeι ≫ f) p (I.subschemeι ⁻¹ᵁ W) ρ) =
      deRhamD (I.subschemeι ≫ f) p (I.subschemeι ⁻¹ᵁ V)
        ((divisorForms f I p).presheaf.map (homOfLE h).op ρ) := by
  rw [Scheme.Modules.pushforward_obj_presheaf_map, Scheme.Modules.pushforward_obj_presheaf_map]
  exact deRhamD_res (f := I.subschemeι ≫ f) p
    (show I.subschemeι ⁻¹ᵁ V ≤ I.subschemeι ⁻¹ᵁ W from fun _ hx => h hx) ρ

/-- **The residue anticommutes with the differentials**: `Res(dφ) = - d(Res φ)`. This is the
sign of the shifted complex `Ω^•_{Y/S}[-1]`. -/
theorem logRes_logD {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I (p + 1)).val.obj (op W)) :
    logRes hI hlog (logD hI hlog φ) =
      -deRhamD (I.subschemeι ≫ f) p (I.subschemeι ⁻¹ᵁ W) (logRes hI hlog φ) := by
  refine logRes_eq_of_local hI hlog _ _ fun x hx => ?_
  obtain ⟨Ux, e, V, hVW, hVU, α, β, hxV, hd⟩ := exists_isResidueDecomp_near hI φ x hx
  set t := e.equationAt hVU
  have hc : e.IsChartDecomp hVU (logEval f I φ hVW (e.basisLE hVU)) α (exactWedge f p V t β) :=
    ⟨hd, exactWedge_exactWedge_self _ _ _ _, by
      rw [deRhamD_exactWedge, exactWedge_neg_right, exactWedge_exactWedge_self, neg_zero], by
      rw [deRhamD_exactWedge, formRes_neg]
      exact (congrArg Neg.neg (formRes_exactWedge_idealFn (e.basisLE hVU) _)).trans neg_zero⟩
  refine ⟨Ux, e, V, hVW, hVU, deRhamD f (p + 1) V α, -deRhamD f p V β, hxV, ?_, ?_⟩
  · unfold Stacks.Divisors.IdealTrivialization.IsResidueDecomp
    refine (logEval_res hVW (logD hI hlog φ) (le_refl V) (e.basisLE hVU)).symm.trans ?_
    rw [← logD_res, e.logD_map_eq_logOfCoord hI hlog φ hVW hVU hc,
      e.logEval_logOfCoord_basisLE, deRhamD_exactWedge, exactWedge_neg_right]
  · refine (map_neg _ _).trans ?_
    rw [divisorForms_map_deRhamD, logRes_map_eq hI hlog e φ _ _ hd, formRes_neg]
    exact congrArg Neg.neg (formRestriction_deRhamD I.subschemeι p V β).symm

/-- **A form with logarithmic poles whose value at the basis element is `t ω` is `ω`.** -/
theorem map_eq_logPolesFormsInclusion {U : X.Opens} (e : Stacks.Divisors.IdealTrivialization I U)
    {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I p).val.obj (op W)) {V : X.Opens} (hVW : V ≤ W)
    (hVU : V ≤ U) (ω : Γ(relativeDifferentialForms f (p : ℤ), V))
    (hω : logEval f I φ hVW (e.basisLE hVU) = e.equationAt hVU • ω) :
    (logPolesForms f I p).val.map (homOfLE hVW).op φ =
      (logPolesFormsInclusion f I p).val.app (op V) ω := by
  refine logEval_ext fun V' h a => ?_
  rw [logEval_res, logEval_logPolesFormsInclusion, e.logEval_eq_coord_smul φ _ (h.trans hVU),
    e.logEval_basisLE_res φ hVW hVU h, hω, forms_map_smul, e.equationAt_res hVU h,
    e.idealFn_eq_mul (h.trans hVU) a, smul_smul]

/-- **In degree zero every form with logarithmic poles is locally a function.** -/
theorem exists_map_eq_logPolesFormsInclusion_zero
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) {W : X.Opens}
    (φ : (logPolesForms f I 0).val.obj (op W)) (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (hVW : V ≤ W), x ∈ V ∧ ∃ ω : Γ(relativeDifferentialForms f ((0 : ℕ) : ℤ), V),
      (logPolesForms f I 0).val.map (homOfLE hVW).op φ =
        (logPolesFormsInclusion f I 0).val.app (op V) ω := by
  obtain ⟨Ux, hxU, ⟨e⟩⟩ := Stacks.Divisors.IdealTrivialization.exists_mem_nonempty hI x
  obtain ⟨V, hV, hxV, α, hα⟩ := e.exists_local_eq_smul (inf_le_right : W ⊓ Ux ≤ Ux)
    (logEval f I φ (inf_le_left : W ⊓ Ux ≤ W) (e.basisLE inf_le_right))
    (formRestriction_logEval φ _ _) x ⟨hx, hxU⟩
  refine ⟨V, hV.trans inf_le_left, hxV, α, map_eq_logPolesFormsInclusion e φ _
    (hV.trans inf_le_right) α ?_⟩
  rw [e.logEval_basisLE_res φ inf_le_left inf_le_right hV]
  exact hα

/-- **The residue of the differential of a form of degree `0` vanishes.** -/
theorem logRes_logD_zero {W : X.Opens} (φ : (logPolesForms f I 0).val.obj (op W)) :
    logRes hI hlog (logD hI hlog φ) = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext (Scheme.Modules.isSheaf _) fun x hx => ?_
  obtain ⟨V, hVW, hxV, ω, hω⟩ := exists_map_eq_logPolesFormsInclusion_zero hI φ x hx
  refine ⟨V, hVW, hxV, ?_⟩
  rw [← logRes_res, ← logD_res, hω, logD_logPolesFormsInclusion, logRes_logPolesFormsInclusion,
    map_zero]

/-! ### The local exactness of the residue sequence -/

include hI hlog in
/-- **The inclusion of forms with no pole is injective**, locally: a form `ω` with `ι ω = 0`
vanishes near every point. -/
theorem exists_map_eq_zero_of_logPolesFormsInclusion_eq_zero {p : ℕ} {W : X.Opens}
    (ω : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hω : (logPolesFormsInclusion f I p).val.app (op W) ω = 0) (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (hVW : V ≤ W), x ∈ V ∧
      (relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE hVW).op ω = 0 := by
  obtain ⟨Ux, hxU, ⟨e⟩⟩ := Stacks.Divisors.IdealTrivialization.exists_mem_nonempty hI x
  refine ⟨W ⊓ Ux, inf_le_left, ⟨hx, hxU⟩, ?_⟩
  have h := logEval_logPolesFormsInclusion (I := I) ω (inf_le_left : W ⊓ Ux ≤ W)
    (e.basisLE inf_le_right)
  rw [hω, logEval_zero] at h
  exact e.eq_zero_of_equationAt_smul_eq_zero hlog inf_le_right p _ h.symm

/-- **Exactness in the middle**, locally: a form with logarithmic poles and residue zero has no
pole. -/
theorem exists_map_eq_logPolesFormsInclusion_of_logRes_eq_zero {p : ℕ} {W : X.Opens}
    (φ : (logPolesForms f I (p + 1)).val.obj (op W)) (hφ : logRes hI hlog φ = 0) (x : X)
    (hx : x ∈ W) :
    ∃ (V : X.Opens) (hVW : V ≤ W), x ∈ V ∧
      ∃ ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V),
        (logPolesForms f I (p + 1)).val.map (homOfLE hVW).op φ =
          (logPolesFormsInclusion f I (p + 1)).val.app (op V) ω := by
  obtain ⟨Ux, e, V, hVW, hVU, α, β, hxV, hd⟩ := exists_isResidueDecomp_near hI φ x hx
  have hβ : formRes I.subschemeι (p : ℤ) V β = 0 := by
    rw [← logRes_map_eq hI hlog e φ _ _ hd, hφ]
    exact map_zero _
  obtain ⟨V', hV', hxV', β₁, ε, hc⟩ := e.exists_isChartDecomp hVU β hβ x hxV
  have hd' := Stacks.Divisors.IdealTrivialization.IsResidueDecomp.res e hd hV'
  refine ⟨V', hV'.trans hVW, hxV',
    (relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hV').op α +
      exactWedge f p V' (e.equationAt (hV'.trans hVU)) β₁, ?_⟩
  refine map_eq_logPolesFormsInclusion e φ _ (hV'.trans hVU) _ ?_
  unfold Stacks.Divisors.IdealTrivialization.IsResidueDecomp at hd'
  rw [hd', hc.1, exactWedge_add_right, exactWedge_smul_right, hc.2.1, add_zero, smul_add]

/-- **The residue is surjective**, locally: every local section of `i_*Ω^p_{Y/S}` is near every
point the residue of a form `dlog t ∧ β`. -/
theorem exists_logRes_eq {p : ℕ} {W : X.Opens} (ρ : Γ(divisorForms f I p, W)) (x : X)
    (hx : x ∈ W) :
    ∃ (V : X.Opens) (hVW : V ≤ W), x ∈ V ∧ ∃ φ : (logPolesForms f I (p + 1)).val.obj (op V),
      logRes hI hlog φ = (divisorForms f I p).presheaf.map (homOfLE hVW).op ρ := by
  obtain ⟨V₀, hV₀, hxV₀, β, hβ⟩ :=
    Stacks.Gysin.exists_subschemeFormPullback_restrict I.subschemeι f p W ρ x hx
  obtain ⟨Ux, hxU, ⟨e⟩⟩ := Stacks.Divisors.IdealTrivialization.exists_mem_nonempty hI x
  have hVU : V₀ ⊓ Ux ≤ Ux := inf_le_right
  set β' := (relativeDifferentialForms f (p : ℤ)).presheaf.map
    (homOfLE (inf_le_left : V₀ ⊓ Ux ≤ V₀)).op β
  have hz : formRes I.subschemeι ((p + 1 : ℕ) : ℤ) (V₀ ⊓ Ux)
      (exactWedge f p (V₀ ⊓ Ux) (e.equationAt hVU) β') = 0 :=
    formRes_exactWedge_idealFn (e.basisLE hVU) β'
  refine ⟨V₀ ⊓ Ux, inf_le_left.trans hV₀, ⟨hxV₀, hxU⟩, e.logOfCoord hVU _ hz, ?_⟩
  have hd : e.IsResidueDecomp (e.logOfCoord hVU _ hz) (le_refl _) hVU 0 β' := by
    unfold Stacks.Divisors.IdealTrivialization.IsResidueDecomp
    rw [e.logEval_logOfCoord_basisLE, smul_zero, zero_add]
  rw [logRes_eq hI hlog (isResidueOf_of_isResidueDecomp hlog e hd), formRes_map,
    ← divisorForms_map_map hV₀ (inf_le_left : V₀ ⊓ Ux ≤ V₀)]
  exact congrArg _ hβ

end AlgebraicGeometry.Scheme.Hom

end
