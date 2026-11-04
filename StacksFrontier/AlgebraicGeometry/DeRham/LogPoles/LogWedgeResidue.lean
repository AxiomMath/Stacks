module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogWedgeLeibniz

/-!
# The residue of a wedge product with a form with no pole

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor for which the
de Rham complex of log poles is defined. This file proves clause (4) of [Stacks, Tag 0FUP]: the
residue `Res : Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1]` of
`StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogResidue` satisfies

`Res(ω ∧ η) = Res(ω) ∧ η|_Y`

for `ω` a local section of `Ω^{p+1}_{X/S}(log Y)` and `η` a local section of `Ω^q_{X/S}`, and
`Res(ω ∧ η) = 0` for `ω` of degree `0`.

On a chart, a residue decomposition `ω(b₀) = t α + dt ∧ β` of `ω` gives the residue decomposition
`(ω ∧ η)(b₀) = t (α ∧ η) + dt ∧ (β ∧ η)` of `ω ∧ η`
(`Stacks.Divisors.IdealTrivialization.isResidueDecomp_logFormsWedge_logPolesFormsInclusion`), and
restriction to `Y` is multiplicative.

## Main results

* `AlgebraicGeometry.Scheme.Hom.logRes_logFormsWedge_logPolesFormsInclusion`: **the residue
  formula** in positive degree.
* `AlgebraicGeometry.Scheme.Hom.logRes_logFormsWedge_logPolesFormsInclusion_zero`: the residue of
  `ω ∧ η` vanishes for `ω` of degree `0`.

## References

* [Stacks Project, Tag 0FUP](https://stacks.math.columbia.edu/tag/0FUP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.SheafOfModules.gradedFormsGOne
  AlgebraicGeometry.SheafOfModules.gradedFormsGMul AlgebraicGeometry.SheafOfModules.gradedFormsGRing

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData}

/-- The wedge product of forms on the divisor commutes with restriction of sections of
`i_*Ω^•_{Y/S}`. -/
theorem divisorForms_map_formWedge {p q : ℕ} {W V : X.Opens} (h : V ≤ W)
    (ρ : Γ(divisorForms f I p, W)) (σ : Γ(divisorForms f I q, W)) :
    (divisorForms f I (p + q)).presheaf.map (homOfLE h).op
        (formWedge (I.subschemeι ≫ f) p q (I.subschemeι ⁻¹ᵁ W) ρ σ) =
      formWedge (I.subschemeι ≫ f) p q (I.subschemeι ⁻¹ᵁ V)
        ((divisorForms f I p).presheaf.map (homOfLE h).op ρ)
        ((divisorForms f I q).presheaf.map (homOfLE h).op σ) := by
  rw [Scheme.Modules.pushforward_obj_presheaf_map, Scheme.Modules.pushforward_obj_presheaf_map,
    Scheme.Modules.pushforward_obj_presheaf_map]
  exact formWedge_res (f := I.subschemeι ≫ f) p q
    (show I.subschemeι ⁻¹ᵁ V ≤ I.subschemeι ⁻¹ᵁ W from fun _ hx => h hx) ρ σ

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Divisors.IdealTrivialization

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : IdealTrivialization I U)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- The value at the basis element of `φ ∧ ι η` is `φ(b₀) ∧ η`. -/
theorem logEval_logFormsWedge_logPolesFormsInclusion {p q : ℕ} {W : X.Opens}
    (φ : (logPolesForms f I p).val.obj (op W)) (η : Γ(relativeDifferentialForms f (q : ℤ), W))
    {V : X.Opens} (hVW : V ≤ W) (hVU : V ≤ U) :
    logEval f I (logFormsWedge hI hlog φ ((logPolesFormsInclusion f I q).val.app (op W) η)) hVW
        (e.basisLE hVU) =
      formWedge f p q V (logEval f I φ hVW (e.basisLE hVU))
        ((relativeDifferentialForms f (q : ℤ)).presheaf.map (homOfLE hVW).op η) := by
  have h := e.equationAt_smul_logEval_logFormsWedge hI hlog φ
    ((logPolesFormsInclusion f I q).val.app (op W) η) hVW hVU
  rw [logEval_logPolesFormsInclusion, formWedge_smul_right] at h
  exact e.eq_of_equationAt_smul_eq hlog hVU h

/-- A residue decomposition of `φ ∧ ι η` from one of `φ`: if `φ(b₀) = t α + dt ∧ β` then
`(φ ∧ ι η)(b₀) = t (α ∧ η) + dt ∧ (β ∧ η)`. -/
theorem isResidueDecomp_logFormsWedge_logPolesFormsInclusion {p q : ℕ} {W : X.Opens}
    (φ : (logPolesForms f I (p + 1)).val.obj (op W)) (η : Γ(relativeDifferentialForms f (q : ℤ), W))
    {V : X.Opens} {hVW : V ≤ W} {hVU : V ≤ U}
    {α : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V)}
    {β : Γ(relativeDifferentialForms f (p : ℤ), V)} (hd : e.IsResidueDecomp φ hVW hVU α β) :
    e.IsResidueDecomp (logFormsCast (Nat.add_right_comm p 1 q)
        (logFormsWedge hI hlog φ ((logPolesFormsInclusion f I q).val.app (op W) η))) hVW hVU
      (formCast (Nat.add_right_comm p 1 q) (formWedge f (p + 1) q V α
          ((relativeDifferentialForms f (q : ℤ)).presheaf.map (homOfLE hVW).op η)))
      (formWedge f p q V β
        ((relativeDifferentialForms f (q : ℤ)).presheaf.map (homOfLE hVW).op η)) := by
  unfold IsResidueDecomp
  set ηV := (relativeDifferentialForms f (q : ℤ)).presheaf.map (homOfLE hVW).op η
  set t := e.equationAt hVU
  refine totForm_injective (p + q + 1) V ?_
  refine (totForm_logEval_logFormsCast (Nat.add_right_comm p 1 q) _ hVW _).trans ?_
  rw [e.logEval_logFormsWedge_logPolesFormsInclusion hI hlog φ η hVW hVU]
  refine (totForm_formWedge (p + 1) q V _ ηV).trans ?_
  refine Eq.trans ?_ (map_add (totForm f (p + q + 1) V) _ _).symm
  have hK : totForm f (p + 1) V (logEval f I φ hVW (e.basisLE hVU)) =
      totScalar f V t * totForm f (p + 1) V α + totExact f V t * totForm f p V β :=
    (congrArg (totForm f (p + 1) V) hd).trans ((map_add (totForm f (p + 1) V) _ _).trans
      (congrArg₂ (· + ·) (totForm_smul (p + 1) V t α) (totForm_exactWedge p V t β)))
  have e1 : totScalar f V t * (totForm f (p + 1) V α * totForm f q V ηV) =
      totForm f (p + q + 1) V (t • formCast (Nat.add_right_comm p 1 q)
        (formWedge f (p + 1) q V α ηV)) :=
    ((totForm_smul (p + q + 1) V t _).trans (congrArg (totScalar f V t * ·)
      ((totForm_formCast (Nat.add_right_comm p 1 q) _).trans
        (totForm_formWedge (p + 1) q V α ηV)))).symm
  have e2 : totExact f V t * (totForm f p V β * totForm f q V ηV) =
      totForm f (p + q + 1) V (exactWedge f (p + q) V t (formWedge f p q V β ηV)) :=
    ((totForm_exactWedge (p + q) V t _).trans (congrArg (totExact f V t * ·)
      (totForm_formWedge p q V β ηV))).symm
  rw [hK, add_mul, mul_assoc, mul_assoc]
  exact congrArg₂ (· + ·) e1 e2

end Stacks.Divisors.IdealTrivialization

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData}
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- **The residue of a wedge product with a form with no pole**:
`Res(φ ∧ η) = Res(φ) ∧ η|_Y` for a local section `φ` of `Ω^{p+1}_{X/S}(log Y)` and a local
section `η` of `Ω^q_{X/S}`, the wedge product read in degree `(p + q) + 1`. -/
theorem logRes_logFormsWedge_logPolesFormsInclusion {p q : ℕ} {W : X.Opens}
    (φ : (logPolesForms f I (p + 1)).val.obj (op W))
    (η : Γ(relativeDifferentialForms f (q : ℤ), W)) :
    logRes hI hlog (logFormsCast (Nat.add_right_comm p 1 q)
        (logFormsWedge hI hlog φ ((logPolesFormsInclusion f I q).val.app (op W) η))) =
      formWedge (I.subschemeι ≫ f) p q (I.subschemeι ⁻¹ᵁ W) (logRes hI hlog φ)
        (formRes I.subschemeι (q : ℤ) W η) := by
  refine logRes_eq_of_local hI hlog _ _ fun x hx => ?_
  obtain ⟨Ux, hxU, ⟨e⟩⟩ := Stacks.Divisors.IdealTrivialization.exists_mem_nonempty hI x
  obtain ⟨V, hV, hxV, α, β, hd⟩ := e.exists_isResidueDecomp φ (inf_le_left : W ⊓ Ux ≤ W)
    (inf_le_right : W ⊓ Ux ≤ Ux) x ⟨hx, hxU⟩
  have hVW : V ≤ W := hV.trans inf_le_left
  have hVU : V ≤ Ux := hV.trans inf_le_right
  refine ⟨Ux, e, V, hVW, hVU, _, _, hxV,
    e.isResidueDecomp_logFormsWedge_logPolesFormsInclusion hI hlog φ η hd, ?_⟩
  refine (divisorForms_map_formWedge hVW _ _).trans ?_
  rw [logRes_map_eq hI hlog e φ hVW hVU hd, ← formRes_map, formRes_formWedge]

/-- The inclusion of forms with no pole commutes with restriction. -/
theorem logPolesFormsInclusion_map {p : ℕ} {W V : X.Opens} (h : V ≤ W)
    (η : Γ(relativeDifferentialForms f (p : ℤ), W)) :
    (logPolesForms f I p).val.map (homOfLE h).op ((logPolesFormsInclusion f I p).val.app (op W) η) =
      (logPolesFormsInclusion f I p).val.app (op V)
        ((relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op η) :=
  logEval_ext fun W' h' a => by
    rw [logEval_res, logEval_logPolesFormsInclusion, logEval_logPolesFormsInclusion, forms_map_map]

/-- **The residue of a wedge product of a form of degree `0` with a form with no pole vanishes**:
a form of degree `0` with logarithmic poles is locally a function, so the product has no pole. -/
theorem logRes_logFormsWedge_logPolesFormsInclusion_zero {q : ℕ} {W : X.Opens}
    (φ : (logPolesForms f I 0).val.obj (op W))
    (η : Γ(relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W)) :
    logRes hI hlog (logFormsCast (Nat.zero_add (q + 1))
        (logFormsWedge hI hlog φ ((logPolesFormsInclusion f I (q + 1)).val.app (op W) η))) = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext (Scheme.Modules.isSheaf _) fun x hx => ?_
  obtain ⟨V, hVW, hxV, ω, hω⟩ := exists_map_eq_logPolesFormsInclusion_zero hI φ x hx
  refine ⟨V, hVW, hxV, ?_⟩
  refine (logRes_res hI hlog hVW _).symm.trans ?_
  rw [logFormsCast_map, ← logFormsWedge_res, hω,
    logPolesFormsInclusion_map,
    logFormsWedge_logPolesFormsInclusion, logFormsCast_logPolesFormsInclusion,
    logRes_logPolesFormsInclusion, map_zero]

end AlgebraicGeometry.Scheme.Hom
