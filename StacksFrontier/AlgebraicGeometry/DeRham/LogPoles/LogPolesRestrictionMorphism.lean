module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.WeightZeroRestriction
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.KernelLocalGeneration
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.EquationDivision
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.MorphismGluing
public import StacksFrontier.AlgebraicGeometry.DeRham.BasePushforward
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ShiftedBoundarySequence
public import StacksFrontier.Algebra.Homology.Embedding.ExtendDesuspend

/-!
# The lower right morphism of short exact sequences of Stacks Tag 0FUQ

Let `Y ⊆ X` be an effective Cartier divisor with ideal sheaf `𝒪_X(-Y)`, `i : Y ⟶ X`, for which the
de Rham complex of log poles is defined, and let `L̄ = 𝒪_X(-Y)|_Y`. The proof of Stacks Tag 0FUQ
uses a morphism of short exact sequences from the shifted log poles sequence of Tag 0FMW,
`0 → Ω^•_{X/S}[1] → Ω^•_{X/S}(log Y)[1] → Ω^•_{Y/S} → 0`, to the shifted residue sequence of
Tag 0FUF for `L̄` on `Y`, whose middle arrow is `ω' + d log t ∧ ω ↦ ω'|_Y + d log s̄ ∧ ω|_Y`.

The middle arrow is obtained by factoring the restriction of weight-zero forms
`Ω^•_{L^⋆/S,0} ⟶ i_*Ω^•_{L̄^⋆/S,0}` (`Stacks.LineBundle.Situation.weightZeroRestrictF`) through
the epimorphism `Ω^•_{L^⋆/S,0} ⟶ Ω^•_{X/S}(log Y)` of the upper left triangle: a local
presentation `α + d log t ∧ η` of the zero form has `α|_Y = 0` and `η|_Y = 0`, because `t` is a
nonzerodivisor on forms ([Stacks, Tag 0FMV]) and the forms vanishing on `Y` are locally
`t a + dt ∧ b`.

## Main definitions

* `Stacks.LineBundle.logPolesRestrictF`: the middle arrow, degreewise.
* `Stacks.LineBundle.logPolesRestrictMorphism`: the morphism of shifted short exact sequences.

## Main results

* `Stacks.LineBundle.epi_toLogPolesF`: the upper left middle arrow is an epimorphism.
* `Stacks.LineBundle.logPolesShiftedSequence_boundary_comp_restriction`: **the lower right
  triangle of Tag 0FUQ at the level of boundary maps.**

## References

* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom)

universe w u

namespace Stacks.Divisors.IdealTrivialization

open _root_.AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : IdealTrivialization I U)

/-- Locally, `dt ∧ η = t · (dt ∧ a)` for a form `η` vanishing on the divisor. -/
theorem exists_local_exactWedge_eq_smul {W : X.Opens} (hW : W ≤ U) (p : ℕ)
    (η : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hη : formRes I.subschemeι (p : ℤ) W η = 0) (x : X) (hx : x ∈ W) :
    ∃ (W' : X.Opens) (hW' : W' ≤ W), x ∈ W' ∧
      ∃ a : Γ(relativeDifferentialForms f (p : ℤ), W'),
        exactWedge f p W' (e.equationAt (hW'.trans hW))
            ((relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE hW').op η) =
          e.equationAt (hW'.trans hW) • exactWedge f p W' (e.equationAt (hW'.trans hW)) a := by
  cases p with
  | zero =>
    obtain ⟨W', hW', hxW', a, ha⟩ := e.exists_local_eq_smul hW η hη x hx
    exact ⟨W', hW', hxW', a, by rw [ha, exactWedge_smul_right]⟩
  | succ q =>
    obtain ⟨W', hW', hxW', a, b, hab⟩ := e.exists_local_eq_smul_add_exactWedge hW q η hη x hx
    refine ⟨W', hW', hxW', a, ?_⟩
    rw [hab, exactWedge_add_right, exactWedge_smul_right, exactWedge_exactWedge_self, add_zero]

/-- **A local presentation `α + d log t ∧ η` of the zero form restricts to zero on the divisor**:
both `α|_Y` and `η|_Y` vanish. -/
theorem formRes_eq_zero_of_logPolesChartForm_eq_zero
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)
    {W : X.Opens} (hW : W ≤ U) (p : ℕ)
    (α : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (η : Γ(relativeDifferentialForms f (p : ℤ), W)) (h : e.logPolesChartForm hW α η = 0) :
    formRes I.subschemeι ((p + 1 : ℕ) : ℤ) W α = 0 ∧ formRes I.subschemeι (p : ℤ) W η = 0 := by
  have hη : formRes I.subschemeι (p : ℤ) W η = 0 := by
    have := e.logRes_logPolesChartForm hI hlog hW α η
    rw [h] at this
    rw [← this]
    exact map_zero ((Scheme.Hom.logResHom f I hI hlog p).val.app (op W)).hom
  refine ⟨?_, hη⟩
  have hrel := (e.logPolesChartForm_eq_zero_iff hW α η).mp h
  refine Stacks.Coherent.modulesSections_eq_of_locally_eq
    ((Scheme.Modules.pushforward I.subschemeι).obj
      (relativeDifferentialForms (I.subschemeι ≫ f) ((p + 1 : ℕ) : ℤ))) W _ 0 fun x hx => ?_
  obtain ⟨W', hW', hxW', a, ha⟩ := e.exists_local_exactWedge_eq_smul hW p η hη x hx
  refine ⟨W', hW', hxW', ?_⟩
  have hrel' := congrArg ((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map
    (homOfLE hW').op) hrel
  rw [map_add, map_zero, Scheme.Modules.map_smul, exactWedge_res, e.equationAt_res, ha,
    ← smul_add] at hrel'
  have h0 := e.eq_zero_of_equationAt_smul_eq_zero hlog (hW'.trans hW) (p + 1) _ hrel'
  have hα : (relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hW').op α =
      -exactWedge f p W' (e.equationAt (hW'.trans hW)) a := eq_neg_of_add_eq_zero_left h0
  refine ((PresheafOfModules.naturality_apply (formRestriction I.subschemeι f
    ((p + 1 : ℕ) : ℤ)).val (homOfLE hW').op α).symm.trans ?_).trans (map_zero _).symm
  show formRes I.subschemeι ((p + 1 : ℕ) : ℤ) W'
    ((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hW').op α) = 0
  rw [hα, formRes_neg, neg_eq_zero]
  refine (formRestriction_exactWedge (f := f) I.subschemeι p W' _ a).trans ?_
  rw [show (I.subschemeι.app W').hom (e.equationAt (hW'.trans hW)) = 0 from app_idealFn _]
  exact exactWedge_zero_left (f := I.subschemeι ≫ f) p _ _

end Stacks.Divisors.IdealTrivialization

namespace Stacks.LineBundle

section Ideal

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  [hI : Stacks.Divisors.IsEffectiveCartierDivisor I] (hlog : f.HasLogPolesDeRhamComplex I)

/-! ### The upper left morphism is an epimorphism -/

/-- The upper left morphism of Stacks Tag 0FUQ in degree `p + 1`, as a morphism of the short exact
sequences of abelian sheaves `0 → Ω^{p+1}_{X/S} → Ω^{p+1}_{L^⋆/S,0} → Ω^p_{X/S} → 0` and
`0 → Ω^{p+1}_{X/S} → Ω^{p+1}_{X/S}(log Y) → i_*Ω^p_{Y/S} → 0`. -/
def toLogPolesShortComplexHom (p : ℕ) :
    (idealSituation f I).residueShortComplex.map (HomologicalComplex.eval _ _ (p + 1)) ⟶
      (Scheme.Hom.logResidueShortComplex f I hI hlog).map
        (HomologicalComplex.eval _ _ (p + 1)) where
  τ₁ := 𝟙 _
  τ₂ := (abelianSheaf X).map (toLogPolesF f I (p + 1))
  τ₃ := (abelianSheaf X).map (Scheme.Hom.formRestriction I.subschemeι f (p : ℤ))
  comm₁₂ := by
    change 𝟙 _ ≫ (abelianSheaf X).map (Scheme.Hom.logPolesFormsInclusion f I (p + 1)) =
      (abelianSheaf X).map ((idealSituation f I).pullbackHom (p + 1)) ≫
        (abelianSheaf X).map (toLogPolesF f I (p + 1))
    rw [Category.id_comp, ← Functor.map_comp, pullbackHom_comp_toLogPolesF]
  comm₂₃ := by
    change (abelianSheaf X).map (toLogPolesHom f I p) ≫
        (abelianSheaf X).map (Scheme.Hom.logResHom f I hI hlog p) =
      (abelianSheaf X).map ((idealSituation f I).residueHom p) ≫
        (abelianSheaf X).map (Scheme.Hom.formRestriction I.subschemeι f (p : ℤ))
    rw [← Functor.map_comp, ← Functor.map_comp, toLogPolesHom_comp_logResHom]

/-- The upper left morphism `Ω^0_{L^⋆/S,0} ⟶ Ω^0_{X/S}(log Y)` is an isomorphism. -/
private theorem isIso_toLogPolesF_zero (hlog : f.HasLogPolesDeRhamComplex I) :
    IsIso (toLogPolesF f I 0) := by
  have := isIso_pullbackHom_zero (idealSituation f I)
  have hS := Scheme.Hom.shortExact_eval_zero f I hI hlog
  have : (abelianSheaf X).Faithful :=
    inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Faithful
  have : Mono (Scheme.Hom.logPolesFormsInclusion f I 0) :=
    (abelianSheaf X).mono_of_mono_map hS.mono_f
  have : Epi (Scheme.Hom.logPolesFormsInclusion f I 0) :=
    (abelianSheaf X).epi_of_epi_map
      ((hS.exact.epi_f_iff).mpr ((CategoryTheory.Limits.isZero_zero _).eq_of_tgt _ _))
  have : IsIso (Scheme.Hom.logPolesFormsInclusion f I 0) := isIso_of_mono_of_epi _
  exact inferInstanceAs (IsIso (inv ((idealSituation f I).pullbackHom 0) ≫
    Scheme.Hom.logPolesFormsInclusion f I 0))

include hlog in
/-- **The upper left morphism `Ω^•_{L^⋆/S,0} ⟶ Ω^•_{X/S}(log Y)` is an epimorphism of abelian
sheaves in every degree**: it is the identity on `Ω^•_{X/S}` and the restriction
`Ω^•_{X/S} ⟶ i_*Ω^•_{Y/S}` on the quotients, which is surjective. -/
theorem epi_abelianSheaf_map_toLogPolesF (n : ℕ) :
    Epi ((abelianSheaf X).map (toLogPolesF f I n)) := by
  cases n with
  | zero =>
    have := isIso_toLogPolesF_zero f I hlog
    infer_instance
  | succ p =>
    have h₁ := (idealSituation f I).shortExact_eval_succ p
    have h₂ := Scheme.Hom.shortExact_eval_succ f I hI hlog p
    have := h₁.epi_g
    have := h₂.epi_g
    have : Epi (toLogPolesShortComplexHom f I hlog p).τ₃ :=
      Scheme.Hom.epi_abelianSheaf_formRestriction I.subschemeι f p
    have : Epi (toLogPolesShortComplexHom f I hlog p).τ₁ :=
      inferInstanceAs (Epi (𝟙 _))
    exact ShortComplex.epi_τ₂_of_exact_of_epi (toLogPolesShortComplexHom f I hlog p) h₂.exact

include hlog in
/-- The upper left morphism `Ω^n_{L^⋆/S,0} ⟶ Ω^n_{X/S}(log Y)` is an epimorphism. -/
theorem epi_toLogPolesF (n : ℕ) : Epi (toLogPolesF f I n) := by
  have : (abelianSheaf X).Faithful :=
    inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Faithful
  have := epi_abelianSheaf_map_toLogPolesF f I hlog n
  exact (abelianSheaf X).epi_of_epi_map inferInstance

/-! ### The restriction of log forms to the divisor -/

/-- **The line-bundle situation of `𝒪_X(-Y)|_Y`** over `S`: the restriction to `Y` of the
situation of `𝒪_X(-Y)`. -/
abbrev divisorSituation : Situation.{u} := (idealSituation f I).baseChange I.subschemeι

include hlog in
/-- **A weight-zero form killed by the upper left morphism restricts to zero on `Y`**, over a base
chart: `α + d log t ∧ η = 0` forces `α|_Y = 0` and `η|_Y = 0`. -/
theorem Situation.BaseChart.weightZeroRestrict_eq_zero_of_toLogPoles_eq_zero
    (c : (idealSituation f I).BaseChart) (p : ℕ)
    (x : Γ((idealSituation f I).weightZero (p + 1), c.U.1)) (hx : c.toLogPoles p x = 0) :
    c.weightZeroRestrict I.subschemeι p x = 0 := by
  obtain ⟨h1, h2⟩ := c.idealTriv.formRes_eq_zero_of_logPolesChartForm_eq_zero hI hlog le_rfl p
    (c.pullPart p x) (((idealSituation f I).residueHom p).app c.U.1 x) hx
  rw [Situation.BaseChart.weightZeroRestrict_apply]
  refine (congrArg₂ ((c.baseChange I.subschemeι).decompose p) h1 h2).trans ?_
  have := (c.baseChange I.subschemeι).decompose_add p 0 0 0 0
  rw [add_zero, add_zero] at this
  exact (add_eq_left.mp this.symm)

include hlog in
/-- **A weight-zero form killed by the upper left morphism restricts to zero on `Y`.** -/
theorem weightZeroRestrictHom_eq_zero_of_toLogPolesHom_eq_zero (p : ℕ) (W : X.Opens)
    (x : Γ((idealSituation f I).weightZero (p + 1), W)) (hx : (toLogPolesHom f I p).app W x = 0) :
    ((idealSituation f I).weightZeroRestrictHom I.subschemeι p).app W x = 0 := by
  refine Stacks.Coherent.modulesSections_eq_of_locally_eq
    ((Scheme.Modules.pushforward I.subschemeι).obj ((divisorSituation f I).weightZero (p + 1)))
    W _ 0 fun y hy => ?_
  obtain ⟨c, hyc, hcW⟩ := (idealSituation f I).exists_baseChart hy
  refine ⟨c.U.1, hcW, hyc, ?_⟩
  have hres : ((idealSituation f I).weightZeroRestrictHom I.subschemeι p).app c.U.1
      (((idealSituation f I).weightZero (p + 1)).presheaf.map (homOfLE hcW).op x) =
      (Scheme.Modules.presheaf ((Scheme.Modules.pushforward I.subschemeι).obj
        ((divisorSituation f I).weightZero (p + 1)))).map (homOfLE hcW).op
        (((idealSituation f I).weightZeroRestrictHom I.subschemeι p).app W x) :=
    PresheafOfModules.naturality_apply
      ((idealSituation f I).weightZeroRestrictHom I.subschemeι p).val (homOfLE hcW).op x
  have hΦ : c.toLogPoles p (((idealSituation f I).weightZero (p + 1)).presheaf.map
      (homOfLE hcW).op x) = 0 := by
    have hx' : (toLogPolesHom f I p).val.app (op W) x = 0 := hx
    have h2 := PresheafOfModules.naturality_apply (toLogPolesHom f I p).val (homOfLE hcW).op x
    rw [hx', map_zero] at h2
    exact (toLogPolesHom_app f I p c _).symm.trans h2
  have h3 := (idealSituation f I).weightZeroRestrictHom_app I.subschemeι p c
    (((idealSituation f I).weightZero (p + 1)).presheaf.map (homOfLE hcW).op x)
  rw [c.weightZeroRestrict_eq_zero_of_toLogPoles_eq_zero f I hlog p _ hΦ] at h3
  rw [← hres, map_zero]
  exact h3

include hlog in
/-- The restriction of weight-zero forms to `Y` vanishes on the kernel of the upper left morphism
`Ω^n_{L^⋆/S,0} ⟶ Ω^n_{X/S}(log Y)`. -/
theorem kernel_ι_toLogPolesF_comp_weightZeroRestrictF (n : ℕ) :
    kernel.ι (toLogPolesF f I n) ≫ (idealSituation f I).weightZeroRestrictF I.subschemeι n = 0 := by
  cases n with
  | zero =>
    have := isIso_toLogPolesF_zero f I hlog
    rw [kernel.ι_of_mono, zero_comp]
  | succ p =>
    refine Scheme.Modules.hom_ext _ _ fun W => ?_
    ext y
    have hy : (toLogPolesHom f I p).app W ((kernel.ι (toLogPolesF f I (p + 1))).app W y) = 0 := by
      have := congrArg (fun φ => Scheme.Modules.Hom.app φ W y) (kernel.condition
        (toLogPolesF f I (p + 1)))
      exact this
    exact weightZeroRestrictHom_eq_zero_of_toLogPolesHom_eq_zero f I hlog p W _ hy

/-- **The middle arrow of the lower right morphism of short exact sequences of Stacks Tag 0FUQ**,
in degree `n`: `Ω^n_{X/S}(log Y) ⟶ i_*Ω^n_{L̄^⋆/S,0}`, `L̄ = 𝒪_X(-Y)|_Y`, sending
`ω' + d log t ∧ ω` to `ω'|_Y + d log s̄ ∧ ω|_Y`, `s̄` the restriction of the generator `s` of
`𝒪_X(-Y)` with `t` the corresponding local equation. It is the factorization of the
restriction of weight-zero forms through the epimorphism `Ω^n_{L^⋆/S,0} ⟶ Ω^n_{X/S}(log Y)`. -/
def logPolesRestrictF (n : ℕ) :
    Scheme.Hom.logPolesForms f I n ⟶
      (Scheme.Modules.pushforward I.subschemeι).obj ((divisorSituation f I).weightZero n) :=
  haveI := epi_toLogPolesF f I hlog n
  Abelian.epiDesc (toLogPolesF f I n) _ (kernel_ι_toLogPolesF_comp_weightZeroRestrictF f I hlog n)

/-- The upper left morphism followed by `logPolesRestrictF` is the restriction of weight-zero forms
to `Y`. -/
theorem toLogPolesF_comp_logPolesRestrictF (n : ℕ) :
    toLogPolesF f I n ≫ logPolesRestrictF f I hlog n =
      (idealSituation f I).weightZeroRestrictF I.subschemeι n :=
  have := epi_toLogPolesF f I hlog n
  Abelian.comp_epiDesc _ _ _

/-- **The lower right middle arrow extends the restriction of forms**: on forms with no pole it is
`ω ↦ π̄^*(ω|_Y)`. -/
theorem logPolesFormsInclusion_comp_logPolesRestrictF (n : ℕ) :
    Scheme.Hom.logPolesFormsInclusion f I n ≫ logPolesRestrictF f I hlog n =
      Scheme.Hom.formRestriction I.subschemeι f (n : ℤ) ≫
        (Scheme.Modules.pushforward I.subschemeι).map ((divisorSituation f I).pullbackHom n) := by
  rw [← pullbackHom_comp_toLogPolesF, Category.assoc, toLogPolesF_comp_logPolesRestrictF]
  exact (idealSituation f I).pullbackHom_comp_weightZeroRestrictF I.subschemeι n

/-- **The lower right middle arrow is compatible with the residues**: the residue of
`ω'|_Y + d log s̄ ∧ ω|_Y` is `ω|_Y`, the residue of `ω' + d log t ∧ ω`. -/
theorem logPolesRestrictF_comp_residueHom (p : ℕ) :
    logPolesRestrictF f I hlog (p + 1) ≫
        (Scheme.Modules.pushforward I.subschemeι).map ((divisorSituation f I).residueHom p) =
      Scheme.Hom.logResHom f I hI hlog p := by
  have := epi_toLogPolesF f I hlog (p + 1)
  refine (cancel_epi (toLogPolesF f I (p + 1))).mp ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (toLogPolesF_comp_logPolesRestrictF f I hlog (p + 1))).trans ?_
  exact ((idealSituation f I).weightZeroRestrictHom_comp_residueHom I.subschemeι p).trans
    (toLogPolesHom_comp_logResHom f I hlog p).symm

/-- **The lower right middle arrow commutes with the differentials**, in abelian sheaves. -/
theorem logDAbHom_comp_logPolesRestrictF (n : ℕ) :
    Scheme.Hom.logDAbHom f I hI hlog n ≫ (abelianSheaf X).map (logPolesRestrictF f I hlog (n + 1)) =
      (abelianSheaf X).map (logPolesRestrictF f I hlog n) ≫
        (idealSituation f I).pushforwardWeightZeroDAbHom I.subschemeι n := by
  have := epi_abelianSheaf_map_toLogPolesF f I hlog n
  refine (cancel_epi ((abelianSheaf X).map (toLogPolesF f I n))).mp ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (weightZeroDAbHom_comp_toLogPolesF f I hlog n).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Functor.map_comp _ _ _).symm.trans (congrArg (abelianSheaf X).map
    (toLogPolesF_comp_logPolesRestrictF f I hlog (n + 1))))).trans ?_
  refine ((idealSituation f I).weightZeroDAbHom_comp_weightZeroRestrictF I.subschemeι n).trans ?_
  refine (congrArg (· ≫ _) ((congrArg (abelianSheaf X).map
    (toLogPolesF_comp_logPolesRestrictF f I hlog n)).symm.trans (Functor.map_comp _ _ _))).trans ?_
  exact Category.assoc _ _ _

/-! ### The lower right morphism as maps of complexes over `f^{-1}𝒪_S` -/

/-- The direct image along `i : Y ⟶ X` over the base rings, from sheaves of
`(i ≫ f)^{-1}𝒪_S`-modules on `Y` to sheaves of `f^{-1}𝒪_S`-modules on `X`. -/
abbrev divisorPushforward :
    SheafOfModules.{u} (Scheme.Hom.baseRingSheaf (divisorSituation f I).f) ⥤
      SheafOfModules.{u} (Scheme.Hom.baseRingSheaf f) :=
  Scheme.Hom.basePushforward I.subschemeι f

/-- The direct image `divisorPushforward f I` is additive. -/
instance : (divisorPushforward f I).Additive :=
  Scheme.Hom.additive_basePushforward I.subschemeι f

/-- The direct image `divisorPushforward f I` preserves finite limits. -/
instance : PreservesFiniteLimits (divisorPushforward f I) :=
  Scheme.Hom.preservesFiniteLimits_basePushforward I.subschemeι f

/-- The direct image `divisorPushforward f I` preserves finite colimits. -/
instance : PreservesFiniteColimits (divisorPushforward f I) :=
  Scheme.Hom.preservesFiniteColimits_basePushforward I.subschemeι f

/-- The identification of the two readings of a direct image along `i : Y ⟶ X` over the base. -/
abbrev divisorPushforwardIso (M : (divisorSituation f I).X.Modules) :
    (divisorPushforward f I).obj ((Scheme.Hom.toBaseModules (divisorSituation f I).f).obj M) ≅
      (Scheme.Hom.toBaseModules f).obj ((Scheme.Modules.pushforward I.subschemeι).obj M) :=
  Scheme.Hom.basePushforwardToBaseModulesIso I.subschemeι f M

/-- **The de Rham complex of the divisor, read on `X`**: the complex `i_*Ω^•_{Y/S}` of sheaves of
`f^{-1}𝒪_S`-modules is the direct image over the base rings of `Ω^•_{Y/S}`. -/
def divisorDeRhamBaseHom :
    Scheme.Hom.divisorDeRhamBase f I ⟶
      ((divisorPushforward f I).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Scheme.Hom.deRhamComplex (divisorSituation f I).f) where
  f n := (divisorPushforwardIso f I
    (Scheme.Hom.relativeDifferentialForms (divisorSituation f I).f (n : ℤ))).inv
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [Scheme.Hom.divisorDeRhamBase_d]
    refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W =>
      ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    rfl

/-- The identification `divisorDeRhamBaseHom` is an isomorphism of complexes. -/
instance isIso_divisorDeRhamBaseHom : IsIso (divisorDeRhamBaseHom f I) := by
  have : ∀ n, IsIso ((divisorDeRhamBaseHom f I).f n) := fun n =>
    inferInstanceAs (IsIso (divisorPushforwardIso f I
      (Scheme.Hom.relativeDifferentialForms (divisorSituation f I).f (n : ℤ))).inv)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The lower right middle arrow, as a map of complexes over `f^{-1}𝒪_S`**:
`Ω^•_{X/S}(log Y) ⟶ i_*Ω^•_{L̄^⋆/S,0}`. -/
def logPolesRestrictBaseMap :
    Scheme.Hom.deRhamComplexLogPoles f I hI hlog ⟶
      ((divisorPushforward f I).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (divisorSituation f I).weightZeroBaseComplex where
  f n := (Scheme.Hom.toBaseModules f).map (logPolesRestrictF f I hlog n) ≫
    (divisorPushforwardIso f I ((divisorSituation f I).weightZero n)).inv
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [Scheme.Hom.deRhamComplexLogPoles_d, Functor.mapHomologicalComplex_obj_d,
      (divisorSituation f I).weightZeroBaseComplex_d]
    refine (_root_.SheafOfModules.toSheaf (Scheme.Hom.baseRingSheaf f)).map_injective ?_
    simp only [Functor.map_comp]
    exact (logDAbHom_comp_logPolesRestrictF f I hlog i).symm

/-- The inclusion `Ω^•_{X/S} ⟶ Ω^•_{X/S}(log Y)` followed by `logPolesRestrictBaseMap` is the
restriction `Ω^•_{X/S} ⟶ i_*Ω^•_{Y/S}` followed by the direct image of the inclusion
`Ω^•_{Y/S} ⟶ Ω^•_{L̄^⋆/S,0}`. -/
theorem deRhamComplexLogPolesInclusion_comp_logPolesRestrictBaseMap :
    Scheme.Hom.deRhamComplexLogPolesInclusion f I hI hlog ≫ logPolesRestrictBaseMap f I hlog =
      Scheme.Hom.divisorRestrictionBase f I ≫ divisorDeRhamBaseHom f I ≫
        ((divisorPushforward f I).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (divisorSituation f I).inclusionBaseMap := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine (_root_.SheafOfModules.toSheaf (Scheme.Hom.baseRingSheaf f)).map_injective ?_
  have h := congrArg (abelianSheaf X).map (logPolesFormsInclusion_comp_logPolesRestrictF f I hlog n)
  simp only [Functor.map_comp] at h
  exact h

/-- `logPolesRestrictBaseMap` followed by the direct image of the residue
`Ω^•_{L̄^⋆/S,0} ⟶ Ω^•_{Y/S}[-1]` is the residue `Ω^•_{X/S}(log Y) ⟶ i_*Ω^•_{Y/S}[-1]`, read through
`divisorDeRhamBaseHom`. -/
theorem logPolesRestrictBaseMap_comp_residueBaseMap :
    logPolesRestrictBaseMap f I hlog ≫
        ((divisorPushforward f I).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (divisorSituation f I).residueBaseMap =
      Scheme.Hom.logResidueBaseMap f hI hlog ≫
        CochainComplex.desuspendLift (divisorPushforward f I) (divisorDeRhamBaseHom f I) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  cases n with
  | zero =>
    exact (Functor.map_isZero (divisorPushforward f I) (isZero_zero _)).eq_of_tgt _ _
  | succ p =>
    refine (_root_.SheafOfModules.toSheaf (Scheme.Hom.baseRingSheaf f)).map_injective ?_
    have h := congrArg (abelianSheaf X).map (logPolesRestrictF_comp_residueHom f I hlog p)
    simp only [Functor.map_comp] at h
    exact h

/-! ### The lower right morphism of shifted short exact sequences -/

/-- The direct image over the base rings, applied to complexes indexed by `ℤ`. -/
abbrev divisorPushforwardInt :=
  (divisorPushforward f I).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The identification `i_*Ω^•_{Y/S} ≅ i_*Ω^•_{Y/S}` of the two readings of the de Rham complex
of the divisor on `X`**, indexed by `ℤ`: the complex `Ω^•_{Y/S}` regarded as a complex on `X`,
and the direct image over the base rings of the de Rham complex of `Y`. -/
def divisorDeRhamIntHom :
    Scheme.Hom.divisorDeRhamInt f I ⟶
      (divisorPushforwardInt f I).obj
        (AlgebraicGeometry.SheafOfModules.deRhamComplexInt
          (Scheme.Hom.deRhamAlgebras (divisorSituation f I).f)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (divisorSituation f I).f))) :=
  HomologicalComplex.extendMap (divisorDeRhamBaseHom f I) ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso (divisorPushforward f I)
      (Scheme.Hom.deRhamComplex (divisorSituation f I).f) ComplexShape.embeddingUpNat).hom

/-- The identification `divisorDeRhamIntHom` is an isomorphism of complexes. -/
instance isIso_divisorDeRhamIntHom : IsIso (divisorDeRhamIntHom f I) := by
  have : IsIso (HomologicalComplex.extendMap (divisorDeRhamBaseHom f I)
      ComplexShape.embeddingUpNat) :=
    Functor.map_isIso (ComplexShape.embeddingUpNat.extendFunctor _) (divisorDeRhamBaseHom f I)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ this (Iso.isIso_hom _)

/-- The lower right middle arrow, indexed by `ℤ`. -/
def logPolesRestrictIntMap :
    Scheme.Hom.deRhamComplexLogPolesInt f I hI hlog ⟶
      (divisorPushforwardInt f I).obj
        ((divisorSituation f I).weightZeroBaseComplex.extend ComplexShape.embeddingUpNat) :=
  HomologicalComplex.extendMap (logPolesRestrictBaseMap f I hlog) ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso (divisorPushforward f I)
      (divisorSituation f I).weightZeroBaseComplex ComplexShape.embeddingUpNat).hom

/-- **The lower right morphism of short exact sequences of Stacks Tag 0FUQ**, from the shifted log
poles sequence of Tag 0FMW, `0 → Ω^•_{X/S}[1] → Ω^•_{X/S}(log Y)[1] → Ω^•_{Y/S} → 0`, to the
direct image on `X` of the shifted residue sequence of Tag 0FUF for `L̄ = 𝒪_X(-Y)|_Y` on `Y`,
`0 → Ω^•_{Y/S}[1] → Ω^•_{L̄^⋆/S,0}[1] → Ω^•_{Y/S} → 0`, over the restriction of forms
`Ω^•_{X/S} ⟶ Ω^•_{Y/S}` and the identity of `Ω^•_{Y/S}`. Its middle arrow is
`ω' + d log t ∧ ω ↦ ω'|_Y + d log s̄ ∧ ω|_Y`. -/
def logPolesRestrictMorphism :
    Stacks.ShiftedBoundary.Morphism (Scheme.Hom.logPolesShiftedSequence f hI hlog)
      ((divisorSituation f I).residueShiftedSequence.map (divisorPushforward f I))
      (Scheme.Hom.divisorRestrictionInt f I ≫ divisorDeRhamIntHom f I)
      (divisorDeRhamIntHom f I) :=
  Stacks.ShiftedBoundary.Morphism.toMapOfShortExact (divisorPushforward f I)
    (Scheme.Hom.divisorRestrictionInt f I ≫ divisorDeRhamIntHom f I)
    (logPolesRestrictIntMap f I hlog) (divisorDeRhamIntHom f I)
    (by
      change HomologicalComplex.extendMap (Scheme.Hom.deRhamComplexLogPolesInclusion f I hI hlog)
            ComplexShape.embeddingUpNat ≫
          HomologicalComplex.extendMap (logPolesRestrictBaseMap f I hlog)
            ComplexShape.embeddingUpNat ≫ _ =
        (HomologicalComplex.extendMap (Scheme.Hom.divisorRestrictionBase f I)
            ComplexShape.embeddingUpNat ≫
          HomologicalComplex.extendMap (divisorDeRhamBaseHom f I) ComplexShape.embeddingUpNat ≫
            _) ≫
          (divisorPushforwardInt f I).map
            (HomologicalComplex.extendMap (divisorSituation f I).inclusionBaseMap
              ComplexShape.embeddingUpNat)
      rw [Category.assoc, Category.assoc,
        CochainComplex.mapHomologicalComplexExtendIso_hom_naturality,
        ← Category.assoc, ← HomologicalComplex.extendMap_comp,
        deRhamComplexLogPolesInclusion_comp_logPolesRestrictBaseMap,
        HomologicalComplex.extendMap_comp, HomologicalComplex.extendMap_comp, Category.assoc,
        Category.assoc])
    (CochainComplex.extend_comp_desuspendExtendIso (divisorPushforward f I)
      (logPolesRestrictBaseMap f I hlog) (divisorSituation f I).residueBaseMap
      (Scheme.Hom.logResidueBaseMap f hI hlog) (divisorDeRhamBaseHom f I)
      (logPolesRestrictBaseMap_comp_residueBaseMap f I hlog))

section Derived

variable [HasDerivedCategory.{w} (SheafOfModules.{u} (Scheme.Hom.baseRingSheaf f))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (Scheme.Hom.baseRingSheaf (divisorSituation f I).f))]

/-- **The direct image `i_*ζ` of a morphism `ζ : K ⟶ K[2]` of `D(Y, (i ≫ f)^{-1}𝒪_S)`**, as a
morphism `i_*K ⟶ (i_*K)[2]` of `D(X, f^{-1}𝒪_S)`: the exact direct image over the base rings on
derived categories, read on the complex `i_*K` through
`Functor.mapDerivedCategoryFactors` and the commutation with the translation by two. -/
def divisorPushforwardDerivedMap
    {K : CochainComplex (SheafOfModules.{u} (Scheme.Hom.baseRingSheaf (divisorSituation f I).f)) ℤ}
    (ζ : DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj K)⟦(2 : ℤ)⟧) :
    DerivedCategory.Q.obj ((divisorPushforwardInt f I).obj K) ⟶
      (DerivedCategory.Q.obj ((divisorPushforwardInt f I).obj K))⟦(2 : ℤ)⟧ :=
  (divisorPushforward f I).mapDerivedCategoryFactors.inv.app K ≫
    (divisorPushforward f I).mapDerivedCategory.map ζ ≫
      ((divisorPushforward f I).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
        ((divisorPushforward f I).mapDerivedCategoryFactors.hom.app K)⟦(2 : ℤ)⟧'

/-- **Stacks Project, Tag 0FUQ, lower right triangle, at the level of boundary maps**: the boundary
map `δ : Ω^•_{Y/S} ⟶ Ω^•_{X/S}[2]` of the shifted log poles sequence of Tag 0FMW followed by the
restriction of forms `Ω^•_{X/S}[2] ⟶ Ω^•_{Y/S}[2]` is the direct image on `X` of the boundary map
`Ω^•_{Y/S} ⟶ Ω^•_{Y/S}[2]` of the shifted residue sequence of Tag 0FUF for `𝒪_X(-Y)|_Y` on `Y`.
This is the functoriality of boundary maps along `Stacks.LineBundle.logPolesRestrictMorphism`, the
morphism of short exact sequences of the proof, and the compatibility of boundary maps with the
exact direct image along the closed immersion `i : Y ⟶ X`. -/
theorem logPolesShiftedSequence_boundary_comp_restriction :
    (Scheme.Hom.logPolesShiftedSequence f hI hlog).boundary ≫
        (DerivedCategory.Q.map
          (Scheme.Hom.divisorRestrictionInt f I ≫ divisorDeRhamIntHom f I))⟦(2 : ℤ)⟧' =
      DerivedCategory.Q.map (divisorDeRhamIntHom f I) ≫
        divisorPushforwardDerivedMap f I
          (divisorSituation f I).residueShiftedSequence.boundary := by
  rw [Stacks.ShiftedBoundary.Morphism.boundary_naturality (logPolesRestrictMorphism f I hlog),
    Stacks.ShiftedBoundary.Sequence.map_boundary]
  rfl

end Derived

end Ideal

end Stacks.LineBundle
