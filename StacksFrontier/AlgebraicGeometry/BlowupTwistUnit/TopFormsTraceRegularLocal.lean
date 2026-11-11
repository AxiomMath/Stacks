module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PointBlowupComparisonIsIso
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.ChainTopFormDataRegularLocal

/-!
# Stacks Project, Tag 0B4T

Let `A` be a regular local ring of dimension two and `A₀ ⊆ A` a subring with `Ω_{A/A₀}` free of
rank `r`, and set `ω_A = Ω^r_{A/A₀}`. For `f : X ⟶ Spec A` the result of a sequence of blowups in
closed points this file proves that there is a map

`φ_X : (Ω^r_{X/A₀})^{**} ⟶ ω_X`

extending the given identification, where `ω_X` is the dualizing module of `X` normalized relative
to `ω_A`. The extension is stated through the composite of
`Stacks.BlowupTwistUnit.ChainTopFormData.topFormsTrace`: pull the top forms of `Spec A` back to `X`,
apply `φ_X`, and take the trace of `f` back to `Spec A`; this composite is required to *be* the
identification `ω_A = Ω^r_{A/A₀}`. Over the open of `Spec A` over which `f` is an isomorphism —
which contains the generic point — the pullback of forms and the trace are the identifications
induced by `f`, so there `φ_X` is the given identification.

The induction runs along the sequence. At a blowup `b : X' ⟶ X` the duality bijection of `b`
turns a map out of `Rb_*((Ω^r_{X'/A₀})^{**})` into a map out of `(Ω^r_{X'/A₀})^{**}`; the map used
is `π ≫ a⁻¹ ≫ φ_X`, where `π : Rb_*((Ω^r_{X'/A₀})^{**}[0]) ⟶ (Ω^r_{X/A₀})^{**}[0]` and the
automorphism `a` are those of `Stacks.BlowupTwistUnit.exists_isIso_comparison_blowUp`, so the
discrepancy `a` that `π` carries is cancelled and the composite does not change.

## Main results

The elided prefix is `Stacks.BlowupTwistUnit`.

* `ChainTopFormData.exists_isIso_comparison`: the comparison at one blowup of the sequence.
* `ChainTopFormData.exists_topFormsTrace_eq`: the induction, for any `ChainTopFormData`.
* `exists_topFormsTrace_eq_baseIsoOfTopForms_inv`: **[Stacks, Tag 0B4T]**, over a regular local
  base of dimension two with the family `ω_X` constructed.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
-/

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Duality
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.ResolutionOfSurfaces

universe u

namespace Stacks.BlowupTwistUnit

section Induction

variable {S₀ S : Scheme.{u}} [IsNoetherian S] {p : S ⟶ S₀} {r : ℕ} {T : Set S}
  {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules}

/-- **The comparison at one blowup of the sequence, with an invertible discrepancy**:
`Stacks.BlowupTwistUnit.exists_isIso_comparison_blowUp` with its side conditions supplied from the
sequence, as in `Stacks.BlowupTwistUnit.ChainTopFormData.pushforwardHom`. -/
theorem ChainTopFormData.exists_isIso_comparison (D : ChainTopFormData p r T ω)
    {W : Scheme.{u}} {h : W ⟶ S} (hc : PointBlowupChain S T W h) (w : W)
    (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T) :
    haveI := compactSpace_of_pointBlowupChain hc
    haveI := quasiSeparatedSpace_of_pointBlowupChain hc
    haveI := compactSpace_of_pointBlowupChain (hc.step w hw hwT)
    haveI := quasiSeparatedSpace_of_pointBlowupChain (hc.step w hw hwT)
    ∃ (π : (quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).obj
        (singleQuasiCoherent
          (hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h))
          (D.isQuasicoherent_hull (hc.step w hw hwT)) 0) ⟶
      singleQuasiCoherent (hullForms p (r : ℤ) h) (D.isQuasicoherent_hull hc) 0)
      (a : hullForms p (r : ℤ) h ⟶ hullForms p (r : ℤ) h), IsIso a ∧
      (DerivedCategory.singleFunctor W.Modules 0).map
          (formsToPushforwardHull (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) (h ≫ p)
            ((AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h) ≫ p) (by simp) (r : ℤ)) ≫
        singleToDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) _ ≫
          π.hom =
      (DerivedCategory.singleFunctor W.Modules 0).map
        ((toReflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) (r : ℤ))).1 ≫ a) := by
  haveI := compactSpace_of_pointBlowupChain hc
  haveI := quasiSeparatedSpace_of_pointBlowupChain hc
  haveI := compactSpace_of_pointBlowupChain (hc.step w hw hwT)
  haveI := quasiSeparatedSpace_of_pointBlowupChain (hc.step w hw hwT)
  haveI := D.isCoherent_base
  haveI := D.isFiniteLocallyFreeOfRank_base
  haveI := isNoetherian_of_pointBlowupChain hc
  haveI := isLocallyNoetherian_of_pointBlowupChain hc
  have hWs := (isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hc
    D.isIntegralRegularSurface).1
  haveI := hWs.isIntegral
  haveI := isCoherent_relativeDifferentials_of_pointBlowupChain p hc
  haveI := isCoherent_pullback_relativeDifferentials_blowUpToBase p h w hw
  haveI := isCoherent_relativeDifferentials_blowUpToBase_comp p h w hw
  obtain ⟨V, hV, hVr⟩ :=
    exists_open_isFiniteLocallyFreeOfRank_over_relativeDifferentials_of_pointBlowupChain
      p r D.isIntegralRegularSurface hc
  haveI := hVr
  obtain ⟨U, hU, hU1, hU2⟩ := exists_open_isFiniteLocallyFreeOfRank_over_pointBlowup p h r w hw
    (exists_ne_of_topologicalKrullDim_eq_two w hWs.topologicalKrullDim_eq) V hV
  haveI := hU1
  haveI := hU2
  haveI : (Scheme.Hom.relativeDifferentials
      ((AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h) ≫ p)).IsCoherent := by
    rw [Category.assoc]
    infer_instance
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        ((AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h) ≫ p)).over U) r := by
    rw [Category.assoc]
    exact hU1
  exact exists_isIso_comparison_blowUp hWs.isRegular hWs.topologicalKrullDim_eq w hw
    (D.ringKrullDim_stalk hc w hw hwT) p h r V hV _ (Category.assoc _ _ _) U hU
    (nonempty_hullFormsPullbackBranch hWs.isRegular hWs.topologicalKrullDim_eq w hw
      (D.ringKrullDim_stalk hc w hw hwT) p h r U hU).some
    (D.isQuasicoherent_hull (hc.step w hw hwT)) (D.isQuasicoherent_hull hc) _

/-- **The induction of [Stacks, Tag 0B4T]**: at every stage of the sequence there is
`φ : (Ω^r_{X/S₀})^{**} ⟶ ω_X` whose composite `Ω^r_{S/S₀} ⟶ ω_S` — pull back the top forms to
`X`, apply `φ`, take the trace of `ω_X` back to `S` — is the given identification. -/
theorem ChainTopFormData.exists_topFormsTrace_eq (D : ChainTopFormData p r T ω)
    {X : Scheme.{u}} {f : X ⟶ S} (hf : PointBlowupChain S T X f) :
    ∃ φ : hullForms p (r : ℤ) f ⟶ ω X f, D.topFormsTrace hf φ = D.baseIso.inv := by
  induction hf with
  | refl =>
    haveI : IsIso (toReflexiveHull
        (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ))).1 :=
      (isReflexive_iff_isIso_toReflexiveHull _).mp D.isReflexive_base
    haveI := compactSpace_of_pointBlowupChain (PointBlowupChain.refl (X := S) (T := T))
    haveI := quasiSeparatedSpace_of_pointBlowupChain (PointBlowupChain.refl (X := S) (T := T))
    exact exists_topFormsTraceAux_id_eq p (r : ℤ) (ω S (𝟙 S))
      (D.isQuasicoherent_dualizing PointBlowupChain.refl)
      (D.isQuasicoherent_hull PointBlowupChain.refl) (D.normalized PointBlowupChain.refl)
      D.baseIso.inv
  | @step W h hh w hw hwT ih =>
    obtain ⟨φ, hφ⟩ := ih
    obtain ⟨π, a, ha, hπ⟩ := D.exists_isIso_comparison hh w hw hwT
    haveI := ha
    exact ⟨_, (D.topFormsTrace_step hh w hw hwT (inv a ≫ φ) π a hπ).trans
      (by rw [IsIso.hom_inv_id_assoc, hφ])⟩

end Induction

/-! ### Over a regular local base -/

section RegularLocal

variable {S₀ S : Scheme.{u}} [IsAffine S] [AlgebraicGeometry.IsNoetherian S]
  [IsRegularLocalRing Γ(S, ⊤)]

/-- **Stacks Project, Tag 0B4T.** Let `A` be a regular local ring of dimension two and `A₀ ⊆ A` a
subring with `Ω_{A/A₀}` free of rank `r`, and set `ω_A = Ω^r_{A/A₀}`. If `f : X ⟶ Spec A` is the
result of a sequence of blowups in closed points then there is a map

`φ_X : (Ω^r_{X/A₀})^{**} ⟶ ω_X`

extending the given identification, `ω_X` being the dualizing module of `X` normalized relative
to `ω_A`.

*Extending the identification* is the equation

`(ChainTopFormData.ofTopForms hS T p r hdimA).topFormsTrace hf φ =
  (baseIsoOfTopForms hS T p r).inv`:

the composite

`Ω^r_{A/A₀} ⟶ f_*((Ω^r_{X/A₀})^{**}) ⟶ Rf_*((Ω^r_{X/A₀})^{**}[0]) ⟶ Rf_*(ω_X[0]) ⟶ ω_A`

— the pullback of top forms into the reflexive hull, then `Rf_*φ_X`, then the trace of `f`, the
counit of `Rf_* ⊣ f^×` at the normalization `ω_X[0] ≅ f^×(ω_A[0])` — is the identification
`ω_A ≅ Ω^r_{A/A₀}`. Over the open `U` of `Spec A` over which `f` is an isomorphism, which contains
the generic point, the pullback of forms is the isomorphism `Ω^r_{U/A₀} ≅ f_*Ω^r_{f⁻¹U/A₀}` and the
trace is the identification of `f_*ω_X` with `ω_A` that `f` induces, so the equation says that
`φ_X` restricted to `f⁻¹U` is the given identification transported along `f`. The equation is about
`φ_X` itself, not about a map built from it up to a unit: the right-hand side is the identification
of `ω_A` with `Ω^r_{A/A₀}`, on the nose.

The hypotheses are the tag's: `S` is an integral regular surface whose ring of global sections is
a regular local ring of dimension two, and `Ω_{S/S₀}` is coherent and free of rank `r`. The family
`ω_X` is `chainDualizingModuleOfTopForms`, constructed; the identification is
`baseIsoOfTopForms`, proved; the normalization is `normalizedChainDualizingModule`, proved.

The proof is the induction of the source (`ChainTopFormData.exists_topFormsTrace_eq`). At each
blowup the comparison `Rb_*((Ω^r_{X'})^{**}[0]) ⟶ (Ω^r_X)^{**}[0]` is built from the dichotomy of
[Stacks, Tag 0B3T], and the automorphism of `(Ω^r_X)^{**}` it differs by from the canonical map is
proved invertible and cancelled (`exists_isIso_comparison_blowUp`); the isomorphism
`Rb_*((Ω^r_{X'})^{**}) ≅ (Ω^r_X)^{**}` the source's proof asserts is not used. -/
@[stacks 0B4T "the map phi_X from the reflexive hull of the top relative differential forms of X \
over A_0 to the dualizing module omega_X normalized relative to omega_A = Omega^r_{A/A_0}, for \
every sequence of blowups in closed points of a regular local base of dimension two, extending \
the given identification: pulling the top forms back to X, applying phi_X and taking the trace of \
omega_X back to Spec A gives the identification omega_A = Omega^r_{A/A_0}. The family omega_X, the \
identification and the normalization are constructed from the hypotheses of the tag, and at each \
blowup the automorphism by which the direct-image comparison differs from the canonical map is \
proved invertible"]
theorem exists_topFormsTrace_eq_baseIsoOfTopForms_inv
    (hS : IsIntegralRegularSurface S) (T : Set S) (p : S ⟶ S₀) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials p).IsCoherent]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials p) r]
    (hdimA : ringKrullDim Γ(S, ⊤) = 2)
    {X : Scheme.{u}} {f : X ⟶ S} (hf : PointBlowupChain S T X f) :
    ∃ φ : hullForms p (r : ℤ) f ⟶ chainDualizingModuleOfTopForms hS T p r X f,
      (ChainTopFormData.ofTopForms hS T p r hdimA).topFormsTrace hf φ =
        (baseIsoOfTopForms hS T p r).inv :=
  (ChainTopFormData.ofTopForms hS T p r hdimA).exists_topFormsTrace_eq hf

end RegularLocal

end Stacks.BlowupTwistUnit
