module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupCanDualSituation
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupDualSituation
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageFibreDimension.GeneralDimension
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Pullback

/-!
# The Situation of Tag 0GA6 at the fibre dimension of the blowup

The witnesses `blowupSituationOf`, `blowupModuleSituationOf`, `blowupTwistedModuleSituationOf`
and `blowupDualSituationOf` carry as their field `d` a Čech vanishing bound of the blowup
(`exists_forall_subsingleton_blowupH`), which is not the source's `d`. [Stacks, Tag 0GA6] takes
`d = d(S)`, the maximum of the dimensions of the fibres of `p : X ⟶ Spec(A)`, and derives the
vanishing `Hⁱ(X, ℱ) = 0` for coherent `ℱ` and `i > d` from [Stacks, Tags 02V7, 01XK].

This file does the same. For any `d` bounding the dimensions of the fibres of `p`:

* `subsingleton_blowupHmod_of_fiber_le` is the vanishing, from the affine-base form of
  [Stacks, Tag 02V7]
  (`FibreDimension.isZero_rightDerived_moduleGlobalSections_of_forall_fiber_dim_le`), `p` being
  proper (`Stacks.Blowup.instIsProperToSpec`);
* the sheaves the witnesses take cohomology of are coherent: `𝒪_X(q)` is invertible because the
  Rees algebra is generated in degree one (`degreeOneCover_reesGrading`), so the twisted pullback
  `𝒪_X(q) ⊗ p^*Ñ` of a finite `A`-module is coherent (`isCoherent_twistedGeometricFactor_obj`),
  and so are `𝒪_{Yₙ}(q)`, `𝒢` and `ℱ`;
* `blowupSituationOfFiberLE`, …, `blowupDualSituationOfFiberLE` are the four witnesses with `d`
  replaced by the fibre-dimension bound.

`Stacks.LocalCohomology.UniformityIII.blowupSituationAt` of
`BitUniformityIII/FibreDimensionBound.lean` is the Situation at the one bound `d = d(S)`,
`fibreDim I`; the witnesses here take every bound `d` of the fibre dimensions as a hypothesis
`hfib`, which is what the corrected Tag 0GAD of `BitUniformityIII/BlowupExtension.lean` is stated
over, and they extend the twisted-pullback witnesses `blowupModuleSituationOf`, … rather than the
`thickeningPullback` ones of `BitUniformityIII/BlowupModuleSituation.lean`.

## References

* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- **`Hⁱ(X, ℱ) = 0` for a coherent `ℱ` on the blowup and `i` above a bound for the dimensions of
the fibres of `p : X ⟶ Spec(A)`**: [Stacks, Tag 02V7] over the affine base `Spec(A)`, which is
where the source's "`Hⁱ(X, ℱ) = 0` for `i > d`" comes from. -/
theorem subsingleton_blowupHmod_of_fiber_le {d : ℕ}
    (hfib : ∀ s, topologicalKrullDim ((Stacks.Blowup.toSpec I).fiber s) ≤ (d : WithBot ℕ∞))
    (F : (blowupScheme I).Modules) [F.IsCoherent] {i : ℕ} (hi : d < i) :
    Subsingleton (blowupHmod I i F) :=
  subsingleton_blowupHmod I i F <| AddCommGrpCat.subsingleton_of_isZero <|
    (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      (R := (blowupScheme I).ringCatSheaf) (U := ⊤) i F).mp <|
    AlgebraicGeometry.FibreDimension.isZero_rightDerived_moduleGlobalSections_of_forall_fiber_dim_le
      (A := A) (Stacks.Blowup.toSpec I) hfib F hi

omit [IsNoetherianRing A] in
/-- **`Proj` of the Rees algebra is covered by the standard opens of degree-one elements**,
because the Rees algebra is generated in degree one over its degree-zero part. -/
theorem degreeOneCover_reesGrading :
    Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.DegreeOneCover (Stacks.Blowup.reesGrading I) :=
  AlgebraicGeometry.Proj.iSup_basicOpen_eq_top' (Stacks.Blowup.reesGrading I)
    (fun f : Stacks.Blowup.reesGrading I 1 => (f : reesAlgebra I))
    (fun f => ⟨1, f.2⟩)
    (by rw [Subtype.range_coe_subtype]
        exact Stacks.Blowup.adjoin_reesGradingZero_reesGrading_one_eq_top I)

/-- The blowup of `Spec A` along `I` is locally Noetherian, being locally of finite type over the
Noetherian scheme `Spec A`. -/
instance : IsLocallyNoetherian (blowupScheme I) :=
  LocallyOfFiniteType.isLocallyNoetherian (Stacks.Blowup.toSpec I)

/-- **`p^*Ñ` is coherent for a finite `A`-module `N`.** -/
theorem isCoherent_pullback_tilde (N : ModuleCat.{u} A) [Module.Finite A N] :
    ((Scheme.Modules.pullback (Stacks.Blowup.toSpec I)).obj
      (AlgebraicGeometry.tilde N)).IsCoherent :=
  Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- **A coherent module tensored with `𝒪_X(q)` is coherent**: `𝒪_X(q)` is invertible. -/
private theorem isCoherent_tensor_blowUpTwist {B : Type u} [CommRing B] (J : Ideal B)
    (F : (blowupScheme J).Modules) [F.IsCoherent] (q : ℤ) :
    (F ⊗ Stacks.Blowup.blowUpTwist J q).IsCoherent := by
  have := Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf
    (Stacks.Blowup.reesGrading J) (degreeOneCover_reesGrading J) q
  exact AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible (blowupScheme J) F
    (Stacks.Blowup.blowUpTwist J q)

/-- **`𝒪_X(q) ⊗ p^*Ñ` is coherent for a finite `A`-module `N`**: `𝒪_X(q)` is invertible. -/
theorem isCoherent_twistedGeometricFactor_obj (q : ℤ) (N : ModuleCat.{u} A) [Module.Finite A N] :
    ((Stacks.Blowup.twistedGeometricFactor I q).obj N).IsCoherent := by
  have := isCoherent_pullback_tilde I N
  exact @Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso _ _ _ _ _
    (RingedSpaceThickening.tensorSheafCommIso (blowupScheme I).toRingedSpace
      (Stacks.Blowup.blowUpTwist I q)
      ((Scheme.Modules.pullback (Stacks.Blowup.toSpec I)).obj (AlgebraicGeometry.tilde N)))
    (isCoherent_tensor_blowUpTwist I _ q)

/-- **`𝒪_X(q)` is coherent.** -/
theorem isCoherent_blowupTwist (q : ℕ) : (blowupTwist I q).IsCoherent := by
  have := Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit (X := blowupScheme I)
  exact @Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso _ _ _ _ _
    (λ_ (blowupTwist I q)).symm
    (isCoherent_tensor_blowUpTwist I (SheafOfModules.unit (blowupScheme I).ringCatSheaf) q)

/-- **`𝒪_{Yₙ}(q)` is coherent**: it is the twisted pullback of `A ⧸ Iⁿ`. -/
theorem isCoherent_thickeningTwist (n q : ℕ) : (thickeningTwist I n q).IsCoherent := by
  have : Module.Finite A (ModuleCat.of A (A ⧸ I ^ n)) :=
    inferInstanceAs (Module.Finite A (A ⧸ I ^ n))
  have hc := isCoherent_twistedGeometricFactor_obj I (q : ℤ) (ModuleCat.of A (A ⧸ I ^ n))
  exact @Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso _ _ _ _ _
    (twistedPullbackQuotientIsoThickeningTwist I n q).symm hc

section PresentationSheaves

variable {S : ShortComplex (ModuleCat.{u} A)} (q : ℤ)

/-- **`𝒢` is coherent** when the middle term of the presentation is finite: it is a
quasi-coherent subsheaf of the coherent `(𝒪_{Yₙ})^{⊕r}(q)`. -/
theorem isCoherent_twistedPullbackImage [Module.Finite A S.X₂] :
    (twistedPullbackImage I q (S := S)).IsCoherent :=
  @Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_mono_of_isQuasicoherent _ _ _ _ _
    (isCoherent_twistedGeometricFactor_obj I q S.X₂) (S.map (twistedPullbackFunctor I q)).iCycles
    (inferInstanceAs (Mono (S.map (twistedPullbackFunctor I q)).iCycles))

/-- **`ℱ` is coherent** when the first term of the presentation is finite: it is a
quasi-coherent subsheaf of the coherent `p^*K(q)`. -/
theorem isCoherent_twistedPullbackSupported [Module.Finite A S.X₁] :
    (twistedPullbackSupported I q (S := S)).IsCoherent :=
  @Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_mono_of_isQuasicoherent _ _ _ _ _
    (isCoherent_twistedGeometricFactor_obj I q S.X₁)
    (kernel.ι (S.map (twistedPullbackFunctor I q)).toCycles)
    (inferInstanceAs (Mono (kernel.ι (S.map (twistedPullbackFunctor I q)).toCycles)))

end PresentationSheaves

/-! ### The witnesses at a vanishing bound -/

section BoundWitnesses

variable {d : ℕ}
  (hvan : ∀ (F : (blowupScheme I).Modules) [F.IsCoherent] {i : ℕ}, d < i →
    Subsingleton (blowupHmod I i F))

include hvan

/-- **The Situation of [Stacks, Tag 0GA6] on the blowup, with `d` any degree above which the
cohomology of every coherent module on `X` vanishes**: `blowupSituationOf` with its field `d`
replaced by that bound. The fibre-dimension bound of the source is one such degree
(`subsingleton_blowupHmod_of_fiber_le`), and `blowupSituationOfFiberLE` is this witness at it; a
bound coming from a covering of `X` by affine opens ([Stacks, Tag 071L]) is another. -/
def blowupSituationOfBound (q₀ : ℕ) (h : IsBaseThreshold I q₀) : Situation A I :=
  { blowupSituationOf I q₀ h with
    d := d
    base_vanishing := fun i q hi _ hq => h.1 i q hi hq
    div_vanishing_gt := fun n _ q hi =>
      haveI := isCoherent_thickeningTwist I n q
      hvan (thickeningTwist I n q) hi
    amb_vanishing_gt := fun _ q hi =>
      haveI := isCoherent_blowupTwist I q
      hvan (blowupTwist I q) hi }

/-- The vanishing degree `d` of `blowupSituationOfBound` is the given bound `d`. -/
theorem blowupSituationOfBound_d (q₀ : ℕ) (h : IsBaseThreshold I q₀) :
    (blowupSituationOfBound I hvan q₀ h).d = d := rfl

/-- The threshold `q₀` of `blowupSituationOfBound` is the given `q₀`. -/
theorem blowupSituationOfBound_q₀ (q₀ : ℕ) (h : IsBaseThreshold I q₀) :
    (blowupSituationOfBound I hvan q₀ h).q₀ = q₀ := rfl

/-- The `ModuleSituation` on the blowup at a vanishing bound. -/
def blowupModuleSituationOfBound (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ) (hcn : c ≤ n) :
    ModuleSituation A I n c :=
  { blowupModuleSituationOf I q₀ h n c hcn with
    toSituation := blowupSituationOfBound I hvan q₀ h
    vanishing_H := fun M _ q hi =>
      haveI : Module.Finite (A ⧸ I ^ n) M.1 := M.2.1
      haveI := finite_resModule I n M.1
      haveI := isCoherent_twistedGeometricFactor_obj I q (resModule I n M.1)
      hvan _ hi
    vanishing_HG := fun M _ q hi =>
      haveI : Module.Finite (A ⧸ I ^ n) (ModuleCat.of (A ⧸ I ^ n)
          (Fin (blowupANCPres I n c M).rank → A ⧸ I ^ n)) :=
        inferInstanceAs (Module.Finite (A ⧸ I ^ n) (Fin _ → A ⧸ I ^ n))
      haveI : Module.Finite A (blowupPresShortComplex I n c M).X₂ :=
        finite_resModule I n (ModuleCat.of (A ⧸ I ^ n)
          (Fin (blowupANCPres I n c M).rank → A ⧸ I ^ n))
      haveI := isCoherent_twistedPullbackImage I q (S := blowupPresShortComplex I n c M)
      hvan _ hi
    vanishing_HF := fun M _ q hi =>
      haveI : Module.Finite (A ⧸ I ^ n) (blowupANCPres I n c M).kernel :=
        (blowupANCPres I n c M).kernelANC.2.1
      haveI : Module.Finite A (blowupPresShortComplex I n c M).X₁ :=
        finite_resModule I n (blowupANCPres I n c M).kernel
      haveI := isCoherent_twistedPullbackSupported I q (S := blowupPresShortComplex I n c M)
      hvan _ hi }

/-- The `TwistedModuleSituation` on the blowup at a vanishing bound. -/
def blowupTwistedModuleSituationOfBound (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ)
    (hcn : c ≤ n) : TwistedModuleSituation A I n c :=
  { blowupTwistedModuleSituationOf I q₀ h n c hcn with
    toModuleSituation := blowupModuleSituationOfBound I hvan q₀ h n c hcn }

/-- **The `DualSituation` on the blowup at a vanishing bound.** -/
def blowupDualSituationOfBound (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ) (hcn : c ≤ n) :
    DualSituation A I n c :=
  { blowupDualSituationOf I q₀ h n c hcn with
    toTwistedModuleSituation := blowupTwistedModuleSituationOfBound I hvan q₀ h n c hcn }

/-- The vanishing degree `d` of `blowupDualSituationOfBound` is the given bound `d`. -/
theorem blowupDualSituationOfBound_d (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ)
    (hcn : c ≤ n) : (blowupDualSituationOfBound I hvan q₀ h n c hcn).d = d := rfl

/-- The threshold `q₀` of `blowupDualSituationOfBound` is the given `q₀`. -/
theorem blowupDualSituationOfBound_q₀ (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ)
    (hcn : c ≤ n) : (blowupDualSituationOfBound I hvan q₀ h n c hcn).q₀ = q₀ := rfl

end BoundWitnesses

/-! ### The witnesses at a fibre-dimension bound -/

section Witnesses

variable {d : ℕ}
  (hfib : ∀ s, topologicalKrullDim ((Stacks.Blowup.toSpec I).fiber s) ≤ (d : WithBot ℕ∞))

include hfib

/-- **The Situation of [Stacks, Tag 0GA6] on the blowup, with `d` a bound for the dimensions of
the fibres of `p`**: `blowupSituationOf` with its field `d` replaced by the fibre-dimension bound,
the vanishing above `d` being [Stacks, Tag 02V7] through `subsingleton_blowupHmod_of_fiber_le`. -/
def blowupSituationOfFiberLE (q₀ : ℕ) (h : IsBaseThreshold I q₀) : Situation A I :=
  blowupSituationOfBound I (fun F _ _ hi => subsingleton_blowupHmod_of_fiber_le I hfib F hi) q₀ h

/-- The vanishing degree `d` of `blowupSituationOfFiberLE` is the given bound `d` on the dimensions
of the fibres. -/
theorem blowupSituationOfFiberLE_d (q₀ : ℕ) (h : IsBaseThreshold I q₀) :
    (blowupSituationOfFiberLE I hfib q₀ h).d = d := rfl

/-- The threshold `q₀` of `blowupSituationOfFiberLE` is the given `q₀`. -/
theorem blowupSituationOfFiberLE_q₀ (q₀ : ℕ) (h : IsBaseThreshold I q₀) :
    (blowupSituationOfFiberLE I hfib q₀ h).q₀ = q₀ := rfl

/-- The `ModuleSituation` on the blowup at a fibre-dimension bound. -/
def blowupModuleSituationOfFiberLE (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ) (hcn : c ≤ n) :
    ModuleSituation A I n c :=
  blowupModuleSituationOfBound I (fun F _ _ hi => subsingleton_blowupHmod_of_fiber_le I hfib F hi)
    q₀ h n c hcn

/-- The `TwistedModuleSituation` on the blowup at a fibre-dimension bound. -/
def blowupTwistedModuleSituationOfFiberLE (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ)
    (hcn : c ≤ n) : TwistedModuleSituation A I n c :=
  blowupTwistedModuleSituationOfBound I
    (fun F _ _ hi => subsingleton_blowupHmod_of_fiber_le I hfib F hi) q₀ h n c hcn

/-- **The `DualSituation` on the blowup at a fibre-dimension bound.** -/
def blowupDualSituationOfFiberLE (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ) (hcn : c ≤ n) :
    DualSituation A I n c :=
  blowupDualSituationOfBound I (fun F _ _ hi => subsingleton_blowupHmod_of_fiber_le I hfib F hi)
    q₀ h n c hcn

/-- The vanishing degree `d` of `blowupDualSituationOfFiberLE` is the given bound `d` on the
dimensions of the fibres. -/
theorem blowupDualSituationOfFiberLE_d (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ) (hcn : c ≤ n) :
    (blowupDualSituationOfFiberLE I hfib q₀ h n c hcn).d = d := rfl

/-- The threshold `q₀` of `blowupDualSituationOfFiberLE` is the given `q₀`. -/
theorem blowupDualSituationOfFiberLE_q₀ (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ)
    (hcn : c ≤ n) : (blowupDualSituationOfFiberLE I hfib q₀ h n c hcn).q₀ = q₀ := rfl

end Witnesses

end Stacks.LocalCohomology.UniformityIII

end
