module

public import StacksFrontier.AlgebraicGeometry.FormsTrace.Glue
public import StacksFrontier.AlgebraicGeometry.FormsTrace.LocalTrace
public import StacksFrontier.AlgebraicGeometry.FormsTrace.Rule

/-!
# The trace maps on forms of a finite syntomic morphism

Let `f : Y ⟶ X` be a finite syntomic morphism of schemes. Over every framed affine open `U` of
`X` (`Stacks.FormsTrace.IsFramedOpen`: `Γ(Y, f⁻¹U)` is zero or has a basis with first vector `1`
whose structure constants come from a syntomic-good chart of the universal family) the trace maps
`Stacks.FormsTrace.localTrace` are defined, and they commute with restriction
(`Stacks.FormsTrace.localTrace_restrict`). The framed opens form a basis of the topology
(`Stacks.FormsTrace.isBasis_framedOpens`), so these maps glue to maps of `𝒪_X`-modules

`Θ^p_{Y/X} : f_*Ω^p_{Y/ℤ} ⟶ Ω^p_{X/ℤ}`,

the maps of Stacks, Lemma 0FLB and Proposition 0FLC.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.formsTrace`: the maps `Θ^p_{Y/X}`.
* `AlgebraicGeometry.formsTraceRule`: the rule `f ↦ Θ_{Y/X}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.absoluteFormsSectionsEquiv_formsTrace_app`: on a framed open the
  sections of `Θ^p_{Y/X}` are the local trace maps.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]

/-- The framed opens of `f`, as an index type. -/
abbrev FramedOpen := {U : X.Opens // Stacks.FormsTrace.IsFramedOpen f U}

omit [IsFinite f] in
variable {f} in
/-- A framed open is affine. -/
theorem FramedOpen.isAffineOpen (U : f.FramedOpen) : IsAffineOpen U.1 := U.2.1

/-- The local trace maps on the framed opens, as a family indexed by the framed opens. -/
abbrev framedLocalTrace (U : f.FramedOpen) (p : ℕ) :
    letI := (f.app U.1).hom.toAlgebra
    ⋀[Γ(Y, f ⁻¹ᵁ U.1)]^p Ω[Γ(Y, f ⁻¹ᵁ U.1)⁄ℤ] →ₗ[Γ(X, U.1)] ⋀[Γ(X, U.1)]^p Ω[Γ(X, U.1)⁄ℤ] :=
  Stacks.FormsTrace.localTrace f U.1 p

/-- The local trace maps commute with restriction between framed opens. -/
theorem localTrace_isRestrictionCompatible [Flat f] [LocallyOfFinitePresentation f] :
    IsRestrictionCompatible f (fun U : f.FramedOpen => U.1) (framedLocalTrace f) :=
  fun U V h p η => Stacks.FormsTrace.localTrace_restrict f ⟨U.1, U.isAffineOpen⟩
    ⟨V.1, V.isAffineOpen⟩ h U.2 V.2 p η

/-- The framed opens form a basis. -/
theorem isBasis_range_framedOpen [Flat f] [LocallyOfFinitePresentation f] (hf : Syntomic f) :
    Opens.IsBasis (Set.range fun U : f.FramedOpen => U.1) := by
  rw [Subtype.range_coe_subtype]
  exact Stacks.FormsTrace.isBasis_framedOpens f hf

/-- **The trace maps on forms of a finite syntomic morphism**
`Θ^p_{Y/X} : f_*Ω^p_{Y/ℤ} ⟶ Ω^p_{X/ℤ}` (Stacks, Lemma 0FLB). -/
def formsTrace (hf : Syntomic f) (p : ℕ) :
    (Scheme.Modules.pushforward f).obj (absoluteDifferentialForms Y p) ⟶
      absoluteDifferentialForms X p :=
  haveI := AlgebraicGeometry.flat hf
  haveI := AlgebraicGeometry.locallyOfFinitePresentation hf
  formsMapOfBasis f (fun U : f.FramedOpen => U.isAffineOpen) (framedLocalTrace f)
    (localTrace_isRestrictionCompatible f) (isBasis_range_framedOpen f hf) p

/-- **On a framed open, the sections of `Θ^p_{Y/X}` are the local trace maps**, read through the
identifications of sections with forms. -/
theorem absoluteFormsSectionsEquiv_formsTrace_app (hf : Syntomic f) (p : ℕ) (U : f.FramedOpen)
    (η : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ U.1)) :
    absoluteFormsSectionsEquiv X U.isAffineOpen p ((f.formsTrace hf p).app U.1 η) =
      framedLocalTrace f U p (absoluteFormsSectionsEquiv Y (U.isAffineOpen.preimage f) p η) := by
  have := AlgebraicGeometry.flat hf
  have := AlgebraicGeometry.locallyOfFinitePresentation hf
  have key := absoluteFormsSectionsEquiv_formsMapOfBasis_app f
    (fun U : f.FramedOpen => U.isAffineOpen) (framedLocalTrace f)
    (localTrace_isRestrictionCompatible f) (isBasis_range_framedOpen f hf) p U η
  convert key using 2
  rfl

/-- **Over an affine open with a frame, `Θ^p_{Y/X}` is the trace of the frame**: for an affine
open `U` of `X` and any frame `F` of `Γ(Y, f⁻¹U)` over `Γ(X, U)` (a basis with first vector `1`
and a syntomic-good chart of the universal family), the sections of `Θ^p_{Y/X}` over `U` are the
trace maps `F.trace` of the framed algebra (`Stacks.FormsTrace.ChartFrame.trace`), read through
the identifications of sections with forms. -/
theorem absoluteFormsSectionsEquiv_formsTrace_app_of_frame (hf : Syntomic f) (p : ℕ)
    {U : X.Opens} (hU : IsAffineOpen U) {d : ℕ} [NeZero d]
    (F : letI := (f.app U).hom.toAlgebra
      Stacks.FormsTrace.ChartFrame d Γ(X, U) Γ(Y, f ⁻¹ᵁ U))
    (η : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) :
    letI := (f.app U).hom.toAlgebra
    absoluteFormsSectionsEquiv X hU p ((f.formsTrace hf p).app U η) =
      F.trace p (absoluteFormsSectionsEquiv Y (hU.preimage f) p η) := by
  let := (f.app U).hom.toAlgebra
  have h := absoluteFormsSectionsEquiv_formsTrace_app f hf p
    ⟨U, hU, Or.inr ⟨d, inferInstance, ⟨F⟩⟩⟩ η
  have h2 : Stacks.FormsTrace.frameTrace Γ(X, U) Γ(Y, f ⁻¹ᵁ U) p =
      F.trace p := Stacks.FormsTrace.frameTrace_eq ⟨d, F⟩ p
  rw [← h2]
  convert h using 2

/-- `formsTrace` unfolded: the glued map of the local trace maps on the framed opens. -/
theorem formsTrace_eq (hf : Syntomic f) (p : ℕ) :
    haveI := AlgebraicGeometry.flat hf
    haveI := AlgebraicGeometry.locallyOfFinitePresentation hf
    f.formsTrace hf p = formsMapOfBasis f (fun U : f.FramedOpen => U.isAffineOpen)
      (framedLocalTrace f) (localTrace_isRestrictionCompatible f)
      (isBasis_range_framedOpen f hf) p :=
  rfl

/-- **The trace maps on forms form a map of de Rham complexes** `f_*Ω^•_{Y/ℤ} → Ω^•_{X/ℤ}`
(Stacks, Proposition 0FLC): on the sections over any open `U` of `X`, `Θ^{p+1}(d η) = d(Θ^p η)`. -/
theorem formsTrace_deRhamComplex_d (hf : Syntomic f) (p : ℕ) (U : X.Opens)
    (η : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) :
    (f.formsTrace hf (p + 1)).app U
        ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op (f ⁻¹ᵁ U)) η) =
      (X.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op U) ((f.formsTrace hf p).app U η) := by
  have := AlgebraicGeometry.flat hf
  have := AlgebraicGeometry.locallyOfFinitePresentation hf
  exact formsMapOfBasis_deRhamComplex_d f _ _ _ _
    (fun U => let := (f.app U.1).hom.toAlgebra
      Stacks.FormsTrace.commutesWithD_frameTrace
        (Stacks.FormsTrace.framed_or_subsingleton_of_isFramedOpen f U.2)) p U η

/-- **The trace maps on forms are linear over the forms of `X`** (Stacks, Proposition 0FLC (2)):
on the sections over any open `U` of `X`, `Θ^{q+p}(f^*ω ∧ η) = ω ∧ Θ^p(η)`. The products are
those of the graded algebras `Ω^•_{·/ℤ}` in degree `(q : ℤ) + p`, transported to degree
`((q + p : ℕ) : ℤ)` by `eqToHom`. -/
theorem formsTrace_mul_absoluteFormsPullback (hf : Syntomic f) (q p : ℕ) (U : X.Opens)
    (ω : Γ(absoluteDifferentialForms X q, U)) (η : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) :
    (f.formsTrace hf (q + p)).app U
        ((eqToHom (congrArg (absoluteDifferentialForms Y) (Nat.cast_add q p).symm)).val.app
          (op (f ⁻¹ᵁ U)) (((absoluteDifferentialFormsAlgebra Y).mul q p).app (op (f ⁻¹ᵁ U))
            (f.absoluteFormsPullback q U ω) η)) =
      (eqToHom (congrArg (absoluteDifferentialForms X) (Nat.cast_add q p).symm)).val.app (op U)
        (((absoluteDifferentialFormsAlgebra X).mul q p).app (op U) ω
          ((f.formsTrace hf p).app U η)) := by
  have := AlgebraicGeometry.flat hf
  have := AlgebraicGeometry.locallyOfFinitePresentation hf
  exact formsMapOfBasis_mul_absoluteFormsPullback f _ _ _ _
    (fun U => let := (f.app U.1).hom.toAlgebra
      Stacks.FormsTrace.isWedgeLinear_frameTrace
        (Stacks.FormsTrace.framed_or_subsingleton_of_isFramedOpen f U.2)) q p U ω η

/-- **Property (1) of Stacks, Lemma 0FLB for the trace maps on forms**: on the sections over any
open `U` of `X`, `Θ^p(b · f^*ω) = Trace_f(b) · ω`. -/
theorem formsTrace_smul_absoluteFormsPullback (hf : Syntomic f) (p : ℕ) (U : X.Opens)
    (b : Γ(Y, f ⁻¹ᵁ U)) (ω : Γ(absoluteDifferentialForms X p, U)) :
    haveI := AlgebraicGeometry.flat hf
    haveI := AlgebraicGeometry.locallyOfFinitePresentation hf
    (f.formsTrace hf p).app U (b • f.absoluteFormsPullback p U ω) =
      (show Γ(X, U) from (f.finiteTrace).app U b) • ω := by
  have := AlgebraicGeometry.flat hf
  have := AlgebraicGeometry.locallyOfFinitePresentation hf
  exact formsMapOfBasis_smul_absoluteFormsPullback f _ _ _ _
    (fun U => by
      let := (f.app U.1).hom.toAlgebra
      intro _ _
      exact Stacks.FormsTrace.isFormsTrace_frameTrace
        (Stacks.FormsTrace.framed_or_subsingleton_of_isFramedOpen f U.2)) p U b ω

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

/-- **The rule of trace maps on forms** `f ↦ Θ_{Y/X}`. -/
def formsTraceRule : FormsTraceRule.{u} := fun _ _ f _ hf p => f.formsTrace hf p

/-- **The rule of trace maps on forms satisfies condition (1) of Stacks, Lemma 0FLB.** -/
theorem formsTraceRule_isTrace : formsTraceRule.{u}.IsTrace :=
  fun _ _ f _ hf p U b ω => f.formsTrace_smul_absoluteFormsPullback hf p U b ω

end AlgebraicGeometry

end
