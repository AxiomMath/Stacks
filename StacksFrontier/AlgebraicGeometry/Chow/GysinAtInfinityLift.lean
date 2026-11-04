module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Modification
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLine
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VeryWeakBivariantCriterion
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestrictionVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Infinity
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequenceOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.SectionPresentation

/-!
# The cap operation of the Gysin class at infinity

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, and let `b : W ⟶ 𝐏¹_X` be a proper morphism which is an isomorphism over the
standard affine chart `𝐀¹_X`, with `i_∞ : W_∞ ⟶ W` the inverse image of the divisor at infinity.
Stacks 0F9J constructs a canonical class `C ∈ A⁰(W_∞ ⟶ X)` by `C ∩ α = i_∞^* β` for any class
`β` on `W ×_X T` restricting over `𝐀¹_X` to the flat pullback of `α`. This file carries out that
construction on every test scheme `T ⟶ X`, with nothing taken as data: lifts exist, two lifts
differ by a class supported at infinity, and the Gysin map at infinity kills such classes.
The statement of the tag is `Stacks.Chow.GysinAtInfinityData` in
`StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity`; its canonical inhabitant, whose cap
operation is `Stacks.Chow.gysinCapAtInfinity`, is `Stacks.Chow.gysinAtInfinityData` of
`StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityClass`.

## Main definitions

* `Stacks.Chow.modificationInfinityModule`, `Stacks.Chow.modificationInfinitySection` — the
  invertible module `𝒪(D_∞)` of the divisor at infinity and its canonical section, pulled back to
  a base change `W ×_X T`; their zero scheme is `W_∞ ×_X T`
  (`Stacks.Chow.zeroScheme_modificationInfinitySection`), identified with it by
  `Stacks.Chow.modificationInfinityZeroSchemeIso`.
* `Stacks.Chow.modificationAffineChart` — the inverse image `b^{-1}(𝐀¹_X) ×_X T` of the affine
  chart, an open subscheme of `W ×_X T` whose projection to `T` is flat of relative dimension one.
* `Stacks.Chow.IsModificationLift` — a class `β ∈ A_{k+1}(W ×_X T)` lifts `α ∈ A_k(T)` when it
  restricts over `𝐀¹_X` to the flat pullback of `α`.
* `Stacks.Chow.modificationInfinityGysin` — the Gysin map `i_∞^*` of the divisor at infinity.
* `Stacks.Chow.gysinCapAtInfinity` — **Stacks 0F9J, the cap operation**
  `C ∩ - : A_k(T) ⟶ A_k(W_∞ ×_X T)`, `α ↦ i_∞^* β` for a chosen lift `β` of `α`.

## Main results

* `Stacks.Chow.zeroScheme_modificationInfinitySection`,
  `Stacks.Chow.isTrivial_modificationInfinityModule` — the fibre at infinity of every base change
  is the zero scheme of a section of an invertible module whose restriction to it is trivial.
* `Stacks.Chow.exists_isModificationLift` — every class has a lift (Stacks 02RC, 02RX).
* `Stacks.Chow.exists_sub_eq_of_isModificationLift` — two lifts differ by a class supported on the
  fibre at infinity (Stacks 02RX).
* `Stacks.Chow.modificationInfinityGysin_chowPushforward_eq_zero` — the Gysin map at infinity
  kills classes supported on the fibre at infinity (Remark 0B6Z).
* `Stacks.Chow.gysinCapAtInfinity_eq_of_isModificationLift` — **Stacks 0F9J, independence of
  the lift**: `C ∩ α = i_∞^* β` for every lift `β` of `α`.

## Implementation notes

A lift of `α` exists but is not unique, so `Stacks.Chow.gysinCapAtInfinity` evaluates `i_∞^*` on
the lift `Classical.choose` picks; `Stacks.Chow.gysinCapAtInfinity_eq_of_isModificationLift`
shows that the value does not depend on that choice, which is what the source calls canonical.
The additivity of the operation is a consequence: a sum of lifts is a lift of the sum.

The cap operation `Stacks.Chow.gysinCapOfLift` of
`StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity` takes the lift and the zero-scheme
presentation as data; the operation here constructs both.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0F93](https://stacks.math.columbia.edu/tag/0F93)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The affine chart of the relative projective line -/

section AffineChart

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The morphism of affine lines `𝐀¹_X ⟶ 𝐀¹_S` induced by `f`. -/
def affineLineOverMap : affineLineOver X ⟶ affineLineOver S :=
  pullback.lift (pullback.fst _ _ ≫ f) (pullback.snd _ _) (terminal.hom_ext _ _)

/-- The morphism of affine lines `𝐀¹_X ⟶ 𝐀¹_S` is `f` on the base. -/
@[reassoc (attr := simp)]
theorem affineLineOverMap_fst :
    affineLineOverMap f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f :=
  pullback.lift_fst _ _ _

/-- The morphism of affine lines `𝐀¹_X ⟶ 𝐀¹_S` preserves the coordinate. -/
@[reassoc (attr := simp)]
theorem affineLineOverMap_snd : affineLineOverMap f ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The chart `𝐀¹_X ⟶ 𝐏¹_X` lies over `X`. -/
@[reassoc (attr := simp)]
theorem projectiveLineAffineChart_fst :
    projectiveLineAffineChart f ≫ pullback.fst f (relativeProjectiveLine S ↘ S) =
      pullback.fst (terminal.from X) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) :=
  pullback.lift_fst _ _ _

/-- The chart `𝐀¹_X ⟶ 𝐏¹_X` is the chart `𝐀¹_S ⟶ 𝐏¹_S` on the second factor. -/
theorem projectiveLineAffineChart_snd :
    projectiveLineAffineChart f ≫ pullback.snd f (relativeProjectiveLine S ↘ S) =
      affineLineOverMap f ≫ affineChart S := by
  refine (pullback.lift_snd _ _ _).trans (pullback.hom_ext ?_ ?_)
  · rw [pullback.lift_fst, affineChart, Category.assoc, pullback.lift_fst, affineLineOverMap_fst]
  · rw [pullback.lift_snd, affineChart, Category.assoc, pullback.lift_snd,
      affineLineOverMap_snd_assoc]

/-- `𝐀¹_X` is the base change of `𝐀¹_S` along `f`. -/
theorem isPullback_affineLineOverMap :
    IsPullback (affineLineOverMap f)
      (pullback.fst (terminal.from X) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))))
      (pullback.fst (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))))
      f := by
  refine IsPullback.of_right ?_ (affineLineOverMap_fst f) (IsPullback.of_hasPullback _ _).flip
  rw [affineLineOverMap_snd, show f ≫ terminal.from S = terminal.from X from
    terminal.hom_ext _ _]
  exact (IsPullback.of_hasPullback _ _).flip

/-- The chart `𝐀¹_X ⟶ 𝐏¹_X` is the base change of the chart `𝐀¹_S ⟶ 𝐏¹_S` along the second
projection of `𝐏¹_X = X ×_S 𝐏¹_S`. -/
theorem isPullback_affineLineOverMap_projectiveLineAffineChart :
    IsPullback (affineLineOverMap f) (projectiveLineAffineChart f) (affineChart S)
      (pullback.snd f (relativeProjectiveLine S ↘ S)) := by
  refine IsPullback.of_bot ?_ (projectiveLineAffineChart_snd f).symm
    (IsPullback.of_hasPullback f (relativeProjectiveLine S ↘ S)).flip
  rw [projectiveLineAffineChart_fst, affineChart_comp]
  exact isPullback_affineLineOverMap f

/-- The complement of the chart `𝐀¹_X ⊆ 𝐏¹_X` is the image of the infinity section. -/
theorem compl_range_projectiveLineAffineChart :
    (Set.range (projectiveLineAffineChart f).base)ᶜ = Set.range (infinitySection f).base := by
  rw [range_fst_of_isPullback (isPullback_affineLineOverMap_projectiveLineAffineChart f).flip,
    range_fst_of_isPullback (isPullback_infinitySection f), ← Set.preimage_compl]
  exact congrArg _ (compl_range_affineChart S)

/-- The projection `Spec ℤ[T] ⟶ Spec ℤ`, written against the terminal scheme. -/
theorem terminalFrom_specPolynomial_eq :
    terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : CommRingCat.of (ULift.{u} ℤ) →+*
        Polynomial (CommRingCat.of (ULift.{u} ℤ)))) ≫
        terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
  terminal.hom_ext _ _

/-- The projection `Spec ℤ[T] ⟶ Spec ℤ` is flat. -/
instance flat_terminalFrom_specPolynomial :
    Flat (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) := by
  have : IsIso (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
    isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal _
  have : Flat (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) := inferInstance
  have hF : ∀ R : CommRingCat.{u},
      Flat (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) :=
    fun _ ↦ inferInstance
  have := hF (CommRingCat.of (ULift.{u} ℤ))
  rw [terminalFrom_specPolynomial_eq]
  exact Flat.comp _ _

/-- The projection `Spec ℤ[T] ⟶ Spec ℤ` is locally of finite type. -/
instance locallyOfFiniteType_terminalFrom_specPolynomial :
    LocallyOfFiniteType (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) := by
  have : IsIso (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
    isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal _
  have : LocallyOfFiniteType (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
    inferInstance
  have hL : ∀ R : CommRingCat.{u},
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) :=
    fun _ ↦ inferInstance
  have := hL (CommRingCat.of (ULift.{u} ℤ))
  rw [terminalFrom_specPolynomial_eq]
  infer_instance

/-- The projection `Spec ℤ[T] ⟶ Spec ℤ` has relative dimension one. -/
theorem relativeDimension_terminalFrom_specPolynomial :
    RelativeDimension (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) 1 := by
  have : IsIso (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
    isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal _
  have sq : IsPullback (𝟙 _) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : CommRingCat.of (ULift.{u} ℤ) →+*
        Polynomial (CommRingCat.of (ULift.{u} ℤ)))))
      (inv (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ))))) :=
    IsPullback.of_horiz_isIso ⟨by rw [terminalFrom_specPolynomial_eq]; simp⟩
  have hL : ∀ R : CommRingCat.{u},
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) :=
    fun _ ↦ inferInstance
  have := hL (CommRingCat.of (ULift.{u} ℤ))
  exact RelativeDimension.of_isPullback sq (relativeDimension_specMap_C _)

end AffineChart

/-! ### The two distinguished divisors of `𝐏¹_S`, pulled back -/

section LineDivisors

attribute [local instance] lineZeroDivisor_isEffectiveCartierDivisor
  lineInfinityDivisor_isEffectiveCartierDivisor

variable {S Y : Scheme.{u}} (φ : Y ⟶ relativeProjectiveLine S)

/-- The invertible module `𝒪(D_∞)` of the divisor at infinity of `𝐏¹_S`, pulled back along
`φ : Y ⟶ 𝐏¹_S`. -/
abbrev lineInfinityModule : Y.Modules :=
  (Scheme.Modules.pullback φ).obj (Stacks.Divisors.divisorSheaf (lineInfinityDivisor S))

/-- The pullback of `𝒪(D_∞)` along `φ` is invertible. -/
instance isInvertible_lineInfinityModule :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      (lineInfinityModule φ) :=
  Stacks.ChernCap42.isInvertible_sheafObj_modulePullback _ _

/-- The canonical section of `𝒪(D_∞)`, pulled back along `φ`. -/
abbrev lineInfinityModuleSection : Γ(lineInfinityModule φ, ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections φ _
    (Stacks.Divisors.divisorSheafGlobalSection (lineInfinityDivisor S))

/-- The zero scheme of the pulled-back canonical section of `𝒪(D_∞)` is the inverse image of
`D_∞`. -/
theorem zeroScheme_lineInfinityModuleSection :
    Stacks.Divisors.zeroScheme Y (lineInfinityModule φ) (lineInfinityModuleSection φ) =
      (lineInfinityDivisor S).comap φ := by
  rw [← zeroScheme_lineInfinityDivisor]
  exact Stacks.Divisors.zeroScheme_pullback _ _ _

/-- The pulled-back `𝒪(D_∞)` restricts trivially to its zero scheme (Stacks 0F93). -/
theorem isTrivial_lineInfinityModule :
    AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme Y (lineInfinityModule φ)
        (lineInfinityModuleSection φ)).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme Y (lineInfinityModule φ)
        (lineInfinityModuleSection φ)).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme Y (lineInfinityModule φ)
        (lineInfinityModuleSection φ)).subschemeι).obj (lineInfinityModule φ)) := by
  refine Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections φ _ _ ?_
  rw [zeroScheme_lineInfinityDivisor]
  exact isTrivial_pullback_divisorSheaf_lineInfinityDivisor S

/-- The invertible module `𝒪(D₀)` of the zero divisor of `𝐏¹_S`, pulled back along `φ`. -/
abbrev lineZeroModule : Y.Modules :=
  (Scheme.Modules.pullback φ).obj (Stacks.Divisors.divisorSheaf (lineZeroDivisor S))

/-- The pullback of `𝒪(D₀)` along `φ` is invertible. -/
instance isInvertible_lineZeroModule :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      (lineZeroModule φ) :=
  Stacks.ChernCap42.isInvertible_sheafObj_modulePullback _ _

/-- The canonical section of `𝒪(D₀)`, pulled back along `φ`. -/
abbrev lineZeroModuleSection : Γ(lineZeroModule φ, ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections φ _
    (Stacks.Divisors.divisorSheafGlobalSection (lineZeroDivisor S))

/-- The zero scheme of the pulled-back canonical section of `𝒪(D₀)` is the inverse image of
`D₀`. -/
theorem zeroScheme_lineZeroModuleSection :
    Stacks.Divisors.zeroScheme Y (lineZeroModule φ) (lineZeroModuleSection φ) =
      (lineZeroDivisor S).comap φ := by
  rw [← zeroScheme_lineZeroDivisor]
  exact Stacks.Divisors.zeroScheme_pullback _ _ _

/-- The pulled-back `𝒪(D₀)` restricts trivially to its zero scheme (Stacks 0F93). -/
theorem isTrivial_lineZeroModule :
    AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme Y (lineZeroModule φ)
        (lineZeroModuleSection φ)).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme Y (lineZeroModule φ)
        (lineZeroModuleSection φ)).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme Y (lineZeroModule φ)
        (lineZeroModuleSection φ)).subschemeι).obj (lineZeroModule φ)) := by
  refine Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections φ _ _ ?_
  rw [zeroScheme_lineZeroDivisor]
  exact isTrivial_pullback_divisorSheaf_lineZeroDivisor S

end LineDivisors

/-! ### The divisor at infinity on a base change of the modification -/

section InfinityDivisor

variable {X S W T : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X)

/-- The morphism `W ×_X T ⟶ W ⟶ 𝐏¹_X`. -/
abbrev modificationBaseChangeToLine : modificationBaseChange f b g ⟶ projectiveLineProduct f :=
  pullback.fst (modificationProjection f b) g ≫ b

/-- **The base-changed fibre at infinity is the inverse image of the divisor at infinity.** The
square formed by `W_∞ ×_X T ⟶ W ×_X T`, the infinity section of `𝐏¹_X` and
`W ×_X T ⟶ 𝐏¹_X` is cartesian. -/
theorem isPullback_modificationInfinityBaseChange :
    IsPullback (modificationInfinityBaseChange f b g)
      (pullback.fst (modificationProjectionAtInfinity f b) g ≫
        pullback.snd b (infinitySection f))
      (modificationBaseChangeToLine f b g) (infinitySection f) := by
  have hleft : IsPullback (pullback.fst (modificationProjectionAtInfinity f b) g)
      (modificationInfinityBaseChange f b g) (modificationInclusionAtInfinity f b)
      (pullback.fst (modificationProjection f b) g) := by
    refine IsPullback.of_bot ?_ (modificationInfinityBaseChange_comp_fst f b g).symm
      (IsPullback.of_hasPullback (modificationProjection f b) g)
    rw [modificationInfinityBaseChange_comp_snd]
    exact IsPullback.of_hasPullback (modificationProjectionAtInfinity f b) g
  exact (hleft.paste_horiz (IsPullback.of_hasPullback b (infinitySection f)).flip).flip

/-- The base-changed inclusion at infinity is a closed immersion. -/
instance isClosedImmersion_modificationInfinityBaseChange :
    IsClosedImmersion (modificationInfinityBaseChange f b g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
    (isPullback_modificationInfinityBaseChange f b g).flip inferInstance

/-- The closed subscheme cut out by `W_∞ ×_X T ⟶ W ×_X T` is the inverse image of the divisor
at infinity. -/
theorem ker_modificationInfinityBaseChange :
    (modificationInfinityBaseChange f b g).ker =
      (infinitySection f).ker.comap (modificationBaseChangeToLine f b g) :=
  AlgebraicGeometry.ker_eq_comap_ker_of_isPullback (isPullback_modificationInfinityBaseChange f b g)

/-- The morphism `W ×_X T ⟶ 𝐏¹_X ⟶ 𝐏¹_S`. -/
abbrev modificationBaseChangeToRelativeLine :
    modificationBaseChange f b g ⟶ relativeProjectiveLine S :=
  modificationBaseChangeToLine f b g ≫ pullback.snd f (relativeProjectiveLine S ↘ S)

/-- **Stacks 0F93, pulled back.** The invertible module `𝒪(D_∞)` of the divisor at infinity of
`𝐏¹_S`, pulled back to `W ×_X T`. -/
abbrev modificationInfinityModule : (modificationBaseChange f b g).Modules :=
  lineInfinityModule (modificationBaseChangeToRelativeLine f b g)

/-- The canonical section of `𝒪(D_∞)`, pulled back to `W ×_X T`. -/
abbrev modificationInfinitySection : Γ(modificationInfinityModule f b g, ⊤) :=
  lineInfinityModuleSection (modificationBaseChangeToRelativeLine f b g)

/-- **Stacks 0F9J, the presentation of the fibre at infinity.** The zero scheme of the pulled-back
canonical section of `𝒪(D_∞)` is the base-changed fibre at infinity `W_∞ ×_X T ⊆ W ×_X T`. -/
theorem zeroScheme_modificationInfinitySection :
    Stacks.Divisors.zeroScheme (modificationBaseChange f b g) (modificationInfinityModule f b g)
        (modificationInfinitySection f b g) =
      (modificationInfinityBaseChange f b g).ker := by
  rw [zeroScheme_lineInfinityModuleSection, ker_modificationInfinityBaseChange,
    ker_infinitySection, ← Scheme.IdealSheafData.comap_comp]

/-- **Stacks 0F9J, the normal bundle at infinity is trivial.** The restriction of the pulled-back
`𝒪(D_∞)` to its zero scheme is trivial. -/
theorem isTrivial_modificationInfinityModule :
    AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b g) (modificationInfinityModule f b g)
        (modificationInfinitySection f b g)).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b g) (modificationInfinityModule f b g)
        (modificationInfinitySection f b g)).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
        (modificationInfinityModule f b g) (modificationInfinitySection f b g)).subschemeι).obj
        (modificationInfinityModule f b g)) :=
  isTrivial_lineInfinityModule _

/-- The identification of the zero scheme of the pulled-back canonical section with the
base-changed fibre at infinity `W_∞ ×_X T`. -/
def modificationInfinityZeroSchemeIso :
    (Stacks.Divisors.zeroScheme (modificationBaseChange f b g) (modificationInfinityModule f b g)
        (modificationInfinitySection f b g)).subscheme ≅
      pullback (modificationProjectionAtInfinity f b) g :=
  (isoSubschemeOfKer (modificationInfinityBaseChange f b g) _
    (zeroScheme_modificationInfinitySection f b g).symm).symm

/-- The identification of the zero scheme of the pulled-back canonical section with the
base-changed fibre at infinity, followed by the inclusion of that fibre, is the inclusion of the
zero scheme. -/
@[reassoc (attr := simp)]
theorem modificationInfinityZeroSchemeIso_hom_comp :
    (modificationInfinityZeroSchemeIso f b g).hom ≫ modificationInfinityBaseChange f b g =
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b g) (modificationInfinityModule f b g)
        (modificationInfinitySection f b g)).subschemeι := by
  rw [modificationInfinityZeroSchemeIso, Iso.symm_hom, Iso.inv_comp_eq,
    isoSubschemeOfKer_hom_subschemeι]

end InfinityDivisor

/-! ### The fibre over zero -/

section ZeroFibre

variable {X S W T : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X)

/-- The zero section of `𝐀¹_X ⟶ X`. -/
abbrev affineLineZeroSection (X : Scheme.{u}) : X ⟶ affineLineOver X :=
  affineLineConstantSection X integralAffineZeroSection

/-- The zero section of `𝐏¹_X` factors through the affine chart. -/
theorem affineLineZeroSection_comp_projectiveLineAffineChart :
    affineLineZeroSection X ≫ projectiveLineAffineChart f = zeroSection f := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, projectiveLineAffineChart_fst, zeroSection_comp_fst]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, projectiveLineAffineChart_snd, zeroSection_comp_snd]
    have h : affineLineZeroSection X ≫ affineLineOverMap f = f ≫ affineLineZeroSection S := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, affineLineOverMap_fst, Category.assoc]
        dsimp only [affineLineZeroSection, affineLineConstantSection]
        rw [pullback.lift_fst_assoc, pullback.lift_fst, Category.id_comp, Category.comp_id]
      · rw [Category.assoc, affineLineOverMap_snd, Category.assoc]
        dsimp only [affineLineZeroSection, affineLineConstantSection]
        rw [pullback.lift_snd, pullback.lift_snd, ← Category.assoc, terminal.comp_from]
    rw [← Category.assoc, h, Category.assoc, lineZeroSection_eq]

/-- **The fibre over zero is `X`.** When `b` is an isomorphism over `𝐀¹_X`, the projection
`W_0 = W ×_{𝐏¹_X} X ⟶ X` of the fibre over the zero section is an isomorphism, the zero section
factoring through `𝐀¹_X`. -/
theorem isIso_modificationFibreAtZeroProjection
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    IsIso (modificationFibreAtZeroProjection f b) := by
  have hl : IsPullback
      (pullback.lift (pullback.fst b (zeroSection f))
        (pullback.snd b (zeroSection f) ≫ affineLineZeroSection X) (by
          rw [pullback.condition, Category.assoc,
            affineLineZeroSection_comp_projectiveLineAffineChart]) :
        pullback b (zeroSection f) ⟶ pullback b (projectiveLineAffineChart f))
      (pullback.snd b (zeroSection f)) (pullback.snd b (projectiveLineAffineChart f))
      (affineLineZeroSection X) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback b (projectiveLineAffineChart f))
    rw [pullback.lift_fst, affineLineZeroSection_comp_projectiveLineAffineChart]
    exact IsPullback.of_hasPullback b (zeroSection f)
  exact hl.isIso_snd_of_isIso hA

/-- The section at zero lies over `X`. -/
theorem modificationSectionAtZero_comp_projection
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA) ≫
      modificationProjection f b = 𝟙 X := by
  rw [modificationSectionAtZero, Category.assoc, modificationProjection, ← Category.assoc
    (pullback.fst b (zeroSection f)), pullback.condition, Category.assoc, zeroSection_comp_fst,
    Category.comp_id, IsIso.inv_hom_id]

/-- The section at zero followed by `b` is the zero section of `𝐏¹_X`. -/
theorem modificationSectionAtZero_comp
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA) ≫ b =
      zeroSection f := by
  rw [modificationSectionAtZero, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/-- The section at zero is the base change of the zero section of `𝐏¹_X` along `b`. -/
theorem isPullback_modificationSectionAtZero
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    IsPullback (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))
      (𝟙 X) b (zeroSection f) := by
  have := isIso_modificationFibreAtZeroProjection f b hA
  have hsq : IsPullback (inv (modificationFibreAtZeroProjection f b)) (𝟙 X)
      (pullback.snd b (zeroSection f)) (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h := hsq.paste_horiz (IsPullback.of_hasPullback b (zeroSection f))
  rwa [Category.id_comp] at h

/-- **The base-changed section at zero is the base change of the zero section of `𝐏¹_X`.** -/
theorem isPullback_modificationSectionAtZeroBaseChange
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    IsPullback (modificationSectionAtZeroBaseChange f b
        (isIso_modificationFibreAtZeroProjection f b hA)
        (modificationSectionAtZero_comp_projection f b hA) g)
      g (modificationBaseChangeToLine f b g) (zeroSection f) := by
  have htop : IsPullback (modificationSectionAtZeroBaseChange f b
        (isIso_modificationFibreAtZeroProjection f b hA)
        (modificationSectionAtZero_comp_projection f b hA) g)
      g (pullback.fst (modificationProjection f b) g)
      (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA)) := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (modificationProjection f b) g).flip
    rw [modificationSectionAtZeroBaseChange_comp_snd,
      modificationSectionAtZero_comp_projection f b hA]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have h := htop.paste_vert (isPullback_modificationSectionAtZero f b hA)
  rwa [Category.comp_id] at h

/-- The base-changed section at zero is a closed immersion. -/
theorem isClosedImmersion_modificationSectionAtZeroBaseChange
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    IsClosedImmersion (modificationSectionAtZeroBaseChange f b
      (isIso_modificationFibreAtZeroProjection f b hA)
      (modificationSectionAtZero_comp_projection f b hA) g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
    (isPullback_modificationSectionAtZeroBaseChange f b g hA).flip inferInstance

/-- **The base-changed section at zero presents the pulled-back divisor `D_0`.** -/
theorem ker_modificationSectionAtZeroBaseChange
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    (modificationSectionAtZeroBaseChange f b (isIso_modificationFibreAtZeroProjection f b hA)
        (modificationSectionAtZero_comp_projection f b hA) g).ker =
      Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
        (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
        (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g)) := by
  rw [AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
      (isPullback_modificationSectionAtZeroBaseChange f b g hA),
    zeroScheme_lineZeroModuleSection, ker_zeroSection, ← Scheme.IdealSheafData.comap_comp]

end ZeroFibre

/-! ### The affine chart of a base change of the modification -/

section AffineChartBaseChange

variable {X S W T : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X)

/-- The inverse image `b^{-1}(𝐀¹_X) ×_X T` of the affine chart in `W ×_X T`. -/
abbrev modificationAffineChart : Scheme.{u} :=
  pullback (modificationBaseChangeToLine f b g) (projectiveLineAffineChart f)

/-- The open immersion `b^{-1}(𝐀¹_X) ×_X T ⟶ W ×_X T`. -/
abbrev modificationAffineChartι : modificationAffineChart f b g ⟶ modificationBaseChange f b g :=
  pullback.fst _ _

/-- The projection `b^{-1}(𝐀¹_X) ×_X T ⟶ T`. -/
abbrev modificationAffineChartProjection : modificationAffineChart f b g ⟶ T :=
  modificationAffineChartι f b g ≫ pullback.snd (modificationProjection f b) g

/-- The base-changed fibre at infinity is the complement of the chart `b^{-1}(𝐀¹_X) ×_X T`. -/
theorem range_modificationInfinityBaseChange :
    Set.range (modificationInfinityBaseChange f b g).base =
      (Set.range (modificationAffineChartι f b g).base)ᶜ := by
  rw [range_fst_of_isPullback (isPullback_modificationInfinityBaseChange f b g),
    range_fst_of_isPullback (IsPullback.of_hasPullback (modificationBaseChangeToLine f b g)
      (projectiveLineAffineChart f)), ← compl_range_projectiveLineAffineChart, Set.preimage_compl]

/-- **The chart over `𝐀¹_X` is an affine line over the test scheme.** When `b` is an isomorphism
over `𝐀¹_X`, the projection `b^{-1}(𝐀¹_X) ×_X T ⟶ T` is the base change of `𝐀¹_X ⟶ X`
along `T ⟶ X`. -/
theorem isPullback_modificationAffineChartProjection
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    IsPullback (pullback.snd (modificationBaseChangeToLine f b g) (projectiveLineAffineChart f))
      (modificationAffineChartProjection f b g)
      (pullback.fst (terminal.from X) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))))
      g := by
  let a : modificationAffineChart f b g ⟶ pullback b (projectiveLineAffineChart f) :=
    pullback.lift (modificationAffineChartι f b g ≫ pullback.fst (modificationProjection f b) g)
      (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
  have hleft : IsPullback a (modificationAffineChartι f b g)
      (pullback.fst b (projectiveLineAffineChart f))
      (pullback.fst (modificationProjection f b) g) := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback b (projectiveLineAffineChart f)).flip
    rw [pullback.lift_snd]
    exact (IsPullback.of_hasPullback _ _).flip
  have hvert := hleft.paste_vert (IsPullback.of_hasPullback (modificationProjection f b) g)
  have hiso : IsPullback (pullback.snd b (projectiveLineAffineChart f))
      (pullback.fst b (projectiveLineAffineChart f) ≫ modificationProjection f b)
      (pullback.fst (terminal.from X) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))))
      (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [← projectiveLineAffineChart_fst, ← Category.assoc, ← pullback.condition,
        Category.comp_id, Category.assoc]⟩
  have h := hvert.paste_horiz hiso
  rwa [pullback.lift_snd, Category.comp_id] at h

/-- The projection of the chart over `𝐀¹_X` to the test scheme is flat. -/
theorem flat_modificationAffineChartProjection
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    Flat (modificationAffineChartProjection f b g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
    (isPullback_modificationAffineChartProjection f b g hA) inferInstance

variable [IsProper b]

/-- The projection of the chart over `𝐀¹_X` to the test scheme has relative dimension one. -/
theorem relativeDimension_modificationAffineChartProjection
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    RelativeDimension (modificationAffineChartProjection f b g) 1 :=
  RelativeDimension.of_isPullback (isPullback_modificationAffineChartProjection f b g hA)
    (relativeDimension_affineLineOver_fst _)

end AffineChartBaseChange

/-! ### The cap operation of the class at infinity -/

section Construction

variable (C : ChowSituation.{u}) {X W T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)

/-- The structure morphism over the base of the chart `b^{-1}(𝐀¹_X) ×_X T`. -/
abbrev modificationAffineChartOver : modificationAffineChart f b g ⟶ C.S :=
  modificationAffineChartι f b g ≫ modificationBaseChangeOver f b g

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType g] in
/-- The projection of the chart over `𝐀¹_X` to the test scheme is a morphism over the base. -/
theorem modificationAffineChartProjection_over :
    modificationAffineChartProjection f b g ≫ g ≫ f = modificationAffineChartOver C f b g := by
  rw [Category.assoc, modificationBaseChange_snd_over]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType g] in
/-- The identification of the zero scheme presenting the base-changed fibre at infinity with that
fibre is a morphism over the base. -/
theorem modificationInfinityZeroSchemeIso_over :
    (modificationInfinityZeroSchemeIso f b g).hom ≫ modificationInfinityBaseChangeOver f b g =
      modificationZeroSchemeOver C f b g (modificationInfinityModule f b g)
        (modificationInfinitySection f b g) := by
  rw [← modificationInfinityBaseChange_over, modificationInfinityZeroSchemeIso_hom_comp_assoc]

/-- **Stacks 0F9J, the lifts.** A class `β ∈ A_{k+1}(W ×_X T)` *lifts* `α ∈ A_k(T)` when its
restriction to the chart `b^{-1}(𝐀¹_X) ×_X T`, the inverse image of the complement of the divisor
at infinity, is the flat pullback of `α` along the projection of the chart to `T`, which is flat
of relative dimension one because `b` is an isomorphism over `𝐀¹_X`. -/
def IsModificationLift (α : chowGroup C (g ≫ f) k)
    (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1)) : Prop :=
  haveI := flat_modificationAffineChartProjection f b g hA
  chowGroupRestrict C (modificationBaseChangeOver f b g) (modificationAffineChartOver C f b g)
      (modificationAffineChartι f b g) rfl (k + 1) β =
    flatPullbackChow C (modificationAffineChartOver C f b g) (g ≫ f)
      (modificationAffineChartProjection f b g) (modificationAffineChartProjection_over C f b g) 1
      (relativeDimension_modificationAffineChartProjection f b g hA) k
      (flatPullbackDescends C _ _ _ _ _ _ k) α

/-- **Stacks 0F9J, existence of lifts** (Stacks 02RC, 02RX): every class on the test scheme has
a lift, restriction of cycle classes to an open subscheme being surjective. -/
theorem exists_isModificationLift (α : chowGroup C (g ≫ f) k) :
    ∃ β, IsModificationLift C f b hA g k α β :=
  surjective_chowGroupRestrict C _ _ _ rfl (k + 1) _

/-- **Stacks 0F9J, two lifts differ by a class supported at infinity** (Stacks 02RX): if `β` and
`β'` both lift `α`, then `β - β'` is pushed forward from the base-changed fibre at infinity, the
complement of the chart over `𝐀¹_X`. -/
theorem exists_sub_eq_of_isModificationLift {α : chowGroup C (g ≫ f) k}
    {β β' : chowGroup C (modificationBaseChangeOver f b g) (k + 1)}
    (h : IsModificationLift C f b hA g k α β) (h' : IsModificationLift C f b hA g k α β') :
    ∃ γ : chowGroup C (modificationInfinityBaseChangeOver f b g) (k + 1),
      β - β' = chowPushforwardOfIsClosedImmersion C (modificationInfinityBaseChangeOver f b g)
        (modificationBaseChangeOver f b g) (modificationInfinityBaseChange f b g)
        (modificationInfinityBaseChange_over f b g) (k + 1) γ := by
  obtain ⟨γ, hγ⟩ := ((exact_chowPushforward_chowGroupRestrict C _ _ _ rfl (k + 1) _ _
    (modificationInfinityBaseChange_over f b g)
    (range_modificationInfinityBaseChange f b g)) (β - β')).1
    (by rw [map_sub, sub_eq_zero]; exact h.trans h'.symm)
  exact ⟨γ, hγ.symm⟩

/-- **The Gysin map at infinity**, `i_∞^* : A_{k+1}(W ×_X T) ⟶ A_k(W_∞ ×_X T)`: the Gysin map of
the pulled-back canonical section of `𝒪(D_∞)` (Stacks 02TO), read on `W_∞ ×_X T` through the
identification of its zero scheme. -/
def modificationInfinityGysin :
    chowGroup C (modificationBaseChangeOver f b g) (k + 1) →+
      chowGroup C (modificationInfinityBaseChangeOver f b g) k :=
  (chowPushforwardOfIso C (modificationZeroSchemeOver C f b g (modificationInfinityModule f b g)
      (modificationInfinitySection f b g)) (modificationInfinityBaseChangeOver f b g)
      (modificationInfinityZeroSchemeIso f b g).hom
      (modificationInfinityZeroSchemeIso_over C f b g) k).comp
    ((gysinSystemOfInvertible C).onChow (modificationBaseChangeOver f b g)
      (modificationInfinityModule f b g) (modificationInfinitySection f b g) k)

/-- **Remark 0B6Z at infinity.** The Gysin map at infinity kills every class supported on the
fibre at infinity, because the normal bundle of the divisor at infinity is trivial. -/
theorem modificationInfinityGysin_chowPushforward_eq_zero
    (γ : chowGroup C (modificationInfinityBaseChangeOver f b g) (k + 1)) :
    modificationInfinityGysin C f b g k
        (chowPushforwardOfIsClosedImmersion C (modificationInfinityBaseChangeOver f b g)
          (modificationBaseChangeOver f b g) (modificationInfinityBaseChange f b g)
          (modificationInfinityBaseChange_over f b g) (k + 1) γ) = 0 := by
  rw [modificationInfinityGysin, AddMonoidHom.comp_apply,
    gysinSystemOfInvertible_onChow_eq_gysinChowOfInvertible,
    gysinChowOfInvertible_chowPushforwardOfIsClosedImmersion_eq_zero C _ k _ _
      (isTrivial_modificationInfinityModule f b g) _ _ _
      (modificationInfinityZeroSchemeIso f b g).symm (by
        rw [Iso.symm_hom, Iso.inv_comp_eq, modificationInfinityZeroSchemeIso_hom_comp]),
    map_zero]

/-- **Stacks 0F9J, the Gysin images of two lifts agree.** -/
theorem modificationInfinityGysin_eq_of_isModificationLift {α : chowGroup C (g ≫ f) k}
    {β β' : chowGroup C (modificationBaseChangeOver f b g) (k + 1)}
    (h : IsModificationLift C f b hA g k α β) (h' : IsModificationLift C f b hA g k α β') :
    modificationInfinityGysin C f b g k β = modificationInfinityGysin C f b g k β' := by
  obtain ⟨γ, hγ⟩ := exists_sub_eq_of_isModificationLift C f b hA g k h h'
  rw [← sub_eq_zero, ← map_sub, hγ, modificationInfinityGysin_chowPushforward_eq_zero]

/-- Lifts are additive. -/
theorem IsModificationLift.add {α α' : chowGroup C (g ≫ f) k}
    {β β' : chowGroup C (modificationBaseChangeOver f b g) (k + 1)}
    (h : IsModificationLift C f b hA g k α β) (h' : IsModificationLift C f b hA g k α' β') :
    IsModificationLift C f b hA g k (α + α') (β + β') := by
  unfold IsModificationLift at h h' ⊢
  rw [map_add, map_add, h, h']

/-- The zero class lifts the zero class. -/
theorem isModificationLift_zero : IsModificationLift C f b hA g k 0 0 := by
  unfold IsModificationLift
  rw [map_zero, map_zero]

/-- **Stacks 0F9J, the cap operation.** `C ∩ - : A_k(T) ⟶ A_k(W_∞ ×_X T)`, `α ↦ i_∞^* β` for a
lift `β` of `α` (`Stacks.Chow.IsModificationLift`). A lift is chosen; by
`Stacks.Chow.gysinCapAtInfinity_eq_of_isModificationLift` the value is the same for every
lift, and that independence is what makes the operation additive. -/
@[stacks 0F9J "the cap operation of the class at infinity on a test scheme: i_∞^* of a lift"]
def gysinCapAtInfinity :
    chowGroup C (g ≫ f) k →+ chowGroup C (modificationInfinityBaseChangeOver f b g) k where
  toFun α := modificationInfinityGysin C f b g k (exists_isModificationLift C f b hA g k α).choose
  map_zero' := by
    rw [modificationInfinityGysin_eq_of_isModificationLift C f b hA g k
      (exists_isModificationLift C f b hA g k 0).choose_spec
      (isModificationLift_zero C f b hA g k), map_zero]
  map_add' α α' := by
    rw [modificationInfinityGysin_eq_of_isModificationLift C f b hA g k
      (exists_isModificationLift C f b hA g k (α + α')).choose_spec
      ((exists_isModificationLift C f b hA g k α).choose_spec.add C f b hA g k
        (exists_isModificationLift C f b hA g k α').choose_spec), map_add]

/-- The value of the cap operation on a class, computed on the chosen lift. -/
theorem gysinCapAtInfinity_apply (α : chowGroup C (g ≫ f) k) :
    gysinCapAtInfinity C f b hA g k α =
      modificationInfinityGysin C f b g k (exists_isModificationLift C f b hA g k α).choose :=
  rfl

/-- **Stacks 0F9J, independence of the chosen lift.** The cap operation is `i_∞^* β` for *every*
lift `β` of `α`: two lifts differ by a class supported on the fibre at infinity (Stacks 02RX), and
the Gysin map at infinity kills such classes because the normal bundle of the divisor at infinity
is trivial (Remark 0B6Z). -/
@[stacks 0F9J "independence of the chosen lift: C ∩ α = i_∞^* β for every lift β of α"]
theorem gysinCapAtInfinity_eq_of_isModificationLift (α : chowGroup C (g ≫ f) k)
    (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1))
    (hβ : IsModificationLift C f b hA g k α β) :
    gysinCapAtInfinity C f b hA g k α = modificationInfinityGysin C f b g k β :=
  modificationInfinityGysin_eq_of_isModificationLift C f b hA g k
    (exists_isModificationLift C f b hA g k α).choose_spec hβ

end Construction

end Stacks.Chow

end
