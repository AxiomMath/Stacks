module

public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.LevelCompatibility
public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.PullbackCoherence
public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.ProjComparisonTwist
public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.FiberInvertible
public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.FiberAmple
public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.ProjFlat
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistFinitePresentation

/-!
# The algebraization of a polarized tower

For a polarized tower `(X_n ⟶ Spec R_n, ℒ_n)` and the cut `d₀` of [Stacks, Tag 0D4F], let
`B = lim A_n` be the graded inverse limit of the graded rings of global sections of the truncated
section algebras, `R = lim Γ(Spec R_n, 𝒪)` and `X = Proj_{Spec R}(B̃) ≅ Proj B`, with
`ℒ = 𝒪_X(1)`. This file proves that `X ⟶ Spec R` is proper, flat and of finite presentation,
that `ℒ` is invertible and ample, and assembles the identifications `X_n ≅ X ×_{Spec R} Spec R_n`
and `ℒ_n ≅ ℒ|_{X_n}` with their compatibilities.

## Main definitions

* `Stacks.PolarizedAlgebraization.PolarizedTower.levelInclusion`: `X_n ⟶ X`.
* `Stacks.PolarizedAlgebraization.PolarizedTower.levelTwistIso`: `ℒ|_{X_n} ≅ ℒ_n`.

## References

* [Stacks Project, Tag 0D4T](https://stacks.math.columbia.edu/tag/0D4T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.ProjectiveDeformation
open Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily
open Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily.AdmissibleDeformation
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open Stacks.Ample (IsAmple IsInvertibleModule)
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.PolarizedAlgebraization

/-- **Compatibility of identifications of inverse images with a transition**: for
`j₁ = i ≫ j₂`, the identification `e₁ : j₁^* ℒ ⟶ 𝒩₁` is the identification `e₂ : j₂^* ℒ ⟶ 𝒩₂`
pulled back along `i`, followed by `pol : i^* 𝒩₂ ⟶ 𝒩₁`. -/
def IsCompatibleIdentification {X₁ X₂ Y : Scheme.{u}} (i : X₁ ⟶ X₂) (j₁ : X₁ ⟶ Y) (j₂ : X₂ ⟶ Y)
    (hj : i ≫ j₂ = j₁) (L : Y.Modules) {N₁ : X₁.Modules} {N₂ : X₂.Modules}
    (e₁ : (Scheme.Modules.pullback j₁).obj L ⟶ N₁) (e₂ : (Scheme.Modules.pullback j₂).obj L ⟶ N₂)
    (pol : (Scheme.Modules.pullback i).obj N₂ ⟶ N₁) : Prop :=
  (Scheme.Modules.pullbackComp i j₂).hom.app L ≫ (Scheme.Modules.pullbackCongr hj).hom.app L ≫ e₁ =
    (Scheme.Modules.pullback i).map e₂ ≫ pol

section Generic

variable {P : PolarizedFamily.{u}} {D₁ D₂ : P.AdmissibleDeformation}
  (φ : AdmissibleDeformation.Hom D₁ D₂) (d₀ : ℕ) (hd₀ : 0 < d₀)
  (hiso : ∀ n : ℤ, IsIso ((algebraPullbackHom φ d₀ hd₀).app n))
  {S : Scheme.{u}} {𝓑 : SheafGradedAlgebra S} {g₁ : D₁.S' ⟶ S} {g₂ : D₂.S' ⟶ S}
  (ψ₁ : SheafGradedAlgebraHom (𝓑.pullback g₁) (D₁.truncatedSectionAlgebra d₀ hd₀))
  (ψ₂ : SheafGradedAlgebraHom (𝓑.pullback g₂) (D₂.truncatedSectionAlgebra d₀ hd₀))
  (hψ₁ : ∀ n : ℤ, IsIso (ψ₁.app n)) (hψ₂ : ∀ n : ℤ, IsIso (ψ₂.app n))

/-- **The identification `(r ≫ c)^* 𝒪(1) ⟶ 𝒩`** through the base change morphism `c` of `ψ`
and a map `θ : r^* 𝒪(1) ⟶ 𝒩`. -/
def twistIdentification {X S T : Scheme.{u}} {𝓑 : SheafGradedAlgebra S}
    {A : SheafGradedAlgebra T} {g : T ⟶ S} (ψ : SheafGradedAlgebraHom (𝓑.pullback g) A)
    (hψ : ∀ n : ℤ, IsIso (ψ.app n)) (r : X ⟶ (relativeProj A).scheme) {N : X.Modules}
    (θ : (Scheme.Modules.pullback r).obj (relativeTwist A 1) ⟶ N) :
    (Scheme.Modules.pullback (r ≫ baseChangeMor ψ hψ)).obj ((twistAlgebra 𝓑).piece 1) ⟶ N :=
  (Scheme.Modules.pullbackComp r (baseChangeMor ψ hψ)).inv.app ((twistAlgebra 𝓑).piece 1) ≫
    (Scheme.Modules.pullback r).map (twistComparisonOne ψ hψ) ≫ θ

/-- `twistIdentification` of an isomorphism is an isomorphism. -/
theorem isIso_twistIdentification {X S T : Scheme.{u}} {𝓑 : SheafGradedAlgebra S}
    {A : SheafGradedAlgebra T} {g : T ⟶ S} (ψ : SheafGradedAlgebraHom (𝓑.pullback g) A)
    (hψ : ∀ n : ℤ, IsIso (ψ.app n)) (r : X ⟶ (relativeProj A).scheme) {N : X.Modules}
    (θ : (Scheme.Modules.pullback r).obj (relativeTwist A 1) ⟶ N) (hθ : IsIso θ) :
    IsIso (twistIdentification ψ hψ r θ) := by
  have := isIso_twistComparisonOne ψ hψ
  exact @IsIso.comp_isIso' _ _ _ _ _ _ _
    (inferInstanceAs (IsIso ((Scheme.Modules.pullbackComp r (baseChangeMor ψ hψ)).app
      ((twistAlgebra 𝓑).piece 1)).inv))
    (@IsIso.comp_isIso' _ _ _ _ _ _ _ (Functor.map_isIso _ _) hθ)

/-- **The identifications of twists through `ψ₁` and `ψ₂` are compatible with a morphism of
admissible deformations**, when `ψ₁` is the transition after `ψ₂`: the identification
`(r'₁ ≫ c₁)^* 𝒪(1) ≅ ℒ'₁` is the identification `(r'₂ ≫ c₂)^* 𝒪(1) ≅ ℒ'₂` pulled back along the
morphism, followed by its polarization. -/
theorem twist_compat_of_hom
    (hc : projBaseChangeHom φ d₀ hd₀ hiso ≫ baseChangeMor ψ₂ hψ₂ = baseChangeMor ψ₁ hψ₁)
    (hg : φ.base ≫ g₂ = g₁)
    (hcompat : IsCompatTriple ψ₁ ψ₂ (algebraPullbackSheafHom φ d₀ hd₀) hg)
    (hext : ∀ (n : ℕ) {F : D₁.S'.Modules}
      (f f' : (Scheme.Modules.pullback g₁).obj (𝓑.piece (n : ℤ)) ⟶ F),
      (∀ b : Γ(𝓑.piece (n : ℤ), ⊤),
        f.app (g₁ ⁻¹ᵁ ⊤) (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp g₁
          (𝓑.piece (n : ℤ)) ⊤ b) =
        f'.app (g₁ ⁻¹ᵁ ⊤) (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp g₁
          (𝓑.piece (n : ℤ)) ⊤ b)) → f = f')
    (i : D₁.X' ⟶ D₂.X')
    (pol : (Scheme.Modules.pullback i).obj D₂.L' ⟶ D₁.L')
    (hpol : (⟨i, pol⟩ : Σ i' : D₁.X' ⟶ D₂.X', (Scheme.Modules.pullback i').obj D₂.L' ⟶ D₁.L') =
      ⟨φ.total, φ.polarization.hom⟩)
    (hj : i ≫ D₂.canonicalProjHom d₀ hd₀ ≫ baseChangeMor ψ₂ hψ₂ =
      D₁.canonicalProjHom d₀ hd₀ ≫ baseChangeMor ψ₁ hψ₁) :
    IsCompatibleIdentification i (D₁.canonicalProjHom d₀ hd₀ ≫ baseChangeMor ψ₁ hψ₁)
      (D₂.canonicalProjHom d₀ hd₀ ≫ baseChangeMor ψ₂ hψ₂) hj ((twistAlgebra 𝓑).piece 1)
      (twistIdentification ψ₁ hψ₁ (D₁.canonicalProjHom d₀ hd₀) (D₁.canonicalTwistMap d₀ hd₀))
      (twistIdentification ψ₂ hψ₂ (D₂.canonicalProjHom d₀ hd₀) (D₂.canonicalTwistMap d₀ hd₀))
      pol := by
  obtain ⟨rfl, h⟩ := Sigma.mk.inj hpol
  obtain rfl := eq_of_heq h
  have hτ := twistComparisonOne_eq_of ψ₁ ψ₂ (algebraPullbackSheafHom φ d₀ hd₀) hψ₁ hψ₂ hiso
    (projBaseChangeHom φ d₀ hd₀ hiso) (projBaseChangeTwistMap φ d₀ hd₀ hiso) rfl hc hg hcompat
    hext
  have key := pullback_two_factorizations φ.total (D₁.canonicalProjHom d₀ hd₀)
    (D₂.canonicalProjHom d₀ hd₀) (projBaseChangeHom φ d₀ hd₀ hiso)
    (baseChangeMor ψ₂ hψ₂) (baseChangeMor ψ₁ hψ₁) hc
    (canonicalProjHom_comp_projBaseChangeHom φ d₀ hd₀ hiso) ((twistAlgebra 𝓑).piece 1)
    (twistComparisonOne ψ₂ hψ₂) (projBaseChangeTwistMap φ d₀ hd₀ hiso)
    (D₁.canonicalTwistMap d₀ hd₀) (D₂.canonicalTwistMap d₀ hd₀) φ.polarization.hom
    (canonicalTwistMap_comp_polarization φ d₀ hd₀ hiso) hj
  rw [← hτ] at key
  exact key

end Generic

namespace PolarizedTower

variable (T : PolarizedTower.{u}) (d₀ : ℕ) (hd₀ : 0 < d₀) (hT : (T.tow d₀ hd₀).IsAdmissible)

/-- The structure morphism `Proj B ⟶ Spec R` of the graded inverse limit. -/
abbrev limitProjToBase :
    AlgebraicGeometry.Proj (T.tow d₀ hd₀).limGrading ⟶ Spec (limit T.globalRing) :=
  Proj.toSpecZero (T.tow d₀ hd₀).limGrading ≫
    Spec.map (CommRingCat.ofHom (algebraMap (limit T.globalRing : CommRingCat.{u})
      ((T.tow d₀ hd₀).limGrading 0)))

/-- `Proj_{Spec R}(B̃) ⟶ Spec R` is `Proj B ⟶ Spec R` through the comparison. -/
theorem toBase_eq :
    (relativeProj (T.limitAlgebra d₀ hd₀)).toBase =
      inv (projComparison (T.tow d₀ hd₀).limGrading) ≫ T.limitProjToBase d₀ hd₀ := by
  rw [IsIso.eq_inv_comp]
  exact projComparison_toBase _

include hT in
/-- **`Proj B ⟶ Spec R` is proper.** -/
theorem isProper_limitProjToBase : IsProper (T.limitProjToBase d₀ hd₀) := by
  have := (T.tow d₀ hd₀).finitePresentation_lim hT
  have := (T.tow d₀ hd₀).finite_limGrading hT 0
  exact AlgebraicGeometry.Proj.isProper_toSpecZero_comp_algebraMap _

include hT in
/-- **`Proj B ⟶ Spec R` is flat.** -/
theorem flat_limitProjToBase : Flat (T.limitProjToBase d₀ hd₀) := by
  have := (T.tow d₀ hd₀).projective_limGrading hT
  exact AlgebraicGeometry.Proj.flat_toSpecZero_comp_algebraMap _ fun d => inferInstance

include hT in
/-- **`Proj B ⟶ Spec R` is of finite presentation.** -/
theorem finitePresentation_limitProjToBase :
    _root_.AlgebraicGeometry.FinitePresentation (T.limitProjToBase d₀ hd₀) := by
  have := (T.tow d₀ hd₀).finitePresentation_lim hT
  exact AlgebraicGeometry.Proj.finitePresentation_toSpecZero_comp_algebraMap _

include hT in
/-- **`X = Proj_{Spec R}(B̃) ⟶ Spec R` is proper.** -/
theorem isProper_toBase : IsProper (relativeProj (T.limitAlgebra d₀ hd₀)).toBase := by
  have := T.isProper_limitProjToBase d₀ hd₀ hT
  rw [toBase_eq]
  infer_instance

include hT in
/-- **`X = Proj_{Spec R}(B̃) ⟶ Spec R` is flat.** -/
theorem flat_toBase : Flat (relativeProj (T.limitAlgebra d₀ hd₀)).toBase := by
  have := T.flat_limitProjToBase d₀ hd₀ hT
  rw [toBase_eq]
  infer_instance

include hT in
/-- **`X = Proj_{Spec R}(B̃) ⟶ Spec R` is of finite presentation.** -/
theorem finitePresentation_toBase :
    _root_.AlgebraicGeometry.FinitePresentation (relativeProj (T.limitAlgebra d₀ hd₀)).toBase := by
  obtain ⟨h1, h2, h3⟩ := T.finitePresentation_limitProjToBase d₀ hd₀ hT
  rw [toBase_eq]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- **`X_n ⟶ X`**: the identification `X_n ≅ Proj_{R_n}(𝒜'_n)` of [Stacks, Tag 0D4F] followed by
the base change morphism `c'_n`. -/
abbrev levelInclusion (n : ℕ) : T.X n ⟶ (relativeProj (T.limitAlgebra d₀ hd₀)).scheme :=
  (T.deformation n).canonicalProjHom d₀ hd₀ ≫ T.levelMor d₀ hd₀ hT n

/-- **`X_n = X ×_{Spec R} Spec R_n`.** -/
theorem isPullback_levelInclusion (n : ℕ) :
    IsPullback (T.levelInclusion d₀ hd₀ hT n) (T.f n)
      (relativeProj (T.limitAlgebra d₀ hd₀)).toBase (T.levelBase n) := by
  have h1 : IsPullback ((T.deformation n).canonicalProjHom d₀ hd₀) (T.f n)
      (relativeProj (T.alg d₀ hd₀ n)).toBase (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨((T.deformation n).canonicalProjHom_comp_toBase d₀ hd₀).trans
      (Category.comp_id _).symm⟩
  have h := h1.paste_horiz (T.isPullback_levelMor d₀ hd₀ hT n)
  rwa [Category.id_comp] at h

variable (hiso : ∀ (n : ℕ) (k : ℤ),
  IsIso ((AdmissibleDeformation.algebraPullbackHom (T.deformationHom n) d₀ hd₀).app k))

/-- `c'_n = φ_n ≫ c'_{n + 1}`, with the morphism of [Stacks, Tag 0D4F]. -/
theorem projBaseChangeHom_comp_levelMor (n : ℕ) :
    projBaseChangeHom (T.deformationHom n) d₀ hd₀ (hiso n) ≫ T.levelMor d₀ hd₀ hT (n + 1) =
      T.levelMor d₀ hd₀ hT n :=
  T.levelMor_comp d₀ hd₀ hT hiso n

include hiso in
/-- **The `X_n ⟶ X` are compatible with the transitions** `i_n : X_n ⟶ X_{n + 1}`. -/
theorem i_comp_levelInclusion (n : ℕ) :
    T.i n ≫ T.levelInclusion d₀ hd₀ hT (n + 1) = T.levelInclusion d₀ hd₀ hT n := by
  have h' : T.i n ≫ (T.deformation (n + 1)).canonicalProjHom d₀ hd₀ =
      (T.deformation n).canonicalProjHom d₀ hd₀ ≫
        projBaseChangeHom (T.deformationHom n) d₀ hd₀ (hiso n) :=
    (canonicalProjHom_comp_projBaseChangeHom (T.deformationHom n) d₀ hd₀ (hiso n)).symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ T.levelMor d₀ hd₀ hT (n + 1)) h').trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg ((T.deformation n).canonicalProjHom d₀ hd₀ ≫ ·)
    (T.projBaseChangeHom_comp_levelMor d₀ hd₀ hT hiso n)

variable (hθ : ∀ n : ℕ, IsIso ((T.deformation n).canonicalTwistMap d₀ hd₀))

/-- **`ℒ|_{X_n} ⟶ ℒ_n`**: the comparison of twists along `c'_n`, followed by the map `θ'` of
[Stacks, Tag 0D4F]; an isomorphism (`isIso_levelTwistMor`). -/
abbrev levelTwistMor (n : ℕ) :
    (Scheme.Modules.pullback (T.levelInclusion d₀ hd₀ hT n)).obj
        ((twistAlgebra (T.limitAlgebra d₀ hd₀)).piece 1) ⟶ (T.deformation n).L' :=
  twistIdentification (T.levelHom d₀ hd₀ n) (T.isIso_levelHom_app d₀ hd₀ hT n)
    ((T.deformation n).canonicalProjHom d₀ hd₀) ((T.deformation n).canonicalTwistMap d₀ hd₀)

include hθ in
/-- `ℒ|_{X_n} ⟶ ℒ_n` is an isomorphism. -/
theorem isIso_levelTwistMor (n : ℕ) : IsIso (T.levelTwistMor d₀ hd₀ hT n) :=
  isIso_twistIdentification _ _ _ _ (hθ n)

include hiso in
/-- **The identifications `ℒ|_{X_n} ≅ ℒ_n` are compatible with the `φ_n`.** -/
theorem levelTwistMor_compat (n : ℕ) :
    IsCompatibleIdentification (T.i n) (T.levelInclusion d₀ hd₀ hT n)
      (T.levelInclusion d₀ hd₀ hT (n + 1)) (T.i_comp_levelInclusion d₀ hd₀ hT hiso n)
      ((twistAlgebra (T.limitAlgebra d₀ hd₀)).piece 1)
      (T.levelTwistMor d₀ hd₀ hT n) (T.levelTwistMor d₀ hd₀ hT (n + 1)) (T.φ n).hom :=
  twist_compat_of_hom (T.deformationHom n) d₀ hd₀ (hiso n) (T.levelHom d₀ hd₀ n)
    (T.levelHom d₀ hd₀ (n + 1)) (T.isIso_levelHom_app d₀ hd₀ hT n)
    (T.isIso_levelHom_app d₀ hd₀ hT (n + 1)) (T.projBaseChangeHom_comp_levelMor d₀ hd₀ hT hiso n)
    (T.deformationHom_base_comp_levelBase n) (T.levelHom_compat d₀ hd₀ n)
    (fun m _ f f' h => T.levelBase_hom_ext d₀ hd₀ n m f f' h)
    (T.i n) (T.φ n).hom rfl (T.i_comp_levelInclusion d₀ hd₀ hT hiso n)

/-- `X_0 ⟶ Proj B`. -/
abbrev levelZeroInclusion : T.X 0 ⟶ AlgebraicGeometry.Proj (T.tow d₀ hd₀).limGrading :=
  T.levelInclusion d₀ hd₀ hT 0 ≫ inv (projComparison (T.tow d₀ hd₀).limGrading)

/-- **`X_0 = Proj B ×_{Spec R} Spec R_0`.** -/
theorem isPullback_levelZeroInclusion :
    IsPullback (T.levelZeroInclusion d₀ hd₀ hT) (T.f 0) (T.limitProjToBase d₀ hd₀)
      (T.levelBase 0) := by
  have h1 : IsPullback (inv (projComparison (T.tow d₀ hd₀).limGrading))
      (relativeProj (T.limitAlgebra d₀ hd₀)).toBase (T.limitProjToBase d₀ hd₀) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, toBase_eq]⟩
  have h := (T.isPullback_levelInclusion d₀ hd₀ hT 0).paste_horiz h1
  rwa [Category.comp_id] at h

include hT in
/-- `Spec R_0 ⟶ Spec R` is a closed immersion. -/
theorem isClosedImmersion_levelBase_zero : IsClosedImmersion (T.levelBase 0) := by
  refine IsClosedImmersion.spec_of_surjective _ ?_
  show Function.Surjective ((Scheme.ΓSpecIso (T.R.obj (op 0))).hom.hom ∘
    (limit.π T.globalRing (op 0)).hom)
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (T.R.obj (op 0))).hom).2.comp
    ((T.tow d₀ hd₀).surjective_limit_π_zero hT)

include hT in
/-- **Every closed point of `Spec R` lies on `Spec R_0`.** -/
theorem mem_range_levelBase_zero (s : Spec (limit T.globalRing)) (hs : IsClosed ({s} : Set _)) :
    s ∈ Set.range (T.levelBase 0) := by
  have hmax : s.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal s).mp hs
  obtain ⟨q, rfl⟩ := (T.tow d₀ hd₀).mem_range_comap_limit_π_zero hT s hmax
  refine ⟨PrimeSpectrum.comap (Scheme.ΓSpecIso (T.R.obj (op 0))).inv.hom q, ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  have h : (Scheme.ΓSpecIso (T.R.obj (op 0))).inv.hom ((T.levelMap 0).hom x) =
      (limit.π T.globalRing (op 0)).hom x :=
    Iso.hom_inv_id_apply (Scheme.ΓSpecIso (T.R.obj (op 0))) ((limit.π T.globalRing (op 0)).hom x)
  exact Iff.of_eq (congrArg (· ∈ q.asIdeal) h)

include hθ in
/-- **`𝒪_{Proj B}(1)|_{X_0} ≅ ℒ_0`.** -/
def levelZeroTwistIso :
    (Scheme.Modules.pullback (T.levelZeroInclusion d₀ hd₀ hT)).obj
        (twistingSheaf (T.tow d₀ hd₀).limGrading 1) ≅ T.L 0 :=
  ((Scheme.Modules.pullbackComp (T.levelInclusion d₀ hd₀ hT 0)
      (inv (projComparison (T.tow d₀ hd₀).limGrading))).app _).symm ≪≫
    (Scheme.Modules.pullback (T.levelInclusion d₀ hd₀ hT 0)).mapIso
      (twistComparisonInv (T.tow d₀ hd₀).limGrading 1) ≪≫
    @asIso _ _ _ _ (T.levelTwistMor d₀ hd₀ hT 0) (T.isIso_levelTwistMor d₀ hd₀ hT hθ 0)

include hT in
/-- `𝒪_{Proj B}(1)` is of finite presentation. -/
theorem isFinitePresentation_limitTwist :
    _root_.SheafOfModules.IsFinitePresentation.{u, u, u}
      (twistingSheaf (T.tow d₀ hd₀).limGrading 1) := by
  have := (T.tow d₀ hd₀).finitePresentation_lim hT
  exact Stacks.ProjTwistFinitePresentation.isFinitePresentation_twistingSheaf _
    (fun r => SetLike.algebraMap_mem_graded _ r) 1

include hT hθ in
/-- **`𝒪_{Proj B}(1)` is invertible.** -/
theorem isInvertibleModule_limitTwist :
    IsInvertibleModule (AlgebraicGeometry.Proj (T.tow d₀ hd₀).limGrading)
      (twistingSheaf (T.tow d₀ hd₀).limGrading 1) := by
  have := T.isClosedImmersion_levelBase_zero d₀ hd₀ hT
  have := T.isProper_limitProjToBase d₀ hd₀ hT
  have := T.isFinitePresentation_limitTwist d₀ hd₀ hT
  have := (T.tow d₀ hd₀).projective_limGrading hT
  exact @isInvertibleModule_of_isPullback _ _ _ _ _ _ _ _
    (T.isPullback_levelZeroInclusion d₀ hd₀ hT) _
    (T.mem_range_levelBase_zero d₀ hd₀ hT) _ _ (T.finitePresentation_limitProjToBase d₀ hd₀ hT)
    (twistingSheaf (T.tow d₀ hd₀).limGrading 1) (T.isFinitePresentation_limitTwist d₀ hd₀ hT)
    (AlgebraicGeometry.Proj.isFlatOver_twistingSheaf _ (fun d => inferInstance) 1) (T.L 0) _
    (T.levelZeroTwistIso d₀ hd₀ hT hθ)

include hT hθ in
/-- **`𝒪_{Proj B}(1)` is ample.** -/
theorem isAmple_limitTwist :
    haveI := T.isInvertibleModule_limitTwist d₀ hd₀ hT hθ
    IsAmple (AlgebraicGeometry.Proj (T.tow d₀ hd₀).limGrading)
      (twistingSheaf (T.tow d₀ hd₀).limGrading 1) := by
  have := T.isInvertibleModule_limitTwist d₀ hd₀ hT hθ
  have := T.isClosedImmersion_levelBase_zero d₀ hd₀ hT
  have := T.isProper_limitProjToBase d₀ hd₀ hT
  exact isAmple_of_isPullback (T.isPullback_levelZeroInclusion d₀ hd₀ hT)
    (T.mem_range_levelBase_zero d₀ hd₀ hT) (twistingSheaf (T.tow d₀ hd₀).limGrading 1) (T.L 0)
    T.isAmple
    (T.levelZeroTwistIso d₀ hd₀ hT hθ)

end PolarizedTower

end Stacks.PolarizedAlgebraization

end
