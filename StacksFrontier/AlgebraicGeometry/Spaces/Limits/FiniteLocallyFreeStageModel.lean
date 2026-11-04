module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FrameChartDescent
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack

/-!
# Finite locally free and invertible modules on a limit come from a stage

Let `X = lim Xᵢ` be the limit of a cofiltered system of quasi-compact and quasi-separated
algebraic spaces over `S` with affine transition morphisms, in the setting of Stacks 07SK.
Stacks 0D2X asserts that

1. every finite locally free `𝒪_X`-module is the pullback of a finite locally free
   `𝒪_{Xᵢ}`-module for some `i`, and
2. every invertible `𝒪_X`-module is the pullback of an invertible `𝒪_{Xᵢ}`-module for some `i`.

Both follow from `AlgebraicGeometry.Space.exists_stage_model_of_hasLocalFrames`: a module which
has frames locally on the small étale site of `X` is the pullback of a module `M` on a stage
having frames of the same sizes on a finite family of étale charts covering that stage.  For a
finite locally free module the local frames are given by its local trivializations, and `M` is
then finite locally free; for an invertible module they have size one, so `M` is finite locally
free of rank one, which is invertibility on the small étale site of an algebraic space
(`AlgebraicGeometry.Space.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one`).

## Main results

* `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOnSite_stage_model`: **Stacks 0D2X (1)**.
* `AlgebraicGeometry.Space.exists_isInvertibleModule_stage_model`: **Stacks 0D2X (2)**.

## References

* [Stacks Project, Tag 0D2X](https://stacks.math.columbia.edu/tag/0D2X)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Cardinal Stacks.SheafOfModules.ChartFrames

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Local frames of finite locally free modules -/

/-- **A finite locally free module has local frames.** -/
theorem hasLocalFrames_of_isFiniteLocallyFreeOnSite {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E) :
    HasLocalFrames (fun _ => True) E := by
  intro V
  obtain ⟨ι, W, g, hcov, hfree⟩ := hE V
  refine ⟨ι, W, g, hcov, fun i => ?_⟩
  obtain ⟨n, e, he⟩ := exists_isFrame_of_isFiniteFree E (hfree i)
  exact ⟨n, trivial, e, he⟩

/-- **A finite locally free module of rank `r` has local frames of size `r`.** -/
theorem hasLocalFrames_of_isFiniteLocallyFreeOfRank {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hE : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r) :
    HasLocalFrames (· = r) E := by
  intro V
  obtain ⟨ι, W, g, hcov, hfree⟩ := hE V
  refine ⟨ι, W, g, hcov, fun i => ?_⟩
  obtain ⟨c, ⟨hc⟩⟩ := hfree i
  obtain ⟨e, he⟩ := exists_isFrame_of_isColimit_cofan E c hc
  exact ⟨r, rfl, e, he⟩

/-! ### Stacks 0D2X -/

variable (B S hS)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hSize : #I < B.cutoff.ord.cof) (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
  (hZ : B.Contains (⊤_ Scheme.{u}))
  (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
  (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))

include hZ hQc hQs in
/-- **Stacks 0D2X, part (1).** Let `X = lim Xᵢ` be the limit of a cofiltered system of
quasi-compact and quasi-separated algebraic spaces over `S` with affine transition morphisms, as
in Stacks 07SK.  Every finite locally free `𝒪_X`-module is the pullback of a finite locally free
`𝒪_{Xᵢ}`-module for some `i`. -/
@[stacks 0D2X "(1)"]
theorem exists_isFiniteLocallyFreeOnSite_stage_model
    (F : Modules.{u, u} B S hS
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2)
    (hF : SheafOfModules.IsFiniteLocallyFreeOnSite F) :
    ∃ (i : I) (Fᵢ : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
        (stageAlgebraicSpace B S hS D hD i).2),
      SheafOfModules.IsFiniteLocallyFreeOnSite Fᵢ ∧
        Nonempty (F ≅ (modulePullback B S hS
          (limitProjection B S hS D hSize hHomSize hD hAffine i)).obj Fᵢ) := by
  obtain ⟨i, M, K, _, W, n, -, hW, hfr, hiso⟩ :=
    exists_stage_model_of_hasLocalFrames hSize hHomSize hD hAffine hZ hQc hQs F
      (hasLocalFrames_of_isFiniteLocallyFreeOnSite F hF)
  choose e he using hfr
  exact ⟨i, M, isFiniteLocallyFreeOnSite_of_isFrame (coversTop_of_pointsCover hW) M he, hiso⟩

include hZ hQc hQs in
/-- **Stacks 0D2X, part (2).** Let `X = lim Xᵢ` be the limit of a cofiltered system of
quasi-compact and quasi-separated algebraic spaces over `S` with affine transition morphisms, as
in Stacks 07SK.  Every invertible `𝒪_X`-module is the pullback of an invertible
`𝒪_{Xᵢ}`-module for some `i`. -/
@[stacks 0D2X "(2)"]
theorem exists_isInvertibleModule_stage_model
    (L : Modules.{u, u} B S hS
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2)
    (hL : IsInvertibleModule (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine) L) :
    ∃ (i : I) (Lᵢ : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
        (stageAlgebraicSpace B S hS D hD i).2),
      IsInvertibleModule (stageAlgebraicSpace B S hS D hD i) Lᵢ ∧
        Nonempty (L ≅ (modulePullback B S hS
          (limitProjection B S hS D hSize hHomSize hD hAffine i)).obj Lᵢ) := by
  obtain ⟨i, M, K, _, W, n, hn, hW, hfr, hiso⟩ :=
    exists_stage_model_of_hasLocalFrames hSize hHomSize hD hAffine hZ hQc hQs L
      (hasLocalFrames_of_isFiniteLocallyFreeOfRank L
        ((isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one L).mp hL))
  choose e he using hfr
  refine ⟨i, M, (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one M).mpr ?_, hiso⟩
  exact isFiniteLocallyFreeOfRank_of_isFrame (coversTop_of_pointsCover hW) M he 1 hn

end AlgebraicGeometry.Space
