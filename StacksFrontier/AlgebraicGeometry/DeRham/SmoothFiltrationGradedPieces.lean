module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepSquaresProof
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceCut
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedComparisonSource
import StacksCore.Tactic.StacksAttribute

/-!
# The graded pieces of the filtration of the de Rham complex of a smooth morphism

Let `f : X ⟶ Y` be a smooth morphism of schemes over a base `S`, with `g : Y ⟶ S` the structure
morphism of the target. [Stacks, Section 0FMK] filters `Ω^•_{X/S}` by the forms pulled back from
`Y` (`Stacks.DeRhamSmooth.deRhamSmoothFiltration`, with its clauses in
`Stacks.DeRhamSmooth.deRhamSmoothFiltration_spec`) and computes the filtration in each degree and
the graded pieces of the filtered complex. This file states those computations.

## Main definitions

* `Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplexOfSmooth`: **the graded pieces of the
  filtered complex**, `gr^kΩ^•_{X/S} ≅ f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`, an
  isomorphism of complexes.

## Main results

* `Stacks.DeRhamSmooth.relativeDifferentialsShortComplex_shortExact_and_locally_split`: the
  sequence `0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` is short exact and locally split.
* `Stacks.DeRhamSmooth.relativeDifferentialsExteriorFiltration_smooth_spec`: the induced
  filtration `Ω^p_{X/S} = F^0 ⊃ F^1 ⊃ … ⊃ F^{p+1} = 0` and its successive quotients
  `gr^kΩ^p_{X/S} ≅ f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^{p-k}_{X/Y}` for `k = 0, …, p`.
* `Stacks.DeRhamSmooth.nonempty_gradedPiece_X_iso_pulledBackTargetFormsTensor`: in each degree,
  `gr^kΩ^p_{X/S} ≅ f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^{p-k}_{X/Y}`.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 02K4](https://stacks.math.columbia.edu/tag/02K4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.DeRhamDirectImage

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace Stacks.DeRhamSmooth

attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **Stacks Project, Section 0FMK: the locally split short exact sequence.** For `f : X ⟶ Y`
smooth over a base `S`, the sequence `0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` is short exact,
and every point of `X` has an open neighbourhood over which it splits. -/
@[stacks 0FMK "the locally split short exact sequence 0 → f^*Ω_{Y/S} → Ω_{X/S} → Ω_{X/Y} → 0 \
of a smooth f (Tag 02K4)"]
theorem relativeDifferentialsShortComplex_shortExact_and_locally_split [Smooth f] :
    (Scheme.Hom.relativeDifferentialsShortComplex f g).ShortExact ∧
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
        Nonempty (Scheme.Hom.relativeDifferentialsShortComplexRestrict f g U).Splitting :=
  ⟨Scheme.Hom.shortExact_relativeDifferentialsShortComplex f g
      (Stacks.Smooth.formallySmoothScheme_of_smooth f),
    Scheme.Hom.exists_nonempty_splitting_relativeDifferentialsRestrict f g⟩

/-- **Stacks Project, Section 0FMK: the filtration of `Ω^p_{X/S}` and its successive
quotients.** For `f : X ⟶ Y` smooth over a base `S` and every `p`, the filtration of
`Ω^p_{X/S} = ⋀^pΩ_{X/S}` induced by `f^*Ω_{Y/S} ⊆ Ω_{X/S}`, whose `k`-th step is the image of
`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} ⋀^{p-k}Ω_{X/S} ⟶ Ω^p_{X/S}`, satisfies:

* `F^0Ω^p_{X/S} = Ω^p_{X/S}`, and the steps decrease;
* `F^{p+1}Ω^p_{X/S} = 0`;
* for `k < p`, writing `p = k + 1 + m`, the canonical morphism
  `f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ⟶ gr^kΩ^p_{X/S}` is an isomorphism;
* for `k = p`, `gr^pΩ^p_{X/S} = F^pΩ^p_{X/S} ≅ f^*Ω^p_{Y/S} ⊗_{𝒪_X} Ω^0_{X/Y}`. -/
@[stacks 0FMK "the filtration Ω^p_{X/S} = F^0 ⊃ F^1 ⊃ … ⊃ F^{p+1} = 0 induced by \
f^*Ω_{Y/S} ⊆ Ω_{X/S}, with gr^kΩ^p_{X/S} ≅ f^*Ω^k_{Y/S} ⊗_{O_X} Ω^{p-k}_{X/Y} for k = 0, …, p \
(for k < p the canonical comparison is an isomorphism; for k = p, gr^p = F^p since F^{p+1} = 0)"]
theorem relativeDifferentialsExteriorFiltration_smooth_spec [Smooth f] (p : ℕ) :
    Scheme.Hom.relativeDifferentialsExteriorFiltration f g p 0 = ⊤ ∧
      Antitone (Scheme.Hom.relativeDifferentialsExteriorFiltration f g p) ∧
      IsZero (Subobject.underlying.obj
        (Scheme.Hom.relativeDifferentialsExteriorFiltration f g p (p + 1))) ∧
      (∀ k m : ℕ, k + 1 + m = p →
        IsIso (Scheme.Hom.relativeDifferentialsPullbackGradedComparison f g k m)) ∧
      Nonempty (Subobject.underlying.obj
          (Scheme.Hom.relativeDifferentialsExteriorFiltration f g p p) ≅
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)).obj
          ((Scheme.Modules.pullback f).obj
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (p : ℤ)),
            AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) : ℤ))) := by
  refine ⟨(Scheme.Hom.relativeDifferentialsExteriorFiltration_spec f g p).1,
    (Scheme.Hom.relativeDifferentialsExteriorFiltration_spec f g p).2, ?_,
    fun k m _ => Scheme.Hom.isIso_relativeDifferentialsPullbackGradedComparison f g k m, ?_⟩
  · have h := _root_.SheafOfModules.exteriorImageFiltration_eq_bot
      (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁)
      (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
      (Scheme.Hom.relativeDifferentialsShortComplex f g).f p (p + 1) (Nat.lt_succ_self p)
    exact (congrArg (fun P => IsZero (Subobject.underlying.obj P)) h).mpr
      (IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero)
  · exact ⟨Subobject.isoOfEq _ _
        (_root_.SheafOfModules.exteriorImageFiltration_eq_imageSubobject _ _ _ p 0 p
          (Nat.add_zero p)) ≪≫
      Stacks.GradedPieceImage.imageSubobjectIsoSource _
        (Scheme.Hom.mono_relativeDifferentialsProdWedgeHomOfEq_of_eq_zero f g p 0 p rfl
          (Nat.add_zero p)) ≪≫
      cutWedgeSourceIsoPullbackTensor f g p⟩

/-- **Stacks Project, Section 0FMK: the graded pieces of the filtered complex.** For
`f : X ⟶ Y` smooth over a base `S` and every `k`, the `k`-th graded piece of the filtration of
`Ω^•_{X/S}` by the forms pulled back from `Y` is

`gr^kΩ^•_{X/S}  ≅  f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`,

an isomorphism of complexes of `(f ∘ g)^{-1}𝒪_S`-modules on `X`. The target is
`Stacks.DeRhamSmooth.gradedTargetComplex`: its degree-`n` term is
`f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^{n-k}_{X/Y}` (`Stacks.DeRhamSmooth.gradedTargetComplex_X`) and
its differential is `(-1)^k(1 ⊗ d_{X/Y})`, the one the shift `[-k]` carries
(`Stacks.DeRhamSmooth.gradedTargetComplex_d`). -/
@[stacks 0FMK "the graded pieces of the filtered complex: \
gr^kΩ^•_{X/S} ≅ f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}O_Y} Ω^•_{X/Y} as complexes, for f smooth"]
def gradedPieceIsoGradedTargetComplexOfSmooth [Smooth f] (k : ℕ) :
    gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g) ≅
      gradedTargetComplex f g k :=
  gradedPieceIsoGradedTargetComplexOfStepSquares f g k (stepSquares f g k).1
    (stepSquares f g k).2

/-- **Stacks Project, Section 0FMK: the graded pieces in each degree, over `f^{-1}𝒪_Y`.** For
`f : X ⟶ Y` smooth over a base `S` and `p = k + j`, the degree-`p` term of the `k`-th graded piece
of the filtration of `Ω^•_{X/S}` is `f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^j_{X/Y}`, read over
`(f ∘ g)^{-1}𝒪_S`. -/
@[stacks 0FMK "gr^kΩ^p_{X/S} ≅ f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}O_Y} Ω^{p-k}_{X/Y} in each \
degree p = k + j, for f smooth"]
theorem nonempty_gradedPiece_X_iso_pulledBackTargetFormsTensor [Smooth f] (k j p : ℕ)
    (h : k + j = p) :
    Nonempty ((gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).X
        (p : ℤ) ≅
      (coefficientRestriction f g).obj ((pulledBackTargetFormsTensor f g k).obj
        ((pushforward (toInverseImageBase f)).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((j : ℕ) : ℤ))))) :=
  ⟨(HomologicalComplex.eval _ _ (p : ℤ)).mapIso (gradedPieceIsoGradedTargetComplexOfSmooth f g k) ≪≫
    gradedTargetXIso f g k j p h⟩

end Stacks.DeRhamSmooth

end
