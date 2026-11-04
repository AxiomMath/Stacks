module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass

/-!
# Base change of a local property of morphisms of locally adic\* formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. Remark 87.21.8 (Stacks 0GBE) defines what
it means for a local property `P` of morphisms of `WAdm^{adic*}`, in the sense of Remark 0ANH, to
be *stable under base change*: for `B → A` and `B → C` in that category, `P (B → A)` should force
`P (C → A ⊗̂_B C)`. It then asserts that the analogue of Lemma 87.21.7 (Stacks 0GBD) holds for
morphisms between locally adic\* formal algebraic spaces over `S`: if `f : X ⟶ Y` has `P`, so
does the second projection `X ×_Y Z ⟶ Z` for every `g : Z ⟶ Y`.

## Main results

* `TopologicalRing.exists_fg_isAdic_of_isAdicStar`: the topology of an object of
  `WAdm^{adic*}` is the adic topology of a finitely generated ideal.
* `TopologicalRing.isAdicStar_completedTensorProduct`: the completed tensor product of objects
  of `WAdm^{adic*}` is an object of `WAdm^{adic*}` (Lemma 87.4.12).
* `AlgebraicGeometry.FormalSpace.completedTensorBaseChangeAxiom_of_adicStarStableBaseChange`:
  a local property of morphisms of `WAdm^{adic*}` stable under base change satisfies
  `AlgebraicGeometry.FormalSpace.CompletedTensorBaseChangeAxiom` at the class `WAdm^{adic*}`.
* `AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_pullback_snd_adicStar`,
  `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_adicStar`,
  `AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_pullback_snd_adicStar` and their
  `_of_stableBaseChangeAdicStar` counterparts: conditions (3), (1) and (2) of Stacks 0ANG for the
  second projection, given a covering `hcover` of `X ×_Y Z` by fibre products of charts and, for
  conditions (1) and (2), the implication (3) ⟹ (1) as `h31`.

## Implementation notes

Objects of `WAdm^{adic*}` are encoded by `TopologicalRing.IsAdicStar`, an adic topological ring
with a finitely generated ideal of definition. Stability under base change is stated in two
forms: `TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar` tests weakly admissible rings
satisfying `TopologicalRing.IsAdicStar`, and
`TopologicalRing.AdicStarPropertyIsStableUnderBaseChange` tests weakly admissible rings whose
topology is the adic topology of a finitely generated ideal.
`TopologicalRing.exists_fg_isAdic_of_isAdicStar` and `Rig.weaklyAdmissible_of_isAdicRing` pass
from `TopologicalRing.IsAdicStar` to the hypotheses of the second form.

The hypothesis `hiso` is the invariance of `P` under isomorphism of targets, which Situation 0CBA
makes part of the hypothesis on `P`.

## References

* [Stacks Project, Tag 0GBE](https://stacks.math.columbia.edu/tag/0GBE)
* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0GBF](https://stacks.math.columbia.edu/tag/0GBF)
* [Stacks Project, Tag 0GB4](https://stacks.math.columbia.edu/tag/0GB4)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

/-- The topology of an object of `WAdm^{adic*}` is the adic topology of a finitely generated
ideal: a finitely generated ideal of definition of an adic topological ring defines the
topology through its powers. -/
theorem exists_fg_isAdic_of_isAdicStar {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] (hR : IsAdicStar R) :
    ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I := by
  obtain ⟨I, hIdef, hIfg⟩ := hR.2
  exact ⟨I, hIfg, Rig.idealOfDefinition_isAdic_of_isAdicRing hR.1 I hIdef⟩

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The completed tensor product of two objects of `WAdm^{adic*}` over a third is again an
object of `WAdm^{adic*}`: it is adic and it has a finitely generated ideal of definition. -/
@[stacks 0GB4 "the adic_finite clauses, assembled as membership in WAdm^{adic*}"]
theorem isAdicStar_completedTensorProduct {A₀ A₁ A : Type u}
    [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀]
    [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [Algebra A₀ A₁] [Algebra A₀ A]
    (h₁ : IsAdicStar A₁) (hA : IsAdicStar A)
    (hc₁ : Continuous (algebraMap A₀ A₁)) (hcA : Continuous (algebraMap A₀ A)) :
    IsAdicStar (CompletedTensorProduct (R := A₀) (M := A₁) (N := A)) := by
  refine ⟨completedTensorProduct_isAdic hc₁ hcA h₁.1.1 h₁.2 hA.1.1 hA.2, ?_⟩
  obtain ⟨K, hKfg, hKdef⟩ := exists_fg_ideal_of_definition hc₁ hcA h₁.1.1 h₁.2 hA.1.1 hA.2
  exact ⟨K, hKdef, hKfg⟩

end

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A local property of morphisms of `WAdm^{adic*}` stable under base change, in the sense of
`TopologicalRing.AdicStarPropertyIsStableUnderBaseChange`, satisfies the completed tensor
base-change axiom at the class `WAdm^{adic*}`, with no condition on the morphism being based
along. -/
theorem completedTensorBaseChangeAxiom_of_adicStarStableBaseChange
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.AdicStarPropertyIsStableUnderBaseChange.{u} P) :
    CompletedTensorBaseChangeAxiom.{u} TopologicalRing.IsAdicStar P (fun _ ↦ True) := by
  intro A₀ A₁ A _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₀ h₁ hA hc₁ hcA hp _
  refine ⟨TopologicalRing.isAdicStar_completedTensorProduct h₁ hA hc₁ hcA, ?_⟩
  exact hP.baseChange (Rig.weaklyAdmissible_of_isAdicRing h₀.1)
    (TopologicalRing.exists_fg_isAdic_of_isAdicStar h₀)
    (Rig.weaklyAdmissible_of_isAdicRing h₁.1)
    (TopologicalRing.exists_fg_isAdic_of_isAdicStar h₁)
    (Rig.weaklyAdmissible_of_isAdicRing hA.1)
    (TopologicalRing.exists_fg_isAdic_of_isAdicStar hA) hc₁ hcA hp

/-- A local property of morphisms of `WAdm^{adic*}` stable under base change, in the sense of
`TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar`, satisfies the completed tensor
base-change axiom at the class `WAdm^{adic*}`, with no condition on the morphism being based
along. -/
theorem completedTensorBaseChangeAxiom_of_stableBaseChangeAdicStar
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar.{u} P) :
    CompletedTensorBaseChangeAxiom.{u} TopologicalRing.IsAdicStar P (fun _ ↦ True) := by
  intro A₀ A₁ A _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₀ h₁ hA hc₁ hcA hp _
  refine ⟨TopologicalRing.isAdicStar_completedTensorProduct h₁ hA hc₁ hcA, ?_⟩
  exact hP.baseChange (Rig.weaklyAdmissible_of_isAdicRing h₀.1) h₀
    (Rig.weaklyAdmissible_of_isAdicRing h₁.1) h₁
    (Rig.weaklyAdmissible_of_isAdicRing hA.1) hA hc₁ hcA hp

/-- Condition (3) of Stacks 0ANG for the second projection. Let `P` be a local property of
morphisms of `WAdm^{adic*}` stable under base change in the sense of
`TopologicalRing.AdicStarPropertyIsStableUnderBaseChange`, invariant under isomorphism of
targets. If `f : X ⟶ Y` satisfies condition (1) of Stacks 0ANG for `P` at the class
`WAdm^{adic*}` and `X ×_Y Z` has a covering `hcover` by fibre products of charts, then the
second projection `X ×_Y Z ⟶ Z` satisfies condition (3). -/
theorem hasPropertyAfterSourceCover_pullback_snd_adicStar
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.AdicStarPropertyIsStableUnderBaseChange.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSndOn B S hS TopologicalRing.IsAdicStar f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f) :
    HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar P (pullback.snd f g) :=
  hasPropertyAfterSourceCover_pullback_snd_of_baseChangeAxiom B S hS
    TopologicalRing.IsAdicStar P (fun _ ↦ True)
    (completedTensorBaseChangeAxiom_of_adicStarStableBaseChange P hP) hiso f g hcover hf
    (hasPropertyOnEveryAffineEtaleDiagram_true B S hS _ g)

/-- Condition (1) of Stacks 0ANG for the second projection. Let `P` be a local property of
morphisms of `WAdm^{adic*}` stable under base change in the sense of
`TopologicalRing.AdicStarPropertyIsStableUnderBaseChange`, invariant under isomorphism of
targets, and for which condition (3) of Stacks 0ANG implies condition (1). If `f : X ⟶ Y`
satisfies condition (1) for `P` at the class `WAdm^{adic*}` and `X ×_Y Z` has a covering
`hcover` by fibre products of charts, then so does the second projection `X ×_Y Z ⟶ Z`. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_adicStar
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.AdicStarPropertyIsStableUnderBaseChange.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSndOn B S hS TopologicalRing.IsAdicStar f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P
      (pullback.snd f g) :=
  h31 _ (hasPropertyAfterSourceCover_pullback_snd_adicStar B S hS P hP hiso f g hcover hf)

/-- Condition (2) of Stacks 0ANG for the second projection. Let `P` be as in
`hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_adicStar`. If `f : X ⟶ Y` satisfies
condition (1) of Stacks 0ANG for `P` at the class `WAdm^{adic*}`, `X ×_Y Z` has a covering
`hcover` by fibre products of charts, `Z` is a formal algebraic space, and the fibre products of
affine étale `W ⟶ Z` with `X ×_Y Z` are formal algebraic spaces (`hpb`, Stacks 0AJ3), then the
second projection `X ×_Y Z ⟶ Z` satisfies condition (2): there is an affine étale covering of
`Z` and, over each of its members, an affine étale covering of the fibre product with
`X ×_Y Z` on which `P` holds. -/
theorem hasPropertyAfterTargetCover_pullback_snd_adicStar
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.AdicStarPropertyIsStableUnderBaseChange.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hpb : ∀ (W : FppfSheaf B S hS) (w : W ⟶ Z), IsAffineFormalAlgebraicSpace B S hS W →
      IsRepresentableEtale B S hS w →
      IsFormalAlgebraicSpace B S hS (pullback w (pullback.snd f g)))
    (hcover : HasBaseChangeCoverOverPullbackSndOn B S hS TopologicalRing.IsAdicStar f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f) :
    HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar P (pullback.snd f g) :=
  hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P
    (pullback.snd f g) hZ hpb
    (hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_adicStar B S hS P hP hiso h31 f g hcover
      hf)

/-! ### The same three conclusions from `TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar`
-/

/-- Condition (3) of Stacks 0ANG for the second projection, as in
`hasPropertyAfterSourceCover_pullback_snd_adicStar`, for `P` stable under base change in the
sense of `TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar`. -/
theorem hasPropertyAfterSourceCover_pullback_snd_of_stableBaseChangeAdicStar
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSndOn B S hS TopologicalRing.IsAdicStar f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f) :
    HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar P (pullback.snd f g) :=
  hasPropertyAfterSourceCover_pullback_snd_of_baseChangeAxiom B S hS
    TopologicalRing.IsAdicStar P (fun _ ↦ True)
    (completedTensorBaseChangeAxiom_of_stableBaseChangeAdicStar P hP) hiso f g hcover hf
    (hasPropertyOnEveryAffineEtaleDiagram_true B S hS _ g)

/-- Condition (1) of Stacks 0ANG for the second projection, as in
`hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_adicStar`, for `P` stable under base change
in the sense of `TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar`. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_of_stableBaseChangeAdicStar
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSndOn B S hS TopologicalRing.IsAdicStar f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P
      (pullback.snd f g) :=
  h31 _ (hasPropertyAfterSourceCover_pullback_snd_of_stableBaseChangeAdicStar B S hS P hP hiso
    f g hcover hf)

/-- Condition (2) of Stacks 0ANG for the second projection, as in
`hasPropertyAfterTargetCover_pullback_snd_adicStar`, for `P` stable under base change in the
sense of `TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar`. -/
theorem hasPropertyAfterTargetCover_pullback_snd_of_stableBaseChangeAdicStar
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hpb : ∀ (W : FppfSheaf B S hS) (w : W ⟶ Z), IsAffineFormalAlgebraicSpace B S hS W →
      IsRepresentableEtale B S hS w →
      IsFormalAlgebraicSpace B S hS (pullback w (pullback.snd f g)))
    (hcover : HasBaseChangeCoverOverPullbackSndOn B S hS TopologicalRing.IsAdicStar f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f) :
    HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar P (pullback.snd f g) :=
  hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P
    (pullback.snd f g) hZ hpb
    (hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_of_stableBaseChangeAdicStar B S hS P hP
      hiso h31 f g hcover hf)

end

end AlgebraicGeometry.FormalSpace

end
