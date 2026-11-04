module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.CompositionIso
import StacksCore.Tactic.StacksAttribute

/-!
# Associativity of the convolution of Fourier-Mukai kernels

Let `S` be a scheme and let `X`, `Y`, `Z`, `W` be schemes over `S`. For kernels `c` on
`X ×_S Y`, `c'` on `Y ×_S Z` and `c''` on `Z ×_S W`, the convolution of [Stacks, Tag 0FYS]

`c' ∘ c = R pr_{13,*}(L pr_{12}^* c ⊗^𝐋 L pr_{23}^* c')`

is associative up to canonical isomorphism:

`c'' ∘ (c' ∘ c) ≅ (c'' ∘ c') ∘ c`.

This is the associativity law of the category of Fourier-Mukai kernels of Section 0G0F of the
source, and its proof is the source's five-step chain, run once from each side towards the common
value `R pr^{1234}_{14,*}((pr_{12}^*c ⊗ pr_{23}^*c') ⊗ pr_{34}^*c'')` on the quadruple fibre
product.

## Main definitions

* `AlgebraicGeometry.fourierMukaiQuadrupleProduct` — the quadruple fibre product
  `X ×_S Y ×_S Z ×_S W`, built as the fibre product of `X ×_S Y ×_S Z` and `X ×_S Z ×_S W` over
  `X ×_S Z`.
* `AlgebraicGeometry.fourierMukaiQuadToXYW`, `AlgebraicGeometry.fourierMukaiQuadToYZW` — its
  projections to `X ×_S Y ×_S W` and to `Y ×_S Z ×_S W`.

## Main results

* `AlgebraicGeometry.isPullback_fourierMukaiQuad_right` — the quadruple product is also the fibre
  product of `X ×_S Y ×_S W` and `Y ×_S Z ×_S W` over `Y ×_S W`.
* `AlgebraicGeometry.fourierMukaiConvolutionAssocIso` — **associativity of convolution**,
  for `X ⟶ S` and `W ⟶ S` flat, all four structure morphisms quasi-compact and
  quasi-separated, and kernels with quasi-coherent cohomology sheaves.

## The source's chain

From the left, with `p = pr^{123}`, `q = pr^{134}`, `r = pr^{1234}`:

1. `q_{13}^* p_{13,*} ≅ r_{134,*} r_{123}^*` by derived base change, [Stacks, Tag 08IB], along
   the defining cartesian square of the quadruple product; Tor independence holds because
   `q_{12} : X ×_S Z ×_S W ⟶ X ×_S Z` is flat, a base change of `W ⟶ S`;
2. `r_{123}^*(p_{12}^*c ⊗ p_{23}^*c') ≅ r_{123}^* p_{12}^* c ⊗ r_{123}^* p_{23}^* c'`, the
   monoidality of derived pullback, [Stacks, Tag 079U];
3. the projection formula for `r_{134}`, [Stacks, Tag 08EU];
4. `q_{14,*} r_{134,*} ≅ r_{14,*}`, [Stacks, Tag 0D5T].

From the right the same four steps run along the cartesian square of
`isPullback_fourierMukaiQuad_right`, where Tor independence holds because
`pr_{23} : X ×_S Y ×_S W ⟶ Y ×_S W` is flat, a base change of `X ⟶ S`; the projection formula
there has the pushed-forward factor in the right-hand slot, so the commutativity constraint of
[Stacks, Tag 0FPB] is applied on both sides of it. The two values are then compared by the
composition isomorphisms of derived pullback, [Stacks, Tag 0D5S], and associativity of
`⊗^𝐋`, [Stacks, Tag 0FPB].

## Implementation notes

*Hypotheses.* Section 0G0F takes all four schemes smooth and proper over `S`. What the chain
uses is quasi-compactness and quasi-separatedness of the four structure morphisms (for the
direct images and the projection formula), flatness of `X ⟶ S` and `W ⟶ S` (for the two Tor
independences) and quasi-coherence of the cohomology of the three kernels (for [Stacks, Tag 08IB]
and [Stacks, Tag 08EU]). All are implied by the source's hypotheses — a perfect object has
quasi-coherent cohomology — so the statement covers the source's case.

*No attribute.* Associativity is one clause of the construction of Section 0G0F, not a
statement of its own; the tag is registered on the category, in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/KernelCategory.lean`.

## References

* [Stacks Project, Tag 0G0F](https://stacks.math.columbia.edu/tag/0G0F)
* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The quadruple fibre product -/

section Geometry

variable {S X Y Z W : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (k : W ⟶ S)

/-- The quadruple fibre product `X ×_S Y ×_S Z ×_S W`, as the fibre product of
`X ×_S Y ×_S Z` and `X ×_S Z ×_S W` over `X ×_S Z`. -/
abbrev fourierMukaiQuadrupleProduct : Scheme.{u} :=
  pullback (fourierMukaiPr13 f g h) (fourierMukaiPr12 f h k)

/-- The projection `pr^{1234}_{123}` to `X ×_S Y ×_S Z`. -/
abbrev fourierMukaiQuadToXYZ :
    fourierMukaiQuadrupleProduct f g h k ⟶ fourierMukaiTripleProduct f g h :=
  pullback.fst _ _

/-- The projection `pr^{1234}_{134}` to `X ×_S Z ×_S W`. -/
abbrev fourierMukaiQuadToXZW :
    fourierMukaiQuadrupleProduct f g h k ⟶ fourierMukaiTripleProduct f h k :=
  pullback.snd _ _

/-- The projection `pr^{1234}_3` to `Z`, read through `X ×_S Y ×_S Z`. -/
lemma fourierMukaiQuad_pr3 :
    fourierMukaiQuadToXYZ f g h k ≫ fourierMukaiPr3 f g h =
      fourierMukaiQuadToXZW f g h k ≫ fourierMukaiPr12 f h k ≫ pullback.snd f h := by
  rw [← fourierMukaiPr13_snd, ← Category.assoc, pullback.condition, Category.assoc]

/-- The projection `pr^{1234}_1` to `X`, read through `X ×_S Y ×_S Z`. -/
lemma fourierMukaiQuad_pr1 :
    fourierMukaiQuadToXYZ f g h k ≫ fourierMukaiPr12 f g h ≫ pullback.fst f g =
      fourierMukaiQuadToXZW f g h k ≫ fourierMukaiPr12 f h k ≫ pullback.fst f h := by
  rw [← fourierMukaiPr13_fst, ← Category.assoc, pullback.condition, Category.assoc]

/-- The structure condition of `X ×_S Y ×_S W`, for the map out of the quadruple product. -/
lemma fourierMukaiQuad_condition :
    (fourierMukaiQuadToXYZ f g h k ≫ fourierMukaiPr12 f g h) ≫ (pullback.snd f g ≫ g) =
      (fourierMukaiQuadToXZW f g h k ≫ fourierMukaiPr3 f h k) ≫ k := by
  have h₁ : fourierMukaiPr12 f g h ≫ (pullback.snd f g ≫ g) = fourierMukaiPr3 f g h ≫ h :=
    pullback.condition
  have h₂ : fourierMukaiPr12 f h k ≫ (pullback.snd f h ≫ h) = fourierMukaiPr3 f h k ≫ k :=
    pullback.condition
  have h₃ := fourierMukaiQuad_pr3 f g h k
  simp only [Category.assoc] at h₁ h₂ h₃ ⊢
  rw [h₁, ← Category.assoc, h₃]
  simp only [Category.assoc]
  rw [h₂]

attribute [reassoc] fourierMukaiPr13_fst fourierMukaiPr13_snd fourierMukaiPr23_fst
  fourierMukaiPr23_snd

/-- The defining square of the quadruple product, read as a rewrite rule from the `X ×_S Z ×_S W`
side to the `X ×_S Y ×_S Z` side. -/
@[reassoc (attr := simp)] lemma fourierMukaiQuadToXZW_pr12 :
    fourierMukaiQuadToXZW f g h k ≫ fourierMukaiPr12 f h k =
      fourierMukaiQuadToXYZ f g h k ≫ fourierMukaiPr13 f g h :=
  pullback.condition.symm

/-- The projection `pr^{1234}_{124}` to `X ×_S Y ×_S W`. -/
def fourierMukaiQuadToXYW :
    fourierMukaiQuadrupleProduct f g h k ⟶ fourierMukaiTripleProduct f g k :=
  pullback.lift (fourierMukaiQuadToXYZ f g h k ≫ fourierMukaiPr12 f g h)
    (fourierMukaiQuadToXZW f g h k ≫ fourierMukaiPr3 f h k) (fourierMukaiQuad_condition f g h k)

/-- The projection `pr^{1234}_{234}` to `Y ×_S Z ×_S W`. -/
def fourierMukaiQuadToYZW :
    fourierMukaiQuadrupleProduct f g h k ⟶ fourierMukaiTripleProduct g h k :=
  pullback.lift (fourierMukaiQuadToXYZ f g h k ≫ fourierMukaiPr23 f g h)
    (fourierMukaiQuadToXZW f g h k ≫ fourierMukaiPr3 f h k) (by
      rw [Category.assoc, ← Category.assoc (fourierMukaiPr23 f g h), fourierMukaiPr23_snd,
        ← fourierMukaiQuad_condition f g h k]
      have h₁ : fourierMukaiPr12 f g h ≫ (pullback.snd f g ≫ g) =
          fourierMukaiPr3 f g h ≫ h := pullback.condition
      rw [Category.assoc, h₁])

/-- `pr^{124}_{12} ∘ pr^{1234}_{124} = pr^{123}_{12} ∘ pr^{1234}_{123}`. -/
@[reassoc (attr := simp)] lemma fourierMukaiQuadToXYW_pr12 :
    fourierMukaiQuadToXYW f g h k ≫ fourierMukaiPr12 f g k =
      fourierMukaiQuadToXYZ f g h k ≫ fourierMukaiPr12 f g h :=
  pullback.lift_fst _ _ _

/-- `pr^{124}_{4} ∘ pr^{1234}_{124} = pr^{134}_{4} ∘ pr^{1234}_{134}`. -/
@[reassoc (attr := simp)] lemma fourierMukaiQuadToXYW_pr3 :
    fourierMukaiQuadToXYW f g h k ≫ fourierMukaiPr3 f g k =
      fourierMukaiQuadToXZW f g h k ≫ fourierMukaiPr3 f h k :=
  pullback.lift_snd _ _ _

/-- `pr^{234}_{23} ∘ pr^{1234}_{234} = pr^{123}_{23} ∘ pr^{1234}_{123}`. -/
@[reassoc (attr := simp)] lemma fourierMukaiQuadToYZW_pr12 :
    fourierMukaiQuadToYZW f g h k ≫ fourierMukaiPr12 g h k =
      fourierMukaiQuadToXYZ f g h k ≫ fourierMukaiPr23 f g h :=
  pullback.lift_fst _ _ _

/-- `pr^{234}_{4} ∘ pr^{1234}_{234} = pr^{134}_{4} ∘ pr^{1234}_{134}`. -/
@[reassoc (attr := simp)] lemma fourierMukaiQuadToYZW_pr3 :
    fourierMukaiQuadToYZW f g h k ≫ fourierMukaiPr3 g h k =
      fourierMukaiQuadToXZW f g h k ≫ fourierMukaiPr3 f h k :=
  pullback.lift_snd _ _ _

/-- `pr^{234}_{34} ∘ pr^{1234}_{234} = pr^{134}_{34} ∘ pr^{1234}_{134}`. -/
lemma fourierMukaiQuadToYZW_pr23 :
    fourierMukaiQuadToYZW f g h k ≫ fourierMukaiPr23 g h k =
      fourierMukaiQuadToXZW f g h k ≫ fourierMukaiPr23 f h k := by
  apply pullback.hom_ext <;> simp

/-- `pr^{124}_{14} ∘ pr^{1234}_{124} = pr^{134}_{14} ∘ pr^{1234}_{134}`. -/
lemma fourierMukaiQuadToXYW_pr13 :
    fourierMukaiQuadToXYW f g h k ≫ fourierMukaiPr13 f g k =
      fourierMukaiQuadToXZW f g h k ≫ fourierMukaiPr13 f h k := by
  apply pullback.hom_ext <;> simp

/-- The square of `isPullback_fourierMukaiQuad_right` commutes. -/
lemma fourierMukaiQuad_right_w :
    fourierMukaiQuadToYZW f g h k ≫ fourierMukaiPr13 g h k =
      fourierMukaiQuadToXYW f g h k ≫ fourierMukaiPr23 f g k := by
  apply pullback.hom_ext <;> simp

section Lift

variable {f g h k} {T : Scheme.{u}} (a : T ⟶ fourierMukaiTripleProduct g h k)
  (b : T ⟶ fourierMukaiTripleProduct f g k)
  (w : a ≫ fourierMukaiPr13 g h k = b ≫ fourierMukaiPr23 f g k)
include w

/-- The `Y`-components of the two legs of a cone over the right square agree. -/
lemma fourierMukaiQuadLift_y :
    a ≫ fourierMukaiPr12 g h k ≫ pullback.fst g h =
      b ≫ fourierMukaiPr12 f g k ≫ pullback.snd f g := by
  have := congrArg (· ≫ pullback.fst g k) w
  simpa only [Category.assoc, fourierMukaiPr13_fst, fourierMukaiPr23_fst] using this

/-- The `W`-components of the two legs of a cone over the right square agree. -/
lemma fourierMukaiQuadLift_w :
    a ≫ fourierMukaiPr3 g h k = b ≫ fourierMukaiPr3 f g k := by
  have := congrArg (· ≫ pullback.snd g k) w
  simpa only [Category.assoc, fourierMukaiPr13_snd, fourierMukaiPr23_snd] using this

/-- The leg to `X ×_S Y ×_S Z` of the lift of a cone over the right square. -/
def fourierMukaiQuadLiftXYZ : T ⟶ fourierMukaiTripleProduct f g h :=
  pullback.lift (b ≫ fourierMukaiPr12 f g k) (a ≫ fourierMukaiPr12 g h k ≫ pullback.snd g h) (by
    have e := congrArg (· ≫ g) (fourierMukaiQuadLift_y a b w)
    simp only [Category.assoc] at e ⊢
    rw [← pullback.condition (f := g) (g := h)]
    exact e.symm)

/-- The `X ×_S Y`-component of `fourierMukaiQuadLiftXYZ a b w` is that of `b`. -/
@[reassoc (attr := simp)] lemma fourierMukaiQuadLiftXYZ_pr12 :
    fourierMukaiQuadLiftXYZ a b w ≫ fourierMukaiPr12 f g h = b ≫ fourierMukaiPr12 f g k :=
  pullback.lift_fst _ _ _

/-- The `Z`-component of `fourierMukaiQuadLiftXYZ a b w` is that of `a`. -/
@[reassoc (attr := simp)] lemma fourierMukaiQuadLiftXYZ_pr3 :
    fourierMukaiQuadLiftXYZ a b w ≫ fourierMukaiPr3 f g h =
      a ≫ fourierMukaiPr12 g h k ≫ pullback.snd g h :=
  pullback.lift_snd _ _ _

/-- The leg to `X ×_S Z ×_S W` of the lift of a cone over the right square. -/
def fourierMukaiQuadLiftXZW : T ⟶ fourierMukaiTripleProduct f h k :=
  pullback.lift (fourierMukaiQuadLiftXYZ a b w ≫ fourierMukaiPr13 f g h)
    (a ≫ fourierMukaiPr3 g h k) (by
      have h₁ : fourierMukaiPr12 g h k ≫ (pullback.snd g h ≫ h) = fourierMukaiPr3 g h k ≫ k :=
        pullback.condition
      simp only [Category.assoc, fourierMukaiPr13_snd_assoc, fourierMukaiQuadLiftXYZ_pr3_assoc]
      rw [h₁])

/-- The `X ×_S Z`-component of `fourierMukaiQuadLiftXZW a b w` is that of
`fourierMukaiQuadLiftXYZ a b w`. -/
@[reassoc (attr := simp)] lemma fourierMukaiQuadLiftXZW_pr12 :
    fourierMukaiQuadLiftXZW a b w ≫ fourierMukaiPr12 f h k =
      fourierMukaiQuadLiftXYZ a b w ≫ fourierMukaiPr13 f g h :=
  pullback.lift_fst _ _ _

/-- The `W`-component of `fourierMukaiQuadLiftXZW a b w` is that of `a`. -/
@[reassoc (attr := simp)] lemma fourierMukaiQuadLiftXZW_pr3 :
    fourierMukaiQuadLiftXZW a b w ≫ fourierMukaiPr3 f h k = a ≫ fourierMukaiPr3 g h k :=
  pullback.lift_snd _ _ _

/-- The lift of a cone over the right square to the quadruple product. -/
def fourierMukaiQuadLift : T ⟶ fourierMukaiQuadrupleProduct f g h k :=
  pullback.lift (fourierMukaiQuadLiftXYZ a b w) (fourierMukaiQuadLiftXZW a b w)
    (pullback.lift_fst _ _ _).symm

/-- The projection of `fourierMukaiQuadLift a b w` to `X ×_S Y ×_S Z` is
`fourierMukaiQuadLiftXYZ a b w`. -/
@[reassoc (attr := simp)] lemma fourierMukaiQuadLift_toXYZ :
    fourierMukaiQuadLift a b w ≫ fourierMukaiQuadToXYZ f g h k = fourierMukaiQuadLiftXYZ a b w :=
  pullback.lift_fst _ _ _

/-- The projection of `fourierMukaiQuadLift a b w` to `X ×_S Z ×_S W` is
`fourierMukaiQuadLiftXZW a b w`. -/
@[reassoc (attr := simp)] lemma fourierMukaiQuadLift_toXZW :
    fourierMukaiQuadLift a b w ≫ fourierMukaiQuadToXZW f g h k = fourierMukaiQuadLiftXZW a b w :=
  pullback.lift_snd _ _ _

/-- The projection of `fourierMukaiQuadLift a b w` to `Y ×_S Z ×_S W` is `a`. -/
lemma fourierMukaiQuadLift_fst :
    fourierMukaiQuadLift a b w ≫ fourierMukaiQuadToYZW f g h k = a := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [fourierMukaiQuadLift_y a b w]
    · simp
  · simp

/-- The projection of `fourierMukaiQuadLift a b w` to `X ×_S Y ×_S W` is `b`. -/
lemma fourierMukaiQuadLift_snd :
    fourierMukaiQuadLift a b w ≫ fourierMukaiQuadToXYW f g h k = b := by
  apply pullback.hom_ext
  · simp
  · simp [fourierMukaiQuadLift_w a b w]

omit w in
/-- A morphism to the quadruple product is the lift of its projections to `Y ×_S Z ×_S W` and
`X ×_S Y ×_S W`. -/
lemma fourierMukaiQuadLift_uniq (m : T ⟶ fourierMukaiQuadrupleProduct f g h k)
    (hm₁ : m ≫ fourierMukaiQuadToYZW f g h k = a) (hm₂ : m ≫ fourierMukaiQuadToXYW f g h k = b) :
    m = fourierMukaiQuadLift a b (by rw [← hm₁, ← hm₂, Category.assoc, Category.assoc,
      fourierMukaiQuad_right_w]) := by
  subst hm₁ hm₂
  have ha : m ≫ fourierMukaiQuadToXYZ f g h k = fourierMukaiQuadLiftXYZ
      (m ≫ fourierMukaiQuadToYZW f g h k) (m ≫ fourierMukaiQuadToXYW f g h k) (by
        rw [Category.assoc, Category.assoc, fourierMukaiQuad_right_w]) := by
    apply pullback.hom_ext
    · simp
    · simp
  apply pullback.hom_ext
  · simpa using ha
  · apply pullback.hom_ext
    · simp [← reassoc_of% ha]
    · simp

end Lift

/-- **The quadruple product is the fibre product of `Y ×_S Z ×_S W` and `X ×_S Y ×_S W` over
`Y ×_S W`**: the square with sides `pr^{1234}_{234}`, `pr^{1234}_{124}` over `pr^{234}_{24}` and
`pr^{124}_{24}` is cartesian. This is the square the right-hand half of the source's chain takes
base change along. -/
lemma isPullback_fourierMukaiQuad_right :
    IsPullback (fourierMukaiQuadToYZW f g h k) (fourierMukaiQuadToXYW f g h k)
      (fourierMukaiPr13 g h k) (fourierMukaiPr23 f g k) :=
  ⟨⟨fourierMukaiQuad_right_w f g h k⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => fourierMukaiQuadLift s.fst s.snd s.condition)
    (fun s => fourierMukaiQuadLift_fst s.fst s.snd s.condition)
    (fun s => fourierMukaiQuadLift_snd s.fst s.snd s.condition)
    (fun s m hm₁ hm₂ => fourierMukaiQuadLift_uniq s.fst s.snd m hm₁ hm₂)⟩⟩

end Geometry

/-! ### Three canonical isomorphisms of derived functors on schemes -/

section Helpers

variable (V : Scheme.{u})

/-- **Commutativity of the derived tensor product** as an isomorphism of functors
`- ⊗^𝐋 A ≅ A ⊗^𝐋 -`: the braiding of the symmetric monoidal structure of [Stacks, Tag 0FPB],
whose tensor bifunctor is `derivedTensorProductFunctor` on the nose. Only its naturality is
used. -/
def dtenBraidIso (A : DerivedCategory V.Modules) :
    dtenR V A ≅ (derivedTensorProductFunctor V.toRingedSpace.sheaf).obj A :=
  letI : MonoidalCategory (DerivedCategory V.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal V.toRingedSpace.sheaf
  letI : SymmetricCategory (DerivedCategory V.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric V.toRingedSpace.sheaf
  (BraidedCategory.tensorLeftIsoTensorRight A).symm

/-- **Associativity of the derived tensor product** as an isomorphism of functors
`(- ⊗^𝐋 A) ⊗^𝐋 B ≅ - ⊗^𝐋 (A ⊗^𝐋 B)`: the associator of the monoidal structure of
[Stacks, Tag 0FPB]. Only its naturality is used. -/
def dtenAssocIso (A B : DerivedCategory V.Modules) :
    dtenR V A ⋙ dtenR V B ≅ dtenR V ((dtenR V B).obj A) :=
  letI : MonoidalCategory (DerivedCategory V.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal V.toRingedSpace.sheaf
  (tensorRightTensor A B).symm

/-- **[Stacks, Tag 0D5T] for schemes**, at two factorizations of one morphism:
`R p_* ⋙ R q_* ≅ R p'_* ⋙ R q'_*` when `p ≫ q = p' ≫ q'`. -/
def dpushCompIsoOfEq {U V₁ V₂ W : Scheme.{u}} (p : U ⟶ V₁) (q : V₁ ⟶ W) (p' : U ⟶ V₂)
    (q' : V₂ ⟶ W) (hpq : p ≫ q = p' ≫ q') : dpush p ⋙ dpush q ≅ dpush p' ⋙ dpush q' :=
  derivedPushforwardCompIso p.toLRSHom.toShHom q.toLRSHom.toShHom ≪≫
    eqToIso (by rw [shHom_comp_eq hpq]) ≪≫
    (derivedPushforwardCompIso p'.toLRSHom.toShHom q'.toLRSHom.toShHom).symm

end Helpers

/-! ### The two halves of the chain -/

section Assoc

variable {S X Y Z W : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (k : W ⟶ S)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
  [QuasiCompact h] [QuasiSeparated h] [QuasiCompact k] [QuasiSeparated k]

/-- `pr^{124}_{24}` is flat when `X ⟶ S` is, being a base change of `pr_2 : X ×_S Y ⟶ Y`. -/
instance flat_fourierMukaiPr23_of_flat [Flat f] : Flat (fourierMukaiPr23 f g k) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_fourierMukaiPr12_pr23 f g k)
    inferInstance

/-- `pr^{1234}_{124}` is quasi-compact: followed by the quasi-separated structure morphism of
`X ×_S Y ×_S W` it is a composite of quasi-compact morphisms. -/
instance quasiCompact_fourierMukaiQuadToXYW : QuasiCompact (fourierMukaiQuadToXYW f g h k) := by
  have : QuasiCompact (fourierMukaiQuadToXYW f g h k ≫ (fourierMukaiPr3 f g k ≫ k)) := by
    rw [fourierMukaiQuadToXYW_pr3_assoc]; infer_instance
  exact QuasiCompact.of_comp (fourierMukaiQuadToXYW f g h k) (fourierMukaiPr3 f g k ≫ k)

/-- `pr^{1234}_{124}` is quasi-separated, for the same reason. -/
instance quasiSeparated_fourierMukaiQuadToXYW :
    QuasiSeparated (fourierMukaiQuadToXYW f g h k) := by
  have : QuasiSeparated (fourierMukaiQuadToXYW f g h k ≫ (fourierMukaiPr3 f g k ≫ k)) := by
    rw [fourierMukaiQuadToXYW_pr3_assoc]; infer_instance
  exact QuasiSeparated.of_comp (fourierMukaiQuadToXYW f g h k) (fourierMukaiPr3 f g k ≫ k)

variable {f g h k}

/-- The base-change step of the left half: [Stacks, Tag 08IB] along the defining square of the
quadruple product, at the convolution tensor of `c` and `c'`. -/
theorem isIso_fourierMukaiConvolutionAssocLeft_baseChange [Flat k]
    {c : DerivedCategory (pullback f g).Modules} (hc : IsQCohAll c)
    {c' : DerivedCategory (pullback g h).Modules} (hc' : IsQCohAll c') :
    IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
      (fourierMukaiQuadToXYZ f g h k).toLRSHom.toShHom
      (fourierMukaiQuadToXZW f g h k).toLRSHom.toShHom
      (fourierMukaiPr13 f g h).toLRSHom.toShHom (fourierMukaiPr12 f h k).toLRSHom.toShHom
      (shHom_comp_eq (pullback.condition (f := fourierMukaiPr13 f g h)
        (g := fourierMukaiPr12 f h k))) (fourierMukaiConvolutionTensor f g h c c')) :=
  derivedBaseChangeIsIsoOnQuasicoherent _ _ _ _ (IsPullback.of_hasPullback _ _) inferInstance
    inferInstance (torIndependent_of_flat_right _ _) _ _
    (isQCohAll_dtenR (isQCohAll_dpull _ hc) (isQCohAll_dpull _ hc'))

/-- The projection-formula step of the left half: [Stacks, Tag 08EU] along `pr^{1234}_{134}`. -/
theorem isIso_fourierMukaiConvolutionAssocLeft_projection
    {c : DerivedCategory (pullback f g).Modules} (hc : IsQCohAll c)
    {c' : DerivedCategory (pullback g h).Modules} (hc' : IsQCohAll c')
    {c'' : DerivedCategory (pullback h k).Modules} (hc'' : IsQCohAll c'') :
    IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
      (fourierMukaiQuadToXZW f g h k).toLRSHom.toShHom
      ((dpull (fourierMukaiQuadToXYZ f g h k)).obj (fourierMukaiConvolutionTensor f g h c c'))
      ((dpull (fourierMukaiPr23 f h k)).obj c'')) :=
  Stacks.Cohomology.ProjectionFormulaQCoh.projectionFormulaMap_isIso_of_isQuasicoherent_homology
    (fourierMukaiQuadToXZW f g h k) inferInstance inferInstance _ _
    (isQCohAll_dpull _ (isQCohAll_dtenR (isQCohAll_dpull _ hc) (isQCohAll_dpull _ hc')))
    (isQCohAll_dpull _ hc'')

/-- Step 1 of the left half: [Stacks, Tag 08IB] along the defining square of the quadruple
product. -/
def fourierMukaiConvolutionAssocLeft₁ [Flat k]
    {c : DerivedCategory (pullback f g).Modules} (hc : IsQCohAll c)
    {c' : DerivedCategory (pullback g h).Modules} (hc' : IsQCohAll c')
    {c'' : DerivedCategory (pullback h k).Modules} (hc'' : IsQCohAll c'') :
    fourierMukaiConvolution f h k (fourierMukaiConvolution f g h c c') c'' ≅
      (dpush (fourierMukaiPr13 f h k)).obj ((dtenR _ ((dpull (fourierMukaiPr23 f h k)).obj c'')).obj
        ((dpush (fourierMukaiQuadToXZW f g h k)).obj
          ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
            (fourierMukaiConvolutionTensor f g h c c')))) :=
  (dpush (fourierMukaiPr13 f h k)).mapIso
    ((dtenR _ ((dpull (fourierMukaiPr23 f h k)).obj c'')).mapIso
      (@asIso _ _ _ _ _ (isIso_fourierMukaiConvolutionAssocLeft_baseChange (k := k) hc hc')))

/-- Step 2 of the left half: the projection formula for `pr^{1234}_{134}`. -/
def fourierMukaiConvolutionAssocLeft₂ [Flat k]
    {c : DerivedCategory (pullback f g).Modules} (hc : IsQCohAll c)
    {c' : DerivedCategory (pullback g h).Modules} (hc' : IsQCohAll c')
    {c'' : DerivedCategory (pullback h k).Modules} (hc'' : IsQCohAll c'') :
    (dpush (fourierMukaiPr13 f h k)).obj ((dtenR _ ((dpull (fourierMukaiPr23 f h k)).obj c'')).obj
        ((dpush (fourierMukaiQuadToXZW f g h k)).obj
          ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
            (fourierMukaiConvolutionTensor f g h c c')))) ≅
      (dpush (fourierMukaiPr13 f h k)).obj ((dpush (fourierMukaiQuadToXZW f g h k)).obj
        ((dtenR _ ((dpull (fourierMukaiQuadToXZW f g h k)).obj
            ((dpull (fourierMukaiPr23 f h k)).obj c''))).obj
          ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
            (fourierMukaiConvolutionTensor f g h c c')))) :=
  (dpush (fourierMukaiPr13 f h k)).mapIso
    (@asIso _ _ _ _ _ (isIso_fourierMukaiConvolutionAssocLeft_projection hc hc' hc''))

/-- Step 3 of the left half: the monoidality of derived pullback along `pr^{1234}_{123}`. -/
def fourierMukaiConvolutionAssocLeft₃ (c : DerivedCategory (pullback f g).Modules)
    (c' : DerivedCategory (pullback g h).Modules) (c'' : DerivedCategory (pullback h k).Modules) :
    (dpush (fourierMukaiPr13 f h k)).obj ((dpush (fourierMukaiQuadToXZW f g h k)).obj
        ((dtenR _ ((dpull (fourierMukaiQuadToXZW f g h k)).obj
            ((dpull (fourierMukaiPr23 f h k)).obj c''))).obj
          ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
            (fourierMukaiConvolutionTensor f g h c c')))) ≅
      (dpush (fourierMukaiPr13 f h k)).obj ((dpush (fourierMukaiQuadToXZW f g h k)).obj
        ((dtenR _ ((dpull (fourierMukaiQuadToXZW f g h k)).obj
            ((dpull (fourierMukaiPr23 f h k)).obj c''))).obj
          ((dtenR _ ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr23 f g h)).obj c'))).obj
            ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr12 f g h)).obj c))))) :=
  (dpush (fourierMukaiPr13 f h k)).mapIso ((dpush (fourierMukaiQuadToXZW f g h k)).mapIso
    ((dtenR _ ((dpull (fourierMukaiQuadToXZW f g h k)).obj
        ((dpull (fourierMukaiPr23 f h k)).obj c''))).mapIso
      ((dpullTensorIso (fourierMukaiQuadToXYZ f g h k)
        ((dpull (fourierMukaiPr23 f g h)).obj c')).app ((dpull (fourierMukaiPr12 f g h)).obj c))))

/-- **The left half of the chain**: the isomorphism
`c'' ∘ (c' ∘ c) ≅ R pr^{134}_{14,*} R pr^{1234}_{134,*}((pr_{12}^*c ⊗ pr_{23}^*c') ⊗ pr_{34}^*c'')`
given by [Stacks, Tag 08IB] along the defining square of the quadruple product, the projection
formula for `pr^{1234}_{134}` and the monoidality of derived pullback. -/
def fourierMukaiConvolutionAssocLeft [Flat k]
    {c : DerivedCategory (pullback f g).Modules} (hc : IsQCohAll c)
    {c' : DerivedCategory (pullback g h).Modules} (hc' : IsQCohAll c')
    {c'' : DerivedCategory (pullback h k).Modules} (hc'' : IsQCohAll c'') :
    fourierMukaiConvolution f h k (fourierMukaiConvolution f g h c c') c'' ≅
      (dpush (fourierMukaiPr13 f h k)).obj ((dpush (fourierMukaiQuadToXZW f g h k)).obj
        ((dtenR _ ((dpull (fourierMukaiQuadToXZW f g h k)).obj
            ((dpull (fourierMukaiPr23 f h k)).obj c''))).obj
          ((dtenR _ ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr23 f g h)).obj c'))).obj
            ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr12 f g h)).obj c))))) :=
  fourierMukaiConvolutionAssocLeft₁ hc hc' hc'' ≪≫ fourierMukaiConvolutionAssocLeft₂ hc hc' hc'' ≪≫
    fourierMukaiConvolutionAssocLeft₃ c c' c''

/-- The base-change step of the right half: [Stacks, Tag 08IB] along the square of
`isPullback_fourierMukaiQuad_right`, at the convolution tensor of `c'` and `c''`. -/
theorem isIso_fourierMukaiConvolutionAssocRight_baseChange [Flat f]
    {c' : DerivedCategory (pullback g h).Modules} (hc' : IsQCohAll c')
    {c'' : DerivedCategory (pullback h k).Modules} (hc'' : IsQCohAll c'') :
    IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
      (fourierMukaiQuadToYZW f g h k).toLRSHom.toShHom
      (fourierMukaiQuadToXYW f g h k).toLRSHom.toShHom
      (fourierMukaiPr13 g h k).toLRSHom.toShHom (fourierMukaiPr23 f g k).toLRSHom.toShHom
      (shHom_comp_eq (fourierMukaiQuad_right_w f g h k))
      (fourierMukaiConvolutionTensor g h k c' c'')) :=
  derivedBaseChangeIsIsoOnQuasicoherent _ _ _ _ (isPullback_fourierMukaiQuad_right f g h k)
    inferInstance inferInstance (torIndependent_of_flat_right _ _) _ _
    (isQCohAll_dtenR (isQCohAll_dpull _ hc') (isQCohAll_dpull _ hc''))

/-- The projection-formula step of the right half: [Stacks, Tag 08EU] along
`pr^{1234}_{124}`. -/
theorem isIso_fourierMukaiConvolutionAssocRight_projection
    {c : DerivedCategory (pullback f g).Modules} (hc : IsQCohAll c)
    {c' : DerivedCategory (pullback g h).Modules} (hc' : IsQCohAll c')
    {c'' : DerivedCategory (pullback h k).Modules} (hc'' : IsQCohAll c'') :
    IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
      (fourierMukaiQuadToXYW f g h k).toLRSHom.toShHom
      ((dpull (fourierMukaiQuadToYZW f g h k)).obj (fourierMukaiConvolutionTensor g h k c' c''))
      ((dpull (fourierMukaiPr12 f g k)).obj c)) :=
  Stacks.Cohomology.ProjectionFormulaQCoh.projectionFormulaMap_isIso_of_isQuasicoherent_homology
    (fourierMukaiQuadToXYW f g h k) inferInstance inferInstance _ _
    (isQCohAll_dpull _ (isQCohAll_dtenR (isQCohAll_dpull _ hc') (isQCohAll_dpull _ hc'')))
    (isQCohAll_dpull _ hc)

/-- Step 1 of the right half: [Stacks, Tag 08IB] along the square of
`isPullback_fourierMukaiQuad_right`. -/
def fourierMukaiConvolutionAssocRight₁ [Flat f]
    {c : DerivedCategory (pullback f g).Modules} (hc : IsQCohAll c)
    {c' : DerivedCategory (pullback g h).Modules} (hc' : IsQCohAll c')
    {c'' : DerivedCategory (pullback h k).Modules} (hc'' : IsQCohAll c'') :
    fourierMukaiConvolution f g k c (fourierMukaiConvolution g h k c' c'') ≅
      (dpush (fourierMukaiPr13 f g k)).obj
        ((dtenR _ ((dpush (fourierMukaiQuadToXYW f g h k)).obj
            ((dpull (fourierMukaiQuadToYZW f g h k)).obj
              (fourierMukaiConvolutionTensor g h k c' c'')))).obj
          ((dpull (fourierMukaiPr12 f g k)).obj c)) :=
  (dpush (fourierMukaiPr13 f g k)).mapIso (((derivedTensorProductFunctor _).flip.mapIso
    (@asIso _ _ _ _ _ (isIso_fourierMukaiConvolutionAssocRight_baseChange (f := f) hc' hc''))).app
      ((dpull (fourierMukaiPr12 f g k)).obj c))

/-- Step 2 of the right half: the commutativity constraint, moving the direct image into the left
slot. -/
def fourierMukaiConvolutionAssocRight₂ (c : DerivedCategory (pullback f g).Modules)
    (c' : DerivedCategory (pullback g h).Modules) (c'' : DerivedCategory (pullback h k).Modules) :
    (dpush (fourierMukaiPr13 f g k)).obj
        ((dtenR _ ((dpush (fourierMukaiQuadToXYW f g h k)).obj
            ((dpull (fourierMukaiQuadToYZW f g h k)).obj
              (fourierMukaiConvolutionTensor g h k c' c'')))).obj
          ((dpull (fourierMukaiPr12 f g k)).obj c)) ≅
      (dpush (fourierMukaiPr13 f g k)).obj
        (((derivedTensorProductFunctor (fourierMukaiTripleProduct f g k).toRingedSpace.sheaf).obj
            ((dpush (fourierMukaiQuadToXYW f g h k)).obj
              ((dpull (fourierMukaiQuadToYZW f g h k)).obj
                (fourierMukaiConvolutionTensor g h k c' c'')))).obj
          ((dpull (fourierMukaiPr12 f g k)).obj c)) :=
  (dpush (fourierMukaiPr13 f g k)).mapIso
    ((dtenBraidIso _ ((dpush (fourierMukaiQuadToXYW f g h k)).obj
        ((dpull (fourierMukaiQuadToYZW f g h k)).obj
          (fourierMukaiConvolutionTensor g h k c' c'')))).app
      ((dpull (fourierMukaiPr12 f g k)).obj c))

/-- Step 3 of the right half: the projection formula for `pr^{1234}_{124}`. -/
def fourierMukaiConvolutionAssocRight₃ [Flat f]
    {c : DerivedCategory (pullback f g).Modules} (hc : IsQCohAll c)
    {c' : DerivedCategory (pullback g h).Modules} (hc' : IsQCohAll c')
    {c'' : DerivedCategory (pullback h k).Modules} (hc'' : IsQCohAll c'') :
    (dpush (fourierMukaiPr13 f g k)).obj
        (((derivedTensorProductFunctor (fourierMukaiTripleProduct f g k).toRingedSpace.sheaf).obj
            ((dpush (fourierMukaiQuadToXYW f g h k)).obj
              ((dpull (fourierMukaiQuadToYZW f g h k)).obj
                (fourierMukaiConvolutionTensor g h k c' c'')))).obj
          ((dpull (fourierMukaiPr12 f g k)).obj c)) ≅
      (dpush (fourierMukaiPr13 f g k)).obj ((dpush (fourierMukaiQuadToXYW f g h k)).obj
        (((derivedTensorProductFunctor
                (fourierMukaiQuadrupleProduct f g h k).toRingedSpace.sheaf).obj
            ((dpull (fourierMukaiQuadToYZW f g h k)).obj
              (fourierMukaiConvolutionTensor g h k c' c''))).obj
          ((dpull (fourierMukaiQuadToXYW f g h k)).obj
            ((dpull (fourierMukaiPr12 f g k)).obj c)))) :=
  (dpush (fourierMukaiPr13 f g k)).mapIso
    (@asIso _ _ _ _ _ (isIso_fourierMukaiConvolutionAssocRight_projection hc hc' hc''))

/-- Step 4 of the right half: the commutativity constraint once more. -/
def fourierMukaiConvolutionAssocRight₄ (c : DerivedCategory (pullback f g).Modules)
    (c' : DerivedCategory (pullback g h).Modules) (c'' : DerivedCategory (pullback h k).Modules) :
    (dpush (fourierMukaiPr13 f g k)).obj ((dpush (fourierMukaiQuadToXYW f g h k)).obj
        (((derivedTensorProductFunctor
                (fourierMukaiQuadrupleProduct f g h k).toRingedSpace.sheaf).obj
            ((dpull (fourierMukaiQuadToYZW f g h k)).obj
              (fourierMukaiConvolutionTensor g h k c' c''))).obj
          ((dpull (fourierMukaiQuadToXYW f g h k)).obj
            ((dpull (fourierMukaiPr12 f g k)).obj c)))) ≅
      (dpush (fourierMukaiPr13 f g k)).obj ((dpush (fourierMukaiQuadToXYW f g h k)).obj
        (((derivedTensorProductFunctor
                (fourierMukaiQuadrupleProduct f g h k).toRingedSpace.sheaf).obj
            ((dpull (fourierMukaiQuadToXYW f g h k)).obj
              ((dpull (fourierMukaiPr12 f g k)).obj c))).obj
          ((dpull (fourierMukaiQuadToYZW f g h k)).obj
            (fourierMukaiConvolutionTensor g h k c' c'')))) :=
  (dpush (fourierMukaiPr13 f g k)).mapIso ((dpush (fourierMukaiQuadToXYW f g h k)).mapIso
    ((dtenBraidIso _ ((dpull (fourierMukaiQuadToXYW f g h k)).obj
        ((dpull (fourierMukaiPr12 f g k)).obj c))).app
      ((dpull (fourierMukaiQuadToYZW f g h k)).obj
        (fourierMukaiConvolutionTensor g h k c' c''))))

/-- Step 5 of the right half: the monoidality and the composition isomorphisms of derived
pullback. -/
def fourierMukaiConvolutionAssocRight₅ (c : DerivedCategory (pullback f g).Modules)
    (c' : DerivedCategory (pullback g h).Modules) (c'' : DerivedCategory (pullback h k).Modules) :
    (dpush (fourierMukaiPr13 f g k)).obj ((dpush (fourierMukaiQuadToXYW f g h k)).obj
        (((derivedTensorProductFunctor
                (fourierMukaiQuadrupleProduct f g h k).toRingedSpace.sheaf).obj
            ((dpull (fourierMukaiQuadToXYW f g h k)).obj
              ((dpull (fourierMukaiPr12 f g k)).obj c))).obj
          ((dpull (fourierMukaiQuadToYZW f g h k)).obj
            (fourierMukaiConvolutionTensor g h k c' c'')))) ≅
      (dpush (fourierMukaiPr13 f g k)).obj ((dpush (fourierMukaiQuadToXYW f g h k)).obj
        (((derivedTensorProductFunctor
                (fourierMukaiQuadrupleProduct f g h k).toRingedSpace.sheaf).obj
            ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr12 f g h)).obj c))).obj
          ((dtenR _ ((dpull (fourierMukaiQuadToXZW f g h k)).obj
              ((dpull (fourierMukaiPr23 f h k)).obj c''))).obj
            ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr23 f g h)).obj c'))))) :=
  (dpush (fourierMukaiPr13 f g k)).mapIso ((dpush (fourierMukaiQuadToXYW f g h k)).mapIso
    (((derivedTensorProductFunctor (fourierMukaiQuadrupleProduct f g h k).toRingedSpace.sheaf).obj
        ((dpull (fourierMukaiQuadToXYW f g h k)).obj
          ((dpull (fourierMukaiPr12 f g k)).obj c))).mapIso
    ((dpullTensorIso (fourierMukaiQuadToYZW f g h k) ((dpull (fourierMukaiPr23 g h k)).obj c'')).app
        ((dpull (fourierMukaiPr12 g h k)).obj c') ≪≫
      ((derivedTensorProductFunctor
          (fourierMukaiQuadrupleProduct f g h k).toRingedSpace.sheaf).flip.mapIso
        ((dpullCompIsoEq (fourierMukaiQuadToYZW f g h k) (fourierMukaiPr23 g h k)
        (fourierMukaiQuadToXZW f g h k) (fourierMukaiPr23 f h k)
        (fourierMukaiQuadToYZW_pr23 f g h k)).app c'')).app
          ((dpull (fourierMukaiQuadToYZW f g h k)).obj ((dpull (fourierMukaiPr12 g h k)).obj c')) ≪≫
      (dtenR _ ((dpull (fourierMukaiQuadToXZW f g h k)).obj
          ((dpull (fourierMukaiPr23 f h k)).obj c''))).mapIso
        ((dpullCompIsoEq (fourierMukaiQuadToYZW f g h k)
        (fourierMukaiPr12 g h k) (fourierMukaiQuadToXYZ f g h k) (fourierMukaiPr23 f g h)
        (fourierMukaiQuadToYZW_pr12 f g h k)).app c')) ≪≫
    ((derivedTensorProductFunctor (fourierMukaiQuadrupleProduct f g h k).toRingedSpace.sheaf).mapIso
      ((dpullCompIsoEq (fourierMukaiQuadToXYW f g h k) (fourierMukaiPr12 f g k)
      (fourierMukaiQuadToXYZ f g h k) (fourierMukaiPr12 f g h)
      (fourierMukaiQuadToXYW_pr12 f g h k)).app c)).app _))

/-- Step 6 of the right half: associativity of the derived tensor product. -/
def fourierMukaiConvolutionAssocRight₆ (c : DerivedCategory (pullback f g).Modules)
    (c' : DerivedCategory (pullback g h).Modules) (c'' : DerivedCategory (pullback h k).Modules) :
    (dpush (fourierMukaiPr13 f g k)).obj ((dpush (fourierMukaiQuadToXYW f g h k)).obj
        (((derivedTensorProductFunctor
                (fourierMukaiQuadrupleProduct f g h k).toRingedSpace.sheaf).obj
            ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr12 f g h)).obj c))).obj
          ((dtenR _ ((dpull (fourierMukaiQuadToXZW f g h k)).obj
              ((dpull (fourierMukaiPr23 f h k)).obj c''))).obj
            ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr23 f g h)).obj c'))))) ≅
      (dpush (fourierMukaiPr13 f g k)).obj ((dpush (fourierMukaiQuadToXYW f g h k)).obj
        ((dtenR _ ((dpull (fourierMukaiQuadToXZW f g h k)).obj
            ((dpull (fourierMukaiPr23 f h k)).obj c''))).obj
          ((dtenR _ ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr23 f g h)).obj c'))).obj
            ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr12 f g h)).obj c))))) :=
  (dpush (fourierMukaiPr13 f g k)).mapIso ((dpush (fourierMukaiQuadToXYW f g h k)).mapIso
    ((dtenAssocIso _ ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
        ((dpull (fourierMukaiPr23 f g h)).obj c'))
        ((dpull (fourierMukaiQuadToXZW f g h k)).obj
          ((dpull (fourierMukaiPr23 f h k)).obj c''))).app
      ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
        ((dpull (fourierMukaiPr12 f g h)).obj c))).symm)

/-- Step 7 of the right half: the composition isomorphism of derived direct image. -/
def fourierMukaiConvolutionAssocRight₇ (c : DerivedCategory (pullback f g).Modules)
    (c' : DerivedCategory (pullback g h).Modules) (c'' : DerivedCategory (pullback h k).Modules) :
    (dpush (fourierMukaiPr13 f g k)).obj ((dpush (fourierMukaiQuadToXYW f g h k)).obj
        ((dtenR _ ((dpull (fourierMukaiQuadToXZW f g h k)).obj
            ((dpull (fourierMukaiPr23 f h k)).obj c''))).obj
          ((dtenR _ ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr23 f g h)).obj c'))).obj
            ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr12 f g h)).obj c))))) ≅
      (dpush (fourierMukaiPr13 f h k)).obj ((dpush (fourierMukaiQuadToXZW f g h k)).obj
        ((dtenR _ ((dpull (fourierMukaiQuadToXZW f g h k)).obj
            ((dpull (fourierMukaiPr23 f h k)).obj c''))).obj
          ((dtenR _ ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr23 f g h)).obj c'))).obj
            ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr12 f g h)).obj c))))) :=
  (dpushCompIsoOfEq (fourierMukaiQuadToXYW f g h k) (fourierMukaiPr13 f g k)
    (fourierMukaiQuadToXZW f g h k) (fourierMukaiPr13 f h k)
    (fourierMukaiQuadToXYW_pr13 f g h k)).app _

/-- **The right half of the chain**: the isomorphism
`(c'' ∘ c') ∘ c ≅ R pr^{134}_{14,*} R pr^{1234}_{134,*}((pr_{12}^*c ⊗ pr_{23}^*c') ⊗ pr_{34}^*c'')`
given by [Stacks, Tag 08IB] along the square of `isPullback_fourierMukaiQuad_right`, the projection
formula for `pr^{1234}_{124}` between two commutativity constraints, the monoidality and the
composition isomorphisms of derived pullback, associativity of `⊗^𝐋`, and the composition
isomorphism of derived direct image. -/
def fourierMukaiConvolutionAssocRight [Flat f]
    {c : DerivedCategory (pullback f g).Modules} (hc : IsQCohAll c)
    {c' : DerivedCategory (pullback g h).Modules} (hc' : IsQCohAll c')
    {c'' : DerivedCategory (pullback h k).Modules} (hc'' : IsQCohAll c'') :
    fourierMukaiConvolution f g k c (fourierMukaiConvolution g h k c' c'') ≅
      (dpush (fourierMukaiPr13 f h k)).obj ((dpush (fourierMukaiQuadToXZW f g h k)).obj
        ((dtenR _ ((dpull (fourierMukaiQuadToXZW f g h k)).obj
            ((dpull (fourierMukaiPr23 f h k)).obj c''))).obj
          ((dtenR _ ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr23 f g h)).obj c'))).obj
            ((dpull (fourierMukaiQuadToXYZ f g h k)).obj
              ((dpull (fourierMukaiPr12 f g h)).obj c))))) :=
  fourierMukaiConvolutionAssocRight₁ hc hc' hc'' ≪≫ fourierMukaiConvolutionAssocRight₂ c c' c'' ≪≫
    fourierMukaiConvolutionAssocRight₃ hc hc' hc'' ≪≫ fourierMukaiConvolutionAssocRight₄ c c' c'' ≪≫
    fourierMukaiConvolutionAssocRight₅ c c' c'' ≪≫ fourierMukaiConvolutionAssocRight₆ c c' c'' ≪≫
    fourierMukaiConvolutionAssocRight₇ c c' c''

/-- **Associativity of the convolution of Fourier-Mukai kernels.** For schemes `X`, `Y`, `Z`,
`W` over `S` with quasi-compact and quasi-separated structure morphisms, `X ⟶ S` and `W ⟶ S`
flat, and kernels `c`, `c'`, `c''` on `X ×_S Y`, `Y ×_S Z`, `Z ×_S W` with quasi-coherent
cohomology sheaves,

`c'' ∘ (c' ∘ c) ≅ (c'' ∘ c') ∘ c`

where `∘` is the convolution `AlgebraicGeometry.fourierMukaiConvolution` of [Stacks, Tag 0FYS].
This is the associativity verified in Section 0G0F of the source, by the source's chain: both
sides are identified with
`R pr^{1234}_{14,*}((pr_{12}^*c ⊗^𝐋 pr_{23}^*c') ⊗^𝐋 pr_{34}^*c'')`. -/
def fourierMukaiConvolutionAssocIso [Flat f] [Flat k]
    {c : DerivedCategory (pullback f g).Modules} (hc : IsQCohAll c)
    {c' : DerivedCategory (pullback g h).Modules} (hc' : IsQCohAll c')
    {c'' : DerivedCategory (pullback h k).Modules} (hc'' : IsQCohAll c'') :
    fourierMukaiConvolution f h k (fourierMukaiConvolution f g h c c') c'' ≅
      fourierMukaiConvolution f g k c (fourierMukaiConvolution g h k c' c'') :=
  fourierMukaiConvolutionAssocLeft hc hc' hc'' ≪≫
    (fourierMukaiConvolutionAssocRight hc hc' hc'').symm

end Assoc

end AlgebraicGeometry

end
