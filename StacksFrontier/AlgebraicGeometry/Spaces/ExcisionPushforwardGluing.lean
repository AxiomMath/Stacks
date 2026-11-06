module

public import StacksFrontier.AlgebraicGeometry.Spaces.ExcisionDiagonalCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.ExcisionPushforwardComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfMorphismDescent

/-!
# Amalgamating a morphism to a modification over the fibre square

Let `f : V ⟶ W` be a separated étale morphism of algebraic spaces over a scheme `S`, let `T` be
a subfunctor of `W` whose preimage is carried isomorphically onto it, let `W₀` contain the open
complement of `T`, and let `h : Y ⟶ V` become an isomorphism over `f^{-1}W₀`.

Let `Q` be an algebraic space over the fibre square `V ×_W V`, say by `κ`. The two pieces of the
fibre square cover `Q`, and a morphism `Q ⟶ Y` over `V` — that is, a lift along `h` of
`κ` followed by the second projection — is determined by its restriction to the diagonal piece,
and any lift on the diagonal piece extends to one on all of `Q`. On the complementary piece
there is nothing to choose: the morphism to `V` lands in `f^{-1}W₀`, where `h` is invertible.

This is the amalgamation step used twice in the proof of Stacks 0BGY: once to build the
canonical morphism `Y ×_W V ⟶ Y` out of which the quasi-inverse of the base-change functor is
made, and once to see that the base change of that quasi-inverse is the identity.

## Main results

* `AlgebraicGeometry.Space.excisionGlue_ext`: two lifts which agree on the diagonal piece are
  equal.
* `AlgebraicGeometry.Space.excisionGlue_exists`: a lift on the diagonal piece extends to a lift
  on the whole of `Q`.

## Implementation notes

Both statements are fppf descent along the two-element covering
`AlgebraicGeometry.Space.isFppfCovering_diagPair_preimage`: the uniqueness half is
`AlgebraicGeometry.Space.hom_ext_of_isFppfCovering` and the existence half
`AlgebraicGeometry.Space.existsUnique_desc_of_isFppfCovering`. The compatibility the latter asks
for on the two diagonal fibre products is the equality of the two projections of the fibre
square of a monomorphism, and on the two mixed ones it is the uniqueness of a lift over
`f^{-1}W₀`, available because the common composite factors through the complementary piece.

The family is indexed by `Bool`, the diagonal piece at `false` and the complementary piece at
`true`, so that the morphism being descended is given by `Bool.rec` and the four compatibility
cases are `cases`.

## References

* [Stacks Project, Tag 0469](https://stacks.math.columbia.edu/tag/0469)
* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_ExcisionPushforwardGluing :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ExcisionPushforwardGluing
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable
  {V W Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W) (h : Y ⟶ V)
  (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
  (hY : IsAlgebraicSpace B S hS Y) (T W₀ : Subfunctor W)
  (hT : IsIso (T.fromPreimage f)) (hcompl : openComplement B S hS T ≤ W₀)
  (hf : IsEtale B S hS f) (hsep : IsSeparated B S hS f)
  (hiso : IsIso (pullback.snd h (W₀.preimage f).ι))
  {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (κ : Q ⟶ pullback f f)
  (hQ : IsAlgebraicSpace B S hS Q)

include hV hW hf hsep hT hcompl in
/-- On the complementary piece of the fibre square the composite to `V` lands in the locus over
which `h` is invertible. -/
theorem range_offDiagPreimage_snd_le :
    Subfunctor.range (((offDiagOpen B S hS f).preimage κ).ι ≫ κ ≫ pullback.snd f f)
      ≤ W₀.preimage f := by
  rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp]
  have hc : (((offDiagOpen B S hS f).preimage κ).ι ≫ κ ≫ pullback.snd f f) ≫ f =
      ((offDiagOpen B S hS f).preimage κ).ι ≫ κ ≫ (pullback.fst f f ≫ f) := by
    simp only [Category.assoc]
    rw [pullback.condition]
  rw [hc]
  exact (range_offDiagPreimage_le_openComplement B S hS f hV hW hf hsep κ T hT).trans hcompl

/-- The two projections of the fibre square of a monomorphism agree. -/
private theorem fst_eq_snd_of_mono {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G)
    [Mono p] : pullback.fst p p = pullback.snd p p :=
  fst_eq_snd_of_mono_eq p

include hV hW hY hf hsep hT hcompl hiso hQ in
/-- **Two lifts along `h` of the second projection which agree on the diagonal piece are
equal.** -/
theorem excisionGlue_ext (m₁ m₂ : Q ⟶ Y)
    (hm₁ : m₁ ≫ h = κ ≫ pullback.snd f f) (hm₂ : m₂ ≫ h = κ ≫ pullback.snd f f)
    (hdiag : ((diagOpen B S hS f).preimage κ).ι ≫ m₁ =
      ((diagOpen B S hS f).preimage κ).ι ≫ m₂) : m₁ = m₂ := by
  refine hom_ext_of_isFppfCovering B S hS _ _
    (isFppfCovering_diagPair_preimage B S hS f hV hW hf hsep κ hQ) hY.isSheaf (fun b => ?_)
  cases b
  · simpa only [diagPair_false] using hdiag
  · simp only [diagPair_true]
    refine lift_unique_of_range_le B S hS h (W₀.preimage f) hiso _
      (range_offDiagPreimage_snd_le B S hS f hV hW T W₀ hT hcompl hf hsep κ) ?_ ?_
    · simp only [Category.assoc, hm₁]
    · simp only [Category.assoc, hm₂]

include hV hW hY hf hsep hT hcompl hiso hQ in
/-- **A lift along `h` on the diagonal piece extends to a lift on the whole of `Q`.** -/
theorem excisionGlue_exists
    (bE : ((diagOpen B S hS f).preimage κ).toFunctor ⟶ Y)
    (hbE : bE ≫ h = ((diagOpen B S hS f).preimage κ).ι ≫ κ ≫ pullback.snd f f) :
    ∃ b : Q ⟶ Y, b ≫ h = κ ≫ pullback.snd f f ∧
      ((diagOpen B S hS f).preimage κ).ι ≫ b = bE := by
  classical
  obtain ⟨bC, hbC⟩ := (existsUnique_lift_of_range_le B S hS h (W₀.preimage f) hiso
    (((offDiagOpen B S hS f).preimage κ).ι ≫ κ ≫ pullback.snd f f)
    (range_offDiagPreimage_snd_le B S hS f hV hW T W₀ hT hcompl hf hsep κ)).exists
  set g : ∀ b : Bool, ((diagPair B S hS f b).preimage κ).toFunctor ⟶ Y :=
    fun b => Bool.rec bE bC b with hg
  have hcov := isFppfCovering_diagPair_preimage B S hS f hV hW hf hsep κ hQ
  have hgE : g false ≫ h =
      ((diagPair B S hS f false).preimage κ).ι ≫ κ ≫ pullback.snd f f := hbE
  have hgC : g true ≫ h =
      ((diagPair B S hS f true).preimage κ).ι ≫ κ ≫ pullback.snd f f := hbC
  have hrangeC : Subfunctor.range
      (((diagPair B S hS f true).preimage κ).ι ≫ κ ≫ pullback.snd f f) ≤ W₀.preimage f :=
    range_offDiagPreimage_snd_le B S hS f hV hW T W₀ hT hcompl hf hsep κ
  have mixed : ∀ {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (a : X ⟶ ((diagPair B S hS f false).preimage κ).toFunctor)
      (c : X ⟶ ((diagPair B S hS f true).preimage κ).toFunctor),
      a ≫ ((diagPair B S hS f false).preimage κ).ι = c ≫ ((diagPair B S hS f true).preimage κ).ι →
      a ≫ g false = c ≫ g true := fun a c hac =>
    lift_unique_of_range_le B S hS h (W₀.preimage f) hiso
      (c ≫ ((diagPair B S hS f true).preimage κ).ι ≫ κ ≫ pullback.snd f f)
      ((Subfunctor.range_comp_le _ _).trans hrangeC)
      (by rw [Category.assoc, hgE, ← Category.assoc, hac, Category.assoc])
      (by rw [Category.assoc, hgC])
  have hcompat : ∀ i j : Bool,
      pullback.fst ((diagPair B S hS f i).preimage κ).ι
          ((diagPair B S hS f j).preimage κ).ι ≫ g i =
        pullback.snd ((diagPair B S hS f i).preimage κ).ι
          ((diagPair B S hS f j).preimage κ).ι ≫ g j := by
    intro i j
    cases i <;> cases j
    · rw [fst_eq_snd_of_mono B S hS ((diagPair B S hS f false).preimage κ).ι]
    · exact mixed _ _ pullback.condition
    · exact (mixed _ _ pullback.condition.symm).symm
    · rw [fst_eq_snd_of_mono B S hS ((diagPair B S hS f true).preimage κ).ι]
  obtain ⟨d, hd, -⟩ := existsUnique_desc_of_isFppfCovering B S hS _ _ hcov hY.isSheaf g hcompat
  refine ⟨d, ?_, hd false⟩
  refine hom_ext_of_isFppfCovering B S hS _ _ hcov hV.isSheaf (fun b => ?_)
  rw [← Category.assoc, hd b]
  cases b
  · exact hbE
  · exact hbC

end AlgebraicGeometry.Space

end
