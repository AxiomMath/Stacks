module

public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedRingAction
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.PullbackSpecGradedAlgebra

/-!
# The homogeneous sections of `f^* B̃`

[Stacks, Tag 0897]'s graded `B`-module structure on `⨁ₙ Hᵖ(X, Fₙ)` is built from the datum
`Stacks.AlgebraicGeometry.GradedProperCohomology.HomogeneousSections`: a homogeneous element of
degree `k` of `B` names a global section of the degree-`k` piece of the sheaf of graded algebras,
additively in the element, carrying the unit of `B` to the unit of the algebra and a product to
the product. **This file supplies that datum for `𝓑 = f^* B̃`**: the section named by `b ∈ 𝒜ₖ` is
the pullback along `f` of the section of `B̃ₖ` named by `b`.

The three laws are the pullback of the corresponding laws on `Spec A`, which are
`Stacks.SpecGraded.homogeneousSection_eval_add`, `homogeneousSection_gOne` and
`castHom_homogeneousSection_mul`. Pulling them back is a matter of reducing to the open `⊤`,
where `Stacks.Conormal.gradedPullback_one_eval` and `gradedPullback_mul_pullbackSection` compute
the unit and the multiplication of `f^* B̃` on pullback sections; the reduction uses that both
sides are global sections, so each is the restriction of its value over `⊤`.

## Main definitions

* `Stacks.AlgebraicGeometry.GradedProperCohomology.pullbackHomogeneousSections`: **the datum.**

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The section of `(f^* B̃)ₖ` named by a homogeneous element of degree `k` of `B`: the pullback
along `f` of the section of `B̃ₖ` it names. -/
abbrev pullbackSpecSection {k : ℕ} (b : ↥(𝒜 k)) :
    ((pullbackGradedAlg 𝒜 f).piece (k : ℤ)).val.sections :=
  pullbackSections f ((specGradedAlg 𝒜).piece (k : ℤ)) (specSection 𝒜 b)

/-- **The homogeneous-sections datum of [Stacks, Tag 0897] for `𝓑 = f^* B̃`.** -/
def pullbackHomogeneousSections : HomogeneousSections (pullbackGradedAlg 𝒜 f) 𝒜 where
  sec b := pullbackSpecSection 𝒜 f b
  eval_add := by
    intro k b b' U
    refine Eq.trans (congrArg (Scheme.Modules.pullbackSection f
        ((specGradedAlg 𝒜).piece (k : ℤ)) ⊤ U.unop le_top)
      (Stacks.SpecGraded.homogeneousSection_eval_add (R := CommRingCat.of A) (S := B)
        (𝒢 := intExtend 𝒜) (k := (k : ℤ)) b b' (op ⊤))) ?_
    exact pullbackSection_add f ((specGradedAlg 𝒜).piece (k : ℤ)) ⊤ le_top _ _
  eval_one := by
    intro U
    refine Eq.trans ?_ (PresheafOfModules.sections_property (pullbackGradedAlg 𝒜 f).one
      (homOfLE (le_top : U.unop ≤ ⊤)).op)
    refine Eq.trans ?_ (congrArg
      (fun z => (((pullbackGradedAlg 𝒜 f).piece 0).val.map
        (homOfLE (le_top : U.unop ≤ ⊤)).op) z)
      (Stacks.Conormal.gradedPullback_one_eval f (specGradedAlg 𝒜) ⊤).symm)
    refine Eq.trans ?_ (pullbackSection_restrict f ((specGradedAlg 𝒜).piece 0) ⊤
      (le_refl (⊤ : X.Opens)) (le_top : U.unop ≤ ⊤) _).symm
    exact congrArg (Scheme.Modules.pullbackSection f ((specGradedAlg 𝒜).piece 0) ⊤ U.unop le_top)
      (congrArg (fun s : ((specGradedAlg 𝒜).piece 0).val.sections => s.eval (op ⊤))
        (Stacks.SpecGraded.homogeneousSection_gOne (R := CommRingCat.of A) (S := B)
          (𝒢 := intExtend 𝒜)))
  castHom_mul := by
    intro k l b b' U
    have hdeg : (l : ℤ) + (k : ℤ) = ((k + l : ℕ) : ℤ) := by push_cast; ring
    have hU : (op (⊤ : X.Opens) : (Opens ↥X)ᵒᵖ) ⟶ U := (homOfLE (le_top : U.unop ≤ ⊤)).op
    -- the two sections are the restrictions of their values over `⊤`
    have hb : (pullbackSpecSection 𝒜 f b).eval U =
        (((pullbackGradedAlg 𝒜 f).piece (k : ℤ)).val.map hU)
          ((pullbackSpecSection 𝒜 f b).eval (op ⊤)) :=
      (PresheafOfModules.sections_property (pullbackSpecSection 𝒜 f b) hU).symm
    have hb' : (pullbackSpecSection 𝒜 f b').eval U =
        (((pullbackGradedAlg 𝒜 f).piece (l : ℤ)).val.map hU)
          ((pullbackSpecSection 𝒜 f b').eval (op ⊤)) :=
      (PresheafOfModules.sections_property (pullbackSpecSection 𝒜 f b') hU).symm
    -- the identity over `⊤`
    have htop : _root_.SheafOfModules.castHom (pullbackGradedAlg 𝒜 f).piece hdeg (op ⊤)
          (((pullbackGradedAlg 𝒜 f).mul (l : ℤ) (k : ℤ)).app (op ⊤)
            ((pullbackSpecSection 𝒜 f b').eval (op ⊤))
            ((pullbackSpecSection 𝒜 f b).eval (op ⊤))) =
        (pullbackSpecSection 𝒜 f
          (GradedMonoid.GMul.mul (A := fun n : ℕ => ↥(𝒜 n)) b b')).eval (op ⊤) := by
      refine Eq.trans (congrArg
        (_root_.SheafOfModules.castHom (pullbackGradedAlg 𝒜 f).piece hdeg (op ⊤))
        (Stacks.Conormal.gradedPullback_mul_pullbackSection f (specGradedAlg 𝒜) (l : ℤ) (k : ℤ)
          ⊤ ((specSection 𝒜 b').eval (op ⊤)) ((specSection 𝒜 b).eval (op ⊤)))) ?_
      refine Eq.trans (castHom_pullbackSection f (specGradedAlg 𝒜).piece hdeg ⊤
        (le_refl (⊤ : X.Opens)) _) ?_
      exact congrArg
        (Scheme.Modules.pullbackSection f ((specGradedAlg 𝒜).piece ((k + l : ℕ) : ℤ)) ⊤ ⊤
          (le_refl (⊤ : X.Opens)))
        (Stacks.SpecGraded.castHom_homogeneousSection_mul (R := CommRingCat.of A) (S := B)
          (𝒢 := intExtend 𝒜) (i := (l : ℤ)) (j := (k : ℤ)) (m := ((k + l : ℕ) : ℤ)) hdeg b' b
          (GradedMonoid.GMul.mul (A := fun n : ℕ => ↥(𝒜 n)) b b')
          (mul_comm (b : B) (b' : B)) (op ⊤))
    rw [hb, hb', ← ((pullbackGradedAlg 𝒜 f).mul (l : ℤ) (k : ℤ)).naturality hU _ _,
      ← castHom_naturality (pullbackGradedAlg 𝒜 f).piece hdeg hU _, htop]
    exact PresheafOfModules.sections_property
      (pullbackSpecSection 𝒜 f (GradedMonoid.GMul.mul (A := fun n : ℕ => ↥(𝒜 n)) b b')) hU

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
