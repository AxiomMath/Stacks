module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.RegularPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Sum
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Summands

/-!
# Blowing up a product of ideals

Blowing up a scheme `X` in a quasi-coherent ideal `I`, and then blowing up the result in the
inverse image of a second ideal `J`, gives the blowup of `X` in the product `I * J`, canonically
over `X`.

## Main definitions

* `AlgebraicGeometry.sequentialBlowUpOver`: the two-step blowup, as an object of `Sch/X`.
* `AlgebraicGeometry.blowUpMulIso`: the canonical isomorphism over `X` between the two-step
  blowup and the blowup in the product.

## Main results

* `AlgebraicGeometry.isCartierOver_sequentialBlowUpOver`: on the two-step blowup the inverse
  image of `I * J` is an effective Cartier divisor.
* `AlgebraicGeometry.isTerminal_sequentialBlowUpOver`: the two-step blowup has the universal
  property of the blowup in `I * J`.
* `AlgebraicGeometry.blowUpMulIso_unique`: the canonical isomorphism is the only isomorphism of
  these two blowups over `X`.

## Implementation notes

Both sides are characterized by the same universal property (Stacks tag 0806,
`Stacks.Blowup.isTerminal_blowUp`), so the comparison is an instance of uniqueness of a
terminal object; that is also why it is automatically compatible with the structure morphisms
to `X` and why it is unique. That the two-step blowup belongs to the relevant category is the
only computation: the inverse image of `I * J` on it is the product of the exceptional divisor
of the second blowup with the inverse image of the exceptional divisor of the first, and the
latter is an effective Cartier divisor by Stacks tag 0809
(`AlgebraicGeometry.isPullbackDefined_blowUpToBase`).

## References

* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I J : X.IdealSheafData)

/-- The two-step blowup of `X`: first in `I`, then in the inverse image of `J`, viewed as an
object of the category of `X`-schemes. -/
abbrev sequentialBlowUpOver : Over X :=
  Over.mk (blowUpToBase (J.comap (blowUpToBase I)) ≫ blowUpToBase I)

/-- On the two-step blowup the inverse image of `I * J` is an effective Cartier divisor: it is
the product of the exceptional divisor of the second blowup with the inverse image of the
exceptional divisor of the first. -/
theorem isCartierOver_sequentialBlowUpOver :
    Stacks.Blowup.IsCartierOver (I * J) (sequentialBlowUpOver I J) := by
  change Stacks.Divisors.IsEffectiveCartierDivisor
    ((I * J).comap (blowUpToBase (J.comap (blowUpToBase I)) ≫ blowUpToBase I))
  rw [comap_mul, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
  refine isEffectiveCartierDivisor_mul _ _ ?_ ?_
  · exact isPullbackDefined_blowUpToBase (J.comap (blowUpToBase I)) (I.comap (blowUpToBase I))
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I)
  · exact Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (J.comap (blowUpToBase I))

/-- **The universal property of the two-step blowup.** The two-step blowup of `X` in `I` and
then the inverse image of `J` is terminal among `X`-schemes on which the inverse image of
`I * J` is an effective Cartier divisor; that is, it is a blowup of `X` in `I * J`. -/
theorem isTerminal_sequentialBlowUpOver :
    Nonempty (IsTerminal (⟨sequentialBlowUpOver I J, isCartierOver_sequentialBlowUpOver I J⟩ :
      Stacks.Blowup.CartierOver (I * J))) := by
  classical
  obtain ⟨hI, ⟨terminalI⟩⟩ := Stacks.Blowup.isTerminal_blowUp I
  obtain ⟨hK, ⟨terminalK⟩⟩ := Stacks.Blowup.isTerminal_blowUp (J.comap (blowUpToBase I))
  have hsplit : ∀ Z : Stacks.Blowup.CartierOver (I * J),
      Stacks.Divisors.IsEffectiveCartierDivisor (I.comap Z.obj.hom) ∧
        Stacks.Divisors.IsEffectiveCartierDivisor (J.comap Z.obj.hom) := by
    intro Z
    have hprod : Stacks.Divisors.IsEffectiveCartierDivisor
        (I.comap Z.obj.hom * J.comap Z.obj.hom) := by
      have h : Stacks.Divisors.IsEffectiveCartierDivisor ((I * J).comap Z.obj.hom) := Z.2
      rwa [comap_mul] at h
    exact ⟨isEffectiveCartierDivisor_left_of_mul _ _ hprod,
      isEffectiveCartierDivisor_right_of_mul _ _ hprod⟩
  have hsecond : ∀ (Z : Stacks.Blowup.CartierOver (I * J))
      (f₁ : (⟨Z.obj, (hsplit Z).1⟩ : Stacks.Blowup.CartierOver I) ⟶
        ⟨Over.mk (blowUpToBase I), hI⟩),
      Stacks.Divisors.IsEffectiveCartierDivisor
        ((J.comap (blowUpToBase I)).comap f₁.hom.left) := by
    intro Z f₁
    have hw : f₁.hom.left ≫ blowUpToBase I = Z.obj.hom := Over.w f₁.hom
    rw [← Scheme.IdealSheafData.comap_comp, hw]
    exact (hsplit Z).2
  refine ⟨IsTerminal.ofUniqueHom (fun Z ↦ ?_) ?_⟩
  · set g := terminalI.from ⟨Z.obj, (hsplit Z).1⟩ with hg
    set k := terminalK.from ⟨Over.mk g.hom.left, hsecond Z g⟩ with hk
    refine ObjectProperty.homMk (Over.homMk k.hom.left ?_)
    have hkw : k.hom.left ≫ blowUpToBase (J.comap (blowUpToBase I)) = g.hom.left := Over.w k.hom
    change k.hom.left ≫ blowUpToBase (J.comap (blowUpToBase I)) ≫ blowUpToBase I = Z.obj.hom
    rw [← Category.assoc, hkw]
    exact Over.w g.hom
  · intro Z f
    apply ObjectProperty.hom_ext
    apply CommaMorphism.ext
    · have hfI : (ObjectProperty.homMk (Over.homMk (U := Z.obj) (V := Over.mk (blowUpToBase I))
          (f.hom.left ≫ blowUpToBase (J.comap (blowUpToBase I))) (by
            change f.hom.left ≫ blowUpToBase (J.comap (blowUpToBase I)) ≫ blowUpToBase I =
              Z.obj.hom
            rw [← Category.assoc]
            exact Over.w f.hom)) :
              (⟨Z.obj, (hsplit Z).1⟩ : Stacks.Blowup.CartierOver I) ⟶
                ⟨Over.mk (blowUpToBase I), hI⟩) =
            terminalI.from ⟨Z.obj, (hsplit Z).1⟩ := terminalI.hom_ext _ _
      have hfl : f.hom.left ≫ blowUpToBase (J.comap (blowUpToBase I)) =
          (terminalI.from ⟨Z.obj, (hsplit Z).1⟩).hom.left :=
        congrArg (fun q ↦ q.hom.left) hfI
      have hf₂ : (ObjectProperty.homMk (Over.homMk f.hom.left hfl) :
          (⟨Over.mk (terminalI.from ⟨Z.obj, (hsplit Z).1⟩).hom.left,
            hsecond Z (terminalI.from ⟨Z.obj, (hsplit Z).1⟩)⟩ :
              Stacks.Blowup.CartierOver (J.comap (blowUpToBase I))) ⟶
            ⟨Over.mk (blowUpToBase (J.comap (blowUpToBase I))), hK⟩) =
          terminalK.from _ := terminalK.hom_ext _ _
      exact congrArg (fun q ↦ q.hom.left) hf₂
    · subsingleton

/-- **Stacks Project, Tag 080A.** Blowing up `X` in `I` and then in the inverse image of `J` is
canonically, over `X`, the blowup of `X` in `I * J`. -/
@[stacks 080A "canonical isomorphism"]
def blowUpMulIso :
    Over.mk (blowUpToBase (J.comap (blowUpToBase I)) ≫ blowUpToBase I) ≅
      Over.mk (blowUpToBase (I * J)) :=
  (ObjectProperty.ι (Stacks.Blowup.IsCartierOver (I * J))).mapIso
    ((Classical.choice (isTerminal_sequentialBlowUpOver I J)).uniqueUpToIso
      (Classical.choice (Classical.choose_spec (Stacks.Blowup.isTerminal_blowUp (I * J)))))

/-- The isomorphism of Stacks tag 080A is the unique isomorphism of these two blowups over
`X`: both are terminal in the same category. -/
@[stacks 080A "uniqueness"]
theorem blowUpMulIso_unique
    (e : Over.mk (blowUpToBase (J.comap (blowUpToBase I)) ≫ blowUpToBase I) ≅
      Over.mk (blowUpToBase (I * J))) : e = blowUpMulIso I J := by
  classical
  have t₂ : IsTerminal (⟨Over.mk (blowUpToBase (I * J)),
      Classical.choose (Stacks.Blowup.isTerminal_blowUp (I * J))⟩ :
        Stacks.Blowup.CartierOver (I * J)) :=
    Classical.choice (Classical.choose_spec (Stacks.Blowup.isTerminal_blowUp (I * J)))
  have key : (ObjectProperty.homMk e.hom :
      (⟨sequentialBlowUpOver I J, isCartierOver_sequentialBlowUpOver I J⟩ :
        Stacks.Blowup.CartierOver (I * J)) ⟶
      ⟨Over.mk (blowUpToBase (I * J)),
        Classical.choose (Stacks.Blowup.isTerminal_blowUp (I * J))⟩) =
      ObjectProperty.homMk (blowUpMulIso I J).hom := t₂.hom_ext _ _
  exact Iso.ext (congrArg (fun q ↦ q.hom) key)

end AlgebraicGeometry

end
