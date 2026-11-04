module

public import StacksFrontier.Deformation.Artin.Versality.GRingNecessity.Algebraic
public import StacksFrontier.Deformation.Artin.Versality.GRingNecessity.Datum
public import StacksFrontier.Deformation.Artin.Versality.GRingNecessity.LimitPreserving
public import StacksFrontier.Deformation.Artin.Versality.GRingNecessity.Versal

/-!
# The categories of Stacks Example 98.12.8 satisfy the hypotheses of Lemma 98.12.7

Let `Λ` be a Noetherian ring, `𝔪` a maximal ideal, `C` a finite type `Λ`-algebra and
`φ : C → Λ_𝔪^∧` a `Λ`-algebra map. Stacks Example 98.12.8 (Tag 07XI) asserts that the category
`𝒳 = 𝒮_F` fibred in sets attached to `S' = (Spec Λ ∖ {𝔪}) ⨿ Spec C` is limit preserving on objects
and has an effective, versal formal object `ξ` over `Λ_𝔪^∧`: these are the hypotheses of Lemma
98.12.7 (Tag 07XH) other than the G-ring hypothesis. This file records these assertions, the
datum the Example reads off the conclusion of 07XH, and the passage from 07XH in lemma form
(for all formal objects satisfying its hypotheses) to its conclusion for `ξ`.

## Main definitions

* `Deformation.Artin.GRingNecessity.AlgebraizationLemmaHolds 𝔪 C B hS`: the statement of Lemma
  98.12.7 with its G-ring hypothesis removed, for the category `𝒳 = 𝒮_F` of `C`.

## Main results

* `…GRingNecessity.isLimitPreservingOnObjects_and_formalObject_isEffective_isVersal`: `𝒳` is
  limit preserving on objects and `ξ` is an effective versal formal object over `Λ_𝔪^∧`.
* `Deformation.Artin.GRingNecessity.algebraizesFiniteTypeFactorizations_of_forall`: the conclusion
  of 07XH for every `(𝒳, ξ)` gives the datum `AlgebraizesFiniteTypeFactorizations`.
* `Deformation.Artin.GRingNecessity.algebraizationConclusion_of_algebraizationLemmaHolds`: Lemma
  98.12.7 in lemma form gives its conclusion for `ξ`.

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 07XH](https://stacks.math.columbia.edu/tag/07XH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Deformation.Artin.GRingNecessity

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal]
  (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))

/-- **Stacks Example 98.12.8 (Tag 07XI), the properties of `𝒳` and `ξ`.** Let `C` be a finite
type `Λ`-algebra and `φ : C → Λ_𝔪^∧` a `Λ`-algebra map. The category `𝒳 = 𝒮_F` fibred in sets
over the big fppf site of `S = Spec Λ` is limit preserving on objects, and `ξ` is a formal object
of `𝒳` over `R = Λ_𝔪^∧` (its base is isomorphic to `R` over `S`) which is effective and versal.
Versality holds over the local ring `𝒪_{S,s}` of `S` at any point `s`, for every algebra
structure of the base of `ξ` over `𝒪_{S,s}` compatible with the structure morphisms, and such a
structure exists at the image `formalObjectPoint` of the closed point of the base, where the
versality hypothesis of Lemma 98.12.7 is formulated. -/
@[stacks 07XI "first assertion of the Example: `𝒳 = 𝒮_F` is limit preserving on objects and \
has an effective, versal formal object `ξ` over `R = Λ_𝔪^∧`"]
theorem isLimitPreservingOnObjects_and_formalObject_isEffective_isVersal
    (C : Type u) [CommRing C] [Algebra Λ C] [Algebra.FiniteType Λ C]
    (φ : C →ₐ[Λ] Completion 𝔪) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B (Spec (.of Λ)) hS
        (factorizationCategory 𝔪 C B hS)
        (Approximation.baseFiberedCategory B (Spec (.of Λ)) hS)
        (Approximation.structureMorphism B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS)) ∧
      IsCompletionBase 𝔪 (formalObject 𝔪 C φ B hS).base ∧
      FormalObject.IsEffective B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p
        (factorizationCategory 𝔪 C B hS).property (formalObject 𝔪 C φ B hS) ∧
      (∃ _ : Algebra ((Spec (.of Λ)).presheaf.stalk (formalObjectPoint 𝔪 C B hS φ) : Type u)
          (formalObject 𝔪 C φ B hS).base.R,
        Spec.map (CommRingCat.ofHom (algebraMap
            ((Spec (.of Λ)).presheaf.stalk (formalObjectPoint 𝔪 C B hS φ) : Type u)
            (formalObject 𝔪 C φ B hS).base.R)) ≫
          (Spec (.of Λ)).fromSpecStalk (formalObjectPoint 𝔪 C B hS φ) =
        (formalObject 𝔪 C φ B hS).base.toS) ∧
      ∀ (s : Spec (.of Λ))
        [Algebra ((Spec (.of Λ)).presheaf.stalk s : Type u) (formalObject 𝔪 C φ B hS).base.R]
        (iΛ : Spec (.of ((Spec (.of Λ)).presheaf.stalk s : Type u)) ⟶ Spec (.of Λ))
        (_ : iΛ = (Spec (.of Λ)).fromSpecStalk s)
        (hΛ : Spec.map (CommRingCat.ofHom (algebraMap
            ((Spec (.of Λ)).presheaf.stalk s : Type u) (formalObject 𝔪 C φ B hS).base.R)) ≫ iΛ =
          (formalObject 𝔪 C φ B hS).base.toS),
        FormalObject.IsVersal B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p
          (factorizationCategory 𝔪 C B hS).property (formalObject 𝔪 C φ B hS)
          ((Spec (.of Λ)).presheaf.stalk s : Type u) iΛ hΛ :=
  ⟨factorizationCategory_isLimitPreservingOnObjects 𝔪 C B hS,
    isCompletionBase_formalObject 𝔪 C φ B hS, formalObject_isEffective 𝔪 C φ B hS,
    ⟨formalObjectStalkAlgebra 𝔪 C B hS φ, formalObjectStalkAlgebra_spec 𝔪 C B hS φ⟩,
    fun s _ iΛ hiΛ hΛ => formalObject_isVersal 𝔪 C B hS φ s iΛ hiΛ hΛ⟩

/-- **Stacks Example 98.12.8 (Tag 07XI), the datum read off the conclusion of 07XH.** If the
conclusion of Lemma 98.12.7 holds for the categories `𝒳 = 𝒮_F` and formal objects `ξ` of the
Example, then for every finite type factorization `Λ → C → Λ_𝔪^∧` there are a finite type
`Λ`-algebra `A`, a maximal ideal `𝔪_A` over `𝔪` with `κ(𝔪) = κ(𝔪_A)`, smoothness of `Λ → A` at
`𝔪_A` (by condition (4) of Tag 02HT) and a `Λ`-algebra map `C → A`. -/
theorem algebraizesFiniteTypeFactorizations_of_forall
    (h : ∀ (C : Type u) [CommRing C] [Algebra Λ C], Algebra.FiniteType Λ C →
      ∀ φ : C →ₐ[Λ] Completion 𝔪,
        AlgebraizationConclusion B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS)
          (formalObject 𝔪 C φ B hS)) :
    AlgebraizesFiniteTypeFactorizations Λ 𝔪 (Completion 𝔪) :=
  fun C _ _ hC φ => exists_smooth_of_algebraizationConclusion 𝔪 C φ B hS (h C hC φ)

/-- **Lemma 98.12.7 (Tag 07XH) without its G-ring hypothesis, for the category `𝒳 = 𝒮_F` of `C`**
(Stacks Example 98.12.8): every formal object `ξ` of `𝒳` which is effective and versal over the
local ring `𝒪_{S,s}` at the image `s` of the closed point of its base (for a compatible algebra
structure), `𝒳` being limit preserving on objects, satisfies the conclusion of 07XH. The
remaining hypothesis of 07XH, that `S = Spec Λ` is locally Noetherian, holds since `Λ` is
Noetherian. -/
def AlgebraizationLemmaHolds (C : Type u) [CommRing C] [Algebra Λ C] : Prop :=
  ∀ (ξ : FormalObject B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p),
    FormalObject.IsEffective B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p
      (factorizationCategory 𝔪 C B hS).property ξ →
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B (Spec (.of Λ)) hS
      (factorizationCategory 𝔪 C B hS)
      (Approximation.baseFiberedCategory B (Spec (.of Λ)) hS)
      (Approximation.structureMorphism B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS)) →
    ∀ (s : Spec (.of Λ)), ξ.base.toS (closedPoint ξ.base.R) = s →
    ∀ (_ : Algebra ((Spec (.of Λ)).presheaf.stalk s : Type u) ξ.base.R)
      (iΛ : Spec (.of ((Spec (.of Λ)).presheaf.stalk s : Type u)) ⟶ Spec (.of Λ))
      (_ : iΛ = (Spec (.of Λ)).fromSpecStalk s)
      (hΛ : Spec.map (CommRingCat.ofHom
        (algebraMap ((Spec (.of Λ)).presheaf.stalk s : Type u) ξ.base.R)) ≫ iΛ = ξ.base.toS),
    FormalObject.IsVersal B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p
      (factorizationCategory 𝔪 C B hS).property ξ ((Spec (.of Λ)).presheaf.stalk s : Type u)
      iΛ hΛ →
    AlgebraizationConclusion B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS) ξ

/-- Lemma 98.12.7 (Tag 07XH) without its G-ring hypothesis, applied to the category `𝒳 = 𝒮_F` of
Stacks Example 98.12.8, gives its conclusion for the formal object `ξ` over `Λ_𝔪^∧`, which
satisfies the hypotheses of the lemma. -/
theorem algebraizationConclusion_of_algebraizationLemmaHolds (C : Type u) [CommRing C]
    [Algebra Λ C] [Algebra.FiniteType Λ C] (h : AlgebraizationLemmaHolds 𝔪 B hS C)
    (φ : C →ₐ[Λ] Completion 𝔪) :
    AlgebraizationConclusion B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS)
      (formalObject 𝔪 C φ B hS) := by
  obtain ⟨hlim, -, heff, -, hvers⟩ :=
    isLimitPreservingOnObjects_and_formalObject_isEffective_isVersal 𝔪 B hS C φ
  let := formalObjectStalkAlgebra 𝔪 C B hS φ
  exact h (formalObject 𝔪 C φ B hS) heff hlim _ rfl _ _ rfl
    (formalObjectStalkAlgebra_spec 𝔪 C B hS φ)
    (hvers _ _ rfl (formalObjectStalkAlgebra_spec 𝔪 C B hS φ))

end Deformation.Artin.GRingNecessity

end
