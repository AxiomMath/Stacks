module

public import StacksFrontier.Cotangent.SurjectionSiteAugmentationSections
public import StacksFrontier.RingTheory.DegreeGEBaseChange

/-!
# The normal form of an object of `C_{B/A}` for a surjective `A → B`

Let `A → B` be a **surjective** ring map and let `C_{B/A}` be the small model
`CommAlgCat.smallBoundedPolynomialSite A B κ` of the polynomial site.  An object of the small
model is an index `(S, g)` — a set `S` of variables together with a point `g : S → B` — naming
the polynomial algebra `A[S]` augmented by `X s ↦ g s`
(`CommAlgCat.boundedPolynomialModel`).

This file proves the normal form the proof of [Stacks, Tag 08RF] works in, and it is the one
place in that proof where the surjectivity of `A → B` is used:

* every object `(S, g)` is **isomorphic in the site** to the object `(S, 0)` with the same
  variables and the point `0` (`CommAlgCat.zeroPointIso`): a surjective `A → B` lifts the point
  `g : S → B` to a point `ã : S → A`, and translating the variables by `ã` is an `A`-algebra
  automorphism of `A[S]` carrying `(A[S], g)` to `(A[S], 0)`; and
* over an object whose point is `0` the sections of `𝒦ⁿ`, the `n`-th power of the augmentation
  ideal of `Ō = 𝒪 ⊗_A B̲`, are `B ⊗_A 𝔪ⁿ` with `𝔪 = (X_s; s ∈ S) ⊆ A[S]`
  (`CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm`).

Writing the sections that way is what lets [Stacks, Tag 08RE] be applied **over `A[S]`** rather
than over `B[S]`, so that the second claim in the proof of [Stacks, Tag 08RF] needs no change of
rings; see the module docstring of
`StacksFrontier.Cotangent.SurjectionSiteAugmentationPowVanishing`.

## Main definitions

* `CommAlgCat.zeroPointIndex`: the object with the same variables and the point `0`.
* `CommAlgCat.smallSiteLift`: a lift `ã : S → A` of the point of an object, along a surjective
  `A → B`.
* `CommAlgCat.zeroPointIso`: **the normal form in the site**, `(S, g) ≅ (S, 0)`.
* `CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm`: **the normal form on sections**,
  `𝒦ⁿ(U) ≅ B ⊗_A 𝔪ⁿ` over an object `U` whose point is `0`.

## Main results

* `MvPolynomial.augmentationIdeal_zero`: the augmentation ideal at the point `0` is the ideal of
  the variables.
* `CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm_symm_tmul`: the normal form in
  coordinates — it carries `b ⊗ p` to `b · p`, read inside `Ō(U) = B[S]`.  This pins the
  isomorphism down, and in particular makes it `𝒪(U)`-equivariant.
* `CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm_symm_comp_baseChange`: the normal
  form is compatible with the inclusions `𝒦ᵐ ⊆ 𝒦ⁿ` for `n ≤ m`.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08RE](https://stacks.math.columbia.edu/tag/08RE)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u

namespace MvPolynomial

/-- **The augmentation ideal at the point `0` is the ideal of the variables.** -/
theorem augmentationIdeal_zero {σ : Type*} {B : Type*} [CommRing B] :
    augmentationIdeal (0 : σ → B) = Ideal.span (Set.range (X : σ → MvPolynomial σ B)) := by
  rw [← span_range_X_sub_C_eq_augmentationIdeal]
  simp

/-- The `n`-th power of the augmentation ideal at the point `0`, read as a `B`-submodule, is
`MvPolynomial.degreeGE σ B n`. -/
theorem restrictScalars_augmentationIdeal_zero_pow (σ : Type*) (B : Type*) [CommRing B]
    (n : ℕ) :
    ((augmentationIdeal (0 : σ → B) ^ n).restrictScalars B) = degreeGE σ B n := by
  rw [augmentationIdeal_zero, restrictScalars_span_range_X_pow]

end MvPolynomial

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-! ### The normal form in the site -/

/-- The object of the small model with the same variables as `i` and the point `0`. -/
def zeroPointIndex (i : boundedPolynomialIndex A B κ) : boundedPolynomialIndex A B κ :=
  ⟨i.1, 0⟩

/-- The object `CommAlgCat.zeroPointIndex A B κ i` has the same variables as `i`. -/
@[simp]
lemma zeroPointIndex_fst (i : boundedPolynomialIndex A B κ) :
    (zeroPointIndex A B κ i).1 = i.1 := rfl

/-- The point of the object `CommAlgCat.zeroPointIndex A B κ i` is `0`. -/
@[simp]
lemma zeroPointIndex_snd (i : boundedPolynomialIndex A B κ) :
    (zeroPointIndex A B κ i).2 = 0 := rfl

/-- An index, read as an object of the small model of the site.  This is the identity, but it
records the category the object is to be read in: `CommAlgCat.boundedPolynomialIndex` is a bare
type, and `CommAlgCat.SmallBoundedPolynomialAugmentation` is the category whose objects it
indexes. -/
def smallSiteObj (i : boundedPolynomialIndex A B κ) :
    SmallBoundedPolynomialAugmentation A B κ := i

/-- **A lift of the point of an object along a surjective `A → B`**: for each variable `s` of the
object `i` an element of `A` mapping to `i.2 s`. -/
def smallSiteLift (hsurj : Function.Surjective (algebraMap A (B : Type u)))
    (i : boundedPolynomialIndex A B κ) : ↥i.1 → A :=
  fun s => (hsurj (i.2 s : (B : Type u))).choose

/-- The lift `CommAlgCat.smallSiteLift` maps to the point of the object along `A → B`. -/
@[simp]
lemma algebraMap_smallSiteLift (hsurj : Function.Surjective (algebraMap A (B : Type u)))
    (i : boundedPolynomialIndex A B κ) (s : ↥i.1) :
    algebraMap A (B : Type u) (smallSiteLift A B κ hsurj i s) = (i.2 s : (B : Type u)) :=
  (hsurj (i.2 s : (B : Type u))).choose_spec

/-- **The triangle of the normal form.** Translating the variables by a lift `ã : S → A` of the
point `g` and then augmenting by `0` is augmenting by `g`: the inverse translation sends `X s` to
`X s + C (ã s)`, which the augmentation by `0` sends to `ã s`, whose image in `B` is `g s`. -/
theorem aeval_zero_comp_translateEquiv_symm
    (hsurj : Function.Surjective (algebraMap A (B : Type u)))
    (i : boundedPolynomialIndex A B κ) :
    (MvPolynomial.aeval (R := A)
          (fun s : ↥i.1 => ((0 : ↥i.1 → (B : Type u)) s : (B : Type u)))).comp
        (MvPolynomial.translateEquiv (smallSiteLift A B κ hsurj i)).symm.toAlgHom =
      MvPolynomial.aeval (R := A) (fun s : ↥i.1 => (i.2 s : (B : Type u))) := by
  refine MvPolynomial.algHom_ext fun s => ?_
  simp

/-- **The normal form in the site.** For a surjective `A → B` every object `(S, g)` of the small
model of `C_{B/A}` is isomorphic to the object `(S, 0)` with the same variables and the point
`0`.

The isomorphism is translation of the variables by a lift `ã : S → A` of `g`
(`CommAlgCat.smallSiteLift`), which is an `A`-algebra automorphism of `A[S]`
(`MvPolynomial.translateEquiv`); its inverse sends `X s` to `X s + C (ã s)`, so composing it with
the augmentation of `(S, 0)` gives `X s ↦ ã s ↦ g s`, which is the augmentation of `(S, g)`.

Surjectivity enters here and nowhere else in the proof of the second claim of
[Stacks, Tag 08RF]. -/
def zeroPointIso (hsurj : Function.Surjective (algebraMap A (B : Type u)))
    (i : boundedPolynomialIndex A B κ) :
    smallSiteObj A B κ i ≅ smallSiteObj A B κ (zeroPointIndex A B κ i) := by
  refine InducedCategory.isoMk (ObjectProperty.isoMk _ (Over.isoMk (CommAlgCat.isoMk
    (MvPolynomial.translateEquiv (smallSiteLift A B κ hsurj i)).symm) ?_))
  exact CommAlgCat.hom_ext (aeval_zero_comp_translateEquiv_symm A B κ hsurj i)

/-! ### The normal form on sections -/

/-- The point naming an object of the small model is the second component of its index. -/
lemma smallSitePoint_eq_snd (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    smallSitePoint A B κ X = fun s => (X.unop.unop.2 s : (B : Type u)) := rfl

/-- An object of the small model whose index has second component `0` has point `0`.  This is how
a consumer discharges the hypothesis of
`CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm` after moving to the normal form
`CommAlgCat.zeroPointIso`. -/
lemma smallSitePoint_eq_zero (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (h : X.unop.unop.2 = 0) : smallSitePoint A B κ X = 0 := by
  rw [smallSitePoint_eq_snd, h]

/-- **The normal form, as an isomorphism in the category presheaves are taken on.** Presheaves on
`C_{B/A}` are functors on `(smallBoundedPolynomialSite A B κ)ᵒᵖ`, the double opposite of the
small model; `CommAlgCat.zeroPointIso` read there says that every object is isomorphic to one
whose point is `0`.

This is the form in which the normal form is used: an objectwise statement about a morphism of
presheaves — that it vanishes, say — holds at an object as soon as it holds at an object
isomorphic to it (`Stacks.SheafOfModules.app_eq_zero_of_iso`), so for a surjective `A → B` such
a statement need only be checked at the objects whose point is `0`. -/
def zeroPointSiteIso (hsurj : Function.Surjective (algebraMap A (B : Type u)))
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    X ≅ Opposite.op (Opposite.op (zeroPointIndex A B κ X.unop.unop)) :=
  ((zeroPointIso A B κ hsurj X.unop.unop).op).op

/-- The target of `CommAlgCat.zeroPointSiteIso` has point `0`, so it satisfies the hypothesis of
`CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm`. -/
lemma smallSitePoint_op_op_zeroPointIndex (i : boundedPolynomialIndex A B κ) :
    smallSitePoint A B κ (Opposite.op (Opposite.op (zeroPointIndex A B κ i))) = 0 :=
  smallSitePoint_eq_zero A B κ _ rfl

/-- **The normal form on sections.** Over an object `U` of the small model whose point is `0` the
sections of `𝒦ⁿ`, the `n`-th power of the augmentation ideal of `Ō = 𝒪 ⊗_A B̲`, are the base
change `B ⊗_A 𝔪ⁿ` of the `n`-th power of the ideal of the variables of `A[S]`.

The chain is: the sections of `𝒦ⁿ` are the `n`-th power of the augmentation ideal of `B[S]` at
the point naming `U` (`CommAlgCat.smallPolynomialAugmentationIdealPowLinearEquiv`), which at the
point `0` is `𝔪ⁿ_B = MvPolynomial.degreeGE S B n`
(`MvPolynomial.restrictScalars_augmentationIdeal_zero_pow`), which is the base change of `𝔪ⁿ`
(`MvPolynomial.degreeGEBaseChangeEquiv`). -/
def smallPolynomialAugmentationIdealPowNormalForm (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (h0 : smallSitePoint A B κ X = 0) :
    ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ n X) ≃ₗ[(B : Type u)]
      (B : Type u) ⊗[A] (MvPolynomial.degreeGE ↥(X.unop.unop.1) A n) :=
  (smallPolynomialAugmentationIdealPowLinearEquiv A B κ n X).trans
    ((LinearEquiv.ofEq _ _ (by
        rw [h0, MvPolynomial.restrictScalars_augmentationIdeal_zero_pow])).trans
      (MvPolynomial.degreeGEBaseChangeEquiv A (B : Type u) ↥(X.unop.unop.1) n).symm)

/-- The identification `CommAlgCat.smallPolynomialAugmentationIdealPowLinearEquiv` of the
sections of `𝒦ⁿ` is the identification `Ō(U) = B[S]` on underlying elements. -/
lemma coe_smallPolynomialAugmentationIdealPowLinearEquiv' (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (x : ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ n X)) :
    ((smallPolynomialAugmentationIdealPowLinearEquiv A B κ n X x :
        ↥(Submodule.restrictScalars (B : Type u)
          (MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) ^ n))) :
        MvPolynomial ↥(X.unop.unop.1) (B : Type u)) =
      smallPolynomialQuotientAlgEquiv A B κ X
        (x : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) := rfl

/-- **The normal form in coordinates.** Read inside `Ō(U) = B[S]`, the inverse of the normal form
carries `b ⊗ p` to `b · p`, the coefficients of `p` pushed along `A → B`.

This pins the isomorphism down.  In particular it is `𝒪(U)`-equivariant: `𝒪(U) = A[S]` acts on
`𝒦ⁿ(U)` through `A[S] → B[S]`, and on `B ⊗_A 𝔪ⁿ` through the right factor, and the formula
`b ⊗ (q · p) ↦ b · (q · p)` is multiplicativity of `MvPolynomial.map`. -/
@[simp]
theorem smallPolynomialAugmentationIdealPowNormalForm_symm_tmul (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) (h0 : smallSitePoint A B κ X = 0)
    (b : (B : Type u)) (p : MvPolynomial.degreeGE ↥(X.unop.unop.1) A n) :
    smallPolynomialQuotientAlgEquiv A B κ X
        (((smallPolynomialAugmentationIdealPowNormalForm A B κ n X h0).symm (b ⊗ₜ p) :
          ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ n X)) :
          ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) =
      b • MvPolynomial.map (algebraMap A (B : Type u)) (p : MvPolynomial ↥(X.unop.unop.1) A) := by
  rw [← coe_smallPolynomialAugmentationIdealPowLinearEquiv' A B κ n X,
    smallPolynomialAugmentationIdealPowNormalForm, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- **The normal form is compatible with the filtration**: for `n ≤ m` the square relating the
normal forms at `m` and at `n` with the inclusions `𝒦ᵐ ⊆ 𝒦ⁿ` and `𝔪ᵐ ⊆ 𝔪ⁿ` commutes.

Both composites carry `b ⊗ p` to `b · p`, by
`CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm_symm_tmul`, the inclusions being the
identity on underlying polynomials. -/
theorem smallPolynomialAugmentationIdealPowNormalForm_symm_comp_baseChange {n m : ℕ} (h : n ≤ m)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) (h0 : smallSitePoint A B κ X = 0) :
    (smallPolynomialAugmentationIdealPowNormalForm A B κ n X h0).symm.toLinearMap.comp
        (LinearMap.baseChange (B : Type u)
          (Submodule.inclusion (MvPolynomial.degreeGE_antitone A ↥(X.unop.unop.1) h))) =
      (Submodule.inclusion
          (smallPolynomialAugmentationIdealPowSubmodule_antitone A B κ h X)).comp
        (smallPolynomialAugmentationIdealPowNormalForm A B κ m X h0).symm.toLinearMap := by
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.inductionOn with
  | tmul b p =>
    refine Subtype.ext ((smallPolynomialQuotientAlgEquiv A B κ X).injective ?_)
    change smallPolynomialQuotientAlgEquiv A B κ X
        (((smallPolynomialAugmentationIdealPowNormalForm A B κ n X h0).symm
            (b ⊗ₜ Submodule.inclusion (MvPolynomial.degreeGE_antitone A _ h) p) :
          ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ n X)) :
          ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) =
      smallPolynomialQuotientAlgEquiv A B κ X
        (((smallPolynomialAugmentationIdealPowNormalForm A B κ m X h0).symm (b ⊗ₜ p) :
          ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ m X)) :
          ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u))
    rw [smallPolynomialAugmentationIdealPowNormalForm_symm_tmul,
      smallPolynomialAugmentationIdealPowNormalForm_symm_tmul]
    rfl
  | add y z hy hz => rw [map_add, map_add, hy, hz]

end CommAlgCat

end
