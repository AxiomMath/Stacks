module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueingDescentBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectBaseChangeEdsSystems

/-!
# The cocycle identities of the base changes of an elementary distinguished square

Let `(U₀ ⊆ W₀, f₀ : V₀ ⟶ W₀)` be an elementary distinguished square and let `p : W ⟶ W₀` be a
morphism of algebraic spaces.  By Stacks 08GN, part (2), the square pulls back to an elementary
distinguished square of `W` (`AlgebraicGeometry.Space.edsPreimage`), and a morphism `q : W' ⟶ W`
over `W₀` induces maps of the three members of the two base changes
(`AlgebraicGeometry.Space.edsPreimageOpenMap`, `…edsPreimageEtaleMap`,
`…edsPreimageInterMap`).

This file proves that **those three constructions are functorial in `q`**: for `q : W' ⟶ W` and
`q' : W'' ⟶ W'` over `W₀`, the map induced by `q' ≫ q` is the map induced by `q'` followed by
the map induced by `q`, and the map induced by an identity is an identity.  Nothing else is
here, and nothing is assumed.

## Why this is needed

The essential surjectivity half of Stacks 09RJ is proved in the source by the induction
principle of Stacks 08GP over the quasi-compact quasi-separated objects of
`(X₀)_{spaces, étale}`, and the step at an elementary distinguished square works with the
*systems* of the three members of the base changes of one square along the stages of
Situation 09RH.  A system of algebraic spaces over a base — the shape at which the colimit
statement of Stacks 09RI is available in this library,
`CategoryTheory.PullbackData.LimitSystem` — asks precisely for transition morphisms that compose
and projections compatible with them, which for the three members of the base changes of one
square is exactly the functoriality below.  So these identities are what turns Situation 09RH,
base changed along an algebraic space étale over `X₀`, into the three systems the step of the
induction needs.

## Main results

* `AlgebraicGeometry.Space.edsPreimageOpenMap_comp_edsPreimageOpenMap`,
  `…edsPreimageEtaleMap_comp_edsPreimageEtaleMap`,
  `…edsPreimageInterMap_comp_edsPreimageInterMap`: the cocycle identities.
* `AlgebraicGeometry.Space.edsPreimageOpenMap_id`, `…edsPreimageEtaleMap_id`,
  `…edsPreimageInterMap_id`: the map induced by an identity is an identity.
* `AlgebraicGeometry.Space.edsPreimageOpenMap_congr`, `…edsPreimageEtaleMap_congr`,
  `…edsPreimageInterMap_congr`: the three maps depend on the morphism `q` only through its
  value, the factorisation `q ≫ p = p'` being a proof.
* `AlgebraicGeometry.Space.edsEtale_hom_ext`: a morphism into the open
  subspace of a base change is determined by its composite with the open immersion, and one into
  the étale algebraic space by its two projections out of the fibre product `V₀ ×_{W₀} W`.

## The hypotheses carried

None beyond the elementary distinguished square and the morphisms themselves.  The third
morphism `r` of each cocycle identity is taken as an argument together with the equation
`r = q' ≫ q` rather than as the composite itself, so that the identity is available for
whichever morphism of the ambient system is at hand: in the application `r` is a transition
morphism or a projection of Situation 09RH and `q' ≫ q` is a composite of two of them, and the
two are equal by the composition law of the system, not by `rfl`.

## References

* [Stacks Project, Lemma 75.9.1 (Tag 08GN)](https://stacks.math.columbia.edu/tag/08GN)
* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W₀ : AlgebraicSpaces B S hS} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : Subfunctor W₀.1} {f₀ : V₀ ⟶ W₀.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W₀.2 U₀ f₀)
  {W W' W'' : AlgebraicSpaces B S hS}

/-! ### Extensionality for the two members of a base change -/

/-- The projection `V₀ ×_{W₀} W ⟶ V₀` of the étale algebraic space of a base change of an
elementary distinguished square, in the spelling that space has as an object of the category of
algebraic spaces over the base. -/
def edsPreimageEtaleToSource (p : W ⟶ W₀) :
    (edsEtale B S hS (edsPreimage hsq p)).obj ⟶ V₀ :=
  pullback.fst f₀ p.hom

/-- **A morphism into the étale algebraic space of a base change of an elementary distinguished
square is determined by its two projections** out of the fibre product `V₀ ×_{W₀} W`; the second
projection is the étale structure morphism of the base-changed square. -/
theorem edsEtale_hom_ext (p : W ⟶ W₀) {T : AlgebraicSpaces B S hS}
    {a b : T ⟶ edsEtale B S hS (edsPreimage hsq p)}
    (h₁ : a.hom ≫ edsPreimageEtaleToSource hsq p = b.hom ≫ edsPreimageEtaleToSource hsq p)
    (h₂ : a ≫ edsEtaleHom B S hS (edsPreimage hsq p) =
      b ≫ edsEtaleHom B S hS (edsPreimage hsq p)) : a = b :=
  ObjectProperty.hom_ext _ (pullback.hom_ext h₁ (congrArg (fun φ ↦ φ.hom) h₂))

/-- The map of étale algebraic spaces induced by `q` is compatible with the projection to
`V₀`. -/
theorem edsPreimageEtaleMap_hom_comp_toSource (p : W ⟶ W₀) (p' : W' ⟶ W₀) (q : W' ⟶ W)
    (hq : q ≫ p = p') :
    (edsPreimageEtaleMap hsq p p' q hq).hom ≫ edsPreimageEtaleToSource hsq p =
      edsPreimageEtaleToSource hsq p' :=
  pullback.lift_fst _ _ _

/-! ### Dependence on the inducing morphism only through its value -/

/-- The map of open subspaces induced by `q` depends on `q` only through its value: the
factorisation `q ≫ p = p'` is a proof, and two proofs of it are interchangeable. -/
theorem edsPreimageOpenMap_congr (p : W ⟶ W₀) (p' : W' ⟶ W₀) {q q' : W' ⟶ W} (hqq : q = q')
    (hq : q ≫ p = p') (hq' : q' ≫ p = p') :
    edsPreimageOpenMap hsq p p' q hq = edsPreimageOpenMap hsq p p' q' hq' := by
  subst hqq; rfl

/-- The map of étale algebraic spaces induced by `q` depends on `q` only through its value. -/
theorem edsPreimageEtaleMap_congr (p : W ⟶ W₀) (p' : W' ⟶ W₀) {q q' : W' ⟶ W} (hqq : q = q')
    (hq : q ≫ p = p') (hq' : q' ≫ p = p') :
    edsPreimageEtaleMap hsq p p' q hq = edsPreimageEtaleMap hsq p p' q' hq' := by
  subst hqq; rfl

/-- The map of intersections induced by `q` depends on `q` only through its value. -/
theorem edsPreimageInterMap_congr (p : W ⟶ W₀) (p' : W' ⟶ W₀) {q q' : W' ⟶ W} (hqq : q = q')
    (hq : q ≫ p = p') (hq' : q' ≫ p = p') :
    edsPreimageInterMap hsq p p' q hq = edsPreimageInterMap hsq p p' q' hq' := by
  subst hqq; rfl

/-- Pasting two commutative squares: `e'' ≫ q' ≫ q = (m' ≫ m) ≫ e`. -/
private theorem comp_comp_eq_comp_comp_of_comm_squares {C : Type*} [Category C]
    {A A' A'' X X' X'' : C} {e : A ⟶ X} {e' : A' ⟶ X'} {e'' : A'' ⟶ X''} {m : A' ⟶ A}
    {m' : A'' ⟶ A'} {q : X' ⟶ X} {q' : X'' ⟶ X'} (h : e' ≫ q = m ≫ e) (h' : e'' ≫ q' = m' ≫ e') :
    e'' ≫ q' ≫ q = (m' ≫ m) ≫ e := by
  simp [← h, reassoc_of% h']

/-! ### The cocycle identities -/

section Cocycle

variable (p : W ⟶ W₀) (p' : W' ⟶ W₀) (p'' : W'' ⟶ W₀) (q : W' ⟶ W) (q' : W'' ⟶ W')
  (hq : q ≫ p = p') (hq' : q' ≫ p' = p'') (r : W'' ⟶ W) (hr : r = q' ≫ q)
  (hrp : r ≫ p = p'')

include hr

/-- **The maps of the open subspaces of the base changes of an elementary distinguished square
compose.**  Both sides are determined by their composite with the open immersion of the base
change to `W`, where both are the inclusion of the open subspace of the base change to `W''`
followed by `r`. -/
theorem edsPreimageOpenMap_comp_edsPreimageOpenMap :
    edsPreimageOpenMap hsq p' p'' q' hq' ≫ edsPreimageOpenMap hsq p p' q hq =
      edsPreimageOpenMap hsq p p'' r hrp := by
  refine edsOpen_hom_ext (hsq := edsPreimage hsq p) ?_
  rw [← comp_comp_eq_comp_comp_of_comm_squares (edsPreimageOpenMap_comp hsq p p' q hq)
    (edsPreimageOpenMap_comp hsq p' p'' q' hq'), ← hr, edsPreimageOpenMap_comp hsq p p'' r hrp]

/-- **The maps of the étale algebraic spaces of the base changes of an elementary distinguished
square compose.**  Both sides are determined by their two projections out of the fibre product
`V₀ ×_{W₀} W`. -/
theorem edsPreimageEtaleMap_comp_edsPreimageEtaleMap :
    edsPreimageEtaleMap hsq p' p'' q' hq' ≫ edsPreimageEtaleMap hsq p p' q hq =
      edsPreimageEtaleMap hsq p p'' r hrp := by
  refine edsEtale_hom_ext hsq p ?_ ?_
  · rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
      edsPreimageEtaleMap_hom_comp_toSource hsq p p' q hq,
      edsPreimageEtaleMap_hom_comp_toSource hsq p' p'' q' hq',
      edsPreimageEtaleMap_hom_comp_toSource hsq p p'' r hrp]
  · rw [← comp_comp_eq_comp_comp_of_comm_squares (edsPreimageEtaleMap_comp hsq p p' q hq)
      (edsPreimageEtaleMap_comp hsq p' p'' q' hq'), ← hr,
      edsPreimageEtaleMap_comp hsq p p'' r hrp]

/-- **The maps of the intersections of the base changes of an elementary distinguished square
compose.**  Both sides are determined by their two projections out of the intersection of the
base change to `W`, and there they are the two identities already proved for the open subspaces
and for the étale algebraic spaces. -/
theorem edsPreimageInterMap_comp_edsPreimageInterMap :
    edsPreimageInterMap hsq p' p'' q' hq' ≫ edsPreimageInterMap hsq p p' q hq =
      edsPreimageInterMap hsq p p'' r hrp := by
  refine (isPullback_edsInter B S hS (edsPreimage hsq p)).hom_ext ?_ ?_
  · rw [← comp_comp_eq_comp_comp_of_comm_squares (edsFst_comp_edsPreimageOpenMap hsq p p' q hq)
      (edsFst_comp_edsPreimageOpenMap hsq p' p'' q' hq'),
      edsPreimageOpenMap_comp_edsPreimageOpenMap hsq p p' p'' q q' hq hq' r hr hrp,
      edsFst_comp_edsPreimageOpenMap hsq p p'' r hrp]
  · rw [← comp_comp_eq_comp_comp_of_comm_squares (edsSnd_comp_edsPreimageEtaleMap hsq p p' q hq)
      (edsSnd_comp_edsPreimageEtaleMap hsq p' p'' q' hq'),
      edsPreimageEtaleMap_comp_edsPreimageEtaleMap hsq p p' p'' q q' hq hq' r hr hrp,
      edsSnd_comp_edsPreimageEtaleMap hsq p p'' r hrp]

end Cocycle

/-! ### The maps induced by an identity -/

variable (p : W ⟶ W₀)

/-- **The map of open subspaces induced by an identity is an identity.** -/
theorem edsPreimageOpenMap_id (hp : (𝟙 W) ≫ p = p) :
    edsPreimageOpenMap hsq p p (𝟙 W) hp = 𝟙 _ := by
  refine edsOpen_hom_ext (hsq := edsPreimage hsq p) ?_
  rw [← edsPreimageOpenMap_comp hsq p p (𝟙 W) hp, Category.comp_id, Category.id_comp]

/-- **The map of étale algebraic spaces induced by an identity is an identity.** -/
theorem edsPreimageEtaleMap_id (hp : (𝟙 W) ≫ p = p) :
    edsPreimageEtaleMap hsq p p (𝟙 W) hp = 𝟙 _ := by
  refine edsEtale_hom_ext hsq p ?_ ?_
  · rw [edsPreimageEtaleMap_hom_comp_toSource hsq p p (𝟙 W) hp,
      ObjectProperty.FullSubcategory.id_hom, Category.id_comp]
  · rw [← edsPreimageEtaleMap_comp hsq p p (𝟙 W) hp, Category.comp_id, Category.id_comp]

/-- **The map of intersections induced by an identity is an identity.** -/
theorem edsPreimageInterMap_id (hp : (𝟙 W) ≫ p = p) :
    edsPreimageInterMap hsq p p (𝟙 W) hp = 𝟙 _ := by
  refine (isPullback_edsInter B S hS (edsPreimage hsq p)).hom_ext ?_ ?_
  · rw [← edsFst_comp_edsPreimageOpenMap hsq p p (𝟙 W) hp, edsPreimageOpenMap_id hsq p hp,
      Category.comp_id, Category.id_comp]
  · rw [← edsSnd_comp_edsPreimageEtaleMap hsq p p (𝟙 W) hp, edsPreimageEtaleMap_id hsq p hp,
      Category.comp_id, Category.id_comp]

end AlgebraicGeometry.Space

end
