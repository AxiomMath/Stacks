module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftAut

/-!
# Conjugating a lift of a morphism of schemes is an action

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`, let `P` be a deformation of `X` and
`Q` a deformation of `Y` over one object of `𝒞_Λ`, and let `ℓ : P.scheme ⟶ Q.scheme` be a lift
of `f` over the base. `Deformation.Examples.globalLiftsOverBaseConj` perturbs `ℓ` into
`β ∘ ℓ ∘ α⁻¹` for a pair `(α, β)` of invertible self-maps of the two total spaces, each over the
base and each fixing its special-fibre immersion. This file records that the perturbation is an
**action** of the group of such pairs: conjugating by `(α₁, β₁)` and then by `(α₂, β₂)` is
conjugating by the composite pair, and conjugating by the identity pair does nothing.

In the six-term exact sequence of [Stacks Project, Tag 0E3V] this is the group law of the
`gact` hypothesis of `Deformation.exact_triple_of_simplyTransitive` and of
`Deformation.map_add_of_simplyTransitive`: the arrow `b` out of `Inf(Def_X) × Inf(Def_Y)` is the
unique derivation carrying the trivial lift where the conjugation carries it, and the additivity
of `b` rests on the conjugation being an additive action of that `Inf` term. That the addition
of the `Inf` term is the composition appearing here is
`Deformation.Examples.localizedTangentEquivSelfMaps_add`.

## Main results

* `Deformation.Examples.globalLiftsOverBaseConj_comp`: conjugating twice is conjugating by the
  composite pair.
* `Deformation.Examples.globalLiftsOverBaseConj_id`: conjugating by the identity pair is the
  identity.

## Implementation notes

Both are equalities in a subtype, so both reduce by `Subtype.ext` and
`Deformation.Examples.globalLiftsOverBaseConj_val` to an identity between composites of
morphisms of schemes, and the only input is `CategoryTheory.IsIso.inv_comp` — the inverse of a
composite is the composite of the inverses in the other order, which is exactly what makes the
two parametrisations of the conjugation agree.

The composite pair's three side conditions are derived rather than taken as hypotheses: a
composite of self-maps over the base is over the base, and a composite fixing the special-fibre
immersion fixes it, both by one rewrite. So the statement takes only the conditions on the two
pairs separately, which is the shape an action law needs.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

section ConjAction

variable {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  {e : Q.base ⟶ P.base} [IsIso e]

omit [IsIso e] in
/-- **Conjugating by the identity pair does nothing.** This is the `act 0` law of the
conjugation action of [Stacks Project, Tag 0E3V]. -/
theorem globalLiftsOverBaseConj_id (ℓ : globalLiftsOverBase f P Q e) :
    globalLiftsOverBaseConj f pX pY ℓ (α := 𝟙 P.scheme) (β := 𝟙 Q.scheme)
        (inferInstanceAs (IsIso (𝟙 P.scheme)))
        (by rw [Category.id_comp]) (by rw [Category.comp_id])
        (by rw [Category.id_comp]) (by rw [Category.comp_id]) = ℓ := by
  refine Subtype.ext ?_
  rw [globalLiftsOverBaseConj_val]
  rw [IsIso.inv_id, Category.id_comp, Category.comp_id]

omit [IsIso e] in
/-- **Conjugating twice is conjugating by the composite pair.** This is the additivity law of
the conjugation action of [Stacks Project, Tag 0E3V]: perturbing `ℓ` by `(α₁, β₁)` and then by
`(α₂, β₂)` perturbs it by `(α₁ ≫ α₂, β₁ ≫ β₂)`, because the inverse of a composite is the
composite of the inverses in the other order.

Note the order: the outer conjugation contributes the *second* factor of the pair on the source
side and the *second* factor on the target side, so the composite pair is
`(α₁ ≫ α₂, β₁ ≫ β₂)` with the two factors in the same order on both sides. In the additive
reading of the `Inf` term, where composition is addition and addition is commutative, this is the
law `gact (g + g') ℓ = gact g (gact g' ℓ)` that
`Deformation.map_add_of_simplyTransitive` consumes. -/
theorem globalLiftsOverBaseConj_comp (ℓ : globalLiftsOverBase f P Q e)
    {α₁ α₂ : P.scheme ⟶ P.scheme} {β₁ β₂ : Q.scheme ⟶ Q.scheme}
    (hα₁ : IsIso α₁) (hα₂ : IsIso α₂)
    (hαb₁ : α₁ ≫ deformationAmbientToBase P e = deformationAmbientToBase P e)
    (hsα₁ : P.specialMap ≫ α₁ = P.specialMap)
    (hβb₁ : β₁ ≫ Q.toBase = Q.toBase)
    (hsβ₁ : Q.specialMap ≫ β₁ = Q.specialMap)
    (hαb₂ : α₂ ≫ deformationAmbientToBase P e = deformationAmbientToBase P e)
    (hsα₂ : P.specialMap ≫ α₂ = P.specialMap)
    (hβb₂ : β₂ ≫ Q.toBase = Q.toBase)
    (hsβ₂ : Q.specialMap ≫ β₂ = Q.specialMap) :
    globalLiftsOverBaseConj f pX pY
        (globalLiftsOverBaseConj f pX pY ℓ hα₁ hαb₁ hsα₁ hβb₁ hsβ₁)
        hα₂ hαb₂ hsα₂ hβb₂ hsβ₂ =
      globalLiftsOverBaseConj f pX pY ℓ (α := α₁ ≫ α₂) (β := β₁ ≫ β₂)
        (letI := hα₁; letI := hα₂; inferInstanceAs (IsIso (α₁ ≫ α₂)))
        (by rw [Category.assoc, hαb₂, hαb₁])
        (by rw [← Category.assoc, hsα₁, hsα₂])
        (by rw [Category.assoc, hβb₂, hβb₁])
        (by rw [← Category.assoc, hsβ₁, hsβ₂]) := by
  let := hα₁
  let := hα₂
  refine Subtype.ext ?_
  rw [globalLiftsOverBaseConj_val, globalLiftsOverBaseConj_val,
    globalLiftsOverBaseConj_val, IsIso.inv_comp]
  simp only [Category.assoc]

end ConjAction

end Deformation.Examples

end
