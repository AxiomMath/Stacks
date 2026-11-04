module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismFiberAutPair
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftClass

/-!
# Conjugating a lift, and the automorphisms of the deformation of `f` it determines

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`, let `P` be a deformation of `X` and
`Q` a deformation of `Y`, and let `ℓ : P.scheme ⟶ Q.scheme` be a lift of `f` over the base in
the sense of `Deformation.Examples.globalLiftsOverBase`. A pair `(α, β)` of invertible self-maps
of the two total spaces, each over the base and each fixing its special-fibre immersion, carries
`ℓ` to the conjugate lift `β ∘ ℓ ∘ α⁻¹`; this is the second action of the proof of
[Stacks Project, Tag 0E3V], the one written there as `β⁻¹ ∘ f' ∘ α`.

This file builds that action and identifies its stabiliser of `ℓ`: the pairs fixing `ℓ` are
exactly the pairs that come from an automorphism of the deformation of `f` determined by `ℓ`.
That is the input `ha` of `Deformation.exact_triple_of_simplyTransitive`, which is what the
three interior spots of the source's sequence are reduced to.

## Main definitions

* `Deformation.Examples.globalLiftsOverBaseConj`: the conjugate `β ∘ ℓ ∘ α⁻¹` of a lift, again a
  lift of `f` over the base.
* `Deformation.Examples.liftDeformationFiberAutEquivCompatiblePairs`:
  `Deformation.Examples.morphismFiberAutEquivSelfMapPairs` at the deformation of `f` determined
  by a lift, where the two total spaces are those of `P` and of `Q` and the arrow of the family
  is the lift itself.

## Main results

* `Deformation.Examples.globalLiftsOverBaseConj_eq_self_iff`: the conjugate of `ℓ` by `(α, β)` is
  `ℓ` exactly when `ℓ ∘ α = β ∘ ℓ`, the source's compatibility of the pair with `f'`.
* `Deformation.Examples.exists_liftDeformationFiberAut_eq_iff`: **the `ha` input of
  [Stacks Project, Tag 0E3V] at a lift.** A pair of self-maps of the two total spaces is the
  pair of components of an automorphism of the deformation of `f` determined by `ℓ` exactly when
  it fixes `ℓ` under conjugation.

## Implementation notes

The family `Deformation.Examples.liftSchemeMorphismFamily` of a lift has `P.scheme` as its
source, `Q.scheme` as its target and the lift as its arrow, and the two components of its arrow
down to the special fibre are the two special-fibre immersions — all by `rfl`. So
`Deformation.Examples.morphismFiberAutEquivSelfMapPairs` at
`Deformation.Examples.liftDeformationObject` is already the statement about `P`, `Q` and `ℓ`,
with no transport; `Deformation.Examples.liftDeformationFiberAutEquivCompatiblePairs` only
names it at that spelling.

The structure morphism of the source of that family is
`Deformation.Examples.deformationAmbientToBase P e` rather than `P.toBase`, because the two
deformations are given over bases related by `e` rather than over one object. The hypothesis on
`α` is therefore stated at that composite; for `e = 𝟙` it is `P.toBase` after
`Deformation.Examples.baseSpecMap_id`, which is the case the source's sequence uses.

The conjugate is written `α⁻¹ ≫ ℓ ≫ β` in diagrammatic order, i.e. `β ∘ ℓ ∘ α⁻¹`. The source
writes the perturbed arrow as `β⁻¹ ∘ f' ∘ α`, which is the conjugate by the inverse pair; the two
parametrisations of the same action differ by inverting, and the stabiliser condition
`ℓ ∘ α = β ∘ ℓ` is the same either way.

Invertibility of `α` is a hypothesis rather than a conclusion: unlike a self-map of a single
deformation, where
`Deformation.Examples.isIso_of_fixes_specialMap_over_base` makes it automatic, here `α` and `β`
are supplied separately and the conjugate has to be formed before any deformation-invariance
argument applies. Invertibility of `β` is not needed to form the conjugate and is not assumed.

No `@[stacks 0E3V]` attribute is carried: this is an input of the source's proof, not a clause of
its statement.

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

section LiftAut

variable {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  {e : Q.base ⟶ P.base} [IsIso e]

/-! ### The automorphisms of the deformation of `f` determined by a lift -/

/-- **An automorphism of the deformation of `f` determined by a lift is exactly a compatible
pair.** `Deformation.Examples.morphismFiberAutEquivSelfMapPairs` at
`Deformation.Examples.liftDeformationObject`, whose two total spaces are those of `P` and of `Q`
and whose arrow is the lift. -/
def liftDeformationFiberAutEquivCompatiblePairs (ℓ : globalLiftsOverBase f P Q e) :
    Aut (morphismDeformationFiberObj f pX pY hf (liftDeformationObject f pX pY hf ℓ)) ≃
      { p : (P.scheme ⟶ P.scheme) × (Q.scheme ⟶ Q.scheme) //
        IsIso p.1 ∧ IsIso p.2 ∧
          p.2 ≫ Q.toBase = Q.toBase ∧
          P.specialMap ≫ p.1 = P.specialMap ∧
          Q.specialMap ≫ p.2 = Q.specialMap ∧
          ℓ.1 ≫ p.2 = p.1 ≫ ℓ.1 } :=
  morphismFiberAutEquivSelfMapPairs f pX pY hf (liftDeformationObject f pX pY hf ℓ)

/-! ### Conjugating a lift -/

/-- **The conjugate `β ∘ ℓ ∘ α⁻¹` of a lift is a lift.** It is over the base because `α` and `β`
are, and it restricts to `f` on the special fibre because `α` and `β` fix the two special-fibre
immersions. -/
def globalLiftsOverBaseConj (ℓ : globalLiftsOverBase f P Q e)
    {α : P.scheme ⟶ P.scheme} {β : Q.scheme ⟶ Q.scheme} (hα : IsIso α)
    (hαb : α ≫ deformationAmbientToBase P e = deformationAmbientToBase P e)
    (hsα : P.specialMap ≫ α = P.specialMap)
    (hβb : β ≫ Q.toBase = Q.toBase)
    (hsβ : Q.specialMap ≫ β = Q.specialMap) :
    globalLiftsOverBase f P Q e := by
  let := hα
  have hαb' : CategoryTheory.inv α ≫ deformationAmbientToBase P e =
      deformationAmbientToBase P e := by
    rw [IsIso.inv_comp_eq, hαb]
  have hsα' : P.specialMap ≫ CategoryTheory.inv α = P.specialMap := by
    rw [IsIso.comp_inv_eq, hsα]
  refine ⟨CategoryTheory.inv α ≫ ℓ.1 ≫ β, ?_, ?_⟩
  · simp only [Category.assoc, hβb, ℓ.2.1, hαb']
  · rw [← Category.assoc, hsα', ← Category.assoc, ℓ.2.2, Category.assoc, hsβ]

omit [IsIso e] in
/-- The underlying morphism of the conjugate lift `globalLiftsOverBaseConj` is `α⁻¹ ≫ ℓ ≫ β`. -/
@[simp]
theorem globalLiftsOverBaseConj_val (ℓ : globalLiftsOverBase f P Q e)
    {α : P.scheme ⟶ P.scheme} {β : Q.scheme ⟶ Q.scheme} (hα : IsIso α)
    (hαb : α ≫ deformationAmbientToBase P e = deformationAmbientToBase P e)
    (hsα : P.specialMap ≫ α = P.specialMap)
    (hβb : β ≫ Q.toBase = Q.toBase)
    (hsβ : Q.specialMap ≫ β = Q.specialMap) :
    (globalLiftsOverBaseConj f pX pY ℓ hα hαb hsα hβb hsβ).1 =
      CategoryTheory.inv α ≫ ℓ.1 ≫ β := rfl

omit [IsIso e] in
/-- **The conjugate of a lift by a pair is the lift itself exactly when the pair is compatible
with it**, i.e. when `ℓ ∘ α = β ∘ ℓ`. -/
theorem globalLiftsOverBaseConj_eq_self_iff (ℓ : globalLiftsOverBase f P Q e)
    {α : P.scheme ⟶ P.scheme} {β : Q.scheme ⟶ Q.scheme} (hα : IsIso α)
    (hαb : α ≫ deformationAmbientToBase P e = deformationAmbientToBase P e)
    (hsα : P.specialMap ≫ α = P.specialMap)
    (hβb : β ≫ Q.toBase = Q.toBase)
    (hsβ : Q.specialMap ≫ β = Q.specialMap) :
    globalLiftsOverBaseConj f pX pY ℓ hα hαb hsα hβb hsβ = ℓ ↔
      ℓ.1 ≫ β = α ≫ ℓ.1 := by
  let := hα
  refine ⟨fun h => ?_, fun h => Subtype.ext ?_⟩
  · exact (IsIso.inv_comp_eq α).mp (congrArg Subtype.val h)
  · rw [globalLiftsOverBaseConj_val, h, IsIso.inv_hom_id_assoc]

/-! ### The `ha` input of the torsor computation -/

/-- **The `ha` input of [Stacks Project, Tag 0E3V] at a lift.** A pair `(α, β)` of invertible
self-maps of the two total spaces, each over the base and each fixing its special-fibre
immersion, is the pair of components of an automorphism of the deformation of `f` determined by
`ℓ` **exactly when it fixes `ℓ` under conjugation**.

This is the hypothesis `ha` of `Deformation.exact_triple_of_simplyTransitive`, with the acting
group the pairs of self-maps, the set of lifts
`Deformation.Examples.globalLiftsOverBase`, the base point `ℓ`, and the action
`Deformation.Examples.globalLiftsOverBaseConj`. In the source: "a pair `(α, β)` of infinitesimal
automorphisms of `X` and `Y` comes from an infinitesimal automorphism of `f'` exactly when it
commutes with `f'`". -/
theorem exists_liftDeformationFiberAut_eq_iff (ℓ : globalLiftsOverBase f P Q e)
    {α : P.scheme ⟶ P.scheme} {β : Q.scheme ⟶ Q.scheme} (hα : IsIso α) (hβ : IsIso β)
    (hαb : α ≫ deformationAmbientToBase P e = deformationAmbientToBase P e)
    (hsα : P.specialMap ≫ α = P.specialMap)
    (hβb : β ≫ Q.toBase = Q.toBase)
    (hsβ : Q.specialMap ≫ β = Q.specialMap) :
    (∃ a : Aut (morphismDeformationFiberObj f pX pY hf
        (liftDeformationObject f pX pY hf ℓ)),
      (liftDeformationFiberAutEquivCompatiblePairs f pX pY hf ℓ a).val = (α, β)) ↔
      globalLiftsOverBaseConj f pX pY ℓ hα hαb hsα hβb hsβ = ℓ := by
  rw [globalLiftsOverBaseConj_eq_self_iff]
  constructor
  · rintro ⟨a, ha⟩
    have hc := (liftDeformationFiberAutEquivCompatiblePairs f pX pY hf ℓ a).2.2.2.2.2.2
    rwa [ha] at hc
  · intro hcomm
    exact ⟨(liftDeformationFiberAutEquivCompatiblePairs f pX pY hf ℓ).symm
        ⟨(α, β), hα, hβ, hβb, hsα, hsβ, hcomm⟩,
      congrArg Subtype.val
        ((liftDeformationFiberAutEquivCompatiblePairs f pX pY hf ℓ).apply_symm_apply _)⟩

end LiftAut

end Deformation.Examples

end
