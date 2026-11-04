module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupGroundFieldExtension

/-!
# A property of the automorphism group of an algebraic stack at a point (Stacks 0DTU)

Let `P` be a property of algebraic spaces over fields which is invariant under ground field
extensions, in the sense of
`AlgebraicGeometry.Stack.IsInvariantUnderGroundFieldExtension`. Let `𝒳` be an algebraic stack
and let `q ∈ |𝒳|` be a point. Stacks 0DTT says that the automorphism group algebraic space
`G_x/k = Isom_𝒳(x, x)` of a field-valued representative `x : Spec k → 𝒳` of `q` has `P` for
*some* representative exactly when it has `P` for *every* representative. Stacks 0DTU is the
definition this equivalence licenses: one says *the automorphism group of `𝒳` at `q` has `P`*
when those equivalent conditions hold.

`AlgebraicGeometry.Stack.AutomorphismGroupHasProperty` is that notion, spelled as condition (2)
of Stacks 0DTT — `P` holds for the automorphism group algebraic space of every field-valued
representative of `q`. So stated it involves no choice of representative at all, and
`AlgebraicGeometry.Stack.automorphismGroupHasProperty_iff_of_representative` is the
well-posedness statement that makes the phrase meaningful: for a ground-field-invariant `P` the
notion is already decided by *any single* representative, so reading the definition at one
representative gives the same answer as reading it at another.

## Main definitions

* `AlgebraicGeometry.Stack.AutomorphismGroupHasProperty`: the automorphism group of `𝒳` at a
  point `q` of `|𝒳|` has `P`.

## Main results

* `AlgebraicGeometry.Stack.automorphismGroupHasProperty_iff_of_representative`: for a
  ground-field-invariant `P` the notion is computed at an arbitrary single representative of the
  point — the well-posedness of **Stacks 0DTU**.
* `AlgebraicGeometry.Stack.automorphismGroupHasProperty_iff_exists`: the two equivalent
  conditions of Stacks 0DTT, read through the definition.
* `AlgebraicGeometry.Stack.exists_of_automorphismGroupHasProperty`: the definition is not
  vacuous — every point of `|𝒳|` has a field-valued representative, so the notion always
  exhibits an algebraic space over a field with `P`. This needs no invariance hypothesis.

## Implementation notes

The definition is stated for the general `P` of Stacks 0DTT, that is for a predicate on the
presheaves on the big fppf site of an object of the big fppf site of `S`, as in
`AlgebraicGeometry.Stack.IsInvariantUnderGroundFieldExtension`. The invariance of `P` is a
hypothesis of the well-posedness results and is not built into the definition, matching the way
Stacks 0DTT is stated in
`AlgebraicGeometry.Stack.exists_pointAutomorphismSpace_iff_forall`; without it
`AlgebraicGeometry.Stack.AutomorphismGroupHasProperty` is still the `∀`-form, hence still
independent of any choice, but it need no longer agree with the `∃`-form.

## Not formalized here

Remark 0DTU goes on to name the instances it is used for: "the automorphism group of `𝒳` at `x`
is finite", and similarly smooth, proper, and so on. Those are instantiations of the definition
below at the property "`G → Spec k` is finite" and its variants, read in the `∀`-form, and they
are not carried out here. Writing one down asks for the property of a bare presheaf that its
structure morphism, as an algebraic space over the field spectrum, is finite — the predicate
`AlgebraicGeometry.Space.IsFinite` applied to a structure morphism. Making such an instance
*useful*, i.e. an instance to which
`AlgebraicGeometry.Stack.automorphismGroupHasProperty_iff_of_representative` applies, needs its
ground field invariance, and that is a descent statement in the unavailable direction: stability
of finiteness under base change is
`AlgebraicGeometry.Space.isFinite_of_isPullback`, but the converse — that finiteness of the base
change along `Spec k' → Spec k` implies finiteness over `Spec k` — asks for finiteness to be
local at the target for the fpqc topology (Stacks 0422-style locality), which this development
does not have; compare the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties`, where the corresponding
locality for separatedness and universal closedness is likewise recorded as a hypothesis rather
than a theorem. The same remark applies verbatim to smooth and proper.

## References

* [Stacks Project, Tag 0DTU](https://stacks.math.columbia.edu/tag/0DTU)
* [Stacks Project, Tag 0DTT](https://stacks.math.columbia.edu/tag/0DTT)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0DTU.** Let `P` be a property of algebraic spaces over fields and let `q` be a point
of `|𝒳|` for an algebraic stack `𝒳`. The *automorphism group of `𝒳` at `q` has `P`* when the
automorphism group algebraic space `G_x/k = Isom_𝒳(x, x)` has `P` for every field-valued
representative `x : Spec k → 𝒳` of `q`.

This is condition (2) of Stacks 0DTT, so it makes no choice of representative. When `P` is
invariant under ground field extensions
(`AlgebraicGeometry.Stack.IsInvariantUnderGroundFieldExtension`) it agrees with condition (1) of
Stacks 0DTT by `AlgebraicGeometry.Stack.automorphismGroupHasProperty_iff_exists`, and it is
decided by any single representative by
`AlgebraicGeometry.Stack.automorphismGroupHasProperty_iff_of_representative`; that is what makes
the phrase well posed, and it is the content of Remark 0DTU. -/
@[stacks 0DTU "the definition: the automorphism group of a stack at a point has P when the \
automorphism group algebraic space of every field-valued representative has P"]
def AutomorphismGroupHasProperty
    (P : ∀ U : BigFppfOver B S hS, ((BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u) → Prop)
    (q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids) : Prop :=
  ∀ p : FieldValuedPoint B S hS 𝒳.val.val,
    pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = q →
      P p.base (pointAutomorphismSpace B S hS 𝒳.val p)

/-- The notion of `AlgebraicGeometry.Stack.AutomorphismGroupHasProperty` is not vacuous: a point
of `|𝒳|` is an equivalence class of field-valued points, hence has a representative, so if the
automorphism group of `𝒳` at `q` has `P` then `P` does hold for the automorphism group algebraic
space of some field-valued point. No invariance of `P` is needed for this. -/
theorem exists_of_automorphismGroupHasProperty
    (P : ∀ U : BigFppfOver B S hS, ((BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u) → Prop)
    {q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids}
    (h : AutomorphismGroupHasProperty B S hS P q) :
    ∃ p : FieldValuedPoint B S hS 𝒳.val.val,
      pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = q ∧
        P p.base (pointAutomorphismSpace B S hS 𝒳.val p) := by
  obtain ⟨p, hp⟩ := Quotient.exists_rep q
  exact ⟨p, hp, h p hp⟩

/-- **The two conditions of Stacks 0DTT read through the definition of Stacks 0DTU.** For a
property `P` of algebraic spaces over fields which is invariant under ground field extensions,
the automorphism group of `𝒳` at `q` has `P` exactly when the automorphism group algebraic space
of *some* field-valued representative of `q` has `P`. -/
theorem automorphismGroupHasProperty_iff_exists
    (P : ∀ U : BigFppfOver B S hS, ((BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u) → Prop)
    (hP : IsInvariantUnderGroundFieldExtension B S hS P)
    (q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids) :
    AutomorphismGroupHasProperty B S hS P q ↔
      ∃ p : FieldValuedPoint B S hS 𝒳.val.val,
        pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = q ∧
          P p.base (pointAutomorphismSpace B S hS 𝒳.val p) :=
  (exists_pointAutomorphismSpace_iff_forall B S hS q P hP).symm

/-- **Stacks 0DTU: the phrase is well posed.** For a property `P` of algebraic spaces over fields
which is invariant under ground field extensions, the statement that the automorphism group of
`𝒳` at `q` has `P` is decided by an arbitrary single field-valued representative `p` of `q`:
it holds exactly when the automorphism group algebraic space `G_p` has `P`. In particular the
answer does not depend on which representative of `q` one reads it at, which is what licenses
the phrase "the automorphism group of `𝒳` at `q` has `P`" of Remark 0DTU. -/
@[stacks 0DTU "the phrase is well posed: for a property invariant under ground field \
extensions, an arbitrary single field-valued representative decides it"]
theorem automorphismGroupHasProperty_iff_of_representative
    (P : ∀ U : BigFppfOver B S hS, ((BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u) → Prop)
    (hP : IsInvariantUnderGroundFieldExtension B S hS P)
    {q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids}
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (hp : pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = q) :
    AutomorphismGroupHasProperty B S hS P q ↔
      P p.base (pointAutomorphismSpace B S hS 𝒳.val p) := by
  refine ⟨fun h => h p hp, fun h => ?_⟩
  exact (automorphismGroupHasProperty_iff_exists B S hS P hP q).mpr ⟨p, hp, h⟩

end AlgebraicGeometry.Stack

end

