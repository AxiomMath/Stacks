module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Field-valued points over a purely inseparable residue field extension

A morphism `Spec K ⟶ X` from the spectrum of a field is the same thing as a point `x` of `X`
together with an embedding `κ(x) ⟶ K` of its residue field. Consequently, if `f : X ⟶ Y` is a
morphism of schemes and `α, β : Spec K ⟶ X` have the same image point `x` and the same
composite with `f`, then `α` and `β` differ only by the two embeddings `κ(x) ⟶ K` they
determine, and those two embeddings agree on `κ(f x)`. So `α = β` as soon as an embedding of
`κ(x)` into a field is determined by its restriction to `κ(f x)` — which is exactly what pure
inseparability of `κ(x)/κ(f x)` provides.

This is the "two towers of fields" step in the proof of [Stacks Project, Tag 0DT9]. There the
source text compares the two towers `κ(r')/κ(u'_i)/κ(u)/κ(p)` and `κ(r')/κ(u'_i)/κ(p')/κ(p)`
and concludes, from pure inseparability of `κ(u)/κ(p)`, that the two induced maps
`κ(u) ⟶ κ(r')` coincide; in the formulation below `X`, `Y`, `K` are `U`, `Spec C` and `κ(r')`,
and the two field-valued points are the source and the target of the arrow `r'`.

## Main results

* `AlgebraicGeometry.eq_of_comp_eq_of_injective_residueFieldMap_comp`: the elementary form —
  two field-valued points with a common image point and a common composite with `f` agree, as
  soon as precomposition with the residue field map of `f` at that point is injective on
  embeddings into the field.
* `AlgebraicGeometry.eq_of_comp_eq_of_isPurelyInseparable`: **the same conclusion from pure
  inseparability of the residue field extension at the common image point.**

## Implementation notes

The algebra structure on `κ(x)` over `κ(f x)` is passed as an instance argument together with
an equation identifying its structure map with `AlgebraicGeometry.Scheme.Hom.residueFieldMap`,
rather than installed by a `let` inside the statement: a `let`-bound instance in the statement
of a theorem is not the instance the caller has, and the caller is the one holding the pure
inseparability. This is the same shape as
`StacksDraft.RingTheory.Jacobson.Constructions.isMaximal_of_isAlgebraic_residueField`.

The elementary form is stated with the injectivity hypothesis rather than with
`CategoryTheory.Epi` on the residue field map because the consumer obtains it from
`IsPurelyInseparable.injective_comp_algebraMap`, which is an injectivity statement about ring
homomorphisms out of the extension.

## References

* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {K : Type u} [Field K]

/-- **A field-valued point of `X` with image point `x` factors through the residue field point
of `x`**, by an embedding `κ(x) ⟶ K` which the factorization determines. -/
theorem exists_specMap_fromSpecResidueField_eq {α : Spec (.of K) ⟶ X} {x : X}
    (hα : α.base (IsLocalRing.closedPoint K) = x) :
    ∃ a : X.residueField x ⟶ CommRingCat.of K,
      Spec.map a ≫ X.fromSpecResidueField x = α :=
  ⟨(X.residueFieldCongr hα.symm).hom ≫ X.descResidueField (Scheme.stalkClosedPointTo α), by
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]⟩

/-- Two field-valued points of `X` with the same image point and the same composite with
`f : X ⟶ Y` agree, as soon as precomposition with the residue field map of `f` at that point is
injective on embeddings of the residue field into the field.

A morphism `Spec K ⟶ X` is a point of `X` together with an embedding of its residue field into
`K`, so the two morphisms differ only in that embedding, and equality of the composites with `f`
says exactly that the two embeddings become equal after precomposition with the residue field
map of `f`. -/
theorem eq_of_comp_eq_of_injective_residueFieldMap_comp {α β : Spec (.of K) ⟶ X} {x : X}
    (hα : α.base (IsLocalRing.closedPoint K) = x)
    (hβ : β.base (IsLocalRing.closedPoint K) = x)
    (hcomp : α ≫ f = β ≫ f)
    (hinj : Function.Injective
      fun a : X.residueField x ⟶ CommRingCat.of K => f.residueFieldMap x ≫ a) :
    α = β := by
  obtain ⟨a, hfa⟩ := exists_specMap_fromSpecResidueField_eq hα
  obtain ⟨b, hfb⟩ := exists_specMap_fromSpecResidueField_eq hβ
  rw [← hfa, ← hfb]
  refine congrArg (· ≫ X.fromSpecResidueField x) (congrArg Spec.map (hinj ?_))
  rw [← Spec.map_inj, ← cancel_mono (Y.fromSpecResidueField (f.base x))]
  simp only [Spec.map_comp, Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [← Category.assoc, ← Category.assoc, hfa, hfb, hcomp]

/-- **A field-valued point of `X` is determined by its image point and its composite with
`f : X ⟶ Y`, when the residue field extension of `f` at that point is purely inseparable.**

The two morphisms determine two embeddings of `κ(x)` into `K` which agree on `κ(f x)`, and a
purely inseparable extension admits at most one embedding into a reduced ring over its base. -/
theorem eq_of_comp_eq_of_isPurelyInseparable {α β : Spec (.of K) ⟶ X} {x : X}
    (hα : α.base (IsLocalRing.closedPoint K) = x)
    (hβ : β.base (IsLocalRing.closedPoint K) = x)
    (hcomp : α ≫ f = β ≫ f)
    [Algebra (Y.residueField (f.base x)) (X.residueField x)]
    (hcompat : algebraMap (Y.residueField (f.base x)) (X.residueField x) =
      (f.residueFieldMap x).hom)
    [IsPurelyInseparable (Y.residueField (f.base x)) (X.residueField x)] :
    α = β := by
  refine eq_of_comp_eq_of_injective_residueFieldMap_comp f hα hβ hcomp fun a b hab => ?_
  refine CommRingCat.hom_ext ?_
  refine IsPurelyInseparable.injective_comp_algebraMap
    (Y.residueField (f.base x)) (X.residueField x) K ?_
  rw [hcompat]
  exact congrArg CommRingCat.Hom.hom hab

end AlgebraicGeometry

end

end
