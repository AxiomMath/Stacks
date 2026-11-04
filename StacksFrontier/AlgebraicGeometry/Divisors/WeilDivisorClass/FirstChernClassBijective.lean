module

public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FactorialOfSurjective
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassInjective
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassSurjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Factorial local rings and the divisor class group

Let `X` be a locally Noetherian integral scheme. The local rings of `X` are unique factorization
domains exactly when `X` is normal and the first Chern class `Pic(X) → Cl(X)` is surjective; and
in that case `Pic(X) → Cl(X)` is an isomorphism. This is [Stacks, Tag 0BE9].

The implication from factoriality to normality is immediate: a unique factorization domain is
integrally closed, which is Tag 0AFV. Surjectivity of the first Chern class under factoriality is
`AlgebraicGeometry.picardToWeilDivisorClassGroup_surjective`, which constructs `𝒪_X(D)` for an
arbitrary Weil divisor `D`. Conversely a normal scheme with surjective first Chern class has
factorial local rings, by
`AlgebraicGeometry.uniqueFactorizationMonoid_stalk_of_surjective_picardToWeilDivisorClassGroup`,
which exhibits every height-one prime of a local ring as a principal ideal. Finally normality
makes the first Chern class injective, by Tag 0BE8, so a surjective one is an isomorphism.

## Main results

* `isNormal_of_forall_uniqueFactorizationMonoid_stalk`: a scheme whose local rings are unique
  factorization domains is normal.
* `picardToWeilDivisorClassGroup_bijective`: on a normal locally Noetherian integral scheme a
  surjective first Chern class is bijective.
* `picardEquivWeilDivisorClassGroup`: the resulting isomorphism `Pic(X) ≅ Cl(X)`.
* `forall_uniqueFactorizationMonoid_stalk_iff_isNormal_and_surjective`: **Stacks 0BE9**, the
  equivalence of the two conditions.
* `picardToWeilDivisorClassGroup_bijective_of_forall_uniqueFactorizationMonoid`: **Stacks 0BE9**,
  the final clause: under either condition `Pic(X) → Cl(X)` is an isomorphism.
* `forall_uniqueFactorizationMonoid_stalk_iff_isNormal_and_surjective_and_picardEquiv`:
  **Stacks 0BE9** in full, the equivalence of the two conditions together with the isomorphism
  `Pic(X) ≅ Cl(X)` that holds in that case.

## References

* [Stacks Project, Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9)
* [Stacks Project, Tag 0AFV](https://stacks.math.columbia.edu/tag/0AFV)
* [Stacks Project, Tag 0BE8](https://stacks.math.columbia.edu/tag/0BE8)
* [Stacks Project, Tag 0BE7](https://stacks.math.columbia.edu/tag/0BE7)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

attribute [local instance] schemePicardGroupAddCommGroup

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
/-- A scheme whose local rings are unique factorization domains is normal: a unique
factorization domain is integrally closed, which is Tag 0AFV.

**Stacks 0BE9**, the normality half of the implication from condition (1) to condition (2). -/
@[stacks 0BE9 "(1) → (2): factorial local rings give a normal scheme"]
theorem isNormal_of_forall_uniqueFactorizationMonoid_stalk
    (h : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) : IsNormal X where
  stalk_isDomain x := inferInstance
  stalk_normal x := by
    have := h x
    infer_instance

/-- On a normal locally Noetherian integral scheme a surjective first Chern class
`Pic(X) → Cl(X)` is bijective, since it is injective by Tag 0BE8.

**Stacks 0BE9**, the final clause under condition (2). -/
@[stacks 0BE9 "final clause under (2): on a normal scheme a surjective c_1 is bijective"]
theorem picardToWeilDivisorClassGroup_bijective [IsNormal X]
    (hsurj : Function.Surjective (picardToWeilDivisorClassGroup X)) :
    Function.Bijective (picardToWeilDivisorClassGroup X) :=
  ⟨picardToWeilDivisorClassGroup_injective X, hsurj⟩

/-- The isomorphism `Pic(X) ≅ Cl(X)` of a normal locally Noetherian integral scheme on which the
first Chern class is surjective. -/
def picardEquivWeilDivisorClassGroup [IsNormal X]
    (hsurj : Function.Surjective (picardToWeilDivisorClassGroup X)) :
    Stacks.SheafOfModules.PicardGroup X.sheaf.obj X.ringCatSheaf.property ≃+
      weilDivisorClassGroup X :=
  AddEquiv.ofBijective _ (picardToWeilDivisorClassGroup_bijective X hsurj)

/-- The isomorphism of `AlgebraicGeometry.picardEquivWeilDivisorClassGroup` is the first Chern
class. -/
@[simp]
theorem picardEquivWeilDivisorClassGroup_apply [IsNormal X]
    (hsurj : Function.Surjective (picardToWeilDivisorClassGroup X))
    (x : Stacks.SheafOfModules.PicardGroup X.sheaf.obj X.ringCatSheaf.property) :
    picardEquivWeilDivisorClassGroup X hsurj x = picardToWeilDivisorClassGroup X x :=
  rfl

/-- **Stacks 0BE9.** For a locally Noetherian integral scheme the local rings are unique
factorization domains exactly when the scheme is normal and the first Chern class
`Pic(X) → Cl(X)` of Tag 0BE7 is surjective.

Forwards, normality is `AlgebraicGeometry.isNormal_of_forall_uniqueFactorizationMonoid_stalk` and
surjectivity is `AlgebraicGeometry.picardToWeilDivisorClassGroup_surjective`; backwards this is
`AlgebraicGeometry.uniqueFactorizationMonoid_stalk_of_surjective_picardToWeilDivisorClassGroup`. -/
@[stacks 0BE9 "the equivalence of conditions (1) and (2)", sga "2 XI 3.8" "partial"]
theorem forall_uniqueFactorizationMonoid_stalk_iff_isNormal_and_surjective :
    (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) ↔
      (IsNormal X ∧ Function.Surjective (picardToWeilDivisorClassGroup X)) := by
  constructor
  · intro h
    exact ⟨isNormal_of_forall_uniqueFactorizationMonoid_stalk X h,
      picardToWeilDivisorClassGroup_surjective h⟩
  · rintro ⟨hNormal, hsurj⟩
    exact uniqueFactorizationMonoid_stalk_of_surjective_picardToWeilDivisorClassGroup hsurj

/-- **Stacks 0BE9, the final clause.** On a locally Noetherian integral scheme whose local rings
are unique factorization domains the first Chern class `Pic(X) → Cl(X)` is an isomorphism:
factoriality makes `X` normal, so Tag 0BE8 gives injectivity, and
`AlgebraicGeometry.picardToWeilDivisorClassGroup_surjective` gives surjectivity. -/
@[stacks 0BE9 "the isomorphism Pic(X) = Cl(X)",
  ega "IV 21.6.10" "(i), injectivity, (ii)",
  sga "2 XI 3.7.1" "special case",
  sga "2 XI 3.8" "special case"]
theorem picardToWeilDivisorClassGroup_bijective_of_forall_uniqueFactorizationMonoid
    (h : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    Function.Bijective (picardToWeilDivisorClassGroup X) :=
  have := isNormal_of_forall_uniqueFactorizationMonoid_stalk X h
  picardToWeilDivisorClassGroup_bijective X (picardToWeilDivisorClassGroup_surjective h)

/-- The isomorphism `Pic(X) ≅ Cl(X)` of a locally Noetherian integral scheme whose local rings
are unique factorization domains. -/
@[sga "2 XI 3.7.1" "special case", sga "2 XI 3.8" "special case"]
def picardEquivWeilDivisorClassGroupOfForallUniqueFactorizationMonoid
    (h : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    Stacks.SheafOfModules.PicardGroup X.sheaf.obj X.ringCatSheaf.property ≃+
      weilDivisorClassGroup X :=
  AddEquiv.ofBijective _
    (picardToWeilDivisorClassGroup_bijective_of_forall_uniqueFactorizationMonoid X h)

/-- **Stacks 0BE9.** Let `X` be a locally Noetherian integral scheme and consider the first Chern
class `Pic(X) → Cl(X)` of Tag 0BE7. The following are equivalent:

1. the local rings of `X` are unique factorization domains, and
2. `X` is normal and `Pic(X) → Cl(X)` is surjective.

In this case `Pic(X) → Cl(X)` is an isomorphism.

The equivalence is
`AlgebraicGeometry.forall_uniqueFactorizationMonoid_stalk_iff_isNormal_and_surjective`, and the
isomorphism is
`AlgebraicGeometry.picardEquivWeilDivisorClassGroupOfForallUniqueFactorizationMonoid`, whose
underlying map is the first Chern class. -/
@[stacks 0BE9 "the full statement: (1) ⟺ (2), and in that case Pic(X) ≅ Cl(X)",
  sga "2 XI 3.7.1" "special case",
  sga "2 XI 3.8" "partial"]
theorem forall_uniqueFactorizationMonoid_stalk_iff_isNormal_and_surjective_and_picardEquiv :
    ((∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) ↔
        IsNormal X ∧ Function.Surjective (picardToWeilDivisorClassGroup X)) ∧
      ((∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) →
        ∃ e : Stacks.SheafOfModules.PicardGroup X.sheaf.obj X.ringCatSheaf.property ≃+
          weilDivisorClassGroup X, ∀ c, e c = picardToWeilDivisorClassGroup X c) :=
  ⟨forall_uniqueFactorizationMonoid_stalk_iff_isNormal_and_surjective X, fun h =>
    ⟨picardEquivWeilDivisorClassGroupOfForallUniqueFactorizationMonoid X h, fun _ => rfl⟩⟩

end AlgebraicGeometry

end
