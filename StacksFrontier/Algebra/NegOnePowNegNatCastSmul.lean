module

public import StacksFrontier.Algebra.NegOnePowSmul

/-!
# The `(-1)^{-k}` action of a negated natural number

For the exponent a negated natural number — the shape the sign of a shift `[-k]` of a cochain
complex has — `units_negOnePow_neg_natCast_smul` states the action of `Int.negOnePow (-k)` as
`(-1 : ℤ) ^ k`, which is the spelling a graded Leibniz rule carries.
-/

@[expose] public section

/-- **The `Int.negOnePow (-k)` action of a negated natural number is multiplication by
`(-1 : ℤ) ^ k`.** The sign that the shift `[-k]` of a cochain complex carries is written
`Int.negOnePow (-(k : ℤ))`, while the sign of a graded Leibniz rule is written `(-1 : ℤ) ^ k`;
this is the identity between the two actions, with no `Int.natAbs` left in it.

Only an additive group is needed: the `ℤˣ` action factors through the `ℤ` action, so this applies
in particular to the morphism groups of a preadditive category, which carry no ring action. -/
public theorem units_negOnePow_neg_natCast_smul {M : Type*} [AddCommGroup M] (k : ℕ) (x : M) :
    (-(k : ℤ)).negOnePow • x = (-1 : ℤ) ^ k • x := by
  rw [units_negOnePow_smul_eq (R := ℤ)]
  simp

end
