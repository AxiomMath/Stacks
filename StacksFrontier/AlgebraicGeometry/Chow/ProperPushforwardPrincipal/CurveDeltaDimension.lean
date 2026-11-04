module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineDimension

/-!
# The delta-dimension of an integral scheme over a field is its topological dimension

Over `Stacks.Chow.fieldChowSituation k` — the spectrum of a field with the constant-zero
dimension function — the delta-dimension of an integral scheme `X` locally of finite type over
`k` is the topological Krull dimension of `X`: `dim_δ(X) = n` as soon as `dim(X) = n`.

Both directions of the comparison are Stacks 02QO, available here as
`Stacks.Chow.topologicalKrullDim_eq_relativeDimension_toNat` and
`Stacks.Chow.relativeDimension_nonneg`: over a Jacobson base whose dimension function vanishes at
closed points, the dimension of an integral closed subscheme is the relative dimension at its
generic point, and that relative dimension is nonnegative. The spectrum of a field is Jacobson
and its dimension function is identically zero, so both hypotheses are free; taking the closed
subscheme to be `X` itself gives the statement.

## Main definitions

* `Stacks.Chow.projectiveLineOverField`: the structure morphism of the projective line, with its
  target the base scheme of `Stacks.Chow.fieldChowSituation k`.

## Main results

* `Stacks.Chow.relativeDimension_fieldChowSituation_genericPoint`: at the generic point of an
  integral scheme over a field the relative dimension is the topological Krull dimension.
* `Stacks.Chow.schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq`: the
  delta-dimension of an integral scheme over a field is its topological Krull dimension.
* `Stacks.Chow.schemeDeltaDimension_projectiveLine`: the projective line has delta-dimension one.

## Implementation notes

The dimension hypothesis is stated as `topologicalKrullDim X = (n : WithBot ℕ∞)` for a natural
number `n`: that is the form in which the dimension of the projective line is available, and the
two coercion towers `ℕ → ℕ∞ → WithBot ℕ∞` and `ℤ → WithTop ℤ → Stacks.Chow.EInt` meet only
through a literal natural number.

The base scheme of `Stacks.Chow.fieldChowSituation k` is `Spec k` definitionally but not
reducibly, so an instance such as `LocallyOfFiniteType` found for a morphism to `Spec k` is not
found again for the same morphism viewed over the base of the situation. Each statement below
therefore takes its morphism with target `(fieldChowSituation k).S`, and the application to the
projective line supplies the instance by hand.

## References

* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k]

/-- The base scheme of `Stacks.Chow.fieldChowSituation k`, the spectrum of a field, is a Jacobson
space. -/
instance fieldChowSituation_jacobsonSpace (k : Type u) [Field k] :
    JacobsonSpace (fieldChowSituation k).S :=
  inferInstanceAs (JacobsonSpace (AlgebraicGeometry.Spec (CommRingCat.of k)))

/-- **The relative dimension at the generic point of a scheme over a field is its dimension.**
For an integral scheme `X` locally of finite type over a field `k` of topological Krull dimension
`n`, the relative dimension of the structure morphism at the generic point of `X` is `n`. -/
theorem relativeDimension_fieldChowSituation_genericPoint {X : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p] [IsIntegral X] {n : ℕ}
    (hdim : topologicalKrullDim X = (n : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation k).dimensionFunction p (genericPoint X) = (n : ℤ) := by
  have hgen : IsGenericPoint (genericPoint X) (Set.univ : Set X) :=
    (IrreducibleSpace.isIrreducible_univ X).isGenericPoint_genericPoint isClosed_univ
  have htop := topologicalKrullDim_eq_relativeDimension_toNat (fieldChowSituation k)
    (fun _ _ ↦ rfl) p (𝟙 X) (genericPoint X) hgen
  have hnonneg := relativeDimension_nonneg (fieldChowSituation k) (fun _ _ ↦ rfl) p
    (((𝟙 X) : X ⟶ X).base (genericPoint X))
  rw [hdim] at htop
  have hnat : (relativeDimension (fieldChowSituation k).dimensionFunction p
      (((𝟙 X) : X ⟶ X).base (genericPoint X))).toNat = n := by
    exact_mod_cast htop.symm
  have hid : ((𝟙 X) : X ⟶ X).base (genericPoint X) = genericPoint X := rfl
  rw [hid] at hnat hnonneg
  omega

/-- **The delta-dimension of an integral scheme over a field is its topological dimension.** For
an integral scheme `X` locally of finite type over a field `k` with `dim(X) = n`, the
delta-dimension of `X` over `Stacks.Chow.fieldChowSituation k` is `n`. -/
theorem schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq {X : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p] [IsIntegral X] {n : ℕ}
    (hdim : topologicalKrullDim X = (n : WithBot ℕ∞)) :
    schemeDeltaDimension (fieldChowSituation k) p = ((n : ℤ) : EInt) := by
  rw [schemeDeltaDimension_eq_genericPoint,
    relativeDimension_fieldChowSituation_genericPoint p hdim]

/-! ### The projective line as a scheme over the base of the situation -/

/-- The structure morphism of the projective line, presented as a morphism to the base scheme of
`Stacks.Chow.fieldChowSituation k`. -/
def projectiveLineOverField (k : Type u) [Field k] :
    projectiveLine k ⟶ (fieldChowSituation k).S :=
  projectiveLine k ↘ AlgebraicGeometry.Spec (.of k)

/-- The projective line over a field `k` is locally of finite type over the base scheme of
`Stacks.Chow.fieldChowSituation k`. -/
instance projectiveLineOverField_locallyOfFiniteType (k : Type u) [Field k] :
    LocallyOfFiniteType (projectiveLineOverField k) :=
  projectiveLine_locallyOfFiniteType_inst k

/-- The projective line over a field `k` is proper over the base scheme of
`Stacks.Chow.fieldChowSituation k`. -/
instance projectiveLineOverField_isProper (k : Type u) [Field k] :
    IsProper (projectiveLineOverField k) :=
  projectiveLine_isProper_inst k

/-- The residue degrees of the structure morphism of the projective line do not depend on which
of the two spellings of its target is used. -/
@[simp]
theorem projectiveLineOverField_residueDegree (k : Type u) [Field k] (x : projectiveLine k) :
    (projectiveLineOverField k).residueDegree x =
      (projectiveLine k ↘ AlgebraicGeometry.Spec (.of k)).residueDegree x :=
  rfl

/-- **The projective line has delta-dimension one.** The projective line over a field `k` has
delta-dimension `1` over `Stacks.Chow.fieldChowSituation k`. -/
theorem schemeDeltaDimension_projectiveLine (k : Type u) [Field k] :
    schemeDeltaDimension (fieldChowSituation k) (projectiveLineOverField k) = ((1 : ℤ) : EInt) :=
  schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq (n := 1)
    (projectiveLineOverField k) (by rw [topologicalKrullDim_projectiveLine]; rfl)

end Stacks.Chow

end
