module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.AffineOpens
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.RingTheory.DimensionFormula

/-!
# The dimension formula for a dominant morphism locally of finite type

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be dominant and locally of finite type with
`X` and `S` integral, let `x` be a point of `X` and `s = f x`. Then

`dim 𝒪_{X, x} + trdeg_{κ(s)} κ(x) ≤ dim 𝒪_{S, s} + trdeg_{R(S)} R(X)`,

with equality when `S` is universally catenary. Dimensions take values in `WithBot ℕ∞`, where
subtraction is truncated, so the formula is stated in this additive form. Transcendence degrees are
`Cardinal.toNat (Algebra.trdeg _ _)`, the `κ(s)`-algebra structure on `κ(x)` is
`Scheme.Hom.residueFieldMap` and the `R(S)`-algebra structure on `R(X)` is
`Scheme.Hom.functionFieldMap`.

## Main results

* `AlgebraicGeometry.ringKrullDim_stalk_add_trdeg_residueField_le` is the inequality.
* `AlgebraicGeometry.ringKrullDim_stalk_add_trdeg_residueField_eq` is the equality for a
  universally catenary base.

## References

* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
* [Stacks Project, Tag 02IJ](https://stacks.math.columbia.edu/tag/02IJ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The common reduction to the affine case for the dimension formula, where `rel` is `≤` or `=`
and `Q` is an extra hypothesis on `S` (`False`, or universal catenarity) that the ring-theoretic
formula `h` may use for the sections over the affine open. -/
private theorem rel_ringKrullDim_stalk_add_trdeg_residueField
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [IsIntegral X] [IsIntegral S] [IsDominant f]
    (rel : WithBot ℕ∞ → WithBot ℕ∞ → Prop) (Q : Prop)
    (hQ : Q → ∀ U : S.Opens, IsAffineOpen U → IsUniversallyCatenary Γ(S, U))
    (h : ∀ (R T : Type u) [CommRing R] [CommRing T] [Algebra R T] [IsNoetherianRing R]
      [Algebra.FiniteType R T] [IsDomain R] [IsDomain T], Function.Injective (algebraMap R T) →
      (Q → IsUniversallyCatenary R) → ∀ (p : Ideal R) (q : Ideal T) [p.IsPrime] [q.IsPrime]
      [q.LiesOver p],
      letI := Ideal.ResidueField.algebraOfLiesOver p q
      rel (q.height + (Cardinal.toNat (Algebra.trdeg p.ResidueField q.ResidueField) : WithBot ℕ∞))
        (p.height + (Cardinal.toNat (Algebra.trdeg R T) : WithBot ℕ∞)))
    (x : X) :
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    letI : Algebra S.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
    rel (ringKrullDim (X.presheaf.stalk x) +
        (Cardinal.toNat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) : WithBot ℕ∞))
      (ringKrullDim (S.presheaf.stalk (f x)) +
        (Cardinal.toNat (Algebra.trdeg S.functionField X.functionField) : WithBot ℕ∞)) := by
  let : Algebra (S.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  let : Algebra S.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
  obtain ⟨U, hU, hsU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show f x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ f ⁻¹ᵁ U from hsU)
  have : Nonempty U := ⟨⟨f x, hsU⟩⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  let : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  have : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).1).symm⟩
  let := Ideal.ResidueField.algebraOfLiesOver (hU.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Algebra.FiniteType Γ(S, U) Γ(X, V) := f.finiteType_appLE hU hV hVU
  have := IsIntegral.component_integral (X := S) U
  have := IsIntegral.component_integral (X := X) V
  have hinj0 := ((tfae_isDominant_of_isIntegral f).out 1 4).mp ‹IsDominant f›
  have hinj : Function.Injective (algebraMap Γ(S, U) Γ(X, V)) :=
    hinj0 ⟨V, hV⟩ ⟨U, hU⟩ inferInstance inferInstance hVU
  rw [hV.ringKrullDim_stalk_eq_height x hxV, hU.ringKrullDim_stalk_eq_height (f x) hsU,
    trdeg_residueField_eq_trdeg_residueField_primeIdealOf f hU hV hVU x hxV,
    trdeg_functionField_eq_trdeg_appLE f hU hV hVU]
  exact h _ _ hinj (fun hQ' => hQ hQ' U hU) _ _

/-- The dimension formula for a dominant morphism `f : X ⟶ S` locally of finite type between
integral schemes over a locally Noetherian base:
`dim 𝒪_{X, x} + trdeg_{κ(f x)} κ(x) ≤ dim 𝒪_{S, f x} + trdeg_{R(S)} R(X)`. -/
@[stacks 02JU "inequality",
  ega "IV 13.3.4" "Inequality dim O_{X_j",
  ega "IV 5.5.6" "partial",
  ega "IV 5.5.8" "more general",
  ega "IV 5.6.5" "(5.6.5.1), special case"]
theorem ringKrullDim_stalk_add_trdeg_residueField_le
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [IsIntegral X] [IsIntegral S] [IsDominant f]
    (x : X) :
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    letI : Algebra S.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
    ringKrullDim (X.presheaf.stalk x) +
        (Cardinal.toNat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) : WithBot ℕ∞)
      ≤ ringKrullDim (S.presheaf.stalk (f x)) +
        (Cardinal.toNat (Algebra.trdeg S.functionField X.functionField) : WithBot ℕ∞) := by
  exact rel_ringKrullDim_stalk_add_trdeg_residueField f _ False (fun h => h.elim)
    (fun _ _ _ _ _ _ _ _ _ hinj _ p q _ _ _ => by
      exact_mod_cast height_add_trdeg_residue_le hinj p q) x

/-- Over a universally catenary base the dimension formula is an equality:
`dim 𝒪_{X, x} + trdeg_{κ(f x)} κ(x) = dim 𝒪_{S, f x} + trdeg_{R(S)} R(X)`. -/
@[stacks 02JU "equality for a universally catenary base",
  ega "IV 5.5.8" "special case",
  ega "IV 5.6.5" "partial"]
theorem ringKrullDim_stalk_add_trdeg_residueField_eq
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [IsIntegral X] [IsIntegral S] [IsDominant f]
    (hS : Scheme.IsUniversallyCatenary S) (x : X) :
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    letI : Algebra S.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
    ringKrullDim (X.presheaf.stalk x) +
        (Cardinal.toNat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) : WithBot ℕ∞)
      = ringKrullDim (S.presheaf.stalk (f x)) +
        (Cardinal.toNat (Algebra.trdeg S.functionField X.functionField) : WithBot ℕ∞) := by
  exact rel_ringKrullDim_stalk_add_trdeg_residueField f _ (Scheme.IsUniversallyCatenary S)
    (fun hS' U hU => fun C _ _ hft => isCatenarySpace_of_isCatenary
      (@isUniversallyCatenary_sections_of_affineOpen S _ hS' ⟨U, hU⟩ C _ _ hft))
    (fun _ _ _ _ _ _ _ _ _ hinj hcat p q _ _ _ => by
      exact_mod_cast height_add_trdeg_residue_eq hinj (hcat hS) p q) x

end AlgebraicGeometry

end
