module

public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DimensionDrop
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree of an effective Cartier divisor on a proper curve

Let `k` be a field and let `X` be a proper scheme of dimension at most one over `k`. An effective
Cartier divisor `D` on `X` is nowhere dense, so its underlying closed subscheme has dimension at
most zero and is therefore finite over `k`. Being finite over a field, it is finite locally free,
and its degree is the dimension of its ring of global sections.

## Main results

* `AlgebraicGeometry.isFinite_divisorSubscheme`: the divisor is finite over the base field.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_divisorSubscheme`: it is finite locally free of
  rank `dim_k Γ(D, 𝒪_D)`, which is its degree.
* `AlgebraicGeometry.topologicalKrullDim_divisorSubscheme_le_zero`: the divisor has dimension at
  most zero.

Together these are the first two assertions of **Stacks Project, Tag 0AYY**.

## References

* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
* [Stacks Project, Tag 056N](https://stacks.math.columbia.edu/tag/056N)
* [Stacks Project, Tag 06LH](https://stacks.math.columbia.edu/tag/06LH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A dimension in `WithBot ℕ∞` which is less than one is at most zero. -/
lemma dim_le_zero_of_lt_one {d : WithBot ℕ∞} (hd : d < 1) : d ≤ 0 := by
  cases d with
  | bot => simp
  | coe d =>
    have h : d < (1 : ℕ∞) := WithBot.coe_lt_coe.mp hd
    rw [Order.lt_one_iff] at h
    subst h
    simp

/-- The closed subscheme underlying an effective Cartier divisor on a scheme of dimension at
most one has dimension at most zero. -/
theorem topologicalKrullDim_divisorSubscheme_le_zero {X : Scheme.{u}}
    (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    topologicalKrullDim D.subscheme ≤ 0 := by
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x ↦ ?_
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  have hX : topologicalKrullDimAt X (D.subschemeι x) ≤ 1 :=
    (topologicalKrullDimAt_le_topologicalKrullDim _).trans hdim
  have hfin : topologicalKrullDimAt X (D.subschemeι x) < ⊤ :=
    lt_of_le_of_lt hX (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top 1))
  exact dim_le_zero_of_lt_one
    (lt_of_lt_of_le (topologicalKrullDimAt_subscheme_lt D inferInstance x hfin) hX)

/-- The ring of global sections of a scheme finite over a field is a finite-dimensional vector
space over that field. -/
lemma finite_globalSections {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsFinite g] :
    letI : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    Module.Finite k Γ(Y, ⊤) := by
  have hΓ : ((Scheme.ΓSpecIso (.of k)).inv).hom.Finite :=
    RingHom.Finite.of_surjective _ ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).2
  exact RingHom.Finite.comp (Scheme.Hom.finite_appTop g) hΓ

/-- **The first assertion of Stacks Project, Tag 0AYY.** An effective Cartier divisor on a proper
scheme of dimension at most one over a field is finite over that field. -/
theorem isFinite_divisorSubscheme (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    IsFinite (D.subschemeι ≫ f) := by
  have hdimD : topologicalKrullDim D.subscheme ≤ 0 :=
    topologicalKrullDim_divisorSubscheme_le_zero hdim D
  cases isEmpty_or_nonempty D.subscheme with
  | inl h =>
    let : IsEmpty D.subscheme := h
    infer_instance
  | inr h =>
    have hdimD0 : topologicalKrullDim D.subscheme = 0 := by
      refine le_antisymm hdimD ?_
      obtain ⟨x⟩ := h
      let : Nonempty (TopologicalSpace.IrreducibleCloseds D.subscheme) :=
        ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
      exact Order.krullDim_nonneg
    exact isFinite_of_finiteType_of_dimension_zero k (D.subschemeι ≫ f) hdimD0

/-- **The second assertion of Stacks Project, Tag 0AYY.** An effective Cartier divisor on a
proper scheme of dimension at most one over a field is finite locally free over that field, of
degree the dimension of its ring of global sections. -/
theorem isFiniteLocallyFreeOfRank_divisorSubscheme
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ f)
      (Module.finrank k Γ(D.subscheme, ⊤)) := by
  let : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  let : IsFinite (D.subschemeι ≫ f) := isFinite_divisorSubscheme k f hdim D
  exact (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_sections_eq (D.subschemeι ≫ f)
    (Module.finrank k Γ(D.subscheme, ⊤))).mpr
      ⟨inferInstance, finite_globalSections (D.subschemeι ≫ f), rfl⟩

end AlgebraicGeometry

end
