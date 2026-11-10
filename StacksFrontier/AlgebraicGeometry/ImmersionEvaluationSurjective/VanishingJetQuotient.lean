module

public import StacksFrontier.AlgebraicGeometry.ImmersionEvaluationSurjective.JetFinrank
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SpanningTupleOpen

/-!
# The vanishing part of the target of the evaluation, and the tuples that span it

The evaluation at `x` of a linear system of sections of an invertible module `ℒ` lands in
`ℒ_x/𝔪_x²ℒ_x`, which is `Stacks.ImmersionEvaluationSurjective.evalQuotient`.  The sections that
*vanish* at `x` land in the submodule `𝔪_xℒ_x/𝔪_x²ℒ_x`, one dimension smaller, and it is that
smaller quotient that Step 4 of the proof of [Stacks, Tag 0FH5] asks a `d`-tuple of sections to
generate.  This file builds it, computes its dimension, and instantiates the determinant locus
of `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SpanningTupleOpen` at it.

The quotient is written in the shape of `Ideal.Cotangent`, as `𝔪_xℒ_x` modulo `𝔪_x·(𝔪_xℒ_x)`;
that this second submodule is the right one — that it is exactly the elements of `𝔪_xℒ_x` lying
in `𝔪_x²ℒ_x` — is `Stacks.ImmersionEvaluationSurjective.comap_subtype_maximalSqSmul`.  In that
shape a trivialization of `ℒ` at `x` identifies it with the cotangent space
`𝔪_x/𝔪_x²` of the local ring, by exactly the computation that
`Stacks.StalkJet.jetEquiv` uses one degree up; the dimension is then `dim X` at a closed point of
a smooth scheme over an algebraically closed field, by the regularity of the local ring.

## What consumes this

Step 4 of [Stacks, Tag 0FH5]: with `V ⊆ H⁰(X, ℒ)` the sections vanishing at `x`, the `d`-tuples
of `V` whose images generate `𝔪_xℒ_x/𝔪_x²ℒ_x` form a nonempty open subset of `V^d`.  **The
consumer — the proof of Tag 0FH5, which goes on to intersect the divisors `H_i = Z(s_i)`, apply
Bertini to the intersections and compare zero cycles — is not built here**; what is below is
phrased so as not to depend on it.  The surjectivity of `V → 𝔪_xℒ_x/𝔪_x²ℒ_x` is an input: it is
the conclusion of Step 3 of the same proof.

## Main definitions

* `Stacks.ImmersionEvaluationSurjective.vanishingEvalQuotient`: **the quotient
  `𝔪_xℒ_x/𝔪_x²ℒ_x`**, carrying the vector space structure over the base field `k`, beside
  `Stacks.ImmersionEvaluationSurjective.evalQuotient`.
* `Stacks.ImmersionEvaluationSurjective.maximalIdealEquivMaximalSmul`: a trivialization carries
  `𝔪_x` onto `𝔪_xℒ_x`.
* `Stacks.ImmersionEvaluationSurjective.cotangentSpaceEquivVanishingEvalQuotient`:
  **`𝔪_x/𝔪_x² ≃ 𝔪_xℒ_x/𝔪_x²ℒ_x`**.

## Main results

* `Stacks.ImmersionEvaluationSurjective.comap_subtype_maximalSqSmul`: the submodule divided out
  is the elements of `𝔪_xℒ_x` that lie in `𝔪_x²ℒ_x`, so the quotient really is
  `𝔪_xℒ_x/𝔪_x²ℒ_x`.
* `Stacks.ImmersionEvaluationSurjective.finrank_vanishingEvalQuotient_of_isClosed`:
  **`dim_k 𝔪_xℒ_x/𝔪_x²ℒ_x = n`** at a closed point of a scheme smooth of dimension `n` there
  over an algebraically closed field.  This is the `d` of Step 4 of [Stacks, Tag 0FH5], and it is
  one less than the dimension `n + 1` of `evalQuotient` computed in
  `Stacks.JetFinrank.finrank_evalQuotient_of_isClosed`.
* `Stacks.ImmersionEvaluationSurjective.exists_basis_spanningOpen_vanishingEvalQuotient`:
  **Step 4 of [Stacks, Tag 0FH5]**: the `n`-tuples of a linear system whose images generate
  `𝔪_xℒ_x/𝔪_x²ℒ_x` form a nonempty open subset of the affine space of tuples, cut out by one
  determinant.

## Implementation notes

As with `Stacks.ImmersionEvaluationSurjective.evalQuotient`, the `k`-vector space structure is
restriction of scalars along `Stacks.ImmersionEvaluationSurjective.baseGerm` and so cannot be an
instance on the bare quotient type; the structure morphism is carried in the type of the
definition.

The identification with the cotangent space is `Submodule.Quotient.equiv` of the stalk
isomorphism `Stacks.StalkJet.stalkEquiv` of a trivialization, whose only input is
`Submodule.map_smul''`: a linear isomorphism carries `I • ⊤` to `I • ⊤`.  The dimension of the
cotangent space is read from `IsRegularLocalRing.iff_finrank_cotangentSpace` exactly as in
`Stacks.JetFinrank.finrank_jetQuotient_of_isClosed`, the residue field at a closed point over an
algebraically closed field being the base field.

The dimension computation does not go through
`Stacks.JetFinrank.finrank_evalQuotient_of_isClosed` and subtract one: subtraction would need
the finite dimensionality of `evalQuotient` and the identification of the quotient by the
vanishing part with the residue field, which is more bookkeeping than computing the cotangent
space again.

No `@[stacks]` attribute is attached: this is a step inside the proof of [Stacks, Tag 0FH5], not
the assertion of a tag.

## References

* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace Opposite

universe u

namespace Stacks.ImmersionEvaluationSurjective

open Stacks.ModuleStalk Stacks.StalkJet

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-! ### The quotient `𝔪_xℒ_x/𝔪_x²ℒ_x` -/

/-- **The vanishing part of the target of the evaluation at `x`**: the quotient
`𝔪_xℒ_x/𝔪_x²ℒ_x`, written as `𝔪_xℒ_x` modulo `𝔪_x·(𝔪_xℒ_x)`, and carrying the vector space
structure over the base field `k` of the structure morphism `f`. -/
def vanishingEvalQuotient (_ : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules) (x : X) : Type u :=
  ↥(maximalSmul L x) ⧸
    (maximalIdeal (X.presheaf.stalk x) •
      (⊤ : Submodule (X.presheaf.stalk x) ↥(maximalSmul L x)))

variable (f : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules) (x : X)

/-- The additive group structure on `𝔪_xℒ_x/𝔪_x²ℒ_x`, as a quotient module. -/
instance addCommGroup_vanishingEvalQuotient : AddCommGroup (vanishingEvalQuotient f L x) :=
  inferInstanceAs (AddCommGroup (↥(maximalSmul L x) ⧸
    (maximalIdeal (X.presheaf.stalk x) •
      (⊤ : Submodule (X.presheaf.stalk x) ↥(maximalSmul L x)))))

/-- The `𝒪_{X,x}`-module structure on `𝔪_xℒ_x/𝔪_x²ℒ_x`, as a quotient module. -/
instance module_stalk_vanishingEvalQuotient :
    Module (X.presheaf.stalk x) (vanishingEvalQuotient f L x) :=
  inferInstanceAs (Module (X.presheaf.stalk x) (↥(maximalSmul L x) ⧸
    (maximalIdeal (X.presheaf.stalk x) •
      (⊤ : Submodule (X.presheaf.stalk x) ↥(maximalSmul L x)))))

/-- The `k`-vector space structure on `𝔪_xℒ_x/𝔪_x²ℒ_x`, by restriction of scalars along the
germ `k → 𝒪_{X,x}` of the structure morphism. -/
instance module_base_vanishingEvalQuotient : Module k (vanishingEvalQuotient f L x) :=
  Module.compHom _ (baseGerm f x)

/-- The scalar action of the base field on `𝔪_xℒ_x/𝔪_x²ℒ_x` is the action of `𝒪_{X,x}` through
the structure map. -/
theorem vanishingEvalQuotient_smul_def (c : k) (q : vanishingEvalQuotient f L x) :
    c • q = baseGerm f x c • q :=
  rfl

/-- **The submodule divided out is exactly the part of `𝔪_xℒ_x` lying in `𝔪_x²ℒ_x`**, so
`Stacks.ImmersionEvaluationSurjective.vanishingEvalQuotient` really is `𝔪_xℒ_x/𝔪_x²ℒ_x`.

The inclusion `𝔪_xℒ_x → ℒ_x` is injective, so it suffices to compare images, and the image of
`𝔪_x·(𝔪_xℒ_x)` is `𝔪_x·𝔪_x·ℒ_x = 𝔪_x²ℒ_x`. -/
theorem comap_subtype_maximalSqSmul :
    Submodule.comap (maximalSmul L x).subtype (maximalSqSmul L x) =
      maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x) ↥(maximalSmul L x)) := by
  rw [← Submodule.comap_map_eq_of_injective (Submodule.injective_subtype (maximalSmul L x))
    (maximalIdeal (X.presheaf.stalk x) • (⊤ : Submodule _ ↥(maximalSmul L x)))]
  congr 1
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, maximalSmul,
    show maximalSqSmul L x =
      maximalIdeal (X.presheaf.stalk x) ^ 2 • (⊤ : Submodule _ _) from rfl,
    pow_two, ← Ideal.smul_eq_mul, Submodule.smul_assoc]

/-! ### The identification with the cotangent space of the local ring -/

variable {L x}

/-- **A trivialization of `ℒ` at `x` carries the maximal ideal onto `𝔪_xℒ_x`.**  This is
`Stacks.StalkJet.map_stalkEquiv_smul_top` for the maximal ideal itself, the ideal being `𝔪_x·𝒪`
as a submodule of the local ring. -/
theorem map_stalkEquiv_maximalIdeal {V : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf L.val V) (hx : x ∈ V) :
    Submodule.map (stalkEquiv t hx).toLinearMap
        ((maximalIdeal (X.presheaf.stalk x) :
          Submodule (X.presheaf.stalk x) (X.presheaf.stalk x))) =
      maximalSmul L x := by
  rw [show ((maximalIdeal (X.presheaf.stalk x)) :
      Submodule (X.presheaf.stalk x) (X.presheaf.stalk x)) =
      maximalIdeal (X.presheaf.stalk x) • (⊤ : Submodule _ _) by simp]
  exact map_stalkEquiv_smul_top t hx _

/-- **A trivialization of `ℒ` at `x` identifies `𝔪_x` with `𝔪_xℒ_x`.** -/
def maximalIdealEquivMaximalSmul {V : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf L.val V) (hx : x ∈ V) :
    ↥(maximalIdeal (X.presheaf.stalk x)) ≃ₗ[X.presheaf.stalk x] ↥(maximalSmul L x) :=
  ((stalkEquiv t hx).submoduleMap
      ((maximalIdeal (X.presheaf.stalk x) :
        Submodule (X.presheaf.stalk x) (X.presheaf.stalk x)))).trans
    (LinearEquiv.ofEq _ _ (map_stalkEquiv_maximalIdeal t hx))

/-- **The cotangent space of the local ring is the vanishing part of the target of the
evaluation**: a trivialization at `x` identifies `𝔪_x/𝔪_x²` with `𝔪_xℒ_x/𝔪_x²ℒ_x`.  This is
`Stacks.StalkJet.jetEquiv` one degree down. -/
def cotangentSpaceEquivVanishingEvalQuotient {V : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf L.val V) (hx : x ∈ V)
    (f : X ⟶ Spec (CommRingCat.of k)) :
    CotangentSpace (X.presheaf.stalk x) ≃ₗ[X.presheaf.stalk x] vanishingEvalQuotient f L x :=
  Submodule.Quotient.equiv _ _ (maximalIdealEquivMaximalSmul t hx) (by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])

/-! ### The dimension at a closed point of a smooth scheme -/

variable (L x)

/-- **The vanishing part `𝔪_xℒ_x/𝔪_x²ℒ_x` of the target of the evaluation at a closed point of a
scheme smooth over an algebraically closed field and of dimension `n` there has dimension `n`.**

This is the `d` of Step 4 of the proof of [Stacks, Tag 0FH5]: `d` sections are needed to generate
it.  It is one less than the dimension of the full target `ℒ_x/𝔪_x²ℒ_x`, computed in
`Stacks.JetFinrank.finrank_evalQuotient_of_isClosed`, the missing dimension being the value at
`x` of a section. -/
theorem finrank_vanishingEvalQuotient_of_isClosed [IsAlgClosed k] [Smooth f]
    [Stacks.Ample.IsInvertibleModule X L] {n : ℕ} (hx : IsClosed ({x} : Set X))
    (hdim : topologicalKrullDimAt X x = (n : WithBot ℕ∞)) :
    Module.finrank k (vanishingEvalQuotient f L x) = n := by
  obtain ⟨V, hxV, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at L x
  let : Algebra k (X.presheaf.stalk x) := (baseGerm f x).toAlgebra
  let : IsScalarTower k (X.presheaf.stalk x) (vanishingEvalQuotient f L x) :=
    ⟨fun c r m => mul_smul (baseGerm f x c) r m⟩
  have : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth_over_field f x
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
  have hbij : Function.Bijective (algebraMap k (ResidueField (X.presheaf.stalk x))) :=
    bijective_algebraMap_residueField_of_isClosed f x hx
  have ek : k ≃ₐ[k] ResidueField (X.presheaf.stalk x) :=
    AlgEquiv.ofBijective (Algebra.ofId k _) hbij
  have hres : Module.finrank k (ResidueField (X.presheaf.stalk x)) = 1 := by
    rw [← ek.toLinearEquiv.finrank_eq, Module.finrank_self]
  have : Module.Finite k (ResidueField (X.presheaf.stalk x)) :=
    Module.Finite.equiv ek.toLinearEquiv
  have hcot : Module.finrank k (CotangentSpace (X.presheaf.stalk x)) = n := by
    have hmul := Module.finrank_mul_finrank k (ResidueField (X.presheaf.stalk x))
      (CotangentSpace (X.presheaf.stalk x))
    rw [hres, one_mul] at hmul
    have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace
      (X.presheaf.stalk x)).mp inferInstance
    rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k X f x hx, hdim] at hreg
    rw [← hmul]
    exact_mod_cast hreg
  rw [← hcot]
  exact (((cotangentSpaceEquivVanishingEvalQuotient t hxV f).restrictScalars k).finrank_eq).symm

/-! ### Step 4 of Tag 0FH5 -/

/-- **Step 4 of the proof of [Stacks, Tag 0FH5]**: for a closed point `x` of a scheme `X` smooth
of dimension `n` there over an algebraically closed field `k`, an invertible module `ℒ`, and a
linear system `V = k^ι` whose evaluation onto `𝔪_xℒ_x/𝔪_x²ℒ_x` is surjective, the `n`-tuples of
`V` whose images generate `𝔪_xℒ_x/𝔪_x²ℒ_x` form a **nonempty open** subset of the affine space
`V^n` of tuples — the nonvanishing locus of a single determinant.

The open is `Stacks.SpanningTuple.spanningOpen` for a basis of `𝔪_xℒ_x/𝔪_x²ℒ_x` indexed by
`Fin n`, which exists because that space has dimension `n`
(`Stacks.ImmersionEvaluationSurjective.finrank_vanishingEvalQuotient_of_isClosed`); the second
conjunct identifies its `k`-points as exactly the spanning tuples, so the open does not depend on
the basis chosen. -/
theorem exists_basis_spanningOpen_vanishingEvalQuotient [IsAlgClosed k] [Smooth f]
    [Stacks.Ample.IsInvertibleModule X L] {n : ℕ} (hx : IsClosed ({x} : Set X))
    (hdim : topologicalKrullDimAt X x = (n : WithBot ℕ∞))
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (ev : (ι → k) →ₗ[k] vanishingEvalQuotient f L x) (hev : Function.Surjective ev) :
    ∃ e : Module.Basis (Fin n) k (vanishingEvalQuotient f L x),
      ((Stacks.SpanningTuple.spanningOpen e ev :
            (Stacks.SpanningTuple.tupleSpace k ι n).Opens) :
          Set (Stacks.SpanningTuple.tupleSpace k ι n)).Nonempty ∧
        ∀ (a : Fin n × ι → k) (p : Spec (CommRingCat.of k)),
          Stacks.SpanningTuple.tuplePoint a p ∈ Stacks.SpanningTuple.spanningOpen e ev ↔
            Submodule.span k (Set.range fun s => ev (Function.curry a s)) = ⊤ := by
  have : Module.Finite k (vanishingEvalQuotient f L x) := Module.Finite.of_surjective ev hev
  refine ⟨Module.finBasisOfFinrankEq k (vanishingEvalQuotient f L x)
    (finrank_vanishingEvalQuotient_of_isClosed f L x hx hdim), ?_, fun a p => ?_⟩
  · exact Stacks.SpanningTuple.nonempty_spanningOpen _ hev
  · exact Stacks.SpanningTuple.mem_spanningOpen_iff _ ev a p

end Stacks.ImmersionEvaluationSurjective

end
