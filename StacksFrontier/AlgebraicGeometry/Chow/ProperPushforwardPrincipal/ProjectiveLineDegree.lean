module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Inversion
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineInfinity
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLinePoints

/-!
# The degree of a principal divisor on the projective line

Stacks 02RU for the projective line: for a nonzero rational function `g` on `ℙ¹_k`,

  `∑_{x ∈ ℙ¹ closed} ord_x(g) · [κ(x) : k] = 0`.

The sum is the one of `Stacks.Chow.principalDivisorDegree` for the structure morphism
`ℙ¹_k ⟶ Spec k`, and the identity is the purely algebraic
`Stacks.Chow.finsum_ordAt_mul_natDegree_add_ordAtInfty_eq_zero` read through the geometry of
`ℙ¹_k`: the points of `ℙ¹_k` are the generic point, the closed points of the first chart — indexed
by the monic irreducible polynomials, each of residue degree its own degree — and the point at
infinity, of residue degree one; the order of vanishing at the generic point is zero, at the
closed point cut out by `p` it is `Stacks.Chow.ordAt p`, and at infinity it is
`Stacks.Chow.ordAtInfty`.

## Main results

* `AlgebraicGeometry.projectiveLineInfinity_notMem_range_projectiveLineXChart` — the point at
  infinity does not lie in the first chart, because the coordinate has a pole there and no zero
  or pole of negative order inside the chart.
* `Stacks.Chow.principalDivisorDegree_projectiveLine_eq_zero` — **Stacks 02RU for the projective
  line.**

## Implementation notes

That infinity is not in the first chart is proved by a function-theoretic separation rather than
by unfolding the gluing datum: the coordinate of the first chart has order `-1` at infinity, by
`AlgebraicGeometry.ord_projectiveLine_infinity`, while at every point of the first chart its order
is the multiplicity of a monic irreducible in a polynomial, hence nonnegative.

The sum over `ℙ¹_k` is re-indexed in two steps. The decomposition of `ℙ¹_k` into the first chart
and the point at infinity (`AlgebraicGeometry.mem_range_projectiveLineXChart_or_eq_infinity`)
splits it as a sum over `Spec k[X]` plus the term at infinity, using that the first chart is
injective on points. The sum over `Spec k[X]` is then transported to a sum over `k[X]` along
`AlgebraicGeometry.bijOn_affineLineGenerator`, after discarding the generic point on one side and
the polynomials that are not monic irreducible on the other, where both summands vanish.

No `@[stacks 02RU]` attribute is placed here. Stacks 02RU is the statement for an arbitrary
proper integral curve over a field, of which this is the case of the projective line; it carries
its tag in
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.NormalizationDescent`. The
reduction of the general case to this one is
`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_properDominant`, which needs a
proper dominant morphism from the curve to `ℙ¹_k`; that morphism is constructed in
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ToProjectiveLine`.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace UniqueFactorizationMonoid

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The projective line over a field is a compact space, being quasi-compact over the spectrum of
the field. -/
instance projectiveLine_compactSpace : CompactSpace (projectiveLine k) :=
  QuasiCompact.compactSpace_of_compactSpace (projectiveLine k ↘ Spec (.of k))

/-- A rational function on `ℙ¹_k` has order zero at the image of the generic point of the first
chart. -/
private theorem ord_projectiveLine_xChart_eq_zero_of_asIdeal_eq_bot
    (g : (projectiveLine k).functionField) (y : Spec (.of (Polynomial k))) (hyb : y.asIdeal = ⊥) :
    (projectiveLine k).ord g ((projectiveLineXChart k).base y) = 0 := by
  rw [eq_genericPoint_of_asIdeal_eq_bot y hyb, projectiveLineXChart_genericPoint_eq,
    ord_projectiveLine_genericPoint_eq_zero]

/-- **The point at infinity does not lie in the first chart.** The coordinate of the first chart
has a simple pole at infinity, while inside the chart its order of vanishing is the multiplicity
of a monic irreducible polynomial in it, hence nonnegative. -/
theorem projectiveLineInfinity_notMem_range_projectiveLineXChart :
    projectiveLineInfinity k ∉ Set.range (projectiveLineXChart k).base := by
  classical
  set g₀ : (projectiveLine k).functionField := (projectiveLineFunctionFieldEquiv k).symm
    (algebraMap (Polynomial k) (RatFunc k) Polynomial.X) with hg₀
  have hg₀e : projectiveLineFunctionFieldEquiv k g₀ =
      algebraMap (Polynomial k) (RatFunc k) Polynomial.X := by
    rw [hg₀]
    simp
  have hinf : (projectiveLine k).ord g₀ (projectiveLineInfinity k) = -1 := by
    rw [ord_projectiveLine_infinity k g₀, hg₀e, Stacks.Chow.ordAtInfty,
      RatFunc.intDegree_polynomial]
    simp
  rintro ⟨y, hy⟩
  have hnonneg : 0 ≤ (projectiveLine k).ord g₀ ((projectiveLineXChart k).base y) := by
    by_cases hyb : y.asIdeal = ⊥
    · rw [ord_projectiveLine_xChart_eq_zero_of_asIdeal_eq_bot k g₀ y hyb]
    · obtain ⟨hpm, hpi, hspan⟩ := affineLineGenerator_spec y hyb
      rw [ord_projectiveLine_xChart_eq_ordAt k hpi hpm y hspan g₀, hg₀e, Stacks.Chow.ordAt,
        RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
      simp
  rw [hy, hinf] at hnonneg
  exact absurd hnonneg (by decide)

/-- A finitely supported sum over `ℙ¹_k` is the sum over the first chart plus the term at
infinity. -/
private theorem finsum_projectiveLine_eq_finsum_xChart_add {M : Type*} [AddCommMonoid M]
    (f : projectiveLine k → M) (hf : (Function.support f).Finite) :
    ∑ᶠ x, f x = (∑ᶠ y : Spec (.of (Polynomial k)), f ((projectiveLineXChart k).base y)) +
      f (projectiveLineInfinity k) := by
  have huniv : (Set.univ : Set (projectiveLine k)) =
      Set.range (projectiveLineXChart k).base ∪ {projectiveLineInfinity k} :=
    (Set.eq_univ_of_forall fun x =>
      (mem_range_projectiveLineXChart_or_eq_infinity x).imp_right (fun h => h)).symm
  calc ∑ᶠ x, f x
      = ∑ᶠ x ∈ Set.range (projectiveLineXChart k).base ∪ {projectiveLineInfinity k}, f x := by
        rw [← huniv, finsum_mem_univ]
    _ = (∑ᶠ x ∈ Set.range (projectiveLineXChart k).base, f x) +
          ∑ᶠ x ∈ ({projectiveLineInfinity k} : Set (projectiveLine k)), f x :=
        finsum_mem_union' (Set.disjoint_singleton_right.2
          (projectiveLineInfinity_notMem_range_projectiveLineXChart k))
          (hf.inter_of_right _) ((Set.finite_singleton _).inter_of_left _)
    _ = _ := by rw [finsum_mem_range projectiveLineXChart_base_injective, finsum_mem_singleton]

end AlgebraicGeometry

namespace Stacks.Chow

variable (k : Type u) [Field k]

/-- A finitely supported sum over a type is the sum over any set containing the support. -/
private theorem finsum_eq_finsum_mem_of_ne_zero_imp {α M : Type*} [AddCommMonoid M]
    {f : α → M} {s : Set α} (h : ∀ x, f x ≠ 0 → x ∈ s) : ∑ᶠ x, f x = ∑ᶠ x ∈ s, f x := by
  rw [← finsum_mem_univ]
  exact finsum_mem_inter_support_eq' _ _ _ fun x hx => ⟨fun _ => h x hx, fun _ => trivial⟩

/-- The part of the degree of a principal divisor on `ℙ¹_k` coming from the first chart is the sum
of `ordAt p g · deg p` over the polynomials `p`. -/
private theorem finsum_xChart_ord_mul_residueDegree_eq [DecidableEq k]
    (g : (projectiveLine k).functionField) :
    ∑ᶠ y : Spec (.of (Polynomial k)), (projectiveLine k).ord g ((projectiveLineXChart k).base y) *
        ((projectiveLine k ↘ Spec (.of k)).residueDegree ((projectiveLineXChart k).base y) : ℤ) =
      ∑ᶠ p : Polynomial k, ordAt p (projectiveLineFunctionFieldEquiv k g) * (p.natDegree : ℤ) := by
  classical
  have hval : ∀ y ∈ {y : Spec (.of (Polynomial k)) | y.asIdeal ≠ ⊥},
      (projectiveLine k).ord g ((projectiveLineXChart k).base y) *
        ((projectiveLine k ↘ Spec (.of k)).residueDegree ((projectiveLineXChart k).base y) : ℤ) =
      ordAt (affineLineGenerator y) (projectiveLineFunctionFieldEquiv k g) *
        ((affineLineGenerator y).natDegree : ℤ) := by
    intro y hy
    obtain ⟨hpm, hpi, hspan⟩ := affineLineGenerator_spec y hy
    rw [ord_projectiveLine_xChart_eq_ordAt k hpi hpm y hspan g,
      residueDegree_projectiveLine_xChart k y,
      residueDegree_projectiveLineAffineStructureMorphism_eq_natDegree k hpi y hspan]
  rw [finsum_eq_finsum_mem_of_ne_zero_imp (s := {y : Spec (.of (Polynomial k)) | y.asIdeal ≠ ⊥}),
    finsum_eq_finsum_mem_of_ne_zero_imp (s := {p : Polynomial k | p.Monic ∧ Irreducible p})]
  · exact finsum_mem_eq_of_bijOn (affineLineGenerator (k := k)) bijOn_affineLineGenerator hval
  · intro p hp
    constructor
    · by_contra hpm
      exact hp (by rw [ordAt_eq_zero_of_not_monic hpm, zero_mul])
    · by_contra hpi
      exact hp (by rw [ordAt_eq_zero_of_not_irreducible hpi, zero_mul])
  · intro y hy
    by_contra hyb
    exact hy (by rw [ord_projectiveLine_xChart_eq_zero_of_asIdeal_eq_bot k g y (not_not.1 hyb),
      zero_mul])
/-- **Stacks 02RU for the projective line.** The degree of a principal divisor on `ℙ¹_k`
vanishes: for a nonzero rational function `g`,

  `∑_{x ∈ ℙ¹} ord_x(g) · [κ(x) : k] = 0`.

The sum runs over the generic point, where the order of vanishing is zero, the closed points of
the first chart, indexed by the monic irreducible polynomials `p` with order `ordAt p` and residue
degree `deg p`, and the point at infinity, with order `ordAtInfty` and residue degree one. So it
is the sum of `Stacks.Chow.finsum_ordAt_mul_natDegree_add_ordAtInfty_eq_zero`. -/
theorem principalDivisorDegree_projectiveLine_eq_zero
    (g : (projectiveLine k).functionField) (hg : g ≠ 0) :
    principalDivisorDegree (projectiveLine k ↘ Spec (.of k)) g = 0 := by
  classical
  have hfin : (Function.support fun x : projectiveLine k => (projectiveLine k).ord g x *
      ((projectiveLine k ↘ Spec (.of k)).residueDegree x : ℤ)).Finite :=
    (finite_support_ord g).subset fun x hx => (mul_ne_zero_iff.mp hx).1
  calc principalDivisorDegree (projectiveLine k ↘ Spec (.of k)) g
      = ∑ᶠ x : projectiveLine k, (projectiveLine k).ord g x *
          ((projectiveLine k ↘ Spec (.of k)).residueDegree x : ℤ) := rfl
    _ = (∑ᶠ p : Polynomial k, ordAt p (projectiveLineFunctionFieldEquiv k g) * (p.natDegree : ℤ)) +
          ordAtInfty (projectiveLineFunctionFieldEquiv k g) := by
      rw [finsum_projectiveLine_eq_finsum_xChart_add k _ hfin,
        finsum_xChart_ord_mul_residueDegree_eq k g, ord_projectiveLine_infinity k g,
        residueDegree_projectiveLine_infinity k]
      simp
    _ = 0 := finsum_ordAt_mul_natDegree_add_ordAtInfty_eq_zero _
          ((map_ne_zero_iff _ (projectiveLineFunctionFieldEquiv k).injective).2 hg)

end Stacks.Chow

end

end
