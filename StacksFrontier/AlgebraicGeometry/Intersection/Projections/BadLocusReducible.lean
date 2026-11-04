module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemma
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.GenericProjection
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceQuotientMap
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.TangencyLocus
public import StacksFrontier.RingTheory.Spectrum.Prime.CodimensionHeight

/-!
# The bad locus of Tag 0B1S is not irreducible

Let `X, Y` be closed subvarieties of `𝐏(V)` which intersect properly, with `X ≠ 𝐏(V)` and
`X ∩ Y ≠ ∅`, and let `𝐏 = 𝐏((End V)ᵛ)` be the parameter space. The bad locus of
`AlgebraicGeometry.ProjectiveSpaceOfModule.badParameterLocus` collects the classes `[g]` having a
representative that violates one of the two clauses of Tag 0B1S. A statement of that tag can ask
for an *irreducible* closed subset `B ⊆ 𝐏` of codimension at least two whose closed points are
exactly the bad ones. This file shows that no such `B` exists for the pair of distinct
hyperplanes of `𝐏²`, so a statement so phrased is vacuous there; the shape the tag is formalized
in is accordingly the pointwise one of
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_closedPoint_line_isGood_of_codimension`,
which asks for a closed `B` with `∀ x ∈ B, 2 ≤ codimension (closureSingleton x)`.

Take `dim_k V = 3` and two linearly independent vectors `a, b` of `V`, and let `X` and `Y` be the
lines of `𝐏²` cut out by `a` and by `b`. They intersect properly in a point, `X ≠ 𝐏²` and
`X ∩ Y ≠ ∅`. The classes of the endomorphisms `g` with `g b ∈ k·a` form a linear subspace `C` of
`𝐏` of codimension two, because `g ↦ g b` is a surjection `End V → V` and `k·a` has corank two.
Every closed point of `C` is bad: for a representative `g` either `X` leaves `U(g)`, and clause
(1) fails, or else `r_g(X)` lies inside `Y` — the preimage of the equation of `Y` under `r_g` is
the equation of `g b`, hence a multiple of the equation of `X` — and then
`dim (r_g(X) ∩ Y) + dim 𝐏² = dim r_g(X) + 2` exceeds `dim r_g(X) + dim Y = dim r_g(X) + 1`, so
clause (2) fails. The class of the rank-one endomorphism `u ↦ ψ(u)·b` with `ψ b = 1` is bad too,
clause (1) failing at the point cut out by any functional killing both `a` and `b`, and it is
*not* in `C`, since it sends `b` to `b ∉ k·a`.

An irreducible closed `B` whose closed points are the bad ones would therefore contain `C`,
because the closed points of a linear subspace are dense in it, and would contain that extra
class, so `C ⊊ B`; strict inclusion of irreducible closed subsets drops the codimension, so
`codim C ≥ codim B + 1 ≥ 3`. But `dim C + codim C ≤ dim 𝐏 = 8` and `dim C = 6`, so
`codim C ≤ 2`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.evalAtVector`: the evaluation `g ↦ g v` as a linear
  map `End V → V`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.hyperplaneTransportSubmodule`: the degree-one
  equations on `𝐏` cutting out the classes of the `g` with `g b ∈ k·a`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.isIrreducible_linearSubspace`: a projective linear
  subspace is irreducible, being the image of the projective space of the quotient.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_singleton_mem_linearSubspace_notMem`:
  the closed points of a projective linear subspace are dense in it.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_linearSubspace_endProjection_iff`: a point of
  `U(g)` is carried by `r_g` into the linear subspace cut out by `W` exactly when it lies on the
  linear subspace cut out by `g(W)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.not_exists_irreducible_badParameterLocus`: for two
  distinct lines of `𝐏²` there is no irreducible closed subset of codimension at least two whose
  closed points are exactly the bad classes.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_intersectProperly_not_exists_irreducible_bad`:
  the same, packaged with the verification that the pair satisfies the remaining hypotheses of
  Tag 0B1S.

## Implementation notes

The codimension bound in the last step is the only place where a bound on a codimension from
*above* is needed, and `AlgebraicGeometry.topologicalKrullDim_add_codimension_le` supplies it:
dimension plus codimension is at most the dimension of the ambient space, in any topological
space.

Density of the closed points is proved through
`AlgebraicGeometry.ProjectiveSpaceOfModule.quotientMap`, the closed immersion
`𝐏(V ⧸ W) ⟶ 𝐏(V)` whose image is the linear subspace: a proper closed subset of `𝐏(V ⧸ W)`
misses a closed point by
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_linearFunctionalPoint_notMem_of_ne_univ`, and a
closed immersion carries closed points to closed points.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### Projective linear subspaces -/

/-- In `WithBot ℕ∞` a quantity that is finite — bounded below by zero and above by a natural
number — cannot satisfy `A + 2 ≤ A + 1`. -/
private theorem not_add_two_le_add_one {A : WithBot ℕ∞} {n : ℕ}
    (h0 : (0 : WithBot ℕ∞) ≤ A) (hn : A ≤ (n : WithBot ℕ∞)) :
    ¬ (A + ((2 : ℕ) : WithBot ℕ∞) ≤ A + 1) := by
  intro hle
  obtain ⟨x, hx⟩ : ∃ x : ℕ∞, (x : WithBot ℕ∞) = A :=
    WithBot.ne_bot_iff_exists.mp fun h => by rw [h] at h0; simp at h0
  have hxne : x ≠ ⊤ := by
    rintro rfl
    rw [← hx] at hn
    exact (ENat.coe_ne_top n) (top_le_iff.mp (WithBot.coe_le_coe.mp hn))
  rw [← hx, show ((2 : ℕ) : WithBot ℕ∞) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) from rfl,
    show (1 : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) from rfl,
    ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe] at hle
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hxne
  rw [← hm] at hle
  have hfin : (m : ℕ) + 2 ≤ m + 1 := by exact_mod_cast hle
  omega


/-- Two sets of degree-one equations cut out the intersection of the subspaces they cut out. -/
public theorem linearSubspace_sup (W W' : Submodule k V) :
    linearSubspace k V (W ⊔ W') = linearSubspace k V W ∩ linearSubspace k V W' := by
  ext q
  rw [Set.mem_inter_iff, mem_linearSubspace_iff, mem_linearSubspace_iff, mem_linearSubspace_iff,
    sup_le_iff]

/-- **A proper subspace is killed by a nonzero functional.** -/
public theorem exists_ne_zero_le_ker_of_ne_top {W : Submodule k V} (hW : W ≠ ⊤) :
    ∃ (f : Module.Dual k V) (_ : f ≠ 0), W ≤ LinearMap.ker f := by
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (p := W) (lt_top_iff_ne_top.mpr hW) inferInstance
  refine ⟨f, hf, fun v hv => LinearMap.mem_ker.mpr ?_⟩
  have hmem : f v ∈ W.map f := ⟨v, hv, rfl⟩
  rwa [hmap, Submodule.mem_bot] at hmem

/-- The point cut out by a functional lies on the linear subspace cut out by `W` exactly when the
functional kills `W`. -/
public theorem mem_linearSubspace_linearFunctionalPoint_iff (W : Submodule k V)
    (f : Module.Dual k V) (hf : f ≠ 0) :
    linearFunctionalPoint k V f hf ∈ linearSubspace k V W ↔ W ≤ LinearMap.ker f := by
  rw [mem_linearSubspace_iff, pointSubmodule_linearFunctionalPoint]

/-- **A proper system of degree-one equations has a solution.** -/
public theorem linearSubspace_nonempty {W : Submodule k V} (hW : W ≠ ⊤) :
    (linearSubspace k V W).Nonempty := by
  obtain ⟨f, hf, hle⟩ := exists_ne_zero_le_ker_of_ne_top k V hW
  exact ⟨_, (mem_linearSubspace_linearFunctionalPoint_iff k V W f hf).mpr hle⟩

/-- **A projective linear subspace is irreducible**: it is the image of the projective space of
the quotient under the closed immersion
`AlgebraicGeometry.ProjectiveSpaceOfModule.quotientMap`, and that projective space is
irreducible. -/
public theorem isIrreducible_linearSubspace [FiniteDimensional k V] {W : Submodule k V}
    (hW : W ≠ ⊤) : IsIrreducible (linearSubspace k V W) := by
  have hnt : Nontrivial (V ⧸ W) := Submodule.Quotient.nontrivial_iff.mpr hW
  rw [← range_quotientMap k V W, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ (projectiveSpaceOfModule k (V ⧸ W))).image _
    (quotientMap k V W).isClosedEmbedding.continuous.continuousOn

/-- A projective linear subspace, as an irreducible closed subset. -/
public def linearSubvariety [FiniteDimensional k V] {W : Submodule k V} (hW : W ≠ ⊤) :
    IrreducibleCloseds (projectiveSpaceOfModule k V) where
  carrier := linearSubspace k V W
  isIrreducible' := isIrreducible_linearSubspace k V hW
  isClosed' := isClosed_linearSubspace k V W

/-- The underlying set of `linearSubvariety k V hW` is `linearSubspace k V W`. -/
@[simp]
public theorem coe_linearSubvariety [FiniteDimensional k V] {W : Submodule k V} (hW : W ≠ ⊤) :
    (linearSubvariety k V hW : Set (projectiveSpaceOfModule k V)) = linearSubspace k V W := rfl

/-- **The closed points of a projective linear subspace are dense in it.** A closed subset of
`𝐏(V)` not containing the whole subspace misses one of its closed points: pull the closed subset
back along the closed immersion `𝐏(V ⧸ W) ⟶ 𝐏(V)`, where it is proper and therefore misses a
point cut out by a functional, and push that point forward. -/
public theorem exists_isClosed_singleton_mem_linearSubspace_notMem [IsAlgClosed k]
    [FiniteDimensional k V] {W : Submodule k V} (hW : W ≠ ⊤)
    {D : Set (projectiveSpaceOfModule k V)} (hD : IsClosed D)
    (hsub : ¬ linearSubspace k V W ⊆ D) :
    ∃ q : projectiveSpaceOfModule k V, IsClosed ({q} : Set (projectiveSpaceOfModule k V)) ∧
      q ∈ linearSubspace k V W ∧ q ∉ D := by
  have hnt : Nontrivial (V ⧸ W) := Submodule.Quotient.nontrivial_iff.mpr hW
  obtain ⟨c, hcW, hcD⟩ := Set.not_subset.mp hsub
  rw [← range_quotientMap k V W] at hcW
  obtain ⟨y₀, rfl⟩ := hcW
  have hDpre : IsClosed ((quotientMap k V W).base ⁻¹' D) :=
    hD.preimage (quotientMap k V W).isClosedEmbedding.continuous
  have hDne : ((quotientMap k V W).base ⁻¹' D) ≠ Set.univ := by
    intro hall
    exact hcD (hall.symm ▸ Set.mem_univ y₀ : y₀ ∈ (quotientMap k V W).base ⁻¹' D)
  obtain ⟨ψ, hψ, hψD⟩ :=
    exists_linearFunctionalPoint_notMem_of_ne_univ k (V ⧸ W) hDpre hDne
  refine ⟨(quotientMap k V W).base (linearFunctionalPoint k (V ⧸ W) ψ hψ), ?_, ?_, hψD⟩
  · exact isClosed_singleton_base (quotientMap k V W) _
      (linearFunctionalPoint_isClosed k (V ⧸ W) ψ hψ)
  · rw [← range_quotientMap k V W]
    exact ⟨_, rfl⟩

/-! ### The image of a projective transformation of a linear subspace -/

/-- **`r_g` pulls degree-one equations back along `g`.** A point of `U(g)` is carried by `r_g`
into the linear subspace cut out by `W` exactly when it lies on the linear subspace cut out by
the image `g(W)`: the equation `v` of the target pulls back to the equation `g v`. -/
public theorem mem_linearSubspace_endProjection_iff (g : V →ₗ[k] V) (W : Submodule k V)
    (y : (endDomain k V g).toScheme) :
    endProjection k V g y ∈ linearSubspace k V W ↔
      (y.val : projectiveSpaceOfModule k V) ∈ linearSubspace k V (W.map g) := by
  rw [mem_linearSubspace_iff, mem_linearSubspace_iff]
  constructor
  · intro h u hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [mem_pointSubmodule_iff]
    have h1 : SymmetricAlgebra.ι k V v ∈ SymPow.symmetricPower 1 k V := by simp
    have hv' := (mem_endProjection_iff k V g y Nat.one_pos h1).mp
      ((mem_pointSubmodule_iff k V _ v).mp (h hv))
    rwa [SymPow.symAlgMap_ι] at hv'
  · intro h v hv
    rw [mem_pointSubmodule_iff]
    have h1 : SymmetricAlgebra.ι k V v ∈ SymPow.symmetricPower 1 k V := by simp
    refine (mem_endProjection_iff k V g y Nat.one_pos h1).mpr ?_
    rw [SymPow.symAlgMap_ι]
    exact (mem_pointSubmodule_iff k V _ (g v)).mp (h ⟨v, hv, rfl⟩)

/-- **`r_g` carries a subset into a linear subspace once the pulled-back equations hold on it.**
-/
public theorem endProjectionImage_subset_linearSubspace (g : V →ₗ[k] V) (W : Submodule k V)
    (S : Set (projectiveSpaceOfModule k V)) (hS : S ⊆ linearSubspace k V (W.map g)) :
    endProjectionImage k V g S ⊆ linearSubspace k V W := by
  rintro _ ⟨y, hy, rfl⟩
  exact (mem_linearSubspace_endProjection_iff k V g W y).mpr (hS hy)

/-! ### Reading a linear subspace of the parameter space on a representative -/

/-- The evaluation of an endomorphism at a vector, as a linear map `End V → V`. -/
public def evalAtVector (v : V) : (V →ₗ[k] V) →ₗ[k] V where
  toFun g := g v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `evalAtVector k V v` sends an endomorphism `g` to `g v`. -/
@[simp]
public theorem evalAtVector_apply (v : V) (g : V →ₗ[k] V) : evalAtVector k V v g = g v := rfl

/-- **Evaluation at a nonzero vector is surjective on endomorphisms**: a rank-one endomorphism
realises any prescribed value. -/
public theorem surjective_evalAtVector {v : V} (hv : v ≠ 0) :
    Function.Surjective (evalAtVector k V v) := by
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one k hv
  exact fun w => ⟨ψ.smulRight w, by simp [LinearMap.smulRight_apply, hψ]⟩

/-- A vector outside the span of a vector is nonzero. -/
private theorem ne_zero_of_notMem_span_singleton {a b : V} (hb : b ∉ Submodule.span k {a}) :
    b ≠ 0 := fun h => hb (h ▸ Submodule.zero_mem _)

/-- A submodule whose finrank differs from that of the ambient module is proper. -/
private theorem ne_top_of_finrank_eq_of_ne {M : Type*} [AddCommGroup M] [Module k M]
    {W : Submodule k M} {m : ℕ} (hW : Module.finrank k W = m) (hm : m ≠ Module.finrank k M) :
    W ≠ ⊤ := by
  rintro rfl
  exact hm (hW.symm.trans (finrank_top k M))

variable [IsAlgClosed k] [FiniteDimensional k V]

/-- A representative of a closed point of the parameter space is a unit multiple of the chosen
representative of its class. -/
private theorem exists_units_smul_eq_rep {p : ClosedPoints k (ParameterModule k V)}
    {g : V →ₗ[k] V} (hg : RepresentsParameterPoint k V p g) :
    ∃ c : kˣ, (c : k) • g = (dualEndClosedPointsEquiv k V p).rep := by
  obtain ⟨hg0, hgeq⟩ := hg
  have hmk : Projectivization.mk k (dualEndClosedPointsEquiv k V p).rep
        (dualEndClosedPointsEquiv k V p).rep_nonzero =
      Projectivization.mk k g hg0 := by
    rw [Projectivization.mk_rep, hgeq]
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff k _ g
    (dualEndClosedPointsEquiv k V p).rep_nonzero hg0).mp hmk
  exact ⟨c, by rw [← hc, Units.smul_def]⟩

/-- **A linear subspace of the parameter space, read on a representative.** A closed point of
`𝐏 = 𝐏((End V)ᵛ)` lies on the linear subspace cut out by a submodule `L` of degree-one forms
exactly when every form of `L` kills any representative endomorphism of that point. -/
public theorem mem_linearSubspace_iff_forall_apply_eq_zero
    {p : ClosedPoints k (ParameterModule k V)} {g : V →ₗ[k] V}
    (hg : RepresentsParameterPoint k V p g) (L : Submodule k (ParameterModule k V)) :
    (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
        linearSubspace k (ParameterModule k V) L ↔ ∀ φ ∈ L, φ g = 0 := by
  obtain ⟨c, hc⟩ := exists_units_smul_eq_rep k V hg
  have hiff : ∀ φ : ParameterModule k V,
      φ ((dualEndClosedPointsEquiv k V p).rep) = 0 ↔ φ g = 0 := by
    intro φ
    rw [← hc, map_smul, smul_eq_mul, mul_eq_zero]
    exact or_iff_right (Units.ne_zero c)
  rw [mem_linearSubspace_iff]
  refine ⟨fun hle φ hφ => (hiff φ).mp
    ((dualEndClosedPointsEquiv_apply k V p φ).mp (hle hφ)), fun hall φ hφ => ?_⟩
  exact (dualEndClosedPointsEquiv_apply k V p φ).mpr ((hiff φ).mpr (hall φ hφ))

/-! ### The classes carrying one line of `𝐏²` into another -/

/-- **The degree-one equations on the parameter space cutting out the classes of the
endomorphisms carrying `b` into the line `k·a`.** Pulling the functionals killing `a` back along
the evaluation `g ↦ g b` gives forms on `End V`, that is degree-one forms on `𝐏`. -/
public def hyperplaneTransportSubmodule (a b : V) : Submodule k (ParameterModule k V) :=
  Submodule.map (evalAtVector k V b).dualMap (Submodule.span k {a}).dualAnnihilator

omit [IsAlgClosed k] in
/-- **What those equations say.** Every one of them kills `g` exactly when `g b` lies on the line
spanned by `a`. -/
public theorem forall_apply_eq_zero_hyperplaneTransportSubmodule_iff (a b : V)
    (g : V →ₗ[k] V) :
    (∀ φ ∈ hyperplaneTransportSubmodule k V a b, φ g = 0) ↔ g b ∈ Submodule.span k {a} := by
  constructor
  · intro hall
    by_contra hnot
    obtain ⟨ψ, hψ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
      (p := Submodule.span k {a}) hnot inferInstance
    refine hψ ?_
    have hmem : ψ ∈ (Submodule.span k {a}).dualAnnihilator := by
      refine (Submodule.mem_dualAnnihilator _).mpr fun w hw => ?_
      have hw' : ψ w ∈ (Submodule.span k {a}).map ψ := ⟨w, hw, rfl⟩
      rwa [hmap, Submodule.mem_bot] at hw'
    have hz := hall ((evalAtVector k V b).dualMap ψ) ⟨ψ, hmem, rfl⟩
    rwa [LinearMap.dualMap_apply, evalAtVector_apply] at hz
  · rintro hmem φ ⟨ψ, hψ, rfl⟩
    rw [LinearMap.dualMap_apply, evalAtVector_apply]
    exact (Submodule.mem_dualAnnihilator _).mp hψ _ hmem

/-- **A closed point of `𝐏` lies on that linear subspace exactly when its representatives carry
`b` into `k·a`.** -/
public theorem mem_linearSubspace_hyperplaneTransportSubmodule_iff
    {p : ClosedPoints k (ParameterModule k V)} {g : V →ₗ[k] V}
    (hg : RepresentsParameterPoint k V p g) (a b : V) :
    (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
        linearSubspace k (ParameterModule k V) (hyperplaneTransportSubmodule k V a b) ↔
      g b ∈ Submodule.span k {a} := by
  rw [mem_linearSubspace_iff_forall_apply_eq_zero k V hg,
    forall_apply_eq_zero_hyperplaneTransportSubmodule_iff]

omit [IsAlgClosed k] in
/-- Those equations are `dim_k V - 1` in number: evaluation at `b` is surjective, so pulling back
along it is injective, and the functionals killing `a` form a subspace of corank one. -/
public theorem finrank_hyperplaneTransportSubmodule {n : ℕ} (hV : Module.finrank k V = n + 1)
    {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.finrank k (hyperplaneTransportSubmodule k V a b) = n := by
  have hinj : Function.Injective (evalAtVector k V b).dualMap :=
    LinearMap.dualMap_injective_of_surjective (surjective_evalAtVector k V hb)
  have heq : Module.finrank k ((Submodule.span k {a}).dualAnnihilator) =
      Module.finrank k (hyperplaneTransportSubmodule k V a b) :=
    (Submodule.equivMapOfInjective _ hinj
      ((Submodule.span k {a} : Submodule k V).dualAnnihilator)).finrank_eq
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (Submodule.span k {a} : Subspace k V)
  rw [finrank_span_singleton ha, hV] at h1
  omega

omit [IsAlgClosed k] in
/-- `ParameterModule k V` has dimension `(dim_k V)²`, so its projective space, the parameter
space, has dimension `(dim_k V)² - 1`. -/
public theorem finrank_parameterModule :
    Module.finrank k (ParameterModule k V) = Module.finrank k V * Module.finrank k V := by
  rw [Subspace.dual_finrank_eq, Module.finrank_linearMap]

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- Two independent vectors span a plane. -/
private theorem finrank_sup_span_singleton {a b : V} (ha : a ≠ 0)
    (hb : b ∉ Submodule.span k {a}) :
    Module.finrank k ((Submodule.span k {a} ⊔ Submodule.span k {b} : Submodule k V)) = 2 := by
  have hb0 := ne_zero_of_notMem_span_singleton k V hb
  have h1 : Module.finrank k (Submodule.span k {a} : Submodule k V) = 1 :=
    finrank_span_singleton ha
  have h2 : Module.finrank k (Submodule.span k {b} : Submodule k V) = 1 :=
    finrank_span_singleton hb0
  have hlt : (Submodule.span k {a} : Submodule k V) <
      Submodule.span k {a} ⊔ Submodule.span k {b} := by
    refine lt_of_le_of_ne le_sup_left fun h => hb ?_
    have hmem : b ∈ (Submodule.span k {a} ⊔ Submodule.span k {b} : Submodule k V) :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self b)
    rwa [← h] at hmem
  have hub := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span k {a} : Submodule k V) (Submodule.span k {b})
  have hstrict := Submodule.finrank_lt_finrank_of_lt hlt
  omega

omit [IsAlgClosed k] in
/-- The corank of a line in a three-dimensional space is two. -/
private theorem finrank_quotient_span_singleton (hV : Module.finrank k V = 3) {a : V}
    (ha : a ≠ 0) : Module.finrank k (V ⧸ Submodule.span k {a}) = 2 := by
  have h := Submodule.finrank_quotient_add_finrank (Submodule.span k {a} : Submodule k V)
  rw [finrank_span_singleton ha, hV] at h
  omega

omit [IsAlgClosed k] in
/-- The two lines of `𝐏²` cut out by two independent vectors have dimension one each. -/
private theorem topologicalKrullDim_hyperplane (hV : Module.finrank k V = 3) {a : V}
    (ha : a ≠ 0) :
    topologicalKrullDim (linearSubspace k V (Submodule.span k {a})) = 1 :=
  topologicalKrullDim_linearSubspace_eq_one k V _ (finrank_quotient_span_singleton k V hV ha)

/-- **Every closed point of the transport subspace is bad.** Let `g` represent such a point, so
`g b ∈ k·a`. If `X` leaves `U(g)` then clause (1) of Tag 0B1S fails at `g`. Otherwise the whole
of `r_g(X)` lies on the line `Y`, because the equation `b` of `Y` pulls back along `r_g` to the
equation `g b`, a multiple of the equation `a` of `X`; then `r_g(X) ∩ Y = r_g(X)` and clause (2)
asks for `dim r_g(X) + 2 ≤ dim r_g(X) + 1`, which fails since `r_g(X)` is nonempty of dimension
at most two. -/
public theorem mem_badParameterLocus_of_mem_linearSubspace_hyperplaneTransportSubmodule
    (hV : Module.finrank k V = 3) {a b : V} (ha : a ≠ 0) (hb : b ≠ 0)
    (p : ClosedPoints k (ParameterModule k V))
    (hp : (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
      linearSubspace k (ParameterModule k V) (hyperplaneTransportSubmodule k V a b)) :
    (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
      badParameterLocus k V (linearSubspace k V (Submodule.span k {a}))
        (linearSubspace k V (Submodule.span k {b})) := by
  have hntV : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  set g := (dualEndClosedPointsEquiv k V p).rep with hgdef
  have hg0 : g ≠ 0 := (dualEndClosedPointsEquiv k V p).rep_nonzero
  have hrep : RepresentsParameterPoint k V p g := ⟨hg0, (Projectivization.mk_rep _).symm⟩
  have hgb : g b ∈ Submodule.span k {a} :=
    (mem_linearSubspace_hyperplaneTransportSubmodule_iff k V hrep a b).mp hp
  refine ⟨p, g, rfl, hrep, fun hgood => ?_⟩
  obtain ⟨hdom, hdim⟩ := hgood
  -- the image of `X` under `r_g` lies on `Y`
  have hmaple : (Submodule.span k {b}).map g ≤ Submodule.span k {a} := by
    rw [Submodule.map_span, Set.image_singleton, Submodule.span_le, Set.singleton_subset_iff]
    exact hgb
  have himg : endProjectionImage k V g (linearSubspace k V (Submodule.span k {a})) ⊆
      linearSubspace k V (Submodule.span k {b}) :=
    endProjectionImage_subset_linearSubspace k V g _ _
      (linearSubspace_antitone k V hmaple)
  have hXne : (linearSubspace k V (Submodule.span k {a})).Nonempty := by
    exact linearSubspace_nonempty k V
      (ne_top_of_finrank_eq_of_ne k (finrank_span_singleton ha) (by omega))
  have hSne : (endProjectionImage k V g (linearSubspace k V (Submodule.span k {a}))).Nonempty :=
    endProjectionImage_nonempty k V hXne hdom
  rw [Set.inter_eq_self_of_subset_left himg,
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (n := 2) hV,
    topologicalKrullDim_hyperplane k V hV hb] at hdim
  -- `dim r_g(X) + 2 ≤ dim r_g(X) + 1` is impossible
  have hA2 : topologicalKrullDim
      (endProjectionImage k V g (linearSubspace k V (Submodule.span k {a}))) ≤
      ((2 : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_subspace_le (projectiveSpaceOfModule k V) _).trans_eq
      (topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (n := 2) hV)
  have hA0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim
      (endProjectionImage k V g (linearSubspace k V (Submodule.span k {a}))) := by
    have : Nonempty
        (endProjectionImage k V g (linearSubspace k V (Submodule.span k {a}))) :=
      hSne.to_subtype
    have : Nonempty (IrreducibleCloseds
        (endProjectionImage k V g (linearSubspace k V (Submodule.span k {a})))) :=
      ⟨IrreducibleCloseds.closureSingleton (Classical.arbitrary _)⟩
    exact Order.krullDim_nonneg
  exact not_add_two_le_add_one hA0 hA2 hdim

/-- **A bad class off the transport subspace.** The rank-one endomorphism `u ↦ ψ(u)·b` with
`ψ b = 1` carries `b` to `b`, which does not lie on `k·a`, so its class is not on the transport
subspace; and clause (1) of Tag 0B1S fails at it, at the point of `X` cut out by any nonzero
functional killing both `a` and `b`. -/
public theorem exists_mem_badParameterLocus_notMem_linearSubspace
    (hV : Module.finrank k V = 3) {a b : V} (ha : a ≠ 0) (hb : b ∉ Submodule.span k {a}) :
    ∃ p : ClosedPoints k (ParameterModule k V),
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
        badParameterLocus k V (linearSubspace k V (Submodule.span k {a}))
          (linearSubspace k V (Submodule.span k {b})) ∧
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∉
        linearSubspace k (ParameterModule k V) (hyperplaneTransportSubmodule k V a b) := by
  have hb0 := ne_zero_of_notMem_span_singleton k V hb
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one k hb0
  set g := ψ.smulRight b with hgdef
  have hgapp : ∀ u : V, g u = ψ u • b := fun u => rfl
  have hgb : g b = b := by rw [hgapp, hψ, one_smul]
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0] at hgb
    exact hb0 (by simpa using hgb.symm)
  set p := (dualEndClosedPointsEquiv k V).symm (Projectivization.mk k g hg0) with hpdef
  have hrep : RepresentsParameterPoint k V p g :=
    ⟨hg0, by rw [hpdef, Equiv.apply_symm_apply]⟩
  refine ⟨p, ⟨p, g, rfl, hrep, fun hgood => ?_⟩, ?_⟩
  · -- clause (1) fails: a point of `X` leaves `U(g)`
    have hsupne : (Submodule.span k {a} ⊔ Submodule.span k {b} : Submodule k V) ≠ ⊤ :=
      ne_top_of_finrank_eq_of_ne k (finrank_sup_span_singleton k V ha hb) (by omega)
    obtain ⟨f, hf, hle⟩ := exists_ne_zero_le_ker_of_ne_top k V hsupne
    have hfa : (Submodule.span k {a} : Submodule k V) ≤ LinearMap.ker f := le_sup_left.trans hle
    have hfb : f b = 0 :=
      LinearMap.mem_ker.mp (hle (Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self b)))
    have hmemX : linearFunctionalPoint k V f hf ∈
        linearSubspace k V (Submodule.span k {a}) :=
      (mem_linearSubspace_linearFunctionalPoint_iff k V _ f hf).mpr hfa
    have hrange : LinearMap.range g ≤ LinearMap.ker f := by
      rintro _ ⟨u, rfl⟩
      rw [LinearMap.mem_ker, hgapp, map_smul, hfb, smul_zero]
    have hnotdom : linearFunctionalPoint k V f hf ∉ endDomain k V g :=
      (notMem_endDomain_iff k V g _).mpr
        ((mem_linearSubspace_linearFunctionalPoint_iff k V _ f hf).mpr hrange)
    exact hnotdom (hgood.1 hmemX)
  · rw [mem_linearSubspace_hyperplaneTransportSubmodule_iff k V hrep a b, hgb]
    exact hb

/-! ### No irreducible closed subset has the bad classes as its closed points -/

omit [IsAlgClosed k] in
/-- The transport equations do not cut out the empty set. -/
public theorem hyperplaneTransportSubmodule_ne_top (hV : Module.finrank k V = 3)
    {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) :
    hyperplaneTransportSubmodule k V a b ≠ ⊤ := by
  refine ne_top_of_finrank_eq_of_ne k (finrank_hyperplaneTransportSubmodule k V (n := 2) hV ha hb)
    ?_
  rw [finrank_parameterModule, hV]
  norm_num

omit [IsAlgClosed k] in
/-- **The transport subspace has dimension six** in the eight-dimensional parameter space. -/
public theorem topologicalKrullDim_linearSubspace_hyperplaneTransportSubmodule
    (hV : Module.finrank k V = 3) {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) :
    topologicalKrullDim
        (linearSubspace k (ParameterModule k V) (hyperplaneTransportSubmodule k V a b)) =
      ((6 : ℕ) : WithBot ℕ∞) := by
  refine topologicalKrullDim_linearSubspace_of_finrank_eq k (ParameterModule k V) _ (m := 6) ?_
  have hq := Submodule.finrank_quotient_add_finrank (hyperplaneTransportSubmodule k V a b)
  have h2 := finrank_hyperplaneTransportSubmodule k V (n := 2) hV ha hb
  rw [finrank_parameterModule, hV] at hq
  omega

/-- A codimension of at least three is incompatible with a dimension of six in an
eight-dimensional space. -/
private theorem not_six_add_le_eight {c : ℕ∞} (h3 : (3 : ℕ∞) ≤ c)
    (hle : ((6 : ℕ) : WithBot ℕ∞) + (c : WithBot ℕ∞) ≤ ((8 : ℕ) : WithBot ℕ∞)) : False := by
  rw [show ((6 : ℕ) : WithBot ℕ∞) = (((6 : ℕ) : ℕ∞) : WithBot ℕ∞) from rfl,
    show ((8 : ℕ) : WithBot ℕ∞) = (((8 : ℕ) : ℕ∞) : WithBot ℕ∞) from rfl,
    ← WithBot.coe_add, WithBot.coe_le_coe] at hle
  have h9 : ((9 : ℕ) : ℕ∞) ≤ ((8 : ℕ) : ℕ∞) := by
    refine le_trans ?_ hle
    calc ((9 : ℕ) : ℕ∞) = ((6 : ℕ) : ℕ∞) + 3 := by norm_num
      _ ≤ ((6 : ℕ) : ℕ∞) + c := add_le_add le_rfl h3
  have h98 : (9 : ℕ) ≤ 8 := by exact_mod_cast h9
  omega

/-- **An irreducible bad locus of codimension at least two is not to be had for two distinct
lines of `𝐏²`.** There is no irreducible closed subset of the
parameter space, of codimension at least two, whose closed points are exactly the bad classes.
Such a `B` would contain the codimension-two transport subspace `C`, every closed point of which
is bad and whose closed points are dense in it, and would also contain a bad class off `C`; so
`C ⊊ B` and `codim C ≥ codim B + 1 ≥ 3`, whereas `dim C = 6` and `dim 𝐏 = 8` force
`codim C ≤ 2`. -/
public theorem not_exists_irreducible_badParameterLocus (hV : Module.finrank k V = 3)
    {a b : V} (ha : a ≠ 0) (hb : b ∉ Submodule.span k {a}) :
    ¬ ∃ B : IrreducibleCloseds (projectiveSpaceOfModule k (ParameterModule k V)),
      (∀ p : ClosedPoints k (ParameterModule k V),
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
            (B : Set (projectiveSpaceOfModule k (ParameterModule k V))) ↔
          (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
            badParameterLocus k V (linearSubspace k V (Submodule.span k {a}))
              (linearSubspace k V (Submodule.span k {b}))) ∧
      (2 : ℕ∞) ≤ codimension B := by
  rintro ⟨B, hB, hcodim⟩
  have hb0 := ne_zero_of_notMem_span_singleton k V hb
  have hLne := hyperplaneTransportSubmodule_ne_top k V hV ha hb0
  obtain ⟨C, hCcoe⟩ : ∃ C : IrreducibleCloseds
      (projectiveSpaceOfModule k (ParameterModule k V)),
      (C : Set (projectiveSpaceOfModule k (ParameterModule k V))) =
        linearSubspace k (ParameterModule k V) (hyperplaneTransportSubmodule k V a b) :=
    ⟨linearSubvariety k (ParameterModule k V) hLne, rfl⟩
  -- the closed points of `C` are bad, and they are dense in `C`, so `C ⊆ B`
  have hCB : (C : Set (projectiveSpaceOfModule k (ParameterModule k V))) ⊆
      (B : Set (projectiveSpaceOfModule k (ParameterModule k V))) := by
    by_contra hns
    rw [hCcoe] at hns
    obtain ⟨q, hqc, hqC, hqB⟩ := exists_isClosed_singleton_mem_linearSubspace_notMem
      k (ParameterModule k V) hLne B.isClosed' hns
    exact hqB ((hB ⟨q, hqc⟩).mpr
      (mem_badParameterLocus_of_mem_linearSubspace_hyperplaneTransportSubmodule
        k V hV ha hb0 ⟨q, hqc⟩ hqC))
  -- a bad class off `C`
  obtain ⟨p₂, hp₂bad, hp₂C⟩ := exists_mem_badParameterLocus_notMem_linearSubspace k V hV ha hb
  have hp₂B : (p₂ : projectiveSpaceOfModule k (ParameterModule k V)) ∈
      (B : Set (projectiveSpaceOfModule k (ParameterModule k V))) := (hB p₂).mpr hp₂bad
  have hCneB : C ≠ B := by
    intro hCB'
    rw [hCB'] at hCcoe
    exact hp₂C (hCcoe ▸ hp₂B)
  have hCltB : C < B := lt_of_le_of_ne hCB hCneB
  -- `codim C ≥ 3`
  have hstep : codimension B + 1 ≤ codimension C := by
    rw [codimension_eq_coheight, codimension_eq_coheight]
    exact Order.coheight_add_one_le hCltB
  have h3 : (3 : ℕ∞) ≤ codimension C := by
    refine le_trans ?_ hstep
    calc (3 : ℕ∞) = 2 + 1 := by norm_num
      _ ≤ codimension B + 1 := add_le_add hcodim le_rfl
  -- `codim C ≤ 2`
  have hle := topologicalKrullDim_add_codimension_le_projectiveSpaceOfModule
    (k := k) (V := ParameterModule k V) (n := 8) (by rw [finrank_parameterModule, hV]) C
  rw [hCcoe,
    topologicalKrullDim_linearSubspace_hyperplaneTransportSubmodule k V hV ha hb0] at hle
  exact not_six_add_le_eight h3 hle

/-- **Tag 0B1S's source hypotheses are satisfiable where its irreducible bad locus is not.** For
two distinct lines of `𝐏²` — which intersect properly in a point, with `X ≠ 𝐏²` and
`X ∩ Y ≠ ∅` — there is no irreducible closed subset of the parameter space, of codimension at
least two, whose closed points are exactly the bad classes. So a statement of the tag asking for
such a `B` is vacuous for this pair, and the shape to use is the pointwise one of
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_closedPoint_line_isGood_of_codimension`,
which asks for a closed `B` with `∀ x ∈ B, 2 ≤ codimension (closureSingleton x)`. -/
public theorem exists_intersectProperly_not_exists_irreducible_badParameterLocus
    (hV : Module.finrank k V = 3) {a b : V} (ha : a ≠ 0)
    (hb : b ∉ Submodule.span k {a}) :
    ∃ X Y : IrreducibleCloseds (projectiveSpaceOfModule k V),
      IntersectProperly X Y ∧
      (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ ∧
      ((X : Set (projectiveSpaceOfModule k V)) ∩
        (Y : Set (projectiveSpaceOfModule k V))).Nonempty ∧
      ¬ ∃ B : IrreducibleCloseds (projectiveSpaceOfModule k (ParameterModule k V)),
        (∀ p : ClosedPoints k (ParameterModule k V),
          (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
              (B : Set (projectiveSpaceOfModule k (ParameterModule k V))) ↔
            (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
              badParameterLocus k V (X : Set (projectiveSpaceOfModule k V))
                (Y : Set (projectiveSpaceOfModule k V))) ∧
        (2 : ℕ∞) ≤ codimension B := by
  have hb0 := ne_zero_of_notMem_span_singleton k V hb
  have hane : (Submodule.span k {a} : Submodule k V) ≠ ⊤ :=
    ne_top_of_finrank_eq_of_ne k (finrank_span_singleton ha) (by omega)
  have hbne : (Submodule.span k {b} : Submodule k V) ≠ ⊤ :=
    ne_top_of_finrank_eq_of_ne k (finrank_span_singleton hb0) (by omega)
  have hsupne : (Submodule.span k {a} ⊔ Submodule.span k {b} : Submodule k V) ≠ ⊤ :=
    ne_top_of_finrank_eq_of_ne k (finrank_sup_span_singleton k V ha hb) (by omega)
  have hquotsup : Module.finrank k
      (V ⧸ (Submodule.span k {a} ⊔ Submodule.span k {b} : Submodule k V)) = 0 + 1 := by
    have h := Submodule.finrank_quotient_add_finrank
      (Submodule.span k {a} ⊔ Submodule.span k {b} : Submodule k V)
    rw [finrank_sup_span_singleton k V ha hb, hV] at h
    omega
  refine ⟨linearSubvariety k V hane, linearSubvariety k V hbne, ?_, ?_, ?_, ?_⟩
  · rw [intersectProperly_iff, coe_linearSubvariety, coe_linearSubvariety,
      ← linearSubspace_sup,
      topologicalKrullDim_linearSubspace_of_finrank_eq k V _ hquotsup,
      topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (n := 2) hV,
      topologicalKrullDim_linearSubspace_of_finrank_eq k V _
        (m := 1) (finrank_quotient_span_singleton k V hV ha),
      topologicalKrullDim_linearSubspace_of_finrank_eq k V _
        (m := 1) (finrank_quotient_span_singleton k V hV hb0)]
    norm_num
  · rw [coe_linearSubvariety]
    obtain ⟨q, -, hq⟩ := exists_closedPoint_notMem_linearSubspace k V
      (N := Submodule.span k {a}) (by rwa [Ne, Submodule.span_singleton_eq_bot])
    intro huniv
    exact hq (huniv.symm ▸ Set.mem_univ q)
  · rw [coe_linearSubvariety, coe_linearSubvariety, ← linearSubspace_sup]
    exact linearSubspace_nonempty k V hsupne
  · rw [coe_linearSubvariety, coe_linearSubvariety]
    exact not_exists_irreducible_badParameterLocus k V hV ha hb

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
