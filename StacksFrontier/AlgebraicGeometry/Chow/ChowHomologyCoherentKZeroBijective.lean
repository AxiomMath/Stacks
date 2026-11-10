module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowHomologyCoherentKZero
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ChowToGradedCoherentKZero
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support

/-!
# Chow homology and coherent K-theory: the reduction of Proposition 42.57.1 to two conditions

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X ⟶ Y` be a closed
immersion of schemes locally of finite type over `S` with `Y` regular and quasi-compact, and
write `A_k(X) = CH_k(X)`. Proposition 42.57.1 (Stacks 0FEW) says that the composition

  `K'₀(X) ⟶ K₀(D_{X, perf}(𝒪_Y)) ⟶ A^*(X ⟶ Y) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`

of the map `ℱ ↦ ℱ[0]` of Stacks 0FEQ, the localized Chern character `ch(X ⟶ Y, -)` and the cap
product `c ↦ c ∩ [Y]` induces an isomorphism `K'₀(X) ⊗ 𝐐 ≅ CH_*(X) ⊗ 𝐐`, and that the canonical
map `CH_k(X) ⊗ 𝐐 ⟶ gr_k K'₀(X) ⊗ 𝐐` is an isomorphism for every `k`.

The source proves this by reducing it to two conditions on the composition, and this file
carries out that reduction: for *any* homomorphism `ch : K'₀(X) ⟶ CH_*(X) ⊗ 𝐐` satisfying the
two conditions, the canonical maps become isomorphisms after tensoring with `𝐐` and `ch` induces
an isomorphism `K'₀(X) ⊗ 𝐐 ≅ CH_*(X) ⊗ 𝐐`. Nothing here is tagged: the proposition is about the
particular composition above, and these are the steps of its proof.

It extends `StacksFrontier.AlgebraicGeometry.Chow.ChowHomologyCoherentKZero`, which proves the
injectivity of the canonical map and the surjectivity of the composition under the two
conditions read on all cycle classes and with the canonical maps as hypotheses; here the
canonical maps are the ones constructed in
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.ChowToGradedCoherentKZero`, condition (2) is read
on integral closed subschemes as in the source, and `X` is Noetherian.

## Main definitions

* `Stacks.Chow.IsDimensionTriangular` — condition (1) of the proof: the class of a coherent
  module whose support has delta-dimension at most `j` goes into `⨁_{j' ≤ j} CH_{j'}(X) ⊗ 𝐐`.
* `Stacks.Chow.IsDiagonalOnIntegral` — condition (2): for an integral closed subscheme `Z` of
  delta-dimension `k` the degree `k` part of the image of `[𝒪_Z]` is `[Z]`.
* `Stacks.Chow.gradedDegreePart` — under condition (1), the degree `k` part of `ch` descended to
  `gr_k K'₀(X) ⟶ CH_k(X) ⊗ 𝐐`, the inverse map constructed in the source.
* `Stacks.Chow.HasLeadingTermOnIntegral` — the form in which the proof establishes the two
  conditions: the image of `[𝒪_Z]` is `[Z]` plus classes of integral closed subschemes of `Z`
  other than `Z`.

## Main results

* `Stacks.Chow.gradedDegreePart_chowToGradedCoherentKZero` — under (1) and (2) that map is a left
  inverse of the canonical map `Stacks.Chow.chowToGradedCoherentKZero`.
* `Stacks.Chow.bijective_rTensor_chowToGradedCoherentKZero` — the canonical map
  `CH_k(X) ⊗ 𝐐 ⟶ gr_k K'₀(X) ⊗ 𝐐` is bijective.
* `Stacks.Chow.surjective_liftBaseChange`, `Stacks.Chow.injective_liftBaseChange`,
  `Stacks.Chow.bijective_liftBaseChange` — `ch` induces a bijection
  `K'₀(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`, when `δ_{X/S}` is bounded below.
* `Stacks.Chow.surjective_liftBaseChange_of_hasLeadingTermOnIntegral` — from that form, `ch`
  induces a surjection `K'₀(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐` with no bound on `δ_{X/S}`, by Noetherian
  induction on the closures of points.
* `Stacks.Chow.exists_relativeDimension_le` — on a Noetherian `X` the function `δ_{X/S}` is
  bounded above, which makes the filtration of `K'₀(X)` by dimension of supports exhaustive.

## Implementation notes

`CH_k(X) ⊗ 𝐐` is `TensorProduct ℤ ℚ (Stacks.Chow.chowGroup C f k)` and `gr_k K'₀(X)` is
`Stacks.Chow.gradedCoherentKZero`. Condition (2) is stated, as in the source, for the integral
closed subschemes of `X`; `Stacks.Chow.cycleGroup_hom_ext` extends it to every cycle class.

The bijectivity of the canonical maps uses only conditions (1) and (2) and the surjectivity of
`CH_k(X) ⟶ gr_k K'₀(X)`, Stacks 02S9 for the Noetherian scheme `X`. The bijectivity of
`K'₀(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐` additionally uses that `δ_{X/S}` is bounded below: injectivity is a
descending induction along the filtration, which ends at `F_{lo-1} K'₀(X) = 0`, and surjectivity
a descending induction along the degrees of `CH_*(X)`, which ends where `CH_j(X) = 0`. The
surjectivity is also proved without that bound, from `Stacks.Chow.HasLeadingTermOnIntegral`,
which records where the lower-order terms of the image of `[𝒪_Z]` live and so lets the induction
run over the closed subsets of `X` instead of over degrees. Whether the injectivity holds without
the bound is not settled here: given conditions (1) and (2) it is equivalent to
`⋂_k F_k K'₀(X) ⊗ 𝐐 = 0`.

## References

* [Stacks Project, Tag 0FEW](https://stacks.math.columbia.edu/tag/0FEW)
* [Stacks Project, Tag 0FEV](https://stacks.math.columbia.edu/tag/0FEV)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Two lemmas on `𝐐 ⊗ A` and on Noetherian schemes -/

/-- An element `a` of an abelian group has `1 ⊗ a = 0` in `𝐐 ⊗ A` exactly when it is torsion:
`𝐐 ⊗ A` is the localization of `A` at the nonzero integers. -/
theorem exists_zsmul_eq_zero_of_one_tmul_eq_zero {A : Type*} [AddCommGroup A] {a : A}
    (h : (1 : ℚ) ⊗ₜ[ℤ] a = 0) : ∃ m : ℤ, m ≠ 0 ∧ m • a = 0 := by
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ A 1)).1 h
  exact ⟨s, nonZeroDivisors.coe_ne_zero s, hs⟩

/-- On a Noetherian scheme locally of finite type over the base the relative dimension `δ_{X/S}`
is bounded above: every point specializes from the generic point of one of the finitely many
irreducible components, and `δ_{X/S}` only drops along a specialization. -/
theorem exists_relativeDimension_le (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] [IsNoetherian X] :
    ∃ hi : ℤ, ∀ x : X, relativeDimension C.dimensionFunction f x ≤ hi := by
  classical
  let g : Set X → ℤ := fun W =>
    if hW : IsIrreducible W then relativeDimension C.dimensionFunction f hW.genericPoint else 0
  obtain ⟨hi, hhi⟩ :=
    ((TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)).image g).bddAbove
  refine ⟨hi, fun x => ?_⟩
  obtain ⟨W, hW, hxW⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
  have hx : x ∈ closure {hW.1.genericPoint} := by
    rw [(hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)).def]
    exact hxW rfl
  calc relativeDimension C.dimensionFunction f x
      ≤ relativeDimension C.dimensionFunction f hW.1.genericPoint :=
        relativeDimension_le_of_mem_closure C f hx
    _ = g W := by simp only [g, dite_eq_left hW.1]
    _ ≤ hi := hhi ⟨W, hW, rfl⟩

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  [IsNoetherian X]

/-! ### The two conditions of the proof of Proposition 42.57.1 -/

/-- **Condition (1) of the proof of Stacks 0FEW** for a homomorphism
`ch : K'₀(X) ⟶ CH_*(X) ⊗ 𝐐`: the class of a coherent module whose support has delta-dimension
at most `j` is sent into `⨁_{j' ≤ j} CH_{j'}(X) ⊗ 𝐐`. -/
def IsDimensionTriangular
    (ch : CoherentKZero X →+ DirectSum ℤ fun j => TensorProduct ℤ ℚ (chowGroup C f j)) : Prop :=
  ∀ (j j' : ℤ) (F : CoherentModulesDimLE C f j), j < j' → ch (KZero.mk _ F.obj) j' = 0

/-- **Condition (2) of the proof of Stacks 0FEW** for a homomorphism
`ch : K'₀(X) ⟶ CH_*(X) ⊗ 𝐐`: for an integral closed subscheme `Z ⊆ X` of delta-dimension `k`
the degree `k` part of the image of `[𝒪_Z]` is the class of `[Z]`. The integral closed
subschemes of `X` are those attached to the points of `X`, `Z` being the reduced induced
structure on the closure of its generic point. -/
def IsDiagonalOnIntegral
    (ch : CoherentKZero X →+ DirectSum ℤ fun j => TensorProduct ℤ ℚ (chowGroup C f j)) : Prop :=
  ∀ (k : ℤ) (x : X) (hx : relativeDimension C.dimensionFunction f x = k),
    ch (KZero.mk _ (integralComponentDimLE C f k x hx).obj) k =
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk' (rationalEquivalences C f k)
        (cycleAssociatedToClosedSubscheme C f (integralComponentAt x).subschemeι k)

variable {C f}
variable (ch : CoherentKZero X →+ DirectSum ℤ fun j => TensorProduct ℤ ℚ (chowGroup C f j))

omit [AlgebraicGeometry.IsNoetherian X] in
/-- Condition (1) extends from the generators of `F_k K'₀(X)` to all of it. -/
theorem IsDimensionTriangular.apply_eq_zero (h1 : IsDimensionTriangular C f ch) {k j : ℤ}
    (hkj : k < j) {z : CoherentKZero X} (hz : z ∈ coherentKZeroFiltration C f k) : ch z j = 0 := by
  have hker := coherentKZeroFiltration_le_ker C f
    ({ toFun := fun w => ch w j, map_zero' := by simp, map_add' := fun a b => by simp } :
      CoherentKZero X →+ TensorProduct ℤ ℚ (chowGroup C f j)) k
    (fun F => h1 k j F hkj) hz
  simpa using hker

/-- The degree `k` part of `ch`, read on `F_k K'₀(X)`. -/
def degreePart (k : ℤ) : coherentKZeroFiltration C f k →+ TensorProduct ℤ ℚ (chowGroup C f k) :=
  { toFun := fun z => ch z k, map_zero' := by simp, map_add' := fun a b => by simp }

/-- Under condition (1) the degree `k` part of `ch` descends to `gr_k K'₀(X)`: this is the map
`gr_k K'₀(X) ⟶ CH_k(X) ⊗ 𝐐` which the proof of Stacks 0FEW shows to be inverse to the canonical
map. -/
def gradedDegreePart (h1 : IsDimensionTriangular C f ch) (k : ℤ) :
    gradedCoherentKZero C f k →+ TensorProduct ℤ ℚ (chowGroup C f k) :=
  gradedCoherentKZeroLift C f k (degreePart ch k) fun _ hz => h1.apply_eq_zero ch (by omega) hz

/-- Under conditions (1) and (2) the descended degree `k` part of `ch` is a left inverse of the
canonical map `CH_k(X) ⟶ gr_k K'₀(X)`, after tensoring the source with `𝐐`: it sends the image of
a cycle class `α` to `1 ⊗ α`. Condition (2) gives this on the class of an integral closed
subscheme, and these generate `CH_k(X)` on the quasi-compact `X`. -/
theorem gradedDegreePart_chowToGradedCoherentKZero (h1 : IsDimensionTriangular C f ch)
    (h2 : IsDiagonalOnIntegral C f ch) (k : ℤ) (α : chowGroup C f k) :
    gradedDegreePart ch h1 k (chowToGradedCoherentKZero C f k α) = (1 : ℚ) ⊗ₜ[ℤ] α := by
  have hψ : (gradedDegreePart ch h1 k).comp (chowToGradedCoherentKZero C f k) =
      (TensorProduct.mk ℤ ℚ (chowGroup C f k) 1).toAddMonoidHom := by
    refine QuotientAddGroup.addMonoidHom_ext _ (cycleGroup_hom_ext C f k fun x hx => ?_)
    change gradedDegreePart ch h1 k (chowToGradedCoherentKZero C f k
        (QuotientAddGroup.mk' (rationalEquivalences C f k) _)) = _
    rw [chowToGradedCoherentKZero_mk_integralComponent C f k x hx]
    exact h2 k x hx
  exact DFunLike.congr_fun hψ α

/-- Under conditions (1) and (2), an element of `F_k K'₀(X)` whose class in `gr_k K'₀(X)` is the
image of a cycle class `α` has degree `k` part `1 ⊗ α`. -/
theorem apply_self_eq_of_toGradedCoherentKZero_eq (h1 : IsDimensionTriangular C f ch)
    (h2 : IsDiagonalOnIntegral C f ch) (k : ℤ) (α : chowGroup C f k)
    (x : coherentKZeroFiltration C f k)
    (hx : toGradedCoherentKZero C f k x = chowToGradedCoherentKZero C f k α) :
    ch x k = (1 : ℚ) ⊗ₜ[ℤ] α := by
  rw [← gradedDegreePart_chowToGradedCoherentKZero ch h1 h2 k α, ← hx]
  rfl

/-! ### The canonical maps are isomorphisms rationally -/

/-- **The "moreover" of Stacks 0FEW, from conditions (1) and (2).** For a homomorphism
`ch : K'₀(X) ⟶ CH_*(X) ⊗ 𝐐` satisfying the two conditions of the proof, the canonical map
`CH_k(X) ⊗ 𝐐 ⟶ gr_k K'₀(X) ⊗ 𝐐` is bijective. Surjectivity is that of the canonical map itself
(Stacks 02S9 on a Noetherian scheme); injectivity is that the descended degree `k` part of `ch`
is a left inverse. -/
theorem bijective_rTensor_chowToGradedCoherentKZero (h1 : IsDimensionTriangular C f ch)
    (h2 : IsDiagonalOnIntegral C f ch) (k : ℤ) :
    Function.Bijective (TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
      (chowToGradedCoherentKZero C f k).toIntLinearMap) := by
  refine ⟨?_, TensorProduct.map_surjective Function.surjective_id
    (chowToGradedCoherentKZero_surjective C f k)⟩
  let ψ := gradedDegreePart ch h1 k
  let B : ℚ →ₗ[ℤ] gradedCoherentKZero C f k →ₗ[ℤ] TensorProduct ℤ ℚ (chowGroup C f k) :=
    { toFun := fun q => q • ψ.toIntLinearMap
      map_add' := fun q q' => by rw [add_smul]
      map_smul' := fun c q => by rw [smul_assoc, RingHom.id_apply] }
  have key : ∀ z : TensorProduct ℤ ℚ (chowGroup C f k),
      TensorProduct.lift B (TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
        (chowToGradedCoherentKZero C f k).toIntLinearMap z) = z := by
    intro z
    induction z with
    | tmul q α =>
      rw [TensorProduct.map_tmul, TensorProduct.lift.tmul]
      change q • ψ (chowToGradedCoherentKZero C f k α) = q ⊗ₜ[ℤ] α
      rw [gradedDegreePart_chowToGradedCoherentKZero ch h1 h2, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  exact fun a b hab => by rw [← key a, ← key b, hab]

/-- Under conditions (1) and (2), `ch` becomes surjective after tensoring the source with `𝐐`,
provided `δ_{X/S}` is bounded below. A descending induction on degrees: condition (2) produces an
element of the image with any prescribed top component, condition (1) makes its components in
higher degrees vanish, and the bound makes `CH_j(X) = 0` for small `j`, which stops the descent. -/
theorem surjective_liftBaseChange (h1 : IsDimensionTriangular C f ch)
    (h2 : IsDiagonalOnIntegral C f ch)
    (lo : ℤ) (hlo : ∀ x : X, lo ≤ relativeDimension C.dimensionFunction f x) :
    Function.Surjective (ch.toIntLinearMap.liftBaseChange ℚ) := by
  refine surjective_of_exists_triangular_preimage _ lo ?_ ?_
  · intro j hj m
    induction m with
    | tmul q α =>
      rw [chowGroup_eq_zero C f (fun x => by have := hlo x; omega) α, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  · intro k m
    induction m with
    | tmul q α =>
      obtain ⟨x, hx⟩ := toGradedCoherentKZero_surjective C f k (chowToGradedCoherentKZero C f k α)
      refine ⟨q ⊗ₜ[ℤ] (x : CoherentKZero X), ?_, fun j hj => ?_⟩
      · rw [LinearMap.liftBaseChange_tmul]
        change q • (ch (x : CoherentKZero X)) k = _
        rw [apply_self_eq_of_toGradedCoherentKZero_eq ch h1 h2 k α x hx, TensorProduct.smul_tmul',
          smul_eq_mul, mul_one]
      · rw [LinearMap.liftBaseChange_tmul]
        change q • (ch (x : CoherentKZero X)) j = 0
        rw [h1.apply_eq_zero ch hj x.2, smul_zero]
    | add a b ha hb =>
      obtain ⟨v, hv1, hv2⟩ := ha
      obtain ⟨w, hw1, hw2⟩ := hb
      exact ⟨v + w, by simp [hv1, hw1], fun j hj => by simp [hv2 j hj, hw2 j hj]⟩

omit [AlgebraicGeometry.IsNoetherian X] in
/-- If `δ_{X/S}` is bounded below by `lo`, then `F_{lo-1} K'₀(X) = 0`: a coherent module whose
support has delta-dimension at most `lo - 1` has empty support, hence is zero. -/
theorem coherentKZeroFiltration_eq_bot (lo : ℤ)
    (hlo : ∀ x : X, lo ≤ relativeDimension C.dimensionFunction f x) :
    coherentKZeroFiltration C f (lo - 1) = ⊥ := by
  refine le_bot_iff.1 ((AddSubgroup.closure_le _).2 ?_)
  rintro _ ⟨F, rfl⟩
  have hsupp : SheafOfModules.supp F.obj.obj = ∅ :=
    Set.eq_empty_of_forall_notMem fun x hx => by
      have := relativeDimension_le_of_mem_supp_dimLE C f (lo - 1) F x hx
      have := hlo x
      omega
  exact KZero.mk_eq_zero_of_isZero (Limits.IsZero.of_full_of_faithful_of_isZero
    (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι F.obj
    (Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty F.obj.obj hsupp))

/-- One step of the descent: under conditions (1) and (2), an element of `F_k K'₀(X)` killed by
`ch` has a nonzero multiple in `F_{k-1} K'₀(X)`. Its class in `gr_k K'₀(X)` is the image of a
cycle class `β` with `1 ⊗ β = 0`, so a nonzero multiple of `β`, hence of the class, vanishes. -/
theorem exists_zsmul_mem_pred_of_apply_eq_zero (h1 : IsDimensionTriangular C f ch)
    (h2 : IsDiagonalOnIntegral C f ch) {k : ℤ} {a : CoherentKZero X}
    (ha : a ∈ coherentKZeroFiltration C f k) (hch : ch a = 0) :
    ∃ m : ℤ, m ≠ 0 ∧ m • a ∈ coherentKZeroFiltration C f (k - 1) := by
  obtain ⟨β, hβ⟩ :=
    chowToGradedCoherentKZero_surjective C f k (toGradedCoherentKZero C f k ⟨a, ha⟩)
  have hdiag := apply_self_eq_of_toGradedCoherentKZero_eq ch h1 h2 k β ⟨a, ha⟩ hβ.symm
  rw [show ((⟨a, ha⟩ : coherentKZeroFiltration C f k) : CoherentKZero X) = a from rfl, hch,
    DirectSum.zero_apply] at hdiag
  obtain ⟨m, hm, hmβ⟩ := exists_zsmul_eq_zero_of_one_tmul_eq_zero hdiag.symm
  refine ⟨m, hm, ?_⟩
  have h0 : toGradedCoherentKZero C f k (m • ⟨a, ha⟩) = 0 := by
    rw [map_zsmul, ← hβ, ← map_zsmul, hmβ, map_zero]
  exact (toGradedCoherentKZero_eq_zero_iff C f k _).1 h0

/-- **The kernel of `ch` lies in `⋂_k F_k K'₀(X)`, rationally.** Under conditions (1) and (2), an
element of `K'₀(X)` killed by `ch` has, for every `k`, a nonzero multiple in `F_k K'₀(X)`. The
filtration is exhaustive, because `δ_{X/S}` is bounded above on the Noetherian `X`, and each step
down is `Stacks.Chow.exists_zsmul_mem_pred_of_apply_eq_zero`. No lower bound on `δ_{X/S}` is
used. -/
theorem exists_zsmul_mem_coherentKZeroFiltration_of_apply_eq_zero
    (h1 : IsDimensionTriangular C f ch) (h2 : IsDiagonalOnIntegral C f ch)
    {a : CoherentKZero X} (ha : ch a = 0) (k : ℤ) :
    ∃ m : ℤ, m ≠ 0 ∧ m • a ∈ coherentKZeroFiltration C f k := by
  obtain ⟨hi, hhi⟩ := exists_relativeDimension_le C f
  have key : ∀ n : ℕ, ∃ m : ℤ, m ≠ 0 ∧ m • a ∈ coherentKZeroFiltration C f (hi - n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨1, one_ne_zero, ?_⟩
      rw [Nat.cast_zero, sub_zero, coherentKZeroFiltration_eq_top C f hhi]
      exact AddSubgroup.mem_top _
    | succ n ih =>
      obtain ⟨m, hm, hma⟩ := ih
      obtain ⟨m', hm', hm'a⟩ := exists_zsmul_mem_pred_of_apply_eq_zero ch h1 h2 hma
        (by rw [map_zsmul, ha, smul_zero])
      refine ⟨m' * m, mul_ne_zero hm' hm, ?_⟩
      rw [mul_smul]
      convert hm'a using 2
      push_cast
      ring
  obtain ⟨m, hm, hma⟩ := key (hi - k).toNat
  exact ⟨m, hm, coherentKZeroFiltration_mono C f (by omega) hma⟩

/-- Under conditions (1) and (2), an element of `K'₀(X)` killed by `ch` is torsion, provided
`δ_{X/S}` is bounded below by `lo`: then `F_{lo-1} K'₀(X) = 0`
(`Stacks.Chow.exists_zsmul_mem_coherentKZeroFiltration_of_apply_eq_zero`). -/
theorem exists_zsmul_eq_zero_of_apply_eq_zero (h1 : IsDimensionTriangular C f ch)
    (h2 : IsDiagonalOnIntegral C f ch)
    (lo : ℤ) (hlo : ∀ x : X, lo ≤ relativeDimension C.dimensionFunction f x)
    (a : CoherentKZero X) (ha : ch a = 0) : ∃ m : ℤ, m ≠ 0 ∧ m • a = 0 := by
  obtain ⟨m, hm, hma⟩ :=
    exists_zsmul_mem_coherentKZeroFiltration_of_apply_eq_zero ch h1 h2 ha (lo - 1)
  rw [coherentKZeroFiltration_eq_bot lo hlo] at hma
  exact ⟨m, hm, (AddSubgroup.mem_bot).1 hma⟩

omit [AlgebraicGeometry.IsNoetherian X] in
/-- `ch` becomes injective after tensoring the source with `𝐐` as soon as every element killed
by `ch` is torsion: an element of `𝐐 ⊗ K'₀(X)` is `s⁻¹ ⊗ a` for an integer `s ≠ 0`. -/
theorem injective_liftBaseChange_of_torsion
    (htors : ∀ a : CoherentKZero X, ch a = 0 → ∃ m : ℤ, m ≠ 0 ∧ m • a = 0) :
    Function.Injective (ch.toIntLinearMap.liftBaseChange ℚ) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  let g := TensorProduct.mk ℤ ℚ (CoherentKZero X) 1
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (nonZeroDivisors ℤ) g z
  rw [Function.uncurry_apply_pair] at hz ⊢
  have hs : (s : ℤ) • IsLocalizedModule.mk' g a s = g a := IsLocalizedModule.mk'_cancel' _ _ _
  have hga : ch a = 0 := by
    have h := congrArg (ch.toIntLinearMap.liftBaseChange ℚ) hs
    rw [map_zsmul, hz, smul_zero] at h
    change 0 = ch.toIntLinearMap.liftBaseChange ℚ ((1 : ℚ) ⊗ₜ[ℤ] a) at h
    rw [LinearMap.liftBaseChange_tmul, one_smul] at h
    exact h.symm
  obtain ⟨m, hm, hma⟩ := htors a hga
  have hg : g a = 0 := by
    have : (m : ℚ) • g a = 0 := by
      rw [Int.cast_smul_eq_zsmul, ← map_zsmul, hma, map_zero]
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hm)
  rw [hg, ← Int.cast_smul_eq_zsmul ℚ] at hs
  exact (smul_eq_zero.1 hs).resolve_left (by exact_mod_cast nonZeroDivisors.coe_ne_zero s)

/-- **Injectivity from separation.** Under conditions (1) and (2), `ch ⊗ 𝐐` is injective as soon
as the filtration by dimension of supports is separated after tensoring with `𝐐`: an element
with a nonzero multiple in every `F_k K'₀(X)` is torsion. By
`Stacks.Chow.exists_zsmul_mem_coherentKZeroFiltration_of_apply_eq_zero` the converse holds as
well, so this is the whole content of injectivity in Stacks 0FEW. -/
theorem injective_liftBaseChange_of_separated (h1 : IsDimensionTriangular C f ch)
    (h2 : IsDiagonalOnIntegral C f ch)
    (hsep : ∀ a : CoherentKZero X,
      (∀ k : ℤ, ∃ m : ℤ, m ≠ 0 ∧ m • a ∈ coherentKZeroFiltration C f k) →
        ∃ m : ℤ, m ≠ 0 ∧ m • a = 0) :
    Function.Injective (ch.toIntLinearMap.liftBaseChange ℚ) :=
  injective_liftBaseChange_of_torsion ch fun a ha =>
    hsep a (exists_zsmul_mem_coherentKZeroFiltration_of_apply_eq_zero ch h1 h2 ha)

/-- Under conditions (1) and (2), `ch` becomes injective after tensoring the source with `𝐐`,
provided `δ_{X/S}` is bounded below: an element of `𝐐 ⊗ K'₀(X)` is `s⁻¹ ⊗ a` for an integer
`s ≠ 0`, and an element `a` with `ch(a) = 0` is torsion. -/
theorem injective_liftBaseChange (h1 : IsDimensionTriangular C f ch)
    (h2 : IsDiagonalOnIntegral C f ch)
    (lo : ℤ) (hlo : ∀ x : X, lo ≤ relativeDimension C.dimensionFunction f x) :
    Function.Injective (ch.toIntLinearMap.liftBaseChange ℚ) :=
  injective_liftBaseChange_of_torsion ch (exists_zsmul_eq_zero_of_apply_eq_zero ch h1 h2 lo hlo)

/-- **Stacks 0FEW, from conditions (1) and (2).** For a homomorphism `ch : K'₀(X) ⟶ CH_*(X) ⊗ 𝐐`
satisfying the two conditions to which the proof of Proposition 42.57.1 reduces, `ch` induces an
isomorphism `K'₀(X) ⊗ 𝐐 ≅ CH_*(X) ⊗ 𝐐`, provided `δ_{X/S}` is bounded below. -/
theorem bijective_liftBaseChange (h1 : IsDimensionTriangular C f ch)
    (h2 : IsDiagonalOnIntegral C f ch)
    (lo : ℤ) (hlo : ∀ x : X, lo ≤ relativeDimension C.dimensionFunction f x) :
    Function.Bijective (ch.toIntLinearMap.liftBaseChange ℚ) :=
  ⟨injective_liftBaseChange ch h1 h2 lo hlo, surjective_liftBaseChange ch h1 h2 lo hlo⟩

/-! ### Surjectivity at the source's hypotheses, by Noetherian induction -/

variable (C f) in
/-- The class `1 ⊗ [Z_x] ∈ CH_*(X) ⊗ 𝐐` of the integral closed subscheme `Z_x` attached to a point
`x`, in the degree `δ_{X/S}(x)` of its delta-dimension. -/
def integralComponentRationalClass (x : X) :
    DirectSum ℤ fun j => TensorProduct ℤ ℚ (chowGroup C f j) :=
  DirectSum.of (fun j => TensorProduct ℤ ℚ (chowGroup C f j))
    (relativeDimension C.dimensionFunction f x)
    ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk' (rationalEquivalences C f _)
      (cycleAssociatedToClosedSubscheme C f (integralComponentAt x).subschemeι _))

variable (C f) in
/-- **Conditions (1) and (2) of the proof of Stacks 0FEW, in the form the proof establishes
them.** For every integral closed subscheme `Z = Z_x` of `X`, the image of `[𝒪_Z]` is `[Z]` plus a
rational combination of the classes of integral closed subschemes of `Z` other than `Z`. The
source obtains this from Lemma 42.50.8 (Stacks 0FB7), which puts the image of `[𝒪_Z]` in the image
of `CH_*(Z) ⟶ CH_*(X)`, and from the computation of its degree `k` part. -/
def HasLeadingTermOnIntegral
    (ch : CoherentKZero X →+ DirectSum ℤ fun j => TensorProduct ℤ ℚ (chowGroup C f j)) : Prop :=
  ∀ x : X, ch (KZero.mk _ (integralComponentDimLE C f _ x rfl).obj) -
      integralComponentRationalClass C f x ∈
    Submodule.span ℚ (integralComponentRationalClass C f '' (closure {x} \ {x}))

/-- On the quasi-compact `X`, `CH_*(X) ⊗ 𝐐` is spanned over `𝐐` by the classes of the integral
closed subschemes. -/
theorem span_range_integralComponentRationalClass :
    Submodule.span ℚ (Set.range (integralComponentRationalClass C f)) = ⊤ := by
  set S := Submodule.span ℚ (Set.range (integralComponentRationalClass C f))
  have hdeg : ∀ (j : ℤ) (α : chowGroup C f j),
      DirectSum.of (fun j => TensorProduct ℤ ℚ (chowGroup C f j)) j ((1 : ℚ) ⊗ₜ[ℤ] α) ∈ S := by
    intro j α
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C f j) α
    let φ : CycleGroup C f j →+ (DirectSum ℤ fun j => TensorProduct ℤ ℚ (chowGroup C f j)) ⧸ S :=
      (S.mkQ.toAddMonoidHom).comp
        ((DirectSum.of (fun j => TensorProduct ℤ ℚ (chowGroup C f j)) j).comp
        ((TensorProduct.mk ℤ ℚ (chowGroup C f j) 1).toAddMonoidHom.comp
          (QuotientAddGroup.mk' (rationalEquivalences C f j))))
    have hφ : φ = 0 := cycleGroup_hom_ext C f j fun x hx => by
      subst hx
      change S.mkQ (integralComponentRationalClass C f x) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero S).1 (DFunLike.congr_fun hφ c)
  refine eq_top_iff.2 fun v _ => ?_
  clear_value S
  clear ‹v ∈ ⊤›
  induction v using DirectSum.induction_on with
  | zero => exact S.zero_mem
  | of j m =>
    induction m using TensorProduct.inductionOn with
    | tmul q α =>
      have h := S.smul_mem q (hdeg j α)
      rwa [← DirectSum.of_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
    | add a b ha hb => rw [map_add]; exact S.add_mem ha hb
  | add a b ha hb => exact S.add_mem ha hb

/-- **Surjectivity in Stacks 0FEW, at the source's hypotheses.** A homomorphism
`ch : K'₀(X) ⟶ CH_*(X) ⊗ 𝐐` satisfying `Stacks.Chow.HasLeadingTermOnIntegral` becomes surjective
after tensoring the source with `𝐐`. No bound on `δ_{X/S}` is needed: the class of an integral
closed subscheme `Z_x` is the image of `[𝒪_{Z_x}]` minus classes of integral closed subschemes
whose closures are strictly smaller, and the closed subsets of the Noetherian space `X` satisfy
the descending chain condition. -/
theorem surjective_liftBaseChange_of_hasLeadingTermOnIntegral
    (h : HasLeadingTermOnIntegral C f ch) :
    Function.Surjective (ch.toIntLinearMap.liftBaseChange ℚ) := by
  set Θ := ch.toIntLinearMap.liftBaseChange ℚ with hΘ
  have hch : ∀ z, ch z ∈ LinearMap.range Θ := fun z =>
    ⟨(1 : ℚ) ⊗ₜ[ℤ] z, by rw [hΘ, LinearMap.liftBaseChange_tmul, one_smul]; rfl⟩
  let c : X → TopologicalSpace.Closeds X := fun x => ⟨closure {x}, isClosed_closure⟩
  have key : ∀ x : X, integralComponentRationalClass C f x ∈ LinearMap.range Θ := by
    intro x
    induction x using (InvImage.wf c wellFounded_lt).induction with
    | _ x ih =>
      have hspan : Submodule.span ℚ (integralComponentRationalClass C f '' (closure {x} \ {x})) ≤
          LinearMap.range Θ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨y, ⟨hy, hyx⟩, rfl⟩
        refine ih y (lt_of_le_of_ne ?_ fun heq => hyx ?_)
        · change closure {y} ⊆ closure {x}
          exact closure_minimal (Set.singleton_subset_iff.2 hy) isClosed_closure
        · have hxy : x ∈ closure {y} := by
            have := congrArg (fun T : TopologicalSpace.Closeds X => (T : Set X)) heq
            change closure {y} = closure {x} at this
            rw [this]
            exact subset_closure rfl
          exact ((specializes_iff_mem_closure.2 hy).antisymm
            (specializes_iff_mem_closure.2 hxy)).eq.symm
      have hsub := (LinearMap.range Θ).sub_mem
        (hch (KZero.mk _ (integralComponentDimLE C f _ x rfl).obj)) (hspan (h x))
      rwa [sub_sub_cancel] at hsub
  rw [← LinearMap.range_eq_top, eq_top_iff,
    ← span_range_integralComponentRationalClass (C := C) (f := f)]
  exact Submodule.span_le.2 (Set.range_subset_iff.2 key)

end Stacks.Chow

end
