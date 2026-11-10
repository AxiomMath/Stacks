module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CapFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.RestrictPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ChowHomologyCoherentKZeroBijective
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.RationalEquivalenceFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.Codimension.CohenMacaulayCase
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ProductOfPuncturedSchemes
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.WideLayerClopenDecomposition
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.OpenImmersionRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.Intersection.CohenMacaulayIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProductRegularImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropApplications
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeCurveDimension
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The codimension grading of the rational Chow group

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a
Noetherian scheme locally of finite type over `S`. Besides the grading of
`CH_*(X) ⊗ 𝐐 = ⨁_k CH_k(X) ⊗ 𝐐` by delta-dimension there is, when `X` is Cohen–Macaulay, a
grading by codimension (Stacks, Section 0FE2): the codimension of an integral closed subscheme
`Z ⊆ X` with generic point `x` is the dimension of the local ring `𝒪_{X,x}`, and
`CH^i(X) ⊗ 𝐐` is spanned by the classes of the `Z` of codimension `i`.

That this is a grading rests on Lemma 0FE3. On a Cohen–Macaulay scheme `x ↦ -dim 𝒪_{X,x}` is
a dimension function (Stacks 0F91), so `δ + codim` is locally constant (Stacks 02IB). Its fibres
`X_n` are open and closed, and the source's `CH^i(X) = ⨁_n CH_{n-i}(X_n)` is realized here by
the projections of `CH_k(X)` onto the pieces `X_{k+i}`: restriction to the piece followed by
pushforward along its inclusion, which is proper as the piece is closed. These projections fix
the class of an integral closed subscheme of codimension `i` and kill those of any other
codimension, which gives the independence of the codimension submodules; they span because on
the quasi-compact `X` a cycle is a finite sum of prime cycles.

Two compatibilities of the grading are proved. The fundamental class `[X]` lies in codimension
zero (Remark 0FE4), its cycle being supported on generic points. Capping with `c ∈ A^p(X)` raises
the codimension by `p` (Section 0FE2, item (4)): for `Z = \overline{\{x\}}` with inclusion `i`,
`c ∩ [Z] = i_*(c ∩ [Z])` by the proper-pushforward axiom of bivariant classes (Stacks 0B76 (1)),
so `c ∩ [Z]` is a combination of classes `[Z_y]` with `y ∈ Z` and `δ(y) = δ(x) - p`; and since
`δ + codim` is constant on the irreducible, hence connected, set `Z`, such `y` have codimension
`codim(x) + p`.

## Main definitions

* `Stacks.Chow.clopenChowProjection` — the projection of `CH_k(X)` onto an open and closed
  subscheme.
* `Stacks.Chow.codimensionChowSubmodule` — `CH^i(X) ⊗ 𝐐 ⊆ CH_*(X) ⊗ 𝐐`.
* `Stacks.Chow.codimensionProjection` — the projection of `CH_*(X) ⊗ 𝐐` onto `CH^i(X) ⊗ 𝐐`, for
  `X` Cohen–Macaulay.

## Main results

* `Stacks.Chow.isInternal_codimensionChowSubmodule` — `CH_*(X) ⊗ 𝐐 = ⨁_i CH^i(X) ⊗ 𝐐` for `X`
  Cohen–Macaulay; `Stacks.Chow.isInternal_codimensionChowSubmodule_of_isRegular` for `X` regular.
* `Stacks.Chow.directSumRight_one_tmul_totalFundamentalClass_mem_codimensionChowSubmodule_zero` —
  `[X] ∈ CH^0(X) ⊗ 𝐐`.
* `Stacks.Chow.chowCohomologyCap_mk_integralComponentAt_mem_closure` — `c ∩ [Z_x]` is a
  combination of the `[Z_y]`, `y ∈ \overline{\{x\}}`, `δ(y) = δ(x) - p`.
* `Stacks.Chow.ringKrullDim_stalk_eq_add_of_mem_closure` — on a Cohen–Macaulay `X` such `y` have
  codimension `codim(x) + p`.
* `Stacks.Chow.of_baseChange_chowCohomologyCap_mem_codimensionChowSubmodule`,
  `Stacks.Chow.apply_mem_codimensionChowSubmodule_add` — capping with a class of degree `p` maps
  `CH^i(X) ⊗ 𝐐` into `CH^{i+p}(X) ⊗ 𝐐`.

## Implementation notes

The source defines `CH^p(X) = ∏_n CH_{n-p}(X_n)` as an abstract group. Here `CH^i(X) ⊗ 𝐐` is a
submodule of `CH_*(X) ⊗ 𝐐`, so that the decomposition `⨁_p CH^p(X) = ⨁_k CH_k(X)` of the source
(for `X` quasi-compact) becomes the statement that these submodules form an internal direct sum;
no choice of the decomposition `X = ∐ X_n` enters the definition. The cap product enters through
`Stacks.Chow.chowCohomologyCap`, degree by degree, and the rational statements are phrased for any
`𝐐`-linear endomorphism acting on each degree as a rational multiple of it.

## References

* [Stacks Project, Section 0FE2](https://stacks.math.columbia.edu/tag/0FE2)
* [Stacks Project, Tag 0FE3](https://stacks.math.columbia.edu/tag/0FE3)
* [Stacks Project, Tag 0FE4](https://stacks.math.columbia.edu/tag/0FE4)
* [Stacks Project, Tag 0FEX](https://stacks.math.columbia.edu/tag/0FEX)
* [Stacks Project, Tag 0F91](https://stacks.math.columbia.edu/tag/0F91)
* [Stacks Project, Tag 02IB](https://stacks.math.columbia.edu/tag/02IB)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Cycles of finite support as combinations of prime cycles -/

section PrimeCycles

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q]

/-- On a quasi-compact scheme a `k`-cycle is the finite sum `∑ n_x [Z_x]` over the points `x` of
its support, `Z_x` being the integral closed subscheme with generic point `x`. -/
theorem eq_sum_cycleAssociatedToClosedSubscheme_integralComponentAt [CompactSpace X] {k : ℤ}
    (α : CycleGroup C q k) :
    α = ∑ x ∈ (finite_support_cycleGroup C q k α).toFinset,
      α.1 x • cycleAssociatedToClosedSubscheme C q (integralComponentAt x).subschemeι k := by
  classical
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  change cycleCoeffHom C q k y α = cycleCoeffHom C q k y (∑ x ∈ _, _)
  rw [map_sum]
  simp only [map_zsmul, cycleCoeffHom_apply, smul_eq_mul]
  by_cases hy : α.1 y = 0
  · rw [hy, eq_comm]
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    have hxy : y ≠ x := fun h ↦ (Set.Finite.mem_toFinset _).1 hx (h ▸ hy)
    rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C q k x hxy, mul_zero]
  · rw [Finset.sum_eq_single_of_mem y ((Set.Finite.mem_toFinset _).2 hy) fun x _ hxy ↦ by
      rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C q k x (Ne.symm hxy),
        mul_zero],
      cycleAssociatedToClosedSubscheme_integralComponentAt_self C q y
      (schemeDeltaDimension_cycleSupportIndex α ⟨y, hy⟩), mul_one]

/-- On a quasi-compact scheme the class of a `k`-cycle lies in the subgroup of `CH_k(X)` generated
by the classes `[Z_x]` of the points `x` of its support. -/
theorem mk_mem_closure_integralComponentAt [CompactSpace X] {k : ℤ} (α : CycleGroup C q k) :
    QuotientAddGroup.mk' (rationalEquivalences C q k) α ∈ AddSubgroup.closure
      ((fun x ↦ QuotientAddGroup.mk' (rationalEquivalences C q k)
        (cycleAssociatedToClosedSubscheme C q (integralComponentAt x).subschemeι k)) ''
          Function.support α.1) := by
  rw [congrArg (QuotientAddGroup.mk' (rationalEquivalences C q k))
    (eq_sum_cycleAssociatedToClosedSubscheme_integralComponentAt C q α), map_sum]
  refine sum_mem fun x hx ↦ ?_
  rw [map_zsmul]
  exact zsmul_mem (AddSubgroup.subset_closure
    (Set.mem_image_of_mem _ ((Set.Finite.mem_toFinset _).1 hx))) _

/-- The class `1 ⊗ [Z_x]` in degree `k = δ(x)` is `Stacks.Chow.integralComponentRationalClass`. -/
theorem of_one_tmul_mk_eq_integralComponentRationalClass {k : ℤ} (x : X)
    (hx : relativeDimension C.dimensionFunction q x = k) :
    DirectSum.of (fun j ↦ TensorProduct ℤ ℚ (chowGroup C q j)) k
        ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk' (rationalEquivalences C q k)
          (cycleAssociatedToClosedSubscheme C q (integralComponentAt x).subschemeι k)) =
      integralComponentRationalClass C q x := by
  subst hx
  rfl

/-- A rational multiple of an element of the subgroup of `CH_k(X)` generated by the classes
`[Z_x]`, `x ∈ S`, all of delta-dimension `k`, lies in the `𝐐`-span of the classes `1 ⊗ [Z_x]`,
`x ∈ S`, in `CH_*(X) ⊗ 𝐐`. -/
theorem of_tmul_mem_span_integralComponentRationalClass {k : ℤ} (r : ℚ)
    {S : Set X} (hS : ∀ x ∈ S, relativeDimension C.dimensionFunction q x = k)
    {β : chowGroup C q k}
    (hβ : β ∈ AddSubgroup.closure ((fun x ↦ QuotientAddGroup.mk' (rationalEquivalences C q k)
        (cycleAssociatedToClosedSubscheme C q (integralComponentAt x).subschemeι k)) '' S)) :
    DirectSum.of (fun j ↦ TensorProduct ℤ ℚ (chowGroup C q j)) k (r ⊗ₜ[ℤ] β) ∈
      Submodule.span ℚ (integralComponentRationalClass C q '' S) := by
  let ψ : chowGroup C q k →+ DirectSum ℤ fun j ↦ TensorProduct ℤ ℚ (chowGroup C q j) :=
    (DirectSum.of (fun j ↦ TensorProduct ℤ ℚ (chowGroup C q j)) k).comp
      (TensorProduct.mk ℤ ℚ (chowGroup C q k) r).toAddMonoidHom
  refine (AddSubgroup.closure_le
    ((Submodule.span ℚ (integralComponentRationalClass C q '' S)).toAddSubgroup.comap ψ)).2 ?_ hβ
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup]
  simp only [ψ, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
  rw [← mul_one r, ← smul_eq_mul, ← TensorProduct.smul_tmul', DirectSum.of_smul,
    of_one_tmul_mk_eq_integralComponentRationalClass C q x (hS x hx)]
  exact Submodule.smul_mem _ r (Submodule.subset_span ⟨x, hx, rfl⟩)

end PrimeCycles

/-! ### Projecting onto an open and closed subscheme -/

section ClopenProjection

/-- The inclusion of an open subscheme whose underlying set is closed is proper: it is a closed
immersion. -/
theorem isProper_opensι_of_isClosed {X : Scheme.{u}} (V : X.Opens) (hV : IsClosed (V : Set X)) :
    IsProper V.ι := by
  have : IsClosedImmersion V.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rwa [Scheme.Opens.range_ι])
  infer_instance

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q]
  (V : X.Opens) [IsProper V.ι]

open Classical in
/-- Restricting a cycle to an open and closed subscheme `V` and pushing it forward again keeps
the coefficients at the points of `V` and kills those outside `V`. -/
theorem properPushforward_cycleGroupOpensRestrict_apply (k : ℤ) (c : CycleGroup C q k) (y : X) :
    (properPushforward C (V.ι ≫ q) q V.ι rfl k (cycleGroupOpensRestrict C q V k c)).1 y =
      if y ∈ V then c.1 y else 0 := by
  split_ifs with hy
  · exact properPushforward_opensRestrict_apply_self C q V k c ⟨y, hy⟩
  · have hVc : IsOpen (V : Set X)ᶜ := by
      have h := V.ι.isClosedMap.isClosed_range
      rw [Scheme.Opens.range_ι] at h
      exact h.isOpen_compl
    exact properPushforward_opensRestrict_apply_of_disjoint C q V ⟨_, hVc⟩
      (Opens.coe_disjoint.1 disjoint_compl_right) k c ⟨y, hy⟩

/-- **The projection of `CH_k(X)` onto an open and closed subscheme `V`**: restriction to `V`
followed by pushforward along the inclusion `V ⟶ X`, which is proper because `V` is closed. On
the class of an integral closed subscheme `Z` it is `[Z]` if `Z ⊆ V` and `0` otherwise
(`Stacks.Chow.clopenChowProjection_mk_integralComponentAt`). -/
def clopenChowProjection (k : ℤ) : chowGroup C q k →+ chowGroup C q k :=
  (properChowPushforward C (V.ι ≫ q) q V.ι rfl k
      (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ k)).comp
    (chowGroupOpensRestrict C q V k
      (flatPullbackFactorsThroughRationalEquivalence_of_opensι C q V k))

/-- On the class of a cycle, the projection onto `V` is the class of the pushforward of the
restriction to `V`. -/
theorem clopenChowProjection_mk (k : ℤ) (c : CycleGroup C q k) :
    clopenChowProjection C q V k (QuotientAddGroup.mk' (rationalEquivalences C q k) c) =
      QuotientAddGroup.mk' (rationalEquivalences C q k)
        (properPushforward C (V.ι ≫ q) q V.ι rfl k (cycleGroupOpensRestrict C q V k c)) :=
  rfl

open Classical in
/-- The projection onto an open and closed subscheme `V` fixes the class of an integral closed
subscheme contained in `V` and kills one disjoint from it. -/
theorem clopenChowProjection_mk_integralComponentAt (k : ℤ) (x : X) :
    clopenChowProjection C q V k (QuotientAddGroup.mk' (rationalEquivalences C q k)
        (cycleAssociatedToClosedSubscheme C q (integralComponentAt x).subschemeι k)) =
      if x ∈ V then QuotientAddGroup.mk' (rationalEquivalences C q k)
        (cycleAssociatedToClosedSubscheme C q (integralComponentAt x).subschemeι k) else 0 := by
  rw [clopenChowProjection_mk]
  have hne : ∀ y, y ≠ x →
      (cycleAssociatedToClosedSubscheme C q (integralComponentAt x).subschemeι k).1 y = 0 :=
    fun y hy ↦ cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C q k x hy
  split_ifs with hx
  on_goal 2 => rw [← map_zero (QuotientAddGroup.mk' (rationalEquivalences C q k))]
  all_goals
    congr 1
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
    rw [properPushforward_cycleGroupOpensRestrict_apply]
    split_ifs with hy
  · rfl
  · exact (hne y fun h ↦ hy (h ▸ hx)).symm
  · exact hne y fun h ↦ hx (h ▸ hy)
  · rfl

end ClopenProjection

/-! ### The codimension of a point -/

section Codimension

variable {X : Scheme.{u}}

/-- At a point whose local ring has dimension `i`, the negative local ring dimension is `-i`. -/
theorem negativeLocalRingDimension_eq_neg {x : X} {i : ℕ}
    (hx : ringKrullDim (X.presheaf.stalk x) = i) : negativeLocalRingDimension X x = -i := by
  simp [negativeLocalRingDimension, hx]

end Codimension

/-! ### The codimension submodules -/

section Grading

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The δ-dimension plus the codimension is locally constant on a Cohen–Macaulay scheme.** The
relative dimension `δ_{X/S}` and `x ↦ -dim 𝒪_{X,x}` are both dimension functions (the latter by
Stacks 0F91), so their difference is locally constant by Stacks 02IB. -/
theorem isLocallyConstant_relativeDimension_sub_negativeLocalRingDimension
    (hX : IsCohenMacaulay X) :
    IsLocallyConstant fun x ↦
      relativeDimension C.dimensionFunction sX x - negativeLocalRingDimension X x := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  obtain ⟨d, hd⟩ :=
    relativeDimension_isDimensionFunction C.isUniversallyCatenary C.dimensionFunction sX
  obtain ⟨d', hd'⟩ := IsCohenMacaulay.negativeLocalRingDimension_isDimensionFunction hX
  have h := DimensionFunction.isLocallyConstant_sub
    (isLocallyNoetherianSpace_of_isLocallyNoetherian X) d d'
  convert h using 2 with x
  rw [hd, hd']

variable [IsNoetherian X]

/-- **The codimension `i` part `CH^i(X) ⊗ 𝐐` of `CH_*(X) ⊗ 𝐐`**: the `𝐐`-span of the classes
`1 ⊗ [Z]` of the integral closed subschemes `Z ⊆ X` of codimension `i`. The codimension of `Z`,
with generic point `x`, is the dimension of the local ring `𝒪_{X,x}`. -/
def codimensionChowSubmodule (i : ℕ) :
    Submodule ℚ (DirectSum ℤ fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)) :=
  Submodule.span ℚ
    (integralComponentRationalClass C sX '' {x | ringKrullDim (X.presheaf.stalk x) = i})

omit [AlgebraicGeometry.IsNoetherian X] in
variable {C sX} in
/-- The class of an integral closed subscheme of codimension `i` lies in `CH^i(X) ⊗ 𝐐`. -/
theorem integralComponentRationalClass_mem_codimensionChowSubmodule {x : X} {i : ℕ}
    (hx : ringKrullDim (X.presheaf.stalk x) = i) :
    integralComponentRationalClass C sX x ∈ codimensionChowSubmodule C sX i :=
  Submodule.subset_span ⟨x, hx, rfl⟩

/-- The codimension submodules span `CH_*(X) ⊗ 𝐐`. -/
theorem iSup_codimensionChowSubmodule : ⨆ i, codimensionChowSubmodule C sX i = ⊤ := by
  rw [eq_top_iff, ← span_range_integralComponentRationalClass (C := C) (f := sX),
    Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, hi⟩ := Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim
    (X.presheaf.stalk x)
  exact Submodule.mem_iSup_of_mem i (integralComponentRationalClass_mem_codimensionChowSubmodule hi)

/-- The open and closed subscheme where a locally constant integer-valued function takes the
value `n`. -/
def fibreOpens {φ : X → ℤ} (hφ : IsLocallyConstant φ) (n : ℤ) : X.Opens :=
  ⟨φ ⁻¹' {n}, hφ.isOpen_fiber n⟩

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The inclusion of a fibre of a locally constant function is proper, the fibre being closed. -/
theorem isProper_fibreOpens_ι {φ : X → ℤ} (hφ : IsLocallyConstant φ) (n : ℤ) :
    IsProper (fibreOpens hφ n).ι :=
  isProper_opensι_of_isClosed _ (hφ.isClosed_fiber n)

variable {sX} in
/-- **The projection of `CH_*(X) ⊗ 𝐐` onto `CH^i(X) ⊗ 𝐐`** for `X` Cohen–Macaulay. On the degree
`k` part it is the projection onto the open and closed subscheme where `δ + codim = k + i`. -/
def codimensionProjection (hX : IsCohenMacaulay X) (i : ℕ) :
    (DirectSum ℤ fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)) →ₗ[ℚ]
      DirectSum ℤ fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j) :=
  DirectSum.lmap fun k ↦
    haveI := isProper_fibreOpens_ι
      (isLocallyConstant_relativeDimension_sub_negativeLocalRingDimension C sX hX) (k + i)
    (clopenChowProjection C sX (fibreOpens
      (isLocallyConstant_relativeDimension_sub_negativeLocalRingDimension C sX hX)
        (k + i)) k).toIntLinearMap.baseChange ℚ

open Classical in
/-- The projection onto `CH^i(X) ⊗ 𝐐` fixes the class of an integral closed subscheme of
codimension `i` and kills the class of one of any other codimension. -/
theorem codimensionProjection_integralComponentRationalClass (hX : IsCohenMacaulay X) (i : ℕ)
    (x : X) :
    codimensionProjection C hX i (integralComponentRationalClass C sX x) =
      if ringKrullDim (X.presheaf.stalk x) = i then integralComponentRationalClass C sX x
      else 0 := by
  obtain ⟨j, hj⟩ := Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim
    (X.presheaf.stalk x)
  have hmem : x ∈ fibreOpens (isLocallyConstant_relativeDimension_sub_negativeLocalRingDimension
      C sX hX) (relativeDimension C.dimensionFunction sX x + i) ↔
      ringKrullDim (X.presheaf.stalk x) = i := by
    change relativeDimension C.dimensionFunction sX x - negativeLocalRingDimension X x =
      relativeDimension C.dimensionFunction sX x + i ↔ _
    rw [negativeLocalRingDimension_eq_neg hj, hj]
    refine ⟨fun h ↦ congrArg _ (by omega : j = i), fun h ↦ ?_⟩
    have : j = i := by exact_mod_cast h
    omega
  rw [integralComponentRationalClass, ← DirectSum.lof_eq_of ℚ, codimensionProjection,
    DirectSum.lmap_lof, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
    clopenChowProjection_mk_integralComponentAt]
  by_cases hx : ringKrullDim (X.presheaf.stalk x) = i
  · rw [ite_eq_left (hmem.2 hx), ite_eq_left hx, DirectSum.lof_eq_of]
  · rw [ite_eq_right (fun h ↦ hx (hmem.1 h)), ite_eq_right hx, TensorProduct.tmul_zero, map_zero]

/-- The projection onto `CH^i(X) ⊗ 𝐐` is the identity on `CH^i(X) ⊗ 𝐐`. -/
theorem codimensionProjection_apply_of_mem (hX : IsCohenMacaulay X) {i : ℕ}
    {v : DirectSum ℤ fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)}
    (hv : v ∈ codimensionChowSubmodule C sX i) : codimensionProjection C hX i v = v := by
  refine (Submodule.span_le (p := LinearMap.eqLocus (codimensionProjection C hX i)
    LinearMap.id)).2 ?_ hv
  rintro _ ⟨x, hx, rfl⟩
  change codimensionProjection C hX i _ = _
  rw [codimensionProjection_integralComponentRationalClass, ite_eq_left (Set.mem_ofPred_eq.mp hx)]
  rfl

/-- The projection onto `CH^i(X) ⊗ 𝐐` kills `CH^j(X) ⊗ 𝐐` for `j ≠ i`. -/
theorem codimensionProjection_apply_of_mem_of_ne (hX : IsCohenMacaulay X) {i j : ℕ}
    (hji : j ≠ i) {v : DirectSum ℤ fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)}
    (hv : v ∈ codimensionChowSubmodule C sX j) : codimensionProjection C hX i v = 0 := by
  refine (Submodule.span_le (p := LinearMap.ker (codimensionProjection C hX i))).2 ?_ hv
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, codimensionProjection_integralComponentRationalClass,
    ite_eq_right]
  rw [Set.mem_ofPred_eq.mp hx]
  exact fun h ↦ hji (by exact_mod_cast h)

/-- **Stacks 0FE2 for rational Chow groups: `CH_*(X) ⊗ 𝐐 = ⨁_i CH^i(X) ⊗ 𝐐`** for `X`
Cohen–Macaulay and Noetherian. The codimension submodules span by
`Stacks.Chow.iSup_codimensionChowSubmodule`, and they are independent because the projection
onto `CH^i(X) ⊗ 𝐐` is the identity on it and kills the others. -/
theorem isInternal_codimensionChowSubmodule (hX : IsCohenMacaulay X) :
    DirectSum.IsInternal (codimensionChowSubmodule C sX) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_
    (iSup_codimensionChowSubmodule C sX)
  intro i
  rw [Submodule.disjoint_def]
  intro v hv hv'
  have hker : (⨆ (j) (_ : j ≠ i), codimensionChowSubmodule C sX j) ≤
      LinearMap.ker (codimensionProjection C hX i) :=
    iSup₂_le fun j hji w hw ↦ codimensionProjection_apply_of_mem_of_ne C sX hX hji hw
  rw [← codimensionProjection_apply_of_mem C sX hX hv]
  exact hker hv'

/-- `CH_*(X) ⊗ 𝐐 = ⨁_i CH^i(X) ⊗ 𝐐` for `X` regular and Noetherian, a regular scheme being
Cohen–Macaulay. -/
theorem isInternal_codimensionChowSubmodule_of_isRegular (hX : IsRegular X) :
    DirectSum.IsInternal (codimensionChowSubmodule C sX) :=
  isInternal_codimensionChowSubmodule C sX (isCohenMacaulay_of_isRegular hX)

end Grading

/-! ### The fundamental class lies in codimension zero -/

section FundamentalClass

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [IsNoetherian X]

/-- **The fundamental class lies in codimension zero (Stacks 0FE4).** The class `1 ⊗ [X]` of the
fundamental class `[X] = ∑_n [X]_n` lies in `CH^0(X) ⊗ 𝐐`: the cycle `[X]_n` is supported on
generic points of irreducible components of `X`, whose local rings have dimension zero. -/
theorem directSumRight_one_tmul_totalFundamentalClass_mem_codimensionChowSubmodule_zero :
    TensorProduct.directSumRight ℤ ℚ ℚ (fun j ↦ chowGroup C sX j)
        ((1 : ℚ) ⊗ₜ[ℤ] totalFundamentalClass C sX) ∈ codimensionChowSubmodule C sX 0 := by
  rw [totalFundamentalClass, TensorProduct.tmul_sum, map_sum]
  refine Submodule.sum_mem _ fun n _ ↦ ?_
  rw [← DirectSum.lof_eq_of ℤ, TensorProduct.directSumRight_tmul_lof, DirectSum.lof_eq_of]
  have hsupp : ∀ x ∈ Function.support (fundamentalCycle C sX n).1,
      relativeDimension C.dimensionFunction sX x = n := fun x hx ↦
    (mem_cyclesOfDimension_iff_forall_point C sX n _).1 (fundamentalCycle C sX n).2 x hx
  refine Submodule.span_mono (Set.image_mono fun x hx ↦ ?_)
    (of_tmul_mem_span_integralComponentRationalClass C sX 1 hsupp
      (mk_mem_closure_integralComponentAt C sX (fundamentalCycle C sX n)))
  by_contra h
  refine hx (cycleAssociatedToClosedSubscheme_apply_eq_zero C sX (𝟙 X) n x ?_)
  rintro ⟨ξ, hξ, -⟩
  refine h ?_
  rw [Set.mem_ofPred_eq, ← hξ]
  exact ringKrullDim_stalk_eq_zero_of_mem_genericPoints ξ

end FundamentalClass

/-! ### Capping with a Chow cohomology class raises the codimension -/

section Cap

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- On a quasi-compact `X`, a class pushed forward along a proper morphism `g : W ⟶ X` lies in the
subgroup of `CH_k(X)` generated by the classes `[Z_y]` of the points `y` of delta-dimension `k` in
the image of `g`. -/
theorem properChowPushforward_mem_closure_integralComponentAt [CompactSpace X] {W : Scheme.{u}}
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (g : W ⟶ X) [IsProper g] (hg : g ≫ sX = sW)
    (k : ℤ) (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sW sX g hg k)
    (β : chowGroup C sW k) :
    properChowPushforward C sW sX g hg k hfac β ∈ AddSubgroup.closure
      ((fun y ↦ QuotientAddGroup.mk' (rationalEquivalences C sX k)
        (cycleAssociatedToClosedSubscheme C sX (integralComponentAt y).subschemeι k)) ''
          {y | y ∈ Set.range g.base ∧ relativeDimension C.dimensionFunction sX y = k}) := by
  induction β using QuotientAddGroup.induction_on with
  | H b =>
    change properChowPushforward C sW sX g hg k hfac
      (QuotientAddGroup.mk' (rationalEquivalences C sW k) b) ∈ _
    rw [properChowPushforward_mk]
    refine AddSubgroup.closure_mono (Set.image_mono ?_)
      (mk_mem_closure_integralComponentAt C sX (properPushforward C sW sX g hg k b))
    intro y hy
    refine ⟨?_, ?_⟩
    · by_contra h
      exact hy (properPushforward_apply_eq_zero_of_notMem_range C sW sX g hg k b y h)
    · exact (mem_cyclesOfDimension_iff_forall_point C sX k _).1
        (properPushforward C sW sX g hg k b).2 y hy

variable (G : GysinSystem C)

/-- **Capping lowers the delta-dimension inside the closure of a point.** For `c ∈ A^p(X)` and
the integral closed subscheme `Z = \overline{\{x\}}` of delta-dimension `k`, the class
`c ∩ [Z] ∈ CH_{k-p}(X)` lies in the subgroup generated by the classes `[Z_y]` of the points `y`
of `Z` of delta-dimension `k - p`. Indeed `[Z] = i_*[Z]` for the inclusion `i : Z ⟶ X`, so
`c ∩ [Z] = i_*(c ∩ [Z])` by the proper-pushforward axiom of bivariant classes (Stacks 0B76 (1)),
and a class pushed forward from `Z` is a combination of classes of integral closed subschemes
of `Z`. -/
theorem chowCohomologyCap_mk_integralComponentAt_mem_closure [CompactSpace X] (p : ℤ)
    (c : chowCohomologyComponent C G sX p) (k : ℤ) (x : X) :
    chowCohomologyCap C G sX p c k (QuotientAddGroup.mk' (rationalEquivalences C sX k)
        (cycleAssociatedToClosedSubscheme C sX (integralComponentAt x).subschemeι k)) ∈
      AddSubgroup.closure ((fun y ↦ QuotientAddGroup.mk' (rationalEquivalences C sX (k - p))
        (cycleAssociatedToClosedSubscheme C sX (integralComponentAt y).subschemeι (k - p))) ''
          {y | y ∈ closure {x} ∧ relativeDimension C.dimensionFunction sX y = k - p}) := by
  set i := (integralComponentAt x).subschemeι
  -- the cartesian square over the inclusion `i`
  let h' : pullback (𝟙 X) (i ≫ 𝟙 X) ⟶ pullback (𝟙 X) (𝟙 X) :=
    pullback.lift (pullback.fst (𝟙 X) (i ≫ 𝟙 X)) (pullback.snd (𝟙 X) (i ≫ 𝟙 X) ≫ i)
      (by rw [Category.assoc, ← pullback.condition])
  have hfst : h' ≫ pullback.fst (𝟙 X) (𝟙 X) = pullback.fst (𝟙 X) (i ≫ 𝟙 X) :=
    pullback.lift_fst _ _ _
  have hsnd : h' ≫ pullback.snd (𝟙 X) (𝟙 X) = pullback.snd (𝟙 X) (i ≫ 𝟙 X) ≫ i :=
    pullback.lift_snd _ _ _
  have sq : IsPullback (pullback.snd (𝟙 X) (i ≫ 𝟙 X)) h' i (pullback.snd (𝟙 X) (𝟙 X)) :=
    IsPullback.of_horiz_isIso ⟨hsnd.symm⟩
  have : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  -- `[Z] = i_*[Z]`
  have hpush : chowGroupCongr C (Category.id_comp sX).symm k
      (QuotientAddGroup.mk' (rationalEquivalences C sX k)
        (cycleAssociatedToClosedSubscheme C sX i k)) =
      properChowPushforward C ((i ≫ 𝟙 X) ≫ sX) (𝟙 X ≫ sX) i (by simp) k
        (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ k)
        (QuotientAddGroup.mk' (rationalEquivalences C ((i ≫ 𝟙 X) ≫ sX) k)
          (cycleAssociatedToClosedSubscheme C ((i ≫ 𝟙 X) ≫ sX) (𝟙 _) k)) := by
    rw [properChowPushforward_mk, properPushforward_cycleAssociatedToClosedSubscheme_id]
    exact Intersection.chowGroupCongr_mk_cycleAssociatedToClosedSubscheme _ i k
  have hcap : chowCohomologyCap C G sX p c k (QuotientAddGroup.mk'
      (rationalEquivalences C sX k) (cycleAssociatedToClosedSubscheme C sX i k)) =
      properChowPushforward C (pullback.fst (𝟙 X) (i ≫ 𝟙 X) ≫ sX) sX
        (h' ≫ pullback.fst (𝟙 X) (𝟙 X)) (by rw [Category.assoc, ← Category.assoc, hfst]) (k - p)
        (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)
        (c.cap (i ≫ 𝟙 X) k (QuotientAddGroup.mk' (rationalEquivalences C ((i ≫ 𝟙 X) ≫ sX) k)
          (cycleAssociatedToClosedSubscheme C ((i ≫ 𝟙 X) ≫ sX) (𝟙 _) k))) := by
    simp only [chowCohomologyCap, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom, chowGroupEquivOfIso_apply]
    rw [hpush, c.proper_naturality (𝟙 X) i h' sq hfst k _
      (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _), chowPushforwardOfIso,
      ← AddMonoidHom.comp_apply, properChowPushforward_comp]
  rw [hcap]
  refine AddSubgroup.closure_mono (Set.image_mono ?_)
    (properChowPushforward_mem_closure_integralComponentAt C sX _ _ _ (k - p) _ _)
  intro y hy
  refine ⟨?_, hy.2⟩
  obtain ⟨w, hw⟩ := hy.1
  have hcomm : (h' ≫ pullback.fst (𝟙 X) (𝟙 X)) = pullback.snd (𝟙 X) (i ≫ 𝟙 X) ≫ i := by
    rw [hfst, ← Category.comp_id (pullback.fst (𝟙 X) (i ≫ 𝟙 X)), pullback.condition,
      Category.comp_id]
  rw [hcomm] at hw
  rw [← coe_support_integralComponentAt, ← Scheme.IdealSheafData.range_subschemeι, ← hw]
  exact ⟨_, rfl⟩

/-- **On a Cohen–Macaulay scheme codimension and delta-dimension add up along a closure.** If `y`
specializes `x` with `δ(y) = δ(x) - p`, then `codim(y) = codim(x) + p`: the function
`δ + codim` is locally constant, hence constant on the irreducible, so connected, closure of
`x`. -/
@[sga "6 X 1.5" "special case"]
theorem ringKrullDim_stalk_eq_add_of_mem_closure (hX : IsCohenMacaulay X) {x y : X}
    (hy : y ∈ closure {x}) {i p : ℕ} (hx : ringKrullDim (X.presheaf.stalk x) = i)
    (hδ : relativeDimension C.dimensionFunction sX y =
      relativeDimension C.dimensionFunction sX x - p) :
    ringKrullDim (X.presheaf.stalk y) = (i + p : ℕ) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hconst := (isLocallyConstant_relativeDimension_sub_negativeLocalRingDimension C sX
    hX).apply_eq_of_isPreconnected
    (isIrreducible_singleton (x := x)).closure.isConnected.isPreconnected hy
    (subset_closure rfl)
  obtain ⟨j, hj⟩ := Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim
    (X.presheaf.stalk y)
  simp only [negativeLocalRingDimension_eq_neg hj, negativeLocalRingDimension_eq_neg hx,
    hδ] at hconst
  rw [hj, show j = i + p by omega]

/-- **Capping the class of a codimension `i` subscheme with a class of degree `p` lands in
codimension `i + p`.** For `X` Cohen–Macaulay and Noetherian, `c ∈ A^p(X)` and `Z_x` of
codimension `i` and delta-dimension `k`, the class `r ⊗ (c ∩ [Z_x])` in degree `k - p` lies in
`CH^{i+p}(X) ⊗ 𝐐`. -/
theorem of_tmul_chowCohomologyCap_mem_codimensionChowSubmodule [IsNoetherian X]
    (hX : IsCohenMacaulay X) (p : ℕ) (c : chowCohomologyComponent C G sX p) (r : ℚ) {x : X}
    {i : ℕ} (hx : ringKrullDim (X.presheaf.stalk x) = i) {k : ℤ}
    (hk : relativeDimension C.dimensionFunction sX x = k) :
    DirectSum.of (fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)) (k - p)
        (r ⊗ₜ[ℤ] chowCohomologyCap C G sX p c k (QuotientAddGroup.mk'
          (rationalEquivalences C sX k)
          (cycleAssociatedToClosedSubscheme C sX (integralComponentAt x).subschemeι k))) ∈
      codimensionChowSubmodule C sX (i + p) := by
  subst hk
  have hS : ∀ y ∈ {y | y ∈ closure {x} ∧ relativeDimension C.dimensionFunction sX y =
      relativeDimension C.dimensionFunction sX x - p},
      relativeDimension C.dimensionFunction sX y =
        relativeDimension C.dimensionFunction sX x - p := fun y hy ↦ hy.2
  refine (Submodule.span_le (p := codimensionChowSubmodule C sX (i + p))).2 ?_
    (of_tmul_mem_span_integralComponentRationalClass C sX r hS
      (chowCohomologyCap_mk_integralComponentAt_mem_closure C sX G p c _ x))
  rintro _ ⟨y, hy, rfl⟩
  exact integralComponentRationalClass_mem_codimensionChowSubmodule
    (ringKrullDim_stalk_eq_add_of_mem_closure C sX hX hy.1 hx hy.2)

/-- **Capping with a class of degree `p` raises the codimension by `p`, degree by degree
(Stacks 0FE2 (4)).** For `X` Cohen–Macaulay and Noetherian and `c ∈ A^p(X)`, if
`v ∈ CH^i(X) ⊗ 𝐐` then the image of its degree `k` part under
`id ⊗ (c ∩ -) : CH_k(X) ⊗ 𝐐 ⟶ CH_{k-p}(X) ⊗ 𝐐` lies in `CH^{i+p}(X) ⊗ 𝐐`. -/
theorem of_baseChange_chowCohomologyCap_mem_codimensionChowSubmodule [IsNoetherian X]
    (hX : IsCohenMacaulay X) (p : ℕ) (c : chowCohomologyComponent C G sX p) {i : ℕ}
    {v : DirectSum ℤ fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)}
    (hv : v ∈ codimensionChowSubmodule C sX i) (k : ℤ) :
    DirectSum.of (fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)) (k - p)
        ((chowCohomologyCap C G sX p c k).toIntLinearMap.baseChange ℚ (v k)) ∈
      codimensionChowSubmodule C sX (i + p) := by
  let Φ : (DirectSum ℤ fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)) →ₗ[ℚ]
      DirectSum ℤ fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j) :=
    DirectSum.lof ℚ ℤ (fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)) (k - p) ∘ₗ
      (chowCohomologyCap C G sX p c k).toIntLinearMap.baseChange ℚ ∘ₗ
        DirectSum.component ℚ ℤ (fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)) k
  change Φ v ∈ _
  refine (Submodule.span_le (p := (codimensionChowSubmodule C sX (i + p)).comap Φ)).2 ?_ hv
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  by_cases hk : relativeDimension C.dimensionFunction sX x = k
  · rw [← of_one_tmul_mk_eq_integralComponentRationalClass C sX x hk]
    simp only [Φ, LinearMap.comp_apply, ← DirectSum.lof_eq_of ℚ, DirectSum.component.lof_self,
      LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap]
    rw [DirectSum.lof_eq_of]
    exact of_tmul_chowCohomologyCap_mem_codimensionChowSubmodule C sX G hX p c 1 hx hk
  · have h0 : DirectSum.component ℚ ℤ (fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)) k
        (integralComponentRationalClass C sX x) = 0 := by
      rw [← DirectSum.apply_eq_component, integralComponentRationalClass]
      exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm hk)
    simp only [Φ, LinearMap.comp_apply, h0, map_zero]
    exact zero_mem _

/-- **Capping with a class of degree `p` raises the codimension by `p` (Stacks 0FE2 (4)).** Let
`X` be Cohen–Macaulay and Noetherian and `c ∈ A^p(X)`. Any `𝐐`-linear endomorphism `L` of
`CH_*(X) ⊗ 𝐐` acting on each degree as `r ⊗ (c ∩ -) : CH_k(X) ⊗ 𝐐 ⟶ CH_{k-p}(X) ⊗ 𝐐` maps
`CH^i(X) ⊗ 𝐐` into `CH^{i+p}(X) ⊗ 𝐐`. -/
theorem apply_mem_codimensionChowSubmodule_add [IsNoetherian X] (hX : IsCohenMacaulay X)
    (p : ℕ) (c : chowCohomologyComponent C G sX p) (r : ℚ)
    (L : (DirectSum ℤ fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)) →ₗ[ℚ]
      DirectSum ℤ fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j))
    (hL : ∀ (k : ℤ) (α : chowGroup C sX k),
      L (DirectSum.of (fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)) k ((1 : ℚ) ⊗ₜ[ℤ] α)) =
        DirectSum.of (fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)) (k - p)
          (r ⊗ₜ[ℤ] chowCohomologyCap C G sX p c k α))
    {i : ℕ} {v : DirectSum ℤ fun j ↦ TensorProduct ℤ ℚ (chowGroup C sX j)}
    (hv : v ∈ codimensionChowSubmodule C sX i) :
    L v ∈ codimensionChowSubmodule C sX (i + p) := by
  refine (Submodule.span_le (p := (codimensionChowSubmodule C sX (i + p)).comap L)).2 ?_ hv
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap,
    ← of_one_tmul_mk_eq_integralComponentRationalClass C sX x rfl, hL]
  exact of_tmul_chowCohomologyCap_mem_codimensionChowSubmodule C sX G hX p c r hx rfl

end Cap

end Stacks.Chow

end
