module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesSeparablePointsBertini
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GlobalSectionsBijective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Stacks 0FI0: `H^0(X)` and `Γ(X, 𝒪_X)`

Assume given (D0), (D1), (D2) and (D3) satisfying (A), (B) and (C)
(`Stacks.WeilCohomology.WeilData`, over the actual category of smooth projective schemes over
`k`, `F` of characteristic zero). Let `X` be a smooth projective scheme over `k` and
`k' = Γ(X, 𝒪_X)`. Stacks 0FI0 says that the following are equivalent:

1. there exist finitely many closed points `x₁, …, x_r ∈ X` whose residue fields are separable
   over `k` such that `H^0(X) → H^0(x₁) ⊕ … ⊕ H^0(x_r)` is injective
   (`Stacks.WeilCohomology.WeilData.SeparablePointsDetectH0`);
2. the map `H^0(Spec(k')) → H^0(X)` is an isomorphism;

that if this is true then `H^0(X)` is a finite separable `F`-algebra; and that if `X` is
equidimensional of dimension `d`, then (1) and (2) are also equivalent to

3. the classes of closed points generate `H^{2d}(X)(d)` as a module over `H^0(X)`
   (`Stacks.WeilCohomology.WeilData.PointClassesGenerate`).

## The proof

* (2) ⇒ (1) and (1) ⇒ (2) are `Concrete/GlobalSectionsSeparablePoints.lean` and
  `Concrete/GlobalSectionsBijective.lean`.
* If (2) holds, `H^0(X) ≅ H^0(Spec(k'))` is a finite separable `F`-algebra by Stacks 0FHQ (2).
* (1) ⇔ (3) is Poincaré duality (A)(b) in the form `∫_X a ∪ γ([x]) = Tr_{H^0(x)/F}(x^* a)`
  (Stacks 0FHG, 0FHQ (4)): for (3) ⇒ (1), by Stacks 0FH5 the closed points may be taken with
  separable residue fields, finitely many suffice as `H^{2d}(X)(d)` is finite dimensional
  (A)(a), and an `a ∈ H^0(X)` killed by all `x^*` pairs to zero with `H^{2d}(X)(d)`. For
  (1) ⇒ (3), a nonzero `a ∈ H^0(X)` orthogonal to all `c ∪ γ([x])` has
  `Tr(x^*a · x^*a^m) = 0` for all `m`, so `x^* a = 0` (`eq_zero_of_trace_mul_aeval_eq_zero`, a
  separable element whose products with its own polynomials have trace zero vanishes in
  characteristic zero); (1) then forces `a = 0`.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.pointCycleClass`: the class `[x] ∈ CH^c(X)` of
  a closed point.
* `Stacks.WeilCohomology.WeilData.PointClassesGenerate`: condition (3).

## Main results

* `Stacks.WeilCohomology.WeilData.separablePointsDetectH0_iff_bijective`: (1) ⇔ (2).
* `Stacks.WeilCohomology.WeilData.finiteDimensional_isSeparable_H0_of_bijective`: `H^0(X)` is
  finite separable.
* `Stacks.WeilCohomology.WeilData.separablePointsDetectH0_iff_pointClassesGenerate`: (1) ⇔ (3).
* `Stacks.WeilCohomology.WeilData.globalSections_criterion`: **Stacks 0FI0**.

## References

* [Stacks Project, Tag 0FI0](https://stacks.math.columbia.edu/tag/0FI0)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-! ### A trace criterion -/

/-- **A separable element `u` of a finite algebra over a field of characteristic zero with
`Tr(u · q(u)) = 0` for every polynomial `q` is zero.** Otherwise the minimal polynomial is
`X^ε ν` with `ε ≤ 1` and `ν` a nonconstant polynomial prime to `X`, and writing
`1 = s X + t ν`, `e = u s(u)` is a nonzero idempotent, whose trace is the dimension of
`e · C ≠ 0`. -/
theorem eq_zero_of_trace_mul_aeval_eq_zero {F C : Type*} [Field F] [CharZero F] [CommRing C]
    [Algebra F C] [FiniteDimensional F C] {u : C} (hu : IsSeparable F u)
    (h : ∀ q : F[X], Algebra.trace F C (u * aeval u q) = 0) : u = 0 := by
  classical
  by_contra hne
  have : Nontrivial C := ⟨⟨u, 0, hne⟩⟩
  set μ := minpoly F u
  obtain ⟨ν, hμ, hν⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd μ
    (minpoly.ne_zero (Algebra.IsIntegral.isIntegral u)) 0
  simp only [map_zero, sub_zero] at hμ hν
  have hn : μ.rootMultiplicity 0 ≤ 1 := rootMultiplicity_le_one_of_separable hu 0
  obtain ⟨s, t, hst⟩ := irreducible_X.coprime_iff_not_dvd.mpr hν
  -- `μ` divides `X ν`
  have hμX : μ ∣ Polynomial.X * ν := by
    rw [hμ]
    exact mul_dvd_mul_right (by simpa using pow_dvd_pow (Polynomial.X : F[X]) hn) ν
  set e := aeval u (s * Polynomial.X)
  have he : e = u * aeval u s := by
    simp only [e, map_mul, aeval_X, mul_comm]
  -- `e` is idempotent
  have hidem : IsIdempotentElem e := by
    have hdvd : μ ∣ (s * Polynomial.X) * (s * Polynomial.X) - s * Polynomial.X := by
      have : (s * Polynomial.X) * (s * Polynomial.X) - s * Polynomial.X =
          -(s * t) * (Polynomial.X * ν) := by
        linear_combination (s * Polynomial.X) * hst
      rw [this]
      exact dvd_mul_of_dvd_right hμX _
    have h0 := aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (minpoly.aeval F u)
    rwa [map_sub, map_mul, sub_eq_zero] at h0
  -- `e` is nonzero
  have he0 : e ≠ 0 := by
    intro he0
    have hdvd : μ ∣ s * Polynomial.X := minpoly.dvd F u he0
    have hνμ : ν ∣ μ := ⟨_, hμ.trans (mul_comm _ _)⟩
    have hν1 : IsUnit ν := by
      have : ν ∣ s * Polynomial.X + t * ν := dvd_add (hνμ.trans hdvd) (dvd_mul_left ν t)
      rw [hst] at this
      exact isUnit_of_dvd_one this
    have := aeval_eq_zero_of_dvd_aeval_eq_zero (hν1.dvd_mul_right.mp hμX) (minpoly.aeval F u)
    rw [aeval_X] at this
    exact hne this
  -- its trace is zero, so it is zero
  have htr : LinearMap.trace F C (Algebra.lmul F C e) = 0 := by
    rw [← Algebra.trace_apply, he]
    exact h s
  have hlm := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero (hidem.map (Algebra.lmul F C)) htr
  exact he0 (by simpa using LinearMap.congr_fun hlm 1)

/-- A spanning set of a finite-dimensional vector space contains a finite spanning set. -/
theorem exists_finset_subset_span_eq_top {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {G : Set V} (hG : Submodule.span K G = ⊤) :
    ∃ T : Finset V, ↑T ⊆ G ∧ Submodule.span K (T : Set V) = ⊤ := by
  classical
  let bas := Module.finBasis K V
  have hfin : ∀ j, ∃ T : Finset V, ↑T ⊆ G ∧ bas j ∈ Submodule.span K ↑T :=
    fun j ↦ Submodule.mem_span_finite_of_mem_span (hG ▸ Submodule.mem_top)
  choose T hTG hTj using hfin
  refine ⟨Finset.univ.biUnion T, fun v hv ↦ ?_, ?_⟩
  · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.1 hv)
    exact hTG j hj
  · refine eq_top_iff.mpr (bas.span_eq ▸ Submodule.span_le.mpr ?_)
    rintro _ ⟨j, rfl⟩
    exact Submodule.span_mono (fun v hv ↦ Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hv⟩)
      (hTj j)

namespace SmoothProjectiveScheme

variable {X : (SmoothProjectiveScheme k).FullSubcategory} {x : X.obj.left}
    (hx : IsClosed ({x} : Set X.obj.left))

/-- **The class `[x] ∈ CH^c(X)` of a closed point** `x`, the class of the closed subscheme
`Spec κ(x) ⟶ X` (`Stacks.WeilCohomology.closedSubschemeClass`). -/
def pointCycleClass (c : ℤ) : codimensionChowGroup k X.obj.hom c :=
  haveI := isClosed_singleton_iff_isClosedImmersion.mp hx
  closedSubschemeClass X.obj.hom (X.obj.left.fromSpecResidueField x) c

/-- The class of a closed point is the class of the zero cycle `[x]`, read in codimension `c`. -/
theorem zeroCycleToCodimension_integralComponentAt (c : ℤ) :
    zeroCycleToCodimension X.obj.hom c
        (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) X.obj.hom 0)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) X.obj.hom
            (integralComponentAt x).subschemeι 0)) =
      pointCycleClass hx c := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have := isIntegral_integralComponentAt x
  have : IsIntegral (Spec (.of (X.obj.left.residueField x))) :=
    inferInstanceAs (IsIntegral (Spec (.of (X.obj.left.residueField x))))
  have hgen : cycleAssociatedToClosedSubscheme (fieldChowSituation k) X.obj.hom
      (integralComponentAt x).subschemeι 0 =
      cycleAssociatedToClosedSubscheme (fieldChowSituation k) X.obj.hom
        (X.obj.left.fromSpecResidueField x) 0 :=
    cycleAssociatedToClosedSubscheme_eq_of_genericPoint_eq (fieldChowSituation k) X.obj.hom
      (integralComponentAt x).subschemeι (X.obj.left.fromSpecResidueField x) (by
      rw [show X.obj.left.fromSpecResidueField x (genericPoint _) = x from
        Scheme.fromSpecResidueField_apply (X := X.obj.left) x _]
      exact genericPointOf_integralComponentAt x) 0
  rw [QuotientAddGroup.mk'_apply, hgen]
  refine zeroCycleToCodimension_mk_cycleAssociatedToClosedSubscheme X.obj.hom _ (fun z ↦ ?_) c
  rw [relativeDimension_comp_closedImmersion,
    show X.obj.left.fromSpecResidueField x z = x from
      Scheme.fromSpecResidueField_apply (X := X.obj.left) x z]
  exact relativeDimension_eq_zero_of_isClosed (fieldChowSituation k) (fun _ _ ↦ rfl) X.obj.hom x hx

end SmoothProjectiveScheme

namespace WeilData

variable {F : Type w} [Field F] {W : WeilData k F}

/-! ### Condition (3) -/

variable (W) in
/-- **Condition (3) of Stacks 0FI0** for `X` equidimensional of dimension `d`: the classes
`γ([x]) ∈ H^{2d}(X)(d)` of the closed points `x ∈ X` generate `H^{2d}(X)(d)` as a module over
`H^0(X)`, that is, the products `c ∪ γ([x])`, `c ∈ H^0(X)`, span it over `F`. -/
def PointClassesGenerate (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) : Prop :=
  Submodule.span F {v : W.Tw X (2 * d) d | ∃ (c : W.H0 X) (x : X.obj.left)
      (hx : IsClosed ({x} : Set X.obj.left)),
      v = W.cupTw X 0 (2 * d) (2 * d) (zero_add _) 0 d d (zero_add _) (W.h0TwEquiv X c)
        (W.cycleClass X d (pointCycleClass hx d))} = ⊤

/-- `∫_X a ∪ (c ∪ v) = ∫_X (a c) ∪ v` for `a, c ∈ H^0(X)`. -/
theorem h0Pairing_cupTw (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (a c : W.H0 X) (v : W.Tw X (2 * d) d) :
    W.h0Pairing X d hX a
        (W.cupTw X 0 (2 * d) (2 * d) (zero_add _) 0 d d (zero_add _) (W.h0TwEquiv X c) v) =
      W.h0Pairing X d hX (a * c) v := by
  simp only [h0Pairing, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.refl_apply]
  rw [pairingTw_apply, pairingTw_apply]
  congr 1
  apply (W.twCoord X _ _).injective
  rw [twCoord_cupTw, twCoord_cupTw, twCoord_cupTw]
  apply Subtype.ext
  simp only [coe_cup]
  rw [W.twCoord_h0TwEquiv X a, W.twCoord_h0TwEquiv X c, W.twCoord_h0TwEquiv X (a * c),
    Subalgebra.coe_mul, mul_assoc]

/-- **`∫_X a ∪ (c ∪ γ([x])) = Tr_{H^0(x)/F}(x^*a · x^*c)`** for a closed point `x` with separable
residue field (Stacks 0FHG, 0FHQ (4)). -/
theorem h0Pairing_cupTw_closedPointClass [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {X : (SmoothProjectiveScheme k).FullSubcategory}
    {d : ℕ} (hX : IsNonemptyEquidimensional X d) {x : X.obj.left}
    (hx : IsClosed ({x} : Set X.obj.left)) (hs : HasSeparableResidueField k X.obj.hom x)
    (a c : W.H0 X) :
    W.h0Pairing X d hX a
        (W.cupTw X 0 (2 * d) (2 * d) (zero_add _) 0 d d (zero_add _) (W.h0TwEquiv X c)
          (W.cycleClass X d (pointCycleClass hx d))) =
      Algebra.trace F (W.H0 (closedPointObj hx hs))
        (H0.pullHom W (closedPointHom hx hs) a * H0.pullHom W (closedPointHom hx hs) c) := by
  have hZ := isNonemptyEquidimensional_closedPointObj hx hs
  rw [h0Pairing_cupTw, ← map_mul]
  exact W.h0Pairing_cycleClass_closedSubschemeClass hA hB hC (closedPointHom hx hs) hX hZ
    (fun c ↦ traceZero_eq_trace hA hB hC
      (topologicalKrullDim_eq_zero_of_isNonemptyEquidimensional hZ) c) (a * c)

/-- `H^0(x)` is a finite separable `F`-algebra (Stacks 0FHQ (2)). -/
theorem finiteDimensional_isSeparable_H0_closedPointObj [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    {X : (SmoothProjectiveScheme k).FullSubcategory} {x : X.obj.left}
    (hx : IsClosed ({x} : Set X.obj.left))
    (hs : HasSeparableResidueField k X.obj.hom x) :
    FiniteDimensional F (W.H0 (closedPointObj hx hs)) ∧
      Algebra.IsSeparable F (W.H0 (closedPointObj hx hs)) := by
  have h0 := topologicalKrullDim_eq_zero_of_isNonemptyEquidimensional
    (isNonemptyEquidimensional_closedPointObj hx hs)
  exact ⟨finiteDimensional_H0_of_dimension_zero hA hB hC h0,
    isSeparable_H0_of_dimension_zero hA hB hC h0⟩

/-- **(1) ⇒ (3) of Stacks 0FI0.** -/
theorem pointClassesGenerate_of_separablePointsDetectH0 [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ} (hX : IsNonemptyEquidimensional X d)
    (h1 : W.SeparablePointsDetectH0 X) :
    W.PointClassesGenerate X d := by
  obtain ⟨r, x, hx, hs, hinj⟩ := h1
  by_contra hM
  obtain ⟨f, hf0, hMf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hM)
  obtain ⟨a, rfl⟩ := (W.h0Pairing_isPerfPair hA.perfectPairing X d hX).bijective_left.2 f
  have hpt : ∀ i, H0.pullHom W (closedPointHom (hx i) (hs i)) a = 0 := by
    intro i
    obtain ⟨_, _⟩ := finiteDimensional_isSeparable_H0_closedPointObj (W := W) hA hB hC (hx i) (hs i)
    refine eq_zero_of_trace_mul_aeval_eq_zero (Algebra.IsSeparable.isSeparable F _) fun q ↦ ?_
    have hv := hMf (Submodule.subset_span ⟨aeval a q, x i, hx i, rfl⟩)
    rw [LinearMap.mem_ker, h0Pairing_cupTw_closedPointClass hA hB hC hX (hx i) (hs i)] at hv
    rwa [aeval_algHom_apply]
  apply hf0
  have ha : a = 0 := by
    have := hinj (a₁ := ⟨a.1, a.2⟩) (a₂ := 0) (funext fun i ↦ Subtype.ext (by
      show W.pull _ a.1 = W.pull _ 0
      rw [map_zero]
      exact congrArg Subtype.val (hpt i)))
    exact Subtype.ext (congrArg Subtype.val this)
  rw [ha, map_zero]

/-- If the classes of closed points generate `H^{2d}(X)(d)` over `H^0(X)`, so do those of the
closed points with separable residue field (Stacks 0FH5). -/
theorem span_separablePointClasses_eq_top {X : (SmoothProjectiveScheme k).FullSubcategory}
    {d : ℕ} (h3 : W.PointClassesGenerate X d) :
    Submodule.span F {v : W.Tw X (2 * d) d | ∃ (c : W.H0 X) (x : X.obj.left)
      (hx : IsClosed ({x} : Set X.obj.left)) (_ : HasSeparableResidueField k X.obj.hom x),
      v = W.cupTw X 0 (2 * d) (2 * d) (zero_add _) 0 d d (zero_add _) (W.h0TwEquiv X c)
        (W.cycleClass X d (pointCycleClass hx d))} = ⊤ := by
  set G : Set (W.Tw X (2 * d) d) := {v | ∃ (c : W.H0 X) (x : X.obj.left)
      (hx : IsClosed ({x} : Set X.obj.left)) (_ : HasSeparableResidueField k X.obj.hom x),
      v = W.cupTw X 0 (2 * d) (2 * d) (zero_add _) 0 d d (zero_add _) (W.h0TwEquiv X c)
        (W.cycleClass X d (pointCycleClass hx d))}
  refine eq_top_iff.mpr (h3 ▸ Submodule.span_le.mpr ?_)
  rintro _ ⟨c, x, hx, rfl⟩
  let φ : chowGroup (fieldChowSituation k) X.obj.hom 0 →+ W.Tw X (2 * d) d :=
    ((W.cupTw X 0 (2 * d) (2 * d) (zero_add (2 * (d : ℤ))) 0 d d (zero_add (d : ℤ))
      (W.h0TwEquiv X c)).toAddMonoidHom.comp (W.cycleClass X d)).comp
      (zeroCycleToCodimension X.obj.hom d)
  have hφ : ∀ (y : X.obj.left) (hy : IsClosed ({y} : Set X.obj.left)),
      φ (QuotientAddGroup.mk' _ (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        X.obj.hom (integralComponentAt y).subschemeι 0)) =
      W.cupTw X 0 (2 * d) (2 * d) (zero_add _) 0 d d (zero_add _) (W.h0TwEquiv X c)
        (W.cycleClass X d (pointCycleClass hy d)) := fun y hy ↦ by
    simp only [φ, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [zeroCycleToCodimension_integralComponentAt hy]
  have hcl : AddSubgroup.closure (separablePointClasses k X.obj.hom) ≤
      (Submodule.span F G).toAddSubgroup.comap φ := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨y, hy, hys, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, hφ y hy]
    exact Submodule.subset_span ⟨c, y, hy, hys, rfl⟩
  have := hcl (mem_closure_separablePointClasses_of_isProjectiveMorphism k X.obj.hom
    ((AlgebraicGeometry.isProjective_iff_isProjectiveMorphism_of_isAffine _).1
      (SmoothProjectiveScheme.isProjective X))
    (QuotientAddGroup.mk' _ (cycleAssociatedToClosedSubscheme
      (fieldChowSituation k) X.obj.hom (integralComponentAt x).subschemeι 0)))
  rwa [AddSubgroup.mem_comap, hφ x hx] at this

/-- **(3) ⇒ (1) of Stacks 0FI0.** -/
theorem separablePointsDetectH0_of_pointClassesGenerate [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ} (hX : IsNonemptyEquidimensional X d)
    (h3 : W.PointClassesGenerate X d) :
    W.SeparablePointsDetectH0 X := by
  classical
  have := hA.finiteDimensionality X d hX (2 * d)
  have : FiniteDimensional F (W.Tw X (2 * d) d) :=
    LinearEquiv.finiteDimensional (W.twCoord X _ _).symm
  obtain ⟨T', hT'G, hspan⟩ :=
    exists_finset_subset_span_eq_top (span_separablePointClasses_eq_top h3)
  choose c x hx hs hv using fun v : T' ↦ hT'G (Finset.mem_coe.2 v.2)
  let e := T'.equivFin
  refine ⟨T'.card, fun i ↦ x (e.symm i), fun i ↦ hx _, fun i ↦ hs _, fun a a' haa ↦ ?_⟩
  rw [← sub_eq_zero]
  set b : W.H0 X := ⟨(a - a').1, (a - a').2⟩
  have hb : ∀ i, H0.pullHom W (closedPointHom (hx (e.symm i)) (hs (e.symm i))) b = 0 := fun i ↦ by
    apply Subtype.ext
    show W.pull _ (a - a').1 = 0
    rw [Submodule.coe_sub, map_sub, sub_eq_zero]
    exact congrArg Subtype.val (congrFun haa i)
  have hzero : W.h0Pairing X d hX b = 0 := by
    refine LinearMap.ext_on hspan fun v hvT ↦ ?_
    obtain ⟨i, hi⟩ := e.symm.surjective ⟨v, hvT⟩
    rw [show v = (e.symm i : W.Tw X (2 * d) d) from (congrArg Subtype.val hi).symm,
      hv (e.symm i), h0Pairing_cupTw_closedPointClass hA hB hC hX (hx _) (hs _), hb i, zero_mul,
      map_zero, LinearMap.zero_apply]
  have hb0 : b = 0 :=
    (W.h0Pairing_isPerfPair hA.perfectPairing X d hX).bijective_left.1
      (hzero.trans (map_zero _).symm)
  exact Subtype.ext (congrArg Subtype.val hb0)

/-- **(1) ⇔ (3) of Stacks 0FI0**, for `X` equidimensional of dimension `d` (possibly empty). -/
theorem separablePointsDetectH0_iff_pointClassesGenerate [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ} (hd : RelativeDimension X.obj.hom d) :
    W.SeparablePointsDetectH0 X ↔ W.PointClassesGenerate X d := by
  rcases isEmpty_or_nonempty X.obj.left with hX | hX
  · have := W.subsingleton_of_isEmpty hB.kunnethIsomorphism hC.pullback hC.mul hC.point X
    have : Subsingleton (W.Tw X (2 * d) d) := (W.twCoord X _ _).toEquiv.subsingleton
    refine ⟨fun _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Fin.elim0, fun i ↦ i.elim0,
      fun i ↦ i.elim0, fun a a' _ ↦ Subsingleton.elim a a'⟩⟩
  have hXd : IsNonemptyEquidimensional X d := ⟨hX, hd⟩
  exact ⟨pointClassesGenerate_of_separablePointsDetectH0 hA hB hC hXd,
    separablePointsDetectH0_of_pointClassesGenerate hA hB hC hXd⟩

/-! ### (1) ⇔ (2), and the finite separability of `H^0(X)` -/

/-- **(1) ⇔ (2) of Stacks 0FI0.** -/
theorem separablePointsDetectH0_iff_bijective [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    (X : (SmoothProjectiveScheme k).FullSubcategory) :
    W.SeparablePointsDetectH0 X ↔ Function.Bijective (W.pullDeg (toSpecGlobalSections X) 0) :=
  ⟨bijective_of_separablePointsDetectH0 X hA hB hC, separablePointsDetectH0_of_bijective hA hB hC X⟩

/-- **If (2) holds, `H^0(X)` is a finite separable `F`-algebra**: it is isomorphic to
`H^0(Spec(k'))`, which is one by Stacks 0FHQ (2). -/
theorem finiteDimensional_isSeparable_H0_of_bijective [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (h2 : Function.Bijective (W.pullDeg (toSpecGlobalSections X) 0)) :
    FiniteDimensional F (W.H0 X) ∧ Algebra.IsSeparable F (W.H0 X) := by
  rcases isEmpty_or_nonempty X.obj.left with hX | ⟨⟨x0⟩⟩
  · have := W.subsingleton_of_isEmpty hB.kunnethIsomorphism hC.pullback hC.mul hC.point X
    have : Subsingleton (W.H0 X) := ⟨fun a b ↦ Subtype.ext (Subsingleton.elim _ _)⟩
    have : Finite (W.H0 X) := Finite.of_subsingleton
    exact ⟨Module.Finite.of_finite, ⟨fun a ↦ by
      rw [IsSeparable, minpoly.subsingleton]
      exact separable_one⟩⟩
  have : Nontrivial (globalSections X) :=
    RingHom.domain_nontrivial (X.obj.left.Γevaluation x0).hom
  have hS := topologicalKrullDim_specGlobalSections X
  have hbij : Function.Bijective (H0.pullHom W (toSpecGlobalSections X)) :=
    ⟨fun c c' hcc ↦ Subtype.ext (congrArg Subtype.val (h2.1 (a₁ := ⟨c.1, c.2⟩) (a₂ := ⟨c'.1, c'.2⟩)
      (Subtype.ext (congrArg Subtype.val hcc)))),
      fun a ↦ by
        obtain ⟨c, hc⟩ := h2.2 ⟨a.1, a.2⟩
        exact ⟨⟨c.1, c.2⟩, Subtype.ext (congrArg Subtype.val hc)⟩⟩
  let e := AlgEquiv.ofBijective (H0.pullHom W (toSpecGlobalSections X)) hbij
  have := finiteDimensional_H0_of_dimension_zero hA hB hC hS
  have := isSeparable_H0_of_dimension_zero hA hB hC hS
  exact ⟨LinearEquiv.finiteDimensional e.toLinearEquiv, AlgEquiv.Algebra.isSeparable e⟩

/-! ### Stacks 0FI0 -/

/-- **Stacks Project, Tag 0FI0.** Assume given (D0), (D1), (D2) and (D3) satisfying (A), (B) and
(C). Let `X` be a smooth projective scheme over `k` and `k' = Γ(X, 𝒪_X)`. Then the following are
equivalent:

1. there exist finitely many closed points `x₁, …, x_r ∈ X` whose residue fields are separable
   over `k` such that `H^0(X) → H^0(x₁) ⊕ … ⊕ H^0(x_r)` is injective
   (`SeparablePointsDetectH0`),
2. the map `H^0(Spec(k')) → H^0(X)` is an isomorphism.

If this is true, then `H^0(X)` is a finite separable algebra over `F`. If `X` is equidimensional
of dimension `d`, then (1) and (2) are also equivalent to

3. the classes of closed points generate `H^{2d}(X)(d)` as a module over `H^0(X)`
   (`PointClassesGenerate`).

Here `Spec(k')` is the smooth projective `k`-scheme `specGlobalSections X` and the map in (2) is
pullback along the canonical morphism `X ⟶ Spec(k')`; "equidimensional of dimension `d`" is
`RelativeDimension X.obj.hom d`, which allows `X = ∅`. -/
@[stacks 0FI0 "(1) ⇔ (2), the finite separability of H^0(X), and (1) ⇔ (3) for X equidimensional \
of dimension d, on the actual Weil data (D0)-(D3) satisfying (A), (B), (C) over the actual \
category of smooth projective k-schemes"]
theorem globalSections_criterion [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (W.SeparablePointsDetectH0 X ↔ Function.Bijective (W.pullDeg (toSpecGlobalSections X) 0)) ∧
      (Function.Bijective (W.pullDeg (toSpecGlobalSections X) 0) →
        FiniteDimensional F (W.H0 X) ∧ Algebra.IsSeparable F (W.H0 X)) ∧
      ∀ d : ℕ, RelativeDimension X.obj.hom d →
        (W.SeparablePointsDetectH0 X ↔ W.PointClassesGenerate X d) :=
  ⟨separablePointsDetectH0_iff_bijective hA hB hC X,
    finiteDimensional_isSeparable_H0_of_bijective hA hB hC X,
    fun _ hd ↦ separablePointsDetectH0_iff_pointClassesGenerate hA hB hC hd⟩

end WeilData

end Stacks.WeilCohomology

end
