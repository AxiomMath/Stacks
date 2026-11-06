module

public import StacksFrontier.AlgebraicGeometry.FunctionField.SectionsIntersectionStalks
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ProjectiveLineNormal
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveChart
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveMonomialSymbol
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveFormalNeighborhoodOfExceptional
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodResidueMap

/-!
# The formal neighbourhood of an exceptional curve of the first kind, unconditionally

Let `X` be a Noetherian scheme and `E ⊂ X` an exceptional curve of the first kind, cut out by an
ideal sheaf `D` and presented as the projective line by `e : 𝐏¹_k ≅ E`. Write `A = lim H⁰(Eₙ, 𝒪ₙ)`
for the ring of compatible functions on the thickenings and `Iₙ` for the projection kernels.
**[Stacks, Tag 0C2K]**: `A` is a complete local Noetherian regular local ring of dimension `2`,
and the kernel of `A ⟶ H⁰(Eₙ, 𝒪ₙ)` is the `n`-th power of its maximal ideal.

`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveFormalNeighborhood.lean` proves the four
conclusions from the bundle `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`,
and every field of that bundle is proved there or downstream except the independence of the
monomials: for `x, y ∈ I₁` whose symbols are `T₀, T₁`,

`∑_{j ≤ d} cⱼ x^{d-j} y^j ∈ I_{d+1}  ⟹  cⱼ ∈ I₁` for all `j ≤ d`.

This file proves it, builds the bundle,
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.exceptionalMonomialData`,
and states the four conclusions with no hypothesis beyond those of the tag.

## The argument

Fix an affine open `V = Spec B` of `X` meeting `E` on which `D` is cut out by a nonzerodivisor `t`.
The `n`-th thickening over `V` is `Spec B / tⁿ⁺¹`, so restriction to `V` is a ring map
`A ⟶ B / tⁿ⁺¹`, and a function in `I_d` restricts to the class of `t^d h`. The class of `h` in
`B / t = Γ(E ∩ V)`, viewed in the function field `K` of `E`, is a *leading coefficient* which is
multiplicative because restriction is a ring map — no comparison of the symbols in different
degrees is needed. Two facts about `E` finish the proof:

* a function on the second thickening vanishing on `E` and on `E ∩ V` vanishes
  (`AlgebraicGeometry.Scheme.IdealSheafData.eq_zero_of_thickeningRestriction_eq_zero`), so the
  leading coefficients of `x` and `y` are independent over `k`;
* `k = Γ(E, 𝒪_E)` is algebraically closed in `K`, because `E ≅ 𝐏¹_k` is integral and normal: an
  element of `K` integral over `Γ(E, 𝒪_E)` lies in every local ring, hence is a global function
  (`AlgebraicGeometry.exists_germToFunctionField_eq_of_eval₂_eq_zero`).

The commutative algebra combining them is
`AlgebraicGeometry.SemistableReduction.coeff_mem_of_sum_genMonomial_mem_of_chart`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.coeff_mem_one_of_sum_genMonomial_mem` — the independence of the monomials.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.exceptionalMonomialData`
  — the five inputs of Tag 0C2K, unconditionally.
* The four clauses of [Stacks, Tag 0C2K].

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Polynomial
open AlgebraicGeometry.SemistableReduction Stacks.Divisors

universe u

namespace AlgebraicGeometry

/-- **A rational function integral over the global functions of an integral normal scheme is a
global function**, when the global functions form a field. An element of the function field
annihilated by a nonzero polynomial over the field `Γ(Y, 𝒪_Y)` is integral over it, hence over
every local ring; the local rings are integrally closed, so it lies in each of them, and an
element of every local ring is a global section. In particular `Γ(Y, 𝒪_Y)` is algebraically
closed in the function field. -/
public theorem exists_germToFunctionField_eq_of_eval₂_eq_zero (Y : Scheme.{u}) [IsIntegral Y]
    [IsNormal Y] [Nonempty (⊤ : Y.Opens)] (hY : IsField Γ(Y, ⊤)) (u : Y.functionField)
    (p : Γ(Y, ⊤)[X]) (hp : p ≠ 0) (hpu : p.eval₂ (Y.germToFunctionField ⊤).hom u = 0) :
    ∃ g : Γ(Y, ⊤), Y.germToFunctionField ⊤ g = u := by
  obtain ⟨b, hb⟩ := hY.mul_inv_cancel (Polynomial.leadingCoeff_ne_zero.2 hp)
  have hint : _root_.IsIntegral Γ(Y, ⊤) u := by
    refine ⟨Polynomial.C b * p,
      Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rwa [mul_comm]), ?_⟩
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C]
    show _ * p.eval₂ (Y.germToFunctionField ⊤).hom u = 0
    rw [hpu, mul_zero]
  refine exists_germToFunctionField_eq_of_forall_mem_range Y ⊤ u fun x => ?_
  let : Algebra Γ(Y, ⊤) (Y.presheaf.stalk x.1) := (Y.presheaf.germ ⊤ x.1 trivial).hom.toAlgebra
  have : IsScalarTower Γ(Y, ⊤) (Y.presheaf.stalk x.1) Y.functionField :=
    functionField_isScalarTower Y ⊤ x
  exact (isIntegrallyClosed_iff Y.functionField).mp (id (IsNormal.stalk_normal x.1))
    hint.tower_top

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData) (V : X.affineOpens)

/-! ### The thickenings over an affine chart as quotients -/

/-- The part over `V` of the `n`-th thickening is `Spec Γ(X, V) ⧸ D(V)ⁿ⁺¹`, on sections. -/
public def thickeningChartEquiv (n : ℕ) :
    Γ(X, V.1) ⧸ D.ideal V ^ (n + 1) ≃+* Γ(thickening D n, thickeningChart D V n) :=
  (Ideal.quotEquivOfEq (ker_thickeningChartSection D V n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (thickeningChartSection_surjective D V n))

/-- `AlgebraicGeometry.Scheme.IdealSheafData.thickeningChartEquiv` sends the class of `b ∈ Γ(X, V)`
to its section over the chart of the `n`-th thickening. -/
public theorem thickeningChartEquiv_mk (n : ℕ) (b : Γ(X, V.1)) :
    thickeningChartEquiv D V n (Ideal.Quotient.mk _ b) = thickeningChartSection D V n b := by
  rw [thickeningChartEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- **Restriction of compatible functions to an affine chart**: the ring map
`A ⟶ Γ(X, V) ⧸ D(V)ⁿ⁺¹` reading the `n`-th component over `V`. -/
public def formalNeighborhoodChart (n : ℕ) :
    formalNeighborhoodRing D →+* Γ(X, V.1) ⧸ D.ideal V ^ (n + 1) :=
  (thickeningChartEquiv D V n).symm.toRingHom.comp
    ((thickeningChartRestrict D V n).comp (formalNeighborhoodProjection D n))

/-- The restriction of `a` to the chart `V` is the class of `b` exactly when `b` and the `n`-th
component of `a` have the same section over the chart of the `n`-th thickening. -/
public theorem formalNeighborhoodChart_eq_mk_iff (n : ℕ) (a : formalNeighborhoodRing D)
    (b : Γ(X, V.1)) :
    formalNeighborhoodChart D V n a = Ideal.Quotient.mk _ b ↔
      thickeningChartSection D V n b =
        thickeningChartRestrict D V n (formalNeighborhoodProjection D n a) := by
  rw [formalNeighborhoodChart, RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq, thickeningChartEquiv_mk, eq_comm]

/-- The restriction of `a` to the chart `V` vanishes exactly when the `n`-th component of `a`
vanishes over the chart of the `n`-th thickening. -/
public theorem formalNeighborhoodChart_eq_zero_iff (n : ℕ) (a : formalNeighborhoodRing D) :
    formalNeighborhoodChart D V n a = 0 ↔
      thickeningChartRestrict D V n (formalNeighborhoodProjection D n a) = 0 := by
  rw [formalNeighborhoodChart, RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, map_eq_zero_iff _ (thickeningChartEquiv D V n).symm.injective]

variable {D}

/-! ### Independence of the monomials -/

variable {k : Type u} [Field k] {e : projectiveLineProj k ≅ D.subscheme}

namespace IsExceptionalCurveOfFirstKind

variable [IsEffectiveCartierDivisor D] (hE : IsExceptionalCurveOfFirstKind D k e)

/-- **The degree-`d` monomials in two elements of `I₁` with symbols `T₀, T₁` are independent over
`A / I₁` modulo `I_{d+1}`.** This is the `monomials_indep` field of
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`. -/
public theorem coeff_mem_one_of_sum_genMonomial_mem {x y : formalNeighborhoodRing D}
    (hx : x ∈ formalNeighborhoodFiltration D 1) (hy : y ∈ formalNeighborhoodFiltration D 1)
    (hsx : hE.formalNeighborhoodSymbol 1 x = MvPolynomial.X 0)
    (hsy : hE.formalNeighborhoodSymbol 1 y = MvPolynomial.X 1)
    (d : ℕ) (c : ℕ → formalNeighborhoodRing D)
    (h : (∑ j ∈ Finset.range (d + 1), c j * genMonomial x y d j) ∈
      formalNeighborhoodFiltration D (d + 1))
    (j : ℕ) (hj : j ≤ d) : c j ∈ formalNeighborhoodFiltration D 1 := by
  have : IsIntegral (projectiveLineProj k) :=
    Stacks.AlgebraicGeometry.ProjPolyChart.isIntegral_proj k 1
  have : IsIntegral D.subscheme := IsIntegral.of_isIso e.hom
  have : IsNormal D.subscheme := Stacks.ResolutionOfSurfaces.isNormal_of_iso_projectiveLineProj k e
  have : Nonempty (⊤ : D.subscheme.Opens) := ⟨⟨genericPoint D.subscheme, trivial⟩⟩
  obtain ⟨V, hqV, t, ht, hVt⟩ := Stacks.CartierAffineLocal.exists_affineOpen_nonZeroDivisor D
    hE.isEffectiveCartierDivisor (D.subschemeι (genericPoint D.subscheme))
  have hVne : Nonempty (D.subschemeι ⁻¹ᵁ V.1) := ⟨⟨genericPoint D.subscheme, hqV⟩⟩
  let S := sectionsSubschemeRingEquivOfIso D k e
  let f : k →+* D.subscheme.functionField :=
    (D.subscheme.germToFunctionField ⊤).hom.comp S.symm.toRingHom
  let π : Γ(X, V.1) →+* D.subscheme.functionField :=
    (D.subscheme.germToFunctionField (D.subschemeι ⁻¹ᵁ V.1)).hom.comp
      (D.subschemeι.app V.1).hom
  have hρI : ∀ a, a ∈ formalNeighborhoodFiltration D 1 ↔ formalNeighborhoodResidue D k e a = 0 :=
    fun a => by rw [← ker_formalNeighborhoodResidue D k e, RingHom.mem_ker]
  refine coeff_mem_of_sum_genMonomial_mem_of_chart (formalNeighborhoodFiltration D) (D.ideal V) t
    hVt ht (formalNeighborhoodChart D V) ?_ ?_ ?_ π ?_ (formalNeighborhoodResidue D k e)
    (surjective_formalNeighborhoodResidue D k (hE.surjective_formalNeighborhoodProjection 0) e)
    hρI f ?_ ?_ hx hy ?_ d c h j hj
  · intro n a b hab
    rw [formalNeighborhoodChart_eq_mk_iff] at hab ⊢
    have := thickeningChartSection_eq_of_le D V (Nat.le_succ n) _ b hab
    rwa [thickeningRestrictionLE_formalNeighborhoodProjection] at this
  · intro n a ha
    rw [formalNeighborhoodChart_eq_zero_iff, RingHom.mem_ker.1 ha, map_zero]
  · intro a ha1 h1
    rw [formalNeighborhoodChart_eq_zero_iff] at h1
    refine RingHom.mem_ker.2 (eq_zero_of_thickeningRestriction_eq_zero V
      hE.isEffectiveCartierDivisor (m := 0) ?_ hVne h1)
    rw [thickeningRestriction_formalNeighborhoodProjection]
    exact RingHom.mem_ker.1 ha1
  · rw [RingHom.ker_comp_of_injective _
      (D.subscheme.germToFunctionField_injective (D.subschemeι ⁻¹ᵁ V.1)), D.ker_subschemeι_app]
  · intro a b hab
    rw [formalNeighborhoodChart_eq_mk_iff] at hab
    have hb := subschemeι_app_eq_of_le V (le_of_eq (pow_one D)) _ b hab
    have hρ : formalNeighborhoodResidue D k e a =
        S ((inclusion (le_of_eq (pow_one D))).appTop.hom (formalNeighborhoodProjection D 0 a)) := by
      rw [formalNeighborhoodResidue_apply, sectionsSubschemeRingEquivOfIso_apply,
        appTop_hom_isoPowOne, sectionsSubschemeRingEquivOfIso_apply]
    simp only [π, f, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hρ,
      RingEquiv.symm_apply_apply]
    rw [hb]
    exact D.subscheme.presheaf.germ_res_apply (homOfLE le_top) _ _ _
  · intro u p hp hpu
    obtain ⟨g, hg⟩ := exists_germToFunctionField_eq_of_eval₂_eq_zero D.subscheme
      (isField_sections_subscheme_of_iso_projectiveLineProj D k e) u
      (p.map S.symm.toRingHom) ((Polynomial.map_ne_zero_iff S.symm.injective).2 hp)
      (by rwa [Polynomial.eval₂_map])
    exact ⟨S g, by simpa [f] using hg⟩
  · intro a b hab
    have hax := Ideal.mul_mem_left _ a hx
    have hby := Ideal.mul_mem_left _ b hy
    have hsym := (hE.formalNeighborhoodSymbol_eq_zero_iff 1 (Ideal.add_mem _ hax hby)).2 hab
    rw [hE.formalNeighborhoodSymbol_add 1 hax hby, hE.formalNeighborhoodSymbol_smul 1 a hx,
      hE.formalNeighborhoodSymbol_smul 1 b hy, hsx, hsy, hE.formalNeighborhoodSymbol_zero,
      hE.formalNeighborhoodSymbol_zero] at hsym
    have h0 := congrArg (fun q => q.coeff (Finsupp.single 0 1)) hsym
    have h1 := congrArg (fun q => q.coeff (Finsupp.single 1 1)) hsym
    simp only [AddMonoidAlgebra.coeff_add, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, Finsupp.add_apply,
      Finsupp.single_eq_single_iff] at h0 h1
    simp only [↓reduceIte, mul_one, Fin.isValue, one_ne_zero, and_true,
      subRegular_zero_right_iff_rightRegular, isRegular_one, IsRegular.right, SubRegular.ne,
      and_self, or_self, mul_zero, add_zero, zero_ne_one, zero_add] at h0 h1
    exact ⟨(hρI a).2 h0, (hρI b).2 h1⟩

end IsExceptionalCurveOfFirstKind

/-! ### The five inputs, and Tag 0C2K -/

/-- **The five geometric inputs of [Stacks, Tag 0C2K] for an exceptional curve of the first
kind**, with nothing carried: two elements of `I₁` whose symbols are the coordinates `T₀, T₁`,
the independence of the monomials in them
(`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.coeff_mem_one_of_sum_genMonomial_mem`), and the spanning statement which it implies by the
dimension count of `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.le_span_pow_sup_iff_coeff_mem_one`. -/
public def IsExceptionalCurveOfFirstKind.exceptionalMonomialData
    (hE : IsExceptionalCurveOfFirstKind D k e) : ExceptionalMonomialData D :=
  haveI : IsEffectiveCartierDivisor D := hE.isEffectiveCartierDivisor
  let x := hE.exists_formalNeighborhoodSymbol_one_eq_X.choose
  let y := hE.exists_formalNeighborhoodSymbol_one_eq_X.choose_spec.choose
  have hxy := hE.exists_formalNeighborhoodSymbol_one_eq_X.choose_spec.choose_spec
  ExceptionalMonomialData.ofMonomialInputsOfExceptional k hE x y
    (Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨hxy.1, Set.singleton_subset_iff.2 hxy.2.1⟩))
    (fun n => by
      cases n with
      | zero => rw [pow_zero, Ideal.one_eq_top]; exact le_top.trans le_sup_left
      | succ m =>
        exact (hE.le_span_pow_sup_iff_coeff_mem_one hxy.1 hxy.2.1 m).2 fun c hc j hj =>
          hE.coeff_mem_one_of_sum_genMonomial_mem hxy.1 hxy.2.1 hxy.2.2.1 hxy.2.2.2 (m + 1) c hc
            j hj)
    (fun d c hc j hj =>
      hE.coeff_mem_one_of_sum_genMonomial_mem hxy.1 hxy.2.1 hxy.2.2.1 hxy.2.2.2 d c hc j hj)

/-- **Stacks 0C2K, the complete Noetherian local clause.** For an exceptional curve of the first
kind on a Noetherian scheme, the ring `lim H⁰(Eₙ, 𝒪ₙ)` of compatible functions on the
infinitesimal thickenings is a Noetherian complete local ring. -/
@[stacks 0C2K "the complete Noetherian local clause"]
public theorem isNoetherianCompleteLocalRing_formalNeighborhoodRing_of_isExceptionalCurveOfFirstKind
    [IsNoetherian X] (hE : D.IsExceptionalCurveOfFirstKind k e) :
    IsNoetherianCompleteLocalRing (formalNeighborhoodRing D) :=
  isNoetherianCompleteLocalRing_formalNeighborhoodRing D k hE hE.exceptionalMonomialData

/-- **Stacks 0C2K, the regularity clause.** For an exceptional curve of the first kind on a
Noetherian scheme, the ring of compatible functions on the thickenings is a regular local ring. -/
@[stacks 0C2K "the regularity clause"]
public theorem isRegularLocalRing_formalNeighborhoodRing_of_isExceptionalCurveOfFirstKind
    [IsNoetherian X] (hE : D.IsExceptionalCurveOfFirstKind k e) :
    IsRegularLocalRing (formalNeighborhoodRing D) :=
  isRegularLocalRing_formalNeighborhoodRing D k hE hE.exceptionalMonomialData

/-- **Stacks 0C2K, the dimension clause.** For an exceptional curve of the first kind on a
Noetherian scheme, the ring of compatible functions on the thickenings has dimension `2`. -/
@[stacks 0C2K "the dimension clause"]
public theorem ringKrullDim_formalNeighborhoodRing_eq_two_of_isExceptionalCurveOfFirstKind
    [IsNoetherian X] (hE : D.IsExceptionalCurveOfFirstKind k e) :
    ringKrullDim (formalNeighborhoodRing D) = 2 :=
  ringKrullDim_formalNeighborhoodRing_eq_two D k hE hE.exceptionalMonomialData

/-- **Stacks 0C2K, the kernel clause.** For an exceptional curve of the first kind on a Noetherian
scheme, the kernel of the projection of the ring of compatible functions to `H⁰(Eₙ₊₁, 𝒪)` is the
`(n + 1)`-st power of the maximal ideal, for the local ring structure that comes with the
regularity clause. -/
@[stacks 0C2K "the kernel clause: the kernel of the projection to E_{n+1} is the (n+1)-st power \
of the maximal ideal"]
public theorem IsExceptionalCurveOfFirstKind.ker_formalNeighborhoodProjection_eq_maximalIdeal_pow
    [IsNoetherian X] (hE : D.IsExceptionalCurveOfFirstKind k e) (n : ℕ) :
    letI : IsLocalRing (formalNeighborhoodRing D) :=
      (isRegularLocalRing_formalNeighborhoodRing_of_isExceptionalCurveOfFirstKind hE).toIsLocalRing
    RingHom.ker (formalNeighborhoodProjection D n) =
      IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ^ (n + 1) :=
  ker_formalNeighborhoodProjection_eq_maximalIdeal_pow_of_isExceptionalCurveOfFirstKind D k hE
    hE.exceptionalMonomialData n

end Scheme.IdealSheafData

end AlgebraicGeometry
