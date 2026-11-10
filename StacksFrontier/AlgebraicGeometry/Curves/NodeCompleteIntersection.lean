module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.Curves.Node
public import StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.FaithfullyFlatStalk
public import StacksFrontier.RingTheory.CompleteIntersection.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.LocalCompleteIntersection.Basic
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
import all StacksFrontier.RingTheory.LocalCompleteIntersection.Basic

/-!
# The local ring at a node is a complete intersection

Let `k` be a field and let `X` be a scheme locally of finite type over `k` with a node at `x`.
Then `𝒪_{X, x}` is a complete intersection over `k`. This is the local-complete-intersection
half of the implication (1) ⟹ (2) of Tag 0C4E.

The completed local ring at a node is a power-series hypersurface in two variables: over an
algebraic closure `K` of `k` the point lies under an ordinary double point, whose completion is
the two-branch multicross ring `K[[x, y]]/(xy)`. A two-variable power-series ring is regular
local of dimension two and a nonzero element of its maximal ideal is a regular sequence of
length one, so this exhibits the completion as a regular local ring modulo a regular sequence.
The map `𝒪_{X, x} → 𝒪_{X_K, x̄}` is flat and local, and the complete intersection property of a
Noetherian local ring descends along such a map, which removes the algebraic closure. Finally
Lemma 09Q6 turns the intrinsic, completion-based condition into the relative one over `k`, for
which the local ring is presented as a localization of the coordinate ring of an affine
neighbourhood.

No separability of `κ(x)/k` is used: the descent along the flat local map needs nothing about
the fibre.

## Main results

* `Stacks.Curves.isCompleteIntersectionRing_of_adicCompletion_ringEquiv_quotient_span_singleton`
  — a Noetherian local ring whose completion is a two-variable power-series ring modulo a
  nonzero element of the maximal ideal is a complete intersection.
* `Stacks.Curves.IsNodalAlgebra.isCompleteIntersectionRing` — a nodal local algebra over a
  field is a complete intersection ring.
* `Stacks.Curves.isCompleteIntersectionRing_stalk_of_hasMulticrossCompletion` — a local ring
  whose completion is the two-branch multicross ring is a complete intersection.
* `Stacks.Curves.isCompleteIntersection_stalk_of_isNode` — the local ring at a node of a scheme
  locally of finite type over `k` is a complete intersection over `k`.  Unlike
  `Stacks.Curves.isCompleteIntersectionRing_stalk_of_isNode` of
  `StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCompleteIntersection` this asks nothing about
  the dimension of `X`, so the complete-intersection-ring step is run inside its proof rather
  than taken from there.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C4E](https://stacks.math.columbia.edu/tag/0C4E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing MvPowerSeries

universe u v

namespace Stacks.Curves

open scoped Pointwise in
/-- A Noetherian local ring whose completion at the maximal ideal is the quotient of the
two-variable power-series ring over a field by a nonzero element of the maximal ideal is a
complete intersection: the power-series ring is regular local and the single element is a
regular sequence in it. -/
theorem isCompleteIntersectionRing_of_adicCompletion_ringEquiv_quotient_span_singleton
    (K : Type u) [Field K] (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : MvPowerSeries (Fin 2) K) (hf0 : f ≠ 0)
    (hfm : f ∈ maximalIdeal (MvPowerSeries (Fin 2) K))
    (e : AdicCompletion (maximalIdeal A) A ≃+*
      (MvPowerSeries (Fin 2) K ⧸ Ideal.span {f})) :
    LocalCompleteIntersection.IsCompleteIntersectionRing A := by
  let R := MvPowerSeries (Fin 2) K
  have _ : IsRegularLocalRing R := MvPowerSeries.isRegularLocalRing K 2
  have _ : IsDomain R := IsRegularLocalRing.isDomain R
  have hsmul : IsSMulRegular R f :=
    IsSMulRegular.of_right_eq_zero_of_smul fun x hx =>
      (mem_nonZeroDivisors_iff.mp (mem_nonZeroDivisors_of_ne_zero hf0)).1 x
        (by simpa [smul_eq_mul] using hx)
  have hproper : Ideal.span ({f} : Set R) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
      (Ideal.span_le.2 (Set.singleton_subset_iff.mpr hfm))
  have _ : Nontrivial (QuotSMulTop f R) := by
    rw [QuotSMulTop, Submodule.Quotient.nontrivial_iff]
    intro htop
    have hmem : (1 : R) ∈ (f : R) • (⊤ : Submodule R R) := by
      rw [htop]
      simp
    rw [Submodule.mem_smul_pointwise_iff_exists] at hmem
    obtain ⟨b, -, hb⟩ := hmem
    exact hproper (Ideal.span_singleton_eq_top.mpr
      (IsUnit.of_mul_eq_one b (by simpa [smul_eq_mul] using hb)))
  have hseq : RingTheory.Sequence.IsRegular R [f] :=
    RingTheory.Sequence.IsRegular.cons hsmul
      (RingTheory.Sequence.IsRegular.nil R (QuotSMulTop f R))
  let F : R →+* AdicCompletion (maximalIdeal A) A :=
    e.symm.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {f}))
  have hF : Function.Surjective F := e.symm.surjective.comp Ideal.Quotient.mk_surjective
  have _ : IsLocalHom F := IsLocalHom.of_surjective F hF
  have hker : RingHom.ker F = Ideal.span ({f} : Set R) := by
    rw [RingHom.ker_comp_of_injective _ e.symm.injective]
    ext x
    rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨R, inferInstance, inferInstance, F, hF, inferInstance, [f], hseq,
    by simpa [Ideal.ofList] using hker.symm⟩

/-- A binary quadratic form of nonzero discriminant is a nonzero power series: its three
coefficients are read off from the coefficients of the monomials `x²`, `x y` and `y²`, and they
cannot all vanish. -/
theorem nodalBinaryQuadratic_ne_zero {K : Type v} [Field K] (a b c : K)
    (hdet : 4 * a * c - b ^ 2 ≠ 0) : nodalBinaryQuadratic a b c ≠ 0 := by
  intro h
  have hc (m : Fin 2 →₀ ℕ) := congrArg (MvPowerSeries.coeff m) h
  have ha : a = 0 := by
    simpa [nodalBinaryQuadratic, MvPowerSeries.X_def, MvPowerSeries.coeff_C_mul, mul_assoc,
      MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial, pow_succ,
      ← Finsupp.single_add, Finsupp.single_eq_single_iff, Finsupp.ext_iff,
      Fin.forall_fin_two] using hc (Finsupp.single 0 2)
  have hb : b = 0 := by
    have h' := congrArg
      (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1)) h
    simpa [nodalBinaryQuadratic, MvPowerSeries.X_def, MvPowerSeries.coeff_C_mul, mul_assoc,
      MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial, pow_succ,
      ← Finsupp.single_add, Finsupp.single_eq_single_iff, Finsupp.ext_iff,
      Fin.forall_fin_two] using h'
  have hc0 : c = 0 := by
    simpa [nodalBinaryQuadratic, MvPowerSeries.X_def, MvPowerSeries.coeff_C_mul, mul_assoc,
      MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial, pow_succ,
      ← Finsupp.single_add, Finsupp.single_eq_single_iff, Finsupp.ext_iff,
      Fin.forall_fin_two] using hc (Finsupp.single 1 2)
  exact hdet (by simp [ha, hb, hc0])

/-- A binary quadratic form has zero constant coefficient, so it lies in the maximal ideal of
the two-variable power-series ring. -/
theorem nodalBinaryQuadratic_mem_maximalIdeal {K : Type v} [Field K] (a b c : K) :
    nodalBinaryQuadratic a b c ∈ maximalIdeal (MvPowerSeries (Fin 2) K) := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
  simp [nodalBinaryQuadratic]

/-- **A nodal local algebra over a field is a complete intersection ring.** Its completion is
the power-series hypersurface cut out by a binary quadratic form of nonzero discriminant, which
is a nonzero element of the maximal ideal of the regular local ring `κ[[x, y]]`. -/
theorem IsNodalAlgebra.isCompleteIntersectionRing (k : Type u) [Field k] (A : Type v)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] (h : IsNodalAlgebra k A) :
    LocalCompleteIntersection.IsCompleteIntersectionRing A := by
  obtain ⟨-, a, b, c, hdet, ⟨e⟩⟩ := ((isNodalAlgebra_tfae k A).out 1 3).mp h
  exact isCompleteIntersectionRing_of_adicCompletion_ringEquiv_quotient_span_singleton
    (ResidueField A) A (nodalBinaryQuadratic a b c) (nodalBinaryQuadratic_ne_zero a b c hdet)
    (nodalBinaryQuadratic_mem_maximalIdeal a b c) e.toRingEquiv

/-- If the completed local ring at a point of a locally Noetherian scheme over a field is the
two-branch multicross ring, then the local ring at that point is a complete intersection: the
multicross ring is the power-series hypersurface `K[[x, y]]/(xy)`. -/
theorem isCompleteIntersectionRing_stalk_of_hasMulticrossCompletion (K : Type u) [Field K]
    (Y : Scheme.{u}) [Y.Over (AlgebraicGeometry.Spec (.of K))] [IsLocallyNoetherian Y] (y : Y)
    (hy : HasMulticrossCompletion K Y y 2) :
    LocalCompleteIntersection.IsCompleteIntersectionRing (Y.presheaf.stalk y) := by
  let A := Y.presheaf.stalk y
  let kToStalk : K →+* A :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (Y ↘ AlgebraicGeometry.Spec (.of K)).appTop ≫
      Y.presheaf.germ ⊤ y trivial).hom
  let _ : Algebra K A := kToStalk.toAlgebra
  have hX : ∀ i : Fin 2, (X i : MvPowerSeries (Fin 2) K) ≠ 0 := by
    intro i h
    have h' := congrArg (MvPowerSeries.coeff (R := K) (Finsupp.single i 1)) h
    simp [MvPowerSeries.coeff_X] at h'
  refine isCompleteIntersectionRing_of_adicCompletion_ringEquiv_quotient_span_singleton K A
    (X 0 * X 1) (mul_ne_zero (hX 0) (hX 1)) ?_
    (hy.some.trans (quotientAlgEquivMulticross (k := K)).symm).toRingEquiv
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
  simp

/-- **A node is a local complete intersection over the ground field.** The local ring at a node
of a scheme locally of finite type over `k` is a complete intersection over `k` in the sense of
Definition 00SD.

This is the local-complete-intersection half of the implication (1) ⟹ (2) of Stacks Tag 0C4E:
by Tag 01UG a scheme locally of finite type over `k` is a local complete intersection over `k`
exactly when all of its local rings are. -/
theorem isCompleteIntersection_stalk_of_isNode (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))] (x : X) (hx : IsNode k X x) :
    letI : Algebra k (X.presheaf.stalk x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
    IsCompleteIntersection k (X.presheaf.stalk x) := by
  let f : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
  let _ : Algebra k (X.presheaf.stalk x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  -- over an algebraic closure of `k` the point lies under an ordinary double point, whose
  -- completed local ring is the power-series hypersurface `K[[x, y]]/(xy)`; the complete
  -- intersection property descends along the faithfully flat local map of local rings induced
  -- by the extension of the ground field
  have hCIRgen : ∀ y : X, IsNode k X y →
      LocalCompleteIntersection.IsCompleteIntersectionRing (X.presheaf.stalk y) := by
    intro y hy
    obtain ⟨-, ybar, hybar, hodp⟩ := hy
    subst hybar
    let K := AlgebraicClosure k
    let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (pullback f g : Scheme.{u})
    let _ : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨pullback.snd f g⟩
    have _ : LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (.of K)) :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd f g))
    have _ : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Y ↘ AlgebraicGeometry.Spec (.of K))
    have hB : LocalCompleteIntersection.IsCompleteIntersectionRing (Y.presheaf.stalk ybar) :=
      isCompleteIntersectionRing_stalk_of_hasMulticrossCompletion K Y ybar hodp.2
    let A := X.presheaf.stalk ((pullback.fst f g).base ybar)
    let B := Y.presheaf.stalk ybar
    have _ : IsNoetherianRing A :=
      inferInstanceAs (IsNoetherianRing (X.presheaf.stalk ((pullback.fst f g).base ybar)))
    have _ : IsNoetherianRing B := inferInstanceAs (IsNoetherianRing (Y.presheaf.stalk ybar))
    have _ : IsLocalRing A :=
      inferInstanceAs (IsLocalRing (X.presheaf.stalk ((pullback.fst f g).base ybar)))
    have _ : IsLocalRing B := inferInstanceAs (IsLocalRing (Y.presheaf.stalk ybar))
    let φ := ((pullback.fst f g).stalkMap ybar).hom
    let _ : Algebra A B := φ.toAlgebra
    have _ : Module.Flat A B := RingHom.flat_algebraMap_iff.mp
      (AlgebraicGeometry.faithfullyFlat_stalkMap_fieldExtension k K X f
        ((pullback.fst f g).base ybar) ybar rfl).flat
    have _ : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom φ)
    exact LocalCompleteIntersection.isCompleteIntersectionRing_of_flat A B hB
  have hCIR : LocalCompleteIntersection.IsCompleteIntersectionRing (X.presheaf.stalk x) :=
    hCIRgen x hx
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U : X.affineOpens := ⟨U₀, hU₀⟩
  let _ : Algebra k Γ(X, U.1) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
  have _ : Algebra.FiniteType k Γ(X, U.1) := by
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom).FiniteType
    exact (f.finiteType_appLE (isAffineOpen_top _) U.2 _).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  let _ : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    (X.presheaf.germ U.1 x hxU).hom.toAlgebra
  have _ : IsScalarTower k Γ(X, U.1) (X.presheaf.stalk x) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    simp only [RingHom.algebraMap_toAlgebra]
    change (X.presheaf.germ ⊤ x (by simp))
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom a) =
      (X.presheaf.germ U.1 x hxU)
        ((f.appTop ≫ X.presheaf.map (homOfLE le_top).op)
          (((Scheme.ΓSpecIso (.of k)).inv).hom a))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [← X.presheaf.germ_res_apply (homOfLE le_top) x hxU]
  let q : Ideal Γ(X, U.1) := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
  have _ : q.IsPrime := (U.2.primeIdealOf ⟨x, hxU⟩).isPrime
  have _ : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
    U.2.isLocalization_stalk ⟨x, hxU⟩
  have _ : IsNoetherianRing Γ(X, U.1) := Algebra.FiniteType.isNoetherianRing k Γ(X, U.1)
  have _ : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  have _ : IsLocalRing (Localization.AtPrime q) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime q) q
  let e : Localization.AtPrime q ≃ₐ[Γ(X, U.1)] X.presheaf.stalk x :=
    IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) (X.presheaf.stalk x)
  exact LocalCompleteIntersection.isCompleteIntersection_of_algEquiv k (e.restrictScalars k)
    ((LocalCompleteIntersection.isCompleteIntersection_atPrime_iff_isCompleteIntersectionRing
      k Γ(X, U.1) q).mpr
      (LocalCompleteIntersection.isCompleteIntersectionRing_of_ringEquiv e.symm.toRingEquiv hCIR))

end Stacks.Curves

end
