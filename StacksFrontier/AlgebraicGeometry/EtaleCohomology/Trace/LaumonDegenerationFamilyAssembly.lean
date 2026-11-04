module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreDegeneration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonDegenerationLine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyLisseLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonLineBasicOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyStalkPurityFibreInput
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonOriginFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonSpecializationInjectionCharNe
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierEquinormStable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCoefficientRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveLocalFrobeniusData
public import StacksFrontier.AlgebraicGeometry.Curves.AffineLineShiftFiniteEtale
public import StacksFrontier.RingTheory.NodalCurve

/-!
# Laumon's degeneration at the origin, assembled (L8)

`Stacks.EtaleCohomology.LaumonDegenerationFamilyInput` (piece L8 of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) asks, for `σ` pure of weight `β` whose
two-parameter Fourier family is pure of weight `β + 1` off `D = 0`, for an open `V` of a curve
through the origin, a representation `τ` of `π₁(V)` pure of weight `β + 1` and the specialization
injection of `H¹_c(𝔸¹_k̄, ℱ_σ)` into the inertia invariants of `τ` at the origin. This file builds
these data:

* a finite extension `k'` of `k` and `c ∈ k'` with `D(s, c s) (s + c s) ≠ 0`
  (`Stacks.EtaleCohomology.exists_aeval_line_ne_zero`), so that the kernel `s (xⁿ⁰ + c x)` is
  nonzero and the line `(s, c s)` is not contained in `D = 0`;
* the family sheaf `K = pr₁^*ℱ_σ ⊗ L_ψ'(t (xⁿ⁰ + c x))` on the plane and an open `V = D(f)` of the
  `t`-line over which `R¹g'_!(K|_{U'})` is lisse
  (`Stacks.EtaleCohomology.exists_laumonFamily_lisseLocus`,
  `Stacks.EtaleCohomology.laumonLineBasicOpen_elim`), the curve `W = 𝔸¹_{k'}` and its origin `y`;
* the local data of Weil II 1.8.4 at `y` (`Stacks.EtaleCohomology.curveLocalFrobeniusData`);
* the representation `τ` of the lisse sheaf
  (`Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse`),
  pure of weight `β + 1` (`Stacks.EtaleCohomology.laumonFamily_isPure_restrictScalarsRep'` with
  `Stacks.EtaleCohomology.laumonFamilyFibreLinearInput`);
* the specialization injection
  (`Stacks.EtaleCohomology.exists_laumonSpecializationInjection_of_baseChange'` with
  `Stacks.EtaleCohomology.laumonOriginFibreCohomologyInput`).

The only input left is the absence of punctual sections of `R¹pr₂! K` at the origin, for `ℓ`
different from the characteristic (`Stacks.EtaleCohomology.LaumonFamilyNoPunctualSectionsInput'`).

## Main results

* `Stacks.EtaleCohomology.natCard_residueField_span_X`: the residue field of `𝔸¹_{k'}` at the
  origin has `#k'` elements.
* `Stacks.EtaleCohomology.laumonDegenerationFamilyInput_of_noPunctualSections`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-! ### The origin of the line -/

section Origin

variable (k' : Type u) [Field k']

/-- **The residue field of `𝔸¹_{k'}` at the origin has `#k'` elements**: `k' → κ((t))` is
bijective, every polynomial being congruent modulo `t` to its constant coefficient (`(t)` is
maximal by `Stacks.NodalCurve.isMaximal_span_X`). -/
theorem natCard_residueField_span_X :
    Nat.card ((Spec (.of (Polynomial k'))).residueField
      (⟨Ideal.span {Polynomial.X}, (Stacks.NodalCurve.isMaximal_span_X k').isPrime⟩ :
        PrimeSpectrum _)) =
      Nat.card k' := by
  set y : PrimeSpectrum (Polynomial k') :=
    ⟨Ideal.span {Polynomial.X}, (Stacks.NodalCurve.isMaximal_span_X k').isPrime⟩
  have : y.asIdeal.IsMaximal := Stacks.NodalCurve.isMaximal_span_X k'
  let φ : k' →+* y.asIdeal.ResidueField :=
    (algebraMap (Polynomial k') y.asIdeal.ResidueField).comp Polynomial.C
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun w => ?_⟩
    obtain ⟨r, rfl⟩ := Ideal.algebraMap_residueField_surjective y.asIdeal w
    refine ⟨r.coeff 0, ?_⟩
    show algebraMap _ _ (Polynomial.C (r.coeff 0)) = _
    rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero, ← neg_mem_iff, neg_sub]
    exact Ideal.mem_span_singleton.2 Polynomial.X_dvd_sub_C
  rw [Nat.card_congr
    (Scheme.Spec.residueFieldIso (.of (Polynomial k')) y).commRingCatIsoToRingEquiv.toEquiv,
    Nat.card_congr (Equiv.ofBijective φ hφ).symm]

end Origin

/-! ### The assembly -/

/-- **L8 from the absence of punctual sections** (Laumon; Kedlaya, *Fourier transforms and p-adic
Weil II*, §6.4; [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the degeneration of the
Fourier family at the origin (`Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`) holds as
soon as `G = R¹pr₂! K` has no punctual sections at the origin, for `ℓ` different from the
characteristic (`Stacks.EtaleCohomology.LaumonFamilyNoPunctualSectionsInput'`). The curve is the
line `(a, c') = (s, c s)` over a finite extension `k'` of `k`, chosen off `D = 0`; `V = D(f)` is an
open of the `s`-line in the lisse locus of `G` missing the origin; `τ` is the representation of
`G|_V`, pure of weight `β + 1` because its Frobenius traces are those of the fibres of the family;
and the specialization map at the origin is the injection `J`, carrying `(π^*) ^ [k' : k]` to the
geometric Frobenius at the origin. -/
theorem laumonDegenerationFamilyInput_of_noPunctualSections
    (hH2 : LaumonFamilyNoPunctualSectionsInput'.{u}) : LaumonDegenerationFamilyInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ ι' β hV hpure ψ hψ n₀ hn₀ D hD hfib
  intro C hC
  classical
  -- the extension `k'` and the slope `c` of the line, off `D = 0` and off `s + c s = 0`
  have hD₁ : D * (MvPolynomial.X 0 + MvPolynomial.X 1) ≠ 0 := by
    refine mul_ne_zero hD fun h0 => ?_
    simpa using congrArg (MvPolynomial.eval ![(1 : k), 0]) h0
  obtain ⟨k', _, _, _, c, hc⟩ := exists_aeval_line_ne_zero k p hD₁
  let : Fintype k' := Fintype.ofFinite k'
  have : Module.Finite k k' := Module.Finite.of_finite
  have : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  rw [map_mul] at hc
  have hlin : (Polynomial.X + Polynomial.C c * Polynomial.X : Polynomial k') ≠ 0 := by
    simpa using right_ne_zero_of_mul hc
  have hh : (Polynomial.X ^ n₀ + Polynomial.C c * Polynomial.X : Polynomial k') ≠ 0 := by
    rcases eq_or_ne n₀ 1 with rfl | h1
    · rwa [pow_one]
    · intro h0
      simpa [Polynomial.coeff_X, Polynomial.coeff_C_mul, Ne.symm h1] using
        congrArg (Polynomial.coeff · n₀) h0
  obtain ⟨n', -, hn'⟩ := FiniteField.card k' p
  have hcard' : Fintype.card k' = p ^ (n' : ℕ) := hn'
  -- the plane, the line and a geometric point of the plane over `x̄`
  have hk'lt : Cardinal.mk k' < B.cutoff :=
    (Cardinal.lt_aleph0_of_finite k').trans B.aleph0_lt_cutoff
  have hsize (R : Type u) [CommRing R] (h : Cardinal.mk R < B.cutoff) :
      schemeSizeBelow B.cutoff (Spec (.of (Polynomial R))) :=
    (schemeSizeBelow_spec_iff B.aleph0_lt_cutoff _).2
      (Polynomial.cardinalMk_le_max.trans_lt (max_lt h B.aleph0_lt_cutoff))
  have hL := hsize k' hk'lt
  have hS := hsize _ ((schemeSizeBelow_spec_iff B.aleph0_lt_cutoff _).1 hL)
  obtain ⟨x', hx'⟩ := exists_geometricPoint_polynomial_map_eq e k' x
  let zz : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))) :=
    x'.map (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (Polynomial.X : Polynomial k'))))
  have hzz : zz.map (laumonFamilyPr₁ k') = x' := by
    simp only [zz]
    rw [← GeometricPoint.map_comp, laumonFourier_specMap_evalRingHom_X_comp_pr₁]
    cases x'
    simp only [GeometricPoint.map, Category.comp_id]
  have hz : (zz.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x := by
    rwa [hzz]
  obtain ⟨p₀⟩ := Stacks.ArtinSchreier.nonempty_finiteEtaleFiber_cover k' (laumonKernel k' n₀ c) zz
  have hσ₁ := continuous_restrictScalarsRep_comp_etaleFundamentalGroupMap
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
    (zz.map (laumonFamilyPr₁ k')) hz b σ hσ
  -- the lisse locus `D(f)` of the family, `t · D(s, c s) (s + c s) ∣ f`
  obtain ⟨g, hg0, hXg, hlis⟩ := exists_laumonFamily_lisseLocus k' B hS hL ℓ b
    (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c zz p₀ _ hσ₁ _ hc
  have hDg : MvPolynomial.aeval ![(Polynomial.X : Polynomial k'), Polynomial.C c * Polynomial.X] D ∣
      g := (dvd_mul_of_dvd_right (dvd_mul_right _ _) _).trans hXg
  have hXg' : (Polynomial.X : Polynomial k') ∣ g := (dvd_mul_right _ _).trans hXg
  -- a compactification of `pr₂`
  have : CompactSpace ↥(B.inclusion.obj (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)) :=
    inferInstanceAs (CompactSpace (Spec (.of (Polynomial k'))))
  have : QuasiSeparatedSpace
      ↥(B.inclusion.obj (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of (Polynomial k'))))
  obtain ⟨jg, -⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace
    (B.inclusion.map (laumonFamilyProjection k' B hS hL))
  -- the open `V = D(g)` of the line and `U' = pr₂⁻¹(V)`
  refine laumonLineBasicOpen_elim k' B hS hL hg0 C ?_
  intro V U' _ _ _ _ _ jV jU g' _ _ _ jg' fV _ _ _ _ jfV hjV hrange hfV hpb hconn
  have := hjV
  have := hconn (AlgebraicClosure k')
  -- the curve `W = 𝔸¹_{k'}` and its origin `y`
  let W : B.Scheme := Stacks.ArtinSchreier.specObject (Polynomial k') B hL
  let fW : W.1 ⟶ Spec (.of k') := Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))
  have : SmoothOfRelativeDimension 1 fW :=
    Stacks.GenericFiniteEtale.smoothOfRelativeDimension_specMap_polynomial k'
  have : LocallyOfFiniteType fW := by unfold fW; infer_instance
  have : QuasiCompact fW := by unfold fW; infer_instance
  have : IsSeparated fW := by unfold fW; infer_instance
  have : IsIntegral W.1 := inferInstanceAs (IsIntegral (Spec (.of (Polynomial k'))))
  let jW : V.1 ⟶ W.1 := B.inclusion.map jV
  let y : W.1 := (⟨Ideal.span {Polynomial.X}, (Stacks.NodalCurve.isMaximal_span_X k').isPrime⟩ :
    PrimeSpectrum _)
  have hy0 : y.asIdeal = Ideal.span {Polynomial.X} := rfl
  have hyc : IsClosed ({y} : Set W.1) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (Stacks.NodalCurve.isMaximal_span_X k')
  have hyV : y ∉ Set.range jW.base := by
    show y ∉ Set.range (B.inclusion.map jV)
    rw [hrange]
    intro hy
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hy (Ideal.mem_span_singleton.2 hXg')
  have hy : jW.base (genericPoint V.1) ⤳ y := by
    rw [genericPoint_eq_of_isOpenImmersion jW]
    exact genericPoint_specializes y
  let dy : ℕ := Module.finrank k k'
  have hdy : 0 < dy := Module.finrank_pos
  have hcardy : Nat.card (W.1.residueField y) = (p ^ n) ^ dy := by
    rw [natCard_residueField_span_X k', Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := k) (V := k'), hcard]
  -- the local data at `y`
  refine curveLocalFrobeniusData jW hy fW hyc C ?_
  intro L Ω _ _ _ _ _ _ _ _ _ A _ _ _ _ _ _ _ _ eA hA P _ Fr hFrD hFr hcardA
  rw [hcardy] at hcardA
  -- the representation `τ` of `G|_V` at the geometric generic point
  let xV : GeometricPoint V.1 := (algebraicClosureGeometricPoint
    (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1))
  obtain ⟨r, ρ, hρ, φ, ψ₀, N, hφψ, hψφ, mτ, τ, Pm, Qm, hτc, hPQ, hQP, hα, hτ⟩ :=
    exists_restrictScalarsRep_of_isLisse B V xV (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
      (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c zz p₀ _ hσ₁ jU g' jg') E
      (algebraMap_conjIntegralSubring_algebraMap _ _) b
      (hlis V U' jV jU g' jg' hjV hrange.subset hpb 1)
  -- `τ` is pure of weight `β + 1`
  have hpτ := laumonFamily_isPure_restrictScalarsRep' laumonFamilyFibreLinearInput B ℓ k U e x E b
    σ ι' β ψ n₀ D hfib k' c hS hL zz hz p₀ hσ₁ g hDg V U' jV jU g' jg' hjV hrange.subset hpb fV p
    n' hcard' xV ρ hρ φ ψ₀ N hφψ hψφ τ Pm Qm hPQ hα hτ hQP
  -- the specialization injection
  obtain ⟨J, hJ, hJT⟩ := exists_laumonSpecializationInjection_of_baseChange' B ℓ
    laumonOriginFibreCohomologyInput hH2 k U f e he j kbar p n hcard hℓp x E b σ hσ ψ n₀ k' c
    (Stacks.FourierDeligne.traceChar_ne_one ψ k' hψ) hh hS hL zz hz p₀ hσ₁ jg V fV jfV
    (AlgebraicClosure k') n' hcard' fW (𝟙 _) (Category.id_comp _) jW hfV U' jU g' jg' hpb y hy0
    hyc hyV hy dy hcardy L Ω A eA hA P Fr hFrD hFr r ρ hρ φ ψ₀ N hφψ hψφ mτ τ Pm Qm hPQ hα hτ
  exact hC V k' fV jfV (AlgebraicClosure k') n' hcard' W fW (𝟙 _) (Category.id_comp _) jW hfV y
    hyc hyV hy L Ω A eA hA P Fr hFrD hFr τ hτc hpτ dy hdy hcardA J hJ hJT

end Stacks.EtaleCohomology

end
