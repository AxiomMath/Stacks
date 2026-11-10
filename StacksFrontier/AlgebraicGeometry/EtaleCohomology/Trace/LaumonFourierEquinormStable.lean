module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierEquinormInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyStalkPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveLinearIotaRealPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharacterTwistAbsIrr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientHigherDirectImageStalkLinearIsoProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FiniteFourier
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierKernelProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.AffineLineFourierKernel

/-!
# Equal absolute values of the Fourier family, for `σ` which stays absolutely irreducible

The first half of Laumon's purity of the two-parameter Fourier family
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya, *Fourier transforms and p-adic
Weil II*, Theorem 6.4), `Stacks.EtaleCohomology.LaumonFourierEquinormStableInput`, from its
geometric inputs:

* the lisse locus of the family at fixed `a`
  (`Stacks.EtaleCohomology.LaumonFourierLineLisseInput`);
* the absolute irreducibility of the Fourier transform (L6,
  `Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput`);
* the identification of the fibres of the family
  (`Stacks.EtaleCohomology.LaumonFourierFamilyFibreInput`);
* a partner of the family which makes it real along `ι'`
  (`Stacks.EtaleCohomology.LaumonFourierFamilyConjugateInput`).

At a fibre over `(k', a, c)` with `D(a, c) ≠ 0`, the family `G_V` over the open `V' = D(D(a, t))`
of the `t`-line is lisse, given by an `E`-linear representation `τ` of `π₁(V')`
(`Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse`); `τ` is absolutely irreducible
(L6, since `σ` stays absolutely irreducible over `k'` and twisting by a character does not change
the stable subspaces), real together with its partner, hence `ι'`-pure of some weight by Weil II
1.5.1 on `V'` (`Stacks.EtaleCohomology.exists_norm_eq_pow_of_isIotaRealizable_curve`). At the
rational point `v` of `V'` over `t = c`, the characteristic polynomial of `τ(F_v)` is that of the
stalk Frobenius of `G_V`, which is that of the Frobenius on `H¹_c` of the fibre (`E`-linear proper
base change, `Stacks.EtaleCohomology.coefficientHigherDirectImageStalkLinearInput`), which is the
fibre characteristic polynomial of `Stacks.EtaleCohomology.LaumonFibreCharpoly`.

## Main results

* `Stacks.EtaleCohomology.exists_laumonPoint_of_eval_ne_zero`: the rational point of `V'` over
  `t = c`.
* `Stacks.EtaleCohomology.laumonFourierEquinormStableInput_of_inputs`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- **The value at `t = c` of the `t`-polynomial `D(a, t)`** is `D(a, c)`. -/
public theorem laumonFourier_eval_eval₂ {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (D : MvPolynomial (Fin 2) k) (a c : k') :
    Polynomial.eval c (MvPolynomial.eval₂ (Polynomial.C.comp (algebraMap k k'))
      ![Polynomial.C a, Polynomial.X] D) =
      MvPolynomial.eval ![a, c] (MvPolynomial.map (algebraMap k k') D) := by
  rw [← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left, MvPolynomial.eval_map]
  congr 1
  · ext r
    simp
  · funext i
    fin_cases i <;> simp

/-- **The rational point of `V'` over `t = c`**: if `V'` is an open of the `t`-line with image
`D(g)` and `g(c) ≠ 0`, there is a closed point `v` of `V'` over the prime `(t - c)`, at which
`k' → κ(v)` is bijective and `t` takes the value `c`. -/
public theorem exists_laumonPoint_of_eval_ne_zero {k' : Type u} [Field k'] {B : BigEtaleSite.{u}}
    {hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k')))} {V' : B.Scheme}
    (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
    (hjV' : IsOpenImmersion (B.inclusion.map jV')) (g : Polynomial k')
    (hrange : Set.range (B.inclusion.map jV') =
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (Polynomial k'))))
    (c : k') (hc : g.eval c ≠ 0) :
    ∃ v : V'.1, IsClosed ({v} : Set V'.1) ∧
      Function.Bijective ((laumonPointRingHom jV' v).comp Polynomial.C) ∧
      laumonPointRingHom jV' v Polynomial.X = laumonPointRingHom jV' v (Polynomial.C c) := by
  let I : Ideal (Polynomial k') := RingHom.ker (Polynomial.evalRingHom c)
  have hI : I.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun y => ⟨Polynomial.C y, by simp⟩
  have hmem : ∀ r : Polynomial k', r ∈ I ↔ r.eval c = 0 := fun r => by
    simp [I, RingHom.mem_ker]
  let P : PrimeSpectrum (Polynomial k') := ⟨I, hI.isPrime⟩
  have hP : P ∈ Set.range (B.inclusion.map jV') := by
    rw [hrange]
    exact (PrimeSpectrum.mem_basicOpen _ _).2 fun h => hc ((hmem g).1 h)
  obtain ⟨v, hv⟩ := hP
  have := hjV'
  have hy : ((B.inclusion.map jV') v).asIdeal = I := by rw [hv]
  have hmax : ((B.inclusion.map jV') v).asIdeal.IsMaximal := hy ▸ hI
  -- the evaluation at `v` through the residue field of `𝔸¹_{k'}` at `(t - c)`
  have key : ∀ r : Polynomial k', laumonPointRingHom jV' v r =
      (B.inclusion.map jV').residueFieldMap v
        ((Scheme.Spec.residueFieldIso (.of (Polynomial k')) ((B.inclusion.map jV') v)).inv
          (algebraMap (Polynomial k') ((B.inclusion.map jV') v).asIdeal.ResidueField r)) := by
    intro r
    have h1 := congrArg (fun φ => φ.hom r) (Scheme.Spec.algebraMap_residueFieldIso_inv
      (CommRingCat.of (Polynomial k')) ((B.inclusion.map jV') v))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    rw [h1]
    exact (Scheme.Γevaluation_naturality_apply (B.inclusion.map jV') v _).symm
  have hdiff : ∀ r s : Polynomial k', (r - s).eval c = 0 →
      laumonPointRingHom jV' v r = laumonPointRingHom jV' v s := by
    intro r s hrs
    rw [key, key]
    congr 2
    rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero, hy]
    exact (hmem _).2 hrs
  refine ⟨v, ?_, ⟨RingHom.injective _, fun w => ?_⟩, hdiff _ _ (by simp)⟩
  · have hpre : ({v} : Set V'.1) = (B.inclusion.map jV') ⁻¹' {P} := by
      ext w
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ hv, fun h =>
        (B.inclusion.map jV').isOpenEmbedding.injective (h.trans hv.symm)⟩
    rw [hpre]
    exact ((PrimeSpectrum.isClosed_singleton_iff_isMaximal P).2 hI).preimage
      (B.inclusion.map jV').continuous
  · obtain ⟨w₁, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      ((B.inclusion.map jV').residueFieldMap v)).surjective w
    obtain ⟨w₂, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (Scheme.Spec.residueFieldIso (.of (Polynomial k')) ((B.inclusion.map jV') v)).inv).surjective
        w₁
    obtain ⟨r, rfl⟩ := Ideal.algebraMap_residueField_surjective _ w₂
    refine ⟨r.eval c, ?_⟩
    rw [RingHom.comp_apply, hdiff (Polynomial.C (r.eval c)) r (by simp), key]

/-- **A section of `laumonFamilyPr₁`**: `Spec` of the evaluation `t ↦ x`, the diagonal
`𝔸¹ → 𝔸²`, since evaluating the constant `C r` of `k'[x][t]` at `t = x` gives back `r`. -/
public theorem laumonFourier_specMap_evalRingHom_X_comp_pr₁ (k' : Type u) [Field k'] :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (Polynomial.X : Polynomial k'))) ≫
      laumonFamilyPr₁ k' = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext1
  exact RingHom.ext fun r => by
    change Polynomial.eval Polynomial.X (Polynomial.C r) = r
    rw [Polynomial.eval_C]

/-- **The pullback of a representation along a morphism of fundamental groups, transported along
an identification of the base points, has continuous restriction of scalars.** -/
public theorem continuous_restrictScalarsRep_comp_etaleFundamentalGroupMap {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y] (g : X ⟶ Y) (x₁ : GeometricPoint X)
    {y : GeometricPoint Y} (h : x₁.map g = y) {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E]
    [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ}
    (σ : EtaleFundamentalGroup Y y →* GL (Fin m) E) (hσ : Continuous (restrictScalarsRep b σ)) :
    Continuous
      (restrictScalarsRep b (σ.comp (h ▸ (etaleFundamentalGroupMap g x₁).toMonoidHom))) := by
  subst h
  exact hσ.comp (etaleFundamentalGroupMap g x₁).continuous

/-- **Equal absolute values of the Fourier family for `σ` which stays absolutely irreducible**
(Laumon; Kedlaya, *Fourier transforms and p-adic Weil II*, Theorem 6.4, first half;
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), from the lisse locus of the family at fixed
`a` (`Stacks.EtaleCohomology.LaumonFourierLineLisseInput`), the absolute irreducibility of the
Fourier transform (L6, `Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput`), the identification
of the fibres (`Stacks.EtaleCohomology.LaumonFourierFamilyFibreInput`) and a real partner
(`Stacks.EtaleCohomology.LaumonFourierFamilyConjugateInput`); `E`-linear proper base change at the
stalks is `Stacks.EtaleCohomology.coefficientHigherDirectImageStalkLinearInput`, Weil II 1.5.1 on
the lisse locus is `Stacks.EtaleCohomology.exists_norm_eq_pow_of_isIotaRealizable_curve`. The
curve `D = 0` is the one off which the family is lisse. -/
public theorem laumonFourierEquinormStableInput_of_inputs
    (hL6 : LaumonFourierLineAbsIrrInput.{u}) (hlis : LaumonFourierLineLisseInput.{u})
    (hfib : LaumonFourierFamilyFibreInput.{u}) (hconj : LaumonFourierFamilyConjugateInput.{u}) :
    LaumonFourierEquinormStableInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ K _ _ _ hirr hst hζ ι' β _ hpure ψ hψ
  obtain ⟨N, hN⟩ := hlis B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr hst hζ ι' β hpure
    ψ hψ
  refine ⟨N, fun n₀ hn₀ hpn₀ => ?_⟩
  obtain ⟨D, hD, hDl⟩ := hN n₀ hn₀ hpn₀
  refine ⟨D, hD, ?_⟩
  intro k' _ _ _ hX' _ _ x' hx' a c hac p₀ hτ₀ _ _ _ j' kbar' _ _ _ p' n' _ _ hcard' hV'
  have hpp : p = p' := CharP.eq k'
    (charP_of_injective_algebraMap (algebraMap k k').injective p) ‹CharP k' p'›
  subst hpp
  classical
  -- a point `z̄` of the `(x, t)`-plane over `x̄'` and the pullback `σ₁` of `σ` to `𝔸¹_{k'}`
  have hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))) :=
    (schemeSizeBelow_spec_iff B.aleph0_lt_cutoff _).2 (Polynomial.cardinalMk_le_max.trans_lt
      (max_lt ((schemeSizeBelow_spec_iff B.aleph0_lt_cutoff _).1 hX') B.aleph0_lt_cutoff))
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
  obtain ⟨pz⟩ := Stacks.ArtinSchreier.nonempty_finiteEtaleFiber_cover k'
    (laumonFourierKernel k' n₀ a) zz
  have hσ₁ := continuous_restrictScalarsRep_comp_etaleFundamentalGroupMap
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
    (zz.map (laumonFamilyPr₁ k')) hz b σ hσ
  refine hDl k' a hS hX' zz hz pz hσ₁ _ ?_
  intro V' U' _ _ _ _ jV' jU g' _ _ _ jg' fV _ _ _ _ jV hjV' hrange hfV hpb hconn hlisse
  -- the rational point `v` of `V'` over `t = c`
  obtain ⟨v, hvcl, hbij, hvX⟩ := exists_laumonPoint_of_eval_ne_zero jV' hjV' _ hrange c
    (by rwa [laumonFourier_eval_eval₂])
  let xV : GeometricPoint V'.1 := geometricPointAt V'.1 v
  -- the representation `τ` of the lisse family `G_V`
  obtain ⟨r, ρ, hρ, φ, ψ₀, N', hφψ, hψφ, mτ, τ, P, Q, hτc, hPQ, hQP, hα, hτ⟩ :=
    exists_restrictScalarsRep_of_isLisse B V' xV _ E
      (algebraMap_conjIntegralSubring_algebraMap _ _) b hlisse
  -- `τ` is absolutely irreducible (L6)
  obtain ⟨p₁⟩ := Stacks.ArtinSchreier.nonempty_finiteEtaleFiber_cover k'
    (Polynomial.C a * Polynomial.X ^ n₀) (zz.map (laumonFamilyPr₁ k'))
  have hirr₁ : ∀ (K' : Type) [Field K'] [IsAlgClosed K'] [Algebra E K']
      (W : Submodule K' (Fin m → K')),
      (∀ g, ∀ w ∈ W, (characterTwist (σ.comp (hz ▸ (etaleFundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
          (zz.map (laumonFamilyPr₁ k'))).toMonoidHom))
        (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
          (Polynomial.C a * Polynomial.X ^ n₀)
          (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) (zz.map (laumonFamilyPr₁ k'))
          p₁) g).val.map (algebraMap E K') *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun K' _ _ _ => (forall_eq_bot_or_eq_top_characterTwist_iff _ _ K').2
      (hst k' (zz.map (laumonFamilyPr₁ k')) hz K')
  have hτirr := hL6 B ℓ k' p E b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom)
    (Stacks.FourierDeligne.traceChar_ne_one ψ k' hψ) hζ n₀ a hS hX' zz pz _ hσ₁ p₁ hirr₁ V' U'
    jV' jU g' jg' hjV' hpb xV ρ hρ φ ψ₀ N' hφψ hψφ τ P Q hPQ hα hτ hQP
  -- a real partner, and Weil II 1.5.1 on `V'`
  obtain ⟨r', τ', hτ', hreal⟩ := hconj B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr hst
    hζ ι' β hpure ψ hψ n₀ k' a hS hX' zz hz pz hσ₁ V' U' jV' jU g' jg' fV hjV' hfV hpb xV ρ hρ φ
    ψ₀ N' hφψ hψφ τ P Q hPQ hα hτ hQP
  have := hconn (AlgebraicClosure k')
  obtain ⟨β', -, hβ'⟩ := exists_norm_eq_pow_of_isIotaRealizable_curve B V' ℓ fV jV
    (AlgebraicClosure k') p n' hcard' hℓp xV E b τ hτc τ' hτ' ι' hreal hτirr
  refine ⟨β' ^ residueDegree fV v, fun z hz' => ?_⟩
  -- the fibre characteristic polynomial is that of `τ(F_v)`
  let vc : closedPoints V'.1 := ⟨v, hvcl⟩
  have : Finite (V'.1.residueField v) := finite_residueField fV v hvcl
  let : Fintype (V'.1.residueField v) := Fintype.ofFinite _
  have : CharP (V'.1.residueField v) p := charP_of_injective_ringHom hbij.injective p
  have hcardv : Fintype.card (V'.1.residueField v) = p ^ (n' * residueDegree fV v) := by
    rw [← Nat.card_eq_fintype_card, natCard_residueField_eq_pow_residueDegree fV v, hcard',
      pow_mul]
  have ha := charpoly_rationalStalkFrobenius_eq_restrictScalarsRep_family B V' xV _ ρ hρ φ ψ₀ N'
    hφψ hψφ E (algebraMap_conjIntegralSubring_algebraMap _ _) b fV τ P Q hPQ hα hτ hQP vc
  have hfinS := finite_rationalStalkLeft_of_isogeny B V' xV _ ρ hρ φ ψ₀ N' hφψ hψφ
    (geometricPointAt V'.1 v)
  refine coefficientHigherDirectImageStalkLinearInput B ℓ k' U' V' g' jg' fV vc
    (AlgebraicClosure (V'.1.residueField v)) p (n' * residueDegree fV v) hcardv _ ?_
  intro Y _ i fY _ _ _ hpbY jY hY
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  obtain ⟨hfinY, heqb⟩ := hY (LAdicSheaf.CoefficientSheaf.inverseImage jU
    (laumonFourierFamilySheaf k' B hS b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom)
      n₀ a zz pz _ hσ₁)) 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
  have := hfinY
  have heqc := hfib B U ℓ k e x E b σ ψ n₀ k' a hS hX' zz hz pz hσ₁ V' U' jV' jU g' hjV' hpb v
    Y i fY hpbY jY (AlgebraicClosure (V'.1.residueField v)) p (n' * residueDegree fV v) hcardv c
    hbij hvX hX' x' hx' p₀ hτ₀ j' kbar' p n' hcard'
  rw [← ha.symm.trans (heqb.trans heqc)] at hz'
  exact hβ' vc z hz'

end Stacks.EtaleCohomology

end
