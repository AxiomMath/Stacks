module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierEquinormInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonLineBasicOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonLineUniformBasicOpen

/-!
# The lisse locus of the Fourier family, line by line

`Stacks.EtaleCohomology.LaumonFourierLineLisseInput`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) asks for one curve `D ≠ 0` of the
`(a, t)`-plane over `k` such that for every finite extension `k'` of `k` and every `a ∈ k'` the
Fourier family `G_V = R¹g'_!(pr₁^*ℱ_σ ⊗ L_ψ'(a xⁿ + x t))` is lisse over `V' = D(D(a, t))`,
together with all the data of `V'` (the open immersion, `U' = pr₂⁻¹(V')`, compactifications, the
curve structure of `V'` and its geometric connectedness).

This file reduces it to the lisseness alone, given line by line
(`Stacks.EtaleCohomology.LaumonFourierLineLisseFibreInput`): for `m = 0` and for every irreducible
`m ∈ k[a]` there is `h_m ∈ k[a, t]` not divisible by `m(a)` such that on every line `a = a₀` with
`m(a₀) = 0` (over any `k'`) the family is lisse over every open `V'` of the `t`-line inside
`D(h_m(a₀, t))` (`Stacks.EtaleCohomology.LaumonFourierLineLisseOn`). For `m = 0` this is a
statement on all lines at once, off the curve `h_0 = 0`; it is what the model of the family over
`k` (on `𝔸³_k`, with the generic lisse locus of `R¹` over `𝔸²_{(a, t)}`) or Laumon's local theory
(for `a ≠ 0` and `n` larger than the slopes of `σ` at `∞`, `ℱ_σ ⊗ L_ψ(a xⁿ)` is totally wild at `∞`
of Swan conductor `n`, and its Fourier transform is lisse on all of `𝔸¹`) provide; the
irreducible `m` take care of the finitely many lines `a = a₀` on which `h_0` vanishes identically
(for the local theory, the line `a = 0`).

The reduction (`Stacks.EtaleCohomology.laumonFourierLineLisseInput_of_fibre`) chooses the curve
with `Stacks.EtaleCohomology.exists_laumonLine_uniform_basicOpen` (so that `D(a₀, t) ≠ 0` on every
line and `D(D(a₀, t))` lies in some `D(h_m(a₀, t))` with `m(a₀) = 0`), and supplies the open
`V' = D(D(a₀, t))` with all its data by `Stacks.EtaleCohomology.laumonLineBasicOpen_elim`.

## Main definitions

* `Stacks.EtaleCohomology.LaumonFourierLineLisseOn`: lisseness of the Fourier family over the
  opens of the lines `a = a₀` with `m(a₀) = 0` lying inside `D(h(a₀, t))`.
* `Stacks.EtaleCohomology.LaumonFourierLineLisseFibreInput`: the line-by-line lisseness of the
  Fourier family.

## Main results

* `Stacks.EtaleCohomology.laumonFourierLineLisseInput_of_fibre`: the line-by-line lisseness
  implies `Stacks.EtaleCohomology.LaumonFourierLineLisseInput`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

section Family

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [Fact ℓ.Prime] [ConnectedSpace U.1]
  (k : Type u) [Field k] [Fintype k] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsIso e]
  (x : GeometricPoint U.1) (E : Type) [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
  (ψ : AddChar k E) (n : ℕ)

/-- **The Fourier family is lisse off `h(a₀, t) = 0` on the lines `a = a₀` with `m(a₀) = 0`**:
for every finite extension `k'` of `k` and `a ∈ k'` with `m(a) = 0`, all the data of the family
(as in `Stacks.EtaleCohomology.LaumonFourierLineLisse`), every open `V'` of the `t`-line with image
inside `D(h(a, t))`, `U' = pr₂⁻¹(V')`, `g' : U' → V'` the restriction of `pr₂` and any
compactification of `g'`, `G_V = R¹g'_!(pr₁^*ℱ_σ ⊗ L_ψ'(a xⁿ + x t))|_{U'}` is lisse
(`ψ' = ψ ∘ Tr_{k'/k}`). -/
public def LaumonFourierLineLisseOn (mk : Polynomial k) (h : MvPolynomial (Fin 2) k) : Prop :=
  ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (a : k'), Polynomial.aeval a mk = 0 →
    ∀ (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
    (pz : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
    (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
        (z.map (laumonFamilyPr₁ k'))).toMonoidHom))))
    (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1]
    (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
    (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')
    [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
    [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g'))),
    IsOpenImmersion (B.inclusion.map jV') →
    Set.range (B.inclusion.map jV') ⊆ (PrimeSpectrum.basicOpen (MvPolynomial.eval₂
      (Polynomial.C.comp (algebraMap k k')) ![Polynomial.C a, Polynomial.X] h) :
        Set (PrimeSpectrum (Polynomial k'))) →
    IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV') →
    (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b
      (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _ hσ₁ jU g'
        jg').toLAdicSheaf.IsLisse

end Family

/-- **The lisse locus of the Fourier family, line by line** (Laumon; Kedlaya, *Fourier transforms
and p-adic Weil II*, §6.4): under the hypotheses of
`Stacks.EtaleCohomology.LaumonFourierLineLisseInput`, there is `N` such that for `n > N` prime to
`p`, for `m = 0` and for every irreducible `m ∈ k[a]` there is `h ∈ k[a, t]` not divisible by
`m(a)` with `Stacks.EtaleCohomology.LaumonFourierLineLisseOn` for `(m, h)`. -/
public def LaumonFourierLineLisseFibreInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e] [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (_ : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    LaumonStablyAbsIrr k e x σ → (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
        kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
      ∀ mk : Polynomial k, (mk = 0 ∨ Irreducible mk) → ∃ h : MvPolynomial (Fin 2) k,
        ¬ Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) mk ∣ h ∧
          LaumonFourierLineLisseOn B U ℓ k e x E b σ ψ n mk h

/-- **The lisse locus of the Fourier family with all its data, from the line-by-line lisseness**:
`Stacks.EtaleCohomology.LaumonFourierLineLisseFibreInput` implies
`Stacks.EtaleCohomology.LaumonFourierLineLisseInput`. The curve `D` is that of
`Stacks.EtaleCohomology.exists_laumonLine_uniform_basicOpen`, and the open `V' = D(D(a, t))` with
`U'`, `g'`, its compactification, the curve structure `fV` with its compactification and the
geometric connectedness are those of `Stacks.EtaleCohomology.laumonLineBasicOpen_elim`. -/
public theorem laumonFourierLineLisseInput_of_fibre (H : LaumonFourierLineLisseFibreInput.{u}) :
    LaumonFourierLineLisseInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ hef j kbar _ _ _ _ p q _ _ hcard hℓp x E _ _ _
    d b m σ hσ K _ _ _ hirr hstab hζ ι' β hV hpure ψ hψ
  obtain ⟨N, hN⟩ := H B U ℓ k f e hef j kbar p q hcard hℓp x E b σ hσ K hirr hstab hζ ι' β hpure
    ψ hψ
  refine ⟨N, fun n hn hpn => ?_⟩
  obtain ⟨D, hD0, hD⟩ := exists_laumonLine_uniform_basicOpen
    (fun mk h => LaumonFourierLineLisseOn B U ℓ k e x E b σ ψ n mk h) (hN n hn hpn)
  refine ⟨D, hD0, ?_⟩
  intro k' _ _ _ a hS hL z hz pz hσ₁ C hC
  obtain ⟨hne, mk, h, hQ, hmk, hle⟩ := hD k' a
  refine laumonLineBasicOpen_elim k' B hS hL hne C ?_
  intro V' U' _ _ _ _ _ jV' jU g' _ _ _ jg' fV _ _ _ _ jfV hopen hrange hfV hpb hgeo
  exact hC V' U' jV' jU g' jg' fV jfV hopen hrange hfV hpb (fun Ω _ _ _ => hgeo Ω)
    (hQ k' a hmk hS hL z hz pz hσ₁ V' U' jV' jU g' jg' hopen
      (hrange.trans_subset (SetLike.coe_subset_coe.2 hle)) hpb)

end Stacks.EtaleCohomology

end
