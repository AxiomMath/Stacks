module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCoefficientRepresentationFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyLisseLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldExtensionPointTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImageCoefficient

/-!
# Purity of the representation `τ` of `G|_V` in Laumon's degeneration

In Laumon's degeneration argument ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) the
family sheaf `K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t (xⁿ⁰ + c x))` on `𝔸² = Spec k'[x][t]`
(`Stacks.EtaleCohomology.laumonFamilySheaf`) is restricted to `U' = pr₂⁻¹(V')` over an open `V'`
of the `t`-line inside `D(f)`, where `f` is divisible by `D(t, c t)`; `G_V = R¹g'_!(K|_{U'})` is
lisse there (`Stacks.EtaleCohomology.exists_laumonFamily_lisseLocus`) and is given by an
`E`-linear representation `τ` of `π₁(V', x̄)`
(`Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse`). This file proves that `τ` is
`ι'`-pure of weight `β + 1` (`Stacks.EtaleCohomology.laumonFamily_isPure_restrictScalarsRep`),
from

* (a) the `E`-linear characteristic polynomial of `τ(F_v)` is that of the geometric Frobenius on
  the rational stalk `(G_V)_v̄`
  (`Stacks.EtaleCohomology.charpoly_rationalStalkFrobenius_eq_restrictScalarsRep_family`);
* (b) `E`-linear proper base change at the stalk: `(G_V)_v̄` is `H¹_c` of the fibre over `κ(v)`
  with the Frobenius of `κ(v)`, `E`-linearly
  (`Stacks.EtaleCohomology.CoefficientHigherDirectImageStalkLinearInput`);
* (c) the fibre of the family over `v` is the twisted sheaf `ℱ_σ ⊗ L_ψ(s xⁿ⁰ + c s x)` on
  `𝔸¹_{κ(v)}` of `Stacks.EtaleCohomology.LaumonFibrePure`, `s` the value of `t` at `v`
  (`Stacks.EtaleCohomology.LaumonFamilyFibreLinearInput`);
* (d) `D(s, c s) ≠ 0`, since `v ∈ D(f)` (`Stacks.EtaleCohomology.laumonPoint_eval_ne_zero`);
* (e) the purity of the fibres `Stacks.EtaleCohomology.LaumonFibrePure`, with
  `#κ(v) = #k' ^ deg v`.

The two inputs (b) and (c) are stated as propositions.

## Main definitions

* `Stacks.EtaleCohomology.laumonPointRingHom`: the evaluation `k'[t] → κ(v)` at a point of `V'`.
* `Stacks.EtaleCohomology.CoefficientHigherDirectImageStalkLinearInput` (b).
* `Stacks.EtaleCohomology.LaumonFamilyFibreLinearInput` (c).

## Main results

* `Stacks.EtaleCohomology.laumonPoint_eval_ne_zero` (d).
* `Stacks.EtaleCohomology.laumonFamily_isPure_restrictScalarsRep`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Point

variable {k' : Type u} [Field k'] {B : BigEtaleSite.{u}}
  {hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k')))} {V' : B.Scheme}
  (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL) (v : V'.1)

/-- **The evaluation `k'[t] → κ(v)` at a point `v` of `V' → 𝔸¹_{k'}`**: global sections of
`𝔸¹_{k'}` pulled back to `V'` and evaluated at `v`. -/
public def laumonPointRingHom : Polynomial k' →+* V'.1.residueField v :=
  (V'.1.Γevaluation v).hom.comp (((B.inclusion.map jV').appTop).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k'))).inv.hom)

/-- The `k`-algebra structure on `κ(v)` through `k → k' → k'[t] → κ(v)`. -/
public abbrev laumonPointAlgebra (k : Type u) [Field k] [Algebra k k'] :
    Algebra k (V'.1.residueField v) :=
  ((laumonPointRingHom jV' v).comp (algebraMap k (Polynomial k'))).toAlgebra

/-- **A polynomial not vanishing on `V'` does not vanish at `v`**: if `V'` lies in `D(f)`, then
`f(v) ≠ 0` in `κ(v)`. -/
public theorem laumonPointRingHom_ne_zero (f : Polynomial k')
    (hrange : Set.range (B.inclusion.map jV') ⊆
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Polynomial k')))) :
    laumonPointRingHom jV' v f ≠ 0 := by
  simp only [laumonPointRingHom, RingHom.comp_apply]
  refine (Scheme.evaluation_ne_zero_iff_mem_basicOpen _ _ _ _).2 ?_
  have h2 : (B.inclusion.map jV') v ∈ (Spec (CommRingCat.of (Polynomial k'))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k'))).inv f) := by
    rw [basicOpen_eq_of_affine]
    exact hrange ⟨v, rfl⟩
  have h3 : v ∈ (B.inclusion.map jV') ⁻¹ᵁ (Spec (CommRingCat.of (Polynomial k'))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k'))).inv f) := h2
  exact (Scheme.preimage_basicOpen (B.inclusion.map jV')
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k'))).inv f)).le h3

/-- **(d) `D(s, c s) ≠ 0` at a point of `V' ⊆ D(f)`**, `s = t(v)`, when `D(t, c t)` divides `f`:
the hypothesis `D(a, c) ≠ 0` of `Stacks.EtaleCohomology.LaumonFibrePure` at
`(a, c) = (s, c s)` over `κ(v)`. -/
public theorem laumonPoint_eval_ne_zero (k : Type u) [Field k] [Algebra k k']
    (D : MvPolynomial (Fin 2) k) (c : k') (f : Polynomial k')
    (hDf :
      MvPolynomial.aeval ![(Polynomial.X : Polynomial k'), Polynomial.C c * Polynomial.X] D ∣ f)
    (hrange : Set.range (B.inclusion.map jV') ⊆
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Polynomial k')))) :
    letI := laumonPointAlgebra jV' v k
    MvPolynomial.eval ![laumonPointRingHom jV' v Polynomial.X,
        laumonPointRingHom jV' v (Polynomial.C c) * laumonPointRingHom jV' v Polynomial.X]
      (MvPolynomial.map (algebraMap k (V'.1.residueField v)) D) ≠ 0 := by
  let := laumonPointAlgebra jV' v k
  set φ := laumonPointRingHom jV' v
  have h : φ (MvPolynomial.aeval ![(Polynomial.X : Polynomial k'), Polynomial.C c * Polynomial.X]
      D) = MvPolynomial.eval ![φ Polynomial.X, φ (Polynomial.C c) * φ Polynomial.X]
        (MvPolynomial.map (algebraMap k (V'.1.residueField v)) D) := by
    rw [MvPolynomial.map_aeval, MvPolynomial.eval_map, MvPolynomial.coe_eval₂Hom]
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact map_mul φ _ _
  rw [← h]
  obtain ⟨g, hg⟩ := hDf
  intro h0
  apply laumonPointRingHom_ne_zero jV' v f hrange
  rw [hg, map_mul, h0, zero_mul]

end Point

/-- **(b) `E`-linear proper base change at the stalks of `Rʳ g_!`** (Tags 0F7L, 0F7I, with
coefficients): for `g : U ⟶ W` separated of finite type with a compactification and a closed
point `w` of `W` (of finite type over a finite field `k`), there are a fibre `Y = U ×_W Spec κ(w)`
of `g` over `w` in the big étale site and a compactification of `Y` over `κ(w)` such that for
every ℓ-adic sheaf `F` with coefficients in a `ℤ_ℓ`-algebra `O` and `E = O[1/ℓ]`, if the rational
stalk of `Rʳ g_! F` at `w̄` is finite-dimensional then so is `Hʳ_c(Y_{κ̄}, F|_Y ⊗ ℚ_ℓ)`, and the
geometric Frobenius at `w` on `(Rʳ g_! F)_w̄ ⊗ ℚ_ℓ` and the Frobenius of `κ(w)` on
`Hʳ_c(Y_{κ̄}, F|_Y ⊗ ℚ_ℓ)` have the same `E`-linear characteristic polynomial (the `E`-structures
coming from the actions of `O`). The existence is stated in continuation-passing form. The
`ℚ_ℓ`-linear form (with `Y` the fibre `U_w`) is
`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageStalkInput_higherDirectImageShriek`. -/
public def CoefficientHigherDirectImageStalkLinearInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fintype k] (U W : B.Scheme) [IsNoetherian U.1] [IsNoetherian W.1]
    (g : U ⟶ W) [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
    (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW] (w : closedPoints W.1)
    [Fintype (W.1.residueField w.1)] (kbar : Type u) [Field kbar]
    [Algebra (W.1.residueField w.1) kbar] [IsAlgClosure (W.1.residueField w.1) kbar] (p n : ℕ)
    [Fact p.Prime] [CharP (W.1.residueField w.1) p]
    (hcard : Fintype.card (W.1.residueField w.1) = p ^ n) (C : Prop),
    (∀ (Y : B.Scheme) [IsNoetherian Y.1] (i : Y ⟶ U) (fY : Y.1 ⟶ Spec (.of (W.1.residueField w.1)))
      [LocallyOfFiniteType fY] [QuasiCompact fY] [IsSeparated fY],
      IsPullback (B.inclusion.map i) fY (B.inclusion.map g) (W.1.fromSpecResidueField w.1) →
      ∀ jY : CompactificationOf (Over.mk fY),
      (∀ {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B U ℓ O)
        (r : ℕ) (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Algebra O E]
        [IsLocalization (Submonoid.powers (ℓ : O)) E]
        (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c)
        [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalStalkLeft B W ℓ
          (F.higherDirectImageShriek B ℓ g jg r).toLAdicSheaf (geometricPointAt W.1 w.1))],
        ∃ hY : FiniteDimensional ℚ_[ℓ]
            (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
              (LAdicSheaf.CoefficientSheaf.inverseImage i F).toLAdicSheaf r),
          letI := (F.higherDirectImageShriek B ℓ g jg r).rationalStalkModule
            (geometricPointAt W.1 w.1) E
          haveI := (F.higherDirectImageShriek B ℓ g jg r).rationalStalkModule_isScalarTower
            (geometricPointAt W.1 w.1) E hOE
          haveI : Module.Finite E (LAdicSheaf.rationalStalkLeft B W ℓ
              (F.higherDirectImageShriek B ℓ g jg r).toLAdicSheaf (geometricPointAt W.1 w.1)) :=
            Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
          letI := (LAdicSheaf.CoefficientSheaf.inverseImage i F).rationalCohomologyModule fY jY
            kbar r E
          haveI := (LAdicSheaf.CoefficientSheaf.inverseImage i
            F).rationalCohomologyModule_isScalarTower fY jY kbar r E hOE
          haveI := hY
          haveI : Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ
              fY jY kbar (LAdicSheaf.CoefficientSheaf.inverseImage i F).toLAdicSheaf r) :=
            Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
          ((F.higherDirectImageShriek B ℓ g jg r).rationalStalkFrobenius E w.1
              (finite_residueField fW w.1 w.2)).charpoly =
            ((LAdicSheaf.CoefficientSheaf.inverseImage i
              F).rationalGeometricCompactlySupportedFrobenius fY jY kbar r E p n hcard).charpoly) →
      C) → C

/-- **(c) The fibres of Laumon's family over the `t`-line**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): for the family sheaf
`K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t (xⁿ⁰ + c x))` on `Spec k'[x][t]`
(`Stacks.EtaleCohomology.laumonFamilySheaf`, `σ₁` the pullback of `σ` to `𝔸¹_{k'}`,
`ψ' = ψ ∘ Tr_{k'/k}`), its restriction `K|_{U'}` to the preimage `U'` of an open `V'` of the
`t`-line, a point `v` of `V'` with finite residue field `κ(v)` and any fibre `Y` of `U' → V'`
over `v` with a compactification over `κ(v)`, the fibre `Y` is `𝔸¹_{κ(v)}` and `K|_Y` is the
twisted sheaf `ℱ_σ ⊗ L_ψ''(s xⁿ⁰ + (c s) x)` of `Stacks.EtaleCohomology.LaumonFibrePure` over
`κ(v)` (`s = t(v)`, `ψ'' = ψ ∘ Tr_{κ(v)/k}`), so that the `E`-linear Frobenius of `κ(v)` on
`H¹_c(Y_{κ̄}, K|_Y ⊗ ℚ_ℓ)` has the characteristic polynomial of the one on
`H¹_c(𝔸¹_{κ̄}, ℱ_σ ⊗ L_ψ''(s xⁿ⁰ + (c s) x) ⊗ ℚ_ℓ)`, for suitable data of `LaumonFibrePure`
(a geometric point `x̄'` of `𝔸¹_{κ(v)}` over `x̄`, a point of the Artin–Schreier cover, a
compactification of `𝔸¹_{κ(v)}`). Stated in continuation-passing form. -/
public def LaumonFamilyFibreLinearInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fintype k] (U : B.Scheme) [ConnectedSpace U.1] [IsNoetherian U.1]
    (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsIso e] (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (ψ : AddChar k E) (n₀ : ℕ) (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (c : k')
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c)))
    (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
        (z.map (laumonFamilyPr₁ k'))).toMonoidHom))))
    (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1]
    (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
    (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V'),
    IsOpenImmersion (B.inclusion.map jV') →
    IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV') →
    ∀ (v : V'.1) [Fintype (V'.1.residueField v)] (Y : B.Scheme) [IsNoetherian Y.1] (i : Y ⟶ U')
      (fY : Y.1 ⟶ Spec (.of (V'.1.residueField v))) [LocallyOfFiniteType fY] [QuasiCompact fY]
      [IsSeparated fY],
    IsPullback (B.inclusion.map i) fY (B.inclusion.map g') (V'.1.fromSpecResidueField v) →
    ∀ (jY : CompactificationOf (Over.mk fY)) (kbar : Type u) [Field kbar]
      [Algebra (V'.1.residueField v) kbar] [IsAlgClosure (V'.1.residueField v) kbar] (p n : ℕ)
      [Fact p.Prime] [CharP (V'.1.residueField v) p]
      (hcard : Fintype.card (V'.1.residueField v) = p ^ n),
    haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
      inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
    letI K := LAdicSheaf.CoefficientSheaf.inverseImage i
      (LAdicSheaf.CoefficientSheaf.inverseImage jU (laumonFamilySheaf k' B hS b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁))
    letI := laumonPointAlgebra jV' v k
    ∀ [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY
        jY kbar K.toLAdicSheaf 1)] (C : Prop),
    (∀ (hX' : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (V'.1.residueField v)))))
      [IsNoetherian (Spec (.of (Polynomial (V'.1.residueField v))))]
      [ConnectedSpace (Spec (.of (Polynomial (V'.1.residueField v))))]
      (x' : GeometricPoint (Spec (.of (Polynomial (V'.1.residueField v)))))
      (hx' : x'.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (algebraMap k (V'.1.residueField v)))) ≫ inv e) = x)
      (p₀' : (finiteEtaleFiberFunctor x').obj (Stacks.ArtinSchreier.cover (V'.1.residueField v)
        (Polynomial (V'.1.residueField v))
        (Polynomial.C (laumonPointRingHom jV' v Polynomial.X) * Polynomial.X ^ n₀ +
          Polynomial.C (laumonPointRingHom jV' v (Polynomial.C c) *
            laumonPointRingHom jV' v Polynomial.X) * Polynomial.X)))
      (hτ : Continuous (restrictScalarsRep b (characterTwist
        (σ.comp (hx' ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap k (V'.1.residueField v)))) ≫ inv e) x').toMonoidHom))
        (Stacks.ArtinSchreier.artinSchreierCharacter (V'.1.residueField v)
          (Polynomial (V'.1.residueField v))
          (Polynomial.C (laumonPointRingHom jV' v Polynomial.X) * Polynomial.X ^ n₀ +
            Polynomial.C (laumonPointRingHom jV' v (Polynomial.C c) *
              laumonPointRingHom jV' v Polynomial.X) * Polynomial.X)
          (ψ.compAddMonoidHom (Algebra.trace k (V'.1.residueField v)).toAddMonoidHom) x' p₀'))))
      [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
        (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v)))))]
      [QuasiCompact (Spec.map (CommRingCat.ofHom
        (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v)))))]
      [IsSeparated (Spec.map (CommRingCat.ofHom
        (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v)))))]
      (j' : CompactificationOf (Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v)))))))
      (hV : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
        (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') ℓ
        (Spec.map (CommRingCat.ofHom
          (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v))))) j' kbar
        (LAdicSheaf.representationSheaf B
          (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX')
          x' (restrictScalarsRep b _) hτ) 1)),
      letI := K.rationalCohomologyModule fY jY kbar 1 E
      haveI := K.rationalCohomologyModule_isScalarTower fY jY kbar 1 E
        (algebraMap_conjIntegralSubring_algebraMap _ _)
      haveI : Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY
          kbar K.toLAdicSheaf 1) := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
      letI := (restrictScalarsRepCoefficientSheaf B
        (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') x' b _
          hτ).rationalCohomologyModule (Spec.map (CommRingCat.ofHom
            (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v))))) j' kbar 1 E
      haveI := (restrictScalarsRepCoefficientSheaf B
        (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') x' b _
          hτ).rationalCohomologyModule_isScalarTower (Spec.map (CommRingCat.ofHom
            (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v))))) j' kbar 1 E
          (algebraMap_conjIntegralSubring_algebraMap _ _)
      haveI : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
          (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') ℓ
          (Spec.map (CommRingCat.ofHom
            (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v))))) j' kbar
          (restrictScalarsRepCoefficientSheaf B
            (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') x' b _
              hτ).toLAdicSheaf 1) := hV
      haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
          (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') ℓ
          (Spec.map (CommRingCat.ofHom
            (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v))))) j' kbar
          (restrictScalarsRepCoefficientSheaf B
            (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') x' b _
              hτ).toLAdicSheaf 1) :=
        Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
      (K.rationalGeometricCompactlySupportedFrobenius fY jY kbar 1 E p n hcard).charpoly =
        ((restrictScalarsRepCoefficientSheaf B
          (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') x' b _
            hτ).rationalGeometricCompactlySupportedFrobenius (Spec.map (CommRingCat.ofHom
              (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v))))) j' kbar 1 E
                p n hcard).charpoly → C) → C

section Reduction

variable (k' : Type u) [Field k'] [Fintype k'] (B : BigEtaleSite.{u})
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (ℓ : ℕ) [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E) (n₀ : ℕ) (c : k')
  (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
  (p₀ : (finiteEtaleFiberFunctor z).obj
    (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c))) {m : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **`G_V = R¹g'_!(K|_{U'})`**: the higher direct image with compact support of the restriction
of the family sheaf `K` (`Stacks.EtaleCohomology.laumonFamilySheaf`) to `U' ⟶ Spec k'[x][t]`,
along `g' : U' ⟶ V'`, with the induced action of the integral part of `E`. -/
public abbrev laumonFamilyRestrictedHigherDirectImage
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁)) {V' U' : B.Scheme}
    [IsNoetherian V'.1] [IsNoetherian U'.1]
    (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')
    [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
    [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g'))) :=
  haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  (LAdicSheaf.CoefficientSheaf.inverseImage jU
    (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁)).higherDirectImageShriek B ℓ g' jg' 1

end Reduction

/-- **Purity of the representation `τ` of `G_V = R¹g'_!(K|_{U'})`**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): let `K` be the family sheaf on
`Spec k'[x][t]` of the pullback `σ₁` of `σ` to `𝔸¹_{k'}`
(`Stacks.EtaleCohomology.laumonFamilySheaf`), `V' ⊆ D(f)` an open of the `t`-line with
`D(t, c t) ∣ f`, `g' : U' ⟶ V'` the restriction of `pr₂`, and
`ρ, φ, ψ, N, τ, P, Q` the data of `Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse`
for `G_V` at a geometric point `x̄` of `V'`. If the fibres of the two-parameter family are pure of
weight `β + 1` off `D = 0` (`Stacks.EtaleCohomology.LaumonFibrePure`), then `τ` is `ι'`-pure
of weight `β + 1`: the eigenvalues of `τ(F_v)` at a closed point `v` have absolute value
`q^{deg v (β + 1) / 2}`, `q = #k'`. The inputs are `E`-linear proper base change at the stalks
(`Stacks.EtaleCohomology.CoefficientHigherDirectImageStalkLinearInput`) and the identification of
the fibres of the family (`Stacks.EtaleCohomology.LaumonFamilyFibreLinearInput`). -/
public theorem laumonFamily_isPure_restrictScalarsRep
    (hb : CoefficientHigherDirectImageStalkLinearInput.{u})
    (hc : LaumonFamilyFibreLinearInput.{u})
    (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k : Type u) [Field k] [Finite k] (U : B.Scheme) [ConnectedSpace U.1] [IsNoetherian U.1]
    (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsIso e] (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (ι' : E →+* ℂ) (β : ℤ) (ψ : AddChar k E) (n₀ : ℕ) (D : MvPolynomial (Fin 2) k)
    (hfib : LaumonFibrePure B U ℓ k e x E b σ ι' β ψ n₀ D)
    (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (c : k')
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c)))
    (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
        (z.map (laumonFamilyPr₁ k'))).toMonoidHom))))
    (f : Polynomial k')
    (hDf :
      MvPolynomial.aeval ![(Polynomial.X : Polynomial k'), Polynomial.C c * Polynomial.X] D ∣ f)
    (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1] [ConnectedSpace V'.1]
    (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
    (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')
    [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
    [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g')))
    (hjV' : IsOpenImmersion (B.inclusion.map jV'))
    (hrange : Set.range (B.inclusion.map jV') ⊆
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Polynomial k'))))
    (hpb : IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV'))
    (fV : V'.1 ⟶ Spec (.of k')) [LocallyOfFiniteType fV] (p n' : ℕ) [Fact p.Prime] [CharP k' p]
    (hcard' : Fintype.card k' = p ^ n') (xV : GeometricPoint V'.1) {r : ℕ}
    (ρ : EtaleFundamentalGroup V'.1 xV →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (φ : (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jU g'
          jg').toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B V' xV ρ hρ)
    (ψ₀ : LAdicSheaf.representationSheaf B V' xV ρ hρ ⟶
      (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jU g'
          jg').toLAdicSheaf) (N : ℕ)
    (hφψ : φ ≫ ψ₀ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ₀ ≫ φ = (ℓ ^ N) • 𝟙 _) {mτ : ℕ}
    (τ : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) E)
    (P : Matrix (Fin r) (Fin (mτ * d)) ℚ_[ℓ]) (Q : Matrix (Fin (mτ * d)) (Fin r) ℚ_[ℓ])
    (hPQ : P * Q = 1)
    (hα : ∀ e' : E, Q * isogenyCoefficientAlgHom B V' xV
      (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jU g' jg')
      ρ hρ φ ψ₀ N E hφψ hψφ (algebraMap_conjIntegralSubring_algebraMap _ _) e' * P =
        restrictScalarsMatrix b (Matrix.scalar (Fin mτ) e'))
    (hτ : ∀ g : EtaleFundamentalGroup V'.1 xV,
      haveI := compactSpace_etaleFundamentalGroup V'.1 xV
      Q * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
        (integralModel ρ hρ g)).val * P = (restrictScalarsRep b τ g).val)
    (hQP : Q * P = 1) :
    ∀ (v : closedPoints V'.1) (z' : ℂ),
      ((τ (geometricFrobeniusFamily fV xV v)).val.charpoly.map ι').IsRoot z' →
      ‖z'‖ = ((p ^ n' : ℕ) : ℝ) ^ (((residueDegree fV v.1 : ℤ) * ((β + 1 : ℤ) : ℝ) : ℝ) / 2) := by
  have := Fintype.ofFinite k
  intro v z' hz'
  have : Finite (V'.1.residueField v.1) := finite_residueField fV v.1 v.2
  let : Fintype (V'.1.residueField v.1) := Fintype.ofFinite _
  have : CharP (V'.1.residueField v.1) p :=
    charP_of_injective_ringHom ((laumonPointRingHom jV' v.1).comp Polynomial.C).injective p
  have hcardv : Fintype.card (V'.1.residueField v.1) = p ^ (n' * residueDegree fV v.1) := by
    rw [← Nat.card_eq_fintype_card, natCard_residueField_eq_pow_residueDegree fV v.1, hcard',
      pow_mul]
  have ha := charpoly_rationalStalkFrobenius_eq_restrictScalarsRep_family B V' xV _ ρ hρ φ ψ₀ N
    hφψ hψφ E (algebraMap_conjIntegralSubring_algebraMap _ _) b fV τ P Q hPQ hα hτ hQP v
  have hfinS := finite_rationalStalkLeft_of_isogeny B V' xV _ ρ hρ φ ψ₀ N hφψ hψφ
    (geometricPointAt V'.1 v.1)
  refine hb B ℓ k' U' V' g' jg' fV v (AlgebraicClosure (V'.1.residueField v.1)) p
    (n' * residueDegree fV v.1) hcardv _ ?_
  intro Y _ i fY _ _ _ hpbY jY hY
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  obtain ⟨hfinY, heqb⟩ := hY (LAdicSheaf.CoefficientSheaf.inverseImage jU
    (laumonFamilySheaf k' B hS b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z
      p₀ _ hσ₁)) 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
  have := hfinY
  refine hc B ℓ k U e x E b σ ψ n₀ k' c hS hL z hz p₀ hσ₁ V' U' jV' jU g' hjV' hpb v.1 Y i fY
    hpbY jY (AlgebraicClosure (V'.1.residueField v.1)) p (n' * residueDegree fV v.1) hcardv _ ?_
  intro hX' _ _ x' hx' p₀' hτ' _ _ _ j' hV heqc
  let := laumonPointAlgebra jV' v.1 k
  have := hV
  have hpure := hfib (V'.1.residueField v.1) hX' x' hx' _ _
    (laumonPoint_eval_ne_zero jV' v.1 k D c f hDf hrange) p₀' hτ' j'
    (AlgebraicClosure (V'.1.residueField v.1)) p (n' * residueDegree fV v.1) hcardv
  have hchar := ha.symm.trans (heqb.trans heqc)
  rw [hchar] at hz'
  have hnorm : ‖z'‖ = ((p ^ (n' * residueDegree fV v.1) : ℕ) : ℝ) ^ (((β + 1 : ℤ) : ℝ) / 2) := by
    first
      | exact hpure z' hz'
  refine hnorm.trans ?_
  rw [pow_mul, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring

end Stacks.EtaleCohomology

end
