module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierEquinormStable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIFinalAssembly
public import StacksFrontier.AlgebraicGeometry.Curves.AffineLineShiftFiniteEtale

/-!
# The reduction of fibre purity to representations which stay absolutely irreducible

Kedlaya's reduction to geometric irreducibility (*Fourier transforms and p-adic Weil II*, §6.4;
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) of the purity of the fibres of the Fourier
family (`Stacks.EtaleCohomology.LaumonFibrePurityInput`) to its case of representations which stay
absolutely irreducible over every finite extension
(`Stacks.EtaleCohomology.LaumonFibrePurityStableInput`) has three steps, stated here as
propositions:

* `Stacks.EtaleCohomology.LaumonStableDecompositionInput` (representation theory): over a finite
  extension `k₀` of `k` and a finite extension `E'` of `E`, the pullback of an absolutely
  irreducible `σ` to `π₁(𝔸¹_{k₀})` is a direct sum of constituents which stay absolutely
  irreducible over every further finite extension (finitely many constituents, an open normal
  subgroup of finite index, Clifford), each `ι''`-pure of the weight of `σ`;
* `Stacks.EtaleCohomology.LaumonFibrePureConstituentInput`: the fibres of a direct sum are pure off
  the product of the curves of the constituents (`H¹_c` of a direct sum is the direct sum, and
  commutes with the extension of scalars `E → E'`);
* `Stacks.EtaleCohomology.LaumonFibrePureDescentInput`: fibre purity descends along a finite
  extension `k₀ / k` of the base field (at a fibre over `k'`, pass to the compositum `k' k₀`, whose
  Frobenius is a power of that of `k'` on the same geometric cohomology; the curve is the norm of
  the curve over `k₀`).

`Stacks.EtaleCohomology.laumonFibreStableReductionInput_of_inputs` proves
`Stacks.EtaleCohomology.LaumonFibreStableReductionInput` from them, and
`Stacks.EtaleCohomology.laumonFibrePurityInput_of_inputs` proves
`Stacks.EtaleCohomology.LaumonFibrePurityInput` from them, duality and the inputs of
`Stacks.EtaleCohomology.laumonFourierEquinormStableInput_of_inputs`.

## Main definitions

* `Stacks.EtaleCohomology.LaumonStableDecompositionInput`,
  `Stacks.EtaleCohomology.LaumonFibrePureConstituentInput`,
  `Stacks.EtaleCohomology.LaumonFibrePureDescentInput`.

## Main results

* `Stacks.EtaleCohomology.laumonFibreStableReductionInput_of_inputs`.
* `Stacks.EtaleCohomology.laumonFibrePurityInput_of_inputs`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

/-- **Descent of the purity of the fibres along a finite extension of the base field** (Kedlaya,
*Fourier transforms and p-adic Weil II*, §6.4): for `σ` on `U ≅ 𝔸¹_k`, a finite extension `k₀` of
`k` and a geometric point `x̄₀` of `𝔸¹_{k₀}` over `x̄`, if the fibres of the pullback of `σ` to
`𝔸¹_{k₀}` (with `ψ ∘ Tr_{k₀/k}`) are pure of weight `β + 1` off a curve `D₀ = 0` over `k₀`, then
the fibres of `σ` are pure of weight `β + 1` off a curve `D = 0` over `k` (the norm of `D₀`). At a
fibre over `k'` pass to the compositum `k' k₀`: the geometric cohomology is the same, with the
Frobenius of `k' k₀` a power of that of `k'`. -/
public def LaumonFibrePureDescentInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
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
    (ι' : E →+* ℂ) (β : ℤ) (ψ : AddChar k E) (n : ℕ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [Algebra k k₀]
    (hX₀ : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k₀))))
    (x₀ : GeometricPoint (Spec (.of (Polynomial k₀))))
    (hx₀ : x₀.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k₀))) ≫
      inv e) = x)
    (D₀ : MvPolynomial (Fin 2) k₀), D₀ ≠ 0 →
    LaumonFibrePure B (Stacks.ArtinSchreier.specObject (Polynomial k₀) B hX₀) ℓ k₀
      (𝟙 (Spec (.of (Polynomial k₀)))) x₀ E b
      (σ.comp (hx₀ ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (algebraMap k k₀))) ≫ inv e) x₀).toMonoidHom))
      ι' β (ψ.compAddMonoidHom (Algebra.trace k k₀).toAddMonoidHom) n D₀ →
    ∃ D : MvPolynomial (Fin 2) k, D ≠ 0 ∧ LaumonFibrePure B U ℓ k e x E b σ ι' β ψ n D

/-- **Purity of the fibres of a direct sum** (Kedlaya, *Fourier transforms and p-adic Weil II*,
§6.4): if after the extension of scalars to a finite extension `E'` of `E` (with an embedding
`ι''` extending `ι'`) the representation `σ` is conjugate to the direct sum of representations
`σᵢ`, and the fibres of each `σᵢ` (with `ψ` composed with `E → E'`) are pure of weight `β + 1`
off `Dᵢ = 0`, then the fibres of `σ` are pure of weight `β + 1` off `∏ Dᵢ = 0`: `H¹_c` of the
twisted direct sum is the direct sum of the `H¹_c` of the twisted constituents, and commutes with
the extension of scalars. -/
public def LaumonFibrePureConstituentInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
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
    (ι' : E →+* ℂ) (β : ℤ) (ψ : AddChar k E) (n : ℕ)
    (E' : Type) [Field E'] [Algebra ℚ_[ℓ] E'] [Algebra E E'] [IsScalarTower ℚ_[ℓ] E E'] {d' : ℕ}
    (b' : Module.Basis (Fin d') ℚ_[ℓ] E') (ι'' : E' →+* ℂ), ι''.comp (algebraMap E E') = ι' →
    ∀ {r : ℕ} (ms : Fin r → ℕ) (σs : ∀ i, EtaleFundamentalGroup U.1 x →* GL (Fin (ms i)) E')
      (eqv : Fin m ≃ Σ i, Fin (ms i)) (M : GL (Σ i, Fin (ms i)) E'),
      (∀ g, (M : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E') *
          Matrix.reindex eqv eqv ((σ g).val.map (algebraMap E E')) *
          ((M⁻¹ : GL (Σ i, Fin (ms i)) E') : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E') =
        Matrix.blockDiagonal' fun i => (σs i g).val) →
    ∀ Ds : Fin r → MvPolynomial (Fin 2) k,
      (∀ i, LaumonFibrePure B U ℓ k e x E' b' (σs i) ι'' β
        ((algebraMap E E').toMonoidHom.compAddChar ψ) n (Ds i)) →
      LaumonFibrePure B U ℓ k e x E b σ ι' β ψ n (∏ i, Ds i)

/-- **Decomposition into constituents which stay absolutely irreducible** (Kedlaya, *Fourier
transforms and p-adic Weil II*, §6.4, reduction to geometric irreducibility): for `σ` on `U ≅ 𝔸¹_k`
absolutely irreducible and `ι'`-pure of weight `β`, there are a finite extension `k₀` of `k`
(`#k₀ = p ^ n₀`) with a geometric point `x̄₀` of `𝔸¹_{k₀}` over `x̄`, a finite extension `E'` of
`E` with an embedding `ι''` extending `ι'`, and representations `σᵢ` of `π₁(𝔸¹_{k₀}, x̄₀)` over
`E'` with continuous restriction of scalars, absolutely irreducible and staying absolutely
irreducible over every finite extension of `k₀` (`Stacks.EtaleCohomology.LaumonStablyAbsIrr`),
`ι''`-pure of weight `β`, whose direct sum is conjugate to the pullback of `σ` to `𝔸¹_{k₀}` after
the extension of scalars to `E'`. (The restriction of `σ` to the open normal subgroup `π₁(𝔸¹_{k₀})`
is semisimple by Clifford; choose `k₀` with the largest number of constituents, bounded by the
dimension; split them over a finite `E'`; the eigenvalues of `σᵢ(F_y)` are among those of
`σ(F_{y₀})^{[κ(y) : κ(y₀)]}`.) -/
public def LaumonStableDecompositionInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (p n : ℕ) [Fact p.Prime] [CharP k p] (_ : Fintype.card k = p ^ n)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E),
    Continuous (restrictScalarsRep b σ) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    ∀ (ι' : E →+* ℂ) (β : ℤ),
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Fintype k₀) (_ : Algebra k k₀)
      (_ : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k₀))))
      (x₀ : GeometricPoint (Spec (.of (Polynomial k₀))))
      (hx₀ : x₀.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k₀))) ≫
        inv e) = x)
      (n₀ : ℕ) (_ : Fintype.card k₀ = p ^ n₀)
      (E' : Type) (_ : Field E') (_ : Algebra ℚ_[ℓ] E') (_ : FiniteDimensional ℚ_[ℓ] E')
      (_ : Algebra E E') (_ : IsScalarTower ℚ_[ℓ] E E') (d' : ℕ)
      (b' : Module.Basis (Fin d') ℚ_[ℓ] E') (ι'' : E' →+* ℂ) (r : ℕ) (ms : Fin r → ℕ)
      (σs : ∀ i, EtaleFundamentalGroup (Spec (.of (Polynomial k₀))) x₀ →* GL (Fin (ms i)) E')
      (eqv : Fin m ≃ Σ i, Fin (ms i)) (M : GL (Σ i, Fin (ms i)) E'),
      ι''.comp (algebraMap E E') = ι' ∧
      (∀ i, Continuous (restrictScalarsRep b' (σs i))) ∧
      (∀ i (K' : Type) [Field K'] [IsAlgClosed K'] [Algebra E' K']
        (W : Submodule K' (Fin (ms i) → K')),
        (∀ g, ∀ v ∈ W, (σs i g).val.map (algebraMap E' K') *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      (∀ i, LaumonStablyAbsIrr k₀ (𝟙 (Spec (.of (Polynomial k₀)))) x₀ (σs i)) ∧
      (haveI := Stacks.GenericFiniteEtale.smoothOfRelativeDimension_specMap_polynomial k₀
      haveI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀)))) :=
        SmoothOfRelativeDimension.smooth 1 _
      ∀ i (y : closedPoints (Spec (.of (Polynomial k₀)))) (z : ℂ),
        ((σs i (geometricFrobeniusFamily
          (Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀)))) x₀ y)).val.charpoly.map
            ι'').IsRoot z →
        ‖z‖ = ((p ^ n₀ : ℕ) : ℝ) ^ (((residueDegree
          (Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀)))) y.1 : ℤ) * β : ℝ) / 2)) ∧
      ∀ g, (M : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E') *
          Matrix.reindex eqv eqv (((σ.comp (hx₀ ▸ (etaleFundamentalGroupMap (Spec.map
            (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k₀))) ≫ inv e)
              x₀).toMonoidHom)) g).val.map (algebraMap E E')) *
          ((M⁻¹ : GL (Σ i, Fin (ms i)) E') : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E') =
        Matrix.blockDiagonal' fun i => (σs i g).val

/-- **The reduction of fibre purity to representations which stay absolutely irreducible**
(`Stacks.EtaleCohomology.LaumonFibreStableReductionInput`), from the decomposition into stable
constituents over a finite extension `k₀`
(`Stacks.EtaleCohomology.LaumonStableDecompositionInput`), the purity of the fibres of a direct sum
(`Stacks.EtaleCohomology.LaumonFibrePureConstituentInput`) and the descent along `k₀ / k`
(`Stacks.EtaleCohomology.LaumonFibrePureDescentInput`): the stable case applies to each constituent
over `k₀`, with `N` the largest of their bounds. -/
public theorem laumonFibreStableReductionInput_of_inputs (hA : LaumonFibrePureDescentInput.{u})
    (hB : LaumonFibrePureConstituentInput.{u}) (hC : LaumonStableDecompositionInput.{u}) :
    LaumonFibreStableReductionInput.{u} := by
  intro hst B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _
    d b m σ hσ K _ _ _ hirr hζ ι' β _ hpure ψ hψ
  classical
  obtain ⟨k₀, _, _, _, hX₀, x₀, hx₀, n₀, hcard₀, E', _, _, _, _, _, d', b', ι'', r, ms, σs, eqv, M,
    hι, hcont, hirrs, hstab, hpures, hM⟩ := hC B U ℓ k f e he p n hcard x E b σ hσ K hirr ι' β hpure
  have : CharP k₀ p := charP_of_injective_algebraMap (algebraMap k k₀).injective p
  have := Stacks.GenericFiniteEtale.smoothOfRelativeDimension_specMap_polynomial k₀
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀)))) :=
    SmoothOfRelativeDimension.smooth 1 _
  have := Stacks.GenericFiniteEtale.connectedSpace_pullback_specMap_polynomial k₀
    (AlgebraicClosure k₀)
  obtain ⟨j₀⟩ : Nonempty (CompactificationOf (Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀)))))) := IsCofiltered.nonempty
  obtain ⟨ζ, hζ⟩ := hζ
  have hζ' : ∃ ζ' : E', IsPrimitiveRoot ζ' p :=
    ⟨algebraMap E E' ζ, hζ.map_of_injective (algebraMap E E').injective⟩
  have hψ₀ : (algebraMap E E').toMonoidHom.compAddChar
      (ψ.compAddMonoidHom (Algebra.trace k k₀).toAddMonoidHom) ≠ 1 := by
    intro h
    apply Stacks.FourierDeligne.traceChar_ne_one ψ k₀ hψ
    ext c
    have hc := congrArg (fun φ : AddChar k₀ E' => φ c) h
    simp only [MonoidHom.compAddChar_apply, AddChar.one_apply] at hc
    exact (algebraMap E E').injective (hc.trans (map_one _).symm)
  have key : ∀ i, ∃ N : ℕ, ∀ n' : ℕ, N < n' → ¬ p ∣ n' →
      ∃ D : MvPolynomial (Fin 2) k₀, D ≠ 0 ∧
        LaumonFibrePure B (Stacks.ArtinSchreier.specObject (Polynomial k₀) B hX₀) ℓ k₀
          (𝟙 (Spec (.of (Polynomial k₀)))) x₀ E' b' (σs i) ι'' β
          ((algebraMap E E').toMonoidHom.compAddChar
            (ψ.compAddMonoidHom (Algebra.trace k k₀).toAddMonoidHom)) n' D := by
    intro i
    have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
        (Stacks.ArtinSchreier.specObject (Polynomial k₀) B hX₀) ℓ
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀)))) j₀ (AlgebraicClosure k₀)
        (LAdicSheaf.representationSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k₀) B hX₀)
          x₀ (restrictScalarsRep b' (σs i)) (hcont i)) 1) :=
      LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ
        (AlgebraicClosure k₀) p n₀ hcard₀ hℓp _ _ _ _ 1
    exact hst B (Stacks.ArtinSchreier.specObject (Polynomial k₀) B hX₀) ℓ k₀
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀))))
      (𝟙 (Spec (.of (Polynomial k₀)))) (Category.id_comp _) j₀ (AlgebraicClosure k₀) p n₀ hcard₀
      hℓp x₀ E' b' (σs i) (hcont i) (AlgebraicClosure E') (hirrs i _) (hstab i) hζ' ι'' β
      (hpures i) _ hψ₀
  choose N hN using key
  refine ⟨Finset.univ.sup N, fun n' hn' hpn' => ?_⟩
  have hle : ∀ i, N i < n' := fun i => lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ i)) hn'
  choose Ds hDs hpDs using fun i => hN i n' (hle i) hpn'
  have hσ₀ := hB B (Stacks.ArtinSchreier.specObject (Polynomial k₀) B hX₀) ℓ k₀
    (𝟙 (Spec (.of (Polynomial k₀)))) x₀ E b _ ι' β
    (ψ.compAddMonoidHom (Algebra.trace k k₀).toAddMonoidHom) n' E' b' ι'' hι ms σs eqv M hM Ds hpDs
  exact hA B U ℓ k e x E b σ ι' β ψ n' k₀ hX₀ x₀ hx₀ (∏ i, Ds i)
    (Finset.prod_ne_zero_iff.2 fun i _ => hDs i) hσ₀

/-- **Fibre purity from its inputs** ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the
purity of the fibres of the Fourier family (`Stacks.EtaleCohomology.LaumonFibrePurityInput`) from
the geometric inputs of the equal absolute values for stable `σ`
(`Stacks.EtaleCohomology.laumonFourierEquinormStableInput_of_inputs`), duality with complex
conjugation (`Stacks.EtaleCohomology.LaumonFibreReciprocityInput`) and the reduction to stable `σ`
(`Stacks.EtaleCohomology.laumonFibreStableReductionInput_of_inputs`). -/
public theorem laumonFibrePurityInput_of_inputs (hL6 : LaumonFourierLineAbsIrrInput.{u})
    (hlis : LaumonFourierLineLisseInput.{u}) (hfib : LaumonFourierFamilyFibreInput.{u})
    (hconj : LaumonFourierFamilyConjugateInput.{u}) (hR : LaumonFibreReciprocityInput.{u})
    (hA : LaumonFibrePureDescentInput.{u}) (hB : LaumonFibrePureConstituentInput.{u})
    (hC : LaumonStableDecompositionInput.{u}) :
    LaumonFibrePurityInput.{u} :=
  laumonFibrePurityInput_of_stable (laumonFibreStableReductionInput_of_inputs hA hB hC)
    (laumonFourierEquinormStableInput_of_inputs hL6 hlis hfib hconj) hR

end Stacks.EtaleCohomology

end
