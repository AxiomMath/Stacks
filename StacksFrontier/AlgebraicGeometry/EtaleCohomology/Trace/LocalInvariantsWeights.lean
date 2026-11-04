module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.InertiaInvariantsWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineLinear
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CurvePointInertia

/-!
# The weights of the Frobenius on the local invariants at a missing point of a curve

Let `V ⊆ W` be opens of the affine line over a finite field `k`, `y ∈ W ∖ V` a closed point,
`A ≅ 𝒪_{W,y}` its local ring, a discrete valuation ring with fraction field the function field
`K` of `V`, `L` a separable closure of `K`, `P` a place of `L` over `y`, `Fr` an arithmetic
Frobenius at `P`, and `I_y = φ(I_P) ⊆ π₁(V, η̄)` the inertia group of `V` at `y`
(`Stacks.FundamentalGroup.curvePointInertia`). For `τ : π₁(V, η̄) → GL_m(E)`, `E` finite over
`ℚ_ℓ`, pure of weight `w` along `ι' : E → ℂ`, Weil II 1.8.4 says that the geometric Frobenius
`τ(φ Fr⁻¹)` on the `E`-subspace of `τ(I_y)`-invariants is mixed of integer weights `≤ w` along
`ι'`. This is `Stacks.EtaleCohomology.CurveLocalInvariantsWeightInput`, the form of Weil II 1.8.4
consumed in the degeneration step of Laumon's theorem.

## Main definitions

* `Stacks.EtaleCohomology.curveLocalRingToFunctionField`: `𝒪_{W,y} → K`.
* `Stacks.EtaleCohomology.CurveLocalInvariantsWeightInput`.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.8.4.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale
open scoped Pointwise

universe u

namespace Stacks.EtaleCohomology

/-- The map `𝒪_{W,y} → κ(η_V)` from the local ring of `W` at `y` to the function field of an
open `V` of `W`, through the stalk at the image of the generic point of `V`, which specializes
to `y`. -/
public def curveLocalRingToFunctionField {V W : Scheme.{u}} [IrreducibleSpace V] (jW : V ⟶ W)
    {y : W} (hy : jW.base (genericPoint V) ⤳ y) :
    W.presheaf.stalk y ⟶ V.residueField (genericPoint V) :=
  W.presheaf.stalkSpecializes hy ≫ jW.stalkMap (genericPoint V) ≫ V.residue (genericPoint V)

/-- **Weil II 1.8.4 at a missing point of a curve, `E`-linearly along one embedding `ι'`.**  Let
`V ⊆ W` be opens of the affine line `𝔸¹_k`, `y ∈ W ∖ V` a closed point, `A` a discrete
valuation ring identified with `𝒪_{W,y}` compatibly with the maps to the function field `K` of `V`,
`P` a place of a separable closure `L` of `K` over `A`, `Fr` an arithmetic Frobenius at `P`, and
`τ : π₁(V, η̄) → GL_m(E)` with `Res_b τ` continuous and pure of weight `w` along `ι'`.  Then the
roots, read along `ι'`, of the characteristic polynomial of the geometric Frobenius `τ(φ Fr⁻¹)`
restricted to the `E`-subspace of invariants of the inertia group `τ(I_y)` have absolute values
`#κ(y) ^ (w' / 2)` with integers `w' ≤ w`. -/
public def CurveLocalInvariantsWeightInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (V : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B V.1 V.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian V.1] [Fact ℓ.Prime] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
    (k : Type u) [Field k] [Fintype k] (f : V.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (_j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (_hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    -- the curve `W ⊇ V` and the missing point `y`
    (W : B.Scheme) (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW] [QuasiCompact fW]
    [IsSeparated fW] [SmoothOfRelativeDimension 1 fW]
    (eW : W.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion eW]
    (_ : eW ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = fW)
    (jW : V.1 ⟶ W.1) [IsOpenImmersion jW]
    (_ : jW ≫ fW = f) (y : W.1) (_ : IsClosed ({y} : Set W.1)) (_ : y ∉ Set.range jW.base)
    (hy : jW.base (genericPoint V.1) ⤳ y)
    -- the local field at `y`
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (V.1.residueField (genericPoint V.1)) L]
    [IsSepClosure (V.1.residueField (genericPoint V.1)) L]
    [Algebra L Ω] [Algebra (V.1.residueField (genericPoint V.1)) Ω]
    [IsScalarTower (V.1.residueField (genericPoint V.1)) L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (V.1.residueField (genericPoint V.1)) Ω]
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (V.1.residueField (genericPoint V.1))]
    [IsFractionRing A (V.1.residueField (genericPoint V.1))] [Algebra A L]
    [IsScalarTower A (V.1.residueField (genericPoint V.1)) L]
    [Finite (IsLocalRing.ResidueField A)]
    (eA : A ≃+* W.1.presheaf.stalk y)
    (_ : ∀ a : A, algebraMap A (V.1.residueField (genericPoint V.1)) a =
      (curveLocalRingToFunctionField jW hy).hom (eA a))
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (Fr : Gal(L / V.1.residueField (genericPoint V.1)))
    (hFrD :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L / V.1.residueField (genericPoint V.1)) P)
    (_ :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P)
    -- the representation
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ}
    (τ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin m) E)
    (_ : Continuous (restrictScalarsRep b τ)) (ι' : E →+* ℂ) (w : ℤ),
    (∀ (z : closedPoints V.1) (c : ℂ),
        ((τ (geometricFrobeniusFamily f ((algebraicClosureGeometricPoint
          (V.1.residueField (genericPoint V.1)) Ω).map
            (V.1.fromSpecResidueField (genericPoint V.1))) z)).val.charpoly.map ι').IsRoot c →
        ‖c‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f z.1 : ℤ) * w : ℝ) / 2)) →
    letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
      (integralClosure A L)
    IsCharpolyNormMixedOfWeightLE (Nat.card (IsLocalRing.ResidueField A)) ι' w
      ((Matrix.toLin' ((τ ((galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr⁻¹) : GL (Fin m) E) :
          Matrix (Fin m) (Fin m) E)).restrict
        (toLin'_mem_invariants_of_mem_normalizer τ
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P)
          (map_inv_mem_normalizer_map_inertia A (V.1.residueField (genericPoint V.1)) L P
            (galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr hFrD)))

end Stacks.EtaleCohomology

end
