module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalInvariantsWeightsOfInjection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCoefficientRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientSheafRationalStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImageCoefficient

/-!
# The specialization map at a missing point of a curve

Let `V ⊆ W ⊆ 𝔸¹_k` be opens of the affine line over a finite field, `y ∈ W ∖ V` a closed point,
and `G` an ℓ-adic sheaf on `W` with coefficients in a `ℤ_ℓ`-algebra `O`, `E = O[1/ℓ]` a finite
extension of `ℚ_ℓ`, whose restriction `G|_V` is lisse. By
`Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse`, `G|_V` is isogenous to `ℱ_ρ` and
`ρ` is conjugate to `Res_b τ` for a representation `τ : π₁(V, η̄) → GL_m(E)`. The specialization
map is the composite

`G_ȳ → (j_* j⁻¹ G)_ȳ → (j_* ℱ_ρ)_ȳ ≅ ρ^{I_y} ≅ τ^{I_y}`

of the stalk of the unit of `j⁻¹ ⊣ j_*`, the isogeny, the identification of the stalk of `j_*` at
`ȳ` with the inertia invariants (`Stacks.EtaleCohomology.curvePointInertiaStalkInput`) and the
conjugation to `τ`. After `⊗ ℚ_ℓ` it is `E`-linear, carries the geometric Frobenius at `y` to
`τ(φ Fr⁻¹)`, and it is injective as soon as the kernels of the stalks at `ȳ` of the units
`Gₙ → j_* j⁻¹ Gₙ` are killed by a fixed power of `ℓ` (`G` has no punctual sections at `y`).
`Stacks.EtaleCohomology.CurveSpecializationInput` states this; it is the specialization step of
Laumon's degeneration argument in Weil II 1.8.4
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), piece P5 of
`Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`.

The proposition is not registered and is not a hypothesis of any registered statement.

## Main definitions

* `Stacks.EtaleCohomology.levelUnitStalkMap`: the stalk of the unit `Fₙ → f_* f⁻¹ Fₙ`.
* `Stacks.EtaleCohomology.CurveSpecializationInput`.

## Main results

* `Stacks.EtaleCohomology.injective_comp_linearEquiv_and_comp_pow`: composing the specialization
  map with an equivariant isomorphism `H ≅ ℚ_ℓ ⊗ G_ȳ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open AlgebraicGeometry.SmallEtale.LAdicSheaf
open scoped Pointwise Matrix

universe u

namespace Stacks.EtaleCohomology

section Unit

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y) {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian Y.obj]

/-- **The stalk at `s̄` of the unit `Fₙ → f_* f⁻¹ Fₙ`** of the level `n` of an ℓ-adic sheaf `F` on
`Y`, for `f : X ⟶ Y`: the colimit over the étale neighbourhoods of `s̄` of the unit of the
adjunction `f⁻¹ ⊣ f_*` at level `n`. -/
public def levelUnitStalkMap (F : LAdicSheaf.{u, u + 1} B Y ℓ) (s : GeometricPoint Y.1) (n : ℕ) :
    finiteLevelStalk B Y ℓ F s n ⟶ etaleStalk B Y.1 Y.2 s
      ((levelPushforward f n).obj ((levelPullback f n).obj (F.level n))).obj :=
  colim.map (Functor.whiskerLeft
    ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.2 s)).op)
    ((levelAdjunction f n).unit.app (F.level n)).hom)

end Unit

/-- **The specialization map at a missing point of a curve.** In the setting of
`Stacks.EtaleCohomology.CurvePointInertiaStalkInput` (`V ⊆ W ⊆ 𝔸¹_k`, `y ∈ W ∖ V` closed, the
local data `A, L, Ω, P, Fr` at `y`), let `G` be an ℓ-adic sheaf on `W` with coefficients in `O`,
`E = O[1/ℓ]`, and let `ρ, φ, ψ, N, τ, P, Q` be data as produced by
`Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse` for `G|_V`: an isogeny
`φ : G|_V → ℱ_ρ`, `ψ : ℱ_ρ → G|_V` with `φ ψ = ℓᴺ = ψ φ`, and matrices `P`, `Q` conjugating the
integral model of `ρ` to `Res_b τ` and the action `α` of `E` to `Res_b(e · 1)`. Suppose that the
kernels of the stalks at `ȳ` of the units `Gₙ → j_* j⁻¹ Gₙ` are all killed by `ℓᴹ`. Then there is
an injective `E`-linear map from the rational stalk `ℚ_ℓ ⊗ G_ȳ` to the `τ(I_y)`-invariants of `E^m`
carrying the geometric Frobenius at `y` to `τ(φ Fr⁻¹)`. -/
public def CurveSpecializationInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (V : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian V.1] [Fact ℓ.Prime] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
    (k : Type u) [Field k] [Fintype k] (f : V.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (_j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (_hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    -- the curve `W ⊇ V` and the missing point `y`
    (W : B.Scheme) [IsNoetherian W.1] (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW]
    [QuasiCompact fW] [IsSeparated fW] [SmoothOfRelativeDimension 1 fW]
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
    (hyf : Finite (W.1.residueField y))
    -- the sheaf `G` on `W`, with coefficients in `O`
    {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (G : LAdicSheaf.CoefficientSheaf B W ℓ O)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] [Algebra O E]
    [IsLocalization (Submonoid.powers (ℓ : O)) E]
    (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c)
    {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E)
    -- the representation of `G|_V` (the data of `exists_restrictScalarsRep_of_isLisse`)
    (r : ℕ) (ρ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (φ : (G.inverseImage (ObjectProperty.homMk jW : V ⟶ W)).toLAdicSheaf ⟶
      LAdicSheaf.representationSheaf B V _ ρ hρ)
    (ψ : LAdicSheaf.representationSheaf B V _ ρ hρ ⟶
      (G.inverseImage (ObjectProperty.homMk jW : V ⟶ W)).toLAdicSheaf) (N : ℕ)
    (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _)
    (m : ℕ) (τ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin m) E)
    (Pm : Matrix (Fin r) (Fin (m * d)) ℚ_[ℓ]) (Qm : Matrix (Fin (m * d)) (Fin r) ℚ_[ℓ])
    (_ : Continuous (restrictScalarsRep b τ)) (_ : Pm * Qm = 1) (_ : Qm * Pm = 1)
    (_ : ∀ e : E, Qm * isogenyCoefficientAlgHom B V _
        (G.inverseImage (ObjectProperty.homMk jW : V ⟶ W)) ρ hρ φ ψ N E hφψ hψφ hOE e * Pm =
      restrictScalarsMatrix b (Matrix.scalar (Fin m) e))
    (_ : ∀ g, Qm * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
        (haveI := compactSpace_etaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
          (V.1.residueField (genericPoint V.1)) Ω).map
            (V.1.fromSpecResidueField (genericPoint V.1)))
         integralModel ρ hρ g)).val * Pm = (restrictScalarsRep b τ g).val)
    -- no punctual sections at `y`
    (M : ℕ)
    (_ : ∀ (n : ℕ) (w : finiteLevelStalk B W ℓ G.toLAdicSheaf
        (Stacks.Frobenius.geometricPointAt W.1 y) n),
      (levelUnitStalkMap (ObjectProperty.homMk jW : V ⟶ W) G.toLAdicSheaf
        (Stacks.Frobenius.geometricPointAt W.1 y) n).hom w = 0 → (ℓ ^ M) • w = 0),
    letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
      (integralClosure A L)
    letI := G.rationalStalkModule (Stacks.Frobenius.geometricPointAt W.1 y) E
    ∃ sp : LAdicSheaf.rationalStalkLeft B W ℓ G.toLAdicSheaf
        (Stacks.Frobenius.geometricPointAt W.1 y) →ₗ[E]
        Representation.invariants ((matrixRepresentation τ).comp
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P).subtype),
      Function.Injective sp ∧
      sp ∘ₗ G.rationalStalkFrobenius E y hyf =
        ((Matrix.toLin' ((τ ((galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr⁻¹) :
          GL (Fin m) E) : Matrix (Fin m) (Fin m) E)).restrict
        (toLin'_mem_invariants_of_mem_normalizer τ
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P)
          (map_inv_mem_normalizer_map_inertia A (V.1.residueField (genericPoint V.1)) L P
            (galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr hFrD))) ∘ₗ sp

/-- **Composing the specialization map with an equivariant isomorphism**: if `sp : S → T` is
injective and carries `F_S` to `F_T`, and `e : H ≅ S` carries `Φ ^ d` to `F_S`, then `sp ∘ e` is
injective and carries `Φ ^ d` to `F_T`. This turns the specialization map of
`Stacks.EtaleCohomology.CurveSpecializationInput` and an identification of `H¹_c` of the special
fibre with the stalk into the injection of
`Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`. -/
public theorem injective_comp_linearEquiv_and_comp_pow {R H S T : Type*} [CommSemiring R]
    [AddCommMonoid H] [AddCommMonoid S] [AddCommMonoid T] [Module R H] [Module R S] [Module R T]
    (sp : S →ₗ[R] T) (hsp : Function.Injective sp) (FS : S →ₗ[R] S) (FT : T →ₗ[R] T)
    (hF : sp ∘ₗ FS = FT ∘ₗ sp) (Φ : H →ₗ[R] H) (dy : ℕ) (e : H ≃ₗ[R] S)
    (he : e.toLinearMap ∘ₗ Φ ^ dy = FS ∘ₗ e.toLinearMap) :
    Function.Injective (sp ∘ₗ e.toLinearMap) ∧
      (sp ∘ₗ e.toLinearMap) ∘ₗ Φ ^ dy = FT ∘ₗ (sp ∘ₗ e.toLinearMap) := by
  refine ⟨hsp.comp e.injective, ?_⟩
  rw [LinearMap.comp_assoc, he, ← LinearMap.comp_assoc, hF, LinearMap.comp_assoc]

end Stacks.EtaleCohomology

end
