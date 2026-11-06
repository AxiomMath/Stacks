module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonSpecializationInjectionIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyStalkPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageShriekBaseChangeIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityUnconditional

/-!
# The specialization injection at the origin of Laumon's degeneration, through base change

In Laumon's degeneration argument ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), piece
P5 of `Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`) the sheaf `G = R¹pr₂! K` on the
`t`-line restricts on the open `V` to `G|_V`, and `F_V = R¹g'_!(K|_{U'})` is the higher direct
image of the restriction of `K` to `U' = pr₂⁻¹(V)`. The base change morphisms of ℓ-adic sheaves
`χ : G|_V → F_V` and `χ' : F_V → G|_V` (Tag 0F7L along the levels,
`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekBaseChangeHom`) compose to `ℓᵃ`, `a` the
sum of the torsion bounds of `K` and `K|_{U'}`, and `χ` is compatible with the coefficients.

For a sheaf `F` with coefficients in `O`, this gives the base change morphisms of coefficient
sheaves
(`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom`,
`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeInv`), the
hypotheses defining `R^r g_! F` being discharged by Tag 0GL0
(`Stacks.EtaleCohomology.lowerShriekConstructibilityInput`). Instantiating
`Stacks.EtaleCohomology.exists_laumonSpecializationInjection_of_isogeny` with them, the
specialization injection `J` exists with `F_V = R¹g'_!(K|_{U'})`
(`Stacks.EtaleCohomology.exists_laumonSpecializationInjection_of_baseChange`).

## Main results

* `LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom_act`
* `LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom_comp_inv`
* `exists_laumonSpecializationInjection_of_baseChange`

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open AlgebraicGeometry.SmallEtale.LAdicSheaf
open Stacks.Frobenius
open scoped Pointwise Matrix

universe u

namespace Stacks.EtaleCohomology

/-! ### The base change morphisms of coefficient sheaves -/

section Coefficient

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
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
  {U W U' V : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] [IsNoetherian U'.1]
  [IsNoetherian V.1] (g : U ⟶ W)
  [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
  (g' : U' ⟶ V) [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
  [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g')))
  (jU : U' ⟶ U) (jV : V ⟶ W)
  (hpb : IsPullback (B.inclusion.map jU) (B.inclusion.map g') (B.inclusion.map g)
    (B.inclusion.map jV))
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B U ℓ O) (r : ℕ)

/-- **The base change morphism `(R^r g_! F)|_V ⟶ R^r g'_!(F|_{U'})` of a sheaf with
coefficients**: the base change morphism of the underlying ℓ-adic sheaves
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekBaseChangeHom`), the hypotheses defining
`R^r g_!` and `R^r g'_!` being Tag 0GL0. -/
def LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom :
    ((F.higherDirectImageShriek B ℓ g jg r).inverseImage jV).toLAdicSheaf ⟶
      ((F.inverseImage jU).higherDirectImageShriek B ℓ g' jg' r).toLAdicSheaf :=
  LAdicSheaf.higherDirectImageShriekBaseChangeHom B ℓ g jg g' jg' jU jV hpb F.toLAdicSheaf r
    (LAdicSheaf.higherDirectImageShriekCondition_of_lowerShriekConstructibilityInput B ℓ g jg
      (lowerShriekConstructibilityInput B) F.toLAdicSheaf r)
    (LAdicSheaf.higherDirectImageShriekCondition_of_lowerShriekConstructibilityInput B ℓ g' jg'
      (lowerShriekConstructibilityInput B) (LAdicSheaf.inverseImage jU F.toLAdicSheaf) r)

/-- **The base change morphism in the other direction**, `R^r g'_!(F|_{U'}) ⟶ (R^r g_! F)|_V`. -/
def LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeInv :
    ((F.inverseImage jU).higherDirectImageShriek B ℓ g' jg' r).toLAdicSheaf ⟶
      ((F.higherDirectImageShriek B ℓ g jg r).inverseImage jV).toLAdicSheaf :=
  LAdicSheaf.higherDirectImageShriekBaseChangeInv B ℓ g jg g' jg' jU jV hpb F.toLAdicSheaf r
    (LAdicSheaf.higherDirectImageShriekCondition_of_lowerShriekConstructibilityInput B ℓ g jg
      (lowerShriekConstructibilityInput B) F.toLAdicSheaf r)
    (LAdicSheaf.higherDirectImageShriekCondition_of_lowerShriekConstructibilityInput B ℓ g' jg'
      (lowerShriekConstructibilityInput B) (LAdicSheaf.inverseImage jU F.toLAdicSheaf) r)

/-- **The base change morphism is compatible with the coefficients.** -/
theorem LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom_act (o : O) :
    (((F.higherDirectImageShriek B ℓ g jg r).inverseImage jV).act o).asHom ≫
        LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom B ℓ g jg g' jg' jU jV hpb
          F r =
      LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom B ℓ g jg g' jg' jU jV hpb
          F r ≫
        (((F.inverseImage jU).higherDirectImageShriek B ℓ g' jg' r).act o).asHom :=
  LAdicSheaf.higherDirectImageShriekBaseChangeHom_naturality B ℓ g jg g' jg' jU jV hpb
    F.toLAdicSheaf r _ _ (F.act o).asHom

/-- **The base change morphisms compose to `ℓ ^ (N + N')`**, `N`, `N'` the torsion bounds of `F`
and `F|_{U'}`. -/
theorem LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom_comp_inv :
    LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom B ℓ g jg g' jg' jU jV hpb F r ≫
        LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeInv B ℓ g jg g' jg' jU jV hpb
          F r =
      (ℓ ^ (LAdicSheaf.torsionBound F.toLAdicSheaf +
        LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU F.toLAdicSheaf))) • 𝟙 _ :=
  LAdicSheaf.higherDirectImageShriekBaseChangeHom_comp_inv B ℓ g jg g' jg' jU jV hpb
    F.toLAdicSheaf r _ _

/-- **The base change morphisms compose to `ℓ ^ (N + N')`** in the other order. -/
theorem LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeInv_comp :
    LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeInv B ℓ g jg g' jg' jU jV hpb F r ≫
        LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom B ℓ g jg g' jg' jU jV hpb
          F r =
      (ℓ ^ (LAdicSheaf.torsionBound F.toLAdicSheaf +
        LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU F.toLAdicSheaf))) • 𝟙 _ :=
  LAdicSheaf.higherDirectImageShriekBaseChangeInv_comp B ℓ g jg g' jg' jU jV hpb
    F.toLAdicSheaf r _ _

end Coefficient

/-! ### The specialization injection -/

/-- **The specialization injection at the origin of Laumon's degeneration, through base change**
(piece P5 of `Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the specialization injection of
`Stacks.EtaleCohomology.exists_laumonSpecializationInjection_of_isogeny` for
`F_V = R¹g'_!(K|_{U'})` (`Stacks.EtaleCohomology.laumonFamilyRestrictedHigherDirectImage`), `U'`
the inverse image of `V` under `pr₂`, through the base change morphisms
`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom`. There is
an injective `E`-linear map `J : H¹_c(U_k̄, ℱ_σ ⊗ ℚ_ℓ) → τ^{I_y}` carrying `(π_U^*) ^ {d_y}` to
`τ(φ Fr⁻¹)`; the inputs are the fibre over the origin (F0, BC) and the absence of punctual
sections (H2). -/
public theorem exists_laumonSpecializationInjection_of_baseChange (B : BigEtaleSite.{u}) (ℓ : ℕ)
    (hF0 : LaumonOriginFibreCohomologyInput.{u})
    (hH2 : LaumonFamilyNoPunctualSectionsInput.{u})
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
    (f : U.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsIso e]
    (he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n)
    (hℓp : ℓ ≠ p) (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ))
    (ψ : AddChar k E) (n₀ : ℕ) (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (c : k')
    (hψ : ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom ≠ 1)
    (hh : (Polynomial.X ^ n₀ + Polynomial.C c * Polynomial.X : Polynomial k') ≠ 0)
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
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL))))
    -- the open `V` of the `t`-line
    (V : B.Scheme) [IsNoetherian V.1] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
    (fV : V.1 ⟶ Spec (.of k'))
    [LocallyOfFiniteType fV] [QuasiCompact fV] [IsSeparated fV] [SmoothOfRelativeDimension 1 fV]
    (jV : CompactificationOf (Over.mk fV)) (kbar' : Type u) [Field kbar'] [Algebra k' kbar']
    [IsAlgClosure k' kbar']
    [ConnectedSpace ↥(Limits.pullback fV (Spec.map (CommRingCat.ofHom (algebraMap k' kbar'))))]
    (n' : ℕ) [CharP k' p] (hcard' : Fintype.card k' = p ^ n')
    (fW : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 ⟶ Spec (.of k'))
    [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW] [SmoothOfRelativeDimension 1 fW]
    (eW : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 ⟶ Spec (.of (Polynomial k')))
    [IsOpenImmersion eW]
    (heW : eW ≫ Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))) = fW)
    (jW : V.1 ⟶ (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1) [IsOpenImmersion jW]
    (hjW : jW ≫ fW = fV)
    -- the restriction `g' : U' ⟶ V` of `pr₂` to `U' = pr₂⁻¹(V)`, with a compactification
    (U' : B.Scheme) [IsNoetherian U'.1]
    (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V)
    [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
    [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g')))
    (hpb : IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL))
      (B.inclusion.map (ObjectProperty.homMk jW : V ⟶ Stacks.ArtinSchreier.specObject
        (Polynomial k') B hL)))
    -- the origin `y`
    (y : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1)
    (hy0 : y.asIdeal = Ideal.span {Polynomial.X}) (hyc : IsClosed ({y} : Set _))
    (hyV : y ∉ Set.range jW.base) (hy : jW.base (genericPoint V.1) ⤳ y) (dy : ℕ)
    (hcardy : Nat.card ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y) =
      (p ^ n) ^ dy)
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
    (eA : A ≃+* (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.presheaf.stalk y)
    (hA : ∀ a : A, algebraMap A (V.1.residueField (genericPoint V.1)) a =
      (curveLocalRingToFunctionField jW hy).hom (eA a))
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (Fr : Gal(L / V.1.residueField (genericPoint V.1)))
    (hFrD :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L / V.1.residueField (genericPoint V.1)) P)
    (hFr :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P)
    -- the representation of `F_V` (the data of `exists_restrictScalarsRep_of_isLisse`)
    (r : ℕ) (ρ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (φ : (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jU g'
          jg').toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B V _ ρ hρ)
    (ψ₀ : LAdicSheaf.representationSheaf B V _ ρ hρ ⟶
      (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jU g'
          jg').toLAdicSheaf) (N : ℕ)
    (hφψ : φ ≫ ψ₀ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ₀ ≫ φ = (ℓ ^ N) • 𝟙 _)
    (mτ : ℕ) (τ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin mτ) E)
    (Pm : Matrix (Fin r) (Fin (mτ * d)) ℚ_[ℓ]) (Qm : Matrix (Fin (mτ * d)) (Fin r) ℚ_[ℓ])
    (hPQ : Pm * Qm = 1)
    (hα : ∀ e' : E, Qm * isogenyCoefficientAlgHom B V _
        (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
          (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jU g' jg')
        ρ hρ φ ψ₀ N E hφψ hψφ
      (algebraMap_conjIntegralSubring_algebraMap _ _) e' * Pm =
        restrictScalarsMatrix b (Matrix.scalar (Fin mτ) e'))
    (hτ : ∀ g, Qm * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
        (haveI := compactSpace_etaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
          (V.1.residueField (genericPoint V.1)) Ω).map
            (V.1.fromSpecResidueField (genericPoint V.1)))
         integralModel ρ hρ g)).val * Pm = (restrictScalarsRep b τ g).val) :
    letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
    letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
      (integralClosure A L)
    ∃ J : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1 →ₗ[E]
        Representation.invariants ((matrixRepresentation τ).comp
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P).subtype),
      Function.Injective J ∧
      J ∘ₗ (((restrictScalarsRepCoefficientSheaf B U x b σ
          hσ).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard) ^ dy) =
        ((Matrix.toLin' ((τ ((galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr⁻¹) :
          GL (Fin mτ) E) : Matrix (Fin mτ) (Fin mτ) E)).restrict
        (toLin'_mem_invariants_of_mem_normalizer τ
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P)
          (map_inv_mem_normalizer_map_inertia A (V.1.residueField (genericPoint V.1)) L P
            (galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr hFrD))) ∘ₗ J := by
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial k'))))
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  exact exists_laumonSpecializationInjection_of_isogeny hF0 hH2 B ℓ k U f e he j kbar p n hcard
    hℓp x E b σ hσ ψ n₀ k' c hψ hh hS hL z hz p₀ hσ₁ jg V fV jV kbar' n' hcard' fW eW heW jW hjW
    y hy0 hyc hyV hy dy hcardy L Ω A eA hA P Fr hFrD hFr
    (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
      (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jU g' jg')
    (LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom B ℓ
      (laumonFamilyProjection k' B hS hL) jg g' jg' jU _ hpb
      (laumonFamilySheaf k' B hS b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c
        z p₀ _ hσ₁) 1)
    (LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom_act B ℓ
      (laumonFamilyProjection k' B hS hL) jg g' jg' jU _ hpb _ 1)
    (LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeInv B ℓ
      (laumonFamilyProjection k' B hS hL) jg g' jg' jU _ hpb _ 1) _
    (LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom_comp_inv B ℓ
      (laumonFamilyProjection k' B hS hL) jg g' jg' jU _ hpb _ 1)
    r ρ hρ φ ψ₀ N hφψ hψφ mτ τ Pm Qm hPQ hα hτ

end Stacks.EtaleCohomology

end
