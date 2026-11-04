module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicLevelPoincarePairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicPoincarePurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopDegreeFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerNondivisibleReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagPurityProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerPointClassLevelSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerPointClassReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyCountAlgClosed

/-!
# Purity of the Frobenius on the cohomology of a smooth proper scheme with a rational point

The last assertion of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (`w = i` when `X` is
smooth and projective) follows from the weight bound by Poincaré duality. For `X` proper over a
finite field `k` with `q` elements, with a `k`-rational point, and `Y = X_k̄` connected and smooth
of relative dimension `d` over `k̄`, this file assembles the finite level Poincaré pairings with
their Frobenius factor `q^d` (`Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing`) from the
proved pieces:

* the count `H^{2d}(Y, ℤ/ℓⁿ⁺¹) ≅ ℤ/ℓⁿ⁺¹`
  (`Stacks.EtaleCohomology.nonempty_ext_unitSheaf_top_addEquiv_zmod_pow`);
* the Frobenius on `H^{2d}(Y, ℤ/ℓⁿ⁺¹)` is multiplication by `q^d`
  (`Stacks.EtaleCohomology.constantExtRestriction_geometricFrobeniusBaseChange_top`), the Kummer
  point class of a rational point being nondivisible
  (`Stacks.EtaleCohomology.rationalPointKummerClassNondivisible_of_kummerFlagPurity`, with
  `Stacks.EtaleCohomology.KummerFlag.kummerFlagPurity` and the level reduction square);
* local purity (`Stacks.EtaleCohomology.localPurity`);

and deduces purity of weight `i` on `Hⁱ(X_k̄, F ⊗ ℚ_ℓ)` from mixedness
(`Stacks.EtaleCohomology.LAdicSheaf.isCharpolyPureOfWeight_of_levelPairing`). The hypotheses
are the two inputs of Poincaré duality on `Y`,
`Stacks.EtaleCohomology.PoincareDualityCore` and `Stacks.EtaleCohomology.TopCohomologyPointClass`,
and the hypotheses on the coefficients `F`, `F'` and the pairing `μ` of
`Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing` and
`Stacks.EtaleCohomology.LAdicSheaf.isCharpolyPureOfWeight_of_levelPairing`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isCharpolyPureOfWeight_of_rationalPoint`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory
  etaleModuleInverseImageSheafPullbackMonoidal etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The base change of a proper morphism to `Spec k̄` is proper. -/
private theorem isProper_pullback_snd_specAlgebraMap {k : Type u} [Field k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] : IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
  MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) ‹IsProper f›

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] [LocallyOfFiniteType f] [IsSeparated f] in
/-- **The Frobenius on the top cohomology of `X_k̄` is multiplication by `q^d`, at a rational
point, given the class of a point**: for `X` proper over `k` with a `k`-rational point and
`Y = X_k̄` connected and smooth of relative dimension `d` over `k̄`, restriction along `π̄` is
multiplication by `q^d` on `H^{2d}(Y, ℤ/ℓⁿ⁺¹)` for every `n`, given that the class of a point
generates `H^{2d}` at level `ℓ` (`Stacks.EtaleCohomology.TopCohomologyPointClass`). -/
theorem constantExtRestriction_geometricFrobeniusBaseChange_top_of_topCohomologyPointClass
    [IsAlgClosed kbar] (d : ℕ)
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] (hℓ : IsUnit (ℓ : kbar))
    (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _) (hTop : TopCohomologyPointClass ℓ kbar) :
    ∀ (n : ℕ) (z : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d)),
      constantExtRestriction (ZMod (ℓ ^ (n + 1)))
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard) (2 * d) z =
          ((p ^ q) ^ d : ℕ) • z :=
  have := isProper_pullback_snd_specAlgebraMap kbar f
  constantExtRestriction_geometricFrobeniusBaseChange_top f kbar ℓ d p q hcard hℓ hpt
    (nonempty_ext_unitSheaf_top_addEquiv_zmod_pow ℓ hℓ
      (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) d)
    (rationalPointKummerClassNondivisible_of_kummerFlagPurity f kbar ℓ d hℓ hTop
      (KummerFlag.kummerFlagPurity kbar ℓ)
      (KummerFlag.kummerPointClassLevelReduction_of_reductionSquare _ _
        (KummerFlag.kummerPointClassReductionSquare _ _)))

/-- **Purity of weight `i` on `Hⁱ(X_k̄, F ⊗ ℚ_ℓ)` for `X` smooth and proper with a rational
point**, given Poincaré duality on `X_k̄`. Let `X` be proper over the finite field `k` with
`p ^ q` elements and a `k`-rational point, `k̄` algebraically closed, `Y = X_k̄` connected and
smooth of relative dimension `d` over `k̄`, `ℓ` invertible in `k̄`, and `F`, `F'` ℓ-adic sheaves
with flat levels and perfect `RΓ(X_k̄, -)` at every level, with pairings
`μₙ : Fₙ ⊗ F'ₙ ⟶ ℤ/ℓⁿ⁺¹` which are perfect on the geometric fibres of `Y`, `F'ₙ|_Y` being lisse
with flat fibres. If the Frobenius on `Hⁱ(X_k̄, F ⊗ ℚ_ℓ)` is mixed of weight `≤ i` and that on
`H^{2d-i}(X_k̄, F' ⊗ ℚ_ℓ)` is mixed of weight `≤ 2d - i`, then the former is pure of weight
`i`, given the core of Poincaré duality (`Stacks.EtaleCohomology.PoincareDualityCore`) and the
class of a point (`Stacks.EtaleCohomology.TopCohomologyPointClass`) over `k̄`. -/
theorem LAdicSheaf.isCharpolyPureOfWeight_of_rationalPoint [IsAlgClosed kbar] (d : ℕ)
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] (hℓ : IsUnit (ℓ : kbar))
    (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _) (hPD : PoincareDualityCore ℓ kbar)
    (hTop : TopCohomologyPointClass ℓ kbar) (F F' : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.levelComplex B X ℓ F n))))
    (hF' : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F' n))
    (hP' : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.levelComplex B X ℓ F' n))))
    (μ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        X.1.smallEtaleTopology)
    (hlisse : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n))))
    (hflat : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
      Module.Flat (ZMod (ℓ ^ (n + 1)))
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk f) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
              (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n)))))
    (hμ : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
      Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n)))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n))) ≫
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).map
          (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar) (ℓ ^ (n + 1))
            (μ n))).hom))
    (i : ℕ) (hi : i ≤ 2 * d) (ι : ℚ_[ℓ] →+* ℂ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar F i)]
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar F' (2 * d - i))]
    (hwt : IsCharpolyMixedOfWeightLE (p ^ q) ι i
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
        (CompactificationOf.ofProper f) kbar p q hcard F i).hom)
    (hwt' : IsCharpolyMixedOfWeightLE (p ^ q) ι (2 * d - i)
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
        (CompactificationOf.ofProper f) kbar p q hcard F' (2 * d - i)).hom) :
    IsCharpolyPureOfWeight (p ^ q) ι i
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
        (CompactificationOf.ofProper f) kbar p q hcard F i).hom := by
  have := isProper_pullback_snd_specAlgebraMap kbar f
  obtain ⟨ε, hl, hr, hε⟩ := LAdicSheaf.exists_levelPairing B X ℓ f kbar p q hcard d hℓ
    (fun _ _ => hPD) hTop
    (nonempty_ext_unitSheaf_top_addEquiv_zmod_pow ℓ hℓ
      (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) d)
    (constantExtRestriction_geometricFrobeniusBaseChange_top_of_topCohomologyPointClass B X ℓ f
      kbar p q hcard d hℓ hpt hTop)
    F F' μ hlisse hflat hμ i hi
  exact LAdicSheaf.isCharpolyPureOfWeight_of_levelPairing B X ℓ f (CompactificationOf.ofProper f)
    kbar p q hcard F F' hF hP hF' hP' i d ι hwt hwt' ε hl hr hε

end Stacks.EtaleCohomology

end
