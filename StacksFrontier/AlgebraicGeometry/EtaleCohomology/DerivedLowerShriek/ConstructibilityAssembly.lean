module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.Constructibility
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.GeometricFibreStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ShrinkCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.AffineLine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.AffineLineReductionOfIsUnit
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeAllUniverses

/-!
# Constructibility of the derived lower shriek: assembly

This file discharges the named arguments of the 0GKZ / 0GL0 / 0GK0 development by the theorems
available here, and reads the results at a coefficient ring `Λ : Type`:

* Tag 095T at every coefficient universe is
  `cohomologyCommutesWithBaseChange_of_isProper_allUniverses`;
* Tag 095U is `isZero_rightDerived_etaleAbelianDirectImage_of_isProper`;
* the case of the affine line (Tag 0GKZ), the argument `hA1` of the 0GL0 reductions, is
  `isConstructibleEtaleComplex_derivedLowerShriekUnbounded_affineLine_of_isUnit` at the ring
  `Shrink.{u + 1} Λ`, read at `Λ` by
  `isConstructibleEtaleComplex_derivedLowerShriekUnbounded_single_of_shrink`.

The results of the last section take Tag 0GKV for primes invertible on the base (`h0GKV`) as a
named argument; they are unregistered intermediates, discharged in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityOfIsUnit`.

## Main results

* `lowerShriekConstructibleOnSheaves_of_shrink`: the sheaf form of 0GL0 descends from
  `Shrink Λ` to `Λ`.
* `lowerShriekConstructibleOnSheaves_affineLine_of_isUnit_natCast_of_directImageZMod`: Tag 0GKZ
  for `Λ : Type` killed by an integer invertible on the base, granted 0GKV.
* `isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_isUnit_natCast_of_directImageZMod`
  and its analogue for `D⁺_{tors, c}`: Tag 0GL0 for `Λ : Type` killed by an integer invertible on
  the target, granted 0GKV.
* `derivedLowerShriekPlusStalkIso`: Tag 0GK0 for bounded below complexes with torsion
  cohomology, at every coefficient universe.
* `isLE_derivedLowerShriekUnbounded_obj_of_fibre_le`: the bound of Tag 0G2A (3).

## References

* [Stacks Project, Tag 0GKZ](https://stacks.math.columbia.edu/tag/0GKZ)
* [Stacks Project, Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0)
* [Stacks Project, Tag 0GK0](https://stacks.math.columbia.edu/tag/0GK0)
* [Stacks Project, Tag 0G2A](https://stacks.math.columbia.edu/tag/0G2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.CompactificationOf

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

/-! ### Tag 0GK0 and the bounds, unconditionally -/

section Stalk

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f)) (y : GeometricPoint Y)

/-- **[Stacks, Tag 0GK0] for bounded below complexes with torsion cohomology.** Let `f : X ⟶ Y` be
a separated morphism of finite type with a compactification `j`, let `Λ` be a ring and let
`ȳ : Spec k ⟶ Y` be a geometric point, with geometric fibre `f_ȳ : X_ȳ ⟶ Spec k`. For every
`K` in `D⁺(X_étale, Λ)` whose cohomology sheaves are torsion there is a canonical isomorphism
`(Rf_! K)_ȳ ≅ RΓ_c(X_ȳ, K|_{X_ȳ})` in `D(Λ)`. -/
def derivedLowerShriekPlusStalkIso (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X))
    (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X).obj K.obj)) :
    (etaleModuleDerivedStalk.{u, r} Λ y).obj
        ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj K.obj) ≅
      (compactlySupportedCohomologyUnbounded.{u, r} y.residueField (pullback.snd f y.hom)
          (j.baseChange (IsPullback.of_hasPullback f y.hom)) Λ).obj
        ((etaleModuleRingDerivedInverseImage.{u, r} Λ (pullback.fst f y.hom)).obj K.obj) :=
  haveI : K.obj.IsGE K.property.choose := K.property.choose_spec
  derivedLowerShriekUnboundedStalkIso.{u, r} Λ f j y
    (fun _ _ p _ ↦ cohomologyCommutesWithBaseChange_of_isProper_allUniverses.{r} p) K.obj
    K.property.choose hK

end Stalk

/-! ### The bound of Tag 0G2A (3) -/

section Bound

variable (Λ : Type) [Ring Λ]

/-- **[Stacks, Tag 0G2A], part (3), the bound on the right.** Let `d` bound the dimensions of the
fibres of `f̄ : X̄ ⟶ Y`, for a compactification `j` of `f`. For `E` in `D⁺_{tors}(X_étale, Λ)`
with `E ≤ b`, `Rf_! E ≤ b + 2d`. -/
theorem isLE_derivedLowerShriekUnbounded_obj_of_fibre_le {X Y : Scheme.{u}} {f : X ⟶ Y}
    (j : CompactificationOf (Over.mk f)) (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim (j.toBase.fiber y) ≤ d)
    (E : DerivedCategory (EtaleModules.{u, 0} Λ X))
    (hE : DerivedCategoryB.derivedCategoryBPlus (IsTorsionEtaleModule.{u, 0} Λ X) E) (b : ℤ)
    [E.IsLE b] : ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj E).IsLE (b + 2 * d) :=
  isLE_derivedLowerShriekUnbounded_obj_of_fibreBound.{u, 0} Λ j
    (fun _ _ p _ ↦
      isZero_rightDerived_etaleAbelianDirectImage_of_isProper p)
    d hd E hE b

end Bound

/-! ### Tags 0GKZ and 0GL0 at a coefficient ring in `Type` -/

section Constructible

variable (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]

/-- **The sheaf form of Tag 0GL0 descends along `Shrink`**: if `Rf_!` carries constructible
torsion sheaves of `Shrink.{u + 1} Λ`-modules to objects with constructible cohomology, it does so
for sheaves of `Λ`-modules. -/
theorem lowerShriekConstructibleOnSheaves_of_shrink {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : LowerShriekConstructibleOnSheaves (Shrink.{u + 1} Λ) f) :
    LowerShriekConstructibleOnSheaves Λ f := fun j F hF hFt ↦
  isConstructibleEtaleComplex_derivedLowerShriekUnbounded_single_of_shrink Λ j F
    (h j _ ((isConstructibleEtaleModule_shrink_iff Λ X F).2 hF)
      ((isTorsionEtaleModule_shrink_iff Λ X F).2 hFt))

/-- A sheaf of modules over a ring in which the integer `n` vanishes is killed by `n`. -/
theorem nsmul_id_eq_zero_of_natCast_eq_zero {R : Type r} [Ring R] {n : ℕ} (hR : (n : R) = 0)
    {X : Scheme.{u}} (F : EtaleModules.{u, r} R X) : n • 𝟙 F = 0 := by
  apply (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} R)).map_injective
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  ext U x
  simp [← Nat.cast_smul_eq_nsmul R, hR]

/-- **[Stacks, Tag 0GKZ] for a coefficient ring in `Type` killed by an integer invertible on the
base, granted Tag 0GKV for primes invertible on the base.** Let `Λ` be a Noetherian ring in which
the integer `n > 0` vanishes, and `Y` an affine scheme on which `n` is invertible. For every
constructible sheaf `ℱ` of `Λ`-modules on `𝔸¹_Y`, `Rf_! ℱ` has constructible cohomology sheaves,
where `f : 𝔸¹_Y ⟶ Y` is the structure morphism and `Rf_!` is computed through any compactification
of `f`. -/
theorem lowerShriekConstructibleOnSheaves_affineLine_of_isUnit_natCast_of_directImageZMod
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit ((ℓ : ℕ) : Γ(S, ⊤)) → ∀ (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    {n : ℕ} (hn0 : 0 < n) (hΛ : (n : Λ) = 0) (Y : Scheme.{u}) [IsAffine Y]
    (hnY : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    LowerShriekConstructibleOnSheaves Λ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) :=
  have hΛ' : ((n : ℕ) : Shrink.{u + 1} Λ) = 0 := by
    simpa using congrArg (Shrink.ringEquiv.{u + 1} Λ).symm hΛ
  lowerShriekConstructibleOnSheaves_of_shrink Λ _ fun j F hF _ ↦
    isConstructibleEtaleComplex_derivedLowerShriekUnbounded_affineLine_of_isUnit
      (Shrink.{u + 1} Λ)
      (fun _ _ p _ ↦ cohomologyCommutesWithBaseChange_of_isProper_allUniverses.{u + 1} p) h0GKV
      (fun _ _ p _ ↦ isZero_rightDerived_etaleAbelianDirectImage_of_isProper p)
      Y j F hF hn0 (nsmul_id_eq_zero_of_natCast_eq_zero hΛ' F) hnY

/-- **[Stacks, Tag 0GL0] for `D⁺_{tors, c}` and a coefficient ring in `Type` killed by an integer
invertible on the target, granted Tag 0GKV for primes invertible on the base.** Let
`f : X ⟶ Y` be a separated morphism of finite presentation of quasi-compact and quasi-separated
schemes, `j` a compactification of `f`, `Λ` a Noetherian ring in which the integer `n > 0`
vanishes, with `n` invertible on `Y`. Then `Rf_!` carries `D⁺_{tors, c}(X_étale, Λ)` into
`D⁺_{tors, c}(Y_étale, Λ)`. -/
theorem isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_isUnit_natCast_of_directImageZMod
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit ((ℓ : ℕ) : Γ(S, ⊤)) → ∀ (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    {n : ℕ} (hn0 : 0 < n) (hΛ : (n : Λ) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (hnY : IsUnit ((n : ℕ) : Γ(Y, ⊤)))
    (j : CompactificationOf (Over.mk f)) (K : DerivedCategory (EtaleModules.{u, 0} Λ X))
    (hK : IsTorsionConstructibleEtaleComplexPlus Λ K) :
    IsTorsionConstructibleEtaleComplexPlus Λ ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj K) :=
  isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_affineLine_of_isUnit.{u, 0}
    Λ (fun _ _ p _ ↦ cohomologyCommutesWithBaseChange_of_isProper p)
    (fun S _ hnS ↦
      lowerShriekConstructibleOnSheaves_affineLine_of_isUnit_natCast_of_directImageZMod Λ h0GKV
        hn0 hΛ S hnS)
    f j K hK hnY

/-- **[Stacks, Tag 0GL0] for `D_c` and a coefficient ring in `Type` killed by an integer
invertible on the target, granted Tag 0GKV for primes invertible on the base.** Let
`f : X ⟶ Y` be a separated morphism of finite presentation of quasi-compact and quasi-separated
schemes, `j` a compactification of `f`, `Λ` a Noetherian ring in which the integer `n > 0`
vanishes, with `n` invertible on `Y`. Then `Rf_!` carries `D_c(X_étale, Λ)` into
`D_c(Y_étale, Λ)`. -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_isUnit_natCast_of_directImageZMod
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit ((ℓ : ℕ) : Γ(S, ⊤)) → ∀ (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    {n : ℕ} (hn0 : 0 < n) (hΛ : (n : Λ) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (hnY : IsUnit ((n : ℕ) : Γ(Y, ⊤)))
    (j : CompactificationOf (Over.mk f)) (K : DerivedCategory (EtaleModules.{u, 0} Λ X))
    (hK : IsConstructibleEtaleComplex Λ K) :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj K) :=
  isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_affineLine_of_isUnit.{u, 0} Λ
    (fun _ _ p _ ↦ cohomologyCommutesWithBaseChange_of_isProper p)
    (fun _ _ p _ ↦
      isZero_rightDerived_etaleAbelianDirectImage_of_isProper p)
    (fun S _ hnS ↦
      lowerShriekConstructibleOnSheaves_affineLine_of_isUnit_natCast_of_directImageZMod Λ h0GKV
        hn0 hΛ S hnS)
    (fun x ↦ isOfFinAddOrder_iff_nsmul_eq_zero.2
      ⟨n, hn0, by rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]⟩)
    f j K hK hnY

end Constructible

end Stacks.EtaleCohomology

end
