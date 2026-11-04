module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveExtWeilPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicFrobeniusLevel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FrobeniusBaseChangeDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityDegreeZero

/-!
# `H⁰` and `H²` of the constant sheaf on a curve, with the Frobenius

Let `X` be a smooth proper curve over an algebraically closed field `k`, `N` an integer invertible
in `k` and `g : X ⟶ X` a morphism over `k`. On `Hⁱ(X, ℤ/N) = Ext^i(ℤ/N_X, ℤ/N_X)`:

* `g^*` is the identity on `H⁰` (`Stacks.Picard.constantExtRestriction_zero_eq`): `H⁰(X, ℤ/N)` is
  `H⁰(X, μ_N) = μ_N(k)` through a primitive root of unity, on which `g` acts trivially;
* `g^*` is multiplication by `c` on `H²` when pullback along `g` multiplies degrees of line bundles
  by `c` (`Stacks.Picard.constantExtRestriction_two_eq_smul`): `H²(X, ℤ/N) ≅ H²(X, μ_N) ≅ ℤ/N`
  through the trace map, and the trace of `g^* y` is `c` times that of `y`
  (Étale Cohomology, Lemma 0AMB).

For `X` proper over a finite field `k` with `q` elements and `X_k̄` a smooth proper curve, the
geometric Frobenius `π_X^*` therefore acts on the levels of `H⁰(X_k̄, ℤ_ℓ)` as the identity and on
those of `H²(X_k̄, ℤ_ℓ)` as multiplication by `q`, and so on `H⁰(X_k̄, ℚ_ℓ)` and `H²(X_k̄, ℚ_ℓ)`
(`Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedFrobenius_constant_zero`,
`Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedFrobenius_constant_two`): the
statements on `H⁰` and `H²` in the proof of [Tag 03V8](https://stacks.math.columbia.edu/tag/03V8).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.Picard

open Stacks.EtaleCohomology

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f]

include f in
/-- **`g^*` on `H²(X, ℤ/N)` of a curve is multiplication by `c`** when pullback along `g` multiplies
degrees of line bundles by `c`: through `H²(X, ℤ/N) ≅ H²(X, μ_N)` the trace map intertwines `g^*`
with multiplication by `c` (Lemma 0AMB). -/
theorem constantExtRestriction_two_eq_smul {N : ℕ} (hN : IsUnit (N : k)) (g : X ⟶ X)
    (hg : g ≫ f = f) (c : ℤ)
    (hdeg : ∀ L : ofScheme X,
      picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le (schemePullbackClassHom g L) =
        c * picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L)
    (y : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology) 2) :
    constantExtRestriction (ZMod N) g 2 y = c • y := by
  have hN0 : N ≠ 0 := Stacks.Kummer.neZero_of_isUnit hN
  haveI : NeZero (N : k) := ⟨hN.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k N
  have hg' : g ≫ f = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) := by
    rw [hg, show CommRingCat.ofHom (RingHom.id k) = 𝟙 _ from rfl, Spec.map_id, Category.comp_id]
  have htw : Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1} g N 2
        (extRootsOfUnityAddEquiv f hζ hN0 2 y) =
      extRootsOfUnityAddEquiv f hζ hN0 2 (constantExtRestriction (ZMod N) g 2 y) := by
    have := rootsOfUnityPullbackMap_extForgetSheafH hζ hN0 f f g (RingHom.id k) 1 hg' (by simp) y
    rw [Nat.cast_one, one_smul] at this
    exact this
  have hT := Stacks.Kummer.smoothProperCurveTrace_rootsOfUnityPullbackMap f f hN hN g c hdeg
    (extRootsOfUnityAddEquiv f hζ hN0 2 y)
  rw [htw] at hT
  apply (extRootsOfUnityAddEquiv f hζ hN0 2).injective
  apply (Stacks.Kummer.smoothProperCurveTrace f hN).injective
  rw [hT, map_zsmul, map_zsmul]

include f in
/-- **`g^*` on `H⁰(X, ℤ/N)` of a curve is the identity** for `g` over `k`: through
`H⁰(X, ℤ/N) ≅ H⁰(X, μ_N) = μ_N(Γ(X, 𝒪_X))`, `g` fixes the roots of unity of `k`. -/
theorem constantExtRestriction_zero_eq {N : ℕ} (hN : IsUnit (N : k)) (g : X ⟶ X)
    (hg : g ≫ f = f)
    (y : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology) 0) :
    constantExtRestriction (ZMod N) g 0 y = y := by
  have hN0 : N ≠ 0 := Stacks.Kummer.neZero_of_isUnit hN
  haveI : NeZero (N : k) := ⟨hN.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k N
  haveI : IsIntegral X := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  haveI : NeZero N := ⟨hN0⟩
  have hg' : g ≫ f = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) := by
    rw [hg, show CommRingCat.ofHom (RingHom.id k) = 𝟙 _ from rfl, Spec.map_id, Category.comp_id]
  have h := rootsOfUnityPullbackMap_extForgetSheafH hζ hN0 f f g (RingHom.id k) 1 hg' (by simp) y
  rw [Nat.cast_one, one_smul,
    rootsOfUnityPullbackMap_zero_eq_self.{u, 0, u + 1} f hζ g hg] at h
  exact ((extRootsOfUnityAddEquiv f hζ hN0 0).injective h).symm

include f in
/-- **`H¹(X, ℤ/N) ≅ Pic(X)[N]` compatibly with pullback** along every `g : X ⟶ X` over `k`:
through `H¹(X, ℤ/N) ≅ H¹(X, μ_N)` (a primitive root of unity) and the Kummer sequence. -/
theorem exists_ext_one_addEquiv_torsionBy {N : ℕ} (hN : IsUnit (N : k)) :
    ∃ e : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology) 1 ≃+
        Submodule.torsionBy ℤ (ofScheme X) (N : ℤ),
      ∀ (g : X ⟶ X) (_ : g ≫ f = f) y, e (constantExtRestriction (ZMod N) g 1 y) =
        torsionByRestrict (A := ofScheme X) (schemePullbackClassHom g) (N : ℤ) (e y) := by
  have hN0 : N ≠ 0 := Stacks.Kummer.neZero_of_isUnit hN
  haveI : NeZero (N : k) := ⟨hN.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k N
  haveI : IsIntegral X := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have hX : IsUnit ((N : ℕ) : Γ(X, ⊤)) := Stacks.Kummer.isUnit_globalSections f hN
  have hsurj := Stacks.Kummer.surjective_sheafH_map_powMap_zero.{u + 1, u, u + 1} X (n := N)
    (Stacks.Kummer.exists_pow_eq_globalUnit.{u} X N f (Nat.pos_of_ne_zero hN0))
  refine ⟨(extRootsOfUnityAddEquiv f hζ hN0 1).trans
    (Stacks.Kummer.h1RootsOfUnityAddEquivPicardTorsion.{u + 1, u + 1, u} X N hN0 hX hsurj),
    fun g hg y => Subtype.ext ?_⟩
  have hg' : g ≫ f = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) := by
    rw [hg, show CommRingCat.ofHom (RingHom.id k) = 𝟙 _ from rfl, Spec.map_id, Category.comp_id]
  have htw : Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1} g N 1
        (extRootsOfUnityAddEquiv f hζ hN0 1 y) =
      extRootsOfUnityAddEquiv f hζ hN0 1 (constantExtRestriction (ZMod N) g 1 y) := by
    have := rootsOfUnityPullbackMap_extForgetSheafH hζ hN0 f f g (RingHom.id k) 1 hg' (by simp) y
    rw [Nat.cast_one, one_smul] at this
    exact this
  change ((Stacks.Kummer.h1RootsOfUnityAddEquivPicardTorsion.{u + 1, u + 1, u} X N hN0 hX hsurj
    (extRootsOfUnityAddEquiv f hζ hN0 1 (constantExtRestriction (ZMod N) g 1 y)) :
      ofScheme X)) = _
  rw [← htw]
  exact Stacks.Kummer.h1RootsOfUnityAddEquivPicardTorsion_naturality.{u + 1, u + 1, u} g N hN0 hX hX
    hsurj hsurj _

end Stacks.Picard

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
-- the structure projections of `Stacks.Models.RegularModelSituation` are global instances whose
-- conclusions match every goal and send instance search astray; they are irrelevant here
attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

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
  [IsAlgClosed kbar] [IsCurve kbar (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [Smooth (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]

local instance : QuasiSeparatedSpace X.obj :=
  @AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace X.1
    (inferInstance : AlgebraicGeometry.IsNoetherian X.1).toIsLocallyNoetherian

include hcard in
/-- **`π_X^*` on the levels of `H²(X_k̄, ℤ_ℓ)` of a curve is multiplication by `q`.** -/
theorem LAdicSheaf.canonicalFrobenius_constantLevel_two (hℓ : IsUnit (ℓ : kbar)) (n : ℕ)
    (x : (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar
      ((2 : ℕ) : ℤ)).obj (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) :
    (canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f (CompactificationOf.ofProper f) kbar p q
      hcard ((padicCoefficientComplex B X ℓ).obj
        (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) ((2 : ℕ) : ℤ)).hom x =
      (Fintype.card k : ℤ) • x := by
  obtain ⟨Φ, hΦ⟩ := LAdicSheaf.exists_addEquiv_constantLevel_frobenius B X ℓ f kbar p q hcard 2 n
  have hN : IsUnit (((ℓ ^ (n + 1) : ℕ)) : kbar) := by rw [Nat.cast_pow]; exact hℓ.pow _
  apply Φ.injective
  refine (hΦ x).trans ?_
  rw [map_zsmul]
  exact Stacks.Picard.constantExtRestriction_two_eq_smul
    (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) hN
    (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
    (geometricFrobeniusBaseChange_comp_snd (Over.mk f) kbar p q hcard) _
    (picardDegree_schemePullbackClassHom_geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
    (Φ x)

include hcard in
/-- **`π_X^*` on the levels of `H⁰(X_k̄, ℤ_ℓ)` of a curve is the identity.** -/
theorem LAdicSheaf.canonicalFrobenius_constantLevel_zero (hℓ : IsUnit (ℓ : kbar)) (n : ℕ)
    (x : (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar
      ((0 : ℕ) : ℤ)).obj (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) :
    (canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f (CompactificationOf.ofProper f) kbar p q
      hcard ((padicCoefficientComplex B X ℓ).obj
        (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) ((0 : ℕ) : ℤ)).hom x =
      x := by
  obtain ⟨Φ, hΦ⟩ := LAdicSheaf.exists_addEquiv_constantLevel_frobenius B X ℓ f kbar p q hcard 0 n
  have hN : IsUnit (((ℓ ^ (n + 1) : ℕ)) : kbar) := by rw [Nat.cast_pow]; exact hℓ.pow _
  apply Φ.injective
  refine (hΦ x).trans ?_

  exact Stacks.Picard.constantExtRestriction_zero_eq
    (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) hN
    (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
    (geometricFrobeniusBaseChange_comp_snd (Over.mk f) kbar p q hcard) (Φ x)

include hcard in
/-- **The levels of `H¹(X_k̄, ℤ_ℓ)` of a curve are `Pic(X_k̄)[ℓⁿ⁺¹]`, with `π_X^*` acting as pullback
along `π̄ = π_X × id`.** -/
theorem LAdicSheaf.exists_addEquiv_constantLevel_one_torsionBy (hℓ : IsUnit (ℓ : kbar)) (n : ℕ) :
    ∃ e : (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar
          ((1 : ℕ) : ℤ)).obj (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n) ≃+
        Submodule.torsionBy ℤ (Stacks.Picard.ofScheme (fieldBaseChange (Over.mk f) kbar))
          ((ℓ : ℤ) ^ (n + 1)),
      ∀ x, e ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f (CompactificationOf.ofProper f)
          kbar p q hcard ((padicCoefficientComplex B X ℓ).obj
            (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) ((1 : ℕ) : ℤ)).hom x) =
        Stacks.Picard.torsionByRestrict
          (A := Stacks.Picard.ofScheme (fieldBaseChange (Over.mk f) kbar))
          (Stacks.Picard.schemePullbackClassHom (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard))
          ((ℓ : ℤ) ^ (n + 1)) (e x) := by
  obtain ⟨Φ, hΦ⟩ := LAdicSheaf.exists_addEquiv_constantLevel_frobenius B X ℓ f kbar p q hcard 1 n
  have hN : IsUnit (((ℓ ^ (n + 1) : ℕ)) : kbar) := by rw [Nat.cast_pow]; exact hℓ.pow _
  obtain ⟨κ, hκ⟩ := Stacks.Picard.exists_ext_one_addEquiv_torsionBy
    (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) hN
  have key : ∀ c : ℤ, ((ℓ ^ (n + 1) : ℕ) : ℤ) = c → ∃ e : (geometricCompactSupportPadicCohomology
        B X ℓ f (CompactificationOf.ofProper f) kbar ((1 : ℕ) : ℤ)).obj
          (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n) ≃+
        Submodule.torsionBy ℤ (Stacks.Picard.ofScheme (fieldBaseChange (Over.mk f) kbar)) c,
      ∀ x, e ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f (CompactificationOf.ofProper f)
          kbar p q hcard ((padicCoefficientComplex B X ℓ).obj
            (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) ((1 : ℕ) : ℤ)).hom x) =
        Stacks.Picard.torsionByRestrict
          (A := Stacks.Picard.ofScheme (fieldBaseChange (Over.mk f) kbar))
          (Stacks.Picard.schemePullbackClassHom (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard))
          c (e x) := by
    rintro c rfl
    refine ⟨Φ.trans κ, fun x => ?_⟩
    change κ (Φ _) = _
    rw [hΦ]
    exact hκ _ (geometricFrobeniusBaseChange_comp_snd (Over.mk f) kbar p q hcard) _
  exact key _ (by push_cast; rfl)

/-- **`π_X^*` on `H²(X_k̄, ℤ_ℓ)` of a curve is multiplication by `q`.** -/
theorem LAdicSheaf.geometricCompactlySupportedFrobenius_constant_two (hℓ : IsUnit (ℓ : kbar)) :
    LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f (CompactificationOf.ofProper f) kbar
        p q hcard (LAdicSheaf.constantSystem B X ℓ) ((2 : ℕ) : ℤ) =
      (Fintype.card k : ℤ) • 𝟙 _ := by
  refine limit.hom_ext fun n => ?_
  have h := LAdicSheaf.geometricCompactlySupportedFrobenius_π B X ℓ f
    (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.constantSystem B X ℓ)
    ((2 : ℕ) : ℤ) n.unop
  change _ ≫ LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f _ kbar _ _ n.unop =
    _ ≫ LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f _ kbar _ _ n.unop
  rw [h]
  ext x
  refine (LAdicSheaf.canonicalFrobenius_constantLevel_two B X ℓ f kbar p q hcard hℓ n.unop _).trans ?_
  exact (map_zsmul _ _ _).symm

/-- **`π_X^*` on `H⁰(X_k̄, ℤ_ℓ)` of a curve is the identity.** -/
theorem LAdicSheaf.geometricCompactlySupportedFrobenius_constant_zero (hℓ : IsUnit (ℓ : kbar)) :
    LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f (CompactificationOf.ofProper f) kbar
        p q hcard (LAdicSheaf.constantSystem B X ℓ) ((0 : ℕ) : ℤ) = 𝟙 _ := by
  refine limit.hom_ext fun n => ?_
  have h := LAdicSheaf.geometricCompactlySupportedFrobenius_π B X ℓ f
    (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.constantSystem B X ℓ)
    ((0 : ℕ) : ℤ) n.unop
  change _ ≫ LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f _ kbar _ _ n.unop =
    _ ≫ LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f _ kbar _ _ n.unop
  rw [h]
  ext x
  exact LAdicSheaf.canonicalFrobenius_constantLevel_zero B X ℓ f kbar p q hcard hℓ n.unop _

/-- **`π_X^*` on `H²(X_k̄, ℚ_ℓ)` of a curve is multiplication by `q`.** -/
theorem LAdicSheaf.rationalGeometricCompactlySupportedFrobenius_constant_two
    (hℓ : IsUnit (ℓ : kbar)) :
    LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f (CompactificationOf.ofProper f)
        kbar p q hcard (LAdicSheaf.constantSystem B X ℓ) ((2 : ℕ) : ℤ) =
      (Fintype.card k : ℤ) • 𝟙 _ := by
  change (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f (CompactificationOf.ofProper f) kbar
      p q hcard (LAdicSheaf.constantSystem B X ℓ) ((2 : ℕ) : ℤ)) = _
  rw [LAdicSheaf.geometricCompactlySupportedFrobenius_constant_two B X ℓ f kbar p q hcard hℓ,
    Functor.map_zsmul, CategoryTheory.Functor.map_id]
  rfl

/-- **`π_X^*` on `H⁰(X_k̄, ℚ_ℓ)` of a curve is the identity.** -/
theorem LAdicSheaf.rationalGeometricCompactlySupportedFrobenius_constant_zero
    (hℓ : IsUnit (ℓ : kbar)) :
    LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f (CompactificationOf.ofProper f)
        kbar p q hcard (LAdicSheaf.constantSystem B X ℓ) ((0 : ℕ) : ℤ) = 𝟙 _ := by
  change (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f (CompactificationOf.ofProper f) kbar
      p q hcard (LAdicSheaf.constantSystem B X ℓ) ((0 : ℕ) : ℤ)) = _
  rw [LAdicSheaf.geometricCompactlySupportedFrobenius_constant_zero B X ℓ f kbar p q hcard hℓ,
    CategoryTheory.Functor.map_id]
  rfl

end Stacks.EtaleCohomology

end
