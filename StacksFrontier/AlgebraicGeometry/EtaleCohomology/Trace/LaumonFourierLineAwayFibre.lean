module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineLisseLattice
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.HomologyGeometricFibres

/-!
# Laumon's local theory away from `a = 0`: the fibres and the first direct image

`Stacks.EtaleCohomology.LaumonFourierLineAwayLevelZeroInput`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) asks that all the `Rˢ g'_!` of the
restriction to `U' = pr₂⁻¹(V')` of the level zero `K₀` of the Fourier family
`K = pr₁^*ℱ_σ ⊗ L_ψ'(a xⁿ + x t)` (a lisse sheaf killed by `ℓ` on `Spec k'[x][t]`) be locally
constant of finite type, for `a ≠ 0` and `n` large prime to `p`. It splits into:

* **the fibres** (`Stacks.EtaleCohomology.LaumonFourierLineAwayFibreVanishing`): for `q ≠ 1`,
  `H^q_c` of `K₀` on the geometric fibre over every point of `V'` vanishes. For `q = 0` this is
  the absence of compactly supported sections of a lisse sheaf on an affine curve, for `q = 2`
  the vanishing of the coinvariants of the inertia at `∞`, where all the slopes equal `n > 1`, and
  for `q ≥ 3` the cohomological dimension of a curve. By proper base change (Tag 0F7L,
  `Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_geometricFibres`) the
  `R^q g'_!(K₀|_{U'})`, `q ≠ 1`, then vanish;
* **the first direct image** (`Stacks.EtaleCohomology.LaumonFourierLineAwayFirstLocallyConstant`):
  `R¹g'_!(K₀|_{U'})` is locally constant of finite type: a constructible sheaf on a curve without
  punctual sections whose stalks have constant length (the Euler characteristic
  `-χ_c = Swan_∞ - rank = (n - 1) rank` of the fibres is constant, by the
  Grothendieck–Ogg–Shafarevich formula) is locally constant.

`Stacks.EtaleCohomology.laumonFourierLineAwayLevelZeroInput_of_fibre` proves
`Stacks.EtaleCohomology.LaumonFourierLineAwayLevelZeroInput` from the two
(`Stacks.EtaleCohomology.LaumonFourierLineAwayFibreInput`), hence, with
`Stacks.EtaleCohomology.laumonFourierLineLisseAwayInput_of_levelZero`,
`Stacks.EtaleCohomology.LaumonFourierLineLisseAwayInput`
(`Stacks.EtaleCohomology.laumonFourierLineLisseAwayInput_of_fibre`).

## Main definitions

* `Stacks.EtaleCohomology.LaumonFourierLineAwayFibreVanishing`,
  `Stacks.EtaleCohomology.LaumonFourierLineAwayFirstLocallyConstant`,
  `Stacks.EtaleCohomology.LaumonFourierLineAwayFibreInput`.

## Main results

* `Stacks.EtaleCohomology.laumonFourierLineAwayLevelZeroInput_of_fibre`.
* `Stacks.EtaleCohomology.laumonFourierLineLisseAwayInput_of_fibre`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard` of the derived category, hence so do the statements here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix
open CategoryTheory.LAdicTower

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

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

/-- **The fibres of the level zero of the Fourier family have no `H^q_c`, `q ≠ 1`, for
`a ≠ 0`**: for every finite extension `k'` of `k`, `a ∈ k'ˣ`, all the data of the family, every
open `V'` of the `t`-line, `U' = pr₂⁻¹(V')`, any compactification of `g' : U' → V'` and every point
`y` of `V'`, `H^q_c` of the restriction of the level zero `K₀` of the flat model of the Fourier
family to the geometric fibre of `g'` at `y` vanishes for `q ≠ 1`. -/
public def LaumonFourierLineAwayFibreVanishing : Prop :=
  ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (a : k'), a ≠ 0 →
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
    IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV') →
    haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
      inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
    ∀ (y : V'.1) (q : ℤ), q ≠ 1 → IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((derivedLowerShriek.{u, 0}
        (pullback.snd (B.inclusion.map g') (GeometricPoint.ofPoint V'.1 y).hom)
        (jg'.baseChange (IsPullback.of_hasPullback (B.inclusion.map g')
          (GeometricPoint.ofPoint V'.1 y).hom)) ℤ_[ℓ]).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} ℤ_[ℓ]
          (pullback.fst (B.inclusion.map g') (GeometricPoint.ofPoint V'.1 y).hom)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)).obj
              (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
            (laumonFourierFamilySheaf k' B hS b
              (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _
                hσ₁).toLAdicSheaf)) 0))))))

/-- **The first direct image of the level zero of the Fourier family is locally constant, for
`a ≠ 0`**: with the data of `Stacks.EtaleCohomology.LaumonFourierLineAwayFibreVanishing`,
`R¹g'_!(K₀|_{U'})` is locally constant of finite type. -/
public def LaumonFourierLineAwayFirstLocallyConstant : Prop :=
  ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (a : k'), a ≠ 0 →
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
    IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV') →
    haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
      inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} ℤ_[ℓ] V'.1.smallEtaleTopology
      ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' 1).obj
        ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)).obj
          (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
            (laumonFourierFamilySheaf k' B hS b
              (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _
                hσ₁).toLAdicSheaf)) 0)))

end Family

/-- **Laumon's local theory away from `a = 0`, on the fibres and in degree one**: under the
hypotheses of `Stacks.EtaleCohomology.LaumonFourierLineLisseInput` there is `N` such that for
`n > N` prime to `p` both `Stacks.EtaleCohomology.LaumonFourierLineAwayFibreVanishing` and
`Stacks.EtaleCohomology.LaumonFourierLineAwayFirstLocallyConstant` hold. -/
public def LaumonFourierLineAwayFibreInput : Prop :=
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
      LaumonFourierLineAwayFibreVanishing B U ℓ k e x E b σ ψ n ∧
        LaumonFourierLineAwayFirstLocallyConstant B U ℓ k e x E b σ ψ n

/-- An additive functor sends an object killed by `m` to an object killed by `m`. -/
private theorem nsmul_id_obj_eq_zero {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {X : C} {m : ℕ} (h : m • 𝟙 X = 0) :
    m • 𝟙 (F.obj X) = 0 := by
  rw [← F.map_id, ← F.map_nsmul, h, F.map_zero]

/-- **The level zero away from `a = 0`, from the fibres and the first direct image**: the
`R^q g'_!(K₀|_{U'})`, `q ≠ 1`, vanish by proper base change from the vanishing on the geometric
fibres (`Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_geometricFibres`, `K₀` being
killed by `ℓ`), and `R¹g'_!(K₀|_{U'})` is locally constant by hypothesis. -/
public theorem laumonFourierLineAwayLevelZeroInput_of_fibre
    (H : LaumonFourierLineAwayFibreInput.{u}) : LaumonFourierLineAwayLevelZeroInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ hef j kbar _ _ _ _ p q _ _ hcard hℓp x E _ _ _
    d b m σ hσ K _ _ _ hirr hstab hζ ι' β hV hpure ψ hψ
  obtain ⟨N, hN⟩ := H B U ℓ k f e hef j kbar p q hcard hℓp x E b σ hσ K hirr hstab hζ ι' β hpure
    ψ hψ
  refine ⟨N, fun n hn hpn => ?_⟩
  obtain ⟨hvan, hone⟩ := hN n hn hpn
  intro k' _ _ _ a ha hS hL z hz pz hσ₁ V' U' _ _ jV' jU g' _ _ _ jg' hopen hpb s
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  by_cases hs : s = 1
  · subst hs
    exact hone k' a ha hS hL z hz pz hσ₁ V' U' jV' jU g' jg' hopen hpb
  · let K₀ := towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
      (laumonFourierFamilySheaf k' B hS b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _ hσ₁).toLAdicSheaf)) 0
    let A := (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)).obj K₀
    have hm : 0 < ℓ ^ (0 + 1) := pow_pos (Fact.out : ℓ.Prime).pos _
    have hK₀ : ℓ ^ (0 + 1) • 𝟙 K₀ = 0 := LAdicSheaf.pow_nsmul_id_padicTower_obj B ℓ _ 0
    have hA : ℓ ^ (0 + 1) • 𝟙 A = 0 := nsmul_id_obj_eq_zero _ hK₀
    let S := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} ℤ_[ℓ] U'.1) 0
    have hSA : ℓ ^ (0 + 1) • 𝟙 (S.obj A) = 0 := nsmul_id_obj_eq_zero S hA
    refine ObjectProperty.prop_of_isZero
      (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
        V'.1.smallEtaleTopology ℤ_[ℓ]) ?_
    refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ s).mapIso
      ((derivedLowerShriek.{u, 0} (B.inclusion.map g') jg' ℤ_[ℓ]).mapIso
        ((StacksDraft.DerivedSectionsComparison.singlePlusQIso
          (EtaleModules.{u, 0} ℤ_[ℓ] U'.1)).app A)))
    exact isZero_homology_derivedLowerShriek_of_geometricFibres ℤ_[ℓ] (B.inclusion.map g') jg'
      (S.obj A) _ hm hSA s (fun y => hvan k' a ha hS hL z hz pz hσ₁ V' U' jV' jU g' jg' hopen hpb
        y s hs)

/-- **The lisse transform away from `a = 0`, from the fibres and the first direct image**:
`Stacks.EtaleCohomology.LaumonFourierLineAwayFibreInput` implies
`Stacks.EtaleCohomology.LaumonFourierLineLisseAwayInput`. -/
public theorem laumonFourierLineLisseAwayInput_of_fibre
    (H : LaumonFourierLineAwayFibreInput.{u}) : LaumonFourierLineLisseAwayInput.{u} :=
  laumonFourierLineLisseAwayInput_of_levelZero (laumonFourierLineAwayLevelZeroInput_of_fibre H)

end Stacks.EtaleCohomology

end
