module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.FirstCohomologyLocallyFree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.Fibre

/-!
# The rank of the first cohomology of a proper flat family with constant functions on fibres

Let `f : X ⟶ Spec A` be proper, flat and locally of finite presentation, with a finite affine
cover with affine intersections, and assume that at every prime `p` the fibre `X_p` has only
constant functions and no cohomology of its structure sheaf above degree one. Then `H¹` of the
Čech model `D` of `𝒪_X` is a finite locally free `A`-module
(`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.isFiniteLocallyFree_homology_one`). This file
computes its rank: near `p` it is free of rank `dim_{κ(p)} H¹(D ⊗_A κ(p))`, and that dimension is
the genus of `X_p`. Hence if every fibre has genus `r`, then `H¹(D)` is finite locally free of
rank `r`.

The argument is the one of `exists_away_free_homology_one`, keeping track of the rank: near `p`
the mapping cone `M` of the unit `A ⟶ D` is a free module of rank `dim_{κ(p)} H¹(M ⊗^L κ(p))`
placed in degree one ([Stacks, Tag 0BCD]); `M` is a complex of flat modules, so
`M ⊗^L κ(p) = M ⊗ κ(p)`, and the long exact sequence of the cone identifies `H¹(M ⊗ κ(p))` with
`H¹(D ⊗ κ(p))`, which is `H¹(X_p, 𝒪)` by the base change of the Čech model ([Stacks, Tag 01XL]).

## Main results

All in the namespace `Stacks.AlgebraicGeometry.ProperFlatGlobalSections`.

* `nonempty_homology_one_iso_homology_one_mappingCone`: `H¹` of a complex agrees with `H¹` of the
  cone of a map into it from the ring placed in degree zero, after any base change.
* `finrank_homology_one_extendScalarsCx_eq_genus`: `dim_K H¹(D ⊗_A K)` is the genus of `X_K`.
* `exists_away_basis_homology_one`: near every prime `p`, `H¹(D)` is free of rank
  `dim_{κ(p)} H¹(D ⊗_A κ(p))`.
* `isFiniteLocallyFreeOfRank_homology_one`: if every fibre has genus `r`, `H¹(D)` is finite
  locally free of rank `r`.

## References

* [Stacks Project, Tag 0GKA](https://stacks.math.columbia.edu/tag/0GKA)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open StacksDraft.Perfect
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

variable {A : Type u} [CommRing A]

/-- **`H¹` of a complex is `H¹` of the cone of a map from the ring in degree zero.** For a map
`u : A ⟶ D` from `A` placed in degree zero and any ring map `φ : A →+* B`, the second map of the
cone triangle identifies `H¹(D ⊗_A B)` with `H¹` of the cone of `u ⊗_A B`, since `B` placed in
degree zero has neither `H¹` nor `H²`. -/
theorem nonempty_homology_one_iso_homology_one_mappingCone {B : Type u} [CommRing B]
    (φ : A →+* B) {D : CochainComplex (ModuleCat.{u} A) ℤ} (u : baseUnitComplex A ⟶ D) :
    Nonempty ((extendScalarsCx φ D).homology 1 ≅
      (CochainComplex.mappingCone (extendScalarsCxMap u φ)).homology 1) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} B)
  let T := DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle (extendScalarsCxMap u φ))
  have hT : T ∈ distTriang _ :=
    DerivedCategory.mappingCone_triangle_distinguished (extendScalarsCxMap u φ)
  have hmono : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 1).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT 1]
    exact ((isZero_homology_extendScalarsCx_baseUnitComplex φ 1 (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors _ 1).app _)).eq_of_src _ _
  have hepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 1).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT 1 2 (by omega)]
    exact ((isZero_homology_extendScalarsCx_baseUnitComplex φ 2 (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors _ 2).app _)).eq_of_tgt _ _
  have hiso : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 1).map T.mor₂) :=
    isIso_of_mono_of_epi _
  exact ⟨((DerivedCategory.homologyFunctorFactors _ 1).app _).symm ≪≫
    @asIso _ _ _ _ ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 1).map T.mor₂) hiso ≪≫
    (DerivedCategory.homologyFunctorFactors _ 1).app _⟩

/-- **`H¹` of a base-changed cone is `H¹` of the base-changed complex.** For a map
`u : A ⟶ D` from `A` placed in degree zero and any ring map `φ : A →+* B`, `H¹` of the cone of `u`
base changed to `B` is `H¹` of `D` base changed to `B`. -/
theorem nonempty_homology_one_extendScalarsCx_mappingCone_iso {B : Type u} [CommRing B]
    (φ : A →+* B) {D : CochainComplex (ModuleCat.{u} A) ℤ} (u : baseUnitComplex A ⟶ D) :
    Nonempty ((extendScalarsCx φ (CochainComplex.mappingCone u)).homology 1 ≅
      (extendScalarsCx φ D).homology 1) :=
  ⟨(HomologicalComplex.homologyFunctor _ _ 1).mapIso (extendScalarsCxMappingConeIso u φ) ≪≫
    (nonempty_homology_one_iso_homology_one_mappingCone φ u).some.symm⟩

/-- **A free `Hⁿ` after localizing termwise gives a basis of the localized `Hⁿ`.** If `Hⁿ` of a
complex `D` of `A`-modules base changed termwise to `A_a` is `A_aʳ`, then the localization at `a`
of `Hⁿ(D)` has a basis indexed by `Fin r`. -/
theorem nonempty_basis_localizedModule_homology_of_iso (D : CochainComplex (ModuleCat.{u} A) ℤ)
    (a : A) (n : ℤ) {r : ℕ}
    (e : (extendScalarsCx (algebraMap A (Localization.Away a)) D).homology n ≅
      ModuleCat.of (Localization.Away a) (ULift.{u} (Fin r → Localization.Away a))) :
    Nonempty (Module.Basis (Fin r) (Localization.Away a)
      (LocalizedModule (Submonoid.powers a) (D.homology n))) := by
  set Aa := Localization.Away a
  set φa := algebraMap A Aa
  have hφa : φa.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φa) :=
    StacksDraft.PseudoCoherence.preservesFiniteLimits_extendScalars_of_flat φa hφa
  have : (ModuleCat.extendScalars.{u, u, u} φa).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  let e₁ : (extendScalarsCx φa D).homology n ≅
      (ModuleCat.extendScalars.{u, u, u} φa).obj (D.homology n) :=
    ShortComplex.mapHomologyIso (D.sc n) (ModuleCat.extendScalars.{u, u, u} φa)
  let e₂ := (extendScalars_iso_localizedModuleFunctor.{u, u} (Submonoid.powers a)).app
    (D.homology n)
  let E : (Fin r → Aa) ≃ₗ[Aa] LocalizedModule (Submonoid.powers a) (D.homology n) :=
    ULift.moduleEquiv.symm.trans
      ((e₂.symm ≪≫ e₁.symm ≪≫ e).toLinearEquiv.symm.trans
      (Shrink.linearEquiv.{u} (Localization (Submonoid.powers a))
        (LocalizedModule (Submonoid.powers a) (D.homology n))))
  exact ⟨(Pi.basisFun Aa (Fin r)).map E⟩

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **`H¹` of the Čech model base changed to a field is `H¹` of the base change.** For a base
change `X_K ⟶ Spec K` of `f` along `Spec K ⟶ Spec A`, `K` a field, the dimension over `K` of `H¹`
of the Čech model of `𝒪_X` base changed termwise to `K` is the genus of `X_K`. -/
theorem finrank_homology_one_extendScalarsCx_eq_genus [IsSeparated f] {K : Type u} [Field K]
    (φ : A →+* K) {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of K)} {g : X' ⟶ X}
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {I : Type u} [Finite I] [LinearOrder I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    Module.finrank K ((extendScalarsCx φ
      (baseAlternatingCechComplex f U hU (SheafOfModules.unit X.ringCatSheaf))).homology 1) =
      genus f' := by
  set O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have : O.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  have : ((Scheme.Modules.pullback g).obj O).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g O
  have : IsSeparated f' := isSeparated_of_isPullback φ hsq
  let e1 := (HomologicalComplex.homologyFunctor _ _ (1 : ℤ)).mapIso
    (baseAlternatingCechComplexBaseChangeIso φ hsq O U hU hUaff)
  let e2 := homologyBaseAlternatingCechComplexIso f' (fun i => g ⁻¹ᵁ U i)
    (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj O)
    (iInf_preimage_isAffineOpen φ hsq U hUaff) 1
  let e3 := (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f').hom).mapIso
    (((AlgebraicGeometry.moduleGlobalSections X').rightDerived 1).mapIso
      (Scheme.Modules.pullbackUnitIso g))
  let e4 := eqToIso (Stacks.TwoAffineCech.cohomologyOverField_eq f'
    (SheafOfModules.unit X'.ringCatSheaf) 1).symm ≪≫
    (structureSheafCohomologyIsoCohomologyOverField K f' 1).symm
  rw [genus_eq_finrank_structureSheafCohomology]
  exact LinearEquiv.finrank_eq (e1 ≪≫ e2 ≪≫ e3 ≪≫ e4).toLinearEquiv

/-- **The fibre of the cone of the unit is concentrated in degree one.** Let `f : X ⟶ Spec A` be
separated with a finite affine cover `U`, and let `p` be a prime of `A` whose fibre `X_p` has only
constant functions and no cohomology of `𝒪` in degrees `≥ 2`. Then the cone of the unit
`A ⟶ D` on the Čech model `D` of `𝒪_X`, base changed termwise to `κ(p)`, has no homology outside
degree one. -/
theorem isZero_homology_extendScalarsCx_mappingCone_unitModelMap [IsSeparated f]
    {I : Type u} [Finite I] [LinearOrder I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (p : Ideal A) [p.IsPrime] {Xp : Scheme.{u}} {fp : Xp ⟶ Spec (.of p.ResidueField)}
    {gp : Xp ⟶ X}
    (hsq : IsPullback gp fp f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (hfib : Function.Bijective (Stacks.Cech.globalRingHom fp).hom)
    (hvan : ∀ j : ℕ, 2 ≤ j → Subsingleton (((moduleGlobalSections Xp).rightDerived j).obj
      ((Scheme.Modules.pullback gp).obj (SheafOfModules.unit X.ringCatSheaf))))
    {j : ℤ} (hj : j ≠ 1) :
    IsZero ((extendScalarsCx (algebraMap A p.ResidueField)
      (CochainComplex.mappingCone (unitModelMap f U hU hU.le))).homology j) := by
  set O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have : O.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  set u := unitModelMap f U hU hU.le
  set ψ := algebraMap A p.ResidueField
  have := isIso_homologyMap_zero_unitModelMap_fibre f U hU hUaff p hsq hfib
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ _ j).mapIso
    (extendScalarsCxMappingConeIso u ψ))
  refine isZero_homology_mappingCone_of_epi_of_mono _ j (j + 1) rfl ?_ ?_
  · by_cases hj0 : j = 0
    · subst hj0
      infer_instance
    rcases lt_or_gt_of_ne hj0 with hneg | hpos
    · exact (ShortComplex.isZero_homology_of_isZero_X₂ _
        ((extendScalarsCx ψ (baseAlternatingCechComplex f U hU O)).isZero_of_isStrictlyGE 0 j
          hneg)).epi _
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = m := ⟨j.toNat, (Int.toNat_of_nonneg hpos.le).symm⟩
      exact (isZero_homology_extendScalarsCx_of_subsingleton f ψ hsq O U hU hUaff m
        (hvan m (by omega))).epi _
  · by_cases hj0 : j + 1 = 0
    · rw [hj0]
      infer_instance
    · exact (isZero_homology_extendScalarsCx_baseUnitComplex ψ (j + 1) hj0).mono _

/-- **Near every prime, `H¹` of the Čech model is free of the rank of the fibre.** Let
`f : X ⟶ Spec A` be proper, flat and locally of finite presentation, with a finite affine cover
`U` with affine intersections, and let `p` be a prime of `A` whose fibre `X_p` has only constant
functions and no cohomology of `𝒪` in degrees `≥ 2`. Then there is `a ∉ p` such that the
localization at `a` of `H¹` of the Čech model `D` of `𝒪_X` has a basis indexed by `Fin n`, where
`n = dim_{κ(p)} H¹(D ⊗_A κ(p))`. -/
theorem exists_away_basis_homology_one [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    {I : Type u} [Finite I] [LinearOrder I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (p : Ideal A) [p.IsPrime] {Xp : Scheme.{u}} {fp : Xp ⟶ Spec (.of p.ResidueField)}
    {gp : Xp ⟶ X}
    (hsq : IsPullback gp fp f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (hfib : Function.Bijective (Stacks.Cech.globalRingHom fp).hom)
    (hvan : ∀ j : ℕ, 2 ≤ j → Subsingleton (((moduleGlobalSections Xp).rightDerived j).obj
      ((Scheme.Modules.pullback gp).obj (SheafOfModules.unit X.ringCatSheaf)))) :
    ∃ a : A, a ∉ p ∧
      Nonempty (Module.Basis (Fin (Module.finrank p.ResidueField
          ((extendScalarsCx (algebraMap A p.ResidueField)
            (baseAlternatingCechComplex f U hU (SheafOfModules.unit X.ringCatSheaf))).homology 1)))
        (Localization.Away a) (LocalizedModule (Submonoid.powers a)
          ((baseAlternatingCechComplex f U hU
            (SheafOfModules.unit X.ringCatSheaf)).homology 1))) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  set O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have : O.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  have hflat : IsFlatOver f.toLRSHom.toShHom O := fun x =>
    (AlgebraicGeometry.MorphismOfGerms.flat_stalkMap_iff_isFlatOverAt_unit f x).1
      (Flat.stalkMap f x)
  set D := baseAlternatingCechComplex f U hU O
  have hDflat : ∀ i, Module.Flat A (D.X i) :=
    flat_baseAlternatingCechComplex_X f U hU O hUaff hflat
  have : (baseUnitComplex A).IsStrictlyLE (Fintype.card I : ℤ) :=
    CochainComplex.isStrictlyLE_of_le _ 0 _ (by omega)
  set u := unitModelMap f U hU hU.le
  set M := CochainComplex.mappingCone u
  have : D.IsStrictlyGE 0 := isStrictlyGE_baseAlternatingCechComplex f U hU O
  have : D.IsStrictlyLE (Fintype.card I : ℤ) := isStrictlyLE_baseAlternatingCechComplex f U hU O
  have := isStrictlyGE_mappingCone u 0
  have := isStrictlyLE_mappingCone u (Fintype.card I : ℤ)
  have := flat_mappingCone_X u
  have hMperf : IsPerfect (DerivedCategory.Q.obj M) :=
    isPerfect_mappingCone u (isPerfect_baseUnitComplex A) <| isPerfect_of_iso
      (alternatingCechIsoDerivedGlobalSectionsOverBase f U hU O haff)
      (isPerfect_derivedGlobalSectionsOverBase_of_isProper f O hflat)
  set ψ := algebraMap A p.ResidueField
  have hvanish : ∀ j : ℤ, j ≠ 1 →
      Module.finrank p.ResidueField (derivedFibreHomology.{u, u} p
        (DerivedCategory.Q.obj M) j) = 0 := by
    intro j hj
    obtain ⟨e⟩ := nonempty_homology_totalDerived_iso_of_flat ψ M (Fintype.card I : ℤ) j
    have := ModuleCat.subsingleton_of_isZero
      ((isZero_homology_extendScalarsCx_mappingCone_unitModelMap f U hU hUaff p hsq hfib hvan
        hj).of_iso e)
    exact Module.finrank_zero_of_subsingleton
  obtain ⟨a, ha, ⟨e⟩⟩ :=
    exists_away_iso_singleFunctor_free_of_fibre_concentrated.{u, u} p
      (DerivedCategory.Q.obj M) hMperf 1 hvanish
  refine ⟨a, ha, ?_⟩
  let := HasDerivedCategory.standard (ModuleCat.{u} (Localization.Away a))
  rw [← LinearEquiv.finrank_eq
    ((nonempty_homology_totalDerived_iso_of_flat ψ M (Fintype.card I : ℤ) 1).some ≪≫
      (nonempty_homology_one_extendScalarsCx_mappingCone_iso ψ u).some).toLinearEquiv]
  exact nonempty_basis_localizedModule_homology_of_iso D a 1
    ((nonempty_homology_one_extendScalarsCx_mappingCone_iso _ u).some.symm ≪≫
      (nonempty_homology_totalDerived_iso_of_flat _ M (Fintype.card I : ℤ) 1).some.symm ≪≫
      (DerivedCategory.homologyFunctor _ 1).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u} (Localization.Away a)) 1).app _)

/-- **`H¹` of the Čech model has the rank of the fibres.** Let `f : X ⟶ Spec A` be proper, flat
and locally of finite presentation, with a finite affine cover `U` with affine intersections,
and assume that at every prime `p` of `A` the fibre `X_p` has only constant functions, no
cohomology of `𝒪` in degrees `≥ 2`, and genus `r`. Then `H¹` of the Čech model of `𝒪_X` is a
finite locally free `A`-module of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_homology_one [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f]
    {I : Type u} [Finite I] [LinearOrder I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (hfib : ∀ (p : Ideal A) [p.IsPrime], Function.Bijective (Stacks.Cech.globalRingHom
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))).hom)
    (hvan : ∀ (p : Ideal A) [p.IsPrime] (j : ℕ), 2 ≤ j → Subsingleton
      (((moduleGlobalSections
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))).rightDerived
          j).obj ((Scheme.Modules.pullback
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))).obj
              (SheafOfModules.unit X.ringCatSheaf))))
    (r : ℕ) (hr : ∀ (p : Ideal A) [p.IsPrime],
      genus (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))) = r) :
    Module.IsFiniteLocallyFreeOfRank A
      ((baseAlternatingCechComplex f U hU (SheafOfModules.unit X.ringCatSheaf)).homology 1) r := by
  classical
  have hloc : ∀ m : {m : Ideal A // m.IsMaximal}, ∃ a : A, a ∉ m.1 ∧
      Nonempty (Module.Basis (Fin r) (Localization.Away a) (LocalizedModule (Submonoid.powers a)
        ((baseAlternatingCechComplex f U hU (SheafOfModules.unit X.ringCatSheaf)).homology 1))) :=
    fun m => by
      have := m.2.isPrime
      have hsq := IsPullback.of_hasPullback f
        (Spec.map (CommRingCat.ofHom (algebraMap A m.1.ResidueField)))
      obtain ⟨a, ha, hb⟩ := exists_away_basis_homology_one f U hU hUaff haff m.1 hsq
        (hfib m.1) (hvan m.1)
      rw [finrank_homology_one_extendScalarsCx_eq_genus f _ hsq U hU hUaff, hr m.1] at hb
      exact ⟨a, ha, hb⟩
  choose a ha hb using hloc
  refine ⟨{m : Ideal A // m.IsMaximal}, a, ?_, hb⟩
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  exact ha ⟨m, hm⟩ (hle (Ideal.subset_span ⟨⟨m, hm⟩, rfl⟩))

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
