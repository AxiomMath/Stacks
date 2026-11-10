module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicExcisionWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointwiseMixedInverseImage
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.FiniteReducedEtale

/-!
# Weights of `Hⁱ_c` along a surjective closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes of finite type over a finite field which is
surjective, for instance `X_red ⟶ X`.  The weights of the geometric Frobenius on
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` are bounded by those on `Hⁱ_c(Z_k̄, F|_Z ⊗ ℚ_ℓ)`: this is the excision
sequence for the decomposition `X = ∅ ⊔ Z`, whose open part vanishes since every sheaf on the
small étale site of the empty scheme is zero.  In the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 3.3) to curves this
replaces a scheme by its reduction, and a finite scheme over `k` by a finite étale one.

## Main results

All names below are in the namespace `Stacks.EtaleCohomology`.

* `isZero_etaleModulesUniv_of_isEmpty`: every sheaf of modules on the small étale site of an
  empty scheme is zero.
* `isZero_compactSupportSheafCohomology_obj`: `Hⁱ_c` of a zero sheaf.
* `isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_surjective`
  (in the namespace `LAdicSheaf`): weights on `X` from weights on a surjective closed subscheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u r

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

/-- **Every sheaf of modules on the small étale site of an empty scheme is zero**: every object of
the site is empty, hence covered by the empty family, and a sheaf takes a terminal value on an
object covered by the empty sieve. The coefficient ring `Λ : Type r` lives in any universe; the
case `Λ : Type` is `Stacks.EtaleCohomology.isZero_etaleModules_of_isEmpty`. -/
theorem isZero_etaleModulesUniv_of_isEmpty (Λ : Type r) [Ring Λ] (U : Scheme.{u}) [IsEmpty U]
    (G : EtaleModules.{u, r} Λ U) : IsZero G := by
  have hbot : ∀ V : U.Etale, ⊥ ∈ U.smallEtaleTopology V := fun V => by
    have : IsEmpty V.left := ⟨fun v => ‹IsEmpty U›.elim (V.hom.base v)⟩
    have h := (Scheme.ofArrows_mem_smallEtaleTopology_iff (W := V)
      (Z := fun e : PEmpty.{1} => V) (fun e => e.elim)).2 (Set.eq_univ_of_forall isEmptyElim)
    refine (U.smallEtaleTopology).superset_covering (fun Y g hg => ?_) h
    obtain ⟨_, _, _, ⟨e⟩, _⟩ := hg
    exact e.elim
  refine IsTerminal.isZero (IsTerminal.isTerminalOfObj (sheafToPresheaf _ _) G ?_)
  exact Functor.isTerminal fun V => Sheaf.isTerminalOfBotCover G V.unop (hbot V.unop)

/-- **`Hⁱ_c(X_k̄, -)` vanishes on a zero sheaf.** -/
theorem isZero_compactSupportSheafCohomology_obj (Λ : Type) [Ring Λ] {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
    (kbar : Type u) [Field kbar] [Algebra k kbar] (i : ℤ) {G : EtaleModules.{u, 0} Λ X}
    (hG : IsZero G) : IsZero ((compactSupportSheafCohomology Λ f j kbar i).obj G) := by
  have hC : IsZero ((HomologicalComplex.single (EtaleModules.{u, 0} Λ X)
      (ComplexShape.up ℤ) 0).obj G) :=
    (HomologicalComplex.single _ _ 0).map_isZero hG
  have h3 : IsZero ((sheafSingleComplex Λ).obj G) :=
    IsZero.of_full_of_faithful_of_isZero (CochainComplex.Plus.ι _) _ hC
  have h4 := (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map_isZero h3
  exact (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map_isZero h4

/-- The rational limit of a tower of `ℤ_ℓ`-modules which are all zero is zero. -/
private theorem isZero_rationalLim_of_forall_isZero {ℓ : ℕ} [Fact ℓ.Prime]
    (A : ℕᵒᵖ ⥤ ModuleCat.{u + 1} ℤ_[ℓ]) (h : ∀ n, IsZero (A.obj n)) :
    IsZero ((rationalLim.{u + 1} (ℓ := ℓ)).obj A) :=
  (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map_isZero
    ((IsZero.iff_id_eq_zero _).2 (limit.hom_ext fun n => (h n).eq_of_tgt _ _))

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
  {X : B.Scheme} [IsNoetherian X.1]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **On an empty scheme the weight bound holds vacuously**: every level of the tower lives on the
small étale site of the empty scheme, hence is zero, and so is `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`. -/
theorem
    LAdicSheaf.isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_isEmpty
    [IsEmpty X.1] (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ} :
    IsCharpolyNormMixedOfWeightLE q' ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
        i).hom := by
  have h : ∀ n : ℕᵒᵖ, IsZero
      ((LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i).obj n) :=
    fun n => (isZero_compactSupportSheafCohomology_obj ℤ_[ℓ] f j kbar i
      (isZero_etaleModulesUniv_of_isEmpty ℤ_[ℓ] X.1 _)).of_iso
      ((LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i).app n).symm
  have : Subsingleton
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
    ModuleCat.isZero_iff_subsingleton.1 (isZero_rationalLim_of_forall_isZero _ h)
  exact isCharpolyNormMixedOfWeightLE_of_subsingleton _

/-- A closed immersion followed by a morphism locally of finite type is locally of finite type;
stated directly since instance search for it times out here. -/
local instance (priority := high) locallyOfFiniteType_comp_surjectiveClosedImmersionWeights
    {S₁ S₂ S₃ : Scheme.{u}} (g : S₁ ⟶ S₂) (h : S₂ ⟶ S₃) [IsClosedImmersion g]
    [LocallyOfFiniteType h] : LocallyOfFiniteType (g ≫ h) :=
  have hg : LocallyOfFiniteType g := ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType g).mp
    ((IsClosedImmersion.iff_isFinite_and_mono g).mp ‹_›).1).2
  @locallyOfFiniteType_comp _ _ _ g h hg ‹_›

namespace LAdicSheaf

omit [LocallyOfFiniteType f] [IsSeparated f] in
/-- **Weights of `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` from a surjective closed subscheme.**  If `i : Z ⟶ X` is a
surjective closed immersion, compactified by the compactification induced by `j`, and the complex
roots, read along `ι`, of the characteristic polynomial of the geometric Frobenius on
`Hⁱ_c(Z_k̄, F|_Z ⊗ ℚ_ℓ)` have absolute values `q' ^ (w / 2)` with `w ≤ b`, so do those on
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`: in the excision sequence for `X = ∅ ⊔ Z` the open part vanishes. -/
theorem isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_surjective
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ) {Z : B.Scheme} [IsNoetherian Z.1] (iZ : Z ⟶ X)
    [IsClosedImmersion (B.inclusion.map iZ)]
    (hsurj : Function.Surjective (B.inclusion.map iZ).base)
    [hX : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    [hZ : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Z ℓ (B.inclusion.map iZ ≫ f)
        (j.restrictClosed (B.inclusion.map iZ)) kbar (LAdicSheaf.inverseImage iZ F) i)]
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ}
    (hFZ : IsCharpolyNormMixedOfWeightLE q' ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B Z ℓ (B.inclusion.map iZ ≫ f)
        (j.restrictClosed (B.inclusion.map iZ)) kbar p q hcard
        (LAdicSheaf.inverseImage iZ F) i).hom) :
    IsCharpolyNormMixedOfWeightLE q' ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
        i).hom := by
  set iZ' := B.inclusion.map iZ
  set T := LAdicSheaf.padicTower B X ℓ F
  let jU : (∅ : Scheme.{u}) ⟶ X.1 := Scheme.emptyTo X.1
  have hij : Set.range jU.base = (Set.range iZ'.base)ᶜ := by
    rw [hsurj.range_eq, Set.compl_univ]
    exact Set.range_eq_empty _
  -- the open part of the tower has vanishing compactly supported cohomology
  have hzero : ∀ n, IsZero ((compactSupportSheafCohomology ℤ_[ℓ] f j kbar i).obj
      ((etaleModuleOpenPart ℤ_[ℓ] jU).obj (T.obj n))) := fun n => by
    have h1 : IsZero ((etaleModuleRestriction.{u, 0} ℤ_[ℓ] jU).obj (T.obj n)) :=
      isZero_etaleModulesUniv_of_isEmpty ℤ_[ℓ] (∅ : Scheme.{u}) _
    have h2 : IsZero ((etaleModuleOpenPart ℤ_[ℓ] jU).obj (T.obj n)) :=
      (etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ] jU).map_isZero h1
    exact isZero_compactSupportSheafCohomology_obj ℤ_[ℓ] f j kbar i h2
  have hsub : Subsingleton ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      ((T ⋙ etaleModuleOpenPart ℤ_[ℓ] jU) ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) :=
    ModuleCat.isZero_iff_subsingleton.1 (isZero_rationalLim_of_forall_isZero _ hzero)
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      ((T ⋙ etaleModuleOpenPart ℤ_[ℓ] jU) ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) :=
    Module.Finite.of_finite
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i)) := hX
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B Z ℓ (iZ' ≫ f)
        (j.restrictClosed iZ') kbar (LAdicSheaf.inverseImage iZ F) i)) := hZ
  have hXT : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (T ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1}
      (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i).symm
  have hZT : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B Z ℓ (LAdicSheaf.inverseImage iZ F) ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (iZ' ≫ f) (j.restrictClosed iZ') kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1}
      (LAdicSheaf.padicTowerCohomologyIso B Z ℓ (iZ' ≫ f) (j.restrictClosed iZ') kbar
        (LAdicSheaf.inverseImage iZ F) i).symm
  -- the closed part of the tower of `X`, read on `Z`
  let eZ : T ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ] iZ' ≅
      LAdicSheaf.padicTower B Z ℓ (LAdicSheaf.inverseImage iZ F) :=
    LAdicSheaf.padicTowerInverseImageIso B ℓ iZ F
  let EZ := towerClosedPartCohomologyIso f j kbar iZ' T i ≪≫ Functor.isoWhiskerRight eZ
    (compactSupportSheafCohomology ℤ_[ℓ] (iZ' ≫ f) (j.restrictClosed iZ') kbar i)
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      ((T ⋙ etaleModuleClosedPart ℤ_[ℓ] iZ') ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1} EZ.symm (hA := hZT)
  rw [LAdicSheaf.isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff]
    at hFZ ⊢
  refine isCharpolyNormMixedOfWeightLE_rationalLim_of_openClosed f j kbar p q hcard iZ' jU hij T
    i (fun n => @Finite.of_subsingleton _ (ModuleCat.isZero_iff_subsingleton.1 (hzero n)))
    (isCharpolyNormMixedOfWeightLE_of_subsingleton _) ?_
  refine (isCharpolyNormMixedOfWeightLE_rationalLimMap_iff_of_iso.{u + 1} EZ _ _ ?_
    (hA' := hZT)).2 hFZ
  rw [Iso.trans_hom, ← Category.assoc,
    towerClosedPartCohomologyIso_hom_frobenius f j kbar p q hcard iZ' T i, Category.assoc,
    Category.assoc]
  congr 1
  refine NatTrans.ext (funext fun n => ?_)
  exact ((compactSupportSheafFrobenius ℤ_[ℓ] (iZ' ≫ f) (j.restrictClosed iZ') kbar p q hcard
    i).naturality (eZ.hom.app n)).symm

omit [IsSeparated f] in
/-- **Weil II in dimension zero, for any finite scheme.**  Let `X` be finite over `k` and `F` an
ℓ-adic sheaf on `X` pointwise `ι`-mixed of weights `≤ w`.  For a reduced surjective closed
subscheme `i : Z ⟶ X` (for instance `X_red`), `Z` is finite étale over the perfect field `k`, the
restriction `F|_Z` is pointwise `ι`-mixed of weights `≤ w`, and so the weights of `Hⁱ_c(X_k̄, F)`,
bounded by those of `Hⁱ_c(Z_k̄, F|_Z)`, are `≤ w + i`. -/
theorem isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_isFinite
    [IsAlgClosed kbar] [CharP kbar p] [IsFinite f] (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (ι : ℚ_[ℓ] →+* ℂ) (w : ℤ) (hF : LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f F (p ^ q) ι w)
    (i : ℤ) {Z : B.Scheme} [IsNoetherian Z.1] (iZ : Z ⟶ X)
    [IsClosedImmersion (B.inclusion.map iZ)] [IsReduced Z.1]
    (hsurj : Function.Surjective (B.inclusion.map iZ).base)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Z ℓ (B.inclusion.map iZ ≫ f)
        (j.restrictClosed (B.inclusion.map iZ)) kbar (LAdicSheaf.inverseImage iZ F) i)] :
    IsCharpolyNormMixedOfWeightLE (p ^ q) ι (w + i)
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
        i).hom := by
  have : PerfectField k := PerfectField.ofFinite
  have : IsFinite (B.inclusion.map iZ ≫ f) := inferInstance
  have : IsReduced (B.inclusion.obj Z) := ‹IsReduced Z.1›
  have : Etale (B.inclusion.map iZ ≫ f) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.etale_of_isFinite_of_isReduced (k := k) _
  have hg : ∀ y : closedPoints Z.1, (B.inclusion.map iZ).base y.1 ∈ closedPoints X.1 :=
    fun y => by
      have h := (B.inclusion.map iZ).isClosedEmbedding.isClosedMap _ y.2
      rwa [Set.image_singleton] at h
  -- instance search for this times out (Lean v4.35.0): supply Mathlib's instance directly
  have : LocallyOfFiniteType (B.inclusion.map iZ) :=
    AlgebraicGeometry.instLocallyOfFiniteTypeOfIsClosedImmersion _
  refine isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_surjective
    B ℓ f j kbar p q hcard F i iZ hsurj ?_
  exact
    LAdicSheaf.isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_etale
      B Z ℓ (B.inclusion.map iZ ≫ f) (j.restrictClosed (B.inclusion.map iZ)) kbar p q hcard
      (LAdicSheaf.inverseImage iZ F) ι w
      (LAdicSheaf.IsPointwiseMixedOfWeightLE.inverseImage X ℓ iZ f hF hg) i

end LAdicSheaf

end Stacks.EtaleCohomology
