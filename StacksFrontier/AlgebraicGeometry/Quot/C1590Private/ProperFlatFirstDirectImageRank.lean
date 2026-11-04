module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProperFlatFibreGenus
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedPushforwardAffineBaseHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.StructureSheafSplitting
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenUniversal
public import StacksFrontier.AlgebraicGeometry.Perfect.BottomRankBettiStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Perfect.BottomRankChart
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Descent.DescentLocusComparison0BF1

/-!
# `R¹f_*𝒪_X` of a proper flat family of curves with `H⁰ = κ` is locally free of rank the genus

Let `f : X ⟶ S` be a proper, flat morphism of schemes of finite presentation all of whose fibres
`X_s` have dimension at most one and `κ(s) = H⁰(X_s, 𝒪_{X_s})`. Then `R¹f_*𝒪_X` is finite locally
free, and near each point `s` its rank is the genus of `X_s`: this is the scheme case of parts (2)
and (3) of Stacks 0E1J, read on the rank.

The proof is the source's. Locally on `S`, `Rf_*𝒪_X = 𝒪_S ⊕ P` with `P` perfect of Tor amplitude in
`[1, ∞)` (Stacks 0E62, part (b)). The derived-fibre Betti numbers of `P` at a point `s` are those
of `Rf_*𝒪_X` in degrees `≥ 1`, which are `dim H^i(X_s, 𝒪)` by cohomology and base change (Stacks
0B91): the genus in degree one and zero in degrees `≥ 2` (Stacks 02UZ). So `P` is a finite locally
free module of rank the genus placed in degree one near `s` (Stacks 0BDK, from 0BCD), and
`R¹f_*𝒪_X = H¹(Rf_*𝒪_X) = H¹(P)`.

## Main results

* `AlgebraicGeometry.C1590Private.homologyDerivedPushforwardModuleIso`: `H^n(Rf_*ℱ) ≅ R^nf_*ℱ`.
* `AlgebraicGeometry.C1590Private.derivedFiberBetti_unit_of_isPullback_of_one_le`: the Betti
  numbers of `Rf_*𝒪_X` in positive degrees at a field-valued point whose fibre is a curve.
* `AlgebraicGeometry.C1590Private.exists_isFiniteLocallyFreeOfRank_restrict_rightDerived_one`:
  near the image of a field-valued point whose fibre is a curve, `R¹f_*𝒪_X` is finite locally
  free of rank the genus of that fibre.
* `AlgebraicGeometry.C1590Private.isFiniteLocallyFreeOfRank_rightDerived_one_of_forall_genus_eq`
  and `AlgebraicGeometry.C1590Private.genus_eq_of_isFiniteLocallyFreeOfRank_rightDerived_one`:
  `R¹f_*𝒪_X` is finite locally free of rank `r` exactly when the fibres have genus `r`.

## Implementation notes

The splitting of Stacks 0E62 (b) is stated in the standard model of the derived categories; this
file reads it in that model (`HasDerivedCategory.standard`, at default priority), with
`Scheme.Modules.instAbelian` raised locally so that the biproduct of the splitting is found.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E62](https://stacks.math.columbia.edu/tag/0E62)
* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry.C1590Private

open ProperFlatFibreEulerCharacteristic

attribute [local instance] HasDerivedCategory.standard

section Homology

variable {X S : Scheme.{u}} (f : X ⟶ S)

attribute [local instance] IsGrothendieckAbelian.enoughInjectives in
/-- **`H^n(Rf_*ℱ) ≅ R^nf_*ℱ`**: the cohomology sheaves of the derived direct image of a module
placed in degree zero are its classical higher direct images. -/
def homologyDerivedPushforwardModuleIso (F : X.Modules) (n : ℕ) :
    (DerivedCategory.homologyFunctor S.Modules n).obj (derivedPushforwardModule f F) ≅
      ((Scheme.Modules.pushforward f).rightDerived n).obj F :=
  have := SheafOfModules.isGrothendieckAbelianU.{u} (structureSheafRing X.toRingedSpace)
  (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (modulePushforward f.toLRSHom.toShHom) (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (exists_quasiIso_isKInjective X.toRingedSpace) n).app F

end Homology

section Betti

variable {Y : Scheme.{u}}

/-- The derived fibre of the structure sheaf placed in degree zero has no cohomology outside
degree zero. -/
theorem isZero_homology_derivedPullback_singleFunctor_unit (y : Y) (j : ℤ) (hj : j ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (Spec (Y.residueField y)).Modules j).obj
      ((derivedPullback (Y.fromSpecResidueField y).toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf)))) :=
  IsZero.of_iso (Scheme.Modules.isZero_homologyFunctor_singleFunctor_obj _ hj)
    ((DerivedCategory.homologyFunctor (Spec (Y.residueField y)).Modules j).mapIso
      (derivedPullbackSingleFlatIso (Y.fromSpecResidueField y).toLRSHom.toShHom _
        (AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFreeOfRank _ 1
          (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit Y)) 0))

/-- **The derived-fibre Betti numbers of the restriction to an open subscheme** are those of the
object at the image point. -/
theorem derivedFiberBetti_restrict {V : Scheme.{u}} (ι : V ⟶ Y) [IsOpenImmersion ι]
    (E : DerivedCategory Y.Modules) (hE : RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) E)
    (hEV : RingedSpace.IsPseudoCoherent (X := V.toRingedSpace)
      ((Scheme.Modules.restrictFunctor ι).mapDerivedCategory.obj E)) (j : ℤ) (v : V) :
    DerivedFibreBetti.derivedFiberBetti V
        ((Scheme.Modules.restrictFunctor ι).mapDerivedCategory.obj E) hEV j v =
      DerivedFibreBetti.derivedFiberBetti Y E hE j (ι.base v) := by
  have h := congrFun (DerivedFibreBetti.derivedFiberBetti_derivedPullback ι E hE j) v
  rw [Function.comp_apply] at h
  exact (congrFun (DerivedFibreBetti.derivedFiberBetti_congr V _ hEV
    ((Scheme.Modules.derivedPullbackIsoMapDerivedCategoryRestrict ι).app E) j) v).symm.trans h

/-- An additive functor preserving the biproduct `A ⊞ P` with `H A = 0` sends it to `H P`. -/
private def obj_biprod_iso_of_isZero {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D] (H : C ⥤ D) [H.Additive]
    (A P : C) [PreservesBinaryBiproduct A P H] (hz : IsZero (H.obj A)) :
    H.obj (A ⊞ P) ≅ H.obj P :=
  H.mapBiprod A P ≪≫ (isoZeroBiprod hz).symm

end Betti

section Hypothesis

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The hypothesis on the fibres: every point of `S` lies under a field-valued point at which the
fibre `Y = X ×_S Spec K` has `K = H⁰(Y, 𝒪_Y)`. -/
def HasFieldGlobalFunctionsFibres : Prop :=
  ∀ s : S, ∃ (K : Type u) (_ : Field K) (p : Spec (.of K) ⟶ S) (Y : Scheme.{u}) (a : Y ⟶ X)
    (g : Y ⟶ Spec (.of K)) (_ : IsPullback a g f p) (pt : Spec (.of K)),
      p.base pt = s ∧ Function.Bijective g.appTop

end Hypothesis

section Rank

attribute [local instance 5000] Scheme.Modules.instAbelian

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f] (hf : FinitePresentation f)

include hf

/-- The hypothesis on the fibres gives `κ(s) = H⁰(X_s, 𝒪_{X_s})` on the scheme-theoretic fibres. -/
theorem bijective_fiber_appTop_of_hasFieldGlobalFunctionsFibres
    (hΓ : HasFieldGlobalFunctionsFibres f) (s : S) :
    Function.Bijective (f.fiberToSpecResidueField s).appTop := by
  obtain ⟨K, _, p, Y, a, g, hsq, pt, hpt, hb⟩ := hΓ s
  obtain ⟨pt', hpt'⟩ : ∃ pt', (S.fromSpecResidueField s).base pt' = s :=
    ⟨IsLocalRing.closedPoint (S.residueField s), Scheme.fromSpecResidueField_apply _ _⟩
  have h₁ := bijective_appTop_iff_derivedFiberBetti_zero_eq_one f hf K p a g hsq pt
  have h₂ := bijective_appTop_iff_derivedFiberBetti_zero_eq_one f hf _ _ _ _
    (isPullback_fiberι_fiberToSpecResidueField f s) pt'
  rw [hpt] at h₁
  exact h₂.2 ((congrArg (DerivedFibreBetti.derivedFiberBetti S
    (derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf))
    (isPseudoCoherent_derivedPushforwardModule_unit f hf) 0) hpt').trans (h₁.1 hb))

/-- **The derived-fibre Betti numbers of `Rf_*𝒪_X` in positive degrees** at a field-valued point
whose fibre is a curve: the genus in degree one and zero above (Stacks 0B91 and 02UZ). -/
theorem derivedFiberBetti_unit_of_isPullback_of_one_le (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ S) {Y : Scheme.{u}} (a : Y ⟶ X) (g : Y ⟶ Spec (.of K))
    (hsq : IsPullback a g f p) (pt : Spec (.of K)) (hdim : topologicalKrullDim Y ≤ 1) (n : ℕ)
    (hn : 1 ≤ n) :
    DerivedFibreBetti.derivedFiberBetti S
        (derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf))
        (isPseudoCoherent_derivedPushforwardModule_unit f hf) n (p.base pt) =
      if n = 1 then genus g else 0 := by
  rw [derivedFiberBetti_eq_finrank_cohomologyOverField f hf K p a g hsq pt n]
  have hgp : IsProper g := MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  split_ifs with h1
  · subst h1
    exact ((structureSheafCohomologyIsoCohomologyOverField K g 1).toLinearEquiv.finrank_eq).symm
  · have hz := @isZero_cohomologyOverField_of_topologicalKrullDim_le _ _ _ g hgp
      (SheafOfModules.unit Y.ringCatSheaf) 1 n (by exact_mod_cast hdim) (by omega)
    have := ModuleCat.subsingleton_of_isZero hz
    exact Module.finrank_zero_of_subsingleton

/-- **`R¹f_*𝒪_X` is free of rank the genus near every point** (the scheme case of Stacks 0E1J,
parts (2) and (3), with the rank). Let `f` be proper, flat and of finite presentation, with
`K = H⁰` on the fibres. If the fibre `Y` at a field-valued point `p` has dimension at most one,
then the image of `p` has an open neighbourhood on which `R¹f_*𝒪_X` is finite locally free of rank
the genus of `Y`. -/
theorem exists_isFiniteLocallyFreeOfRank_restrict_rightDerived_one
    (hΓ : HasFieldGlobalFunctionsFibres f) (K : Type u) [Field K] (p : Spec (.of K) ⟶ S)
    {Y : Scheme.{u}} (a : Y ⟶ X) (g : Y ⟶ Spec (.of K)) (hsq : IsPullback a g f p)
    (pt : Spec (.of K)) (hdim : topologicalKrullDim Y ≤ 1) :
    ∃ (W : S.Opens) (_ : p.base pt ∈ W),
      Scheme.Modules.IsFiniteLocallyFreeOfRank ((((Scheme.Modules.pushforward f).rightDerived 1).obj
          (SheafOfModules.unit X.ringCatSheaf)).restrict W.ι) (genus g) := by
  have hfib : ∀ s : S, Function.Bijective ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
      (f.fiberToSpecResidueField s).appTop) := fun s =>
    (bijective_fiber_appTop_of_hasFieldGlobalFunctionsFibres f hf hΓ s).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (S.residueField s)).inv)
  obtain ⟨-, hsplit⟩ :=
    Stacks.AlgebraicGeometry.ProperFlatStructureSheafSplitting.properFlat_structureSheaf_splitting
      f hf hfib
  obtain ⟨V, ι, hι, P, ⟨v₀, hv₀⟩, hPperf, ⟨b, hPtor⟩, ⟨e⟩⟩ := hsplit (p.base pt)
  have := hι
  set E := derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf)
  have hE := isPseudoCoherent_derivedPushforwardModule_unit f hf
  set EV := (Scheme.Modules.restrictFunctor ι).mapDerivedCategory.obj E
  have hEV : RingedSpace.IsPseudoCoherent (X := V.toRingedSpace) EV :=
    RingedSpace.IsPseudoCoherent.of_iso.{u, u + 1}
      (DerivedFibreBetti.isPseudoCoherent_derivedPullback ι E hE)
      ((Scheme.Modules.derivedPullbackIsoMapDerivedCategoryRestrict ι).app E)
  have hPpc := DerivedFibreBetti.isPseudoCoherent_of_isPerfect P hPperf
  -- the Betti numbers of `P`
  have hkey : ∀ (v : V) (n : ℕ), 1 ≤ n →
      DerivedFibreBetti.derivedFiberBetti V P hPpc n v =
        DerivedFibreBetti.derivedFiberBetti V EV hEV n v := by
    intro v n hn
    rw [DerivedFibreBetti.derivedFiberBetti_congr V hEV
      (RingedSpace.IsPseudoCoherent.of_iso.{u, u + 1} hEV e) e]
    unfold DerivedFibreBetti.derivedFiberBetti
    have hz : IsZero ((DerivedCategory.homologyFunctor (Spec (V.residueField v)).Modules n).obj
        ((derivedPullback (V.fromSpecResidueField v).toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor V.Modules 0).obj V.unitModule))) :=
      isZero_homology_derivedPullback_singleFunctor_unit (Y := V) v n (by omega)
    let L : DerivedCategory V.Modules ⥤ DerivedCategory (Spec (V.residueField v)).Modules :=
      derivedPullback (V.fromSpecResidueField v).toLRSHom.toShHom
    let : L.CommShift ℤ := Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift
      (V.fromSpecResidueField v).toLRSHom.toShHom
    have : L.IsTriangulated :=
      Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated
        (V.fromSpecResidueField v).toLRSHom.toShHom
    let H := DerivedCategory.homologyFunctor (Spec (V.residueField v)).Modules n
    have : PreservesBinaryBiproduct ((DerivedCategory.singleFunctor V.Modules 0).obj V.unitModule)
        P L := preservesBinaryBiproduct_of_preservesBiproduct L _ _
    have : PreservesBinaryBiproduct
        (L.obj ((DerivedCategory.singleFunctor V.Modules 0).obj V.unitModule)) (L.obj P) H :=
      preservesBinaryBiproduct_of_preservesBiproduct H _ _
    let i := H.mapIso
        (L.mapBiprod ((DerivedCategory.singleFunctor V.Modules 0).obj V.unitModule) P) ≪≫
      obj_biprod_iso_of_isZero H _ _ hz
    exact ((moduleSpecΓFunctor (R := V.residueField v)).mapIso i).toLinearEquiv.finrank_eq.symm
  set g₀ := genus g
  have hβ : ∀ j : ℤ,
      DerivedFibreBetti.derivedFiberBetti V P hPpc j v₀ = if j = 1 then g₀ else 0 := by
    intro j
    rcases lt_or_ge j 1 with hj | hj
    · rw [ite_eq_right (by omega)]
      exact BottomRankStratum.derivedFiberBetti_eq_zero_of_lt P hPpc 1 b hPtor v₀ hj
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n := ⟨j.toNat, by omega⟩
      rw [hkey v₀ n (by omega), derivedFiberBetti_restrict ι E hE hEV, hv₀,
        derivedFiberBetti_unit_of_isPullback_of_one_le f hf K p a g hsq pt hdim n (by omega)]
      by_cases h1 : n = 1
      · subst h1
        simp [g₀]
      · rw [ite_eq_right h1, ite_eq_right (by exact_mod_cast h1)]
  have hv₀mem : v₀ ∈ Scheme.Modules.singleDegreeRankOpen P 1 g₀ :=
    (Scheme.Modules.mem_singleDegreeRankOpen_iff P 1 g₀ hPperf v₀).2 hβ
  set W' := Scheme.Modules.singleDegreeRankOpen P 1 g₀
  have hW' := (Scheme.Modules.isSingleDegreeRank_singleDegreeRankOpen P 1 g₀).2
  set R1 := ((Scheme.Modules.pushforward f).rightDerived 1).obj (SheafOfModules.unit X.ringCatSheaf)
  have hz1 : IsZero ((DerivedCategory.homologyFunctor V.Modules 1).obj
      ((DerivedCategory.singleFunctor V.Modules 0).obj V.unitModule)) :=
    Scheme.Modules.isZero_homologyFunctor_singleFunctor_obj _ (by decide)
  have : (DerivedCategory.homologyFunctor V.Modules 1).Additive := inferInstance
  have : PreservesBinaryBiproduct ((DerivedCategory.singleFunctor V.Modules 0).obj V.unitModule)
      P (DerivedCategory.homologyFunctor V.Modules 1) :=
    preservesBinaryBiproduct_of_preservesBiproduct _ _ _
  let i1 : (Scheme.Modules.restrictFunctor ι).obj R1 ≅
      (DerivedCategory.homologyFunctor V.Modules 1).obj P :=
    (Scheme.Modules.restrictFunctor ι).mapIso
        (homologyDerivedPushforwardModuleIso f (SheafOfModules.unit X.ringCatSheaf) 1).symm ≪≫
      ((Scheme.Modules.homologyFunctor_mapDerivedCategory_restrictFunctor_iso ι 1).app E).symm ≪≫
      (DerivedCategory.homologyFunctor V.Modules 1).mapIso e ≪≫
      obj_biprod_iso_of_isZero _ _ _ hz1
  have hr : Scheme.Modules.IsFiniteLocallyFreeOfRank
      ((Scheme.Modules.restrictFunctor (W'.ι ≫ ι)).obj R1) g₀ :=
    ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ g₀).2 hW').of_iso
      ((Scheme.Modules.restrictFunctor W'.ι).mapIso i1.symm ≪≫
        ((Scheme.Modules.restrictFunctorComp W'.ι ι).app R1).symm)
  have hrange : Set.range (ι ''ᵁ W').ι = Set.range (W'.ι ≫ ι) := by simp [Set.range_comp]
  let φ : (ι ''ᵁ W').toScheme ≅ W'.toScheme :=
    IsOpenImmersion.isoOfRangeEq (ι ''ᵁ W').ι (W'.ι ≫ ι) hrange
  exact ⟨ι ''ᵁ W', ⟨v₀, hv₀mem, hv₀⟩, (hr.restrict φ.hom).of_iso
    (((Scheme.Modules.restrictFunctorCongr
        (IsOpenImmersion.isoOfRangeEq_hom_fac (ι ''ᵁ W').ι (W'.ι ≫ ι) hrange)).app R1).symm ≪≫
      (Scheme.Modules.restrictFunctorComp φ.hom (W'.ι ≫ ι)).app R1).symm⟩

/-- **`R¹f_*𝒪_X` is finite locally free of rank `r` when the fibres have genus `r`.** If every
point lies under a field-valued point whose fibre is a curve with `H⁰` the field and of genus `r`,
then `R¹f_*𝒪_X` is finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_rightDerived_one_of_forall_genus_eq (r : ℕ)
    (hC : ∀ s : S, ∃ (K : Type u) (_ : Field K) (p : Spec (.of K) ⟶ S) (Y : Scheme.{u})
      (a : Y ⟶ X) (g : Y ⟶ Spec (.of K)) (_ : IsPullback a g f p) (pt : Spec (.of K)),
        p.base pt = s ∧ topologicalKrullDim Y ≤ 1 ∧ Function.Bijective g.appTop ∧ genus g = r) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)) r := by
  have hΓ : HasFieldGlobalFunctionsFibres f := fun s => by
    obtain ⟨K, _, p, Y, a, g, hsq, pt, hpt, -, hb, -⟩ := hC s
    exact ⟨K, inferInstance, p, Y, a, g, hsq, pt, hpt, hb⟩
  have hW : ∀ s : S, ∃ (W : S.Opens) (_ : s ∈ W), Scheme.Modules.IsFiniteLocallyFreeOfRank
      ((((Scheme.Modules.pushforward f).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf)).restrict W.ι) r := fun s => by
    obtain ⟨K, _, p, Y, a, g, hsq, pt, hpt, hd, -, hg⟩ := hC s
    obtain ⟨W, hsW, hr⟩ :=
      exists_isFiniteLocallyFreeOfRank_restrict_rightDerived_one f hf hΓ K p a g hsq pt hd
    exact ⟨W, hpt ▸ hsW, hg ▸ hr⟩
  choose W hsW hr using hW
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top W
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hsW x⟩) hr

/-- **The fibres have the genus of `R¹f_*𝒪_X`.** If `R¹f_*𝒪_X` is finite locally free of rank `r`,
then every fibre at a field-valued point which is a curve has genus `r`. -/
theorem genus_eq_of_isFiniteLocallyFreeOfRank_rightDerived_one
    (hΓ : HasFieldGlobalFunctionsFibres f) {r : ℕ}
    (hR : Scheme.Modules.IsFiniteLocallyFreeOfRank
      (((Scheme.Modules.pushforward f).rightDerived 1).obj (SheafOfModules.unit X.ringCatSheaf)) r)
    (K : Type u) [Field K] (p : Spec (.of K) ⟶ S) {Y : Scheme.{u}} (a : Y ⟶ X)
    (g : Y ⟶ Spec (.of K)) (hsq : IsPullback a g f p) (pt : Spec (.of K))
    (hdim : topologicalKrullDim Y ≤ 1) : genus g = r := by
  obtain ⟨W, hW, hr⟩ :=
    exists_isFiniteLocallyFreeOfRank_restrict_rightDerived_one f hf hΓ K p a g hsq pt hdim
  exact DescentLocusComparison.eq_of_isFiniteLocallyFreeOfRank (Y := W.toScheme) _
    (⟨p.base pt, hW⟩ : W.toScheme)
    ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).1 hr)
    ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).1 (hR.restrict W.ι))

end Rank

end AlgebraicGeometry.C1590Private

end
