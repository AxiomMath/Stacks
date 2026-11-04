module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.AdicReductionComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.DerivedReduction
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleDerivedSheaves
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedReductionTower
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedRestrictionProducts
public import StacksFrontier.AlgebraicGeometry.ProEtale.QuasiCompactFinalObject
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.LocallyConstantTrivialization
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ProetaleTestingFamily
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.Situation
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EventuallyConstantDifference
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleConstantSheaf
import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteComparison
import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SurjectiveTowerDerivedLimit
import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedCompletion
import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ReductionTowerAmplitude
import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# The reductions of a constructible complex on the pro-étale site

Let `Λ` be a Noetherian ring, `I ⊆ Λ` an ideal, `X` a quasi-compact scheme and `K` an object of
`D_cons(X, Λ)`. Set `Kₙ = K ⊗_Λ^L \underline{Λ/Iⁿ}`. There are integers `a ≤ b` such that
`K = R lim Kₙ` and `Hⁱ(K) = 0` for `i ∉ [a, b]`, every `Kₙ` has Tor amplitude in `[a, b]`, and
every `Kₙ` has constructible cohomology sheaves.

## Main definitions

* `AlgebraicGeometry.ProEtale.weaklyContractibleObjectsSituation`: `X_proét` with its
  w-contractible affine objects, ringed by `\underline{Λ}`.

## Main results

* `AlgebraicGeometry.ProEtale.exists_hasTorAmplitude_derivedReduction_pow`: the uniform Tor
  amplitude of the reductions.
* `AlgebraicGeometry.ProEtale.hasExactLimitsOfShape_discrete_nat_sheafModuleCat` and
  `AlgebraicGeometry.ProEtale.epi_milnorDifference_sheafModuleCat`: countable products of
  sheaves of `Λ`-modules on `X_proét` are exact, and `R¹lim` of a tower of surjections vanishes.
* `AlgebraicGeometry.ProEtale.exists_isDerivedLimit_derivedReductionTower_and_hasTorAmplitude`:
  parts (1) and (2), `K = R lim Kₙ` with cohomology in `[a, b]`, and the Tor amplitude of the
  `Kₙ` in `[a, b]`.
* `AlgebraicGeometry.ProEtale.hasConstructibleCohomology_derivedReduction_pow`: the
  constructibility of the cohomology sheaves of the reductions.
* `AlgebraicGeometry.ProEtale.hasTorAmplitude_of_hasTorAmplitude_etaleInverseImage`: `ε⁻¹`
  reflects Tor amplitude.
* `AlgebraicGeometry.ProEtale.exists_etaleInverseImage_iso_derivedReduction_pow`: the reductions
  come from constructible complexes of finite Tor dimension on the étale site.

## Implementation notes

In part (1) the tower `Kₙ = K ⊗_Λ^L \underline{Λ/Iⁿ}` and its derived limit are read in the
derived category of sheaves of `Λ`-modules on `X_proét`, which is equivalent to `D(X_proét, Λ)`
by `AlgebraicGeometry.ProEtale.derivedModuleEquiv`; the vanishing of the cohomology sheaves is
stated for `K` itself.

In part (4) the object `Lₙ` is shown to have finite Tor dimension on the whole of `X_étale`
(`Stacks.ModuleSheaf.HasFiniteTorDimension`), which is the uniform form of the local finiteness
of Tor dimension required of an object of `D_ctf(X_étale, Λ/Iⁿ)`.

## References

* [Stacks Project, Tag 09C2](https://stacks.math.columbia.edu/tag/09C2)
* [Stacks Project, Tag 099M](https://stacks.math.columbia.edu/tag/099M)
* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
* [Stacks Project, Tag 09BR](https://stacks.math.columbia.edu/tag/09BR)
* [Stacks Project, Tag 09AK](https://stacks.math.columbia.edu/tag/09AK)
* [Stacks Project, Tag 09B1](https://stacks.math.columbia.edu/tag/09B1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u}) (Λ : Type (max (u + 1) w)) [CommRing Λ] (I : Ideal Λ)
  [IsNoetherianRing Λ]

/-- **Uniform Tor amplitude of the reductions of a constructible complex.** If `X` is
quasi-compact and `K` lies in `D_cons(X, Λ)`, there are integers `a` and `b` such that every
reduction `K ⊗_Λ^L Λ/Iⁿ` has Tor amplitude in `[a, b]`. -/
@[sga "6 I 5.5" "special case"]
theorem exists_hasTorAmplitude_derivedReduction_pow [CompactSpace X]
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K) :
    ∃ a b : ℤ, ∀ n : ℕ, Stacks.ModuleSheaf.HasTorAmplitude (J := Scheme.ProEt.topology X)
      ((derivedReduction.{u, w} X Λ (I ^ n)).obj K) (Set.Icc a b) := by
  obtain ⟨a, b, h⟩ := Stacks.ModuleSheaf.exists_hasTorAmplitude_of_locallyHasFiniteTorDimension
    Scheme.ProEt.isTerminal_mk_id (fun S hS => Scheme.ProEt.exists_finite_coversTop_le S hS)
    _ hK.2.2
  exact ⟨a, b, fun n => h.derivedExtendScalars_pow I (IsNoetherian.noetherian I) n⟩

/-- **The reductions of a constructible complex have constructible cohomology sheaves.** If `X`
is quasi-compact and `K` lies in `D_cons(X, Λ)`, every reduction
`Kₙ = K ⊗_Λ^L Λ/Iⁿ` has constructible cohomology sheaves. -/
@[stacks 09C2 "part (3)"]
theorem hasConstructibleCohomology_derivedReduction_pow [CompactSpace X]
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    (n : ℕ) :
    HasConstructibleModuleSheafCohomology.{u, w} X (Λ ⧸ I ^ n)
      ((derivedReduction.{u, w} X Λ (I ^ n)).obj K) := by
  obtain ⟨a, b, h⟩ := exists_hasTorAmplitude_derivedReduction_pow X Λ I hK
  exact (minus_and_isConstructibleModuleSheaf'_homology_derivedExtendScalars I
    ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K)
    ⟨⟨b, (pow_one I ▸ h 1).isGE_isLE.2⟩, hK.2.1⟩ n).2

section Bounds

attribute [local instance] SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

/-- The small pro-étale site of `X` with its affine objects with w-contractible ring of global
sections, which are weakly contractible and cover every object, ringed by the constant
coefficient ring sheaf `\underline{Λ}`. -/
def weaklyContractibleObjectsSituation :
    Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation.{max (u + 1) w, u, u + 1,
      max (u + 1) w} X.ProEt (Scheme.ProEt.topology X) where
  B := Scheme.ProEt.IsAffineWContractible
  isWeaklyContractible U hU _ _ φ hφ :=
    have := hU.1
    Scheme.ProEt.surjective_app_of_isWContractible U hU.2 φ hφ
  hasEnoughObjects := Scheme.ProEt.hasEnoughObjects_isAffineWContractible
  O := Stacks.SheafOfModules.Tensor.ringSheaf
    (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O

/-- **Countable products of sheaves of `Λ`-modules on `X_proét` are exact** (Stacks 0947 (4)). -/
instance hasExactLimitsOfShape_discrete_nat_sheafModuleCat :
    HasExactLimitsOfShape (Discrete ℕ)
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) :=
  HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ)
    (constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ).symm

omit [IsNoetherianRing Λ] in
/-- **`R¹lim` of a tower of surjections of sheaves of `Λ`-modules on `X_proét` vanishes**
(Stacks 0947 (3)): the Milnor difference of a tower whose transition maps are epimorphisms is an
epimorphism. -/
theorem epi_milnorDifference_sheafModuleCat
    (G : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (hG : ∀ n : ℕ, Epi (G.map (homOfLE (Nat.le_succ n)).op)) :
    Epi (Stacks.InverseSystem.milnorDifference (fun n : ℕ ↦ G.obj ⟨n⟩)
      (fun n : ℕ ↦ G.map (homOfLE (Nat.le_succ n)).op)) := by
  let E := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  refine Stacks.InverseSystem.epi_milnorDifference_of_epi_map E.functor _ _ ?_
  exact Stacks.WeaklyContractible.epi_milnorDifference_of_epi_map_succ
    (weaklyContractibleObjectsSituation X Λ) (G ⋙ E.functor)
    (fun n => have := hG n; E.functor.map_epi _)

/-- **Bounds and the derived limit from a Tor amplitude of the first reduction.** Let `K` be an
object of `D_cons(X, Λ)` whose first reduction `K ⊗_Λ^L \underline{Λ/I}` has Tor amplitude in
`[a, b]`. Then `K = R lim Kₙ`, with the reduction maps as projections, `Hⁱ(K) = 0` for
`i ∉ [a, b]`, and every `Kₙ` has Tor amplitude in `[a, b]`. -/
theorem isDerivedLimit_derivedReductionTower_and_hasTorAmplitude_of_hasTorAmplitude
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    {a b : ℤ} (h : Stacks.ModuleSheaf.HasTorAmplitude (J := Scheme.ProEt.topology X)
      ((derivedReduction.{u, w} X Λ I).obj K) (Set.Icc a b)) :
    (NoetherianAdicCompletion.IsDerivedLimitWithProjections
          (derivedReductionTower.{u, w} X Λ I
            ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K))
          ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K)
          (fun n ↦ (Stacks.ModuleSheaf.derivedReductionMap (Scheme.ProEt.topology X) Λ I
            ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K)).app ⟨n⟩) ∧
        ∀ i : ℤ, i ∉ Set.Icc a b →
          IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      ∀ n : ℕ, Stacks.ModuleSheaf.HasTorAmplitude (J := Scheme.ProEt.topology X)
        ((derivedReduction.{u, w} X Λ (I ^ n)).obj K) (Set.Icc a b) := by
  have hI : I.FG := IsNoetherian.noetherian I
  let e := derivedModuleEquiv.{u, max (u + 1) w, w} X Λ
  let K' := e.inverse.obj K
  have hc : IsDerivedComplete I K' := isDerivedComplete_derivedModuleEquiv_inverse_obj X I hK.1
  have hlim :=
    (Stacks.ModuleSheaf.isDerivedComplete_iff_isDerivedLimitWithProjections_derivedReductionTower
      (Scheme.ProEt.topology X) Λ I K').1 hc
  refine ⟨⟨hlim, fun i hi => ?_⟩, fun n => h.derivedExtendScalars_pow I hI n⟩
  have h₂ : ∀ n : ℕ, IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedReductionTower.{u, w} X Λ I K').obj ⟨n⟩)) := fun n =>
    Stacks.ModuleSheaf.isZero_homology_derivedReductionTower_obj I hI h n hi
  have h₃ : ∀ n : ℕ, Epi ((DerivedCategory.homologyFunctor _ (i - 1)).map
      ((derivedReductionTower.{u, w} X Λ I K').map (homOfLE (Nat.le_succ n)).op)) := fun n =>
    Stacks.ModuleSheaf.epi_homology_derivedReductionTower_map I hI h n (by rwa [sub_add_cancel])
  have h₁ := epi_milnorDifference_sheafModuleCat X Λ
    (derivedReductionTower.{u, w} X Λ I K' ⋙ DerivedCategory.homologyFunctor _ (i - 1)) h₃
  have hK' : IsZero ((DerivedCategory.homologyFunctor _ i).obj K') :=
    DerivedCategory.isZero_homology_of_isDerivedLimit _ K' hlim.isDerivedLimit i h₁ h₂
  let E := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  have h₄ : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (E.functor.mapDerivedCategory.obj K')) :=
    (E.functor.map_isZero hK').of_iso ((E.functor.mapDerivedCategoryHomologyIso i).app K')
  exact h₄.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso (e.counitIso.app K).symm)

/-- Let `X` be quasi-compact and `K` an object of `D_cons(X, Λ)`, and set
`Kₙ = K ⊗_Λ^L \underline{Λ/Iⁿ}`. There are integers `a` and `b` such that

1. `K = R lim Kₙ`, with the reduction maps `K ⟶ Kₙ` as projections, and `Hⁱ(K) = 0` for
   `i ∉ [a, b]`;
2. every `Kₙ` has Tor amplitude in `[a, b]`.

In (1) the tower `Kₙ` is read in the derived category of sheaves of `Λ`-modules, as the derived
tensor product of `K` with the constant sheaves `\underline{Λ/Iⁿ}`; in (2) `Kₙ` is the derived
reduction of `K`, an object of `D(X_proét, Λ/Iⁿ)`. -/
@[stacks 09C2 "parts (1) and (2)"]
theorem exists_isDerivedLimit_derivedReductionTower_and_hasTorAmplitude [CompactSpace X]
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K) :
    ∃ a b : ℤ,
      (NoetherianAdicCompletion.IsDerivedLimitWithProjections
          (derivedReductionTower.{u, w} X Λ I
            ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K))
          ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K)
          (fun n ↦ (Stacks.ModuleSheaf.derivedReductionMap (Scheme.ProEt.topology X) Λ I
            ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K)).app ⟨n⟩) ∧
        ∀ i : ℤ, i ∉ Set.Icc a b →
          IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      ∀ n : ℕ, Stacks.ModuleSheaf.HasTorAmplitude (J := Scheme.ProEt.topology X)
        ((derivedReduction.{u, w} X Λ (I ^ n)).obj K) (Set.Icc a b) := by
  obtain ⟨a, b, h⟩ := exists_hasTorAmplitude_derivedReduction_pow X Λ I hK
  exact ⟨a, b, isDerivedLimit_derivedReductionTower_and_hasTorAmplitude_of_hasTorAmplitude X Λ I hK
    (pow_one I ▸ h 1)⟩

end Bounds

section Etale

open MonoidalCategory

attribute [local instance] Sheaf.monoidalCategory Stacks.ModuleSheaf.derivedMonoidal
  Stacks.ModuleSheaf.derivedSymmetric

/-- **Inverse image along `ε` reflects Tor amplitude.** If `ε⁻¹ L` has Tor amplitude in `S`, so
has `L`. -/
theorem hasTorAmplitude_of_hasTorAmplitude_etaleInverseImage (R : Type (max (u + 1) w))
    [CommRing R]
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w} R))) (S : Set ℤ)
    (h : Stacks.ModuleSheaf.HasTorAmplitude (J := Scheme.ProEt.topology X)
      ((Scheme.etaleInverseImage.{u, w} X R).mapDerivedCategory.obj L) S) :
    Stacks.ModuleSheaf.HasTorAmplitude (J := X.smallEtaleTopology) L S := by
  intro G i hi
  let J := Scheme.ProEt.topology X
  let G' := X.etaleToProetale
  have : RepresentablyFlat G' := flat_of_preservesFiniteLimits _
  have (V : X.ProEtᵒᵖ) : IsFiltered (CostructuredArrow G'.op V) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence G' (Opposite.unop V))
  have (V : X.ProEtᵒᵖ) : HasColimitsOfShape (CostructuredArrow G'.op V)
      (ModuleCat.{max (u + 1) w} R) :=
    hasColimitsOfShape_of_essentiallySmall.{max (u + 1) w} _ _
  have (V : X.ProEtᵒᵖ) : HasColimitsOfShape (CostructuredArrow G'.op V)
      (Type (max (u + 1) w)) :=
    hasColimitsOfShape_of_essentiallySmall.{max (u + 1) w} _ _
  have : (G'.sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} R)
      X.smallEtaleTopology J).IsRightAdjoint :=
    (Scheme.etaleInverseImageAdjunction.{w} X R).isRightAdjoint
  let Φ := G'.sheafPullback (ModuleCat.{max (u + 1) w} R) X.smallEtaleTopology J
  let eΦ : Φ ≅ Scheme.etaleInverseImage.{u, w} X R :=
    Functor.sheafPullbackConstruction.sheafPullbackIso G' _ X.smallEtaleTopology J
  have : PreservesFiniteLimits Φ := preservesFiniteLimits_of_natIso eΦ.symm
  let Lₑ := (DerivedCategory.singleFunctor _ 0).obj G
  obtain ⟨e₁⟩ := Stacks.ModuleSheaf.nonempty_homology_sheafPullback_tensor_iso G' R
    X.smallEtaleTopology J L Lₑ 0 i
  let eK : Φ.mapDerivedCategory.obj L ≅
      (Scheme.etaleInverseImage.{u, w} X R).mapDerivedCategory.obj L :=
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso Φ _ eΦ).app L
  let eL : Φ.mapDerivedCategory.obj Lₑ ≅ (DerivedCategory.singleFunctor _ 0).obj (Φ.obj G) :=
    (Φ.mapDerivedCategorySingleFunctor 0).app _
  have hz : IsZero (Φ.obj ((DerivedCategory.homologyFunctor _ i).obj (L ⊗ Lₑ))) :=
    (h (Φ.obj G) i hi).of_iso (e₁ ≪≫ (DerivedCategory.homologyFunctor _ i).mapIso (eK ⊗ᵢ eL))
  have : (Scheme.etaleInverseImage.{u, w} X R).Faithful :=
    (Scheme.etaleInverseImageAdjunction.{w} X R).fullyFaithfulLOfIsIsoUnit.faithful
  have : Φ.Faithful := Functor.Faithful.of_iso eΦ.symm
  rw [IsZero.iff_id_eq_zero] at hz ⊢
  exact Φ.map_injective (by rw [Φ.map_id, hz, Φ.map_zero])

/-- **The reductions of a constructible complex come from the étale site.** If `X` is
quasi-compact and `K` lies in `D_cons(X, Λ)`, every reduction
`Kₙ = K ⊗_Λ^L Λ/Iⁿ` is `ε⁻¹ Lₙ` for an object `Lₙ` of `D(X_étale, Λ/Iⁿ)` with constructible
cohomology sheaves and finite Tor dimension.

Here `ε⁻¹` on derived categories is `ε⁻¹` applied termwise. -/
@[stacks 09C2 "part (4)"]
theorem exists_etaleInverseImage_iso_derivedReduction_pow [CompactSpace X]
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    (n : ℕ) :
    ∃ L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ n))),
      (∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf.{u, max (u + 1) w, w} X (Λ ⧸ I ^ n)
        ((DerivedCategory.homologyFunctor _ i).obj L)) ∧
      Stacks.ModuleSheaf.HasFiniteTorDimension (J := X.smallEtaleTopology) L ∧
      Nonempty ((Scheme.etaleInverseImage.{u, w} X (Λ ⧸ I ^ n)).mapDerivedCategory.obj L ≅
        (derivedReduction.{u, w} X Λ (I ^ n)).obj K) := by
  obtain ⟨a, b, hT⟩ := exists_hasTorAmplitude_derivedReduction_pow X Λ I hK
  have hC := hasConstructibleCohomology_derivedReduction_pow X Λ I hK n
  set Kn := (derivedReduction.{u, w} X Λ (I ^ n)).obj K
  have hbelow : DerivedCategoryB.IsBoundedBelow Kn := by
    have := (hT n).isGE_isLE.1
    exact ⟨a, fun i hi => Kn.isZero_of_isGE a i hi⟩
  have hplus : DerivedCategoryB.derivedCategoryBPlus
      (Scheme.etaleInverseImage.{u, w} X (Λ ⧸ I ^ n)).essImage Kn :=
    ⟨hbelow, fun i => etaleInverseImage_essImage_of_isConstructibleModuleSheaf' _ (hC i)⟩
  obtain ⟨L, ⟨e⟩⟩ := ((DerivedCategoryB.derivedCategoryBPlus_essImage_iff _
    (Scheme.etaleInverseImageAdjunction.{w} X (Λ ⧸ I ^ n))
    (fun I _ => Scheme.rightAcyclic_etaleInverseImage_obj.{w} X _ I) Kn).1 hplus).2
  have hL : Stacks.ModuleSheaf.HasTorAmplitude (J := Scheme.ProEt.topology X)
      ((Scheme.etaleInverseImage.{u, w} X (Λ ⧸ I ^ n)).mapDerivedCategory.obj L) (Set.Icc a b) :=
    fun G i hi => (hT n G i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (e ⊗ᵢ Iso.refl _))
  refine ⟨L, fun i => ?_, ⟨a, b, hasTorAmplitude_of_hasTorAmplitude_etaleInverseImage.{u, w} X _ L _
    hL⟩, ⟨e⟩⟩
  rw [← isConstructibleModuleSheaf'_etaleInverseImage_iff]
  exact ObjectProperty.prop_of_iso (IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X (Λ ⧸ I ^ n))
    (((DerivedCategory.homologyFunctor _ i).mapIso e).symm ≪≫
      ((Scheme.etaleInverseImage.{u, w} X (Λ ⧸ I ^ n)).mapDerivedCategoryHomologyIso i).app L)
    (hC i)

end Etale

end AlgebraicGeometry.ProEtale

end
