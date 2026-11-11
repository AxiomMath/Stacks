module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapCanonicalAdicLimit
public import StacksFrontier.RingTheory.LocalCohomology.IdealPowerFirstDerivedLimit
public import StacksFrontier.RingTheory.LocalCohomology.MittagLefflerEventualRange
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian

/-!
# The two assertions of Tag 0EFX at the closed point

Let `A` be a Noetherian local ring, `I ⊆ A` an ideal and `M` a finite `A`-module, and let
`T = {𝔪}`. This module proves, in Situation [Stacks, Tag 0EFU] at that locus, both assertions of
[Stacks, Tag 0EFX]: the inverse systems `{H^i_𝔪(IⁿM)}` are pro-zero for `i ≤ s`, and the images
of the transition maps in degree `s + 1` inject into a fixed term.

The inputs are three, all available at this locus:

* `{H^i_𝔪(M/IⁿM)}` satisfies the Mittag-Leffler condition, in every degree
  (`Stacks.LocalCohomology.isMittagLefflerCategorical_localCohomologyAdicTower_closedPoint`);
* the canonical map `H^i_𝔪(M) ⟶ lim H^i_𝔪(M/IⁿM)` is an isomorphism for `i ≤ s`, which is
  part (4) of [Stacks, Tag 0EFY] and the isomorphism assertion of [Stacks, Tag 0EFR];
* the long exact sequence of `0 → IⁿM → M → M/IⁿM → 0` with its connecting map, natural in `n`.

The second input is proved in the **coreflection** model of local cohomology
(`Stacks.Algebraization.isIso_localCohomologyAdicQuotientToLimit_closedPoint`), while the first,
the third and the statement of Tag 0EFX are in the **set-indexed** model. Bridging the two is the
first half of this module, and it was the one piece missing: the comparison of the two models is
[Stacks, Tag 0955], and the two towers of adic quotients are also spelled differently —
`Stacks.LocalCohomology.idealPowerQuotientTower`, whose transition maps are `Submodule.mapQ`
of the identity, against `AlgebraicGeometry.ProEtale.adicQuotientModuleSystem`, built from its
successor maps by `CategoryTheory.Functor.ofOpSequence`. Both towers have the same terms and both
are compatible with the quotient maps out of `M`, which are epimorphisms, so the transition maps
agree and the identity is a natural isomorphism.

The second half is the diagram chase the source compresses into "(some details omitted)" in the
first paragraph of its proof, carried out at `T = {𝔪}`.

## Main results

* `Stacks.LocalCohomology.idealPowerQuotientTowerIsoAdicQuotientModuleSystem` — the two spellings
  of the tower `n ↦ M/IⁿM` agree.
* `Stacks.LocalCohomology.localCohomologyWithSupportInModuleFunctorIso` — the two models of
  `H^i_{V(J)}` on modules agree, naturally in the module.
* `Stacks.LocalCohomology.isIso_limitLift_localCohomologyAdicCone_closedPoint` — part (4) of
  [Stacks, Tag 0EFY] at `T = {𝔪}`, carried into the set-indexed model: the limit comparison of
  the canonical cone on `{H^i_𝔪(M/IⁿM)}` with point `H^i_𝔪(M)` is invertible for `i ≤ s`.
* `Stacks.LocalCohomology.exists_range_eq_of_isArtinian` — the ranges of the transition maps of a
  tower of Artinian modules stabilize, in the range form the eventual-range lemma consumes.
* `Stacks.LocalCohomology.exists_forall_injective_localCohomologyAdicProjection_of_isIso` —
  part (1) of [Stacks, Tag 0EFY] in one degree, in the set-indexed model, from Artinianness and
  the limit comparison.
* `Stacks.LocalCohomology.exists_map_idealPowerTower_eq_zero_of_injective_of_range_le` and
  `Stacks.LocalCohomology.hasStableImageIdealPowerCohomology_of_range_le` — the two diagram
  chases of the first paragraph of the proof of [Stacks, Tag 0EFX].
* `Stacks.Algebraization.exists_map_idealPowerTower_eq_zero_closedPoint` and
  `Stacks.Algebraization.hasStableImageIdealPowerCohomology_closedPoint` — **the two assertions of
  [Stacks, Tag 0EFX] at `T = {𝔪}`**, with nothing assumed beyond Situation [Stacks, Tag 0EFU].

## What this leaves open for a general `T`

The source's locus is an arbitrary specialization-stable `T ⊆ V(I)`, and its last paragraph
reduces that case to the per-prime assertion **uniformly in `𝔮 ∈ T`**, by Lemmas
[Stacks, Tag 0EF9] and [Stacks, Tag 0EFA] (proved as
`Stacks.LocalCohomology.localCohomologyWithSupportIn_map_eq_zero_of_local` and
`Stacks.LocalCohomology.eventually_injective_image_localCohomologyWithSupportIn`). The two
theorems below are that per-prime assertion at one prime: `BootstrapSituation.localize` and
`BootstrapSituation.shrink` (parts (F) and (E) of [Stacks, Tag 0EFV]) turn a situation and a
`𝔮 ∈ T` into a situation over `A_𝔮` whose locus is the closed point. What is still owed is the
uniformity, which is the source's local-duality paragraph: the vanishing is transported to the
finite Ext modules `Ext^j_A(IⁿM, ω_A^•)`, spread to an open neighbourhood, and made uniform over
each level set of the dimension function.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0EFR](https://stacks.math.columbia.edu/tag/0EFR)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A]

/-! ### The two spellings of the tower of adic quotients -/

/-- The transition maps of the two spellings of the tower `n ↦ M/IⁿM` agree: both become the
quotient map `M ⟶ M/IᵐM` after precomposition with `M ⟶ M/IⁿM`, which is an epimorphism. -/
theorem idealPowerQuotientTower_map_eq (I : Ideal A) (M : ModuleCat.{u} A)
    {n m : ℕᵒᵖ} (g : n ⟶ m) :
    (idealPowerQuotientTower.{u, u} I M).map g =
      (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M).map g := by
  have hepi : Epi ((idealPowerQuotientCone.{u, u} I M).π.app n) :=
    (ModuleCat.epi_iff_surjective _).2
      (Submodule.mkQ_surjective (I ^ n.unop • (⊤ : Submodule A M)))
  refine hepi.left_cancellation _ _ ?_
  rw [(idealPowerQuotientCone.{u, u} I M).w g]
  exact (Dualizing.adicQuotientProjection_comp_map A I M (leOfHom g.unop)).symm

/-- **The two spellings of the tower `n ↦ M/IⁿM` agree.** `idealPowerQuotientTower` defines the
transition maps directly, as `Submodule.mapQ` of the identity of `M`;
`AlgebraicGeometry.ProEtale.adicQuotientModuleSystem` builds them from the successor maps by
`CategoryTheory.Functor.ofOpSequence`. The terms are the same module, and both towers are
compatible with the quotient maps `M ⟶ M/IⁿM`, which are epimorphisms, so the transition maps
agree and the identity is a natural isomorphism. -/
def idealPowerQuotientTowerIsoAdicQuotientModuleSystem (I : Ideal A) (M : ModuleCat.{u} A) :
    idealPowerQuotientTower.{u, u} I M ≅
      AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {_ _} g =>
    (Category.comp_id _).trans
      ((idealPowerQuotientTower_map_eq A I M g).trans (Category.id_comp _).symm)

/-! ### The two models of local cohomology with closed support, on modules -/

/-- **The two models of `H^i_{V(J)}` on modules agree, naturally in the module.** The set-indexed
model is the total right derived functor of `V(J)`-supported sections; the coreflection model is
the one of [Stacks, Tag 0A6Q]. Over a Noetherian ring the comparison of [Stacks, Tag 0A6U] is a
natural isomorphism, which is [Stacks, Tag 0955]. -/
def localCohomologyWithSupportInModuleFunctorIso [IsNoetherianRing A] (J : Ideal A) (hJ : J.FG)
    (i : ℤ) :
    localCohomologyWithSupportInModuleFunctor.{u, u} A (PrimeSpectrum.zeroLocus (J : Set A)) i ≅
      DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
        localCohomologyDerived.{u, u} A J hJ ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i :=
  Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0)
    (Functor.isoWhiskerRight
      (@asIso _ _ _ _ (compareSectionsWithSupportLocalCohomology.{u, u} A J hJ)
        (isIso_compareSectionsWithSupportLocalCohomology.{u, u} A J hJ))
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i))

/-- A connecting image `δ_k y` dies at level `m` when the transition image of `y` comes from
`H^p_T(M)`. -/
private theorem map_idealPowerTower_localCohomologyδ_eq_zero {R : Type u} [CommRing R]
    (T : Set (PrimeSpectrum R)) (I : Ideal R) (M : ModuleCat.{u} R) (p q : ℤ) (hpq : p + 1 = q)
    {m k : ℕ} (hmk : m ≤ k)
    (y : (localCohomologyWithSupportInModuleFunctor.{u, u} R T p).obj
      ((idealPowerQuotientTower.{u, u} I M).obj (op k)))
    (hy : ((localCohomologyWithSupportInModuleFunctor.{u, u} R T p).map
        ((idealPowerQuotientTower.{u, u} I M).map (homOfLE hmk).op)).hom y ∈
      LinearMap.range ((localCohomologyAdicCone.{u, u} R T I p M).π.app (op m)).hom) :
    ((localCohomologyWithSupportInModuleFunctor.{u, u} R T q).map
      ((idealPowerTower.{u, u} I M).map (homOfLE hmk).op)).hom
        ((localCohomologyδ.{u, u} T
          (idealPowerShortComplex_shortExact.{u, u} I M k) p q hpq).hom y) = 0 := by
  obtain ⟨g, hg⟩ := hy
  have hnat := localCohomologyδ_idealPowerShortComplex_naturality.{u, u} T I M p q hpq hmk
  have hzero := localCohomologyMap_comp_localCohomologyδ.{u, u} T
    (idealPowerShortComplex_shortExact.{u, u} I M m) p q hpq
  refine (ConcreteCategory.congr_hom hnat y).symm.trans ?_
  change (localCohomologyδ.{u, u} T (idealPowerShortComplex_shortExact.{u, u} I M m) p q
    hpq).hom (((localCohomologyWithSupportInModuleFunctor.{u, u} R T p).map
      ((idealPowerQuotientTower.{u, u} I M).map (homOfLE hmk).op)).hom y) = 0
  rw [← hg]
  exact ConcreteCategory.congr_hom hzero g

/-! ### The comparison on the tower and the cone of adic quotients -/

variable [IsNoetherianRing A]

/-- The comparison of the two models, read on the tower `n ↦ H^i(M/IⁿM)` of the local
cohomologies of the adic quotients. -/
def localCohomologyAdicTowerIso (J : Ideal A) (hJ : J.FG) (I : Ideal A) (i : ℤ)
    (M : ModuleCat.{u} A) :
    localCohomologyAdicTower.{u, u} A (PrimeSpectrum.zeroLocus (J : Set A)) I i M ≅
      Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i :=
  NatIso.ofComponents
    (fun n => (localCohomologyWithSupportInModuleFunctorIso A J hJ i).app
      ((idealPowerQuotientTower.{u, u} I M).obj n))
    fun {n m} g => by
      change (localCohomologyWithSupportInModuleFunctor.{u, u} A
              (PrimeSpectrum.zeroLocus (J : Set A)) i).map
            ((idealPowerQuotientTower.{u, u} I M).map g) ≫ _ =
          _ ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
            localCohomologyDerived.{u, u} A J hJ ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
              ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M).map g)
      rw [← idealPowerQuotientTower_map_eq A I M g]
      exact (localCohomologyWithSupportInModuleFunctorIso A J hJ i).hom.naturality
        ((idealPowerQuotientTower.{u, u} I M).map g)

/-- **The two canonical cones correspond under the comparison.** The legs of both cones are the
image of one and the same map — the quotient map `M ⟶ M/IⁿM` — under the respective model of
`H^i`, so the square required of the comparison is its own naturality at that map. -/
def localCohomologyAdicConeIso (J : Ideal A) (hJ : J.FG) (I : Ideal A) (i : ℤ)
    (M : ModuleCat.{u} A) :
    (Cone.postcompose (localCohomologyAdicTowerIso A J hJ I i M).hom).obj
        (localCohomologyAdicCone.{u, u} A (PrimeSpectrum.zeroLocus (J : Set A)) I i M) ≅
      Stacks.Algebraization.localCohomologyAdicQuotientCone A I J hJ M i :=
  Cone.ext ((localCohomologyWithSupportInModuleFunctorIso A J hJ i).app M) fun n =>
    (localCohomologyWithSupportInModuleFunctorIso A J hJ i).hom.naturality
      (Dualizing.adicQuotientProjection A I M n.unop)

/-- **Part (4) of [Stacks, Tag 0EFY] at `T = {𝔪}`, in the set-indexed model.** In Situation
[Stacks, Tag 0EFU] with `A` local and `T = {𝔪}`, the canonical comparison
`H^i_𝔪(M) ⟶ lim H^i_𝔪(M/IⁿM)` of the set-indexed model is an isomorphism for `i ≤ s`.

The same assertion in the coreflection model is
`Stacks.Algebraization.isIso_localCohomologyAdicQuotientToLimit_closedPoint`; what is done here is
to carry it across the comparison of the two models, [Stacks, Tag 0955], and across the two
spellings of the tower of adic quotients. That passage is what the set-indexed statements of
[Stacks, Tag 0EFX] need, their own inputs — the Mittag-Leffler condition and the long exact
sequence of `0 → IⁿM → M → M/IⁿM → 0` — living on the set-indexed side. -/
theorem isIso_limitLift_localCohomologyAdicCone_closedPoint
    (S : Stacks.Algebraization.BootstrapSituation.{u, u, u}) [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) (i : ℤ) (hi : i ≤ S.s) :
    IsIso (limit.lift (localCohomologyAdicTower.{u, u} S.A S.T S.I i (ModuleCat.of S.A S.M))
      (localCohomologyAdicCone.{u, u} S.A S.T S.I i (ModuleCat.of S.A S.M))) := by
  have hTz : S.T = PrimeSpectrum.zeroLocus ((maximalIdeal S.A : Ideal S.A) : Set S.A) := by
    rw [hT, Stacks.Algebraization.zeroLocus_maximalIdeal]
  rw [hTz]
  have hiso : IsIso ((limit.isLimit
      (Dualizing.adicQuotientLocalCohomologySystem S.A S.I (maximalIdeal S.A)
          (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i)).lift
      (Stacks.Algebraization.localCohomologyAdicQuotientCone S.A S.I (maximalIdeal S.A)
        (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) i)) :=
    Stacks.Algebraization.isIso_localCohomologyAdicQuotientToLimit_closedPoint S hT i hi
  have hlim' : IsLimit (Stacks.Algebraization.localCohomologyAdicQuotientCone S.A S.I
      (maximalIdeal S.A) (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) i) :=
    IsLimit.ofPointIso (limit.isLimit _)
  have hlim : IsLimit (localCohomologyAdicCone.{u, u} S.A
      (PrimeSpectrum.zeroLocus ((maximalIdeal S.A : Ideal S.A) : Set S.A)) S.I i
      (ModuleCat.of S.A S.M)) :=
    IsLimit.postcomposeHomEquiv
      (localCohomologyAdicTowerIso S.A (maximalIdeal S.A) (Ideal.fg_of_isNoetherianRing _)
        S.I i (ModuleCat.of S.A S.M)) _
      (hlim'.ofIsoLimit
        (localCohomologyAdicConeIso S.A (maximalIdeal S.A) (Ideal.fg_of_isNoetherianRing _)
          S.I i (ModuleCat.of S.A S.M)).symm)
  exact (IsLimit.conePointUniqueUpToIso hlim (limit.isLimit _)).isIso_hom

/-! ### The diagram chase of the first paragraph of the proof of Tag 0EFX -/

section Chase

variable {A}

omit [IsNoetherianRing A] in
/-- **The diagram chase of the first paragraph of the proof of [Stacks, Tag 0EFX].** Fix a degree
`i` and a level `m`. Assume

* `hinj`, that the projections `H^i_T(M) ⟶ H^i_T(M/IⁿM)` are injective from some level on, which
  is part (1) of [Stacks, Tag 0EFY] in degree `i`; and
* `hrange`, that the images of the transition maps of `{H^{i-1}_T(M/IⁿM)}` into level `m` are
  eventually contained in the image of `H^{i-1}_T(M)` there, which is what the Mittag-Leffler
  condition and part (4) of [Stacks, Tag 0EFY] give in degree `i - 1`, through
  `Stacks.LocalCohomology.range_transitionMap_le_range_cone_π`.

Then some transition map `H^i_T(IᵏM) ⟶ H^i_T(IᵐM)` vanishes.

*Argument.* Take `j` at least the level of `hinj` and the index of `hrange`. Injectivity of
`H^i_T(M) ⟶ H^i_T(M/IʲM)` and exactness of `H^i_T(IʲM) → H^i_T(M) → H^i_T(M/IʲM)` make
`H^i_T(IʲM) ⟶ H^i_T(M)` the zero map, so by exactness of
`H^{i-1}_T(M/IʲM) → H^i_T(IʲM) → H^i_T(M)` every class in `H^i_T(IʲM)` is `δ_j y`. The naturality
of `δ` carries `δ_j y` along the transition map to `δ_m` of the transition image of `y`, which by
`hrange` comes from `H^{i-1}_T(M)`; and `δ_m` kills the image of `H^{i-1}_T(M) ⟶ H^{i-1}_T(M/IᵐM)`,
two consecutive maps of the long exact sequence. So the transition map from level `j` vanishes. -/
theorem exists_map_idealPowerTower_eq_zero_of_injective_of_range_le
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A) (i : ℤ) (m : ℕ)
    (hinj : ∃ m₀ : ℕ, ∀ n : ℕ, m₀ ≤ n →
      Function.Injective ((localCohomologyAdicCone.{u, u} A T I i M).π.app (op n)).hom)
    (hrange : ∃ C : ℕ, ∃ _hmC : m ≤ C, ∀ (k : ℕ) (hmk : m ≤ k) (_hCk : C ≤ k),
      LinearMap.range ((localCohomologyAdicTower.{u, u} A T I (i - 1) M).map
          (homOfLE hmk).op).hom ≤
        LinearMap.range ((localCohomologyAdicCone.{u, u} A T I (i - 1) M).π.app (op m)).hom) :
    ∃ k : ℕ, ∃ h : m ≤ k,
      (localCohomologyWithSupportInModuleFunctor.{u, u} A T i).map
        ((idealPowerTower.{u, u} I M).map (homOfLE h).op) = 0 := by
  obtain ⟨m₀, hm₀⟩ := hinj
  obtain ⟨C, hmC, hC⟩ := hrange
  have hji : i - 1 + 1 = i := by omega
  have hmj : m ≤ max m₀ C := hmC.trans (le_max_right _ _)
  refine ⟨max m₀ C, hmj, ?_⟩
  -- `H^i_T(IʲM) ⟶ H^i_T(M)` is zero, by injectivity of the projection at level `j`.
  have hα : ∀ z, ((localCohomologyWithSupportInModuleFunctor.{u, u} A T i).map
      (idealPowerInclusion.{u, u} I M (max m₀ C))).hom z = 0 := by
    intro z
    have hcomp := localCohomologyMap_comp_localCohomologyMap.{u, u} T
      (idealPowerShortComplex_shortExact.{u, u} I M (max m₀ C)) i
    have h2 : ((localCohomologyAdicCone.{u, u} A T I i M).π.app (op (max m₀ C))).hom
        (((localCohomologyWithSupportInModuleFunctor.{u, u} A T i).map
          (idealPowerInclusion.{u, u} I M (max m₀ C))).hom z) = 0 :=
      ConcreteCategory.congr_hom hcomp z
    exact hm₀ (max m₀ C) (le_max_left _ _) (h2.trans (map_zero _).symm)
  -- Hence every class at level `j` is a connecting image.
  have hδ : ∀ x : (localCohomologyWithSupportInModuleFunctor.{u, u} A T i).obj
      ((idealPowerTower.{u, u} I M).obj (op (max m₀ C))),
      ∃ y, (localCohomologyδ.{u, u} T
        (idealPowerShortComplex_shortExact.{u, u} I M (max m₀ C)) (i - 1) i hji).hom y = x :=
    fun x =>
      (ShortComplex.moduleCat_exact_iff _).mp
        (localCohomology_exact₁.{u, u} T
          (idealPowerShortComplex_shortExact.{u, u} I M (max m₀ C)) (i - 1) i hji) x (hα x)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, hy⟩ := hδ x
  rw [← hy]
  exact map_idealPowerTower_localCohomologyδ_eq_zero T I M (i - 1) i hji hmj y
    (hC (max m₀ C) hmj (le_max_right _ _) ⟨y, rfl⟩)

omit [IsNoetherianRing A] in
/-- **The stable-image assertion of [Stacks, Tag 0EFX], from the eventual ranges one degree
below.** With `hrange` as in `exists_map_idealPowerTower_eq_zero_of_injective_of_range_le`, but
in degree `j - 1` and at every level, the stable-image assertion of the tag holds in degree `j`,
based at any `m₀` at all.

*Argument.* Let `m ≥ m₀`, let `k` be past the index `hrange` provides at level `m`, and let `x`
in `H^j_T(IᵏM)` have transition image at level `m` killed by the transition map down to level
`m₀`. The inclusion `IᵏM ⊆ M` factors through `IᵐM` and then through `I^{m₀}M`, so `x` already
dies in `H^j_T(M)`; by exactness it is `δ_k y`, and the naturality of `δ` together with `hrange`
and the vanishing of `δ_m` on the image of `H^{j-1}_T(M)` make its transition image at level `m`
zero — which is more than asked, the assertion only requiring that image to inject into level
`m₀`. -/
theorem hasStableImageIdealPowerCohomology_of_range_le
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A) (j : ℤ) (m₀ : ℕ)
    (hrange : ∀ m : ℕ, ∃ C : ℕ, ∃ _hmC : m ≤ C, ∀ (k : ℕ) (hmk : m ≤ k) (_hCk : C ≤ k),
      LinearMap.range ((localCohomologyAdicTower.{u, u} A T I (j - 1) M).map
          (homOfLE hmk).op).hom ≤
        LinearMap.range ((localCohomologyAdicCone.{u, u} A T I (j - 1) M).π.app (op m)).hom) :
    HasStableImageIdealPowerCohomology.{u, u} T I M j m₀ := by
  have hji : j - 1 + 1 = j := by omega
  have hfac : ∀ {a b : ℕ} (h : a ≤ b), (idealPowerTower.{u, u} I M).map (homOfLE h).op ≫
      idealPowerInclusion.{u, u} I M a = idealPowerInclusion.{u, u} I M b := by
    intro a b h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  intro m hm₀m
  obtain ⟨C, hmC, hC⟩ := hrange m
  refine ⟨C, hmC, fun k hCk x hx => ?_⟩
  rw [LinearMap.mem_ker] at hx
  have hmk : m ≤ k := hmC.trans hCk
  have hα : ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
      (idealPowerInclusion.{u, u} I M k)).hom x = 0 := by
    have h1 : idealPowerInclusion.{u, u} I M k =
        (idealPowerTower.{u, u} I M).map (homOfLE hmk).op ≫
          ((idealPowerTower.{u, u} I M).map (homOfLE hm₀m).op ≫
            idealPowerInclusion.{u, u} I M m₀) := by
      rw [hfac hm₀m, hfac hmk]
    have hx' : ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
        ((idealPowerTower.{u, u} I M).map (homOfLE hm₀m).op)).hom
          (((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
            ((idealPowerTower.{u, u} I M).map (homOfLE hmk).op)).hom x) = 0 := hx
    rw [h1, Functor.map_comp, Functor.map_comp]
    change ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
        (idealPowerInclusion.{u, u} I M m₀)).hom
        (((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
          ((idealPowerTower.{u, u} I M).map (homOfLE hm₀m).op)).hom
          (((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
            ((idealPowerTower.{u, u} I M).map (homOfLE hmk).op)).hom x)) = 0
    rw [hx', map_zero]
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (localCohomology_exact₁.{u, u} T
      (idealPowerShortComplex_shortExact.{u, u} I M k) (j - 1) j hji) x hα
  change ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
      ((idealPowerTower.{u, u} I M).map (homOfLE hmk).op)).hom x = 0
  rw [← hy]
  exact map_idealPowerTower_localCohomologyδ_eq_zero T I M (j - 1) j hji hmk y
    (hC k hmk hCk ⟨y, rfl⟩)

end Chase

/-! ### The eventual ranges of a tower of Artinian modules -/

/-- **The ranges of the transition maps of a tower of Artinian modules stabilize.** At each level
they form a descending chain of submodules of an Artinian module.

This is the range formulation that `Stacks.LocalCohomology.range_transitionMap_le_range_cone_π`
consumes. `Stacks.LocalCohomology.isMittagLeffler_forget_of_isArtinian` draws from the same
descending chain the set-level `CategoryTheory.Functor.IsMittagLeffler` of the underlying tower of
sets instead. -/
theorem exists_range_eq_of_isArtinian {R : Type u} [Ring R] {F : ℕᵒᵖ ⥤ ModuleCat.{u} R}
    (hF : ∀ n : ℕᵒᵖ, IsArtinian R (F.obj n)) (i : ℕ) :
    ∃ C : ℕ, ∃ hiC : i ≤ C, ∀ (k : ℕ) (hCk : C ≤ k),
      LinearMap.range (F.map (homOfLE (hiC.trans hCk)).op).hom =
        LinearMap.range (F.map (homOfLE hiC).op).hom := by
  have hstep : ∀ a b : ℕ, a ≤ b →
      LinearMap.range (F.map (homOfLE (show i ≤ i + b by omega)).op).hom ≤
        LinearMap.range (F.map (homOfLE (show i ≤ i + a by omega)).op).hom := by
    intro a b hab
    have hc : F.map (homOfLE (show i ≤ i + b by omega)).op =
        F.map (homOfLE (show i + a ≤ i + b by omega)).op ≫
          F.map (homOfLE (show i ≤ i + a by omega)).op := by
      rw [← F.map_comp]
      exact congrArg F.map (Subsingleton.elim _ _)
    rw [hc]
    exact LinearMap.range_comp_le_range _ _
  have _ := hF (op i)
  obtain ⟨c, hc⟩ := IsArtinian.monotone_stabilizes
    (⟨fun d => (LinearMap.range (F.map (homOfLE (show i ≤ i + d by omega)).op).hom :
        (Submodule R (F.obj (op i)))ᵒᵈ), fun a b hab => hstep a b hab⟩ :
      ℕ →o (Submodule R (F.obj (op i)))ᵒᵈ)
  refine ⟨i + c, by omega, fun k hCk => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, k = i + d := ⟨k - i, by omega⟩
  exact (hc d (by omega)).symm

/-! ### Part (1) of Tag 0EFY in the set-indexed model, from the limit comparison -/

omit [IsNoetherianRing A] in
/-- **The projections `H^i_T(M) ⟶ H^i_T(M/IⁿM)` are injective from some level on**, as soon as
`H^i_T(M)` is Artinian and the limit comparison of the canonical cone is invertible. That is
part (1) of [Stacks, Tag 0EFY] in degree `i`, in the set-indexed model.

The kernels of the projections form a descending chain in the Artinian module `H^i_T(M)`, so they
are constant from some level on; the constant value lies in every kernel, and the projections are
jointly injective, being the components of the invertible comparison to the limit. -/
theorem exists_forall_injective_localCohomologyAdicProjection_of_isIso
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A) (i : ℤ)
    (hart : IsArtinian A ((localCohomologyWithSupportInModuleFunctor.{u, u} A T i).obj M))
    (hiso : IsIso (limit.lift (localCohomologyAdicTower.{u, u} A T I i M)
      (localCohomologyAdicCone.{u, u} A T I i M))) :
    ∃ m₀ : ℕ, ∀ n : ℕ, m₀ ≤ n →
      Function.Injective ((localCohomologyAdicCone.{u, u} A T I i M).π.app (op n)).hom := by
  refine exists_forall_injective_of_isArtinian hart
    (fun n => (localCohomologyAdicCone.{u, u} A T I i M).π.app (op n))
    (fun n m h => (localCohomologyAdicCone.{u, u} A T I i M).w (homOfLE h).op) ?_
  intro x hx
  have hz : ∀ n : ℕᵒᵖ,
      (limit.π (localCohomologyAdicTower.{u, u} A T I i M) n).hom
          ((limit.lift (localCohomologyAdicTower.{u, u} A T I i M)
            (localCohomologyAdicCone.{u, u} A T I i M)).hom x) =
        (limit.π (localCohomologyAdicTower.{u, u} A T I i M) n).hom 0 := by
    intro n
    obtain ⟨p⟩ := n
    rw [map_zero]
    exact (ConcreteCategory.congr_hom
      (limit.lift_π (localCohomologyAdicCone.{u, u} A T I i M) (op p)) x).trans (hx p)
  have h0 : (limit.lift (localCohomologyAdicTower.{u, u} A T I i M)
      (localCohomologyAdicCone.{u, u} A T I i M)).hom x = 0 :=
    Limits.Concrete.limit_ext _ _ _ hz
  have := hiso
  exact (ConcreteCategory.bijective_of_isIso
    (limit.lift (localCohomologyAdicTower.{u, u} A T I i M)
      (localCohomologyAdicCone.{u, u} A T I i M))).1 (h0.trans (map_zero _).symm)

/-! ### The two assertions of Tag 0EFX, assembled -/

omit [IsNoetherianRing A] in
/-- **The pro-zero assertion of [Stacks, Tag 0EFX] in degree `i`**, from the Artinianness of the
terms and the invertibility of the limit comparison in degrees `i` and `i - 1`. -/
theorem exists_map_idealPowerTower_eq_zero_of_isArtinian_of_isIso
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A) (i : ℤ)
    (hart : IsArtinian A ((localCohomologyWithSupportInModuleFunctor.{u, u} A T i).obj M))
    (hartT : ∀ n : ℕᵒᵖ, IsArtinian A ((localCohomologyAdicTower.{u, u} A T I (i - 1) M).obj n))
    (hiso : IsIso (limit.lift (localCohomologyAdicTower.{u, u} A T I i M)
      (localCohomologyAdicCone.{u, u} A T I i M)))
    (hiso' : IsIso (limit.lift (localCohomologyAdicTower.{u, u} A T I (i - 1) M)
      (localCohomologyAdicCone.{u, u} A T I (i - 1) M)))
    (m : ℕ) :
    ∃ k : ℕ, ∃ h : m ≤ k,
      (localCohomologyWithSupportInModuleFunctor.{u, u} A T i).map
        ((idealPowerTower.{u, u} I M).map (homOfLE h).op) = 0 :=
  exists_map_idealPowerTower_eq_zero_of_injective_of_range_le T I M i m
    (exists_forall_injective_localCohomologyAdicProjection_of_isIso A T I M i hart hiso)
    (range_transitionMap_le_range_cone_π _ hiso' (exists_range_eq_of_isArtinian hartT) m)

omit [IsNoetherianRing A] in
/-- **The stable-image assertion of [Stacks, Tag 0EFX] in degree `j`**, from the Artinianness of
the terms and the invertibility of the limit comparison in degree `j - 1`. -/
theorem hasStableImageIdealPowerCohomology_of_isArtinian_of_isIso
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A) (j : ℤ) (m₀ : ℕ)
    (hartT : ∀ n : ℕᵒᵖ, IsArtinian A ((localCohomologyAdicTower.{u, u} A T I (j - 1) M).obj n))
    (hiso' : IsIso (limit.lift (localCohomologyAdicTower.{u, u} A T I (j - 1) M)
      (localCohomologyAdicCone.{u, u} A T I (j - 1) M))) :
    HasStableImageIdealPowerCohomology.{u, u} T I M j m₀ :=
  hasStableImageIdealPowerCohomology_of_range_le T I M j m₀ fun m =>
    range_transitionMap_le_range_cone_π _ hiso' (exists_range_eq_of_isArtinian hartT) m

end Stacks.LocalCohomology

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (S : BootstrapSituation.{u, u, u})

/-- At `T = {𝔪}` over a Noetherian local ring every term of the tower `{H^i_T(M/IⁿM)}` is
Artinian: each `M/IⁿM` is a finite module. -/
theorem isArtinian_localCohomologyAdicTower_closedPoint [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) (i : ℤ) (n : ℕᵒᵖ) :
    IsArtinian S.A ((localCohomologyAdicTower.{u, u} S.A S.T S.I i
      (ModuleCat.of S.A S.M)).obj n) := by
  rw [hT]
  let : Module.Finite S.A ((idealPowerQuotientTower.{u, u} S.I
    (ModuleCat.of S.A S.M)).obj n) := Module.Finite.quotient S.A _
  exact isArtinian_localCohomologyWithSupportIn_closedPoint S.A
    ((idealPowerQuotientTower.{u, u} S.I (ModuleCat.of S.A S.M)).obj n) i

/-- **Stacks Project, Tag 0EFX, the pro-zero assertion, at `T = {𝔪}`.** In Situation
[Stacks, Tag 0EFU] with `A` local and `T = {𝔪}`, the inverse system `{H^i_𝔪(IⁿM)}` is pro-zero
for every `i ≤ s`: for every `m` some transition map `H^i_𝔪(IᵏM) ⟶ H^i_𝔪(IᵐM)` vanishes.

This is the first paragraph of the source's proof, carried out at this locus. Its two inputs are
`isIso_limitLift_localCohomologyAdicCone_closedPoint`, which is part (4) of [Stacks, Tag 0EFY]
and the isomorphism assertion of [Stacks, Tag 0EFR] in the set-indexed model, and the
Artinianness of local cohomology at the closed point of a finite module, which supplies both
part (1) of [Stacks, Tag 0EFY] (through a descending chain of kernels) and the Mittag-Leffler
condition in the range form that the eventual-range lemma consumes. Nothing beyond the situation
is assumed; in particular `A` need not be `I`-adically complete.

The source's `T` is an arbitrary specialization-stable subset of `V(I)`. The general case is the
last paragraph of the source's proof: it needs the per-prime assertion **uniformly** in `𝔮 ∈ T`,
which the source gets by transporting the vanishing to the finite Ext modules
`Ext^j_A(IⁿM, ω_A^•)` by local duality and spreading it out. The statement proved here is exactly
the per-prime input of that argument at a single prime, since
`Stacks.Algebraization.BootstrapSituation.localize` and
`Stacks.Algebraization.BootstrapSituation.shrink` turn a situation and a `𝔮 ∈ T` into a situation
over `A_𝔮` with locus the closed point. The general case is
`Stacks.Algebraization.isProZeroIdealPowerCohomology`. -/
@[stacks 0EFX "the pro-zero assertion for i ≤ s at T = {𝔪} over a Noetherian local ring in \
Situation 0EFU"]
theorem exists_map_idealPowerTower_eq_zero_closedPoint [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) (i : ℤ) (hi : i ≤ S.s) (m : ℕ) :
    ∃ k : ℕ, ∃ h : m ≤ k,
      (localCohomologyWithSupportInModuleFunctor.{u, u} S.A S.T i).map
        ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M)).map (homOfLE h).op) = 0 := by
  have hart : IsArtinian S.A ((localCohomologyWithSupportInModuleFunctor.{u, u} S.A S.T i).obj
      (ModuleCat.of S.A S.M)) := by
    rw [hT]
    exact isArtinian_localCohomologyWithSupportIn_closedPoint S.A (ModuleCat.of S.A S.M) i
  exact exists_map_idealPowerTower_eq_zero_of_isArtinian_of_isIso S.A S.T S.I
    (ModuleCat.of S.A S.M) i hart
    (isArtinian_localCohomologyAdicTower_closedPoint S hT (i - 1))
    (isIso_limitLift_localCohomologyAdicCone_closedPoint S hT i hi)
    (isIso_limitLift_localCohomologyAdicCone_closedPoint S hT (i - 1) (by omega)) m

/-- **Stacks Project, Tag 0EFX, the stable-image assertion, at `T = {𝔪}`.** In Situation
[Stacks, Tag 0EFU] with `A` local and `T = {𝔪}`, the stable-image assertion of the tag holds in
degree `s + 1`, based at `m₀ = 0`: for every `m` there is a `c ≥ m` such that for `k ≥ c` the
image of `H^{s+1}_𝔪(IᵏM) ⟶ H^{s+1}_𝔪(IᵐM)` maps injectively to `H^{s+1}_𝔪(I⁰M)`.

Its single input is the invertibility of the limit comparison in degree `s` itself, which is
inside the range `i ≤ s` of `isIso_limitLift_localCohomologyAdicCone_closedPoint`; the
Artinianness of the terms turns it into the containment of the stable images in the image of
`H^s_𝔪(M)`, and the naturality of the connecting map of
`0 → IⁿM → M → M/IⁿM → 0` does the rest. Nothing beyond the situation is assumed.

As with the pro-zero assertion, the general specialization-stable `T` needs the uniformity in
`𝔮 ∈ T` of the source's last paragraph; see
`exists_map_idealPowerTower_eq_zero_closedPoint`. The general case is
`Stacks.Algebraization.exists_hasStableImageIdealPowerCohomology`. -/
@[stacks 0EFX "the stable-image assertion in degree s + 1 at T = {𝔪} over a Noetherian local \
ring in Situation 0EFU"]
theorem hasStableImageIdealPowerCohomology_closedPoint [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) :
    HasStableImageIdealPowerCohomology.{u, u} S.T S.I (ModuleCat.of S.A S.M) (S.s + 1) 0 := by
  have hiso' : IsIso (limit.lift
      (localCohomologyAdicTower.{u, u} S.A S.T S.I (S.s + 1 - 1) (ModuleCat.of S.A S.M))
      (localCohomologyAdicCone.{u, u} S.A S.T S.I (S.s + 1 - 1) (ModuleCat.of S.A S.M))) := by
    rw [show S.s + 1 - 1 = S.s from by omega]
    exact isIso_limitLift_localCohomologyAdicCone_closedPoint S hT S.s le_rfl
  exact hasStableImageIdealPowerCohomology_of_isArtinian_of_isIso S.A S.T S.I
    (ModuleCat.of S.A S.M) (S.s + 1) 0
    (isArtinian_localCohomologyAdicTower_closedPoint S hT (S.s + 1 - 1)) hiso'

end Stacks.Algebraization

end
