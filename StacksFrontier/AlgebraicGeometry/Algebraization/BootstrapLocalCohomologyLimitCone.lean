module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalCohomologyLimit
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CechCompletionUnit
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantConsequences
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian

/-!
# Stacks 0EFR as a limit cone, for an `I`-adically complete local ring

In the bootstrap situation of [Stacks, Tag 0EFU] with `A` local and `T = {𝔪}`, [Stacks, Tag
0EFR] asserts that `Hⁱ_𝔪(M) ⟶ lim Hⁱ_𝔪(M/IⁿM)` is an isomorphism for `i ≤ s`, the map being the
one induced by the quotient maps `M ⟶ M/IⁿM`. The library's registration,
`Stacks.Algebraization.isIso_localCohomologyToAdicQuotientLimit_of_isAdicComplete`, is about the
arrow `Stacks.Algebraization.localCohomologyToAdicQuotientLimit`, whose second factor is defined
from an existentially quantified presentation and is not known to be the canonical map. This
file proves the statement about the canonical map, as `IsLimit` of the cone
`Stacks.LocalCohomology.Bootstrap.cone` (the form in which Theorem 0EIE consumes it), when `A`
is `I`-adically complete.

The two displays of the source's proof are used as they stand: the first,
`Hⁱ_𝔪(M) ≅ Hⁱ(RΓ_𝔪(M)^∧)` for `i ≤ s` through the completion unit, is
`Stacks.Algebraization.isIso_homology_localCohomologyToCompletedLocalCohomology_maximalIdeal`;
the second, `Hⁱ(RΓ_𝔪(M)^∧) ≅ lim Hⁱ_𝔪(M/IⁿM)`, now through the canonical maps, comes from part
(1) of [Stacks, Tag 0EEW] with its projections
(`Dualizing.isDerivedLimitWithProjections_completedLocalCohomologyProjection_of_finite`) and
the Milnor sequence of a derived limit with specified projections
(`DerivedCategory.exists_isIso_homology_of_isDerivedLimitWithProjections`), whose `R¹lim` term
vanishes because the modules `H^{i-1}_𝔪(M/IⁿM)` are Artinian. The supported-sections model of
local cohomology used by the cone is matched with the coreflection model by the natural
comparison `Stacks.LocalCohomology.compareSectionsWithSupportLocalCohomology`, an isomorphism
over a Noetherian ring.

None of the statements here carries a Stacks registration: they are prerequisites of
Theorem 0EIE.

## Main results

* `DerivedCategory.exists_isIso_homology_of_isDerivedLimitWithProjections` — the Milnor
  comparison through specified projections, when the `R¹lim` term vanishes.
* `Stacks.Algebraization.nonempty_isLimit_mapCone_localCohomologyDerived` — the limit
  identification in the coreflection model, given the first display of the proof.
* `Stacks.Algebraization.nonempty_isLimit_cone_of_isAdicComplete` — Stacks 0EFR as a limit cone,
  for `I`-adically complete `A`.

## References

* [Stacks Project, Tag 0EFR](https://stacks.math.columbia.edu/tag/0EFR)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0DXJ](https://stacks.math.columbia.edu/tag/0DXJ)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated IsLocalRing Opposite

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace DerivedCategory

variable {A : Type u} [Ring A]

/-- **The Milnor comparison for a derived limit with specified projections.** If `K` is a
derived limit of a tower `F` in `D(A)` with projections `pₙ`, and the system `H^{r-1}(Fₙ)` is
Mittag-Leffler, then the maps `Hʳ(pₙ)` exhibit `Hʳ(K)` as the inverse limit of the `Hʳ(Fₙ)`. -/
theorem exists_isIso_homology_of_isDerivedLimitWithProjections
    (F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A)) (K : DerivedCategory (ModuleCat.{u} A))
    (p : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩)
    (h : NoetherianAdicCompletion.IsDerivedLimitWithProjections F K p) (r : ℤ)
    (hML : IsMittagLefflerCategorical (F ⋙ homologyFunctor (ModuleCat.{u} A) (r - 1))) :
    ∃ q : (homologyFunctor (ModuleCat.{u} A) r).obj K ⟶
        limit (F ⋙ homologyFunctor (ModuleCat.{u} A) r),
      IsIso q ∧ ∀ n : ℕ, q ≫ limit.π (F ⋙ homologyFunctor (ModuleCat.{u} A) r) (op n) =
        (homologyFunctor (ModuleCat.{u} A) r).map (p n) := by
  let H := homologyFunctor (ModuleCat.{u} A) r
  obtain ⟨a, b, hT, hdata⟩ := isDerivedLimit_homology_shortExact F K h.isDerivedLimit
  obtain ⟨e, incl, q, w, -, -, hq, hshort⟩ := hdata r
  have : Mono q := hshort.exact.mono_g (((Preadditive.epi_iff_isZero_cokernel _).1
    (Stacks.Algebraization.epi_milnorDifference_of_isMittagLefflerCategorical _ hML)).eq_of_src _ _)
  have : Epi q := hshort.epi_g
  have hqiso : IsIso q := isIso_of_mono_of_epi q
  obtain ⟨δ, hδ⟩ := h
  obtain ⟨α, hα₁, hα₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hδ hT (𝟙 _) (𝟙 _)
    (by simp)
  let φ : Triangle.mk (Pi.lift p) _ δ ⟶ Triangle.mk a _ b :=
    { hom₁ := α
      hom₂ := 𝟙 _
      hom₃ := 𝟙 _
      comm₁ := by simpa using hα₁
      comm₂ := by simp
      comm₃ := by simpa using hα₃ }
  have hαiso : IsIso α :=
    isIso₁_of_isIso₂₃ φ hδ hT (by dsimp [φ]; infer_instance) (by dsimp [φ]; infer_instance)
  refine ⟨H.map α ≫ q, inferInstance, fun n ↦ ?_⟩
  rw [Category.assoc, hq, ← H.map_comp, ← H.map_comp]
  congr 1
  have h₁ : Pi.lift p ≫ 𝟙 _ = α ≫ a := hα₁
  rw [Category.comp_id] at h₁
  rw [← Category.assoc, ← h₁, Pi.lift_π]

end DerivedCategory

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The tower `n ↦ M/IⁿM` of `Stacks.LocalCohomology.idealPowerQuotientTower` is the tower
`AlgebraicGeometry.ProEtale.adicQuotientModuleSystem` of Tag 0EEW: the two have the same terms
and the same transition maps. -/
def idealPowerQuotientTowerIso (I : Ideal A) (M : ModuleCat.{u} A) :
    idealPowerQuotientTower.{u, u} I M ≅
      AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro m n g
    have h : n.unop ≤ m.unop := leOfHom g.unop
    have hg : g = (homOfLE h).op := Subsingleton.elim _ _
    subst hg
    rw [Dualizing.adicQuotientModuleSystem_map A I M h]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    rfl)

/-- **Stacks Tag 0EFR, the limit identification, in the coreflection model.** For a finite module
`M` over a Noetherian local ring `A` with maximal ideal `𝔪`, and a degree `i` in which the
completion unit `RΓ_𝔪(M) ⟶ RΓ_𝔪(M)^∧` induces an isomorphism on cohomology, the maps
`Hⁱ_𝔪(M) ⟶ Hⁱ_𝔪(M/IⁿM)` induced by the quotient maps exhibit `Hⁱ_𝔪(M)` as the inverse limit of
the `Hⁱ_𝔪(M/IⁿM)`.

By Stacks 0EEW part (1) with its projections,
`Dualizing.isDerivedLimitWithProjections_completedLocalCohomologyProjection_of_finite`, the
completion is the derived limit of `RΓ_𝔪(M/IⁿM)` with projections lifting these maps; the Milnor
sequence of that derived limit has vanishing `R¹lim` term because `{H^{i-1}_𝔪(M/IⁿM)}` is
Mittag-Leffler, the modules being Artinian; so `Hⁱ(RΓ_𝔪(M)^∧) ⟶ lim Hⁱ_𝔪(M/IⁿM)` is bijective,
and precomposing with the invertible `Hⁱ` of the unit gives the cone map. -/
theorem nonempty_isLimit_mapCone_localCohomologyDerived [IsLocalRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M] (i : ℤ)
    (hunit : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((Dualizing.derivedCompletionReflection A I I.fg_of_isNoetherianRing).2.unit.app
        ((localCohomologyDerived A (maximalIdeal A) (Ideal.fg_of_isNoetherianRing _)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))))) :
    Nonempty (IsLimit ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
      localCohomologyDerived A (maximalIdeal A) (Ideal.fg_of_isNoetherianRing _) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapCone
          (idealPowerQuotientCone.{u, u} I M))) := by
  let hm : (maximalIdeal A).FG := Ideal.fg_of_isNoetherianRing _
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
  let Φ := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
    localCohomologyDerived A (maximalIdeal A) hm ⋙ H
  let p := Dualizing.completedLocalCohomologyProjection A I (maximalIdeal A)
    I.fg_of_isNoetherianRing hm M
  have hp := Dualizing.isDerivedLimitWithProjections_completedLocalCohomologyProjection_of_finite
    A I (maximalIdeal A) I.fg_of_isNoetherianRing hm M
  have hpunit := Dualizing.completedLocalCohomologyUnit_comp_projection A I (maximalIdeal A)
    I.fg_of_isNoetherianRing hm M
  obtain ⟨q, hq, hqπ⟩ := DerivedCategory.exists_isIso_homology_of_isDerivedLimitWithProjections _ _
    p hp i (isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology A I M (i - 1))
  let F := Dualizing.adicQuotientLocalCohomologySystem A I (maximalIdeal A) hm M ⋙ H
  let X := (localCohomologyDerived A (maximalIdeal A) hm).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)
  let un : X ⟶
      Dualizing.completedLocalCohomology A I (maximalIdeal A) I.fg_of_isNoetherianRing hm M :=
    (Dualizing.derivedCompletionReflection A I I.fg_of_isNoetherianRing).2.unit.app X
  have hun : IsIso (H.map un) := hunit
  let e : idealPowerQuotientTower.{u, u} I M ⋙ Φ ≅ F :=
    Functor.isoWhiskerRight (idealPowerQuotientTowerIso I M) Φ
  let c := (Cones.postcompose e.hom).obj (Φ.mapCone (idealPowerQuotientCone.{u, u} I M))
  let ℓ : c.pt ⟶ limit F := H.map un ≫ q
  have hℓ : IsIso ℓ := @IsIso.comp_isIso _ _ _ _ _ _ _ hun hq
  have hlift : limit.lift F c = ℓ := by
    apply limit.hom_ext
    rintro ⟨n⟩
    rw [limit.lift_π]
    have h1 : ℓ ≫ limit.π F (op n) = H.map un ≫ H.map (p n) :=
      (Category.assoc _ _ _).trans (congrArg (H.map un ≫ ·) (hqπ n))
    have h3 : H.map un ≫ H.map (p n) = H.map ((localCohomologyDerived A (maximalIdeal A) hm).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
          (ModuleCat.ofHom (I ^ n • ⊤ : Submodule A M).mkQ))) :=
      (H.map_comp _ _).symm.trans (congrArg H.map (hpunit n))
    have h2 : c.π.app (op n) = H.map ((localCohomologyDerived A (maximalIdeal A) hm).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
          (ModuleCat.ofHom (I ^ n • ⊤ : Submodule A M).mkQ))) := by
      show Φ.map ((idealPowerQuotientCone.{u, u} I M).π.app (op n)) ≫ Φ.map (𝟙 _) = _
      rw [Φ.map_id, Category.comp_id]
      rfl
    exact h2.trans (h3.symm.trans h1.symm)
  have : IsIso (limit.lift F c) := hlift ▸ hℓ
  have : IsIso ((limit.isLimit F).lift c) := this
  exact ⟨(IsLimit.postcomposeHomEquiv e _).1 (IsLimit.ofPointIso (t := c) (limit.isLimit F))⟩

/-- **Stacks Tag 0EFR, the limit identification, in the form of a limit cone.** In the bootstrap
situation of Stacks 0EFU with `A` local, `I`-adically complete and `T = {𝔪}`, for every `i ≤ s`
the cone `Hⁱ_T(M) ⟶ Hⁱ_T(M/IⁿM)` given by `H^i_T` of the quotient maps `M ⟶ M/IⁿM` is a limit
cone: `Hⁱ_𝔪(M) = lim Hⁱ_𝔪(M/IⁿM)` through the canonical maps.

This is the source's proof. By the first display of the proof
(`Stacks.Algebraization.isIso_homology_localCohomologyToCompletedLocalCohomology_maximalIdeal`,
from Stacks 0DXP and Stacks 0EFQ) the completion unit `RΓ_𝔪(M) ⟶ RΓ_𝔪(M)^∧` is an isomorphism
on `Hⁱ` for `i ≤ s`, and the second display, `Hⁱ(RΓ_𝔪(M)^∧) = lim Hⁱ_𝔪(M/IⁿM)`, holds through
the maps induced by the quotient maps by
`Stacks.Algebraization.nonempty_isLimit_mapCone_localCohomologyDerived`. The supported-sections
model of `Hⁱ_T` used by the cone agrees with the coreflection model naturally in the module over
a Noetherian ring (Stacks 0955), which transports the limit cone. -/
theorem nonempty_isLimit_cone_of_isAdicComplete
    (S : BootstrapSituation.{u, u, u}) [IsLocalRing S.A] [IsAdicComplete S.I S.A]
    (hT : S.T = {IsLocalRing.closedPoint S.A}) (i : ℤ) (hi : i ≤ S.s) :
    Nonempty (IsLimit (Stacks.LocalCohomology.Bootstrap.cone.{u, u} S i)) := by
  let hm : (maximalIdeal S.A).FG := Ideal.fg_of_isNoetherianRing _
  let M := ModuleCat.of S.A S.M
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i
  let X := (localCohomologyDerived S.A (maximalIdeal S.A) hm).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj M)
  have hcomp := isIso_homology_localCohomologyToCompletedLocalCohomology_maximalIdeal S hT i hi
  have hunit : IsIso (H.map ((Dualizing.derivedCompletionReflection S.A S.I
      S.I.fg_of_isNoetherianRing).2.unit.app X)) := by
    let sh := completedLocalCohomologyShrinkIso S.A S.I (maximalIdeal S.A) (maximalIdeal S.A)
      S.I.fg_of_isNoetherianRing hm hm M rfl
    have h : H.map ((Dualizing.derivedCompletionReflection S.A S.I
        S.I.fg_of_isNoetherianRing).2.unit.app X) =
        H.map (localCohomologyToCompletedLocalCohomology S.A S.I (maximalIdeal S.A)
          (maximalIdeal S.A) S.I.fg_of_isNoetherianRing hm hm M rfl) ≫ H.map sh.inv := by
      rw [← H.map_comp]
      congr 1
      let un : X ⟶ Dualizing.completedLocalCohomology S.A S.I (maximalIdeal S.A)
          S.I.fg_of_isNoetherianRing hm M :=
        (Dualizing.derivedCompletionReflection S.A S.I S.I.fg_of_isNoetherianRing).2.unit.app X
      exact ((Category.assoc un sh.hom sh.inv).trans
        ((congrArg (un ≫ ·) sh.hom_inv_id).trans (Category.comp_id un))).symm
    rw [h]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hcomp (H.mapIso sh.symm).isIso_hom
  obtain ⟨hlim⟩ := nonempty_isLimit_mapCone_localCohomologyDerived S.I M i hunit
  have hT' : S.T = PrimeSpectrum.zeroLocus ((maximalIdeal S.A : Ideal S.A) : Set S.A) := by
    rw [hT, zeroLocus_maximalIdeal]
  have hiso : IsIso (compareSectionsWithSupportLocalCohomology.{u, u} S.A (maximalIdeal S.A) hm) :=
    isIso_compareSectionsWithSupportLocalCohomology.{u, u} S.A (maximalIdeal S.A) hm
  let β : DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0 ⋙
      localCohomologyDerived S.A (maximalIdeal S.A) hm ⋙ H ≅
        localCohomologyWithSupportInModuleFunctor.{u, u} S.A
          (PrimeSpectrum.zeroLocus ((maximalIdeal S.A : Ideal S.A) : Set S.A)) i :=
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (asIso (compareSectionsWithSupportLocalCohomology.{u, u} S.A (maximalIdeal S.A) hm)).symm H)
  have key : ∀ T : Set (PrimeSpectrum S.A),
      T = PrimeSpectrum.zeroLocus ((maximalIdeal S.A : Ideal S.A) : Set S.A) →
        Nonempty (IsLimit (localCohomologyAdicCone.{u, u} S.A T S.I i M)) := by
    rintro T rfl
    exact ⟨IsLimit.mapConeEquiv β hlim⟩
  exact key S.T hT'

end Stacks.Algebraization
