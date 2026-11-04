module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDerivedDualityCoherence
public import StacksFrontier.AlgebraicGeometry.Modules.OpenCoverAcyclic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.Homology.HomComplex.Evaluation.Iterated
import StacksCore.Tactic.StacksAttribute

/-!
# On a quasi-compact scheme, `R𝓗om_{𝒪_X}(-, K)` exchanges `D⁺_Coh(𝒪_X)` and `D⁻_Coh(𝒪_X)`

Let `X` be a locally Noetherian **quasi-compact** scheme and `K` a dualizing complex on it
([Stacks, Tag 0A87]). This file proves the boundedness half of the fourth assertion of
[Stacks, Tag 0A89]: the duality functor `D = R𝓗om_{𝒪_X}(-, K)` of
`Stacks.Duality.dualizingDerivedSheafHomFunctor` carries `D⁺_Coh(𝒪_X)` into `D⁻_Coh(𝒪_X)` and
`D⁻_Coh(𝒪_X)` into `D⁺_Coh(𝒪_X)`, hence carries `D^b_Coh(𝒪_X)` into itself.

## Main results

* `Stacks.Duality.exists_isLE_restrictSpec_derivedSheafHom` and
  `Stacks.Duality.exists_isGE_restrictSpec_derivedSheafHom` — the affine-local bounds: over
  `Spec Γ(X, U)`, `R𝓗om_{𝒪_X}(L, K)` is bounded above when `L` is bounded below, and bounded
  below when `L` is bounded above.
* `Stacks.Duality.isBoundedAbove_of_forall_isLE_restrictSpec` and
  `Stacks.Duality.isBoundedBelow_of_forall_isGE_restrictSpec` — affine-local bounds give a global
  bound on a quasi-compact scheme.
* `Stacks.Duality.derivedCategoryBMinus_isCoherent_dualizingDerivedSheafHom` and
  `Stacks.Duality.derivedCategoryBPlus_isCoherent_dualizingDerivedSheafHom` —
  **[Stacks, Tag 0A89]**, the two exchanges.
* `Stacks.Duality.derivedCategoryBBounded_isCoherent_dualizingDerivedSheafHom` —
  **[Stacks, Tag 0A89]**, `D` carries `D^b_Coh(𝒪_X)` into itself.

## The proof

Coherence is `Stacks.Duality.derivedCategoryB_isCoherent_dualizingDerivedSheafHom` and needs no
quasi-compactness. The bounds are where quasi-compactness enters, and they are read on the
**module** side, which [Stacks, Tag 0A88] now makes possible for an unbounded object of
`D_Coh`: over an affine open `U` the chain of transports of
`Stacks.Duality.isCoherent_homology_derivedSheafHom_of_isDualizingComplex` identifies

`R𝓗om_{𝒪_X}(L, K)|_{Spec Γ(X, U)}` with `(R Hom_A(M, ω))~`, `A = Γ(X, U)`,

for `M` a presentation of `L` there and `ω` the dualizing model of `K`. The two bound exchanges
over a ring, `StacksDraft.DerivedHom.derivedHom_isLE_of_isGE_of_injectiveAmplitude` and
`derivedHom_isGE_of_isLE_of_injectiveAmplitude`, then bound `R Hom_A(M, ω)` in terms of the
injective amplitude `[a, b]` of `ω`, and derived sheafification carries the bound over.

The bound so obtained is `b - p` resp. `a - p`, with `p` the bound on `L` — uniform in `U` — but
`a` and `b` are the injective amplitude of `ω` over `Γ(X, U)` and depend on `U`. That is exactly
why the assertion needs `X` quasi-compact: a finite affine cover, which
`TopologicalSpace.IsOpenCover.exists_finite_of_compactSpace` extracts from
`AlgebraicGeometry.iSup_affineOpens_eq_top`, has finitely many such bounds and so a maximum.
Vanishing of a cohomology sheaf then descends from the cover by
`Stacks.AlgebraicGeometry.Modules.isZero_of_isZero_restrictFunctor`.

## Implementation notes

The affine-local bounds are stated for the object restricted to `Spec Γ(X, U)` rather than to
`U`, because that is where the identification above lives; descending to `X` therefore needs
vanishing to be reflected along the restriction by the isomorphism `U ≅ Spec Γ(X, U)`, which is
`Stacks.Duality.isZero_of_isZero_restrictFunctor_of_isIso`, read off
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCompInvIso`.

Quasi-compactness is `[CompactSpace X]`, the spelling the surrounding development uses (for
instance `AlgebraicGeometry.isAmple_of_hasEventuallyVanishingH1_of_epi`).

The derived category is the standard model, at priority 10000, as in
`StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDerivedDualityCoherence`.

## Where the bounded anti-equivalence lives

[Stacks, Tag 0A89] asserts that `D` **induces an anti-equivalence**
`D^b_Coh(𝒪_X) ⟶ D^b_Coh(𝒪_X)`; what this file supplies is that `D` carries `D^b_Coh(𝒪_X)` into
itself, which is the `"preservation of bounded coherent objects"` fragment of the affine
decomposition of [Stacks, Tag 0A7C] and is what makes `D` a functor there. The anti-equivalence
follows formally from invertibility of the canonical morphism `id → D ∘ D` of
`Stacks.Duality.dualizingDerivedSheafHomBiduality`, and is
`Stacks.Duality.boundedCoherentDualizingDerivedSheafHom_isEquivalence` of
`StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDerivedDualityBiduality`.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A88](https://stacks.math.columbia.edu/tag/0A88)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

-- Standard model only: `Stacks.SheafOfModules.derivedSheafHom`,
--   `Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`,
--   `StacksDraft.DerivedHom.derivedHomAdjunction`.
attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

/-! ### Descending vanishing from a finite affine cover -/

/-- **Restriction along an isomorphism of schemes reflects vanishing**: for `g : A ⟶ B` an
isomorphism, an `𝒪_B`-module whose restriction along `g` is zero is zero. -/
theorem isZero_of_isZero_restrictFunctor_of_isIso {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g]
    {N : B.Modules} (h : IsZero ((Scheme.Modules.restrictFunctor g).obj N)) : IsZero N :=
  IsZero.of_iso ((Scheme.Modules.restrictFunctor (inv g)).map_isZero h)
    ((Scheme.Modules.restrictFunctorCompInvIso g).app N).symm

/-- Vanishing of a cohomology sheaf after restriction to `Spec Γ(X, U)` gives vanishing after
restriction to the affine open `U` itself. -/
theorem isZero_homology_restrict_of_isZero_homology_restrictSpec
    {X : Scheme.{u}} (U : X.affineOpens) (E : DerivedCategory X.Modules) (n : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (Spec Γ(X, (U : X.Opens))).Modules n).obj
      ((Scheme.Modules.restrictFunctor U.2.isoSpec.inv).mapDerivedCategory.obj
        ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).mapDerivedCategory.obj E)))) :
    IsZero ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).obj
      ((DerivedCategory.homologyFunctor X.Modules n).obj E)) := by
  refine IsZero.of_iso ?_ ((DerivedCategoryB.mapDerivedCategoryHomologyIso
    (Scheme.Modules.restrictFunctor (U : X.Opens).ι) n).app E).symm
  refine isZero_of_isZero_restrictFunctor_of_isIso U.2.isoSpec.inv ?_
  exact IsZero.of_iso h ((DerivedCategoryB.mapDerivedCategoryHomologyIso
    (Scheme.Modules.restrictFunctor U.2.isoSpec.inv) n).app _).symm

/-- **A global bound above from affine-local bounds, on a quasi-compact scheme**: if for every
affine open `U` of `X` the restriction of `E` to `Spec Γ(X, U)` is bounded above, then `E` is
bounded above. -/
theorem isBoundedAbove_of_forall_isLE_restrictSpec {X : Scheme.{u}} [CompactSpace X]
    (E : DerivedCategory X.Modules)
    (h : ∀ U : X.affineOpens, ∃ m : ℤ,
      ((Scheme.Modules.restrictFunctor U.2.isoSpec.inv).mapDerivedCategory.obj
        ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).mapDerivedCategory.obj E)).IsLE m) :
    DerivedCategoryB.IsBoundedAbove E := by
  obtain ⟨s, hs⟩ := (show TopologicalSpace.IsOpenCover (fun V : X.affineOpens => (V : X.Opens))
    from iSup_affineOpens_eq_top X).exists_finite_of_compactSpace
  choose m hm using h
  obtain ⟨N, hN⟩ := (s.image m).exists_le
  refine ⟨N, fun n hn => ?_⟩
  refine Stacks.AlgebraicGeometry.Modules.isZero_of_isZero_restrictFunctor
    (fun i : s => ((i : X.affineOpens) : X.Opens)) hs (fun i => ?_)
  refine isZero_homology_restrict_of_isZero_homology_restrictSpec (i : X.affineOpens) E n ?_
  have hmi : m (i : X.affineOpens) ≤ N := hN _ (Finset.mem_image_of_mem m i.2)
  have := hm (i : X.affineOpens)
  exact DerivedCategory.isZero_of_isLE _ (m (i : X.affineOpens)) n (by omega)

/-- **A global bound below from affine-local bounds, on a quasi-compact scheme**: if for every
affine open `U` of `X` the restriction of `E` to `Spec Γ(X, U)` is bounded below, then `E` is
bounded below. -/
theorem isBoundedBelow_of_forall_isGE_restrictSpec {X : Scheme.{u}} [CompactSpace X]
    (E : DerivedCategory X.Modules)
    (h : ∀ U : X.affineOpens, ∃ m : ℤ,
      ((Scheme.Modules.restrictFunctor U.2.isoSpec.inv).mapDerivedCategory.obj
        ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).mapDerivedCategory.obj E)).IsGE m) :
    DerivedCategoryB.IsBoundedBelow E := by
  obtain ⟨s, hs⟩ := (show TopologicalSpace.IsOpenCover (fun V : X.affineOpens => (V : X.Opens))
    from iSup_affineOpens_eq_top X).exists_finite_of_compactSpace
  choose m hm using h
  obtain ⟨N, hN⟩ := (s.image (fun U => -m U)).exists_le
  refine ⟨-N, fun n hn => ?_⟩
  refine Stacks.AlgebraicGeometry.Modules.isZero_of_isZero_restrictFunctor
    (fun i : s => ((i : X.affineOpens) : X.Opens)) hs (fun i => ?_)
  refine isZero_homology_restrict_of_isZero_homology_restrictSpec (i : X.affineOpens) E n ?_
  have hmi : -m (i : X.affineOpens) ≤ N :=
    hN _ (Finset.mem_image_of_mem (fun U => -m U) i.2)
  have := hm (i : X.affineOpens)
  exact DerivedCategory.isZero_of_isGE _ (m (i : X.affineOpens)) n (by omega)

/-! ### The affine-local bounds -/

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **Affine-local model of `R𝓗om_{𝒪_X}(L, K)`**: over an affine open `U`, the restriction of
`R𝓗om_{𝒪_X}(L, K)` to `Spec Γ(X, U)` is the derived sheafification of `R Hom_A(M, ω)`, for
`M` a module-side presentation of `L` (with the same bounds as `L`) and `ω` of finite injective
amplitude `[a, b]`. -/
private theorem exists_restrictSpec_derivedSheafHom_iso
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (L : DerivedCategory X.Modules)
    (hLcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent)
    (U : X.affineOpens) :
    ∃ (M ω : DerivedCategory (ModuleCat.{u} Γ(X, (U : X.Opens)))) (a b : ℤ),
      StacksDraft.InjectiveDimension.HasInjectiveAmplitude ω a b ∧
      (∀ p, L.IsGE p → M.IsGE p) ∧ (∀ p, L.IsLE p → M.IsLE p) ∧
      Nonempty (((tilde.functor Γ(X, (U : X.Opens))).mapDerivedCategory.obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction
          (R := (Γ(X, (U : X.Opens)) : Type u))).hom.obj (op M, ω))) ≅
        (Scheme.Modules.restrictFunctor U.2.isoSpec.inv).mapDerivedCategory.obj
          ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).mapDerivedCategory.obj
            (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L)).obj K))) := by
  let _ : IsAffine (U : X.Opens).toScheme := U.2
  have hR : IsNoetherianRing Γ(X, (U : X.Opens)) := IsLocallyNoetherian.component_noetherian U
  have _ : IsLocallyNoetherian (Spec Γ(X, (U : X.Opens))) := isLocallyNoetherian_Spec.mpr hR
  obtain ⟨ω, hω, ⟨eK⟩⟩ := exists_isDualizingComplex_iso_tilde_of_hasDualizingModelOn U.2 K
    (hK (U : X.Opens) U.2)
  obtain ⟨M, hM, ⟨eL⟩⟩ := exists_iso_tilde_of_isCoherent_homology Γ(X, (U : X.Opens))
    ((Scheme.Modules.restrictFunctor U.2.isoSpec.inv).mapDerivedCategory.obj
      ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).mapDerivedCategory.obj L))
    (fun i => isCoherent_homology_restrictFunctor U.2.isoSpec.inv _
      (fun j => isCoherent_homology_restrictFunctor (U : X.Opens).ι L hLcoh j) i)
  obtain ⟨a, b, hab⟩ := hω.finiteInjectiveDimension
  have hiso : IsIso (affineDerivedTildeHomComparison Γ(X, (U : X.Opens)) M ω) :=
    isIso_affineDerivedTildeHomComparison_of_finite_homology Γ(X, (U : X.Opens)) M ω hM
      hω.finiteInjectiveDimension
  have e2 := ((Stacks.SheafOfModules.derivedSheafHom
        (Spec Γ(X, (U : X.Opens))).sheaf).mapIso (Iso.op eL.symm)).app
      ((tilde.functor Γ(X, (U : X.Opens))).mapDerivedCategory.obj ω) ≪≫
    ((Stacks.SheafOfModules.derivedSheafHom (Spec Γ(X, (U : X.Opens))).sheaf).obj
      (op ((Scheme.Modules.restrictFunctor U.2.isoSpec.inv).mapDerivedCategory.obj
        ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).mapDerivedCategory.obj L)))).mapIso
          eK.symm
  refine ⟨M, ω, a, b, hab, fun p hLp => ?_, fun p hLp => ?_, ⟨asIso
    (affineDerivedTildeHomComparison Γ(X, (U : X.Opens)) M ω) ≪≫ e2 ≪≫
      (Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso U.2.isoSpec.inv
        ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).mapDerivedCategory.obj L)
        ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).mapDerivedCategory.obj K)).symm ≪≫
      (Scheme.Modules.restrictFunctor U.2.isoSpec.inv).mapDerivedCategory.mapIso
        (Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso (U : X.Opens) L K).symm⟩⟩
  · have hLp' : ((Scheme.Modules.restrictFunctor U.2.isoSpec.inv).mapDerivedCategory.obj
        ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).mapDerivedCategory.obj L)).IsGE p :=
      CategoryTheory.Functor.isGE_obj_mapDerivedCategory _ _ p
        (CategoryTheory.Functor.isGE_obj_mapDerivedCategory _ L p hLp)
    exact (DerivedCategory.isGE_iff _ p).2 fun i hi =>
      (StandardModel.isZero_homology_mapDerivedCategory_obj_iff _ M i).1 <|
        IsZero.of_iso ((DerivedCategory.isGE_iff _ p).1 hLp' i hi)
          ((DerivedCategory.homologyFunctor (Spec Γ(X, (U : X.Opens))).Modules i).mapIso eL)
  · have := Stacks.Homology.isLE_mapDerivedCategory_obj
      (Scheme.Modules.restrictFunctor (U : X.Opens).ι) L p
    have hLp' : ((Scheme.Modules.restrictFunctor U.2.isoSpec.inv).mapDerivedCategory.obj
        ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).mapDerivedCategory.obj L)).IsLE p :=
      Stacks.Homology.isLE_mapDerivedCategory_obj _ _ p
    exact (DerivedCategory.isLE_iff _ p).2 fun i hi =>
      (StandardModel.isZero_homology_mapDerivedCategory_obj_iff _ M i).1 <|
        IsZero.of_iso (DerivedCategory.isZero_of_isLE _ p i hi)
          ((DerivedCategory.homologyFunctor (Spec Γ(X, (U : X.Opens))).Modules i).mapIso eL)

/-- **Over an affine open, `R𝓗om_{𝒪_X}(L, K)` is bounded above when `L` is bounded below**: for
`K` a dualizing complex and `L ∈ D^{≥p}` with coherent cohomology sheaves, the restriction of
`R𝓗om_{𝒪_X}(L, K)` to `Spec Γ(X, U)` is in `D^{≤m}` for some `m`. -/
theorem exists_isLE_restrictSpec_derivedSheafHom
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (L : DerivedCategory X.Modules)
    (hLcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent)
    (p : ℤ) (hLp : L.IsGE p) (U : X.affineOpens) :
    ∃ m : ℤ, ((Scheme.Modules.restrictFunctor U.2.isoSpec.inv).mapDerivedCategory.obj
      ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).mapDerivedCategory.obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L)).obj K))).IsLE m := by
  obtain ⟨M, ω, a, b, hab, hMp, -, ⟨e⟩⟩ := exists_restrictSpec_derivedSheafHom_iso hK L hLcoh U
  have := StacksDraft.DerivedHom.derivedHom_isLE_of_isGE_of_injectiveAmplitude
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := (Γ(X, (U : X.Opens)) : Type u)))
    M ω p a b (hMp p hLp) hab
  have := Stacks.Homology.isLE_mapDerivedCategory_obj
    (tilde.functor Γ(X, (U : X.Opens)))
    ((StacksDraft.DerivedHom.derivedHomAdjunction
      (R := (Γ(X, (U : X.Opens)) : Type u))).hom.obj (op M, ω)) (b - p)
  exact ⟨b - p, DerivedCategory.TStructure.t.isLE_of_iso e (b - p)⟩

/-- **Over an affine open, `R𝓗om_{𝒪_X}(L, K)` is bounded below when `L` is bounded above**: for
`K` a dualizing complex and `L ∈ D^{≤p}` with coherent cohomology sheaves, the restriction of
`R𝓗om_{𝒪_X}(L, K)` to `Spec Γ(X, U)` is in `D^{≥m}` for some `m`. -/
theorem exists_isGE_restrictSpec_derivedSheafHom
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (L : DerivedCategory X.Modules)
    (hLcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent)
    (p : ℤ) (hLp : L.IsLE p) (U : X.affineOpens) :
    ∃ m : ℤ, ((Scheme.Modules.restrictFunctor U.2.isoSpec.inv).mapDerivedCategory.obj
      ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).mapDerivedCategory.obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L)).obj K))).IsGE m := by
  obtain ⟨M, ω, a, b, hab, -, hMp, ⟨e⟩⟩ := exists_restrictSpec_derivedSheafHom_iso hK L hLcoh U
  have := StacksDraft.DerivedHom.derivedHom_isGE_of_isLE_of_injectiveAmplitude
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := (Γ(X, (U : X.Opens)) : Type u)))
    M ω p a b (hMp p hLp) hab
  have := CategoryTheory.Functor.isGE_obj_mapDerivedCategory
    (tilde.functor Γ(X, (U : X.Opens))) _ (a - p) this
  exact ⟨a - p, DerivedCategory.TStructure.t.isGE_of_iso e (a - p)⟩

/-! ### Clause 4 of Tag 0A89 -/

/-- On a quasi-compact locally Noetherian scheme, `D = R𝓗om_{𝒪_X}(-, K)` carries `D⁺_Coh(𝒪_X)`
into `D⁻_Coh(𝒪_X)`, for `K` a dualizing complex. -/
@[stacks 0A89 "exchange of bounded below and bounded above"]
theorem derivedCategoryBMinus_isCoherent_dualizingDerivedSheafHom [CompactSpace X]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (L : DerivedCategory X.Modules)
    (hL : DerivedCategoryB.derivedCategoryBPlus (A := X.Modules) (isCoherentSheaf X) L) :
    DerivedCategoryB.derivedCategoryBMinus (A := X.Modules) (isCoherentSheaf X)
      ((dualizingDerivedSheafHomFunctor X K).obj (op L)) := by
  obtain ⟨p, hp⟩ := hL.1
  exact ⟨isBoundedAbove_of_forall_isLE_restrictSpec _
      (exists_isLE_restrictSpec_derivedSheafHom hK L hL.2 p
        ((DerivedCategory.isGE_iff L p).2 hp)),
    derivedCategoryB_isCoherent_dualizingDerivedSheafHom X hK L hL.2⟩

/-- On a quasi-compact locally Noetherian scheme, `D = R𝓗om_{𝒪_X}(-, K)` carries `D⁻_Coh(𝒪_X)`
into `D⁺_Coh(𝒪_X)`, for `K` a dualizing complex.

Together with `Stacks.Duality.derivedCategoryBMinus_isCoherent_dualizingDerivedSheafHom` this is
the assertion that `D` **exchanges** the two subcategories. -/
@[stacks 0A89 "exchange of bounded above and bounded below"]
theorem derivedCategoryBPlus_isCoherent_dualizingDerivedSheafHom [CompactSpace X]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (L : DerivedCategory X.Modules)
    (hL : DerivedCategoryB.derivedCategoryBMinus (A := X.Modules) (isCoherentSheaf X) L) :
    DerivedCategoryB.derivedCategoryBPlus (A := X.Modules) (isCoherentSheaf X)
      ((dualizingDerivedSheafHomFunctor X K).obj (op L)) := by
  obtain ⟨p, hp⟩ := hL.1
  exact ⟨isBoundedBelow_of_forall_isGE_restrictSpec _
      (exists_isGE_restrictSpec_derivedSheafHom hK L hL.2 p
        ((DerivedCategory.isLE_iff L p).2 hp)),
    derivedCategoryB_isCoherent_dualizingDerivedSheafHom X hK L hL.2⟩

/-- On a quasi-compact locally Noetherian scheme, `D = R𝓗om_{𝒪_X}(-, K)` carries
`D^b_Coh(𝒪_X)` into itself, for `K` a dualizing complex.

This is the preservation statement, the counterpart of the
`"preservation of bounded coherent objects"` fragment of the affine decomposition of
[Stacks, Tag 0A7C]; it is what makes `D` a functor on `D^b_Coh(𝒪_X)`, and the anti-equivalence
the tag asserts there is
`Stacks.Duality.boundedCoherentDualizingDerivedSheafHom_isEquivalence`. -/
@[stacks 0A89 "preservation of bounded coherent objects"]
theorem derivedCategoryBBounded_isCoherent_dualizingDerivedSheafHom [CompactSpace X]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (L : DerivedCategory X.Modules)
    (hL : DerivedCategoryB.derivedCategoryBBounded (A := X.Modules) (isCoherentSheaf X) L) :
    DerivedCategoryB.derivedCategoryBBounded (A := X.Modules) (isCoherentSheaf X)
      ((dualizingDerivedSheafHomFunctor X K).obj (op L)) :=
  ⟨⟨(derivedCategoryBPlus_isCoherent_dualizingDerivedSheafHom hK L ⟨hL.1.2, hL.2⟩).1,
      (derivedCategoryBMinus_isCoherent_dualizingDerivedSheafHom hK L ⟨hL.1.1, hL.2⟩).1⟩,
    derivedCategoryB_isCoherent_dualizingDerivedSheafHom X hK L hL.2⟩

end Stacks.Duality

end
