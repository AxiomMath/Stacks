module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosedImmersionCoherence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineCoherentDerivedHom
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHomBifunctor
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictLocality
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness

/-!
# Coherence of the derived internal Hom on a locally Noetherian scheme, and Tag 0A79

Let `X` be a locally Noetherian scheme. [Stacks, Tag 0D0C] says that the derived internal Hom
`R𝓗om_{𝒪_X}(K, L)` of an object `K` of `D⁻_Coh(𝒪_X)` and an object `L` of `D⁺_Coh(𝒪_X)` lies in
`D⁺_Coh(𝒪_X)`. This file proves that, and then deduces [Stacks, Tag 0A79]: for a closed immersion
`i : Z ⟶ X` into a locally Noetherian scheme, `R ℰom(𝒪_Z, -)` carries `D⁺_Coh(𝒪_X)` into
`D⁺_Coh(𝒪_Z)`.

## The two arguments

**Tag 0D0C.** Boundedness below of `R𝓗om_{𝒪_X}(K, L)` is
`Stacks.SheafOfModules.isBoundedBelow_derivedSheafHom`, which needs only the two cohomological
bounds and no coherence. Coherence of the cohomology sheaves is local on `X`
(`AlgebraicGeometry.Modules.isCoherent_of_restrict`), so it suffices to prove it after restricting
to an affine open `U`; the derived internal Hom commutes with that restriction by
[Stacks, Tag 08DL] in the form `Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`, and
with the transport along `U.isoSpec` by `Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso`.
On `Spec R` with `R` Noetherian the two arguments are derived sheafifications of objects of
`D⁻_Coh(R)` and `D⁺_Coh(R)` — this is [Stacks, Tag 06Z0], in the form
`AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`, together with the reflection of
finiteness of a cohomology module out of coherence of the associated cohomology sheaf — and there
the statement is `AlgebraicGeometry.derivedCategoryBPlus_isCoherent_affineDerivedSheafHom`.

**Tag 0A79.** Derived pushforward along the closed immersion turns `R ℰom(𝒪_Z, K)` into
`R𝓗om_{𝒪_X}(Ri_*𝒪_Z, K)` by [Stacks, Tag 0A77], in the bifunctor form
`derivedSheafHomExactSupportPushforwardNatIso`; `Ri_*𝒪_Z` is the coherent module `i_*𝒪_Z` in degree
zero, hence an object of `D⁻_Coh(𝒪_X)`, so Tag 0D0C makes the cohomology sheaves of that derived
internal Hom coherent. Pushforward along `i` is exact, so it commutes with taking cohomology, and
coherence descends along it by
`Stacks.AlgebraicGeometry.ClosedImmersionCoherence.isCoherent_pushforward_iff` once the cohomology
sheaf is known to be quasi-coherent, which is part (1) of [Stacks, Tag 0A78]. Boundedness below is
`AlgebraicGeometry.Scheme.isBoundedBelow_derivedSheafHomExactSupport_of_isCoherent`.

## Main results

* `AlgebraicGeometry.exists_derivedCategoryBMinus_finite_iso_tilde` and
  `AlgebraicGeometry.exists_derivedCategoryBPlus_finite_iso_tilde` — an object of
  `D⁻_Coh(𝒪_{Spec R})` resp. `D⁺_Coh(𝒪_{Spec R})` is the derived sheafification of an object of
  `D⁻_Coh(R)` resp. `D⁺_Coh(R)`.
* `AlgebraicGeometry.isCoherent_restrict_of_isOpenImmersion`,
  `AlgebraicGeometry.derivedCategoryBMinus_isCoherent_restrictFunctor_mapDerivedCategory` and
  `AlgebraicGeometry.derivedCategoryBPlus_isCoherent_restrictFunctor_mapDerivedCategory` —
  coherence, `D⁻_Coh` and `D⁺_Coh` pass to the restriction along an open immersion.
* `AlgebraicGeometry.isCoherent_homology_derivedSheafHom_of_isAffine` and
  `AlgebraicGeometry.isCoherent_homology_derivedSheafHom` — the coherence clause of
  [Stacks, Tag 0D0C] on an affine scheme and on an arbitrary locally Noetherian scheme.
* `AlgebraicGeometry.derivedCategoryBPlus_isCoherent_derivedSheafHom` — **[Stacks, Tag 0D0C]**.
* `AlgebraicGeometry.derivedSheafHomExactSupport_mem_derivedCategoryBPlus_coherent` —
  **[Stacks, Tag 0A79]**.

## Implementation notes

**Which coherence predicate.** The repository carries two coherence predicates with the same two
fields, the root `SheafOfModules.IsCoherent` of [Stacks, Tag 01BW] and
`Stacks.SheafOfModules.IsCoherent`; they are identified by
`AlgebraicGeometry.CoherentAbelian.isCoherent_iff_stacksIsCoherent`. Statements about a single
module are made with the root predicate, which is what
`Stacks.AlgebraicGeometry.ClosedImmersionCoherence.isCoherent_pushforward_iff` and
`AlgebraicGeometry.Modules.isCoherent_of_restrict` consume; the two packaged `D⁺_Coh` statements
carrying a `@[stacks]` attribute use the named object property
`Stacks.SheafOfModules.coherentModules`, which is the spelling the surrounding development —
`AlgebraicGeometry.Scheme.isBoundedBelow_derivedSheafHomExactSupport_of_isCoherent` and the affine
case of [Stacks, Tag 0A79] — is stated at.

That is not cosmetic. `AlgebraicGeometry.Scheme.Modules` is a semireducible `def`, and
`DerivedCategoryB.derivedCategoryBPlus` takes its ambient category as an implicit argument
determined by the object property; writing the property as the lambda
`fun M : Y.Modules => M.IsCoherent` therefore pins that argument to `Y.Modules`, and instance
synthesis then fails to see the `Abelian` instance through the `def` when the object being tested
is produced by `Stacks.SheafOfModules.derivedSheafHom`, whose values live in the
`StructureSheafModules` spelling. The named property `coherentModules Y.ringCatSheaf` does not have
that problem. This is the same three-spellings hazard recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/ExactSupportQuasicoherent.lean`.

**Why the derived model is pinned with priority.** The affine inputs are stated at
`CategoryTheory.HasDerivedCategory.standard` and the import closure installs the locally small
model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` as a *global* instance, so the
local attribute below carries priority `10000`, as
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean` requires of its
importers.

## References

* [Stacks Project, Tag 0A79](https://stacks.math.columbia.edu/tag/0A79)
* [Stacks Project, Tag 0D0C](https://stacks.math.columbia.edu/tag/0D0C)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u})

/-- Derived sheafification preserves and reflects cohomological boundedness above. -/
theorem isBoundedAbove_tilde_mapDerivedCategory_obj_iff (M : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategoryB.IsBoundedAbove ((tilde.functor R).mapDerivedCategory.obj M) ↔
      DerivedCategoryB.IsBoundedAbove M :=
  ⟨fun ⟨n, hn⟩ => ⟨n, fun i hi =>
      (StandardModel.isZero_homology_mapDerivedCategory_obj_iff R M i).1 (hn i hi)⟩,
    fun ⟨n, hn⟩ => ⟨n, fun i hi =>
      (StandardModel.isZero_homology_mapDerivedCategory_obj_iff R M i).2 (hn i hi)⟩⟩

/-- A cohomology module of `M` is finite as soon as the corresponding cohomology sheaf of `M̃` is
coherent. -/
theorem finite_homology_of_isCoherent_homology_tilde (M : DerivedCategory (ModuleCat.{u} R))
    (n : ℤ)
    (h : ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        ((tilde.functor R).mapDerivedCategory.obj M)).IsCoherent) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M) := by
  have hft : ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      ((tilde.functor R).mapDerivedCategory.obj M)).IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).2
  have hsrc : (((tilde.functor R).mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor (Spec R).Modules n).obj M).IsFiniteType := hft
  have hft' : ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n ⋙
      tilde.functor R).obj M).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (((tilde.functor R).mapDerivedCategoryHomologyIso n).app M)
  exact (tilde_isFiniteType_iff _).mp hft'

/-- Coherence is invariant under isomorphism, for the root predicate. -/
theorem isCoherent_of_modulesIso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G)
    (h : F.IsCoherent) : G.IsCoherent :=
  CoherentAbelian.isCoherent_of_stacksIsCoherent
    ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).prop_of_iso e
      (CoherentAbelian.isCoherent_iff_stacksIsCoherent.mp h))

/-- The cohomology sheaves of a complex with coherent cohomology sheaves are quasi-coherent. -/
private theorem isQuasicoherent_homology_of_isCoherent {X : Scheme.{u}}
    (E : DerivedCategory X.Modules)
    (hE : ∀ n, ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsCoherent) (n : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent :=
  have := hE n
  (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1

/-- A complex of `R`-modules whose derived sheafification is isomorphic to a coherent complex
has finite cohomology modules. -/
private theorem finite_homology_of_iso_tilde (M : DerivedCategory (ModuleCat.{u} R))
    (E : DerivedCategory (Spec R).Modules) (e : (tilde.functor R).mapDerivedCategory.obj M ≅ E)
    (hE : ∀ n, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E).IsCoherent) (n : ℤ) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M) :=
  finite_homology_of_isCoherent_homology_tilde R M n
    (isCoherent_of_modulesIso ((DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso e).symm
      (hE n))

/-- An object of `D⁻_Coh(𝒪_{Spec R})` is the derived sheafification of an object of `D⁻_Coh(R)`. -/
theorem exists_derivedCategoryBMinus_finite_iso_tilde (E : DerivedCategory (Spec R).Modules)
    (hE : DerivedCategoryB.derivedCategoryBMinus
      (fun M : (Spec R).Modules => M.IsCoherent) E) :
    ∃ M : DerivedCategory (ModuleCat.{u} R),
      DerivedCategoryB.derivedCategoryBMinus (fun N : ModuleCat.{u} R => Module.Finite R N) M ∧
        Nonempty ((tilde.functor R).mapDerivedCategory.obj M ≅ E) := by
  obtain ⟨M, ⟨e⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R E
    (isQuasicoherent_homology_of_isCoherent E hE.2)
  exact ⟨M, ⟨(isBoundedAbove_tilde_mapDerivedCategory_obj_iff R M).1
    (DerivedCategoryB.isBoundedAbove_of_iso e.symm hE.1),
      finite_homology_of_iso_tilde R M E e hE.2⟩, ⟨e⟩⟩

/-- An object of `D⁺_Coh(𝒪_{Spec R})` is the derived sheafification of an object of `D⁺_Coh(R)`. -/
theorem exists_derivedCategoryBPlus_finite_iso_tilde (E : DerivedCategory (Spec R).Modules)
    (hE : DerivedCategoryB.derivedCategoryBPlus
      (fun M : (Spec R).Modules => M.IsCoherent) E) :
    ∃ M : DerivedCategory (ModuleCat.{u} R),
      DerivedCategoryB.derivedCategoryBPlus (fun N : ModuleCat.{u} R => Module.Finite R N) M ∧
        Nonempty ((tilde.functor R).mapDerivedCategory.obj M ≅ E) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := StandardModel.exists_isBoundedBelow_iso_mapDerivedCategory R E
    ⟨hE.1, isQuasicoherent_homology_of_isCoherent E hE.2⟩
  exact ⟨M, ⟨hM, finite_homology_of_iso_tilde R M E e hE.2⟩, ⟨e⟩⟩

/-! ### Restriction along an open immersion -/

/-- **Coherence passes to the restriction along an open immersion.** A coherent module is
quasi-coherent of finite type, both of which restrict, and on the locally Noetherian source the
two give coherence back ([Stacks, Tag 01XZ]). -/
theorem isCoherent_restrict_of_isOpenImmersion {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] [IsLocallyNoetherian X] (F : Y.Modules) (hF : F.IsCoherent) :
    ((Scheme.Modules.restrictFunctor g).obj F).IsCoherent := by
  have hqf := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have := hqf.1
  have := hqf.2
  have h2 : ((Scheme.Modules.restrictFunctor g).obj F).IsFiniteType :=
    AlgebraicGeometry.isFiniteType_restrict g F
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- Restriction along an open immersion preserves the vanishing of a cohomology sheaf. -/
private theorem isZero_homology_restrictFunctor_mapDerivedCategory {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsOpenImmersion g] (K : DerivedCategory Y.Modules) (m : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor Y.Modules m).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules m).obj
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj K)) :=
  ((Scheme.Modules.restrictFunctor g).map_isZero h).of_iso
    ((DerivedCategoryB.mapDerivedCategoryHomologyIso (Scheme.Modules.restrictFunctor g) m).app K)

/-- Restriction along an open immersion preserves coherence of a cohomology sheaf. -/
private theorem isCoherent_homology_restrictFunctor_mapDerivedCategory {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsOpenImmersion g] [IsLocallyNoetherian X] (K : DerivedCategory Y.Modules)
    (n : ℤ) (h : ((DerivedCategory.homologyFunctor Y.Modules n).obj K).IsCoherent) :
    ((DerivedCategory.homologyFunctor X.Modules n).obj
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj K)).IsCoherent :=
  isCoherent_of_modulesIso ((DerivedCategoryB.mapDerivedCategoryHomologyIso
    (Scheme.Modules.restrictFunctor g) n).app K).symm
    (isCoherent_restrict_of_isOpenImmersion g _ h)

/-- Restriction along an open immersion of schemes carries `D⁻_Coh` into `D⁻_Coh`. -/
theorem derivedCategoryBMinus_isCoherent_restrictFunctor_mapDerivedCategory
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (K : DerivedCategory Y.Modules)
    (hK : DerivedCategoryB.derivedCategoryBMinus
      (fun M : Y.Modules => M.IsCoherent) K) :
    DerivedCategoryB.derivedCategoryBMinus
      (fun M : X.Modules => M.IsCoherent)
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj K) := by
  obtain ⟨n₀, hn₀⟩ := hK.1
  exact ⟨⟨n₀, fun m hm => isZero_homology_restrictFunctor_mapDerivedCategory g K m (hn₀ m hm)⟩,
    fun n => isCoherent_homology_restrictFunctor_mapDerivedCategory g K n (hK.2 n)⟩

/-- Restriction along an open immersion of schemes carries `D⁺_Coh` into `D⁺_Coh`. -/
theorem derivedCategoryBPlus_isCoherent_restrictFunctor_mapDerivedCategory
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (K : DerivedCategory Y.Modules)
    (hK : DerivedCategoryB.derivedCategoryBPlus
      (fun M : Y.Modules => M.IsCoherent) K) :
    DerivedCategoryB.derivedCategoryBPlus
      (fun M : X.Modules => M.IsCoherent)
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj K) := by
  obtain ⟨n₀, hn₀⟩ := hK.1
  exact ⟨⟨n₀, fun m hm => isZero_homology_restrictFunctor_mapDerivedCategory g K m (hn₀ m hm)⟩,
    fun n => isCoherent_homology_restrictFunctor_mapDerivedCategory g K n (hK.2 n)⟩

/-- Restriction along an isomorphism of schemes reflects coherence. -/
theorem isCoherent_of_restrict_iso {Y A : Scheme.{u}} [IsLocallyNoetherian Y] (e : A ≅ Y)
    (G : Y.Modules) (h : (G.restrict e.hom).IsCoherent) : G.IsCoherent :=
  have hqf := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    (G.restrict e.hom)
  have := isQuasicoherent_of_restrict_iso e G hqf.1
  have := isFiniteType_of_restrict_iso e G hqf.2
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType G

/-! ### The coherence clause of Tag 0D0C on an affine scheme -/

/-- **The coherence clause of [Stacks, Tag 0D0C] on an affine scheme, at sheaf level.** -/
theorem isCoherent_homology_derivedSheafHom_of_isAffine (W : Scheme.{u}) [IsAffine W]
    [IsLocallyNoetherian W] (E F : DerivedCategory W.Modules)
    (hE : DerivedCategoryB.derivedCategoryBMinus (fun M : W.Modules => M.IsCoherent) E)
    (hF : DerivedCategoryB.derivedCategoryBPlus (fun M : W.Modules => M.IsCoherent) F)
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor W.Modules n).obj
      (((Stacks.SheafOfModules.derivedSheafHom W.sheaf).obj (op E)).obj F)).IsCoherent := by
  have hR : IsNoetherianRing Γ(W, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top W⟩
  have : IsLocallyNoetherian (Spec Γ(W, ⊤)) := isLocallyNoetherian_Spec.mpr hR
  have hE' := derivedCategoryBMinus_isCoherent_restrictFunctor_mapDerivedCategory
    W.isoSpec.inv E hE
  have hF' := derivedCategoryBPlus_isCoherent_restrictFunctor_mapDerivedCategory
    W.isoSpec.inv F hF
  obtain ⟨K, hK, ⟨eK⟩⟩ := exists_derivedCategoryBMinus_finite_iso_tilde Γ(W, ⊤) _ hE'
  obtain ⟨L, hL, ⟨eL⟩⟩ := exists_derivedCategoryBPlus_finite_iso_tilde Γ(W, ⊤) _ hF'
  have h := derivedCategoryBPlus_isCoherent_affineDerivedSheafHom Γ(W, ⊤) K L hK hL
  have e2 := ((Stacks.SheafOfModules.derivedSheafHom (Spec Γ(W, ⊤)).sheaf).mapIso
      (Iso.op eK.symm)).app ((tilde.functor Γ(W, ⊤)).mapDerivedCategory.obj L) ≪≫
    ((Stacks.SheafOfModules.derivedSheafHom (Spec Γ(W, ⊤)).sheaf).obj
      (op ((Scheme.Modules.restrictFunctor W.isoSpec.inv).mapDerivedCategory.obj E))).mapIso eL
  refine isCoherent_of_restrict_iso W.isoSpec.symm _ ?_
  refine isCoherent_of_modulesIso
    ((DerivedCategoryB.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor W.isoSpec.inv) n).app _) ?_
  refine isCoherent_of_modulesIso
    ((DerivedCategory.homologyFunctor (Spec Γ(W, ⊤)).Modules n).mapIso
      (Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso W.isoSpec.inv E F)).symm ?_
  exact isCoherent_of_modulesIso
    ((DerivedCategory.homologyFunctor (Spec Γ(W, ⊤)).Modules n).mapIso e2) (h.2 n)

/-! ### The coherence clause of Tag 0D0C on a locally Noetherian scheme -/

/-- **The coherence clause of [Stacks, Tag 0D0C].** -/
theorem isCoherent_homology_derivedSheafHom (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (E F : DerivedCategory Y.Modules)
    (hE : DerivedCategoryB.derivedCategoryBMinus (fun M : Y.Modules => M.IsCoherent) E)
    (hF : DerivedCategoryB.derivedCategoryBPlus (fun M : Y.Modules => M.IsCoherent) F)
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor Y.Modules n).obj
      (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op E)).obj F)).IsCoherent := by
  refine AlgebraicGeometry.Modules.isCoherent_of_restrict _
    (fun U : Y.affineOpens => (U : Y.Opens)) (iSup_affineOpens_eq_top Y) fun U => ?_
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := Y.ringCatSheaf) (U : Y.Opens)
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := Y.ringCatSheaf) (U : Y.Opens)
  have : IsAffine (U : Y.Opens).toScheme := U.2
  have hres := isCoherent_homology_derivedSheafHom_of_isAffine (U : Y.Opens).toScheme
    ((Scheme.Modules.restrictFunctor (U : Y.Opens).ι).mapDerivedCategory.obj E)
    ((Scheme.Modules.restrictFunctor (U : Y.Opens).ι).mapDerivedCategory.obj F)
    (derivedCategoryBMinus_isCoherent_restrictFunctor_mapDerivedCategory (U : Y.Opens).ι E hE)
    (derivedCategoryBPlus_isCoherent_restrictFunctor_mapDerivedCategory (U : Y.Opens).ι F hF) n
  refine isCoherent_of_modulesIso
    ((DerivedCategoryB.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor (U : Y.Opens).ι) n).app _) ?_
  exact isCoherent_of_modulesIso
    ((DerivedCategory.homologyFunctor (U : Y.Opens).toScheme.Modules n).mapIso
      (Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso (U : Y.Opens) E F)).symm hres

/-- **Stacks Project, Tag 0D0C.** Let `X` be a locally Noetherian scheme, `K` an object of
`D⁻_Coh(𝒪_X)` and `L` an object of `D⁺_Coh(𝒪_X)`. Then `R𝓗om_{𝒪_X}(K, L)` lies in
`D⁺_Coh(𝒪_X)`.

Boundedness below is `Stacks.SheafOfModules.isBoundedBelow_derivedSheafHom`, which needs only the
two cohomological bounds; coherence of the cohomology sheaves is
`isCoherent_homology_derivedSheafHom`. -/
@[stacks 0D0C]
theorem derivedCategoryBPlus_isCoherent_derivedSheafHom (Y : Scheme.{u})
    [IsLocallyNoetherian Y] (E F : DerivedCategory Y.Modules)
    (hE : DerivedCategoryB.derivedCategoryBMinus
      (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf) E)
    (hF : DerivedCategoryB.derivedCategoryBPlus
      (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf) F) :
    DerivedCategoryB.derivedCategoryBPlus
      (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op E)).obj F) :=
  ⟨Stacks.SheafOfModules.isBoundedBelow_derivedSheafHom Y.sheaf E F hE.1 hF.1, fun n =>
    CoherentAbelian.isCoherent_iff_stacksIsCoherent.mp
      (isCoherent_homology_derivedSheafHom Y E F
        ⟨hE.1, fun m => CoherentAbelian.isCoherent_iff_stacksIsCoherent.mpr (hE.2 m)⟩
        ⟨hF.1, fun m => CoherentAbelian.isCoherent_iff_stacksIsCoherent.mpr (hF.2 m)⟩ n)⟩

/-! ### Single complexes and transport -/

/-- `D⁻_Coh` is closed under isomorphisms. -/
theorem derivedCategoryBMinus_isCoherent_of_iso {X : Scheme.{u}}
    {A B : DerivedCategory X.Modules} (e : A ≅ B)
    (h : DerivedCategoryB.derivedCategoryBMinus (fun M : X.Modules => M.IsCoherent) A) :
    DerivedCategoryB.derivedCategoryBMinus (fun M : X.Modules => M.IsCoherent) B :=
  ⟨DerivedCategoryB.isBoundedAbove_of_iso e h.1, fun n =>
    isCoherent_of_modulesIso ((DerivedCategory.homologyFunctor X.Modules n).mapIso e) (h.2 n)⟩

/-- A coherent module, read as a complex in degree zero, is an object of `D⁻_Coh`. -/
theorem derivedCategoryBMinus_isCoherent_singleFunctor_obj {X : Scheme.{u}} (M : X.Modules)
    (hM : M.IsCoherent) :
    DerivedCategoryB.derivedCategoryBMinus (fun N : X.Modules => N.IsCoherent)
      ((DerivedCategory.singleFunctor X.Modules 0).obj M) := by
  refine ⟨⟨0, fun i hi => DerivedCategory.isZero_of_isLE
    ((DerivedCategory.singleFunctor X.Modules 0).obj M) 0 i hi⟩, fun n => ?_⟩
  rcases lt_trichotomy n 0 with h | rfl | h
  · exact CoherentAbelian.isCoherent_of_stacksIsCoherent
      (ObjectProperty.prop_of_isZero (P := Stacks.SheafOfModules.coherentModules X.ringCatSheaf)
        (DerivedCategory.isZero_of_isGE ((DerivedCategory.singleFunctor X.Modules 0).obj M)
          0 n h))
  · exact isCoherent_of_modulesIso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app M).symm hM
  · exact CoherentAbelian.isCoherent_of_stacksIsCoherent
      (ObjectProperty.prop_of_isZero (P := Stacks.SheafOfModules.coherentModules X.ringCatSheaf)
        (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor X.Modules 0).obj M)
          0 n h))

/-! ### Stacks 0A79 -/

open RingedSpaceModuleAdjunction in
/-- **Stacks Project, Tag 0A79.** Let `i : Z ⟶ X` be a closed immersion of schemes with `X`
locally Noetherian. Then `R ℰom(𝒪_Z, -)` carries `D⁺_Coh(𝒪_X)` into `D⁺_Coh(𝒪_Z)`. -/
@[stacks 0A79]
theorem derivedSheafHomExactSupport_mem_derivedCategoryBPlus_coherent
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : DerivedCategoryB.derivedCategoryBPlus
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf) K) :
    DerivedCategoryB.derivedCategoryBPlus
      (Stacks.SheafOfModules.coherentModules Z.ringCatSheaf)
      ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
        i).derivedSheafHomExactSupport.obj K) := by
  have : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  set S := Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i
  have hKroot : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) n).obj
        K).IsCoherent := fun n => CoherentAbelian.isCoherent_iff_stacksIsCoherent.mpr (hK.2 n)
  have hqc := Scheme.derivedSheafHomExactSupport_mem_derivedCategoryBPlus_of_noetherian i K
    ⟨hK.1, isQuasicoherent_homology_of_isCoherent K hKroot⟩
  have hE := derivedCategoryBMinus_isCoherent_of_iso
    (Scheme.pushforwardDerivedStructureSheafIso i)
    (derivedCategoryBMinus_isCoherent_singleFunctor_obj _
      (AlgebraicGeometry.ClosedImmersionCoherentImage.isCoherent_pushforward_unit i))
  refine ⟨Scheme.isBoundedBelow_derivedSheafHomExactSupport_of_isCoherent i K hK, fun n => ?_⟩
  have hRHom := isCoherent_homology_derivedSheafHom X _ K hE ⟨hK.1, hKroot⟩ n
  refine CoherentAbelian.isCoherent_iff_stacksIsCoherent.mp
    ((@Stacks.AlgebraicGeometry.ClosedImmersionCoherence.isCoherent_pushforward_iff Z X
      ‹_› ‹_› i ‹_› _ (hqc.2 n)).mp ?_)
  exact isCoherent_of_modulesIso
    (((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).mapIso
        (S.derivedSheafHomExactSupportPushforwardNatIso.app K)).symm ≪≫
      (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (modulePushforward S.i) n).app (S.derivedSheafHomExactSupport.obj K))
    hRHom

end AlgebraicGeometry

end
