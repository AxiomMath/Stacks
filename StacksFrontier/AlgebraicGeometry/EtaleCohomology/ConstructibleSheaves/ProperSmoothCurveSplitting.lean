module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.RightDerivedConstantUnitBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ProperSmoothCurveConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel

/-!
# `Rᵠ f_* 𝐙/ℓ` for a family of curves over a Noetherian base: splitting along `ℓ`

Let `S` be a Noetherian scheme, `ℓ` a prime and `f : X ⟶ S` proper and smooth with geometrically
connected fibres of dimension at most one. Write `S = U ∪ Z` with `U` the open subscheme where `ℓ`
is invertible and `Z = V(ℓ)` the closed subscheme where it vanishes. Proper base change
([Stacks, Tag 095T], `Stacks.EtaleCohomology.rightDerivedConstantUnitProperBaseChangeIso`)
identifies the inverse images of `Rᵠ f_* 𝐙/ℓ` on `U` and `Z` with the higher direct images for the
restricted families, and a sheaf is constructible as soon as its inverse images to the strata
of a finite constructible partition are ([Stacks, Tag 09YR]). On `Z` the prime `ℓ` is zero, which
is case (b) of the proof of [Stacks, Tag 0GKV]
(`Stacks.ArtinSchreier.isConstructibleEtaleModule_rightDerivedConstantUnit_of_charP`). On `U` it
is invertible, which is case (a); here case (a) is a hypothesis of the reduction.

## Main results

* `isConstructibleEtaleModule_inverseImage_rightDerivedConstantUnit_iff`: for a proper `f` and any
  `j : T ⟶ S`, constructibility of `j⁻¹ Rᵠ f_* 𝐙/ℓ` is constructibility of `Rᵠ f_{T*} 𝐙/ℓ` for the
  base change `f_T`.
* `isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian_of_invertible`: the
  reduction of the Noetherian case of [Stacks, Tag 0GKV] to case (a).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

section Fibre

/-- **Fibres of a base change along an immersion are fibres of the original morphism.** -/
theorem topologicalKrullDim_fiber_pullbackSnd_le_of_isImmersion {X S W : Scheme.{u}} (f : X ⟶ S)
    (ι : W ⟶ S) [IsImmersion ι] {n : WithBot ℕ∞} (h : ∀ s, topologicalKrullDim (f.fiber s) ≤ n)
    (w : W) : topologicalKrullDim ((pullback.snd f ι).fiber w) ≤ n := by
  let φ : (pullback.snd f ι).base ⁻¹' {w} → f.base ⁻¹' {ι.base w} := fun x =>
    ⟨(pullback.fst f ι).base x.1, by
      show (pullback.fst f ι ≫ f).base x.1 = ι.base w
      rw [pullback.condition, Scheme.Hom.comp_apply, x.2]⟩
  have hφ : IsHomeomorph φ := by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨(pullback.fst f ι).isEmbedding.restrict
      (fun x hx => (φ ⟨x, hx⟩).2), fun y => ?_⟩
    obtain ⟨x, hx⟩ : y.1 ∈ Set.range (pullback.fst f ι).base := by
      rw [Scheme.Pullback.range_fst]
      show f.base y.1 ∈ Set.range ι.base
      rw [show f.base y.1 = ι.base w from y.2]
      exact Set.mem_range_self _
    have hxw : (pullback.snd f ι).base x = w := by
      apply ι.isEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hx]
      exact y.2
    exact ⟨⟨x, hxw⟩, Subtype.ext hx⟩
  rw [((pullback.snd f ι).fiberHomeo w).isHomeomorph.topologicalKrullDim_eq,
    hφ.topologicalKrullDim_eq, ← (f.fiberHomeo (ι.base w)).isHomeomorph.topologicalKrullDim_eq]
  exact h _

end Fibre

section Transfer

variable (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj) [IsProper f]
  (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ)

/-- **Constructibility of `j⁻¹ Rᵠ f_* 𝐙/ℓ` is constructibility of `Rᵠ f_{T*} 𝐙/ℓ`**, for `f`
proper, any morphism `j : T ⟶ S` of the big étale site and the base change `f_T : X_T ⟶ T`
(proper base change, [Stacks, Tag 095T]). -/
theorem isConstructibleEtaleModule_inverseImage_rightDerivedConstantUnit_iff {T XT : B.Scheme}
    (j : T ⟶ S) (gT : XT.obj ⟶ X.obj) (fT : XT.obj ⟶ T.obj)
    (sq : IsPullback gT fT f (B.inclusion.map j)) :
    IsBigSiteConstructibleEtaleModule B T (ZMod ℓ)
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (B.inclusion.map j)).obj
          (rightDerivedConstantUnit f q (ZMod ℓ))) ↔
      IsBigSiteConstructibleEtaleModule B T (ZMod ℓ) (rightDerivedConstantUnit fT q (ZMod ℓ)) := by
  let e := rightDerivedConstantUnitProperBaseChangeIso f (B.inclusion.map j) gT fT sq ℓ q
  exact ⟨IsBigSiteConstructibleEtaleModule.of_iso B (ZMod ℓ) e,
    IsBigSiteConstructibleEtaleModule.of_iso B (ZMod ℓ) e.symm⟩

/-- The inverse image on the bounded site of the transport of `Rᵠ f_* 𝐙/ℓ` along a morphism
`j : T ⟶ S` is constructible as soon as `Rᵠ f_{T*} 𝐙/ℓ` is, `f_T` being the base change. -/
theorem isConstructibleModuleSheaf_pullback_rightDerivedConstantUnit {T XT : B.Scheme}
    (j : T ⟶ S) (gT : XT.obj ⟶ X.obj) (fT : XT.obj ⟶ T.obj)
    (sq : IsPullback gT fT f (B.inclusion.map j))
    (h : IsBigSiteConstructibleEtaleModule B T (ZMod ℓ) (rightDerivedConstantUnit fT q (ZMod ℓ))) :
    IsConstructibleModuleSheaf B T (ZMod ℓ)
      (((AlgebraicGeometry.smallEtaleBaseChange B j).sheafPullback (ModuleCat.{u + 1} (ZMod ℓ))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).obj
          ((etaleModulesToSmallEtale B S (ZMod ℓ)).obj (rightDerivedConstantUnit f q (ZMod ℓ)))) :=
  isConstructibleModuleSheaf_congr B (ZMod ℓ) T
    (etaleModulesToSmallEtalePullbackIso B (ZMod ℓ) j _)
    ((isConstructibleEtaleModule_inverseImage_rightDerivedConstantUnit_iff B f ℓ q j gT fT sq).2 h)

end Transfer

section Splitting

variable (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
  [GeometricallyConnected f] (hdim : ∀ s : S.obj, topologicalKrullDim (f.fiber s) ≤ 1)
  [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ)

/-- If a natural number is invertible on `X`, it is invertible on `Y`. -/
theorem isUnit_natCast_of_hom {X Y : Scheme.{u}} (g : Y ⟶ X) {p : ℕ}
    (hX : IsUnit (p : Γ(X, ⊤))) : IsUnit (p : Γ(Y, ⊤)) :=
  (map_natCast g.appTop.hom p) ▸ hX.map g.appTop.hom

/-- A natural number is the image of the same natural number under a ring map into the global
sections of a spectrum. -/
theorem natCast_ΓSpec {R : CommRingCat.{u}} (p : ℕ) :
    (p : Γ(Spec R, ⊤)) = (Scheme.ΓSpecIso R).inv.hom (p : R) :=
  (map_natCast (Scheme.ΓSpecIso R).inv.hom p).symm

include hdim in
/-- **The Noetherian case of [Stacks, Tag 0GKV], granted case (a).** Let `S` be Noetherian, `ℓ` a
prime and `f : X ⟶ S` proper and smooth with geometrically connected fibres of dimension at most
one. Suppose that case (a) holds: for every such family over a Noetherian base on which `ℓ` is
invertible, `Rᵠ f_* 𝐙/ℓ` is constructible. Then `Rᵠ f_* 𝐙/ℓ` is constructible.

The base is split as `S = U ∪ Z`, `U` the locus where `ℓ` is invertible and `Z = V(ℓ)`; the
inverse images of `Rᵠ f_* 𝐙/ℓ` to `U` and `Z` are the higher direct images of the restricted
families by proper base change; on `Z` case (b) applies
(`Stacks.ArtinSchreier.isConstructibleEtaleModule_rightDerivedConstantUnit_of_charP`); and
constructibility is checked on the two strata ([Stacks, Tag 09YR]). -/
theorem isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian_of_invertible
    (ha : ∀ (X' S' : B.Scheme) (f' : X'.obj ⟶ S'.obj) [IsProper f'] [Smooth f']
      [GeometricallyConnected f'], (∀ s : S'.obj, topologicalKrullDim (f'.fiber s) ≤ 1) →
      IsNoetherian S'.obj → IsUnit ((ℓ : ℕ) : Γ(S'.obj, ⊤)) →
      IsBigSiteConstructibleEtaleModule B S' (ZMod ℓ) (rightDerivedConstantUnit f' q (ZMod ℓ))) :
    IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)) := by
  have := fun (S T : B.Scheme) (f : T ⟶ S) =>
    SmallEtale.isRightAdjointPushforward_moduleCat.{u, 0, 0} B (ZMod ℓ) f
  have := SmallEtale.hasWeakSheafifyOver_moduleCat.{u, 0, 0} B (ZMod ℓ)
  let A : CommRingCat.{u} := Γ(S.obj, ⊤)
  let r : A := (ℓ : A)
  -- the open stratum `U = D(ℓ)` and the closed stratum `Z = V(ℓ)`, as base changes of affine
  -- immersions along `S ⟶ Spec Γ(S, ⊤)`
  let φU : A ⟶ CommRingCat.of (Localization.Away r) := CommRingCat.ofHom (algebraMap A _)
  let φZ : A ⟶ CommRingCat.of (A ⧸ Ideal.span {r}) := CommRingCat.ofHom (Ideal.Quotient.mk _)
  let ιU := pullback.snd (Spec.map φU) S.obj.toSpecΓ
  let ιZ := pullback.snd (Spec.map φZ) S.obj.toSpecΓ
  have hU : B.Contains (pullback (Spec.map φU) S.obj.toSpecΓ) :=
    Scheme.size_lt_of_isOpenImmersion ιU S.property
  have hZ : B.Contains (pullback (Spec.map φZ) S.obj.toSpecΓ) :=
    Scheme.size_lt_of_isClosedImmersion ιZ S.property
  let TU := B.obj _ hU
  let TZ := B.obj _ hZ
  let jU : TU ⟶ S := ObjectProperty.homMk ιU
  let jZ : TZ ⟶ S := ObjectProperty.homMk ιZ
  have hXU : B.Contains (pullback f ιU) :=
    Scheme.size_lt_of_isOpenImmersion (pullback.fst f ιU) X.property
  have hXZ : B.Contains (pullback f ιZ) :=
    Scheme.size_lt_of_isClosedImmersion (pullback.fst f ιZ) X.property
  let XU := B.obj _ hXU
  let XZ := B.obj _ hXZ
  let fU : XU.obj ⟶ TU.obj := pullback.snd f ιU
  let fZ : XZ.obj ⟶ TZ.obj := pullback.snd f ιZ
  have hdim' : ∀ {W : Scheme.{u}} (ι : W ⟶ S.obj) [IsImmersion ι] (s : W),
      topologicalKrullDim ((pullback.snd f ι).fiber s) ≤ 1 := fun ι _ =>
    topologicalKrullDim_fiber_pullbackSnd_le_of_isImmersion f ι hdim
  -- `ℓ` is invertible on `U` and zero on `Z`
  have hUunit : IsUnit ((ℓ : ℕ) : Γ(TU.obj, ⊤)) := by
    refine isUnit_natCast_of_hom (pullback.fst (Spec.map φU) S.obj.toSpecΓ) ?_
    rw [natCast_ΓSpec]
    refine IsUnit.map _ ?_
    show IsUnit ((ℓ : Localization.Away r))
    rw [← map_natCast (algebraMap A (Localization.Away r))]
    exact IsLocalization.Away.algebraMap_isUnit r
  have hZzero : ((ℓ : ℕ) : Γ(TZ.obj, ⊤)) = 0 := by
    refine Stacks.ArtinSchreier.natCast_eq_zero_of_hom
      (pullback.fst (Spec.map φZ) S.obj.toSpecΓ) ?_
    rw [natCast_ΓSpec]
    refine (congrArg _ ?_).trans (map_zero _)
    show ((ℓ : A ⧸ Ideal.span {r})) = 0
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {r}))]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self r)
  have : IsNoetherian TU.obj := Stacks.Coherent.isNoetherian_of_isOpenImmersion ιU
  have : IsNoetherian TZ.obj := isNoetherian_of_isClosedImmersion ιZ
  -- the two strata
  have hcU : IsBigSiteConstructibleEtaleModule B TU (ZMod ℓ)
      (rightDerivedConstantUnit fU q (ZMod ℓ)) :=
    ha XU TU fU (hdim' ιU) inferInstance hUunit
  have hcZ : IsBigSiteConstructibleEtaleModule B TZ (ZMod ℓ)
      (rightDerivedConstantUnit fZ q (ZMod ℓ)) :=
    Stacks.ArtinSchreier.isConstructibleEtaleModule_rightDerivedConstantUnit_of_charP B fZ
      (hdim' ιZ) ℓ hZzero q
  -- membership in the two strata
  have hmemU : ∀ x : S.obj, x ∈ Set.range ιU ↔ r ∉ (S.obj.toSpecΓ x).asIdeal := fun x => by
    rw [Scheme.Pullback.range_snd]
    show S.obj.toSpecΓ x ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away r)))
      ↔ _
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact PrimeSpectrum.mem_basicOpen _ _
  have hmemZ : ∀ x : S.obj, x ∈ Set.range ιZ ↔ r ∈ (S.obj.toSpecΓ x).asIdeal := fun x => by
    rw [Scheme.Pullback.range_snd]
    show S.obj.toSpecΓ x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {r})))
      ↔ _
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact SetLike.coe_subset_coe.trans (Ideal.span_singleton_le_iff_mem _)
  have hrangeZ : Set.range ιZ = (Set.range ιU)ᶜ := by
    ext x
    rw [Set.mem_compl_iff, hmemU, hmemZ, not_not]
  have hopen : IsOpen (Set.range ιU) := ιU.isOpenEmbedding.isOpen_range
  have hLN : IsLocallyNoetherian S.obj := IsNoetherian.toIsLocallyNoetherian
  have hqs : QuasiSeparatedSpace S.obj := @IsLocallyNoetherian.quasiSeparatedSpace S.obj hLN
  have hcU' : Topology.IsConstructible (Set.range ιU) :=
    IsCompact.isConstructible (TopologicalSpace.NoetherianSpace.isCompact _) hopen
  -- assemble over the two strata
  let T : Bool → B.Scheme := fun b => Bool.casesOn b TZ TU
  let j : ∀ b, T b ⟶ S := fun b => Bool.casesOn (motive := fun b => T b ⟶ S) b jZ jU
  refine isConstructibleModuleSheaf_of_constructible_immersion_cover B S (ZMod ℓ) _ T j ?_ ?_ ?_ ?_
  · rintro (_ | _)
    · exact inferInstanceAs (IsImmersion ιZ)
    · exact inferInstanceAs (IsImmersion ιU)
  · rintro (_ | _)
    · exact hrangeZ ▸ hcU'.compl
    · exact hcU'
  · refine (Set.eq_univ_of_forall fun x => ?_).symm
    by_cases hx : r ∈ (S.obj.toSpecΓ x).asIdeal
    · exact Set.mem_iUnion.2 ⟨false, (hmemZ x).2 hx⟩
    · exact Set.mem_iUnion.2 ⟨true, (hmemU x).2 hx⟩
  · rintro (_ | _)
    · exact isConstructibleModuleSheaf_pullback_rightDerivedConstantUnit B f ℓ q jZ
        (pullback.fst f ιZ) fZ (IsPullback.of_hasPullback f ιZ) hcZ
    · exact isConstructibleModuleSheaf_pullback_rightDerivedConstantUnit B f ℓ q jU
        (pullback.fst f ιU) fU (IsPullback.of_hasPullback f ιU) hcU

end Splitting

end Stacks.EtaleCohomology

end
