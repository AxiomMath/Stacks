module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSurjectiveAffineSource

/-!
# A Noetherian algebraic space covered by finitely many finite maps from affines is affine

This file proves the following strengthening of Stacks 07VP.  Let `X` be a Noetherian algebraic
space over a scheme `S` and let `fᵢ : Yᵢ ⟶ X`, for `i` in a finite index type, be finite
morphisms from affine algebraic spaces which are *jointly* surjective: every point of `|X|` lies
in the image of some `|fᵢ|`.  Then `X` is affine.

For a single index this is Stacks 07VP, and the proof is that of
`AlgebraicGeometry.Space.isAffineSpace_of_isFinite_of_isSurjective`: by Stacks 0D2V it suffices
that `H¹(X, 𝓕) = 0` for every coherent `𝓕`, and by the dévissage of Stacks 07US and the
Noetherian induction `AlgebraicGeometry.Space.forall_property_idealPushforward_of_step` it
suffices to treat `i_*ℐ` for a reduced closed subspace `i : Z ⟶ X` with `|Z|` irreducible.
That step uses surjectivity only through the base change `Yᵢ ×_X Z ⟶ Z`, and for a jointly
surjective finite family one of those base changes is surjective: their images are closed, they
cover `|Z|`, and `|Z|` is irreducible.

## Main results

* `AlgebraicGeometry.Space.property_idealPushforward_of_lt_of_isSurjective_pullback`: the step
  of the Noetherian induction of Stacks 07UT, with surjectivity of the base change along `Z`
  in place of surjectivity of `f`.
* `AlgebraicGeometry.Space.exists_isSurjective_pullback_snd_of_isReducedIrreducible`: for a
  jointly surjective finite family, some base change along a reduced closed subspace with
  irreducible space of points is surjective.
* `AlgebraicGeometry.Space.isAffineSpace_of_isFinite_of_forall_exists_pointsMap_eq`: the
  statement above.

## References

* [Stacks Project, Tag 07VP](https://stacks.math.columbia.edu/tag/07VP)
* [Stacks Project, Tag 07UT](https://stacks.math.columbia.edu/tag/07UT)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

section Step

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

variable (hZtop : B.Contains (⊤_ Scheme.{u}))

/-- The base change of a finite morphism along a closed subspace is finite. -/
private theorem isFinite_pullback_snd_closedSubfunctorι {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hf : IsFinite B S hS f.hom) {Z : Subfunctor X.1} (hZ : IsClosedSubspace B S hS Z) :
    IsFinite B S hS (pullback.snd f (closedSubfunctorι B S hS hZ)).hom :=
  isFinite_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS
    (IsPullback.of_hasPullback f (closedSubfunctorι B S hS hZ))) hf

/-- **The step of the Noetherian induction of Stacks 07UT along a finite morphism which is
surjective over `Z`.**  This is `AlgebraicGeometry.Space.property_idealPushforward_of_lt` with
the surjectivity of `f : Y ⟶ X` weakened to surjectivity of its base change
`f' : Y ×_X Z ⟶ Z` along the reduced irreducible closed subspace `Z`, which is all that the
argument uses: it enters only through the support of `f'_*𝒪_{Y ×_X Z}` being all of `Z`
(Stacks 0GF7). -/
theorem property_idealPushforward_of_lt_of_isSurjective_pullback
    (X Y : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (f : Y ⟶ X) (hf : IsFinite B S hS f.hom)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (hext : ClosedUnderCoherentExtensions B S hS X P)
    (hsum : ∀ N : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 N → ∀ r : ℕ, 0 < r →
      P (⨁ fun _ : Fin r => N) → P N)
    (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z)
    (hfs : IsSurjective B S hS (pullback.snd f (closedSubfunctorι B S hS hZ)).hom)
    (hbase : ∀ M : Modules.{u, u} B S hS (pullback f (closedSubfunctorι B S hS hZ)).1
        (pullback f (closedSubfunctorι B S hS hZ)).2,
      M.IsQuasicoherentOnSite → IsCoherent B S hS _ _ M →
        P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
          ((modulePushforward B S hS (pullback.snd f (closedSubfunctorι B S hS hZ))).obj M)))
    (hint : IsReducedIrreducible B S hS Z)
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ))
    (hsmall : ∀ N : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 N →
      moduleSupportSet B S hS X N ⊂ moduleSupportSet B S hS X
        ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) →
      P N) :
    P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) := by
  let Zs := closedSubfunctorSpace B S hS hZ
  let iZ := closedSubfunctorι B S hS hZ
  by_cases hI : I.1 = ⊥
  · exact hzero _ (isZero_modulePushforward_of_eq_bot B S hS X hZ I hI)
  have hNZ := isNoetherian_closedSubfunctor B S hS hZtop X hX hZ
  have hIimg := moduleSupportSet_idealPushforward_eq_image B S hS X hX.2.2 hZ hint I hI
  set f' := pullback.snd f iZ
  have hf' : IsFinite B S hS f'.hom := isFinite_pullback_snd_closedSubfunctorι B S hS f hf hZ
  have : Fact (HasEtaleLocalProperty B S hS (pullback f iZ).1
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) :=
    ⟨isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (pullback f iZ).2 Zs.2 f'.hom
      (isLocallyOfFiniteType_of_isFinite B S hS (pullback f iZ).2 Zs.2 hf') hNZ.2.2⟩
  have hG : IsCoherent B S hS Zs.1 Zs.2 ((modulePushforward B S hS f').obj
      (SheafOfModules.unit (structureRingSheaf B S hS (pullback f iZ)))) :=
    isCoherent_modulePushforward_of_isFinite' B S hS f' hf' hNZ.2.2 _
      (isCoherent_structureSheaf B S hS (pullback f iZ).1 (pullback f iZ).2)
  obtain ⟨J, hJI, hJq, hJne, r, hr, M, hMq, hMc, m, hm, hcok, hcoksupp⟩ :=
    exists_mono_pi_modulePushforward B S hS hZtop f' hf' hNZ hint.1 hint.2 I.1 I.2 hI hG
      (supportOfSheaf_modulePushforward_structureSheaf_eq_univ B S hS f' hfs)
  have hJbot : J ≠ ⊥ := ne_bot_of_idealUnitLocus_nonempty B S hS Zs J hJne
  have hJc := isCoherent_quasicoherentIdeal B S hS Zs hNZ.2.2 ⟨J, hJq⟩
  have hPc : IsCoherent B S hS Zs.1 Zs.2
      (∏ᶜ fun _ : Fin r => (J.toSheafOfModules : Modules.{u, u} B S hS Zs.1 Zs.2)) :=
    isCoherent_piConst B S hS Zs.1 Zs.2 _ hJc r
  have hiZf : IsFinite B S hS iZ.hom := isFinite_of_isClosedImmersion B S hS _ hZ.2
  have hAc : IsCoherent B S hS Zs.1 Zs.2 ((modulePushforward B S hS f').obj M) :=
    isCoherent_modulePushforward_of_isFinite' B S hS f' hf' hNZ.2.2 M hMc
  have hAX := isCoherent_modulePushforward_of_isFinite' B S hS iZ hiZf hX.2.2 _ hAc
  have hPX := isCoherent_modulePushforward_of_isFinite' B S hS iZ hiZf hX.2.2 _ hPc
  have hlt : ∀ {A C : Modules.{u, u} B S hS Zs.1 Zs.2} (φ : A ⟶ C),
      IsCoherent B S hS Zs.1 Zs.2 (cokernel φ) →
      moduleSupportSet B S hS Zs (cokernel φ) ⊆ idealZeroLocus B S hS Zs J →
      moduleSupportSet B S hS X (cokernel ((modulePushforward B S hS iZ).map φ)) ⊂
        moduleSupportSet B S hS X ((modulePushforward B S hS iZ).obj I.1.toSheafOfModules) :=
    fun φ hφ hsupp => by
      rw [hIimg, moduleSupportSet_cokernel_modulePushforward B S hS X Zs iZ hZ.2 φ hφ]
      exact lt_of_le_of_lt (Set.image_mono hsupp)
        (image_idealZeroLocus_ssubset B S hS hZ hint J hJbot)
  have hPprod := hext _ (shortExact_cokernelSequence_modulePushforward B S hS X Zs iZ m hm)
    hAX hPX (isCoherent_cokernel B S hS X.1 X.2 hAX hPX _) (hbase M hMq hMc)
    (hsmall _ (isCoherent_cokernel B S hS X.1 X.2 hAX hPX _) (hlt m hcok hcoksupp))
  have hJX := isCoherent_modulePushforward_quasicoherentIdeal B S hS hX.2.2 iZ hZ.2 ⟨J, hJq⟩
  have hPJ : P ((modulePushforward B S hS iZ).obj J.toSheafOfModules) :=
    hsum _ hJX r hr (property_of_iso B S hS X P hzero hext hPX
      (isCoherent_of_iso B S hS X.2
        (modulePushforwardBiproductConstIso B S hS X iZ r J.toSheafOfModules).symm hPX)
      (modulePushforwardBiproductConstIso B S hS X iZ r J.toSheafOfModules).symm hPprod)
  let incl : J.toSheafOfModules ⟶ I.1.toSheafOfModules := I.1.factorThru J.ι
    fun W x => hJI W x.2
  have hincl : Mono incl := by
    have h : incl ≫ I.1.ι = J.ι := SheafOfModules.Submodule.factorThru_ι _ _ _
    have : Mono (incl ≫ I.1.ι) := h ▸ SheafOfModules.Submodule.mono_ι_via_forget J
    exact mono_of_mono _ I.1.ι
  have hIc := isCoherent_quasicoherentIdeal B S hS Zs hNZ.2.2 I
  have hcokI : IsCoherent B S hS Zs.1 Zs.2 (cokernel incl) :=
    isCoherent_cokernel B S hS Zs.1 Zs.2 hJc hIc incl
  have hIX := isCoherent_modulePushforward_quasicoherentIdeal B S hS hX.2.2 iZ hZ.2 I
  have hltI := hlt incl hcokI
    (supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective B S hS Zs J incl
      fun V hV s => ⟨⟨s.1, (Submodule.eq_top_iff'.1 hV) _⟩, rfl⟩)
  exact hext _ (shortExact_cokernelSequence_modulePushforward B S hS X Zs iZ incl hincl) hJX hIX
    (isCoherent_cokernel B S hS X.1 X.2 hJX hIX _) hPJ
    (hsmall _ (isCoherent_cokernel B S hS X.1 X.2 hJX hIX _) hltI)

/-- **For a jointly surjective finite family, some base change along a reduced irreducible closed
subspace is surjective.**  Let `fᵢ : Yᵢ ⟶ X`, `i` in a finite type, be finite morphisms whose
images cover `|X|`, and let `Z ⊆ X` be a closed subspace with `|Z|` irreducible.  The images of
the base changes `Yᵢ ×_X Z ⟶ Z` are closed, because finite morphisms are universally closed,
and they cover `|Z|`; an irreducible space is not a finite union of proper closed subsets. -/
theorem exists_isSurjective_pullback_snd_of_isReducedIrreducible {ι : Type*} [Finite ι]
    {X : AlgebraicSpaces B S hS} (Y : ι → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (hf : ∀ i, IsFinite B S hS (f i).hom)
    (hsurj : ∀ x : points B S hS X.1, ∃ i, ∃ y : points B S hS (Y i).1,
      pointsMap B S hS (Y i).1 (f i).hom y = x)
    (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z) (hint : IsReducedIrreducible B S hS Z) :
    ∃ i, IsSurjective B S hS (pullback.snd (f i) (closedSubfunctorι B S hS hZ)).hom := by
  classical
  have := hint.2
  have := Fintype.ofFinite ι
  have hcl : ∀ i, IsClosed (Set.range (pointsMap B S hS
      (pullback (f i) (closedSubfunctorι B S hS hZ)).1
      (pullback.snd (f i) (closedSubfunctorι B S hS hZ)).hom)) := by
    intro i
    have hf' := isFinite_pullback_snd_closedSubfunctorι B S hS (f i) (hf i) hZ
    have hproper : IsProper B S hS (pullback.snd (f i) (closedSubfunctorι B S hS hZ)).hom :=
      ((isFinite_iff_isAffineHom_and_isProper B S hS (pullback (f i)
        (closedSubfunctorι B S hS hZ)).2 (closedSubfunctorSpace B S hS hZ).2 _).mp hf').2
    rw [← Set.image_univ]
    exact isClosed_of_universallyClosed B S hS (closedSubfunctorSpace B S hS hZ).2 _
      hproper.universallyClosed _ isClosed_univ
  set R := fun i => Set.range (pointsMap B S hS (pullback (f i)
      (closedSubfunctorι B S hS hZ)).1 (pullback.snd (f i) (closedSubfunctorι B S hS hZ)).hom)
  have hcover : (Set.univ : Set (points B S hS (closedSubfunctorSpace B S hS hZ).1)) ⊆
      ⋃₀ ↑(Finset.univ.image R) := by
    intro z _
    obtain ⟨i, y, hy⟩ := hsurj (pointsMap B S hS _ (closedSubfunctorι B S hS hZ).hom z)
    have sq := AlgebraicSpaces.isPullback_hom B S hS
      (IsPullback.of_hasPullback (f i) (closedSubfunctorι B S hS hZ))
    obtain ⟨w, -, hw⟩ := exists_point_of_isPullback_presheaf B S hS sq y z hy
    exact Set.mem_sUnion.2 ⟨R i, by simp, w, hw⟩
  have hirr : IsIrreducible (Set.univ : Set (points B S hS (closedSubfunctorSpace B S hS hZ).1)) :=
    IrreducibleSpace.isIrreducible_univ _
  obtain ⟨z, hz, hi⟩ := isIrreducible_iff_sUnion_isClosed.mp hirr (Finset.univ.image R)
    (by
      intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
      exact hcl i) hcover
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
  exact ⟨i, fun z => hi (Set.mem_univ z)⟩

/-- **The step of Stacks 07VP for a jointly surjective finite family.**  This is
`AlgebraicGeometry.Space.isZero_rightDerived_one_idealPushforward_of_lt` with the single finite
surjection from an affine space replaced by a finite family of finite morphisms from affine
spaces whose images cover `|X|`: the member whose base change along `Z` is surjective
(`AlgebraicGeometry.Space.exists_isSurjective_pullback_snd_of_isReducedIrreducible`) does the
work. -/
theorem isZero_rightDerived_one_idealPushforward_of_lt_of_family {ι : Type*} [Finite ι]
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (Y : ι → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X) (hf : ∀ i, IsFinite B S hS (f i).hom)
    (hsurj : ∀ x : points B S hS X.1, ∃ i, ∃ y : points B S hS (Y i).1,
      pointsMap B S hS (Y i).1 (f i).hom y = x)
    (hY : ∀ i, IsAffineSpace B S hS (Y i).1)
    (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z) (hint : IsReducedIrreducible B S hS Z)
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ))
    (hsmall : ∀ N : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 N →
      moduleSupportSet B S hS X N ⊂ moduleSupportSet B S hS X
        ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) →
      have := enoughInjectives_modules B S hS X.1 X.2
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj N)) :
    have := enoughInjectives_modules B S hS X.1 X.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj
        ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules)) := by
  have := enoughInjectives_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  let Γ := globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O)
  obtain ⟨i, hi⟩ := exists_isSurjective_pullback_snd_of_isReducedIrreducible B S hS Y f hf hsurj
    Z hZ hint
  exact property_idealPushforward_of_lt_of_isSurjective_pullback B S hS hZtop X (Y i) hX (f i)
    (hf i) (fun N => IsZero ((Γ.rightDerived 1).obj N)) (fun N hN => Functor.map_isZero _ hN)
    (fun E hE _ _ _ h1 h3 => Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂ hE Γ 1 h1
        h3)
    (fun N _ r hr h => isZero_obj_of_isZero_obj_biproduct (Γ.rightDerived 1) N hr h) Z hZ hi
    (fun M hMq _ => isZero_rightDerived_modulePushforward_modulePushforward_of_isPullback B S hS
      (IsPullback.of_hasPullback (f i) (closedSubfunctorι B S hS hZ)) (hf i) hZ.2 (hY i) M hMq 1
        one_pos)
    hint I hsmall

/-- **Stacks 07VP for a jointly surjective finite family.**  Let `X` be a Noetherian algebraic
space over `S` and let `fᵢ : Yᵢ ⟶ X`, `i` in a finite type, be finite morphisms from affine
algebraic spaces such that every point of `|X|` is in the image of some `|fᵢ|`.  Then `X` is
affine.

The proof of `AlgebraicGeometry.Space.isAffineSpace_of_isFinite_of_isSurjective` goes through
with its step replaced by
`AlgebraicGeometry.Space.isZero_rightDerived_one_idealPushforward_of_lt_of_family`. -/
theorem isAffineSpace_of_isFinite_of_forall_exists_pointsMap_eq {ι : Type*} [Finite ι]
    (X : AlgebraicSpaces B S hS) (Y : ι → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (hf : ∀ i, IsFinite B S hS (f i).hom)
    (hsurj : ∀ x : points B S hS X.1, ∃ i, ∃ y : points B S hS (Y i).1,
      pointsMap B S hS (Y i).1 (f i).hom y = x)
    (hY : ∀ i, IsAffineSpace B S hS (Y i).1) (hX : IsNoetherian B S hS hZtop X.1) :
    IsAffineSpace B S hS X.1 := by
  have := enoughInjectives_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  let Γ := globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O)
  have hzero : ∀ N : Modules.{u, u} B S hS X.1 X.2, IsZero N → IsZero ((Γ.rightDerived 1).obj N) :=
    fun N hN => Functor.map_isZero _ hN
  have hext : ClosedUnderCoherentExtensions B S hS X (fun N => IsZero ((Γ.rightDerived 1).obj N)) :=
    fun E hE _ _ _ h1 h3 => Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂ hE Γ 1 h1 h3
  exact isAffineSpace_of_forall_isCoherent_isZero_rightDerived_one B S hS hZtop X hX
    fun F hF => property_of_ideal_pushforward_and_extensions B S hS X hX
      (fun N => IsZero ((Γ.rightDerived 1).obj N)) (Or.inr hzero) hext
      (fun Z hZ hint I => forall_property_idealPushforward_of_step B S hS hZtop X hX _ hzero hext
        (isZero_rightDerived_one_idealPushforward_of_lt_of_family B S hS hZtop X hX Y f hf hsurj hY)
        Z hZ hint I) F hF

end Step

end AlgebraicGeometry.Space

end
