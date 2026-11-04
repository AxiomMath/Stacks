module

public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundlePoints
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Modules.LocallySplitShortExact
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic

/-!
# The morphism of vector bundles induced by a subbundle

Let `0 ⟶ 𝒜 ⟶ ℬ ⟶ 𝒞 ⟶ 0` be a short exact sequence of quasi-coherent `𝒪_X`-modules with `𝒞`
finite locally free of rank `c`. The inclusion `𝒜 ⟶ ℬ` induces a morphism of vector bundles
`𝐕(ℬ) ⟶ 𝐕(𝒜)` over `X`. If the sequence is split, `𝐕(ℬ) = 𝐕(𝒜) ×_X 𝐕(𝒞)` and the morphism is the
first projection, the base change of `𝐕(𝒞) ⟶ X`; the sequence splits locally on `X`, so in
general `𝐕(ℬ) ⟶ 𝐕(𝒜)` is flat, locally of finite type and of relative dimension `c`.

## Main results

* `Stacks.Chow.isPullback_vectorBundleMap_of_splitting` — the split case.
* `Stacks.Chow.flat_vectorBundleMap_of_shortExact`,
  `Stacks.Chow.locallyOfFiniteType_vectorBundleMap_of_shortExact`,
  `Stacks.Chow.relativeDimension_vectorBundleMap_of_shortExact` — the general case.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.Chow

section SplitAlgebra

variable {C : Type*} [Category C] [Preadditive C] {S : ShortComplex C} (σ : S.Splitting) {M : C}

/-- For a splitting `σ` of `S`, precomposing `σ.r ≫ a + S.g ≫ b` with the section `σ.s` gives
`b`. -/
theorem Splitting.s_comp_add (a : S.X₁ ⟶ M) (b : S.X₃ ⟶ M) :
    σ.s ≫ (σ.r ≫ a + S.g ≫ b) = b := by
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, σ.s_r, σ.s_g, Limits.zero_comp,
    zero_add, Category.id_comp]

/-- For a splitting `σ` of `S`, precomposing `σ.r ≫ a + S.g ≫ b` with `S.f` gives `a`. -/
theorem Splitting.f_comp_add (a : S.X₁ ⟶ M) (b : S.X₃ ⟶ M) :
    S.f ≫ (σ.r ≫ a + S.g ≫ b) = a := by
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, σ.f_r, S.zero, Limits.zero_comp,
    add_zero, Category.id_comp]

/-- For a splitting `σ` of `S`, every morphism `m` out of `S.X₂` equals
`σ.r ≫ (S.f ≫ m) + S.g ≫ (σ.s ≫ m)`. -/
theorem Splitting.eq_add (m : S.X₂ ⟶ M) : m = σ.r ≫ (S.f ≫ m) + S.g ≫ (σ.s ≫ m) := by
  rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, σ.id, Category.id_comp]

end SplitAlgebra

/-- A point `v` of `𝐕(ℱ)` is the image of a point `m` of `𝐕(𝒢)` under `𝐕(g)` iff the module
morphism attached to `v` is `g` followed by the one attached to `m`. -/
private theorem comp_vectorBundleMap_eq_iff {X : Scheme.{u}}
    {F G : SheafOfModules.{u} X.ringCatSheaf} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (g : F ⟶ G) {W : Over X}
    (m : W ⟶ vectorBundleOver X (F := G)) (v : W ⟶ vectorBundleOver X (F := F)) :
    m ≫ vectorBundleMap X g = v ↔
      g ≫ vectorBundleHomEquiv G W m = vectorBundleHomEquiv F W v := by
  rw [← vectorBundleHomEquiv_comp_vectorBundleMap]
  exact (vectorBundleHomEquiv F W).apply_eq_iff_eq.symm

section Split

variable {X : Scheme.{u}} {S : ShortComplex X.Modules} [S.X₁.IsQuasicoherent]
  [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] (σ : S.Splitting)
  {W : Scheme.{u}} (x : W ⟶ vectorBundle X S.X₃) (y : W ⟶ vectorBundle X S.X₁)
  (hxy : x ≫ vectorBundleToBase X S.X₃ = y ≫ vectorBundleToBase X S.X₁)

/-- The point of `𝐕(ℬ)` with components `y` in `𝐕(𝒜)` and `x` in `𝐕(𝒞)`, for a split sequence. -/
def splitLift : Over.mk (y ≫ vectorBundleToBase X S.X₁) ⟶ vectorBundleOver X (F := S.X₂) :=
  (vectorBundleHomEquiv S.X₂ _).symm
    (σ.r ≫ vectorBundleHomEquiv S.X₁ _ (Over.homMk y rfl) +
      S.g ≫ vectorBundleHomEquiv S.X₃ _ (Over.homMk x hxy))

/-- Under `vectorBundleHomEquiv`, the point `splitLift σ x y hxy` of `𝐕(ℬ)` corresponds to
`σ.r ≫ y' + S.g ≫ x'`, where `y'` and `x'` correspond to `y` and `x`. -/
theorem splitLift_spec :
    vectorBundleHomEquiv S.X₂ _ (splitLift σ x y hxy) =
      σ.r ≫ vectorBundleHomEquiv S.X₁ _ (Over.homMk y rfl) +
        S.g ≫ vectorBundleHomEquiv S.X₃ _ (Over.homMk x hxy) :=
  (vectorBundleHomEquiv S.X₂ _).apply_symm_apply _

/-- The image of `splitLift σ x y hxy` in `𝐕(𝒞)` under the map induced by `σ.s` is `x`. -/
theorem splitLift_comp_s :
    splitLift σ x y hxy ≫ vectorBundleMap X σ.s = Over.homMk x hxy := by
  refine (comp_vectorBundleMap_eq_iff _ _ _).2 ?_
  exact (congrArg (σ.s ≫ ·) (splitLift_spec σ x y hxy)).trans (Splitting.s_comp_add σ _ _)

/-- The image of `splitLift σ x y hxy` in `𝐕(𝒜)` under the map induced by `S.f` is `y`. -/
theorem splitLift_comp_f :
    splitLift σ x y hxy ≫ vectorBundleMap X S.f = Over.homMk y rfl := by
  refine (comp_vectorBundleMap_eq_iff _ _ _).2 ?_
  exact (congrArg (S.f ≫ ·) (splitLift_spec σ x y hxy)).trans (Splitting.f_comp_add σ _ _)

/-- A point `m` of `𝐕(ℬ)` whose images in `𝐕(𝒞)` and `𝐕(𝒜)` are `x` and `y` is
`splitLift σ x y hxy`. -/
theorem splitLift_unique
    (m : Over.mk (y ≫ vectorBundleToBase X S.X₁) ⟶ vectorBundleOver X (F := S.X₂))
    (h₁ : m.left ≫ (vectorBundleMap X σ.s).left = x)
    (h₂ : m.left ≫ (vectorBundleMap X S.f).left = y) : m = splitLift σ x y hxy := by
  apply (vectorBundleHomEquiv S.X₂ _).injective
  refine Eq.trans ?_ (splitLift_spec σ x y hxy).symm
  have e₁ := ((comp_vectorBundleMap_eq_iff σ.s m (Over.homMk x hxy)).1 (Over.OverMorphism.ext h₁))
  have e₂ := ((comp_vectorBundleMap_eq_iff S.f m (Over.homMk y rfl)).1 (Over.OverMorphism.ext h₂))
  exact (Splitting.eq_add σ _).trans (congrArg₂ (fun a b => σ.r ≫ a + S.g ≫ b) e₂ e₁)

include σ in
/-- **A split sequence gives a product of vector bundles**: for `ℬ = 𝒜 ⊕ 𝒞`, the square formed by
`𝐕(ℬ) ⟶ 𝐕(𝒞)`, `𝐕(ℬ) ⟶ 𝐕(𝒜)` and the two projections to `X` is cartesian. -/
theorem isPullback_vectorBundleMap_of_splitting :
    IsPullback (vectorBundleMap X σ.s).left (vectorBundleMap X S.f).left
      (vectorBundleToBase X S.X₃) (vectorBundleToBase X S.X₁) :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    ((vectorBundleMap_left_comp X σ.s).trans (vectorBundleMap_left_comp X S.f).symm)
    (fun s => (splitLift σ s.fst s.snd s.condition).left)
    (fun s => congrArg (fun h => h.left) (splitLift_comp_s σ s.fst s.snd s.condition))
    (fun s => congrArg (fun h => h.left) (splitLift_comp_f σ s.fst s.snd s.condition))
    (fun s m h₁ h₂ => congrArg (fun h => h.left)
      (splitLift_unique σ s.fst s.snd s.condition
        (Over.homMk m (by
          rw [← h₂]
          exact (congrArg (m ≫ ·) (vectorBundleMap_left_comp X S.f)).symm.trans
            (Category.assoc _ _ _).symm)) h₁ h₂)))

end Split

section Local

/-- **A property local on the target holds for a morphism restricted to the range of an open
immersion** as soon as it holds for a base change of the morphism along that open immersion. -/
theorem morphismProperty_morphismRestrict_opensRange (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {Y' Y U U' : Scheme.{u}} {q : Y' ⟶ Y} {j : U ⟶ Y} [IsOpenImmersion j]
    {j' : U' ⟶ Y'} {q' : U' ⟶ U} (h : IsPullback j' q' q j) (hq' : P q') :
    P (q ∣_ j.opensRange) := by
  refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange q j)).mpr ?_
  refine (P.arrow_mk_iso_iff (Arrow.isoMk h.isoPullback (Iso.refl _) ?_)).mp hq'
  simp

variable {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
  [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃]

omit [S.X₃.IsQuasicoherent] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] in
/-- Over an open `U` of `X`, the morphism `𝐕(ι^*ℬ) ⟶ 𝐕(ι^*𝒜)` is the base change of
`𝐕(ℬ) ⟶ 𝐕(𝒜)` along the open immersion `𝐕(ι^*𝒜) ⟶ 𝐕(𝒜)`. -/
theorem isPullback_vectorBundleMap_restrict (U : X.Opens) :
    IsPullback (vectorBundleBaseChangeMap U.ι S.X₂)
      (vectorBundleMap U ((Scheme.Modules.pullback U.ι).map S.f)).left
      (vectorBundleMap X S.f).left (vectorBundleBaseChangeMap U.ι S.X₁) := by
  refine IsPullback.of_bot ?_
    (vectorBundleMap_pullback_comp_vectorBundleBaseChangeMap U.ι S.X₁ S.f).symm
    (isPullback_vectorBundleBaseChangeMap U.ι S.X₁)
  refine (isPullback_vectorBundleBaseChangeMap U.ι S.X₂).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans ((vectorBundleMap_left_comp U _).symm.trans
      (Category.id_comp _).symm)
  · exact (Category.comp_id _).trans ((vectorBundleMap_left_comp X S.f).symm.trans
      (Category.id_comp _).symm)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

include hS in
/-- **`𝐕(ℬ) ⟶ 𝐕(𝒜)` has every property local on the target and stable under base change which the
vector bundles of the restrictions of `𝒞` to the opens of `X` have.** The sequence splits locally,
and in the split case the morphism is a base change of `𝐕(𝒞) ⟶ X`. -/
theorem morphismProperty_vectorBundleMap_of_shortExact (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    (hP : ∀ U : X.Opens, P (vectorBundleToBase U ((Scheme.Modules.pullback U.ι).obj S.X₃))) :
    P (vectorBundleMap X S.f).left := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun y => ?_
  obtain ⟨U, hxU, ⟨σ⟩⟩ := exists_nonempty_splitting_restrict_of_isFiniteLocallyFree S hS
    (vectorBundleToBase X S.X₁ y)
  have hU := isPullback_vectorBundleBaseChangeMap U.ι S.X₁
  have : IsOpenImmersion (vectorBundleBaseChangeMap U.ι S.X₁) :=
    MorphismProperty.of_isPullback hU.flip inferInstance
  refine ⟨(vectorBundleBaseChangeMap U.ι S.X₁).opensRange, ?_, ?_⟩
  · have hrange := Scheme.Pullback.range_fst (vectorBundleToBase X S.X₁) U.ι
    have hy : y ∈ Set.range (pullback.fst (vectorBundleToBase X S.X₁) U.ι) := by
      rw [hrange]
      exact ⟨⟨_, hxU⟩, rfl⟩
    obtain ⟨z, hz⟩ := hy
    refine ⟨hU.isoPullback.inv z, ?_⟩
    rw [← hz, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  · refine morphismProperty_morphismRestrict_opensRange P
      (isPullback_vectorBundleMap_restrict S U) ?_
    let σ' : (S.map (Scheme.Modules.pullback U.ι)).Splitting :=
      σ.ofIso (ShortComplex.mapNatIso S (Scheme.Modules.restrictFunctorIsoPullback U.ι))
    have : ((S.map (Scheme.Modules.pullback U.ι)).X₁).IsQuasicoherent :=
      inferInstanceAs (((Scheme.Modules.pullback U.ι).obj S.X₁).IsQuasicoherent)
    have : ((S.map (Scheme.Modules.pullback U.ι)).X₂).IsQuasicoherent :=
      inferInstanceAs (((Scheme.Modules.pullback U.ι).obj S.X₂).IsQuasicoherent)
    have : ((S.map (Scheme.Modules.pullback U.ι)).X₃).IsQuasicoherent :=
      inferInstanceAs (((Scheme.Modules.pullback U.ι).obj S.X₃).IsQuasicoherent)
    exact MorphismProperty.of_isPullback (isPullback_vectorBundleMap_of_splitting σ')
      (hP U)

variable (c : ℕ) [hc : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ c]

omit [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] in
/-- For an open `U` of `X`, the vector bundle of the restriction of `𝒞` to `U` is an affine space
bundle of rank `c` over `U`. -/
theorem isAffineSpaceBundle_vectorBundleToBase_pullback (U : X.Opens) :
    IsAffineSpaceBundle (vectorBundleToBase U ((Scheme.Modules.pullback U.ι).obj S.X₃)) c :=
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback U.ι S.X₃ c
  isAffineSpaceBundle_vectorBundleToBase _ c

include hS hc in
/-- **The morphism `𝐕(ℬ) ⟶ 𝐕(𝒜)` induced by a subbundle is flat.** -/
theorem flat_vectorBundleMap_of_shortExact : Flat (vectorBundleMap X S.f).left := by
  have _ : IsZariskiLocalAtTarget (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat) (Q := RingHom.Flat)
  exact morphismProperty_vectorBundleMap_of_shortExact S hS @Flat fun U =>
    flat_of_isAffineSpaceBundle _ c (isAffineSpaceBundle_vectorBundleToBase_pullback S c U)

include hS hc in
/-- **The morphism `𝐕(ℬ) ⟶ 𝐕(𝒜)` induced by a subbundle is locally of finite type.** -/
theorem locallyOfFiniteType_vectorBundleMap_of_shortExact :
    LocallyOfFiniteType (vectorBundleMap X S.f).left := by
  have _ : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@LocallyOfFiniteType.{u})
  exact morphismProperty_vectorBundleMap_of_shortExact S hS @LocallyOfFiniteType fun U =>
    locallyOfFiniteType_of_isAffineSpaceBundle _ c
      (isAffineSpaceBundle_vectorBundleToBase_pullback S c U)

include hS hc in
/-- **The morphism `𝐕(ℬ) ⟶ 𝐕(𝒜)` induced by a subbundle with locally free quotient of rank `c`
has relative dimension `c`.** -/
theorem relativeDimension_vectorBundleMap_of_shortExact :
    haveI := locallyOfFiniteType_vectorBundleMap_of_shortExact S hS c
    AlgebraicGeometry.RelativeDimension (vectorBundleMap X S.f).left c := by
  have _ : IsZariskiLocalAtTarget (locallyOfFiniteTypeRelativeDimension.{u} c) :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.zariskiPrecoverage_le_fpqcPrecoverage
  have h := morphismProperty_vectorBundleMap_of_shortExact S hS
    (locallyOfFiniteTypeRelativeDimension.{u} c) fun U =>
      have := locallyOfFiniteType_of_isAffineSpaceBundle _ c
        (isAffineSpaceBundle_vectorBundleToBase_pullback S c U)
      ⟨inferInstance, relativeDimension_of_isAffineSpaceBundle _ c
        (isAffineSpaceBundle_vectorBundleToBase_pullback S c U)⟩
  exact h.choose_spec

end Local

end Stacks.Chow

end
