module

public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.FiniteStageContinuity
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Injectivity

/-!
# A Galois-fixed Picard class descends to a finite Galois stage, still fixed

Let `k` be a field, let `X` be a quasi-compact, quasi-separated scheme over `k` with
`H⁰(X, 𝒪_X) = k`, and let `K/k` be a Galois extension. A class of `Pic(X_K)` descends to a finite
subextension (`Stacks.Picard.exists_finiteSubextension_schemePullbackClass_eq`, which is Tag 0B8W
(2) in Picard form). This file adds what the *surjectivity* clause of
[Stacks, Tag 0CDT](https://stacks.math.columbia.edu/tag/0CDT) needs beyond that: if the class is
fixed by `Gal(K/k)`, then it descends to a **finite Galois** subextension `E/k` and the class it
descends to is fixed by `Gal(E/k)`.

The source calls the second point "the transition maps of the directed system are injective"
([Stacks, Tag 0CC5], Varieties Lemma 33.30.3). That is literally what is used here: the
projection `X_K ⟶ X_E` is the base change of `Spec K ⟶ Spec E` along `X_E ⟶ Spec E`, and
`H⁰(X_E, 𝒪) = E` by degree-zero flat base change (Tag 02KH), so Tag 0CC5 makes
`Pic(X_E) → Pic(X_K)` injective. Injectivity turns the identity `σ • x = x` upstairs into
`σ|_E • y = y` downstairs, one `σ` at a time; no enlargement of the stage is needed, and in
particular the argument does not need the eventual-injectivity side of the colimit.

## Main definitions

* `Stacks.Picard.stageProjection` — the projection `X_K ⟶ X_E` at an intermediate field `E`:
  the identity on `X` and the inclusion `E ⊆ K` on `Spec`.
* `Stacks.Picard.stageTransition` — the analogous morphism `X_F ⟶ X_E` for `E ≤ F`.

## Main results

* `Stacks.Picard.isPullback_stageProjection` — `X_K` is the base change of `X_E` along
  `Spec K ⟶ Spec E`. This is what lets Tag 0CC5, stated for a canonical base change, apply to
  `Stacks.Picard.stageProjection`.
* `Stacks.Picard.isIso_appTop_stage` — `H⁰(X_E, 𝒪_{X_E}) = E` follows from `H⁰(X, 𝒪_X) = k` by
  degree-zero flat base change.
* `Stacks.Picard.injective_schemePullbackClass_stageProjection` — **Tag 0CC5 along the stage
  projection**: `Pic(X_E) → Pic(X_K)` is injective.
* `Stacks.Picard.galoisTwist_comp_stageProjection` — the twist by `σ` upstairs is the twist by
  `σ|_E` downstairs: `f_σ ≫ p_E = p_E ≫ f_{σ|_E}`.
* `Stacks.Picard.exists_finiteGaloisSubextension_galoisFixed` — **the reduction of Tag 0CDT to a
  finite Galois extension.** A `Gal(K/k)`-fixed class of `Pic(X_K)` is the pullback of a
  `Gal(E/k)`-fixed class of `Pic(X_E)` for some finite Galois subextension `E/k`.

## Implementation notes

**Why `Stacks.Picard.stageProjection` is a `pullback.lift` rather than a limit projection.** The
morphism is determined by its two legs, so a `pullback.lift` gives both the construction and the
uniqueness (`Stacks.Picard.eq_stageProjection`) in one step; the projection produced by
`Stacks.Picard.exists_finiteSubextension_schemePullbackClass_eq` is identified with it by that
uniqueness, which is how the two halves of the reduction are glued.

**The Galois stage.** The subextension produced by the limit argument is finite but need not be
normal, so it is replaced by its normal closure in `K`
(`IntermediateField.normalClosure`), which is finite (`normalClosure.is_finiteDimensional`) and
normal (`normalClosure.normal`, using that `K/k` is normal) and contains it
(`IntermediateField.le_normalClosure`). The class is carried along by
`Stacks.Picard.stageTransition`.

**Why the stage must be normal.** Only then does `σ ↦ σ|_E` make sense as a map
`Gal(K/k) → Gal(E/k)` (`AlgEquiv.restrictNormal`), and only then is it surjective
(`AlgEquiv.restrictNormalHom_surjective`), which is needed to realise *every* element of
`Gal(E/k)` as the restriction of an element of `Gal(K/k)` and so to conclude that the descended
class is fixed by all of `Gal(E/k)`.

## References

* [Stacks Project, Tag 0CDT](https://stacks.math.columbia.edu/tag/0CDT)
* [Stacks Project, Tag 0CC5](https://stacks.math.columbia.edu/tag/0CC5)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Picard

section Stages

variable {k K : Type u} [Field k] [Field K] [Algebra k K] (X : Over (Spec (.of k)))

/-- `Spec` of a composite of ring homomorphisms is the composite of the `Spec`s, in reverse. -/
private lemma specMap_ofHom_comp_specMap_ofHom {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (g : B →+* C) (h : A →+* C) (H : g.comp f = h) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom h) := by
  rw [← Spec.map_comp, ← H]
  rfl

/-- `Spec` of the inclusion of an intermediate field, followed by the structure morphism of the
intermediate field, is the structure morphism of the extension. -/
lemma specMap_algebraMap_comp_spectrumMap (E : IntermediateField k K) :
    Spec.map (CommRingCat.ofHom (algebraMap E K)) ≫ spectrumMap k E = spectrumMap k K :=
  specMap_ofHom_comp_specMap_ofHom _ _ _ (IsScalarTower.algebraMap_eq k E K).symm

/-- `Spec` of the inclusion of one intermediate field in a larger one, followed by the structure
morphism of the larger one, is the structure morphism of the smaller one. -/
lemma specMap_inclusion_comp_specMap_algebraMap {E F : IntermediateField k K} (h : E ≤ F) :
    Spec.map (CommRingCat.ofHom (algebraMap F K)) ≫
        Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap E K)) :=
  specMap_ofHom_comp_specMap_ofHom _ _ _ (by ext x; rfl)

/-- **The projection of the base change to a stage.** The morphism `X_K ⟶ X_E` which is the
identity on the `X`-coordinate and `Spec` of the inclusion `E ⊆ K` on the other. -/
def stageProjection (E : IntermediateField k K) :
    SchemeOver.baseChange k K X ⟶ pullback X.hom (spectrumMap k E) :=
  pullback.lift (pullback.fst X.hom (spectrumMap k K))
    (pullback.snd X.hom (spectrumMap k K) ≫
      Spec.map (CommRingCat.ofHom (algebraMap E K)))
    (by rw [Category.assoc, specMap_algebraMap_comp_spectrumMap, pullback.condition])

/-- The stage projection `X_K ⟶ X_E` followed by the projection `X_E ⟶ X` is the projection
`X_K ⟶ X`. -/
@[simp]
lemma stageProjection_comp_fst (E : IntermediateField k K) :
    stageProjection X E ≫ pullback.fst X.hom (spectrumMap k E) =
      pullback.fst X.hom (spectrumMap k K) :=
  pullback.lift_fst _ _ _

/-- The stage projection `X_K ⟶ X_E` followed by `X_E ⟶ Spec E` is `X_K ⟶ Spec K` followed by
`Spec` of the inclusion `E ⊆ K`. -/
@[simp]
lemma stageProjection_comp_snd (E : IntermediateField k K) :
    stageProjection X E ≫ pullback.snd X.hom (spectrumMap k E) =
      pullback.snd X.hom (spectrumMap k K) ≫
        Spec.map (CommRingCat.ofHom (algebraMap E K)) :=
  pullback.lift_snd _ _ _

/-- A morphism `X_K ⟶ X_E` over `X` whose `Spec` component is the inclusion `E ⊆ K` is *the*
stage projection. -/
lemma eq_stageProjection (E : IntermediateField k K)
    (p : SchemeOver.baseChange k K X ⟶ pullback X.hom (spectrumMap k E))
    (hp₁ : p ≫ pullback.fst X.hom (spectrumMap k E) =
      pullback.fst X.hom (spectrumMap k K))
    (hp₂ : p ≫ pullback.snd X.hom (spectrumMap k E) =
      pullback.snd X.hom (spectrumMap k K) ≫
        Spec.map (CommRingCat.ofHom (algebraMap E K))) :
    p = stageProjection X E :=
  pullback.hom_ext (hp₁.trans (stageProjection_comp_fst X E).symm)
    (hp₂.trans (stageProjection_comp_snd X E).symm)

/-- `Spec` of the inclusion of one intermediate field in a larger one, followed by the structure
morphism of the smaller one, is the structure morphism of the larger one. -/
lemma specMap_inclusion_comp_spectrumMap {E F : IntermediateField k K} (h : E ≤ F) :
    Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) ≫
        spectrumMap k E = spectrumMap k F :=
  specMap_ofHom_comp_specMap_ofHom _ _ _ (by ext x; rfl)

/-- **The transition morphism between two stages**, `X_F ⟶ X_E` for `E ≤ F`. -/
def stageTransition {E F : IntermediateField k K} (h : E ≤ F) :
    pullback X.hom (spectrumMap k F) ⟶ pullback X.hom (spectrumMap k E) :=
  pullback.lift (pullback.fst X.hom (spectrumMap k F))
    (pullback.snd X.hom (spectrumMap k F) ≫
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom))
    (by rw [Category.assoc, specMap_inclusion_comp_spectrumMap, pullback.condition])

/-- The stage projection at `E` factors through the stage projection at a larger `F`. -/
lemma stageProjection_eq_comp_stageTransition {E F : IntermediateField k K} (h : E ≤ F) :
    stageProjection X E = stageProjection X F ≫ stageTransition X h := by
  refine (eq_stageProjection X E _ ?_ ?_).symm
  · rw [Category.assoc, show stageTransition X h ≫ pullback.fst X.hom (spectrumMap k E) =
      pullback.fst X.hom (spectrumMap k F) from pullback.lift_fst _ _ _,
      stageProjection_comp_fst]
  · rw [Category.assoc, show stageTransition X h ≫ pullback.snd X.hom (spectrumMap k E) =
      pullback.snd X.hom (spectrumMap k F) ≫
        Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) from
      pullback.lift_snd _ _ _, ← Category.assoc, stageProjection_comp_snd, Category.assoc,
      specMap_inclusion_comp_specMap_algebraMap]

/-- **`X_K` is the base change of `X_E` along `Spec K ⟶ Spec E`.** The outer square is the base
change of `X` to `K` and the right square is the base change of `X` to `E`, so the left square is
a pullback. -/
lemma isPullback_stageProjection (E : IntermediateField k K) :
    IsPullback (stageProjection X E) (pullback.snd X.hom (spectrumMap k K))
      (pullback.snd X.hom (spectrumMap k E))
      (Spec.map (CommRingCat.ofHom (algebraMap E K))) := by
  refine IsPullback.of_right ?_ (stageProjection_comp_snd X E)
    (IsPullback.of_hasPullback X.hom (spectrumMap k E))
  rw [stageProjection_comp_fst, specMap_algebraMap_comp_spectrumMap]
  exact IsPullback.of_hasPullback X.hom (spectrumMap k K)

end Stages

section Injectivity

variable {k K : Type u} [Field k] [Field K] [Algebra k K] (X : Over (Spec (.of k)))
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]

/-- The stage `X_E` is quasi-compact: it is affine over `X`. -/
instance compactSpace_stage (E : IntermediateField k K) :
    CompactSpace (pullback X.hom (spectrumMap k E) : Scheme.{u}) :=
  letI : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) X.hom :=
    ⟨fun sq H => isAffineHom_isStableUnderBaseChange.of_isPullback sq H⟩
  letI : IsAffineHom (pullback.snd (spectrumMap k E) X.hom) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  letI : IsAffineHom (pullback.fst X.hom (spectrumMap k E)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  inferInstance

/-- The stage `X_E` is quasi-separated: it is affine over `X`. -/
instance quasiSeparatedSpace_stage (E : IntermediateField k K) :
    QuasiSeparatedSpace (pullback X.hom (spectrumMap k E) : Scheme.{u}) :=
  letI : MorphismProperty.IsStableUnderBaseChangeAlong (@QuasiSeparated) X.hom :=
    ⟨fun sq H => quasiSeparated_isStableUnderBaseChange.of_isPullback sq H⟩
  letI : QuasiSeparated (pullback.fst X.hom (spectrumMap k E)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst X.hom (spectrumMap k E))

/-- **`H⁰(X_E, 𝒪_{X_E}) = E`.** Degree-zero flat base change (Tag 02KH) makes the square of
global sections a pushout, and a pushout of an isomorphism is an isomorphism. -/
lemma isIso_appTop_stage (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop))
    (E : IntermediateField k K) :
    IsIso ((Scheme.ΓSpecIso (.of (E : IntermediateField k K))).inv ≫
      (pullback.snd X.hom (spectrumMap k E)).appTop) := by
  have hfl : (algebraMap k (E : IntermediateField k K)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have : IsIso X.hom.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv _
  have := (Stacks.AlgebraicGeometry.PicardBaseChange.isPushout_appTop_baseChange hfl
    X.hom).isIso_inr_of_isIso
  infer_instance

/-- **Tag 0CC5 along the stage projection.** Pullback `Pic(X_E) → Pic(X_K)` along the stage
projection is injective: `X_K` is the base change of `X_E` along the field extension `K/E`, and
`H⁰(X_E, 𝒪) = E`. -/
theorem injective_schemePullbackClass_stageProjection
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop))
    (E : IntermediateField k K) :
    Function.Injective (schemePullbackClass (stageProjection X E)) := by
  let e := (isPullback_stageProjection X E).isoPullback
  have hinj : Function.Injective (schemePullbackClass e.hom) :=
    Function.LeftInverse.injective (g := schemePullbackClass e.inv) fun u => by
      rw [schemePullbackClass_comp, e.inv_hom_id, schemePullbackClass_id]
  rw [← (isPullback_stageProjection X E).isoPullback_hom_fst]
  intro z w hzw
  refine injective_schemePullbackClass_of_globalSectionsIso
    (algebraMap (E : IntermediateField k K) K) (pullback.snd X.hom (spectrumMap k E))
    (isIso_appTop_stage X hΓ E) (hinj ?_)
  rwa [schemePullbackClass_comp, schemePullbackClass_comp]

end Injectivity

section Fixed

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  (X : Over (Spec (.of k)))

omit [IsGalois k K] in
/-- **The twist by `σ` upstairs is the twist by `σ|_E` downstairs.** For a normal intermediate
field `E`, the automorphism `id_X × Spec(σ)` of `X_K` followed by the projection to `X_E` is the
projection followed by `id_X × Spec(σ|_E)`. -/
lemma galoisTwist_comp_stageProjection (E : IntermediateField k K)
    [Normal k (E : IntermediateField k K)] (σ : K ≃ₐ[k] K) :
    galoisTwist k K X σ ≫ stageProjection X E =
      stageProjection X E ≫ galoisTwist k (E : IntermediateField k K) X
        (σ.restrictNormal (E : IntermediateField k K)) := by
  have hring : specMapAlgAut k K σ ≫
        Spec.map (CommRingCat.ofHom (algebraMap (E : IntermediateField k K) K)) =
      Spec.map (CommRingCat.ofHom (algebraMap (E : IntermediateField k K) K)) ≫
        specMapAlgAut k (E : IntermediateField k K) (σ.restrictNormal E) := by
    rw [show specMapAlgAut k (E : IntermediateField k K)
          (σ.restrictNormal (E : IntermediateField k K)) =
        Spec.map (CommRingCat.ofHom
          (σ.restrictNormal (E : IntermediateField k K)).toRingEquiv.toRingHom) from rfl,
      show specMapAlgAut k K σ = Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) from rfl,
      ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
    refine congrArg CommRingCat.ofHom ?_
    ext x
    exact (σ.restrictNormal_commutes (E : IntermediateField k K) x).symm
  have hK : galoisTwist k K X σ ≫ pullback.snd X.hom (spectrumMap k K) =
      pullback.snd X.hom (spectrumMap k K) ≫ specMapAlgAut k K σ :=
    galoisTwist_comp_snd k K X σ
  have hE : galoisTwist k (E : IntermediateField k K) X (σ.restrictNormal E) ≫
      pullback.snd X.hom (spectrumMap k E) =
      pullback.snd X.hom (spectrumMap k E) ≫
        specMapAlgAut k (E : IntermediateField k K) (σ.restrictNormal E) :=
    galoisTwist_comp_snd k (E : IntermediateField k K) X _
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, stageProjection_comp_fst, galoisTwist_comp_fst,
      galoisTwist_comp_fst, stageProjection_comp_fst]
  · rw [Category.assoc, Category.assoc, hE, stageProjection_comp_snd, reassoc_of% hK, hring,
      reassoc_of% stageProjection_comp_snd]

variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]

/-- **The reduction of Stacks Tag 0CDT to a finite Galois extension.** Let `X` be a quasi-compact,
quasi-separated scheme over a field `k` with `H⁰(X, 𝒪_X) = k`, and let `K/k` be a Galois
extension. A class of `Pic(X_K)` fixed by `Gal(K/k)` is the pullback, along the stage projection,
of a class of `Pic(X_E)` fixed by `Gal(E/k)`, for some finite Galois subextension `E/k`.

The descent to a finite stage is Tag 0B8W (2) in Picard form
(`Stacks.Picard.exists_finiteSubextension_schemePullbackClass_eq`), the stage is replaced by its
normal closure, and the fixedness of the descended class is read off the injectivity of
Tag 0CC5 (`Stacks.Picard.injective_schemePullbackClass_stageProjection`). -/
theorem exists_finiteGaloisSubextension_galoisFixed
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop))
    (x : ofScheme (SchemeOver.baseChange k K X)) (hx : x ∈ galoisFixedClasses k K X) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E) (_ : Normal k E)
      (y : ofScheme (pullback X.hom (spectrumMap k E))),
      schemePullbackClass (stageProjection X E) y = x ∧
        ∀ τ : (E : IntermediateField k K) ≃ₐ[k] (E : IntermediateField k K),
          schemePullbackClass (galoisTwist k (E : IntermediateField k K) X τ) y = y := by
  obtain ⟨E₀, hE₀, p, y₀, hp₁, hp₂, hpy⟩ :=
    exists_finiteSubextension_schemePullbackClass_eq X x
  let := hE₀
  -- replace the stage by its normal closure in `K`
  let E : IntermediateField k K := IntermediateField.normalClosure k E₀ K
  let : FiniteDimensional k (E : IntermediateField k K) :=
    normalClosure.is_finiteDimensional k E₀ K
  let : Normal k (E : IntermediateField k K) := normalClosure.normal k E₀ K
  have hle : E₀ ≤ E := IntermediateField.le_normalClosure E₀
  have hy : schemePullbackClass (stageProjection X E)
      (schemePullbackClass (stageTransition X hle) y₀) = x := by
    rwa [schemePullbackClass_comp, ← stageProjection_eq_comp_stageTransition,
      ← eq_stageProjection X E₀ p hp₁ hp₂]
  refine ⟨E, inferInstance, inferInstance, _, hy, fun τ => ?_⟩
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := E) (E := K) τ
  have hστ : σ.restrictNormal (E : IntermediateField k K) = τ := hσ
  refine injective_schemePullbackClass_stageProjection X hΓ E ?_
  rw [schemePullbackClass_comp, ← hστ, ← galoisTwist_comp_stageProjection X E σ,
    ← schemePullbackClass_comp, hy]
  exact hx σ

end Fixed

end Stacks.Picard

end
