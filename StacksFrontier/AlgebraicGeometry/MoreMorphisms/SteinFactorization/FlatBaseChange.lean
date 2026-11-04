module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.RelativeSpectrum
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Stein factorization commutes with flat base change

Let `f : X ⟶ S` be a universally closed, quasi-separated morphism of schemes, factored as
`X --f'--> S' --π--> S` with `S' = f.normalization`, and let `g : T ⟶ S` be flat.  The base
change `f_T : X ×_S T ⟶ T` is again universally closed and quasi-separated, so it has its own
factorization; this module proves that the two agree, that is, that the intermediate scheme of
the factorization of `f_T` is `T ×_S S'`.

The comparison morphism is Mathlib's `AlgebraicGeometry.Scheme.Hom.normalizationPullback`, which
by `AlgebraicGeometry.Scheme.Hom.normalizationPullback_snd` and
`AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationPullback_fst` carries both factors of
the factorization of `f_T` to the base changes of the factors of `f`.  Mathlib shows it is an
isomorphism for *smooth* `g` ([Stacks, Tag 03GV]); here it is shown to be an isomorphism for
flat `g` under the extra hypothesis that `f` is universally closed, which is the situation of
[Stacks, Tag 03GY].

## Main results

* `Stacks.AlgebraicGeometry.isIso_app_of_isPullback_of_flat` and
  `Stacks.AlgebraicGeometry.isIso_c_of_isPullback_of_flat`: the condition `a_* 𝒪 = 𝒪` on a
  quasi-compact, quasi-separated morphism `a` is stable under flat base change.
* `Stacks.SteinFactorization.isIso_normalizationPullback`: the comparison morphism from the
  normalization of the base change to the base change of the normalization is an isomorphism.
* `Stacks.SteinFactorization.normalizationPullbackIso` and
  `Stacks.SteinFactorization.toNormalization_normalizationPullbackIso_hom_left`: that
  isomorphism, read as an identification over `T` of the two factorizations.

## Implementation notes

The universally closed case is easier than the smooth case because the integral closures
involved are everything.  Over an affine open `U ⊆ S` and an affine open `V ⊆ T` with
`V ⊆ g⁻¹U`, Mathlib's `AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`
identifies `Γ(T, V) ⊗_{Γ(S, U)} Γ(X, f⁻¹U)` with `Γ(X ×_S T, f_T⁻¹V)`; when the ring map
`Γ(S, U) ⟶ Γ(X, f⁻¹U)` is already an isomorphism, one tensor factor is redundant and the other
leg of the pushout is an isomorphism too.  That is
`Stacks.AlgebraicGeometry.isIso_app_of_isPullback_of_flat`, and the affine opens `V ⊆ g⁻¹U`
and their basic opens form a basis of `T`, so the sheaf statement follows by
`Stacks.AlgebraicGeometry.isIso_c_of_isIso_app_basicOpen`.

That general statement is applied not to `f` itself but to its first factor `f'`, which does
satisfy `f'_* 𝒪_X = 𝒪_{S'}` by `Stacks.SteinFactorization.isIso_c_toNormalization`.  Since
`f = f' ≫ π`, the square exhibiting `X ×_S T ⟶ S' ×_S T` as a base change of `f'` along the
flat morphism `S' ×_S T ⟶ S'` is the top square of a two-row pullback diagram, hence cartesian
by `CategoryTheory.IsPullback.of_bot`.  The comparison morphism is then checked to be an
isomorphism on the affine opens `π_T⁻¹V` of `S' ×_S T`, exactly as in
`AlgebraicGeometry.isIso_toPushforwardSpectrum`: its sections map, composed with those of
`(f_T)' : X ×_S T ⟶ (f_T).normalization`, which are an isomorphism because `f_T` is universally
closed, give the sections map of the base-changed first factor.

## References

* [Stacks Project, Tag 03GY](https://stacks.math.columbia.edu/tag/03GY)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 03GV](https://stacks.math.columbia.edu/tag/03GV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry

variable {W Z W' Z' : Scheme.{u}} {v : W' ⟶ W} {a' : W' ⟶ Z'} {a : W ⟶ Z} {u : Z' ⟶ Z}

/-- Let
```
W' --v--> W
|         |
a'        a
v         v
Z' --u--> Z
```
be a cartesian square with `a` quasi-compact and quasi-separated, `u` flat, and
`a_* 𝒪_W = 𝒪_Z`.  Then `Γ(Z', V') ⟶ Γ(W', a'⁻¹V')` is an isomorphism for every affine open
`V' ⊆ Z'` contained in the preimage of an affine open `V ⊆ Z`.

Both the source and the target are base changes along `Γ(Z, V) ⟶ Γ(Z', V')`: the target by
flat base change for the sections of a quasi-compact, quasi-separated morphism, and the source
trivially, since `Γ(Z, V) ⟶ Γ(W, a⁻¹V)` is an isomorphism. -/
public theorem isIso_app_of_isPullback_of_flat (H : IsPullback v a' a u)
    [QuasiCompact a] [QuasiSeparated a] [Flat u] (hc : IsIso a.c)
    {V : Z.Opens} (hV : IsAffineOpen V) {V' : Z'.Opens} (hV' : IsAffineOpen V')
    (hle : V' ≤ u ⁻¹ᵁ V) :
    IsIso (a'.app V') := by
  have hUY : a' ⁻¹ᵁ V' = v ⁻¹ᵁ (a ⁻¹ᵁ V) ⊓ a' ⁻¹ᵁ V' := by
    simp_rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hle]
  have hps := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hle (le_refl (a ⁻¹ᵁ V))
    hUY hV hV' (a.isCompact_preimage hV.isCompact)
    (a.isQuasiSeparated_preimage hV.isQuasiSeparated)
  have hleft : IsIso (a.appLE V (a ⁻¹ᵁ V) le_rfl) := by
    rw [← Scheme.Hom.app_eq_appLE]
    infer_instance
  have hinr : IsIso (pushout.inr (a.appLE V (a ⁻¹ᵁ V) le_rfl) (u.appLE V V' hle)) :=
    (IsPushout.of_hasPushout _ _).isIso_inr_of_isIso
  have heq : pushout.inr (a.appLE V (a ⁻¹ᵁ V) le_rfl) (u.appLE V V' hle) ≫
      pushoutSection H hle (le_refl (a ⁻¹ᵁ V)) hUY = a'.app V' := by
    rw [Scheme.Hom.app_eq_appLE]
    exact pushout.inr_desc _ _ _
  rw [← heq]
  infer_instance

/-- **The condition `a_* 𝒪 = 𝒪` is stable under flat base change.**  For a cartesian square as
in `Stacks.AlgebraicGeometry.isIso_app_of_isPullback_of_flat`, with `a` quasi-compact and
quasi-separated and `u` flat, `a_* 𝒪_W = 𝒪_Z` implies `a'_* 𝒪_{W'} = 𝒪_{Z'}`.

This is [Stacks, Tag 02KH] in degree zero for the structure sheaf, in the special case where
the direct image is the structure sheaf of the base; the affine opens of `Z'` lying over an
affine open of `Z`, and their basic opens, form a basis of `Z'`. -/
@[ega "III 4.3.4" "partial"]
public theorem isIso_c_of_isPullback_of_flat (H : IsPullback v a' a u)
    [QuasiCompact a] [QuasiSeparated a] [Flat u] (hc : IsIso a.c) :
    IsIso a'.c := by
  refine isIso_c_of_isIso_app_basicOpen a'
    (ι := Σ V : Z.affineOpens, { V' : Z'.affineOpens // V'.1 ≤ u ⁻¹ᵁ V.1 })
    (fun p ↦ p.2.1.1) (fun p ↦ p.2.1.2) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
      (show u.base x ∈ (⊤ : Z.Opens) from trivial)
    obtain ⟨V', hV', hxV', hle⟩ := Opens.isBasis_iff_nbhd.mp Z'.isBasis_affineOpens
      (show x ∈ u ⁻¹ᵁ V from hxV)
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, ⟨⟨V', hV'⟩, hle⟩⟩, hxV'⟩
  · intro p r
    exact isIso_app_of_isPullback_of_flat H hc p.1.2 (p.2.1.2.basicOpen r)
      ((Z'.basicOpen_le r).trans p.2.2)

end Stacks.AlgebraicGeometry

namespace Stacks.SteinFactorization

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) [UniversallyClosed f] [QuasiSeparated f]

/-- The base change along `g : T ⟶ S` of the first factor `f' : X ⟶ S'` of the factorization of
`f`, as a morphism `X ×_S T ⟶ S' ×_S T`. -/
private noncomputable def toNormalizationBaseChange :
    pullback f g ⟶ pullback f.fromNormalization g :=
  pullback.map f g f.fromNormalization g f.toNormalization (𝟙 T) (𝟙 S) (by simp) (by simp)

/-- The base-changed first factor is a morphism over `T`. -/
private theorem toNormalizationBaseChange_comp_snd :
    toNormalizationBaseChange f g ≫ pullback.snd f.fromNormalization g = pullback.snd f g :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The base-changed first factor is compatible with the projections to `X` and `S'`. -/
private theorem toNormalizationBaseChange_comp_fst :
    toNormalizationBaseChange f g ≫ pullback.fst f.fromNormalization g =
      pullback.fst f g ≫ f.toNormalization :=
  pullback.lift_fst _ _ _

/-- The square exhibiting `X ×_S T ⟶ S' ×_S T` as the base change of the first factor
`f' : X ⟶ S'` along the projection `S' ×_S T ⟶ S'`: it is the top row of the two-row pullback
diagram obtained from the factorization `f = f' ≫ π`. -/
private theorem isPullback_toNormalizationBaseChange :
    IsPullback (pullback.fst f g) (toNormalizationBaseChange f g) f.toNormalization
      (pullback.fst f.fromNormalization g) := by
  have hs : IsPullback (pullback.fst f g)
      (toNormalizationBaseChange f g ≫ pullback.snd f.fromNormalization g)
      (f.toNormalization ≫ f.fromNormalization) g := by
    rw [toNormalizationBaseChange_comp_snd, Scheme.Hom.toNormalization_fromNormalization]
    exact IsPullback.of_hasPullback f g
  exact hs.of_bot (toNormalizationBaseChange_comp_fst f g).symm
    (IsPullback.of_hasPullback f.fromNormalization g)

/-- The first factor of the factorization of the base change `f_T : X ×_S T ⟶ T` of `f`,
followed by the comparison morphism, is the base change of the first factor of `f`. -/
private theorem toNormalization_normalizationPullback :
    (pullback.snd f g).toNormalization ≫ f.normalizationPullback g =
      toNormalizationBaseChange f g := by
  rw [toNormalizationBaseChange]
  simp [Scheme.Hom.normalizationPullback]

variable [Flat g]

/-- The base-changed first factor still satisfies `(f'_T)_* 𝒪 = 𝒪`, because `g` is flat. -/
@[ega "III 4.3.4" "the clause, special case"]
private theorem isIso_c_toNormalizationBaseChange :
    IsIso (toNormalizationBaseChange f g).c :=
  Stacks.AlgebraicGeometry.isIso_c_of_isPullback_of_flat
    (isPullback_toNormalizationBaseChange f g) (isIso_c_toNormalization f)

/-- The comparison morphism is an isomorphism on sections over the preimage of an affine open
`V ⊆ T`: composed with the sections of the first factor of the factorization of `f_T`, which
are an isomorphism because `f_T` is universally closed, it gives the sections of the
base-changed first factor, which are an isomorphism because `g` is flat. -/
private theorem isIso_normalizationPullback_app (V : T.affineOpens) :
    IsIso ((f.normalizationPullback g).app
      (pullback.snd f.fromNormalization g ⁻¹ᵁ V.1)) := by
  have hpre : f.normalizationPullback g ⁻¹ᵁ (pullback.snd f.fromNormalization g ⁻¹ᵁ V.1) =
      (pullback.snd f g).fromNormalization ⁻¹ᵁ V.1 := by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.normalizationPullback_snd]
  have hfst : IsIso ((pullback.snd f g).toNormalization.app
      (f.normalizationPullback g ⁻¹ᵁ (pullback.snd f.fromNormalization g ⁻¹ᵁ V.1))) := by
    rw [hpre]
    exact isIso_app_toNormalization (pullback.snd f g) V.2
  have hbc : IsIso ((toNormalizationBaseChange f g).app
      (pullback.snd f.fromNormalization g ⁻¹ᵁ V.1)) :=
    have := isIso_c_toNormalizationBaseChange f g
    inferInstance
  have hmap : ∀ {V₁ V₂ : (pullback f g).Opens} (h : V₁ = V₂),
      IsIso ((pullback f g).presheaf.map (eqToHom h).op) := fun _ ↦ inferInstance
  have hcomp : IsIso ((f.normalizationPullback g).app
      (pullback.snd f.fromNormalization g ⁻¹ᵁ V.1) ≫
        (pullback.snd f g).toNormalization.app
          (f.normalizationPullback g ⁻¹ᵁ (pullback.snd f.fromNormalization g ⁻¹ᵁ V.1))) := by
    rw [← Scheme.Hom.comp_app, Scheme.Hom.congr_app (toNormalization_normalizationPullback f g)]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hbc (hmap _)
  exact IsIso.of_isIso_comp_right _ ((pullback.snd f g).toNormalization.app _)

/-- **Stacks Project, Tag 03GY (flat_base_change).**  Formation of the factorization
`f = π ∘ f'` of a universally closed, quasi-separated morphism commutes with flat base change:
the comparison morphism from the normalization of the base change `f_T : X ×_S T ⟶ T` to the
base change `T ×_S S'` of the normalization of `S` in `X` is an isomorphism.

Together with `AlgebraicGeometry.Scheme.Hom.normalizationPullback_snd` and
`AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationPullback_fst`, which say that the
comparison morphism matches the two factors, this is the assertion that the whole factorization
is obtained from that of `f` by base change. -/
@[stacks 03GY "flat_base_change", ega "III 4.3.4" "more general"]
public instance isIso_normalizationPullback : IsIso (f.normalizationPullback g) := by
  have hcov : ⨆ V : T.affineOpens, pullback.snd f.fromNormalization g ⁻¹ᵁ V.1 = ⊤ :=
    (pullback.snd f.fromNormalization g).iSup_preimage_eq_top (iSup_affineOpens_eq_top T)
  have h : MorphismProperty.isomorphisms Scheme.{u} (f.normalizationPullback g) := by
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := MorphismProperty.isomorphisms Scheme.{u}) _ hcov]
    intro V
    exact (isIso_morphismRestrict_iff_isIso_app (f.normalizationPullback g)
      (V.2.preimage (pullback.snd f.fromNormalization g))).mpr
      (isIso_normalizationPullback_app f g V)
  exact h

/-- **Stacks Project, Tag 03GY (flat_base_change).**  The identification, over `T`, of the
intermediate scheme of the factorization of the base change `f_T : X ×_S T ⟶ T` with the base
change `T ×_S S'` of the intermediate scheme of the factorization of `f`. -/
@[stacks 03GY "flat_base_change", ega "III 4.3.4" "more general"]
public noncomputable def normalizationPullbackIso :
    Over.mk (pullback.snd f g).fromNormalization ≅
      Over.mk (pullback.snd f.fromNormalization g) :=
  Over.isoMk (asIso (f.normalizationPullback g)) (Scheme.Hom.normalizationPullback_snd f g)

/-- **Stacks Project, Tag 03GY (flat_base_change).**  Under that identification the first
factor of the factorization of `f_T` becomes the base change of the first factor of `f`. -/
@[stacks 03GY "flat_base_change"]
public theorem toNormalization_normalizationPullbackIso_hom_left :
    (pullback.snd f g).toNormalization ≫ (normalizationPullbackIso f g).hom.left ≫
        pullback.fst f.fromNormalization g = pullback.fst f g ≫ f.toNormalization :=
  Scheme.Hom.toNormalization_normalizationPullback_fst f g

end Stacks.SteinFactorization
