module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coinduction of a quasi-coherent module along a groupoid scheme

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `s` and `t` flat, quasi-compact and
quasi-separated, and let `𝒢` be a quasi-coherent module on `U`.  Then `s_* t^* 𝒢` is again
quasi-coherent, and it carries a canonical isomorphism
`α : t^* s_* t^* 𝒢 ≅ s^* s_* t^* 𝒢`, natural in `𝒢`.

The isomorphism is built from the two cartesian squares of the composition diagram of the
groupoid.  Flat base change in degree zero turns the left-hand side into
`pr_{1, *} pr_0^* t^* 𝒢` and the right-hand side into `pr_{1, *} c^* t^* 𝒢`, and the two agree
because `t ∘ c = t ∘ pr_0`.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.coinductionTargetBaseChange` and
  `Stacks.Groupoids.GroupoidScheme.coinductionSourceBaseChange` are the base-change morphisms
  `t^* s_* ⟶ pr_{1, *} pr_0^*` and `s^* s_* ⟶ pr_{1, *} c^*` of the two squares, and
  `..._Iso` are those morphisms as isomorphisms at a quasi-coherent module.
* `Stacks.Groupoids.GroupoidScheme.coinductionComparison` is the canonical identification
  `pr_0^* t^* ≅ c^* t^*` of functors, coming from `t ∘ c = t ∘ pr_0`.
* `Stacks.Groupoids.GroupoidScheme.coinductionAlpha` is the canonical isomorphism
  `α : t^* s_* t^* 𝒢 ≅ s^* s_* t^* 𝒢` of Tag 07TR.

## Main results

* `Stacks.Groupoids.GroupoidScheme.isPullback_composableArrows` and
  `Stacks.Groupoids.GroupoidScheme.isPullback_comp_snd_source` are the two cartesian squares,
  on underlying schemes.
* `Stacks.Groupoids.GroupoidScheme.isQuasicoherent_pushforwardSource_pullbackTarget` says that
  `s_* t^* 𝒢` is quasi-coherent.
* `Stacks.Groupoids.GroupoidScheme.coinductionAlpha_naturality` says that `α` is natural in
  `𝒢`, which is the sense in which it is canonical.

## Implementation notes

The two cartesian squares are the ones already available for a groupoid scheme: the defining
square of the scheme of composable arrows, and the square formed by composition and the second
projection over two copies of the source map, which says that a composable pair of arrows is
determined by its second member together with its composite.  Both are squares in
`CategoryTheory.Over S`; they are transported to the underlying schemes by
`CategoryTheory.Over.forget`, which preserves pullbacks.

What this file establishes is the construction of `α`, its naturality, and the quasi-coherence
of `s_* t^* 𝒢`, and the three tag attributes say so.  The cocycle condition and the
normalization along the identity section, which together make `(s_* t^* 𝒢, α)` a quasi-coherent
module on the groupoid, and the right adjointness of the resulting functor to the forgetful
functor, come in the source from a second description of the same construction:  pushforward
along the morphism of groupoid schemes built from `s` and `(r_0, r_1) ↦ r_0^{-1} ∘ r_1`, out of
the groupoid scheme attached to the equivalence relation `R ×_{t, U, t} R` on `R`, composed
with the descent equivalence for the fpqc covering `{t : R ⟶ U}`.  That route needs the second
groupoid scheme and the descent equivalence, and is left to a later file.

Inverse images of modules form a pseudofunctor rather than a strictly functorial operation, so
`coinductionComparison` carries the canonical comparison isomorphisms between an iterated
inverse image and the inverse image along the composite.

## References

* [Stacks Project, Tag 07TR](https://stacks.math.columbia.edu/tag/07TR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

namespace GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The defining square of the scheme of composable arrows is cartesian on underlying
schemes. -/
theorem isPullback_composableArrows :
    IsPullback (pullback.fst G.source G.target).left
      (pullback.snd G.source G.target).left G.source.left G.target.left :=
  (IsPullback.of_hasPullback G.source G.target).map (Over.forget S)

/-- Composition and the second projection, over two copies of the source map, form a cartesian
square on underlying schemes. -/
@[sga "3 V 1.2" "(2)"]
theorem isPullback_comp_snd_source :
    IsPullback G.comp.left (pullback.snd G.source G.target).left G.source.left
      G.source.left :=
  (comp_source_isPullback G).map (Over.forget S)

/-- The base-change morphism `t^* s_* ⟶ pr_{1, *} pr_0^*` of the defining square of the scheme
of composable arrows. -/
noncomputable def coinductionTargetBaseChange :
    Scheme.Modules.pushforward G.source.left ⋙ Scheme.Modules.pullback G.target.left ⟶
      Scheme.Modules.pullback (pullback.fst G.source G.target).left ⋙
        Scheme.Modules.pushforward (pullback.snd G.source G.target).left :=
  Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
    (isPullback_composableArrows G).w

/-- The base-change morphism `s^* s_* ⟶ pr_{1, *} c^*` of the square formed by composition and
the second projection over two copies of the source map. -/
noncomputable def coinductionSourceBaseChange :
    Scheme.Modules.pushforward G.source.left ⋙ Scheme.Modules.pullback G.source.left ⟶
      Scheme.Modules.pullback G.comp.left ⋙
        Scheme.Modules.pushforward (pullback.snd G.source G.target).left :=
  Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
    (isPullback_comp_snd_source G).w

section BaseChange

variable [QuasiCompact G.source.left] [QuasiSeparated G.source.left]

/-- At a quasi-coherent module, the base-change morphism of the defining square of the scheme of
composable arrows is an isomorphism. -/
theorem isIso_coinductionTargetBaseChange_app [Flat G.target.left]
    (F : G.arrows.left.Modules) [F.IsQuasicoherent] :
    IsIso ((coinductionTargetBaseChange G).app F) :=
  Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
    (isPullback_composableArrows G) F

/-- At a quasi-coherent module, the base-change morphism of the square formed by composition and
the second projection is an isomorphism. -/
theorem isIso_coinductionSourceBaseChange_app [Flat G.source.left]
    (F : G.arrows.left.Modules) [F.IsQuasicoherent] :
    IsIso ((coinductionSourceBaseChange G).app F) :=
  Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
    (isPullback_comp_snd_source G) F

/-- The base-change isomorphism `t^* s_* ℱ ≅ pr_{1, *} pr_0^* ℱ` at a quasi-coherent module. -/
noncomputable def coinductionTargetBaseChangeIso [Flat G.target.left]
    (F : G.arrows.left.Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pullback G.target.left).obj
        ((Scheme.Modules.pushforward G.source.left).obj F) ≅
      (Scheme.Modules.pushforward (pullback.snd G.source G.target).left).obj
        ((Scheme.Modules.pullback (pullback.fst G.source G.target).left).obj F) :=
  have := isIso_coinductionTargetBaseChange_app G F
  asIso ((coinductionTargetBaseChange G).app F)

/-- The forward direction of the target base-change isomorphism is the base-change morphism. -/
@[simp]
theorem coinductionTargetBaseChangeIso_hom [Flat G.target.left]
    (F : G.arrows.left.Modules) [F.IsQuasicoherent] :
    (coinductionTargetBaseChangeIso G F).hom = (coinductionTargetBaseChange G).app F :=
  rfl

/-- The base-change isomorphism `s^* s_* ℱ ≅ pr_{1, *} c^* ℱ` at a quasi-coherent module. -/
noncomputable def coinductionSourceBaseChangeIso [Flat G.source.left]
    (F : G.arrows.left.Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pullback G.source.left).obj
        ((Scheme.Modules.pushforward G.source.left).obj F) ≅
      (Scheme.Modules.pushforward (pullback.snd G.source G.target).left).obj
        ((Scheme.Modules.pullback G.comp.left).obj F) :=
  have := isIso_coinductionSourceBaseChange_app G F
  asIso ((coinductionSourceBaseChange G).app F)

/-- The forward direction of the source base-change isomorphism is the base-change morphism. -/
@[simp]
theorem coinductionSourceBaseChangeIso_hom [Flat G.source.left]
    (F : G.arrows.left.Modules) [F.IsQuasicoherent] :
    (coinductionSourceBaseChangeIso G F).hom = (coinductionSourceBaseChange G).app F :=
  rfl

end BaseChange

/-- The inverse image along the target of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_pullbackTarget (𝒢 : G.objects.left.Modules) [𝒢.IsQuasicoherent] :
    ((Scheme.Modules.pullback G.target.left).obj 𝒢).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback G.target.left 𝒢

/-- **The first assertion of Tag 07TR.**  For a groupoid scheme whose source map is
quasi-compact and quasi-separated, the module `s_* t^* 𝒢` is quasi-coherent. -/
@[stacks 07TR "the quasi-coherence of `s_* t^* 𝒢`"]
theorem isQuasicoherent_pushforwardSource_pullbackTarget
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left]
    (𝒢 : G.objects.left.Modules) [𝒢.IsQuasicoherent] :
    ((Scheme.Modules.pushforward G.source.left).obj
      ((Scheme.Modules.pullback G.target.left).obj 𝒢)).IsQuasicoherent :=
  have := isQuasicoherent_pullbackTarget G 𝒢
  inferInstance

/-- The canonical identification `pr_0^* t^* ≅ c^* t^*`, coming from the equality
`t ∘ c = t ∘ pr_0` of morphisms from the scheme of composable arrows to the object scheme. -/
noncomputable def coinductionComparison :
    Scheme.Modules.pullback G.target.left ⋙
        Scheme.Modules.pullback (pullback.fst G.source G.target).left ≅
      Scheme.Modules.pullback G.target.left ⋙ Scheme.Modules.pullback G.comp.left :=
  Scheme.Modules.pullbackComp (pullback.fst G.source G.target).left G.target.left ≪≫
    Scheme.Modules.pullbackCongr (congrArg Over.Hom.left G.target_comp).symm ≪≫
    (Scheme.Modules.pullbackComp G.comp.left G.target.left).symm

/-- The comparison `pr_0^* t^* 𝒢 ≅ c^* t^* 𝒢` is natural in `𝒢`. -/
theorem coinductionComparison_naturality {𝒢 𝒢' : G.objects.left.Modules} (φ : 𝒢 ⟶ 𝒢') :
    (coinductionComparison G).hom.app 𝒢 ≫
        (Scheme.Modules.pullback G.comp.left).map
          ((Scheme.Modules.pullback G.target.left).map φ) =
      (Scheme.Modules.pullback (pullback.fst G.source G.target).left).map
          ((Scheme.Modules.pullback G.target.left).map φ) ≫
        (coinductionComparison G).hom.app 𝒢' :=
  ((coinductionComparison G).hom.naturality φ).symm

/-- **The canonical isomorphism `α` of Tag 07TR.**  For a groupoid scheme `(U, R, s, t, c)` with
`s` and `t` flat, quasi-compact and quasi-separated and a quasi-coherent module `𝒢` on `U`, this
is the canonical isomorphism `t^* s_* t^* 𝒢 ≅ s^* s_* t^* 𝒢`.  It is the composite of the two
flat base-change isomorphisms of the squares of the composition diagram with the identification
of `pr_0^* t^* 𝒢` and `c^* t^* 𝒢`.

This does not include the cocycle condition and the normalization along the identity section,
which are what make `(s_* t^* 𝒢, α)` a quasi-coherent module on the groupoid scheme. -/
@[stacks 07TR "the construction of the canonical isomorphism `α`; not the cocycle and \
identity conditions making `(s_* t^* 𝒢, α)` a module on the groupoid, and not the functor \
to `QCoh(U, R, s, t, c)` nor its right adjointness to the forgetful functor"]
noncomputable def coinductionAlpha [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left]
    (𝒢 : G.objects.left.Modules) [𝒢.IsQuasicoherent] :
    (Scheme.Modules.pullback G.target.left).obj
        ((Scheme.Modules.pushforward G.source.left).obj
          ((Scheme.Modules.pullback G.target.left).obj 𝒢)) ≅
      (Scheme.Modules.pullback G.source.left).obj
        ((Scheme.Modules.pushforward G.source.left).obj
          ((Scheme.Modules.pullback G.target.left).obj 𝒢)) :=
  have := isQuasicoherent_pullbackTarget G 𝒢
  coinductionTargetBaseChangeIso G ((Scheme.Modules.pullback G.target.left).obj 𝒢) ≪≫
    (Scheme.Modules.pushforward (pullback.snd G.source G.target).left).mapIso
      ((coinductionComparison G).app 𝒢) ≪≫
    (coinductionSourceBaseChangeIso G ((Scheme.Modules.pullback G.target.left).obj 𝒢)).symm

/-- The canonical isomorphism `α` is natural in `𝒢`, which is the sense in which the
construction `𝒢 ↦ (s_* t^* 𝒢, α)` is canonical. -/
@[stacks 07TR "the naturality of `α` in `𝒢`"]
theorem coinductionAlpha_naturality [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left]
    {𝒢 𝒢' : G.objects.left.Modules} [𝒢.IsQuasicoherent] [𝒢'.IsQuasicoherent]
    (φ : 𝒢 ⟶ 𝒢') :
    (coinductionAlpha G 𝒢).hom ≫
        (Scheme.Modules.pullback G.source.left).map
          ((Scheme.Modules.pushforward G.source.left).map
            ((Scheme.Modules.pullback G.target.left).map φ)) =
      (Scheme.Modules.pullback G.target.left).map
          ((Scheme.Modules.pushforward G.source.left).map
            ((Scheme.Modules.pullback G.target.left).map φ)) ≫
        (coinductionAlpha G 𝒢').hom := by
  have h𝒢 := isQuasicoherent_pullbackTarget G 𝒢
  have h𝒢' := isQuasicoherent_pullbackTarget G 𝒢'
  have hT := (coinductionTargetBaseChange G).naturality
    ((Scheme.Modules.pullback G.target.left).map φ)
  have hS := (coinductionSourceBaseChange G).naturality
    ((Scheme.Modules.pullback G.target.left).map φ)
  simp only [Functor.comp_map] at hT hS
  have hSinv : (coinductionSourceBaseChangeIso G
          ((Scheme.Modules.pullback G.target.left).obj 𝒢)).inv ≫
        (Scheme.Modules.pullback G.source.left).map
          ((Scheme.Modules.pushforward G.source.left).map
            ((Scheme.Modules.pullback G.target.left).map φ)) =
      (Scheme.Modules.pushforward (pullback.snd G.source G.target).left).map
          ((Scheme.Modules.pullback G.comp.left).map
            ((Scheme.Modules.pullback G.target.left).map φ)) ≫
        (coinductionSourceBaseChangeIso G
          ((Scheme.Modules.pullback G.target.left).obj 𝒢')).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
      coinductionSourceBaseChangeIso_hom, coinductionSourceBaseChangeIso_hom]
    exact hS
  simp only [coinductionAlpha, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [hSinv, ← Functor.map_comp_assoc, coinductionComparison_naturality G φ,
    Functor.map_comp_assoc]
  rw [coinductionTargetBaseChangeIso_hom, coinductionTargetBaseChangeIso_hom,
    ← Category.assoc, ← hT, Category.assoc]

end GroupoidScheme

end Stacks.Groupoids

end
