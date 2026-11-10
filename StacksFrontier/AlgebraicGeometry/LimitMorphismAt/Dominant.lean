module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Scheme-theoretic images: density and rigidity

Two facts about Mathlib's scheme-theoretic image `AlgebraicGeometry.Scheme.Hom.image` that
Mathlib itself does not record, and that any statement about inverse systems of
scheme-theoretic images needs.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isSchemeTheoreticallyDominant_toImage`: for a quasi-compact `f`,
  the canonical morphism `X ⟶ f.image` is scheme-theoretically dominant, that is, has trivial
  kernel ideal sheaf. Mathlib has the topological statement
  (`AlgebraicGeometry.Scheme.instIsDominantToImageOfQuasiCompact`) and the class
  `AlgebraicGeometry.IsSchemeTheoreticallyDominant`, but not this instance; it is the
  scheme-theoretic form of Stacks 01R8 part (4). The resulting equation
  `AlgebraicGeometry.Scheme.Hom.ker_toImage` is in
  `StacksFrontier/AlgebraicGeometry/Limits/FiniteTypeSystem.lean`.
* `AlgebraicGeometry.eq_of_isSchemeTheoreticallyDominant`: a scheme-theoretically dominant
  morphism is an epimorphism against pairs of morphisms into a separated target, that is, two
  morphisms out of its codomain that agree after it and agree over the separated base are
  equal. This is the rigidity that replaces a topological "dense image" argument when the
  conclusion wanted is an equality of morphisms of schemes rather than of sets.

## Route

Density is the sheaf-theoretic statement that `𝒪(U)/ker → 𝒪(f⁻¹U)` is injective, which Mathlib
already has as `AlgebraicGeometry.Scheme.Hom.toImage_app_injective`; what is added here is that
the affine opens `f.imageι ⁻¹ᵁ U` for `U` affine in the target cover the image, so the local
statement glues to `ker = ⊥`.

Rigidity is the equalizer argument. For `u v : Z ⟶ W` agreeing over `g : W ⟶ T` the morphism
`CategoryTheory.Limits.pullback.lift u v : Z ⟶ Limits.pullback g g` meets the diagonal of `g`
in a subscheme of `Z` which is closed exactly because `g` is separated; a scheme-theoretically
dominant morphism factoring through a closed subscheme forces that subscheme to be the whole of
`Z`, by `AlgebraicGeometry.IsClosedImmersion.isIso_iff_ker_eq_bot`.

The auxiliary equations `AlgebraicGeometry.Scheme.Hom.ker_imageι` and
`AlgebraicGeometry.Scheme.Hom.ker_imageι_comp` record that the closed embedding of the image has
the same kernel ideal as the morphism itself, and that postcomposing it does not change that
kernel; they need neither quasi-compactness nor density.

## Universe situation

Everything is at a single scheme universe `u`, as in Mathlib's scheme-theoretic image API.

## Transparency gotchas

`AlgebraicGeometry.Scheme.Hom.image` is an `abbrev` for `f.ker.subscheme` and
`AlgebraicGeometry.Scheme.Hom.imageι` an `abbrev` for `f.ker.subschemeι`, so rewriting with
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι` against `f.imageι.ker` relies on that
reducibility; `ker_imageι` below names the resulting equation so that no later proof depends on
it firing.

Binding the pullback vertex and its first projection with `set` in the rigidity proof makes the
instance search for `IsClosedImmersion` run into a deterministic `whnf` timeout, since the
local definitions are unfolded repeatedly; the proof below therefore writes the projections out.

## References

* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8), part (4).

## Not done here

The remaining parts of Stacks 01R8 are not proved: parts (1) and (2) are Mathlib's definition
of `AlgebraicGeometry.Scheme.Hom.image`, and part (3), compatibility of the scheme-theoretic
image with restriction to an open of the target, is not established.

Stacks 01R9, the functoriality `AlgebraicGeometry.Scheme.Hom.imageMap` of the scheme-theoretic
image, is in `StacksFrontier/AlgebraicGeometry/SchemeTheoreticImage/Basic.lean`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {X Y Z W T : Scheme.{u}}

/-- The kernel of the closed embedding of the scheme-theoretic image is the kernel of `f`. -/
lemma Scheme.Hom.ker_imageι (f : X ⟶ Y) : f.imageι.ker = f.ker :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- Composing the closed embedding of the scheme-theoretic image with a further morphism does
not change the kernel. -/
lemma Scheme.Hom.ker_imageι_comp (f : X ⟶ Y) (q : Y ⟶ Z) :
    (f.imageι ≫ q).ker = (f ≫ q).ker := by
  rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_imageι, Scheme.Hom.ker_comp]

/-- The affine opens of the scheme-theoretic image of `f` obtained by restricting an affine
open of the target along the closed embedding `AlgebraicGeometry.Scheme.Hom.imageι`. -/
noncomputable def Scheme.Hom.imageAffineOpens (f : X ⟶ Y) (U : Y.affineOpens) :
    f.image.affineOpens :=
  ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩

/-- The opens `Scheme.Hom.imageAffineOpens f U`, for `U` ranging over the affine opens of the
target, cover the scheme-theoretic image of `f`. -/
lemma Scheme.Hom.iSup_imageAffineOpens (f : X ⟶ Y) :
    ⨆ U : Y.affineOpens, (f.imageAffineOpens U).1 = ⊤ :=
  f.imageι.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y)

/-- The canonical morphism from the source to the scheme-theoretic image has trivial kernel:
the image is the smallest closed subscheme of the target through which `f` factors, so no
proper closed subscheme of it absorbs `f`. -/
instance Scheme.Hom.isSchemeTheoreticallyDominant_toImage (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top f.imageAffineOpens
    f.iSup_imageAffineOpens fun U ↦ ?_
  simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [← RingHom.injective_iff_ker_eq_bot]
  exact f.toImage_app_injective U

/-- A scheme-theoretically dominant morphism `p : X ⟶ Z` is an epimorphism against pairs of
morphisms into a scheme separated over some base: if `u v : Z ⟶ W` agree after composing with
`p` and agree after composing with a separated `g : W ⟶ T`, then `u = v`.

Dominance and separatedness are explicit arguments rather than instances on purpose. At the
point of use `W` is an object of a functor built by a semireducible `def`, so the implicit
scheme arguments of `IsSeparated g` are that functor object rather than the scheme `g` is
literally a morphism out of; the two are definitionally but not reducibly equal, and keyed
instance matching misses the available instance. Passing the proof explicitly checks the types
at default transparency, where they do agree. -/
lemma eq_of_isSchemeTheoreticallyDominant {p : X ⟶ Z} {u v : Z ⟶ W} {g : W ⟶ T}
    (hp : IsSchemeTheoreticallyDominant p) (hsep : IsSeparated g)
    (hg : u ≫ g = v ≫ g) (h : p ≫ u = p ≫ v) :
    u = v := by
  have := hp
  have := hsep
  have hfac : p ≫ pullback.lift u v hg = (p ≫ u) ≫ pullback.diagonal g :=
    pullback.hom_ext (by simp) (by simp [h])
  have hiso : IsIso (pullback.fst (pullback.lift u v hg) (pullback.diagonal g)) := by
    have hle := (pullback.lift p (p ≫ u) hfac).le_ker_comp
      (pullback.fst (pullback.lift u v hg) (pullback.diagonal g))
    rw [pullback.lift_fst, p.ker_eq_bot, le_bot_iff] at hle
    exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hle
  have hcond := pullback.condition (f := pullback.lift u v hg) (g := pullback.diagonal g)
  have e₁ := congrArg (· ≫ pullback.fst g g) hcond
  have e₂ := congrArg (· ≫ pullback.snd g g) hcond
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
    pullback.diagonal_snd, Category.comp_id] at e₁ e₂
  exact (cancel_epi (pullback.fst (pullback.lift u v hg) (pullback.diagonal g))).mp
    (e₁.trans e₂.symm)

end AlgebraicGeometry
