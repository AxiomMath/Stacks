module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute

/-!
# Scheme-theoretically dense open subschemes

An open subscheme `U` of a scheme `X` is *scheme-theoretically dense* when, for every open
subscheme `V` of `X`, the scheme-theoretic image of `U ∩ V` in `V` is all of `V`. This is
strictly stronger than topological density: it sees nilpotents supported away from `U`.

Scheme-theoretic density is stable under intersection, and two morphisms of `S`-schemes into a
separated `S`-scheme that agree on an open subscheme whose scheme-theoretic closure is the whole
source are equal.

## Main definitions

* `AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense`: scheme-theoretic density of an
  open subscheme.

## Main results

* `AlgebraicGeometry.Scheme.Opens.isSchemeTheoreticallyDense_inf`: the intersection of two
  scheme-theoretically dense opens is scheme-theoretically dense.
* `AlgebraicGeometry.eq_of_isSchemeTheoreticallyDominant_ι`: morphisms of `S`-schemes into a
  separated `S`-scheme which agree on an open subscheme whose scheme-theoretic closure is the
  whole source are equal.
* `AlgebraicGeometry.eq_of_isSchemeTheoreticallyDense`: the same conclusion under the stronger
  hypothesis that the open subscheme is scheme-theoretically dense.
* `AlgebraicGeometry.Scheme.Opens.isSchemeTheoreticallyDense_iff_isSchemeTheoreticallyDominant`:
  an open subscheme with quasi-compact inclusion is scheme-theoretically dense if and only if
  its scheme-theoretic closure is the whole scheme.
* `AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isIso_imageι`: a morphism is
  scheme-theoretically dominant if and only if its scheme-theoretic image is the whole target.

## References

* [Stacks Project, Tag 01RB](https://stacks.math.columbia.edu/tag/01RB)
* [Stacks Project, Tag 01RD](https://stacks.math.columbia.edu/tag/01RD)
* [Stacks Project, Tag 01RF](https://stacks.math.columbia.edu/tag/01RF)
* [Stacks Project, Tag 01RH](https://stacks.math.columbia.edu/tag/01RH)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

add_to_stacks 01RB "part (1): the scheme-theoretic closure of an open subscheme"
  AlgebraicGeometry.Scheme.Hom.image

/-- A morphism is scheme-theoretically dominant exactly when the inclusion of its
scheme-theoretic image into the target is an isomorphism, that is, when its scheme-theoretic
image is the whole target. For the inclusion `U.ι` of an open subscheme `U ⊆ X` this says that
the scheme-theoretic closure of `U` in `X` is `X`. -/
theorem isSchemeTheoreticallyDominant_iff_isIso_imageι {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSchemeTheoreticallyDominant f ↔ IsIso f.imageι :=
  (isSchemeTheoreticallyDominant_iff f).trans
    (Scheme.isIso_subschemeι_iff_eq_bot f.ker).symm

namespace Scheme.Opens

/-- An open subscheme `U` of `X` is scheme-theoretically dense if, for every open subscheme
`V` of `X`, the scheme-theoretic image in `V` of `U ∩ V` is all of `V`. -/
@[stacks 01RB "part (2)", sga "3 IX 4.1" "single open subscheme"]
abbrev IsSchemeTheoreticallyDense {X : Scheme.{u}} (U : X.Opens) : Prop :=
  ∀ V : X.Opens, IsSchemeTheoreticallyDominant ((V.ι ⁻¹ᵁ U).ι)

/-- The intersection of scheme-theoretically dense open subschemes is
scheme-theoretically dense. -/
@[stacks 01RF]
theorem isSchemeTheoreticallyDense_inf {X : Scheme.{u}} (U V : X.Opens)
    (hU : IsSchemeTheoreticallyDense U)
    (hV : IsSchemeTheoreticallyDense V) :
    IsSchemeTheoreticallyDense (U ⊓ V) := by
  intro W
  let A : W.toScheme.Opens := W.ι ⁻¹ᵁ U
  have : IsSchemeTheoreticallyDominant A.ι := hU W
  let e : A.toScheme ≅ (W ⊓ U : X.Opens) :=
    W.ι.isoImage A ≪≫ Scheme.isoOfEq X (by
      simp [A, Scheme.Hom.image_preimage_eq_opensRange_inf, inf_comm])
  let B : (W ⊓ U : X.Opens).toScheme.Opens := (W ⊓ U).ι ⁻¹ᵁ V
  have : IsSchemeTheoreticallyDominant B.ι := hV (W ⊓ U)
  let l : ((W ⊓ U : X.Opens) : Scheme) ⟶ W.toScheme := e.inv ≫ A.ι
  let g : B.toScheme ⟶ W.toScheme := B.ι ≫ l
  let T : W.toScheme.Opens := W.ι ⁻¹ᵁ (U ⊓ V)
  let f : T.toScheme ⟶ W.toScheme := T.ι
  let fX : T.toScheme ⟶ X := f ≫ W.ι
  let gX : B.toScheme ⟶ X := g ≫ W.ι
  have hlcomp : l ≫ W.ι = (W ⊓ U).ι := by
    dsimp [l, e]
    simp [Scheme.isoOfEq_inv_ι]
  have hgX : gX = B.ι ≫ (W ⊓ U).ι := by
    dsimp [gX, g]
    rw [Category.assoc, hlcomp]
  have hrangeO : fX.opensRange = gX.opensRange := by
    simp only [hgX]
    simp [fX, f, T, B, Scheme.Hom.opensRange_comp,
      Scheme.Hom.image_preimage_eq_opensRange_inf, inf_assoc]
  have hrange : Set.range ⇑fX = Set.range ⇑gX := by
    simpa only [Scheme.Hom.coe_opensRange] using
      congrArg (fun Z : X.Opens => (Z : Set X)) hrangeO
  let iso : T.toScheme ≅ B.toScheme := IsOpenImmersion.isoOfRangeEq fX gX hrange
  have hfac : iso.hom ≫ g = f := by
    apply (cancel_mono W.ι).1
    change iso.hom ≫ gX = fX
    simp [iso, IsOpenImmersion.isoOfRangeEq_hom_fac]
  change IsSchemeTheoreticallyDominant f
  rw [← hfac]
  infer_instance

/-- The inclusion of a scheme-theoretically dense open subscheme is scheme-theoretically
dominant. -/
private theorem isSchemeTheoreticallyDominant_ι_of_isSchemeTheoreticallyDense
    {X : Scheme.{u}} {U : X.Opens} (hU : IsSchemeTheoreticallyDense U) :
    IsSchemeTheoreticallyDominant U.ι := by
  have hi : IsIso ((⊤ : X.Opens).ι) := inferInstanceAs (IsIso (Scheme.topIso X).hom)
  refine ⟨?_⟩
  rw [← Scheme.Hom.ker_comp_of_isIso ((⊤ : X.Opens).ι.preimageIso U).hom U.ι,
    Scheme.Hom.preimageIso_hom_ι, Scheme.Hom.ker_comp, (hU ⊤).ker_eq_bot,
    Scheme.IdealSheafData.map_bot]
  exact (⊤ : X.Opens).ι.ker_eq_bot

/-- An open subscheme whose inclusion is quasi-compact is scheme-theoretically dense exactly
when its scheme-theoretic closure is the whole scheme, that is, when its inclusion is
scheme-theoretically dominant. -/
@[stacks 01RD]
theorem isSchemeTheoreticallyDense_iff_isSchemeTheoreticallyDominant {X : Scheme.{u}}
    (U : X.Opens) [QuasiCompact U.ι] :
    IsSchemeTheoreticallyDense U ↔ IsSchemeTheoreticallyDominant U.ι :=
  ⟨isSchemeTheoreticallyDominant_ι_of_isSchemeTheoreticallyDense,
    fun _ V ↦ .of_isPullback (isPullback_morphismRestrict V.ι U)⟩

end Scheme.Opens

/-- Let `X`, `Y` be schemes over `S` and let `f, g : X ⟶ Y` be morphisms over `S` which agree
after restriction to an open subscheme `U ⊆ X`. If the scheme-theoretic closure of `U` in `X` is
`X`, that is, `U.ι` is scheme-theoretically dominant, and `Y ⟶ S` is separated, then `f = g`. -/
@[stacks 01RH "hypothesis: the scheme-theoretic closure of `U` in `X` is `X`, i.e. `U.ι` is \
scheme-theoretically dominant"]
theorem eq_of_isSchemeTheoreticallyDominant_ι {S : Scheme.{u}} {X Y : Over S}
    (f g : X ⟶ Y) (U : X.left.Opens) [IsSchemeTheoreticallyDominant U.ι]
    [IsSeparated Y.hom] (hfg : U.ι ≫ f.left = U.ι ≫ g.left) :
    f = g := by
  let e : equalizer f g ⟶ X := equalizer.ι f g
  let a : Over.mk (U.ι ≫ X.hom) ⟶ equalizer f g := equalizer.lift
      (Over.homMk U.ι : Over.mk (U.ι ≫ X.hom) ⟶ X) (by ext; exact hfg)
  have hae : a.left ≫ e.left = U.ι := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : e.left.ker = ⊥ := by
    apply le_bot_iff.mp
    calc
      e.left.ker ≤ (a.left ≫ e.left).ker := Scheme.Hom.le_ker_comp _ _
      _ = U.ι.ker := by rw [hae]
      _ = ⊥ := U.ι.ker_eq_bot
  have : IsIso e.left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have : IsIso ((Over.forget S).map e) := by change IsIso e.left; infer_instance
  have : IsIso e := isIso_of_reflects_iso e (Over.forget S)
  rw [← cancel_epi (equalizer.ι f g)]
  exact equalizer.condition f g

/-- Two morphisms of schemes over `S` into a separated `S`-scheme are equal if they agree on a
scheme-theoretically dense open subscheme of their source. -/
theorem eq_of_isSchemeTheoreticallyDense {S : Scheme.{u}} {X Y : Over S}
    (f g : X ⟶ Y) (U : X.left.Opens) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    [IsSeparated Y.hom] (hfg : U.ι ≫ f.left = U.ι ≫ g.left) :
    f = g := by
  have := Scheme.Opens.isSchemeTheoreticallyDominant_ι_of_isSchemeTheoreticallyDense hU
  exact eq_of_isSchemeTheoreticallyDominant_ι f g U hfg

end AlgebraicGeometry
