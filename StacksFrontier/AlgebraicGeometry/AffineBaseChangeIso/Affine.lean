module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.AffineSections
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Corner
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.PushoutComparison

/-!
# Affine base change for direct images of quasi-coherent modules

Let
```
Y' --q'--> Y
|p'        |p
T' --q-->  T
```
be a cartesian square of schemes all four of which are affine, and let `G` be a quasi-coherent
`𝒪_Y`-module.  **This file proves that the canonical base-change morphism
`q^* p_* G ⟶ p'_* (q')^* G` is invertible.**  Together with
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom` this is
the base-change assertion of Stacks Tag 02KG.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.specSquareOfRingSquare`: the square of spectra
  attached to a commutative square of rings.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.baseChangeNatTrans_app_app_top`: on global
  sections the base-change morphism carries the unit for the lower horizontal morphism to the
  unit for the upper one.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_specSquare`: the
  base-change morphism of the square of spectra of a pushout square of rings is invertible at
  every quasi-coherent module.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_affine`: **the
  all-affine case**, for an arbitrary cartesian square of affine schemes.

## Route

Three steps.

**From affine schemes to spectra.**  `AlgebraicGeometry.Scheme.isoSpec` identifies each corner
with the spectrum of its ring of global sections, compatibly with the vertical morphisms by
`AlgebraicGeometry.Scheme.isoSpec_hom_naturality`, and
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_cornerIso` transports
invertibility between the two squares.  The resulting square of rings is a pushout by
Mathlib's `AlgebraicGeometry.isPushout_appTop_of_isPullback`, which needs exactly the three
affineness instances it is given and derives the fourth.

**From spectra to global sections.**  On an affine scheme a morphism of quasi-coherent modules
is invertible as soon as it is invertible on global sections, by
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ`; both sides are
quasi-coherent, the direct images by
`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom` and the
inverse images by `Stacks.AlgebraicGeometry.SectionsColimit.isQuasicoherent_pullback_specMap`.

**On global sections.**  Both sides are extensions of scalars of the one module `Γ(G, ⊤)`: the
source along `Γ(T) ⟶ Γ(T')` and the target along `Γ(Y) ⟶ Γ(Y')`, in both cases by
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_transposeExtend_pullbackΓUnit`, with the
direct images contributing only a restriction of scalars, which is what
`AlgebraicGeometry.pushforwardΓIso` records.  The base-change morphism is compatible with the
two structural maps -- that is `baseChangeNatTrans_app_app_top`, which is Mathlib's
`CategoryTheory.unit_mateEquiv_symm` evaluated on global sections -- so
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_of_isPushout` applies.

`baseChangeNatTrans_app_app_top` itself is `unit_mateEquiv_symm` for the two
inverse-image--direct-image adjunctions, evaluated at the module and then at the top open.  The
identification of composite direct images that the base-change morphism is the mate of
contributes, on sections over the top open, one restriction map of the module along an equality
of opens, which is an identity because the category of opens of a scheme is a preorder.

## Implementation notes

The Beck--Chevalley machinery of `Stacks.AlgebraicGeometry.QcohRestrictEquiv` is not used
here: its component formula reproduces what the definition of the mate already gives, and its
transfer results take invertibility of the comparison as a hypothesis.  The base-change
morphism *is* the Beck--Chevalley comparison of the four adjunctions in the square, but this
file does not use or check that identification.

## What is not done

**No project tag attribute is attached here.**  The square is required to be affine at all four
corners; the reduction of the general case to this one is
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom`, in
`Reduction.lean`, which consumes this file.  Nothing here says anything about the two other
assertions of the tag, namely quasi-coherence of the direct image, which is proved elsewhere,
and the comparison with the derived direct image, which is not proved anywhere in this
repository.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.TwoSquare
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChangeIso

/-! ### The base-change morphism on global sections -/

section Top

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- On global sections the base-change morphism carries the unit of the adjunction for the
lower horizontal morphism to the unit of the adjunction for the upper one. -/
lemma baseChangeNatTrans_app_app_top (w : g' ≫ f = f' ≫ g) (F : X.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        ((Scheme.Modules.pushforward f).obj F)).app ⊤ ≫
      ((AffinePushforward.baseChangeNatTrans w).app F).app (g ⁻¹ᵁ ⊤) =
    ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F).app (f ⁻¹ᵁ ⊤) := by
  have h := unit_mateEquiv_symm (Scheme.Modules.pullbackPushforwardAdjunction g')
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso w).hom) F
  have h2 := congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    AffinePushforward.pushforwardSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Functor.id_obj] at h2
  refine h2.symm.trans ?_
  refine Eq.trans ?_ (Category.comp_id _)
  congr 1
  refine Eq.trans ?_ (((Scheme.Modules.pullback g').obj F).presheaf.map_id _)
  exact congrArg ((Scheme.Modules.pullback g').obj F).presheaf.map (Subsingleton.elim _ _)

end Top

/-! ### The square of spectra of a pushout square of rings -/

section Spectra

variable {A B A' B' : CommRingCat.{u}} {pb : A ⟶ B} {qa : A ⟶ A'} {qb : B ⟶ B'} {pb' : A' ⟶ B'}

/-- The commutative square of spectra attached to a commutative square of rings. -/
lemma specSquareOfRingSquare (hw : pb ≫ qb = qa ≫ pb') :
    Spec.map qb ≫ Spec.map pb = Spec.map pb' ≫ Spec.map qa := by
  rw [← Spec.map_comp, ← Spec.map_comp, hw]

/-- **Affine base change, for a pushout square of rings.**  The base-change morphism of the
square of spectra of a pushout square of commutative rings is invertible at every
quasi-coherent module. -/
theorem isIso_baseChangeNatTrans_specSquare (hsq : IsPushout pb qa qb pb')
    (F : (Spec B).Modules) [F.IsQuasicoherent] :
    IsIso ((AffinePushforward.baseChangeNatTrans (specSquareOfRingSquare hsq.w)).app F) := by
  have hsrc : ((Scheme.Modules.pushforward (Spec.map pb) ⋙
      Scheme.Modules.pullback (Spec.map qa)).obj F).IsQuasicoherent :=
    SectionsColimit.isQuasicoherent_pullback_specMap qa _
  have htgt : ((Scheme.Modules.pullback (Spec.map qb) ⋙
      Scheme.Modules.pushforward (Spec.map pb')).obj F).IsQuasicoherent :=
    AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom (Spec.map pb') _
  refine AffineBaseChange.isIso_of_isIso_moduleSpecΓ _ ?_
  refine isIso_of_isPushout hsq
    (u := (pushforwardΓIso A B pb).inv.app F ≫
      pullbackΓUnit qa ((Scheme.Modules.pushforward (Spec.map pb)).obj F))
    (isIso_transposeExtend_comp qa _ _ (isIso_transposeExtend_pullbackΓUnit qa _))
    (v := pullbackΓUnit qb F) (isIso_transposeExtend_pullbackΓUnit qb F)
    ((pushforwardΓIso A' B' pb').app ((Scheme.Modules.pullback (Spec.map qb)).obj F)) _
    fun x => ?_
  exact congr($(baseChangeNatTrans_app_app_top (specSquareOfRingSquare hsq.w) F).hom x)

end Spectra

/-! ### The all-affine case -/

section Affine

variable {Y' Y T' T : Scheme.{u}} {q' : Y' ⟶ Y} {p' : Y' ⟶ T'} {p : Y ⟶ T} {q : T' ⟶ T}

/-- The square of spectra of global sections attached to a cartesian square of affine
schemes. -/
lemma specSquare (hq : IsPullback q' p' p q) [IsAffine Y] [IsAffine T'] [IsAffine T] :
    Spec.map q'.appTop ≫ Spec.map p.appTop = Spec.map p'.appTop ≫ Spec.map q.appTop :=
  specSquareOfRingSquare (isPushout_appTop_of_isPullback hq).w

/-- Reduction of the all-affine case to the square of spectra. -/
theorem isIso_of_isIso_specSquare (hq : IsPullback q' p' p q) [IsAffine Y'] [IsAffine Y]
    [IsAffine T'] [IsAffine T] (G : Y.Modules)
    (H : IsIso ((AffinePushforward.baseChangeNatTrans (specSquare hq)).app
      ((Scheme.Modules.pullback Y.isoSpec.inv).obj G))) :
    IsIso ((AffinePushforward.baseChangeNatTrans hq.w).app G) :=
  isIso_baseChangeNatTrans_of_cornerIso hq.w (specSquare hq)
    (a := Y'.isoSpec.hom) (b := Y.isoSpec.inv) (c := T'.isoSpec.hom) (d := T.isoSpec.inv)
    (Scheme.isoSpec_hom_naturality p') (Scheme.isoSpec_inv_naturality p).symm
    (by rw [Scheme.isoSpec_hom_naturality]; simp)
    (by rw [Scheme.isoSpec_hom_naturality]; simp) G H

/-- **Affine base change for direct images of quasi-coherent modules.**  For a cartesian square
of schemes all four of which are affine, the canonical base-change morphism
`q^* p_* G ⟶ p'_* (q')^* G` is invertible at every quasi-coherent module `G`. -/
theorem isIso_baseChangeNatTrans_of_affine (hq : IsPullback q' p' p q) [IsAffine Y']
    [IsAffine Y] [IsAffine T'] [IsAffine T] (G : Y.Modules) [G.IsQuasicoherent] :
    IsIso ((AffinePushforward.baseChangeNatTrans hq.w).app G) := by
  have hqc : ((Scheme.Modules.pullback Y.isoSpec.inv).obj G).IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback _ G
  exact isIso_of_isIso_specSquare hq G
    (isIso_baseChangeNatTrans_specSquare (isPushout_appTop_of_isPullback hq) _)

end Affine

end Stacks.AlgebraicGeometry.AffineBaseChangeIso

end
