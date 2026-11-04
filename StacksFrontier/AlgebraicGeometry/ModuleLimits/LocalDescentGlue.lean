module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescent

/-!
# Local descent data: from the affine case, to the overlaps, and glued

This file carries out the three steps of the Zariski glueing argument for
[Stacks Project, Tag 01ZR] (2) at the level of the localized canonical equation
`Stacks.AlgebraicGeometry.ModuleLimits.LocalDescent` of
`StacksFrontier/AlgebraicGeometry/ModuleLimits/LocalDescent.lean`:

* the equation that the **affine case** of the tag produces over an affine open of the stage,
  phrased for the restricted morphisms `AlgebraicGeometry.Scheme.Hom.resLE` which are the
  transitions of `AlgebraicGeometry.EventualLimit.preimageDiagram`, implies the localized
  equation — `localDescent_of_resLE_canonical_eq`, which is the pentagon
  `Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctor_map_canHom` read on sections;
* two local descent data over the same open have **equal pullbacks to the limit** —
  `map_resLE_eq_of_localDescent`, which is the hypothesis that part (3) of the tag consumes in
  order to make them equal at a later stage;
* local descent data over an open covering which agree on the overlaps **glue** —
  `exists_canonical_eq_of_cover`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_target_le`: pulling a section back
  commutes with shrinking the open of the target, at an arbitrary open of the source.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictPullbackObjIso_hom_pullbackSection'` and
  `restrictPullbackObjIso_inv_pullbackSection'`: the comparison of a restricted pullback with
  the pullback of a restriction, on a pulled-back section, at an arbitrary open.
* `Stacks.AlgebraicGeometry.ModuleLimits.localDescent_of_resLE_canonical_eq`: the affine case's
  equation gives a local descent datum.
* `Stacks.AlgebraicGeometry.ModuleLimits.map_resLE_eq_of_localDescent`: two local descent data
  agree after pullback to the limit.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictTo_pullbackRestrictHom`: the pullback of a
  morphism of restrictions commutes with shrinking the open.  This is what makes an eventual
  equality over an overlap an equality of the *transported* data.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_canonical_eq_of_cover`: **the glueing.**

## Implementation notes

The three primed lemmas exist because the existing comparison lemmas are stated at the open
`U.ι ⁻¹ᵁ U'` of `U`, which is *equal* to an arbitrary open `U''` of `U` only when `U'` is taken
to be `U.ι ''ᵁ U''` — and then not definitionally.  Rather than transport, the primed versions
are deduced from the unprimed ones by `pullbackSection_target_le`, which absorbs the difference
into a restriction map.

Every proof here works in the `· .val.app (op U)` spelling and instantiates its rewrite rules
completely; a rule with a metavariable in a section argument does not match, because the
composite of a morphism of restrictions with a section of the ambient module is type-correct
only up to an unfolding unavailable at reducible transparency.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

section Target

/-- Restriction in the pushforward of a pullback is restriction along the preimage. -/
theorem pullback_pushforward_val_map {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : U ⟶ V)
    (x : ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f).obj M).val.obj (op V)) :
    ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f).obj M).val.map i.op x
      = ((Scheme.Modules.pullback f).obj M).val.map ((Opens.map f.base).map i).op x := rfl

/-- **Pulling back a section commutes with shrinking the open of the target**, at an arbitrary
open of the source.  `Stacks.Conormal.pullbackSection_restrict` is the case where the open of
the source is the whole preimage, and
`Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_shrink` shrinks the open of the source
instead. -/
theorem pullbackSection_target_le {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    {U U' : X.Opens} (hU : U' ≤ U) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) (h' : W ≤ f ⁻¹ᵁ U')
    (a : M.val.obj (op U)) :
    Scheme.Modules.pullbackSection f M U' W h' (M.val.map (homOfLE hU).op a)
      = Scheme.Modules.pullbackSection f M U W h a := by
  have hnat := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val (homOfLE hU).op a
  dsimp only [Functor.id_obj] at hnat
  unfold Scheme.Modules.pullbackSection
  rw [hnat,
    pullback_pushforward_val_map f M (homOfLE hU),
    ← PresheafOfModules.map_comp_apply ((Scheme.Modules.pullback f).obj M).val
      ((Opens.map f.base).map (homOfLE hU)).op (homOfLE h').op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U) a),
    PresheafOfModules.congr_map_apply ((Scheme.Modules.pullback f).obj M).val
      (Subsingleton.elim (((Opens.map f.base).map (homOfLE hU)).op ≫ (homOfLE h').op)
        (homOfLE h).op)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U) a)]

/-- The image in `Y` of the preimage of `U''` under the restricted morphism lies in the preimage
of the image of `U''`. -/
private theorem image_resLE_preimage_le {Y X : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens}
    {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (U'' : U.toScheme.Opens) :
    V.ι ''ᵁ (Scheme.Hom.resLE f U V e ⁻¹ᵁ U'') ≤ f ⁻¹ᵁ (U.ι ''ᵁ U'') := by
  refine (Scheme.Hom.image_mono V.ι ?_).trans (V.ι.image_preimage_le _)
  conv_rhs => rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.resLE_comp_ι f e,
    Scheme.Hom.comp_preimage]
  exact Scheme.Hom.preimage_mono _ (U.ι.preimage_image_eq _).ge

end Target

section RestrictPullback

variable {Y X : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U)
  (F : X.Modules)

/-- The comparison of a restricted pullback with the pullback of a restriction, on a pulled-back
section, at an arbitrary open of the restricted target.  This is
`Stacks.AlgebraicGeometry.ModuleLimits.restrictPullbackObjIso_hom_pullbackSection` with the open
of `U` unrestricted. -/
theorem restrictPullbackObjIso_hom_pullbackSection' (U'' : U.toScheme.Opens)
    (V' : V.toScheme.Opens) (hf4 : V' ≤ Scheme.Hom.resLE f U V e ⁻¹ᵁ U'')
    (h : V.ι ''ᵁ V' ≤ f ⁻¹ᵁ (U.ι ''ᵁ U'')) (a : F.val.obj (op (U.ι ''ᵁ U''))) :
    (Stacks.Modules.restrictPullbackObjIso f e F).hom.val.app (op V')
        (Scheme.Modules.pullbackSection f F (U.ι ''ᵁ U'') (V.ι ''ᵁ V') h a)
      = Scheme.Modules.pullbackSection (Scheme.Hom.resLE f U V e)
          (Scheme.Modules.restrict F U.ι) U'' V' hf4 a := by
  have hle : U.ι ⁻¹ᵁ (U.ι ''ᵁ U'') ≤ U'' := (U.ι.preimage_image_eq U'').le
  have hf4' : V' ≤ Scheme.Hom.resLE f U V e ⁻¹ᵁ (U.ι ⁻¹ᵁ (U.ι ''ᵁ U'')) := by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage]
    exact (V.ι.preimage_image_eq V').ge.trans (Scheme.Hom.preimage_mono _ h)
  have h₃ : V' ≤ (Scheme.Hom.resLE f U V e ≫ U.ι) ⁻¹ᵁ (U.ι ''ᵁ U'') := by
    rw [Scheme.Hom.comp_preimage]
    exact hf4'
  rw [restrictPullbackObjIso_hom_pullbackSection f e F (U.ι ''ᵁ U'') V' h h₃ hf4' a]
  exact pullbackSection_target_le (Scheme.Hom.resLE f U V e)
    (Scheme.Modules.restrict F U.ι) hle V' hf4 hf4' a

/-- The inverse comparison, at an arbitrary open of the restricted target. -/
theorem restrictPullbackObjIso_inv_pullbackSection' (U'' : U.toScheme.Opens)
    (V' : V.toScheme.Opens) (hf4 : V' ≤ Scheme.Hom.resLE f U V e ⁻¹ᵁ U'')
    (h : V.ι ''ᵁ V' ≤ f ⁻¹ᵁ (U.ι ''ᵁ U'')) (a : F.val.obj (op (U.ι ''ᵁ U''))) :
    (Stacks.Modules.restrictPullbackObjIso f e F).inv.val.app (op V')
        (Scheme.Modules.pullbackSection (Scheme.Hom.resLE f U V e)
          (Scheme.Modules.restrict F U.ι) U'' V' hf4 a)
      = Scheme.Modules.pullbackSection f F (U.ι ''ᵁ U'') (V.ι ''ᵁ V') h a := by
  rw [← restrictPullbackObjIso_hom_pullbackSection' f e F U'' V' hf4 h a]
  exact congrArg
    (fun k : Scheme.Modules.restrict ((Scheme.Modules.pullback f).obj F) V.ι ⟶
        Scheme.Modules.restrict ((Scheme.Modules.pullback f).obj F) V.ι =>
      k.val.app (op V')
        (Scheme.Modules.pullbackSection f F (U.ι ''ᵁ U'') (V.ι ''ᵁ V') h a))
    (Stacks.Modules.restrictPullbackObjIso f e F).hom_inv_id

end RestrictPullback

section ValImage

variable {X : Scheme.{u}} {M N : X.Modules}

/-- `restrictSections_image` in the `· .val` spelling: over the image of an open of `O` the
sectionwise family of a morphism of restrictions is that morphism's own action. -/
theorem valSections_image {O : X.Opens}
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U' : O.toScheme.Opens) (h : O.ι ''ᵁ U' ≤ O) (m : M.val.obj (op (O.ι ''ᵁ U'))) :
    valSections θ (O.ι ''ᵁ U') h m = θ.val.app (op U') m :=
  (restrictSections_eq_valSections θ (O.ι ''ᵁ U') h m).symm.trans
    ((restrictSections_image θ U' h m).trans (restrictHomApp_apply θ U' m))

end ValImage

section Unique

variable {P Z X : Scheme.{u}} (q : P ⟶ Z) (g : Z ⟶ X) (pi : P ⟶ X) (hpi : q ≫ g = pi)
  {F G : X.Modules}
  (φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G)
  {T : X.Opens} {R : Z.Opens} (hR : R ≤ g ⁻¹ᵁ T) {W₀ : P.Opens} (hW₀ : W₀ ≤ q ⁻¹ᵁ R)

/-- The action on a doubly pulled-back section of the pullback of a local descent datum,
conjugated so that its source is a double pullback. -/
private theorem map_resLE_val_app_doublePullbackSection
    (Θ : Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj F) R.ι ⟶
      Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj G) R.ι)
    (U'' : T.toScheme.Opens)
    (hW : R.ι ''ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'') ≤ g ⁻¹ᵁ (T.ι ''ᵁ U''))
    (a : F.val.obj (op (T.ι ''ᵁ U''))) :
    ((Scheme.Modules.pullback (Scheme.Hom.resLE q R W₀ hW₀)).map
          ((Stacks.Modules.restrictPullbackObjIso g hR F).inv ≫ Θ)).val.app
        (op (Scheme.Hom.resLE q R W₀ hW₀ ⁻¹ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')))
        (doublePullbackSection (Scheme.Hom.resLE q R W₀ hW₀) (Scheme.Hom.resLE g T R hR)
          (Scheme.Modules.restrict F T.ι) U'' a)
      = Scheme.Modules.pullbackSection (Scheme.Hom.resLE q R W₀ hW₀)
          (Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj G) R.ι)
          (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')
          (Scheme.Hom.resLE q R W₀ hW₀ ⁻¹ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')) le_rfl
          (valSections Θ (R.ι ''ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U''))
            (Scheme.Opens.ι_image_le R _)
            (Scheme.Modules.pullbackSection g F (T.ι ''ᵁ U'')
              (R.ι ''ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')) hW a)) := by
  unfold doublePullbackSection
  rw [Functor.map_comp, comp_val_app,
    Scheme.Modules.pullbackSection_naturality (Scheme.Hom.resLE q R W₀ hW₀)
      (Stacks.Modules.restrictPullbackObjIso g hR F).inv
      (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')
      (Scheme.Hom.resLE q R W₀ hW₀ ⁻¹ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')) le_rfl
      (Scheme.Modules.pullbackSection (Scheme.Hom.resLE g T R hR)
        (Scheme.Modules.restrict F T.ι) U'' (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'') le_rfl a),
    restrictPullbackObjIso_inv_pullbackSection' g hR F U''
      (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'') le_rfl hW a,
    Scheme.Modules.pullbackSection_naturality (Scheme.Hom.resLE q R W₀ hW₀) Θ
      (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')
      (Scheme.Hom.resLE q R W₀ hW₀ ⁻¹ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')) le_rfl
      (Scheme.Modules.pullbackSection g F (T.ι ''ᵁ U'')
        (R.ι ''ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')) hW a),
    ← valSections_image Θ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'') (Scheme.Opens.ι_image_le R _)
      (Scheme.Modules.pullbackSection g F (T.ι ''ᵁ U'')
        (R.ι ''ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')) hW a)]

include hpi hR in
/-- **Two local descent data over the same open become equal after pullback to the limit.**
This is the hypothesis that the eventual-equality half of [Stacks Project, Tag 01ZR] — part (3)
— consumes in order to make them equal at a later stage. -/
theorem map_resLE_eq_of_localDescent
    (Θ₁ Θ₂ : Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj F) R.ι ⟶
      Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj G) R.ι)
    (h₁ : LocalDescent q g pi hpi φ R Θ₁) (h₂ : LocalDescent q g pi hpi φ R Θ₂) :
    (Scheme.Modules.pullback (Scheme.Hom.resLE q R W₀ hW₀)).map Θ₁
      = (Scheme.Modules.pullback (Scheme.Hom.resLE q R W₀ hW₀)).map Θ₂ := by
  refine (cancel_epi ((Scheme.Modules.pullback (Scheme.Hom.resLE q R W₀ hW₀)).map
    (Stacks.Modules.restrictPullbackObjIso g hR F).inv)).mp ?_
  rw [← Functor.map_comp, ← Functor.map_comp]
  refine hom_ext_of_doublePullbackSection (Scheme.Hom.resLE q R W₀ hW₀)
    (Scheme.Hom.resLE g T R hR) (F := Scheme.Modules.restrict F T.ι) fun U'' a => ?_
  -- the opens in play
  have hW := image_resLE_preimage_le g hR U''
  have hWZ : R.ι ''ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'') ≤ R := Scheme.Opens.ι_image_le R _
  have hV := image_resLE_preimage_le q hW₀ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')
  have hV' : W₀.ι ''ᵁ (Scheme.Hom.resLE q R W₀ hW₀ ⁻¹ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U''))
      ≤ pi ⁻¹ᵁ (T.ι ''ᵁ U'') := by
    rw [← hpi, Scheme.Hom.comp_preimage]
    exact hV.trans (Scheme.Hom.preimage_mono _ hW)
  rw [map_resLE_val_app_doublePullbackSection q g hR hW₀ Θ₁ U'' hW a,
    map_resLE_val_app_doublePullbackSection q g hR hW₀ Θ₂ U'' hW a]
  have hbridge : ∀ w : ((Scheme.Modules.pullback g).obj G).val.obj
        (op (R.ι ''ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U''))),
      Scheme.Modules.pullbackSection (Scheme.Hom.resLE q R W₀ hW₀)
          (Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj G) R.ι)
          (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')
          (Scheme.Hom.resLE q R W₀ hW₀ ⁻¹ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')) le_rfl w
        = (Stacks.Modules.restrictPullbackObjIso q hW₀
              ((Scheme.Modules.pullback g).obj G)).hom.val.app
            (op (Scheme.Hom.resLE q R W₀ hW₀ ⁻¹ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')))
            (Scheme.Modules.pullbackSection q ((Scheme.Modules.pullback g).obj G)
              (R.ι ''ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U''))
              (W₀.ι ''ᵁ (Scheme.Hom.resLE q R W₀ hW₀ ⁻¹ᵁ
                (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U''))) hV w) :=
    fun w => (restrictPullbackObjIso_hom_pullbackSection' q hW₀
      ((Scheme.Modules.pullback g).obj G) (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')
      (Scheme.Hom.resLE q R W₀ hW₀ ⁻¹ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U''))
      le_rfl hV w).symm
  rw [hbridge, hbridge]
  refine congrArg _ ?_
  have e := (h₁ (T.ι ''ᵁ U'') (R.ι ''ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')) hW hWZ
      (W₀.ι ''ᵁ (Scheme.Hom.resLE q R W₀ hW₀ ⁻¹ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')))
      hV hV' a).trans
    (h₂ (T.ι ''ᵁ U'') (R.ι ''ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')) hW hWZ
      (W₀.ι ''ᵁ (Scheme.Hom.resLE q R W₀ hW₀ ⁻¹ᵁ (Scheme.Hom.resLE g T R hR ⁻¹ᵁ U'')))
      hV hV' a).symm
  refine Eq.trans (inv_val_app_apply (canHom q g pi hpi G) _ _).symm ?_
  rw [e]
  exact inv_val_app_apply (canHom q g pi hpi G) _ _

end Unique

section FromAffine

variable {P Z X : Scheme.{u}} (q : P ⟶ Z) (g : Z ⟶ X) (pi : P ⟶ X) (hpi : q ≫ g = pi)
  {F G : X.Modules}
  (φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G)
  {T : X.Opens} {Z₀ : Z.Opens} {W₀ : P.Opens} (hZ : Z₀ ≤ g ⁻¹ᵁ T) (hW : W₀ ≤ q ⁻¹ᵁ Z₀)
  (hW' : W₀ ≤ pi ⁻¹ᵁ T) (hW₂ : q ⁻¹ᵁ Z₀ ≤ W₀)
  (hres : Scheme.Hom.resLE q Z₀ W₀ hW ≫ Scheme.Hom.resLE g T Z₀ hZ
    = Scheme.Hom.resLE pi T W₀ hW')

include hpi hres hW₂ in
/-- **The canonical equation over an open, from the canonical equation of the restricted
data.**  The restricted morphisms `AlgebraicGeometry.Scheme.Hom.resLE` are the transition
morphisms and cone legs of `AlgebraicGeometry.EventualLimit.preimageDiagram` and
`preimageCone`, so this is what the affine case of [Stacks Project, Tag 01ZR] (2), applied over
an affine open of the stage, produces. -/
theorem localDescent_of_resLE_canonical_eq
    (ψ : (Scheme.Modules.pullback (Scheme.Hom.resLE g T Z₀ hZ)).obj
        (Scheme.Modules.restrict F T.ι) ⟶
      (Scheme.Modules.pullback (Scheme.Hom.resLE g T Z₀ hZ)).obj
        (Scheme.Modules.restrict G T.ι))
    (hψ : (Scheme.Modules.pullback (Scheme.Hom.resLE q Z₀ W₀ hW)).map ψ ≫
          canHom (Scheme.Hom.resLE q Z₀ W₀ hW) (Scheme.Hom.resLE g T Z₀ hZ)
            (Scheme.Hom.resLE pi T W₀ hW') hres (Scheme.Modules.restrict G T.ι)
        = canHom (Scheme.Hom.resLE q Z₀ W₀ hW) (Scheme.Hom.resLE g T Z₀ hZ)
              (Scheme.Hom.resLE pi T W₀ hW') hres (Scheme.Modules.restrict F T.ι) ≫
            ((Stacks.Modules.restrictPullbackObjIso pi hW' F).inv ≫
              (Scheme.Modules.restrictFunctor W₀.ι).map φ ≫
                (Stacks.Modules.restrictPullbackObjIso pi hW' G).hom)) :
    LocalDescent q g pi hpi φ Z₀
      ((Stacks.Modules.restrictPullbackObjIso g hZ F).hom ≫ ψ ≫
        (Stacks.Modules.restrictPullbackObjIso g hZ G).inv) := by
  -- the pentagon, solved for the restriction of the canonical identification
  have pent : ∀ K : X.Modules,
      (Scheme.Modules.restrictFunctor W₀.ι).map (canHom q g pi hpi K)
        = ((Stacks.Modules.restrictPullbackObjIso q hW
              ((Scheme.Modules.pullback g).obj K)).hom ≫
            (Scheme.Modules.pullback (Scheme.Hom.resLE q Z₀ W₀ hW)).map
                (Stacks.Modules.restrictPullbackObjIso g hZ K).hom ≫
              canHom (Scheme.Hom.resLE q Z₀ W₀ hW) (Scheme.Hom.resLE g T Z₀ hZ)
                  (Scheme.Hom.resLE pi T W₀ hW') hres (Scheme.Modules.restrict K T.ι)) ≫
                (Stacks.Modules.restrictPullbackObjIso pi hW' K).inv := by
    intro K
    rw [Iso.eq_comp_inv]
    exact restrictFunctor_map_canHom q g pi hpi hZ hW hW' hres K
  -- the morphism-level equation
  have hb : pullbackRestrictHom q hW
        ((Stacks.Modules.restrictPullbackObjIso g hZ F).hom ≫ ψ ≫
          (Stacks.Modules.restrictPullbackObjIso g hZ G).inv) ≫
        (Scheme.Modules.restrictFunctor W₀.ι).map (canHom q g pi hpi G)
      = (Scheme.Modules.restrictFunctor W₀.ι).map (canHom q g pi hpi F) ≫
        (Scheme.Modules.restrictFunctor W₀.ι).map φ := by
    rw [pullbackRestrictHom, pent G, pent F]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hΘ : (Scheme.Modules.pullback (Scheme.Hom.resLE q Z₀ W₀ hW)).map
          ((Stacks.Modules.restrictPullbackObjIso g hZ F).hom ≫ ψ ≫
            (Stacks.Modules.restrictPullbackObjIso g hZ G).inv) ≫
          (Scheme.Modules.pullback (Scheme.Hom.resLE q Z₀ W₀ hW)).map
            (Stacks.Modules.restrictPullbackObjIso g hZ G).hom
        = (Scheme.Modules.pullback (Scheme.Hom.resLE q Z₀ W₀ hW)).map
            (Stacks.Modules.restrictPullbackObjIso g hZ F).hom ≫
          (Scheme.Modules.pullback (Scheme.Hom.resLE q Z₀ W₀ hW)).map ψ := by
      rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    rw [reassoc_of% hΘ, reassoc_of% hψ]
    simp only [Iso.hom_inv_id, Category.comp_id]
  -- read it on sections
  intro U W hW2 hWZ V hV hV' a
  have hVW₀ : V ≤ W₀ := (hV.trans (Scheme.Hom.preimage_mono _ hWZ)).trans hW₂
  rw [← valSections_pullbackRestrictHom q hW
      ((Stacks.Modules.restrictPullbackObjIso g hZ F).hom ≫ ψ ≫
        (Stacks.Modules.restrictPullbackObjIso g hZ G).inv) W hWZ V hVW₀ hV
      (Scheme.Modules.pullbackSection g F U W hW2 a)]
  have hsec := congrArg (fun k : Scheme.Modules.restrict
      ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F)) W₀.ι ⟶
      Scheme.Modules.restrict ((Scheme.Modules.pullback pi).obj G) W₀.ι =>
    valSections k V hVW₀
      (Scheme.Modules.pullbackSection q ((Scheme.Modules.pullback g).obj F) W V hV
        (Scheme.Modules.pullbackSection g F U W hW2 a))) hb
  simp only [valSections_comp, valSections_restrictFunctor_map] at hsec
  rw [hsec, canHom_val_app_pullbackSection q g pi hpi F U W V hW2 hV hV' a]

end FromAffine

section Shrink

variable {Z P : Scheme.{u}} (γ : P ⟶ Z) {A B : Z.Modules} {Z₀ R : Z.Opens} (hR : R ≤ Z₀)
  {W₀ W₀' : P.Opens} (hW : W₀ ≤ γ ⁻¹ᵁ Z₀) (hW₂ : W₀' ≤ γ ⁻¹ᵁ R) (hW₀' : W₀' ≤ W₀)

include hR hW₂ hW₀' in
/-- **The pullback of a morphism of restrictions commutes with shrinking the open.**  This is
what makes the eventual equality produced by part (3) of [Stacks Project, Tag 01ZR] over an
overlap an equality of the *transported* local descent data. -/
theorem restrictTo_pullbackRestrictHom
    (Θ : Scheme.Modules.restrict A Z₀.ι ⟶ Scheme.Modules.restrict B Z₀.ι) :
    restrictTo hW₀' (pullbackRestrictHom γ hW Θ)
      = pullbackRestrictHom γ hW₂ (restrictTo hR Θ) := by
  refine (cancel_epi (Stacks.Modules.restrictPullbackObjIso γ hW₂ A).inv).mp ?_
  refine hom_ext_of_pullbackSection (Scheme.Hom.resLE γ R W₀' hW₂)
    (M := Scheme.Modules.restrict A R.ι) fun U'' x => ?_
  -- the opens in play
  have hVim : W₀'.ι ''ᵁ (Scheme.Hom.resLE γ R W₀' hW₂ ⁻¹ᵁ U'') ≤ W₀' :=
    Scheme.Opens.ι_image_le W₀' _
  have hU₁ : R.ι ''ᵁ U'' ≤ R := Scheme.Opens.ι_image_le R _
  have hVU := image_resLE_preimage_le γ hW₂ U''
  have key : ∀ Ξ : Scheme.Modules.restrict ((Scheme.Modules.pullback γ).obj A) W₀'.ι ⟶
        Scheme.Modules.restrict ((Scheme.Modules.pullback γ).obj B) W₀'.ι,
      ((Stacks.Modules.restrictPullbackObjIso γ hW₂ A).inv ≫ Ξ).val.app
          (op (Scheme.Hom.resLE γ R W₀' hW₂ ⁻¹ᵁ U''))
          (Scheme.Modules.pullbackSection (Scheme.Hom.resLE γ R W₀' hW₂)
            (Scheme.Modules.restrict A R.ι) U''
            (Scheme.Hom.resLE γ R W₀' hW₂ ⁻¹ᵁ U'') le_rfl x)
        = valSections Ξ (W₀'.ι ''ᵁ (Scheme.Hom.resLE γ R W₀' hW₂ ⁻¹ᵁ U'')) hVim
          (Scheme.Modules.pullbackSection γ A (R.ι ''ᵁ U'')
            (W₀'.ι ''ᵁ (Scheme.Hom.resLE γ R W₀' hW₂ ⁻¹ᵁ U'')) hVU x) := by
    intro Ξ
    rw [comp_val_app,
      restrictPullbackObjIso_inv_pullbackSection' γ hW₂ A U''
        (Scheme.Hom.resLE γ R W₀' hW₂ ⁻¹ᵁ U'') le_rfl hVU x,
      valSections_image Ξ (Scheme.Hom.resLE γ R W₀' hW₂ ⁻¹ᵁ U'') hVim _]
  rw [key, key, valSections_restrictTo hW₀' (pullbackRestrictHom γ hW Θ)
      (W₀'.ι ''ᵁ (Scheme.Hom.resLE γ R W₀' hW₂ ⁻¹ᵁ U'')) hVim _,
    valSections_pullbackRestrictHom γ hW Θ (R.ι ''ᵁ U'') (hU₁.trans hR)
      (W₀'.ι ''ᵁ (Scheme.Hom.resLE γ R W₀' hW₂ ⁻¹ᵁ U'')) (hVim.trans hW₀') hVU x,
    valSections_pullbackRestrictHom γ hW₂ (restrictTo hR Θ) (R.ι ''ᵁ U'') hU₁
      (W₀'.ι ''ᵁ (Scheme.Hom.resLE γ R W₀' hW₂ ⁻¹ᵁ U'')) hVim hVU x,
    valSections_restrictTo hR Θ (R.ι ''ᵁ U'') hU₁ x]

end Shrink

section Glue

variable {P Z X : Scheme.{u}} (q : P ⟶ Z) (g : Z ⟶ X) (pi : P ⟶ X) (hpi : q ≫ g = pi)
  {F G : X.Modules}
  (φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G)

include hpi in
/-- **Zariski glueing of the canonical equation.**  Local descent data over the members of an
open covering of the stage which agree on the overlaps glue to a morphism satisfying the
canonical equation of [Stacks Project, Tag 01ZR] (2). -/
theorem exists_canonical_eq_of_cover {ι : Type u} (Zc : ι → Z.Opens)
    (hcov : ∀ x : Z, ∃ a, x ∈ Zc a)
    (Θ : ∀ a : ι, Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj F) (Zc a).ι ⟶
      Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj G) (Zc a).ι)
    (hΘ : ∀ a, LocalDescent q g pi hpi φ (Zc a) (Θ a))
    (hagree : ∀ (a b : ι) (W : Z.Opens) (ha : W ≤ Zc a) (hb : W ≤ Zc b)
      (m : ((Scheme.Modules.pullback g).obj F).val.obj (op W)),
      valSections (Θ a) W ha m = valSections (Θ b) W hb m) :
    ∃ Φ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G,
      (Scheme.Modules.pullback q).map Φ ≫ canHom q g pi hpi G
        = canHom q g pi hpi F ≫ φ := by
  obtain ⟨Φ, hΦ⟩ := exists_hom_app_eq_of_cover Zc hcov
    (fun a W h => restrictSections (Θ a) W h)
    (fun a W h => restrictSections_add (Θ a) W h)
    (fun a W h => restrictSections_smul (Θ a) W h)
    (fun a W V hUV hV => restrictSections_res (Θ a) W V hUV hV)
    (fun a b W ha hb m => (restrictSections_eq_valSections (Θ a) W ha m).trans
      ((hagree a b W ha hb m).trans
        (restrictSections_eq_valSections (Θ b) W hb m).symm))
  have hΦ' : ∀ (b : ι) (W : Z.Opens) (h : W ≤ Zc b)
      (m : ((Scheme.Modules.pullback g).obj F).val.obj (op W)),
      Φ.val.app (op W) m = valSections (Θ b) W h m := fun b W h m =>
    (hΦ b W h m).trans (restrictSections_eq_valSections (Θ b) W h m)
  refine ⟨Φ, canonical_eq_of_localCanonicalEq q g pi hpi φ Φ ?_⟩
  intro U W hW _ V hV hV' a
  refine ((Scheme.Modules.pullback pi).obj G).isSheaf.section_ext (U := op V) ?_
  intro x hx
  obtain ⟨b, hb⟩ := hcov (q.base x)
  refine ⟨V ⊓ q ⁻¹ᵁ (W ⊓ Zc b), inf_le_left, ⟨hx, hV hx, hb⟩, ?_⟩
  have hW₁ : W ⊓ Zc b ≤ g ⁻¹ᵁ U := inf_le_left.trans hW
  have hV₁ : V ⊓ q ⁻¹ᵁ (W ⊓ Zc b) ≤ q ⁻¹ᵁ (W ⊓ Zc b) := inf_le_right
  have hV₁' : V ⊓ q ⁻¹ᵁ (W ⊓ Zc b) ≤ pi ⁻¹ᵁ U := inf_le_left.trans hV'
  have hV₁W : V ⊓ q ⁻¹ᵁ (W ⊓ Zc b) ≤ q ⁻¹ᵁ W :=
    hV₁.trans (Scheme.Hom.preimage_mono _ inf_le_left)
  -- the two sides, restricted to the smaller open
  have hRHS : ((Scheme.Modules.pullback pi).obj G).val.map
        (homOfLE (inf_le_left : V ⊓ q ⁻¹ᵁ (W ⊓ Zc b) ≤ V)).op
        (φ.val.app (op V) (Scheme.Modules.pullbackSection pi F U V hV' a))
      = φ.val.app (op (V ⊓ q ⁻¹ᵁ (W ⊓ Zc b)))
        (Scheme.Modules.pullbackSection pi F U (V ⊓ q ⁻¹ᵁ (W ⊓ Zc b)) hV₁' a) := by
    rw [← PresheafOfModules.naturality_apply φ.val
        (homOfLE (inf_le_left : V ⊓ q ⁻¹ᵁ (W ⊓ Zc b) ≤ V)).op
        (Scheme.Modules.pullbackSection pi F U V hV' a),
      pullbackSection_shrink pi F U V (V ⊓ q ⁻¹ᵁ (W ⊓ Zc b)) hV' inf_le_left hV₁' a]
  have hLHS : ((Scheme.Modules.pullback pi).obj G).val.map
        (homOfLE (inf_le_left : V ⊓ q ⁻¹ᵁ (W ⊓ Zc b) ≤ V)).op
        ((canHom q g pi hpi G).val.app (op V)
          (Scheme.Modules.pullbackSection q ((Scheme.Modules.pullback g).obj G) W V hV
            (Φ.val.app (op W) (Scheme.Modules.pullbackSection g F U W hW a))))
      = (canHom q g pi hpi G).val.app (op (V ⊓ q ⁻¹ᵁ (W ⊓ Zc b)))
        (Scheme.Modules.pullbackSection q ((Scheme.Modules.pullback g).obj G) (W ⊓ Zc b)
          (V ⊓ q ⁻¹ᵁ (W ⊓ Zc b)) hV₁
          (valSections (Θ b) (W ⊓ Zc b) inf_le_right
            (Scheme.Modules.pullbackSection g F U (W ⊓ Zc b) hW₁ a))) := by
    rw [← PresheafOfModules.naturality_apply (canHom q g pi hpi G).val
        (homOfLE (inf_le_left : V ⊓ q ⁻¹ᵁ (W ⊓ Zc b) ≤ V)).op _,
      pullbackSection_shrink q ((Scheme.Modules.pullback g).obj G) W V
        (V ⊓ q ⁻¹ᵁ (W ⊓ Zc b)) hV inf_le_left hV₁W
        (Φ.val.app (op W) (Scheme.Modules.pullbackSection g F U W hW a)),
      ← pullbackSection_target_le q ((Scheme.Modules.pullback g).obj G)
        (inf_le_left : W ⊓ Zc b ≤ W) (V ⊓ q ⁻¹ᵁ (W ⊓ Zc b)) hV₁W hV₁
        (Φ.val.app (op W) (Scheme.Modules.pullbackSection g F U W hW a)),
      ← PresheafOfModules.naturality_apply Φ.val
        (homOfLE (inf_le_left : W ⊓ Zc b ≤ W)).op
        (Scheme.Modules.pullbackSection g F U W hW a),
      pullbackSection_shrink g F U W (W ⊓ Zc b) hW inf_le_left hW₁ a,
      hΦ' b (W ⊓ Zc b) inf_le_right
        (Scheme.Modules.pullbackSection g F U (W ⊓ Zc b) hW₁ a)]
  exact hLHS.trans ((hΘ b U (W ⊓ Zc b) hW₁ inf_le_right
    (V ⊓ q ⁻¹ᵁ (W ⊓ Zc b)) hV₁ hV₁' a).trans hRHS.symm)

end Glue

end Stacks.AlgebraicGeometry.ModuleLimits

end
