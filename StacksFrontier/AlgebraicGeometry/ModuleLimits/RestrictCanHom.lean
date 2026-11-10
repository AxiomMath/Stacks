module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionCalculus
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic

/-!
# Restricting the canonical identification to an open

`Stacks.AlgebraicGeometry.ModuleLimits.canHom q g pi hpi F` identifies `q^*(g^*F)` with
`pi^*F` for `q ≫ g = pi`.  Restricting that identification to an open `W₀` of the source, over
an open `Z₀` of the middle scheme and an open `U` of the target, gives the canonical
identification for the three restricted morphisms
`AlgebraicGeometry.Scheme.Hom.resLE` — conjugated by the three comparisons
`Stacks.Modules.restrictPullbackObjIso` of a restricted pullback with the pullback of a
restriction.  That is `restrictFunctor_map_canHom`, and it is the coherence a Zariski-glueing
argument for [Stacks Project, Tag 01ZR] (2) needs in order to check the tag's canonical equation
locally.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.restrictPullbackObjIso_hom_pullbackSection`: the
  comparison `Stacks.Modules.restrictPullbackObjIso` carries the pullback of a section to the
  pullback of the restricted section along the restricted morphism.  This is the computation the
  pentagon is assembled from.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctor_map_canHom`: **the pentagon.**
* `Stacks.AlgebraicGeometry.ModuleLimits.resLE_comp_resLE_of_comp_eq`: the three restricted
  morphisms compose, which is what makes the right-hand side of the pentagon typecheck.

## Implementation notes

`Stacks.Modules.restrictPullbackIso` is a five-fold composite — the comparison of a restriction
with a pullback at each end, `AlgebraicGeometry.Scheme.Modules.pullbackComp` twice and
`pullbackCongr` once — and the action of every one of those five on a pulled-back section is
known, so `restrictPullbackObjIso_hom_pullbackSection` is a chain of rewrites with no transport.
The pentagon then follows from
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_triplePullbackSection`: both sides send a
thrice pulled-back section to the pullback along the total composite of the restriction of the
section.  No `cat_disch`, no `eqToHom` and no transparency lever appears; a proof of this
statement by pseudofunctor coherence fails with `aesop failed, exhaustive search`.

Two shape points.  The composite's action on sections is reached through the `rfl`-lemma
`comp_val_app` rather than by `change`: a `change` naming the whole composite exhausts the
recursion depth, while rewriting with a lemma stated at abstract types does not.  And the one
step that mixes the `restrictFunctor` spelling with the `canHom` spelling is isolated as a
`have` whose statement is written in the *consumer's* spelling and whose proof is a bare
application of `canHom_val_app_pullbackSection`; stating it the other way round again exhausts
the recursion depth.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- The three restricted morphisms compose: if `q ≫ g = pi` then
`q|_{W₀→Z₀} ≫ g|_{Z₀→U} = pi|_{W₀→U}`. -/
theorem resLE_comp_resLE_of_comp_eq {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X)
    (hpi : q ≫ g = pi) {U : X.Opens} {Z₀ : Z.Opens} {W₀ : W.Opens} (hZ : Z₀ ≤ g ⁻¹ᵁ U)
    (hW : W₀ ≤ q ⁻¹ᵁ Z₀) (hW' : W₀ ≤ pi ⁻¹ᵁ U) :
    Scheme.Hom.resLE q Z₀ W₀ hW ≫ Scheme.Hom.resLE g U Z₀ hZ
      = Scheme.Hom.resLE pi U W₀ hW' := by
  rw [Scheme.Hom.resLE_comp_resLE]
  subst hpi
  rfl

/-- The sections of a composite are the composite on sections. -/
theorem comp_val_app {Y : Scheme.{u}} {A B C : Y.Modules} (α : A ⟶ B) (β : B ⟶ C)
    (V : Y.Opens) (x : A.val.obj (op V)) :
    (α ≫ β).val.app (op V) x = β.val.app (op V) (α.val.app (op V) x) := rfl

/-- The inverse of `AlgebraicGeometry.Scheme.Modules.pullbackComp q g` sends the pullback of a
section along `q ≫ g` to its pullback along `g` followed by its pullback along `q`. -/
theorem pullbackComp_inv_val_app_pullbackSection {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X)
    (F : X.Modules) (U : X.Opens) (W₀ : Z.Opens) (V : W.Opens) (hg : W₀ ≤ g ⁻¹ᵁ U)
    (hf : V ≤ q ⁻¹ᵁ W₀) (h : V ≤ (q ≫ g) ⁻¹ᵁ U) (a : F.val.obj (op U)) :
    ((Scheme.Modules.pullbackComp q g).inv.app F).val.app (op V)
        (pullbackSection (q ≫ g) F U V h a)
      = pullbackSection q ((Scheme.Modules.pullback g).obj F) W₀ V hf
          (pullbackSection g F U W₀ hg a) := by
  rw [← pullbackSection_comp q g F U W₀ V hg hf h a]
  exact congrArg (fun k : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F) ⟶
      (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F) =>
      k.val.app (op V) (pullbackSection q ((Scheme.Modules.pullback g).obj F) W₀ V hf
        (pullbackSection g F U W₀ hg a)))
    ((Scheme.Modules.pullbackComp q g).app F).hom_inv_id

/-- The comparison `Stacks.Modules.restrictPullbackObjIso` of a restricted pullback with the
pullback of a restriction carries the pullback of a section to the pullback, along the restricted
morphism, of the restricted section. -/
theorem restrictPullbackObjIso_hom_pullbackSection {Y X : Scheme.{u}} (f : Y ⟶ X)
    {U : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (F : X.Modules) (U' : X.Opens)
    (V' : V.toScheme.Opens) (h : V.ι ''ᵁ V' ≤ f ⁻¹ᵁ U')
    (h₃ : V' ≤ (Scheme.Hom.resLE f U V e ≫ U.ι) ⁻¹ᵁ U')
    (hf4 : V' ≤ Scheme.Hom.resLE f U V e ⁻¹ᵁ (U.ι ⁻¹ᵁ U'))
    (a : F.val.obj (op U')) :
    (Stacks.Modules.restrictPullbackObjIso f e F).hom.val.app (op V')
        (pullbackSection f F U' (V.ι ''ᵁ V') h a)
      = pullbackSection (Scheme.Hom.resLE f U V e) (Scheme.Modules.restrict F U.ι)
          (U.ι ⁻¹ᵁ U') V' hf4 (F.val.map (homOfLE (U.ι.image_preimage_le U')).op a) := by
  have h₁ : V' ≤ V.ι ⁻¹ᵁ (V.ι ''ᵁ V') := (V.ι.preimage_image_eq V').ge
  have h₂ : V' ≤ (V.ι ≫ f) ⁻¹ᵁ U' := h₁.trans (Scheme.Hom.preimage_mono _ h)
  rw [Stacks.Modules.restrictPullbackObjIso, Stacks.Modules.restrictPullbackIso]
  change ((Scheme.Modules.pullback (Scheme.Hom.resLE f U V e)).map
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app F)).val.app (op V')
    (((Scheme.Modules.pullbackComp (Scheme.Hom.resLE f U V e) U.ι).inv.app F).val.app (op V')
      (((Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι f e).symm).hom.app F).val.app
          (op V')
        (((Scheme.Modules.pullbackComp V.ι f).hom.app F).val.app (op V')
          (((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app
            ((Scheme.Modules.pullback f).obj F)).val.app (op V')
              (pullbackSection f F U' (V.ι ''ᵁ V') h a))))) = _
  rw [restrictFunctorIsoPullback_hom_val_app V.ι ((Scheme.Modules.pullback f).obj F) V' h₁
      (pullbackSection f F U' (V.ι ''ᵁ V') h a),
    pullbackSection_comp V.ι f F U' (V.ι ''ᵁ V') V' h h₁ h₂ a,
    pullbackSection_congr (Scheme.Hom.resLE_comp_ι f e).symm F U' V' h₂ h₃ a,
    pullbackComp_inv_val_app_pullbackSection (Scheme.Hom.resLE f U V e) U.ι F U'
      (U.ι ⁻¹ᵁ U') V' le_rfl hf4 h₃ a,
    pullbackSection_naturality (Scheme.Hom.resLE f U V e)
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app F) (U.ι ⁻¹ᵁ U') V' hf4
      (pullbackSection U.ι F U' (U.ι ⁻¹ᵁ U') le_rfl a),
    Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection U.ι F U' (U.ι ⁻¹ᵁ U')
      le_rfl (U.ι.image_preimage_le U') a]

/-- A preimage under the restricted morphism of a preimage under `U.ι`. -/
private theorem preimage_le_resLE_preimage {Y X : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens}
    {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (U' : X.Opens) :
    V.ι ⁻¹ᵁ (f ⁻¹ᵁ U') ≤ Scheme.Hom.resLE f U V e ⁻¹ᵁ (U.ι ⁻¹ᵁ U') := by
  conv_rhs => rw [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage]

/-! ### Pentagon: restricting the canonical identification -/

/-- **The pentagon.** Restricting the canonical identification `canHom q g pi hpi F` to `W₀` is,
up to the comparisons `Stacks.Modules.restrictPullbackObjIso`, the canonical identification for
the three restricted morphisms `AlgebraicGeometry.Scheme.Hom.resLE`. -/
theorem restrictFunctor_map_canHom {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X)
    (hpi : q ≫ g = pi) {U : X.Opens} {Z₀ : Z.Opens} {W₀ : W.Opens} (hZ : Z₀ ≤ g ⁻¹ᵁ U)
    (hW : W₀ ≤ q ⁻¹ᵁ Z₀) (hW' : W₀ ≤ pi ⁻¹ᵁ U)
    (hres : Scheme.Hom.resLE q Z₀ W₀ hW ≫ Scheme.Hom.resLE g U Z₀ hZ
      = Scheme.Hom.resLE pi U W₀ hW') (F : X.Modules) :
    (Scheme.Modules.restrictFunctor W₀.ι).map (canHom q g pi hpi F) ≫
        (Stacks.Modules.restrictPullbackObjIso pi hW' F).hom
      = (Stacks.Modules.restrictPullbackObjIso q hW ((Scheme.Modules.pullback g).obj F)).hom ≫
        (Scheme.Modules.pullback (Scheme.Hom.resLE q Z₀ W₀ hW)).map
            (Stacks.Modules.restrictPullbackObjIso g hZ F).hom ≫
          canHom (Scheme.Hom.resLE q Z₀ W₀ hW) (Scheme.Hom.resLE g U Z₀ hZ)
            (Scheme.Hom.resLE pi U W₀ hW') hres (Scheme.Modules.restrict F U.ι) := by
  refine (cancel_epi ((Scheme.Modules.restrictFunctorIsoPullback W₀.ι).inv.app
    ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F)))).mp ?_
  refine hom_ext_of_triplePullbackSection W₀.ι q g (F := F) fun U' a => ?_
  -- the opens and the order relations between them
  have him : W₀.ι ''ᵁ (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U'))) ≤ q ⁻¹ᵁ (g ⁻¹ᵁ U') :=
    W₀.ι.image_preimage_le _
  have hpiLe : W₀.ι ''ᵁ (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U'))) ≤ pi ⁻¹ᵁ U' := by
    subst hpi
    exact him
  have hf4 : (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U')))
      ≤ Scheme.Hom.resLE pi U W₀ hW' ⁻¹ᵁ (U.ι ⁻¹ᵁ U') := by
    subst hpi
    exact preimage_le_resLE_preimage _ hW' U'
  have hf4q := preimage_le_resLE_preimage q hW (V := W₀) (g ⁻¹ᵁ U')
  have hf4g := preimage_le_resLE_preimage g hZ (V := Z₀) U'
  have hz0 : Z₀.ι ''ᵁ (Z₀.ι ⁻¹ᵁ (g ⁻¹ᵁ U')) ≤ g ⁻¹ᵁ U' := Z₀.ι.image_preimage_le _
  -- the common value of the comparison on a thrice pulled-back section
  have h0 : ((Scheme.Modules.restrictFunctorIsoPullback W₀.ι).inv.app
        ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F))).val.app
        (op (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U')))) (triplePullbackSection W₀.ι q g F U' a)
      = pullbackSection q ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ U')
          (W₀.ι ''ᵁ (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U')))) him
          (pullbackSection g F U' (g ⁻¹ᵁ U') le_rfl a) := by
    rw [triplePullbackSection,
      Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection W₀.ι
        ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F))
        (q ⁻¹ᵁ (g ⁻¹ᵁ U')) (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U'))) le_rfl him
        (doublePullbackSection q g F U' a),
      doublePullbackSection,
      pullbackSection_shrink q ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ U')
        (q ⁻¹ᵁ (g ⁻¹ᵁ U')) (W₀.ι ''ᵁ (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U')))) le_rfl him him
        (pullbackSection g F U' (g ⁻¹ᵁ U') le_rfl a)]
  have hL : ((Scheme.Modules.restrictFunctorIsoPullback W₀.ι).inv.app
        ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F)) ≫
        ((Scheme.Modules.restrictFunctor W₀.ι).map (canHom q g pi hpi F) ≫
          (Stacks.Modules.restrictPullbackObjIso pi hW' F).hom)).val.app
        (op (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U')))) (triplePullbackSection W₀.ι q g F U' a)
      = pullbackSection (Scheme.Hom.resLE pi U W₀ hW') (Scheme.Modules.restrict F U.ι)
          (U.ι ⁻¹ᵁ U') (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U'))) hf4
          (F.val.map (homOfLE (U.ι.image_preimage_le U')).op a) := by
    rw [comp_val_app, comp_val_app, h0]
    have e1 : ((Scheme.Modules.restrictFunctor W₀.ι).map (canHom q g pi hpi F)).val.app
          (op (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U'))))
          (pullbackSection q ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ U')
            (W₀.ι ''ᵁ (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U')))) him
            (pullbackSection g F U' (g ⁻¹ᵁ U') le_rfl a))
        = pullbackSection pi F U' (W₀.ι ''ᵁ (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U')))) hpiLe a :=
      canHom_val_app_pullbackSection q g pi hpi F U' (g ⁻¹ᵁ U')
        (W₀.ι ''ᵁ (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U')))) le_rfl him hpiLe a
    rw [e1, restrictPullbackObjIso_hom_pullbackSection pi hW' F U'
      (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U'))) hpiLe hf4 hf4 a]
  have hR : ((Scheme.Modules.restrictFunctorIsoPullback W₀.ι).inv.app
        ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F)) ≫
        ((Stacks.Modules.restrictPullbackObjIso q hW
            ((Scheme.Modules.pullback g).obj F)).hom ≫
          (Scheme.Modules.pullback (Scheme.Hom.resLE q Z₀ W₀ hW)).map
              (Stacks.Modules.restrictPullbackObjIso g hZ F).hom ≫
            canHom (Scheme.Hom.resLE q Z₀ W₀ hW) (Scheme.Hom.resLE g U Z₀ hZ)
              (Scheme.Hom.resLE pi U W₀ hW') hres
              (Scheme.Modules.restrict F U.ι))).val.app
        (op (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U')))) (triplePullbackSection W₀.ι q g F U' a)
      = pullbackSection (Scheme.Hom.resLE pi U W₀ hW') (Scheme.Modules.restrict F U.ι)
          (U.ι ⁻¹ᵁ U') (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U'))) hf4
          (F.val.map (homOfLE (U.ι.image_preimage_le U')).op a) := by
    rw [comp_val_app, comp_val_app, comp_val_app, h0,
      restrictPullbackObjIso_hom_pullbackSection q hW ((Scheme.Modules.pullback g).obj F)
        (g ⁻¹ᵁ U') (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U'))) him hf4q hf4q
        (pullbackSection g F U' (g ⁻¹ᵁ U') le_rfl a),
      pullbackSection_shrink g F U' (g ⁻¹ᵁ U') (Z₀.ι ''ᵁ (Z₀.ι ⁻¹ᵁ (g ⁻¹ᵁ U')))
        le_rfl hz0 hz0 a,
      pullbackSection_naturality (Scheme.Hom.resLE q Z₀ W₀ hW)
        (Stacks.Modules.restrictPullbackObjIso g hZ F).hom (Z₀.ι ⁻¹ᵁ (g ⁻¹ᵁ U'))
        (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U'))) hf4q
        (pullbackSection g F U' (Z₀.ι ''ᵁ (Z₀.ι ⁻¹ᵁ (g ⁻¹ᵁ U'))) hz0 a),
      restrictPullbackObjIso_hom_pullbackSection g hZ F U' (Z₀.ι ⁻¹ᵁ (g ⁻¹ᵁ U')) hz0
        hf4g hf4g a,
      canHom_val_app_pullbackSection (Scheme.Hom.resLE q Z₀ W₀ hW)
        (Scheme.Hom.resLE g U Z₀ hZ) (Scheme.Hom.resLE pi U W₀ hW') hres
        (Scheme.Modules.restrict F U.ι) (U.ι ⁻¹ᵁ U') (Z₀.ι ⁻¹ᵁ (g ⁻¹ᵁ U'))
        (W₀.ι ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U'))) hf4g hf4q hf4
        (F.val.map (homOfLE (U.ι.image_preimage_le U')).op a)]
  exact hL.trans hR.symm


end Stacks.AlgebraicGeometry.ModuleLimits

end
