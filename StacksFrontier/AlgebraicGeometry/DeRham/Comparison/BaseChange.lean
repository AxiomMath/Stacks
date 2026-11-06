module

public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.Conditions
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# Base change of the maps of Stacks Section 0FL7

Consider a commutative square of schemes

```
Y' --b--> Y
|f'       |f
X' --a--> X
```

(`w : b ≫ f = f' ≫ a`), an `𝒪_Y`-module `L`, an `𝒪_{Y'}`-module `L'` and a map
`e : b^*L ⟶ L'` (the identification `b^*det(NL_{Y/X}) ≅ det(NL_{Y'/X'})` of Section 0FKB in the
source). The square of Lemma 0H9G, which condition (0H9E) of Section 0FL7 asks to commute, has
right-hand vertical arrow

`b^*(f^*Ω^p_{X/ℤ} ⊗ L) ≅ b^*f^*Ω^p_{X/ℤ} ⊗ b^*L ⟶ f'^*Ω^p_{X'/ℤ} ⊗ L'`,

the comparison of Tag 01CD followed by `b^*f^* ≅ (b ≫ f)^* = (f' ≫ a)^* ≅ f'^*a^*`, then
`f'^*` of the canonical map `a^*Ω^p_{X/ℤ} ⟶ Ω^p_{X'/ℤ}`, on the first factor and `e` on the
second. This file constructs that arrow, states the compatibility of two families of maps, and
proves the facts about it that do not depend on the particular maps: its values on pullbacks of
local sections, that compatibility can be checked elementwise (over a basis and on generators),
the adjoint form, that compatibilities compose along horizontally composed squares, the
identity square, and the transport of a family along a square whose upper edge induces
isomorphisms on forms (for instance restriction to an open subscheme).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.pullbackFormsBaseChange`: `b^*f^*Ω^p_{X/ℤ} ⟶ f'^*Ω^p_{X'/ℤ}`.
* `AlgebraicGeometry.Scheme.Hom.twistedPullbackFormsBaseChange`: the right-hand vertical arrow
  `b^*(f^*Ω^p_{X/ℤ} ⊗ L) ⟶ f'^*Ω^p_{X'/ℤ} ⊗ L'` of the square of Lemma 0H9G.
* `AlgebraicGeometry.Scheme.Hom.GarelMaps.IsCompatible`: the square of Lemma 0H9G commutes for
  all `p`.
* `AlgebraicGeometry.Scheme.Hom.compBaseChangeHom`: the composite of the maps `e`, `e'` of two
  horizontally composable squares.
* `AlgebraicGeometry.Scheme.Hom.GarelMaps.baseChange` and `GarelMaps.restrict`: the unique
  compatible family along a square whose upper edge induces isomorphisms on absolute forms, and
  its instance for the inclusion of an open subscheme.

## Main results

* `AlgebraicGeometry.Scheme.Hom.pullbackFormsBaseChange_pullbackSection`,
  `twistedPullbackFormsBaseChange_pullbackUnit_tmul` and
  `twistedPullbackFormsBaseChange_pullbackSection_tmul`: the arrows on pullbacks of local
  sections.
* `AlgebraicGeometry.Scheme.Hom.GarelMaps.isCompatible_iff`, `isCompatible_of_isBasis` and
  `isCompatible_iff_homEquiv`: compatibility on local sections, over a basis on generators, and
  through the adjunction `b^* ⊣ b_*`.
* `AlgebraicGeometry.Scheme.Hom.pullbackFormsBaseChange_comp`,
  `twistedPullbackFormsBaseChange_comp` and `GarelMaps.IsCompatible.comp`: compatibility along two
  horizontally composed squares implies compatibility along the outer square.
* `AlgebraicGeometry.Scheme.Hom.GarelMaps.isCompatible_id_iff`: along the identity square, with
  `e` the identity law, compatibility is equality.
* `AlgebraicGeometry.Scheme.Hom.GarelMaps.isCompatible_baseChange` and
  `GarelMaps.IsCompatible.eq_baseChange`.

## Implementation notes

Every identity between the arrows is proved on pullbacks of local sections: a morphism out of a
pullback `g^*M` is determined by its values on the images of local sections of `M` under the unit
of `g^* ⊣ g_*` (`Stacks.PullbackTensorCoherence.pullback_hom_ext` and its variants), and the
coherence isomorphisms `Scheme.Modules.pullbackComp` and `Scheme.Modules.pullbackCongr` act on
those images by `Scheme.Modules.pullbackSection_comp` and `Scheme.Modules.pullbackSection_congr`.
This avoids the pseudofunctor coherences of the pullback entirely.

The comparison of Tag 01CD is `Stacks.PullbackTensorCoherence.pullbackTensorComparison`, which is
the oplax tensorator of the monoidal pullback
(`Stacks.PullbackStrictTensorator.delta_pullbackStrictMonoidal_eq`); its section formula is what
the computations use.

The squares are arbitrary commutative squares; the hypothesis of Lemma 0H9G that `Y'` is an open
subscheme of `X' ×_X Y` plays no role in the construction or in any statement here.

## References

* [Stacks Project, Section 0FL7](https://stacks.math.columbia.edu/tag/0FL7)
* [Stacks Project, Tag 0H9E](https://stacks.math.columbia.edu/tag/0H9E)
* [Stacks Project, Tag 0H9G](https://stacks.math.columbia.edu/tag/0H9G)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/


@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open Stacks.PullbackTensorCoherence

universe u

namespace AlgebraicGeometry

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.AlgebraicGeometry.PullbackSectionMul.schemeTensorStrict

/-- Two morphisms out of an iterated pullback `g^*f^*M` agreeing on the iterated pullbacks of local
sections of `M` are equal. -/
theorem Scheme.Modules.pullback_pullback_hom_ext {Z Y X : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    {M : X.Modules} {N : Z.Modules}
    {θ₁ θ₂ : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M) ⟶ N}
    (h : ∀ (U : X.Opens) (x : M.val.obj (op U)),
      θ₁.val.app (op (g ⁻¹ᵁ f ⁻¹ᵁ U))
          (Scheme.Modules.pullbackSection g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)
            (g ⁻¹ᵁ f ⁻¹ᵁ U) le_rfl (Scheme.Modules.pullbackSection f M U (f ⁻¹ᵁ U) le_rfl x)) =
        θ₂.val.app (op (g ⁻¹ᵁ f ⁻¹ᵁ U))
          (Scheme.Modules.pullbackSection g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)
            (g ⁻¹ᵁ f ⁻¹ᵁ U) le_rfl (Scheme.Modules.pullbackSection f M U (f ⁻¹ᵁ U) le_rfl x))) :
    θ₁ = θ₂ := by
  refine ((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).homEquiv _ N).injective ?_
  refine pullback_hom_ext f.toLRSHom.toShHom fun U x => ?_
  have e : ∀ θ : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M) ⟶ N,
      (((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).homEquiv _ N) θ).val.app
          (op (f ⁻¹ᵁ U.unop)) (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom M U x) =
        θ.val.app (op (g ⁻¹ᵁ f ⁻¹ᵁ U.unop))
          (Scheme.Modules.pullbackSection g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U.unop)
            (g ⁻¹ᵁ f ⁻¹ᵁ U.unop) le_rfl
            (Scheme.Modules.pullbackSection f M U.unop (f ⁻¹ᵁ U.unop) le_rfl x)) := fun θ => by
    refine (Stacks.RingedSpace.homEquiv_val_app g.toLRSHom.toShHom _ N θ _ _).trans ?_
    rw [Stacks.Conormal.pullbackSection_self, Stacks.Conormal.pullbackSection_self]
    rfl
  exact (e θ₁).trans ((h U.unop x).trans (e θ₂).symm)

namespace Scheme.Hom

variable {X X' Y Y' : Scheme.{u}} {f : Y ⟶ X} {a : X' ⟶ X} {f' : Y' ⟶ X'} {b : Y' ⟶ Y}

/-- In a commutative square, `V ≤ b⁻¹W` and `W ≤ f⁻¹U` give `V ≤ f'⁻¹(a⁻¹U)`. -/
theorem le_preimage_preimage_of_comm (w : b ≫ f = f' ≫ a) {U : X.Opens} {W : Y.Opens} {V : Y'.Opens}
    (hf : W ≤ f ⁻¹ᵁ U) (hb : V ≤ b ⁻¹ᵁ W) : V ≤ f' ⁻¹ᵁ (a ⁻¹ᵁ U) := by
  intro y hy
  have h : y ∈ (b ≫ f) ⁻¹ᵁ U := hf (hb hy)
  rwa [w] at h

/-- The inverse of the comparison `(f ≫ g)^* ≅ f^*g^*` carries the pullback of a section along
`f ≫ g` to its iterated pullback. -/
private theorem pullbackComp_inv_app_pullbackSection {Z Y X : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) (W : Y.Opens) (V : Z.Opens) (hg : W ≤ g ⁻¹ᵁ U)
    (hf : V ≤ f ⁻¹ᵁ W) (h : V ≤ (f ≫ g) ⁻¹ᵁ U) (x : M.val.obj (op U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op V)
        (Scheme.Modules.pullbackSection (f ≫ g) M U V h x) =
      Scheme.Modules.pullbackSection f ((Scheme.Modules.pullback g).obj M) W V hf
        (Scheme.Modules.pullbackSection g M U W hg x) :=
  (congrArg _ (Scheme.Modules.pullbackSection_comp f g M U W V hg hf h x).symm).trans
    (Stacks.SheafOfModules.inv_val_app_hom_val_app ((Scheme.Modules.pullbackComp f g).app M)
      (op V) _)

/-- The map `b^*f^*Ω^p_{X/ℤ} ⟶ f'^*Ω^p_{X'/ℤ}` of a commutative square:
`b^*f^* ≅ (b ≫ f)^* = (f' ≫ a)^* ≅ f'^*a^*` followed by `f'^*` of the canonical map
`a^*Ω^p_{X/ℤ} ⟶ Ω^p_{X'/ℤ}`. -/
noncomputable def pullbackFormsBaseChange (w : b ≫ f = f' ≫ a) (p : ℤ) :
    (Scheme.Modules.pullback b).obj (f.pullbackForms p) ⟶ f'.pullbackForms p :=
  (Scheme.Modules.pullbackComp b f).hom.app (absoluteDifferentialForms X p) ≫
    (Scheme.Modules.pullbackCongr w).hom.app (absoluteDifferentialForms X p) ≫
    (Scheme.Modules.pullbackComp f' a).inv.app (absoluteDifferentialForms X p) ≫
    (Scheme.Modules.pullback f').map (a.absoluteFormsMap p)

/-- `b^*f^*Ω^p_{X/ℤ} ⟶ f'^*Ω^p_{X'/ℤ}` carries the iterated pullback of a local form `ω` on `X`
to the pullback along `f'` of the pullback `a^*ω` of `ω` along `a`. -/
theorem pullbackFormsBaseChange_pullbackSection (w : b ≫ f = f' ≫ a) (p : ℤ) (U : X.Opens)
    (W : Y.Opens) (V : Y'.Opens) (hf : W ≤ f ⁻¹ᵁ U) (hb : V ≤ b ⁻¹ᵁ W)
    (ω : (absoluteDifferentialForms X p).val.obj (op U)) :
    (pullbackFormsBaseChange w p).val.app (op V)
        (Scheme.Modules.pullbackSection b (f.pullbackForms p) W V hb
          (Scheme.Modules.pullbackSection f (absoluteDifferentialForms X p) U W hf ω)) =
      Scheme.Modules.pullbackSection f' (absoluteDifferentialForms X' p) (a ⁻¹ᵁ U) V
        (le_preimage_preimage_of_comm w hf hb) (a.absoluteFormsPullback p U ω) := by
  have h1 := Scheme.Modules.pullbackSection_comp b f (absoluteDifferentialForms X p) U W V hf hb
    (hb.trans (Scheme.Hom.preimage_mono b hf)) ω
  have h2 := Scheme.Modules.pullbackSection_congr w (absoluteDifferentialForms X p) U V
    (hb.trans (Scheme.Hom.preimage_mono b hf)) (le_preimage_preimage_of_comm w hf hb) ω
  have h3' := pullbackComp_inv_app_pullbackSection f' a (absoluteDifferentialForms X p) U
    (a ⁻¹ᵁ U) V le_rfl (le_preimage_preimage_of_comm w hf hb)
    (le_preimage_preimage_of_comm w hf hb) ω
  have h4 := Scheme.Modules.pullbackSection_naturality f' (a.absoluteFormsMap p) (a ⁻¹ᵁ U) V
    (le_preimage_preimage_of_comm w hf hb)
    (Scheme.Modules.pullbackSection a (absoluteDifferentialForms X p) U (a ⁻¹ᵁ U) le_rfl ω)
  have h5 := Stacks.Conormal.pullbackSection_self a (absoluteDifferentialForms X p) U ω
  refine (congrArg (fun x => ((Scheme.Modules.pullback f').map (a.absoluteFormsMap p)).val.app
    (op V) (((Scheme.Modules.pullbackComp f' a).inv.app (absoluteDifferentialForms X p)).val.app
      (op V) (((Scheme.Modules.pullbackCongr w).hom.app
        (absoluteDifferentialForms X p)).val.app (op V) x))) h1).trans ?_
  refine (congrArg (fun x => ((Scheme.Modules.pullback f').map (a.absoluteFormsMap p)).val.app
    (op V) (((Scheme.Modules.pullbackComp f' a).inv.app (absoluteDifferentialForms X p)).val.app
      (op V) x)) h2).trans ?_
  refine (congrArg (fun x => ((Scheme.Modules.pullback f').map (a.absoluteFormsMap p)).val.app
    (op V) x) h3').trans ?_
  refine h4.trans ?_
  exact congrArg (fun x => Scheme.Modules.pullbackSection f' (absoluteDifferentialForms X' p)
    (a ⁻¹ᵁ U) V (le_preimage_preimage_of_comm w hf hb)
      ((a.absoluteFormsMap p).val.app (op (a ⁻¹ᵁ U)) x))
    h5

variable {X'' Y'' : Scheme.{u}} {a' : X'' ⟶ X'} {f'' : Y'' ⟶ X''} {b' : Y'' ⟶ Y'}

/-- The maps `b^*f^*Ω^p_{X/ℤ} ⟶ f'^*Ω^p_{X'/ℤ}` compose along horizontally composed squares. -/
theorem pullbackFormsBaseChange_comp (w : b ≫ f = f' ≫ a) (w' : b' ≫ f' = f'' ≫ a')
    (wc : (b' ≫ b) ≫ f = f'' ≫ (a' ≫ a)) (p : ℤ) :
    pullbackFormsBaseChange wc p =
      (Scheme.Modules.pullbackComp b' b).inv.app (f.pullbackForms p) ≫
        (Scheme.Modules.pullback b').map (pullbackFormsBaseChange w p) ≫
          pullbackFormsBaseChange w' p := by
  refine Scheme.Modules.pullback_pullback_hom_ext (b' ≫ b) f fun U x => ?_
  have hL := pullbackFormsBaseChange_pullbackSection wc p U (f ⁻¹ᵁ U)
    ((b' ≫ b) ⁻¹ᵁ f ⁻¹ᵁ U) le_rfl le_rfl x
  refine hL.trans ?_
  have hc' := pullbackComp_inv_app_pullbackSection b' b (f.pullbackForms p) (f ⁻¹ᵁ U)
    (b ⁻¹ᵁ f ⁻¹ᵁ U) ((b' ≫ b) ⁻¹ᵁ f ⁻¹ᵁ U) le_rfl le_rfl le_rfl
    (Scheme.Modules.pullbackSection f (absoluteDifferentialForms X p) U (f ⁻¹ᵁ U) le_rfl x)
  have hn := Scheme.Modules.pullbackSection_naturality b' (pullbackFormsBaseChange w p)
    (b ⁻¹ᵁ f ⁻¹ᵁ U) ((b' ≫ b) ⁻¹ᵁ f ⁻¹ᵁ U) le_rfl
    (Scheme.Modules.pullbackSection b (f.pullbackForms p) (f ⁻¹ᵁ U) (b ⁻¹ᵁ f ⁻¹ᵁ U) le_rfl
      (Scheme.Modules.pullbackSection f (absoluteDifferentialForms X p) U (f ⁻¹ᵁ U) le_rfl x))
  have h1 := pullbackFormsBaseChange_pullbackSection w p U (f ⁻¹ᵁ U) (b ⁻¹ᵁ f ⁻¹ᵁ U) le_rfl
    le_rfl x
  have h2 := pullbackFormsBaseChange_pullbackSection w' p (a ⁻¹ᵁ U) (b ⁻¹ᵁ f ⁻¹ᵁ U)
    ((b' ≫ b) ⁻¹ᵁ f ⁻¹ᵁ U) (le_preimage_preimage_of_comm w le_rfl le_rfl) le_rfl
    (a.absoluteFormsPullback p U x)
  have h3 := absoluteFormsPullback_comp a a' p U x
  refine Eq.symm ((congrArg (fun y => (pullbackFormsBaseChange w' p).val.app
    (op ((b' ≫ b) ⁻¹ᵁ f ⁻¹ᵁ U)) (((Scheme.Modules.pullback b').map
      (pullbackFormsBaseChange w p)).val.app (op ((b' ≫ b) ⁻¹ᵁ f ⁻¹ᵁ U)) y)) hc').trans ?_)
  refine (congrArg (fun y => (pullbackFormsBaseChange w' p).val.app
    (op ((b' ≫ b) ⁻¹ᵁ f ⁻¹ᵁ U)) y) hn).trans ?_
  refine (congrArg (fun y => (pullbackFormsBaseChange w' p).val.app
    (op ((b' ≫ b) ⁻¹ᵁ f ⁻¹ᵁ U)) (Scheme.Modules.pullbackSection b' (f'.pullbackForms p)
      (b ⁻¹ᵁ f ⁻¹ᵁ U) ((b' ≫ b) ⁻¹ᵁ f ⁻¹ᵁ U) le_rfl y)) h1).trans ?_
  refine h2.trans ?_
  exact congrArg (Scheme.Modules.pullbackSection f'' (absoluteDifferentialForms X'' p)
    ((a' ≫ a) ⁻¹ᵁ U) ((b' ≫ b) ⁻¹ᵁ f ⁻¹ᵁ U) _) h3.symm

variable (L : Y.Modules) {L' : Y'.Modules}

/-- **The right-hand vertical arrow of the square of Stacks Lemma 0H9G**:
`b^*(f^*Ω^p_{X/ℤ} ⊗ L) ⟶ b^*f^*Ω^p_{X/ℤ} ⊗ b^*L ⟶ f'^*Ω^p_{X'/ℤ} ⊗ L'`, the comparison of
Tag 01CD followed by `pullbackFormsBaseChange` and `e`. -/
noncomputable def twistedPullbackFormsBaseChange (w : b ≫ f = f' ≫ a)
    (e : (Scheme.Modules.pullback b).obj L ⟶ L') (p : ℤ) :
    (Scheme.Modules.pullback b).obj (f.twistedPullbackForms L p) ⟶
      f'.twistedPullbackForms L' p :=
  pullbackTensorComparison b.toLRSHom.toShHom (f.pullbackForms p) L ≫
    MonoidalCategoryStruct.tensorHom (C := Y'.Modules) (pullbackFormsBaseChange w p) e

/-- The arrow of Lemma 0H9G on the pullback of a local pure tensor `s ⊗ l`. -/
theorem twistedPullbackFormsBaseChange_pullbackUnit_tmul (w : b ≫ f = f' ≫ a)
    (e : (Scheme.Modules.pullback b).obj L ⟶ L') (p : ℤ) (W : Y.Opens)
    (s : (f.pullbackForms p).val.obj (op W)) (l : L.val.obj (op W)) :
    (twistedPullbackFormsBaseChange L w e p).val.app (op (b ⁻¹ᵁ W))
        (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom (f.twistedPullbackForms L p) (op W)
          (tmul Y.toRingedSpace (f.pullbackForms p) L (op W) s l)) =
      tmul Y'.toRingedSpace (f'.pullbackForms p) L' (op (b ⁻¹ᵁ W))
        ((pullbackFormsBaseChange w p).val.app (op (b ⁻¹ᵁ W))
          (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom (f.pullbackForms p) (op W) s))
        (e.val.app (op (b ⁻¹ᵁ W))
          (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom L (op W) l)) := by
  have h1 := pullbackTensorComparison_pullbackUnit b.toLRSHom.toShHom (f.pullbackForms p) L
    (op W) s l
  have h2 := tensorHom_tmul (Z := Y'.toRingedSpace) (pullbackFormsBaseChange w p) e
    (op (b ⁻¹ᵁ W)) (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom (f.pullbackForms p) (op W) s)
    (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom L (op W) l)
  exact (congrArg ((pullbackFormsBaseChange w p ⊗ₘ e).val.app (op (b ⁻¹ᵁ W))) h1).trans h2

variable {L'' : Y''.Modules}

/-- The composite `(b' ≫ b)^*L ≅ b'^*b^*L ⟶ b'^*L' ⟶ L''` of the maps `e` and `e'` of two
horizontally composable squares. -/
noncomputable abbrev compBaseChangeHom (e : (Scheme.Modules.pullback b).obj L ⟶ L')
    (e' : (Scheme.Modules.pullback b').obj L' ⟶ L'') :
    (Scheme.Modules.pullback (b' ≫ b)).obj L ⟶ L'' :=
  (Scheme.Modules.pullbackComp b' b).inv.app L ≫ (Scheme.Modules.pullback b').map e ≫ e'

/-- The arrows of Lemma 0H9G compose along horizontally composed squares. -/
theorem twistedPullbackFormsBaseChange_comp (w : b ≫ f = f' ≫ a) (w' : b' ≫ f' = f'' ≫ a')
    (wc : (b' ≫ b) ≫ f = f'' ≫ (a' ≫ a)) (e : (Scheme.Modules.pullback b).obj L ⟶ L')
    (e' : (Scheme.Modules.pullback b').obj L' ⟶ L'') (p : ℤ) :
    twistedPullbackFormsBaseChange L wc (compBaseChangeHom L e e') p =
      (Scheme.Modules.pullbackComp b' b).inv.app (f.twistedPullbackForms L p) ≫
        (Scheme.Modules.pullback b').map (twistedPullbackFormsBaseChange L w e p) ≫
          twistedPullbackFormsBaseChange L' w' e' p := by
  refine pullback_tensor_hom_ext (b' ≫ b).toLRSHom.toShHom (A := f.pullbackForms p) (B := L)
    fun U s l => ?_
  have hL := twistedPullbackFormsBaseChange_pullbackUnit_tmul L wc (compBaseChangeHom L e e') p
    U.unop s l
  refine hL.trans ?_
  obtain ⟨U⟩ := U
  -- the units of `b' ≫ b` are the composites of the units
  have hA : ∀ (M : Y.Modules) (x : M.val.obj (op U)),
      ((Scheme.Modules.pullbackComp b' b).inv.app M).val.app (op ((b' ≫ b) ⁻¹ᵁ U))
          (Stacks.RingedSpace.pullbackUnit (b' ≫ b).toLRSHom.toShHom M (op U) x) =
        Stacks.RingedSpace.pullbackUnit b'.toLRSHom.toShHom ((Scheme.Modules.pullback b).obj M)
          (op (b ⁻¹ᵁ U)) (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom M (op U) x) :=
    fun M x => Scheme.Modules.pullbackComp_inv_unit b' b M U x
  have hB : ∀ {M N : Y'.Modules} (φ : M ⟶ N) (x : M.val.obj (op (b ⁻¹ᵁ U))),
      ((Scheme.Modules.pullback b').map φ).val.app (op ((b' ≫ b) ⁻¹ᵁ U))
          (Stacks.RingedSpace.pullbackUnit b'.toLRSHom.toShHom M (op (b ⁻¹ᵁ U)) x) =
        Stacks.RingedSpace.pullbackUnit b'.toLRSHom.toShHom N (op (b ⁻¹ᵁ U))
          (φ.val.app (op (b ⁻¹ᵁ U)) x) :=
    fun φ x => Scheme.Modules.unit_app_val_app_naturality b' φ (b ⁻¹ᵁ U) x
  have E1 : (pullbackFormsBaseChange wc p).val.app (op ((b' ≫ b) ⁻¹ᵁ U))
      (Stacks.RingedSpace.pullbackUnit (b' ≫ b).toLRSHom.toShHom (f.pullbackForms p) (op U) s) =
        (pullbackFormsBaseChange w' p).val.app (op ((b' ≫ b) ⁻¹ᵁ U))
          (Stacks.RingedSpace.pullbackUnit b'.toLRSHom.toShHom (f'.pullbackForms p)
            (op (b ⁻¹ᵁ U)) ((pullbackFormsBaseChange w p).val.app (op (b ⁻¹ᵁ U))
              (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom (f.pullbackForms p)
                (op U) s))) :=
    (SheafOfModules.Hom.congr_val_app (pullbackFormsBaseChange_comp w w' wc p) _ _).trans
      (congrArg ((pullbackFormsBaseChange w' p).val.app (op ((b' ≫ b) ⁻¹ᵁ U)))
        ((congrArg (((Scheme.Modules.pullback b').map (pullbackFormsBaseChange w p)).val.app
          (op ((b' ≫ b) ⁻¹ᵁ U))) (hA _ s)).trans (hB _ _)))
  have E2 : (compBaseChangeHom L e e').val.app (op ((b' ≫ b) ⁻¹ᵁ U))
      (Stacks.RingedSpace.pullbackUnit (b' ≫ b).toLRSHom.toShHom L (op U) l) =
        e'.val.app (op ((b' ≫ b) ⁻¹ᵁ U))
          (Stacks.RingedSpace.pullbackUnit b'.toLRSHom.toShHom L' (op (b ⁻¹ᵁ U))
            (e.val.app (op (b ⁻¹ᵁ U))
              (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom L (op U) l))) :=
    congrArg (e'.val.app (op ((b' ≫ b) ⁻¹ᵁ U)))
      ((congrArg (((Scheme.Modules.pullback b').map e).val.app (op ((b' ≫ b) ⁻¹ᵁ U)))
        (hA L l)).trans (hB e _))
  have hC := twistedPullbackFormsBaseChange_pullbackUnit_tmul L w e p U s l
  have hD := twistedPullbackFormsBaseChange_pullbackUnit_tmul L' w' e' p (b ⁻¹ᵁ U)
    ((pullbackFormsBaseChange w p).val.app (op (b ⁻¹ᵁ U))
      (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom (f.pullbackForms p) (op U) s))
    (e.val.app (op (b ⁻¹ᵁ U)) (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom L (op U) l))
  refine Eq.symm ((congrArg (fun y => (twistedPullbackFormsBaseChange L' w' e' p).val.app
    (op ((b' ≫ b) ⁻¹ᵁ U)) (((Scheme.Modules.pullback b').map
      (twistedPullbackFormsBaseChange L w e p)).val.app (op ((b' ≫ b) ⁻¹ᵁ U)) y))
    (hA _ (tmul Y.toRingedSpace (f.pullbackForms p) L (op U) s l))).trans ?_)
  refine (congrArg (fun y => (twistedPullbackFormsBaseChange L' w' e' p).val.app
    (op ((b' ≫ b) ⁻¹ᵁ U)) y) (hB _ _)).trans ?_
  refine (congrArg (fun y => (twistedPullbackFormsBaseChange L' w' e' p).val.app
    (op ((b' ≫ b) ⁻¹ᵁ U)) (Stacks.RingedSpace.pullbackUnit b'.toLRSHom.toShHom
      (f'.twistedPullbackForms L' p) (op (b ⁻¹ᵁ U)) y)) hC).trans ?_
  refine hD.trans ?_
  exact congrArg₂ (tmul Y''.toRingedSpace (f''.pullbackForms p) L'' (op ((b' ≫ b) ⁻¹ᵁ U)))
    E1.symm E2.symm

variable {L}

/-- **Compatibility of two families of maps with a commutative square** (condition (0H9E) of
Stacks Section 0FL7, in the form of Lemma 0H9G): for every `p` the square
`b^*Ω^p_{Y/ℤ} ⟶ b^*(f^*Ω^p_{X/ℤ} ⊗ L) ⟶ f'^*Ω^p_{X'/ℤ} ⊗ L'` and
`b^*Ω^p_{Y/ℤ} ⟶ Ω^p_{Y'/ℤ} ⟶ f'^*Ω^p_{X'/ℤ} ⊗ L'` commutes. -/
def GarelMaps.IsCompatible (w : b ≫ f = f' ≫ a) (e : (Scheme.Modules.pullback b).obj L ⟶ L')
    (c : f.GarelMaps L) (c' : f'.GarelMaps L') : Prop :=
  ∀ p : ℕ, (Scheme.Modules.pullback b).map (c p) ≫ twistedPullbackFormsBaseChange L w e p =
    b.absoluteFormsMap p ≫ c' p

/-- Compatibility through the adjunction `b^* ⊣ b_*`: an equation of morphisms
`Ω^p_{Y/ℤ} ⟶ b_*(f'^*Ω^p_{X'/ℤ} ⊗ L')`. -/
theorem GarelMaps.isCompatible_iff_homEquiv (w : b ≫ f = f' ≫ a)
    (e : (Scheme.Modules.pullback b).obj L ⟶ L') (c : f.GarelMaps L) (c' : f'.GarelMaps L') :
    GarelMaps.IsCompatible w e c c' ↔ ∀ p : ℕ,
      c p ≫ (Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _
          (twistedPullbackFormsBaseChange L w e p) =
        (Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _ (b.absoluteFormsMap p) ≫
          (Scheme.Modules.pushforward b).map (c' p) := by
  refine forall_congr' fun p => ?_
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  exact (Equiv.apply_eq_iff_eq _).symm

/-- **Compatibility on local sections**: for every local form `η` on `Y` over `W`, the image of
`c^p(η)` in `f'^*Ω^p_{X'/ℤ} ⊗ L'` over `b⁻¹W` is `c'^p` of the pullback of `η` along `b`. -/
theorem GarelMaps.isCompatible_iff (w : b ≫ f = f' ≫ a)
    (e : (Scheme.Modules.pullback b).obj L ⟶ L') (c : f.GarelMaps L) (c' : f'.GarelMaps L') :
    GarelMaps.IsCompatible w e c c' ↔ ∀ (p : ℕ) (W : Y.Opens)
      (η : (absoluteDifferentialForms Y p).val.obj (op W)),
      (twistedPullbackFormsBaseChange L w e p).val.app (op (b ⁻¹ᵁ W))
          (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom (f.twistedPullbackForms L p) (op W)
            ((c p).val.app (op W) η)) =
        (c' p).val.app (op (b ⁻¹ᵁ W)) (b.absoluteFormsPullback p W η) := by
  refine forall_congr' fun p => ⟨fun h W η => ?_, fun h => ?_⟩
  · have h1 := SheafOfModules.Hom.congr_val_app h (op (b ⁻¹ᵁ W))
      (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom (absoluteDifferentialForms Y p)
        (op W) η)
    have h2 := Scheme.Modules.unit_app_val_app_naturality b (c p) W η
    exact (congrArg ((twistedPullbackFormsBaseChange L w e p).val.app (op (b ⁻¹ᵁ W)))
      h2.symm).trans h1
  · refine pullback_hom_ext b.toLRSHom.toShHom fun W η => ?_
    have h2 := Scheme.Modules.unit_app_val_app_naturality b (c p) W.unop η
    exact (congrArg ((twistedPullbackFormsBaseChange L w e p).val.app (op (b ⁻¹ᵁ W.unop)))
      h2).trans (h W.unop η)

/-- **Compatibilities compose**: compatibility along two horizontally composable squares gives
compatibility along the outer square, for the composite of the two maps `e` and `e'`. -/
theorem GarelMaps.IsCompatible.comp {w : b ≫ f = f' ≫ a} {w' : b' ≫ f' = f'' ≫ a'}
    (wc : (b' ≫ b) ≫ f = f'' ≫ (a' ≫ a)) {e : (Scheme.Modules.pullback b).obj L ⟶ L'}
    {e' : (Scheme.Modules.pullback b').obj L' ⟶ L''} {c : f.GarelMaps L} {c' : f'.GarelMaps L'}
    {c'' : f''.GarelMaps L''} (h : GarelMaps.IsCompatible w e c c')
    (h' : GarelMaps.IsCompatible w' e' c' c'') :
    GarelMaps.IsCompatible wc (compBaseChangeHom L e e') c c'' := by
  intro p
  rw [twistedPullbackFormsBaseChange_comp L w w' wc e e', absoluteFormsMap_comp b b',
    ← Category.assoc, (Scheme.Modules.pullbackComp b' b).inv.naturality (c p),
    Category.assoc, Category.assoc, Category.assoc]
  congr 1
  rw [Functor.comp_map, ← Category.assoc, ← Functor.map_comp, h p, Functor.map_comp,
    Category.assoc, h' p]

/-- **Compatibility may be checked locally and on generators**: it suffices to check the
elementwise form of `isCompatible_iff` over the opens `W` of a basis of `Y`, for `η` in a set
generating the sections of `Ω^p_{Y/ℤ}` over `W` as a `Γ(Y, W)`-module. -/
theorem GarelMaps.isCompatible_of_isBasis (w : b ≫ f = f' ≫ a)
    (e : (Scheme.Modules.pullback b).obj L ⟶ L') (c : f.GarelMaps L) (c' : f'.GarelMaps L')
    {𝔅 : Set Y.Opens} (h𝔅 : Opens.IsBasis 𝔅)
    (S : ∀ (p : ℕ) (W : Y.Opens), Set ((absoluteDifferentialForms Y p).val.obj (op W)))
    (hS : ∀ (p : ℕ), ∀ W ∈ 𝔅, Submodule.span (Y.ringCatSheaf.obj.obj (op W)) (S p W) = ⊤)
    (h : ∀ (p : ℕ), ∀ W ∈ 𝔅, ∀ η ∈ S p W,
      (twistedPullbackFormsBaseChange L w e p).val.app (op (b ⁻¹ᵁ W))
          (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom (f.twistedPullbackForms L p) (op W)
            ((c p).val.app (op W) η)) =
        (c' p).val.app (op (b ⁻¹ᵁ W)) (b.absoluteFormsPullback p W η)) :
    GarelMaps.IsCompatible w e c c' := by
  refine (GarelMaps.isCompatible_iff w e c c').2 fun p => ?_
  let N := (Scheme.Modules.pushforward b).obj (f'.twistedPullbackForms L' p)
  let g₁ : absoluteDifferentialForms Y p ⟶ N :=
    c p ≫ (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app _ ≫
      (Scheme.Modules.pushforward b).map (twistedPullbackFormsBaseChange L w e p)
  let g₂ : absoluteDifferentialForms Y p ⟶ N :=
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app _ ≫
      (Scheme.Modules.pushforward b).map (b.absoluteFormsMap p ≫ c' p)
  have e₁ : ∀ (W : Y.Opens) (η : (absoluteDifferentialForms Y p).val.obj (op W)),
      g₁.val.app (op W) η = (twistedPullbackFormsBaseChange L w e p).val.app (op (b ⁻¹ᵁ W))
          (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom (f.twistedPullbackForms L p) (op W)
            ((c p).val.app (op W) η)) := fun W η => rfl
  have e₂ : ∀ (W : Y.Opens) (η : (absoluteDifferentialForms Y p).val.obj (op W)),
      g₂.val.app (op W) η = (c' p).val.app (op (b ⁻¹ᵁ W)) (b.absoluteFormsPullback p W η) :=
    fun W η => rfl
  have hB : ∀ W ∈ 𝔅, ∀ η, g₁.val.app (op W) η = g₂.val.app (op W) η := by
    intro W hW η
    have hη : η ∈ Submodule.span (Y.ringCatSheaf.obj.obj (op W)) (S p W) :=
      hS p W hW ▸ Submodule.mem_top
    induction hη using Submodule.span_induction with
    | mem x hx => exact (e₁ W x).trans ((h p W hW x hx).trans (e₂ W x).symm)
    | zero => rw [map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul r x _ hx => rw [map_smul, map_smul, hx]
  have hg : g₁ = g₂ := by
    refine Scheme.Modules.hom_ext g₁ g₂ fun O => ?_
    ext z
    have hc : ∀ x : O, ∃ V ∈ 𝔅, (x : Y) ∈ V ∧ V ≤ O := fun x =>
      (Opens.isBasis_iff_nbhd.mp h𝔅) x.2
    choose V hV𝔅 hxV hVO using hc
    have key : ∀ (x : O) (g : absoluteDifferentialForms Y p ⟶ N),
        N.val.map (homOfLE (hVO x)).op (g.val.app (op O) z) =
          g.val.app (op (V x)) ((absoluteDifferentialForms Y p).val.map (homOfLE (hVO x)).op z) :=
      fun x g => (PresheafOfModules.naturality_apply g.val (homOfLE (hVO x)).op z).symm
    exact TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf _).obj N) V O
      (fun x => homOfLE (hVO x)) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV _⟩) _ _
      fun x => (key x g₁).trans ((hB _ (hV𝔅 x) _).trans (key x g₂).symm)
  exact fun W η => (e₁ W η).symm.trans ((SheafOfModules.Hom.congr_val_app hg (op W) η).trans
    (e₂ W η))

/-! ### The identity square -/

/-- For the identity square, `(𝟙 Y)^*f^*Ω^p_{X/ℤ} ⟶ f^*Ω^p_{X/ℤ}` is the identity law. -/
theorem pullbackFormsBaseChange_id (w : 𝟙 Y ≫ f = f ≫ 𝟙 X) (p : ℤ) :
    pullbackFormsBaseChange w p = (Scheme.Modules.pullbackId Y).hom.app (f.pullbackForms p) := by
  refine Scheme.Modules.pullback_pullback_hom_ext (𝟙 Y) f fun U x => ?_
  refine (pullbackFormsBaseChange_pullbackSection w p U (f ⁻¹ᵁ U) (f ⁻¹ᵁ U) le_rfl le_rfl
    x).trans ?_
  refine (congrArg (Scheme.Modules.pullbackSection f (absoluteDifferentialForms X p) U
    (f ⁻¹ᵁ U) le_rfl) (absoluteFormsPullback_id p U x)).trans ?_
  rw [Stacks.Conormal.pullbackSection_self (𝟙 Y)]
  exact (Scheme.Modules.pullbackId_hom_app_unit _ _ _).symm

variable (L) in
/-- For the identity square and `e` the identity law, the arrow of Lemma 0H9G is the identity
law. -/
theorem twistedPullbackFormsBaseChange_id (w : 𝟙 Y ≫ f = f ≫ 𝟙 X) (p : ℤ) :
    twistedPullbackFormsBaseChange L w ((Scheme.Modules.pullbackId Y).hom.app L) p =
      (Scheme.Modules.pullbackId Y).hom.app (f.twistedPullbackForms L p) := by
  refine pullback_tensor_hom_ext (Scheme.Hom.toLRSHom (𝟙 Y)).toShHom (A := f.pullbackForms p)
    (B := L)
    fun U s l => ?_
  refine (twistedPullbackFormsBaseChange_pullbackUnit_tmul L w _ p U.unop s l).trans ?_
  refine Eq.trans ?_ (Scheme.Modules.pullbackId_hom_app_unit _ U.unop _).symm
  exact congrArg₂ (tmul Y.toRingedSpace (f.pullbackForms p) L U)
    ((SheafOfModules.Hom.congr_val_app (pullbackFormsBaseChange_id w p) _ _).trans
      (Scheme.Modules.pullbackId_hom_app_unit _ U.unop s))
    (Scheme.Modules.pullbackId_hom_app_unit _ U.unop l)

/-- **Along the identity square, compatibility is equality**, when `e` is the identity law. -/
theorem GarelMaps.isCompatible_id_iff (w : 𝟙 Y ≫ f = f ≫ 𝟙 X) (c c' : f.GarelMaps L) :
    GarelMaps.IsCompatible w ((Scheme.Modules.pullbackId Y).hom.app L) c c' ↔ c = c' := by
  refine ⟨fun h => funext fun p => ?_, fun h p => ?_⟩
  · have hp := h p
    rw [twistedPullbackFormsBaseChange_id L w, absoluteFormsMap_id Y] at hp
    have hn := (Scheme.Modules.pullbackId Y).hom.naturality (c p)
    rw [hn] at hp
    exact (((Scheme.Modules.pullbackId Y).app _).cancel_iso_hom_left _ _).1 hp
  · subst h
    rw [twistedPullbackFormsBaseChange_id L w, absoluteFormsMap_id Y]
    exact (Scheme.Modules.pullbackId Y).hom.naturality (c p)

/-! ### Transport along a square whose upper edge induces isomorphisms on forms -/

/-- The transport of a family `c` along a commutative square whose upper edge `b` induces
isomorphisms `b^*Ω^p_{Y/ℤ} ≅ Ω^p_{Y'/ℤ}`: the unique family compatible with `c`. -/
noncomputable def GarelMaps.baseChange (w : b ≫ f = f' ≫ a)
    (e : (Scheme.Modules.pullback b).obj L ⟶ L') [∀ p : ℤ, IsIso (b.absoluteFormsMap p)]
    (c : f.GarelMaps L) : f'.GarelMaps L' :=
  fun p => inv (b.absoluteFormsMap p) ≫ (Scheme.Modules.pullback b).map (c p) ≫
    twistedPullbackFormsBaseChange L w e p

/-- The transported family is compatible with the given one. -/
theorem GarelMaps.isCompatible_baseChange (w : b ≫ f = f' ≫ a)
    (e : (Scheme.Modules.pullback b).obj L ⟶ L') [∀ p : ℤ, IsIso (b.absoluteFormsMap p)]
    (c : f.GarelMaps L) : GarelMaps.IsCompatible w e c (c.baseChange w e) :=
  fun _ => (IsIso.hom_inv_id_assoc _ _).symm

/-- A family compatible with `c` along a square whose upper edge induces isomorphisms on forms
is the transported family: compatible families are unique there. -/
theorem GarelMaps.IsCompatible.eq_baseChange {w : b ≫ f = f' ≫ a}
    {e : (Scheme.Modules.pullback b).obj L ⟶ L'} [∀ p : ℤ, IsIso (b.absoluteFormsMap p)]
    {c : f.GarelMaps L} {c' : f'.GarelMaps L'} (h : GarelMaps.IsCompatible w e c c') :
    c' = c.baseChange w e :=
  funext fun p => (IsIso.eq_inv_comp _).2 (h p).symm

/-! ### Restriction to an open subscheme -/

/-- The square restricting `f` to an open subscheme `U` of `Y`. -/
theorem restrict_comm (U : Y.Opens) : U.ι ≫ f = (U.ι ≫ f) ≫ 𝟙 X :=
  (Category.comp_id _).symm

/-- **Restriction of a family of maps to an open subscheme** `U ⊆ Y`, along the square with
upper edge the inclusion of `U` and lower edge the identity of `X`, with `e` the identity. -/
noncomputable def GarelMaps.restrict (U : Y.Opens) (c : f.GarelMaps L) :
    (U.ι ≫ f).GarelMaps ((Scheme.Modules.pullback U.ι).obj L) :=
  c.baseChange (restrict_comm U) (𝟙 _)

/-- The restriction to an open subscheme is compatible with the given family. -/
theorem GarelMaps.isCompatible_restrict (U : Y.Opens) (c : f.GarelMaps L) :
    GarelMaps.IsCompatible (restrict_comm U) (𝟙 _) c (c.restrict U) :=
  GarelMaps.isCompatible_baseChange _ _ c

/-- The arrow of Lemma 0H9G on the pullback of a local pure tensor `s ⊗ l` over `W`, restricted
to an open `V ≤ b⁻¹W`. -/
theorem twistedPullbackFormsBaseChange_pullbackSection_tmul (w : b ≫ f = f' ≫ a)
    (e : (Scheme.Modules.pullback b).obj L ⟶ L') (p : ℤ) (W : Y.Opens) (V : Y'.Opens)
    (h : V ≤ b ⁻¹ᵁ W) (s : (f.pullbackForms p).val.obj (op W)) (l : L.val.obj (op W)) :
    (twistedPullbackFormsBaseChange L w e p).val.app (op V)
        (Scheme.Modules.pullbackSection b (f.twistedPullbackForms L p) W V h
          (tmul Y.toRingedSpace (f.pullbackForms p) L (op W) s l)) =
      tmul Y'.toRingedSpace (f'.pullbackForms p) L' (op V)
        ((pullbackFormsBaseChange w p).val.app (op V)
          (Scheme.Modules.pullbackSection b (f.pullbackForms p) W V h s))
        (e.val.app (op V) (Scheme.Modules.pullbackSection b L W V h l)) := by
  refine (PresheafOfModules.naturality_apply (twistedPullbackFormsBaseChange L w e p).val
    (homOfLE h).op _).trans ?_
  refine (congrArg _ (twistedPullbackFormsBaseChange_pullbackUnit_tmul L w e p W s l)).trans ?_
  refine (tmul_restrict (homOfLE h).op _ _).trans ?_
  exact congrArg₂ (tmul Y'.toRingedSpace (f'.pullbackForms p) L' (op V))
    (PresheafOfModules.naturality_apply (pullbackFormsBaseChange w p).val (homOfLE h).op _).symm
    (PresheafOfModules.naturality_apply e.val (homOfLE h).op _).symm

end Scheme.Hom

end AlgebraicGeometry
