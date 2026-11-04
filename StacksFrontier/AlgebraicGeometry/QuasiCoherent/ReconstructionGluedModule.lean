module

public import StacksFrontier.AlgebraicGeometry.InvertibleLocal.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeModuleGlue.Chart

/-!
# Gluing a module from modules on an open cover, and invertibility of the glued module

Let `Y` be a scheme, let `V i` be an open cover of `Y` and let `L i` be a sheaf of
`𝒪_{V i}`-modules for each `i`.  This file assembles the `L i` into a single sheaf of
`𝒪_Y`-modules restricting to each `L i`, and shows that it is invertible when every `L i` is,
under the transition hypotheses that are exactly necessary for that to hold.

The transition hypotheses are the data fields of
`Stacks.AlgebraicGeometry.SchemeModuleGlue.ChartGlueData`: for each pair `i j` and each open
`W` of `Y` inside both `V i` and `V j`, an `𝒪_Y(W)`-linear isomorphism between the sections of
`L i` and of `L j` above `W`, compatible with shrinking `W` and satisfying the cocycle condition
`φ_{jk} ∘ φ_{ij} = φ_{ik}`.  Nothing weaker suffices: the glued module is the sheaf of families
of sections that agree under the `φ_{ij}`, and without the compatibility with restriction such
families are not closed under restriction, while without the cocycle condition the comparison
over a triple overlap is not well defined.

Invertibility of the glued module is then
`Stacks.Modules.isInvertible_of_isInvertible_restrict_isOpenCover` of
`StacksFrontier/AlgebraicGeometry/InvertibleLocal/Basic.lean` — invertibility of a module on a
scheme is local on the base — applied to the chart isomorphisms.

All three transition hypotheses are shown to be *implied* by the conclusion:
`AlgebraicGeometry.transOfRestrictIso`, `AlgebraicGeometry.transOfRestrictIso_resLE` and
`AlgebraicGeometry.transOfRestrictIso_trans` build them, in exactly the form the gluing asks
for, out of a single module restricting to the `L i`.  So nothing stronger than the conclusion
is assumed and no gap is hidden inside a hypothesis.

## Main definitions

* `AlgebraicGeometry.overlapChartSections` — the sections of a module on an open subscheme over
  an open of the ambient scheme, with scalars the functions on that open.  This is the spelling
  in which the gluing machinery takes its transition data.
* `AlgebraicGeometry.pushforwardRestrictSectionsEquiv` — for `W ≤ V`, the sections above `W` of
  the restriction of a module `M` to `V` are the sections of `M` over `W`.
* `AlgebraicGeometry.chartSectionsEquivOfIso` — an isomorphism of modules on `V` read on
  sections above an open of `Y`.
* `AlgebraicGeometry.transOfRestrictIso` — the transition isomorphisms carried by a single
  module restricting to the `L i`.
* `AlgebraicGeometry.restrictOfLEIso` — for `W ≤ V`, the restriction to `W` of a module on `Y`,
  read through a module on `V` isomorphic to its restriction there.

## Main results

* `AlgebraicGeometry.exists_module_of_overlapCompatible` — the gluing: a single `𝒪_Y`-module
  whose restriction to each `V i` is isomorphic to `L i`.
* `AlgebraicGeometry.exists_invertibleModule_of_isOpenCover_of_overlapCompatible` — the same
  module, together with its invertibility when each `L i` is invertible.
* `AlgebraicGeometry.transOfRestrictIso_resLE` and
  `AlgebraicGeometry.transOfRestrictIso_trans` — the converses: the transition data built from a
  global module satisfies the compatibility with restriction and the cocycle condition.
* `AlgebraicGeometry.restrictHomOfLEIso` and `AlgebraicGeometry.restrictHomOfLEIso_trans` — the
  same converse content in the `restrict` spelling, where it reads as an isomorphism
  `L i|_W ≅ L j|_W` of sheaves of modules on the open subscheme `W`.

## Relation to [Stacks, Tag 0GPJ]

The conclusion of [Stacks, Tag 0GPJ] is a *single* isomorphism of schemes together with a
*single* invertible module; what
`AlgebraicGeometry.exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover` proves is
the per-chart form, opens `V i` covering `Y` and for each `i` an isomorphism `f i : V i ≅ U i`
and an invertible module `L i` on `V i`.  The Stacks source dismisses the passage from one to
the other with "We omit the details".

`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGluedIso.lean` supplies the scheme
half of that passage as a reduction.  This file supplies the module half, also **as a
reduction**: the transition isomorphisms are isolated as hypotheses, and the converses above
show that nothing stronger than the conclusion has been assumed.

The transitions are *not* discharged for the reconstruction's own charts, and cannot be with
what this repository has.  The `L i` come out of
`AlgebraicGeometry.exists_eq_compl_supportSet_schemeIso_invertibleSheaf` by independent
existential choices, one per index, and are related only through the single global equivalence
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)`.  Producing a transition isomorphism over `V i ⊓ V j` needs a
rigidity theorem for the matched pair `(f i, L i)` — that the isomorphism of schemes and the
invertible module attached to a quasi-coherent equivalence are determined by the equivalence,
hence compatible with restriction to a smaller open — and this repository contains no such
statement in any form.

## Implementation notes

**Why the sections comparison is only a restriction map.**  The sections of
`(V.ι)_* (M|_V)` over `W` are, by `rfl`, the sections of `M` over `V.ι ''ᵁ (V.ι ⁻¹ᵁ W)`, with
the scalars transported along `V.ι.app W` and `(V.ι.appIso _).inv`.  For `W ≤ V` that open is
`W` again, so `pushforwardRestrictSectionsEquiv` is `M.val.map` along an equality of opens; its
linearity is `Scheme.Hom.app_appIso_inv`, which says the transported scalar is the restriction
of the original one, and `Scheme.Opens.ι_appIso`, which says that for the inclusion of an open
subscheme the comparison of sections is the identity.

**Everything in sight is a restriction map of `M`.**  That is why
`PresheafOfModules.map_map_eq_map_map` closes the compatibility with restriction: both sides are
a composite of two restriction maps of `M` between the same pair of opens, and morphisms between
opens are unique.  The same lemma is needed in the form of
`PresheafOfModules.map_map_eq_self` in
`StacksFrontier/AlgebraicGeometry/SchemeModuleGlue/Chart.lean`, for the same reason.  It is stated
for an abstract presheaf of modules on a space rather than for `M.val` because at `M.val` the
rewrite fails: `Scheme.ringCatSheaf` is `TopCat.Sheaf`, which instance search does not see
through, so the composite is not recognised as type-correct.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.SchemeModuleGlue

universe u

namespace PresheafOfModules

variable {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}

/-- **Two restrictions of a section through different intermediate opens agree.**  Restricting
from `A` to `D` through `B` and through `C` gives the same section: the two composites are
morphisms `A ⟶ D` in the category of opens, and those are unique.

This is `PresheafOfModules.map_map_eq_self` of
`StacksFrontier/AlgebraicGeometry/SchemeModuleGlue/Chart.lean` with `A = D` dropped. -/
theorem map_map_eq_map_map (N : PresheafOfModules.{u} 𝒪) {A B C D : Opens X}
    (f : (op A : (Opens X)ᵒᵖ) ⟶ op B) (g : (op B : (Opens X)ᵒᵖ) ⟶ op D)
    (f' : (op A : (Opens X)ᵒᵖ) ⟶ op C) (g' : (op C : (Opens X)ᵒᵖ) ⟶ op D)
    (x : N.obj (op A)) : N.map g (N.map f x) = N.map g' (N.map f' x) := by
  rw [← N.map_comp_apply, ← N.map_comp_apply]
  exact N.congr_map_apply (Subsingleton.elim _ _) x

end PresheafOfModules

namespace AlgebraicGeometry

/-! ### The sections of a chart module over an open of the base -/

/-- The sections of a module `L` on the open subscheme `V` of `Y` over an open `W` of `Y`, as a
module over the functions on `W`.  By `rfl` the underlying type is the sections of `L` over
`V.ι ⁻¹ᵁ W`; passing through the pushforward is what makes the scalars `𝒪_Y(W)`, so that every
open of `Y` carries its sections over one ring and the transition data below needs no
transport. -/
abbrev overlapChartSections {Y : Scheme.{u}} (V : Y.Opens) (L : V.toScheme.Modules)
    (W : Y.Opens) : ModuleCat.{u} (ToType (Y.ringCatSheaf.obj.obj (op W))) :=
  ((Scheme.Modules.pushforward V.ι).obj L).val.obj (op W)

/-! ### The gluing -/

/-- **Gluing a family of modules on an open cover into a single module.**  Let `V i` be opens of
the scheme `Y` and let `L i` be a module on each open subscheme `V i`.  Given, for each pair
`i j` and each open `W` of `Y` inside both `V i` and `V j`, an `𝒪_Y(W)`-linear isomorphism
`φ i j` between the sections of `L i` and of `L j` above `W`, compatible with shrinking `W` and
satisfying the cocycle condition, there is a single module on `Y` whose restriction to each
`V i` is isomorphic to `L i`.

The hypotheses are exactly the data fields of
`Stacks.AlgebraicGeometry.SchemeModuleGlue.ChartGlueData`; the module is its `glued` and the
isomorphisms are its `chartIso`.  See `AlgebraicGeometry.transOfRestrictIso` and its two
companion lemmas for the converse, which builds the hypotheses out of the conclusion. -/
theorem exists_module_of_overlapCompatible {Y : Scheme.{u}} {ι : Type u}
    (V : ι → Y.Opens) (L : ∀ i, (V i).toScheme.Modules)
    (φ : ∀ (i j : ι) {W : Y.Opens}, W ≤ V i → W ≤ V j →
      overlapChartSections (V i) (L i) W ≃ₗ[Y.ringCatSheaf.obj.obj (op W)]
        overlapChartSections (V j) (L j) W)
    (φ_map : ∀ (i j : ι) {W W' : Y.Opens} (hi : W ≤ V i) (hj : W ≤ V j) (hW : W' ≤ W)
      (s : overlapChartSections (V i) (L i) W),
      φ i j (hW.trans hi) (hW.trans hj)
          (((Scheme.Modules.pushforward (V i).ι).obj (L i)).val.resLE hW s)
        = ((Scheme.Modules.pushforward (V j).ι).obj (L j)).val.resLE hW (φ i j hi hj s))
    (φ_trans : ∀ (i j k : ι) {W : Y.Opens} (hi : W ≤ V i) (hj : W ≤ V j) (hk : W ≤ V k)
      (s : overlapChartSections (V i) (L i) W),
      φ j k hj hk (φ i j hi hj s) = φ i k hi hk s) :
    ∃ M : Y.Modules, ∀ i, Nonempty (Scheme.Modules.restrict M (V i).ι ≅ L i) :=
  let G : ChartGlueData Y V :=
    { chart := fun i => (V i).toScheme
      hom := fun i => (V i).ι
      sheaf := L
      trans := φ
      trans_map := φ_map
      trans_trans := φ_trans }
  ⟨G.glued, fun i => ⟨chartIso G i ((V i).ι_image_le ⊤)⟩⟩

/-- **The glued module is invertible when every chart module is.**  This is
`AlgebraicGeometry.exists_module_of_overlapCompatible` with the invertibility of the glued
module added, which is where the `V i` have to cover `Y`: invertibility of a module on a scheme
is local on the base by `Stacks.Modules.isInvertible_of_isInvertible_restrict_isOpenCover`, and
the chart isomorphisms carry the invertibility of `L i` over to the restriction of the glued
module.

Together with `AlgebraicGeometry.exists_schemeIso_of_isOpenCover_of_overlapCompatible` of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGluedIso.lean` this is the whole last
step of [Stacks, Tag 0GPJ], reduced to the two overlap compatibilities for the schemes and the
transition data for the modules. -/
theorem exists_invertibleModule_of_isOpenCover_of_overlapCompatible {Y : Scheme.{u}} {ι : Type u}
    (V : ι → Y.Opens) (hV : IsOpenCover V) (L : ∀ i, (V i).toScheme.Modules)
    (hL : ∀ i, Stacks.SheafOfModules.IsInvertible (V i).toScheme.presheaf
      (V i).toScheme.ringCatSheaf.2 (L i))
    (φ : ∀ (i j : ι) {W : Y.Opens}, W ≤ V i → W ≤ V j →
      overlapChartSections (V i) (L i) W ≃ₗ[Y.ringCatSheaf.obj.obj (op W)]
        overlapChartSections (V j) (L j) W)
    (φ_map : ∀ (i j : ι) {W W' : Y.Opens} (hi : W ≤ V i) (hj : W ≤ V j) (hW : W' ≤ W)
      (s : overlapChartSections (V i) (L i) W),
      φ i j (hW.trans hi) (hW.trans hj)
          (((Scheme.Modules.pushforward (V i).ι).obj (L i)).val.resLE hW s)
        = ((Scheme.Modules.pushforward (V j).ι).obj (L j)).val.resLE hW (φ i j hi hj s))
    (φ_trans : ∀ (i j k : ι) {W : Y.Opens} (hi : W ≤ V i) (hj : W ≤ V j) (hk : W ≤ V k)
      (s : overlapChartSections (V i) (L i) W),
      φ j k hj hk (φ i j hi hj s) = φ i k hi hk s) :
    ∃ M : Y.Modules, (∀ i, Nonempty (Scheme.Modules.restrict M (V i).ι ≅ L i)) ∧
      Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M := by
  obtain ⟨M, hM⟩ := exists_module_of_overlapCompatible V L φ φ_map φ_trans
  refine ⟨M, hM, Stacks.Modules.isInvertible_of_isInvertible_restrict_isOpenCover M V hV
    fun i => ?_⟩
  have : Stacks.SheafOfModules.IsInvertible (V i).toScheme.presheaf
    (V i).toScheme.ringCatSheaf.2 (L i) := hL i
  exact Stacks.SheafOfModules.isInvertible_of_iso _ _ (hM i).some.symm

/-! ### The sections comparison for a restriction -/

/-- An open of `Y` contained in `V` is the image of its preimage in the open subscheme `V`. -/
theorem image_preimage_ι_eq_self {Y : Scheme.{u}} (V : Y.Opens) {W : Y.Opens} (h : W ≤ V) :
    V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

/-- Two restrictions of a function between two equal opens compose to the identity.  This is
the statement of `PresheafOfModules.map_map_eq_self` for the structure sheaf, which is what the
scalars of the sections comparison need. -/
theorem ringPresheaf_map_map_self {Y : Scheme.{u}} {A B : Y.Opens}
    (f : (op A : (Opens Y)ᵒᵖ) ⟶ op B) (g : (op B : (Opens Y)ᵒᵖ) ⟶ op A)
    (r : Y.presheaf.obj (op A)) : (Y.presheaf.map g) ((Y.presheaf.map f) r) = r := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp,
    show f ≫ g = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
  rfl

/-- **The sections above `W ≤ V` of the restriction of `M` to `V` are the sections of `M` over
`W`.**  The underlying map is the restriction of `M` along the equality
`V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W`; its linearity over `𝒪_Y(W)` is `Scheme.Hom.app_appIso_inv`.

This is the only non-formal ingredient of the converse below: it is what makes the two chart
descriptions of a global module comparable. -/
def pushforwardRestrictSectionsEquiv {Y : Scheme.{u}} (M : Y.Modules)
    (V : Y.Opens) {W : Y.Opens} (h : W ≤ V) :
    overlapChartSections V (Scheme.Modules.restrict M V.ι) W
      ≃ₗ[Y.ringCatSheaf.obj.obj (op W)] M.val.obj (op W) where
  toFun x := M.val.map (eqToHom (image_preimage_ι_eq_self V h).symm).op x
  invFun y := M.val.map (eqToHom (image_preimage_ι_eq_self V h)).op y
  map_add' x y := map_add (M.val.restrictₛₗ (eqToHom (image_preimage_ι_eq_self V h).symm).op) x y
  map_smul' r x := by
    refine Eq.trans (map_smulₛₗ
      (M.val.restrictₛₗ (eqToHom (image_preimage_ι_eq_self V h).symm).op)
      (((V.ι.appIso (V.ι ⁻¹ᵁ W)).inv).hom ((V.ι.app W).hom r))
      (x : M.val.obj (op (V.ι ''ᵁ (V.ι ⁻¹ᵁ W))))) ?_
    congr 1
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Opens.ι_app]
    exact ringPresheaf_map_map_self _ _ r
  left_inv x :=
    PresheafOfModules.map_map_eq_self M.val (eqToHom (image_preimage_ι_eq_self V h).symm).op
      (eqToHom (image_preimage_ι_eq_self V h)).op
      (x : M.val.obj (op (V.ι ''ᵁ (V.ι ⁻¹ᵁ W))))
  right_inv y :=
    PresheafOfModules.map_map_eq_self M.val (eqToHom (image_preimage_ι_eq_self V h)).op
      (eqToHom (image_preimage_ι_eq_self V h).symm).op y

/-- `AlgebraicGeometry.pushforwardRestrictSectionsEquiv` acts by the restriction map of `M`. -/
theorem pushforwardRestrictSectionsEquiv_apply {Y : Scheme.{u}} (M : Y.Modules) (V : Y.Opens)
    {W : Y.Opens} (h : W ≤ V)
    (x : overlapChartSections V (Scheme.Modules.restrict M V.ι) W) :
    pushforwardRestrictSectionsEquiv M V h x
      = M.val.map (eqToHom (image_preimage_ι_eq_self V h).symm).op
          (x : M.val.obj (op (V.ι ''ᵁ (V.ι ⁻¹ᵁ W)))) := rfl

/-- The sections comparison commutes with restriction to a smaller open: both sides are two
restriction maps of `M` between the same pair of opens. -/
theorem pushforwardRestrictSectionsEquiv_resLE {Y : Scheme.{u}} (M : Y.Modules) (V : Y.Opens)
    {W W' : Y.Opens} (h : W ≤ V) (hW : W' ≤ W)
    (x : overlapChartSections V (Scheme.Modules.restrict M V.ι) W) :
    pushforwardRestrictSectionsEquiv M V (hW.trans h)
        (((Scheme.Modules.pushforward V.ι).obj (Scheme.Modules.restrict M V.ι)).val.resLE hW x)
      = M.val.resLE hW (pushforwardRestrictSectionsEquiv M V h x) := by
  have hL : pushforwardRestrictSectionsEquiv M V (hW.trans h)
        (((Scheme.Modules.pushforward V.ι).obj (Scheme.Modules.restrict M V.ι)).val.resLE hW x)
      = M.val.map (eqToHom (image_preimage_ι_eq_self V (hW.trans h)).symm).op
          (M.val.map (homOfLE (show V.ι ''ᵁ (V.ι ⁻¹ᵁ W') ≤ V.ι ''ᵁ (V.ι ⁻¹ᵁ W) from
            Scheme.Hom.image_mono _ ((Opens.map V.ι.base).map (homOfLE hW)).le)).op
            (x : M.val.obj (op (V.ι ''ᵁ (V.ι ⁻¹ᵁ W))))) := rfl
  have hR : M.val.resLE hW (pushforwardRestrictSectionsEquiv M V h x)
      = M.val.map (homOfLE hW).op
          (M.val.map (eqToHom (image_preimage_ι_eq_self V h).symm).op
            (x : M.val.obj (op (V.ι ''ᵁ (V.ι ⁻¹ᵁ W))))) := rfl
  rw [hL, hR]
  exact PresheafOfModules.map_map_eq_map_map M.val _ _ _ _ _

/-- `AlgebraicGeometry.pushforwardRestrictSectionsEquiv_resLE` read through the inverse. -/
theorem pushforwardRestrictSectionsEquiv_symm_resLE {Y : Scheme.{u}} (M : Y.Modules)
    (V : Y.Opens) {W W' : Y.Opens} (h : W ≤ V) (hW : W' ≤ W) (y : M.val.obj (op W)) :
    (pushforwardRestrictSectionsEquiv M V (hW.trans h)).symm (M.val.resLE hW y)
      = ((Scheme.Modules.pushforward V.ι).obj (Scheme.Modules.restrict M V.ι)).val.resLE hW
          ((pushforwardRestrictSectionsEquiv M V h).symm y) := by
  rw [LinearEquiv.symm_apply_eq, pushforwardRestrictSectionsEquiv_resLE M V h hW,
    LinearEquiv.apply_symm_apply]

/-- An isomorphism of modules on the open subscheme `V`, read on the sections above an open `W`
of `Y`.  It is the evaluation at `W` of the pushforward of the isomorphism. -/
def chartSectionsEquivOfIso {Y : Scheme.{u}} {V : Y.Opens}
    {L L' : V.toScheme.Modules} (e : L ≅ L') (W : Y.Opens) :
    overlapChartSections V L W ≃ₗ[Y.ringCatSheaf.obj.obj (op W)] overlapChartSections V L' W :=
  ((Scheme.Modules.pushforward V.ι ⋙
    SheafOfModules.evaluation Y.ringCatSheaf (op W)).mapIso e).toLinearEquiv

/-- `AlgebraicGeometry.chartSectionsEquivOfIso` commutes with restriction to a smaller open,
being the component of a morphism of presheaves of modules. -/
theorem chartSectionsEquivOfIso_resLE {Y : Scheme.{u}} {V : Y.Opens}
    {L L' : V.toScheme.Modules} (e : L ≅ L') {W W' : Y.Opens} (hW : W' ≤ W)
    (x : overlapChartSections V L W) :
    chartSectionsEquivOfIso e W' (((Scheme.Modules.pushforward V.ι).obj L).val.resLE hW x)
      = ((Scheme.Modules.pushforward V.ι).obj L').val.resLE hW (chartSectionsEquivOfIso e W x) :=
  PresheafOfModules.app_resLE ((Scheme.Modules.pushforward V.ι).map e.hom).val hW x

/-- `AlgebraicGeometry.chartSectionsEquivOfIso_resLE` read through the inverse. -/
theorem chartSectionsEquivOfIso_symm_resLE {Y : Scheme.{u}} {V : Y.Opens}
    {L L' : V.toScheme.Modules} (e : L ≅ L') {W W' : Y.Opens} (hW : W' ≤ W)
    (y : overlapChartSections V L' W) :
    (chartSectionsEquivOfIso e W').symm (((Scheme.Modules.pushforward V.ι).obj L').val.resLE hW y)
      = ((Scheme.Modules.pushforward V.ι).obj L).val.resLE hW
          ((chartSectionsEquivOfIso e W).symm y) := by
  rw [LinearEquiv.symm_apply_eq, chartSectionsEquivOfIso_resLE, LinearEquiv.apply_symm_apply]

/-! ### The converse: the transition data carried by a glued module -/

/-- **The transition isomorphism carried by a single module restricting to the `L i`.**  Over an
open `W` inside both `V i` and `V j`, the sections of `L i` and of `L j` above `W` are both the
sections of `M` over `W`; comparing the two descriptions gives the isomorphism.

This is the first of the three transition hypotheses of
`AlgebraicGeometry.exists_module_of_overlapCompatible`, built out of its conclusion.  The other
two are `AlgebraicGeometry.transOfRestrictIso_resLE` and
`AlgebraicGeometry.transOfRestrictIso_trans`. -/
def transOfRestrictIso {Y : Scheme.{u}} {ι : Type u} {V : ι → Y.Opens}
    {L : ∀ i, (V i).toScheme.Modules} (M : Y.Modules)
    (e : ∀ i, Scheme.Modules.restrict M (V i).ι ≅ L i) (i j : ι) {W : Y.Opens}
    (hi : W ≤ V i) (hj : W ≤ V j) :
    overlapChartSections (V i) (L i) W ≃ₗ[Y.ringCatSheaf.obj.obj (op W)]
      overlapChartSections (V j) (L j) W :=
  (chartSectionsEquivOfIso (e i) W).symm.trans
    ((pushforwardRestrictSectionsEquiv M (V i) hi).trans
      ((pushforwardRestrictSectionsEquiv M (V j) hj).symm.trans
        (chartSectionsEquivOfIso (e j) W)))

/-- **The second transition hypothesis holds for `AlgebraicGeometry.transOfRestrictIso`.**  Each
of the four comparisons it is composed of commutes with restriction to a smaller open. -/
theorem transOfRestrictIso_resLE {Y : Scheme.{u}} {ι : Type u} {V : ι → Y.Opens}
    {L : ∀ i, (V i).toScheme.Modules} (M : Y.Modules)
    (e : ∀ i, Scheme.Modules.restrict M (V i).ι ≅ L i) (i j : ι) {W W' : Y.Opens}
    (hi : W ≤ V i) (hj : W ≤ V j) (hW : W' ≤ W)
    (s : overlapChartSections (V i) (L i) W) :
    transOfRestrictIso M e i j (hW.trans hi) (hW.trans hj)
        (((Scheme.Modules.pushforward (V i).ι).obj (L i)).val.resLE hW s)
      = ((Scheme.Modules.pushforward (V j).ι).obj (L j)).val.resLE hW
          (transOfRestrictIso M e i j hi hj s) := by
  simp only [transOfRestrictIso, LinearEquiv.trans_apply]
  rw [chartSectionsEquivOfIso_symm_resLE, pushforwardRestrictSectionsEquiv_resLE,
    pushforwardRestrictSectionsEquiv_symm_resLE, chartSectionsEquivOfIso_resLE]

/-- **The cocycle condition holds for `AlgebraicGeometry.transOfRestrictIso`.**  The two
comparisons attached to `j` cancel, because both are the single description of the sections of
`M` over `W` coming from the chart `V j`. -/
theorem transOfRestrictIso_trans {Y : Scheme.{u}} {ι : Type u} {V : ι → Y.Opens}
    {L : ∀ i, (V i).toScheme.Modules} (M : Y.Modules)
    (e : ∀ i, Scheme.Modules.restrict M (V i).ι ≅ L i) (i j k : ι) {W : Y.Opens}
    (hi : W ≤ V i) (hj : W ≤ V j) (hk : W ≤ V k)
    (s : overlapChartSections (V i) (L i) W) :
    transOfRestrictIso M e j k hj hk (transOfRestrictIso M e i j hi hj s)
      = transOfRestrictIso M e i k hi hk s := by
  simp only [transOfRestrictIso, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply]

/-! ### The same converse in the `restrict` spelling -/

/-- **Reading the restriction of a module to a smaller open through a chart.**  Let `M` be a
module on `Y`, let `L` be a module on the open subscheme `V` isomorphic to `M|_V`, and let
`W ≤ V`.  Then `M|_W` is isomorphic to the restriction of `L` along `W ⟶ V`.

This is the composite of `Scheme.Modules.restrictFunctorCongr` along `(W ⟶ V) ≫ V.ι = W.ι`,
`Scheme.Modules.restrictFunctorComp`, and the given isomorphism restricted to `W`. -/
def restrictOfLEIso {Y : Scheme.{u}} {V : Y.Opens} (M : Y.Modules) (L : V.toScheme.Modules)
    (e : Scheme.Modules.restrict M V.ι ≅ L) {W : Y.Opens} (h : W ≤ V) :
    Scheme.Modules.restrict M W.ι ≅ Scheme.Modules.restrict L (Y.homOfLE h) :=
  ((Scheme.Modules.restrictFunctorCongr (Y.homOfLE_ι h)).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp (Y.homOfLE h) V.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).mapIso e

/-- **A global module restricting to the `L i` makes them agree over every open contained in two
members of the cover.**  This is the content of `AlgebraicGeometry.transOfRestrictIso` in the
`restrict` spelling, where it reads as an isomorphism of sheaves of modules on the open
subscheme `W` rather than as a map of sections. -/
def restrictHomOfLEIso {Y : Scheme.{u}} {ι : Type u} {V : ι → Y.Opens}
    {L : ∀ i, (V i).toScheme.Modules} (M : Y.Modules)
    (e : ∀ i, Scheme.Modules.restrict M (V i).ι ≅ L i) (i j : ι) {W : Y.Opens}
    (hi : W ≤ V i) (hj : W ≤ V j) :
    Scheme.Modules.restrict (L i) (Y.homOfLE hi) ≅
      Scheme.Modules.restrict (L j) (Y.homOfLE hj) :=
  (restrictOfLEIso M (L i) (e i) hi).symm ≪≫ restrictOfLEIso M (L j) (e j) hj

/-- **The cocycle condition for `AlgebraicGeometry.restrictHomOfLEIso`.**  The three comparisons
attached to `i`, `j`, `k` over one open `W` compose, because each is obtained from the single
description of `M|_W`. -/
theorem restrictHomOfLEIso_trans {Y : Scheme.{u}} {ι : Type u} {V : ι → Y.Opens}
    {L : ∀ i, (V i).toScheme.Modules} (M : Y.Modules)
    (e : ∀ i, Scheme.Modules.restrict M (V i).ι ≅ L i) (i j k : ι) {W : Y.Opens}
    (hi : W ≤ V i) (hj : W ≤ V j) (hk : W ≤ V k) :
    restrictHomOfLEIso M e i j hi hj ≪≫ restrictHomOfLEIso M e j k hj hk =
      restrictHomOfLEIso M e i k hi hk := by
  simp only [restrictHomOfLEIso, Iso.trans_assoc, Iso.self_symm_id_assoc]

end AlgebraicGeometry

end
