module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.Cocycle
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorGenerator
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Descent

/-!
# Recognizing the glue of a unit cocycle

Let `(X, 𝒪_X)` be a ringed space, let `U : ι → Opens X` be a family of opens covering `X`, and
let `D` be a unit transition cocycle for `U`
(`Stacks.SheafOfModules.UnitTransitionCocycle`), glued into an invertible sheaf of modules
`D.glue`. This file proves the *recognition* statement for that construction: a sheaf of modules
`P` carrying a generator `p i` over each `U i` whose pairwise transition units are exactly the
units of `D` is isomorphic to `D.glue`.

Gluing produces a module from a cocycle; recognition is the converse reading, and it is what lets
a module given by *other* means be identified with a glue. In particular it is the step needed
in the norm construction of
[Stacks, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY): the norm of an invertible module
is defined there as the glue of the cocycle of normed transition units, so comparing the norm of
a tensor product with the tensor product of the norms means comparing a glue with a tensor
product, and nothing presents a tensor product as a glue. Recognition does: by
`Stacks.SheafOfModules.tmulGenerator` the elementary tensors of the chart generators are chart
generators of the tensor product, and by
`Stacks.SheafOfModules.generatorRatioUnit_tmulGenerator` their transition units are the pointwise
products.

## The construction

The comparison is built in the direction `P ⟶ D.glue`, which needs no gluing of morphisms. A
section of `D.glue` over `W` is a compatible family of local coordinates
`s i ∈ 𝒪_X(W ⊓ U i)`, so a section `t` of `P` over `W` determines one outright: take for `s i`
the coordinate `Stacks.SheafOfModules.generatorCoordOfLE` of `t|_{W ⊓ U i}` in the frame `p i`. The
compatibility condition is exactly `transition_mul_generatorCoordOfLE`, the statement that changing
the frame multiplies the coordinate by the transition unit, which is where the hypothesis on the
transition units of the `p i` is used and the only place. Additivity, semilinearity and
compatibility with restriction are the corresponding properties of `generatorCoordOfLE`, checked
coordinatewise.

That the comparison is an isomorphism is read off over an open `B` inside a single chart `U i`:
there the `i`-th coordinate carries all of the data
(`Stacks.SheafOfModules.UnitTransitionCocycle.chartLinearEquiv`), the composite with it is the
coordinate map in the frame `p i`, and that is a bijection because `p i` is a generator. The sheaf
condition then propagates bijectivity to every open, by
`Stacks.SheafOfModules.bijective_app_of_bijective_on_cover`.

## Main definitions

* `Stacks.SheafOfModules.chartCoord`: the coordinates of a local section of `P` in a family of
  chart frames.
* `Stacks.SheafOfModules.UnitTransitionCocycle.glueSection`: the section of the glued module whose
  chart coordinates are those of a given section of `P`.
* `Stacks.SheafOfModules.UnitTransitionCocycle.glueHom`: the comparison morphism `P ⟶ D.glue`.
* `Stacks.SheafOfModules.cocycleOfChartGenerators`: the cocycle of transition units of a family
  of chart generators.
* `Stacks.SheafOfModules.isoOfChartGenerators`: **two modules with chart generators on a common
  cover and the same transition units are isomorphic.** This is the form in which recognition is
  consumed, neither module being presented as a glue.

## Main results

* `Stacks.SheafOfModules.UnitTransitionCocycle.transition_mul_generatorCoordOfLE`: changing the
  chart frame multiplies the coordinate of a section by the transition unit.
* `Stacks.SheafOfModules.UnitTransitionCocycle.bijective_glueHom_app_of_le`: the comparison is
  bijective on the sections over an open inside a chart.
* `Stacks.SheafOfModules.UnitTransitionCocycle.glueIsoOfChartGenerators`: **a module carrying
  chart generators whose transition units are those of a unit cocycle is the glue of that
  cocycle.**
* `Stacks.SheafOfModules.glueCocycleIso`: a module carrying chart generators on a covering family
  is the glue of the cocycle of their own transition units.

## Implementation notes

**Which sheaf of rings.** The module `P` is stated over `structureSheafRing X`, which is
`@[instance_reducible]`, so that the scalar action of `Γ(X, V)` on `P(V)` is found by instance
search. `Stacks.SheafOfModules.UnitTransitionCocycle.glue` is declared over the equal but opaque
`structureSheaf X.sheaf`, and there instance search does *not* see through to `Γ(X, V)`; the
scalar action on `D.glue(V)` has to be written with the scalar in that spelling. The two are
`rfl`-equal, so `P ⟶ D.glue` elaborates and no bridge is needed, but a single equation whose two
sides scale a section of `P` and a section of `D.glue` by one scalar cannot be *stated*: no
spelling of the scalar type serves both. Semilinearity of `glueHom` is therefore discharged
inside the structure literal, where the elaborator supplies the well-typed goal, and the
reusable content is the coordinatewise
`Stacks.SheafOfModules.chartCoord_smul` instead.

Several steps are written entirely in term mode, with every argument supplied, because `rw` fails
on them with *"the target expression is not type-correct under the `implicit` transparency
level"* — the two readings of the section ring are definitionally but not reducibly equal, so
`kabstract` cannot see the pattern. No transparency option is set anywhere here.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} {P : _root_.SheafOfModules.{u} (structureSheafRing X)}

/-! ### The coordinate of a local section in a frame -/

/-- The coordinate of a section in a frame is characterized by the equation it satisfies. -/
theorem generatorCoordOfLE_unique {A : Opens X.carrier} (s : GeneratorSections X P A)
    {V : Opens X.carrier} (h : V ≤ A) (a : P.val.obj (op V)) (c : X.presheaf.obj (op V))
    (hc : c • P.val.map (homOfLE h).op s.val = a) :
    c = generatorCoordOfLE s h a :=
  (generatorEquiv s h).eq_symm_apply.mpr hc

/-- Reading the coordinate in a frame is a bijection from the sections to the functions. -/
theorem bijective_generatorCoordOfLE {A : Opens X.carrier} (s : GeneratorSections X P A)
    {V : Opens X.carrier} (h : V ≤ A) :
    Function.Bijective (generatorCoordOfLE s h) :=
  (generatorEquiv s h).symm.bijective

/-! ### The coordinates of a section in a family of chart frames -/

section Chart

variable {ι : Type u} {U : ι → Opens X.carrier}

/-- The coordinates of a section of `P` over `W` in a family of chart frames: the `i`-th
coordinate is the coordinate, in the frame `p i`, of the restriction of the section to
`W ⊓ U i`. -/
noncomputable def chartCoord (p : ∀ i, GeneratorSections X P (U i))
    {W : Opens X.carrier} (t : P.val.obj (op W)) (i : ι) :
    X.presheaf.obj (op (W ⊓ U i)) :=
  generatorCoordOfLE (p i) (inf_le_right : W ⊓ U i ≤ U i)
    (P.val.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op t)

/-- Restricting a section in two steps is restricting it directly. -/
private theorem map_map_homOfLE {A B C : Opens X.carrier} (h : B ≤ A) (k : C ≤ B)
    (t : P.val.obj (op A)) (hC : C ≤ A) :
    P.val.map (homOfLE k).op (P.val.map (homOfLE h).op t) = P.val.map (homOfLE hC).op t :=
  (PresheafOfModules.map_comp_apply P.val (homOfLE h).op (homOfLE k).op t).symm.trans
    (PresheafOfModules.congr_map_apply P.val (Subsingleton.elim _ _) t)

/-- A chart coordinate restricted to a smaller open is the coordinate of the restricted
section. -/
theorem map_chartCoord (p : ∀ i, GeneratorSections X P (U i))
    {W : Opens X.carrier} (t : P.val.obj (op W)) (i : ι)
    {Z : Opens X.carrier} (h : Z ≤ W ⊓ U i) :
    X.presheaf.map (homOfLE h).op (chartCoord p t i) =
      generatorCoordOfLE (p i) (h.trans (inf_le_right : W ⊓ U i ≤ U i))
        (P.val.map (homOfLE (h.trans (inf_le_left : W ⊓ U i ≤ W))).op t) := by
  refine (generatorCoordOfLE_restrict (p i) (inf_le_right : W ⊓ U i ≤ U i) h
    (P.val.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op t)).symm.trans ?_
  refine congrArg (generatorCoordOfLE (p i) (h.trans (inf_le_right : W ⊓ U i ≤ U i))) ?_
  exact map_map_homOfLE _ _ t _

/-- Over an open inside the `i`-th chart the `i`-th chart coordinate is the coordinate in the
frame `p i` itself. -/
theorem chartCoord_self (p : ∀ i, GeneratorSections X P (U i)) (i : ι)
    {W : Opens X.carrier} (hW : W ≤ U i) (t : P.val.obj (op W)) :
    X.presheaf.map (homOfLE (le_inf le_rfl hW)).op (chartCoord p t i) =
      generatorCoordOfLE (p i) hW t := by
  refine (map_chartCoord p t i (le_inf le_rfl hW)).trans ?_
  refine congrArg (generatorCoordOfLE (p i) hW) ?_
  exact (PresheafOfModules.congr_map_apply P.val
      (Subsingleton.elim _ (𝟙 (op W))) t).trans (PresheafOfModules.map_id_apply P.val _ t)

/-- The chart coordinates of a sum are the sums of the chart coordinates. -/
theorem chartCoord_add (p : ∀ i, GeneratorSections X P (U i)) {W : Opens X.carrier}
    (t t' : P.val.obj (op W)) (i : ι) :
    chartCoord p (t + t') i = chartCoord p t i + chartCoord p t' i :=
  (congrArg (generatorCoordOfLE (p i) (inf_le_right : W ⊓ U i ≤ U i))
      (map_add (P.val.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op).hom t t')).trans
    (generatorCoordOfLE_add (p i) (inf_le_right : W ⊓ U i ≤ U i) _ _)

/-- The chart coordinates of `r • t` are those of `t` multiplied by the restrictions of `r`. -/
theorem chartCoord_smul (p : ∀ i, GeneratorSections X P (U i)) {W : Opens X.carrier}
    (r : X.presheaf.obj (op W)) (t : P.val.obj (op W)) (i : ι) :
    chartCoord p (r • t) i =
      X.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r * chartCoord p t i :=
  (congrArg (generatorCoordOfLE (p i) (inf_le_right : W ⊓ U i ≤ U i))
      (PresheafOfModules.map_smul P.val (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r t)).trans
    (generatorCoordOfLE_smul_coeff (p i) (inf_le_right : W ⊓ U i ≤ U i) _ _)

/-- The chart coordinates of a restricted section are the restricted chart coordinates. -/
theorem chartCoord_restrict (p : ∀ i, GeneratorSections X P (U i))
    {W W' : Opens X.carrier} (h : W' ≤ W) (t : P.val.obj (op W)) (i : ι) :
    chartCoord p (W := W') (P.val.map (homOfLE h).op t) i =
      X.presheaf.map (homOfLE (inf_le_inf_right (U i) h)).op (chartCoord p t i) := by
  refine Eq.trans ?_ (map_chartCoord p t i (inf_le_inf_right (U i) h)).symm
  refine congrArg (generatorCoordOfLE (p i) (inf_le_right : W' ⊓ U i ≤ U i)) ?_
  exact map_map_homOfLE _ _ t _

end Chart

/-! ### Recognizing the glue -/

namespace UnitTransitionCocycle

variable {ι : Type u} {U : ι → Opens X.carrier} (D : UnitTransitionCocycle X U)
  (p : ∀ i, GeneratorSections X P (U i))
  (hp : ∀ (i j : ι) (A : Opens X.carrier) (hi : A ≤ U i) (hj : A ≤ U j),
    generatorRatioUnit P A (generatorRestrict P hj (p j)) (generatorRestrict P hi (p i)) =
      D.transition i j A hi hj)

include hp in
/-- The `i`-th chart generator is the `j`-th scaled by the transition unit from `i` to `j`. -/
theorem generator_eq_transition_smul (i j : ι) {Z : Opens X.carrier}
    (hi : Z ≤ U i) (hj : Z ≤ U j) :
    (generatorRestrict P hi (p i)).val =
      (D.transition i j Z hi hj).val • (generatorRestrict P hj (p j)).val := by
  have hu : generatorRatio P Z (generatorRestrict P hj (p j)) (generatorRestrict P hi (p i)) =
      (D.transition i j Z hi hj).val :=
    (generatorRatioUnit_val P Z (generatorRestrict P hj (p j))
      (generatorRestrict P hi (p i))).symm.trans (congrArg Units.val (hp i j Z hi hj))
  exact (generatorRatio_spec P Z (generatorRestrict P hj (p j))
    (generatorRestrict P hi (p i))).trans
    (congrArg (fun z => z • (generatorRestrict P hj (p j)).val) hu)

include hp in
/-- **Changing the chart frame multiplies the coordinate by the transition unit.** This is the
cocycle condition for the chart coordinates of a section, and the only place the hypothesis on
the transition units of the chart generators is used. -/
theorem transition_mul_generatorCoordOfLE (i j : ι) {Z : Opens X.carrier}
    (hi : Z ≤ U i) (hj : Z ≤ U j) (t : P.val.obj (op Z)) :
    (D.transition i j Z hi hj).val * generatorCoordOfLE (p i) hi t =
      generatorCoordOfLE (p j) hj t := by
  refine generatorCoordOfLE_unique (p j) hj t _ ?_
  refine Eq.trans ?_ (generatorCoordOfLE_smul (p i) hi t)
  refine Eq.trans ?_ (congrArg (fun z : P.val.obj (op Z) => generatorCoordOfLE (p i) hi t • z)
    (generator_eq_transition_smul D p hp i j hi hj).symm)
  refine Eq.trans (congrArg (fun r : X.presheaf.obj (op Z) =>
      r • (generatorRestrict P hj (p j)).val)
    (mul_comm (D.transition i j Z hi hj).val (generatorCoordOfLE (p i) hi t))) ?_
  exact mul_smul (generatorCoordOfLE (p i) hi t) (D.transition i j Z hi hj).val
    (generatorRestrict P hj (p j)).val

include hp in
/-- The section of the glued module whose chart coordinates are those of `t`. -/
noncomputable def glueSection {W : Opens X.carrier} (t : P.val.obj (op W)) :
    D.glue.val.obj (op W) := by
  refine ⟨chartCoord p t, fun i j => ?_⟩
  exact ((congrArg (fun z : X.presheaf.obj (op (W ⊓ U i ⊓ (W ⊓ U j))) =>
        (D.transition i j (W ⊓ U i ⊓ (W ⊓ U j)) (inf_le_left.trans inf_le_right)
          (inf_le_right.trans inf_le_right)).val * z)
      (map_chartCoord p t i (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i))).trans
    (transition_mul_generatorCoordOfLE D p hp i j (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_right) _)).trans
    (map_chartCoord p t j (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j)).symm

include hp in
/-- The coordinates of `glueSection D p hp t` are the chart coordinates of `t`. -/
theorem glueSection_val {W : Opens X.carrier} (t : P.val.obj (op W)) (i : ι) :
    (glueSection D p hp t).val i = chartCoord p t i := rfl

include hp in
/-- `glueSection` is additive. -/
theorem glueSection_add {W : Opens X.carrier} (t t' : P.val.obj (op W)) :
    glueSection D p hp (t + t') = glueSection D p hp t + glueSection D p hp t' :=
  Subtype.ext (funext fun i => chartCoord_add p t t' i)

include hp in
/-- `glueSection` commutes with restriction. -/
theorem glueSection_restrict {W W' : Opens X.carrier} (h : W' ≤ W) (t : P.val.obj (op W)) :
    glueSection D p hp (W := W') (P.val.map (homOfLE h).op t) =
      D.glue.val.map (homOfLE h).op (glueSection D p hp t) :=
  Subtype.ext (funext fun i =>
    (chartCoord_restrict p h t i).trans (D.sectionsMap_val h (glueSection D p hp t) i).symm)

include hp in
/-- **The comparison morphism from `P` to the glue of the cocycle**, reading a section of `P` as
its family of chart coordinates. -/
noncomputable def glueHom : P ⟶ D.glue :=
  ⟨{ app A := ModuleCat.ofHom
        { toFun := glueSection D p hp (W := A.unop)
          map_add' := glueSection_add D p hp
          map_smul' := fun r t => Subtype.ext (funext fun i => chartCoord_smul p r t i) }
     naturality := by
       intro A B f
       apply ModuleCat.hom_ext
       refine LinearMap.ext fun t => ?_
       change glueSection D p hp (W := B.unop) (P.val.map f t) =
         D.glue.val.map f (glueSection D p hp t)
       rw [PresheafOfModules.congr_map_apply P.val
           (Subsingleton.elim f (homOfLE f.unop.le).op) t,
         PresheafOfModules.congr_map_apply D.glue.val
           (Subsingleton.elim f (homOfLE f.unop.le).op) (glueSection D p hp t)]
       exact glueSection_restrict D p hp f.unop.le t }⟩

include hp in
/-- On sections, the comparison morphism is `glueSection`. -/
theorem glueHom_app {W : Opens X.carrier} (t : P.val.obj (op W)) :
    (glueHom D p hp).val.app (op W) t = glueSection D p hp t := rfl

include hp in
/-- Over an open inside the `i`-th chart the comparison reads off the coordinate in the `i`-th
chart frame. -/
theorem chartLinearEquiv_glueSection (i : ι) {B : Opens X.carrier} (hB : B ≤ U i)
    (t : P.val.obj (op B)) :
    D.chartLinearEquiv i hB (glueSection D p hp t) = generatorCoordOfLE (p i) hB t :=
  chartCoord_self p i hB t

include hp in
/-- The comparison is bijective on the sections over an open inside a chart: there it is the
chart trivialization followed by reading the coordinate in that chart's frame. -/
theorem bijective_glueHom_app_of_le (i : ι) {B : Opens X.carrier} (hB : B ≤ U i) :
    Function.Bijective ((glueHom D p hp).val.app (op B)).hom := by
  have hb : Function.Bijective
      (⇑(D.chartLinearEquiv i hB).symm ∘ generatorCoordOfLE (p i) hB) :=
    (D.chartLinearEquiv i hB).symm.bijective.comp (bijective_generatorCoordOfLE (p i) hB)
  have h : ⇑(D.chartLinearEquiv i hB).symm ∘ generatorCoordOfLE (p i) hB =
      ⇑((glueHom D p hp).val.app (op B)).hom := by
    funext t
    exact (congrArg (D.chartLinearEquiv i hB).symm
        (chartLinearEquiv_glueSection D p hp i hB t)).symm.trans
      ((D.chartLinearEquiv i hB).symm_apply_apply (glueSection D p hp t))
  exact h ▸ hb

include hp in
/-- The comparison is an isomorphism, by the sheaf condition. -/
theorem isIso_glueHom (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) : IsIso (glueHom D p hp) := by
  refine isIso_of_isIso_val_app _ fun A => ?_
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
  refine bijective_app_of_bijective_on_cover (glueHom D p hp) U
    (TopologicalSpace.IsOpenCover.mk (top_le_iff.1 hU)) ?_ A.unop
  intro i V hV
  exact bijective_glueHom_app_of_le D p hp i hV

include hp in
/-- **A module carrying a generator over each member of a covering family, whose pairwise
transition units are those of a unit transition cocycle, is the glue of that cocycle.** -/
noncomputable def glueIsoOfChartGenerators (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) :
    D.glue ≅ P :=
  haveI := isIso_glueHom D p hp hU
  (asIso (glueHom D p hp)).symm

end UnitTransitionCocycle

/-! ### Two modules with the same chart transition units -/

section Compare

variable {ι : Type u} {U : ι → Opens X.carrier}

/-- The cocycle of transition units of a family of chart generators. -/
noncomputable def cocycleOfChartGenerators (p : ∀ i, GeneratorSections X P (U i)) :
    UnitTransitionCocycle X U where
  transition i j V hi hj :=
    generatorRatioUnit P V (generatorRestrict P hj (p j)) (generatorRestrict P hi (p i))
  restrict {i j _V W} hi hj h :=
    ((congrArg₂ (generatorRatioUnit P W)
        (generatorRestrict_trans P hj h (p j)).symm
        (generatorRestrict_trans P hi h (p i)).symm).trans
      (generatorRatioUnit_restrict P h (generatorRestrict P hj (p j))
        (generatorRestrict P hi (p i)))).symm
  symm i j V hi hj :=
    generatorRatioUnit_symm P V (generatorRestrict P hj (p j)) (generatorRestrict P hi (p i))
  cocycle i j k V hi hj hk :=
    (mul_comm _ _).trans (generatorRatioUnit_comp P V (generatorRestrict P hk (p k))
      (generatorRestrict P hj (p j)) (generatorRestrict P hi (p i)))

/-- The transition units of `cocycleOfChartGenerators p` are the ratios of the restricted
generators. -/
@[simp]
theorem cocycleOfChartGenerators_transition (p : ∀ i, GeneratorSections X P (U i)) (i j : ι)
    (V : Opens X.carrier) (hi : V ≤ U i) (hj : V ≤ U j) :
    (cocycleOfChartGenerators p).transition i j V hi hj =
      generatorRatioUnit P V (generatorRestrict P hj (p j)) (generatorRestrict P hi (p i)) :=
  rfl

/-- A module carrying a generator over each member of a covering family is the glue of the
cocycle of their transition units. -/
noncomputable def glueCocycleIso (p : ∀ i, GeneratorSections X P (U i))
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) :
    (cocycleOfChartGenerators p).glue ≅ P :=
  UnitTransitionCocycle.glueIsoOfChartGenerators (cocycleOfChartGenerators p) p
    (fun _ _ _ _ _ => rfl) hU

/-- **Two modules carrying generators over a common covering family, with the same pairwise
transition units, are isomorphic.** This is the form in which recognition is consumed: neither
module need be presented as a glue. -/
noncomputable def isoOfChartGenerators
    (P Q : _root_.SheafOfModules.{u} (structureSheafRing X))
    (p : ∀ i, GeneratorSections X P (U i)) (q : ∀ i, GeneratorSections X Q (U i))
    (hpq : ∀ (i j : ι) (A : Opens X.carrier) (hi : A ≤ U i) (hj : A ≤ U j),
      generatorRatioUnit Q A (generatorRestrict Q hj (q j)) (generatorRestrict Q hi (q i)) =
        generatorRatioUnit P A (generatorRestrict P hj (p j)) (generatorRestrict P hi (p i)))
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) :
    P ≅ Q :=
  (glueCocycleIso p hU).symm.trans
    (UnitTransitionCocycle.glueIsoOfChartGenerators (cocycleOfChartGenerators p) q hpq hU)

end Compare

end Stacks.SheafOfModules

end
