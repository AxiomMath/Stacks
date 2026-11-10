module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending morphisms of schemes of finite presentation through an affine-transition limit

Let `D` be a cofiltered diagram of quasi-compact and quasi-separated schemes whose transition
morphisms are affine, and let `c` be a limit cone for it. Stacks 01ZM says that the category of
schemes of finite presentation over `c.pt` is the colimit over the index category of the
categories of schemes of finite presentation over the `D.obj i`. This file proves part (3) of
that statement: two morphisms over `D.obj i` whose base changes to `c.pt` agree already agree
over `D.obj j` for some `j ⟶ i`.

The proof applies Mathlib's
`AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` not to `D` itself but
to the diagram `j ↦ X ×_{D.obj i} D.obj j` of base changes of the source, indexed by the over
category `Over i`. The point is that this diagram is again a cofiltered diagram of quasi-compact
and quasi-separated schemes with affine transition morphisms, and that its limit is
`X ×_{D.obj i} c.pt`.

## Main definitions

* `AlgebraicGeometry.Scheme.baseChangeDiagram` is the diagram `j ↦ X ×_{D.obj i} D.obj j` on
  `Over i`.
* `AlgebraicGeometry.Scheme.baseChangeCone` is its cone with apex `X ×_{D.obj i} c.pt`.
* `AlgebraicGeometry.Scheme.baseChangeStructureMap` is the natural morphism from
  `baseChangeDiagram` to the constant diagram at `D.obj i`.
* `AlgebraicGeometry.Scheme.baseChangeComparison` compares an iterated base change with the
  corresponding direct one.

## Main results

* `AlgebraicGeometry.Scheme.eventually_eq_of_baseChange_eq` is part (3) of Stacks 01ZM.
* `AlgebraicGeometry.Scheme.eventually_eq_of_baseChange_eq_of_locallyOfFiniteType` is the sharper
  statement actually proved: it assumes of the source only quasi-compactness over `D.obj i` and
  of the target only local finite type.
* `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_essentiallySmall` and
  `AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_essentiallySmall` lift the two Mathlib
  factorization lemmas from small to essentially small index categories.

## Implementation notes

Mathlib's two factorization lemmas are stated for a diagram indexed by a category `I : Type u`
with `[Category.{u} I]`, where `u` is the universe of the schemes. The diagram of base changes is
indexed by `Over i`, whose universes are those of `I`, so the statements here are given for
`{I : Type v} [Category.{w} I] [EssentiallySmall.{u} I]` and transported along
`CategoryTheory.equivSmallModel`; `CategoryTheory.CostructuredArrow.essentiallySmall` then
supplies `EssentiallySmall.{u} (Over i)`. A limit in a smaller category of schemes need not stay
a limit after enlarging the universe, which is why smallness is a hypothesis rather than a
consequence.

`baseChangeDiagram` is defined as a composite of `CategoryTheory.Over.post`,
`CategoryTheory.Over.pullback` and `CategoryTheory.Over.forget`, so that
`CategoryTheory.Over.isLimitConePost` gives `isLimitBaseChangeCone` for free. None of its
components are reducible, so `rw` and `simp` cannot see that `(baseChangeDiagram D i X).obj j` is
`pullback (D.map j.hom) X.hom`; the four lemmas `baseChangeDiagram_map_fst`,
`baseChangeDiagram_map_snd`, `baseChangeCone_π_fst` and `baseChangeCone_π_snd` are the interface
through which the rest of the file works, each proved by `dsimp only` down to a `pullback.lift`
and then `CategoryTheory.Limits.pullback.lift_fst`. They also pin the definitions down: a cone
over a diagram of pullbacks is determined by the two projections of each of its legs.

Parts (1) and (2) of Stacks 01ZM are not proved here. Part (1) — that every scheme of finite
presentation over `c.pt` descends — needs the existence of limits of affine-transition systems
(Stacks 01YX) and the relative approximation result Stacks 0GS1. Part (2) needs
`baseChangeComparison` together with `exists_π_app_comp_eq_of_essentiallySmall`, both provided
here; what blocks it is that `Category.assoc` is not applicable, as a `rw` or a `simp` lemma, to
a term `(h ≫ (baseChangeCone D i X c).π.app j) ≫ pullback.fst _ _`, because that term is not
type-correct at `implicit` transparency.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/
@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.Scheme

/-- Mathlib's `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` for
a diagram indexed by an essentially small, but not necessarily small, cofiltered category: an
`S`-morphism from the limit of `D` to a scheme `X` locally of finite presentation over `S`
factors through some `D.obj i`. -/
theorem exists_π_app_comp_eq_of_essentiallySmall
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    {S X : Scheme.{u}} (t : D ⟶ (Functor.const I).obj S) (f : X ⟶ S)
    [LocallyOfFinitePresentation f]
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (a : c.pt ⟶ X) (ha : c.π ≫ t = (Functor.const I).map (a ≫ f)) :
    ∃ (i : I) (g : D.obj i ⟶ X), c.π.app i ≫ g = a ∧ g ≫ f = t.app i := by
  let e := equivSmallModel.{u} I
  let _ : IsCofiltered (SmallModel.{u} I) := IsCofiltered.of_equivalence e
  have {i j} (h : i ⟶ j) : IsAffineHom ((e.inverse ⋙ D).map h) := by dsimp; infer_instance
  have (i : SmallModel.{u} I) : CompactSpace ((e.inverse ⋙ D).obj i) := by dsimp; infer_instance
  have (i : SmallModel.{u} I) : QuasiSeparatedSpace ((e.inverse ⋙ D).obj i) := by
    dsimp; infer_instance
  obtain ⟨i, g, hg⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (e.inverse ⋙ D) (Functor.whiskerLeft e.inverse t) f (c.whisker e.inverse)
    ((Functor.Initial.isLimitWhiskerEquiv e.inverse c).symm hc) a
    (by ext i; exact congrArg (fun n => n.app (e.inverse.obj i)) ha)
  exact ⟨e.inverse.obj i, g, hg⟩

/-- Mathlib's `AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` for a
diagram indexed by an essentially small, but not necessarily small, cofiltered category: two
`S`-morphisms `D.obj i ⟶ X` into a scheme locally of finite type over `S` which agree after
composing with the limit projection already agree at some `j ⟶ i`. -/
theorem exists_hom_comp_eq_comp_of_essentiallySmall
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    {S X : Scheme.{u}} (t : D ⟶ (Functor.const I).obj S) (f : X ⟶ S)
    [LocallyOfFiniteType f]
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)]
    {i : I} (a b : D.obj i ⟶ X) (ha : t.app i = a ≫ f) (hb : t.app i = b ≫ f)
    (hab : c.π.app i ≫ a = c.π.app i ≫ b) :
    ∃ (j : I) (e : j ⟶ i), D.map e ≫ a = D.map e ≫ b := by
  let e := equivSmallModel.{u} I
  let _ : IsCofiltered (SmallModel.{u} I) := IsCofiltered.of_equivalence e
  have (j : SmallModel.{u} I) : CompactSpace ((e.inverse ⋙ D).obj j) := by dsimp; infer_instance
  have {j k} (h : j ⟶ k) : IsAffineHom ((e.inverse ⋙ D).map h) := by dsimp; infer_instance
  let q := e.unitIso.inv.app i
  obtain ⟨j, h, hh⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (e.inverse ⋙ D) (Functor.whiskerLeft e.inverse t) f (c.whisker e.inverse)
    ((Functor.Initial.isLimitWhiskerEquiv e.inverse c).symm hc)
    (D.map q ≫ a) (D.map q ≫ b)
    (by simpa [q, ha] using (t.naturality q).symm)
    (by simpa [q, hb] using (t.naturality q).symm)
    (by simpa using hab)
  exact ⟨e.inverse.obj j, e.inverse.map h ≫ q, by simpa using hh⟩

section BaseChange

variable {I : Type v} [Category.{w} I] (D : I ⥤ Scheme.{u}) (i : I) (X : Over (D.obj i))

/-- Given a diagram `D` of schemes, an index `i` and a scheme `X` over `D.obj i`, the diagram
`j ↦ X ×_{D.obj i} D.obj j` of base changes of `X`, indexed by the objects of `D` over `i`. -/
@[sga "3 VIB 10.0"]
def baseChangeDiagram : Over i ⥤ Scheme.{u} :=
  Over.post D ⋙ Over.pullback X.hom ⋙ Over.forget _

/-- The value of `AlgebraicGeometry.Scheme.baseChangeDiagram` at `j` is the base change of `X`
along the transition morphism `D.obj j.left ⟶ D.obj i`. -/
@[simp]
theorem baseChangeDiagram_obj (j : Over i) :
    (baseChangeDiagram D i X).obj j = pullback (D.map j.hom) X.hom :=
  rfl

/-- The transition morphisms of `AlgebraicGeometry.Scheme.baseChangeDiagram` are, on the
`D`-component, the transition morphisms of `D`. -/
@[reassoc (attr := simp)]
theorem baseChangeDiagram_map_fst {j k : Over i} (e : j ⟶ k) :
    (baseChangeDiagram D i X).map e ≫ pullback.fst (D.map k.hom) X.hom =
      pullback.fst (D.map j.hom) X.hom ≫ D.map e.left := by
  dsimp only [baseChangeDiagram, Functor.comp_map, Over.forget_map]
  exact pullback.lift_fst _ _ _

/-- The transition morphisms of `AlgebraicGeometry.Scheme.baseChangeDiagram` are the identity on
the `X`-component. -/
@[reassoc (attr := simp)]
theorem baseChangeDiagram_map_snd {j k : Over i} (e : j ⟶ k) :
    (baseChangeDiagram D i X).map e ≫ pullback.snd (D.map k.hom) X.hom =
      pullback.snd (D.map j.hom) X.hom := by
  dsimp only [baseChangeDiagram, Functor.comp_map, Over.forget_map]
  exact pullback.lift_snd _ _ _

/-- The transition morphisms of `AlgebraicGeometry.Scheme.baseChangeDiagram` are affine, being
base changes of the transition morphisms of `D`. -/
theorem isAffineHom_baseChangeDiagram_map
    [∀ {j k : I} (e : j ⟶ k), IsAffineHom (D.map e)] {j k : Over i} (e : j ⟶ k) :
    IsAffineHom ((baseChangeDiagram D i X).map e) := by
  have inst : IsAffineHom (D.map e.left) := inferInstance
  have sq : IsPullback ((baseChangeDiagram D i X).map e) (pullback.fst (D.map j.hom) X.hom)
      (pullback.fst (D.map k.hom) X.hom) (D.map e.left) := by
    refine IsPullback.of_right ?_ (baseChangeDiagram_map_fst D i X e)
      ((IsPullback.of_hasPullback (D.map k.hom) X.hom).flip)
    rw [baseChangeDiagram_map_snd, ← D.map_comp, Over.w]
    exact (IsPullback.of_hasPullback (D.map j.hom) X.hom).flip
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip inst

/-- The natural morphism from `AlgebraicGeometry.Scheme.baseChangeDiagram` to the constant
diagram at `D.obj i`, through which every base change of `X` is a scheme over `D.obj i`. -/
def baseChangeStructureMap :
    baseChangeDiagram D i X ⟶ (Functor.const _).obj (D.obj i) where
  app j := pullback.snd (D.map j.hom) X.hom ≫ X.hom
  naturality j k e := by
    dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
    rw [Category.comp_id]
    exact baseChangeDiagram_map_snd_assoc D i X e X.hom

/-- The components of `AlgebraicGeometry.Scheme.baseChangeStructureMap` are the structure
morphisms of the base changes of `X`; this pins the definition down. -/
@[simp]
theorem baseChangeStructureMap_app (j : Over i) :
    (baseChangeStructureMap D i X).app j = pullback.snd (D.map j.hom) X.hom ≫ X.hom :=
  rfl

variable (c : Cone D)

/-- The cone over `AlgebraicGeometry.Scheme.baseChangeDiagram` with apex `X ×_{D.obj i} c.pt`
obtained from a cone `c` over `D`. -/
def baseChangeCone : Cone (baseChangeDiagram D i X) :=
  (Over.pullback X.hom ⋙ Over.forget _).mapCone ((Over.conePost _ _).obj c)

/-- The apex of `AlgebraicGeometry.Scheme.baseChangeCone` is the base change of `X` along the
leg of `c` at `i`. -/
@[simp]
theorem baseChangeCone_pt : (baseChangeCone D i X c).pt = pullback (c.π.app i) X.hom :=
  rfl

/-- On the `D`-component, the legs of `AlgebraicGeometry.Scheme.baseChangeCone` are the legs
of `c`. -/
@[reassoc (attr := simp)]
theorem baseChangeCone_π_fst (j : Over i) :
    (baseChangeCone D i X c).π.app j ≫ pullback.fst (D.map j.hom) X.hom =
      pullback.fst (c.π.app i) X.hom ≫ c.π.app j.left := by
  dsimp only [baseChangeCone, Functor.mapCone, Cone.functoriality, Functor.comp_map,
    Over.forget_map]
  exact pullback.lift_fst _ _ _

/-- On the `X`-component, the legs of `AlgebraicGeometry.Scheme.baseChangeCone` are the
identity. -/
@[reassoc (attr := simp)]
theorem baseChangeCone_π_snd (j : Over i) :
    (baseChangeCone D i X c).π.app j ≫ pullback.snd (D.map j.hom) X.hom =
      pullback.snd (c.π.app i) X.hom := by
  dsimp only [baseChangeCone, Functor.mapCone, Cone.functoriality, Functor.comp_map,
    Over.forget_map]
  exact pullback.lift_snd _ _ _

/-- `AlgebraicGeometry.Scheme.baseChangeCone` is a limit cone whenever `c` is: base change
preserves limits, and `CategoryTheory.Over.forget i` is initial on a cofiltered category. -/
def isLimitBaseChangeCone [IsCofiltered I] (hc : IsLimit c) :
    IsLimit (baseChangeCone D i X c) :=
  haveI : IsConnected (Over i) := isConnected_of_isTerminal (Over i) Over.mkIdTerminal
  isLimitOfPreserves (Over.pullback X.hom ⋙ Over.forget _) (Over.isLimitConePost _ hc)

/-- The over category of an essentially small category is essentially small. -/
theorem essentiallySmall_over [EssentiallySmall.{u} I] : EssentiallySmall.{u} (Over i) :=
  CostructuredArrow.essentiallySmall (S := 𝟭 I) (T := i)

end BaseChange

section Comparison

variable {S S' T : Scheme.{u}} (p : S ⟶ T) (q : S' ⟶ S) (r : S' ⟶ T) (h : q ≫ p = r) (X : Over T)

/-- Base changing along `q` and then along `p` is base changing along `r = q ≫ p`. -/
def baseChangeComparison :
    (Over.pullback q).obj ((Over.pullback p).obj X) ≅ (Over.pullback r).obj X :=
  Over.isoMk (pullbackLeftPullbackSndIso X.hom p q ≪≫ pullback.congrHom rfl h) (by
    dsimp
    simp [pullback.congrHom_hom, pullbackLeftPullbackSndIso_hom_snd])

/-- `AlgebraicGeometry.Scheme.baseChangeComparison` is the identity on the `X`-component. Since
a morphism of schemes over `S'` into a base change of `X` is determined by its composition with
the projection to `X`, this pins the definition down. -/
@[reassoc]
theorem baseChangeComparison_hom_left_fst :
    (baseChangeComparison p q r h X).hom.left ≫ pullback.fst X.hom r =
      pullback.fst ((Over.pullback p).obj X).hom q ≫ pullback.fst X.hom p := by
  dsimp [baseChangeComparison]
  simp [pullback.congrHom_hom, pullbackLeftPullbackSndIso_hom_fst]

end Comparison

variable {I : Type v} [Category.{w} I]

/-- The sharp form of part (3) of Stacks 01ZM: of the source only quasi-compactness over
`D.obj i` is used, and of the target only local finite type. -/
theorem eventually_eq_of_baseChange_eq_of_locallyOfFiniteType
    [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)]
    (i : I) (X Y : Over (D.obj i))
    (hX : QuasiCompact X.hom) (hY : LocallyOfFiniteType Y.hom) (f g : X ⟶ Y)
    (hfg : (Over.pullback (c.π.app i)).map f = (Over.pullback (c.π.app i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (D.map e)).map f = (Over.pullback (D.map e)).map g := by
  let _ : LocallyOfFiniteType Y.hom := hY
  let _ : QuasiCompact X.hom := hX
  let _ : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let _ : EssentiallySmall.{u} (Over i) := essentiallySmall_over i
  let E := baseChangeDiagram D i X
  let d := baseChangeCone D i X c
  let t := baseChangeStructureMap D i X
  have {j k : Over i} (e : j ⟶ k) : IsAffineHom (E.map e) :=
    isAffineHom_baseChangeDiagram_map D i X e
  have hqc (j : Over i) : QuasiCompact (pullback.fst (D.map j.hom) X.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (D.map j.hom) X.hom).flip hX
  have (j : Over i) : CompactSpace (E.obj j) :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.fst (D.map j.hom) X.hom)
      (hqc j) inferInstance
  have heq : pullback.fst X.hom (c.π.app i) ≫ f.left =
      pullback.fst X.hom (c.π.app i) ≫ g.left := by
    simpa [pullback.lift_fst] using
      congrArg (fun k => k.left ≫ pullback.fst Y.hom (c.π.app i)) hfg
  have hw (k : X ⟶ Y) : t.app (Over.mk (𝟙 i)) =
      (pullback.snd (D.map (𝟙 i)) X.hom ≫ k.left) ≫ Y.hom := by
    rw [Category.assoc, Over.w]
    rfl
  obtain ⟨j, e, hj⟩ := exists_hom_comp_eq_comp_of_essentiallySmall E d
    (isLimitBaseChangeCone D i X c hc) t Y.hom
    (i := Over.mk (𝟙 i))
    (pullback.snd (D.map (𝟙 i)) X.hom ≫ f.left)
    (pullback.snd (D.map (𝟙 i)) X.hom ≫ g.left)
    (hw f) (hw g)
    (by
      have h := congrArg (fun k => (pullbackSymmetry (c.π.app i) X.hom).hom ≫ k) heq
      simp only [pullbackSymmetry_hom_comp_fst_assoc] at h
      refine (baseChangeCone_π_snd_assoc D i X c (Over.mk (𝟙 i)) f.left).trans
        (h.trans (baseChangeCone_π_snd_assoc D i X c (Over.mk (𝟙 i)) g.left).symm))
  refine ⟨j.left, j.hom, ?_⟩
  apply Over.OverMorphism.ext
  refine pullback.hom_ext (f := Y.hom) (g := D.map j.hom) ?_ ?_
  · have hj' : pullback.snd (D.map j.hom) X.hom ≫ f.left =
        pullback.snd (D.map j.hom) X.hom ≫ g.left := by
      have h := baseChangeDiagram_map_snd_assoc D i X e f.left
      have h' := baseChangeDiagram_map_snd_assoc D i X e g.left
      exact h.symm.trans (hj.trans h')
    simpa [pullback.lift_fst] using
      congrArg (fun k => (pullbackSymmetry X.hom (D.map j.hom)).hom ≫ k) hj'
  · simp

/-- **Stacks Project, Tag 01ZM, part (3).** Two morphisms between schemes of finite presentation
at one stage of a cofiltered inverse system of quasi-compact and quasi-separated schemes with
affine transition morphisms, which become equal after base change to the limit, are equal after
passing to a later stage. -/
@[stacks 01ZM "part (3)",
  sga "3 VIB 10.0" "(i) injectivity",
  sga "4 VII 5.2" "(a) injectivity",
  sga "4 VII 5.3" "faithfulness", ega "IV 8.13.1" "special case, uniqueness"]
theorem eventually_eq_of_baseChange_eq
    [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X Y : Over (D.obj i))
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom) (f g : X ⟶ Y)
    (hfg : (Over.pullback (c.π.app i)).map f = (Over.pullback (c.π.app i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (D.map e)).map f = (Over.pullback (D.map e)).map g := by
  let _ : LocallyOfFinitePresentation Y.hom := hY.1
  exact eventually_eq_of_baseChange_eq_of_locallyOfFiniteType D c hc i X Y hX.2.1 inferInstance
    f g hfg

end AlgebraicGeometry.Scheme

end

end
