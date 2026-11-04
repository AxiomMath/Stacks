module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectDescentBridgeCocycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectSquareStep

/-!
# The bridge between the hom-level comparison of Stacks 09RI and the square step of Stacks 09RJ

The elementary-distinguished-square step of the essential surjectivity half of Stacks 09RJ is
`AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_edsPreimage` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectSquareStep.lean`.  Its hypothesis `hc`
is an equation between morphisms of `D(𝒪_{P'})`, `P'` the intersection of the base change of the
square to the limit, written in the derived pullbacks of the cube of Stacks 08GN.

The comparison isomorphism `c` that the source feeds to that step is produced by full
faithfulness, Stacks 09RI, at the intersection of the square: it is an isomorphism
`c : Lt_P^*A₀ ≅ Lt_P^*Bo₀` *at a stage*, `t_P` the map of intersections induced by the transition
morphism, whose image under the hom-level map to the limit is prescribed.  That map to the limit
is `AlgebraicGeometry.Space.DescentSituation.homProjection` — equivalently
`CategoryTheory.PullbackData.LimitSystem.projHom`, equivalently
`AlgebraicGeometry.Space.DerivedPullbackComposition.factorHom` — for the composition comparison
of the factorisation `r_P ≫ t_P = s_P` of the maps of intersections.

**This file identifies the two.**  Given the geometry of the step and the objects at the chosen
stage, it builds the two isomorphisms `α` and `β` with a common target that Stacks 09RI is to be
applied to, the transported comparison `c'` at the stage of the step, and proves that the
equation Stacks 09RI delivers for `α` and `β` *is* the hypothesis `hc` of the step.

## The geometry

Three morphisms to the ambient space of the square, `p_b : W_b ⟶ W₀`, `p : W ⟶ W₀` and
`p' : W' ⟶ W₀`, with `q : W ⟶ W_b` and `q' : W' ⟶ W` over `W₀` and `s : W' ⟶ W_b` with
`s = q' ≫ q`.  In Situation 09RH, `W_b` is the base change of `W₀` to the chosen stage, `W` its
base change to a later stage, `W' = W₀ ×_{X₀} X` its base change to the limit, and `q`, `q'`,
`s` are the transition morphisms and the projections.  Nothing below uses more than the three
factorisations.

## Main definitions

* `AlgebraicGeometry.Space.edsBridgeComparison`: the comparison isomorphism `c'` over the
  intersection of the square over `W`, transported from the comparison `c` over the intersection
  of the square over `W_b` by the two square isomorphisms of the cube.
* `AlgebraicGeometry.Space.edsBridgeLimitObj`: the object `E|_{P'}` of `D(𝒪_{P'})` that `α` and
  `β` land in.
* `AlgebraicGeometry.Space.edsBridgeInterComp`: the composition comparison of the factorisation
  `r_P ≫ t_P = s_P` of the maps of intersections, the comparison the hom-level map of
  Stacks 09RI conjugates by.
* `AlgebraicGeometry.Space.edsBridgeFst` and `…edsBridgeSnd`: the two isomorphisms `α` and `β`
  with common target `E|_{P'}` to which Stacks 09RI is applied.
* `AlgebraicGeometry.Space.edsBridgeOpenSquare`, `…edsBridgeEtaleSquare`,
  `…edsBridgeOpenSquare'`, `…edsBridgeEtaleSquare'` and `…edsBridgeCartesianSquare`: the five
  square isomorphisms of the cube of Stacks 08GN that `α`, `β` and `hc` are assembled from.

## Main results

* `AlgebraicGeometry.Space.hc_edsBridgeComparison_of_factorHom`: **the bridge.**  If the
  hom-level map to the limit of Stacks 09RI sends `c` to `α ∘ β⁻¹`, then the transported
  comparison satisfies the hypothesis `hc` of the square step.
* `AlgebraicGeometry.Space.edsBridge_conj_eq_of_factorHom`: the same with the left side written
  as the derived pullback of `c` conjugated by the two square isomorphisms over `q`, which is
  the form the algebra produces it in.
* `AlgebraicGeometry.Space.map_edsBridgeComparison_hom`: the derived pullback of the transported
  comparison, written out.
* `AlgebraicGeometry.Space.edsBridgeCore` and `…edsBridgeMapConj`: the algebra of the bridge, for
  free isomorphisms of a free category.

## The hypotheses carried, and why each is an input rather than part of the conclusion

*`A_b`, `Bo_b`, `hA`, `hBo`, `αU`, `αV`: the inductive hypotheses at the two members of the
square.*  Unchanged from
`AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_edsPreimage`; see "The
hypotheses carried" in the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectSquareStep.lean`.  The two objects are
taken at the base stage `W_b` and the objects at the stage `W` of the step are their derived
pullbacks, which is what the source's "after increasing `i` we may assume `i = j`" produces: the
inductive hypotheses are found at two stages, advanced to a common one, and the step is then run
at a stage beyond it.

*`c` and the equation `hfac`: the output of Stacks 09RI.*  `c` is an isomorphism at the stage
`W` between the derived pullbacks of the two objects on the intersection over `W_b`, and `hfac`
says that the hom-level map to the limit sends it to `α ∘ β⁻¹`.  That pair is exactly what
`AlgebraicGeometry.Space.DescentSituation.exists_stageIso_of_isPerfect` produces, and producing
it is a statement about the inverse system, not part of the square step.  It is an argument
here, as `c` and `hc` are arguments of the step itself.

*`s` and `hs`: the composite projection.*  The morphism `s : W' ⟶ W_b` is taken as an argument
together with `hs : s = q' ≫ q` rather than as the composite, because in Situation 09RH it is a
projection of the system and `q' ≫ q` is a composite of a projection with a transition
morphism; the two are equal by the composition law of the system, not by `rfl`.  The same
convention is used throughout
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectDescentBridgeCocycle.lean`.

No `Prop` binder stands in for missing mathematics, and in particular the identification being
built is nowhere assumed.

## What is not here

*The production of `c` and of `hfac`.*  Stacks 09RI at the intersection is not proved or assumed
here; the equation `hfac` is an argument.

*The induction and the affine base case.*  Running Stacks 08GP needs, besides this bridge and the
square step, the colimit statement of Stacks 09RI for the intersection system and the affine case
of the induction; neither is in this library and neither is assumed below.

*The composition with the square step.*  The conclusion of
`AlgebraicGeometry.Space.hc_edsBridgeComparison_of_factorHom` is the hypothesis `hc` of
`AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_edsPreimage` with the five
square isomorphisms written as the isomorphisms
`AlgebraicGeometry.Space.edsBridgeOpenSquare'`, `…edsBridgeCartesianSquare` and
`…edsBridgeEtaleSquare'` at the objects, where that step writes the components of those
isomorphisms: `(e.app M).hom` against `e.hom.app M`, which is `CategoryTheory.Iso.app_hom`.  The
two are the same morphism and the elaborator identifies them, but on these objects — derived
categories of `𝒪`-modules on the small étale site, whose `CategoryTheory.Category` instance is
reached through the derived-category model — the *kernel* does not finish the check of the
resulting term inside one declaration's heartbeat budget, and the identity resists being split
into cheaper pieces because the cost is in the repeated instance arguments of the five
compositions rather than in any one of the five factors.  So the composite statement is not
below, and feeding the bridge to the step is one `CategoryTheory.Iso.app_hom` rewrite away.

## Implementation notes

Every isomorphism below is a composite of square isomorphisms and composition comparisons of the
one pseudofunctoriality datum `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`, the
datum the hypothesis `hc` of the square step is written in.  The proof of the bridge uses **no
coherence** of that datum: it cancels isomorphisms and uses functoriality of the derived
pullbacks, nothing more.  In particular no cube identity
(`AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_cube`) is needed, and the
argument is reversible — `AlgebraicGeometry.Space.edsBridgeCore` cancels isomorphisms on both
sides — though only the direction the square step consumes is stated.

The hypothesis of the bridge is the hom-level map of Stacks 09RI **written out** as the derived
pullback along `r_P` conjugated by
`AlgebraicGeometry.Space.edsBridgeInterComp`, rather than as
`AlgebraicGeometry.Space.DerivedPullbackComposition.factorHom` of the factorisation
`r_P ≫ t_P = s_P`.  The two are the same by `rfl` —
`AlgebraicGeometry.Space.DescentSituation.homProjection` is the conjugated form on the nose and
`…factorHom` is `CategoryTheory.Iso.homCongr` of the same two components — and the conjugated
form is the one that composes with
`AlgebraicGeometry.Space.DescentSituation.homProjection` without any unfolding; asking the
elaborator to see through `CategoryTheory.Iso.homCongr` at these objects instead exhausts the
heartbeat budget.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Lemma 75.10.8 (Tag 08HB)](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Lemma 75.9.1 (Tag 08GN)](https://stacks.math.columbia.edu/tag/08GN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

/-! ### Conjugates of free isomorphisms

The four declarations of this section are about free isomorphisms of a free category.  They are
stated and named rather than inlined because the isomorphisms the bridge applies them to are
large — a composite of comparisons of total left derived functors — and an application of a
named identity costs a head unification, while the same step taken by `rw` or `simp` on the terms
themselves sends the elaborator into the unfolding of those derived functors. -/

/-- A morphism conjugated by two isomorphisms, as an isomorphism. -/
def edsBridgeConj {C : Type*} [Category C] {X Y Z T : C} (a : X ≅ Y) (e : X ≅ Z) (b : Z ≅ T) :
    Y ≅ T :=
  a.symm ≪≫ e ≪≫ b

/-- A fourfold conjugate: the shape of the first isomorphism the bridge feeds to Stacks 09RI. -/
def edsBridgeConj₄ {C : Type*} [Category C] {X₁ X₂ Z₁ A₁ T : C} (iA : X₁ ≅ X₂) (mA : X₁ ≅ Z₁)
    (k₁ : Z₁ ≅ A₁) (k₂ : A₁ ≅ T) : X₂ ≅ T :=
  iA.symm ≪≫ mA ≪≫ k₁ ≪≫ k₂

/-- A fivefold conjugate: the shape of the second isomorphism the bridge feeds to
Stacks 09RI. -/
def edsBridgeConj₅ {C : Type*} [Category C] {X₁ X₂ Z₁ A₁ A₂ T : C} (iA : X₁ ≅ X₂)
    (mA : X₁ ≅ Z₁) (k₁ : Z₁ ≅ A₁) (k₂ : A₁ ≅ A₂) (k₃ : A₂ ≅ T) : X₂ ≅ T :=
  iA.symm ≪≫ mA ≪≫ k₁ ≪≫ k₂ ≪≫ k₃

/-- The image of a conjugate under a functor. -/
theorem edsBridgeMapConj {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z T : C} (a : X ≅ Y) (e : X ≅ Z) (b : Z ≅ T) :
    F.map (edsBridgeConj a e b).hom =
      (F.mapIso a).inv ≫ F.map e.hom ≫ (F.mapIso b).hom := by
  simp [edsBridgeConj]

/-- **The algebraic content of the bridge.**  A morphism whose conjugate by one pair of
isomorphisms is a prescribed composite has a prescribed conjugate by any other pair.  Every
variable is free: no coherence of the pseudofunctoriality datum and no property of the derived
pullbacks enters the bridge, only cancellation of isomorphisms and functoriality. -/
theorem edsBridgeCore {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ A₁ A₂ A₃ T : C}
    (iA : X₁ ≅ X₂) (iB : Y₁ ≅ Y₂) (mA : X₁ ≅ Z₁) (mB : Y₁ ≅ Z₂)
    (k₁ : Z₁ ≅ A₁) (k₂ : A₁ ≅ T) (k₃ : Z₂ ≅ A₂) (k₄ : A₂ ≅ A₃) (k₅ : A₃ ≅ T)
    (g : X₁ ⟶ Y₁)
    (h : iA.inv ≫ g ≫ iB.hom =
      (edsBridgeConj₄ iA mA k₁ k₂).hom ≫ (edsBridgeConj₅ iB mB k₃ k₄ k₅).inv) :
    mA.inv ≫ g ≫ mB.hom = k₁.hom ≫ k₂.hom ≫ k₅.inv ≫ k₄.inv ≫ k₃.inv := by
  simp only [edsBridgeConj₄, edsBridgeConj₅, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Category.assoc] at h
  have key := congrArg (fun t ↦ mA.inv ≫ iA.hom ≫ t ≫ iB.inv ≫ mB.hom) h
  simpa using key

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W₀ : AlgebraicSpaces B S hS} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : Subfunctor W₀.1} {f₀ : V₀ ⟶ W₀.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W₀.2 U₀ f₀)
  {Wb W W' : AlgebraicSpaces B S hS} (pb : Wb ⟶ W₀) (p : W ⟶ W₀) (p' : W' ⟶ W₀)
  (q : W ⟶ Wb) (q' : W' ⟶ W) (hq : q ≫ pb = p) (hq' : q' ≫ p = p')
  (s : W' ⟶ Wb) (hs : s = q' ≫ q) (hsp : s ≫ pb = p')
  (Ab : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsOpen B S hS (edsPreimage hsq pb)))))
  (Bb : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsEtale B S hS (edsPreimage hsq pb)))))
  (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W')))

/-! ### The objects of the step at the stage `W` -/

/-- The object on the open subspace of the square over `W` that the step is run with: the derived
pullback of the object at the base stage along the map of open subspaces induced by `q`. -/
abbrev edsBridgeOpenObj : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsOpen B S hS (edsPreimage hsq p)))) :=
  (smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq pb p q hq)).obj Ab

/-- The object on the étale algebraic space of the square over `W` that the step is run with. -/
abbrev edsBridgeEtaleObj : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsEtale B S hS (edsPreimage hsq p)))) :=
  (smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq pb p q hq)).obj Bb

/-- The object `A₀ = A_b|_{P_b}` on the intersection of the square over `W_b`: the one
Stacks 09RI is applied to. -/
abbrev edsBridgeInterOpenObj : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsInter B S hS (edsPreimage hsq pb)))) :=
  (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq pb))).obj Ab

/-- The object `Bo₀ = Bo_b|_{P_b}` on the intersection of the square over `W_b`. -/
abbrev edsBridgeInterEtaleObj : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsInter B S hS (edsPreimage hsq pb)))) :=
  (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq pb))).obj Bb

/-- The object `E|_{P'}` of `D(𝒪_{P'})` that the two isomorphisms of Stacks 09RI land in: the
restriction of `E` to the intersection of the square over `W'`, taken through the open
subspace. -/
abbrev edsBridgeLimitObj : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsInter B S hS (edsPreimage hsq p')))) :=
  (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p'))).obj
    ((smallEtaleDerivedModulePullback B S hS
      (edsOpenHom B S hS (edsPreimage hsq p'))).obj E)

/-! ### The square isomorphisms of the faces of the cube -/

/-- The square isomorphism of the face of the cube over `q` through the open subspace:
`Lt_P^*(A_b|_{P_b}) ≅ (Lt_U^*A_b)|_{P}`. -/
def edsBridgeOpenSquare :
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p q hq)).obj
        (edsBridgeInterOpenObj hsq pb Ab) ≅
      (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p))).obj
        (edsBridgeOpenObj hsq pb p q hq Ab) :=
  ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsFst B S hS (edsPreimage hsq p)) (edsPreimageOpenMap hsq pb p q hq)
    (edsPreimageInterMap hsq pb p q hq) (edsFst B S hS (edsPreimage hsq pb))
    (edsFst_comp_edsPreimageOpenMap hsq pb p q hq)).app Ab

/-- The square isomorphism of the face of the cube over `q` through the étale algebraic space:
`Lt_P^*(Bo_b|_{P_b}) ≅ (Lt_V^*Bo_b)|_{P}`. -/
def edsBridgeEtaleSquare :
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p q hq)).obj
        (edsBridgeInterEtaleObj hsq pb Bb) ≅
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p))).obj
        (edsBridgeEtaleObj hsq pb p q hq Bb) :=
  ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsSnd B S hS (edsPreimage hsq p)) (edsPreimageEtaleMap hsq pb p q hq)
    (edsPreimageInterMap hsq pb p q hq) (edsSnd B S hS (edsPreimage hsq pb))
    (edsSnd_comp_edsPreimageEtaleMap hsq pb p q hq)).app Bb

/-- The square isomorphism of the face of the cube over `q'` through the open subspace. -/
def edsBridgeOpenSquare' :
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q' hq')).obj
        ((smallEtaleDerivedModulePullback B S hS
          (edsFst B S hS (edsPreimage hsq p))).obj (edsBridgeOpenObj hsq pb p q hq Ab)) ≅
      (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p'))).obj
        ((smallEtaleDerivedModulePullback B S hS
          (edsPreimageOpenMap hsq p p' q' hq')).obj (edsBridgeOpenObj hsq pb p q hq Ab)) :=
  ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsFst B S hS (edsPreimage hsq p')) (edsPreimageOpenMap hsq p p' q' hq')
    (edsPreimageInterMap hsq p p' q' hq') (edsFst B S hS (edsPreimage hsq p))
    (edsFst_comp_edsPreimageOpenMap hsq p p' q' hq')).app
    (edsBridgeOpenObj hsq pb p q hq Ab)

/-- The square isomorphism of the face of the cube over `q'` through the étale algebraic
space. -/
def edsBridgeEtaleSquare' :
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q' hq')).obj
        ((smallEtaleDerivedModulePullback B S hS
          (edsSnd B S hS (edsPreimage hsq p))).obj (edsBridgeEtaleObj hsq pb p q hq Bb)) ≅
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p'))).obj
        ((smallEtaleDerivedModulePullback B S hS
          (edsPreimageEtaleMap hsq p p' q' hq')).obj (edsBridgeEtaleObj hsq pb p q hq Bb)) :=
  ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsSnd B S hS (edsPreimage hsq p')) (edsPreimageEtaleMap hsq p p' q' hq')
    (edsPreimageInterMap hsq p p' q' hq') (edsSnd B S hS (edsPreimage hsq p))
    (edsSnd_comp_edsPreimageEtaleMap hsq p p' q' hq')).app
    (edsBridgeEtaleObj hsq pb p q hq Bb)

/-- The square isomorphism of the cartesian square of the square over `W'`, at `E`:
`(E|_{U'})|_{P'} ≅ (E|_{V'})|_{P'}`. -/
def edsBridgeCartesianSquare :
    (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p'))).obj
        ((smallEtaleDerivedModulePullback B S hS
          (edsOpenHom B S hS (edsPreimage hsq p'))).obj E) ≅
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p'))).obj
        ((smallEtaleDerivedModulePullback B S hS
          (edsEtaleHom B S hS (edsPreimage hsq p'))).obj E) :=
  ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsSnd B S hS (edsPreimage hsq p')) (edsEtaleHom B S hS (edsPreimage hsq p'))
    (edsFst B S hS (edsPreimage hsq p')) (edsOpenHom B S hS (edsPreimage hsq p'))
    (isPullback_edsInter B S hS (edsPreimage hsq p')).flip.w).app E

/-! ### The transported comparison -/

variable (c : (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p q hq)).obj
      (edsBridgeInterOpenObj hsq pb Ab) ≅
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p q hq)).obj
      (edsBridgeInterEtaleObj hsq pb Bb))

/-- **The comparison isomorphism over the intersection of the square over `W`**, transported
from the comparison `c` over the intersection of the square over `W_b` by the two square
isomorphisms of the faces of the cube over `q`.  This is the comparison the square step is run
with. -/
def edsBridgeComparison :
    (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p))).obj
        (edsBridgeOpenObj hsq pb p q hq Ab) ≅
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p))).obj
        (edsBridgeEtaleObj hsq pb p q hq Bb) :=
  edsBridgeConj (edsBridgeOpenSquare hsq pb p q hq Ab) c (edsBridgeEtaleSquare hsq pb p q hq Bb)

/-- The derived pullback along `r_P` of the transported comparison, written out. -/
theorem map_edsBridgeComparison_hom :
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q' hq')).map
        (edsBridgeComparison hsq pb p q hq Ab Bb c).hom =
      ((smallEtaleDerivedModulePullback B S hS
            (edsPreimageInterMap hsq p p' q' hq')).mapIso
          (edsBridgeOpenSquare hsq pb p q hq Ab)).inv ≫
        (smallEtaleDerivedModulePullback B S hS
          (edsPreimageInterMap hsq p p' q' hq')).map c.hom ≫
        ((smallEtaleDerivedModulePullback B S hS
            (edsPreimageInterMap hsq p p' q' hq')).mapIso
          (edsBridgeEtaleSquare hsq pb p q hq Bb)).hom :=
  edsBridgeMapConj
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q' hq'))
    (edsBridgeOpenSquare hsq pb p q hq Ab) c (edsBridgeEtaleSquare hsq pb p q hq Bb)

/-! ### The two isomorphisms of Stacks 09RI, and the bridge -/

variable
  (αU : (smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq p p' q' hq')).obj
      (edsBridgeOpenObj hsq pb p q hq Ab) ≅
    (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS (edsPreimage hsq p'))).obj E)
  (αV : (smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq p p' q' hq')).obj
      (edsBridgeEtaleObj hsq pb p q hq Bb) ≅
    (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS (edsPreimage hsq p'))).obj E)

section Bridge

include hs

/-- The composition comparison of the factorisation `r_P ≫ t_P = s_P` of the maps of
intersections: `Lt_P^* ⋙ Lr_P^* ≅ Ls_P^*`.  The factorisation is the cocycle identity
`AlgebraicGeometry.Space.edsPreimageInterMap_comp_edsPreimageInterMap`. -/
def edsBridgeInterComp :
    smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p q hq) ⋙
        smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q' hq') ≅
      smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p' s hsp) :=
  (DerivedPullbackComposition.canonical B S hS).iso
    (edsPreimageInterMap hsq p p' q' hq') (edsPreimageInterMap hsq pb p q hq)
    (edsPreimageInterMap hsq pb p' s hsp)
    (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb p p' q q' hq hq' s hs hsp)

/-- **The first isomorphism `α` that Stacks 09RI is applied to**:
`Ls_P^*(A_b|_{P_b}) ≅ E|_{P'}`, built from the composition comparison of `r_P ≫ t_P = s_P`, the
square isomorphisms of the two faces of the cube through the open subspace, and the inductive
hypothesis `αU`. -/
def edsBridgeFst :
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p' s hsp)).obj
        (edsBridgeInterOpenObj hsq pb Ab) ≅
      edsBridgeLimitObj hsq p' E :=
  edsBridgeConj₄
    ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
      (edsBridgeInterOpenObj hsq pb Ab))
    ((smallEtaleDerivedModulePullback B S hS
      (edsPreimageInterMap hsq p p' q' hq')).mapIso (edsBridgeOpenSquare hsq pb p q hq Ab))
    (edsBridgeOpenSquare' hsq pb p p' q q' hq hq' Ab)
    ((smallEtaleDerivedModulePullback B S hS
      (edsFst B S hS (edsPreimage hsq p'))).mapIso αU)

/-- **The second isomorphism `β` that Stacks 09RI is applied to**:
`Ls_P^*(Bo_b|_{P_b}) ≅ E|_{P'}`, built from the composition comparison of `r_P ≫ t_P = s_P`, the
square isomorphisms of the two faces of the cube through the étale algebraic space, the inductive
hypothesis `αV`, and the square isomorphism of the cartesian square of the square over `W'`. -/
def edsBridgeSnd :
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p' s hsp)).obj
        (edsBridgeInterEtaleObj hsq pb Bb) ≅
      edsBridgeLimitObj hsq p' E :=
  edsBridgeConj₅
    ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
      (edsBridgeInterEtaleObj hsq pb Bb))
    ((smallEtaleDerivedModulePullback B S hS
      (edsPreimageInterMap hsq p p' q' hq')).mapIso (edsBridgeEtaleSquare hsq pb p q hq Bb))
    (edsBridgeEtaleSquare' hsq pb p p' q q' hq hq' Bb)
    ((smallEtaleDerivedModulePullback B S hS
      (edsSnd B S hS (edsPreimage hsq p'))).mapIso αV)
    (edsBridgeCartesianSquare hsq p' E).symm

/-- **The bridge, at the conjugated comparison.**  The hypothesis `hfac` is the hom-level map to
the limit of Stacks 09RI applied to `c`, written out: the derived pullback along `r_P` conjugated
by the composition comparison of `r_P ≫ t_P = s_P`, which is
`AlgebraicGeometry.Space.DescentSituation.homProjection` of the system of intersections and
`AlgebraicGeometry.Space.DerivedPullbackComposition.factorHom` of that factorisation, both by
definition.  If it sends `c` to `α ∘ β⁻¹`, then the derived pullback along `r_P` of
`c`, conjugated by the two square isomorphisms of the faces of the cube over `q`, is the right
side of the hypothesis `hc` of the elementary-distinguished-square step.

Composed with `AlgebraicGeometry.Space.map_edsBridgeComparison_hom`, which rewrites the left
side as the derived pullback of the transported comparison, this is
`AlgebraicGeometry.Space.hc_edsBridgeComparison_of_factorHom`. -/
theorem edsBridge_conj_eq_of_factorHom
    (hfac : ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
            (edsBridgeInterOpenObj hsq pb Ab)).inv ≫
          (smallEtaleDerivedModulePullback B S hS
            (edsPreimageInterMap hsq p p' q' hq')).map c.hom ≫
          ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
            (edsBridgeInterEtaleObj hsq pb Bb)).hom =
      (edsBridgeFst hsq pb p p' q q' hq hq' s hs hsp Ab E αU).hom ≫
        (edsBridgeSnd hsq pb p p' q q' hq hq' s hs hsp Bb E αV).inv) :
    ((smallEtaleDerivedModulePullback B S hS
            (edsPreimageInterMap hsq p p' q' hq')).mapIso
          (edsBridgeOpenSquare hsq pb p q hq Ab)).inv ≫
        (smallEtaleDerivedModulePullback B S hS
          (edsPreimageInterMap hsq p p' q' hq')).map c.hom ≫
        ((smallEtaleDerivedModulePullback B S hS
            (edsPreimageInterMap hsq p p' q' hq')).mapIso
          (edsBridgeEtaleSquare hsq pb p q hq Bb)).hom =
      (edsBridgeOpenSquare' hsq pb p p' q q' hq hq' Ab).hom ≫
        (smallEtaleDerivedModulePullback B S hS
          (edsFst B S hS (edsPreimage hsq p'))).map αU.hom ≫
        (edsBridgeCartesianSquare hsq p' E).hom ≫
        (smallEtaleDerivedModulePullback B S hS
          (edsSnd B S hS (edsPreimage hsq p'))).map αV.inv ≫
        (edsBridgeEtaleSquare' hsq pb p p' q q' hq hq' Bb).inv :=
  edsBridgeCore
    ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
      (edsBridgeInterOpenObj hsq pb Ab))
    ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
      (edsBridgeInterEtaleObj hsq pb Bb))
    ((smallEtaleDerivedModulePullback B S hS
      (edsPreimageInterMap hsq p p' q' hq')).mapIso (edsBridgeOpenSquare hsq pb p q hq Ab))
    ((smallEtaleDerivedModulePullback B S hS
      (edsPreimageInterMap hsq p p' q' hq')).mapIso (edsBridgeEtaleSquare hsq pb p q hq Bb))
    (edsBridgeOpenSquare' hsq pb p p' q q' hq hq' Ab)
    ((smallEtaleDerivedModulePullback B S hS
      (edsFst B S hS (edsPreimage hsq p'))).mapIso αU)
    (edsBridgeEtaleSquare' hsq pb p p' q q' hq hq' Bb)
    ((smallEtaleDerivedModulePullback B S hS
      (edsSnd B S hS (edsPreimage hsq p'))).mapIso αV)
    (edsBridgeCartesianSquare hsq p' E).symm
    ((smallEtaleDerivedModulePullback B S hS
      (edsPreimageInterMap hsq p p' q' hq')).map c.hom)
    hfac

/-- **The bridge.**  The hypothesis `hc` of the elementary-distinguished-square step
`AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_edsPreimage`, for the
transported comparison `AlgebraicGeometry.Space.edsBridgeComparison`, from the hom-level equation
of Stacks 09RI for `α` and `β`.

This is the identification that step was missing: `α` and `β` are built from the square
isomorphisms of the cube of Stacks 08GN and the inductive hypotheses `αU`, `αV`, and the equation
Stacks 09RI delivers for them *is* `hc`. -/
theorem hc_edsBridgeComparison_of_factorHom
    (hfac : ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
            (edsBridgeInterOpenObj hsq pb Ab)).inv ≫
          (smallEtaleDerivedModulePullback B S hS
            (edsPreimageInterMap hsq p p' q' hq')).map c.hom ≫
          ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
            (edsBridgeInterEtaleObj hsq pb Bb)).hom =
      (edsBridgeFst hsq pb p p' q q' hq hq' s hs hsp Ab E αU).hom ≫
        (edsBridgeSnd hsq pb p p' q q' hq hq' s hs hsp Bb E αV).inv) :
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q' hq')).map
        (edsBridgeComparison hsq pb p q hq Ab Bb c).hom =
      (edsBridgeOpenSquare' hsq pb p p' q q' hq hq' Ab).hom ≫
        (smallEtaleDerivedModulePullback B S hS
          (edsFst B S hS (edsPreimage hsq p'))).map αU.hom ≫
        (edsBridgeCartesianSquare hsq p' E).hom ≫
        (smallEtaleDerivedModulePullback B S hS
          (edsSnd B S hS (edsPreimage hsq p'))).map αV.inv ≫
        (edsBridgeEtaleSquare' hsq pb p p' q q' hq hq' Bb).inv :=
  (map_edsBridgeComparison_hom hsq pb p p' q q' hq hq' Ab Bb c).trans
    (edsBridge_conj_eq_of_factorHom hsq pb p p' q q' hq hq' s hs hsp Ab Bb E c αU αV hfac)

end Bridge

end AlgebraicGeometry.Space

end
