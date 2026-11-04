module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpacesOfComposable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.GroupStructure

/-!
# A groupoid with equal source and target is the trivial-action groupoid of its stabilizer

Let `G` be a groupoid in algebraic spaces over `B`, with object space `U` and arrow space `R`,
whose source and target morphisms agree. Then every arrow of `G` is a loop, so the stabilizer
`G/U` of Stacks 0447 — the fibre product of `(t, s) : R ⟶ U ×_B U` with the diagonal of `U` — is
the whole arrow space: the projection `G/U ⟶ R` is an isomorphism, its inverse sending an arrow
to that arrow together with its common source and target. Since the stabilizer is a group object
in the slice over `U` (Stacks 0447), and since on arrows its multiplication *is* composition in
`G`, the groupoid `G` read over its own object space is the action groupoid of Stacks 0444 for
the trivial action of `G/U` on `U`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrowIso`: the projection of the
  stabilizer to the arrow space, as an isomorphism of presheaves.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.overObjects`: the groupoid read over its own
  object space, which is the base over which the action groupoid of the stabilizer lives.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.trivialActionGroupoid`: the action groupoid of
  the trivial action of the stabilizer on the object space, Stacks 0444 at the group object of
  Stacks 0447.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isAlgebraicSpace_stabilizer`: the underlying
  presheaf of the stabilizer, read in the slice over the object space, is an algebraic space.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.trivialActionIso`: **a groupoid in algebraic
  spaces whose source equals its target is the action groupoid of the trivial action of its
  stabilizer group on its object space**, as an isomorphism of groupoids in algebraic spaces.

## Implementation notes

The base. The stabilizer is a group object of the slice over the object space, so the action
groupoid of Stacks 0444 built from it is a groupoid in algebraic spaces over the *object space*,
not over `B`; and `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Iso` compares two groupoids over
one base. The comparison is therefore stated for
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.overObjects`, the given groupoid with its structure
morphisms to the base replaced by the identity of the object space and by the source. That is a
reading of the same quintuple `(U, R, s, t, c)`, not a weakening: the object space, the arrow
space, the source, the target, the composition and the pointwise groupoid condition are the
given ones, and the hypothesis `s = t` is what makes the replacement legitimate — with `s = t`
the composition law has the source of its first factor, which is what the new structure morphism
of the arrow space demands.

The trivial action is `CategoryTheory.ModObj.trivialAction`, installed as a local instance.
`AlgebraicGeometry.Space.modObjTensorUnit`, the other instance in the library making a monoid
object act on the monoidal unit, is not in scope here; the two differ in their spelling of the
action morphism, although not in its value.

Transport. `AlgebraicGeometry.Space.ActionGroupoidConstruction` records its object and arrow
spaces as equalities of algebraic spaces and its structure morphisms as heterogeneous
equalities, so each of the latter is turned into an equation of morphisms by conjugating with
the induced `CategoryTheory.eqToHom`, through `CategoryTheory.conj_eqToHom_iff_heq`, exactly as
in `AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_trivialActionGroupoid_iff`. Nothing in this
file is `private`: the comparison is *data*, so the body of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.trivialActionIso` is exposed by the module's
`@[expose] public section`, and an exposed body may only mention public declarations — every
clause feeding it has to be public too.

The composition law is the one field whose heterogeneous equality cannot be transported by
conjugation alone, the two sides having fibre products of *different* morphisms as domains. It
is handled by `transportedComp` below, whose hypotheses name the two fibre products' data as
variables so that the equalities can be substituted; the content of the lemma is then that
`AlgebraicGeometry.composableToPullback` is the lift of the two projections of the presheaf of
composable pairs.

With that in hand the composition clause of the comparison is an equation of morphisms out of
the presheaf of composable pairs, which is the shape in which
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizer_mul_comp_arrow` — multiplication in the
stabilizer is groupoid composition — applies, its test object being that presheaf read in the
slice over the object space along the composition morphism of the action groupoid. Evaluating
the resulting equation at a composable pair is `AlgebraicGeometry.natTrans_app_congr` together
with `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose_eval`.

The right unitor of the slice is not used to name the first projection of the arrow space
`G/U ⊗ U`: `CartesianMonoidalCategory.fst` is the same morphism and is the one the composition
of the action groupoid is stated with, so only the *inverse* of the unitor, which has no such
spelling, appears — in the backwards map on arrow spaces.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

attribute [local instance] ModObj.trivialAction
attribute [local implicit_reducible] toGroupoidInFunctors AlgebraicSpaces.fiberProduct

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The stabilizer of a groupoid in algebraic spaces, read in the slice over the object space,
has an algebraic space as its underlying presheaf: it is the same presheaf as the stabilizer
read as an algebraic space over `S`. -/
theorem isAlgebraicSpace_stabilizer (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsAlgebraicSpace C S hS (stabilizer G).left :=
  (stabilizerOverBase G).property

/-- When source and target agree, the underlying arrow of a stabilizer element is an
isomorphism of presheaves: its inverse sends an arrow to itself together with its common
source and target. -/
noncomputable def stabilizerArrowIso (G : GroupoidInAlgebraicSpaces C S hS B)
    (h : G.source = G.target) : (stabilizer G).left ≅ G.arrows.obj where
  hom := stabilizerArrow G
  inv := pullback.lift (𝟙 G.arrows.obj) G.source.hom
    (stabilizerArrow_condition G (𝟙 G.arrows.obj) G.source.hom (Category.id_comp _) (by
      have hhom : G.source.hom = G.target.hom :=
        congrArg (fun f : G.arrows ⟶ G.objects => f.hom) h
      rw [Category.id_comp, hhom]))
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      exact stabilizerArrow_source G
  inv_hom_id := pullback.lift_fst _ _ _

/-- The forward morphism of `stabilizerArrowIso` is the projection of the stabilizer to the
arrow space. -/
@[simp]
theorem stabilizerArrowIso_hom (G : GroupoidInAlgebraicSpaces C S hS B)
    (h : G.source = G.target) : (stabilizerArrowIso G h).hom = stabilizerArrow G := rfl

/-- A groupoid in algebraic spaces whose source and target agree, read as a groupoid over its
own object space: the object space, the arrow space, the source, the target and the composition
are unchanged, the object space lies over the base by the identity and the arrow space by the
source.

Composition is a morphism over the new base because the source of a composite is the source of
its second factor, which with `s = t` is the source of its first factor. -/
noncomputable def overObjects (G : GroupoidInAlgebraicSpaces C S hS B)
    (h : G.source = G.target) : GroupoidInAlgebraicSpaces C S hS G.objects where
  objects := G.objects
  arrows := G.arrows
  objectsToBase := 𝟙 G.objects
  arrowsToBase := G.source
  source := G.source
  target := G.target
  source_over := Category.comp_id _
  target_over := (Category.comp_id _).trans h.symm
  comp := G.comp
  comp_over := by
    refine ObjectProperty.hom_ext _ ?_
    have hhom : G.source.hom = G.target.hom :=
      congrArg (fun f : G.arrows ⟶ G.objects => f.hom) h
    have hcomp : G.comp.hom =
        groupoidCompose G (pullback.fst G.source.hom G.target.hom)
          (pullback.snd G.source.hom G.target.hom) pullback.condition := by
      rw [groupoidCompose_eq_comp, pullback.lift_fst_snd, Category.id_comp]
    change G.comp.hom ≫ G.source.hom =
      pullback.fst G.source.hom G.target.hom ≫ G.source.hom
    calc G.comp.hom ≫ G.source.hom
        = groupoidCompose G (pullback.fst G.source.hom G.target.hom)
            (pullback.snd G.source.hom G.target.hom) pullback.condition ≫ G.source.hom :=
          congrArg (fun k => k ≫ G.source.hom) hcomp
      _ = pullback.snd G.source.hom G.target.hom ≫ G.source.hom :=
          groupoidCompose_source G _ _ _
      _ = pullback.snd G.source.hom G.target.hom ≫ G.target.hom :=
          congrArg (fun k => pullback.snd G.source.hom G.target.hom ≫ k) hhom
      _ = pullback.fst G.source.hom G.target.hom ≫ G.source.hom := pullback.condition.symm
  pointwiseGroupoid := G.pointwiseGroupoid

/-- The underlying groupoid in presheaves does not see the base: reading a groupoid over its own
object space leaves it unchanged. -/
theorem overObjects_toGroupoidInFunctors (G : GroupoidInAlgebraicSpaces C S hS B)
    (h : G.source = G.target) :
    (overObjects G h).toGroupoidInFunctors = G.toGroupoidInFunctors := rfl

/-- The transport of a heterogeneous equality of composition laws. If the object and arrow
presheaves, the source and the target of two groupoid-like data agree, and their composition
laws are heterogeneously equal, then the composition law of the first, read on the presheaf of
composable pairs of arrows, is the composition law of the second read along any lift `l` of the
two projections of that presheaf.

This is the shape in which the `comp_eq` field of
`AlgebraicGeometry.Space.ActionGroupoidConstruction` is usable: conjugation by
`CategoryTheory.eqToHom` does not apply to it, the domains of its two sides being fibre products
of different morphisms. -/
theorem transportedComp {O R O' R' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {s t : R ⟶ O} {s' t' : R' ⟶ O'} (c : pullback s t ⟶ R) (c' : pullback s' t' ⟶ R')
    (hR : R = R') (hO : O = O') (hs : s ≍ s') (ht : t ≍ t') (hc : c ≍ c')
    (l : Deformation.composableArrows O R s t ⟶ pullback s' t')
    (hl₁ : l ≫ pullback.fst s' t' = composableFst s t ≫ eqToHom hR)
    (hl₂ : l ≫ pullback.snd s' t' = composableSnd s t ≫ eqToHom hR) :
    composableToPullback s t ≫ c ≫ eqToHom hR = l ≫ c' := by
  cases hR
  cases hO
  obtain rfl := eq_of_heq hs
  obtain rfl := eq_of_heq ht
  obtain rfl := eq_of_heq hc
  rw [eqToHom_refl, Category.comp_id] at hl₁ hl₂
  rw [eqToHom_refl, Category.comp_id]
  have hl : l = composableToPullback s t :=
    pullback.hom_ext (by rw [hl₁, composableToPullback_comp_pullbackFst])
      (by rw [hl₂, composableToPullback_comp_pullbackSnd])
  rw [hl]

/-- A morphism of presheaves into the underlying presheaf of an object `P` of a slice category,
read as a morphism of that slice: its domain becomes an object of the slice along the composite
with the structure morphism of `P`. -/
abbrev overHomMk {Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (P : Over Y)
    {D : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (m : D ⟶ P.left) : Over.mk (m ≫ P.hom) ⟶ P :=
  Over.homMk m rfl

/-- **Composition in the action groupoid of the trivial action of the stabilizer is composition
in the groupoid**, read on the arrows underlying the two factors.

The composition morphism of the action groupoid of Stacks 0444 has multiplication in the group
object as its first component (`Stacks.Groupoids.ActionGroupoid.composition_fst`), and
multiplication in the stabilizer is groupoid composition on the underlying arrows
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizer_mul_comp_arrow`), applied here to the
two projections of the given generalized point `M` of the domain of that composition
morphism. -/
theorem actionCompositionArrow (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : Over G.objects.obj}
    (M : T ⟶ pullback (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
      γ[stabilizer G,𝟙_ (Over G.objects.obj)])
    (m : T.left ⟶ (pullback (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
      γ[stabilizer G,𝟙_ (Over G.objects.obj)]).left) (hm : M.left = m)
    (w : (m ≫ (pullback.fst (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
            γ[stabilizer G,𝟙_ (Over G.objects.obj)]).left ≫
          (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G) ≫
        G.source.hom =
        (m ≫ (pullback.snd (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
            γ[stabilizer G,𝟙_ (Over G.objects.obj)]).left ≫
          (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G) ≫
        G.target.hom) :
    m ≫ (Stacks.Groupoids.ActionGroupoid.composition (stabilizer G)
          (𝟙_ (Over G.objects.obj))).left ≫
        (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G =
      groupoidCompose G
        (m ≫ (pullback.fst (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
          γ[stabilizer G, 𝟙_ (Over G.objects.obj)]).left ≫
          (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G)
        (m ≫ (pullback.snd (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
          γ[stabilizer G, 𝟙_ (Over G.objects.obj)]).left ≫
          (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G) w := by
  subst hm
  obtain ⟨w', hw'⟩ := stabilizer_mul_comp_arrow G T
    (M ≫ (pullback.fst (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
      γ[stabilizer G, 𝟙_ (Over G.objects.obj)] ≫
      fst (stabilizer G) (𝟙_ (Over G.objects.obj))))
    (M ≫ (pullback.snd (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
      γ[stabilizer G, 𝟙_ (Over G.objects.obj)] ≫
      fst (stabilizer G) (𝟙_ (Over G.objects.obj))))
  have hlift : lift
        (M ≫ (pullback.fst (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
          γ[stabilizer G, 𝟙_ (Over G.objects.obj)] ≫
          fst (stabilizer G) (𝟙_ (Over G.objects.obj))))
        (M ≫ (pullback.snd (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
          γ[stabilizer G, 𝟙_ (Over G.objects.obj)] ≫
          fst (stabilizer G) (𝟙_ (Over G.objects.obj)))) ≫ μ[stabilizer G] =
      M ≫ (Stacks.Groupoids.ActionGroupoid.composition (stabilizer G)
        (𝟙_ (Over G.objects.obj)) ≫ fst (stabilizer G) (𝟙_ (Over G.objects.obj))) := by
    rw [Stacks.Groupoids.ActionGroupoid.composition_fst, ← comp_lift, Category.assoc]
  rw [groupoidCompose_eq_comp]
  calc M.left ≫ (Stacks.Groupoids.ActionGroupoid.composition (stabilizer G)
          (𝟙_ (Over G.objects.obj))).left ≫
        (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G
      = (lift
            (M ≫ (pullback.fst (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
              γ[stabilizer G, 𝟙_ (Over G.objects.obj)] ≫
              fst (stabilizer G) (𝟙_ (Over G.objects.obj))))
            (M ≫ (pullback.snd (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
              γ[stabilizer G, 𝟙_ (Over G.objects.obj)] ≫
              fst (stabilizer G) (𝟙_ (Over G.objects.obj)))) ≫
          μ[stabilizer G]).left ≫ stabilizerArrow G := by
        rw [hlift]
        rfl
    _ = pullback.lift
          ((M ≫ (pullback.fst (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
            γ[stabilizer G, 𝟙_ (Over G.objects.obj)] ≫
            fst (stabilizer G) (𝟙_ (Over G.objects.obj)))).left ≫ stabilizerArrow G)
          ((M ≫ (pullback.snd (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
            γ[stabilizer G, 𝟙_ (Over G.objects.obj)] ≫
            fst (stabilizer G) (𝟙_ (Over G.objects.obj)))).left ≫ stabilizerArrow G) w' ≫
          G.comp.hom := hw'
    _ = pullback.lift
          (M.left ≫ (pullback.fst (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
            γ[stabilizer G, 𝟙_ (Over G.objects.obj)]).left ≫
            (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G)
          (M.left ≫ (pullback.snd (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
            γ[stabilizer G, 𝟙_ (Over G.objects.obj)]).left ≫
            (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G) w ≫
          G.comp.hom := by
        refine congrArg (fun k => k ≫ G.comp.hom) (pullback.hom_ext ?_ ?_)
        · rw [pullback.lift_fst, pullback.lift_fst, Over.comp_left, Over.comp_left,
            Category.assoc, Category.assoc]
        · rw [pullback.lift_snd, pullback.lift_snd, Over.comp_left, Over.comp_left,
            Category.assoc, Category.assoc]

/-- Conjugating a heterogeneously equal pair of morphisms by `eqToHom` makes them equal. -/
private theorem eqToHom_comp_eq_comp_eqToHom_of_heq {X Y X' Y' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y') (h : f ≍ g) :
    eqToHom hX ≫ g = f ≫ eqToHom hY := by
  subst hX hY
  cases h
  simp

/-- Composable pairs of arrows have equal images under two maps that intertwine source and target
with the same map on objects. -/
private theorem composable_comp_eq_comp {O R X Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {s t : R ⟶ O} {a b : R ⟶ X} {p q : X ⟶ Y} {e : O ⟶ Y} (hs : a ≫ p = s ≫ e)
    (ht : b ≫ q = t ≫ e) : (composableFst s t ≫ a) ≫ p = (composableSnd s t ≫ b) ≫ q := by
  rw [Category.assoc, hs, ← Category.assoc, composableFst_comp_source, Category.assoc, ← ht,
    Category.assoc]

section TrivialAction

variable (G : GroupoidInAlgebraicSpaces C S hS B) (h : G.source = G.target)
  (A : Space.ActionGroupoidConstruction G.objects (stabilizer G)
    (𝟙_ (Over G.objects.obj)) (isAlgebraicSpace_stabilizer G) G.objects.property)

/-- The object space of the action groupoid of the trivial action of the stabilizer is the
object space of the groupoid. -/
theorem trivialActionObjects_obj : A.groupoid.objects.obj = G.objects.obj :=
  congrArg (fun z => z.obj) A.objects_eq

/-- The arrow space of the action groupoid of the trivial action of the stabilizer is the
product of the stabilizer with the object space over the object space. -/
theorem trivialActionArrows_obj :
    A.groupoid.arrows.obj = (stabilizer G ⊗ 𝟙_ (Over G.objects.obj)).left :=
  congrArg (fun z => z.obj) A.arrows_eq

/-- The structure morphism of the object space of the action groupoid of the trivial action is
the transport along the identification of that space with the object space. -/
theorem trivialActionObjectsToBase_hom :
    A.groupoid.objectsToBase.hom = eqToHom (trivialActionObjects_obj G A) := by
  have h2 := (conj_eqToHom_iff_heq A.groupoid.objectsToBase.hom (𝟙 G.objects.obj)
    (trivialActionObjects_obj G A) rfl).2 A.objectsToBase_eq
  simpa using h2

/-- The structure morphism of the arrow space of the action groupoid of the trivial action is
the transport of the structure morphism of the product. -/
theorem trivialActionArrowsToBase_hom :
    A.groupoid.arrowsToBase.hom = eqToHom (trivialActionArrows_obj G A) ≫
      (stabilizer G ⊗ 𝟙_ (Over G.objects.obj)).hom := by
  have h2 := (conj_eqToHom_iff_heq A.groupoid.arrowsToBase.hom
    (stabilizer G ⊗ 𝟙_ (Over G.objects.obj)).hom (trivialActionArrows_obj G A) rfl).2
    A.arrowsToBase_eq
  simpa using h2

/-- The source of the action groupoid of the trivial action is the second projection of the
product, up to the two identifications. -/
theorem trivialActionSource_hom :
    eqToHom (trivialActionArrows_obj G A) ≫
        (snd (stabilizer G) (𝟙_ (Over G.objects.obj))).left =
      A.groupoid.source.hom ≫ eqToHom (trivialActionObjects_obj G A) :=
  eqToHom_comp_eq_comp_eqToHom_of_heq _ _ _ _ A.source_eq

/-- The target of the action groupoid of the trivial action is again the second projection of
the product: the action is trivial. -/
theorem trivialActionTarget_hom :
    eqToHom (trivialActionArrows_obj G A) ≫
        (snd (stabilizer G) (𝟙_ (Over G.objects.obj))).left =
      A.groupoid.target.hom ≫ eqToHom (trivialActionObjects_obj G A) :=
  eqToHom_comp_eq_comp_eqToHom_of_heq _ _ _ _ A.target_eq

/-- The map on object spaces of the comparison: the identification of the object space of the
action groupoid with the object space of the groupoid. -/
noncomputable abbrev trivialActionMapObjects :
    A.groupoid.objects.obj ⟶ G.objects.obj :=
  eqToHom (trivialActionObjects_obj G A)

/-- The map on arrow spaces of the comparison: an arrow of the action groupoid is a stabilizer
element together with a point of the object space, and it is sent to the arrow of the groupoid
underlying that stabilizer element. -/
noncomputable abbrev trivialActionMapArrows :
    A.groupoid.arrows.obj ⟶ G.arrows.obj :=
  eqToHom (trivialActionArrows_obj G A) ≫
    (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G

/-- The inverse map on arrow spaces: an arrow of the groupoid is a stabilizer element, since
source and target agree, and is paired with its common endpoint. -/
noncomputable abbrev trivialActionInvArrows :
    G.arrows.obj ⟶ A.groupoid.arrows.obj :=
  (stabilizerArrowIso G h).inv ≫ (ρ_ (stabilizer G)).inv.left ≫
    eqToHom (trivialActionArrows_obj G A).symm

/-- The first projection of the arrow space of the trivial-action groupoid, followed by the
structure morphism of the stabilizer, is the second projection: the structure morphism of the
product computed along either factor. -/
theorem trivialActionFstHom :
    (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ (stabilizer G).hom =
      (snd (stabilizer G) (𝟙_ (Over G.objects.obj))).left := by
  change pullback.fst (stabilizer G).hom (𝟙 G.objects.obj) ≫ (stabilizer G).hom =
    pullback.snd (stabilizer G).hom (𝟙 G.objects.obj)
  rw [pullback.condition, Category.comp_id]

/-- The first projection of the arrow space is a split epimorphism, with the inverse of the
right unitor as a section. -/
theorem trivialActionFst_unitorInv :
    (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ (ρ_ (stabilizer G)).inv.left =
      𝟙 (stabilizer G ⊗ 𝟙_ (Over G.objects.obj)).left :=
  congrArg (fun k : (stabilizer G ⊗ 𝟙_ (Over G.objects.obj)) ⟶
    (stabilizer G ⊗ 𝟙_ (Over G.objects.obj)) => k.left) (ρ_ (stabilizer G)).hom_inv_id

/-- The inverse of the right unitor is a section of the first projection of the arrow
space. -/
theorem trivialActionUnitorInv_fst :
    (ρ_ (stabilizer G)).inv.left ≫ (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left =
      𝟙 (stabilizer G).left :=
  congrArg (fun k : stabilizer G ⟶ stabilizer G => k.left) (ρ_ (stabilizer G)).inv_hom_id

/-- The comparison respects the source. -/
theorem trivialActionMapArrows_source :
    trivialActionMapArrows G A ≫ G.source.hom =
      A.groupoid.source.hom ≫ trivialActionMapObjects G A := by
  change (eqToHom (trivialActionArrows_obj G A) ≫
    (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G) ≫
      G.source.hom = _
  rw [Category.assoc, Category.assoc, stabilizerArrow_source, trivialActionFstHom,
    trivialActionSource_hom]

/-- The comparison respects the target. -/
theorem trivialActionMapArrows_target :
    trivialActionMapArrows G A ≫ G.target.hom =
      A.groupoid.target.hom ≫ trivialActionMapObjects G A := by
  change (eqToHom (trivialActionArrows_obj G A) ≫
    (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G) ≫
      G.target.hom = _
  rw [Category.assoc, Category.assoc, stabilizerArrow_target, trivialActionFstHom,
    trivialActionTarget_hom]

/-- The two projections of the presheaf of composable pairs of the action groupoid have
composable images under the comparison. -/
theorem trivialActionComposable :
    (composableFst A.groupoid.source.hom A.groupoid.target.hom ≫
        trivialActionMapArrows G A) ≫ G.source.hom =
      (composableSnd A.groupoid.source.hom A.groupoid.target.hom ≫
        trivialActionMapArrows G A) ≫ G.target.hom :=
  composable_comp_eq_comp (trivialActionMapArrows_source G A) (trivialActionMapArrows_target G A)

/-- The two projections of the presheaf of composable pairs of the action groupoid, transported
to the arrow space of the product, land in the domain of the composition morphism of the action
groupoid. -/
theorem trivialActionLiftCondition :
    (composableFst A.groupoid.source.hom A.groupoid.target.hom ≫
        eqToHom (trivialActionArrows_obj G A)) ≫
      (snd (stabilizer G) (𝟙_ (Over G.objects.obj))).left =
      (composableSnd A.groupoid.source.hom A.groupoid.target.hom ≫
        eqToHom (trivialActionArrows_obj G A)) ≫
      γ[stabilizer G, 𝟙_ (Over G.objects.obj)].left :=
  composable_comp_eq_comp (trivialActionSource_hom G A) (trivialActionTarget_hom G A)

/-- **The comparison respects composition**, as an equation of morphisms out of the presheaf of
composable pairs of arrows of the action groupoid. -/
theorem trivialActionComp_map :
    composableToPullback A.groupoid.source.hom A.groupoid.target.hom ≫
        A.groupoid.comp.hom ≫ trivialActionMapArrows G A =
      groupoidCompose G
        (composableFst A.groupoid.source.hom A.groupoid.target.hom ≫
          trivialActionMapArrows G A)
        (composableSnd A.groupoid.source.hom A.groupoid.target.hom ≫
          trivialActionMapArrows G A) (trivialActionComposable G A) := by
  have htr := transportedComp A.groupoid.comp.hom
    (A.compositionDomainIso.hom ≫ (Stacks.Groupoids.ActionGroupoid.composition
      (stabilizer G) (𝟙_ (Over G.objects.obj))).left)
    (trivialActionArrows_obj G A) (trivialActionObjects_obj G A)
    A.source_eq A.target_eq A.comp_eq
    (pullback.lift _ _ (trivialActionLiftCondition G A))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hfst : (pullback.lift _ _ (trivialActionLiftCondition G A) ≫
        A.compositionDomainIso.hom) ≫
      (pullback.fst (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
        γ[stabilizer G, 𝟙_ (Over G.objects.obj)]).left =
      composableFst A.groupoid.source.hom A.groupoid.target.hom ≫
        eqToHom (trivialActionArrows_obj G A) := by
    rw [Category.assoc, A.compositionDomainIso_fst, pullback.lift_fst]
  have hsnd : (pullback.lift _ _ (trivialActionLiftCondition G A) ≫
        A.compositionDomainIso.hom) ≫
      (pullback.snd (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
        γ[stabilizer G, 𝟙_ (Over G.objects.obj)]).left =
      composableSnd A.groupoid.source.hom A.groupoid.target.hom ≫
        eqToHom (trivialActionArrows_obj G A) := by
    rw [Category.assoc, A.compositionDomainIso_snd, pullback.lift_snd]
  have ha : (pullback.lift _ _ (trivialActionLiftCondition G A) ≫
        A.compositionDomainIso.hom) ≫
      (pullback.fst (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
          γ[stabilizer G, 𝟙_ (Over G.objects.obj)]).left ≫
        (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G =
      composableFst A.groupoid.source.hom A.groupoid.target.hom ≫
        trivialActionMapArrows G A := by
    rw [← Category.assoc, hfst, Category.assoc]
  have hb : (pullback.lift _ _ (trivialActionLiftCondition G A) ≫
        A.compositionDomainIso.hom) ≫
      (pullback.snd (snd (stabilizer G) (𝟙_ (Over G.objects.obj)))
          γ[stabilizer G, 𝟙_ (Over G.objects.obj)]).left ≫
        (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G =
      composableSnd A.groupoid.source.hom A.groupoid.target.hom ≫
        trivialActionMapArrows G A := by
    rw [← Category.assoc, hsnd, Category.assoc]
  have hw := actionCompositionArrow G
    (overHomMk _ (pullback.lift _ _ (trivialActionLiftCondition G A) ≫
      A.compositionDomainIso.hom))
    (pullback.lift _ _ (trivialActionLiftCondition G A) ≫ A.compositionDomainIso.hom) rfl
    (by rw [ha, hb]; exact trivialActionComposable G A)
  change composableToPullback A.groupoid.source.hom A.groupoid.target.hom ≫
    A.groupoid.comp.hom ≫ eqToHom (trivialActionArrows_obj G A) ≫
      (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G = _
  rw [← Category.assoc A.groupoid.comp.hom (eqToHom (trivialActionArrows_obj G A)),
    ← Category.assoc (composableToPullback A.groupoid.source.hom A.groupoid.target.hom), htr,
    ← Category.assoc (pullback.lift _ _ (trivialActionLiftCondition G A))
      A.compositionDomainIso.hom,
    Category.assoc (pullback.lift _ _ (trivialActionLiftCondition G A) ≫
      A.compositionDomainIso.hom)]
  exact hw.trans (groupoidCompose_congr G _ _ ha hb)

/-- The map on object spaces of the comparison is a morphism over the base. -/
theorem trivialActionMapObjects_over :
    trivialActionMapObjects G A ≫ (overObjects G h).objectsToBase.hom =
      A.groupoid.objectsToBase.hom := by
  change eqToHom (trivialActionObjects_obj G A) ≫ 𝟙 G.objects.obj = _
  rw [Category.comp_id, trivialActionObjectsToBase_hom]

/-- The map on arrow spaces of the comparison is a morphism over the base. -/
theorem trivialActionMapArrows_over :
    trivialActionMapArrows G A ≫ (overObjects G h).arrowsToBase.hom =
      A.groupoid.arrowsToBase.hom := by
  change (eqToHom (trivialActionArrows_obj G A) ≫
    (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G) ≫
      G.source.hom = _
  rw [Category.assoc, Category.assoc, stabilizerArrow_source,
    Over.w (fst (stabilizer G) (𝟙_ (Over G.objects.obj))), trivialActionArrowsToBase_hom]

/-- The comparison morphism from the action groupoid of the trivial action of the stabilizer to
the groupoid read over its object space. -/
noncomputable def trivialActionHom : Hom A.groupoid (overObjects G h) :=
  Hom.mk' (trivialActionMapObjects G A) (trivialActionMapArrows G A)
    (fun T a => natTrans_app_congr (trivialActionMapArrows_source G A) T a)
    (fun T a => natTrans_app_congr (trivialActionMapArrows_target G A) T a)
    (fun T a b hab =>
      ((groupoidCompose_eval G
          (composableFst A.groupoid.source.hom A.groupoid.target.hom ≫
            trivialActionMapArrows G A)
          (composableSnd A.groupoid.source.hom A.groupoid.target.hom ≫
            trivialActionMapArrows G A) (trivialActionComposable G A) T
          ⟨(a, b), hab⟩).symm.trans
        (natTrans_app_congr (trivialActionComp_map G A) T ⟨(a, b), hab⟩).symm))
    (trivialActionMapObjects_over G h A) (trivialActionMapArrows_over G h A)

/-- The map on object spaces underlying the comparison morphism. -/
theorem trivialActionHom_mapObjects :
    (trivialActionHom G h A).toGroupoidHom.mapObjects = trivialActionMapObjects G A := rfl

/-- The map on arrow spaces underlying the comparison morphism. -/
theorem trivialActionHom_mapArrows :
    (trivialActionHom G h A).toGroupoidHom.mapArrows = trivialActionMapArrows G A := rfl

/-- The action groupoid of the trivial action of the stabilizer on the object space, which is
**Stacks 0444** at the group object of Stacks 0447. This is the canonical witness of the
hypothesis `A` below. -/
noncomputable def trivialActionGroupoid :
    Space.ActionGroupoidConstruction G.objects (stabilizer G) (𝟙_ (Over G.objects.obj))
      (isAlgebraicSpace_stabilizer G) G.objects.property :=
  Space.groupoidOfAction G.objects (stabilizer G) (𝟙_ (Over G.objects.obj))
    (isAlgebraicSpace_stabilizer G) G.objects.property

/-- **A groupoid with equal source and target is the trivial-action groupoid of its
stabilizer.** Let `G` be a groupoid in algebraic spaces over `B` whose source and target agree.
Its stabilizer is then a group algebraic space over the object space `U` whose underlying
presheaf is the arrow space, and `G`, read as a groupoid over `U`, is the action groupoid of
Stacks 0444 for the trivial action of the stabilizer on `U`. -/
noncomputable def trivialActionIso : Iso A.groupoid (overObjects G h) :=
  Iso.mk' (trivialActionHom G h A) (eqToHom (trivialActionObjects_obj G A).symm)
    (trivialActionInvArrows G h A)
    (by
      rw [trivialActionHom_mapObjects]
      change eqToHom (trivialActionObjects_obj G A) ≫
        eqToHom (trivialActionObjects_obj G A).symm = _
      rw [eqToHom_trans, eqToHom_refl])
    (by
      rw [trivialActionHom_mapObjects]
      change eqToHom (trivialActionObjects_obj G A).symm ≫
        eqToHom (trivialActionObjects_obj G A) = _
      rw [eqToHom_trans, eqToHom_refl]
      rfl)
    (by
      rw [trivialActionHom_mapArrows]
      change (eqToHom (trivialActionArrows_obj G A) ≫
          (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G) ≫
        ((stabilizerArrowIso G h).inv ≫ (ρ_ (stabilizer G)).inv.left ≫
          eqToHom (trivialActionArrows_obj G A).symm) = _
      rw [Category.assoc, Category.assoc,
        ← Category.assoc (stabilizerArrow G), ← stabilizerArrowIso_hom G h,
        (stabilizerArrowIso G h).hom_inv_id, Category.id_comp,
        ← Category.assoc (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left,
        trivialActionFst_unitorInv, Category.id_comp, eqToHom_trans, eqToHom_refl])
    (by
      rw [trivialActionHom_mapArrows]
      change ((stabilizerArrowIso G h).inv ≫ (ρ_ (stabilizer G)).inv.left ≫
          eqToHom (trivialActionArrows_obj G A).symm) ≫
        (eqToHom (trivialActionArrows_obj G A) ≫
          (fst (stabilizer G) (𝟙_ (Over G.objects.obj))).left ≫ stabilizerArrow G) = _
      rw [Category.assoc, Category.assoc,
        ← Category.assoc (eqToHom (trivialActionArrows_obj G A).symm), eqToHom_trans,
        eqToHom_refl, Category.id_comp,
        ← Category.assoc (ρ_ (stabilizer G)).inv.left, trivialActionUnitorInv_fst,
        Category.id_comp, ← stabilizerArrowIso_hom G h, (stabilizerArrowIso G h).inv_hom_id]
      rfl)

end TrivialAction

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
