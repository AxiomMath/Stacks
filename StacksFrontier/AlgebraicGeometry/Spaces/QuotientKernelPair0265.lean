module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Logic.Relation
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.KernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relation of a pre-relation is the kernel pair of its quotient presheaf

Let `j` be a pre-relation from `R` to `U` over a base scheme `S`, presented on a site of
`S`-schemes by a functor `F`. Its quotient presheaf identifies two `T`-valued points of `U`
exactly when they are related, provided the induced relations on points are equivalence
relations; and if moreover `j` is a monomorphism, the relation is *the kernel pair* of the
projection onto the quotient presheaf: the square formed by the target and source maps on
functors of points and two copies of the projection is a pullback square.

## Main definitions

* `Stacks.Groupoids.PreRelation.relLift` is the chosen `T`-valued point of `R` witnessing a
  relation between two `T`-valued points of `U`.
* `Stacks.Groupoids.relQuotient` is the presheaf whose value at `X` is the quotient of the
  `F.obj X`-valued points of `U` by the relation induced by `j`, and
  `Stacks.Groupoids.toRelQuotient` is its canonical projection.

## Main results

* `Stacks.Groupoids.PreRelation.mono_of_isEquivalenceRelation` and
  `Stacks.Groupoids.PreRelation.isPreEquivalenceRelation_of_isEquivalenceRelation` derive
  monicity and the pointwise equivalence condition from the internal
  equivalence-relation structure.
* `Stacks.Groupoids.toQuotientPresheaf_app_eq_iff`: two points of `U` have the same image in
  the quotient presheaf if and only if they are related.
* `Stacks.Groupoids.isPullback_toQuotientPresheaf_self_of_isPreEquivalenceRelation`: for a
  pre-equivalence relation which is a monomorphism, the relation is the kernel pair of the
  projection onto the quotient presheaf;
  `Stacks.Groupoids.isPullback_toQuotientPresheaf_of_isEquivalenceRelation` is the same
  conclusion with both hypotheses discharged from the internal structure, hence available for
  an étale equivalence relation.

## Implementation notes

The value of the quotient presheaf at `X` is the quotient of `Hom(F.obj X, U)` by the
relation *generated* by the pairs `(r ≫ j.source, r ≫ j.target)`, so recovering a relation
from an equality of classes needs the generated equivalence relation to collapse. Rather
than transport the pointwise description of a coequalizer of types across the evaluation
functor, the collapse is obtained from the universal property in the presheaf category
itself: `Stacks.Groupoids.relQuotient` is the quotient by the induced relation, which is
already an equivalence relation at every object and is functorial because the relation is
stable under precomposition, so the projection onto it factors through the quotient presheaf
and detects equality of classes. No pointwise description of the coequalizer, and hence no
preservation of colimits by evaluation, is used.

Monicity of `j` enters only through
`Stacks.Groupoids.PreRelation.eq_of_target_eq_of_source_eq`: it makes the witness of a
relation unique, which is what turns the surjection of
`Stacks.Groupoids.toQuotientPresheaf_app_eq_iff` into a bijection and so lets the lift of a
pullback cone be defined objectwise and be natural. The equivalence-relation hypothesis is
the pointwise `Stacks.Groupoids.IsPreEquivalenceRelation` rather than the internal
`CategoryTheory.IsEquivalenceRelation`; only symmetry and the equivalence of the induced
relations are used, never reflexivity or transitivity of the internal structure.

## References

* [Stacks Project, Tag 02VG](https://stacks.math.columbia.edu/tag/02VG)
* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Groupoids

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]

namespace PreRelation

variable {R U : Over S} (j : PreRelation R U)

/-- A point of `R` is determined by its target and its source as soon as the pre-relation is
a monomorphism: the two maps to `U` are the composites of `j` with the two projections, so
agreeing on both means agreeing after composing with `j`. -/
theorem eq_of_target_eq_of_source_eq [Mono j] {T : Over S} {r r' : T ⟶ R}
    (ht : r ≫ j.target = r' ≫ j.target) (hs : r ≫ j.source = r' ≫ j.source) : r = r' :=
  (cancel_mono j).1 (prod.hom_ext (by simpa using ht) (by simpa using hs))

/-- **A pre-relation carrying an internal equivalence-relation structure is a
monomorphism.** The target and source maps are jointly monic, and they are the composites of
the pre-relation with the two projections of the product, so agreeing after composing with
the pre-relation forces agreement. -/
theorem mono_of_isEquivalenceRelation [IsEquivalenceRelation j.target j.source] : Mono j := by
  obtain ⟨e⟩ :=
    IsEquivalenceRelation.nonempty_equivalenceRelation (p₁ := j.target) (p₂ := j.source)
  refine ⟨fun a b hab => e.right_cancellation a b ?_ ?_⟩
  · simpa using congrArg (· ≫ prod.fst) hab
  · simpa using congrArg (· ≫ prod.snd) hab

/-- **An internal equivalence-relation structure induces an equivalence relation on the
points of `U` over every `S`-scheme.** Reflexivity, symmetry and transitivity of the induced
relation are witnessed by composing a point with the reflexivity section, with the symmetry
automorphism, and with the transitivity map out of the limiting pullback cone. -/
theorem isPreEquivalenceRelation_of_isEquivalenceRelation
    [IsEquivalenceRelation j.target j.source] : IsPreEquivalenceRelation j := by
  obtain ⟨e⟩ :=
    IsEquivalenceRelation.nonempty_equivalenceRelation (p₁ := j.target) (p₂ := j.source)
  refine fun T => ⟨fun x => ⟨x ≫ e.r, by simp, by simp⟩, ?_, ?_⟩
  · rintro x y ⟨r, hx, hy⟩
    exact ⟨r ≫ e.s, by rw [Category.assoc, e.symmetry₁, hy],
      by rw [Category.assoc, e.symmetry₂, hx]⟩
  · rintro x y z ⟨r₁, hx₁, hy₁⟩ ⟨r₂, hy₂, hz₂⟩
    have hc : r₁ ≫ j.source = r₂ ≫ j.target := by rw [hy₁, hy₂]
    refine ⟨PullbackCone.IsLimit.lift e.isLimit r₁ r₂ hc ≫ e.t, ?_, ?_⟩
    · rw [Category.assoc, e.transitivity₁, ← Category.assoc,
        PullbackCone.IsLimit.lift_fst, hx₁]
    · rw [Category.assoc, e.transitivity₂, ← Category.assoc,
        PullbackCone.IsLimit.lift_snd, hz₂]

/-- The relation induced on points is stable under precomposition. -/
theorem rel_comp {T T' : Over S} (g : T' ⟶ T) {x y : T ⟶ U} (h : j.Rel x y) :
    j.Rel (g ≫ x) (g ≫ y) := by
  obtain ⟨r, hx, hy⟩ := h
  exact ⟨g ≫ r, by rw [Category.assoc, hx], by rw [Category.assoc, hy]⟩

/-- A chosen point of `R` witnessing that two points of `U` are related. -/
noncomputable def relLift {T : Over S} {x y : T ⟶ U} (h : j.Rel x y) : T ⟶ R := h.choose

/-- The chosen witness `relLift h` has target the first of the two related points. -/
@[simp]
theorem relLift_target {T : Over S} {x y : T ⟶ U} (h : j.Rel x y) :
    j.relLift h ≫ j.target = x := h.choose_spec.1

/-- The chosen witness `relLift h` has source the second of the two related points. -/
@[simp]
theorem relLift_source {T : Over S} {x y : T ⟶ U} (h : j.Rel x y) :
    j.relLift h ≫ j.source = y := h.choose_spec.2

/-- For a monomorphic pre-relation the witness of a relation is unique, so every witness is
the chosen one. -/
theorem eq_relLift [Mono j] {T : Over S} {x y : T ⟶ U} (h : j.Rel x y) (r : T ⟶ R)
    (ht : r ≫ j.target = x) (hs : r ≫ j.source = y) : r = j.relLift h :=
  eq_of_target_eq_of_source_eq j (by rw [ht, relLift_target]) (by rw [hs, relLift_source])

end PreRelation

section RelQuotient

variable (F : C ⥤ Over S) {R U : Over S} (j : PreRelation R U)

/-- The presheaf whose value at `X` is the quotient of the `F.obj X`-valued points of `U` by
the relation induced by the pre-relation `j`. The relation is stable under precomposition, so
the restriction maps descend to the quotients. -/
noncomputable def relQuotient : Cᵒᵖ ⥤ Type u where
  obj X := Quot (j.Rel (T := F.obj X.unop))
  map {X _} g := ↾(Quot.lift (fun x : (points F U).obj X => Quot.mk _ (F.map g.unop ≫ x))
    fun _ _ h => Quot.sound (j.rel_comp (F.map g.unop) h))
  map_id _ := by
    ext x
    induction x using Quot.ind with
    | _ x => simp
  map_comp _ _ := by
    ext x
    induction x using Quot.ind with
    | _ x => simp

/-- The canonical projection from the restricted functor of points of `U` onto the quotient
by the relation induced by `j`. -/
noncomputable def toRelQuotient : points F U ⟶ relQuotient F j where
  app X := ↾(fun x : (points F U).obj X => Quot.mk (j.Rel (T := F.obj X.unop)) x)
  naturality _ _ _ := by ext x; rfl

/-- The projection `toRelQuotient` sends a point to its class under the induced relation. -/
@[simp]
theorem toRelQuotient_app_apply (X : Cᵒᵖ) (x : (points F U).obj X) :
    (toRelQuotient F j).app X x = Quot.mk (j.Rel (T := F.obj X.unop)) x := rfl

/-- The projection onto the quotient by the induced relation coequalizes the source and the
target maps on functors of points: a point `r` of `R` relates its target to its source, and
the induced relations are symmetric. -/
theorem sourceMap_toRelQuotient (hj : IsPreEquivalenceRelation j) :
    sourceMap F j ≫ toRelQuotient F j = targetMap F j ≫ toRelQuotient F j := by
  ext X r
  exact Quot.sound ((hj (F.obj X.unop)).symm ⟨r, rfl, rfl⟩)

/-- Equal morphisms of presheaves of types agree on every element. -/
private theorem congr_app_apply {P Q : Cᵒᵖ ⥤ Type u} {f g : P ⟶ Q} (h : f = g) (X : Cᵒᵖ)
    (x : P.obj X) : f.app X x = g.app X x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app h X) x

/-- The map from the quotient presheaf to the quotient by the induced relation given by the
universal property of the coequalizer. -/
noncomputable def relQuotientDesc (hj : IsPreEquivalenceRelation j) :
    quotientPresheaf F j ⟶ relQuotient F j :=
  coequalizer.desc (toRelQuotient F j) (sourceMap_toRelQuotient F j hj)

/-- The map `relQuotientDesc` sends the class in the quotient presheaf of a point to its class
under the induced relation. -/
@[simp]
theorem relQuotientDesc_toQuotientPresheaf_apply (hj : IsPreEquivalenceRelation j) (X : Cᵒᵖ)
    (x : (points F U).obj X) :
    (relQuotientDesc F j hj).app X ((toQuotientPresheaf F j).app X x) =
      Quot.mk (j.Rel (T := F.obj X.unop)) x := by
  have h := coequalizer.π_desc (toRelQuotient F j) (sourceMap_toRelQuotient F j hj)
  exact congr_app_apply h X x

/-- **Two points of `U` have the same image in the quotient presheaf exactly when they are
related.** The nontrivial direction is that the equivalence relation generated by the pairs
`(r ≫ j.source, r ≫ j.target)` is no larger than the induced relation, which holds because
the latter is already an equivalence relation at every object and the projection onto the
quotient by it factors through the quotient presheaf. -/
@[sga "3 IV 3.1.2" "partial"]
theorem toQuotientPresheaf_app_eq_iff (hj : IsPreEquivalenceRelation j) {X : Cᵒᵖ}
    {x y : (points F U).obj X} :
    (toQuotientPresheaf F j).app X x = (toQuotientPresheaf F j).app X y ↔ j.Rel x y := by
  refine ⟨fun h => (hj (F.obj X.unop)).eqvGen_iff.1 (Quot.eqvGen_exact ?_), ?_⟩
  · rw [← relQuotientDesc_toQuotientPresheaf_apply F j hj X x,
      ← relQuotientDesc_toQuotientPresheaf_apply F j hj X y, h]
  · rintro ⟨r, rfl, rfl⟩
    simpa using (congr_app_apply (coequalizer.condition (sourceMap F j) (targetMap F j)) X r).symm

/-- **The relation induced by a monomorphic pre-equivalence relation is the kernel pair of
the projection onto its quotient presheaf.** Two points of `U` have the same image in the
quotient presheaf exactly when they are the target and the source of a point of `R`, and
monicity makes that point unique, so the square of the target and source maps against two
copies of the projection is cartesian.

This is the presheaf-level content of the étale-equivalence-relation quotient: the kernel
pair of the quotient map is the relation one started from.

The name carries `_self` because the cartesian square is the one formed by the projection onto
the quotient presheaf with itself, as in
`Stacks.Groupoids.isPullback_toQuotientPresheaf_self`, whose hypothesis is the internal
equivalence-relation structure instead; `Stacks.Groupoids.isPullback_toQuotientPresheaf` is an
unrelated square, between the quotient presheaves of two different pre-relations. -/
theorem isPullback_toQuotientPresheaf_self_of_isPreEquivalenceRelation
    [Mono j] (hj : IsPreEquivalenceRelation j) :
    IsPullback (targetMap F j) (sourceMap F j) (toQuotientPresheaf F j)
      (toQuotientPresheaf F j) := by
  have hrel (s : PullbackCone (toQuotientPresheaf F j) (toQuotientPresheaf F j)) (X : Cᵒᵖ)
      (z : s.pt.obj X) : j.Rel (s.fst.app X z) (s.snd.app X z) :=
    (toQuotientPresheaf_app_eq_iff F j hj).1 (congr_app_apply s.condition X z)
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (coequalizer.condition (sourceMap F j) (targetMap F j)).symm
    (fun s => { app := fun X => ↾(fun z => j.relLift (hrel s X z)), naturality := ?_ })
    (fun s => ?_) (fun s => ?_) (fun s m hfst hsnd => ?_))
  · intro X Y g
    ext z
    refine (j.eq_relLift (hrel s Y (s.pt.map g z)) _ ?_ ?_).symm
    · show (F.map g.unop ≫ j.relLift (hrel s X z)) ≫ j.target = _
      rw [Category.assoc, PreRelation.relLift_target]
      exact (ConcreteCategory.congr_hom (s.fst.naturality g) z).symm
    · show (F.map g.unop ≫ j.relLift (hrel s X z)) ≫ j.source = _
      rw [Category.assoc, PreRelation.relLift_source]
      exact (ConcreteCategory.congr_hom (s.snd.naturality g) z).symm
  · ext X z
    exact PreRelation.relLift_target j (hrel s X z)
  · ext X z
    exact PreRelation.relLift_source j (hrel s X z)
  · ext X z
    exact j.eq_relLift (hrel s X z) _ (congr_app_apply hfst X z) (congr_app_apply hsnd X z)

/-- **The kernel pair of the projection onto the quotient presheaf of an internal equivalence
relation is the relation itself.** This is
`Stacks.Groupoids.isPullback_toQuotientPresheaf_self_of_isPreEquivalenceRelation`
with both of its hypotheses discharged from the internal equivalence-relation structure, and
so applies verbatim to an étale equivalence relation, whose defining structure includes
`CategoryTheory.IsEquivalenceRelation` of the target and source maps. Alias of
`Stacks.Groupoids.isPullback_toQuotientPresheaf_self`. -/
alias isPullback_toQuotientPresheaf_of_isEquivalenceRelation :=
  isPullback_toQuotientPresheaf_self

end RelQuotient

end Stacks.Groupoids

end
