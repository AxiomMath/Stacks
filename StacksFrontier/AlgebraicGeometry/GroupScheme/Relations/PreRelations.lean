module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.Topology.Separation.KolmogorovQuotient
public import StacksCore.Tactic.StacksAttribute

/-!
# Equivalence relations: internal characterization, points, and restriction

An internal equivalence relation on a scheme over a base is exactly a monic pre-relation whose
induced relation on `T`-valued points is an equivalence relation for every `T`. A
pre-equivalence relation induces an equivalence relation on the underlying points of the
scheme. A pre-relation can also be restricted along a morphism to the scheme it lives on: the
restriction is the pullback of the pre-relation along the product of the morphism with itself,
and it preserves relations, pre-equivalence relations and equivalence relations.

## Main definitions

* `AlgebraicGeometry.PreRelation.restriction` is the scheme of the restricted pre-relation.
* `AlgebraicGeometry.PreRelation.restrict` is the restricted pre-relation.

## Main results

* `Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation` identifies the
  internal and pointwise forms of being an equivalence relation.
* `AlgebraicGeometry.PreRelation.equivalence_sourceTargetRel` states that a pre-equivalence
  relation induces an equivalence relation on points.
* `AlgebraicGeometry.PreRelation.isPreEquivalenceRelation_restrict` and
  `AlgebraicGeometry.PreRelation.isEquivalenceRelation_restrict` say that restriction preserves
  pre-equivalence relations and equivalence relations.

## Implementation notes

`CategoryTheory.IsEquivalenceRelation`, applied to the target and source maps, is the internal
categorical form of the condition that the induced relation on every set of `T`-valued points
is an equivalence relation; the pointwise condition without monicity is retained separately as
`Stacks.Groupoids.IsPreEquivalenceRelation`. The characterization theorem proves that the
internal and pointwise forms agree, and lives in the namespace of that vocabulary.

`Function.SourceTargetRel` states the relation on points in the source; the second theorem
applies it to the maps on underlying points induced by the source and target morphisms of a
pre-relation. Its proof runs through field-valued points: a `T`-valued point of the relation
is produced from a field-valued point of the scheme, and `Spec` of a common extension field
realizes transitivity.

The product in `Over S` is the fibre product over `S`. Thus the restricted scheme is the
categorical pullback of `prod.map g g` and `j`, and its map to the product is the first
pullback projection. Preservation of monomorphisms by this construction is the general
categorical theorem `CategoryTheory.Limits.pullback.fst_of_mono`.

## References

* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Tag 022Q](https://stacks.math.columbia.edu/tag/022Q)
* [Stacks Project, Tag 02V8](https://stacks.math.columbia.edu/tag/02V8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

/-- An internal equivalence relation is exactly a monic pre-relation whose
relation on `T`-valued points is an equivalence relation for every `T`. -/
theorem isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation
    {S : AlgebraicGeometry.Scheme.{u}} {R U : Over S} (j : PreRelation R U) :
    CategoryTheory.IsEquivalenceRelation j.target j.source ↔
      (CategoryTheory.Mono j ∧ IsPreEquivalenceRelation j) := by
  constructor
  · rintro ⟨⟨e⟩⟩
    constructor
    · constructor
      intro T f g h
      apply e.right_cancellation
      · simpa [PreRelation.target, Category.assoc] using congrArg (fun k => k ≫ prod.fst) h
      · simpa [PreRelation.source, Category.assoc] using congrArg (fun k => k ≫ prod.snd) h
    · intro T
      constructor
      · intro x
        exact ⟨x ≫ e.r, by simp [Category.assoc], by simp [Category.assoc]⟩
      · intro x y hxy
        rcases hxy with ⟨r, hr₁, hr₂⟩
        exact ⟨r ≫ e.s, by rw [Category.assoc, e.symmetry₁, hr₂],
          by rw [Category.assoc, e.symmetry₂, hr₁]⟩
      · intro x y z hxy hyz
        rcases hxy with ⟨r, hr₁, hr₂⟩
        rcases hyz with ⟨r', hr₁', hr₂'⟩
        let l := PullbackCone.IsLimit.lift e.isLimit r r' (hr₂.trans hr₁'.symm)
        refine ⟨l ≫ e.t, ?_, ?_⟩
        · rw [Category.assoc, e.transitivity₁, ← Category.assoc,
            PullbackCone.IsLimit.lift_fst, hr₁]
        · rw [Category.assoc, e.transitivity₂, ← Category.assoc,
            PullbackCone.IsLimit.lift_snd, hr₂']
  · rintro ⟨hj, he⟩
    let _ : CategoryTheory.Mono j := hj
    have h_joint : CategoryTheory.JointlyMono₂ j.target j.source := by
      constructor
      intro T f g h₁ h₂
      apply (cancel_mono j).mp
      apply prod.hom_ext
      · simpa [PreRelation.target, Category.assoc] using h₁
      · simpa [PreRelation.source, Category.assoc] using h₂
    rcases (he U).refl (𝟙 U) with ⟨r, hr₁, hr₂⟩
    have h_self : j.Rel j.target j.source := ⟨𝟙 R, by simp, by simp⟩
    rcases (he R).symm h_self with ⟨s, hs₁, hs₂⟩
    rcases (he (pullback j.source j.target)).trans
      ⟨pullback.fst j.source j.target, rfl, rfl⟩
      ⟨pullback.snd j.source j.target, pullback.condition.symm, rfl⟩ with ⟨t, ht₁, ht₂⟩
    let h_refl : ReflexiveRelation j.target j.source :=
      { toJointlyMono₂ := h_joint, r := r, reflexivity₁ := hr₁, reflexivity₂ := hr₂ }
    let h_symm : SymmetricRelation j.target j.source :=
      { toJointlyMono₂ := h_joint, s := s, symmetry₁ := hs₁, symmetry₂ := hs₂ }
    let h_trans : TransitiveRelation j.target j.source :=
      { toJointlyMono₂ := h_joint, c := pullback.cone j.source j.target,
        isLimit := pullback.isLimit j.source j.target, t := t,
        transitivity₁ := ht₁, transitivity₂ := ht₂ }
    exact EquivalenceRelation.isEquivalenceRelation
      { __ := h_refl
        __ := h_symm
        __ := h_trans }

end Stacks.Groupoids

namespace AlgebraicGeometry

add_to_stacks 022Q "the relation on points" Function.SourceTargetRel

variable {S : Scheme.{u}}

namespace PreRelation

/-- A field-valued point of an `S`-scheme, regarded as an `S`-scheme itself. -/
private noncomputable def pointOver {X : Over S} (p : FieldValuedPoint X.left) : Over S :=
  Over.mk (p.map ≫ X.hom)

/-- A field-valued point of an `S`-scheme, regarded as a morphism of `S`-schemes. -/
private noncomputable def pointHom {X : Over S} (p : FieldValuedPoint X.left) :
    pointOver p ⟶ X :=
  Over.homMk p.map

private lemma pointHom_point {X : Over S} (p : FieldValuedPoint X.left) :
    (pointHom p).left.base (IsLocalRing.closedPoint p.carrier) = p.point := rfl

private lemma pointHom_comp_point {X Y : Over S} (p : FieldValuedPoint X.left) (f : X ⟶ Y) :
    (pointHom p ≫ f).left.base (IsLocalRing.closedPoint p.carrier) = f.left.base p.point := rfl

/-- The image of a field-valued point under a morphism of schemes. -/
private noncomputable def mapFieldPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : FieldValuedPoint X) : FieldValuedPoint Y where
  carrier := p.carrier
  map := p.map ≫ f

private lemma mapFieldPoint_point {X Y : Scheme.{u}} (f : X ⟶ Y) (p : FieldValuedPoint X) :
    (mapFieldPoint f p).point = f.base p.point :=
  rfl

private lemma canonicalFieldPoint_point {X : Scheme.{u}} (x : X) :
    (FieldValuedPoint.canonical X x).point = x :=
  Scheme.fromSpecResidueField_apply x _

private lemma point_eq_of_dominates {X : Scheme.{u}}
    {p q : FieldValuedPoint X} (h : p.Dominates q) : p.point = q.point :=
  (FieldValuedPoint.hasCommonExtension_iff_point_eq p q).mp ⟨p, ⟨𝟙 _, by simp⟩, h⟩

private lemma mapFieldPoint_canonical_point {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    (mapFieldPoint f (FieldValuedPoint.canonical X x)).point = f.base x := by
  rw [mapFieldPoint_point, canonicalFieldPoint_point]

/-- A field-valued point of `U` lifted through a morphism `g : R ⟶ U` along a factorization
of its map. -/
private noncomputable def liftPointMap {R U : Over S} (g : R ⟶ U)
    (q : FieldValuedPoint R.left) (p : FieldValuedPoint U.left)
    (f : Spec (.of p.carrier) ⟶ Spec (.of q.carrier))
    (h : f ≫ q.map ≫ g.left = p.map) : pointOver p ⟶ R :=
  Over.homMk (f ≫ q.map) (by
    calc
      (f ≫ q.map) ≫ R.hom = (f ≫ q.map ≫ g.left) ≫ U.hom := by
        rw [← g.w]
        simp [Category.assoc]
      _ = p.map ≫ U.hom := by rw [h])

private lemma liftPointMap_comp {R U : Over S} (g : R ⟶ U)
    (q : FieldValuedPoint R.left) (p : FieldValuedPoint U.left)
    (f : Spec (.of p.carrier) ⟶ Spec (.of q.carrier))
    (h : f ≫ q.map ≫ g.left = p.map) :
    liftPointMap g q p f h ≫ g = pointHom p := by
  ext
  exact h

/-- Composing a lifted point with `k` gives a point with the same image as the lifted point
under `k`. -/
private lemma liftPointMap_point {R U V : Over S} (g : R ⟶ U) (k : R ⟶ V)
    (q : FieldValuedPoint R.left) (p : FieldValuedPoint U.left)
    (f : Spec (.of p.carrier) ⟶ Spec (.of q.carrier))
    (h : f ≫ q.map ≫ g.left = p.map) :
    (⟨p.carrier, (liftPointMap g q p f h ≫ k).left⟩ : FieldValuedPoint V.left).point =
      (mapFieldPoint k.left q).point :=
  point_eq_of_dominates ⟨f, (Category.assoc _ _ _).symm⟩

private lemma point_rel_of_rel {R U X : Over S} (j : Stacks.Groupoids.PreRelation R U)
    (p : FieldValuedPoint X.left) {a b : pointOver p ⟶ U}
    (h : j.Rel a b) :
    Function.SourceTargetRel j.source.left.base j.target.left.base
      (a.left.base (IsLocalRing.closedPoint p.carrier))
      (b.left.base (IsLocalRing.closedPoint p.carrier)) := by
  rcases h with ⟨r, hrt, hrs⟩
  let c : (pointOver p).left := IsLocalRing.closedPoint p.carrier
  change Spec (.of p.carrier) at c
  refine ⟨r.left.base c, ?_, ?_⟩
  · show j.target.left.base (r.left.base c) = a.left.base c
    show (r.left ≫ j.target.left) c = a.left.base c
    exact congrArg (fun f : _ => f c) (congrArg (fun f : pointOver p ⟶ U => f.left) hrt)
  · show j.source.left.base (r.left.base c) = b.left.base c
    show (r.left ≫ j.source.left) c = b.left.base c
    exact congrArg (fun f : _ => f c) (congrArg (fun f : pointOver p ⟶ U => f.left) hrs)

/-- **Stacks Project, Tag 022Q.** A pre-equivalence relation induces an equivalence relation on
the underlying points of the scheme. -/
@[stacks 022Q]
theorem equivalence_sourceTargetRel {R U : Over S} (j : Stacks.Groupoids.PreRelation R U)
    (hj : Stacks.Groupoids.IsPreEquivalenceRelation j) :
    Equivalence (Function.SourceTargetRel j.source.left.base j.target.left.base) := by
  constructor
  · intro x
    let p := FieldValuedPoint.canonical U.left x
    have hrel : j.Rel (pointHom p) (pointHom p) := (hj (pointOver p)).refl _
    have hpoint := point_rel_of_rel j p hrel
    rw [pointHom_point] at hpoint
    simpa [p, canonicalFieldPoint_point] using hpoint
  · intro x y hxy
    rcases hxy with ⟨r, hrt, hrs⟩
    let q := FieldValuedPoint.canonical R.left r
    let qt := mapFieldPoint j.target.left q
    let qs := mapFieldPoint j.source.left q
    have hqt : qt.point = x := (mapFieldPoint_canonical_point _ _).trans hrt
    have hqs : qs.point = y := (mapFieldPoint_canonical_point _ _).trans hrs
    have hrel : j.Rel (pointHom q ≫ j.target) (pointHom q ≫ j.source) :=
      ⟨pointHom q, rfl, rfl⟩
    have hsym := (hj (pointOver q)).symm hrel
    have hpoint := point_rel_of_rel j q hsym
    rw [pointHom_comp_point, pointHom_comp_point] at hpoint
    rw [← hqt, ← hqs]
    exact hpoint
  · intro x y z hxy hyz
    rcases hxy with ⟨r₁, hr₁t, hr₁s⟩
    rcases hyz with ⟨r₂, hr₂t, hr₂s⟩
    let q₁ := FieldValuedPoint.canonical R.left r₁
    let q₂ := FieldValuedPoint.canonical R.left r₂
    let q₁t := mapFieldPoint j.target.left q₁
    let q₁s := mapFieldPoint j.source.left q₁
    let q₂t := mapFieldPoint j.target.left q₂
    let q₂s := mapFieldPoint j.source.left q₂
    have hq₁t : q₁t.point = x := (mapFieldPoint_canonical_point _ _).trans hr₁t
    have hq₁s : q₁s.point = y := (mapFieldPoint_canonical_point _ _).trans hr₁s
    have hq₂t : q₂t.point = y := (mapFieldPoint_canonical_point _ _).trans hr₂t
    have hq₂s : q₂s.point = z := (mapFieldPoint_canonical_point _ _).trans hr₂s
    have hmid : q₁s.point = q₂t.point := hq₁s.trans hq₂t.symm
    rcases (FieldValuedPoint.hasCommonExtension_iff_point_eq q₁s q₂t).2 hmid with
      ⟨p, ⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩⟩
    let r₁' := liftPointMap j.source q₁ p f₁ hf₁
    let r₂' := liftPointMap j.target q₂ p f₂ hf₂
    have h₁ : j.Rel (r₁' ≫ j.target) (pointHom p) :=
      ⟨r₁', rfl, liftPointMap_comp j.source q₁ p f₁ hf₁⟩
    have h₂ : j.Rel (pointHom p) (r₂' ≫ j.source) :=
      ⟨r₂', liftPointMap_comp j.target q₂ p f₂ hf₂, rfl⟩
    have htr := (hj (pointOver p)).trans h₁ h₂
    let xExt : FieldValuedPoint U.left :=
      { carrier := p.carrier, map := (r₁' ≫ j.target).left }
    let zExt : FieldValuedPoint U.left :=
      { carrier := p.carrier, map := (r₂' ≫ j.source).left }
    have hfinal : Function.SourceTargetRel j.source.left.base j.target.left.base
        xExt.point zExt.point :=
      point_rel_of_rel j p htr
    have hx : xExt.point = x := (liftPointMap_point j.source j.target q₁ p f₁ hf₁).trans hq₁t
    have hz : zExt.point = z := (liftPointMap_point j.target j.source q₂ p f₂ hf₂).trans hq₂s
    simpa [hx, hz] using hfinal

variable {R U U' : Over S} (j : Stacks.Groupoids.PreRelation R U)

/-- The scheme underlying the restriction of a pre-relation along `g`. -/
noncomputable abbrev restriction (g : U' ⟶ U) : Over S :=
  pullback (prod.map g g) j

/-- The restriction of a pre-relation along `g`. -/
@[stacks 02V8 "the restricted pre-relation",
  stacks 02V9 "the restriction R|_{U'} of a pre-relation along U' -> U"]
noncomputable abbrev restrict (g : U' ⟶ U) :
    Stacks.Groupoids.PreRelation (restriction j g) U' :=
  pullback.fst (prod.map g g) j

add_to_stacks 02V8 "preservation of relations" CategoryTheory.Limits.pullback.fst_of_mono
add_to_ega "I 3.3.12" "more general" CategoryTheory.Limits.pullback.fst_of_mono

/-- Restriction preserves pre-equivalence relations. -/
@[stacks 02V8 "preservation of pre-equivalence relations"]
theorem isPreEquivalenceRelation_restrict (g : U' ⟶ U)
    (hj : Stacks.Groupoids.IsPreEquivalenceRelation j) :
    Stacks.Groupoids.IsPreEquivalenceRelation (restrict j g) := by
  intro T
  let liftRel : ∀ {x y : T ⟶ U'}, j.Rel (x ≫ g) (y ≫ g) → (restrict j g).Rel x y := by
    rintro x y ⟨r, hr₁, hr₂⟩
    have hcomm : prod.lift x y ≫ prod.map g g = r ≫ j := by
      apply prod.hom_ext
      all_goals simp [Category.assoc, hr₁, hr₂]
    refine ⟨pullback.lift (prod.lift x y) r hcomm, ?_, ?_⟩
    all_goals rw [← Category.assoc, pullback.lift_fst]; simp
  let forgetRel : ∀ {x y : T ⟶ U'},
      (restrict j g).Rel x y → j.Rel (x ≫ g) (y ≫ g) := by
    rintro x y ⟨r, hr₁, hr₂⟩
    refine ⟨r ≫ pullback.snd (prod.map g g) j, ?_, ?_⟩
    all_goals rw [Category.assoc, ← pullback.condition_assoc]
    · simpa [restrict, Category.assoc] using congrArg (fun k => k ≫ g) hr₁
    · simpa [restrict, Category.assoc] using congrArg (fun k => k ≫ g) hr₂
  exact ⟨fun x => liftRel ((hj T).refl (x ≫ g)),
    fun {_ _} h => liftRel ((hj T).symm (forgetRel h)),
    fun {_ _ _} hxy hyz => liftRel ((hj T).trans (forgetRel hxy) (forgetRel hyz))⟩

/-- Restriction preserves equivalence relations. -/
@[stacks 02V8 "preservation of equivalence relations"]
instance isEquivalenceRelation_restrict (g : U' ⟶ U)
    [hj : CategoryTheory.IsEquivalenceRelation j.target j.source] :
    CategoryTheory.IsEquivalenceRelation (restrict j g).target (restrict j g).source := by
  rw [Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation] at hj ⊢
  let _ : Mono j := hj.1
  exact ⟨inferInstance, isPreEquivalenceRelation_restrict j g hj.2⟩

end PreRelation

end AlgebraicGeometry
