module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationsOverSpace
public import StacksFrontier.Topology.Separation.KolmogorovQuotient

/-!
# The relation on points cut out by a pre-relation

Let `j : R ⟶ U ×_Z U` be a pre-relation on a presheaf `U` over a base presheaf `Z` on the big
fppf site of a scheme `S`. Its target and source maps induce maps `|R| → |U|` on the sets of
points, and therefore a binary relation on `|U|`: a point `x` is related to a point `y` when
some point `r` of `R` has `t(r) = x` and `s(r) = y`. When `j` is a pre-equivalence relation
this relation on `|U|` is an equivalence relation.

## Main results

* `AlgebraicGeometry.Space.PreRelation.isPreEquivalenceRelation_sourceTargetRel`: the relation
  induced on `|U|` by a pre-equivalence relation is an equivalence relation.

## Implementation notes

The relation on `|U|` is `Function.SourceTargetRel` applied to the two induced maps
`|R| → |U|`, in the order `(source, target)`, so that `x` is related to `y` when
`∃ r, t(r) = x ∧ s(r) = y`.

Everything is stated for an arbitrary presheaf `Z` as base and for arbitrary objects of
`CategoryTheory.Over Z`, as for `AlgebraicGeometry.Space.PreRelation`; the algebraic-space
axioms are not used.

## References

* [Stacks Project, Tag 043F](https://stacks.math.columbia.edu/tag/043F)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

namespace PreRelation

/-! ### Test points and field-valued points -/

/-- The field-valued point of `X.left` underlying a test point of `X` over a field-valued
point `p` of the base: the same field, the same structure map, and the section of `X.left`
which the test point is. -/
private noncomputable def testPointRepresentative {X : Over Z}
    (p : FieldValuedPoint B S hS Z)
    (x : TestPoint (p.siteObject B S hS Z) (yonedaEquiv.symm p.value) X) :
    FieldValuedPoint B S hS X.left where
  carrier := p.carrier
  field := p.field
  contained := p.contained
  toBase := p.toBase
  value := yonedaEquiv x.1

/-- A test point of `X` over `p` has `p` as its image in the base. -/
private theorem testPoint_base_value {X : Over Z} (p : FieldValuedPoint B S hS Z)
    (x : TestPoint (p.siteObject B S hS Z) (yonedaEquiv.symm p.value) X) :
    X.hom.app (op (p.siteObject B S hS Z)) (yonedaEquiv x.1) = p.value := by
  rw [← yonedaEquiv_comp, x.2]
  simp

/-- Pushing a test point forward along a morphism over the base and then taking its
field-valued representative agrees with pushing the representative forward. -/
private theorem testPointRepresentative_class_map {X Y : Over Z} (g : X ⟶ Y)
    (p : FieldValuedPoint B S hS Z)
    (x : TestPoint (p.siteObject B S hS Z) (yonedaEquiv.symm p.value) X) :
    (FieldValuedPoint.map B S hS X.left g.left (testPointRepresentative p x)).class
        B S hS Y.left =
      (testPointRepresentative p (mapTestPoint g x)).class B S hS Y.left := by
  change pointsMap B S hS X.left g.left
    ((testPointRepresentative p x).class B S hS X.left) = _
  rw [pointsMap_class]
  apply Quot.sound
  refine ⟨testPointRepresentative p (mapTestPoint g x), ?_,
    FieldValuedPoint.dominates_refl B S hS Y.left
      (testPointRepresentative p (mapTestPoint g x))⟩
  refine ⟨𝟙 _, ?_⟩
  change (Y.left.map (𝟙 _).op)
    (g.left.app (op (p.siteObject B S hS Z)) (yonedaEquiv x.1)) =
      yonedaEquiv (x.1 ≫ g.left)
  rw [yonedaEquiv_comp]
  simp

/-- The test point of `X` over the image in the base of a field-valued point of `X.left`:
the section itself, read as a morphism out of the represented presheaf. -/
private noncomputable def testPointOfFieldValuedPoint {X : Over Z}
    (u : FieldValuedPoint B S hS X.left) :
    TestPoint ((FieldValuedPoint.map B S hS X.left X.hom u).siteObject B S hS Z)
      (yonedaEquiv.symm (FieldValuedPoint.map B S hS X.left X.hom u).value) X := by
  refine ⟨yonedaEquiv.symm u.value, ?_⟩
  change yonedaEquiv.symm u.value ≫ X.hom =
    yonedaEquiv.symm ((FieldValuedPoint.map B S hS X.left X.hom u).value)
  exact yonedaEquiv_symm_naturality_right (u.siteObject B S hS X.left) X.hom u.value

/-- Taking the field-valued representative of the test point of a field-valued point returns
the same point of `|X|`. -/
private theorem testPointRepresentative_testPointOfFieldValuedPoint_class {X : Over Z}
    (u : FieldValuedPoint B S hS X.left) :
    (testPointRepresentative
        (FieldValuedPoint.map B S hS X.left X.hom u)
        (testPointOfFieldValuedPoint u)).class B S hS X.left =
      u.class B S hS X.left := by
  apply Quot.sound
  refine ⟨u, ?_, FieldValuedPoint.dominates_refl B S hS X.left u⟩
  refine ⟨𝟙 _, ?_⟩
  change X.left.map (𝟙 (u.siteObject B S hS X.left)).op
    (yonedaEquiv (yonedaEquiv.symm u.value)) = u.value
  simp

/-- Pushing a field-valued point of `X.left` forward along `g` is the field-valued
representative of the test point of `X` pushed forward along `g`. -/
private theorem testPointRepresentative_map_class {X Y : Over Z} (g : X ⟶ Y)
    (u : FieldValuedPoint B S hS X.left) :
    (FieldValuedPoint.map B S hS X.left g.left u).class B S hS Y.left =
      (testPointRepresentative
        (FieldValuedPoint.map B S hS X.left X.hom u)
        (mapTestPoint g (testPointOfFieldValuedPoint u))).class B S hS Y.left := by
  rw [← pointsMap_class, ← testPointRepresentative_testPointOfFieldValuedPoint_class]
  exact testPointRepresentative_class_map g
    (FieldValuedPoint.map B S hS X.left X.hom u) (testPointOfFieldValuedPoint u)

/-- The section of `Y.left` underlying the test point of a field-valued point of `X.left`
pushed forward along `g`. -/
private theorem mapTestPoint_testPointOfFieldValuedPoint_value {X Y : Over Z} (g : X ⟶ Y)
    (u : FieldValuedPoint B S hS X.left) :
    yonedaEquiv
        (mapTestPoint g (testPointOfFieldValuedPoint u)).1 =
      g.left.app (op (u.siteObject B S hS X.left)) u.value := by
  change yonedaEquiv (yonedaEquiv.symm u.value ≫ g.left) = _
  rw [yonedaEquiv_comp]
  simp
  rfl

/-! ### Restricting a test point to an extension of its field -/

/-- Restrict a test point of `X` over a field-valued point `p` of the base along a morphism
of field spectra exhibiting `q` as an extension of `p`. -/
private noncomputable def extendTestPoint {X : Over Z} (p q : FieldValuedPoint B S hS Z)
    (f : q.siteObject B S hS Z ⟶ p.siteObject B S hS Z)
    (hbase : Z.map f.op p.value = q.value)
    (x : TestPoint (p.siteObject B S hS Z) (yonedaEquiv.symm p.value) X) :
    TestPoint (q.siteObject B S hS Z) (yonedaEquiv.symm q.value) X :=
  ⟨yoneda.map f ≫ x.1, by
    change (yoneda.map f ≫ x.1) ≫ X.hom = yonedaEquiv.symm q.value
    rw [Category.assoc, x.2, ← hbase]
    exact yonedaEquiv_symm_naturality_left f Z p.value⟩

/-- Restricting a test point to an extension of its field does not change the point of `|X|`
it represents. -/
private theorem testPointRepresentative_extendTestPoint_class {X : Over Z}
    (p q : FieldValuedPoint B S hS Z) (f : q.siteObject B S hS Z ⟶ p.siteObject B S hS Z)
    (hbase : Z.map f.op p.value = q.value)
    (x : TestPoint (p.siteObject B S hS Z) (yonedaEquiv.symm p.value) X) :
    (testPointRepresentative q (extendTestPoint p q f hbase x)).class B S hS X.left =
      (testPointRepresentative p x).class B S hS X.left := by
  apply Quot.sound
  refine ⟨testPointRepresentative q (extendTestPoint p q f hbase x),
    FieldValuedPoint.dominates_refl B S hS X.left
      (testPointRepresentative q (extendTestPoint p q f hbase x)), ?_⟩
  refine ⟨f, ?_⟩
  change X.left.map f.op (yonedaEquiv x.1) = yonedaEquiv (yoneda.map f ≫ x.1)
  apply yonedaEquiv.symm.injective
  simpa using (yonedaEquiv_symm_naturality_left f X.left (yonedaEquiv x.1)).symm

/-- Restricting the pushforward of the test point of a field-valued point `u` of `X.left` to an
extension `q` of its field represents the pushforward of `u`. -/
private theorem testPointRepresentative_extendTestPoint_map_class {X Y : Over Z} (g : X ⟶ Y)
    (u : FieldValuedPoint B S hS X.left) (q : FieldValuedPoint B S hS Z)
    (f : q.siteObject B S hS Z ⟶ (FieldValuedPoint.map B S hS X.left X.hom u).siteObject B S hS Z)
    (hbase : Z.map f.op (FieldValuedPoint.map B S hS X.left X.hom u).value = q.value) :
    (testPointRepresentative q (extendTestPoint _ q f hbase
        (mapTestPoint g (testPointOfFieldValuedPoint u)))).class B S hS Y.left =
      (FieldValuedPoint.map B S hS X.left g.left u).class B S hS Y.left :=
  (testPointRepresentative_extendTestPoint_class _ q f hbase _).trans
    (testPointRepresentative_map_class g u).symm

/-! ### The induced relation on points -/

variable {R U : Over Z} (j : PreRelation R U)

/-- Restricting a related pair of test points to an extension of their field keeps them
related. -/
private theorem rel_extendTestPoint (p q : FieldValuedPoint B S hS Z)
    (f : q.siteObject B S hS Z ⟶ p.siteObject B S hS Z)
    (hbase : Z.map f.op p.value = q.value)
    {x y : TestPoint (p.siteObject B S hS Z) (yonedaEquiv.symm p.value) U}
    (h : j.Rel (yonedaEquiv.symm p.value) x y) :
    j.Rel (yonedaEquiv.symm q.value)
      (extendTestPoint p q f hbase x) (extendTestPoint p q f hbase y) := by
  rcases h with ⟨r, hrt, hrs⟩
  refine ⟨⟨yoneda.map f ≫ r.1, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, r.2, ← hbase]
    exact yonedaEquiv_symm_naturality_left f Z p.value
  · change (yoneda.map f ≫ r.1) ≫ j.target.left = yoneda.map f ≫ x.1
    rw [Category.assoc, hrt]
  · change (yoneda.map f ≫ r.1) ≫ j.source.left = yoneda.map f ≫ y.1
    rw [Category.assoc, hrs]

/-- A related pair of test points of `U` gives a related pair of points of `|U|`. -/
private theorem sourceTargetRel_of_rel (p : FieldValuedPoint B S hS Z)
    {x y : TestPoint (p.siteObject B S hS Z) (yonedaEquiv.symm p.value) U}
    (h : j.Rel (yonedaEquiv.symm p.value) x y) :
    Function.SourceTargetRel
      (pointsMap B S hS R.left j.source.left)
      (pointsMap B S hS R.left j.target.left)
      ((testPointRepresentative p x).class B S hS U.left)
      ((testPointRepresentative p y).class B S hS U.left) := by
  rcases h with ⟨r, hrt, hrs⟩
  refine ⟨(testPointRepresentative p r).class B S hS R.left, ?_, ?_⟩
  · rw [pointsMap_class, testPointRepresentative_class_map,
      show mapTestPoint j.target r = x from Subtype.ext hrt]
  · rw [pointsMap_class, testPointRepresentative_class_map,
      show mapTestPoint j.source r = y from Subtype.ext hrs]

/-- The target and the source of the test point of a field-valued point of `R` are
related. -/
private theorem rel_testPointOfFieldValuedPoint (u : FieldValuedPoint B S hS R.left) :
    j.Rel (yonedaEquiv.symm (FieldValuedPoint.map B S hS R.left R.hom u).value)
      (mapTestPoint j.target (testPointOfFieldValuedPoint u))
      (mapTestPoint j.source (testPointOfFieldValuedPoint u)) :=
  ⟨testPointOfFieldValuedPoint u, rfl, rfl⟩

/-- A pre-equivalence relation `j : R ⟶ U ×_Z U` induces an equivalence relation on `|U|`:
`x` is related to `y` when some point `r` of `|R|` has `t(r) = x` and `s(r) = y`. -/
@[stacks 043F]
theorem isPreEquivalenceRelation_sourceTargetRel (hj : IsPreEquivalenceRelation j) :
    Equivalence
      (Function.SourceTargetRel
        (pointsMap B S hS R.left j.source.left)
        (pointsMap B S hS R.left j.target.left)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨u, rfl⟩ := Quot.exists_rep a
    let p := FieldValuedPoint.map B S hS U.left U.hom u
    simpa [p, testPointRepresentative_testPointOfFieldValuedPoint_class] using
      sourceTargetRel_of_rel j p ((hj (p.siteObject B S hS Z) (yonedaEquiv.symm p.value)).refl
        (testPointOfFieldValuedPoint u))
  · intro a b hab
    rcases hab with ⟨r, hta, hso⟩
    obtain ⟨u, rfl⟩ := Quot.exists_rep r
    let p := FieldValuedPoint.map B S hS R.left R.hom u
    have hrev := (hj (p.siteObject B S hS Z) (yonedaEquiv.symm p.value)).symm
      (rel_testPointOfFieldValuedPoint j u)
    have hpoints := sourceTargetRel_of_rel j p hrev
    rw [← testPointRepresentative_map_class j.target u,
      ← testPointRepresentative_map_class j.source u] at hpoints
    rw [pointsMap_class] at hta hso
    rw [← hso, ← hta]
    simpa [p] using hpoints
  · intro a b c hab hbc
    rcases hab with ⟨r, hta₁, hso₁⟩
    rcases hbc with ⟨s, hta₂, hso₂⟩
    obtain ⟨r₀, rfl⟩ := Quot.exists_rep r
    obtain ⟨s₀, rfl⟩ := Quot.exists_rep s
    let p := FieldValuedPoint.map B S hS R.left R.hom r₀
    let p' := FieldValuedPoint.map B S hS R.left R.hom s₀
    let q₁ := testPointOfFieldValuedPoint r₀
    let q₂ := testPointOfFieldValuedPoint s₀
    let x₁ := mapTestPoint j.target q₁
    let y₁ := mapTestPoint j.source q₁
    let y₂ := mapTestPoint j.target q₂
    let z₂ := mapTestPoint j.source q₂
    let e₁ := FieldValuedPoint.map B S hS R.left j.source.left r₀
    let e₂ := FieldValuedPoint.map B S hS R.left j.target.left s₀
    have hmiddle : e₁.class B S hS U.left = e₂.class B S hS U.left := by
      calc
        e₁.class B S hS U.left = b := by simpa [e₁] using hso₁
        _ = e₂.class B S hS U.left := by simpa [e₂] using hta₂.symm
    obtain ⟨v, ⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩⟩ :=
      (FieldValuedPoint.class_eq_class_iff B S hS U.left e₁ e₂).mp hmiddle
    let f₁' : v.siteObject B S hS U.left ⟶ p.siteObject B S hS Z := f₁
    let f₂' : v.siteObject B S hS U.left ⟶ p'.siteObject B S hS Z := f₂
    have hv₁ : yonedaEquiv y₁.1 =
        j.source.left.app (op (r₀.siteObject B S hS R.left)) r₀.value := by
      simpa [q₁, y₁] using mapTestPoint_testPointOfFieldValuedPoint_value j.source r₀
    have hv₂ : yonedaEquiv y₂.1 =
        j.target.left.app (op (s₀.siteObject B S hS R.left)) s₀.value := by
      simpa [q₂, y₂] using mapTestPoint_testPointOfFieldValuedPoint_value j.target s₀
    have hf₁' : U.left.map f₁'.op (yonedaEquiv y₁.1) = v.value := by
      rwa [hv₁]
    have hf₂' : U.left.map f₂'.op (yonedaEquiv y₂.1) = v.value := by
      rwa [hv₂]
    let q := FieldValuedPoint.map B S hS U.left U.hom v
    have hbase (w : FieldValuedPoint B S hS Z)
        (t : TestPoint (w.siteObject B S hS Z) (yonedaEquiv.symm w.value) U)
        (f : v.siteObject B S hS U.left ⟶ w.siteObject B S hS Z)
        (hf : U.left.map f.op (yonedaEquiv t.1) = v.value) :
        Z.map f.op w.value = q.value := by
      change Z.map f.op w.value =
        U.hom.app (op (v.siteObject B S hS U.left)) v.value
      rw [← testPoint_base_value w t, ← hf]
      exact (congrArg (fun k ↦ k (yonedaEquiv t.1)) (U.hom.naturality f.op)).symm
    have hbase₁ := hbase p y₁ f₁' hf₁'
    have hbase₂ := hbase p' y₂ f₂' hf₂'
    have hmid (w : FieldValuedPoint B S hS Z)
        (t : TestPoint (w.siteObject B S hS Z) (yonedaEquiv.symm w.value) U)
        (f : v.siteObject B S hS U.left ⟶ w.siteObject B S hS Z)
        (hf : U.left.map f.op (yonedaEquiv t.1) = v.value) :
        yoneda.map f ≫ t.1 = yonedaEquiv.symm v.value := by
      rw [← hf]
      simpa using (yonedaEquiv_symm_naturality_left f U.left (yonedaEquiv t.1))
    have hmid₁ := hmid p y₁ f₁' hf₁'
    have hmid₂ := hmid p' y₂ f₂' hf₂'
    have hrel₁ := rel_extendTestPoint j p q f₁' hbase₁ (rel_testPointOfFieldValuedPoint j r₀)
    have hrel₂ := rel_extendTestPoint j p' q f₂' hbase₂ (rel_testPointOfFieldValuedPoint j s₀)
    have hy : extendTestPoint p q f₁' hbase₁ y₁ = extendTestPoint p' q f₂' hbase₂ y₂ :=
      Subtype.ext (hmid₁.trans hmid₂.symm)
    rw [← hy] at hrel₂
    have hresult := sourceTargetRel_of_rel j q
      ((hj (q.siteObject B S hS Z) (yonedaEquiv.symm q.value)).trans hrel₁ hrel₂)
    have hxclass :=
      (testPointRepresentative_extendTestPoint_map_class j.target r₀ q f₁' hbase₁).trans hta₁
    have hzclass :=
      (testPointRepresentative_extendTestPoint_map_class j.source s₀ q f₂' hbase₂).trans hso₂
    rwa [hxclass, hzclass] at hresult

end PreRelation

end AlgebraicGeometry.Space

end
