module

public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.InvarianceOnOrbits
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.OrbitSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.SetTheoreticEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafCondition

/-!
# Invariance and separation of orbits read off a fibre-product square

Fix a scheme `S` in a big fppf site `B` and a presheaf `Z` on the big fppf site of `S`, let
`j : R ⟶ U ×_Z U` be a pre-relation of presheaves over `Z`, and let `φ : U ⟶ X` be a morphism
over `Z` whose target is an algebraic space. Pulling the pre-relation back along the canonical
morphism `c : U ×_X U ⟶ U ×_Z U` gives the cartesian square
```
(U ×_X U) ×_{U ×_Z U} R  --p-->  R
         |q                      |j
         v                       v
     U ×_X U        --c-->   U ×_Z U
```
and the two projections `p` and `q` detect the two conditions of **Stacks 048V**: the
morphism `φ` is set-theoretically invariant exactly when `p` is surjective, and — for a
set-theoretic pre-equivalence relation — it separates the orbits of `j` exactly when `p` and
`q` are both surjective. Surjectivity of `p` and `q` forces the pre-relation to be a
set-theoretic pre-equivalence relation. If `φ` is invariant in the sense of **Stacks 048E**,
the pre-relation maps to `U ×_X U` by `(t, s)`, the condition on `p` is automatic, and
separation of orbits becomes surjectivity of `(t, s)`.

## Main definitions

* `AlgebraicGeometry.Space.selfFibreProduct` and
  `AlgebraicGeometry.Space.selfFibreProductToProduct` are `U ×_X U` and the canonical
  morphism `c`.
* `AlgebraicGeometry.Space.PreRelation.invarianceFibreProduct` is the upper left corner of
  the square, with projections
  `AlgebraicGeometry.Space.PreRelation.invarianceToRelation` (`p`) and
  `AlgebraicGeometry.Space.PreRelation.invarianceToSelfFibreProduct` (`q`).
* `AlgebraicGeometry.Space.PreRelation.toSelfFibreProduct` is the morphism `(t, s)` to
  `U ×_X U` determined by an invariant morphism.
* `AlgebraicGeometry.Space.FieldValuedPoint.overObject` is the object of the slice over `Z`
  determined by a field-valued point of `Z`, and
  `AlgebraicGeometry.Space.restrictTestPoint` restricts a point over a field-valued point of
  `Z` along an extension of its field.

## Main results

* `AlgebraicGeometry.Space.isSetTheoreticallyInvariant_iff_isSurjective_invarianceToRelation`:
  **Stacks 049Y**, part (1).
* `AlgebraicGeometry.Space.separatesOrbits_iff_isSurjective`: **Stacks 049Y**, part (2).
* `AlgebraicGeometry.Space.isSetTheoreticPreEquivalenceRelation_of_isSurjective` and
  `AlgebraicGeometry.Space.separatesOrbits_of_isSurjective`: **Stacks 049Y**, part (3).
* `AlgebraicGeometry.Space.separatesOrbits_iff_isSurjective_toSelfFibreProduct`: **Stacks
  049Y**, part (4).
* `AlgebraicGeometry.Space.isSurjective_left_iff`: a morphism of the slice over `Z` is
  surjective on points exactly when every point of its target over a field-valued point of
  `Z` lifts through it after a single extension of the field.
* `AlgebraicGeometry.Space.exists_geometricPoint_restriction`: every field-valued point is
  the restriction of a geometric point along an algebraic closure of its field.
* `AlgebraicGeometry.Space.injective_map_of_fieldValuedPointHom` and
  `AlgebraicGeometry.Space.eq_of_comp_yoneda_map_eq`: an extension of the field of a
  field-valued point is injective on the sections of an algebraic space, so two morphisms out
  of the presheaf represented by a field spectrum which agree after a field extension are
  equal.

## Implementation notes

The fibre products are taken in the slice `CategoryTheory.Over Z` of presheaves on the big
fppf site, whose categorical product is the fibre product over `Z`; this is the category in
which `AlgebraicGeometry.Space.PreRelation` of **Stacks 043C** lives, so `U ×_Z U` is
literally `U ⨯ U` there and no choice of cartesian squares has to be made. The target `X` is
an object of the slice because the comparison morphism `c` only exists for a morphism `φ`
over the base, as in the source, where every object in sight is an algebraic space over `B`.
Surjectivity is that of **Stacks 03ME**, measured on the underlying morphisms of presheaves,
which forgets the structure morphisms to the base.

The source proves part (1) and leaves parts (2), (3) and (4) to the reader, with the hint of
passing to an algebraically closed field of large cardinality and reading off the resulting
diagram of sets. Here the arguments are run with field extensions instead of one large field,
which avoids the construction of such a field: surjectivity of a morphism of the slice is
`AlgebraicGeometry.Space.isSurjective_left_iff`, namely liftability of a point of the target
after a single extension of its field, and the two projections translate into the statements
that the endpoints of an arrow of `j` acquire the same image under `φ` after one extension
(for `p`), and that a pair of points of `U` with the same image under `φ` becomes the pair of
endpoints of an arrow of `j` after one extension (for `q`). The universal properties of the
two fibre products turn these into the lifting problems for `p` and for `q`.

The only input from the algebraic-space axioms on `X` is that restriction along a field
extension is injective on its sections: a morphism of field spectra is a one-element fpqc
covering by `AlgebraicGeometry.Space.fpqc_singleton_of_fieldSpecHom`, and an algebraic space
is separated for every fpqc covering by
`AlgebraicGeometry.IsAlgebraicSpace.isSeparatedFor_fpqc`. This is what descends an equality
of sections of `X` obtained over an extension field, and it is also what makes agreement of
the images under `φ` after an extension equivalent to agreement over the given field; the
latter is why the relation of being joined by an arrow after one extension is, under
surjectivity of `p` and `q`, the relation of having the same image under `φ`, hence an
equivalence relation.

Orbits are the ones of **Stacks 048Q**, where the chain of arrows cutting out an orbit is
allowed to appear after an extension of the field. For a set-theoretic pre-equivalence
relation such a chain collapses to a single arrow: the chain is restricted to an algebraic
closure of the extension field, where the relation of **Stacks 0490** is an equivalence
relation, and that relation is exactly the relation of being joined by one arrow after a
further extension.

## References

* [Stacks Project, Tag 049Y](https://stacks.math.columbia.edu/tag/049Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Passing to an algebraic closure -/

/-- Every field-valued point of a presheaf over `S` is the restriction of a geometric point
along an algebraic closure of its field. -/
theorem exists_geometricPoint_restriction (q : FieldValuedPoint B S hS Z) :
    ∃ (g : GeometricPoint B S hS Z)
      (f : g.val.siteObject B S hS Z ⟶ q.siteObject B S hS Z),
      Z.map f.op q.value = g.val.value :=
  ⟨⟨algClosurePoint q, AlgebraicClosure.isAlgClosed q.carrier⟩, algClosureHom q, rfl⟩

/-! ### Descent along an extension of the field of a point -/

/-- Restriction along an extension of the field of a field-valued point is injective on the
sections of an algebraic space: a field extension is a one-element fpqc covering, and an
algebraic space is separated for every fpqc covering. -/
@[ega "I 3.5.5" "more general"]
theorem injective_map_of_fieldValuedPointHom
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (p q : FieldValuedPoint B S hS G)
    (α : p.siteObject B S hS G ⟶ q.siteObject B S hS G) :
    Function.Injective (F.map α.op) :=
  Presieve.isSeparatedFor_singleton.1
    (hF.isSeparatedFor_fpqc (singleton_mem_fpqc_of_fieldValuedPointHom p q α))

/-! ### Surjectivity on points, tested on field-valued points -/

/-- The object of the slice over `Z` determined by a field-valued point of `Z`: the presheaf
represented by the spectrum of its field, mapping to `Z` by the point itself. -/
noncomputable abbrev FieldValuedPoint.overObject (b : FieldValuedPoint B S hS Z) : Over Z :=
  Over.mk (yonedaEquiv.symm b.value)

/-- The restriction morphism between the slice objects of two field-valued points of `Z`,
one of which is the restriction of the other along an extension of its field. -/
noncomputable def FieldValuedPoint.overObjectHom {b b' : FieldValuedPoint B S hS Z}
    (f : b'.siteObject B S hS Z ⟶ b.siteObject B S hS Z)
    (hf : Z.map f.op b.value = b'.value) : b'.overObject ⟶ b.overObject :=
  Over.homMk (yoneda.map f) (by
    change yoneda.map f ≫ yonedaEquiv.symm b.value = yonedaEquiv.symm b'.value
    rw [yonedaEquiv_symm_naturality_left, hf])

/-- A morphism of the slice over `Z` is surjective on points exactly when every point of its
target over a field-valued point of `Z` lifts through it after a single extension of the
field.

A point of the target over a field-valued point `b` of `Z` is a morphism of the slice from
`b.overObject`, and the lift is a morphism of the slice from the slice object of the
restricted point. -/
theorem isSurjective_left_iff {W V : Over Z} (g : W ⟶ V) :
    IsSurjective B S hS g.left ↔
      ∀ (b : FieldValuedPoint B S hS Z) (y : b.overObject ⟶ V),
        ∃ (b' : FieldValuedPoint B S hS Z)
          (f : b'.siteObject B S hS Z ⟶ b.siteObject B S hS Z)
          (hf : Z.map f.op b.value = b'.value)
          (w : b'.overObject ⟶ W),
          w ≫ g = FieldValuedPoint.overObjectHom f hf ≫ y := by
  have hgw : g.left ≫ V.hom = W.hom := Over.w g
  constructor
  · intro hsurj b y
    have hyb : y.left ≫ V.hom = yonedaEquiv.symm b.value := Over.w y
    obtain ⟨x, hx⟩ := hsurj
      ((⟨b.carrier, b.contained, b.toBase, yonedaEquiv y.left⟩ :
        FieldValuedPoint B S hS V.left).class B S hS V.left)
    obtain ⟨w₀, hw₀⟩ := Quot.exists_rep x
    have hx' : (FieldValuedPoint.map B S hS W.left g.left w₀).class B S hS V.left =
        (⟨b.carrier, b.contained, b.toBase, yonedaEquiv y.left⟩ :
          FieldValuedPoint B S hS V.left).class B S hS V.left := by
      rwa [← hw₀] at hx
    obtain ⟨r, ⟨β, hβ⟩, ⟨α, hα⟩⟩ :=
      (FieldValuedPoint.class_eq_class_iff B S hS V.left _ _).mp hx'
    -- the two field extensions, read between the objects of the site
    let α' : (fieldObject (hS := hS) r.carrier r.contained r.toBase) ⟶
      (fieldObject (hS := hS) b.carrier b.contained b.toBase) := α
    let β' : (fieldObject (hS := hS) r.carrier r.contained r.toBase) ⟶
      (fieldObject (hS := hS) w₀.carrier w₀.contained w₀.toBase) := β
    refine ⟨⟨r.carrier, r.contained, r.toBase, Z.map α'.op b.value⟩, α', rfl, ?_, ?_⟩
    · refine Over.homMk (yonedaEquiv.symm (W.left.map β'.op w₀.value)) ?_
      change yonedaEquiv.symm (W.left.map β'.op w₀.value) ≫ W.hom =
        yonedaEquiv.symm (Z.map α'.op b.value)
      rw [yonedaEquiv_symm_naturality_right, ← hgw]
      congr 1
      change V.hom.app _ (g.left.app _ (W.left.map β'.op w₀.value)) = Z.map α'.op b.value
      rw [NatTrans.naturality_apply]
      have hβ' : V.left.map β'.op
          (g.left.app (op (fieldObject (hS := hS) w₀.carrier w₀.contained w₀.toBase))
            w₀.value) = r.value := hβ
      have hα' : V.left.map α'.op (yonedaEquiv y.left) = r.value := hα
      rw [hβ', ← hα', NatTrans.naturality_apply]
      congr 1
      change V.hom.app _ (yonedaEquiv y.left) = b.value
      rw [← yonedaEquiv_comp, hyb]
      exact yonedaEquiv.apply_symm_apply b.value
    · refine Over.OverMorphism.ext ?_
      change yonedaEquiv.symm (W.left.map β'.op w₀.value) ≫ g.left = yoneda.map α' ≫ y.left
      apply yonedaEquiv.injective
      rw [← yonedaEquiv_naturality]
      change yonedaEquiv (yonedaEquiv.symm (W.left.map β'.op w₀.value) ≫ g.left) =
        V.left.map α'.op (yonedaEquiv y.left)
      have hβ' : V.left.map β'.op
          (g.left.app (op (fieldObject (hS := hS) w₀.carrier w₀.contained w₀.toBase))
            w₀.value) = r.value := hβ
      have hα' : V.left.map α'.op (yonedaEquiv y.left) = r.value := hα
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply, NatTrans.naturality_apply, hβ', hα']
  · intro h x
    obtain ⟨v, hv⟩ := Quot.exists_rep x
    obtain ⟨b', f, hf, w, hw⟩ := h
      ⟨v.carrier, v.contained, v.toBase, V.hom.app (op (v.siteObject B S hS V.left)) v.value⟩
      (Over.homMk (yonedaEquiv.symm v.value) (by
        change yonedaEquiv.symm v.value ≫ V.hom =
          yonedaEquiv.symm (V.hom.app (op (v.siteObject B S hS V.left)) v.value)
        rw [yonedaEquiv_symm_naturality_right]
        rfl))
    have hval : g.left.app (op (b'.siteObject B S hS Z)) (yonedaEquiv w.left) =
        V.left.map f.op v.value := by
      have hw' : w.left ≫ g.left = yoneda.map f ≫ yonedaEquiv.symm v.value :=
        congrArg (fun k : b'.overObject ⟶ V ↦ k.left) hw
      rw [← yonedaEquiv_comp, hw', ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
    refine ⟨(⟨b'.carrier, b'.contained, b'.toBase, yonedaEquiv w.left⟩ :
      FieldValuedPoint B S hS W.left).class B S hS W.left, ?_⟩
    rw [← hv]
    change (FieldValuedPoint.map B S hS W.left g.left
      ⟨b'.carrier, b'.contained, b'.toBase, yonedaEquiv w.left⟩).class B S hS V.left =
      v.class B S hS V.left
    exact FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS V.left
      ⟨_, FieldValuedPoint.dominates_refl B S hS V.left _, ⟨f, hval.symm⟩⟩

/-! ### Points of the slice as morphisms of the slice -/

/-- A point of `W` over a field-valued point of `Z`, read as a morphism of the slice out of
the slice object of that point. -/
private noncomputable def overHomOfTestPoint {b : FieldValuedPoint B S hS Z} {W : Over Z}
    (x : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) W) :
    b.overObject ⟶ W := Over.homMk x.1 x.2

/-- A morphism of the slice out of the slice object of a field-valued point of `Z`, read as a
point of its target over that point. -/
private noncomputable def testPointOfOverHom {b : FieldValuedPoint B S hS Z} {W : Over Z}
    (x : b.overObject ⟶ W) :
    TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) W := ⟨x.left, Over.w x⟩

/-- Two morphisms from the presheaf represented by the spectrum of the field of a
field-valued point of `Z` to an algebraic space which agree after an extension of that field
are equal. -/
theorem eq_of_comp_yoneda_map_eq {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {b b' : FieldValuedPoint B S hS Z}
    (f : b'.siteObject B S hS Z ⟶ b.siteObject B S hS Z)
    {A A' : yoneda.obj (b.siteObject B S hS Z) ⟶ Y}
    (h : yoneda.map f ≫ A = yoneda.map f ≫ A') : A = A' := by
  refine yonedaEquiv.injective (injective_map_of_fieldValuedPointHom hY b' b f ?_)
  rw [yonedaEquiv_naturality, yonedaEquiv_naturality, h]

/-! ### Restricting a point along an extension of its field -/

/-- The restriction of a point of `W` over a field-valued point of `Z` along an extension of
the field of that point. -/
noncomputable def restrictTestPoint {b b' : FieldValuedPoint B S hS Z}
    (f : b'.siteObject B S hS Z ⟶ b.siteObject B S hS Z)
    (hf : Z.map f.op b.value = b'.value) {W : Over Z}
    (x : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) W) :
    TestPoint (b'.siteObject B S hS Z) (yonedaEquiv.symm b'.value) W :=
  ⟨yoneda.map f ≫ x.1, by
    rw [Category.assoc, x.2, yonedaEquiv_symm_naturality_left, hf]⟩

/-- The underlying morphism of `restrictTestPoint f hf x` is `yoneda.map f ≫ x.1`. -/
@[simp]
theorem restrictTestPoint_val {b b' : FieldValuedPoint B S hS Z}
    (f : b'.siteObject B S hS Z ⟶ b.siteObject B S hS Z)
    (hf : Z.map f.op b.value = b'.value) {W : Over Z}
    (x : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) W) :
    (restrictTestPoint f hf x).1 = yoneda.map f ≫ x.1 := rfl

/-! ### The square of the lemma -/

variable {R U X : Over Z}

set_option synthInstance.maxHeartbeats 400000 in
-- the default instance search for `HasPullbacks (Over Z)` runs out of heartbeats
/-- The pullbacks of `Over Z`, found once (the default search runs out of heartbeats) and
cached as a local instance. -/
noncomputable local instance (priority := high) hasPullbacksOverPresheaf :
    HasPullbacks (Over Z) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- the default instance search for `HasBinaryProducts (Over Z)` runs out of heartbeats
/-- The binary products of `Over Z`, found once (the default search runs out of heartbeats)
and cached as a local instance. -/
noncomputable local instance (priority := high) hasBinaryProductsOverPresheaf :
    HasBinaryProducts (Over Z) := inferInstance

/-- The pullback of two morphisms of `Over Z`, from `hasPullbacksOverPresheaf`. -/
noncomputable local instance (priority := high) hasPullbackOverPresheaf {A B C : Over Z}
    (f : A ⟶ C) (g : B ⟶ C) : HasPullback f g :=
  hasPullbacksOverPresheaf.has_limit _

/-- The binary product of two objects of `Over Z`, from `hasBinaryProductsOverPresheaf`. -/
noncomputable local instance (priority := high) hasBinaryProductOverPresheaf (A B : Over Z) :
    HasBinaryProduct A B :=
  hasBinaryProductsOverPresheaf.has_limit _

/-- The fibre product `U ×_X U` of a morphism out of `U` with itself. -/
noncomputable abbrev selfFibreProduct (φ : U ⟶ X) : Over Z := pullback φ φ

/-- The canonical morphism `c : U ×_X U ⟶ U ×_Z U`. -/
noncomputable def selfFibreProductToProduct (φ : U ⟶ X) : selfFibreProduct φ ⟶ U ⨯ U :=
  prod.lift (pullback.fst φ φ) (pullback.snd φ φ)

/-- The composite of `selfFibreProductToProduct φ` with the first projection is the first
projection of `U ×_X U`. -/
@[simp]
theorem selfFibreProductToProduct_fst (φ : U ⟶ X) :
    selfFibreProductToProduct φ ≫ prod.fst = pullback.fst φ φ := prod.lift_fst _ _

/-- The composite of `selfFibreProductToProduct φ` with the second projection is the second
projection of `U ×_X U`. -/
@[simp]
theorem selfFibreProductToProduct_snd (φ : U ⟶ X) :
    selfFibreProductToProduct φ ≫ prod.snd = pullback.snd φ φ := prod.lift_snd _ _

/-- The fibre product `(U ×_X U) ×_{U ×_Z U} R` of the canonical morphism `c` with a
pre-relation `j : R ⟶ U ×_Z U`. -/
noncomputable abbrev PreRelation.invarianceFibreProduct (j : PreRelation R U) (φ : U ⟶ X) :
    Over Z := pullback (selfFibreProductToProduct φ) j

/-- The projection `p : (U ×_X U) ×_{U ×_Z U} R ⟶ R`. -/
noncomputable abbrev PreRelation.invarianceToRelation (j : PreRelation R U) (φ : U ⟶ X) :
    j.invarianceFibreProduct φ ⟶ R := pullback.snd (selfFibreProductToProduct φ) j

/-- The projection `q : (U ×_X U) ×_{U ×_Z U} R ⟶ U ×_X U`. -/
noncomputable abbrev PreRelation.invarianceToSelfFibreProduct (j : PreRelation R U)
    (φ : U ⟶ X) : j.invarianceFibreProduct φ ⟶ selfFibreProduct φ :=
  pullback.fst (selfFibreProductToProduct φ) j

/-- The two ways of reading the endpoints of a morphism into `(U ×_X U) ×_{U ×_Z U} R` agree:
through `p` and then `j`, or through `q` and then the projections of `U ×_X U`. -/
private theorem comp_invarianceToRelation_endpoints {W : Over Z} (j : PreRelation R U)
    (φ : U ⟶ X) (d : W ⟶ j.invarianceFibreProduct φ) :
    (d ≫ j.invarianceToRelation φ) ≫ j.target =
        (d ≫ j.invarianceToSelfFibreProduct φ) ≫ pullback.fst φ φ ∧
      (d ≫ j.invarianceToRelation φ) ≫ j.source =
        (d ≫ j.invarianceToSelfFibreProduct φ) ≫ pullback.snd φ φ := by
  have hcond : j.invarianceToSelfFibreProduct φ ≫ selfFibreProductToProduct φ =
      j.invarianceToRelation φ ≫ j := pullback.condition
  constructor
  · calc (d ≫ j.invarianceToRelation φ) ≫ j.target
        = d ≫ (j.invarianceToRelation φ ≫ j) ≫ prod.fst := by simp [PreRelation.target]
      _ = d ≫ (j.invarianceToSelfFibreProduct φ ≫ selfFibreProductToProduct φ) ≫
            prod.fst := by rw [← hcond]
      _ = (d ≫ j.invarianceToSelfFibreProduct φ) ≫ pullback.fst φ φ := by simp
  · calc (d ≫ j.invarianceToRelation φ) ≫ j.source
        = d ≫ (j.invarianceToRelation φ ≫ j) ≫ prod.snd := by simp [PreRelation.source]
      _ = d ≫ (j.invarianceToSelfFibreProduct φ ≫ selfFibreProductToProduct φ) ≫
            prod.snd := by rw [← hcond]
      _ = (d ≫ j.invarianceToSelfFibreProduct φ) ≫ pullback.snd φ φ := by simp

/-- A morphism to `R` lifts through `p` exactly when the two endpoints of the arrow of the
pre-relation it describes have the same image under `φ`. -/
private theorem exists_lift_invarianceToRelation_iff {W : Over Z} (j : PreRelation R U)
    (φ : U ⟶ X) (ρ : W ⟶ R) :
    (∃ d : W ⟶ j.invarianceFibreProduct φ, d ≫ j.invarianceToRelation φ = ρ) ↔
      (ρ ≫ j.target) ≫ φ = (ρ ≫ j.source) ≫ φ := by
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨ht, hs⟩ := comp_invarianceToRelation_endpoints j φ d
    rw [hd] at ht hs
    rw [ht, hs]
    simp [pullback.condition]
  · intro h
    have hc : pullback.lift (f := φ) (g := φ) (ρ ≫ j.target) (ρ ≫ j.source) h ≫
        selfFibreProductToProduct φ = ρ ≫ j := by
      refine prod.hom_ext ?_ ?_
      · rw [Category.assoc, selfFibreProductToProduct_fst, pullback.lift_fst]
        exact (Category.assoc ρ j prod.fst).symm
      · rw [Category.assoc, selfFibreProductToProduct_snd, pullback.lift_snd]
        exact (Category.assoc ρ j prod.snd).symm
    exact ⟨pullback.lift _ ρ hc, pullback.lift_snd _ _ hc⟩

/-- A morphism to `U ×_X U` lifts through `q` exactly when its two components are the
endpoints of an arrow of the pre-relation. -/
private theorem exists_lift_invarianceToSelfFibreProduct_iff {W : Over Z}
    (j : PreRelation R U) (φ : U ⟶ X) (a : W ⟶ selfFibreProduct φ) :
    (∃ d : W ⟶ j.invarianceFibreProduct φ,
        d ≫ j.invarianceToSelfFibreProduct φ = a) ↔
      ∃ ρ : W ⟶ R, ρ ≫ j.target = a ≫ pullback.fst φ φ ∧
        ρ ≫ j.source = a ≫ pullback.snd φ φ := by
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨ht, hs⟩ := comp_invarianceToRelation_endpoints j φ d
    rw [hd] at ht hs
    exact ⟨d ≫ j.invarianceToRelation φ, ht, hs⟩
  · rintro ⟨ρ, ht, hs⟩
    have hc : a ≫ selfFibreProductToProduct φ = ρ ≫ j :=
      prod.hom_ext (by simp [← ht, PreRelation.target])
        (by simp [← hs, PreRelation.source])
    exact ⟨pullback.lift a ρ hc, pullback.lift_fst _ _ hc⟩

/-! ### Arrows and agreement after an extension of the field -/

/-- Two points of `U` over a field-valued point of `Z` are the endpoints of an arrow of the
pre-relation after one extension of the field. -/
private def RelAfterExtension (j : PreRelation R U) (b : FieldValuedPoint B S hS Z)
    (x y : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) U) : Prop :=
  ∃ (b' : FieldValuedPoint B S hS Z)
    (f : b'.siteObject B S hS Z ⟶ b.siteObject B S hS Z)
    (hf : Z.map f.op b.value = b'.value),
    j.Rel (yonedaEquiv.symm b'.value) (restrictTestPoint f hf x) (restrictTestPoint f hf y)

/-- The two endpoints of an arrow of the pre-relation over a field-valued point of `Z` have
the same image under `φ` after one extension of the field. -/
private def EndpointsAgreeAfterExtension (j : PreRelation R U) (φ : U ⟶ X)
    (b : FieldValuedPoint B S hS Z)
    (r : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) R) : Prop :=
  ∃ (b' : FieldValuedPoint B S hS Z)
    (f : b'.siteObject B S hS Z ⟶ b.siteObject B S hS Z)
    (_ : Z.map f.op b.value = b'.value),
    ((yoneda.map f ≫ r.1) ≫ j.target.left) ≫ φ.left =
      ((yoneda.map f ≫ r.1) ≫ j.source.left) ≫ φ.left

private theorem relAfterExtension_of_rel (j : PreRelation R U)
    {b : FieldValuedPoint B S hS Z}
    {x y : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) U}
    (h : j.Rel (yonedaEquiv.symm b.value) x y) : RelAfterExtension j b x y := by
  have hid : Z.map (𝟙 (b.siteObject B S hS Z)).op b.value = b.value := by simp
  obtain ⟨r, hrt, hrs⟩ := h
  refine ⟨b, 𝟙 _, hid, restrictTestPoint (𝟙 _) hid r, ?_, ?_⟩
  · simp only [restrictTestPoint_val]
    exact hrt
  · simp only [restrictTestPoint_val]
    exact hrs

private theorem relAfterExtension_restrict (j : PreRelation R U)
    {b b' : FieldValuedPoint B S hS Z}
    (f : b'.siteObject B S hS Z ⟶ b.siteObject B S hS Z)
    (hf : Z.map f.op b.value = b'.value)
    {x y : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) U}
    (h : RelAfterExtension j b' (restrictTestPoint f hf x) (restrictTestPoint f hf y)) :
    RelAfterExtension j b x y := by
  obtain ⟨b'', g, hg, ρ, h₁, h₂⟩ := h
  have hcomp : Z.map (g ≫ f).op b.value = b''.value := by
    rw [op_comp, Functor.map_comp, types_comp_apply, hf, hg]
  refine ⟨b'', g ≫ f, hcomp, ρ, ?_, ?_⟩
  · rw [h₁]
    simp [Functor.map_comp]
  · rw [h₂]
    simp [Functor.map_comp]

private theorem rel_restrict (j : PreRelation R U) {b b' : FieldValuedPoint B S hS Z}
    (f : b'.siteObject B S hS Z ⟶ b.siteObject B S hS Z)
    (hf : Z.map f.op b.value = b'.value)
    {x y : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) U}
    (h : j.Rel (yonedaEquiv.symm b.value) x y) :
    j.Rel (yonedaEquiv.symm b'.value) (restrictTestPoint f hf x)
      (restrictTestPoint f hf y) := by
  obtain ⟨r, hrt, hrs⟩ := h
  refine ⟨restrictTestPoint f hf r, ?_, ?_⟩
  · rw [restrictTestPoint_val, restrictTestPoint_val, Category.assoc, hrt]
  · rw [restrictTestPoint_val, restrictTestPoint_val, Category.assoc, hrs]

private theorem weaklyEquivalent_restrict (j : PreRelation R U)
    {b b' : FieldValuedPoint B S hS Z}
    (f : b'.siteObject B S hS Z ⟶ b.siteObject B S hS Z)
    (hf : Z.map f.op b.value = b'.value)
    {x y : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) U}
    (h : j.WeaklyEquivalent b x y) :
    j.WeaklyEquivalent b' (restrictTestPoint f hf x) (restrictTestPoint f hf y) := by
  change Relation.EqvGen (j.Rel (yonedaEquiv.symm b.value)) x y at h
  induction h with
  | rel a c hac => exact Relation.EqvGen.rel _ _ (rel_restrict j f hf hac)
  | refl a => exact Relation.EqvGen.refl _
  | symm a c _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a c e _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

private theorem equivalent_of_relAfterExtension (j : PreRelation R U)
    {b : FieldValuedPoint B S hS Z}
    {x y : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) U}
    (h : RelAfterExtension j b x y) : j.Equivalent b x y := by
  obtain ⟨b', f, hf, hrel⟩ := h
  exact ⟨b', f, hf, restrictTestPoint f hf x, restrictTestPoint f hf y, rfl, rfl,
    Relation.EqvGen.rel _ _ hrel⟩

/-! ### Points of `U` in the fibre of a field-valued point of `Z` -/

/-- A point of `U` over a field-valued point of `Z`, read as a section of `U` in the fibre of
that point. -/
private noncomputable def fibreOfTestPoint {b : FieldValuedPoint B S hS Z}
    (x : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) U) :
    {v : U.left.obj (op (b.siteObject B S hS Z)) //
      U.hom.app (op (b.siteObject B S hS Z)) v = b.value} :=
  ⟨yonedaEquiv x.1, by
    rw [← yonedaEquiv_comp, x.2]
    exact yonedaEquiv.apply_symm_apply b.value⟩

/-- A section of `U` in the fibre of a field-valued point of `Z`, read as a point of `U` over
that point. -/
private noncomputable def testPointOfFibre {b : FieldValuedPoint B S hS Z}
    (v : {v : U.left.obj (op (b.siteObject B S hS Z)) //
      U.hom.app (op (b.siteObject B S hS Z)) v = b.value}) :
    TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) U :=
  ⟨yonedaEquiv.symm v.1, by rw [yonedaEquiv_symm_naturality_right, v.2]⟩

private theorem fibreOfTestPoint_testPointOfFibre {b : FieldValuedPoint B S hS Z}
    (v : {v : U.left.obj (op (b.siteObject B S hS Z)) //
      U.hom.app (op (b.siteObject B S hS Z)) v = b.value}) :
    fibreOfTestPoint (U := U) (testPointOfFibre v) = v :=
  Subtype.ext (yonedaEquiv.apply_symm_apply v.1)

/-- Over a field-valued point of `Z`, the relation of **Stacks 0490** on the sections of `U`
in the fibre of the point is the relation of being the endpoints of an arrow of the
pre-relation after one extension of the field. -/
private theorem setTheoreticRel_iff_relAfterExtension (j : PreRelation R U)
    (b : FieldValuedPoint B S hS Z)
    (x y : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) U) :
    j.SetTheoreticRel b.carrier b.contained b.toBase b.value
        (fibreOfTestPoint y) (fibreOfTestPoint x) ↔ RelAfterExtension j b x y := by
  constructor
  · rintro ⟨r, f, hs, ht⟩
    have hfy : U.hom.app (op (fieldObject (hS := hS) b.carrier b.contained b.toBase))
      (fibreOfTestPoint (U := U) y).1 = b.value := (fibreOfTestPoint (U := U) y).2
    have hRhom : j.source.left ≫ U.hom = R.hom := Over.w j.source
    have hsplit : R.hom.app (op (r.siteObject B S hS R.left)) r.value =
        U.hom.app (op (r.siteObject B S hS R.left))
          (j.source.left.app (op (r.siteObject B S hS R.left)) r.value) := by
      rw [← hRhom]
      rfl
    have hbase : R.hom.app (op (r.siteObject B S hS R.left)) r.value =
        Z.map f.op b.value := by
      rw [hsplit, hs, NatTrans.naturality_apply, hfy]
    refine ⟨⟨r.carrier, r.contained, r.toBase, Z.map f.op b.value⟩, f, rfl,
      ⟨yonedaEquiv.symm r.value, ?_⟩, ?_, ?_⟩
    · rw [yonedaEquiv_symm_naturality_right]
      exact congrArg yonedaEquiv.symm hbase
    · refine yonedaEquiv.injective ?_
      rw [restrictTestPoint_val, yonedaEquiv_comp, Equiv.apply_symm_apply,
        ← yonedaEquiv_naturality]
      exact ht
    · refine yonedaEquiv.injective ?_
      rw [restrictTestPoint_val, yonedaEquiv_comp, Equiv.apply_symm_apply,
        ← yonedaEquiv_naturality]
      exact hs
  · rintro ⟨b', f, hf, ρ, hρt, hρs⟩
    refine ⟨⟨b'.carrier, b'.contained, b'.toBase, yonedaEquiv ρ.1⟩, f, ?_, ?_⟩
    · change j.source.left.app _ (yonedaEquiv ρ.1) =
        U.left.map f.op (fibreOfTestPoint (U := U) y).1
      rw [← yonedaEquiv_comp, hρs, restrictTestPoint_val, ← yonedaEquiv_naturality]
      rfl
    · change j.target.left.app _ (yonedaEquiv ρ.1) =
        U.left.map f.op (fibreOfTestPoint (U := U) x).1
      rw [← yonedaEquiv_comp, hρt, restrictTestPoint_val, ← yonedaEquiv_naturality]
      rfl

private theorem equivalence_relAfterExtension (j : PreRelation R U)
    (hj : IsSetTheoreticPreEquivalenceRelation j) (g : GeometricPoint B S hS Z) :
    Equivalence (RelAfterExtension j g.val) := by
  have := g.property
  have h := hj g.val.carrier g.val.contained g.val.toBase g.val.value
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact (setTheoreticRel_iff_relAfterExtension j g.val x x).mp (h.refl _)
  · intro x y hxy
    exact (setTheoreticRel_iff_relAfterExtension j g.val y x).mp
      (h.symm ((setTheoreticRel_iff_relAfterExtension j g.val x y).mpr hxy))
  · intro x y z hxy hyz
    exact (setTheoreticRel_iff_relAfterExtension j g.val x z).mp
      (h.trans ((setTheoreticRel_iff_relAfterExtension j g.val y z).mpr hyz)
        ((setTheoreticRel_iff_relAfterExtension j g.val x y).mpr hxy))

private theorem equivalence_setTheoreticRel (j : PreRelation R U)
    (b : FieldValuedPoint B S hS Z) (h : Equivalence (RelAfterExtension j b)) :
    Equivalence (j.SetTheoreticRel b.carrier b.contained b.toBase b.value) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    have hv := (setTheoreticRel_iff_relAfterExtension j b (testPointOfFibre v)
      (testPointOfFibre v)).mpr (h.refl _)
    rwa [fibreOfTestPoint_testPointOfFibre] at hv
  · intro v w hvw
    have h₁ : RelAfterExtension j b (testPointOfFibre w) (testPointOfFibre v) := by
      refine (setTheoreticRel_iff_relAfterExtension j b (testPointOfFibre w)
        (testPointOfFibre v)).mp ?_
      rwa [fibreOfTestPoint_testPointOfFibre, fibreOfTestPoint_testPointOfFibre]
    have h₂ := (setTheoreticRel_iff_relAfterExtension j b (testPointOfFibre v)
      (testPointOfFibre w)).mpr (h.symm h₁)
    rwa [fibreOfTestPoint_testPointOfFibre, fibreOfTestPoint_testPointOfFibre] at h₂
  · intro u v w huv hvw
    have h₁ : RelAfterExtension j b (testPointOfFibre v) (testPointOfFibre u) := by
      refine (setTheoreticRel_iff_relAfterExtension j b (testPointOfFibre v)
        (testPointOfFibre u)).mp ?_
      rwa [fibreOfTestPoint_testPointOfFibre, fibreOfTestPoint_testPointOfFibre]
    have h₂ : RelAfterExtension j b (testPointOfFibre w) (testPointOfFibre v) := by
      refine (setTheoreticRel_iff_relAfterExtension j b (testPointOfFibre w)
        (testPointOfFibre v)).mp ?_
      rwa [fibreOfTestPoint_testPointOfFibre, fibreOfTestPoint_testPointOfFibre]
    have h₃ := (setTheoreticRel_iff_relAfterExtension j b (testPointOfFibre w)
      (testPointOfFibre u)).mpr (h.trans h₂ h₁)
    rwa [fibreOfTestPoint_testPointOfFibre, fibreOfTestPoint_testPointOfFibre] at h₃

private theorem relAfterExtension_of_weaklyEquivalent (j : PreRelation R U)
    (hj : IsSetTheoreticPreEquivalenceRelation j) (g : GeometricPoint B S hS Z)
    {x y : TestPoint (g.val.siteObject B S hS Z) (yonedaEquiv.symm g.val.value) U}
    (h : j.WeaklyEquivalent g.val x y) : RelAfterExtension j g.val x y := by
  have heq := equivalence_relAfterExtension j hj g
  change Relation.EqvGen (j.Rel (yonedaEquiv.symm g.val.value)) x y at h
  induction h with
  | rel a c hac => exact relAfterExtension_of_rel j hac
  | refl a => exact heq.refl a
  | symm a c _ ih => exact heq.symm ih
  | trans a c e _ _ ih₁ ih₂ => exact heq.trans ih₁ ih₂

private theorem relAfterExtension_of_equivalent (j : PreRelation R U)
    (hj : IsSetTheoreticPreEquivalenceRelation j) (b : FieldValuedPoint B S hS Z)
    {x y : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) U}
    (h : j.Equivalent b x y) : RelAfterExtension j b x y := by
  obtain ⟨q, fq, hfq, x', y', hx', hy', hweak⟩ := h
  obtain ⟨gq, fc, hfc⟩ := exists_geometricPoint_restriction q
  have hweak' := weaklyEquivalent_restrict j fc hfc hweak
  have hcomp : Z.map (fc ≫ fq).op b.value = gq.val.value := by
    rw [op_comp, Functor.map_comp, types_comp_apply, hfq, hfc]
  refine relAfterExtension_restrict j (fc ≫ fq) hcomp ?_
  have hx : restrictTestPoint fc hfc x' = restrictTestPoint (fc ≫ fq) hcomp x := by
    refine Subtype.ext ?_
    rw [restrictTestPoint_val, restrictTestPoint_val, hx', Functor.map_comp, Category.assoc]
  have hy : restrictTestPoint fc hfc y' = restrictTestPoint (fc ≫ fq) hcomp y := by
    refine Subtype.ext ?_
    rw [restrictTestPoint_val, restrictTestPoint_val, hy', Functor.map_comp, Category.assoc]
  rw [← hx, ← hy]
  exact relAfterExtension_of_weaklyEquivalent j hj gq hweak'

/-! ### Surjectivity of the two projections -/

private theorem isSurjective_invarianceToRelation_iff (j : PreRelation R U) (φ : U ⟶ X) :
    IsSurjective B S hS (j.invarianceToRelation φ).left ↔
      ∀ (b : FieldValuedPoint B S hS Z)
        (r : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) R),
        EndpointsAgreeAfterExtension j φ b r := by
  rw [isSurjective_left_iff]
  constructor
  · intro h b r
    obtain ⟨b', f, hf, w, hw⟩ := h b (overHomOfTestPoint r)
    exact ⟨b', f, hf, congrArg (fun k : b'.overObject ⟶ X ↦ k.left)
      ((exists_lift_invarianceToRelation_iff j φ _).mp ⟨w, hw⟩)⟩
  · intro h b y
    obtain ⟨b', f, hf, hagree⟩ := h b (testPointOfOverHom y)
    exact ⟨b', f, hf, (exists_lift_invarianceToRelation_iff j φ
      (FieldValuedPoint.overObjectHom f hf ≫ y)).mpr (Over.OverMorphism.ext hagree)⟩

private theorem isSurjective_invarianceToSelfFibreProduct_iff (j : PreRelation R U)
    (φ : U ⟶ X) :
    IsSurjective B S hS (j.invarianceToSelfFibreProduct φ).left ↔
      ∀ (b : FieldValuedPoint B S hS Z)
        (x y : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) U),
        x.1 ≫ φ.left = y.1 ≫ φ.left → RelAfterExtension j b x y := by
  rw [isSurjective_left_iff]
  constructor
  · intro h b x y hxy
    have hxy' : overHomOfTestPoint x ≫ φ = overHomOfTestPoint y ≫ φ :=
      Over.OverMorphism.ext hxy
    obtain ⟨b', f, hf, w, hw⟩ :=
      h b (pullback.lift (overHomOfTestPoint x) (overHomOfTestPoint y) hxy')
    obtain ⟨ρ, ht, hs⟩ :=
      (exists_lift_invarianceToSelfFibreProduct_iff j φ _).mp ⟨w, hw⟩
    rw [Category.assoc, pullback.lift_fst] at ht
    rw [Category.assoc, pullback.lift_snd] at hs
    exact ⟨b', f, hf, testPointOfOverHom ρ,
      congrArg (fun k : b'.overObject ⟶ U ↦ k.left) ht,
      congrArg (fun k : b'.overObject ⟶ U ↦ k.left) hs⟩
  · intro h b a
    have hcond : (testPointOfOverHom (a ≫ pullback.fst φ φ)).1 ≫ φ.left =
        (testPointOfOverHom (a ≫ pullback.snd φ φ)).1 ≫ φ.left := by
      have := congrArg (fun k : b.overObject ⟶ X ↦ k.left)
        (show a ≫ pullback.fst φ φ ≫ φ = a ≫ pullback.snd φ φ ≫ φ by
          rw [pullback.condition])
      change (a ≫ pullback.fst φ φ).left ≫ φ.left = (a ≫ pullback.snd φ φ).left ≫ φ.left
      simpa only [Over.comp_left, Category.assoc] using this
    obtain ⟨b', f, hf, ρ, ht, hs⟩ := h b _ _ hcond
    refine ⟨b', f, hf, ?_⟩
    refine (exists_lift_invarianceToSelfFibreProduct_iff j φ
      (FieldValuedPoint.overObjectHom f hf ≫ a)).mpr ⟨overHomOfTestPoint ρ, ?_, ?_⟩
    · refine Over.OverMorphism.ext ?_
      change ρ.1 ≫ j.target.left =
        (FieldValuedPoint.overObjectHom f hf ≫ a).left ≫ (pullback.fst φ φ).left
      rw [ht, restrictTestPoint_val]
      rfl
    · refine Over.OverMorphism.ext ?_
      change ρ.1 ≫ j.source.left =
        (FieldValuedPoint.overObjectHom f hf ≫ a).left ≫ (pullback.snd φ φ).left
      rw [hs, restrictTestPoint_val]
      rfl

/-! ### The four parts of the lemma -/

/-- **Stacks 049Y, part (1).** A morphism `φ : U ⟶ X` over the base, with `X` an algebraic
space, is set-theoretically invariant under a pre-relation `j : R ⟶ U ×_Z U` if and only if
the projection `p : (U ×_X U) ×_{U ×_Z U} R ⟶ R` is surjective. -/
@[stacks 049Y "part (1)"]
theorem isSetTheoreticallyInvariant_iff_isSurjective_invarianceToRelation
    (hX : IsAlgebraicSpace B S hS X.left) (j : PreRelation R U) (φ : U ⟶ X) :
    IsSetTheoreticallyInvariant j φ.left ↔
      IsSurjective B S hS (j.invarianceToRelation φ).left := by
  rw [isSurjective_invarianceToRelation_iff]
  constructor
  · intro hφ b r
    obtain ⟨g, f, hf⟩ := exists_geometricPoint_restriction b
    exact ⟨g.val, f, hf,
      hφ g (mapTestPoint j.target (restrictTestPoint f hf r))
        (mapTestPoint j.source (restrictTestPoint f hf r))
        (j.rel_target_source (restrictTestPoint f hf r))⟩
  · intro h g x y hrel
    obtain ⟨r, hrt, hrs⟩ := hrel
    obtain ⟨b', f, hf, hagree⟩ := h g.val r
    refine eq_of_comp_yoneda_map_eq hX f ?_
    simpa only [Category.assoc, reassoc_of% hrt, reassoc_of% hrs] using hagree

/-- **Stacks 049Y, part (3).** If both projections of the square are surjective, then the
morphism `φ` separates the orbits of the pre-relation. -/
@[stacks 049Y "part (3): separation of orbits"]
theorem separatesOrbits_of_isSurjective (hX : IsAlgebraicSpace B S hS X.left)
    (j : PreRelation R U) (φ : U ⟶ X)
    (hp : IsSurjective B S hS (j.invarianceToRelation φ).left)
    (hq : IsSurjective B S hS (j.invarianceToSelfFibreProduct φ).left) :
    SeparatesOrbits j φ.left := by
  refine ⟨(isSetTheoreticallyInvariant_iff_isSurjective_invarianceToRelation hX j φ).mpr hp,
    ?_⟩
  rw [isSurjective_invarianceToSelfFibreProduct_iff] at hq
  intro g x y hxy
  exact equivalent_of_relAfterExtension j (hq g.val x y hxy)

/-- Over a field-valued point of `Z`, if both projections of the square are surjective then
two points of `U` are the endpoints of an arrow of the pre-relation after one extension of
the field exactly when they have the same image under `φ`. -/
private theorem relAfterExtension_iff_eq_comp (hX : IsAlgebraicSpace B S hS X.left)
    (j : PreRelation R U) (φ : U ⟶ X)
    (hp : ∀ (b : FieldValuedPoint B S hS Z)
      (r : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) R),
      EndpointsAgreeAfterExtension j φ b r)
    (hq : ∀ (b : FieldValuedPoint B S hS Z)
      (x y : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) U),
      x.1 ≫ φ.left = y.1 ≫ φ.left → RelAfterExtension j b x y)
    (b : FieldValuedPoint B S hS Z)
    (x y : TestPoint (b.siteObject B S hS Z) (yonedaEquiv.symm b.value) U) :
    RelAfterExtension j b x y ↔ x.1 ≫ φ.left = y.1 ≫ φ.left := by
  refine ⟨?_, hq b x y⟩
  rintro ⟨b', f, hf, r, h₁, h₂⟩
  obtain ⟨b'', f', hf', hagree⟩ := hp b' r
  refine eq_of_comp_yoneda_map_eq hX (f' ≫ f) ?_
  simpa only [Functor.map_comp, Category.assoc, reassoc_of% h₁, reassoc_of% h₂,
    restrictTestPoint_val] using hagree

/-- **Stacks 049Y, part (3).** If both projections of the square are surjective, then the
pre-relation is a set-theoretic pre-equivalence relation. -/
@[stacks 049Y "part (3): set-theoretic pre-equivalence relation"]
theorem isSetTheoreticPreEquivalenceRelation_of_isSurjective
    (hX : IsAlgebraicSpace B S hS X.left) (j : PreRelation R U) (φ : U ⟶ X)
    (hp : IsSurjective B S hS (j.invarianceToRelation φ).left)
    (hq : IsSurjective B S hS (j.invarianceToSelfFibreProduct φ).left) :
    IsSetTheoreticPreEquivalenceRelation j := by
  rw [isSurjective_invarianceToRelation_iff] at hp
  rw [isSurjective_invarianceToSelfFibreProduct_iff] at hq
  intro k _ _ hk bb β
  refine equivalence_setTheoreticRel j ⟨k, hk, bb, β⟩ ⟨fun x ↦ ?_, fun hxy ↦ ?_,
    fun hxy hyz ↦ ?_⟩
  · exact (relAfterExtension_iff_eq_comp hX j φ hp hq _ x x).mpr rfl
  · exact (relAfterExtension_iff_eq_comp hX j φ hp hq _ _ _).mpr
      ((relAfterExtension_iff_eq_comp hX j φ hp hq _ _ _).mp hxy).symm
  · exact (relAfterExtension_iff_eq_comp hX j φ hp hq _ _ _).mpr
      (((relAfterExtension_iff_eq_comp hX j φ hp hq _ _ _).mp hxy).trans
        ((relAfterExtension_iff_eq_comp hX j φ hp hq _ _ _).mp hyz))

/-- **Stacks 049Y, part (2).** For a set-theoretic pre-equivalence relation, a morphism
`φ : U ⟶ X` over the base, with `X` an algebraic space, separates the orbits of the
pre-relation if and only if both projections `p` and `q` of the square are surjective. -/
@[stacks 049Y "part (2)"]
theorem separatesOrbits_iff_isSurjective (hX : IsAlgebraicSpace B S hS X.left)
    (j : PreRelation R U) (φ : U ⟶ X) (hj : IsSetTheoreticPreEquivalenceRelation j) :
    SeparatesOrbits j φ.left ↔
      (IsSurjective B S hS (j.invarianceToRelation φ).left ∧
        IsSurjective B S hS (j.invarianceToSelfFibreProduct φ).left) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ separatesOrbits_of_isSurjective hX j φ h.1 h.2⟩
  · exact (isSetTheoreticallyInvariant_iff_isSurjective_invarianceToRelation hX j φ).mp h.1
  · rw [isSurjective_invarianceToSelfFibreProduct_iff]
    intro b x y hxy
    obtain ⟨g, f, hf⟩ := exists_geometricPoint_restriction b
    refine relAfterExtension_restrict j f hf ?_
    refine relAfterExtension_of_equivalent j hj g.val ?_
    refine h.2 g (restrictTestPoint f hf x) (restrictTestPoint f hf y) ?_
    rw [restrictTestPoint_val, restrictTestPoint_val, Category.assoc, Category.assoc, hxy]

/-! ### The induced morphism from the relation -/

/-- The morphism `(t, s) : R ⟶ U ×_X U` determined by a morphism `φ` invariant under the
pre-relation. -/
noncomputable def PreRelation.toSelfFibreProduct (j : PreRelation R U) (φ : U ⟶ X)
    (hφ : IsInvariant j φ.left) : R ⟶ selfFibreProduct φ :=
  pullback.lift j.target j.source (Over.OverMorphism.ext hφ)

/-- The composite of `j.toSelfFibreProduct φ hφ` with the first projection of `U ×_X U` is the
target map of `j`. -/
@[simp]
theorem PreRelation.toSelfFibreProduct_fst (j : PreRelation R U) (φ : U ⟶ X)
    (hφ : IsInvariant j φ.left) :
    j.toSelfFibreProduct φ hφ ≫ pullback.fst φ φ = j.target :=
  pullback.lift_fst _ _ _

/-- The composite of `j.toSelfFibreProduct φ hφ` with the second projection of `U ×_X U` is the
source map of `j`. -/
@[simp]
theorem PreRelation.toSelfFibreProduct_snd (j : PreRelation R U) (φ : U ⟶ X)
    (hφ : IsInvariant j φ.left) :
    j.toSelfFibreProduct φ hφ ≫ pullback.snd φ φ = j.source :=
  pullback.lift_snd _ _ _

private theorem isSurjective_toSelfFibreProduct_iff (j : PreRelation R U) (φ : U ⟶ X)
    (hφ : IsInvariant j φ.left) :
    IsSurjective B S hS (j.toSelfFibreProduct φ hφ).left ↔
      IsSurjective B S hS (j.invarianceToSelfFibreProduct φ).left := by
  have key : ∀ {W : Over Z} (a : W ⟶ selfFibreProduct φ),
      (∃ w : W ⟶ R, w ≫ j.toSelfFibreProduct φ hφ = a) ↔
        ∃ d : W ⟶ j.invarianceFibreProduct φ,
          d ≫ j.invarianceToSelfFibreProduct φ = a := by
    intro W a
    rw [exists_lift_invarianceToSelfFibreProduct_iff]
    refine exists_congr fun w ↦ ⟨fun hw ↦ ⟨?_, ?_⟩, fun hw ↦ ?_⟩
    · rw [← hw, Category.assoc, PreRelation.toSelfFibreProduct_fst]
    · rw [← hw, Category.assoc, PreRelation.toSelfFibreProduct_snd]
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, PreRelation.toSelfFibreProduct_fst]
        exact hw.1
      · rw [Category.assoc, PreRelation.toSelfFibreProduct_snd]
        exact hw.2
  rw [isSurjective_left_iff, isSurjective_left_iff]
  exact forall_congr' fun b ↦ forall_congr' fun a ↦ exists_congr fun b' ↦
    exists_congr fun f ↦ exists_congr fun hf ↦ key _

/-- **Stacks 049Y, part (4).** If `φ : U ⟶ X` is invariant under a set-theoretic
pre-equivalence relation `j : R ⟶ U ×_Z U`, with `X` an algebraic space, then `φ` separates
the orbits of `j` if and only if the induced morphism `(t, s) : R ⟶ U ×_X U` is
surjective. -/
@[stacks 049Y "part (4)"]
theorem separatesOrbits_iff_isSurjective_toSelfFibreProduct
    (hX : IsAlgebraicSpace B S hS X.left) (j : PreRelation R U) (φ : U ⟶ X)
    (hφ : IsInvariant j φ.left) (hj : IsSetTheoreticPreEquivalenceRelation j) :
    SeparatesOrbits j φ.left ↔
      IsSurjective B S hS (j.toSelfFibreProduct φ hφ).left := by
  rw [isSurjective_toSelfFibreProduct_iff, separatesOrbits_iff_isSurjective hX j φ hj]
  have hp : IsSurjective B S hS (j.invarianceToRelation φ).left :=
    (isSetTheoreticallyInvariant_iff_isSurjective_invarianceToRelation hX j φ).mp
      (isSetTheoreticallyInvariant_of_isInvariant j φ.left hφ)
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hp, h⟩⟩

end AlgebraicGeometry.Space

end
