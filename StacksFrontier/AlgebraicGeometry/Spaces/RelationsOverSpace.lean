module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic

/-!
# Relations and equivalence relations on an algebraic space over an algebraic space

Fix a scheme `S` contained in a big fppf site `B`, and let `Z` be an algebraic space over
`S`. A *pre-relation* on an algebraic space `U` over `Z` is a morphism `j : R ⟶ U ×_Z U` of
algebraic spaces over `Z`; its two components are the *target* and *source* maps
`t, s : R ⟶ U`. A pre-relation induces, for every scheme `T` over `Z`, a binary relation on
the `T`-valued points of `U`: two points are related when they are the target and the
source of a common `T`-valued point of `R`. The pre-relation is a *pre-equivalence
relation* when all of these binary relations are equivalence relations, a *relation* when
`j` is a monomorphism, and an *equivalence relation* when both hold.

## Main definitions

* `AlgebraicGeometry.Space.PreRelation` is a pre-relation on an algebraic space over `Z`,
  stated for an arbitrary category with binary products so that the single notion also
  serves the slice of `AlgebraicGeometry.AlgebraicSpaces` over an algebraic space, where
  `StacksFrontier/AlgebraicGeometry/Spaces/InvariantMorphisms.lean` states invariance.
* `AlgebraicGeometry.Space.PreRelation.target` and
  `AlgebraicGeometry.Space.PreRelation.source` are its two maps to `U`.
* `AlgebraicGeometry.Space.TestPoint` is the set of `T`-valued points over a `Z`-valued
  point of a test scheme `T`, and `AlgebraicGeometry.Space.mapTestPoint` is the action of a
  morphism over `Z` on them.
* `AlgebraicGeometry.Space.PreRelation.Rel` is the induced relation on test points.
* `AlgebraicGeometry.Space.IsPreEquivalenceRelation` is the pointwise equivalence
  condition.
* `CategoryTheory.Mono` expresses that a pre-relation is a relation, and
  `CategoryTheory.IsEquivalenceRelation` that it is an equivalence relation.

## Main results

* `AlgebraicGeometry.Space.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation`:
  the internal categorical equivalence-relation condition on the pair `(t, s)` holds
  exactly when `j` is a monomorphism and the induced relation on the points of every test
  scheme over `Z` is an equivalence relation. This is the identification of parts (2)–(4)
  of the source definition with Mathlib's internal notion.
* `AlgebraicGeometry.Space.PreRelation.rel_target_source`: the target and the source of a
  test point of `R` are related.
* `AlgebraicGeometry.Space.PreRelation.testPoint_eq_of_mono`: for a relation the witness
  exhibiting a related pair is unique.

## Implementation notes

The big fppf site is kept separate from the base: `B` is the site and `Z` is the base
algebraic space, which the source calls `B`. Algebraic spaces over `S` are presheaves on
the big fppf site of `S`, so algebraic spaces over `Z` are objects of
`CategoryTheory.Over Z`, whose categorical product is the fibre product over `Z` — hence a
pre-relation is literally a morphism to a categorical product, exactly as for schemes in
`AlgebraicGeometry.Spaces.EquivalenceRelations`. No binary-product instance has to be
supplied: the presheaf category has all pullbacks, so instance resolution finds products
in the slice.

Everything is stated for arbitrary objects of `CategoryTheory.Over Z`, that is for
arbitrary presheaves over `Z`, and not only for algebraic spaces, exactly as in
`AlgebraicGeometry.Spaces.Morphisms`: no definition and no proof here uses the
algebraic-space axioms, and clients impose `AlgebraicGeometry.IsAlgebraicSpace` where the
source definition does. This also keeps the file independent of Tag 02X2 — algebraicity of
a fibre product of algebraic spaces — and of Tag 025Z — that a representable presheaf is
an algebraic space. Restricting along the full subcategory of algebraic spaces loses
nothing: that inclusion is full and faithful, and by Tag 02X2 the presheaf fibre product
of algebraic spaces is again their product there, so for algebraic `R`, `U` and `Z` the
notions defined here are the notions of the source.

A test scheme `T` over `Z` is an object of the big fppf site of `S` together with a
morphism `b` from its representable presheaf to `Z`; its `U`-valued points are the
morphisms to `U` over `b`, which is `AlgebraicGeometry.Space.TestPoint`. Quantifying over
test *schemes* rather than over all objects of `CategoryTheory.Over Z` is what the source
asks for; the two are equivalent only through the existence of étale atlases, which is not
used here.

## References

* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Test points -/

/-- The `X`-valued points of a test scheme `T` over the base `Z`, that is the morphisms
from the presheaf represented by `T` to `X` lying over the given `Z`-valued point `b`
of `T`. -/
abbrev TestPoint (T : BigFppfOver B S hS) (b : yoneda.obj T ⟶ Z) (X : Over Z) :=
  { f : yoneda.obj T ⟶ X.left // f ≫ X.hom = b }

/-- Push a test point forward along a morphism over the base. -/
def mapTestPoint {T : BigFppfOver B S hS} {b : yoneda.obj T ⟶ Z} {X Y : Over Z}
    (f : X ⟶ Y) (x : TestPoint T b X) : TestPoint T b Y :=
  ⟨x.1 ≫ f.left, by rw [Category.assoc, Over.w f, x.2]⟩

/-- A test point of `X` over `b`, read as a morphism over `Z` out of the object `b`
of the slice. -/
private def testPointArrow {T : BigFppfOver B S hS} {b : yoneda.obj T ⟶ Z} {X : Over Z}
    (x : TestPoint T b X) : (Over.mk b : Over Z) ⟶ X :=
  Over.homMk x.1 x.2

/-! ### Pre-relations -/

section Ambient

variable {C : Type*} [Category C] [HasBinaryProducts C]

/-- **Stacks 043C, part (1).** A *pre-relation* from `R` to `U` is a morphism from `R` to
the product `U ⨯ U`.

This is stated for an arbitrary category with binary products because the two bases it is
taken over are different categories. Over a base algebraic space `Z` it is instantiated at
the slice `CategoryTheory.Over Z` of presheaves on the big fppf site, whose categorical
product is the fibre product `U ×_Z U`, which is the notion of the source; over an
algebraic space `B` it is instantiated at the slice `CategoryTheory.Over B` of the category
`AlgebraicGeometry.AlgebraicSpaces`, which is the shape the invariance notions of **Stacks
048E** in `StacksFrontier/AlgebraicGeometry/Spaces/InvariantMorphisms.lean` are stated at. -/
@[stacks 043C "part (1): pre-relation"]
abbrev PreRelation (R U : C) := R ⟶ U ⨯ U

namespace PreRelation

variable {R U : C} (j : PreRelation R U)

/-- **Stacks 043C, part (1).** The *target* map of a pre-relation, its composite with the
first projection of the product. -/
@[stacks 043C "part (1): target"]
noncomputable abbrev target : R ⟶ U := j ≫ prod.fst

/-- **Stacks 043C, part (1).** The *source* map of a pre-relation, its composite with the
second projection of the product. -/
@[stacks 043C "part (1): source"]
noncomputable abbrev source : R ⟶ U := j ≫ prod.snd

end PreRelation

end Ambient

namespace PreRelation

variable {R U : Over Z} (j : PreRelation R U)

/-- The relation induced by a pre-relation on the `U`-valued points of a test scheme `T`
over the base: two points are related when they are the target and the source of a common
`R`-valued point of `T`. -/
abbrev Rel {T : BigFppfOver B S hS} (b : yoneda.obj T ⟶ Z)
    (x y : TestPoint T b U) : Prop :=
  ∃ r : TestPoint T b R, (r.1 ≫ j.target.left = x.1) ∧ (r.1 ≫ j.source.left = y.1)

/-- The target and the source of a test point of `R` are related. -/
theorem rel_target_source {T : BigFppfOver B S hS} {b : yoneda.obj T ⟶ Z}
    (r : TestPoint T b R) :
    j.Rel b (mapTestPoint j.target r) (mapTestPoint j.source r) :=
  ⟨r, rfl, rfl⟩

/-- For a *relation*, that is a monic pre-relation, the test point of `R` exhibiting a
related pair of test points of `U` is unique. -/
theorem testPoint_eq_of_mono [Mono j] {T : BigFppfOver B S hS} {b : yoneda.obj T ⟶ Z}
    {x y : TestPoint T b U} {r s : TestPoint T b R}
    (hr₁ : r.1 ≫ j.target.left = x.1) (hr₂ : r.1 ≫ j.source.left = y.1)
    (hs₁ : s.1 ≫ j.target.left = x.1) (hs₂ : s.1 ≫ j.source.left = y.1) : r.1 = s.1 := by
  have hcomp : testPointArrow r ≫ j = testPointArrow s ≫ j := by
    apply prod.hom_ext
    · apply CategoryTheory.Over.OverMorphism.ext
      simpa [testPointArrow, target, Category.assoc] using hr₁.trans hs₁.symm
    · apply CategoryTheory.Over.OverMorphism.ext
      simpa [testPointArrow, source, Category.assoc] using hr₂.trans hs₂.symm
  have heq : testPointArrow r = testPointArrow s := (cancel_mono j).mp hcomp
  exact congrArg (fun f ↦ f.left) heq

end PreRelation

/-- **Stacks 043C, part (3).** A pre-relation is a *pre-equivalence relation* when the
relation it induces on the `U`-valued points is an equivalence relation for every test
scheme over the base. -/
@[stacks 043C "part (3): pre-equivalence relation"]
abbrev IsPreEquivalenceRelation {R U : Over Z} (j : PreRelation R U) : Prop :=
  ∀ (T : BigFppfOver B S hS) (b : yoneda.obj T ⟶ Z), Equivalence (j.Rel b)

add_to_stacks 043C "part (2): relation" CategoryTheory.Mono
add_to_stacks 043C "part (4): equivalence relation" CategoryTheory.IsEquivalenceRelation

/-! ### The pointwise characterization of an equivalence relation -/

/-- A point `w` of `F` over the point `a` of `G` under `f` and `g` evaluates compatibly. -/
private theorem app_yonedaEquiv_eq_of_comp_eq {T : BigFppfOver B S hS}
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (w : yoneda.obj T ⟶ F) (a : G.obj (op T))
    (f : F ⟶ H) (g : G ⟶ H) (h : w ≫ f = yonedaEquiv.symm a ≫ g) :
    f.app (op T) (yonedaEquiv w) = g.app (op T) a := by
  simpa [yonedaEquiv_comp] using congrArg yonedaEquiv h

/-- Build a morphism over the base out of pointwise witnesses: if `j` is monic and every
test point of `X` admits a test point of `R` whose target and source are its images under
`p` and `q`, then those witnesses assemble into a morphism `X ⟶ R` over `Z` satisfying
`r ≫ t = p` and `r ≫ s = q`.

Monicity is what makes the construction natural: it forces the witness chosen over a test
scheme to restrict to the witness chosen over any smaller one. -/
private noncomputable def liftPointwiseRelation {X R U : Over Z}
    (j : PreRelation R U) (p q : X ⟶ U)
    (h : ∀ (T : BigFppfOver B S hS) (b : yoneda.obj T ⟶ Z) (x : TestPoint T b X),
      ∃ r : TestPoint T b R,
        r.1 ≫ j.target.left = x.1 ≫ p.left ∧ r.1 ≫ j.source.left = x.1 ≫ q.left)
    [Mono j] : { r : X ⟶ R // r ≫ j.target = p ∧ r ≫ j.source = q } := by
  let chooseWitness (T : BigFppfOver B S hS) (a : X.left.obj (op T)) :
      TestPoint T ((yonedaEquiv.symm a) ≫ X.hom) R :=
    Classical.choose (h T ((yonedaEquiv.symm a) ≫ X.hom) ⟨yonedaEquiv.symm a, rfl⟩)
  have hw (T : BigFppfOver B S hS) (a : X.left.obj (op T)) :
      (chooseWitness T a).1 ≫ j.target.left = yonedaEquiv.symm a ≫ p.left ∧
        (chooseWitness T a).1 ≫ j.source.left = yonedaEquiv.symm a ≫ q.left := by
    simpa [PreRelation.target, PreRelation.source] using
      Classical.choose_spec (h T ((yonedaEquiv.symm a) ≫ X.hom) ⟨yonedaEquiv.symm a, rfl⟩)
  let α : X.left ⟶ R.left :=
    { app := fun Y ↦ TypeCat.ofHom fun (a : X.left.obj Y) ↦ by
        have a' : X.left.obj (op Y.unop) := by simpa using a
        simpa using yonedaEquiv (chooseWitness Y.unop a').1
      naturality := by
        intro Y Y' f
        ext a
        let T₀ := Y.unop
        let T₁ := Y'.unop
        let g : T₁ ⟶ T₀ := f.unop
        let w₀ := chooseWitness T₀ (by simpa using a)
        let a₁ := X.left.map f a
        let w₁ := chooseWitness T₁ (by simpa using a₁)
        have hx : yonedaEquiv.symm a₁ = yoneda.map g ≫ yonedaEquiv.symm a := by
          apply yonedaEquiv.injective
          simpa [a₁, g] using (yonedaEquiv_naturality (yonedaEquiv.symm a) g)
        let w₀' : TestPoint T₁ ((yonedaEquiv.symm a₁) ≫ X.hom) R :=
          ⟨yoneda.map g ≫ w₀.1, by simp only [Category.assoc, w₀.2, hx]⟩
        let x₁ : TestPoint T₁ ((yonedaEquiv.symm a₁) ≫ X.hom) U :=
          ⟨yonedaEquiv.symm a₁ ≫ p.left, by
            rw [Category.assoc, Over.w p]⟩
        let y₁ : TestPoint T₁ ((yonedaEquiv.symm a₁) ≫ X.hom) U :=
          ⟨yonedaEquiv.symm a₁ ≫ q.left, by
            rw [Category.assoc, Over.w q]⟩
        obtain ⟨hw₀t, hw₀s⟩ : w₀.1 ≫ j.target.left = yonedaEquiv.symm a ≫ p.left ∧
            w₀.1 ≫ j.source.left = yonedaEquiv.symm a ≫ q.left := hw T₀ _
        have h₁ : w₀'.1 ≫ j.target.left = x₁.1 := by
          simp only [w₀', x₁, Category.assoc, hw₀t, hx]
        have h₂ : w₀'.1 ≫ j.source.left = y₁.1 := by
          simp only [w₀', y₁, Category.assoc, hw₀s, hx]
        have huniq : w₀'.1 = w₁.1 :=
          PreRelation.testPoint_eq_of_mono j (x := x₁) (y := y₁) h₁ h₂ (hw T₁ a₁).1 (hw T₁ a₁).2
        calc
          yonedaEquiv w₁.1 = yonedaEquiv (yoneda.map g ≫ w₀.1) :=
            congrArg yonedaEquiv huniq.symm
          _ = R.left.map f (yonedaEquiv w₀.1) := by
            symm
            simpa [g] using (yonedaEquiv_naturality w₀.1 g) }
  let r : X ⟶ R := Over.homMk α (by
    ext T a
    exact app_yonedaEquiv_eq_of_comp_eq _ a R.hom X.hom (chooseWitness T.unop a).2)
  refine ⟨r, ?_, ?_⟩
  · exact Over.OverMorphism.ext (by
      ext T a
      exact app_yonedaEquiv_eq_of_comp_eq _ a _ _ (hw T.unop a).1)
  · exact Over.OverMorphism.ext (by
      ext T a
      exact app_yonedaEquiv_eq_of_comp_eq _ a _ _ (hw T.unop a).2)


/-- **Stacks 043C, parts (2)-(4).** A pre-relation of algebraic spaces over `Z` is an
internal categorical equivalence relation exactly when it is a monomorphism and the
relation it induces on the points of every test scheme over `Z` is an equivalence
relation. -/
@[stacks 043C "parts (2)-(4): pointwise characterization"]
theorem isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation
    {R U : Over Z} (j : PreRelation R U) :
    CategoryTheory.IsEquivalenceRelation j.target j.source ↔
      (CategoryTheory.Mono j ∧ IsPreEquivalenceRelation j) := by
  constructor
  · rintro ⟨⟨e⟩⟩
    constructor
    · constructor
      intro T f g hfg
      apply e.right_cancellation
      · simpa [PreRelation.target, Category.assoc] using
          congrArg (fun k ↦ k ≫ prod.fst) hfg
      · simpa [PreRelation.source, Category.assoc] using
          congrArg (fun k ↦ k ≫ prod.snd) hfg
    · intro T b
      constructor
      · intro x
        refine ⟨⟨x.1 ≫ e.r.left, ?_⟩, ?_, ?_⟩
        · rw [Category.assoc, Over.w e.r, x.2]
        · rw [Category.assoc, ← Over.comp_left, e.reflexivity₁]; simp
        · rw [Category.assoc, ← Over.comp_left, e.reflexivity₂]; simp
      · intro x y hxy
        rcases hxy with ⟨r, hr₁, hr₂⟩
        refine ⟨⟨r.1 ≫ e.s.left, ?_⟩, ?_, ?_⟩
        · rw [Category.assoc, Over.w e.s, r.2]
        · rw [Category.assoc, ← Over.comp_left, e.symmetry₁]; exact hr₂
        · rw [Category.assoc, ← Over.comp_left, e.symmetry₂]; exact hr₁
      · intro x y z hxy hyz
        rcases hxy with ⟨r, hr₁, hr₂⟩
        rcases hyz with ⟨r', hr₁', hr₂'⟩
        let T' : Over Z := Over.mk b
        let r'₁ : T' ⟶ R := Over.homMk r.1 r.2
        let r'₂ : T' ⟶ R := Over.homMk r'.1 r'.2
        have hmatch : r'₁ ≫ j.source = r'₂ ≫ j.target :=
          CategoryTheory.Over.OverMorphism.ext (hr₂.trans hr₁'.symm)
        let l := PullbackCone.IsLimit.lift e.isLimit r'₁ r'₂ hmatch
        have hl₁ : l ≫ e.c.fst = r'₁ :=
          PullbackCone.IsLimit.lift_fst e.isLimit r'₁ r'₂ hmatch
        have hl₂ : l ≫ e.c.snd = r'₂ :=
          PullbackCone.IsLimit.lift_snd e.isLimit r'₁ r'₂ hmatch
        refine ⟨⟨(l ≫ e.t).left, Over.w (l ≫ e.t)⟩, ?_, ?_⟩
        · rw [← Over.comp_left, Category.assoc, e.transitivity₁, ← Category.assoc, hl₁]
          exact hr₁
        · rw [← Over.comp_left, Category.assoc, e.transitivity₂, ← Category.assoc, hl₂]
          exact hr₂'
  · rintro ⟨hj, he⟩
    have : Mono j := hj
    have h_joint : CategoryTheory.JointlyMono₂ j.target j.source := by
      constructor
      intro Y f g h₁ h₂
      apply (cancel_mono j).mp
      apply prod.hom_ext
      · simpa [PreRelation.target, Category.assoc] using h₁
      · simpa [PreRelation.source, Category.assoc] using h₂
    let reflData := liftPointwiseRelation j (𝟙 U) (𝟙 U) (by
      intro T b x
      rcases (he T b).refl x with ⟨r, hr₁, hr₂⟩
      refine ⟨r, ?_, ?_⟩
      · simpa using hr₁
      · simpa using hr₂)
    let h_refl : ReflexiveRelation j.target j.source :=
      { toJointlyMono₂ := h_joint
        r := reflData.val
        reflexivity₁ := by simpa using reflData.property.1
        reflexivity₂ := by simpa using reflData.property.2 }
    let symmData := liftPointwiseRelation j j.source j.target (by
      intro T b x
      exact (he T b).symm
        (⟨x, rfl, rfl⟩ : j.Rel b (mapTestPoint j.target x) (mapTestPoint j.source x)))
    let h_symm : SymmetricRelation j.target j.source :=
      { toJointlyMono₂ := h_joint
        s := symmData.val
        symmetry₁ := by simpa using symmData.property.1
        symmetry₂ := by simpa using symmData.property.2 }
    let c : PullbackCone j.source j.target := pullback.cone j.source j.target
    let transData := liftPointwiseRelation j (c.fst ≫ j.target) (c.snd ≫ j.source) (by
      intro T b x
      let r₁ := mapTestPoint c.fst x
      let r₂ := mapTestPoint c.snd x
      let xt := mapTestPoint j.target r₁
      let ym := mapTestPoint j.source r₁
      let zt := mapTestPoint j.source r₂
      have hmid : ym.1 = (mapTestPoint j.target r₂).1 := by
        change x.1 ≫ c.fst.left ≫ j.source.left = x.1 ≫ c.snd.left ≫ j.target.left
        simpa [Category.assoc] using congrArg (fun k ↦ x.1 ≫ k.left) c.condition
      have hrel₁ : j.Rel b xt ym := ⟨r₁, rfl, rfl⟩
      have hrel₂ : j.Rel b ym zt := ⟨r₂, hmid.symm, rfl⟩
      rcases (he T b).trans hrel₁ hrel₂ with ⟨r, hr₁, hr₂⟩
      refine ⟨r, ?_, ?_⟩
      · simpa [xt, r₁, mapTestPoint, Category.assoc] using hr₁
      · simpa [zt, r₂, mapTestPoint, Category.assoc] using hr₂)
    let h_trans : TransitiveRelation j.target j.source :=
      { toJointlyMono₂ := h_joint
        c := c
        isLimit := pullback.isLimit j.source j.target
        t := transData.val
        transitivity₁ := by simpa using transData.property.1
        transitivity₂ := by simpa using transData.property.2 }
    exact EquivalenceRelation.isEquivalenceRelation
      { __ := h_refl
        __ := h_symm
        __ := h_trans }

end AlgebraicGeometry.Space

end
