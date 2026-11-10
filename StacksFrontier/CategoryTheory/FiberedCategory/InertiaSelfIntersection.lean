module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.RelativeInertia
public import StacksFrontier.CategoryTheory.TwoFibreProductOver
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift

/-!
# The self-intersection of a point and the base change of the inertia along it

Fix a base category `𝒞`, categories `𝒰` and `𝒳` over `𝒞` with structure functors `p𝒰` and
`p𝒳`, and a 1-morphism `X : 𝒰 ⥤ 𝒳` over `𝒞` (so `X ⋙ p𝒳 = p𝒰`). Two 2-fibre products over
`𝒞` (**Stacks 0040**) are attached to these data:

```text
ℛ = 𝒰 ×_{X, 𝒳, X} 𝒰             the self-intersection of Stacks 04T4
𝒫 = ℐ_𝒳 ×_{π, 𝒳, X} 𝒰           the base change along X of the inertia of Stacks 034I
```

An object of `ℛ` over `W` is a triple `(a, b, ψ)` with `a`, `b` over `W` and `ψ : X a ≅ X b`
vertical; an object of `𝒫` over `W` is a triple `((y, α), a, φ)` with `α` an automorphism of `y`
lying over an identity, `a` over `W` and `φ : y ≅ X a` vertical. Sending `((y, α), a, φ)` to
`(a, a, φ⁻¹ ∘ α ∘ φ)` is a functor `𝒫 ⥤ ℛ` with no hypotheses at all; this file constructs a
functor in the other direction, from `ℛ`, whose projection to `𝒰` is a base change of `X`, to
`𝒫`, whose projection to `𝒰` is the one being studied.

**This file builds `ℛ ⥤ 𝒫` and proves it is an equivalence**, from exactly two inputs:

* `CategoryTheory.InertiaSelfIntersection.SeparationData`, a vertical identification
  `ψ_R : R.x ≅ R.y` of the two ends of each object of `ℛ`. This is what turns the comparison
  isomorphism of an object of `ℛ` into an *automorphism* of `X R.x`, and it is the only place
  where anything about `X` is used. For a section of a gerbe it is
  `AlgebraicGeometry.Stack.nonempty_iso_fiber_of_iso_section_image`.
* `CategoryTheory.InertiaSelfIntersection.ThinData`, uniqueness of morphisms of `𝒰` lying over a
  fixed morphism of `𝒞`. This is thinness of the fibres of `p𝒰`
  (`CategoryTheory.Functor.hom_unique_of_fiber_isThin`), which holds when `𝒰` is a category
  fibred in setoids — in particular when it is representable (**Stacks 02ZX**).

Neither input mentions a gerbe, a topology, or an algebraic structure: the comparison is a
statement about categories over a base.

## Main definitions

* `CategoryTheory.InertiaSelfIntersection.Relation` and `…InertiaBase`: the two 2-fibre
  products `ℛ` and `𝒫` above.
* `CategoryTheory.InertiaSelfIntersection.SeparationData` and `…ThinData`: the two inputs.
* `CategoryTheory.InertiaSelfIntersection.auto` and `…inertiaObj`: the automorphism
  `ψ_R⁻¹ ∘ φ_R` of `X R.x` attached to an object of `ℛ`, and the object of the inertia it names.
* `CategoryTheory.InertiaSelfIntersection.toInertiaBase`: **the comparison functor** `ℛ ⥤ 𝒫`.
* `CategoryTheory.InertiaSelfIntersection.preimage` and `…ofInertiaBase`: the arrow and the
  object of `ℛ` a morphism, resp. an object, of `𝒫` comes from.

## Main results

* `CategoryTheory.InertiaSelfIntersection.toInertiaBase_comp_structureFunctor`: the comparison is
  strictly over `𝒞`.
* `CategoryTheory.InertiaSelfIntersection.toInertiaBase_comp_snd`: composed with the projection
  of `𝒫` to `𝒰` it is the *first* projection of `ℛ`, on the nose.
* `CategoryTheory.InertiaSelfIntersection.faithful_toInertiaBase`,
  `…full_toInertiaBase`, `…essSurj_toInertiaBase` and `…isEquivalence_toInertiaBase`: the
  comparison is an equivalence of categories.

## Implementation notes

Faithfulness needs only that the comparison isomorphism of an object of `𝒫` is invertible: the
`𝒳`-component of a morphism of `𝒫` is determined by its `𝒰`-component. Fullness and essential
surjectivity are where `ThinData` enters — fullness because a morphism of `ℛ` has *two*
components over one morphism of `𝒞` while a morphism of `𝒫` has one, and essential surjectivity
because the separating isomorphism of an object of `ℛ` whose two ends are the same object has to
be recognised as the identity (`sep_ofInertiaBase_inv`).

The three little `IsHomLift` lemmas at the top (`isHomLift_comp_vertical`,
`isHomLift_vertical_comp`, `isHomLift_inv`) take their lifting hypotheses as explicit arguments
rather than as instances. That is deliberate: the objects of a 2-fibre product spell their base
object as a projection, so a lift held in the context is not found by synthesis at the spelling
the goal uses, and passing it explicitly lets defeq do the work. The same reason is why
`isoCancelLeft` and `isoCancelRight` exist rather than a call to `simp`: `simp` matches the
*implicit* type arguments of a composition syntactically, and `(RelativeInertia.π p𝒳).obj P.x`
and `P.x.obj` are the same object spelled two ways.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 02ZX](https://stacks.math.columbia.edu/tag/02ZX)
* [Stacks Project, Tag 034I](https://stacks.math.columbia.edu/tag/034I)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒰 : Type u₂} [Category.{v₂} 𝒰]
  {𝒳 : Type u₃} [Category.{v₃} 𝒳]

namespace InertiaSelfIntersection

variable (p𝒰 : 𝒰 ⥤ 𝒞) (p𝒳 : 𝒳 ⥤ 𝒞) (X : 𝒰 ⥤ 𝒳)

/-- The self-intersection `ℛ = 𝒰 ×_{X, 𝒳, X} 𝒰`. -/
abbrev Relation : Type _ := TwoFibreProductOver p𝒰 p𝒰 p𝒳 X X

/-- The base change `𝒫 = ℐ_𝒳 ×_𝒳 𝒰` of the inertia along `X`. -/
abbrev InertiaBase : Type _ :=
  TwoFibreProductOver (RelativeInertia.π p𝒳 ⋙ p𝒳) p𝒰 p𝒳 (RelativeInertia.π p𝒳) X

/-- A vertical endomorphism of an object is sent by the structure functor to an identity. -/
lemma map_eq_id_of_isHomLift_id {W : 𝒞} {a : 𝒳} (φ : a ⟶ a)
    (h : p𝒳.IsHomLift (𝟙 W) φ) : p𝒳.map φ = 𝟙 (p𝒳.obj a) := by
  have := h
  have hd : p𝒳.obj a = W := IsHomLift.domain_eq p𝒳 (𝟙 W) φ
  rw [IsHomLift.fac' p𝒳 (𝟙 W) φ]
  subst hd
  simp

/-- A morphism of `𝒰` lying over `k` has `X`-image lying over `k`. -/
lemma isHomLift_map (hX : X ⋙ p𝒳 = p𝒰) {k l : 𝒞} (f : k ⟶ l) {a b : 𝒰} (φ : a ⟶ b)
    (h : p𝒰.IsHomLift f φ) : p𝒳.IsHomLift f (X.map φ) := by
  refine (Functor.isHomLift_comp_iff X p𝒳 f φ).1 ?_
  rwa [hX]

/-- A morphism over `f` followed by a vertical morphism lies over `f`. -/
lemma isHomLift_comp_vertical {𝒜 : Type*} [Category 𝒜] (p : 𝒜 ⥤ 𝒞) {R S : 𝒞} {a b c : 𝒜}
    (f : R ⟶ S) (φ : a ⟶ b) (ψ : b ⟶ c) (hφ : p.IsHomLift f φ)
    (hψ : p.IsHomLift (𝟙 S) ψ) : p.IsHomLift f (φ ≫ ψ) :=
  have := hφ
  have := hψ
  inferInstance

/-- A vertical morphism followed by a morphism over `f` lies over `f`. -/
lemma isHomLift_vertical_comp {𝒜 : Type*} [Category 𝒜] (p : 𝒜 ⥤ 𝒞) {R S : 𝒞} {a b c : 𝒜}
    (f : R ⟶ S) (φ : a ⟶ b) (ψ : b ⟶ c) (hφ : p.IsHomLift (𝟙 R) φ)
    (hψ : p.IsHomLift f ψ) : p.IsHomLift f (φ ≫ ψ) :=
  have := hφ
  have := hψ
  inferInstance

/-- The inverse of a vertical isomorphism is vertical. -/
lemma isHomLift_inv {𝒜 : Type*} [Category 𝒜] (p : 𝒜 ⥤ 𝒞) {W : 𝒞} {a b : 𝒜} (e : a ≅ b)
    (h : p.IsHomLift (𝟙 W) e.hom) : p.IsHomLift (𝟙 W) e.inv :=
  have := h
  IsHomLift.lift_id_inv p W e

/-- Conjugating an endomorphism by an isomorphism, read backwards. -/
lemma isoCancelLeft {A B : 𝒳} (e : A ≅ B) (f : A ⟶ A) :
    e.inv ≫ f = (e.inv ≫ f ≫ e.hom) ≫ e.inv := by simp

/-- Conjugating an endomorphism by an isomorphism, read forwards. -/
lemma isoCancelRight {A B : 𝒳} (e : A ≅ B) (f : A ⟶ A) :
    e.hom ≫ e.inv ≫ f ≫ e.hom = f ≫ e.hom := by simp

/-- The data needed to turn an arrow of the self-intersection into an automorphism: a vertical
identification of its two ends. -/
def SeparationData : Type _ :=
  ∀ R : Relation p𝒰 p𝒳 X, { ψ : R.x ≅ R.y // p𝒰.IsHomLift (𝟙 R.base) ψ.hom }

/-- Uniqueness of morphisms over a fixed morphism of the base. -/
abbrev ThinData : Prop :=
  ∀ {R T : 𝒞} (k : R ⟶ T) {a b : 𝒰} (φ₁ φ₂ : a ⟶ b),
    p𝒰.IsHomLift k φ₁ → p𝒰.IsHomLift k φ₂ → φ₁ = φ₂

/-- The automorphism of `X R.x` attached to an object of the self-intersection. -/
def auto (sep : SeparationData p𝒰 p𝒳 X) (R : Relation p𝒰 p𝒳 X) : Aut (X.obj R.x) :=
  .of (R.iso ≪≫ (X.mapIso (sep R).1).symm)

/-- The automorphism attached to an object of the self-intersection lies over an identity: both
of its factors do. -/
lemma isHomLift_auto_hom (hX : X ⋙ p𝒳 = p𝒰) (sep : SeparationData p𝒰 p𝒳 X)
    (R : Relation p𝒰 p𝒳 X) :
    p𝒳.IsHomLift (𝟙 R.base) (auto p𝒰 p𝒳 X sep R).asIso.hom := by
  have h₁ : p𝒳.IsHomLift (𝟙 R.base) R.iso.hom := R.vertical
  have h₂ : p𝒰.IsHomLift (𝟙 R.base) (sep R).1.inv :=
    isHomLift_inv p𝒰 (sep R).1 (sep R).2
  have h₃ : p𝒳.IsHomLift (𝟙 R.base) (X.map (sep R).1.inv) :=
    isHomLift_map p𝒰 p𝒳 X hX (𝟙 R.base) _ h₂
  have := h₁
  have := h₃
  change p𝒳.IsHomLift (𝟙 R.base) (R.iso.hom ≫ X.map (sep R).1.inv)
  infer_instance

/-- The `X`-image of the first end of an object of the self-intersection lies over its base
object. -/
lemma obj_eq_base (hX : X ⋙ p𝒳 = p𝒰) (R : Relation p𝒰 p𝒳 X) :
    p𝒳.obj (X.obj R.x) = R.base := by
  rw [← Functor.comp_obj X p𝒳, hX]
  exact R.hx

/-- The object of the inertia attached to an object of the self-intersection. -/
def inertiaObj (hX : X ⋙ p𝒳 = p𝒰) (sep : SeparationData p𝒰 p𝒳 X)
    (R : Relation p𝒰 p𝒳 X) : RelativeInertia p𝒳 where
  obj := X.obj R.x
  auto := auto p𝒰 p𝒳 X sep R
  cond := map_eq_id_of_isHomLift_id p𝒳 _ (isHomLift_auto_hom p𝒰 p𝒳 X hX sep R)

/-- The comparison functor `ℛ ⥤ 𝒫` from the self-intersection to the base change of the
inertia. -/
def toInertiaBase (hX : X ⋙ p𝒳 = p𝒰) (sep : SeparationData p𝒰 p𝒳 X)
    (thin : ThinData p𝒰) : Relation p𝒰 p𝒳 X ⥤ InertiaBase p𝒰 p𝒳 X where
  obj R :=
    { base := R.base
      x := inertiaObj p𝒰 p𝒳 X hX sep R
      y := R.x
      hx := obj_eq_base p𝒰 p𝒳 X hX R
      hy := R.hx
      iso := Iso.refl _
      vertical := IsHomLift.id (obj_eq_base p𝒰 p𝒳 X hX R) }
  map {R T} h :=
    { hbase := h.hbase
      a :=
        { hom := X.map h.a
          comm := by
            change X.map h.a ≫ (auto p𝒰 p𝒳 X sep T).asIso.hom
              = (auto p𝒰 p𝒳 X sep R).asIso.hom ≫ X.map h.a
            have key : h.b ≫ (sep T).1.inv = (sep R).1.inv ≫ h.a := by
              refine thin h.hbase _ _ ?_ ?_
              · exact isHomLift_comp_vertical p𝒰 h.hbase h.b (sep T).1.inv h.hb
                  (isHomLift_inv p𝒰 (sep T).1 (sep T).2)
              · exact isHomLift_vertical_comp p𝒰 h.hbase (sep R).1.inv h.a
                  (isHomLift_inv p𝒰 (sep R).1 (sep R).2) h.ha
            simp only [auto, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc]
            rw [← Category.assoc, h.w, Category.assoc, ← X.map_comp, key, X.map_comp] }
      b := h.a
      ha := (Functor.isHomLift_comp_iff (RelativeInertia.π p𝒳) p𝒳 h.hbase _).2
        (isHomLift_map p𝒰 p𝒳 X hX h.hbase _ h.ha)
      hb := h.ha
      w := (Category.comp_id (X.map h.a)).trans (Category.id_comp (X.map h.a)).symm }
  map_id R := TwoFibreProductOver.Hom.ext' (RelativeInertiaHom.ext (X.map_id R.x)) rfl
  map_comp f g :=
    TwoFibreProductOver.Hom.ext' (RelativeInertiaHom.ext (X.map_comp f.a g.a)) rfl

/-- A vertical endomorphism condition recognised from the inertia's `cond` field. -/
lemma isHomLift_of_map_eq_id {W : 𝒞} {a : 𝒳} (φ : a ⟶ a)
    (h : p𝒳.map φ = 𝟙 (p𝒳.obj a)) (hb : p𝒳.obj a = W) : p𝒳.IsHomLift (𝟙 W) φ := by
  refine IsHomLift.of_fac' p𝒳 (𝟙 W) φ hb hb ?_
  rw [h]
  subst hb
  simp

variable {p𝒰 p𝒳 X}

/-- The comparison functor is strictly over the base. -/
lemma toInertiaBase_comp_structureFunctor (hX : X ⋙ p𝒳 = p𝒰)
    (sep : SeparationData p𝒰 p𝒳 X) (thin : ThinData p𝒰) :
    toInertiaBase p𝒰 p𝒳 X hX sep thin ⋙
        TwoFibreProductOver.structureFunctor (RelativeInertia.π p𝒳 ⋙ p𝒳) p𝒰 p𝒳
          (RelativeInertia.π p𝒳) X =
      TwoFibreProductOver.structureFunctor p𝒰 p𝒰 p𝒳 X X := rfl

/-- The comparison functor carries the projection to `𝒰` of the base change of the inertia to
the first projection of the self-intersection. -/
lemma toInertiaBase_comp_snd (hX : X ⋙ p𝒳 = p𝒰)
    (sep : SeparationData p𝒰 p𝒳 X) (thin : ThinData p𝒰) :
    toInertiaBase p𝒰 p𝒳 X hX sep thin ⋙
        TwoFibreProductOver.snd (RelativeInertia.π p𝒳 ⋙ p𝒳) p𝒰 p𝒳
          (RelativeInertia.π p𝒳) X =
      TwoFibreProductOver.fst p𝒰 p𝒰 p𝒳 X X := rfl

section Equiv

variable (hX : X ⋙ p𝒳 = p𝒰) (sep : SeparationData p𝒰 p𝒳 X) (thin : ThinData p𝒰)

/-- The comparison functor from the self-intersection to the base change of the inertia is
faithful. -/
instance faithful_toInertiaBase : (toInertiaBase p𝒰 p𝒳 X hX sep thin).Faithful where
  map_injective {R T} f g hfg := by
    have ha : f.a = g.a := congrArg TwoFibreProductOver.Hom.b hfg
    have hbase : f.hbase = g.hbase := by
      rw [TwoFibreProductOver.Hom.hbase_eq, TwoFibreProductOver.Hom.hbase_eq, ha]
    refine TwoFibreProductOver.Hom.ext' ha (thin f.hbase f.b g.b f.hb ?_)
    rw [hbase]
    exact g.hb

/-- The arrow of the self-intersection built from a morphism of the base change of the
inertia. -/
def preimage (sep : SeparationData p𝒰 p𝒳 X)
    {R T : Relation p𝒰 p𝒳 X} (k : R.base ⟶ T.base) (m : R.x ⟶ T.x)
    (hm : p𝒰.IsHomLift k m)
    (hcomm : X.map m ≫ T.iso.hom ≫ X.map (sep T).1.inv
      = (R.iso.hom ≫ X.map (sep R).1.inv) ≫ X.map m) : R ⟶ T where
  hbase := k
  a := m
  b := (sep R).1.inv ≫ m ≫ (sep T).1.hom
  ha := hm
  hb := isHomLift_vertical_comp p𝒰 k _ _ (isHomLift_inv p𝒰 (sep R).1 (sep R).2)
    (isHomLift_comp_vertical p𝒰 k m (sep T).1.hom hm (sep T).2)
  w := by
    have step := congrArg (fun z => z ≫ X.map (sep T).1.hom) hcomm
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
      Category.comp_id] at step
    exact step

/-- The comparison functor from the self-intersection to the base change of the inertia is
full. -/
instance full_toInertiaBase : (toInertiaBase p𝒰 p𝒳 X hX sep thin).Full where
  map_surjective {R T} h := by
    set m : R.x ⟶ T.x := h.b
    have hw : h.a.hom ≫ 𝟙 (X.obj T.x) = 𝟙 (X.obj R.x) ≫ X.map m := h.w
    have e1 : h.a.hom ≫ 𝟙 (X.obj T.x) = h.a.hom := Category.comp_id _
    have e2 : 𝟙 (X.obj R.x) ≫ X.map m = X.map m := Category.id_comp _
    have hah : h.a.hom = X.map m := e1.symm.trans (hw.trans e2)
    refine ⟨preimage sep h.hbase m h.hb ?_, ?_⟩
    · rw [← hah]
      exact h.a.comm
    · refine TwoFibreProductOver.Hom.ext' ?_ rfl
      exact RelativeInertiaHom.ext hah.symm

/-- A morphism of the inertia is vertical as soon as its underlying morphism is. -/
lemma isHomLift_inertiaHom {W : 𝒞} {A B : RelativeInertia p𝒳} (φ : A ⟶ B)
    (h : p𝒳.IsHomLift (𝟙 W) φ.hom) :
    (RelativeInertia.π p𝒳 ⋙ p𝒳).IsHomLift (𝟙 W) φ :=
  (Functor.isHomLift_comp_iff (RelativeInertia.π p𝒳) p𝒳 (𝟙 W) φ).2 h

/-- The object of the self-intersection attached to an object of the base change of the
inertia: the automorphism of `P.x`, conjugated into an automorphism of `X P.y`. -/
abbrev ofInertiaBase (P : InertiaBase p𝒰 p𝒳 X) : Relation p𝒰 p𝒳 X where
  base := P.base
  x := P.y
  y := P.y
  hx := P.hy
  hy := P.hy
  iso := P.iso.symm ≪≫ P.x.auto.asIso ≪≫ P.iso
  vertical := isHomLift_vertical_comp p𝒳 (𝟙 P.base) _ _ (isHomLift_inv p𝒳 P.iso P.vertical)
    (isHomLift_vertical_comp p𝒳 (𝟙 P.base) _ _ (isHomLift_of_map_eq_id p𝒳 _ P.x.cond P.hx)
      P.vertical)

/-- The identity of `P.y` is vertical. -/
lemma isHomLift_id_y (P : InertiaBase p𝒰 p𝒳 X) :
    p𝒰.IsHomLift (𝟙 P.base) (𝟙 P.y) :=
  IsHomLift.id P.hy

include thin in
/-- For that object the separating isomorphism is the identity: both its ends are the same
object, and the fibres are thin. -/
lemma sep_ofInertiaBase_inv (P : InertiaBase p𝒰 p𝒳 X) :
    (sep (ofInertiaBase P)).1.inv = 𝟙 P.y :=
  thin (𝟙 P.base) _ _
    (isHomLift_inv p𝒰 (sep (ofInertiaBase P)).1 (sep (ofInertiaBase P)).2)
    (isHomLift_id_y P)

include thin in
/-- At the object attached to an object `P` of the base change of the inertia, the automorphism
of the comparison is the automorphism of `P` conjugated by the comparison isomorphism of `P`. -/
lemma auto_ofInertiaBase (P : InertiaBase p𝒰 p𝒳 X) :
    (auto p𝒰 p𝒳 X sep (ofInertiaBase P)).asIso.hom
      = P.iso.inv ≫ P.x.auto.asIso.hom ≫ P.iso.hom := by
  change (P.iso.inv ≫ P.x.auto.asIso.hom ≫ P.iso.hom)
      ≫ X.map (sep (ofInertiaBase P)).1.inv
    = P.iso.inv ≫ P.x.auto.asIso.hom ≫ P.iso.hom
  rw [sep_ofInertiaBase_inv sep thin P, X.map_id, Category.comp_id]

/-- The comparison 1-morphism out of the object attached to `P`. -/
def essSurjHom (P : InertiaBase p𝒰 p𝒳 X) :
    (toInertiaBase p𝒰 p𝒳 X hX sep thin).obj (ofInertiaBase P) ⟶ P := by
  refine { hbase := 𝟙 P.base, a := ⟨P.iso.inv, ?_⟩, b := 𝟙 P.y,
           ha := ?_, hb := isHomLift_id_y P, w := ?_ }
  · change P.iso.inv ≫ P.x.auto.asIso.hom
      = (auto p𝒰 p𝒳 X sep (ofInertiaBase P)).asIso.hom ≫ P.iso.inv
    rw [auto_ofInertiaBase sep thin P]
    exact isoCancelLeft P.iso P.x.auto.asIso.hom
  · exact isHomLift_inertiaHom _ (isHomLift_inv p𝒳 P.iso P.vertical)
  · change P.iso.inv ≫ P.iso.hom = 𝟙 (X.obj P.y) ≫ X.map (𝟙 P.y)
    rw [X.map_id, Category.id_comp]
    exact P.iso.inv_hom_id

/-- The comparison 1-morphism into the object attached to `P`. -/
def essSurjInv (P : InertiaBase p𝒰 p𝒳 X) :
    P ⟶ (toInertiaBase p𝒰 p𝒳 X hX sep thin).obj (ofInertiaBase P) := by
  refine { hbase := 𝟙 P.base, a := ⟨P.iso.hom, ?_⟩, b := 𝟙 P.y,
           ha := ?_, hb := isHomLift_id_y P, w := ?_ }
  · change P.iso.hom ≫ (auto p𝒰 p𝒳 X sep (ofInertiaBase P)).asIso.hom
      = P.x.auto.asIso.hom ≫ P.iso.hom
    rw [auto_ofInertiaBase sep thin P]
    exact isoCancelRight P.iso P.x.auto.asIso.hom
  · exact isHomLift_inertiaHom _ P.vertical
  · change P.iso.hom ≫ 𝟙 (X.obj P.y) = P.iso.hom ≫ X.map (𝟙 P.y)
    rw [X.map_id]

/-- The comparison functor hits every object of the base change of the inertia. -/
def essSurjIso (P : InertiaBase p𝒰 p𝒳 X) :
    (toInertiaBase p𝒰 p𝒳 X hX sep thin).obj (ofInertiaBase P) ≅ P where
  hom := essSurjHom hX sep thin P
  inv := essSurjInv hX sep thin P
  hom_inv_id := by
    refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · refine RelativeInertiaHom.ext ?_
      change P.iso.inv ≫ P.iso.hom = 𝟙 (X.obj P.y)
      exact P.iso.inv_hom_id
    · change (𝟙 P.y : P.y ⟶ P.y) ≫ 𝟙 P.y = 𝟙 P.y
      exact Category.id_comp _
  inv_hom_id := by
    refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · refine RelativeInertiaHom.ext ?_
      change P.iso.hom ≫ P.iso.inv = 𝟙 P.x.obj
      exact P.iso.hom_inv_id
    · change (𝟙 P.y : P.y ⟶ P.y) ≫ 𝟙 P.y = 𝟙 P.y
      exact Category.id_comp _

/-- The comparison functor from the self-intersection to the base change of the inertia is
essentially surjective. -/
instance essSurj_toInertiaBase : (toInertiaBase p𝒰 p𝒳 X hX sep thin).EssSurj where
  mem_essImage P := ⟨ofInertiaBase P, ⟨essSurjIso hX sep thin P⟩⟩

/-- The comparison functor from the self-intersection to the base change of the inertia is an
equivalence of categories. -/
instance isEquivalence_toInertiaBase :
    (toInertiaBase p𝒰 p𝒳 X hX sep thin).IsEquivalence where

end Equiv

end InertiaSelfIntersection

end CategoryTheory

end
