module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pushforward squares and their induced functors

A pushforward square in a category cofibered in groupoids, and the functor
between localizations that such a square induces.

## Main definitions

* `PushforwardChoice` records chosen cocartesian
  lifts of a fixed arrow.
* `PushforwardFunctor` records the functor on
  fibres determined by such lifts.
* `PushforwardSquare` packages the two functors
  and the natural isomorphism between their composites.
* `pushforwardFunctorOfChoice` is the functor on fibres forced by a choice of pushforwards.
* `pushforwardComparison` is the comparison isomorphism of the two pushforwards of the image
  of an object, and `pushforwardSquareOfChoices` is the pushforward square it assembles.
* `pushforwardChoiceOfIsCofibered` is a choice of pushforwards in a category cofibered in
  groupoids.
* `inducedFunctorToPullback` is the functor induced
  by the chosen pushforward square.

## Main results

* `pushforwardFunctorsFormTwoCommutativeSquare`
  constructs the pushforward square for a morphism of cofibered categories.
* `pushforwardComparison_hom_fac` characterizes the 2-cell of
  `pushforwardSquareOfChoices` by its compatibility with the chosen cocartesian arrows.

## Implementation notes

### Pushforwards and morphisms of cofibered categories

A morphism of categories over the base is represented by a functor whose
composite with the target projection is equal to the source projection.  The
vertical functors retain their chosen cocartesian arrows, so subsequent results
can use the same choices rather than merely isomorphic replacements.

### The functor induced by a pushforward square

The categorical pullback is Mathlib's category of triples consisting of two
objects and an isomorphism between their images. The induced functor sends an
object `x` to its chosen pushforward, its image under the functor over the base,
and the component at `x` of the pushforward square's natural isomorphism.

## References

* [Stacks Project, Tag 06HI](https://stacks.math.columbia.edu/tag/06HI)
-/

@[expose] public section

namespace Deformation

/-! ### Pushforwards and morphisms of cofibered categories -/

section
open CategoryTheory CategoryTheory.Functor
universe vC uC vF uF vG uG

/-- A morphism lying over `f` lies over `f.op` after passing to opposite categories. -/
private lemma isHomLift_op'
    {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {B A : C} {x y : F} (f : B ⟶ A) (φ : x ⟶ y) [p.IsHomLift f φ] :
    p.op.IsHomLift f.op φ.op := by
  subst_hom_lift p f φ
  exact Functor.IsHomLift.map φ.op

/-- A morphism whose opposite lies over `f.op` for `p.op` lies over `f` for `p`. -/
private lemma isHomLift_unop'
    {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {B A : C} {x y : F} (f : B ⟶ A) (φ : x ⟶ y) [inst : p.op.IsHomLift f.op φ.op] :
    p.IsHomLift f φ := by
  subst_hom_lift p.op f.op φ.op
  exact Functor.IsHomLift.map φ

/-- An arrow lying over `f` whose opposite is strongly cartesian for the opposite projection
is strongly cocartesian. -/
public lemma stronglyCocartesian_of_op_stronglyCartesian
    {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {B A : C} (f : B ⟶ A) {x y : F} (i : x ⟶ y)
    [p.IsHomLift f i] (hi : p.op.IsStronglyCartesian f.op i.op) :
    p.IsStronglyCocartesian f i := by
  let : p.op.IsStronglyCartesian f.op i.op := hi
  refine ⟨?_⟩
  intro z g j hj
  have : p.op.IsHomLift (g.op ≫ f.op) j.op := by
    simpa only [← op_comp] using isHomLift_op' p (f ≫ g) j
  obtain ⟨k, ⟨hk, hfac⟩, huniq⟩ := hi.universal_property' g.op j.op
  refine ⟨k.unop, ⟨isHomLift_unop' p g k.unop (inst := hk), ?_⟩, ?_⟩
  · simpa using congrArg Quiver.Hom.unop hfac
  · intro k' ⟨hk', hfac'⟩
    have hk'op : p.op.IsHomLift g.op k'.op := isHomLift_op' p g k'
    have hfac'op : k'.op ≫ i.op = j.op := by
      simpa using congrArg Quiver.Hom.op hfac'
    exact congrArg Quiver.Hom.unop (huniq k'.op ⟨hk'op, hfac'op⟩)

/-- A functor over the base sends an arrow lying over `f` to a strongly cocartesian arrow,
provided the target projection is cofibered in groupoids. -/
public lemma mapped_cocartesian
    {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
    {G : Type uG} [Category.{vG} G] (pF : F ⥤ C) (pG : G ⥤ C)
    (hG : pG.op.IsFiberedInGroupoids) (φ : F ⥤ G) (hφ : φ ⋙ pG = pF)
    {B A : C} {f : B ⟶ A} {x y : F} (i : x ⟶ y)
    [pF.IsHomLift f i] : pG.IsStronglyCocartesian f (φ.map i) := by
  have : pG.IsHomLift f (φ.map i) := Functor.isHomLift_map_of_comp_eq hφ f i
  have : pG.op.IsHomLift f.op (φ.map i).op := isHomLift_op' pG f (φ.map i)
  exact stronglyCocartesian_of_op_stronglyCartesian pG f (φ.map i)
    (hG.isStronglyCartesian_homLift f.op (φ.map i).op)


/-- Chosen pushforwards of all objects in the fibre over `B` along `f`. -/
public structure PushforwardChoice
    {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {B A : C} (f : B ⟶ A) where
  /-- The chosen pushforward object. -/
  obj : p.Fiber B → p.Fiber A
  /-- The chosen arrow to the pushforward. -/
  inclusion : ∀ x, x.1 ⟶ (obj x).1
  /-- The chosen arrow has the universal property of a pushforward. -/
  cocartesian : ∀ x, p.IsStronglyCocartesian f (inclusion x)

/-- The functor determined by a choice of pushforwards.  Its naturality field
states that its action on arrows is the one forced by the chosen cocartesian
arrows. -/
public structure PushforwardFunctor
    {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {B A : C} {f : B ⟶ A} (P : PushforwardChoice p f) where
  /-- The induced action on morphisms. -/
  map : ∀ {x y : p.Fiber B}, (x ⟶ y) → (P.obj x ⟶ P.obj y)
  map_id : ∀ x, map (𝟙 x) = 𝟙 (P.obj x)
  map_comp : ∀ {x y z} (g : x ⟶ y) (h : y ⟶ z), map (g ≫ h) = map g ≫ map h
  inclusion_naturality : ∀ {x y} (g : x ⟶ y),
    P.inclusion x ≫ Functor.Fiber.fiberInclusion.map (map g) =
      Functor.Fiber.fiberInclusion.map g ≫ P.inclusion y

/-- The pushforward functor underlying `PushforwardFunctor`. -/
public def PushforwardFunctor.toFunctor
    {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {B A : C} {f : B ⟶ A} {P : PushforwardChoice p f}
    (Q : PushforwardFunctor P) : p.Fiber B ⥤ p.Fiber A where
  obj := P.obj
  map := Q.map
  map_id := Q.map_id
  map_comp := Q.map_comp

/-- The pair of chosen pushforward functors and the natural isomorphism making
their square with a functor over the base 2-commutative. -/
public structure PushforwardSquare
    {C : Type uC} [Category.{vC} C]
    {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
    {pF : F ⥤ C} {pG : G ⥤ C} (φ : F ⥤ G) (hφ : φ ⋙ pG = pF)
    {B A : C} {f : B ⟶ A} (PF : PushforwardChoice pF f)
    (PG : PushforwardChoice pG f) where
  /-- The pushforward functor in the source category. -/
  source : PushforwardFunctor PF
  /-- The pushforward functor in the target category. -/
  target : PushforwardFunctor PG
  /-- The 2-cell witnessing commutativity of the square. -/
  comm : source.toFunctor ⋙
      Functor.Fiber.inducedFunctor (p := pG) (S := A)
        (F := Functor.Fiber.fiberInclusion (p := pF) (S := A) ⋙ φ)
        (by simpa only [Functor.assoc, hφ] using
          (Functor.Fiber.fiberInclusion_comp_eq_const (p := pF) (S := A))) ≅
    Functor.Fiber.inducedFunctor (p := pG) (S := B)
        (F := Functor.Fiber.fiberInclusion (p := pF) (S := B) ⋙ φ)
        (by simpa only [Functor.assoc, hφ] using
          (Functor.Fiber.fiberInclusion_comp_eq_const (p := pF) (S := B))) ⋙
      target.toFunctor

/-- An arrow of the fibre over `B` followed by a chosen arrow to a pushforward lies over `f`. -/
public lemma homLift_comp_fiber
    {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {B A : C} {f : B ⟶ A} (P : PushforwardChoice p f)
    {x y : p.Fiber B} (g : x ⟶ y) :
    p.IsHomLift f (Functor.Fiber.fiberInclusion.map g ≫ P.inclusion y) := by
  have : p.IsHomLift f (P.inclusion y) := (P.cocartesian y).toIsHomLift
  simpa [Functor.Fiber.fiberInclusion] using @IsHomLift.comp_lift_id_left' C F _ _ p
    x.1 y.1 (P.obj y).1 B (Functor.Fiber.fiberInclusion.map g) g.2
    B A f (P.inclusion y) (inferInstance : p.IsHomLift f (P.inclusion y))

/-- A chosen arrow to a pushforward followed by an arrow of the fibre over `A` lies over `f`. -/
public lemma homLift_inclusion_comp
    {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {B A : C} {f : B ⟶ A} (P : PushforwardChoice p f)
    (x : p.Fiber B) {y : p.Fiber A} (h : P.obj x ⟶ y) :
    p.IsHomLift f (P.inclusion x ≫ Functor.Fiber.fiberInclusion.map h) :=
  @IsHomLift.comp_lift_id_right' C F _ _ p B A x.1 (P.obj x).1 y.1 f
    (P.inclusion x) (P.cocartesian x).toIsHomLift A
    (Functor.Fiber.fiberInclusion.map h) h.2

/-- The arrow between chosen pushforwards forced by an arrow of the fibre over `B`: the unique
vertical arrow through which the chosen cocartesian arrow factors. -/
public noncomputable def pushforwardMapOfChoice
    {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {B A : C} {f : B ⟶ A} (P : PushforwardChoice p f)
    {x y : p.Fiber B} (g : x ⟶ y) : P.obj x ⟶ P.obj y := by
  classical
  letI : p.IsStronglyCocartesian f (P.inclusion x) := P.cocartesian x
  let ψ := Functor.Fiber.fiberInclusion.map g ≫ P.inclusion y
  have hψ : p.IsHomLift f ψ := homLift_comp_fiber P g
  letI : p.IsHomLift f ψ := hψ
  let χ := @IsStronglyCocartesian.map C F _ _ p B A x.1 (P.obj x).1 f
    (P.inclusion x) (P.cocartesian x) A (P.obj y).1 (𝟙 A) f
    (Category.comp_id f).symm ψ hψ
  have hχ : p.IsHomLift (𝟙 A) χ :=
    @IsStronglyCocartesian.map_isHomLift C F _ _ p B A x.1 (P.obj x).1 f
      (P.inclusion x) (P.cocartesian x) A (P.obj y).1 (𝟙 A) f
      (Category.comp_id f).symm ψ hψ
  exact ⟨χ, hχ⟩

/-- The forced arrow between chosen pushforwards is compatible with the chosen arrows. -/
public lemma pushforwardMapOfChoice_fac
    {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {B A : C} {f : B ⟶ A} (P : PushforwardChoice p f)
    {x y : p.Fiber B} (g : x ⟶ y) :
    P.inclusion x ≫ Functor.Fiber.fiberInclusion.map (pushforwardMapOfChoice P g) =
      Functor.Fiber.fiberInclusion.map g ≫ P.inclusion y := by
  classical
  let : p.IsStronglyCocartesian f (P.inclusion x) := P.cocartesian x
  let ψ := Functor.Fiber.fiberInclusion.map g ≫ P.inclusion y
  have hψ : p.IsHomLift f ψ := homLift_comp_fiber P g
  let : p.IsHomLift f ψ := hψ
  show P.inclusion x ≫
      @IsStronglyCocartesian.map C F _ _ p B A x.1 (P.obj x).1 f
        (P.inclusion x) (P.cocartesian x) A (P.obj y).1 (𝟙 A) f
        (Category.comp_id f).symm ψ hψ = ψ
  exact @IsStronglyCocartesian.fac C F _ _ p B A x.1 (P.obj x).1 f
    (P.inclusion x) (P.cocartesian x) A (P.obj y).1 (𝟙 A) f
    (Category.comp_id f).symm ψ hψ

/-- The functor on fibres determined by a choice of pushforwards: its action on an arrow is
the unique vertical arrow forced by the chosen cocartesian arrows.  Together with
`Deformation.pushforwardSquareOfChoices` this is the sense in which a choice of pushforwards
*determines* the vertical functors and the 2-cell of Tag 06HI. -/
public noncomputable def pushforwardFunctorOfChoice
    {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {B A : C} {f : B ⟶ A} (P : PushforwardChoice p f) :
    PushforwardFunctor P := by
  classical
  refine
    { map := fun g => pushforwardMapOfChoice P g
      map_id := ?_
      map_comp := ?_
      inclusion_naturality := ?_ }
  · intro x
    apply Functor.Fiber.hom_ext
    have hfac := pushforwardMapOfChoice_fac P (𝟙 x)
    have hmap : P.inclusion x ≫
        Functor.Fiber.fiberInclusion.map (pushforwardMapOfChoice P (𝟙 x)) =
        P.inclusion x ≫ 𝟙 (P.obj x).1 := by
      rw [hfac]
      change (𝟙 x.1) ≫ P.inclusion x = P.inclusion x ≫ 𝟙 (P.obj x).1
      simp
    exact @IsStronglyCocartesian.ext C F _ _ p B A x.1 (P.obj x).1 f
      (P.inclusion x) (P.cocartesian x) A (P.obj x).1 (𝟙 A)
      (Functor.Fiber.fiberInclusion.map (pushforwardMapOfChoice P (𝟙 x)))
      (𝟙 (P.obj x).1) (pushforwardMapOfChoice P (𝟙 x)).2
      (IsHomLift.id (P.obj x).2) hmap
  · intro x y z g h
    apply Functor.Fiber.hom_ext
    have hmap : P.inclusion x ≫
        Functor.Fiber.fiberInclusion.map (pushforwardMapOfChoice P (g ≫ h)) =
        P.inclusion x ≫ Functor.Fiber.fiberInclusion.map
          (pushforwardMapOfChoice P g ≫ pushforwardMapOfChoice P h) := by
      rw [pushforwardMapOfChoice_fac P (g ≫ h)]
      change (g.1 ≫ h.1) ≫ P.inclusion z =
        P.inclusion x ≫ (pushforwardMapOfChoice P g).1 ≫
          (pushforwardMapOfChoice P h).1
      have fac_h : P.inclusion y ≫ (pushforwardMapOfChoice P h).1 =
          h.1 ≫ P.inclusion z := by
        simpa only [Functor.Fiber.fiberInclusion] using pushforwardMapOfChoice_fac P h
      have fac_g : P.inclusion x ≫ (pushforwardMapOfChoice P g).1 =
          g.1 ≫ P.inclusion y := by
        simpa only [Functor.Fiber.fiberInclusion] using pushforwardMapOfChoice_fac P g
      rw [Category.assoc, ← fac_h, ← Category.assoc, ← fac_g]
      simp [Category.assoc]
    exact @IsStronglyCocartesian.ext C F _ _ p B A x.1 (P.obj x).1 f
      (P.inclusion x) (P.cocartesian x) A (P.obj z).1 (𝟙 A)
      (Functor.Fiber.fiberInclusion.map (pushforwardMapOfChoice P (g ≫ h)))
      (Functor.Fiber.fiberInclusion.map
        (pushforwardMapOfChoice P g ≫ pushforwardMapOfChoice P h))
      (pushforwardMapOfChoice P (g ≫ h)).2
      (pushforwardMapOfChoice P g ≫ pushforwardMapOfChoice P h).2
      hmap
  · intro x y g
    let : p.IsStronglyCocartesian f (P.inclusion x) := P.cocartesian x
    exact pushforwardMapOfChoice_fac P g
/-- Two strongly cocartesian arrows out of the same object lying over the same arrow of the
base have canonically isomorphic codomains, by the universal property in both directions. -/
public noncomputable def cocartesianComparison
    {C : Type uC} [Category.{vC} C] {G : Type uG} [Category.{vG} G]
    (p : G ⥤ C) {B A : C} (f : B ⟶ A)
    (a : p.Fiber B) (b c : p.Fiber A)
    (u : a.1 ⟶ b.1) (v : a.1 ⟶ c.1)
    (hu : p.IsStronglyCocartesian f u) (hv : p.IsStronglyCocartesian f v) : b ≅ c := by
  classical
  letI : p.IsStronglyCocartesian f u := hu
  letI : p.IsStronglyCocartesian f v := hv
  let hom := IsStronglyCocartesian.map p f u (Category.comp_id f).symm v
  let inv := IsStronglyCocartesian.map p f v (Category.comp_id f).symm u
  letI : p.IsHomLift (𝟙 A) hom :=
    IsStronglyCocartesian.map_isHomLift p f u (Category.comp_id f).symm v
  letI : p.IsHomLift (𝟙 A) inv :=
    IsStronglyCocartesian.map_isHomLift p f v (Category.comp_id f).symm u
  have hhom : u ≫ hom = v := IsStronglyCocartesian.fac p f u (Category.comp_id f).symm v
  have hinv : v ≫ inv = u := IsStronglyCocartesian.fac p f v (Category.comp_id f).symm u
  refine {
    hom := ⟨hom, inferInstance⟩
    inv := ⟨inv, inferInstance⟩
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · apply Functor.Fiber.hom_ext
    simp only [Functor.map_comp, Functor.Fiber.fiberInclusion]
    change hom ≫ inv = 𝟙 b.1
    let : p.IsHomLift (𝟙 A) (𝟙 b.1) := IsHomLift.id b.2
    apply IsStronglyCocartesian.ext (p := p) (f := f) u (𝟙 A)
    rw [← Category.assoc u hom inv, hhom, hinv]
    simp
  · apply Functor.Fiber.hom_ext
    simp only [Functor.map_comp, Functor.Fiber.fiberInclusion]
    change inv ≫ hom = 𝟙 c.1
    let : p.IsHomLift (𝟙 A) (𝟙 c.1) := IsHomLift.id c.2
    apply IsStronglyCocartesian.ext (p := p) (f := f) v (𝟙 A)
    rw [← Category.assoc v inv hom, hinv, hhom]
    simp

/-- The comparison isomorphism of two strongly cocartesian arrows carries the first to the
second. -/
public lemma cocartesianComparison_hom_fac
    {C : Type uC} [Category.{vC} C] {G : Type uG} [Category.{vG} G]
    (p : G ⥤ C) {B A : C} (f : B ⟶ A)
    (a : p.Fiber B) (b c : p.Fiber A)
    (u : a.1 ⟶ b.1) (v : a.1 ⟶ c.1)
    (hu : p.IsStronglyCocartesian f u) (hv : p.IsStronglyCocartesian f v) :
    u ≫ Functor.Fiber.fiberInclusion.map
      (cocartesianComparison p f a b c u v hu hv).hom = v := by
  show u ≫ IsStronglyCocartesian.map p f u (Category.comp_id f).symm v = v
  exact IsStronglyCocartesian.fac p f u (Category.comp_id f).symm v

/-- A square of vertical arrows commutes as soon as it does after precomposition with a
strongly cocartesian arrow, in the shape produced by two chosen pushforwards. -/
public lemma naturality_from_cocartesian
    {C : Type uC} [Category.{vC} C] {G : Type uG} [Category.{vG} G]
    (p : G ⥤ C) {B A : C} (f : B ⟶ A)
    {X Y U V W Z : G} (u : X ⟶ Y) [p.IsStronglyCocartesian f u]
    (g : X ⟶ U) (l : Y ⟶ V) (a : V ⟶ W) (b : Y ⟶ Z) (r : Z ⟶ W)
    (uy : U ⟶ V) (vy : U ⟶ W) (vx : X ⟶ Z)
    (hl : u ≫ l = g ≫ uy) (ha : uy ≫ a = vy)
    (hr : vx ≫ r = g ≫ vy) (hb : u ≫ b = vx)
    (hlift : p.IsHomLift (𝟙 A) l) (halift : p.IsHomLift (𝟙 A) a)
    (hblift : p.IsHomLift (𝟙 A) b) (hrlift : p.IsHomLift (𝟙 A) r) :
    l ≫ a = b ≫ r := by
  let : p.IsHomLift (𝟙 A) l := hlift
  let : p.IsHomLift (𝟙 A) a := halift
  let : p.IsHomLift (𝟙 A) b := hblift
  let : p.IsHomLift (𝟙 A) r := hrlift
  let : p.IsHomLift (𝟙 A) (l ≫ a) := IsHomLift.comp_of_lift_id p A l a
  let : p.IsHomLift (𝟙 A) (b ≫ r) := IsHomLift.comp_of_lift_id p A b r
  apply Functor.IsStronglyCocartesian.ext p f u (𝟙 A)
  rw [← Category.assoc u l a, hl, Category.assoc g uy a, ha, ← hr, ← hb,
    Category.assoc u b r]

/-- The functor between the fibres over a fixed object of the base induced by a functor over
the base. -/
public abbrev fiberFunctorOver
    {C : Type uC} [Category.{vC} C]
    {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
    {pF : F ⥤ C} {pG : G ⥤ C} (φ : F ⥤ G) (hφ : φ ⋙ pG = pF) (S : C) :
    pF.Fiber S ⥤ pG.Fiber S :=
  Functor.Fiber.inducedFunctor (p := pG) (S := S)
    (F := Functor.Fiber.fiberInclusion (p := pF) (S := S) ⋙ φ)
    (by simpa only [Functor.assoc, hφ] using
      (Functor.Fiber.fiberInclusion_comp_eq_const (p := pF) (S := S)))

/-- The comparison isomorphism between the image of the chosen pushforward of an object and
the chosen pushforward of its image: both receive a strongly cocartesian arrow over `f` from
the image of that object. -/
public noncomputable def pushforwardComparison
    {C : Type uC} [Category.{vC} C]
    {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
    (pF : F ⥤ C) (pG : G ⥤ C)
    (hG : IsCofiberedInGroupoids pG)
    (φ : F ⥤ G) (hφ : φ ⋙ pG = pF)
    {B A : C} {f : B ⟶ A}
    (PF : PushforwardChoice pF f) (PG : PushforwardChoice pG f)
    (x : pF.Fiber B) :
    (fiberFunctorOver φ hφ A).obj (PF.obj x) ≅
      PG.obj ((fiberFunctorOver φ hφ B).obj x) :=
  letI : pF.IsHomLift f (PF.inclusion x) := (PF.cocartesian x).toIsHomLift
  cocartesianComparison pG f ((fiberFunctorOver φ hφ B).obj x)
    ((fiberFunctorOver φ hφ A).obj (PF.obj x))
    (PG.obj ((fiberFunctorOver φ hφ B).obj x))
    (φ.map (PF.inclusion x)) (PG.inclusion ((fiberFunctorOver φ hφ B).obj x))
    (mapped_cocartesian pF pG hG φ hφ (PF.inclusion x))
    (PG.cocartesian ((fiberFunctorOver φ hφ B).obj x))

/-- The comparison isomorphism carries the image of the chosen arrow to the chosen arrow of
the image.  This characterizes it, because the image of the chosen arrow is cocartesian. -/
public lemma pushforwardComparison_hom_fac
    {C : Type uC} [Category.{vC} C]
    {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
    (pF : F ⥤ C) (pG : G ⥤ C)
    (hG : IsCofiberedInGroupoids pG)
    (φ : F ⥤ G) (hφ : φ ⋙ pG = pF)
    {B A : C} {f : B ⟶ A}
    (PF : PushforwardChoice pF f) (PG : PushforwardChoice pG f)
    (x : pF.Fiber B) :
    φ.map (PF.inclusion x) ≫ Functor.Fiber.fiberInclusion.map
        (pushforwardComparison pF pG hG φ hφ PF PG x).hom =
      PG.inclusion ((fiberFunctorOver φ hφ B).obj x) :=
  let : pF.IsHomLift f (PF.inclusion x) := (PF.cocartesian x).toIsHomLift
  cocartesianComparison_hom_fac pG f ((fiberFunctorOver φ hφ B).obj x)
    ((fiberFunctorOver φ hφ A).obj (PF.obj x))
    (PG.obj ((fiberFunctorOver φ hφ B).obj x))
    (φ.map (PF.inclusion x)) (PG.inclusion ((fiberFunctorOver φ hφ B).obj x))
    (mapped_cocartesian pF pG hG φ hφ (PF.inclusion x))
    (PG.cocartesian ((fiberFunctorOver φ hφ B).obj x))

/-- Chosen pushforwards along an arrow in the base determine the two vertical functors between
the fibres together with the 2-cell making the square with a morphism of categories cofibered
in groupoids 2-commutative: the functors are forced by the chosen cocartesian arrows and the
2-cell is the comparison isomorphism of cocartesian arrows. -/
public noncomputable def pushforwardSquareOfChoices
    {C : Type uC} [Category.{vC} C]
    {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
    (pF : F ⥤ C) (pG : G ⥤ C)
    (hG : IsCofiberedInGroupoids pG)
    (φ : F ⥤ G) (hφ : φ ⋙ pG = pF)
    {B A : C} {f : B ⟶ A}
    (PF : PushforwardChoice pF f) (PG : PushforwardChoice pG f) :
    PushforwardSquare φ hφ PF PG where
  source := pushforwardFunctorOfChoice PF
  target := pushforwardFunctorOfChoice PG
  comm := NatIso.ofComponents (pushforwardComparison pF pG hG φ hφ PF PG) (by
    intro x y g
    apply Functor.Fiber.hom_ext
    let QF := pushforwardFunctorOfChoice PF
    let QG := pushforwardFunctorOfChoice PG
    let FA := fiberFunctorOver φ hφ A
    let FB := fiberFunctorOver φ hφ B
    let α := pushforwardComparison pF pG hG φ hφ PF PG
    let ux := φ.map (PF.inclusion x)
    let uy := φ.map (PF.inclusion y)
    let vx := PG.inclusion (FB.obj x)
    let vy := PG.inclusion (FB.obj y)
    let leftMap := (QF.toFunctor ⋙ FA).map g
    let rightMap := (FB ⋙ QG.toFunctor).map g
    have : pF.IsHomLift f (PF.inclusion x) := (PF.cocartesian x).toIsHomLift
    have hux : pG.IsStronglyCocartesian f ux :=
      mapped_cocartesian pF pG hG φ hφ (PF.inclusion x)
    let : pG.IsStronglyCocartesian f ux := hux
    have hleft : ux ≫ Functor.Fiber.fiberInclusion.map leftMap =
        Functor.Fiber.fiberInclusion.map (FB.map g) ≫ uy := by
      change φ.map (PF.inclusion x) ≫
          φ.map (Functor.Fiber.fiberInclusion.map (QF.map g)) =
        φ.map (Functor.Fiber.fiberInclusion.map g) ≫ φ.map (PF.inclusion y)
      rw [← Functor.map_comp φ (PF.inclusion x)
        (Functor.Fiber.fiberInclusion.map (QF.map g)),
        ← Functor.map_comp φ (Functor.Fiber.fiberInclusion.map g) (PF.inclusion y)]
      exact congrArg (fun k => φ.map k) (QF.inclusion_naturality g)
    have hright : vx ≫ Functor.Fiber.fiberInclusion.map rightMap =
        Functor.Fiber.fiberInclusion.map (FB.map g) ≫ vy := by
      change PG.inclusion (FB.obj x) ≫
          Functor.Fiber.fiberInclusion.map (QG.map (FB.map g)) =
        Functor.Fiber.fiberInclusion.map (FB.map g) ≫ PG.inclusion (FB.obj y)
      exact QG.inclusion_naturality (FB.map g)
    exact naturality_from_cocartesian pG f ux
      (Functor.Fiber.fiberInclusion.map (FB.map g))
      (Functor.Fiber.fiberInclusion.map leftMap)
      (Functor.Fiber.fiberInclusion.map (α y).hom)
      (Functor.Fiber.fiberInclusion.map (α x).hom)
      (Functor.Fiber.fiberInclusion.map rightMap) uy vy vx
      hleft (pushforwardComparison_hom_fac pF pG hG φ hφ PF PG y) hright
      (pushforwardComparison_hom_fac pF pG hG φ hφ PF PG x)
      leftMap.2 (α y).hom.2 (α x).hom.2 rightMap.2)

/-- Chosen pushforwards along an arrow in the base give functors between the
fibres, and a morphism of categories cofibered in groupoids intertwines these
functors up to a natural isomorphism. -/
@[stacks 06HI "pushforward_square"]
public theorem pushforwardFunctorsFormTwoCommutativeSquare
    {C : Type uC} [Category.{vC} C]
    {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
    (pF : F ⥤ C) (pG : G ⥤ C)
    (hG : IsCofiberedInGroupoids pG)
    (φ : F ⥤ G) (hφ : φ ⋙ pG = pF)
    {B A : C} {f : B ⟶ A}
    (PF : PushforwardChoice pF f) (PG : PushforwardChoice pG f) :
    Nonempty (PushforwardSquare φ hφ PF PG) :=
  ⟨pushforwardSquareOfChoices pF pG hG φ hφ PF PG⟩

/-- A category cofibered in groupoids admits a choice of pushforwards along every arrow of the
base. -/
public noncomputable def pushforwardChoiceOfIsCofibered
    {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} (hp : IsCofiberedInGroupoids p) {B A : C} (f : B ⟶ A) :
    PushforwardChoice p f := by
  classical
  choose y a ha using fun x : p.Fiber B => exists_pushforward hp f x.1 x.2
  refine ⟨fun x => ⟨y x, ?_⟩, a,
    fun x => isStronglyCocartesian_of_isCofiberedInGroupoids hp f (a x) (ha x)⟩
  let : p.IsHomLift f (a x) := ha x
  exact IsHomLift.codomain_eq p f (a x)
end

/-! ### The functor induced by a pushforward square -/

section
open CategoryTheory
universe vC uC vF uF vG uG

/-- The functor from the source fibre to the categorical pullback induced by a
chosen two-commutative pushforward square. -/
@[stacks 06HI "induced_functor", sga "7 VI 2.6(b)" "induced functor to 2-fp"]
public def inducedFunctorToPullback
    {C : Type uC} [Category.{vC} C]
    {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
    {pF : F ⥤ C} {pG : G ⥤ C} {φ : F ⥤ G} {hφ : φ ⋙ pG = pF}
    {B A : C} {f : B ⟶ A}
    {PF : PushforwardChoice pF f}
    {PG : PushforwardChoice pG f}
    (Q : PushforwardSquare φ hφ PF PG) :
    pF.Fiber B ⥤
      Limits.CategoricalPullback
        (Functor.Fiber.inducedFunctor (p := pG) (S := A)
          (F := Functor.Fiber.fiberInclusion (p := pF) (S := A) ⋙ φ)
          (by simpa only [Functor.assoc, hφ] using
            (Functor.Fiber.fiberInclusion_comp_eq_const (p := pF) (S := A))))
        Q.target.toFunctor :=
  (Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (Functor.Fiber.inducedFunctor (p := pG) (S := A)
      (F := Functor.Fiber.fiberInclusion (p := pF) (S := A) ⋙ φ)
      (by simpa only [Functor.assoc, hφ] using
        (Functor.Fiber.fiberInclusion_comp_eq_const (p := pF) (S := A))))
    Q.target.toFunctor (pF.Fiber B)).obj
    { fst := Q.source.toFunctor
      snd := Functor.Fiber.inducedFunctor (p := pG) (S := B)
        (F := Functor.Fiber.fiberInclusion (p := pF) (S := B) ⋙ φ)
        (by simpa only [Functor.assoc, hφ] using
          (Functor.Fiber.fiberInclusion_comp_eq_const (p := pF) (S := B)))
      iso := Q.comm }

end

end Deformation
