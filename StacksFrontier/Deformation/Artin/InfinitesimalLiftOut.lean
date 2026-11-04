module

public import StacksFrontier.Deformation.Artin.Infinitesimal
public import StacksFrontier.Deformation.Artin.Infinitesimal.LiftsAlong

/-!
# Lifts out of the base: the source's `Lift(x, A')` (Stacks 07Y7)

An *infinitesimal deformation* of an object `x` of a category fibred in groupoids over a base
`U`, in the sense of the source, is a lift of `x` along an arrow `U ⟶ U'` *out of* `U`: an object
`x'` over `U'` together with an arrow `x ⟶ x'` over `U ⟶ U'`.  On the big fppf site and for a
square-zero surjection `A' ⟶ A` of `S`-algebras this is the source's `Lift(x, A')`, whose objects
are the morphisms `x ⟶ x'` lying over `Spec A ⟶ Spec A'`; a lift is an *extension* of `x`, not a
restriction of it.  `StacksFrontier/Deformation/Artin/Infinitesimal.lean` develops the
functoriality of lifts along an arrow *into* the base (`Deformation.Artin.Lift`); this file
develops the same functoriality for lifts out of the base.

A morphism `F` of categories fibred in groupoids, together with a morphism `φ` from the pullback
of `F x` to an object `y` over `V`, induces a functor from lifts of `x` along `a : U ⟶ U'` to
lifts of `y` along `d : V ⟶ V'`, for any commutative square `b ≫ a = d ≫ c` in the base.  On a
lift `x ⟶ x'` the functor takes the chosen pullback of `F x'` along `c`, with structure arrow the
factorization of `y ⟶ F x ⟶ F x'` through the cartesian arrow.  The functor comes equipped with
natural cartesian comparison arrows, and it is unique up to a unique isomorphism commuting with
those arrows; applied to a composite of morphisms of fibred groupoids it gives the composition
isomorphism.

## Main definitions

* `Deformation.Artin.LiftOut` — the source's `Lift(x, A')`: lifts of `x` along `a : U ⟶ U'`,
  i.e. arrows `x ⟶ x'` of the total category lying over `a`.
* `Deformation.Artin.LiftOutFunctor` — a functor between categories of such lifts, bundled with
  its natural cartesian comparison arrows.
* `Deformation.Artin.liftImageFiberFunctor` — the image under `F` of a lift of `x`, as a functor
  to the fibre over `U'`.
* `Deformation.Artin.bridgeOutComparison` — the structure arrow of the induced lift of `y`.

## Main results

* `Deformation.Artin.liftOutFunctorOfPullback`, `Deformation.Artin.liftFunctorOfHom` — the
  induced functor on lifts (**Stacks 07Y7**, the functor).
* `Deformation.Artin.liftOutFunctor_unique` — uniqueness of that functor up to a unique
  isomorphism (**Stacks 07Y7**, uniqueness).
* `Deformation.Artin.liftFunctorOfHom_comp`, `Deformation.Artin.liftOutFunctor_comp` — the
  composition isomorphism (**Stacks 07Y7**, compatibility with composition).

## Implementation notes

The category of lifts is `Deformation.Artin.LiftAlong`, the fibre of the functor on
`Under`-categories induced by the structure functor, with the arrow out of `p x` named through
`hx`.  The arrows of lifts are the triangles commuting over an identity, hence cartesian, so the
category of lifts is a groupoid.  The targets of the induced lifts are taken from a choice of
pullbacks for the target fibred category.

## References

* [Stacks Project, Tag 07Y7](https://stacks.math.columbia.edu/tag/07Y7)
-/

@[expose] public section

namespace Deformation.Artin

/-! ### Functoriality of categories of lifts along an arrow out of the base -/

section
open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {X : Type u₂} [Category.{v₂} X]
variable {Y : Type u₃} [Category.{v₃} Y]

-- `Fiber` and `Fiber.fiberInclusion` are plain `def`s, so goals mentioning an object of a fibre
-- or its image in the ambient category are not type-correct at `implicit` transparency and the
-- instance arguments of `IsHomLift` are not found without unfolding them.
attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

/-- **The source's `Lift(x, A')`.** Lifts of `x` to `U'` along `a : U ⟶ U'`, where `x` lies over
`U`: an object `x'` of `X` lying over `U'` together with an arrow `x ⟶ x'` lying over `a`, the
arrows of lifts being the triangles commuting over the identity of `U'`.

Over the big fppf site of `S` and for a map `A' ⟶ A` of `S`-algebras one takes `U = Spec A`,
`U' = Spec A'` and `a : Spec A ⟶ Spec A'`, so that an object is a morphism `x ⟶ x'` of `X`
lying over `Spec A ⟶ Spec A'`: a lift is an *extension* of `x`, not a restriction of it. This
is `Deformation.Artin.LiftAlong` with the arrow out of `p x` named through `hx`. -/
public abbrev LiftOut (p : X ⥤ C) {U U' : C} (a : U ⟶ U') (x : X)
    (hx : p.obj x = U) :=
  LiftAlong p x (eqToHom hx ≫ a)

/-- A functor on lifts induced by a morphism of fibred categories and a morphism over the
base-change arrow. The comparison maps give the canonical cartesian squares and are natural in
morphisms of lifts. -/
public structure LiftOutFunctor (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ U) (c : V' ⟶ U') (d : V ⟶ V')
    (x : X) (hx : p.obj x = U) (y : Y) (hy : q.obj y = V)
    (φ : y ⟶ F.obj x) where
  /-- The underlying functor on categories of lifts. -/
  toFunctor : LiftOut p a x hx ⥤ LiftOut q d y hy
  /-- The comparison arrow from the target of the induced lift to the image under `F` of the
  target of the given lift. -/
  comparison (t : LiftOut p a x hx) :
    (toFunctor.obj t).1.right ⟶ F.obj t.1.right
  /-- Each comparison arrow is strongly cartesian over `c`. -/
  isCartesian (t : LiftOut p a x hx) :
    q.IsStronglyCartesian c (comparison t)
  /-- The square formed by a lift, its image, the comparison arrow and `φ` commutes. -/
  comm (t : LiftOut p a x hx) :
    (toFunctor.obj t).1.hom ≫ comparison t = φ ≫ F.map t.1.hom
  /-- The comparison arrows are natural in morphisms of lifts. -/
  natural {s t : LiftOut p a x hx} (m : s ⟶ t) :
    (toFunctor.map m).1.right ≫ comparison t =
      comparison s ≫ F.map m.1.right

/-- The target of a lift of `x` along `a : U ⟶ U'` lies over `U'`. -/
public lemma liftOut_base_obj (p : X ⥤ C) {U U' : C} (a : U ⟶ U')
    (x : X) (hx : p.obj x = U) (t : LiftOut p a x hx) :
    p.obj t.1.right = U' :=
  liftAlong_base_obj p x _ t

/-- The structure arrow of a lift of `x` along `a` lies over `a`. -/
public lemma liftOut_isHomLift (p : X ⥤ C) {U U' : C} (a : U ⟶ U')
    (x : X) (hx : p.obj x = U) (t : LiftOut p a x hx) :
    p.IsHomLift a t.1.hom := by
  subst hx
  simpa using liftAlong_isHomLift p x _ t

/-- A morphism of lifts along `a` lies over the identity of the target of `a`. -/
public lemma liftOut_morphism_isHomLift (p : X ⥤ C) {U U' : C} (a : U ⟶ U')
    (x : X) (hx : p.obj x = U) {s t : LiftOut p a x hx} (m : s ⟶ t) :
    p.IsHomLift (𝟙 U') m.1.right :=
  liftAlong_morphism_isHomLift p x _ m

/-- The arrow underlying a composite of morphisms of lifts. -/
@[simp]
public lemma liftOut_comp_right (p : X ⥤ C) {U U' : C} (a : U ⟶ U')
    (x : X) (hx : p.obj x = U) {s t u : LiftOut p a x hx} (m : s ⟶ t) (n : t ⟶ u) :
    (m ≫ n).1.right = m.1.right ≫ n.1.right := rfl

/-- Morphisms of lifts are determined by the arrow between the targets. -/
public lemma liftOut_hom_ext (p : X ⥤ C) {U U' : C} (a : U ⟶ U')
    (x : X) (hx : p.obj x = U) {s t : LiftOut p a x hx} {m n : s ⟶ t}
    (h : m.1.right = n.1.right) : m = n :=
  Subtype.ext (Under.UnderMorphism.ext h)

/-- An arrow out of `x` lying over `a` is a lift of `x` along `a`. -/
public def liftOutMk (p : X ⥤ C) {U U' : C} (a : U ⟶ U')
    (x : X) (hx : p.obj x = U) {z : X} (hz : p.obj z = U') (g : x ⟶ z)
    (hg : p.IsHomLift a g) : LiftOut p a x hx :=
  liftAlongMk p x _ hz g (by subst hx; simpa using hg)

/-- The target of the lift attached to an arrow out of `x` is the target of that arrow. -/
@[simp]
public lemma liftOutMk_right (p : X ⥤ C) {U U' : C} (a : U ⟶ U')
    (x : X) (hx : p.obj x = U) {z : X} (hz : p.obj z = U') (g : x ⟶ z)
    (hg : p.IsHomLift a g) : (liftOutMk p a x hx hz g hg).1.right = z := rfl

/-- The structure arrow of the lift attached to an arrow out of `x` is that arrow. -/
@[simp]
public lemma liftOutMk_hom (p : X ⥤ C) {U U' : C} (a : U ⟶ U')
    (x : X) (hx : p.obj x = U) {z : X} (hz : p.obj z = U') (g : x ⟶ z)
    (hg : p.IsHomLift a g) : (liftOutMk p a x hx hz g hg).1.hom = g := rfl

/-- A commuting triangle over the identity of `U'` is a morphism of lifts. -/
public def liftOutHomMk (p : X ⥤ C) {U U' : C} (a : U ⟶ U')
    (x : X) (hx : p.obj x = U) {s t : LiftOut p a x hx}
    (f : s.1.right ⟶ t.1.right) (hf : p.IsHomLift (𝟙 U') f)
    (h : s.1.hom ≫ f = t.1.hom) : s ⟶ t := by
  refine ⟨Under.homMk f h, ?_⟩
  apply IsHomLift.of_fac' (Under.post (X := x) p) (𝟙 (Under.mk (eqToHom hx ≫ a)))
    (Under.homMk f h) s.2 t.2
  apply Under.UnderMorphism.ext
  change p.map f = _
  have := hf
  have hfac := IsHomLift.fac' p (𝟙 U') f
  rw [hfac]
  simp only [Under.eqToHom_right, Under.comp_right, Under.id_right]
  congr 1

/-- The arrow underlying `Deformation.Artin.liftOutHomMk`. -/
@[simp]
public lemma liftOutHomMk_right (p : X ⥤ C) {U U' : C} (a : U ⟶ U')
    (x : X) (hx : p.obj x = U) {s t : LiftOut p a x hx}
    (f : s.1.right ⟶ t.1.right) (hf : p.IsHomLift (𝟙 U') f)
    (h : s.1.hom ≫ f = t.1.hom) : (liftOutHomMk p a x hx f hf h).1.right = f := rfl

/-- The image under `F` of the structure arrow of a lift along `a` lies over `a`. -/
public lemma liftOut_map_hom_isHomLift (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y)
    (hF : F ⋙ q = p) {U U' : C} (a : U ⟶ U')
    (x : X) (hx : p.obj x = U) (t : LiftOut p a x hx) :
    q.IsHomLift a (F.map t.1.hom) :=
  lift_map_isHomLift p q F hF a hx (liftOut_base_obj p a x hx t) t.1.hom
    (liftOut_isHomLift p a x hx t)

/-! #### The image of a lift in the fibre over `U'` -/

/-- A lift of `x` along `a`, mapped to the image under `F` of its target: the composite of the
inclusion of the fibre, the forgetful functor of `Under x` and `F`. -/
public def liftImageFunctor (p : X ⥤ C) (F : X ⥤ Y) {U U' : C} (a : U ⟶ U')
    (x : X) (hx : p.obj x = U) : LiftOut p a x hx ⥤ Y :=
  Functor.Fiber.fiberInclusion ⋙ Under.forget x ⋙ F

/-- The image under `F` of the target of a lift of `x` along `a`, as an object of the fibre of
`q` over `U'`. -/
public def liftImageFiber (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' : C} (a : U ⟶ U') (x : X) (hx : p.obj x = U) (t : LiftOut p a x hx) :
    q.Fiber U' :=
  imageFiber p q F hF t.1.right (liftOut_base_obj p a x hx t)

/-- The image under `F` of a morphism of lifts of `x` along `a`, as a morphism of the fibre of
`q` over `U'`. -/
public def liftImageFiberMap (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' : C} (a : U ⟶ U') (x : X) (hx : p.obj x = U) {s t : LiftOut p a x hx} (m : s ⟶ t) :
    liftImageFiber p q F hF a x hx s ⟶ liftImageFiber p q F hF a x hx t :=
  ⟨F.map m.1.right, lift_map_isHomLift p q F hF (𝟙 U')
    (liftOut_base_obj p a x hx s) (liftOut_base_obj p a x hx t) m.1.right
    (liftOut_morphism_isHomLift p a x hx m)⟩

/-- **Stacks 07Y7, the functor on fibres.** The functor from lifts of `x` along `a` to the
fibre of `q` over `U'` carrying a lift `x ⟶ x'` to the object `F x'` and a morphism of lifts
to its image under `F`. -/
public def liftImageFiberFunctor (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' : C} (a : U ⟶ U') (x : X) (hx : p.obj x = U) :
    LiftOut p a x hx ⥤ q.Fiber U' where
  obj t := liftImageFiber p q F hF a x hx t
  map m := liftImageFiberMap p q F hF a x hx m
  map_id t := Functor.Fiber.hom_ext ((liftImageFunctor p F a x hx).map_id t)
  map_comp m n := Functor.Fiber.hom_ext ((liftImageFunctor p F a x hx).map_comp m n)

/-- `F` carries identities of lifts to identities of the fibre. -/
@[simp]
public lemma liftImageFiberMap_id (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' : C} (a : U ⟶ U') (x : X) (hx : p.obj x = U) (t : LiftOut p a x hx) :
    liftImageFiberMap p q F hF a x hx (𝟙 t) = 𝟙 (liftImageFiber p q F hF a x hx t) :=
  (liftImageFiberFunctor p q F hF a x hx).map_id t

/-- `F` carries composites of morphisms of lifts to composites in the fibre. -/
@[simp]
public lemma liftImageFiberMap_comp (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' : C} (a : U ⟶ U') (x : X) (hx : p.obj x = U) {s t u : LiftOut p a x hx}
    (m : s ⟶ t) (n : t ⟶ u) :
    liftImageFiberMap p q F hF a x hx (m ≫ n) =
      liftImageFiberMap p q F hF a x hx m ≫ liftImageFiberMap p q F hF a x hx n :=
  (liftImageFiberFunctor p q F hF a x hx).map_comp m n

-- The objects and arrows these package are compared, during instance synthesis and during
-- unification, with their unpackaged spellings `F x'` and `F m`; without this the comparison
-- is not made at `implicit` transparency and the `IsHomLift` instances are not found.
attribute [local implicit_reducible] imageFiber liftImageFunctor liftImageFiber
  liftImageFiberMap

/-! #### The induced functor on lifts -/

/-- The structure arrow of the lift of `y` along `d` induced by a lift `t` of `x` along `a`:
the factorization of `y ⟶ F x ⟶ F x'` through the chosen cartesian arrow over `c`. -/
public noncomputable def bridgeOutComparison (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ U) (c : V' ⟶ U') (d : V ⟶ V')
    (hsq : b ≫ a = d ≫ c) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩)
    (t : LiftOut p a x hx) :
    y ⟶ (e.obj c (liftImageFiber p q F hF a x hx t)).1 := by
  haveI : q.IsHomLift b (pullbackComparison p q hq F hF b x hx y hy e φ) :=
    pullbackComparison_isHomLift p q hq F hF b x hx y hy e φ
  haveI : q.IsHomLift a (F.map t.1.hom) := liftOut_map_hom_isHomLift p q F hF a x hx t
  haveI : q.IsStronglyCartesian c (e.map c (liftImageFiber p q F hF a x hx t)) :=
    e.isStronglyCartesian c _
  haveI : q.IsHomLift (b ≫ a)
      (pullbackComparison p q hq F hF b x hx y hy e φ ≫ F.map t.1.hom) := inferInstance
  exact Functor.IsStronglyCartesian.map q c
    (e.map c (liftImageFiber p q F hF a x hx t)) hsq
    (pullbackComparison p q hq F hF b x hx y hy e φ ≫ F.map t.1.hom)

/-- The defining factorization of `Deformation.Artin.bridgeOutComparison`, and the fact that it
lies over `d`. -/
private lemma bridgeOutComparison_fac_and_isHomLift (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ U) (c : V' ⟶ U') (d : V ⟶ V')
    (hsq : b ≫ a = d ≫ c) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩)
    (t : LiftOut p a x hx) :
    bridgeOutComparison p q hq F hF a b c d hsq x hx y hy e φ t ≫
        e.map c (liftImageFiber p q F hF a x hx t) =
      pullbackComparison p q hq F hF b x hx y hy e φ ≫ F.map t.1.hom ∧
    q.IsHomLift d (bridgeOutComparison p q hq F hF a b c d hsq x hx y hy e φ t) := by
  have : q.IsHomLift b (pullbackComparison p q hq F hF b x hx y hy e φ) :=
    pullbackComparison_isHomLift p q hq F hF b x hx y hy e φ
  have : q.IsHomLift a (F.map t.1.hom) := liftOut_map_hom_isHomLift p q F hF a x hx t
  have : q.IsStronglyCartesian c (e.map c (liftImageFiber p q F hF a x hx t)) :=
    e.isStronglyCartesian c _
  have : q.IsHomLift (b ≫ a)
      (pullbackComparison p q hq F hF b x hx y hy e φ ≫ F.map t.1.hom) := inferInstance
  exact ⟨Functor.IsStronglyCartesian.fac q c
      (e.map c (liftImageFiber p q F hF a x hx t)) hsq
      (pullbackComparison p q hq F hF b x hx y hy e φ ≫ F.map t.1.hom),
    Functor.IsStronglyCartesian.map_isHomLift q c
      (e.map c (liftImageFiber p q F hF a x hx t)) hsq
      (pullbackComparison p q hq F hF b x hx y hy e φ ≫ F.map t.1.hom)⟩

/-- The defining factorization of `Deformation.Artin.bridgeOutComparison`. -/
public lemma bridgeOutComparison_fac (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ U) (c : V' ⟶ U') (d : V ⟶ V')
    (hsq : b ≫ a = d ≫ c) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩)
    (t : LiftOut p a x hx) :
    bridgeOutComparison p q hq F hF a b c d hsq x hx y hy e φ t ≫
        e.map c (liftImageFiber p q F hF a x hx t) =
      pullbackComparison p q hq F hF b x hx y hy e φ ≫ F.map t.1.hom :=
  (bridgeOutComparison_fac_and_isHomLift p q hq F hF a b c d hsq x hx y hy e φ t).1

/-- `Deformation.Artin.bridgeOutComparison` lies over the arrow `d` of the commutative square. -/
public lemma bridgeOutComparison_isHomLift (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ U) (c : V' ⟶ U') (d : V ⟶ V')
    (hsq : b ≫ a = d ≫ c) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩)
    (t : LiftOut p a x hx) :
    q.IsHomLift d (bridgeOutComparison p q hq F hF a b c d hsq x hx y hy e φ t) :=
  (bridgeOutComparison_fac_and_isHomLift p q hq F hF a b c d hsq x hx y hy e φ t).2

/-- The triangle making the chosen pullback of the image of a morphism of lifts a morphism of
the induced lifts of `y`. -/
public lemma bridgeOutComparison_naturality (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ U) (c : V' ⟶ U') (d : V ⟶ V')
    (hsq : b ≫ a = d ≫ c) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩)
    {s t : LiftOut p a x hx} (m : s ⟶ t) :
    bridgeOutComparison p q hq F hF a b c d hsq x hx y hy e φ s ≫
        Functor.Fiber.fiberInclusion.map
          (e.homMap c (liftImageFiberMap p q F hF a x hx m)) =
      bridgeOutComparison p q hq F hF a b c d hsq x hx y hy e φ t := by
  have hs : q.IsHomLift d (bridgeOutComparison p q hq F hF a b c d hsq x hx y hy e φ s) :=
    bridgeOutComparison_isHomLift p q hq F hF a b c d hsq x hx y hy e φ s
  have ht : q.IsHomLift d (bridgeOutComparison p q hq F hF a b c d hsq x hx y hy e φ t) :=
    bridgeOutComparison_isHomLift p q hq F hF a b c d hsq x hx y hy e φ t
  have hm : q.IsHomLift (𝟙 V')
      (Functor.Fiber.fiberInclusion.map (e.homMap c (liftImageFiberMap p q F hF a x hx m))) :=
    (e.homMap c (liftImageFiberMap p q F hF a x hx m)).2
  have hcart : q.IsStronglyCartesian c (e.map c (liftImageFiber p q F hF a x hx t)) :=
    e.isStronglyCartesian c _
  have hcomp : q.IsHomLift d
      (bridgeOutComparison p q hq F hF a b c d hsq x hx y hy e φ s ≫
        Functor.Fiber.fiberInclusion.map
          (e.homMap c (liftImageFiberMap p q F hF a x hx m))) :=
    IsHomLift.comp_lift_id_right' q d
      (bridgeOutComparison p q hq F hF a b c d hsq x hx y hy e φ s) V'
      (Functor.Fiber.fiberInclusion.map (e.homMap c (liftImageFiberMap p q F hF a x hx m)))
  have hfac : Functor.Fiber.fiberInclusion.map
        (e.homMap c (liftImageFiberMap p q F hF a x hx m)) ≫
      e.map c (liftImageFiber p q F hF a x hx t) =
    e.map c (liftImageFiber p q F hF a x hx s) ≫ F.map m.1.right :=
    e.homMap_fac c (liftImageFiberMap p q F hF a x hx m)
  refine Functor.IsStronglyCartesian.ext q c
    (e.map c (liftImageFiber p q F hF a x hx t)) d ?_
  rw [Category.assoc, hfac, ← Category.assoc,
    bridgeOutComparison_fac p q hq F hF a b c d hsq x hx y hy e φ s,
    Category.assoc, ← F.map_comp, Under.w m.1,
    bridgeOutComparison_fac p q hq F hF a b c d hsq x hx y hy e φ t]

/-- The induced lift of `y`, as an object of `Under y`. -/
public noncomputable def bridgeUnder (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ U) (c : V' ⟶ U') (d : V ⟶ V')
    (hsq : b ≫ a = d ≫ c) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩)
    (t : LiftOut p a x hx) : Under y :=
  Under.mk (bridgeOutComparison p q hq F hF a b c d hsq x hx y hy e φ t)

/-- The induced arrow of induced lifts, as a morphism of `Under y`. -/
public noncomputable def bridgeUnderMap (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ U) (c : V' ⟶ U') (d : V ⟶ V')
    (hsq : b ≫ a = d ≫ c) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩)
    {s t : LiftOut p a x hx} (m : s ⟶ t) :
    bridgeUnder p q hq F hF a b c d hsq x hx y hy e φ s ⟶
      bridgeUnder p q hq F hF a b c d hsq x hx y hy e φ t :=
  Under.homMk
    (Functor.Fiber.fiberInclusion.map (e.homMap c (liftImageFiberMap p q F hF a x hx m)))
    (bridgeOutComparison_naturality p q hq F hF a b c d hsq x hx y hy e φ m)

/-- The induced functor on lifts, read in `Under y`. -/
public noncomputable def bridgeUnderFunctor (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ U) (c : V' ⟶ U') (d : V ⟶ V')
    (hsq : b ≫ a = d ≫ c) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩) :
    LiftOut p a x hx ⥤ Under y where
  obj t := bridgeUnder p q hq F hF a b c d hsq x hx y hy e φ t
  map m := bridgeUnderMap p q hq F hF a b c d hsq x hx y hy e φ m
  map_id t := by
    apply Under.UnderMorphism.ext
    change Functor.Fiber.fiberInclusion.map
        (e.homMap c (liftImageFiberMap p q F hF a x hx (𝟙 t))) = 𝟙 _
    rw [liftImageFiberMap_id, e.homMap_id, CategoryTheory.Functor.map_id]
  map_comp m n := by
    apply Under.UnderMorphism.ext
    change Functor.Fiber.fiberInclusion.map
        (e.homMap c (liftImageFiberMap p q F hF a x hx (m ≫ n))) = _
    rw [liftImageFiberMap_comp, e.homMap_comp]
    exact CategoryTheory.Functor.map_comp _ _ _

/-- **Stacks 07Y7.** Let `F : X ⥤ Y` be a `1`-morphism of categories fibred in groupoids over
`C`, let `b ≫ a = d ≫ c` be a commutative square of the base with `a : U ⟶ U'`, `b : V ⟶ U`,
`c : V' ⟶ U'` and `d : V ⟶ V'`, let `x` lie over `U`, let `y` lie over `V`, and let `φ` be a
morphism `F(x)|_V ⟶ y` of the fibre over `V`. Then there is a canonical functor from the lifts
of `x` along `a` to the lifts of `y` along `d`: a lift `x ⟶ x'` is carried to the chosen
pullback of `F x'` along `c`, whose structure arrow out of `y` is the factorization of
`y ⟶ F x ⟶ F x'` through that cartesian arrow.

Over the big fppf site this is the source's `Lift(x, A') ⟶ Lift(y, B')` for the commutative
diagram of `S`-algebras with rows `A' ⟶ A`, `B' ⟶ B` and columns `A' ⟶ B'`, `A ⟶ B`. -/
@[stacks 07Y7 "the functor, on the source's Lift(x, A'), lifts out of the base"]
public noncomputable def liftOutFunctorOfPullback (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ U) (c : V' ⟶ U') (d : V ⟶ V')
    (hsq : b ≫ a = d ≫ c) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩) :
    LiftOutFunctor p q F a b c d x hx y hy
      (pullbackComparison p q hq F hF b x hx y hy e φ) where
  toFunctor :=
    { obj := fun t => liftOutMk q d y hy (e.obj c (liftImageFiber p q F hF a x hx t)).2
        (bridgeOutComparison p q hq F hF a b c d hsq x hx y hy e φ t)
        (bridgeOutComparison_isHomLift p q hq F hF a b c d hsq x hx y hy e φ t)
      map := fun m => liftOutHomMk q d y hy
        (Functor.Fiber.fiberInclusion.map (e.homMap c (liftImageFiberMap p q F hF a x hx m)))
        (e.homMap c (liftImageFiberMap p q F hF a x hx m)).2
        (bridgeOutComparison_naturality p q hq F hF a b c d hsq x hx y hy e φ m)
      map_id := fun t => Functor.Fiber.hom_ext
        ((bridgeUnderFunctor p q hq F hF a b c d hsq x hx y hy e φ).map_id t)
      map_comp := fun m n => Functor.Fiber.hom_ext
        ((bridgeUnderFunctor p q hq F hF a b c d hsq x hx y hy e φ).map_comp m n) }
  comparison t := e.map c (liftImageFiber p q F hF a x hx t)
  isCartesian _ := e.isStronglyCartesian c _
  comm t := bridgeOutComparison_fac p q hq F hF a b c d hsq x hx y hy e φ t
  natural m :=
    e.homMap_fac c (liftImageFiberMap p q F hF a x hx m)

/-- The specification of an induced functor on lifts mentions the arrow `φ` only through the
commuting square, so a construction satisfying it transports along an equality of arrows. -/
public def LiftOutFunctor.ofEq {p : X ⥤ C} {q : Y ⥤ C} {F : X ⥤ Y}
    {U U' V V' : C} {a : U ⟶ U'} {b : V ⟶ U} {c : V' ⟶ U'} {d : V ⟶ V'}
    {x : X} {hx : p.obj x = U} {y : Y} {hy : q.obj y = V} {φ φ' : y ⟶ F.obj x}
    (L : LiftOutFunctor p q F a b c d x hx y hy φ) (h : φ = φ') :
    LiftOutFunctor p q F a b c d x hx y hy φ' where
  toFunctor := L.toFunctor
  comparison := L.comparison
  isCartesian := L.isCartesian
  comm t := (L.comm t).trans (by rw [h])
  natural := L.natural

/-- In a category fibred in groupoids every arrow lying over an arrow of the base is cartesian
over it. -/
public lemma isCartesian_of_isHomLift (q : Y ⥤ C) (hq : q.IsFiberedInGroupoids)
    {V U : C} (b : V ⟶ U) {u v : Y} (χ : u ⟶ v) (hχ : q.IsHomLift b χ) :
    q.IsCartesian b χ := by
  have : q.IsHomLift b χ := hχ
  have : q.IsStronglyCartesian b χ := hq.isStronglyCartesian_homLift b χ
  infer_instance

/-- A chosen pullback arrow is cartesian over the arrow it lies above. -/
public lemma isCartesian_of_chosenPullback (q : Y ⥤ C) {V U : C} (b : V ⟶ U)
    (e : q.ChoiceOfPullbacks) (w : q.Fiber U) : q.IsCartesian b (e.map b w) := by
  have : q.IsStronglyCartesian b (e.map b w) := e.isStronglyCartesian b w
  infer_instance

/-- In a category fibred in groupoids an arrow `y ⟶ F x` over `b` is cartesian, so it and the
chosen cartesian arrow over `b` identify `y` with the chosen pullback of `F x`, in the fibre
over `V`. -/
public noncomputable def pullbackDatumIso (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {V U : C} (b : V ⟶ U) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (χ : y ⟶ F.obj x) (hχ : q.IsHomLift b χ) :
    (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ≅ ⟨y, hy⟩ :=
  Functor.fiberIsoOfCartesian
    (z := (e.pullbackFunctor b).obj (imageFiber p q F hF x hx))
    (z' := ⟨y, hy⟩)
    b (e.map b (imageFiber p q F hF x hx)) χ
    (isCartesian_of_chosenPullback q b e (imageFiber p q F hF x hx))
    (isCartesian_of_isHomLift q hq b χ hχ)

/-- The defining factorization of `Deformation.Artin.pullbackDatumIso`. -/
public lemma pullbackDatumIso_inv_fac (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {V U : C} (b : V ⟶ U) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (χ : y ⟶ F.obj x) (hχ : q.IsHomLift b χ) :
    Functor.Fiber.fiberInclusion.map (pullbackDatumIso p q hq F hF b x hx y hy e χ hχ).inv ≫
      e.map b (imageFiber p q F hF x hx) = χ :=
  Functor.fiberIsoOfCartesian_inv_fac
    (z := (e.pullbackFunctor b).obj (imageFiber p q F hF x hx))
    (z' := ⟨y, hy⟩)
    b (e.map b (imageFiber p q F hF x hx)) χ
    (isCartesian_of_chosenPullback q b e (imageFiber p q F hF x hx))
    (isCartesian_of_isHomLift q hq b χ hχ)

/-- The morphism out of the chosen pullback attached to an arrow `y ⟶ F x` lying over `b`: the
identification, in the groupoid fibre over `V`, of the chosen pullback of `F x` with `y`. -/
public noncomputable def pullbackDatum (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {V U : C} (b : V ⟶ U) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (χ : y ⟶ F.obj x) (hχ : q.IsHomLift b χ) :
    (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩ :=
  (pullbackDatumIso p q hq F hF b x hx y hy e χ hχ).hom

/-- `Deformation.Artin.pullbackDatum` is a section of `Deformation.Artin.pullbackComparison`:
the source's datum `φ` and an arrow `y ⟶ F x` over `b` carry the same information. -/
public lemma pullbackComparison_pullbackDatum (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {V U : C} (b : V ⟶ U) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (χ : y ⟶ F.obj x) (hχ : q.IsHomLift b χ) :
    pullbackComparison p q hq F hF b x hx y hy e
        (pullbackDatum p q hq F hF b x hx y hy e χ hχ) = χ := by
  let : IsGroupoid (q.Fiber V) := hq.fiber_isGroupoid V
  rw [pullbackComparison, pullbackDatum, IsIso.Iso.inv_hom]
  exact pullbackDatumIso_inv_fac p q hq F hF b x hx y hy e χ hχ

/-- **Stacks 07Y7, the functor, read off an arrow over `b`.** The induced functor on lifts
attached to an arrow `y ⟶ F x` lying over `b` instead of to a morphism out of the chosen
pullback.  The two data correspond by `Deformation.Artin.pullbackComparison` and
`Deformation.Artin.pullbackDatum`, and the underlying functor is the one
`Deformation.Artin.liftOutFunctorOfPullback` builds; stating the construction this way fixes its
comparison arrow to be the given arrow, which is what the composition clause below needs. -/
public noncomputable def liftFunctorOfHom (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ U) (c : V' ⟶ U') (d : V ⟶ V')
    (hsq : b ≫ a = d ≫ c) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (χ : y ⟶ F.obj x) (hχ : q.IsHomLift b χ) :
    LiftOutFunctor p q F a b c d x hx y hy χ :=
  (liftOutFunctorOfPullback p q hq F hF a b c d hsq x hx y hy e
    (pullbackDatum p q hq F hF b x hx y hy e χ hχ)).ofEq
      (pullbackComparison_pullbackDatum p q hq F hF b x hx y hy e χ hχ)

/-- Two constructions satisfying the cartesian-square specification are uniquely isomorphic by
an isomorphism commuting with their comparison maps. In particular, the direct functor for a
composite of morphisms of fibred groupoids agrees canonically with the composite of the induced
lift functors. -/
@[stacks 07Y7 "uniqueness, on the source's Lift(x, A'), lifts out of the base"]
public theorem liftOutFunctor_unique (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ U) (c : V' ⟶ U') (d : V ⟶ V')
    (x : X) (hx : p.obj x = U) (y : Y) (hy : q.obj y = V)
    (φ : y ⟶ F.obj x)
    (L M : LiftOutFunctor p q F a b c d x hx y hy φ) :
    ∃! η : L.toFunctor ≅ M.toFunctor,
      ∀ t : LiftOut p a x hx,
        (η.hom.app t).1.right ≫ M.comparison t = L.comparison t := by
  have hcart (N : LiftOutFunctor p q F a b c d x hx y hy φ) (t : LiftOut p a x hx) :
      q.IsCartesian c (N.comparison t) := by
    have := N.isCartesian t
    infer_instance
  let LF : LiftOut p a x hx → q.Fiber V' := fun t =>
    ⟨(L.toFunctor.obj t).1.right, liftOut_base_obj q d y hy (L.toFunctor.obj t)⟩
  let MF : LiftOut p a x hx → q.Fiber V' := fun t =>
    ⟨(M.toFunctor.obj t).1.right, liftOut_base_obj q d y hy (M.toFunctor.obj t)⟩
  let fiso : ∀ t : LiftOut p a x hx, LF t ≅ MF t := fun t =>
    Functor.fiberIsoOfCartesian (z := LF t) (z' := MF t) c
      (L.comparison t) (M.comparison t) (hcart L t) (hcart M t)
  let E : ∀ t : LiftOut p a x hx,
      (L.toFunctor.obj t).1.right ≅ (M.toFunctor.obj t).1.right := fun t =>
    Functor.Fiber.fiberInclusion.mapIso (fiso t)
  have hEfac (t : LiftOut p a x hx) : (E t).hom ≫ M.comparison t = L.comparison t :=
    Functor.fiberIsoOfCartesian_hom_fac (z := LF t) (z' := MF t) c
      (L.comparison t) (M.comparison t) (hcart L t) (hcart M t)
  have hEhom (t : LiftOut p a x hx) : q.IsHomLift (𝟙 V') (E t).hom := (fiso t).hom.2
  have hEtri (t : LiftOut p a x hx) :
      (L.toFunctor.obj t).1.hom ≫ (E t).hom = (M.toFunctor.obj t).1.hom := by
    have h1 : q.IsHomLift d ((L.toFunctor.obj t).1.hom) :=
      liftOut_isHomLift q d y hy (L.toFunctor.obj t)
    have h2 : q.IsHomLift d ((M.toFunctor.obj t).1.hom) :=
      liftOut_isHomLift q d y hy (M.toFunctor.obj t)
    have h3 : q.IsHomLift (𝟙 V') (E t).hom := hEhom t
    have h4 : q.IsStronglyCartesian c (M.comparison t) := M.isCartesian t
    have h5 : q.IsHomLift d ((L.toFunctor.obj t).1.hom ≫ (E t).hom) :=
      IsHomLift.comp_lift_id_right' q d ((L.toFunctor.obj t).1.hom) V' (E t).hom
    refine Functor.IsStronglyCartesian.ext q c (M.comparison t) d ?_
    rw [Category.assoc, hEfac, L.comm t, M.comm t]
  let ηapp : ∀ t : LiftOut p a x hx, L.toFunctor.obj t ≅ M.toFunctor.obj t := fun t =>
    liftAlongIsoMk q y _ (E t) (hEhom t) (hEtri t)
  have hηapp (t : LiftOut p a x hx) : (ηapp t).hom.1.right = (E t).hom := rfl
  have hnat {s t : LiftOut p a x hx} (m : s ⟶ t) :
      L.toFunctor.map m ≫ (ηapp t).hom = (ηapp s).hom ≫ M.toFunctor.map m := by
    refine liftOut_hom_ext q d y hy ?_
    have h1 : q.IsHomLift (𝟙 V') (L.toFunctor.map m).1.right :=
      liftOut_morphism_isHomLift q d y hy (L.toFunctor.map m)
    have h2 : q.IsHomLift (𝟙 V') (M.toFunctor.map m).1.right :=
      liftOut_morphism_isHomLift q d y hy (M.toFunctor.map m)
    have h3 : q.IsHomLift (𝟙 V') (E s).hom := hEhom s
    have h4 : q.IsHomLift (𝟙 V') (E t).hom := hEhom t
    have h5 : q.IsStronglyCartesian c (M.comparison t) := M.isCartesian t
    have h6 : q.IsHomLift (𝟙 V') ((L.toFunctor.map m).1.right ≫ (E t).hom) :=
      IsHomLift.comp_lift_id_right' q (𝟙 V') ((L.toFunctor.map m).1.right) V' (E t).hom
    have h7 : q.IsHomLift (𝟙 V') ((E s).hom ≫ (M.toFunctor.map m).1.right) :=
      IsHomLift.comp_lift_id_right' q (𝟙 V') (E s).hom V' ((M.toFunctor.map m).1.right)
    rw [liftOut_comp_right, liftOut_comp_right, hηapp, hηapp]
    refine Functor.IsStronglyCartesian.ext q c (M.comparison t) (𝟙 V') ?_
    rw [Category.assoc, hEfac, L.natural m, ← hEfac s, Category.assoc, ← M.natural m,
      Category.assoc]
  let η : L.toFunctor ≅ M.toFunctor := NatIso.ofComponents ηapp hnat
  have hη (t : LiftOut p a x hx) : η.hom.app t = (ηapp t).hom := rfl
  refine ⟨η, fun t => ?_, fun η' hη' => ?_⟩
  · rw [hη t, hηapp t]
    exact hEfac t
  · apply Iso.ext
    apply NatTrans.ext
    funext t
    refine liftOut_hom_ext q d y hy ?_
    have h1 : q.IsHomLift (𝟙 V') (η'.hom.app t).1.right :=
      liftOut_morphism_isHomLift q d y hy (η'.hom.app t)
    have h2 : q.IsHomLift (𝟙 V') (η.hom.app t).1.right :=
      liftOut_morphism_isHomLift q d y hy (η.hom.app t)
    have h3 : q.IsStronglyCartesian c (M.comparison t) := M.isCartesian t
    refine Functor.IsStronglyCartesian.ext q c (M.comparison t) (𝟙 V') ?_
    rw [hη' t, hη t, hηapp t, hEfac t]

/-- Any construction on lifts for a composite of morphisms of fibred groupoids is canonically
isomorphic to the composite of any two constructions for the factors. The second morphism acts
over the identity square at the target of the first. At every lift, the isomorphism is the
unique vertical morphism commuting with the two cartesian comparison arrows. This is the
general comparison; the source's clause for the construction itself is
`Deformation.Artin.liftFunctorOfHom_comp`, which instantiates it at the three functors
`Deformation.Artin.liftFunctorOfHom` builds. -/
public noncomputable def liftOutFunctor_comp
    {Z : Type*} [Category Z]
    (p : X ⥤ C) (q : Y ⥤ C) (r : Z ⥤ C)
    (_hq : q.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
    (F : X ⥤ Y) (G : Y ⥤ Z)
    (_hF : F ⋙ q = p) (hG : G ⋙ r = q)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ U)
    (c : V' ⟶ U') (d : V ⟶ V')
    (_hsq : b ≫ a = d ≫ c)
    (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V)
    (z : Z) (hz : r.obj z = V)
    (φ : y ⟶ F.obj x) (ψ : z ⟶ G.obj y)
    (_hφ : q.IsHomLift b φ) (_hψ : r.IsHomLift (𝟙 V) ψ)
    (L : LiftOutFunctor p q F a b c d x hx y hy φ)
    (M : LiftOutFunctor q r G d (𝟙 V) (𝟙 V') d y hy z hz ψ)
    (N : LiftOutFunctor p r (F ⋙ G) a b c d x hx z hz (ψ ≫ G.map φ)) :
    {η : L.toFunctor ⋙ M.toFunctor ≅ N.toFunctor //
      ∀ t : LiftOut p a x hx,
        (η.hom.app t).1.right ≫ N.comparison t =
          M.comparison (L.toFunctor.obj t) ≫ G.map (L.comparison t)} := by
  let γ (t : LiftOut p a x hx) :=
    M.comparison (L.toFunctor.obj t) ≫ G.map (L.comparison t)
  let K : LiftOutFunctor p r (F ⋙ G) a b c d x hx z hz (ψ ≫ G.map φ) := {
    toFunctor := L.toFunctor ⋙ M.toFunctor
    comparison := γ
    isCartesian := by
      intro t
      let : r.IsStronglyCartesian (𝟙 V')
          (M.comparison (L.toFunctor.obj t)) := M.isCartesian (L.toFunctor.obj t)
      let : q.IsHomLift c (L.comparison t) := (L.isCartesian t).toIsHomLift
      let hGmap : r.IsHomLift c (G.map (L.comparison t)) :=
        lift_map_isHomLift q r G hG c
          (IsHomLift.domain_eq q c (L.comparison t))
          (IsHomLift.codomain_eq q c (L.comparison t))
          (L.comparison t) (L.isCartesian t).toIsHomLift
      let : r.IsHomLift c (G.map (L.comparison t)) := hGmap
      let : r.IsStronglyCartesian c (G.map (L.comparison t)) :=
        hr.isStronglyCartesian_homLift c (G.map (L.comparison t))
      simpa [γ] using
        (inferInstance : r.IsStronglyCartesian
          (𝟙 V' ≫ c) (M.comparison (L.toFunctor.obj t) ≫ G.map (L.comparison t)))
    comm := by
      intro t
      let u := L.toFunctor.obj t
      change (M.toFunctor.obj u).1.hom ≫ γ t =
        (ψ ≫ G.map φ) ≫ (F ⋙ G).map t.1.hom
      calc
        (M.toFunctor.obj u).1.hom ≫ γ t =
            ((M.toFunctor.obj u).1.hom ≫ M.comparison u) ≫ G.map (L.comparison t) := by
          dsimp [γ]
          exact (Category.assoc ..).symm
        _ = (ψ ≫ G.map u.1.hom) ≫ G.map (L.comparison t) := by rw [M.comm u]
        _ = ψ ≫ G.map (u.1.hom ≫ L.comparison t) := by
          simp only [Category.assoc, ← G.map_comp]
        _ = ψ ≫ G.map (φ ≫ F.map t.1.hom) := by rw [L.comm t]
        _ = (ψ ≫ G.map φ) ≫ (F ⋙ G).map t.1.hom := by
          simp only [G.map_comp, Category.assoc, Functor.comp_map]
    natural := by
      intro s t m
      change (M.toFunctor.map (L.toFunctor.map m)).1.right ≫ γ t =
        γ s ≫ (F ⋙ G).map m.1.right
      calc
        (M.toFunctor.map (L.toFunctor.map m)).1.right ≫ γ t =
            ((M.toFunctor.map (L.toFunctor.map m)).1.right ≫
              M.comparison (L.toFunctor.obj t)) ≫ G.map (L.comparison t) := by
                dsimp [γ]
                exact (Category.assoc ..).symm
        _ = (M.comparison (L.toFunctor.obj s) ≫
              G.map ((L.toFunctor.map m).1.right)) ≫ G.map (L.comparison t) :=
                congrArg (fun f => f ≫ G.map (L.comparison t))
                  (M.natural (L.toFunctor.map m))
        _ = M.comparison (L.toFunctor.obj s) ≫
              G.map ((L.toFunctor.map m).1.right ≫ L.comparison t) :=
                (Category.assoc ..).trans
                  (congrArg (fun f => M.comparison (L.toFunctor.obj s) ≫ f)
                    (G.map_comp (L.toFunctor.map m).1.right (L.comparison t)).symm)
        _ = M.comparison (L.toFunctor.obj s) ≫
              G.map (L.comparison s ≫ F.map m.1.right) :=
                congrArg (fun f => M.comparison (L.toFunctor.obj s) ≫ G.map f)
                  (L.natural m)
        _ = (M.comparison (L.toFunctor.obj s) ≫ G.map (L.comparison s)) ≫
              G.map (F.map m.1.right) :=
                (congrArg (fun f => M.comparison (L.toFunctor.obj s) ≫ f)
                  (G.map_comp (L.comparison s) (F.map m.1.right))).trans
                    (Category.assoc ..).symm
        _ = γ s ≫ (F ⋙ G).map m.1.right := rfl
  }
  have huniq := liftOutFunctor_unique p r (F ⋙ G) a b c d x hx z hz
    (ψ ≫ G.map φ) K N
  exact ⟨_, Classical.choose_spec huniq.exists⟩

/-- A composite of `1`-morphisms over the base is again a `1`-morphism over the base. -/
public lemma comp_over_base {Z : Type*} [Category Z] {p : X ⥤ C} {q : Y ⥤ C} {r : Z ⥤ C}
    {F : X ⥤ Y} {G : Y ⥤ Z} (hF : F ⋙ q = p) (hG : G ⋙ r = q) : (F ⋙ G) ⋙ r = p := by
  rw [Functor.assoc, hG, hF]

/-- The commutative square with identity columns at an arrow of the base: the square along
which a second `1`-morphism acts on the lifts the first one produced. -/
public lemma id_comp_square {V V' : C} (d : V ⟶ V') : 𝟙 V ≫ d = d ≫ 𝟙 V' := by simp

/-- The arrow attached to a composite of `1`-morphisms, namely `ψ` followed by the image of
`φ`, lies over the arrow `b` that `φ` lies over. -/
public lemma comp_comparison_isHomLift {Z : Type*} [Category Z] (q : Y ⥤ C) (r : Z ⥤ C)
    (F : X ⥤ Y) (G : Y ⥤ Z) (hG : G ⋙ r = q) {V U : C} (b : V ⟶ U) (x : X) (y : Y) (z : Z)
    (φ : y ⟶ F.obj x) (hφ : q.IsHomLift b φ)
    (ψ : z ⟶ G.obj y) (hψ : r.IsHomLift (𝟙 V) ψ) :
    r.IsHomLift b (ψ ≫ G.map φ) := by
  have : q.IsHomLift b φ := hφ
  have : r.IsHomLift (𝟙 V) ψ := hψ
  have : r.IsHomLift b (G.map φ) :=
    lift_map_isHomLift q r G hG b (IsHomLift.domain_eq q b φ)
      (IsHomLift.codomain_eq q b φ) φ hφ
  have h : r.IsHomLift (𝟙 V ≫ b) (ψ ≫ G.map φ) := inferInstance
  simpa using h

/-- **Stacks 07Y7, compatibility with composition.** The construction is compatible with
composition of `1`-morphisms of categories fibred in groupoids: the functor on lifts induced
by `F` and `φ`, followed by the functor on lifts induced by `G` and `ψ` over the identity
square at `d`, is canonically isomorphic to the functor on lifts induced by `F ⋙ G` and the
composite arrow `ψ ≫ G φ`, by the unique isomorphism commuting with the cartesian comparison
arrows.

All three functors here are built, not assumed to satisfy the specification: each is, by
definition, a functor `Deformation.Artin.liftOutFunctorOfPullback` builds from the datum
`Deformation.Artin.pullbackDatum` attaches to the given arrow. The source's data are covered
because a morphism out of the chosen pullback gives such an arrow, by
`Deformation.Artin.pullbackComparison` and
`Deformation.Artin.pullbackComparison_isHomLift`. -/
@[stacks 07Y7 "compatibility with composition, on the source's Lift(x, A'), lifts out of the base"]
public noncomputable def liftFunctorOfHom_comp {Z : Type*} [Category Z]
    (p : X ⥤ C) (q : Y ⥤ C) (r : Z ⥤ C)
    (hq : q.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
    (F : X ⥤ Y) (G : Y ⥤ Z) (hF : F ⋙ q = p) (hG : G ⋙ r = q)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ U) (c : V' ⟶ U') (d : V ⟶ V')
    (hsq : b ≫ a = d ≫ c) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (z : Z) (hz : r.obj z = V)
    (eY : q.ChoiceOfPullbacks) (eZ : r.ChoiceOfPullbacks)
    (φ : y ⟶ F.obj x) (hφ : q.IsHomLift b φ)
    (ψ : z ⟶ G.obj y) (hψ : r.IsHomLift (𝟙 V) ψ) :
    {η : (liftFunctorOfHom p q hq F hF a b c d hsq x hx y hy eY φ hφ).toFunctor ⋙
          (liftFunctorOfHom q r hr G hG d (𝟙 V) (𝟙 V') d (id_comp_square d) y hy z hz
            eZ ψ hψ).toFunctor ≅
        (liftFunctorOfHom p r hr (F ⋙ G) (comp_over_base hF hG) a b c d hsq x hx z hz eZ
          (ψ ≫ G.map φ)
          (comp_comparison_isHomLift q r F G hG b x y z φ hφ ψ hψ)).toFunctor //
      ∀ t : LiftOut p a x hx,
        (η.hom.app t).1.right ≫
            (liftFunctorOfHom p r hr (F ⋙ G) (comp_over_base hF hG) a b c d hsq x hx z hz eZ
              (ψ ≫ G.map φ)
              (comp_comparison_isHomLift q r F G hG b x y z φ hφ ψ hψ)).comparison t =
          (liftFunctorOfHom q r hr G hG d (𝟙 V) (𝟙 V') d (id_comp_square d) y hy z hz
              eZ ψ hψ).comparison
            ((liftFunctorOfHom p q hq F hF a b c d hsq x hx y hy eY φ hφ).toFunctor.obj t) ≫
            G.map ((liftFunctorOfHom p q hq F hF a b c d hsq x hx y hy eY φ hφ).comparison t)} :=
  liftOutFunctor_comp p q r hq hr F G hF hG a b c d hsq x hx y hy z hz φ ψ hφ hψ
    (liftFunctorOfHom p q hq F hF a b c d hsq x hx y hy eY φ hφ)
    (liftFunctorOfHom q r hr G hG d (𝟙 V) (𝟙 V') d (id_comp_square d) y hy z hz eZ ψ hψ)
    (liftFunctorOfHom p r hr (F ⋙ G) (comp_over_base hF hG) a b c d hsq x hx z hz eZ
      (ψ ≫ G.map φ) (comp_comparison_isHomLift q r F G hG b x y z φ hφ ψ hψ))

end

end Deformation.Artin
