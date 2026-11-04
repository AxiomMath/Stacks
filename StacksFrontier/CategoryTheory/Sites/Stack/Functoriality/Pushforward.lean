module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.StronglyCartesianEqToHom

/-!
# Pushforward of a fibred category along a functor

Let `u : 𝒞 ⥤ 𝒟` be a functor and `p : 𝒮 ⥤ 𝒟` a category over `𝒟`. The category `u^p𝒮` has
as objects the pairs `(U, y)` with `U : 𝒞` and `y : 𝒮` satisfying `p y = u U`, and as
morphisms `(U, y) ⟶ (U', y')` the pairs `(a, β)` with `a : U ⟶ U'` in `𝒞` and `β : y ⟶ y'`
in `𝒮` satisfying `p β = u a`. It is a category over `𝒞` via `(U, y) ↦ U`, and it is fibred
over `𝒞` as soon as `p` is fibred over `𝒟`. If `u` is the continuous functor defining a
morphism of sites `f : 𝒟 → 𝒞`, then `u^p𝒮` is written `f_*𝒮`, the pushforward of `𝒮`
along `f`.

Both defining conditions `p y = u U` and `p β = u a` are *equalities*, so `u^p𝒮` is the
strict pullback of `u` and `p` in the category of categories; that is the name used here.
It is not Mathlib's `CategoryTheory.Limits.CategoricalPullback u p`, whose objects carry an
*isomorphism* `u U ≅ p y` in place of the equality: the two categories are genuinely
inequivalent, and it is the strict one whose strongly cartesian morphisms are described by
`StrictPullback.isStronglyCartesian_of_fib` below.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮]

/-- An object of the strict pullback `u^p𝒮` of `u : 𝒞 ⥤ 𝒟` and `p : 𝒮 ⥤ 𝒟`: a pair
`(U, y)` of an object `U` of `𝒞` and an object `y` of `𝒮` with `p y = u U`. -/
structure StrictPullback (u : 𝒞 ⥤ 𝒟) (p : 𝒮 ⥤ 𝒟) where
  /-- The object `U` of `𝒞`. -/
  base : 𝒞
  /-- The object `y` of `𝒮`. -/
  fib : 𝒮
  /-- `y` lies over `u U`, on the nose. -/
  over : p.obj fib = u.obj base

namespace StrictPullback

variable {u : 𝒞 ⥤ 𝒟} {p : 𝒮 ⥤ 𝒟}

/-- A morphism `(U, y) ⟶ (U', y')` of `u^p𝒮`: a pair `(a, β)` of a morphism `a : U ⟶ U'`
of `𝒞` and a morphism `β : y ⟶ y'` of `𝒮` with `p β = u a`. -/
@[ext]
structure Hom (X Y : StrictPullback u p) where
  /-- The `𝒞`-component `a : U ⟶ U'`. -/
  base : X.base ⟶ Y.base
  /-- The `𝒮`-component `β : y ⟶ y'`. -/
  fib : X.fib ⟶ Y.fib
  /-- `β` lies over `a`, on the nose. -/
  over : p.map fib = eqToHom X.over ≫ u.map base ≫ eqToHom Y.over.symm

/-- The identity morphism of `u^p𝒮`, the pair of identities. -/
@[simps]
def Hom.id (X : StrictPullback u p) : Hom X X where
  base := 𝟙 X.base
  fib := 𝟙 X.fib
  over := by simp

/-- Composition in `u^p𝒮`, componentwise. -/
@[simps]
def Hom.comp {X Y Z : StrictPullback u p} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fib := f.fib ≫ g.fib
  over := by rw [Functor.map_comp, f.over, g.over, Functor.map_comp]; simp

/-- `u^p𝒮` is a category, with componentwise identities and composition. -/
instance instCategory : Category (StrictPullback u p) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by apply Hom.ext <;> simp
  comp_id f := by apply Hom.ext <;> simp
  assoc f g h := by apply Hom.ext <;> simp

/-- The `𝒞`-component of the identity morphism of `u^p𝒮` is the identity of `𝒞`. -/
@[simp] lemma id_base (X : StrictPullback u p) : Hom.base (𝟙 X) = 𝟙 X.base := rfl

/-- The `𝒮`-component of the identity morphism of `u^p𝒮` is the identity of `𝒮`. -/
@[simp] lemma id_fib (X : StrictPullback u p) : Hom.fib (𝟙 X) = 𝟙 X.fib := rfl

/-- The `𝒞`-component of a composite in `u^p𝒮` is the composite of the `𝒞`-components. -/
@[simp] lemma comp_base {X Y Z : StrictPullback u p} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base := rfl

/-- The `𝒮`-component of a composite in `u^p𝒮` is the composite of the `𝒮`-components. -/
@[simp] lemma comp_fib {X Y Z : StrictPullback u p} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fib = f.fib ≫ g.fib := rfl

/-- The structure functor `u^p𝒮 ⥤ 𝒞` exhibiting `u^p𝒮` as a category over `𝒞`:
`(U, y) ↦ U` and `(a, β) ↦ a`. -/
@[simps, implicit_reducible]
def structureFunctor (u : 𝒞 ⥤ 𝒟) (p : 𝒮 ⥤ 𝒟) : StrictPullback u p ⥤ 𝒞 where
  obj X := X.base
  map f := f.base

/-- Every morphism of `u^p𝒮` lies over its own `𝒞`-component. -/
lemma isHomLift_hom {X Y : StrictPullback u p} (f : X ⟶ Y) :
    (structureFunctor u p).IsHomLift f.base f :=
  IsHomLift.map (p := structureFunctor u p) f

/-- The `𝒞`-component of a morphism of `u^p𝒮` is the only morphism of `𝒞` it lies over. -/
lemma base_eq {X Y : StrictPullback u p} (a : X.base ⟶ Y.base) (f : X ⟶ Y)
    [(structureFunctor u p).IsHomLift a f] : f.base = a := by
  -- `IsHomLift.fac'` states this with `eqToHom`s on both sides whose proofs are of
  -- `(structureFunctor u p).obj X = X.base`, i.e. of `X.base = X.base`; spelling them as `rfl`
  -- lets `simp` erase them.
  have h : f.base = eqToHom (rfl : X.base = X.base) ≫ a ≫ eqToHom (rfl : Y.base = Y.base) :=
    IsHomLift.fac' (structureFunctor u p) a f
  simpa using h

/-- A morphism of `u^p𝒮` lying over `a` has `𝒮`-component lying over the corresponding
morphism `p y ⟶ p y'`. -/
private lemma isHomLift_fib {X Y : StrictPullback u p} (a : X.base ⟶ Y.base) (f : X ⟶ Y)
    [(structureFunctor u p).IsHomLift a f] :
    p.IsHomLift (eqToHom X.over ≫ u.map a ≫ eqToHom Y.over.symm) f.fib :=
  IsHomLift.of_fac' p _ _ rfl rfl (by simp [f.over, base_eq a f])

/-- The universal property of a morphism of `u^p𝒮` whose `𝒮`-component is strongly
cartesian: a morphism into its codomain factors uniquely through it once a factorization of
the `𝒞`-components is given. -/
private lemma existsUnique_of_fib {X Y : StrictPullback u p} (f : X ⟶ Y)
    (hβ : p.IsStronglyCartesian (eqToHom X.over ≫ u.map f.base ≫ eqToHom Y.over.symm) f.fib)
    {Z : StrictPullback u p} (a : Z.base ⟶ X.base) (g : Z ⟶ Y)
    [hg : (structureFunctor u p).IsHomLift (a ≫ f.base) g] :
    ∃! h : Z ⟶ X, (structureFunctor u p).IsHomLift a h ∧ h ≫ f = g := by
  have hgbase : g.base = a ≫ f.base := base_eq _ g
  have : p.IsHomLift ((eqToHom Z.over ≫ u.map a ≫ eqToHom X.over.symm) ≫
      eqToHom X.over ≫ u.map f.base ≫ eqToHom Y.over.symm) g.fib := by
    convert isHomLift_fib (a ≫ f.base) g using 1
    simp
  obtain ⟨δ, ⟨hδ, hδ_comp⟩, hδ_uniq⟩ :=
    hβ.universal_property' (eqToHom Z.over ≫ u.map a ≫ eqToHom X.over.symm) g.fib
  have hδ_map : p.map δ = eqToHom Z.over ≫ u.map a ≫ eqToHom X.over.symm := by
    have := hδ
    simpa using IsHomLift.fac' p (eqToHom Z.over ≫ u.map a ≫ eqToHom X.over.symm) δ
  refine ⟨⟨a, δ, hδ_map⟩, ⟨isHomLift_hom ⟨a, δ, hδ_map⟩, Hom.ext hgbase.symm hδ_comp⟩, ?_⟩
  rintro h ⟨_, hh⟩
  have hh_base : h.base = a := base_eq a h
  have := isHomLift_fib a h
  exact Hom.ext hh_base
    (hδ_uniq h.fib ⟨inferInstance, by simpa using congr_arg Hom.fib hh⟩)

/-- A morphism of `u^p𝒮` is strongly cartesian over `𝒞` as soon as its `𝒮`-component is
strongly cartesian over `𝒟`. -/
lemma isStronglyCartesian_of_fib {X Y : StrictPullback u p} (f : X ⟶ Y)
    (hβ : p.IsStronglyCartesian (eqToHom X.over ≫ u.map f.base ≫ eqToHom Y.over.symm) f.fib) :
    (structureFunctor u p).IsStronglyCartesian f.base f :=
  have := isHomLift_hom f
  Functor.IsStronglyCartesian.mk fun a g hg ↦ existsUnique_of_fib (hg := hg) f hβ a g

/-- **Stacks 04WB**.
If `p : 𝒮 ⥤ 𝒟` is a fibred category, then so is the pushforward `u^p𝒮 ⥤ 𝒞` along any
functor `u : 𝒞 ⥤ 𝒟`. -/
@[stacks 04WB]
theorem isFibered_structureFunctor (u : 𝒞 ⥤ 𝒟) (p : 𝒮 ⥤ 𝒟) [p.IsFibered] :
    (structureFunctor u p).IsFibered := by
  refine Functor.IsFibered.of_exists_isStronglyCartesian fun Y U a ↦ ?_
  obtain ⟨y, β, _⟩ := Functor.IsPreFibered.exists_isCartesian' (p := p) (a := Y.fib)
    (u.map a ≫ eqToHom Y.over.symm)
  have hβs : p.IsStronglyCartesian (u.map a ≫ eqToHom Y.over.symm) β := inferInstance
  have hy : p.obj y = u.obj U := IsHomLift.domain_eq p (u.map a ≫ eqToHom Y.over.symm) β
  have hover : p.map β = eqToHom hy ≫ u.map a ≫ eqToHom Y.over.symm := by
    rw [IsHomLift.fac' p (u.map a ≫ eqToHom Y.over.symm) β]; simp
  let X : StrictPullback u p := ⟨U, y, hy⟩
  let f : X ⟶ Y := ⟨a, β, hover⟩
  exact ⟨X, f, isStronglyCartesian_of_fib f
    (Functor.IsStronglyCartesian.eqToHom_comp hy _ β hβs)⟩

attribute [instance] isFibered_structureFunctor

end StrictPullback

/-- **Stacks 04WE**.
Notation: for a morphism of sites `f : 𝒟 → 𝒞` given by a continuous functor
`u : 𝒞 ⥤ 𝒟` and a fibred category `p : 𝒮 ⥤ 𝒟`, one writes `f_*𝒮` for the fibred category
`u^p𝒮` over `𝒞` and calls it the *pushforward of `𝒮` along `f`*. The topologies `J` and `K`
and the continuity of `u` play no role in the construction; they are the data of `f`, which
is what this notation names. -/
@[stacks 04WE]
def pushforwardFibredCategory (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟)
    (u : 𝒞 ⥤ 𝒟) [u.IsContinuous J K] (p : 𝒮 ⥤ 𝒟) [p.IsFibered] :
    StrictPullback u p ⥤ 𝒞 :=
  StrictPullback.structureFunctor u p

/-- The pushforward `f_*𝒮` is a fibred category over `𝒞`. -/
theorem isFibered_pushforwardFibredCategory (J : GrothendieckTopology 𝒞)
    (K : GrothendieckTopology 𝒟) (u : 𝒞 ⥤ 𝒟) [u.IsContinuous J K] (p : 𝒮 ⥤ 𝒟) [p.IsFibered] :
    (pushforwardFibredCategory J K u p).IsFibered :=
  StrictPullback.isFibered_structureFunctor u p

end CategoryTheory
