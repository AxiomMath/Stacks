module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStageBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional

/-!
# Polarized families across a pushout along a thickening (Stacks 0D44)

Let

```
T  --i-->  T'
|          |
f          g
|          |
v          v
S  --h-->  S'
```

be a commutative square of schemes of the big fppf site. Base change makes the fibre categories
of the polarized families of Stacks 0D1M into a contravariant assignment on the site, and the two
ways of restricting a polarized family over `S'` to the overlap `T` are canonically identified.
The resulting comparison functor

`𝒫olarized_{S'} ⟶ 𝒫olarized_S ×_{𝒫olarized_T} 𝒫olarized_{T'}`

into the 2-fibre product is the functor of Stacks 0D44, which asserts it to be an equivalence
when the square is a pushout with `i` a thickening and `f` affine.

## Main definitions

* `CategoryTheory.Functor.fiberPullback`: for a fibred category `p`, the base-change functor
  `p.Fiber S ⥤ p.Fiber R` along a morphism `R ⟶ S` of the base, together with
  `CategoryTheory.Functor.fiberPullbackHom`, the cartesian morphism it comes from.
* `CategoryTheory.Functor.fiberPullbackCompIso`: the comparison of an iterated base change with
  the base change along the composite.
* `CategoryTheory.Functor.fiberSquareRestriction`: for a commutative square in the base, the
  comparison functor from the fibre over the fourth corner to the 2-fibre product of the fibres
  over the other three.
* `AlgebraicGeometry.polarizedFiberPullback`: base change of polarized families on fibre
  categories.
* `AlgebraicGeometry.polarizedPushoutRestriction`: **Stacks 0D44**, the comparison functor
  `𝒫olarized_{S'} ⟶ 𝒫olarized_S ×_{𝒫olarized_T} 𝒫olarized_{T'}`.

## Main results

* `CategoryTheory.Functor.fiberPullback_map_fac`: the base change of a morphism of a fibre
  category is characterized by its compatibility with the cartesian morphisms.
* `AlgebraicGeometry.polarizedFiberPullbackObjIso`: the base change of a polarized family is the
  fibre product of total spaces with the polarization pulled back, that is
  `AlgebraicGeometry.PolarizedFamily.stageBaseChange`.

## Implementation notes

**What is not proved here.** That the comparison functor is an equivalence — the assertion of
Stacks 0D44 — is not proved. One of its two inputs is absent from this development: Stacks 07RX,
the equivalence between the schemes flat and locally of finite presentation over the pushout and
the triples of such schemes over the three other corners. The other, the equivalence of Stacks
08KU for quasi-coherent modules flat over the base, is available as
`Stacks.Pushout.isEquivalence_flatBaseChangeTripleFunctor` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningPushout08KU.lean`. Neither half of the
conclusion survives the absence of Stacks 07RX: essential surjectivity is exactly
the gluing of the total space and of the polarization, and even faithfulness fails without the
pushout description of the total space, since a thickening is not an epimorphism of schemes and a
morphism out of the total space over `S'` is therefore not determined by its restrictions to the
total spaces over `S` and over `T'`.

**The comparison functor needs no hypothesis on the square beyond commutativity**, so it is
constructed here for an arbitrary commutative square and in particular covers the situation of
the tag; this is the same generality as the comparison functor of Stacks 08KU in the file named
above.

The base change on fibre categories is the one given by the *chosen* cartesian lifts of the
fibred structure, which is how `CategoryTheory.Functor.IsPreFibered.pullbackObj` presents them,
so it is determined only up to canonical isomorphism. For polarized families
`AlgebraicGeometry.polarizedFiberPullbackObjIso` identifies it with the explicit fibre-product
base change, every morphism of a category fibred in groupoids being cartesian over its image. The
fibred structure used is the unconditional one, so nothing is carried.

The 2-fibre product is Mathlib's `CategoryTheory.Limits.CategoricalPullback`, and the comparison
functor is obtained from its universal property
`CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback` applied
to the two base-change functors together with the overlap isomorphism, rather than built by hand.

The base change of a morphism is introduced twice, once as a morphism of the ambient category
between the chosen base changes and once as the action of the functor, the two being
interchangeable by `CategoryTheory.Functor.fiberInclusion_map_fiberPullback_map`. The reason is
that a morphism of a fibre category and its underlying morphism of the ambient category have
different normal forms, and the hypotheses that a morphism lies over a given morphism of the base
are resolved by instance search, which does not see through the projection of a fibre category to
its ambient category: each statement is therefore written in the normal form of the
`CategoryTheory.Functor.IsHomLift` hypotheses it has to discharge.

The general part of this file is category theory and belongs in a file of its own next to
`Mathlib/CategoryTheory/FiberedCategory/Fiber.lean`; it is here because nothing else consumes it
yet.

## References

* [Stacks Project, Tag 0D44](https://stacks.math.columbia.edu/tag/0D44)
* [Stacks Project, Tag 0D1M](https://stacks.math.columbia.edu/tag/0D1M)
* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 08KU](https://stacks.math.columbia.edu/tag/08KU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)
  [p.IsFibered] {R S : 𝒮} (f : R ⟶ S)

omit [p.IsFibered] in
/-- An isomorphism of the ambient category lying over an identity of the base is an isomorphism
of the fibre category. -/
def fiberIsoMk {V : 𝒮} {a b : p.Fiber V}
    (e : Fiber.fiberInclusion.obj a ≅ Fiber.fiberInclusion.obj b)
    (he : p.IsHomLift (𝟙 V) e.hom) : a ≅ b where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, haveI := he; IsHomLift.lift_id_inv p V e⟩
  hom_inv_id := Fiber.hom_ext (by rw [Functor.map_comp, Functor.map_id]; exact e.hom_inv_id)
  inv_hom_id := Fiber.hom_ext (by rw [Functor.map_comp, Functor.map_id]; exact e.inv_hom_id)

omit [p.IsFibered] in
/-- The morphism of the ambient category underlying the isomorphism of a fibre category built
from an isomorphism lying over an identity is that isomorphism. -/
@[simp]
theorem fiberInclusion_map_fiberIsoMk_hom {V : 𝒮} {a b : p.Fiber V}
    (e : Fiber.fiberInclusion.obj a ≅ Fiber.fiberInclusion.obj b)
    (he : p.IsHomLift (𝟙 V) e.hom) :
    Fiber.fiberInclusion.map (fiberIsoMk p e he).hom = e.hom :=
  rfl

/-- The base change along `f : R ⟶ S` of a morphism of the fibre of `p` over `S`, as a morphism
of the ambient category between the chosen base changes of its source and target: the morphism
induced by the universal property of the chosen cartesian morphism at the target. -/
def fiberPullbackMap {a b : p.Fiber S} (φ : a ⟶ b) :
    IsPreFibered.pullbackObj a.2 f ⟶ IsPreFibered.pullbackObj b.2 f :=
  haveI : p.IsHomLift (𝟙 S) φ.1 := φ.2
  IsCartesian.map p f (IsPreFibered.pullbackMap b.2 f) (IsPreFibered.pullbackMap a.2 f ≫ φ.1)

/-- The base change of a morphism of a fibre category lies over the identity of the new base. -/
instance isHomLift_fiberPullbackMap {a b : p.Fiber S} (φ : a ⟶ b) :
    p.IsHomLift (𝟙 R) (fiberPullbackMap p f φ) :=
  haveI : p.IsHomLift (𝟙 S) φ.1 := φ.2
  IsCartesian.map_isHomLift p f (IsPreFibered.pullbackMap b.2 f)
    (IsPreFibered.pullbackMap a.2 f ≫ φ.1)

/-- The base change of a morphism is compatible with the chosen cartesian morphisms. -/
@[reassoc]
theorem fiberPullbackMap_fac {a b : p.Fiber S} (φ : a ⟶ b) :
    fiberPullbackMap p f φ ≫ IsPreFibered.pullbackMap b.2 f =
      IsPreFibered.pullbackMap a.2 f ≫ φ.1 :=
  have : p.IsHomLift (𝟙 S) φ.1 := φ.2
  IsCartesian.fac p f (IsPreFibered.pullbackMap b.2 f)
    (IsPreFibered.pullbackMap a.2 f ≫ φ.1)

/-- The base change of an identity morphism is an identity. -/
theorem fiberPullbackMap_id (a : p.Fiber S) :
    fiberPullbackMap p f (𝟙 a) = 𝟙 (IsPreFibered.pullbackObj a.2 f) := by
  have h : p.IsHomLift (𝟙 R) (𝟙 (IsPreFibered.pullbackObj a.2 f)) :=
    IsHomLift.id (IsPreFibered.pullbackObj_proj a.2 f)
  refine IsCartesian.ext p f (IsPreFibered.pullbackMap a.2 f) _ _ ?_
  rw [fiberPullbackMap_fac]
  show IsPreFibered.pullbackMap a.2 f ≫ 𝟙 _ = _
  simp

/-- The base change of a composite is the composite of the base changes. -/
theorem fiberPullbackMap_comp {a b c : p.Fiber S} (φ : a ⟶ b) (ψ : b ⟶ c) :
    fiberPullbackMap p f (φ ≫ ψ) = fiberPullbackMap p f φ ≫ fiberPullbackMap p f ψ := by
  refine IsCartesian.ext p f (IsPreFibered.pullbackMap c.2 f) _ _ ?_
  rw [Category.assoc, fiberPullbackMap_fac, fiberPullbackMap_fac, ← Category.assoc,
    fiberPullbackMap_fac, Category.assoc]
  rfl

/-- **The base-change functor on fibre categories.** Along `f : R ⟶ S` it takes an object of the
fibre of a fibred category over `S` to its chosen base change in the fibre over `R`. -/
@[ega "I 3.3.7" "more general"]
def fiberPullback : p.Fiber S ⥤ p.Fiber R where
  obj a := ⟨IsPreFibered.pullbackObj a.2 f, IsPreFibered.pullbackObj_proj a.2 f⟩
  map φ := ⟨fiberPullbackMap p f φ, isHomLift_fiberPullbackMap p f φ⟩
  map_id a := Subtype.ext (fiberPullbackMap_id p f a)
  map_comp φ ψ := Subtype.ext (fiberPullbackMap_comp p f φ ψ)

/-- The morphism of the ambient category underlying the action of the base-change functor on a
morphism is the base change of that morphism. -/
theorem fiberInclusion_map_fiberPullback_map {a b : p.Fiber S} (φ : a ⟶ b) :
    Fiber.fiberInclusion.map ((fiberPullback p f).map φ) = fiberPullbackMap p f φ :=
  rfl

/-- The cartesian morphism from the base change of `a` along `f` to `a`. -/
def fiberPullbackHom (a : p.Fiber S) :
    Fiber.fiberInclusion.obj ((fiberPullback p f).obj a) ⟶ Fiber.fiberInclusion.obj a :=
  IsPreFibered.pullbackMap a.2 f

/-- The morphism from the base change of `a` along `f` to `a` is cartesian over `f`. -/
instance isCartesian_fiberPullbackHom (a : p.Fiber S) :
    p.IsCartesian f (fiberPullbackHom p f a) :=
  inferInstanceAs (p.IsCartesian f (IsPreFibered.pullbackMap a.2 f))

/-- **The base change of a morphism is the morphism induced on the chosen base changes**: it is
the unique morphism over the identity commuting with the two cartesian morphisms. -/
@[reassoc (attr := simp)]
theorem fiberPullback_map_fac {a b : p.Fiber S} (φ : a ⟶ b) :
    Fiber.fiberInclusion.map ((fiberPullback p f).map φ) ≫ fiberPullbackHom p f b =
      fiberPullbackHom p f a ≫ Fiber.fiberInclusion.map φ :=
  fiberPullbackMap_fac p f φ

section Comp

variable {T : 𝒮} (g : S ⟶ T)

/-- An iterated base change is cartesian over the composite: a composite of cartesian morphisms
of a fibred category is cartesian. -/
instance isCartesian_fiberPullbackHom_comp (a : p.Fiber T) :
    p.IsCartesian (f ≫ g)
      (fiberPullbackHom p f ((fiberPullback p g).obj a) ≫ fiberPullbackHom p g a) :=
  IsFibered.comp f g (fiberPullbackHom p f ((fiberPullback p g).obj a)) (fiberPullbackHom p g a)

/-- The comparison, at one object, of the iterated base change along `f` and `g` with the base
change along the composite: both are domains of cartesian morphisms over `f ≫ g` with the same
target. -/
def fiberPullbackCompIsoApp (a : p.Fiber T) :
    (fiberPullback p f).obj ((fiberPullback p g).obj a) ≅ (fiberPullback p (f ≫ g)).obj a :=
  fiberIsoMk p
    (IsCartesian.domainUniqueUpToIso p (f ≫ g) (fiberPullbackHom p (f ≫ g) a)
      (fiberPullbackHom p f ((fiberPullback p g).obj a) ≫ fiberPullbackHom p g a))
    (IsCartesian.domainUniqueUpToIso_inv_isHomLift p (f ≫ g) (fiberPullbackHom p (f ≫ g) a)
      (fiberPullbackHom p f ((fiberPullback p g).obj a) ≫ fiberPullbackHom p g a))

/-- The comparison of iterated base changes commutes with the cartesian morphisms. -/
@[reassoc (attr := simp)]
theorem fiberInclusion_map_fiberPullbackCompIsoApp_hom (a : p.Fiber T) :
    Fiber.fiberInclusion.map (fiberPullbackCompIsoApp p f g a).hom ≫
        fiberPullbackHom p (f ≫ g) a =
      fiberPullbackHom p f ((fiberPullback p g).obj a) ≫ fiberPullbackHom p g a :=
  IsCartesian.fac p (f ≫ g) (fiberPullbackHom p (f ≫ g) a) _

/-- **The comparison of an iterated base change with the base change along the composite.** -/
def fiberPullbackCompIso : fiberPullback p g ⋙ fiberPullback p f ≅ fiberPullback p (f ≫ g) :=
  NatIso.ofComponents (fun a ↦ fiberPullbackCompIsoApp p f g a)
    (fun {a b} φ ↦ Fiber.hom_ext (by
      simp only [Functor.map_comp, Functor.comp_map]
      refine IsCartesian.ext p (f ≫ g) (fiberPullbackHom p (f ≫ g) b) _ _ ?_
      simp))

end Comp

section Square

variable {U U' V V' : 𝒮} (i : U ⟶ U') (q : U ⟶ V) (r : U' ⟶ V') (w : V ⟶ V')
  (hsq : q ≫ w = i ≫ r)

/-- For a commutative square `q ≫ w = i ≫ r`, the comparison of the two ways of restricting the
fibre over `V'` to the fibre over `U`. -/
def fiberPullbackSquareIso :
    fiberPullback p w ⋙ fiberPullback p q ≅ fiberPullback p r ⋙ fiberPullback p i :=
  fiberPullbackCompIso p q w ≪≫ eqToIso (congrArg (fun k : U ⟶ V' ↦ fiberPullback p k) hsq) ≪≫
    (fiberPullbackCompIso p i r).symm

/-- **The comparison functor of a commutative square in the base.** It takes an object of the
fibre over `V'` to its two base changes to the fibres over `V` and over `U'`, together with the
canonical identification of their further base changes to the fibre over `U`. -/
def fiberSquareRestriction : p.Fiber V' ⥤ (fiberPullback p q) ⊡ (fiberPullback p i) :=
  (CatCommSqOver.toFunctorToCategoricalPullback (fiberPullback p q) (fiberPullback p i)
      (p.Fiber V')).obj
    ⟨fiberPullback p w, fiberPullback p r, fiberPullbackSquareIso p i q r w hsq⟩

/-- The first component of the comparison functor is the base change along `w`. -/
@[simp]
theorem fiberSquareRestriction_obj_fst (a : p.Fiber V') :
    ((fiberSquareRestriction p i q r w hsq).obj a).fst = (fiberPullback p w).obj a := rfl

/-- The second component of the comparison functor is the base change along `r`. -/
@[simp]
theorem fiberSquareRestriction_obj_snd (a : p.Fiber V') :
    ((fiberSquareRestriction p i q r w hsq).obj a).snd = (fiberPullback p r).obj a := rfl

/-- On morphisms, the first component of the comparison functor is the base change along `w`. -/
@[simp]
theorem fiberSquareRestriction_map_fst {a b : p.Fiber V'} (φ : a ⟶ b) :
    ((fiberSquareRestriction p i q r w hsq).map φ).fst = (fiberPullback p w).map φ := rfl

/-- On morphisms, the second component of the comparison functor is the base change along `r`. -/
@[simp]
theorem fiberSquareRestriction_map_snd {a b : p.Fiber V'} (φ : a ⟶ b) :
    ((fiberSquareRestriction p i q r w hsq).map φ).snd = (fiberPullback p r).map φ := rfl

end Square

end CategoryTheory.Functor

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u})

/-- Polarized families form a fibred category over the big fppf site: they form a category
fibred in groupoids, with no hypothesis. -/
instance polarizedProjection_isFibered : (polarizedProjection B).IsFibered :=
  polarizedProjection_isFiberedInGroupoids_unconditional.isFibered

/-- **Base change of polarized families on fibre categories.** Along a morphism `g : V ⟶ U` of
schemes of the big fppf site it takes a polarized family with base `U` to its base change with
base `V`. -/
def polarizedFiberPullback {V U : B.Schemes} (g : V ⟶ U) :
    (polarizedProjection B).Fiber U ⥤ (polarizedProjection B).Fiber V :=
  (polarizedProjection B).fiberPullback g

/-- The base change of a polarized family is the fibre product of total spaces with the
polarization pulled back, that is `AlgebraicGeometry.PolarizedFamily.stageBaseChange`: both carry
a cartesian morphism over the same morphism of bases, every morphism of polarized families being
cartesian over its base map. -/
def polarizedFiberPullbackObjIso (x : PolarizedFamily B) {V : B.Schemes} (g : V ⟶ x.base) :
    Functor.Fiber.fiberInclusion.obj
        ((polarizedFiberPullback B g).obj (Functor.Fiber.mk (p := polarizedProjection B) rfl)) ≅
      x.stageBaseChange g :=
  haveI _hlift : (polarizedProjection B).IsHomLift g (x.stageBaseChangeHom g) :=
    IsHomLift.map (polarizedProjection B) (x.stageBaseChangeHom g)
  have hcart : (polarizedProjection B).IsCartesian g (x.stageBaseChangeHom g) :=
    haveI := polarizedProjection_isFiberedInGroupoids_unconditional.isStronglyCartesian_homLift
      (p := polarizedProjection B) g (x.stageBaseChangeHom g)
    inferInstance
  have hchosen : (polarizedProjection B).IsCartesian g
      (Functor.fiberPullbackHom (polarizedProjection B) g
        (Functor.Fiber.mk (p := polarizedProjection B) rfl)) :=
    Functor.isCartesian_fiberPullbackHom (polarizedProjection B) g _
  @Functor.IsCartesian.domainUniqueUpToIso _ _ _ _ (polarizedProjection B) _ _ _ _ g
    (x.stageBaseChangeHom g) hcart _
    (Functor.fiberPullbackHom (polarizedProjection B) g
      (Functor.Fiber.mk (p := polarizedProjection B) rfl)) hchosen

/-- **Stacks 0D44.** For a commutative square `f ≫ h = i ≫ g` of schemes of the big fppf site,
the comparison functor from the polarized families with base `S'` to the 2-fibre product of those
with base `S` and those with base `T'` over those with base `T`. -/
@[stacks 0D44 "the functor of the comparison on fibre categories; that it is an equivalence is \
not proved here, Stacks 07RX being absent"]
def polarizedPushoutRestriction {T T' S S' : B.Schemes} (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S')
    (h : S ⟶ S') (hsq : f ≫ h = i ≫ g) :
    (polarizedProjection B).Fiber S' ⥤
      (polarizedFiberPullback B f) ⊡ (polarizedFiberPullback B i) :=
  (polarizedProjection B).fiberSquareRestriction i f g h hsq

end AlgebraicGeometry

end
