module

public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap

/-!
# Naming the fibrewise data of a 1-morphism of fibred categories

The fibre `CategoryTheory.Functor.Fiber` of a functor carries its category structure through the
instance argument of the functor, so an isomorphism of fibre objects, and the clause of
Stacks 02ZN about objects being locally in an essential image on fibres, both mention that
instance. Where the functor is built from several layers — a localization of a comma category, or
a stackification over a big site — the instance is no longer found by synthesis at the point where
such a statement is written down, although it is found once and for all here.

This file therefore names the fibrewise data, for a generic 1-morphism of fibred categories over
a generic base. A statement about a concrete 1-morphism is then an *application* of one of these
names, so the instance is instantiated rather than synthesised. The two names that mention the
instance are kept semireducible for that reason, and come with the constructor and the destructor
that a consumer needs in their place.

## Main definitions

* `CategoryTheory.Functor.FiberIso`: an isomorphism of two objects of a fibre, with
  `CategoryTheory.Functor.FiberIso.mk'`, `CategoryTheory.Functor.FiberIso.iso`,
  `CategoryTheory.Functor.FiberIso.ofEq`, `CategoryTheory.Functor.FiberIso.symm`,
  `CategoryTheory.Functor.FiberIso.trans`, `CategoryTheory.Functor.FiberIso.pullback` and
  `CategoryTheory.Functor.FiberIso.pullbackComp`.
* `CategoryTheory.Functor.fiberMapObj`: the image of an object of a fibre under the functor induced
  on fibres by a 1-morphism of fibred categories, with
  `CategoryTheory.Functor.fiberMapObj_val` for its underlying object.
* `CategoryTheory.Functor.IsLocallyEssImageOnFibers`: **clause (2) of Stacks 02ZN** — every object
  of a fibre of the target is, along a covering sieve of the base, in the essential image of the
  functor induced on fibres; with `CategoryTheory.Functor.IsLocallyEssImageOnFibers.mk'` and
  `CategoryTheory.Functor.IsLocallyEssImageOnFibers.out`.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 02XY](https://stacks.math.columbia.edu/tag/02XY)
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮]

/-- **An isomorphism of two objects of a fibre.** -/
def FiberIso {p : 𝒳 ⥤ 𝒞} {U : 𝒞} (a b : p.Fiber U) : Type v₂ := a ≅ b

/-- An isomorphism of the underlying objects lying over an identity is an isomorphism of the
fibre. -/
def FiberIso.mk' {p : 𝒳 ⥤ 𝒞} {U : 𝒞} {a b : p.Fiber U} (e : a.1 ≅ b.1)
    (he : p.IsHomLift (𝟙 U) e.hom) : FiberIso a b :=
  Fiber.isoMk e he

/-- An isomorphism of the fibre, read as such. -/
def FiberIso.iso {p : 𝒳 ⥤ 𝒞} {U : 𝒞} {a b : p.Fiber U} (e : FiberIso a b) : a ≅ b := e

/-- An equality of objects of a fibre is an isomorphism of the fibre. -/
def FiberIso.ofEq {p : 𝒳 ⥤ 𝒞} {U : 𝒞} {a b : p.Fiber U} (hab : a = b) : FiberIso a b :=
  eqToIso hab

/-- The inverse of an isomorphism of a fibre. -/
def FiberIso.symm {p : 𝒳 ⥤ 𝒞} {U : 𝒞} {a b : p.Fiber U} (e : FiberIso a b) : FiberIso b a :=
  e.iso.symm

/-- The composition of two isomorphisms of a fibre. -/
def FiberIso.trans {p : 𝒳 ⥤ 𝒞} {U : 𝒞} {a b c : p.Fiber U} (e : FiberIso a b)
    (f : FiberIso b c) : FiberIso a c :=
  e.iso ≪≫ f.iso

/-- The chosen pullback of an isomorphism of a fibre. -/
noncomputable def FiberIso.pullback {p : 𝒳 ⥤ 𝒞} (hp : p.IsFibered) {U : 𝒞} {a b : p.Fiber U}
    (e : FiberIso a b) {V : 𝒞} (f : V ⟶ U) :
    letI := hp
    FiberIso (pullbackFiber p a f) (pullbackFiber p b f) :=
  letI := hp
  pullbackFiberIso e.iso f

/-- The chosen pullback along a composite agrees with the iterated chosen pullback. -/
noncomputable def FiberIso.pullbackComp {p : 𝒳 ⥤ 𝒞} (hp : p.IsFibered) {U : 𝒞} (a : p.Fiber U)
    {V Z : 𝒞} (f : V ⟶ U) (g : Z ⟶ V) :
    letI := hp
    FiberIso (pullbackFiber p (pullbackFiber p a f) g) (pullbackFiber p a (g ≫ f)) :=
  letI := hp
  pullbackFiberCompIso a f g

/-- **The image of an object of a fibre** under the functor a 1-morphism of fibred categories
induces on fibres. -/
abbrev fiberMapObj {p : 𝒳 ⥤ 𝒞} {r : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} (hF : F ⋙ r = p) (U : 𝒞)
    (z : p.Fiber U) : r.Fiber U :=
  (fiberFunctorOfCompEq hF U).obj z

/-- The underlying object of the image of an object of a fibre. -/
@[simp]
theorem fiberMapObj_val {p : 𝒳 ⥤ 𝒞} {r : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} (hF : F ⋙ r = p) (U : 𝒞)
    (z : p.Fiber U) : (fiberMapObj hF U z).1 = F.obj z.1 := rfl

/-- **Clause (2) of Stacks 02ZN.** Every object of a fibre of the target is, along a covering
sieve of the base, in the essential image of the functor induced on fibres. -/
def IsLocallyEssImageOnFibers {p : 𝒳 ⥤ 𝒞} {r : 𝒮 ⥤ 𝒞} (hr : r.IsPreFibered) {F : 𝒳 ⥤ 𝒮}
    (hF : F ⋙ r = p) (J : GrothendieckTopology 𝒞) : Prop :=
  letI := hr
  ∀ (U : 𝒞) (x : r.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
    (fiberFunctorOfCompEq hF V).essImage (pullbackFiber r x f)

/-- Clause (2) of Stacks 02ZN holds as soon as it holds at every object of every fibre. -/
theorem IsLocallyEssImageOnFibers.mk' {p : 𝒳 ⥤ 𝒞} {r : 𝒮 ⥤ 𝒞} {hr : r.IsPreFibered}
    {F : 𝒳 ⥤ 𝒮} {hF : F ⋙ r = p} {J : GrothendieckTopology 𝒞}
    (hyp : letI := hr
      ∀ (U : 𝒞) (x : r.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (fiberFunctorOfCompEq hF V).essImage (pullbackFiber r x f)) :
    IsLocallyEssImageOnFibers hr hF J := hyp

/-- Clause (2) of Stacks 02ZN, read at every object of every fibre. -/
theorem IsLocallyEssImageOnFibers.out {p : 𝒳 ⥤ 𝒞} {r : 𝒮 ⥤ 𝒞} {hr : r.IsPreFibered}
    {F : 𝒳 ⥤ 𝒮} {hF : F ⋙ r = p} {J : GrothendieckTopology 𝒞}
    (hyp : IsLocallyEssImageOnFibers hr hF J) :
    letI := hr
    ∀ (U : 𝒞) (x : r.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hF V).essImage (pullbackFiber r x f) := hyp

end CategoryTheory.Functor

end
