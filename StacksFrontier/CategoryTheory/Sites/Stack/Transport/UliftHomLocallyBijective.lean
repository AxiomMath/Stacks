module

public import StacksFrontier.CategoryTheory.FiberedCategory.Amelioration
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveNatEquiv
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.UliftHomStack
public import StacksFrontier.CategoryTheory.Sites.Stackification.RawLocalEquality

/-!
# The two clauses of Stacks 02ZN across the morphism-universe lift

Let `K : 𝒜 ⥤ ℬ` be a 1-morphism of fibred categories over a site `(𝒞, J)`, with `𝒜` and `ℬ` in one
hom universe. Raising the morphism universes of both sides gives a 1-morphism
`K⁺ : ULiftHom 𝒜 ⥤ ULiftHom ℬ` over `𝒞`, and this file shows that `K⁺` satisfies the two clauses of
Stacks 02ZN as soon as `K` does.

This is what lets the determinacy clause of Stacks 02ZN be applied to a 1-morphism whose source and
target live one morphism universe below the one the explicit stackification works in: the
stackification raises the morphisms of its input, so a target offered to the criterion has to be
presented at the raised morphism universe too.

## Main definitions

* `CategoryTheory.Functor.uliftHomMap`: the morphism-universe lift of a functor.
* `CategoryTheory.Functor.IsFibredOneMorphism.morSectionEquiv`: for a *fully faithful* 1-morphism
  over `𝒞`, the bijection on sections of the morphism presheaves it induces.

## Main results

* `CategoryTheory.Functor.isFibredOneMorphism_uliftHomUp` and
  `CategoryTheory.Functor.isFibredOneMorphism_uliftHomDown`: raising and forgetting the morphism
  universe are 1-morphisms of fibred categories over `𝒞`.
* `CategoryTheory.Functor.isFibered_uliftHomProj_of_isFibered`: the lift of a fibred category is
  fibred.
* `CategoryTheory.Functor.IsFibredOneMorphism.uliftHom`: the lift of a 1-morphism is a 1-morphism.
* `CategoryTheory.Functor.IsFibredOneMorphism.isLocallyBijective_morPresheafMap_uliftHom`: clause
  (1) of Stacks 02ZN for the lift.
* `CategoryTheory.Functor.IsFibredOneMorphism.essImage_uliftHom`: clause (2) of Stacks 02ZN for the
  lift.

## Implementation notes

The morphism presheaves of `K⁺` take their values one universe above those of `K`, so they are not
objects of one functor category and there is no isomorphism of presheaves to transport the two
local conditions along. What there is instead is a family of bijections on *sections*, natural in
the object of `𝒞/U`, and `CategoryTheory.Presheaf.isLocallyInjective_of_natEquiv` and
`CategoryTheory.Presheaf.isLocallySurjective_of_natEquiv` transport the conditions along such a
family with no hypothesis relating the two universes.

That family is `CategoryTheory.Functor.IsFibredOneMorphism.morSectionEquiv`, which is
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap` with the hom universes of its two
total categories untied: the formula — conjugation of the fibre functor by the comparison
isomorphisms of the chosen pullbacks — makes sense across universes, and the map of presheaves does
not, so what can be recorded is the bijection on sections. Its naturality is
`CategoryTheory.Functor.IsFibredOneMorphism.morRestrict_mapPullbackFiberIso_conj`, which is already
stated for independent hom universes, and it is a bijection because a fully faithful 1-morphism
over `𝒞` induces a fully faithful functor on each fibre
(`CategoryTheory.Functor.fullyFaithful_fiberFunctorOfCompEq`). `CategoryTheory.BasedCategory` is
avoided throughout: `CategoryTheory.BasedCategory.Equivalence.morSectionEquiv` is the same
bijection for an equivalence over `𝒞`, but its statement goes through
`CategoryTheory.BasedCategory.ofFunctor`, and a term mixing that spelling of the lift with this one
is type-correct only after unfolding it.

The content is then the commuting square
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap_app_uliftHom`: the map of morphism
presheaves of `K⁺`, applied to a transported section, is the transport of the map of morphism
presheaves of `K` applied to the section. Both sides are conjugates by comparison isomorphisms of
chosen pullbacks, and after cancelling the section — which enters both sides through the same
morphism — the square reduces to the single identity
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_uliftHom_comm` between the
comparison isomorphisms of `K`, of `K⁺` and of the two lifts. That identity says that the two
factorizations of `K⁺ ∘ up = up ∘ K` give the same comparison isomorphism, and it is proved from
the universal property of a cartesian lift: both sides carry the image of the chosen cartesian lift
of `𝒜` to the chosen cartesian lift of `ULiftHom ℬ`.
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso_comp` is that statement for a
composite of 1-morphisms, but it is stated with the three total categories sharing one hom
universe, which is exactly what fails here: `𝒜` and `ULiftHom 𝒜` do not.

Clause (2) needs no universe-crossing transport. An essential image is a statement about objects
and isomorphisms of a fibre, the fibres of `r` and of its lift have the same objects, and their
isomorphisms correspond; the *same* covering sieve works, and the witness is carried over by the
fibre functor of the lift followed by the comparison isomorphism of the two chosen pullbacks.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 042V](https://stacks.math.columbia.edu/tag/042V)
-/

@[expose] public section

namespace CategoryTheory.Functor

open Opposite

universe v₁ u₁ v₂ u₂ u₃ v₃ v₄ u₄ v₅ u₅

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒜 : Type u₂} [Category.{v₂} 𝒜]
  {ℬ : Type u₃} [Category.{v₂} ℬ]

/-! ### Sections of the morphism presheaves of a 1-morphism, at independent hom universes -/

namespace IsFibredOneMorphism

section Comp

variable {𝒜' : Type u₄} [Category.{v₄} 𝒜'] {𝒜'' : Type u₅} [Category.{v₅} 𝒜'']
  {p : 𝒜 ⥤ 𝒞} {p' : 𝒜' ⥤ 𝒞} {p'' : 𝒜'' ⥤ 𝒞} {E : 𝒜 ⥤ 𝒜'} {F : 𝒜' ⥤ 𝒜''}
  [p.IsFibered] [p'.IsFibered] [p''.IsFibered]

/-- **The comparison isomorphisms of two 1-morphisms over `𝒞` compose to the comparison
isomorphism of the composite**, with the hom universes of the three total categories independent.

`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso_comp` is the same identity, with
those three universes tied to one another by its variable block; the morphism-universe lift puts a
category and its lift on two sides of the composite, so that form does not apply. The proof is the
same: both sides carry the image of the chosen cartesian lift to the chosen cartesian lift. -/
theorem mapPullbackFiberIso_comp' (hE : p.IsFibredOneMorphism p' E)
    (hF : p'.IsFibredOneMorphism p'' F) {U : 𝒞} (a : p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    ((hE.comp hF).mapPullbackFiberIso a f).hom =
      (hF.mapPullbackFiberIso ((fiberFunctorOfCompEq hE.comp_eq U).obj a) f).hom ≫
        (fiberFunctorOfCompEq hF.comp_eq V).map (hE.mapPullbackFiberIso a f).hom := by
  have hscE : p'.IsStronglyCartesian f (E.map (IsPreFibered.pullbackMap a.2 f)) :=
    hE.map_isStronglyCartesian f _ inferInstance
  have hscF : p''.IsStronglyCartesian f (F.map (E.map (IsPreFibered.pullbackMap a.2 f))) :=
    hF.map_isStronglyCartesian f _ hscE
  have h1 : Fiber.fiberInclusion.map ((hE.comp hF).mapPullbackFiberIso a f).hom ≫
      F.map (E.map (IsPreFibered.pullbackMap a.2 f)) =
      IsPreFibered.pullbackMap ((fiberFunctorOfCompEq (hE.comp hF).comp_eq U).obj a).2 f :=
    mapPullbackFiberIso_hom_fac (hE.comp hF) a f
  have h2 : (Fiber.fiberInclusion.map
        (hF.mapPullbackFiberIso ((fiberFunctorOfCompEq hE.comp_eq U).obj a) f).hom ≫
      F.map (Fiber.fiberInclusion.map (hE.mapPullbackFiberIso a f).hom)) ≫
      F.map (E.map (IsPreFibered.pullbackMap a.2 f)) =
      IsPreFibered.pullbackMap ((fiberFunctorOfCompEq (hE.comp hF).comp_eq U).obj a).2 f :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ Fiber.fiberInclusion.map
            (hF.mapPullbackFiberIso ((fiberFunctorOfCompEq hE.comp_eq U).obj a) f).hom ≫ z)
          ((F.map_comp _ _).symm.trans
            (congrArg F.map (mapPullbackFiberIso_hom_fac hE a f)))).trans
        (mapPullbackFiberIso_hom_fac hF ((fiberFunctorOfCompEq hE.comp_eq U).obj a) f))
  exact fiber_hom_ext_of_cartesian f (F.map (E.map (IsPreFibered.pullbackMap a.2 f)))
    inferInstance _ _ (h1.trans h2.symm)

/-- The inverse form of
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso_comp'`. -/
theorem mapPullbackFiberIso_comp_inv' (hE : p.IsFibredOneMorphism p' E)
    (hF : p'.IsFibredOneMorphism p'' F) {U : 𝒞} (a : p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    ((hE.comp hF).mapPullbackFiberIso a f).inv =
      (fiberFunctorOfCompEq hF.comp_eq V).map (hE.mapPullbackFiberIso a f).inv ≫
        (hF.mapPullbackFiberIso ((fiberFunctorOfCompEq hE.comp_eq U).obj a) f).inv :=
  congrArg Iso.inv (Iso.ext (mapPullbackFiberIso_comp' hE hF a f) :
    (hE.comp hF).mapPullbackFiberIso a f =
      hF.mapPullbackFiberIso ((fiberFunctorOfCompEq hE.comp_eq U).obj a) f ≪≫
        (fiberFunctorOfCompEq hF.comp_eq V).mapIso (hE.mapPullbackFiberIso a f))

omit [p.IsFibered] [p'.IsFibered] [p''.IsFibered] in
/-- The functor induced on a fibre by a composite of 1-morphisms over `𝒞` is the composite of the
induced functors, read on morphisms, with the three hom universes independent. -/
theorem fiberFunctorOfCompEq_comp_map' (hE : p.IsFibredOneMorphism p' E)
    (hF : p'.IsFibredOneMorphism p'' F) {V : 𝒞} {x y : p.Fiber V} (m : x ⟶ y) :
    (fiberFunctorOfCompEq (hE.comp hF).comp_eq V).map m =
      (fiberFunctorOfCompEq hF.comp_eq V).map ((fiberFunctorOfCompEq hE.comp_eq V).map m) :=
  Fiber.hom_ext rfl

end Comp

section Section

variable {𝒜' : Type u₄} [Category.{v₄} 𝒜'] {p : 𝒜 ⥤ 𝒞} {p' : 𝒜' ⥤ 𝒞} {E : 𝒜 ⥤ 𝒜'}
  [p.IsFibered] [p'.IsFibered]

/-- **The map of morphism presheaves of Stacks 042V, on sections.** A section of `Mor(a, b)` over
`g` is carried to a section of `Mor(E a, E b)` over `g` by the fibre functor of `E`, conjugated by
the comparison isomorphisms of the chosen pullbacks.

This is the component of `CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap` with the hom
universes of the two total categories untied. The map of presheaves exists only when they agree —
its source is valued in the hom universe of `𝒜` and its target in that of `𝒜'` — while the formula
makes sense always. -/
noncomputable def morSection (hE : p.IsFibredOneMorphism p' E) {U : 𝒞} (a b : p.Fiber U)
    (g : Over U)
    (m : pullbackFiber p a g.hom ⟶ pullbackFiber p b g.hom) :
    pullbackFiber p' ((fiberFunctorOfCompEq hE.comp_eq U).obj a) g.hom ⟶
      pullbackFiber p' ((fiberFunctorOfCompEq hE.comp_eq U).obj b) g.hom :=
  (hE.mapPullbackFiberIso a g.hom).hom ≫
    (fiberFunctorOfCompEq hE.comp_eq g.left).map m ≫ (hE.mapPullbackFiberIso b g.hom).inv

/-- `CategoryTheory.Functor.IsFibredOneMorphism.morSection` written out. -/
theorem morSection_eq (hE : p.IsFibredOneMorphism p' E) {U : 𝒞} (a b : p.Fiber U) (g : Over U)
    (m : pullbackFiber p a g.hom ⟶ pullbackFiber p b g.hom) :
    hE.morSection a b g m = (hE.mapPullbackFiberIso a g.hom).hom ≫
      (fiberFunctorOfCompEq hE.comp_eq g.left).map m ≫
      (hE.mapPullbackFiberIso b g.hom).inv := rfl

/-- **Stacks 042V, as the naturality of
`CategoryTheory.Functor.IsFibredOneMorphism.morSection`**: restricting a section along an arrow of
`𝒞/U` and then transporting it is transporting it and then restricting. -/
theorem morSection_naturality (hE : p.IsFibredOneMorphism p' E) {U : 𝒞} (a b : p.Fiber U)
    {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : pullbackFiber p a g₂.hom ⟶ pullbackFiber p b g₂.hom) :
    hE.morSection a b g₁ (morRestrict p a b h m) =
      morRestrict p' ((fiberFunctorOfCompEq hE.comp_eq U).obj a)
        ((fiberFunctorOfCompEq hE.comp_eq U).obj b) h (hE.morSection a b g₂ m) :=
  hE.morRestrict_mapPullbackFiberIso_conj a b h m

/-- **`CategoryTheory.Functor.IsFibredOneMorphism.morSection` is a bijection for a fully faithful
1-morphism over `𝒞`**, since such a 1-morphism induces a fully faithful functor on each fibre and
conjugation by isomorphisms is a bijection. -/
noncomputable def morSectionEquiv (hE : p.IsFibredOneMorphism p' E) (hfull : E.Full)
    (hfaith : E.Faithful) {U : 𝒞} (a b : p.Fiber U) (g : Over U) :
    (pullbackFiber p a g.hom ⟶ pullbackFiber p b g.hom) ≃
      (pullbackFiber p' ((fiberFunctorOfCompEq hE.comp_eq U).obj a) g.hom ⟶
        pullbackFiber p' ((fiberFunctorOfCompEq hE.comp_eq U).obj b) g.hom) :=
  Equiv.ofBijective (hE.morSection a b g)
    (((hE.mapPullbackFiberIso a g.hom).symm.homCongr
        (hE.mapPullbackFiberIso b g.hom).symm).bijective.comp
      ((FullyFaithful.nonempty_iff_map_bijective _).mp
        (fullyFaithful_fiberFunctorOfCompEq hE.comp_eq hfull hfaith g.left) _ _))

/-- `CategoryTheory.Functor.IsFibredOneMorphism.morSectionEquiv` is
`CategoryTheory.Functor.IsFibredOneMorphism.morSection`. -/
theorem morSectionEquiv_apply (hE : p.IsFibredOneMorphism p' E) (hfull : E.Full)
    (hfaith : E.Faithful) {U : 𝒞} (a b : p.Fiber U) (g : Over U)
    (m : pullbackFiber p a g.hom ⟶ pullbackFiber p b g.hom) :
    hE.morSectionEquiv hfull hfaith a b g m = hE.morSection a b g m := rfl

end Section

section SharedHomUniverse

variable {ℬ₀ : Type u₄} [Category.{v₂} ℬ₀] {p : 𝒜 ⥤ 𝒞} {r₀ : ℬ₀ ⥤ 𝒞} {F₀ : 𝒜 ⥤ ℬ₀}
  [p.IsFibered] [r₀.IsFibered]

/-- The components of `CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap` are
`CategoryTheory.Functor.IsFibredOneMorphism.morSection`. -/
theorem morPresheafMap_app_eq_morSection (hF : p.IsFibredOneMorphism r₀ F₀) {U : 𝒞}
    (a b : p.Fiber U) (g : (Over U)ᵒᵖ) (m : (morPresheaf p a b).obj g) :
    (hF.morPresheafMap a b).app g m = hF.morSection a b g.unop m := rfl

end SharedHomUniverse

section CompSection

variable {𝒜' : Type u₄} [Category.{v₄} 𝒜'] {𝒜'' : Type u₅} [Category.{v₅} 𝒜'']
  {p : 𝒜 ⥤ 𝒞} {p' : 𝒜' ⥤ 𝒞} {p'' : 𝒜'' ⥤ 𝒞} {E : 𝒜 ⥤ 𝒜'} {F : 𝒜' ⥤ 𝒜''}
  [p.IsFibered] [p'.IsFibered] [p''.IsFibered]

/-- **The maps on sections of two 1-morphisms over `𝒞` compose**, with the hom universes of the
three total categories independent. This is
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap_comp` on sections. -/
theorem morSection_comp (hE : p.IsFibredOneMorphism p' E) (hF : p'.IsFibredOneMorphism p'' F)
    {U : 𝒞} (a b : p.Fiber U) (g : Over U)
    (m : pullbackFiber p a g.hom ⟶ pullbackFiber p b g.hom) :
    hF.morSection ((fiberFunctorOfCompEq hE.comp_eq U).obj a)
        ((fiberFunctorOfCompEq hE.comp_eq U).obj b) g (hE.morSection a b g m) =
      (hE.comp hF).morSection a b g m := by
  simp only [morSection_eq, mapPullbackFiberIso_comp' hE hF a g.hom,
    mapPullbackFiberIso_comp_inv' hE hF b g.hom, fiberFunctorOfCompEq_comp_map' hE hF m,
    Functor.map_comp, Category.assoc]

end CompSection

end IsFibredOneMorphism

/-! ### Raising the morphism universe, as a 1-morphism of fibred categories -/

/-- Raising the morphism universe is a full functor: a lifted morphism is the lift of its own
underlying morphism. -/
theorem full_uliftHomUp : (ULiftHom.up : 𝒜 ⥤ ULiftHom.{v₃} 𝒜).Full where
  map_surjective := fun {_ _} f ↦ ⟨f.down, rfl⟩

/-- Raising the morphism universe is a faithful functor. -/
theorem faithful_uliftHomUp : (ULiftHom.up : 𝒜 ⥤ ULiftHom.{v₃} 𝒜).Faithful where
  map_injective := fun {_ _ _ _} h ↦ congrArg ULift.down h

/-- **Raising the morphism universe is a 1-morphism of fibred categories over `𝒞`**: it is strictly
over `𝒞`, and it preserves strongly cartesian morphisms because it is the forward functor of an
equivalence of categories under which the two structure functors correspond. -/
theorem isFibredOneMorphism_uliftHomUp (p : 𝒜 ⥤ 𝒞) :
    p.IsFibredOneMorphism (uliftHomProj p : ULiftHom.{v₃} 𝒜 ⥤ 𝒞)
      (ULiftHom.up : 𝒜 ⥤ ULiftHom.{v₃} 𝒜) :=
  ⟨rfl, fun {_ _} f {_ _} φ hφ ↦
    (ULiftHom.equiv (C := 𝒜)).isStronglyCartesian_map_functor
      (uliftHomProj p : ULiftHom.{v₃} 𝒜 ⥤ 𝒞) rfl f φ hφ⟩

/-- **Forgetting the morphism-universe lift is a 1-morphism of fibred categories over `𝒞`**: it is
the inverse functor of that same equivalence. -/
theorem isFibredOneMorphism_uliftHomDown (p : 𝒜 ⥤ 𝒞) :
    (uliftHomProj p : ULiftHom.{v₃} 𝒜 ⥤ 𝒞).IsFibredOneMorphism p
      (ULiftHom.down : ULiftHom.{v₃} 𝒜 ⥤ 𝒜) :=
  ⟨rfl, fun {_ _} f {_ _} φ hφ ↦
    (ULiftHom.equiv (C := 𝒜)).symm.isStronglyCartesian_map_functor p rfl f φ hφ⟩

/-- **The morphism-universe lift of a fibred category over `𝒞` is fibred.** This is the lifting
equivalence together with Stacks 042X; it is an instance because every statement about the chosen
pullbacks of the lift needs it, and because the criterion of Stacks 02ZN takes the fibredness of
its target as an instance argument, so the clauses fed to it have to be about the same one. -/
instance isFibered_uliftHomProj_of_isFibered (p : 𝒜 ⥤ 𝒞) [p.IsFibered] :
    (uliftHomProj p : ULiftHom.{v₃} 𝒜 ⥤ 𝒞).IsFibered :=
  (uliftHomBasedEquivalence p).isFibered ‹p.IsFibered›

/-- The morphism-universe lift of a functor: the same action on objects and on morphisms, read
between the lifted categories. -/
abbrev uliftHomMap (K : 𝒜 ⥤ ℬ) : ULiftHom.{v₃} 𝒜 ⥤ ULiftHom.{v₃} ℬ :=
  (ULiftHom.down : ULiftHom.{v₃} 𝒜 ⥤ 𝒜) ⋙ K ⋙ (ULiftHom.up : ℬ ⥤ ULiftHom.{v₃} ℬ)

namespace IsFibredOneMorphism

variable {p : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {K : 𝒜 ⥤ ℬ}

/-- **The morphism-universe lift of a 1-morphism of fibred categories over `𝒞` is again one**: it
is the composite of forgetting the lift, the given 1-morphism, and taking the lift. -/
theorem uliftHom (hK : p.IsFibredOneMorphism r K) :
    (uliftHomProj p : ULiftHom.{v₃} 𝒜 ⥤ 𝒞).IsFibredOneMorphism
      (uliftHomProj r : ULiftHom.{v₃} ℬ ⥤ 𝒞)
      (uliftHomMap K : ULiftHom.{v₃} 𝒜 ⥤ ULiftHom.{v₃} ℬ) :=
  (isFibredOneMorphism_uliftHomDown p).comp (hK.comp (isFibredOneMorphism_uliftHomUp r))

/-- **The fibre functor of the morphism-universe lift is surjective on objects**: an object of a
fibre of the lift is the lift of an object of the fibre, the two fibres having the same underlying
objects. -/
theorem surjective_fiberFunctorOfCompEq_uliftHomUp_obj (p : 𝒜 ⥤ 𝒞) (U : 𝒞) :
    Function.Surjective
      (fiberFunctorOfCompEq (isFibredOneMorphism_uliftHomUp p).comp_eq U).obj :=
  fun x ↦ ⟨⟨ULiftHom.objDown x.1, x.2⟩, Subtype.ext rfl⟩

/-- The two factorizations of `K⁺ ∘ up = up ∘ K` induce the same map on the objects of a fibre. -/
theorem fiberFunctorOfCompEq_uliftHom_obj (hK : p.IsFibredOneMorphism r K) (U : 𝒞)
    (a : p.Fiber U) :
    (fiberFunctorOfCompEq hK.uliftHom.comp_eq U).obj
        ((fiberFunctorOfCompEq (isFibredOneMorphism_uliftHomUp p).comp_eq U).obj a) =
      (fiberFunctorOfCompEq (isFibredOneMorphism_uliftHomUp r).comp_eq U).obj
        ((fiberFunctorOfCompEq hK.comp_eq U).obj a) := rfl

variable [hp : p.IsFibered] [hr : r.IsFibered]
  [hp' : (uliftHomProj p : ULiftHom.{v₃} 𝒜 ⥤ 𝒞).IsFibered]
  [hr' : (uliftHomProj r : ULiftHom.{v₃} ℬ ⥤ 𝒞).IsFibered]

include hp hr hp' hr'

/-! ### Clause (1) of Stacks 02ZN for the lift -/

/-- **The commuting square for the morphism-universe lift.** Transporting a section along the lift
of the source and then applying the map on sections of the lift of `K` is applying the map on
sections of `K` and then transporting along the lift of the target.

The two composites of 1-morphisms are the two factorizations of `K⁺ ∘ up = up ∘ K`, so this is
`CategoryTheory.Functor.IsFibredOneMorphism.morSection_comp` applied twice. -/
theorem morSection_uliftHom_comm (hK : p.IsFibredOneMorphism r K) {U : 𝒞} (a b : p.Fiber U)
    (g : Over U) (m : pullbackFiber p a g.hom ⟶ pullbackFiber p b g.hom) :
    hK.uliftHom.morSection
        ((fiberFunctorOfCompEq (isFibredOneMorphism_uliftHomUp p).comp_eq U).obj a)
        ((fiberFunctorOfCompEq (isFibredOneMorphism_uliftHomUp p).comp_eq U).obj b) g
        ((isFibredOneMorphism_uliftHomUp p).morSection a b g m) =
      (isFibredOneMorphism_uliftHomUp r).morSection
        ((fiberFunctorOfCompEq hK.comp_eq U).obj a) ((fiberFunctorOfCompEq hK.comp_eq U).obj b) g
        (hK.morSection a b g m) :=
  (morSection_comp (isFibredOneMorphism_uliftHomUp p) hK.uliftHom a b g m).trans
    (morSection_comp hK (isFibredOneMorphism_uliftHomUp r) a b g m).symm

/-- **Clause (1) of Stacks 02ZN transports to the morphism-universe lift**: if the maps of morphism
presheaves induced by `K` are locally injective and locally surjective, then so are those induced
by its lift. The two families of presheaves take their values in different `Type` universes, so the
transport is along the bijections on sections of the two lifts. -/
theorem isLocallyBijective_morPresheafMap_uliftHom (hK : p.IsFibredOneMorphism r K)
    (J : GrothendieckTopology 𝒞)
    (hKmor : ∀ (U : 𝒞) (a b : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hK.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over U) (hK.morPresheafMap a b))
    (U : 𝒞) (a b : (uliftHomProj p : ULiftHom.{v₃} 𝒜 ⥤ 𝒞).Fiber U) :
    Presheaf.IsLocallyInjective (J.over U) (hK.uliftHom.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) (hK.uliftHom.morPresheafMap a b) := by
  obtain ⟨a, rfl⟩ := surjective_fiberFunctorOfCompEq_uliftHomUp_obj p U a
  obtain ⟨b, rfl⟩ := surjective_fiberFunctorOfCompEq_uliftHomUp_obj p U b
  obtain ⟨_, _⟩ := hKmor U a b
  let α := fun X : (Over U)ᵒᵖ ↦ (isFibredOneMorphism_uliftHomUp p).morSectionEquiv
    full_uliftHomUp faithful_uliftHomUp a b X.unop
  let β := fun X : (Over U)ᵒᵖ ↦ (isFibredOneMorphism_uliftHomUp r).morSectionEquiv
    full_uliftHomUp faithful_uliftHomUp ((fiberFunctorOfCompEq hK.comp_eq U).obj a)
      ((fiberFunctorOfCompEq hK.comp_eq U).obj b) X.unop
  have hsq := fun (X : (Over U)ᵒᵖ) ↦ hK.morSection_uliftHom_comm a b X.unop
  exact ⟨Presheaf.isLocallyInjective_of_natEquiv (J.over U) (hK.morPresheafMap a b) _ α β
      (fun h ↦ (isFibredOneMorphism_uliftHomUp p).morSection_naturality a b h.unop) hsq,
    Presheaf.isLocallySurjective_of_natEquiv (J.over U) (hK.morPresheafMap a b) _ α β
      (fun h ↦ (isFibredOneMorphism_uliftHomUp r).morSection_naturality _ _ h.unop) hsq⟩

/-! ### Clause (2) of Stacks 02ZN for the lift -/

omit hp hp' in
/-- **An object of a fibre in the essential image of `K` has its lift in the essential image of
`K⁺`.** The fibres of a category over `𝒞` and of its lift have the same objects and corresponding
isomorphisms, so a witness downstairs is carried up by the fibre functor of the lift, composed
with the comparison isomorphism of the two chosen pullbacks.

This is clause (2) of Stacks 02ZN transported one arrow at a time, so that whatever covering
carries the clause downstairs carries it upstairs — a covering family as well as a covering
sieve. -/
theorem essImage_uliftHom_pullbackFiber (hK : p.IsFibredOneMorphism r K) {U V : 𝒞} (f : V ⟶ U)
    (x : r.Fiber U)
    (h : (fiberFunctorOfCompEq hK.comp_eq V).essImage (pullbackFiber r x f)) :
    (fiberFunctorOfCompEq hK.uliftHom.comp_eq V).essImage
      (pullbackFiber (uliftHomProj r : ULiftHom.{v₃} ℬ ⥤ 𝒞)
        ((fiberFunctorOfCompEq (isFibredOneMorphism_uliftHomUp r).comp_eq U).obj x) f) := by
  obtain ⟨c, ⟨ψ⟩⟩ := h
  refine ⟨(fiberFunctorOfCompEq (isFibredOneMorphism_uliftHomUp p).comp_eq V).obj c, ⟨?_⟩⟩
  exact eqToIso (fiberFunctorOfCompEq_uliftHom_obj hK V c) ≪≫
    Functor.mapIso (fiberFunctorOfCompEq (isFibredOneMorphism_uliftHomUp r).comp_eq V) ψ ≪≫
    ((isFibredOneMorphism_uliftHomUp r).mapPullbackFiberIso x f).symm

omit hp hp' in
/-- **Clause (2) of Stacks 02ZN transports to the morphism-universe lift**, with the *same*
covering sieve, by
`CategoryTheory.Functor.IsFibredOneMorphism.essImage_uliftHom_pullbackFiber` at each of its
arrows. -/
theorem essImage_uliftHom (hK : p.IsFibredOneMorphism r K) (J : GrothendieckTopology 𝒞)
    (hKobj : ∀ (U : 𝒞) (x : r.Fiber U), ∃ R ∈ J U,
      ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (fiberFunctorOfCompEq hK.comp_eq V).essImage (pullbackFiber r x f))
    (U : 𝒞) (x : (uliftHomProj r : ULiftHom.{v₃} ℬ ⥤ 𝒞).Fiber U) :
    ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hK.uliftHom.comp_eq V).essImage
        (pullbackFiber (uliftHomProj r : ULiftHom.{v₃} ℬ ⥤ 𝒞) x f) := by
  obtain ⟨x, rfl⟩ := surjective_fiberFunctorOfCompEq_uliftHomUp_obj r U x
  obtain ⟨R, hR, hmem⟩ := hKobj U x
  exact ⟨R, hR, fun V f hf ↦ essImage_uliftHom_pullbackFiber hK f x (hmem hf)⟩

end IsFibredOneMorphism

end CategoryTheory.Functor

end
