module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibrewiseEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stackification.RawLocalEquality
public import StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two clauses of Stacks 02ZN transport along an equivalence over the site

Let `(𝒞, J)` be a site, let `p : 𝒜 ⥤ 𝒞`, `p' : ℬ ⥤ 𝒞` and `q : 𝒳 ⥤ 𝒞` be fibred categories, let
`E : 𝒜 ⥤ ℬ` be a 1-morphism over `𝒞` which is an equivalence over `𝒞`, and let `K : ℬ ⥤ 𝒳` be a
1-morphism over `𝒞`. Then the two clauses of **Stacks 02ZN** for `K` — that the induced maps of
morphism presheaves are locally injective and locally surjective, and that every object of a
fibre of `q` is, along a covering sieve, in the essential image of `K` on fibres — hold for the
composite `E ⋙ K` out of `p`.

Both halves are formal. For the first, the maps of morphism presheaves compose
(`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap_comp`) and the one belonging to `E` is
a *bijection* over every object of the site over `U`: its component there is the fibre functor of
`E`, which is fully faithful because `E` is, conjugated by the comparison isomorphisms of the
chosen pullbacks. A locally injective map followed by a locally injective map is locally
injective, and likewise for local surjectivity, so no covering sieve has to be produced. For the
second, the fibre functor of a composite is the composite of the fibre functors, the fibre functor
of `E` is essentially surjective, and precomposing an essentially surjective functor does not
change an essential image, so the *same* covering sieve works.

This is what lets a presentation of a fibred category be replaced by an equivalent one before the
recognition criterion for a stackification is applied: Stacks 05YQ, for instance, proves the two
clauses for the pointwise groupoid fibration of free rank-`d` algebra structures, while the
criterion asks for them on the quotient prestack of the conjugation action groupoid, and the two
are equivalent over the site rather than equal.

## Main definitions

* `CategoryTheory.Functor.IsEquivalenceOver.toEquivalence`: the underlying equivalence of
  categories of an equivalence over the base.

## Main results

* `CategoryTheory.Functor.IsEquivalenceOver.full` and
  `CategoryTheory.Functor.IsEquivalenceOver.faithful`: an equivalence over the base is fully
  faithful.
* `CategoryTheory.Functor.essSurj_fiberFunctorOfCompEq_of_isEquivalenceOver`: it induces an
  essentially surjective functor on every fibre.
* `CategoryTheory.Functor.bijective_morPresheafMap_app_of_isEquivalenceOver`: the map of morphism
  presheaves it induces is bijective over every object of the site over `U`.
* `isLocallyInjective_and_isLocallySurjective_comp_of_isEquivalenceOver`, in the namespace
  `CategoryTheory.Functor.Stackification`: clause (1) of Stacks 02ZN transports.
* `CategoryTheory.Functor.Stackification.essImage_comp_of_isEquivalenceOver`: clause (2) of
  Stacks 02ZN transports.
* `isLocallyBijective_morPresheafMap_comp_of_isEquivalenceOver`, in the same namespace: the two
  together, in the shape the recognition criterion of Stacks 02ZN and 02ZP consumes.
* `isLocallyBijective_morPresheafMap_comp_of_equivalenceOver`: the same for the bundled
  `StacksRepresentableCFG.EquivalenceOver`, so that a caller holding either form can use it.

## Implementation notes

All three total categories are taken at one morphism universe `v`, because
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap` has one: its source and its target are
the morphism presheaves of the two categories, both valued in their morphism universe. The base's
morphism universe is free.

The hypothesis that `E` is an equivalence over the base is
`CategoryTheory.Functor.IsEquivalenceOver`, which does *not* carry `E ⋙ p' = p`; that equation
comes from the separate hypothesis that `E` is a 1-morphism over `𝒞`, as
`CategoryTheory.Functor.IsFibredOneMorphism.comp_eq`. The bundled
`StacksRepresentableCFG.EquivalenceOver` of the representability criterion carries both, and
`StacksRepresentableCFG.EquivalenceOver.toFunctorIsEquivalenceOver` together with
`StacksRepresentableCFG.EquivalenceOver.hom.w` turns one into the pair of hypotheses used here, so
a caller holding the bundled form can use these results unchanged.

The fibre functor of a 1-morphism over the base is named twice in the library, as
`CategoryTheory.Functor.fiberFunctorOfCompEq` and as `CategoryTheory.Functor.Fiber.mapOfComp`; the
two are definitionally equal, which is
`CategoryTheory.Functor.fiberFunctorOfCompEq_eq_mapOfComp`, and that is what carries the essential
surjectivity of `CategoryTheory.Functor.fiber_essSurj_of_isEquivalenceOver` to the first of them.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 02ZP](https://stacks.math.columbia.edu/tag/02ZP)
* [Stacks Project, Tag 042V](https://stacks.math.columbia.edu/tag/042V)
-/

@[expose] public section

namespace CategoryTheory.Functor

open CategoryTheory

universe vb v u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒜 : Type u₂} [Category.{v} 𝒜]
  {ℬ : Type u₃} [Category.{v} ℬ] {𝒳 : Type u₄} [Category.{v} 𝒳]
  {p : 𝒜 ⥤ 𝒞} {p' : ℬ ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} {E : 𝒜 ⥤ ℬ} {K : ℬ ⥤ 𝒳}

/-! ### An equivalence over the base is fully faithful -/

/-- **The underlying equivalence of categories of an equivalence over the base**, forgetting that
the quasi-inverse is again over the base and that the unit and the counit are vertical. The unit
is reoriented, `CategoryTheory.Functor.IsEquivalenceOver` stating it as `E ⋙ inv ≅ 𝟭`. -/
def IsEquivalenceOver.toEquivalence (hEeq : IsEquivalenceOver p p' E) : 𝒜 ≌ ℬ :=
  Equivalence.mk E hEeq.inv hEeq.unitIso.symm hEeq.counitIso

/-- An equivalence over the base is full. -/
theorem IsEquivalenceOver.full (hEeq : IsEquivalenceOver p p' E) : E.Full :=
  inferInstanceAs (hEeq.toEquivalence.functor.Full)

/-- An equivalence over the base is faithful. -/
theorem IsEquivalenceOver.faithful (hEeq : IsEquivalenceOver p p' E) : E.Faithful :=
  inferInstanceAs (hEeq.toEquivalence.functor.Faithful)

/-! ### The fibre functor of an equivalence over the base -/

/-- The two names the library gives the functor induced on a fibre by a 1-morphism over the base
agree. -/
theorem fiberFunctorOfCompEq_eq_mapOfComp (hE : E ⋙ p' = p) (U : 𝒞) :
    fiberFunctorOfCompEq hE U = Fiber.mapOfComp p p' E hE U := rfl

/-- **An equivalence over the base induces an essentially surjective functor on every fibre.** -/
@[sga "1 VI 4.2" "(i)"]
theorem essSurj_fiberFunctorOfCompEq_of_isEquivalenceOver (hE : E ⋙ p' = p)
    (hEeq : IsEquivalenceOver p p' E) (U : 𝒞) : (fiberFunctorOfCompEq hE U).EssSurj := by
  rw [fiberFunctorOfCompEq_eq_mapOfComp hE U]
  exact fiber_essSurj_of_isEquivalenceOver hE hEeq U

/-- **The functor induced on a fibre by a composite of 1-morphisms over the base is the composite
of the induced functors.** -/
theorem fiberFunctorOfCompEq_comp_eq [p.IsFibered] [p'.IsFibered] [q.IsFibered]
    (hE : p.IsFibredOneMorphism p' E) (hK : p'.IsFibredOneMorphism q K) (U : 𝒞) :
    fiberFunctorOfCompEq (hE.comp hK).comp_eq U =
      fiberFunctorOfCompEq hE.comp_eq U ⋙ fiberFunctorOfCompEq hK.comp_eq U := rfl

/-! ### The map of morphism presheaves of an equivalence over the base -/

/-- **The map of morphism presheaves induced by an equivalence over the base is bijective over
every object of the site over `U`.** Its component there is the fibre functor of the equivalence,
which is fully faithful, conjugated by the comparison isomorphisms of the chosen pullbacks, and
conjugation by isomorphisms is a bijection. -/
theorem bijective_morPresheafMap_app_of_isEquivalenceOver [p.IsFibered] [p'.IsFibered]
    (hE : p.IsFibredOneMorphism p' E) (hEeq : IsEquivalenceOver p p' E)
    {U : 𝒞} (a b : p.Fiber U) (g : (Over U)ᵒᵖ) :
    Function.Bijective ((hE.morPresheafMap a b).app g) := by
  set e := hE.mapPullbackFiberIso a g.unop.hom
  set e' := hE.mapPullbackFiberIso b g.unop.hom
  have he : ⇑((hE.morPresheafMap a b).app g) =
      (e.symm.homCongr e'.symm) ∘ (fiberFunctorOfCompEq hE.comp_eq g.unop.left).map := rfl
  rw [he]
  exact (e.symm.homCongr e'.symm).bijective.comp
    ((FullyFaithful.nonempty_iff_map_bijective _).mp
      (fullyFaithful_fiberFunctorOfCompEq hE.comp_eq hEeq.full hEeq.faithful g.unop.left) _ _)

namespace Stackification

variable [p.IsFibered] [p'.IsFibered] [q.IsFibered]

/-- **Clause (1) of Stacks 02ZN transports along an equivalence over the site on the source.** If
the maps of morphism presheaves induced by `K` are locally injective and locally surjective, then
so are those induced by `E ⋙ K`: the two maps compose, and the one induced by the equivalence is
bijective over every object, hence locally injective and locally surjective. -/
theorem isLocallyInjective_and_isLocallySurjective_comp_of_isEquivalenceOver
    (hE : p.IsFibredOneMorphism p' E) (hEeq : IsEquivalenceOver p p' E)
    (hK : p'.IsFibredOneMorphism q K) (J : GrothendieckTopology 𝒞)
    (hKmor : ∀ (U : 𝒞) (a b : p'.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hK.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over U) (hK.morPresheafMap a b))
    (U : 𝒞) (a b : p.Fiber U) :
    Presheaf.IsLocallyInjective (J.over U) ((hE.comp hK).morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) ((hE.comp hK).morPresheafMap a b) := by
  rw [← IsFibredOneMorphism.morPresheafMap_comp hE hK a b]
  have hbij := bijective_morPresheafMap_app_of_isEquivalenceOver hE hEeq a b
  have : Presheaf.IsLocallyInjective (J.over U) (hE.morPresheafMap a b) :=
    Presheaf.isLocallyInjective_of_injective _ _ fun g => (hbij g).1
  have : Presheaf.IsLocallySurjective (J.over U) (hE.morPresheafMap a b) :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun g => (hbij g).2
  obtain ⟨_, _⟩ := hKmor U ((fiberFunctorOfCompEq hE.comp_eq U).obj a)
    ((fiberFunctorOfCompEq hE.comp_eq U).obj b)
  exact ⟨inferInstance, inferInstance⟩

/-- **An object of a fibre lying in the essential image of `K` lies in the essential image of
`E ⋙ K`**, for `E` an equivalence over the site on the source. The fibre functor of `E ⋙ K` is
the fibre functor of `E` followed by that of `K`, the first is essentially surjective, and
precomposing an essentially surjective functor does not change an essential image.

This is clause (2) of Stacks 02ZN transported one object at a time, so that whatever covering
carries the clause for `K` carries it for `E ⋙ K` — a covering family as well as a covering
sieve. -/
theorem essImage_comp_apply_of_isEquivalenceOver
    (hE : p.IsFibredOneMorphism p' E) (hEeq : IsEquivalenceOver p p' E)
    (hK : p'.IsFibredOneMorphism q K) {V : 𝒞} {z : q.Fiber V}
    (h : (fiberFunctorOfCompEq hK.comp_eq V).essImage z) :
    (fiberFunctorOfCompEq (hE.comp hK).comp_eq V).essImage z := by
  have := essSurj_fiberFunctorOfCompEq_of_isEquivalenceOver hE.comp_eq hEeq V
  rw [fiberFunctorOfCompEq_comp_eq hE hK V]
  exact essImage_comp_apply_of_essSurj.mpr h

/-- **Clause (2) of Stacks 02ZN transports along an equivalence over the site on the source.** The
*same* covering sieve works, by
`CategoryTheory.Functor.Stackification.essImage_comp_apply_of_isEquivalenceOver` at each of its
arrows. -/
theorem essImage_comp_of_isEquivalenceOver
    (hE : p.IsFibredOneMorphism p' E) (hEeq : IsEquivalenceOver p p' E)
    (hK : p'.IsFibredOneMorphism q K) (J : GrothendieckTopology 𝒞)
    (hKobj : ∀ (U : 𝒞) (x : q.Fiber U), ∃ R ∈ J U,
      ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (fiberFunctorOfCompEq hK.comp_eq V).essImage (pullbackFiber q x f))
    (U : 𝒞) (x : q.Fiber U) :
    ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq (hE.comp hK).comp_eq V).essImage (pullbackFiber q x f) := by
  obtain ⟨R, hR, hmem⟩ := hKobj U x
  exact ⟨R, hR, fun V f hf =>
    essImage_comp_apply_of_isEquivalenceOver hE hEeq hK (hmem hf)⟩

/-- **The two clauses of Stacks 02ZN transport along an equivalence over the site on the source**,
in the shape the recognition criterion of Stacks 02ZN and 02ZP consumes: from the two clauses for
a 1-morphism `K` out of `p'` and an equivalence `E` over `𝒞` from `p` to `p'`, the two clauses for
`E ⋙ K` out of `p`. -/
theorem isLocallyBijective_morPresheafMap_comp_of_isEquivalenceOver
    (hE : p.IsFibredOneMorphism p' E) (hEeq : IsEquivalenceOver p p' E)
    (hK : p'.IsFibredOneMorphism q K) (J : GrothendieckTopology 𝒞)
    (hKmor : ∀ (U : 𝒞) (a b : p'.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hK.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over U) (hK.morPresheafMap a b))
    (hKobj : ∀ (U : 𝒞) (x : q.Fiber U), ∃ R ∈ J U,
      ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (fiberFunctorOfCompEq hK.comp_eq V).essImage (pullbackFiber q x f)) :
    (∀ (U : 𝒞) (a b : p.Fiber U),
        Presheaf.IsLocallyInjective (J.over U) ((hE.comp hK).morPresheafMap a b) ∧
          Presheaf.IsLocallySurjective (J.over U) ((hE.comp hK).morPresheafMap a b)) ∧
      (∀ (U : 𝒞) (x : q.Fiber U), ∃ R ∈ J U,
        ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
          (fiberFunctorOfCompEq (hE.comp hK).comp_eq V).essImage (pullbackFiber q x f)) :=
  ⟨isLocallyInjective_and_isLocallySurjective_comp_of_isEquivalenceOver hE hEeq hK J hKmor,
    essImage_comp_of_isEquivalenceOver hE hEeq hK J hKobj⟩

/-- **The two clauses of Stacks 02ZN transport along a bundled equivalence over the site**, the
same statement for the `StacksRepresentableCFG.EquivalenceOver` of the representability criterion.
That form carries the strict commutation of its forward functor with the structure functors, so
only preservation of strongly cartesian morphisms has to be supplied separately. -/
theorem isLocallyBijective_morPresheafMap_comp_of_equivalenceOver
    (e : StacksRepresentableCFG.EquivalenceOver p p')
    (hE : p.IsFibredOneMorphism p' e.hom.functor) (hK : p'.IsFibredOneMorphism q K)
    (J : GrothendieckTopology 𝒞)
    (hKmor : ∀ (U : 𝒞) (a b : p'.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hK.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over U) (hK.morPresheafMap a b))
    (hKobj : ∀ (U : 𝒞) (x : q.Fiber U), ∃ R ∈ J U,
      ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (fiberFunctorOfCompEq hK.comp_eq V).essImage (pullbackFiber q x f)) :
    (∀ (U : 𝒞) (a b : p.Fiber U),
        Presheaf.IsLocallyInjective (J.over U) ((hE.comp hK).morPresheafMap a b) ∧
          Presheaf.IsLocallySurjective (J.over U) ((hE.comp hK).morPresheafMap a b)) ∧
      (∀ (U : 𝒞) (x : q.Fiber U), ∃ R ∈ J U,
        ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
          (fiberFunctorOfCompEq (hE.comp hK).comp_eq V).essImage (pullbackFiber q x f)) :=
  isLocallyBijective_morPresheafMap_comp_of_isEquivalenceOver hE
    e.toFunctorIsEquivalenceOver hK J hKmor hKobj

end Stackification

end CategoryTheory.Functor

end
