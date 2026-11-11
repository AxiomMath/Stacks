module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationExtensions
public import StacksFrontier.CategoryTheory.Sites.Stackification.ExtensionFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Stackification.GroupoidStackification
public import StacksFrontier.CategoryTheory.Sites.Stackification.InducedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stackification.TransportAlongEquivalenceOver

/-!
# A 1-morphism inducing an equivalence of stackifications

Let `(𝒞, J)` be a site and let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids
over `𝒞`. Stacks 06WQ and 06WR take as hypothesis that *`f` induces an equivalence of
stackifications*: given stackifications `G_𝒳 : 𝒳 ⥤ 𝒳'` and `G_𝒴 : 𝒴 ⥤ 𝒴'` in the sense of
Stacks 02ZN, the 1-morphism `f' : 𝒳' ⥤ 𝒴'` that `f` induces, with its 2-isomorphism
`f ⋙ G_𝒴 ≅ G_𝒳 ⋙ f'`, is an equivalence over `𝒞`.

This file proves that this hypothesis implies the two local criteria of Stacks 02ZN for `f`
itself, `CategoryTheory.Functor.IsFibredOneMorphism.IsStackificationEquivalence'`, in which the
hom universe of the base is independent of the common hom universe of the total categories. This
is the form in which the proof of Stacks 06WR consumes it. Stackifications are
`CategoryTheory.Functor.IsFibredOneMorphism.IsStackification`, and the special case with base and
total categories at one hom universe,
`CategoryTheory.Functor.IsFibredOneMorphism.isStackificationEquivalence_of_isEquivalenceOver`, is
in `StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationInduced`; the lemmas it rests on,
in `StacksFrontier.CategoryTheory.Sites.Stackification.InducedEquivalence`, need that common
universe, so the argument is given again here at independent universes.

## Main results

All are in the namespace `CategoryTheory.Functor.IsFibredOneMorphism`.

* `isLocallyBijective_morPresheafMap_of_isEquivalenceOver'` and
  `exists_mem_essImage_pullbackFiber_of_isEquivalenceOver`: the two clauses of Stacks 02ZN for a
  1-morphism inducing an equivalence of stackifications.
* `isStackificationEquivalence'_of_isEquivalenceOver`:
  a 1-morphism of categories fibred in groupoids inducing an equivalence of stackifications
  satisfies the two local criteria of Stacks 02ZN.

## Implementation notes

The criteria for `f` are read off those for `f ⋙ G_𝒴`, which are those for `G_𝒳 ⋙ f'` carried
across the 2-isomorphism. The maps of morphism presheaves compose, the one induced by `f'` is
bijective, and a first factor of a locally bijective composite whose second factor `G_𝒴` is
locally injective is locally bijective. For objects, an object `y` of a fibre of `𝒴` has
`G_𝒴 y` isomorphic, locally, to `G_𝒴 (f x)`: the isomorphism lifts locally to a morphism of
fibres of `𝒴` by local surjectivity for `G_𝒴`, and it is invertible because the fibres of `𝒴`
are groupoids.

The stack condition on `𝒳'` and `𝒴'` is part of the hypothesis, as in the source, but the
argument does not use it.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 06WQ](https://stacks.math.columbia.edu/tag/06WQ)
* [Stacks Project, Tag 06WR](https://stacks.math.columbia.edu/tag/06WR)
-/

@[expose] public section

open CategoryTheory Opposite

universe vb v u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.Functor.IsFibredOneMorphism

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒳 : Type u₂} [Category.{v} 𝒳]
  {𝒴 : Type u₃} [Category.{v} 𝒴] {𝒳' : Type u₄} [Category.{v} 𝒳'] {𝒴' : Type u₅}
  [Category.{v} 𝒴'] {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {p' : 𝒳' ⥤ 𝒞} {q' : 𝒴' ⥤ 𝒞}
  [p.IsFibered] [q.IsFibered] [p'.IsFibered] [q'.IsFibered]

variable {J : GrothendieckTopology 𝒞} {f : 𝒳 ⥤ 𝒴} {GX : 𝒳 ⥤ 𝒳'} {GY : 𝒴 ⥤ 𝒴'} {f' : 𝒳' ⥤ 𝒴'}
  (hf : p.IsFibredOneMorphism q f) {hGX : p.IsFibredOneMorphism p' GX}
  {hGY : q.IsFibredOneMorphism q' GY} (hf' : p'.IsFibredOneMorphism q' f')
  (hf'eq : IsEquivalenceOver p' q' f') (α : f ⋙ GY ≅ GX ⋙ f')
  (hα : ∀ a : 𝒳, q'.IsHomLift (𝟙 (p.obj a)) (α.hom.app a))

include hf' hf'eq α hα in
/-- **Clause (1) of Stacks 02ZN for a 1-morphism inducing an equivalence of stackifications.** -/
theorem isLocallyBijective_morPresheafMap_of_isEquivalenceOver'
    (hGXs : hGX.IsStackification J) (hGYs : hGY.IsStackification J) (U : 𝒞) (x y : p.Fiber U) :
    Presheaf.IsLocallyInjective (J.over U) (hf.morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective (J.over U) (hf.morPresheafMap x y) := by
  obtain ⟨-, hGXmor, -⟩ := hGXs
  obtain ⟨-, hGYmor, -⟩ := hGYs
  have hK : ∀ (U : 𝒞) (a b : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) ((hGX.comp hf').morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over U) ((hGX.comp hf').morPresheafMap a b) := by
    intro U a b
    rw [← morPresheafMap_comp hGX hf' a b]
    have hbij := bijective_morPresheafMap_app_of_isEquivalenceOver hf' hf'eq
      ((fiberFunctorOfCompEq hGX.comp_eq U).obj a) ((fiberFunctorOfCompEq hGX.comp_eq U).obj b)
    have : Presheaf.IsLocallyInjective (J.over U) (hf'.morPresheafMap
        ((fiberFunctorOfCompEq hGX.comp_eq U).obj a)
        ((fiberFunctorOfCompEq hGX.comp_eq U).obj b)) :=
      Presheaf.isLocallyInjective_of_injective _ _ fun g => (hbij g).1
    have : Presheaf.IsLocallySurjective (J.over U) (hf'.morPresheafMap
        ((fiberFunctorOfCompEq hGX.comp_eq U).obj a)
        ((fiberFunctorOfCompEq hGX.comp_eq U).obj b)) :=
      Presheaf.isLocallySurjective_of_surjective _ _ fun g => (hbij g).2
    obtain ⟨_, _⟩ := hGXmor U a b
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨h₁, h₂⟩ := Stackification.isLocallyBijective_morPresheafMap_of_natIso hf hGY J
    (hGX.comp hf') α hα hK U x y
  rw [← morPresheafMap_comp hf hGY x y] at h₁ h₂
  obtain ⟨_, _⟩ := hGYmor U ((fiberFunctorOfCompEq hf.comp_eq U).obj x)
    ((fiberFunctorOfCompEq hf.comp_eq U).obj y)
  exact ⟨Presheaf.isLocallyInjective_of_isLocallyInjective _ _ (hGY.morPresheafMap _ _),
    Presheaf.isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective _ _
      (hGY.morPresheafMap _ _)⟩

include hf' hf'eq α hα in
/-- **Clause (2) of Stacks 02ZN for a 1-morphism inducing an equivalence of stackifications**, for
a target fibred in groupoids. -/
theorem exists_mem_essImage_pullbackFiber_of_isEquivalenceOver (hq : q.IsFiberedInGroupoids)
    (hGXs : hGX.IsStackification J) (hGYs : hGY.IsStackification J) (U : 𝒞) (y : q.Fiber U) :
    ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃k : V ⟶ U⦄, R.arrows k →
      (fiberFunctorOfCompEq hf.comp_eq V).essImage (pullbackFiber q y k) := by
  obtain ⟨-, -, hGXobj⟩ := hGXs
  obtain ⟨-, hGYmor, -⟩ := hGYs
  have := essSurj_fiberFunctorOfCompEq_of_isEquivalenceOver hf'.comp_eq hf'eq U
  let z := (fiberFunctorOfCompEq hGY.comp_eq U).obj y
  let x'' := (fiberFunctorOfCompEq hf'.comp_eq U).objPreimage z
  let e₀ : (fiberFunctorOfCompEq hf'.comp_eq U).obj x'' ≅ z :=
    (fiberFunctorOfCompEq hf'.comp_eq U).objObjPreimageIso z
  obtain ⟨R₁, hR₁, h₁⟩ := hGXobj U x''
  have hloc : ∀ ⦃V : 𝒞⦄ (k : V ⟶ U), R₁.arrows k → ∃ S ∈ J V, ∀ ⦃W : 𝒞⦄ ⦃c : W ⟶ V⦄,
      S.arrows c → (fiberFunctorOfCompEq hf.comp_eq W).essImage (pullbackFiber q y (c ≫ k)) := by
    intro V k hk
    obtain ⟨x, ⟨e₁⟩⟩ := h₁ hk
    let a := (fiberFunctorOfCompEq hf.comp_eq V).obj x
    let b := pullbackFiber q y k
    let μ : (fiberFunctorOfCompEq hGY.comp_eq V).obj a ⟶
        (fiberFunctorOfCompEq hGY.comp_eq V).obj b :=
      (natIsoFiber (hf.comp hGY) (hGX.comp hf') α hα x).hom ≫
        (fiberFunctorOfCompEq hf'.comp_eq V).map e₁.hom ≫ (hf'.mapPullbackFiberIso x'' k).inv ≫
        (pullbackFiberIso e₀ k).hom ≫ (hGY.mapPullbackFiberIso y k).hom
    have := (hGYmor V a b).2
    let σ := morSection q' ((fiberFunctorOfCompEq hGY.comp_eq V).obj a)
      ((fiberFunctorOfCompEq hGY.comp_eq V).obj b) μ
    have hSmem : Presheaf.imageSieve (hGY.morPresheafMap a b) σ ∈ (J.over V) (Over.mk (𝟙 V)) :=
      Presheaf.imageSieve_mem (J.over V) (hGY.morPresheafMap a b) σ
    refine ⟨Sieve.overEquiv (Over.mk (𝟙 V)) (Presheaf.imageSieve (hGY.morPresheafMap a b) σ),
      (J.mem_over_iff _).1 hSmem, fun W c hc => ?_⟩
    obtain ⟨n, -⟩ := mem_of_overEquiv hc
    let n' : pullbackFiber q a c ⟶ pullbackFiber q b c := n
    have : IsIso n' := (hq.fiber_isGroupoid W).all_isIso n'
    exact ⟨pullbackFiber p x c, ⟨(hf.mapPullbackFiberIso x c).symm ≪≫ asIso n' ≪≫
      pullbackFiberCompIso' y k c (c ≫ k) rfl⟩⟩
  choose S hS hS' using hloc
  refine ⟨Sieve.bind R₁.arrows S, J.bind_covering hR₁ hS, ?_⟩
  rintro W _ ⟨V, c, k, hk, hc, rfl⟩
  exact hS' k hk hc

include hf' hf'eq α hα in
/-- **A 1-morphism inducing an equivalence of stackifications satisfies the two local criteria of
Stacks 02ZN.** Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over `𝒞`, let
`G_𝒳 : 𝒳 ⥤ 𝒳'` and `G_𝒴 : 𝒴 ⥤ 𝒴'` be stackifications, and let `f' : 𝒳' ⥤ 𝒴'` be a 1-morphism
which is an equivalence over `𝒞`, with a vertical 2-isomorphism `f ⋙ G_𝒴 ≅ G_𝒳 ⋙ f'`. Then `f`
satisfies `CategoryTheory.Functor.IsFibredOneMorphism.IsStackificationEquivalence'`. -/
theorem isStackificationEquivalence'_of_isEquivalenceOver (hq : q.IsFiberedInGroupoids)
    (hGXs : hGX.IsStackification J) (hGYs : hGY.IsStackification J) :
    hf.IsStackificationEquivalence' J :=
  ⟨isLocallyBijective_morPresheafMap_of_isEquivalenceOver' hf hf' hf'eq α hα hGXs hGYs,
    exists_mem_essImage_pullbackFiber_of_isEquivalenceOver hf hf' hf'eq α hα hq hGXs hGYs⟩

end CategoryTheory.Functor.IsFibredOneMorphism

end
