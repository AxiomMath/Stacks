module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyFunctor

/-!
# The unit of the extension of Stacks 0435, read on a fibre

Let `G : 𝒮 ⥤ 𝒮'` and `F : 𝒮 ⥤ 𝒳` be 1-morphisms of fibred categories over a site `(𝒞, J)`
satisfying the hypotheses of Stacks 0435, and let `H = extend` be the extension of `F` along `G`.
The 2-isomorphism `CategoryTheory.Functor.Stackification.unit : G ⋙ H ≅ F` has vertical
components (`CategoryTheory.Functor.Stackification.isHomLift_id_unitHom`), so over every object
of `𝒞` it induces an isomorphism between the values of the two induced functors on fibres. This
file records that, and the one consequence needed: an object of a fibre of `𝒳` in the essential
image of `F` on fibres is in the essential image of `G ⋙ H` there.

## Main definitions

* `CategoryTheory.Functor.Stackification.extendFiberUnitIso`: the component of the
  2-isomorphism read in the fibre.

## Main results

* `CategoryTheory.Functor.Stackification.essImage_extend_comp_of_essImage`: the essential image
  of `F` on a fibre is contained in that of `G ⋙ H`.

## Implementation notes

Nothing here is about the construction of `H`; only that its unit is a vertical isomorphism. The
fibre object is destructured as `⟨A, rfl⟩`, which replaces the object of `𝒞` by the image of `A`:
`CategoryTheory.Functor.Stackification.isHomLift_id_unitHom` is stated over `𝟙 (p.obj A)`, and
`CategoryTheory.Functor.Fiber.isoMk` asks for an isomorphism over the identity of the object the
fibre is taken at.

## References

* [Stacks 0435](https://stacks.math.columbia.edu/tag/0435).
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
-/

@[expose] public section

namespace CategoryTheory.Functor.Stackification

open CategoryTheory

universe vb v v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒮 : Type u₂} [Category.{v} 𝒮] {𝒮' : Type u₃}
  [Category.{v} 𝒮'] {𝒳 : Type u₄} [Category.{v₄} 𝒳] {J : GrothendieckTopology 𝒞}
  {p : 𝒮 ⥤ 𝒞} {p' : 𝒮' ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'} {F : 𝒮 ⥤ 𝒳}
  [p.IsFibered] [p'.IsFibered] [q.IsFibered]
  (hG : p.IsFibredOneMorphism p' G) (hF : p.IsFibredOneMorphism q F)
  (hmor : ∀ (U : 𝒞) (x y : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap x y))
  (hqmor : ∀ (U : 𝒞) (x y : q.Fiber U), IsMorSheaf q J U x y)
  (hobj : ∀ (U : 𝒞) (x' : p'.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
    (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x' f))
  (hdesc : HasEffectiveDescent q J)

/-- **The component of the 2-isomorphism `G ⋙ H ≅ F` of Stacks 0435, read in the fibre over the
image of `A`.** It is the component itself, which is an isomorphism lying over an identity. -/
noncomputable def extendFiberUnitIso (A : 𝒮) :
    (fiberFunctorOfCompEq
        (hG.comp (extend_isFibredOneMorphism hG hF hmor hqmor hobj hdesc)).comp_eq
        (p.obj A)).obj ⟨A, rfl⟩ ≅
      (fiberFunctorOfCompEq hF.comp_eq (p.obj A)).obj ⟨A, rfl⟩ :=
  haveI := isIso_unitHom hG hF hmor hqmor hobj hdesc A
  Fiber.isoMk (asIso (unitHom hG hF hmor hqmor hobj hdesc A))
    (isHomLift_id_unitHom hG hF hmor hqmor hobj hdesc A)

/-- **An object of a fibre of `𝒳` in the essential image of `F` is in the essential image of
`G ⋙ H`**, for `H` the extension of `F` along `G` of Stacks 0435. The witness is the same object
of the fibre of `𝒮`, carried by the component of the 2-isomorphism `G ⋙ H ≅ F`.

Stated one object at a time, so that whatever covering carries clause (2) of Stacks 02ZN for `F`
carries it for `G ⋙ H` — a covering family as well as a covering sieve. -/
theorem essImage_extend_comp_of_essImage (V : 𝒞) {z : q.Fiber V}
    (h : (fiberFunctorOfCompEq hF.comp_eq V).essImage z) :
    (fiberFunctorOfCompEq
      (hG.comp (extend_isFibredOneMorphism hG hF hmor hqmor hobj hdesc)).comp_eq V).essImage z := by
  obtain ⟨a, ⟨e⟩⟩ := h
  obtain ⟨A, rfl⟩ := a
  exact ⟨⟨A, rfl⟩, ⟨extendFiberUnitIso hG hF hmor hqmor hobj hdesc A ≪≫ e⟩⟩

end CategoryTheory.Functor.Stackification

end
