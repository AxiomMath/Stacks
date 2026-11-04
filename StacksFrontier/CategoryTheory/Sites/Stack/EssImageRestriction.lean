module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap

/-!
# Essential images of fibre functors are stable under further restriction

Let `p : 𝒜 ⥤ 𝒞` and `p' : 𝒮 ⥤ 𝒞` be fibred categories and let `G : 𝒜 ⥤ 𝒮` be a 1-morphism over
`𝒞`. If the chosen restriction of an object `x` of a fibre of `p'` along `f : V ⟶ U` is in the
essential image of the functor `G` induces on the fibre over `V`, then its chosen restriction
along any composite `ε ≫ f` is in the essential image of the functor induced on the fibre over
the source of `ε`.

Clause (2) of Stacks 02ZN therefore survives passing from a covering family to a refinement of
it, which is what lets two objects of one fibre be presented over a *common* family: the
pointwise intersection of two covering families by open immersions refines both.

## Main results

* `CategoryTheory.Functor.IsFibredOneMorphism.essImage_pullbackFiber_comp`: the statement above.

## Implementation notes

The witness over the smaller object is the chosen restriction along `ε` of the witness over `V`.
The isomorphism is the uniqueness of cartesian lifts
(`CategoryTheory.Functor.fiberIsoOfCartesian`) applied to two morphisms over `ε ≫ f` into `x`:
the chosen cartesian lift of `ε ≫ f`, and the image under `G` of the chosen cartesian lift of
`ε`, followed by the given isomorphism and the chosen cartesian lift of `f`. The second is
strongly cartesian because `G` preserves strongly cartesian morphisms, because an isomorphism
over an identity is strongly cartesian, and because strongly cartesian morphisms compose.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
-/

@[expose] public section

namespace CategoryTheory.Functor.IsFibredOneMorphism

open CategoryTheory

-- The chosen pullbacks, the fibre and its inclusion, and the induced functor on fibres are
-- semireducible, so the endpoints of the composites below agree only once they unfold.
attribute [local implicit_reducible] Fiber Fiber.fiberInclusion IsPreFibered.pullbackObj

universe vb v₁ v₂ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒜 : Type u₂} [Category.{v₁} 𝒜]
  {𝒮 : Type u₃} [Category.{v₂} 𝒮] {p : 𝒜 ⥤ 𝒞} {p' : 𝒮 ⥤ 𝒞} {G : 𝒜 ⥤ 𝒮}
  [p.IsFibered] [p'.IsFibered]

/-- **The essential image of a fibre functor is stable under further restriction.** If the chosen
restriction of `x` along `f` is in the essential image of `G` on the fibre over the source of
`f`, then so is its chosen restriction along `ε ≫ f` on the fibre over the source of `ε`. -/
theorem essImage_pullbackFiber_comp (hG : p.IsFibredOneMorphism p' G)
    {U V W : 𝒞} {f : V ⟶ U} {ε : W ⟶ V} {b : W ⟶ U} (hb : ε ≫ f = b) (x : p'.Fiber U)
    (h : (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x f)) :
    (fiberFunctorOfCompEq hG.comp_eq W).essImage (pullbackFiber p' x b) := by
  subst hb
  obtain ⟨a, ⟨e⟩⟩ := h
  refine ⟨pullbackFiber p a ε, ⟨?_⟩⟩
  -- the given isomorphism, followed by the chosen cartesian lift of `f`, is cartesian over `f`
  have hiso : p'.IsHomLift (𝟙 V) (Fiber.fiberInclusion.map e.hom) := e.hom.2
  have hisoI : IsIso (Fiber.fiberInclusion.map e.hom) := inferInstance
  have hisoC : p'.IsStronglyCartesian (𝟙 V) (Fiber.fiberInclusion.map e.hom) :=
    IsStronglyCartesian.of_isIso p' (𝟙 V) _
  have hpbf : p'.IsStronglyCartesian f (IsPreFibered.pullbackMap x.2 f) :=
    IsFibered.isStronglyCartesian_of_isCartesian p' f _
  have hψ₀ : p'.IsStronglyCartesian (𝟙 V ≫ f)
      (Fiber.fiberInclusion.map e.hom ≫ IsPreFibered.pullbackMap x.2 f) := inferInstance
  rw [Category.id_comp] at hψ₀
  -- its precomposition with the image of the chosen cartesian lift of `ε` is cartesian
  -- over `ε ≫ f`
  have hpbε : p.IsStronglyCartesian ε (IsPreFibered.pullbackMap a.2 ε) :=
    IsFibered.isStronglyCartesian_of_isCartesian p ε _
  have hG' : p'.IsStronglyCartesian ε (G.map (IsPreFibered.pullbackMap a.2 ε)) :=
    hG.map_isStronglyCartesian ε _ hpbε
  have hψ : p'.IsStronglyCartesian (ε ≫ f)
      (G.map (IsPreFibered.pullbackMap a.2 ε) ≫
        Fiber.fiberInclusion.map e.hom ≫ IsPreFibered.pullbackMap x.2 f) :=
    inferInstance
  exact fiberIsoOfCartesian (ε ≫ f)
    (G.map (IsPreFibered.pullbackMap a.2 ε) ≫
      Fiber.fiberInclusion.map e.hom ≫ IsPreFibered.pullbackMap x.2 f)
    (IsPreFibered.pullbackMap x.2 (ε ≫ f)) inferInstance inferInstance

end CategoryTheory.Functor.IsFibredOneMorphism

end
