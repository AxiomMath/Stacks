module

public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification

/-!
# The fibres of the split model are the fibres (Stacks 004A)

Let `p : 𝒳 ⥤ 𝒞` be a fibred category. The split model `𝒮'` of Stacks 004A is presented through
its fibres `CategoryTheory.Functor.SplitFiber p V`, whose objects are the pairs `(x, f : V ⟶ U)`
with `x` an object of the fibre `𝒳_U`. This file compares that fibre with the fibre `𝒳_V` itself,
which is the fibrewise half of Stacks 004A: the pair `(x, f)` is evaluated as the chosen pullback
`f^* x`, and the resulting functor is an equivalence.

It is only an equivalence and not an isomorphism of categories: it is bijective on morphisms —
the two hom types are *equal* by the definition of the category structure on `SplitFiber p V` —
but very far from injective on objects, since every `(x, f)` with `f` an isomorphism evaluates to
an object isomorphic to `x`. Consequently a diagram built from `SplitFiber` cannot be replaced by
the corresponding diagram of fibres inside a 1-categorical colimit; only the colimits are
comparable, and then only up to equivalence.

## Main definitions

* `CategoryTheory.Functor.SplitFiber.evaluation`: the evaluation functor `𝒮'_V ⥤ 𝒳_V`.
* `CategoryTheory.Functor.SplitFiber.fiberEquiv`: **Stacks 004A, fibrewise** — the equivalence
  `𝒮'_V ≌ 𝒳_V`.

## Main results

* `CategoryTheory.Functor.SplitFiber.isEquivalence_evaluation`: evaluation is an equivalence.
* `CategoryTheory.Functor.SplitFiber.evaluationPullbackIso`: evaluation intertwines the strict
  restriction functors of the split model with the pullback functors of the canonical choice of
  pullbacks.

## References

* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
* [Stacks Project, Tag 02XY](https://stacks.math.columbia.edu/tag/02XY)
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

namespace SplitFiber

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.chosenPullbacks

variable (p : 𝒳 ⥤ 𝒞) [p.IsFibered]

/-- Evaluation of the fibre of the split model over `V` in the fibre of `p` over `V`: the pair
`(x, f)` is sent to the chosen pullback `f^* x`, and a morphism to itself, the two hom types being
equal. -/
noncomputable def evaluation (V : 𝒞) : p.SplitFiber V ⥤ p.Fiber V where
  obj o := o.toFiber
  map α := toFiberHom α

/-- Evaluation sends the pair `(x, f)` to the chosen pullback `f^* x`. -/
@[simp]
lemma evaluation_obj (V : 𝒞) (o : p.SplitFiber V) : (evaluation p V).obj o = o.toFiber := rfl

/-- Evaluation acts on a morphism of split fibres as the same morphism of fibres. -/
@[simp]
lemma evaluation_map {V : 𝒞} {o o' : p.SplitFiber V} (α : o ⟶ o') :
    (evaluation p V).map α = toFiberHom α := rfl

/-- Evaluation is full. -/
instance full_evaluation (V : 𝒞) : (evaluation p V).Full where
  map_surjective α := ⟨ofFiberHom α, rfl⟩

/-- Evaluation is faithful. -/
instance faithful_evaluation (V : 𝒞) : (evaluation p V).Faithful where
  map_injective h := toFiberHom_injective h

/-- Evaluation is essentially surjective: the object `x` of `𝒳_V` is the value at the pair
`(x, 𝟙 V)`, up to the canonical comparison `𝟙^* x ≅ x`. -/
instance essSurj_evaluation (V : 𝒞) : (evaluation p V).EssSurj where
  mem_essImage x := ⟨⟨V, x, 𝟙 V⟩, ⟨pullbackFiberIdIso x⟩⟩

/-- Evaluation is an equivalence of categories. -/
instance isEquivalence_evaluation (V : 𝒞) : (evaluation p V).IsEquivalence where

/-- **The fibrewise half of Stacks 004A.** The equivalence between the fibre of the split model
over `V` and the fibre `𝒳_V` of `p`, given by evaluation. The tag itself is registered on
`CategoryTheory.Functor.exists_isFibredEquivalenceOver_presheafOfCategories`, the equivalence of
the whole fibred categories. -/
noncomputable def fiberEquiv (V : 𝒞) : p.SplitFiber V ≌ p.Fiber V :=
  (evaluation p V).asEquivalence

/-- The functor of `fiberEquiv p V` is `evaluation p V`. -/
@[simp]
lemma fiberEquiv_functor (V : 𝒞) : (fiberEquiv p V).functor = evaluation p V := rfl

/-- The comparison between the twofold chosen pullback and the chosen pullback along the
composite is compatible with the projection to the first chosen pullback. -/
@[reassoc]
lemma pullbackFiberCompIso_hom_pullbackFiberProj {V W : 𝒞} (g : W ⟶ V) (o : p.SplitFiber V) :
    Fiber.fiberInclusion.map (pullbackFiberCompIso o.obj o.hom g).hom ≫
        pullbackFiberProj o.obj o.hom g =
      IsPreFibered.pullbackMap o.toFiber.2 g := by
  apply IsStronglyCartesian.ext p o.hom o.proj g
  rw [Category.assoc, pullbackFiberProj_fac, pullbackFiberCompIso_hom_fac]

/-- Evaluation intertwines the strict restriction functor of the split model along `g` with the
pullback functor along `g` of the canonical choice of pullbacks. The strict diagram of split fibres
used to form colimits is therefore stagewise comparable to the diagram of fibres and pullback
functors of Stacks 02XN. -/
noncomputable def evaluationPullbackIso {V W : 𝒞} (g : W ⟶ V) :
    evaluation p V ⋙ (chosenPullbacks p).pullbackFunctor g ≅
      restrict p g ⋙ evaluation p W :=
  NatIso.ofComponents (fun o => pullbackFiberCompIso o.obj o.hom g)
    (fun {o o'} α => by
      apply fiber_hom_ext_of_cartesian (g ≫ o'.hom)
        (IsPreFibered.pullbackMap o'.obj.2 (g ≫ o'.hom))
        (IsPreFibered.pullbackMap.IsCartesian o'.obj.2 (g ≫ o'.hom))
      change Fiber.fiberInclusion.map
          ((chosenPullbacks p).homMap g (toFiberHom α) ≫
            (pullbackFiberCompIso o'.obj o'.hom g).hom) ≫ _ =
        Fiber.fiberInclusion.map
          ((pullbackFiberCompIso o.obj o.hom g).hom ≫ restrictHom g (toFiberHom α)) ≫ _
      rw [Functor.map_comp, Functor.map_comp, Category.assoc,
        pullbackFiberCompIso_hom_fac, ← Category.assoc, chosenPullbacks_homMap,
        pullbackFiberHom_fac, Category.assoc, Category.assoc, restrictHom_fac,
        pullbackFiberCompIso_hom_pullbackFiberProj_assoc])

end SplitFiber

end CategoryTheory.Functor

end
