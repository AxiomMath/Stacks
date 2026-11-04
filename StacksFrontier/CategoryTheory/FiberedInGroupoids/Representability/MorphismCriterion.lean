module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoClassPresheafRepresentable
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceFunctorComparison
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindex

/-!
# A criterion for a 1-morphism of categories fibred in groupoids to be representable

Let `𝒳`, `𝒴` be categories fibred in groupoids over `𝒞`, let `F : 𝒳 ⥤ 𝒴` be a 1-morphism over
`𝒞` and make a choice of pullbacks for `𝒴`. If

1. each functor `F_U : 𝒳_U ⥤ 𝒴_U` between fibre categories is faithful, and
2. for each `U` and each object `y` of the fibre `𝒴_U` the presheaf on `𝒞/U`
   `(f : V ⟶ U) ↦ {(x, φ) | x ∈ 𝒳_V, φ : f^* y ⟶ F(x)}/≅` is representable,

then `F` is representable in the sense of Stacks 02Y7. The statement is made for `𝒞` and `𝒳`
with objects and morphisms in one universe `u` and `𝒴` with morphisms in `u`.

## Main results

* `CategoryTheory.isRepresentableMorphism_of_faithful_of_isRepresentable`: a 1-morphism of
  categories fibred in groupoids which is faithful on fibres and whose presheaves of pairs
  `(x, φ)` are representable is representable.
-/

@[expose] public section

namespace CategoryTheory

universe u u₃

attribute [local implicit_reducible] Functor.Fiber TwoFibreProductOver.fst
  Functor.ChoiceOfPullbacks.sliceFunctor Functor.ChoiceOfPullbacks.sliceObj

variable {𝒞 : Type u} [Category.{u} 𝒞] {𝒳 : Type u} [Category.{u} 𝒳] {𝒴 : Type u₃}
  [Category.{u} 𝒴]

/-- Let `𝒳`, `𝒴` be categories fibred in groupoids over `𝒞`, let `F : 𝒳 ⥤ 𝒴` be a 1-morphism
over `𝒞` and let `c` be a choice of pullbacks for `𝒴`. If every functor `F_U : 𝒳_U ⥤ 𝒴_U` on
fibre categories is faithful, and if for every `U` and every object `y` of `𝒴_U` the presheaf on
`𝒞/U` of isomorphism classes of pairs `(x, φ : f^* y ⟶ F(x))` is representable, then `F` is a
representable 1-morphism in the sense of Stacks 02Y7. -/
@[stacks 02Y9]
theorem isRepresentableMorphism_of_faithful_of_isRepresentable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞)
    (F : 𝒳 ⥤ 𝒴) (hF : F ⋙ p𝒴 = p𝒳) (h𝒳 : p𝒳.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (c : p𝒴.ChoiceOfPullbacks)
    (hfaithful : ∀ U : 𝒞, (Stacks.RepresentableMorphism.inducedFiberFunctor p𝒳 p𝒴 F hF U).Faithful)
    (hrepresentable : ∀ (U : 𝒞) (y : p𝒴.Fiber U),
      (PairIsoClass.presheaf F c y h𝒳 h𝒴 hF).IsRepresentable) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism p𝒳 p𝒴 F := by
  intro U G hG
  have hfib : (TwoFibreProductOver.fst (Over.forget U) p𝒳 p𝒴 G F).IsFiberedInGroupoids :=
    TwoFibreProductOver.fst_isFiberedInGroupoids U p𝒳 p𝒴 F G h𝒳 h𝒴 hF hG
  have hthin : ∀ f : Over U,
      Quiver.IsThin ((TwoFibreProductOver.fst (Over.forget U) p𝒳 p𝒴 G F).Fiber f) := by
    intro f A B
    refine ⟨fun u v => (TwoFibreProductOver.FstFiber.homEquiv A B).injective (Subtype.ext ?_)⟩
    refine Stacks.RepresentableMorphism.fiberHom_injective_of_inducedFiberFunctor_faithful p𝒳 p𝒴 F
      hF f.left (hfaithful f.left) _ _ (TwoFibreProductOver.FstFiber.homEquiv A B u).2.1
      (TwoFibreProductOver.FstFiber.homEquiv A B v).2.1 ?_
    rw [(TwoFibreProductOver.FstFiber.homEquiv A B u).2.2,
      (TwoFibreProductOver.FstFiber.homEquiv A B v).2.2]
  set y : p𝒴.Fiber U := Functor.ChoiceOfPullbacks.sliceObj G hG
  set α : G ≅ c.sliceFunctor y := Functor.ChoiceOfPullbacks.sliceFunctorIso c G hG h𝒴
  have hαv : ∀ f : Over U, p𝒴.IsHomLift (𝟙 ((Over.forget U).obj f)) (α.hom.app f) := fun f =>
    Functor.ChoiceOfPullbacks.sliceComparison_isHomLift c G hG f
  have hfib' : Functor.IsFiberedInGroupoids
      (TwoFibreProductOver.fst (Over.forget U) p𝒳 p𝒴 (c.sliceFunctor y) F) :=
    TwoFibreProductOver.fst_isFiberedInGroupoids U p𝒳 p𝒴 F (c.sliceFunctor y) h𝒳 h𝒴 hF
      (c.sliceFunctor_comp y)
  have := hfib.isFibered
  have := hfib'.isFibered
  have hiso := Functor.isoClassPresheafIso hfib hfib'
    (TwoFibreProductOver.reindex_comp_fst (G := F) α hαv)
    (TwoFibreProductOver.reindexSymm_comp_fst (G := F) α hαv)
    (TwoFibreProductOver.reindexSymm_reindex_obj (G := F) α hαv)
    (TwoFibreProductOver.reindex_reindexSymm_obj (G := F) α hαv)
  obtain ⟨X, ⟨hX⟩⟩ := hrepresentable U y
  have hX' : (Functor.isoClassPresheaf
      (TwoFibreProductOver.fst (Over.forget U) p𝒳 p𝒴 (c.sliceFunctor y) F)).RepresentableBy X := hX
  exact Stacks.RepresentableMorphism.isRepresentableCFG_of_isRepresentable _
    ((StacksRepresentableCFG.representable_iff _).2
      ⟨⟨hfib, hthin⟩, X, ⟨StacksRepresentableCFG.isoClassRepresentableBy_of_representableBy
        (hX'.ofIso hiso.symm)⟩⟩)

end CategoryTheory
