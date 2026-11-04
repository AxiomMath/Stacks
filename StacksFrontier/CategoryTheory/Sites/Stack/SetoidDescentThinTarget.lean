module

public import StacksFrontier.CategoryTheory.Sites.Stack.SetoidDescent

/-!
# Being a stack in setoids descends along a base change with thin target fibres

Let `(𝒞, J)` be a site and let
```text
𝒯₂ ⟶ 𝒯₁
↓      ↓G
𝒮₂ ⟶F 𝒮₁
```
be a 2-cartesian diagram of categories over `𝒞`, with `𝒯₂` the 2-fibre product `𝒮₂ ×_{𝒮₁} 𝒯₁` of
Stacks 0040. `CategoryTheory.Functor.isStackInSetoids_of_isStackInSetoids_twoFibreProduct`
(Stacks 05W9) descends the setoid condition from `𝒯₂` to `𝒯₁` when `F` is **fully faithful** and
locally essentially surjective on fibres. This file proves the same conclusion from a different
hypothesis on `F`: no fullness, but **thin fibres for `𝒮₁`**.

That is the form the descent criterion is used in when `𝒮₁` and `𝒮₂` are categories fibred in
groupoids represented by presheaves of sets — their fibres are then thin for free, while `F` is
in general not full. It is what Stacks 05XL consumes.

## Main results

* `CategoryTheory.Functor.eq_id_of_isThin_of_locallyEssSurj`, the substance: every endomorphism of
  an object of a fibre of `𝒯₁` is the identity.
* `CategoryTheory.Functor.isStackInSetoids_of_isThin_of_locallyEssSurj`: `𝒯₁` is a stack in
  setoids.

## Implementation notes

The proof is that of `CategoryTheory.Functor.eq_id_of_fibre_isThin_of_locallyEssSurj` with its one
use of fullness removed. There, fullness of `F` on the fibre over `V` produces an endomorphism `a`
of `z` with `F a = ε ∘ G (f^* γ) ∘ ε⁻¹`, which is what makes `(a, f^* γ)` an endomorphism of the
object `(V, z, f^* y, ε)` of the 2-fibre product. Here the fibres of `𝒮₁` are thin, so `G (f^* γ)`
is *already* the identity on the fibre over `V`, and `(𝟙 z, f^* γ)` is such an endomorphism with no
`a` to produce. The rest is unchanged: the fibre of the 2-fibre product over `V` being thin, that
endomorphism is the identity, so `f^* γ` is; and the presheaf `Mor(y, y)` of `𝒯₁` being a sheaf,
`γ` itself is.

Of the hypothesis that the 2-fibre product is a stack in setoids only thinness of its fibres is
used, so the local step is stated with that alone, as in
`StacksFrontier.CategoryTheory.Sites.Stack.SetoidDescent`.

## References

* [Stacks Project, Tag 05W9](https://stacks.math.columbia.edu/tag/05W9)
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

universe v u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v} 𝒞]
variable {𝒮₁ : Type u₂} [Category.{v} 𝒮₁] {𝒮₂ : Type u₃} [Category.{v} 𝒮₂]
  {𝒯₁ : Type u₄} [Category.{v} 𝒯₁]
  {p𝒮₁ : 𝒮₁ ⥤ 𝒞} {p𝒮₂ : 𝒮₂ ⥤ 𝒞} {p𝒯₁ : 𝒯₁ ⥤ 𝒞} {F : 𝒮₂ ⥤ 𝒮₁} {G : 𝒯₁ ⥤ 𝒮₁}

/-- Every endomorphism `γ` of an object `y` of a fibre of `𝒯₁` is the identity, when the fibres of
`𝒮₁` and of the 2-fibre product `𝒮₂ ×_{𝒮₁} 𝒯₁` are thin and every object of a fibre of `𝒮₁` is
locally in the essential image of `F`.

This is `CategoryTheory.Functor.eq_id_of_fibre_isThin_of_locallyEssSurj` with fullness of `F`
traded for thinness of the fibres of `𝒮₁`: over a member `f : V ⟶ U` of the covering sieve
supplied by local essential surjectivity there are an object `z` of `𝒮₂` and an isomorphism
`ε : F z ≅ G (f^* y)`, and `(𝟙 z, f^* γ)` is an endomorphism of the object `(V, z, f^* y, ε)` of
the 2-fibre product precisely because `G (f^* γ)` is the identity on the thin fibre of `𝒮₁` over
`V`. -/
theorem eq_id_of_isThin_of_locallyEssSurj (hFeq : F ⋙ p𝒮₁ = p𝒮₂)
    (hGeq : G ⋙ p𝒮₁ = p𝒯₁) (hgpd₁ : p𝒮₁.IsFiberedInGroupoids)
    (hthin₁ : ∀ V : 𝒞, Quiver.IsThin (p𝒮₁.Fiber V))
    {J : GrothendieckTopology 𝒞} (hstack : p𝒯₁.IsStack J)
    (hloc : LocallyEssSurjOnFibers hgpd₁.isFibered hFeq J)
    (hthin : ∀ V : 𝒞,
      Quiver.IsThin ((TwoFibreProductOver.structureFunctor p𝒮₂ p𝒯₁ p𝒮₁ F G).Fiber V))
    {U : 𝒞} {y : p𝒯₁.Fiber U} (γ : y ⟶ y) :
    γ = 𝟙 y := by
  have hT : p𝒯₁.IsFibered := hstack.isFibered
  have hS : p𝒮₁.IsFibered := hgpd₁.isFibered
  have hG : IsFibredOneMorphism p𝒯₁ p𝒮₁ G :=
    IsFibredOneMorphism.of_isFiberedInGroupoids hgpd₁ hGeq
  obtain ⟨R, hR, hRess⟩ := hloc U ((Fiber.mapOfComp p𝒯₁ p𝒮₁ G hGeq U).obj y)
  refine eq_of_pullbackFiberHom_locally_eq p𝒯₁ (hstack.isMorSheaf U y y) hR ?_
  intro V f hf
  rw [pullbackFiberHom_id]
  obtain ⟨z, ⟨e⟩⟩ := hRess f hf
  have hGγV : (Fiber.mapOfComp p𝒯₁ p𝒮₁ G hGeq V).map (pullbackFiberHom γ f) = 𝟙 _ :=
    (hthin₁ V _ _).elim _ _
  have hGmap : G.map (Fiber.fiberInclusion.map (pullbackFiberHom γ f)) = 𝟙 _ :=
    (congrArg Fiber.fiberInclusion.map hGγV).trans (Fiber.fiberInclusion.map_id _)
  have hw : F.map (𝟙 z.1) ≫
        (Fiber.fiberInclusion.mapIso (e ≪≫ mapPullbackFiberIso' hG y f)).hom =
      (Fiber.fiberInclusion.mapIso (e ≪≫ mapPullbackFiberIso' hG y f)).hom ≫
        G.map (Fiber.fiberInclusion.map (pullbackFiberHom γ f)) := by
    rw [hGmap, F.map_id]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  refine Fiber.hom_ext ?_
  let P : TwoFibreProductOver p𝒮₂ p𝒯₁ p𝒮₁ F G :=
    { base := V
      x := z.1
      y := (pullbackFiber p𝒯₁ y f).1
      hx := z.2
      hy := (pullbackFiber p𝒯₁ y f).2
      iso := Fiber.fiberInclusion.mapIso (e ≪≫ mapPullbackFiberIso' hG y f)
      vertical := (e ≪≫ mapPullbackFiberIso' hG y f).hom.2 }
  let Φ : P ⟶ P :=
    { hbase := 𝟙 V
      a := 𝟙 z.1
      b := Fiber.fiberInclusion.map (pullbackFiberHom γ f)
      ha := IsHomLift.id z.2
      hb := (pullbackFiberHom γ f).2
      w := hw }
  have hlift : (TwoFibreProductOver.structureFunctor p𝒮₂ p𝒯₁ p𝒮₁ F G).IsHomLift (𝟙 V) Φ := by
    refine IsHomLift.of_fac' _ (𝟙 V) Φ rfl rfl ?_
    change (𝟙 V) = eqToHom rfl ≫ (𝟙 V) ≫ eqToHom rfl
    simp
  let Pf : (TwoFibreProductOver.structureFunctor p𝒮₂ p𝒯₁ p𝒮₁ F G).Fiber V := ⟨P, rfl⟩
  have hΦ : Φ = 𝟙 P := congrArg Subtype.val ((hthin V Pf Pf).elim ⟨Φ, hlift⟩ (𝟙 Pf))
  exact congrArg TwoFibreProductOver.Hom.b hΦ

/-- `𝒯₁` is a stack in setoids when it is a stack fibred in groupoids, the fibres of `𝒮₁` are thin,
every object of a fibre of `𝒮₁` is locally in the essential image of `F`, and the 2-fibre product
`𝒮₂ ×_{𝒮₁} 𝒯₁` is a stack in setoids.

This is `CategoryTheory.Functor.isStackInSetoids_of_isStackInSetoids_twoFibreProduct`
(**Stacks 05W9**) with fullness of `F` traded for thinness of the fibres of `𝒮₁`. As there, being
a stack and having groupoid fibres are hypotheses, so the content is thinness of the fibres of
`𝒯₁`, and that is `CategoryTheory.Functor.eq_id_of_isThin_of_locallyEssSurj` applied to
`β ∘ α⁻¹`, the fibres of `𝒯₁` being groupoids. -/
theorem isStackInSetoids_of_isThin_of_locallyEssSurj (hFeq : F ⋙ p𝒮₁ = p𝒮₂)
    (hGeq : G ⋙ p𝒮₁ = p𝒯₁) (hgpd₁ : p𝒮₁.IsFiberedInGroupoids)
    (hthin₁ : ∀ V : 𝒞, Quiver.IsThin (p𝒮₁.Fiber V))
    (hgpdT : p𝒯₁.IsFiberedInGroupoids) {J : GrothendieckTopology 𝒞} (hstack : p𝒯₁.IsStack J)
    (hloc : LocallyEssSurjOnFibers hgpd₁.isFibered hFeq J)
    (hT₂ : (TwoFibreProductOver.structureFunctor p𝒮₂ p𝒯₁ p𝒮₁ F G).IsStackInSetoids J) :
    p𝒯₁.IsStackInSetoids J where
  isStack := hstack
  fiber_isGroupoid := hgpdT.fiber_isGroupoid
  fiber_isThin U y y' := by
    refine ⟨fun α β ↦ ?_⟩
    have : IsGroupoid (p𝒯₁.Fiber U) := hgpdT.fiber_isGroupoid U
    have hα : IsIso α := IsGroupoid.all_isIso α
    have hid := eq_id_of_isThin_of_locallyEssSurj hFeq hGeq hgpd₁ hthin₁ hstack hloc
      hT₂.fiber_isThin (β ≫ CategoryTheory.inv α)
    exact (show β = α by simpa using hid).symm

end Functor

end CategoryTheory

end
