module

public import StacksFrontier.CategoryTheory.Sites.Stack.FaithfulDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.Setoid

/-!
# Being a stack in setoids descends along a fully faithful base change (Stacks 05W9)

Let `(𝒞, J)` be a site and let
```
𝒯₂ ⟶ 𝒯₁
↓      ↓G
𝒮₂ ⟶F 𝒮₁
```
be a 2-cartesian diagram of stacks in groupoids over `𝒞`. If `F` is fully faithful, every object of
a fibre of `𝒮₁` is locally in the essential image of `F`, and `𝒯₂` is a stack in setoids, then `𝒯₁`
is a stack in setoids.

As in `StacksFrontier.CategoryTheory.Sites.Stack.FaithfulDescent`, `𝒯₂` is taken to *be* the 2-fibre
product `𝒮₂ ×_{𝒮₁} 𝒯₁` of Stacks 0040, `CategoryTheory.TwoFibreProductOver`, which is the reduction
the source's proof opens with.

## Main results

* `CategoryTheory.Functor.eq_id_of_fibre_isThin_of_locallyEssSurj`, the substance: every
  endomorphism of an object of a fibre of `𝒯₁` is the identity.
* `CategoryTheory.Functor.isStackInSetoids_of_isStackInSetoids_twoFibreProduct`: **Stacks 05W9**.

## Implementation notes

Being a stack in setoids is `CategoryTheory.Functor.IsStackInSetoids`, the conjunction of being a
stack, having groupoid fibres and having thin fibres. The first two are part of the hypothesis that
`𝒯₁` is a stack in groupoids, so what 05W9 adds — and what is proved here — is thinness of the
fibres of `𝒯₁`, exactly as the source's proof says: "we have to show that the sheaf `Aut(y)` on
`𝒞/U` is trivial".

Of the hypothesis that `𝒯₂` is a stack in setoids only thinness of its fibres is used, and of the
full faithfulness of `F` only fullness; the source's hypotheses are nonetheless the ones the tagged
statement carries, and the local step
`CategoryTheory.Functor.eq_id_of_fibre_isThin_of_locallyEssSurj` is stated with the weaker ones.
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

universe v u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v} 𝒞]
variable {𝒮₁ : Type u₂} [Category.{v} 𝒮₁] {𝒮₂ : Type u₃} [Category.{v} 𝒮₂]
  {𝒯₁ : Type u₄} [Category.{v} 𝒯₁]
  {p𝒮₁ : 𝒮₁ ⥤ 𝒞} {p𝒮₂ : 𝒮₂ ⥤ 𝒞} {p𝒯₁ : 𝒯₁ ⥤ 𝒞} {F : 𝒮₂ ⥤ 𝒮₁} {G : 𝒯₁ ⥤ 𝒮₁}

/-- The substance of Stacks 05W9: every endomorphism `γ` of an object `y` of a fibre of `𝒯₁` is the
identity.

Over each member `f : V ⟶ U` of the covering sieve supplied by local essential surjectivity there
are an object `z` of `𝒮₂` and an isomorphism `ε : F z ≅ G (f^* y)`, so `(V, z, f^* y, ε)` is an
object `P` of the 2-fibre product. Fullness of `F` on the fibre over `V` produces an endomorphism
`a` of `z` with `F a = ε ∘ G (f^* γ) ∘ ε⁻¹`, and `(a, f^* γ)` is then an endomorphism of `P` in the
fibre of the 2-fibre product over `V`. That fibre being thin, it is the identity, so `f^* γ` is the
identity; and the presheaf `Mor(y, y)` of `𝒯₁` being a sheaf, `γ` itself is. -/
theorem eq_id_of_fibre_isThin_of_locallyEssSurj (hFeq : F ⋙ p𝒮₁ = p𝒮₂)
    (hGeq : G ⋙ p𝒮₁ = p𝒯₁) (hgpd₁ : p𝒮₁.IsFiberedInGroupoids)
    (hgpd₂ : p𝒮₂.IsFiberedInGroupoids) [F.Full] [F.Faithful]
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
  replace e := e ≪≫ mapPullbackFiberIso' hG y f
  obtain ⟨hFull, -⟩ :=
    (IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber p𝒮₂ p𝒮₁ hgpd₂ hgpd₁ F hFeq).1
      ⟨inferInstance, inferInstance⟩ V
  obtain ⟨a, ha⟩ := hFull.map_surjective
    (e.hom ≫ (Fiber.mapOfComp p𝒯₁ p𝒮₁ G hGeq V).map (pullbackFiberHom γ f) ≫ e.inv)
  have hwfib : (Fiber.mapOfComp p𝒮₂ p𝒮₁ F hFeq V).map a ≫ e.hom =
      e.hom ≫ (Fiber.mapOfComp p𝒯₁ p𝒮₁ G hGeq V).map (pullbackFiberHom γ f) := by
    rw [ha]; simp
  refine Fiber.hom_ext ?_
  let P : TwoFibreProductOver p𝒮₂ p𝒯₁ p𝒮₁ F G :=
    { base := V
      x := z.1
      y := (pullbackFiber p𝒯₁ y f).1
      hx := z.2
      hy := (pullbackFiber p𝒯₁ y f).2
      iso := Fiber.fiberInclusion.mapIso e
      vertical := e.hom.2 }
  let Φ : P ⟶ P :=
    { hbase := 𝟙 V
      a := Fiber.fiberInclusion.map a
      b := Fiber.fiberInclusion.map (pullbackFiberHom γ f)
      ha := a.2
      hb := (pullbackFiberHom γ f).2
      w := congrArg Fiber.fiberInclusion.map hwfib }
  have hlift : (TwoFibreProductOver.structureFunctor p𝒮₂ p𝒯₁ p𝒮₁ F G).IsHomLift (𝟙 V) Φ := by
    refine IsHomLift.of_fac' _ (𝟙 V) Φ rfl rfl ?_
    change (𝟙 V) = eqToHom rfl ≫ (𝟙 V) ≫ eqToHom rfl
    simp
  let Pf : (TwoFibreProductOver.structureFunctor p𝒮₂ p𝒯₁ p𝒮₁ F G).Fiber V := ⟨P, rfl⟩
  exact congrArg (fun φ : Pf ⟶ Pf => φ.1.b) ((hthin V Pf Pf).elim ⟨Φ, hlift⟩ (𝟙 Pf))

/-- **Stacks 05W9**. In a 2-cartesian diagram of stacks in groupoids over a site, if `F` is fully
faithful, every object of a fibre of `𝒮₁` is locally in the essential image of `F`, and the 2-fibre
product `𝒮₂ ×_{𝒮₁} 𝒯₁` is a stack in setoids, then `𝒯₁` is a stack in setoids.

Being a stack and having groupoid fibres are hypotheses — they are what makes `𝒯₁` a stack in
groupoids — so the content is thinness of the fibres of `𝒯₁`, and that is
`CategoryTheory.Functor.eq_id_of_fibre_isThin_of_locallyEssSurj` applied to `β ∘ α⁻¹`, the fibres
of `𝒯₁` being groupoids. -/
@[stacks 05W9]
theorem isStackInSetoids_of_isStackInSetoids_twoFibreProduct (hFeq : F ⋙ p𝒮₁ = p𝒮₂)
    (hGeq : G ⋙ p𝒮₁ = p𝒯₁) (hgpd₁ : p𝒮₁.IsFiberedInGroupoids)
    (hgpd₂ : p𝒮₂.IsFiberedInGroupoids) (hgpdT : p𝒯₁.IsFiberedInGroupoids)
    [F.Full] [F.Faithful] {J : GrothendieckTopology 𝒞} (hstack : p𝒯₁.IsStack J)
    (hloc : LocallyEssSurjOnFibers hgpd₁.isFibered hFeq J)
    (hT₂ : (TwoFibreProductOver.structureFunctor p𝒮₂ p𝒯₁ p𝒮₁ F G).IsStackInSetoids J) :
    p𝒯₁.IsStackInSetoids J where
  isStack := hstack
  fiber_isGroupoid := hgpdT.fiber_isGroupoid
  fiber_isThin U y y' := by
    refine ⟨fun α β ↦ ?_⟩
    have : IsGroupoid (p𝒯₁.Fiber U) := hgpdT.fiber_isGroupoid U
    exact ((comp_inv_eq_id α).1 (eq_id_of_fibre_isThin_of_locallyEssSurj hFeq hGeq hgpd₁ hgpd₂
      hstack hloc hT₂.fiber_isThin (β ≫ CategoryTheory.inv α))).symm

end Functor

end CategoryTheory
