module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.TwoFibreProductOver
public import StacksFrontier.CategoryTheory.Sites.Stack.Groupoid
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap

/-!
# Faithfulness descends along a locally essentially surjective base change (Stacks 06DV)

Let `(𝒞, J)` be a site and let
```
𝒯₂ ⟶ 𝒯₁
↓G'    ↓G
𝒮₂ ⟶F 𝒮₁
```
be a 2-cartesian diagram of categories fibred in groupoids over `𝒞`, with `𝒯₁` a stack. If every
object of a fibre of `𝒮₁` is, locally on the base, in the essential image of `F`, and if `G'` is
faithful, then `G` is faithful.

Following the source, `𝒯₂` is taken to *be* the 2-fibre product `𝒮₂ ×_{𝒮₁} 𝒯₁` of Stacks 0040,
`CategoryTheory.TwoFibreProductOver`, and `G'` its first projection: the source's proof opens by
replacing `𝒯₂` with that model.

## Main definitions

* `CategoryTheory.Functor.LocallyEssSurjOnFibers`, the hypothesis that for every `U` and every `x`
  in the fibre over `U` there is a covering sieve of `U` along each member of which the base change
  of `x` is in the essential image of `F` on fibres.

## Main results

* `CategoryTheory.Functor.mapPullbackFiberIso'` and
  `CategoryTheory.Functor.mapPullbackFiberIso'_naturality`: a 1-morphism of fibred categories
  commutes with base change on fibres, up to a canonical isomorphism natural in the fibre morphism.
* `CategoryTheory.Functor.eq_id_of_map_eq_id_of_locallyEssSurj`, the local step: an endomorphism of
  an object of a fibre of `𝒯₁` that `G` sends to the identity is the identity.
* `CategoryTheory.Functor.faithful_of_faithful_fst`: **Stacks 06DV**.
* `CategoryTheory.Functor.eq_id_of_map_eq_id_of_locallyEssSurj_univ` and
  `CategoryTheory.Functor.faithful_of_faithful_fst_univ`: the same, with the morphism universe of
  the three fibred categories independent of that of the site.

## Implementation notes

"2-cartesian diagram of stacks in groupoids" is weakened to exactly the hypotheses the argument
uses: `𝒮₁` and `𝒯₁` are fibred in groupoids, and `𝒯₁` is a stack. Nothing is assumed of `𝒮₂`
beyond its being a category over `𝒞`, and neither `𝒯₂` nor `𝒮₂` is assumed fibred: the object of
`𝒯₂` that the argument builds is written down by hand, and the only property of `𝒯₂` used is the
faithfulness of `G'`. That `F` and `G` preserve strongly cartesian morphisms is not assumed
either — it is automatic because the target `𝒮₁` is fibred in groupoids
(`CategoryTheory.Functor.IsFibredOneMorphism.of_isFiberedInGroupoids`).

The comparison isomorphism `mapPullbackFiberIso'` is
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso` for a different choice of the
functor induced on fibres: the latter uses `CategoryTheory.Functor.fiberFunctorOfCompEq`, whereas
Stacks 003Z — whose reduction of faithfulness to the fibres is what this file rests on — is stated
for `CategoryTheory.Functor.Fiber.mapOfComp`. Its naturality in the fibre morphism, which is what
the argument actually needs, is proved here.

The base-change comparisons and the local essential-surjectivity predicate allow independent
morphism universes for the base, source and target; a fibred category over a site need not have
the morphism universe of the site, and a stackification in general does not. The four categories
in the faithfulness criterion below still share a morphism universe; in its `_univ` form the
three fibred categories share a morphism universe which need not be that of the site.
`CategoryTheory.Functor.IsFibredOneMorphism.isCartesian_map_pullbackMap` of
`StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap` is reused rather than
restated; it is already stated for independent universes.
-/

@[expose] public section

-- The chosen pullbacks of `CategoryTheory.Functor.IsPreFibered` and the inclusion of a fibre are
-- semireducible, so the endpoints of the composites below agree only up to unfolding them.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

namespace Functor

universe v v₂ v₃ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v} 𝒞]

/-! ### Base change along a 1-morphism of fibred categories -/

section MapPullbackFiber

variable {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₃} 𝒴]
variable {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} [p.IsFibered] [q.IsFibered] {G : 𝒳 ⥤ 𝒴}
variable (hG : IsFibredOneMorphism p q G)

/-- For a 1-morphism `G` of fibred categories over `𝒞`, the chosen pullback of `G x` along `f` is
canonically isomorphic, in the fibre, to `G` applied to the chosen pullback of `x` along `f`: both
carry a cartesian morphism over `f` to `G x`. This is
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso` with the functor induced on fibres
spelled as `CategoryTheory.Functor.Fiber.mapOfComp`, the spelling Stacks 003Z uses. -/
noncomputable def mapPullbackFiberIso' {U : 𝒞} (y : p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    pullbackFiber q ((Fiber.mapOfComp p q G hG.comp_eq U).obj y) f ≅
      (Fiber.mapOfComp p q G hG.comp_eq V).obj (pullbackFiber p y f) :=
  fiberIsoOfCartesian f
    (IsPreFibered.pullbackMap ((Fiber.mapOfComp p q G hG.comp_eq U).obj y).2 f)
    (G.map (IsPreFibered.pullbackMap y.2 f)) inferInstance
    (hG.isCartesian_map_pullbackMap y f)

/-- The comparison isomorphism `CategoryTheory.Functor.mapPullbackFiberIso'` is natural in the
morphism of the fibre: base changing a morphism and then applying `G` on fibres agrees with
applying `G` and then base changing. -/
lemma mapPullbackFiberIso'_naturality {U : 𝒞} {y y' : p.Fiber U} (m : y ⟶ y') {V : 𝒞} (f : V ⟶ U) :
    (mapPullbackFiberIso' hG y f).hom ≫
        (Fiber.mapOfComp p q G hG.comp_eq V).map (pullbackFiberHom m f) =
      pullbackFiberHom ((Fiber.mapOfComp p q G hG.comp_eq U).map m) f ≫
        (mapPullbackFiberIso' hG y' f).hom := by
  refine fiber_hom_ext_of_cartesian f (G.map (IsPreFibered.pullbackMap y'.2 f))
    (hG.isCartesian_map_pullbackMap y' f) _ _ ?_
  have hy : Fiber.fiberInclusion.map ((Fiber.mapOfComp p q G hG.comp_eq V).map
      (pullbackFiberHom m f)) = G.map (Fiber.fiberInclusion.map (pullbackFiberHom m f)) := rfl
  have hm : Fiber.fiberInclusion.map ((Fiber.mapOfComp p q G hG.comp_eq U).map m) =
      G.map (Fiber.fiberInclusion.map m) := rfl
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hy,
    ← Functor.map_comp G, pullbackFiberHom_fac, Functor.map_comp G, mapPullbackFiberIso',
    mapPullbackFiberIso', fiberIsoOfCartesian_hom_fac_assoc, fiberIsoOfCartesian_hom_fac,
    pullbackFiberHom_fac, hm]

end MapPullbackFiber

/-! ### Local essential surjectivity on fibres -/

/-- The hypothesis of Stacks 06DV on `F : 𝒮₂ ⥤ 𝒮₁`: for every object `U` of `𝒞` and every object
`x` of the fibre of `𝒮₁` over `U` there is a covering sieve of `U` such that along each of its
members `f : V ⟶ U` the base change `f^* x` is in the essential image of `F` on the fibres
over `V`.

The base change refers to the chosen pullbacks of `q`, which is why fibredness of `q` is an
argument rather than an instance, as it is for condition (2) of
`CategoryTheory.Functor.IsStack`. -/
def LocallyEssSurjOnFibers {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₃} 𝒴]
    {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} (hq : q.IsFibered) {F : 𝒳 ⥤ 𝒴} (hF : F ⋙ q = p)
    (J : GrothendieckTopology 𝒞) : Prop :=
  haveI : q.IsFibered := hq
  ∀ (U : 𝒞) (x : q.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R f →
    ∃ z : p.Fiber V, Nonempty ((Fiber.mapOfComp p q F hF V).obj z ≅ pullbackFiber q x f)

/-! ### Stacks 06DV -/

/-- The local step of Stacks 06DV, with independent morphism universes. -/
private theorem eq_id_of_map_eq_id_of_locallyEssSurj_aux
    {𝒮₁ : Type u₂} [Category.{v₂} 𝒮₁] {𝒮₂ : Type u₃} [Category.{v₂} 𝒮₂]
    {𝒯₁ : Type u₄} [Category.{v₂} 𝒯₁]
    {p𝒮₁ : 𝒮₁ ⥤ 𝒞} {p𝒮₂ : 𝒮₂ ⥤ 𝒞} {p𝒯₁ : 𝒯₁ ⥤ 𝒞} {F : 𝒮₂ ⥤ 𝒮₁} {G : 𝒯₁ ⥤ 𝒮₁}
    (hFeq : F ⋙ p𝒮₁ = p𝒮₂) (hGeq : G ⋙ p𝒮₁ = p𝒯₁)
    (hgpd₁ : p𝒮₁.IsFiberedInGroupoids) {J : GrothendieckTopology 𝒞}
    (hstack : p𝒯₁.IsStack J) (hloc : LocallyEssSurjOnFibers hgpd₁.isFibered hFeq J)
    (hfst : (TwoFibreProductOver.fst p𝒮₂ p𝒯₁ p𝒮₁ F G).Faithful)
    {U : 𝒞} {y : p𝒯₁.Fiber U} (γ : y ⟶ y)
    (hγ : (Fiber.mapOfComp p𝒯₁ p𝒮₁ G hGeq U).map γ = 𝟙 _) :
    γ = 𝟙 y := by
  have hT : p𝒯₁.IsFibered := hstack.isFibered
  have hS : p𝒮₁.IsFibered := hgpd₁.isFibered
  have hG : IsFibredOneMorphism p𝒯₁ p𝒮₁ G :=
    IsFibredOneMorphism.of_isFiberedInGroupoids hgpd₁ hGeq
  obtain ⟨R, hR, hRess⟩ := hloc U ((Fiber.mapOfComp p𝒯₁ p𝒮₁ G hGeq U).obj y)
  refine eq_of_pullbackFiberHom_locally_eq p𝒯₁ (hstack.isMorSheaf U y y) hR fun V f hf ↦ ?_
  rw [pullbackFiberHom_id]
  obtain ⟨z, ⟨e⟩⟩ := hRess f hf
  have hGγV : (Fiber.mapOfComp p𝒯₁ p𝒮₁ G hGeq V).map (pullbackFiberHom γ f) = 𝟙 _ := by
    have h := mapPullbackFiberIso'_naturality hG γ f
    rw [hγ, pullbackFiberHom_id, Category.id_comp] at h
    exact (Iso.cancel_iso_hom_left (mapPullbackFiberIso' hG y f) _ _).1
      (h.trans (Category.comp_id _).symm)
  have hGmap : G.map (Fiber.fiberInclusion.map (pullbackFiberHom γ f)) =
      𝟙 (G.obj (pullbackFiber p𝒯₁ y f).1) := congrArg Fiber.fiberInclusion.map hGγV
  have hw : F.map (𝟙 z.1) ≫
        (Fiber.fiberInclusion.mapIso (e ≪≫ mapPullbackFiberIso' hG y f)).hom =
      (Fiber.fiberInclusion.mapIso (e ≪≫ mapPullbackFiberIso' hG y f)).hom ≫
        G.map (Fiber.fiberInclusion.map (pullbackFiberHom γ f)) := by
    rw [hGmap, Functor.map_id, Category.id_comp]
    exact (Category.comp_id _).symm
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
  exact congrArg TwoFibreProductOver.Hom.b
    (show Φ = 𝟙 P from Functor.map_injective (TwoFibreProductOver.fst p𝒮₂ p𝒯₁ p𝒮₁ F G) rfl)

/-- Stacks 06DV, with independent morphism universes. -/
private theorem faithful_of_faithful_fst_aux
    {𝒮₁ : Type u₂} [Category.{v₂} 𝒮₁] {𝒮₂ : Type u₃} [Category.{v₂} 𝒮₂]
    {𝒯₁ : Type u₄} [Category.{v₂} 𝒯₁]
    {p𝒮₁ : 𝒮₁ ⥤ 𝒞} {p𝒮₂ : 𝒮₂ ⥤ 𝒞} {p𝒯₁ : 𝒯₁ ⥤ 𝒞} {F : 𝒮₂ ⥤ 𝒮₁} {G : 𝒯₁ ⥤ 𝒮₁}
    (hFeq : F ⋙ p𝒮₁ = p𝒮₂) (hGeq : G ⋙ p𝒮₁ = p𝒯₁)
    (hgpd₁ : p𝒮₁.IsFiberedInGroupoids) (hgpdT : p𝒯₁.IsFiberedInGroupoids)
    {J : GrothendieckTopology 𝒞} (hstack : p𝒯₁.IsStack J)
    (hloc : LocallyEssSurjOnFibers hgpd₁.isFibered hFeq J)
    (hfst : (TwoFibreProductOver.fst p𝒮₂ p𝒯₁ p𝒮₁ F G).Faithful) :
    G.Faithful := by
  rw [IsFiberedInGroupoids.faithful_iff_forall_fiber p𝒯₁ p𝒮₁ hgpdT hgpd₁ G hGeq]
  intro U
  refine ⟨fun {y y'} α β hab ↦ ?_⟩
  have : IsGroupoid (p𝒯₁.Fiber U) := hgpdT.fiber_isGroupoid U
  have hα : IsIso α := IsGroupoid.all_isIso α
  have hγ : (Fiber.mapOfComp p𝒯₁ p𝒮₁ G hGeq U).map (β ≫ CategoryTheory.inv α) = 𝟙 _ := by
    rw [Functor.map_comp, Functor.map_inv, ← hab, IsIso.hom_inv_id]
  rw [← Category.id_comp α,
    ← eq_id_of_map_eq_id_of_locallyEssSurj_aux hFeq hGeq hgpd₁ hstack hloc hfst _ hγ,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

section Faithful

variable {𝒮₁ : Type u₂} [Category.{v} 𝒮₁] {𝒮₂ : Type u₃} [Category.{v} 𝒮₂]
  {𝒯₁ : Type u₄} [Category.{v} 𝒯₁]
  {p𝒮₁ : 𝒮₁ ⥤ 𝒞} {p𝒮₂ : 𝒮₂ ⥤ 𝒞} {p𝒯₁ : 𝒯₁ ⥤ 𝒞} {F : 𝒮₂ ⥤ 𝒮₁} {G : 𝒯₁ ⥤ 𝒮₁}

/-- The local step of Stacks 06DV: an endomorphism `γ` of an object `y` of a fibre of `𝒯₁` that `G`
sends to the identity is itself the identity.

Over each member `f : V ⟶ U` of the covering sieve supplied by local essential surjectivity, an
object `z` of `𝒮₂` and an isomorphism `F z ≅ G (f^* y)` are available, so
`(V, z, f^* y, F z ≅ G (f^* y))` is an object `P` of the 2-fibre product and `(𝟙 z, f^* γ)` an
endomorphism of it whose first projection is the identity. Faithfulness of that projection makes
the endomorphism itself the identity, so `f^* γ` is the identity; and the presheaf `Mor(y, y)` of
`𝒯₁` being a sheaf, `γ` itself is. -/
theorem eq_id_of_map_eq_id_of_locallyEssSurj (hFeq : F ⋙ p𝒮₁ = p𝒮₂)
    (hGeq : G ⋙ p𝒮₁ = p𝒯₁) (hgpd₁ : p𝒮₁.IsFiberedInGroupoids) {J : GrothendieckTopology 𝒞}
    (hstack : p𝒯₁.IsStack J) (hloc : LocallyEssSurjOnFibers hgpd₁.isFibered hFeq J)
    (hfst : (TwoFibreProductOver.fst p𝒮₂ p𝒯₁ p𝒮₁ F G).Faithful)
    {U : 𝒞} {y : p𝒯₁.Fiber U} (γ : y ⟶ y)
    (hγ : (Fiber.mapOfComp p𝒯₁ p𝒮₁ G hGeq U).map γ = 𝟙 _) :
    γ = 𝟙 y :=
  eq_id_of_map_eq_id_of_locallyEssSurj_aux hFeq hGeq hgpd₁ hstack hloc hfst γ hγ

/-- **Stacks 06DV**. In a 2-cartesian diagram of categories fibred in groupoids over a site with
`𝒯₁` a stack, if every object of a fibre of `𝒮₁` is locally in the essential image of
`F : 𝒮₂ ⥤ 𝒮₁` and the first projection `𝒮₂ ×_{𝒮₁} 𝒯₁ ⥤ 𝒮₂` is faithful, then `G : 𝒯₁ ⥤ 𝒮₁` is
faithful.

By Stacks 003Z faithfulness may be checked on the fibres; there the fibres of `𝒯₁` are groupoids,
so two morphisms `α`, `β : y ⟶ y'` with `G α = G β` differ by the endomorphism `β ∘ α⁻¹` of `y`,
which `G` sends to the identity and which is therefore the identity by
`CategoryTheory.Functor.eq_id_of_map_eq_id_of_locallyEssSurj`. -/
@[stacks 06DV]
theorem faithful_of_faithful_fst (hFeq : F ⋙ p𝒮₁ = p𝒮₂) (hGeq : G ⋙ p𝒮₁ = p𝒯₁)
    (hgpd₁ : p𝒮₁.IsFiberedInGroupoids) (hgpdT : p𝒯₁.IsFiberedInGroupoids)
    {J : GrothendieckTopology 𝒞} (hstack : p𝒯₁.IsStack J)
    (hloc : LocallyEssSurjOnFibers hgpd₁.isFibered hFeq J)
    (hfst : (TwoFibreProductOver.fst p𝒮₂ p𝒯₁ p𝒮₁ F G).Faithful) :
    G.Faithful :=
  faithful_of_faithful_fst_aux hFeq hGeq hgpd₁ hgpdT hstack hloc hfst

end Faithful

section FaithfulUniv

variable {𝒮₁ : Type u₂} [Category.{v₂} 𝒮₁] {𝒮₂ : Type u₃} [Category.{v₂} 𝒮₂]
  {𝒯₁ : Type u₄} [Category.{v₂} 𝒯₁]
  {p𝒮₁ : 𝒮₁ ⥤ 𝒞} {p𝒮₂ : 𝒮₂ ⥤ 𝒞} {p𝒯₁ : 𝒯₁ ⥤ 𝒞} {F : 𝒮₂ ⥤ 𝒮₁} {G : 𝒯₁ ⥤ 𝒮₁}

/-- The local step of Stacks 06DV, with the morphism universe of `𝒮₁`, `𝒮₂` and `𝒯₁` independent
of that of the site: an endomorphism `γ` of an object `y` of a fibre of `𝒯₁` that `G` sends to
the identity is itself the identity.

Over each member `f : V ⟶ U` of the covering sieve supplied by local essential surjectivity, an
object `z` of `𝒮₂` and an isomorphism `F z ≅ G (f^* y)` are available, so
`(V, z, f^* y, F z ≅ G (f^* y))` is an object `P` of the 2-fibre product and `(𝟙 z, f^* γ)` an
endomorphism of it whose first projection is the identity. Faithfulness of that projection makes
the endomorphism itself the identity, so `f^* γ` is the identity; and the presheaf `Mor(y, y)` of
`𝒯₁` being a sheaf, `γ` itself is. -/
theorem eq_id_of_map_eq_id_of_locallyEssSurj_univ (hFeq : F ⋙ p𝒮₁ = p𝒮₂)
    (hGeq : G ⋙ p𝒮₁ = p𝒯₁) (hgpd₁ : p𝒮₁.IsFiberedInGroupoids) {J : GrothendieckTopology 𝒞}
    (hstack : p𝒯₁.IsStack J) (hloc : LocallyEssSurjOnFibers hgpd₁.isFibered hFeq J)
    (hfst : (TwoFibreProductOver.fst p𝒮₂ p𝒯₁ p𝒮₁ F G).Faithful)
    {U : 𝒞} {y : p𝒯₁.Fiber U} (γ : y ⟶ y)
    (hγ : (Fiber.mapOfComp p𝒯₁ p𝒮₁ G hGeq U).map γ = 𝟙 _) :
    γ = 𝟙 y :=
  eq_id_of_map_eq_id_of_locallyEssSurj_aux hFeq hGeq hgpd₁ hstack hloc hfst γ hγ

/-- **Stacks 06DV**, with the morphism universe of `𝒮₁`, `𝒮₂` and `𝒯₁` independent of that of
the site, as for a stackification. In a 2-cartesian diagram of categories fibred in groupoids over
a site with `𝒯₁` a stack, if every object of a fibre of `𝒮₁` is locally in the essential image of
`F : 𝒮₂ ⥤ 𝒮₁` and the first projection `𝒮₂ ×_{𝒮₁} 𝒯₁ ⥤ 𝒮₂` is faithful, then `G : 𝒯₁ ⥤ 𝒮₁` is
faithful.

By Stacks 003Z faithfulness may be checked on the fibres; there the fibres of `𝒯₁` are groupoids,
so two morphisms `α`, `β : y ⟶ y'` with `G α = G β` differ by the endomorphism `β ∘ α⁻¹` of `y`,
which `G` sends to the identity and which is therefore the identity by
`CategoryTheory.Functor.eq_id_of_map_eq_id_of_locallyEssSurj_univ`. -/
theorem faithful_of_faithful_fst_univ (hFeq : F ⋙ p𝒮₁ = p𝒮₂) (hGeq : G ⋙ p𝒮₁ = p𝒯₁)
    (hgpd₁ : p𝒮₁.IsFiberedInGroupoids) (hgpdT : p𝒯₁.IsFiberedInGroupoids)
    {J : GrothendieckTopology 𝒞} (hstack : p𝒯₁.IsStack J)
    (hloc : LocallyEssSurjOnFibers hgpd₁.isFibered hFeq J)
    (hfst : (TwoFibreProductOver.fst p𝒮₂ p𝒯₁ p𝒮₁ F G).Faithful) :
    G.Faithful :=
  faithful_of_faithful_fst_aux hFeq hGeq hgpd₁ hgpdT hstack hloc hfst

end FaithfulUniv

end Functor

end CategoryTheory

