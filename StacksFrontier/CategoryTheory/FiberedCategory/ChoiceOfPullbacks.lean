module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack
import StacksCore.Tactic.StacksAttribute

/-!
# Fibred categories, a choice of pullbacks, and the pullback functors it induces

Let `p : 𝒳 ⥤ 𝒮` be a functor. It is a *fibred category* (Stacks 02XM) when for every object `x`
of `𝒳` lying over an object `U` of `𝒮` and every morphism `f : V ⟶ U` of `𝒮` some strongly
cartesian morphism `f^* x ⟶ x` lies over `f`. A *choice of pullbacks* for `p` (Stacks 02XN)
picks, for every morphism `f : V ⟶ U` of the base and every object `x` of the fibre `𝒳_U`, such a
strongly cartesian morphism `f^* x ⟶ x`. Such a choice makes every `f : V ⟶ U` act as a genuine
functor `f^* : 𝒳_U ⥤ 𝒳_V` between the fibres, the *pullback functor*: the universal property of
`f^* x' ⟶ x'` factors the composite `f^* x ⟶ x ⟶ x'` uniquely through it, and uniqueness of the
factorisation is what makes the assignment functorial.

## Main definitions

* `CategoryTheory.Functor.IsFibredCategory`, Stacks 02XM, the definition of a fibred category in
  the source's own words;
* `CategoryTheory.Functor.ChoiceOfPullbacks`, Stacks 02XN (1);
* `CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor`, Stacks 02XN (2);
* `CategoryTheory.Functor.chosenPullbacks`, the choice of pullbacks that the axiom of choice
  provides for a fibred category, namely Mathlib's
  `CategoryTheory.Functor.IsPreFibered.pullbackMap`.

## Main results

* `CategoryTheory.Functor.isFibredCategory_iff_isFibered`: Stacks 02XM is Mathlib's
  `CategoryTheory.Functor.IsFibered`, so the whole Mathlib API of fibred categories applies to
  the source's definition;
* `CategoryTheory.Functor.ChoiceOfPullbacks.isFibered`: a functor admitting a choice of pullbacks
  is a fibred category, so the hypothesis of Stacks 02XN costs nothing to drop;
* `CategoryTheory.Functor.nonempty_choiceOfPullbacks_iff_isFibered`: conversely, and by the axiom
  of choice, a fibred category admits a choice of pullbacks;
* `CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctorIdIso` and
  `CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctorCompIso`, the canonical comparisons
  `𝟙^* ≅ 𝟭` and `(f ∘ g)^* ≅ g^* ∘ f^*` that every choice of pullbacks has. A *splitting*
  (Stacks 02XX) asks for these comparisons to be equalities.

## Implementation notes

Mathlib's `CategoryTheory.Functor.IsPreFibered` is a `Prop`: it asserts that cartesian lifts exist,
and `IsPreFibered.pullbackObj`, `IsPreFibered.pullbackMap` extract one such lift by
`Classical.choice`. That single choice is the one used throughout
`StacksFrontier/CategoryTheory/Sites/Descent/IsStack.lean`, where `pullbackFiber` is its object part
and `pullbackFiberIdIso`, `pullbackFiberCompIso` are the two comparisons above; see
`chosenPullbacks_objIdIso` and `chosenPullbacks_objCompIso`. Stacks 02XX quantifies over *all*
choices of pullbacks, so the choice must be available as data rather than extracted from a `Prop`,
and that is what `ChoiceOfPullbacks` provides; `chosenPullbacks` is the bridge back to Mathlib's
canonical choice.

The source assumes `p` is a fibred category before making a choice of pullbacks. Requiring the
chosen lifts to be strongly cartesian, as the source does, already implies that (`isFibered`), so
the structure below takes no hypothesis on `p`.

**Which Mathlib class is Stacks 02XM.** It is `CategoryTheory.Functor.IsFibered`, and *not*
`CategoryTheory.Functor.IsPreFibered`. Both are stated in the SGA 1 VI.6.1 form, with
`CategoryTheory.Functor.IsCartesian` rather than
`CategoryTheory.Functor.IsStronglyCartesian` — which is the notion Stacks 02XM uses and Mathlib
tags `@[stacks 02XK]`. `IsPreFibered` asks only that cartesian lifts exist, and a cartesian
morphism need not be strongly cartesian; `IsFibered` adds that cartesian morphisms compose, and
that is exactly what makes every cartesian morphism strongly cartesian
(`CategoryTheory.Functor.IsFibered.isStronglyCartesian_of_isCartesian`). The converse direction
is `CategoryTheory.Functor.IsFibered.of_exists_isStronglyCartesian`. Mathlib's
`Mathlib/CategoryTheory/FiberedCategory/Fibered.lean` states the equivalence in its module
docstring; `isFibredCategory_iff_isFibered` below is it as a theorem.
-/

@[expose] public section

-- The instance arguments of `IsHomLift` and `IsStronglyCartesian` are only found after unfolding
-- the inclusion of a fibre into `𝒳`.

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

-- `Fiber` and `Fiber.fiberInclusion` are plain `def`s, so goals mentioning an object of a fibre or
-- its image in `𝒳` are not type-correct at `implicit` transparency and `rw`/`simp` refuse them.
attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

/-- **Stacks 02XN (1).**
A *choice of pullbacks* for `p : 𝒳 ⥤ 𝒮` is a choice, for every morphism `f : V ⟶ U` of `𝒮` and
every object `x` of the fibre of `p` over `U`, of an object `f^* x` of the fibre over `V` together
with a strongly cartesian morphism `f^* x ⟶ x` lying over `f`. -/
@[stacks_fixed 02XN "(1)"]
structure ChoiceOfPullbacks (p : 𝒳 ⥤ 𝒮) where
  /-- The chosen pullback `f^* x`, an object of the fibre over `V`. -/
  obj {V U : 𝒮} (f : V ⟶ U) (x : p.Fiber U) : p.Fiber V
  /-- The chosen morphism `f^* x ⟶ x`, lying over `f`. -/
  map {V U : 𝒮} (f : V ⟶ U) (x : p.Fiber U) : (obj f x).1 ⟶ x.1
  /-- The chosen morphism `f^* x ⟶ x` is strongly cartesian over `f`. -/
  isStronglyCartesian {V U : 𝒮} (f : V ⟶ U) (x : p.Fiber U) : p.IsStronglyCartesian f (map f x)

attribute [instance] ChoiceOfPullbacks.isStronglyCartesian

namespace ChoiceOfPullbacks

variable {p : 𝒳 ⥤ 𝒮} (c : p.ChoiceOfPullbacks)

include c in
/-- A functor admitting a choice of pullbacks is a fibred category: the chosen lifts are the
strongly cartesian lifts asked for by `CategoryTheory.Functor.IsFibered`. -/
lemma isFibered : p.IsFibered :=
  IsFibered.of_exists_isStronglyCartesian fun a _ f =>
    ⟨(c.obj f (Fiber.mk (rfl : p.obj a = p.obj a))).1, c.map f _, c.isStronglyCartesian f _⟩

/-! ### The pullback functor

Fix `f : V ⟶ U`. A morphism `α : x ⟶ x'` of the fibre over `U` composes with the chosen lift at
`x` to a morphism `f^* x ⟶ x'` over `f`, which therefore factors uniquely through the chosen lift
at `x'` by a morphism `f^* x ⟶ f^* x'` over `𝟙 V`, i.e. a morphism of the fibre over `V`. -/

/-- The morphism `f^* x ⟶ f^* x'` of the fibre over `V` induced by a morphism `α : x ⟶ x'` of the
fibre over `U`: the unique lift of `𝟙 V` through which `f^* x ⟶ x ⟶ x'` factors. -/
noncomputable def homMap {V U : 𝒮} (f : V ⟶ U) {x x' : p.Fiber U} (α : x ⟶ x') :
    c.obj f x ⟶ c.obj f x' :=
  have : p.IsHomLift (𝟙 U) (Fiber.fiberInclusion.map α) := α.2
  have : p.IsStronglyCartesian f (c.map f x) := c.isStronglyCartesian f x
  have : p.IsStronglyCartesian f (c.map f x') := c.isStronglyCartesian f x'
  have : p.IsHomLift f (c.map f x ≫ Fiber.fiberInclusion.map α) := inferInstance
  ⟨IsStronglyCartesian.map p f (c.map f x') (Category.id_comp f).symm
    (c.map f x ≫ Fiber.fiberInclusion.map α), inferInstance⟩

/-- The chosen lift at `x` followed by a morphism of the fibre lies over `f`. -/
private theorem isHomLift_map_comp {V U : 𝒮} (f : V ⟶ U) {x x' : p.Fiber U} (α : x ⟶ x') :
    p.IsHomLift f (c.map f x ≫ Fiber.fiberInclusion.map α) :=
  have : p.IsHomLift (𝟙 U) (Fiber.fiberInclusion.map α) := α.2
  have : p.IsStronglyCartesian f (c.map f x) := c.isStronglyCartesian f x
  inferInstance

/-- The square defining `CategoryTheory.Functor.ChoiceOfPullbacks.homMap` commutes. -/
@[reassoc (attr := simp)]
lemma homMap_fac {V U : 𝒮} (f : V ⟶ U) {x x' : p.Fiber U} (α : x ⟶ x') :
    Fiber.fiberInclusion.map (c.homMap f α) ≫ c.map f x' =
      c.map f x ≫ Fiber.fiberInclusion.map α :=
  have := c.isHomLift_map_comp f α
  IsStronglyCartesian.fac p f (c.map f x') (Category.id_comp f).symm
    (c.map f x ≫ Fiber.fiberInclusion.map α)

/-- The defining factorisation determines `CategoryTheory.Functor.ChoiceOfPullbacks.homMap`. -/
lemma homMap_uniq {V U : 𝒮} (f : V ⟶ U) {x x' : p.Fiber U} (α : x ⟶ x')
    (β : c.obj f x ⟶ c.obj f x')
    (hβ : Fiber.fiberInclusion.map β ≫ c.map f x' = c.map f x ≫ Fiber.fiberInclusion.map α) :
    β = c.homMap f α :=
  have := c.isHomLift_map_comp f α
  have : p.IsHomLift (𝟙 V) (Fiber.fiberInclusion.map β) := β.2
  Fiber.hom_ext (IsStronglyCartesian.map_uniq p f (c.map f x') (Category.id_comp f).symm
    (c.map f x ≫ Fiber.fiberInclusion.map α) (Fiber.fiberInclusion.map β) hβ)

/-- Base change along `f` of an identity is an identity. -/
@[simp]
lemma homMap_id {V U : 𝒮} (f : V ⟶ U) (x : p.Fiber U) : c.homMap f (𝟙 x) = 𝟙 _ :=
  (c.homMap_uniq f (𝟙 x) (𝟙 _) (by simp [Fiber.fiberInclusion])).symm

/-- Base change along `f` respects composition. -/
@[reassoc]
lemma homMap_comp {V U : 𝒮} (f : V ⟶ U) {x x' x'' : p.Fiber U} (α : x ⟶ x') (β : x' ⟶ x'') :
    c.homMap f (α ≫ β) = c.homMap f α ≫ c.homMap f β :=
  (c.homMap_uniq f _ _ (by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, homMap_fac, homMap_fac_assoc])).symm

/-- **Stacks 02XN (2).**
The *pullback functor* `f^* : 𝒳_U ⥤ 𝒳_V` between the fibres of `p` attached to a morphism
`f : V ⟶ U` of `𝒮` by a choice of pullbacks. -/
@[stacks 02XN "(2)", simps]
noncomputable def pullbackFunctor {V U : 𝒮} (f : V ⟶ U) : p.Fiber U ⥤ p.Fiber V where
  obj x := c.obj f x
  map α := c.homMap f α
  map_id x := c.homMap_id f x
  map_comp α β := c.homMap_comp f α β

/-! ### The canonical comparisons `𝟙^* ≅ 𝟭` and `(f ∘ g)^* ≅ g^* ∘ f^*`

Both comparisons come from the same principle: two objects of a fibre carrying cartesian morphisms
over one and the same morphism of the base into one and the same object are canonically isomorphic
in the fibre (`CategoryTheory.Functor.fiberIsoOfCartesian`). For `𝟙^*` the two competing lifts of
`𝟙 U` at `x` are the chosen one and `𝟙 x`; for `(f ∘ g)^*` they are the chosen lift of `f ∘ g` and
the composite of the chosen lifts of `f` and of `g`, which is strongly cartesian because strongly
cartesian morphisms compose. -/

/-- The chosen pullback along an identity is canonically isomorphic, in the fibre, to the object
itself. -/
noncomputable def objIdIso {U : 𝒮} (x : p.Fiber U) : c.obj (𝟙 U) x ≅ x :=
  have : p.IsHomLift (𝟙 U) (𝟙 x.1) := IsHomLift.id x.2
  fiberIsoOfCartesian (𝟙 U) (c.map (𝟙 U) x) (𝟙 x.1) inferInstance inferInstance

/-- The comparison `𝟙^* x ≅ x` is, in `𝒳`, the chosen lift of `𝟙 U` at `x` itself. -/
@[simp]
lemma fiberInclusion_map_objIdIso_hom {U : 𝒮} (x : p.Fiber U) :
    Fiber.fiberInclusion.map (c.objIdIso x).hom = c.map (𝟙 U) x :=
  have : p.IsHomLift (𝟙 U) (𝟙 x.1) := IsHomLift.id x.2
  (Category.comp_id _).symm.trans
    (fiberIsoOfCartesian_hom_fac (𝟙 U) (c.map (𝟙 U) x) (𝟙 x.1) inferInstance inferInstance)

/-- The chosen pullback of a chosen pullback is canonically isomorphic, in the fibre, to the
chosen pullback along the composite. -/
noncomputable def objCompIso {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (x : p.Fiber U) :
    c.obj (g ≫ f) x ≅ c.obj g (c.obj f x) :=
  fiberIsoOfCartesian (g ≫ f) (c.map (g ≫ f) x) (c.map g (c.obj f x) ≫ c.map f x)
    inferInstance inferInstance

/-- The comparison `(f ∘ g)^* x ≅ g^* (f^* x)` is compatible with the two cartesian lifts of
`f ∘ g` at `x` that it compares. -/
@[reassoc (attr := simp)]
lemma objCompIso_hom_fac {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (x : p.Fiber U) :
    Fiber.fiberInclusion.map (c.objCompIso g f x).hom ≫ c.map g (c.obj f x) ≫ c.map f x =
      c.map (g ≫ f) x :=
  fiberIsoOfCartesian_hom_fac (g ≫ f) (c.map (g ≫ f) x) (c.map g (c.obj f x) ≫ c.map f x)
    inferInstance inferInstance

/-- `CategoryTheory.Functor.ChoiceOfPullbacks.objIdIso` is natural. -/
@[reassoc]
lemma objIdIso_hom_naturality {U : 𝒮} {x x' : p.Fiber U} (α : x ⟶ x') :
    c.homMap (𝟙 U) α ≫ (c.objIdIso x').hom = (c.objIdIso x).hom ≫ α :=
  Fiber.hom_ext <| by
    rw [Functor.map_comp, Functor.map_comp, fiberInclusion_map_objIdIso_hom,
      fiberInclusion_map_objIdIso_hom, homMap_fac]

/-- The canonical isomorphism `𝟙^* ≅ 𝟭`: whatever the choice of pullbacks, the pullback functor
along an identity is naturally isomorphic to the identity functor, because a cartesian morphism
lying over an isomorphism is an isomorphism. -/
noncomputable def pullbackFunctorIdIso (U : 𝒮) : c.pullbackFunctor (𝟙 U) ≅ 𝟭 (p.Fiber U) :=
  NatIso.ofComponents c.objIdIso fun α => c.objIdIso_hom_naturality α

/-- `CategoryTheory.Functor.ChoiceOfPullbacks.objCompIso` is natural. -/
@[reassoc]
lemma objCompIso_hom_naturality {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) {x x' : p.Fiber U}
    (α : x ⟶ x') : c.homMap (g ≫ f) α ≫ (c.objCompIso g f x').hom =
      (c.objCompIso g f x).hom ≫ c.homMap g (c.homMap f α) := by
  refine fiber_hom_ext_of_cartesian (g ≫ f)
    (c.map g (c.obj f x') ≫ c.map f x') inferInstance _ _ ?_
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, objCompIso_hom_fac,
    homMap_fac, Category.assoc, homMap_fac_assoc, homMap_fac, objCompIso_hom_fac_assoc]

/-- The canonical isomorphism `(f ∘ g)^* ≅ g^* ∘ f^*` attached to a choice of pullbacks. -/
noncomputable def pullbackFunctorCompIso {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) :
    c.pullbackFunctor (g ≫ f) ≅ c.pullbackFunctor f ⋙ c.pullbackFunctor g :=
  NatIso.ofComponents (c.objCompIso g f) fun α => c.objCompIso_hom_naturality g f α

end ChoiceOfPullbacks

/-! ### The canonical choice of pullbacks of a fibred category -/

/-- The choice of pullbacks of a fibred category obtained from Mathlib's
`CategoryTheory.Functor.IsPreFibered.pullbackMap`, i.e. the one the axiom of choice provides.
Its object part is `CategoryTheory.Functor.pullbackFiber`. -/
noncomputable def chosenPullbacks (p : 𝒳 ⥤ 𝒮) [p.IsFibered] : p.ChoiceOfPullbacks where
  obj f x := ⟨IsPreFibered.pullbackObj x.2 f, IsPreFibered.pullbackObj_proj x.2 f⟩
  map f x := IsPreFibered.pullbackMap x.2 f
  isStronglyCartesian f _ := IsFibered.isStronglyCartesian_of_isCartesian p f _

/-- The object part of the canonical choice of pullbacks. -/
@[simp]
lemma chosenPullbacks_obj (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {V U : 𝒮} (f : V ⟶ U) (x : p.Fiber U) :
    (chosenPullbacks p).obj f x = pullbackFiber p x f := rfl

/-- The chosen cartesian lift of the canonical choice of pullbacks. -/
@[simp]
lemma chosenPullbacks_map (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {V U : 𝒮} (f : V ⟶ U) (x : p.Fiber U) :
    (chosenPullbacks p).map f x = IsPreFibered.pullbackMap x.2 f := rfl

/-- On morphisms too, the canonical choice of pullbacks induces the base change of
`CategoryTheory.Functor.pullbackFiberHom`: the pullback functors of `chosenPullbacks` are the
pullback functors implicit in `StacksFrontier/CategoryTheory/Sites/Descent/IsStack.lean`. -/
@[simp]
lemma chosenPullbacks_homMap (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {V U : 𝒮} (f : V ⟶ U) {x x' : p.Fiber U}
    (α : x ⟶ x') : (chosenPullbacks p).homMap f α = pullbackFiberHom α f :=
  pullbackFiberHom_uniq α f _ ((chosenPullbacks p).homMap_fac f α)

/-- The comparison `𝟙^* ≅ 𝟭` of the canonical choice of pullbacks is
`CategoryTheory.Functor.pullbackFiberIdIso`. -/
lemma chosenPullbacks_objIdIso (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮} (x : p.Fiber U) :
    (chosenPullbacks p).objIdIso x = pullbackFiberIdIso x := rfl

/-- The comparison `(f ∘ g)^* ≅ g^* ∘ f^*` of the canonical choice of pullbacks is the inverse of
`CategoryTheory.Functor.pullbackFiberCompIso`. -/
lemma chosenPullbacks_objCompIso (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U)
    (x : p.Fiber U) :
    (chosenPullbacks p).objCompIso g f x = (pullbackFiberCompIso x f g).symm := rfl

/-- A functor is a fibred category exactly when it admits a choice of pullbacks. The forward
direction is `CategoryTheory.Functor.ChoiceOfPullbacks.isFibered`; the reverse is the axiom of
choice, in the shape of `CategoryTheory.Functor.chosenPullbacks`. -/
lemma nonempty_choiceOfPullbacks_iff_isFibered (p : 𝒳 ⥤ 𝒮) :
    Nonempty p.ChoiceOfPullbacks ↔ p.IsFibered :=
  ⟨fun ⟨c⟩ => c.isFibered, fun _ => ⟨chosenPullbacks p⟩⟩

/-! ### The definition of a fibred category -/

/-- **Stacks 02XM.** A functor `p : 𝒳 ⥤ 𝒮` is a *fibred category over `𝒮`* when for every object
`x` of `𝒳` lying over an object `U` of `𝒮` and every morphism `f : V ⟶ U` of `𝒮` there exists a
strongly cartesian morphism `f^* x ⟶ x` lying over `f`.

That `φ` lies over `f` is part of `CategoryTheory.Functor.IsStronglyCartesian`, which extends
`CategoryTheory.Functor.IsHomLift`. See the implementation notes for why this is Mathlib's
`CategoryTheory.Functor.IsFibered` and not its `CategoryTheory.Functor.IsPreFibered`. -/
@[stacks 02XM]
def IsFibredCategory (p : 𝒳 ⥤ 𝒮) : Prop :=
  ∀ (U V : 𝒮) (x : 𝒳), p.obj x = U → ∀ f : V ⟶ U,
    ∃ (y : 𝒳) (φ : y ⟶ x), p.IsStronglyCartesian f φ

/-- **Stacks 02XM is Mathlib's `CategoryTheory.Functor.IsFibered`.** Forward, a strongly
cartesian lift of every base morphism makes `p` fibred by
`CategoryTheory.Functor.IsFibered.of_exists_isStronglyCartesian`. Backward, a fibred category has
a cartesian lift of every base morphism by `CategoryTheory.Functor.IsPreFibered.exists_isCartesian`
and every cartesian morphism of a fibred category is strongly cartesian by
`CategoryTheory.Functor.IsFibered.isStronglyCartesian_of_isCartesian`. -/
@[stacks 02XM "the identification with Mathlib's `Functor.IsFibered`",
  sga "1 VI 6.11" "Sufficiency"]
theorem isFibredCategory_iff_isFibered (p : 𝒳 ⥤ 𝒮) : p.IsFibredCategory ↔ p.IsFibered := by
  refine ⟨fun h => IsFibered.of_exists_isStronglyCartesian fun a R f => h (p.obj a) R a rfl f,
    fun _ U V x hx f => ?_⟩
  obtain ⟨y, φ, _⟩ := IsPreFibered.exists_isCartesian p hx f
  exact ⟨y, φ, IsFibered.isStronglyCartesian_of_isCartesian p f φ⟩

end CategoryTheory.Functor

-- Mathlib's class of fibred categories is Stacks 02XM, in the equivalent SGA 1 VI.6.1 form; the
-- identification is `CategoryTheory.Functor.isFibredCategory_iff_isFibered`.
add_to_stacks 02XM "Mathlib's SGA 1 VI.6.1 form of the definition, identified with the Stacks \
form by `CategoryTheory.Functor.isFibredCategory_iff_isFibered`"
  CategoryTheory.Functor.IsFibered
