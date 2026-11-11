module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import StacksCore.Tactic.StacksAttribute

/-!
# The pullback pseudofunctor of a fibred category (Stacks 02XO)

Let `p : 𝒳 ⥤ 𝒮` be a fibred category, in the sense of Mathlib's
`CategoryTheory.Functor.IsFibered`. Choosing, for every `f : V ⟶ U` in `𝒮` and every object `a`
of the fibre `p.Fiber U`, a strongly cartesian lift of `f` with target `a` — which is what
`IsPreFibered.pullbackObj` and `IsPreFibered.pullbackMap` provide — gives a pullback functor
`f* : p.Fiber U ⥤ p.Fiber V`, and these assemble into a pseudofunctor
`LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat`.

The engine of the construction is the essential uniqueness of strongly cartesian
factorisations, isolated here as `CartStruct p f F`: the data of a natural family of strongly
cartesian projections `F a ⟶ a` lying over `f`, for a functor `F` between fibres. Any two
cartesian structures over the same `f` induce a *unique* natural isomorphism between the
underlying functors (`cmpIso`), and the unitor `(𝟙 U)* ≅ 𝟭` and compositor
`(g ∘ f)* ≅ f* ⋙ g*` are exactly the comparisons attached to the two evident cartesian
structures. The three pseudofunctor coherences follow from the same uniqueness.

Mathlib has the converse construction, recovering a fibred category from a pseudofunctor
(`Pseudofunctor.CoGrothendieck`), but not this direction. The pullbacks used here are the
specific choice supplied by `IsPreFibered`; Stacks 02XO itself, for an arbitrary choice of
pullbacks, is `CategoryTheory.Functor.ChoiceOfPullbacks.pseudofunctor` and
`CategoryTheory.Functor.ChoiceOfPullbacks.existsUnique_compIso`
(`StacksFrontier/CategoryTheory/FiberedCategory/FiberedInGroupoidsPseudofunctor.lean`).
`pbMapComp_uniq` records that the compositor here is the unique natural isomorphism compatible
with the chosen cartesian lifts.
-/

@[expose] public section

-- Load-bearing: the `CartStruct` projections and `fiberPullback` are compared past their
-- reducibility setting throughout. Removing this option gives 28 errors.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Functor.IsFibered

open Opposite


universe v₁ u₁ v₂ u₂
variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-!
## A cartesian projection structure on a functor between fibres

A `CartStruct p f F`, for `F : p.Fiber U ⥤ p.Fiber W` and `f : W ⟶ U`, is a natural family
of strongly cartesian projections `F.obj a ⟶ a` lying over `f`.  Any two such structures
over the same `f` induce a *unique* natural isomorphism (`cmpIso`); this is the essential
uniqueness of the pullback functor and is the engine of Stacks 02XO.
-/

/-- The data exhibiting `F : p.Fiber U ⥤ p.Fiber W` as a pullback functor along `f : W ⟶ U`: for
every object `a` of `p.Fiber U` a projection `F.obj a ⟶ a` in `𝒳` that is strongly cartesian
over `f`, natural in `a`. -/
structure CartStruct (p : 𝒳 ⥤ 𝒮) {U W : 𝒮} (f : W ⟶ U)
    (F : p.Fiber U ⥤ p.Fiber W) where
  /-- The projection `F.obj a ⟶ a` in `𝒳`, for each object `a` of `p.Fiber U`. -/
  proj : (a : p.Fiber U) → ((Fiber.fiberInclusion.obj (F.obj a)) ⟶ Fiber.fiberInclusion.obj a)
  /-- Each projection `proj a` is strongly cartesian over `f`. -/
  isCart : ∀ a, p.IsStronglyCartesian f (proj a)
  /-- The projections are natural in `a`. -/
  naturality : ∀ {a b : p.Fiber U} (ψ : a ⟶ b),
    Fiber.fiberInclusion.map (F.map ψ) ≫ proj b = proj a ≫ Fiber.fiberInclusion.map ψ

namespace CartStruct

/-- The underlying comparison morphism, built from the universal property. -/
noncomputable def cmpUnderlying {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U W : 𝒮} {f : W ⟶ U}
    {F G : p.Fiber U ⥤ p.Fiber W} (cF : CartStruct p f F) (cG : CartStruct p f G)
    (a : p.Fiber U) :
    Fiber.fiberInclusion.obj (F.obj a) ⟶ Fiber.fiberInclusion.obj (G.obj a) :=
  letI := cG.isCart a
  letI := (cF.isCart a).toIsHomLift
  IsStronglyCartesian.map p f (cG.proj a) (by simp : f = 𝟙 W ≫ f) (cF.proj a)

/-- The comparison morphism is *vertical*: it lies over `𝟙 W`, since it was obtained from the
universal property with the factorisation `f = 𝟙 W ≫ f`. Made an instance just below, so that the
`IsStronglyCartesian` API accepts it as an argument. -/
theorem cmpUnderlying_isHomLift {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U W : 𝒮} {f : W ⟶ U}
    {F G : p.Fiber U ⥤ p.Fiber W} (cF : CartStruct p f F) (cG : CartStruct p f G)
    (a : p.Fiber U) : p.IsHomLift (𝟙 W) (cmpUnderlying cF cG a) := by
  have := cG.isCart a
  have := (cF.isCart a).toIsHomLift
  unfold cmpUnderlying
  infer_instance

attribute [instance] cmpUnderlying_isHomLift

/-- The defining triangle of the comparison morphism: composing it with the projection of `cG`
recovers the projection of `cF`. This equation is what every coherence proof below rewrites
with. -/
theorem cmpUnderlying_fac {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U W : 𝒮} {f : W ⟶ U}
    {F G : p.Fiber U ⥤ p.Fiber W} (cF : CartStruct p f F) (cG : CartStruct p f G)
    (a : p.Fiber U) : cmpUnderlying cF cG a ≫ cG.proj a = cF.proj a := by
  have := cG.isCart a
  have := (cF.isCart a).toIsHomLift
  unfold cmpUnderlying
  exact IsStronglyCartesian.fac _ _ _ _ _

/-- The comparison morphism is the *only* vertical morphism satisfying the triangle of
`cmpUnderlying_fac`. This is the universal property of the strongly cartesian projection
`cG.proj a`, and it is the source of the essential uniqueness of the pullback functor. -/
theorem cmpUnderlying_uniq {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U W : 𝒮} {f : W ⟶ U}
    {F G : p.Fiber U ⥤ p.Fiber W} (cF : CartStruct p f F) (cG : CartStruct p f G)
    (a : p.Fiber U) (χ : Fiber.fiberInclusion.obj (F.obj a) ⟶ Fiber.fiberInclusion.obj (G.obj a))
    [p.IsHomLift (𝟙 W) χ] (hχ : χ ≫ cG.proj a = cF.proj a) : χ = cmpUnderlying cF cG a := by
  have := cG.isCart a
  have := (cF.isCart a).toIsHomLift
  unfold cmpUnderlying
  exact IsStronglyCartesian.map_uniq p f (cG.proj a) (by simp) (cF.proj a) χ hχ

/-- Reflexivity of the comparison: comparing a cartesian structure with itself gives the identity.
Together with `cmpUnderlying_comp` this is what makes the components of `cmpIso` invertible. -/
theorem cmpUnderlying_id {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U W : 𝒮} {f : W ⟶ U}
    {F : p.Fiber U ⥤ p.Fiber W} (cF : CartStruct p f F) (a : p.Fiber U) :
    cmpUnderlying cF cF a = 𝟙 _ := by
  have : p.IsHomLift (𝟙 W) (𝟙 (Fiber.fiberInclusion.obj (F.obj a))) :=
    IsHomLift.id (F.obj a).2
  symm
  apply cmpUnderlying_uniq
  simp

/-- Transitivity of the comparison: the comparison from `cF` to `cG` followed by the one from `cG`
to `cH` is the comparison from `cF` to `cH`, both being vertical and satisfying the same
triangle. -/
theorem cmpUnderlying_comp {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U W : 𝒮} {f : W ⟶ U}
    {F G H : p.Fiber U ⥤ p.Fiber W} (cF : CartStruct p f F) (cG : CartStruct p f G)
    (cH : CartStruct p f H) (a : p.Fiber U) :
    cmpUnderlying cF cG a ≫ cmpUnderlying cG cH a = cmpUnderlying cF cH a := by
  refine cmpUnderlying_uniq cF cH a _ ?_
  rw [Category.assoc, cmpUnderlying_fac, cmpUnderlying_fac]

/-- Naturality of the underlying comparison. -/
theorem cmpUnderlying_natural {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U W : 𝒮} {f : W ⟶ U}
    {F G : p.Fiber U ⥤ p.Fiber W} (cF : CartStruct p f F) (cG : CartStruct p f G)
    {a b : p.Fiber U} (ψ : a ⟶ b) :
    Fiber.fiberInclusion.map (F.map ψ) ≫ cmpUnderlying cF cG b =
      cmpUnderlying cF cG a ≫ Fiber.fiberInclusion.map (G.map ψ) := by
  have := cG.isCart b
  refine IsStronglyCartesian.ext p f (cG.proj b) (g := 𝟙 W) ?_
  rw [Category.assoc, cmpUnderlying_fac, cF.naturality ψ, Category.assoc,
    cG.naturality ψ, ← Category.assoc, cmpUnderlying_fac]

/-- The comparison as a fibre morphism. -/
noncomputable def cmpMor {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U W : 𝒮} {f : W ⟶ U}
    {F G : p.Fiber U ⥤ p.Fiber W} (cF : CartStruct p f F) (cG : CartStruct p f G)
    (a : p.Fiber U) : F.obj a ⟶ G.obj a :=
  Fiber.homMk p W (cmpUnderlying cF cG a)

/-- `cmpMor` is nothing but `cmpUnderlying` regarded in the fibre: its image under
`Fiber.fiberInclusion` is the underlying comparison morphism. This is the bridge that lets the
`cmpUnderlying` equations be applied to statements about `cmpIso`. -/
theorem cmpMor_incl {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U W : 𝒮} {f : W ⟶ U}
    {F G : p.Fiber U ⥤ p.Fiber W} (cF : CartStruct p f F) (cG : CartStruct p f G)
    (a : p.Fiber U) :
    Fiber.fiberInclusion.map (cmpMor cF cG a) = cmpUnderlying cF cG a := by
  unfold cmpMor
  exact Fiber.fiberInclusion_homMk _ _ _

/-- Comparing `cF` with `cG` and then `cG` back with `cF` gives the identity: by
`cmpUnderlying_comp` the composite is the comparison of `cF` with itself, which is the identity
by `cmpUnderlying_id`. This is what makes the components of `cmpIso` invertible. -/
theorem cmpMor_comp_cmpMor_id {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U W : 𝒮} {f : W ⟶ U}
    {F G : p.Fiber U ⥤ p.Fiber W} (cF : CartStruct p f F) (cG : CartStruct p f G)
    (a : p.Fiber U) : cmpMor cF cG a ≫ cmpMor cG cF a = 𝟙 (F.obj a) := by
  apply Fiber.fiberInclusion.map_injective
  rw [Functor.map_comp, cmpMor_incl, cmpMor_incl, cmpUnderlying_comp, cmpUnderlying_id]
  exact (CategoryTheory.Functor.map_id _ _).symm

/-- The canonical natural isomorphism `F ≅ G` induced by two cartesian structures over the
same `f`.  This is the uniqueness of the pullback functor. -/
noncomputable def cmpIso {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U W : 𝒮} {f : W ⟶ U}
    {F G : p.Fiber U ⥤ p.Fiber W} (cF : CartStruct p f F) (cG : CartStruct p f G) : F ≅ G :=
  NatIso.ofComponents
    (fun a => { hom := cmpMor cF cG a
                inv := cmpMor cG cF a
                hom_inv_id := cmpMor_comp_cmpMor_id cF cG a
                inv_hom_id := cmpMor_comp_cmpMor_id cG cF a })
    (by
      intro a b ψ
      apply Fiber.fiberInclusion.map_injective
      rw [Functor.map_comp, Functor.map_comp, cmpMor_incl, cmpMor_incl]
      exact cmpUnderlying_natural cF cG ψ)

/-- The underlying `𝒳`-morphism of a component of `cmpIso` is the underlying comparison
morphism. This is the bridge from statements about `cmpIso` to the `cmpUnderlying` equations. -/
theorem cmpIso_hom_app_incl {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U W : 𝒮} {f : W ⟶ U}
    {F G : p.Fiber U ⥤ p.Fiber W} (cF : CartStruct p f F) (cG : CartStruct p f G)
    (a : p.Fiber U) :
    Fiber.fiberInclusion.map ((cmpIso cF cG).hom.app a) = cmpUnderlying cF cG a := by
  simp only [cmpIso, NatIso.ofComponents_hom_app]
  exact cmpMor_incl _ _ _

/-- The underlying `𝒳`-morphism of a component of `(cmpIso cF cG).inv` is the comparison run
the other way, from `cG` to `cF`. -/
theorem cmpIso_inv_app_incl {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U W : 𝒮} {f : W ⟶ U}
    {F G : p.Fiber U ⥤ p.Fiber W} (cF : CartStruct p f F) (cG : CartStruct p f G)
    (a : p.Fiber U) :
    Fiber.fiberInclusion.map ((cmpIso cF cG).inv.app a) = cmpUnderlying cG cF a := by
  simp only [cmpIso, NatIso.ofComponents_inv_app]
  exact cmpMor_incl _ _ _

/-- Composition of cartesian structures: if `F` has one over `f` and `G` over `g`, then
`F ⋙ G` has one over `g ≫ f`. -/
noncomputable def comp {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U V W : 𝒮} {f : V ⟶ U} {g : W ⟶ V}
    {F : p.Fiber U ⥤ p.Fiber V} {G : p.Fiber V ⥤ p.Fiber W}
    (cF : CartStruct p f F) (cG : CartStruct p g G) :
    CartStruct p (g ≫ f) (F ⋙ G) where
  proj a := cG.proj (F.obj a) ≫ cF.proj a
  isCart a := by
    have := cG.isCart (F.obj a)
    have := cF.isCart a
    exact IsStronglyCartesian.comp p
  naturality {a b} ψ := by
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [← Category.assoc, cG.naturality (F.map ψ), Category.assoc, cF.naturality ψ,
      ← Category.assoc]

end CartStruct

open CartStruct

/-! ## The pullback functor `f*` and its canonical cartesian structure -/

/-- Action of `f*` on a morphism `ψ` of `p.Fiber U`, via the universal property. -/
noncomputable def fiberPullbackMap {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U V : 𝒮} (f : V ⟶ U)
    {a b : p.Fiber U} (ψ : a ⟶ b) :
    (Fiber.mk (IsPreFibered.pullbackObj_proj a.2 f) : p.Fiber V) ⟶
      Fiber.mk (IsPreFibered.pullbackObj_proj b.2 f) := by
  have hf' : f = 𝟙 V ≫ f := by simp
  have hlift : p.IsHomLift f
      (IsPreFibered.pullbackMap a.2 f ≫ Fiber.fiberInclusion.map ψ) := by
    have h2 : p.IsHomLift (f ≫ 𝟙 U)
        (IsPreFibered.pullbackMap a.2 f ≫ Fiber.fiberInclusion.map ψ) :=
      IsHomLift.comp p f (𝟙 U) (IsPreFibered.pullbackMap a.2 f) (Fiber.fiberInclusion.map ψ)
    simpa using h2
  exact Fiber.homMk p V
    (IsStronglyCartesian.map p f (IsPreFibered.pullbackMap b.2 f) hf'
      (IsPreFibered.pullbackMap a.2 f ≫ Fiber.fiberInclusion.map ψ))

/-- The underlying `𝒳`-morphism of `fiberPullbackMap f ψ` is the morphism supplied by the
universal property of the chosen cartesian lift of `f` at `b`, applied to
`pullbackMap a.2 f ≫ ψ`. -/
theorem fiberPullbackMap_incl {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U V : 𝒮} (f : V ⟶ U)
    {a b : p.Fiber U} (ψ : a ⟶ b) (hf' : f = 𝟙 V ≫ f) :
    Fiber.fiberInclusion.map (fiberPullbackMap f ψ) =
      IsStronglyCartesian.map p f (IsPreFibered.pullbackMap b.2 f) hf'
        (IsPreFibered.pullbackMap a.2 f ≫ Fiber.fiberInclusion.map ψ) := by
  unfold fiberPullbackMap
  simp [Fiber.fiberInclusion_homMk]

/-- The chosen cartesian projections `pullbackMap · f` are natural in the fibre object: the square
they form with `ψ` and `fiberPullbackMap f ψ` commutes. This is the `naturality` field of
`cartPullback`. -/
theorem fiberPullbackMap_comm {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U V : 𝒮} (f : V ⟶ U)
    {a b : p.Fiber U} (ψ : a ⟶ b) :
    Fiber.fiberInclusion.map (fiberPullbackMap f ψ) ≫ IsPreFibered.pullbackMap b.2 f =
      IsPreFibered.pullbackMap a.2 f ≫ Fiber.fiberInclusion.map ψ := by
  rw [fiberPullbackMap_incl f ψ (by simp)]
  exact IsStronglyCartesian.fac _ _ _ _ _

/-- Definition 3: the pullback functor `f* : p.Fiber U ⥤ p.Fiber V`. -/
noncomputable def fiberPullback {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U V : 𝒮} (f : V ⟶ U) :
    p.Fiber U ⥤ p.Fiber V where
  obj a := Fiber.mk (IsPreFibered.pullbackObj_proj a.2 f)
  map ψ := fiberPullbackMap f ψ
  map_id a := by
    apply Fiber.fiberInclusion.map_injective
    rw [fiberPullbackMap_incl f (𝟙 a) (by simp)]
    have h1 : p.IsHomLift (𝟙 V) (𝟙 (IsPreFibered.pullbackObj a.2 f)) :=
      IsHomLift.id (IsPreFibered.pullbackObj_proj a.2 f)
    refine (IsStronglyCartesian.map_uniq p f (IsPreFibered.pullbackMap a.2 f) (by simp) _
      (𝟙 _) ?_).symm
    rw [Category.id_comp, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  map_comp {a b c} ψ ψ' := by
    apply Fiber.fiberInclusion.map_injective
    rw [fiberPullbackMap_incl f (ψ ≫ ψ') (by simp)]
    have hcomp : p.IsHomLift (𝟙 V)
        (Fiber.fiberInclusion.map (fiberPullbackMap f ψ) ≫
          Fiber.fiberInclusion.map (fiberPullbackMap f ψ')) :=
      IsHomLift.comp_of_lift_id p V
        (Fiber.fiberInclusion.map (fiberPullbackMap f ψ))
        (Fiber.fiberInclusion.map (fiberPullbackMap f ψ'))
    refine (IsStronglyCartesian.map_uniq p f (IsPreFibered.pullbackMap c.2 f) (by simp) _
      (Fiber.fiberInclusion.map (fiberPullbackMap f ψ) ≫
        Fiber.fiberInclusion.map (fiberPullbackMap f ψ')) ?_).symm
    rw [Category.assoc, fiberPullbackMap_comm f ψ', ← Category.assoc,
      fiberPullbackMap_comm f ψ, Category.assoc, Functor.map_comp]

/-- On objects, `f*` sends `a` to the source of the chosen strongly cartesian lift of `f`
ending at `a` (a correctness statement for Definition 3). -/
theorem fiberPullback_obj {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U V : 𝒮} (f : V ⟶ U) (a : p.Fiber U) :
    (fiberPullback f).obj a = Fiber.mk (IsPreFibered.pullbackObj_proj a.2 f) := rfl

/-- The canonical cartesian structure on `f*` over `f`, with projections `pullbackMap`. -/
noncomputable def cartPullback {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U V : 𝒮} (f : V ⟶ U) :
    CartStruct p f (fiberPullback f) where
  proj a := IsPreFibered.pullbackMap a.2 f
  isCart _ := inferInstance
  naturality ψ := fiberPullbackMap_comm f ψ

/-- Cartesian structure on the identity functor over `𝟙 U` (projections `𝟙`). -/
noncomputable def cartId {p : 𝒳 ⥤ 𝒮} [p.IsFibered] (U : 𝒮) :
    CartStruct p (𝟙 U) (𝟭 (p.Fiber U)) where
  proj a := 𝟙 (Fiber.fiberInclusion.obj a)
  isCart a := by
    have : p.IsHomLift (𝟙 U) (𝟙 (Fiber.fiberInclusion.obj a)) := IsHomLift.id a.2
    exact IsStronglyCartesian.of_isIso p (𝟙 U) (𝟙 (Fiber.fiberInclusion.obj a))
  naturality {a b} ψ := by simp

/-- Cartesian structure on `f* ⋙ g*` over `g ≫ f`. -/
noncomputable def cartComp {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U V W : 𝒮} (f : V ⟶ U) (g : W ⟶ V) :
    CartStruct p (g ≫ f) (fiberPullback f ⋙ fiberPullback g) :=
  CartStruct.comp (cartPullback f) (cartPullback g)

/-- The projections of `cartPullback f` are the chosen cartesian lifts of `f`. -/
theorem cartPullback_proj {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U V : 𝒮} (f : V ⟶ U) (a : p.Fiber U) :
    (cartPullback f).proj a = IsPreFibered.pullbackMap a.2 f := rfl

/-- The comparison from the chosen pullback along an identity to the identity functor is the
chosen cartesian lift of that identity: the triangle defining it has `𝟙` on the right. -/
theorem cmpUnderlying_cartPullback_cartId {p : 𝒳 ⥤ 𝒮} [p.IsFibered] (U : 𝒮) (a : p.Fiber U) :
    cmpUnderlying (cartPullback (𝟙 U)) (cartId U) a = IsPreFibered.pullbackMap a.2 (𝟙 U) := by
  have h := cmpUnderlying_fac (cartPullback (𝟙 U)) (cartId U) a
  rwa [show (cartId U).proj a = 𝟙 _ from rfl, Category.comp_id] at h

/-! ## The pullback pseudofunctor -/

/-- Object part: `U ↦ Cat.of (p.Fiber U)`. -/
noncomputable def pbObj (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (U : LocallyDiscrete 𝒮ᵒᵖ) : Cat :=
  Cat.of (p.Fiber U.as.unop)

/-- 1-cell part: `φ ↦ (φ.unop)*`. -/
noncomputable def pbMap (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U V : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V) :
    pbObj p U ⟶ pbObj p V :=
  Cat.Hom.ofFunctor (fiberPullback φ.as.unop)

/-- The 1-cell `pbMap p φ` acts on morphisms by `fiberPullbackMap`. -/
theorem pbMap_map (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U V : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V)
    {a b : ↑(pbObj p U)} (ψ : a ⟶ b) :
    (pbMap p φ).toFunctor.map ψ = fiberPullbackMap φ.as.unop ψ := rfl

/-- The unitor `(𝟙 U)* ≅ 𝟭 (p.Fiber U)`, the canonical isomorphism coming from the uniqueness of
strongly cartesian factorisations (Stacks 02XO (2) for the choice of pullbacks of `IsPreFibered`).
-/
noncomputable def pbMapId (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (U : LocallyDiscrete 𝒮ᵒᵖ) :
    pbMap p (𝟙 U) ≅ 𝟙 (pbObj p U) :=
  Cat.Hom.isoMk (cmpIso (cartPullback (𝟙 U.as.unop)) (cartId U.as.unop))

/-- The compositor `(g ≫ f)* ≅ f* ⋙ g*`, the canonical isomorphism compatible with the chosen
cartesian lifts; `pbMapComp_uniq` shows it is the only such isomorphism (Stacks 02XO (1) for the
choice of pullbacks of `IsPreFibered`). -/
@[sga "4 VI 6.1.2" "(6.1.2.1)"]
noncomputable def pbMapComp (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
    {U V W : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V) (γ : V ⟶ W) :
    pbMap p (φ ≫ γ) ≅ pbMap p φ ≫ pbMap p γ :=
  Cat.Hom.isoMk (cmpIso (cartPullback (φ ≫ γ).as.unop) (cartComp φ.as.unop γ.as.unop))

/-- Component description of the unitor. -/
theorem pbMapId_hom_app (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (U : LocallyDiscrete 𝒮ᵒᵖ)
    (X : ↑(pbObj p U)) :
    Fiber.fiberInclusion.map ((pbMapId p U).hom.toNatTrans.app X) =
      cmpUnderlying (cartPullback (𝟙 U.as.unop)) (cartId U.as.unop) X :=
  cmpIso_hom_app_incl _ _ X

/-- Component description of the compositor. -/
theorem pbMapComp_hom_app (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
    {U V W : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V) (γ : V ⟶ W) (X : ↑(pbObj p U)) :
    Fiber.fiberInclusion.map ((pbMapComp p φ γ).hom.toNatTrans.app X) =
      cmpUnderlying (cartPullback (φ ≫ γ).as.unop) (cartComp φ.as.unop γ.as.unop) X :=
  cmpIso_hom_app_incl _ _ X

/-- Component description of the *inverse* of the compositor: it is the comparison run the other
way, from `cartComp φ γ` to `cartPullback (φ ≫ γ)`. The coherence proofs need this direction as
well as `pbMapComp_hom_app`. -/
theorem pbMapComp_inv_app (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
    {U V W : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V) (γ : V ⟶ W) (X : ↑(pbObj p U)) :
    Fiber.fiberInclusion.map ((pbMapComp p φ γ).inv.toNatTrans.app X) =
      cmpUnderlying (cartComp φ.as.unop γ.as.unop) (cartPullback (φ ≫ γ).as.unop) X :=
  cmpIso_inv_app_incl _ _ X

/-- Extensionality for fibre morphisms into a chosen pullback object: they are determined by
composition with the cartesian projection. -/
theorem fiberHom_ext_pullback {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U V : 𝒮} (g : V ⟶ U)
    {c : p.Fiber V} {X : p.Fiber U}
    (m₁ m₂ : c ⟶ (fiberPullback g).obj X)
    (h : Fiber.fiberInclusion.map m₁ ≫ IsPreFibered.pullbackMap X.2 g =
         Fiber.fiberInclusion.map m₂ ≫ IsPreFibered.pullbackMap X.2 g) : m₁ = m₂ := by
  apply Fiber.fiberInclusion.map_injective
  exact IsStronglyCartesian.ext p g (IsPreFibered.pullbackMap X.2 g) (g := 𝟙 V) h

/-! ## Coherences (Stacks 02XO) -/

/-- Transport of a chosen cartesian projection along an equality `g = g'` of base morphisms: the
two projections differ only by the `eqToHom` identifying their sources. The coherences need this
because `(f ≫ g) ≫ h` and `f ≫ (g ≫ h)` are equal but not syntactically identical, so their
chosen pullback objects are only equal up to `eqToHom`. -/
theorem pullbackMap_congr {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U V : 𝒮} (X : p.Fiber U)
    {g g' : V ⟶ U} (h : g = g') :
    IsPreFibered.pullbackMap X.2 g
      = eqToHom (by rw [h]) ≫ IsPreFibered.pullbackMap X.2 g' := by
  subst h
  simp

/-- The associativity coherence of the pullback pseudofunctor (the `map₂_associator` field of
`pullbackPseudofunctor`): the two ways of comparing `((f ≫ g) ≫ h)*` with `f* ⋙ g* ⋙ h*`,
through `pbMapComp` and the bicategorical associator, agree. Both sides are vertical morphisms
into the chosen pullback along `f ≫ g ≫ h`, so `fiberHom_ext_pullback` reduces this to the
triangle `cmpUnderlying_fac`. -/
theorem pbMapComp_associator (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
    {b₀ b₁ b₂ b₃ : LocallyDiscrete 𝒮ᵒᵖ} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃) :
    (pbMapComp p (f ≫ g) h).hom ≫
        Bicategory.whiskerRight (pbMapComp p f g).hom (pbMap p h) ≫
          (Bicategory.associator (pbMap p f) (pbMap p g) (pbMap p h)).hom ≫
            Bicategory.whiskerLeft (pbMap p f) (pbMapComp p g h).inv ≫
              (pbMapComp p f (g ≫ h)).inv =
      eqToHom (by rw [Category.assoc]) := by
  apply Cat.Hom₂.ext
  ext X
  apply fiberHom_ext_pullback (f ≫ g ≫ h).as.unop
  simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
    Cat.associator_hom_app, Cat.Hom₂.eqToHom_toNatTrans, CategoryTheory.eqToHom_app]
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_map]
  simp only [eqToHom_refl, Category.id_comp, Category.assoc]
  -- Move the chosen lift along `(f ≫ g) ≫ h` on the right to the one along `f ≫ g ≫ h`, then
  -- cancel the `(f, g ≫ h)`-comparison against its triangle.
  rw [← pullbackMap_congr X (show ((f ≫ g) ≫ h).as.unop = (f ≫ g ≫ h).as.unop by
        rw [Category.assoc]),
    pbMapComp_hom_app, pbMap_map, ← cartPullback_proj (f ≫ g ≫ h).as.unop X,
    pbMapComp_inv_app p f (g ≫ h), cmpUnderlying_fac,
    show (cartComp f.as.unop (g ≫ h).as.unop).proj X
      = (cartPullback (g ≫ h).as.unop).proj ((pbMap p f).toFunctor.obj X)
          ≫ IsPreFibered.pullbackMap X.2 f.as.unop from rfl]
  -- Cancel the `(g, h)`-comparison against its triangle, and expand what is left of it.
  rw [pbMapComp_inv_app p g h,
    ← Category.assoc (cmpUnderlying (cartComp g.as.unop h.as.unop)
      (cartPullback (g ≫ h).as.unop) ((pbMap p f).toFunctor.obj X)),
    cmpUnderlying_fac,
    show (cartComp g.as.unop h.as.unop).proj ((pbMap p f).toFunctor.obj X)
      = IsPreFibered.pullbackMap ((fiberPullback g.as.unop).obj
            ((pbMap p f).toFunctor.obj X)).2 h.as.unop
          ≫ IsPreFibered.pullbackMap ((pbMap p f).toFunctor.obj X).2 g.as.unop from rfl]
  -- Slide the `h`-pullback of the `(f, g)`-comparison past the chosen lift of `h`.
  rw [Category.assoc (IsPreFibered.pullbackMap ((fiberPullback g.as.unop).obj
        ((pbMap p f).toFunctor.obj X)).2 h.as.unop),
    ← Category.assoc (Fiber.fiberInclusion.map
        (fiberPullbackMap h.as.unop ((pbMapComp p f g).hom.toNatTrans.app X)))
      (IsPreFibered.pullbackMap ((fiberPullback g.as.unop).obj
        ((pbMap p f).toFunctor.obj X)).2 h.as.unop),
    fiberPullbackMap_comm h.as.unop, pbMapComp_hom_app]
  -- Telescope the `(f, g)`- and then the `(f ≫ g, h)`-comparison against their triangles.
  rw [show IsPreFibered.pullbackMap ((pbMap p f).toFunctor.obj X).2 g.as.unop
          ≫ IsPreFibered.pullbackMap X.2 f.as.unop
      = (cartComp f.as.unop g.as.unop).proj X from rfl,
    Category.assoc (IsPreFibered.pullbackMap ((fiberPullback (f ≫ g).as.unop).obj X).2 h.as.unop),
    cmpUnderlying_fac,
    show IsPreFibered.pullbackMap ((fiberPullback (f ≫ g).as.unop).obj X).2 h.as.unop
          ≫ (cartPullback (f ≫ g).as.unop).proj X
      = (cartComp (f ≫ g).as.unop h.as.unop).proj X from rfl,
    cmpUnderlying_fac]
  rfl

/-- The left unitor coherence of the pullback pseudofunctor (the `map₂_left_unitor` field of
`pullbackPseudofunctor`): the compositor at `(𝟙 b₀, f)`, whiskered with the unitor
`(𝟙 b₀)* ≅ 𝟭`, is the comparison induced by `𝟙 b₀ ≫ f = f`. -/
theorem pbMapComp_left_unitor (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
    {b₀ b₁ : LocallyDiscrete 𝒮ᵒᵖ} (f : b₀ ⟶ b₁) :
    (pbMapComp p (𝟙 b₀) f).hom ≫
        Bicategory.whiskerRight (pbMapId p b₀).hom (pbMap p f) ≫
          (Bicategory.leftUnitor (pbMap p f)).hom =
      eqToHom (by rw [Category.id_comp]) := by
  apply Cat.Hom₂.ext
  ext X
  apply fiberHom_ext_pullback f.as.unop
  simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.leftUnitor_hom_app, CategoryTheory.eqToHom_app]
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_map, pbMapComp_hom_app]
  simp only [eqToHom_refl, Category.id_comp]
  rw [pbMap_map, fiberPullbackMap_comm, pbMapId_hom_app,
    cmpUnderlying_cartPullback_cartId,
    show IsPreFibered.pullbackMap ((fiberPullback (𝟙 b₀ : b₀ ⟶ b₀).as.unop).obj X).2 f.as.unop ≫
        IsPreFibered.pullbackMap X.2 (𝟙 b₀.as.unop)
      = (cartComp (𝟙 b₀ : b₀ ⟶ b₀).as.unop f.as.unop).proj X from rfl,
    cmpUnderlying_fac]
  change IsPreFibered.pullbackMap X.2 (𝟙 b₀ ≫ f).as.unop = _
  rw [pullbackMap_congr X (show ((𝟙 b₀ ≫ f).as.unop) = f.as.unop by simp)]

/-- The right unitor coherence of the pullback pseudofunctor (the `map₂_right_unitor` field of
`pullbackPseudofunctor`): the compositor at `(f, 𝟙 b₁)`, whiskered with the unitor
`(𝟙 b₁)* ≅ 𝟭`, is the comparison induced by `f ≫ 𝟙 b₁ = f`. -/
theorem pbMapComp_right_unitor (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
    {b₀ b₁ : LocallyDiscrete 𝒮ᵒᵖ} (f : b₀ ⟶ b₁) :
    (pbMapComp p f (𝟙 b₁)).hom ≫
        Bicategory.whiskerLeft (pbMap p f) (pbMapId p b₁).hom ≫
          (Bicategory.rightUnitor (pbMap p f)).hom =
      eqToHom (by rw [Category.comp_id]) := by
  apply Cat.Hom₂.ext
  ext X
  apply fiberHom_ext_pullback f.as.unop
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.rightUnitor_hom_app, CategoryTheory.eqToHom_app]
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_map, pbMapComp_hom_app]
  simp only [eqToHom_refl, Category.id_comp]
  rw [pbMapId_hom_app, cmpUnderlying_cartPullback_cartId,
    show IsPreFibered.pullbackMap ((pbMap p f).toFunctor.obj X).2 (𝟙 b₁.as.unop) ≫
        IsPreFibered.pullbackMap X.2 f.as.unop
      = (cartComp f.as.unop (𝟙 b₁ : b₁ ⟶ b₁).as.unop).proj X from rfl,
    cmpUnderlying_fac]
  change IsPreFibered.pullbackMap X.2 (f ≫ 𝟙 b₁).as.unop = _
  rw [pullbackMap_congr X (show ((f ≫ 𝟙 b₁).as.unop) = f.as.unop by simp)]

/-- The pullback pseudofunctor associated to a fibred category `p`, for the choice of pullbacks
of `IsPreFibered` (Stacks 02XO for an arbitrary choice is
`CategoryTheory.Functor.ChoiceOfPullbacks.pseudofunctor`). Its object part is
`U ↦ Cat.of (p.Fiber U)`, its 1-cell part is `f ↦ f*`, its unitor is `(𝟙 U)* ≅ 𝟭 (p.Fiber U)`
and its compositor is `(g ≫ f)* ≅ f* ⋙ g*`. -/
@[sga "4 VI 7.1.4" "partial", sga "4 XVII 3.3.3" "Forward direction"]
noncomputable def pullbackPseudofunctor (p : 𝒳 ⥤ 𝒮) [p.IsFibered] :
    Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat :=
  pseudofunctorOfIsLocallyDiscrete
    (obj := pbObj p)
    (map := fun {_ _} φ => pbMap p φ)
    (mapId := fun U => pbMapId p U)
    (mapComp := fun {_ _ _} φ γ => pbMapComp p φ γ)
    (map₂_associator := fun {_ _ _ _} f g h => pbMapComp_associator p f g h)
    (map₂_left_unitor := fun {_ _} f => pbMapComp_left_unitor p f)
    (map₂_right_unitor := fun {_ _} f => pbMapComp_right_unitor p f)

/-- Property 1: object part. -/
theorem pullbackPseudofunctor_obj (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (U : 𝒮) :
    (pullbackPseudofunctor p).obj ⟨op U⟩ = Cat.of (p.Fiber U) := rfl

/-- Property 2: 1-cell part is the pullback functor `f*`. -/
theorem pullbackPseudofunctor_map (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U V : 𝒮} (f : V ⟶ U) :
    ((pullbackPseudofunctor p).map
        (⟨f.op⟩ : (⟨op U⟩ : LocallyDiscrete 𝒮ᵒᵖ) ⟶ ⟨op V⟩)).toFunctor
      = fiberPullback (p := p) f := rfl

/-- Property 3: the unitor data `mapId` is the canonical isomorphism `(𝟙 U)* ≅ 𝟭 (Fiber p U)`. -/
theorem pullbackPseudofunctor_mapId (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (U : LocallyDiscrete 𝒮ᵒᵖ) :
    (pullbackPseudofunctor p).mapId U = pbMapId p U :=
  pseudofunctorOfIsLocallyDiscrete_mapId _ _ _ _ _ _ _ U

/-- Property 4: the compositor data `mapComp` is the canonical isomorphism
`(g ≫ f)* ≅ f* ⋙ g*`. -/
theorem pullbackPseudofunctor_mapComp (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
    {U V W : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V) (γ : V ⟶ W) :
    (pullbackPseudofunctor p).mapComp φ γ = pbMapComp p φ γ :=
  pseudofunctorOfIsLocallyDiscrete_mapComp _ _ _ _ _ _ _ φ γ

/-- The compositor of the pullback pseudofunctor is compatible with the chosen strongly
cartesian lifts: on each object `X`, its underlying comparison morphism, followed by the
composite of the chosen cartesian projections over `γ` and over `φ`, is the chosen cartesian
projection over `φ ≫ γ`. -/
@[sga "1 VI 7.2" "partial"]
theorem pullbackPseudofunctor_mapComp_compatible (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
    {U V W : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V) (γ : V ⟶ W) (X : ↑(pbObj p U)) :
    Fiber.fiberInclusion.map (((pullbackPseudofunctor p).mapComp φ γ).hom.toNatTrans.app X)
        ≫ (cartComp φ.as.unop γ.as.unop).proj X =
      IsPreFibered.pullbackMap X.2 (φ ≫ γ).as.unop := by
  rw [pullbackPseudofunctor_mapComp, pbMapComp_hom_app]
  exact cmpUnderlying_fac _ _ _

/-- The compositor is the *unique* isomorphism `(g ≫ f)* ≅ f* ⋙ g*` compatible with the chosen
cartesian lifts: any isomorphism whose components satisfy the compatibility triangle of
`pullbackPseudofunctor_mapComp_compatible` equals `pbMapComp`. -/
@[sga "4 VI 6.1.2" "(6.1.2.1)"]
theorem pbMapComp_uniq (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
    {U V W : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V) (γ : V ⟶ W)
    (θ : pbMap p (φ ≫ γ) ≅ pbMap p φ ≫ pbMap p γ)
    (hθ : ∀ X : ↑(pbObj p U),
      Fiber.fiberInclusion.map (θ.hom.toNatTrans.app X) ≫
          (cartComp φ.as.unop γ.as.unop).proj X =
        IsPreFibered.pullbackMap X.2 (φ ≫ γ).as.unop) :
    θ = pbMapComp p φ γ := by
  apply Iso.ext
  apply Cat.Hom₂.ext
  ext X
  apply Fiber.fiberInclusion.map_injective
  rw [pbMapComp_hom_app]
  exact cmpUnderlying_uniq (cartPullback (φ ≫ γ).as.unop) (cartComp φ.as.unop γ.as.unop) X
    (Fiber.fiberInclusion.map (θ.hom.toNatTrans.app X)) (hθ X)

end CategoryTheory.Functor.IsFibered
