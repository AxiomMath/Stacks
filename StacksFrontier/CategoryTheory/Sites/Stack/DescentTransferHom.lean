module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.SieveDescentDatum
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberComp

/-!
# Transferring morphisms along the gluing isomorphisms of a descent datum

Let `D` be a descent datum relative to a sieve `R` on `U`, and let `f : V ⟶ U`, `g : W ⟶ U` be
arrows of `R`. A morphism `a : ω ⟶ D.obj f` lying over `u : Z ⟶ V` is carried, for every
`v : Z ⟶ W` with `u ≫ f = v ≫ g`, to a morphism `ω ⟶ D.obj g` lying over `v`: factor `a`
through the chosen pullback of `D.obj f` along `u`, apply the gluing isomorphism of `D` at
`(u, v)`, and compose with the chosen pullback morphism along `v`.

The transfer is the identity on a pair `(u, u)`, composes by the cocycle condition, and commutes
with precomposition by the compatibility of the gluing isomorphisms with base change. These are
the three facts the gluing of a descent datum along a single covering morphism consumes.

No Stacks tag states this on its own; it is the bookkeeping behind Stacks 026B and 026E.

## Main definitions

* `CategoryTheory.Functor.SieveDescentDatum.transferHom`: the transfer.

## Main results

* `CategoryTheory.Functor.SieveDescentDatum.transferHom_self`,
  `CategoryTheory.Functor.SieveDescentDatum.transferHom_transferHom`,
  `CategoryTheory.Functor.SieveDescentDatum.comp_transferHom`.

## Implementation notes

The lifting lemmas are restated below with their `IsHomLift` and `IsCartesian` hypotheses as
explicit arguments. The objects of the fibre and of `𝒳` that occur here (`Fiber.fiberInclusion.obj`
of a chosen pullback and `IsPreFibered.pullbackObj`) are equal only after unfolding, which
instance search does not do, so the instance-implicit forms of the Mathlib lemmas do not apply.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

open CategoryTheory Category Limits

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒮}

section Lifts

/-- A composite of a morphism over an identity followed by a morphism over `f` lies over `f`,
with both hypotheses explicit. -/
theorem isHomLift_id_comp_explicit {a b c : 𝒳} {S T : 𝒮} {f : S ⟶ T} {φ : a ⟶ b}
    {ψ : b ⟶ c} (hφ : p.IsHomLift (𝟙 S) φ) (hψ : p.IsHomLift f ψ) : p.IsHomLift f (φ ≫ ψ) :=
  @IsHomLift.comp_lift_id_left _ _ _ _ p _ _ _ _ _ f ψ hψ φ hφ

/-- A composite of a morphism over `f` followed by a morphism over an identity lies over `f`,
with both hypotheses explicit. -/
theorem isHomLift_comp_id_explicit {a b c : 𝒳} {S T : 𝒮} {f : S ⟶ T} {φ : a ⟶ b}
    {ψ : b ⟶ c} (hφ : p.IsHomLift f φ) (hψ : p.IsHomLift (𝟙 T) ψ) : p.IsHomLift f (φ ≫ ψ) :=
  @IsHomLift.comp_lift_id_right _ _ _ _ p _ _ _ _ _ f φ hφ ψ hψ

/-- A morphism lies over at most one morphism between two given objects of the base. -/
theorem isHomLift_base_unique {R S : 𝒮} {a b : 𝒳} {f f' : R ⟶ S} {φ : a ⟶ b}
    (h : p.IsHomLift f φ) (h' : p.IsHomLift f' φ) : f = f' :=
  (@IsHomLift.fac _ _ _ _ p _ _ _ _ f φ h).trans (@IsHomLift.fac _ _ _ _ p _ _ _ _ f' φ h').symm

/-- Lying over a morphism is invariant under rewriting it. -/
theorem isHomLift_of_eq_base {R S : 𝒮} {a b : 𝒳} {f f' : R ⟶ S} {φ : a ⟶ b} (e : f = f')
    (h : p.IsHomLift f φ) : p.IsHomLift f' φ :=
  e ▸ h

end Lifts

variable [p.IsFibered]

section LiftTo

variable {V Z : 𝒮} (x : p.Fiber V) (u : Z ⟶ V) {ω : 𝒳}

/-- The factorization of a morphism over `u` through the chosen pullback morphism along `u`, as
a morphism into the chosen pullback seen in `𝒳`. -/
def liftToPullback (a : ω ⟶ x.1) (ha : p.IsHomLift u a) :
    ω ⟶ Fiber.fiberInclusion.obj (pullbackFiber p x u) :=
  @IsCartesian.map _ _ _ _ p _ _ _ _ u (IsPreFibered.pullbackMap x.2 u)
    (IsPreFibered.pullbackMap.IsCartesian x.2 u) _ a ha

/-- The chosen pullback morphism lies over `u`. -/
theorem isHomLift_pullbackMap_of_fiber : p.IsHomLift u (IsPreFibered.pullbackMap x.2 u) :=
  (IsPreFibered.pullbackMap.IsCartesian x.2 u).toIsHomLift

/-- The factorization lies over the identity. -/
theorem isHomLift_liftToPullback (a : ω ⟶ x.1) (ha : p.IsHomLift u a) :
    p.IsHomLift (𝟙 Z) (liftToPullback x u a ha) :=
  @IsCartesian.map_isHomLift _ _ _ _ p _ _ _ _ u (IsPreFibered.pullbackMap x.2 u)
    (IsPreFibered.pullbackMap.IsCartesian x.2 u) _ a ha

/-- The factorization followed by the chosen pullback morphism is the original morphism. -/
theorem liftToPullback_fac (a : ω ⟶ x.1) (ha : p.IsHomLift u a) :
    liftToPullback x u a ha ≫ IsPreFibered.pullbackMap x.2 u = a :=
  @IsCartesian.fac _ _ _ _ p _ _ _ _ u (IsPreFibered.pullbackMap x.2 u)
    (IsPreFibered.pullbackMap.IsCartesian x.2 u) _ a ha

/-- The factorization is the only morphism over the identity with that property. -/
theorem liftToPullback_uniq (a : ω ⟶ x.1) (ha : p.IsHomLift u a)
    (ψ : ω ⟶ Fiber.fiberInclusion.obj (pullbackFiber p x u)) (hψ : p.IsHomLift (𝟙 Z) ψ)
    (h : ψ ≫ IsPreFibered.pullbackMap x.2 u = a) : ψ = liftToPullback x u a ha :=
  @IsCartesian.map_uniq _ _ _ _ p _ _ _ _ u (IsPreFibered.pullbackMap x.2 u)
    (IsPreFibered.pullbackMap.IsCartesian x.2 u) _ a ha ψ hψ h

/-- The factorization of the chosen pullback morphism itself is the identity. -/
theorem liftToPullback_self :
    liftToPullback x u (IsPreFibered.pullbackMap x.2 u) (isHomLift_pullbackMap_of_fiber x u) =
      𝟙 (Fiber.fiberInclusion.obj (pullbackFiber p x u)) :=
  (liftToPullback_uniq x u _ _ _ (IsHomLift.id (IsPreFibered.pullbackObj_proj x.2 u))
    (Category.id_comp _)).symm

/-- The chosen pullback morphism is strongly cartesian. -/
theorem isStronglyCartesian_pullbackMap_of_fiber :
    p.IsStronglyCartesian u (IsPreFibered.pullbackMap x.2 u) :=
  @IsFibered.isStronglyCartesian_of_isCartesian _ _ _ _ p _ _ _ u _ _ _
    (IsPreFibered.pullbackMap.IsCartesian x.2 u)

end LiftTo

namespace SieveDescentDatum

variable {U : 𝒮} {R : Sieve U} (D : SieveDescentDatum p R)

/-- **The transfer of a morphism along the gluing isomorphism** at `(u, v)`: a morphism
`a : ω ⟶ D.obj f` over `u` is factored through the chosen pullback along `u`, carried by the
gluing isomorphism to the chosen pullback of `D.obj g` along `v`, and composed with the chosen
pullback morphism. -/
def transferHom {V W Z : 𝒮} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g) (u : Z ⟶ V)
    (v : Z ⟶ W) (h : u ≫ f = v ≫ g) {ω : 𝒳} (a : ω ⟶ (D.obj f hf).1)
    (ha : p.IsHomLift u a) : ω ⟶ (D.obj g hg).1 :=
  liftToPullback (D.obj f hf) u a ha ≫ Fiber.fiberInclusion.map (D.iso hf hg u v h).hom ≫
    IsPreFibered.pullbackMap (D.obj g hg).2 v

/-- The transfer lies over `v`. -/
theorem isHomLift_transferHom {V W Z : 𝒮} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (u : Z ⟶ V) (v : Z ⟶ W) (h : u ≫ f = v ≫ g) {ω : 𝒳} (a : ω ⟶ (D.obj f hf).1)
    (ha : p.IsHomLift u a) : p.IsHomLift v (D.transferHom hf hg u v h a ha) :=
  isHomLift_id_comp_explicit (isHomLift_liftToPullback _ u a ha)
    (isHomLift_id_comp_explicit (D.iso hf hg u v h).hom.2 (isHomLift_pullbackMap_of_fiber _ v))

/-- **The transfer along a pair `(u, u)` from an arrow to itself is the identity.** -/
theorem transferHom_self {V Z : 𝒮} {f : V ⟶ U} (hf : R f) (u : Z ⟶ V) (h : u ≫ f = u ≫ f)
    {ω : 𝒳} (a : ω ⟶ (D.obj f hf).1) (ha : p.IsHomLift u a) :
    D.transferHom hf hf u u h a ha = a := by
  unfold transferHom
  rw [D.iso_self hf u h]
  exact (congrArg (liftToPullback (D.obj f hf) u a ha ≫ ·) (Category.id_comp _)).trans
    (liftToPullback_fac _ u a ha)

/-- The transfer depends on the pair `(u, v)` and on the morphism only through their values. -/
theorem transferHom_congr {V W Z : 𝒮} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    {u u' : Z ⟶ V} {v v' : Z ⟶ W} (hu : u = u') (hv : v = v') (h : u ≫ f = v ≫ g)
    (h' : u' ≫ f = v' ≫ g) {ω : 𝒳} {a a' : ω ⟶ (D.obj f hf).1} (e : a = a')
    (ha : p.IsHomLift u a) (ha' : p.IsHomLift u' a') :
    D.transferHom hf hg u v h a ha = D.transferHom hf hg u' v' h' a' ha' := by
  subst hu hv e
  rfl

/-- The transfer of the chosen pullback morphism itself is the gluing isomorphism followed by the
chosen pullback morphism. -/
theorem transferHom_pullbackMap {V W Z : 𝒮} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (u : Z ⟶ V) (v : Z ⟶ W) (h : u ≫ f = v ≫ g) :
    D.transferHom hf hg u v h (IsPreFibered.pullbackMap (D.obj f hf).2 u)
        (isHomLift_pullbackMap_of_fiber _ u) =
      Fiber.fiberInclusion.map (D.iso hf hg u v h).hom ≫
        IsPreFibered.pullbackMap (D.obj g hg).2 v := by
  unfold transferHom
  rw [liftToPullback_self]
  exact Category.id_comp _

/-- The factorization through the chosen pullback along `v` of a transfer is the factorization
of the original morphism followed by the gluing isomorphism. -/
theorem liftToPullback_transferHom {V W Z : 𝒮} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (u : Z ⟶ V) (v : Z ⟶ W) (h : u ≫ f = v ≫ g) {ω : 𝒳} (a : ω ⟶ (D.obj f hf).1)
    (ha : p.IsHomLift u a) :
    liftToPullback (D.obj g hg) v (D.transferHom hf hg u v h a ha)
        (D.isHomLift_transferHom hf hg u v h a ha) =
      liftToPullback (D.obj f hf) u a ha ≫ Fiber.fiberInclusion.map (D.iso hf hg u v h).hom :=
  (liftToPullback_uniq _ v _ _ _ (isHomLift_comp_id_explicit (isHomLift_liftToPullback _ u a ha)
    (D.iso hf hg u v h).hom.2) (Category.assoc _ _ _)).symm

/-- **Transfers compose**, by the cocycle condition of the datum. -/
theorem transferHom_transferHom {V W X Z : 𝒮} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    {k : X ⟶ U} (hk : R k) (u : Z ⟶ V) (v : Z ⟶ W) (w : Z ⟶ X) (h₁ : u ≫ f = v ≫ g)
    (h₂ : v ≫ g = w ≫ k) (h₃ : u ≫ f = w ≫ k) {ω : 𝒳} (a : ω ⟶ (D.obj f hf).1)
    (ha : p.IsHomLift u a) :
    D.transferHom hg hk v w h₂ (D.transferHom hf hg u v h₁ a ha)
        (D.isHomLift_transferHom hf hg u v h₁ a ha) =
      D.transferHom hf hk u w h₃ a ha := by
  rw [transferHom, D.liftToPullback_transferHom hf hg u v h₁ a ha, transferHom, assoc]
  refine congrArg (_ ≫ ·) ?_
  erw [← assoc, ← Functor.map_comp, D.cocycle hf hg hk u v w h₁ h₂ h₃]

/-- **Transfers commute with precomposition**, by the compatibility of the gluing isomorphisms
with base change. -/
theorem comp_transferHom {V W Z Z' : 𝒮} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (u : Z ⟶ V) (v : Z ⟶ W) (h : u ≫ f = v ≫ g) (γ : Z' ⟶ Z) {ω ω' : 𝒳}
    (a : ω ⟶ (D.obj f hf).1) (ha : p.IsHomLift u a) (t : ω' ⟶ ω) (ht : p.IsHomLift γ t)
    (h' : (γ ≫ u) ≫ f = (γ ≫ v) ≫ g) (hta : p.IsHomLift (γ ≫ u) (t ≫ a)) :
    t ≫ D.transferHom hf hg u v h a ha = D.transferHom hf hg (γ ≫ u) (γ ≫ v) h' (t ≫ a) hta := by
  have hiso := D.iso_pullback hf hg u v h γ
  set L := liftToPullback (D.obj f hf) (γ ≫ u) (t ≫ a) hta
  set ci := (pullbackFiberCompIso (D.obj f hf) u γ).inv
  set pγ := IsPreFibered.pullbackMap (pullbackFiber p (D.obj f hf) u).2 γ
  have key : t ≫ liftToPullback (D.obj f hf) u a ha = L ≫ Fiber.fiberInclusion.map ci ≫ pγ := by
    refine @IsStronglyCartesian.ext _ _ _ _ p _ _ _ _ u _
      (isStronglyCartesian_pullbackMap_of_fiber _ u) _ _ γ _ _
      (isHomLift_comp_id_explicit ht (isHomLift_liftToPullback _ u a ha))
      (isHomLift_id_comp_explicit (isHomLift_liftToPullback _ _ _ hta)
        (isHomLift_id_comp_explicit ci.2 (isHomLift_pullbackMap_of_fiber _ γ))) ?_
    erw [assoc, liftToPullback_fac, assoc, assoc, pullbackFiberCompIso_inv_fac, liftToPullback_fac]
  unfold transferHom
  rw [← hiso, ← assoc, key]
  simp only [Functor.map_comp, pullbackFiberIso_hom]
  erw [assoc, assoc, ← pullbackFiberHom_fac_assoc, ← pullbackFiberCompIso_hom_fac, assoc, assoc]

end SieveDescentDatum

end CategoryTheory.Functor
