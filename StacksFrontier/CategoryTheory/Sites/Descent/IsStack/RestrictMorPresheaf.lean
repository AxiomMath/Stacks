module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.Transfer

/-!
# The morphism presheaf of a full subcategory

Let `p : 𝒳 ⥤ 𝒮` be a fibred category and `P` a property of objects of `𝒳` such that the source
of every strongly cartesian morphism into an object with property `P` is isomorphic over the
identity to an object with property `P`. Then the restriction of `p` to the full subcategory cut
out by `P` is a fibred category, and its presheaf `Mor(x, y)` is isomorphic to the presheaf
`Mor(ι x, ι y)` of `p`.

## Main definitions

* `CategoryTheory.Functor.pullbackFiberιIso`, the identification of the chosen pullbacks;
* `CategoryTheory.Functor.morSectionιEquiv` and
  `CategoryTheory.Functor.morPresheafιIso`, the bijection on sections and the resulting
  isomorphism of presheaves.

## Main results

* `CategoryTheory.Functor.isFibered_restrict_of_closed`: the restriction of `p` is a fibred
  category.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- If the source of every strongly cartesian morphism into an object with property `P` is
isomorphic over the identity to an object with property `P`, then the restriction of the fibred
category `p` to the full subcategory cut out by `P` is a fibred category. -/
theorem isFibered_restrict_of_closed (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) [p.IsFibered]
    (h1 : ClosedUnderStronglyCartesian p P) : (restrict p P).IsFibered := by
  refine IsFibered.of_exists_isStronglyCartesian fun a V f => ?_
  obtain ⟨a₀, θ', -, hθ'⟩ := exists_isCartesian_restrict p P h1 rfl f
  exact ⟨a₀, θ', isStronglyCartesian_of_isStronglyCartesian_map_ι p P f θ' inferInstance⟩

variable (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) [p.IsFibered]
  (h1 : ClosedUnderStronglyCartesian p P)

/-- The image under `P.ι` of the chosen pullback of `x` along `f` inside the full subcategory is a
`p`-cartesian lift of `f` at `ι x`, hence canonically isomorphic to the chosen pullback of `ι x`
along `f` taken in `𝒳`. -/
noncomputable def pullbackFiberιIso {U : 𝒮} (x : (restrict p P).Fiber U) {V : 𝒮} (f : V ⟶ U) :
    haveI := isFibered_restrict_of_closed p P h1
    P.ι.obj (pullbackFiber (restrict p P) x f).1 ≅ (pullbackFiber p (fiberι p P x) f).1 :=
  haveI := isFibered_restrict_of_closed p P h1
  haveI : p.IsCartesian f (P.ι.map (IsPreFibered.pullbackMap x.2 f)) :=
    isCartesian_map_ι p P h1 f _ (IsPreFibered.pullbackMap.IsCartesian x.2 f)
  IsCartesian.domainUniqueUpToIso p f (IsPreFibered.pullbackMap (fiberι p P x).2 f)
    (P.ι.map (IsPreFibered.pullbackMap x.2 f))

variable {p P}

/-- The image under `P.ι` of the chosen pullback map in the full subcategory is `p`-cartesian. -/
private lemma isCartesian_map_ι_pullbackMap {U : 𝒮} (x : (restrict p P).Fiber U) {V : 𝒮}
    (f : V ⟶ U) :
    haveI := isFibered_restrict_of_closed p P h1
    p.IsCartesian f (P.ι.map (IsPreFibered.pullbackMap x.2 f)) :=
  haveI := isFibered_restrict_of_closed p P h1
  isCartesian_map_ι p P h1 f _ (IsPreFibered.pullbackMap.IsCartesian x.2 f)

/-- The forward direction of `pullbackFiberιIso` lies over the identity, so it is an isomorphism
of the fibre of `p` over `V`. -/
lemma isHomLift_pullbackFiberιIso_hom {U : 𝒮} (x : (restrict p P).Fiber U) {V : 𝒮} (f : V ⟶ U) :
    haveI := isFibered_restrict_of_closed p P h1
    p.IsHomLift (𝟙 V) (pullbackFiberιIso p P h1 x f).hom :=
  have := isFibered_restrict_of_closed p P h1
  have := isCartesian_map_ι_pullbackMap h1 x f
  IsCartesian.domainUniqueUpToIso_inv_isHomLift p f
    (IsPreFibered.pullbackMap (fiberι p P x).2 f) (P.ι.map (IsPreFibered.pullbackMap x.2 f))

/-- The inverse of `pullbackFiberιIso` lies over the identity. -/
lemma isHomLift_pullbackFiberιIso_inv {U : 𝒮} (x : (restrict p P).Fiber U) {V : 𝒮} (f : V ⟶ U) :
    haveI := isFibered_restrict_of_closed p P h1
    p.IsHomLift (𝟙 V) (pullbackFiberιIso p P h1 x f).inv :=
  have := isFibered_restrict_of_closed p P h1
  have := isCartesian_map_ι_pullbackMap h1 x f
  IsCartesian.domainUniqueUpToIso_hom_isHomLift p f
    (IsPreFibered.pullbackMap (fiberι p P x).2 f) (P.ι.map (IsPreFibered.pullbackMap x.2 f))

/-- `pullbackFiberιIso` is compatible with the two chosen cartesian lifts it compares. -/
@[reassoc]
lemma pullbackFiberιIso_hom_fac {U : 𝒮} (x : (restrict p P).Fiber U) {V : 𝒮} (f : V ⟶ U) :
    haveI := isFibered_restrict_of_closed p P h1
    (pullbackFiberιIso p P h1 x f).hom ≫ IsPreFibered.pullbackMap (fiberι p P x).2 f =
      P.ι.map (IsPreFibered.pullbackMap x.2 f) :=
  have := isFibered_restrict_of_closed p P h1
  have := isCartesian_map_ι_pullbackMap h1 x f
  IsCartesian.fac p f (IsPreFibered.pullbackMap (fiberι p P x).2 f)
    (P.ι.map (IsPreFibered.pullbackMap x.2 f))

/-- Conjugating by `pullbackFiberιIso` turns the restriction map of the chosen pullbacks of `x`
inside the full subcategory into the restriction map of the chosen pullbacks of `ι x` in `𝒳`. This
is the naturality of `pullbackFiberιIso`. -/
lemma map_pullbackFiberMap_restrict {U : 𝒮} (x : (restrict p P).Fiber U) {g₁ g₂ : Over U}
    (h : g₁ ⟶ g₂) :
    haveI := isFibered_restrict_of_closed p P h1
    P.ι.map (pullbackFiberMap (restrict p P) x h) ≫ (pullbackFiberιIso p P h1 x g₂.hom).hom =
      (pullbackFiberιIso p P h1 x g₁.hom).hom ≫ pullbackFiberMap p (fiberι p P x) h := by
  have := isFibered_restrict_of_closed p P h1
  have := isHomLift_pullbackFiberιIso_hom h1 x g₁.hom
  have := isHomLift_pullbackFiberιIso_hom h1 x g₂.hom
  have := (isHomLift_restrict_iff p P h.left _).1 (pullbackFiberMap_isHomLift (restrict p P) x h)
  refine IsStronglyCartesian.ext p g₂.hom
    (IsPreFibered.pullbackMap (fiberι p P x).2 g₂.hom) h.left ?_
  rw [Category.assoc, Category.assoc, pullbackFiberιIso_hom_fac, pullbackFiberMap_fac,
    pullbackFiberιIso_hom_fac, ← Functor.map_comp, pullbackFiberMap_fac]

/-- The bijection between the sections over `g` of `Mor(x, y)` for the restriction of `p` and
those of `Mor(ι x, ι y)` for `p`, given by `P.ι` conjugated by `pullbackFiberιIso`. -/
noncomputable def morSectionιEquiv {U : 𝒮} (x y : (restrict p P).Fiber U) (g : Over U) :
    haveI := isFibered_restrict_of_closed p P h1
    (pullbackFiber (restrict p P) x g.hom ⟶ pullbackFiber (restrict p P) y g.hom) ≃
      (pullbackFiber p (fiberι p P x) g.hom ⟶ pullbackFiber p (fiberι p P y) g.hom) :=
  haveI := isFibered_restrict_of_closed p P h1
  { toFun := fun m => ⟨(pullbackFiberιIso p P h1 x g.hom).inv ≫
        P.ι.map (Fiber.fiberInclusion.map m) ≫ (pullbackFiberιIso p P h1 y g.hom).hom,
      isHomLift_id_comp p _ _ (isHomLift_pullbackFiberιIso_inv h1 x g.hom)
        (isHomLift_id_comp p _ _ ((isHomLift_restrict_iff p P (𝟙 g.left) _).1 m.2)
          (isHomLift_pullbackFiberιIso_hom h1 y g.hom))⟩
    invFun := fun n => ⟨P.fullyFaithfulι.preimage ((pullbackFiberιIso p P h1 x g.hom).hom ≫
        Fiber.fiberInclusion.map n ≫ (pullbackFiberιIso p P h1 y g.hom).inv), by
      apply (isHomLift_restrict_iff p P (𝟙 g.left) _).2
      rw [P.fullyFaithfulι.map_preimage]
      exact isHomLift_id_comp p _ _ (isHomLift_pullbackFiberιIso_hom h1 x g.hom)
        (isHomLift_id_comp p _ _ n.2 (isHomLift_pullbackFiberιIso_inv h1 y g.hom))⟩
    left_inv := fun m => by
      apply Fiber.hom_ext
      apply P.ι.map_injective
      change P.ι.map (P.fullyFaithfulι.preimage _) = P.ι.map (Fiber.fiberInclusion.map m)
      rw [P.fullyFaithfulι.map_preimage]
      simp [Fiber.fiberInclusion]
    right_inv := fun n => by
      apply Fiber.hom_ext
      change (pullbackFiberιIso p P h1 x g.hom).inv ≫
          P.ι.map (P.fullyFaithfulι.preimage _) ≫ (pullbackFiberιIso p P h1 y g.hom).hom =
        Fiber.fiberInclusion.map n
      rw [P.fullyFaithfulι.map_preimage]
      simp [Fiber.fiberInclusion] }

/-- Conjugating the restriction map of chosen pullbacks by the inverse of `pullbackFiberιIso`. -/
@[reassoc]
lemma pullbackFiberιIso_inv_map_pullbackFiberMap {U : 𝒮} (x : (restrict p P).Fiber U)
    {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    haveI := isFibered_restrict_of_closed p P h1
    (pullbackFiberιIso p P h1 x g₁.hom).inv ≫ P.ι.map (pullbackFiberMap (restrict p P) x h) =
      pullbackFiberMap p (fiberι p P x) h ≫ (pullbackFiberιIso p P h1 x g₂.hom).inv := by
  have := isFibered_restrict_of_closed p P h1
  rw [Iso.inv_comp_eq, ← Category.assoc, ← map_pullbackFiberMap_restrict h1 x h,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The presheaf `Mor(x, y)` of the restriction of `p` to a full subcategory is isomorphic to the
presheaf `Mor(ι x, ι y)` of `p`. -/
noncomputable def morPresheafιIso {U : 𝒮} (x y : (restrict p P).Fiber U) :
    haveI := isFibered_restrict_of_closed p P h1
    morPresheaf (restrict p P) x y ≅ morPresheaf p (fiberι p P x) (fiberι p P y) :=
  haveI := isFibered_restrict_of_closed p P h1
  NatIso.ofComponents (fun g => Equiv.toIso (morSectionιEquiv h1 x y g.unop)) <| by
    rintro ⟨g₂⟩ ⟨g₁⟩ ⟨h⟩
    ext m
    change morSectionιEquiv h1 x y g₁ (morRestrict (restrict p P) x y h m) =
      morRestrict p (fiberι p P x) (fiberι p P y) h (morSectionιEquiv h1 x y g₂ m)
    refine morRestrict_uniq p (fiberι p P x) (fiberι p P y) h
      (morSectionιEquiv h1 x y g₂ m) _ ?_
    change ((pullbackFiberιIso p P h1 x g₁.hom).inv ≫
          P.ι.map (Fiber.fiberInclusion.map (morRestrict (restrict p P) x y h m)) ≫
          (pullbackFiberιIso p P h1 y g₁.hom).hom) ≫
        IsPreFibered.pullbackMap (fiberι p P y).2 g₁.hom =
      pullbackFiberMap p (fiberι p P x) h ≫
        ((pullbackFiberιIso p P h1 x g₂.hom).inv ≫
          P.ι.map (Fiber.fiberInclusion.map m) ≫
          (pullbackFiberιIso p P h1 y g₂.hom).hom) ≫
        IsPreFibered.pullbackMap (fiberι p P y).2 g₂.hom
    simp only [Category.assoc]
    rw [pullbackFiberιIso_hom_fac, ← Functor.map_comp, morRestrict_fac, Functor.map_comp,
      Functor.map_comp, ← pullbackFiberιIso_hom_fac h1 y g₂.hom,
      pullbackFiberιIso_inv_map_pullbackFiberMap_assoc]

end Functor

end CategoryTheory
