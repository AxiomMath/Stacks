module

public import StacksFrontier.CategoryTheory.Sites.Stackification.GroupoidStackification
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeEffectiveDescent
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeGluing
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeStack
public import StacksFrontier.CategoryTheory.Sites.Stack.MorSeparated
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise

/-!
# The third stage of the stackification of a fibred category with `Mor`-sheaves

Let `p : 𝒳 ⥤ 𝒞` be a fibred category over a site `(𝒞, J)` whose presheaves `Mor(x, y)` are
sheaves — condition (2) of Stacks 026F. Then the first two stages of the construction of the
stackification of Stacks 02ZN change nothing, and the third stage alone,
`CategoryTheory.Functor.DescentPair`, is a stackification of `p`: it is a stack, the 1-morphism
`CategoryTheory.Functor.toDescentPair` into it is fully faithful, and every object of it is locally
in the image. This file records those facts in the form a consumer applies them, including that
the third stage is fibred in groupoids when `p` is.

The one input not already in the construction is that `Mor`-sheaves make locally equal morphisms
equal (`CategoryTheory.Functor.eq_of_locallyEqual_of_isMorSheaf`): a morphism of `𝒳` factors
through the chosen cartesian lift of its base morphism by a morphism of a fibre, and two such
factorizations agreeing locally agree by separatedness of the morphism presheaf.

## Main results

* `CategoryTheory.Functor.eq_of_locallyEqual_of_isMorSheaf`: locally equal morphisms are equal.
* `CategoryTheory.Functor.isStack_descentPairProj_of_isMorSheaf`: the third stage is a stack.
* `CategoryTheory.Functor.essImage_pullbackFiber_toDescentPair`: its objects are locally in the
  image of `CategoryTheory.Functor.toDescentPair`.
* `CategoryTheory.Functor.isFiberedInGroupoids_descentPairProj`: it is fibred in groupoids when
  `p` is.
* `CategoryTheory.Functor.full_toDescentPair` and `CategoryTheory.Functor.faithful_toDescentPair`:
  `CategoryTheory.Functor.toDescentPair` is fully faithful when `p` is fibred in groupoids.

## References

* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 02ZP](https://stacks.math.columbia.edu/tag/02ZP)
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

universe vb w t₁ t₂

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

section Separated

variable {𝒞 : Type t₁} [Category.{vb} 𝒞] {𝒳 : Type t₂} [Category.{w} 𝒳]
  {p : 𝒳 ⥤ 𝒞} [p.IsFibered] {J : GrothendieckTopology 𝒞}

/-- **`Mor`-sheaves make locally equal morphisms equal.** If the presheaves `Mor(x, y)` of a
fibred category are sheaves, two morphisms of the total category which are locally equal — they
lie over one morphism of the base and agree after precomposition with every morphism lying over a
member of a covering sieve — are equal. -/
theorem eq_of_locallyEqual_of_isMorSheaf
    (hmor : ∀ (U : 𝒞) (x y : p.Fiber U), IsMorSheaf p J U x y)
    {x y : 𝒳} {a b : x ⟶ y} (h : p.LocallyEqual J a b) : a = b := by
  obtain ⟨hab, R, hR, hloc⟩ := h
  let U := p.obj x
  let V := p.obj y
  let s : U ⟶ V := p.map a
  let y₀ : p.Fiber V := Fiber.mk (rfl : p.obj y = V)
  let x₀ : p.Fiber U := Fiber.mk (rfl : p.obj x = U)
  let y' := pullbackFiber p y₀ s
  let π : y'.1 ⟶ y := IsPreFibered.pullbackMap y₀.2 s
  have : p.IsCartesian s π := IsPreFibered.pullbackMap.IsCartesian y₀.2 s
  have key : ∀ c : x ⟶ y, p.map a = p.map c →
      ∃ (c' : x ⟶ y'.1) (_ : p.IsHomLift (𝟙 U) c'), c' ≫ π = c := fun c hc ↦ by
    have : p.IsHomLift s c := by
      change p.IsHomLift (p.map a) c
      rw [hc]
      infer_instance
    exact ⟨_, IsCartesian.map_isHomLift p s π c, IsCartesian.fac p s π c⟩
  obtain ⟨a', ha'l, ha'⟩ := key a rfl
  obtain ⟨b', hb'l, hb'⟩ := key b hab
  have hmn : (⟨a', ha'l⟩ : x₀ ⟶ y') = ⟨b', hb'l⟩ := by
    refine eq_of_pullbackFiberHom_locally_eq (p := p) (hmor U x₀ y') hR fun W f hf ↦ ?_
    let φf : (pullbackFiber p x₀ f).1 ⟶ x := IsPreFibered.pullbackMap x₀.2 f
    have : p.IsCartesian f φf := IsPreFibered.pullbackMap.IsCartesian x₀.2 f
    have hφ : R.arrows (p.map φf) := by
      rw [IsHomLift.fac' p f φf, eqToHom_refl, Category.comp_id]
      exact R.downward_closed hf _
    have h₂ : φf ≫ a' = φf ≫ b' := by
      have : p.IsHomLift f (φf ≫ a') := IsHomLift.comp_lift_id_right' p f φf U a'
      have : p.IsHomLift f (φf ≫ b') := IsHomLift.comp_lift_id_right' p f φf U b'
      refine IsStronglyCartesian.ext p s π f ?_
      rw [Category.assoc, Category.assoc, ha', hb']
      exact hloc φf hφ
    apply Fiber.hom_ext
    have : p.IsCartesian f (IsPreFibered.pullbackMap y'.2 f) :=
      IsPreFibered.pullbackMap.IsCartesian y'.2 f
    refine IsCartesian.ext p f (IsPreFibered.pullbackMap y'.2 f) _ _ ?_
    rw [pullbackFiberHom_fac, pullbackFiberHom_fac]
    exact h₂
  rw [← ha', ← hb', show a' = b' from congrArg Fiber.fiberInclusion.map hmn]

end Separated

section ThirdStage

variable {𝒞 : Type t₁} [Category.{vb} 𝒞] {𝒴 : Type t₂} [Category.{max t₁ t₂ w vb} 𝒴]
  {q : 𝒴 ⥤ 𝒞} [q.IsFibered] {J : GrothendieckTopology 𝒞}

/-- **The third stage of the stackification of a fibred category with `Mor`-sheaves is a stack.**
This is Stacks 026F for `CategoryTheory.Functor.descentPairProj`, whose two remaining conditions
are `CategoryTheory.Functor.isMorSheaf_descentPairProj` and
`CategoryTheory.Functor.hasEffectiveDescent_descentPairProj`. -/
theorem isStack_descentPairProj_of_isMorSheaf
    (hmor : ∀ (U : 𝒞) (x y : q.Fiber U), IsMorSheaf q J U x y) :
    (q.descentPairProj J).IsStack J where
  isFibered := inferInstance
  isMorSheaf := isMorSheaf_descentPairProj hmor (eq_of_locallyEqual_of_isMorSheaf hmor)
  hasEffectiveDescent :=
    hasEffectiveDescent_descentPairProj hmor (eq_of_locallyEqual_of_isMorSheaf hmor)

variable (q J) in
/-- **Every object of the third stage is locally in the image**: along every arrow of the sieve of
a descent pair, its chosen pullback is isomorphic, in the fibre, to the image of an object of the
fibre of `𝒴` under `CategoryTheory.Functor.toDescentPair`. -/
theorem essImage_pullbackFiber_toDescentPair (U : 𝒞) (x' : (q.descentPairProj J).Fiber U) :
    ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq (isFibredOneMorphism_toDescentPair q J).comp_eq V).essImage
        (pullbackFiber (q.descentPairProj J) x' f) := by
  obtain ⟨A, rfl⟩ := x'
  refine ⟨A.sieve, A.sieve_mem, fun V f hf ↦ ?_⟩
  obtain ⟨x, e, he⟩ := exists_isHomLift_id_iso_toDescentPair_obj A f hf
  have hx : q.obj x = V := by
    have h0 := IsHomLift.domain_eq (q.descentPairProj J) (𝟙 V) e.hom
    rwa [← Functor.comp_obj, toDescentPair_comp_descentPairProj] at h0
  have hcart : (q.descentPairProj J).IsCartesian f
      (DescentMor.mk (DescentPairData.pullbackHom A f) : A.pullback f ⟶ A) :=
    have := isStronglyCartesian_pullbackHom A f
    inferInstance
  have hV : (q.descentPairProj J).obj (A.pullback f) = V := rfl
  have hA : (q.descentPairProj J).obj A = A.pt := rfl
  have hfib : ((fiberFunctorOfCompEq (isFibredOneMorphism_toDescentPair q J).comp_eq V).obj
        (Fiber.mk hx)) ≅ (Fiber.mk hV) := Fiber.isoMk e he
  have hcmp : (Fiber.mk hV : (q.descentPairProj J).Fiber V) ≅
      pullbackFiber (q.descentPairProj J) (Fiber.mk hA) f :=
    (fiberIsoOfCartesian f (IsPreFibered.pullbackMap (Fiber.mk hA).2 f)
      (DescentMor.mk (DescentPairData.pullbackHom A f))
      (IsPreFibered.pullbackMap.IsCartesian _ _) hcart).symm
  exact ⟨Fiber.mk hx, ⟨hfib ≪≫ hcmp⟩⟩

/-- **The third stage of the stackification of a category fibred in groupoids with `Mor`-sheaves
is fibred in groupoids.** This is Stacks 02ZP for the third stage. -/
theorem isFiberedInGroupoids_descentPairProj (hq : q.IsFiberedInGroupoids)
    (hmor : ∀ (U : 𝒞) (x y : q.Fiber U), IsMorSheaf q J U x y) :
    (q.descentPairProj J).IsFiberedInGroupoids :=
  Stackification.isFiberedInGroupoids_of_isStackification hq
    (isStack_descentPairProj_of_isMorSheaf hmor) (isFibredOneMorphism_toDescentPair q J)
    (fun U x y ↦ isLocallyBijective_morPresheafMap_toDescentPair U x y)
    (essImage_pullbackFiber_toDescentPair q J)

/-- **The functors induced on fibres by the 1-morphism into the third stage are full and
faithful**, for a category fibred in groupoids with `Mor`-sheaves. Faithfulness and fullness on
isomorphisms are `CategoryTheory.Functor.isFibrewiseFullyFaithful_toDescentPair`; every morphism of
a fibre of `𝒴` is an isomorphism. -/
theorem full_faithful_fiber_toDescentPair (hq : q.IsFiberedInGroupoids)
    (hmor : ∀ (U : 𝒞) (x y : q.Fiber U), IsMorSheaf q J U x y) (U : 𝒞) :
    (Fiber.mapOfComp q (q.descentPairProj J) (toDescentPair q J)
        (isFibredOneMorphism_toDescentPair q J).comp_eq U).Full ∧
      (Fiber.mapOfComp q (q.descentPairProj J) (toDescentPair q J)
        (isFibredOneMorphism_toDescentPair q J).comp_eq U).Faithful := by
  have hff := isFibrewiseFullyFaithful_toDescentPair hmor (J := J)
    (eq_of_locallyEqual_of_isMorSheaf hmor)
  refine ⟨⟨fun {a b} m ↦ ?_⟩, ⟨fun {a b} m n h ↦ hff.faithful m n h⟩⟩
  have hm : IsIso m :=
    ((isFiberedInGroupoids_descentPairProj hq hmor).fiber_isGroupoid U).all_isIso m
  obtain ⟨ι, hι⟩ := hff.full_iso (a := a) (b := b) (@asIso _ _ _ _ m hm)
  exact ⟨ι.hom, hι⟩

/-- **The 1-morphism into the third stage is full and faithful**, for a category fibred in
groupoids with `Mor`-sheaves: Stacks 003Z turns fibrewise full faithfulness into full
faithfulness. -/
theorem full_and_faithful_toDescentPair (hq : q.IsFiberedInGroupoids)
    (hmor : ∀ (U : 𝒞) (x y : q.Fiber U), IsMorSheaf q J U x y) :
    (toDescentPair q J).Full ∧ (toDescentPair q J).Faithful :=
  (IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber q (q.descentPairProj J) hq
    (isFiberedInGroupoids_descentPairProj hq hmor) (toDescentPair q J)
    (isFibredOneMorphism_toDescentPair q J).comp_eq).2
    (full_faithful_fiber_toDescentPair hq hmor)

end ThirdStage

end CategoryTheory.Functor

end
