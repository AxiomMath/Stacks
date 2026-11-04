module

public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackification
public import StacksFrontier.CategoryTheory.Sites.Stackification.LocalEquality
import StacksCore.Tactic.EgaSgaAttribute

/-! # Local equality of raw morphisms from local injectivity of the morphism presheaves

Let `N : 𝒜 ⥤ ℬ` be a 1-morphism of fibred categories over a site `(𝒞, J)` whose induced maps of
the morphism presheaves of Stacks 02ZB are locally injective — the injectivity half of clause (1)
of Stacks 02ZN. This file converts that statement about presheaves on the slices `𝒞/U` back into
the statement about *raw* morphisms of `𝒜` out of which
`CategoryTheory.Functor.isLocallyInjective_morPresheafMap` produces it: two morphisms of `𝒜` with
the same image under `N` are locally equal.

The two readings are not interchangeable without an argument: a section of `Mor(x, y)` is a
morphism of a *fibre*, so a pair of raw morphisms must first be factored through the chosen
cartesian lift of the morphism of `𝒞` they lie over. That factorisation is available because `N`
carries the chosen lift to a strongly cartesian morphism, which then cancels.

## Main results

* `CategoryTheory.Functor.base_eq_of_isHomLift_of_eq`: equal morphisms of the total category lie
  over equal morphisms of the base, when the two base morphisms share their domain and codomain.
* `CategoryTheory.Functor.locallyEqual_of_map_eq`: **the raw form of the injectivity half of
  clause (1) of Stacks 02ZN** — two morphisms of `𝒜` identified by `N` are locally equal.
* `CategoryTheory.Functor.fullyFaithful_fiberFunctorOfCompEq`: a fully faithful 1-morphism over
  the base induces a fully faithful functor on each fibre.
* `CategoryTheory.Functor.faithful_of_faithful_fiberFunctorOfCompEq`: conversely, a 1-morphism of
  fibred categories that is faithful on every fibre is faithful.

## Implementation notes

The fibre objects are written out as `CategoryTheory.Functor.Fiber.mk rfl` rather than bound by
`set`: a `set`-bound fibre object makes the underlying object of `𝒜` opaque, and the instances
`CategoryTheory.Functor.IsHomLift` that the chosen cartesian lifts are found through then no
longer match the ones in context.

## References

* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

open CategoryTheory

universe v vb v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒜 : Type u₂} [Category.{v} 𝒜] {ℬ : Type u₃}
  [Category.{v} ℬ]

/-- **Equal morphisms of the total category lie over equal morphisms of the base**, provided the
two base morphisms have the same domain and the same codomain. -/
lemma base_eq_of_isHomLift_of_eq (r : ℬ ⥤ 𝒞) {a b : ℬ} {R S : 𝒞} (f g : R ⟶ S)
    (χ χ' : a ⟶ b) (h : χ = χ') (hf : r.IsHomLift f χ) (hg : r.IsHomLift g χ') : f = g := by
  subst h
  exact (cancel_mono _).1 ((cancel_epi _).1
    ((IsHomLift.fac' r f χ).symm.trans (IsHomLift.fac' r g χ)))

section FibreFullyFaithful

variable {𝒜' : Type u₂} [Category.{v₂} 𝒜'] {ℬ' : Type u₃} [Category.{v₃} ℬ']
  {q : 𝒜' ⥤ 𝒞} {r : ℬ' ⥤ 𝒞} {N : 𝒜' ⥤ ℬ'}

/-- **A fully faithful functor over the base induces a fully faithful functor on each fibre.**
Faithfulness is faithfulness of `N` read through the faithful inclusion of a fibre; fullness uses
that a functor strictly over the base reflects `CategoryTheory.Functor.IsHomLift`, so the preimage
of a vertical morphism is vertical. -/
theorem fullyFaithful_fiberFunctorOfCompEq (hN : N ⋙ r = q) (hfull : N.Full)
    (hfaith : N.Faithful) (U : 𝒞) :
    Nonempty (fiberFunctorOfCompEq hN U).FullyFaithful := by
  refine (Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr fun A B =>
    ⟨fun m₁ m₂ hm => ?_, fun n => ?_⟩
  · refine Fiber.hom_ext (hfaith.map_injective ?_)
    rw [← fiberInclusion_map_fiberFunctorOfCompEq_map hN m₁,
      ← fiberInclusion_map_fiberFunctorOfCompEq_map hN m₂]
    exact congrArg Fiber.fiberInclusion.map hm
  · obtain ⟨g, hg⟩ := hfull.map_surjective (Fiber.fiberInclusion.map n)
    have hlift : r.IsHomLift (𝟙 U) (N.map g) := by
      rw [hg]
      exact n.2
    have hqlift : q.IsHomLift (𝟙 U) g :=
      isHomLift_of_isHomLift_map_of_comp_eq hN (𝟙 U) g hlift
    refine ⟨Fiber.homMk q U g, Fiber.hom_ext ?_⟩
    exact (fiberInclusion_map_fiberFunctorOfCompEq_map hN (Fiber.homMk q U g)).trans hg

end FibreFullyFaithful

variable {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {N : 𝒜 ⥤ ℬ}
variable [q.IsFibered] [r.IsFibered]

omit [q.IsFibered] [r.IsFibered] in
/-- **A 1-morphism of fibred categories identifies the vertical factors of two morphisms it
identifies**, the factors taken through a strongly cartesian morphism of the source. -/
private lemma map_map_eq_of_map_eq_of_isStronglyCartesian (hN : q.IsFibredOneMorphism r N) {R S : 𝒞}
    (f : R ⟶ S) {x a b : 𝒜} (φ : x ⟶ b) [q.IsStronglyCartesian f φ] (hf : f = 𝟙 R ≫ f)
    (m₁ m₂ : a ⟶ b) [q.IsHomLift f m₁] [q.IsHomLift f m₂] (h : N.map m₁ = N.map m₂) :
    N.map (IsStronglyCartesian.map q f φ hf m₁) = N.map (IsStronglyCartesian.map q f φ hf m₂) := by
  have := hN.map_isStronglyCartesian f φ inferInstance
  have := hN.map_isHomLift (𝟙 R) (IsStronglyCartesian.map q f φ hf m₁)
  have := hN.map_isHomLift (𝟙 R) (IsStronglyCartesian.map q f φ hf m₂)
  refine IsStronglyCartesian.ext r f (N.map φ) (𝟙 R) ?_
  rw [← N.map_comp, ← N.map_comp, IsStronglyCartesian.fac q f φ hf m₁,
    IsStronglyCartesian.fac q f φ hf m₂, h]

/-- **Two morphisms identified by a 1-morphism of fibred categories factor through one cartesian
lift via vertical morphisms with equal image** in the fibre functor. -/
private lemma exists_vertical_factors {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {N : 𝒜 ⥤ ℬ} [q.IsFibered]
    (hN : q.IsFibredOneMorphism r N) {a b : 𝒜}
    (m₁ m₂ : a ⟶ b) (h : N.map m₁ = N.map m₂) :
    q.map m₁ = q.map m₂ ∧ ∃ (fb : q.Fiber (q.obj a)) (lam : fb.1 ⟶ b)
      (n₁ n₂ : (Functor.Fiber.mk (rfl : q.obj a = q.obj a) : q.Fiber (q.obj a)) ⟶ fb),
      Fiber.fiberInclusion.map n₁ ≫ lam = m₁ ∧ Fiber.fiberInclusion.map n₂ ≫ lam = m₂ ∧
      (fiberFunctorOfCompEq hN.comp_eq (q.obj a)).map n₁ =
        (fiberFunctorOfCompEq hN.comp_eq (q.obj a)).map n₂ := by
  have l₁ : r.IsHomLift (q.map m₁) (N.map m₁) := hN.map_isHomLift (q.map m₁) m₁
  have l₂ : r.IsHomLift (q.map m₂) (N.map m₂) := hN.map_isHomLift (q.map m₂) m₂
  have hbase : q.map m₁ = q.map m₂ := base_eq_of_isHomLift_of_eq r _ _ _ _ h l₁ l₂
  -- the chosen cartesian lift of `q.map m₁` with target `b`
  set bF : q.Fiber (q.obj b) := Functor.Fiber.mk rfl
  set fb : q.Fiber (q.obj a) := Functor.pullbackFiber q bF (q.map m₁)
  set lam : fb.1 ⟶ b := Functor.IsPreFibered.pullbackMap bF.2 (q.map m₁)
  have hlamS : q.IsStronglyCartesian (q.map m₁) lam := by
    have : q.IsCartesian (q.map m₁) lam := Functor.IsPreFibered.pullbackMap.IsCartesian bF.2 _
    infer_instance
  have hone : q.map m₁ = 𝟙 (q.obj a) ≫ q.map m₁ := by simp
  have e₁ : q.IsHomLift (q.map m₁) m₁ := IsHomLift.map m₁
  have e₂ : q.IsHomLift (q.map m₁) m₂ := by
    rw [hbase]
    exact IsHomLift.map m₂
  -- the two vertical factors
  set t₁ := Functor.IsStronglyCartesian.map q (q.map m₁) lam hone m₁
  set t₂ := Functor.IsStronglyCartesian.map q (q.map m₁) lam hone m₂
  have ht₁lift : q.IsHomLift (𝟙 (q.obj a)) t₁ :=
    Functor.IsStronglyCartesian.map_isHomLift q (q.map m₁) lam hone m₁
  have ht₂lift : q.IsHomLift (𝟙 (q.obj a)) t₂ :=
    Functor.IsStronglyCartesian.map_isHomLift q (q.map m₁) lam hone m₂
  have hNt : N.map t₁ = N.map t₂ :=
    map_map_eq_of_map_eq_of_isStronglyCartesian hN _ lam hone m₁ m₂ h
  refine ⟨hbase, fb, lam, Functor.Fiber.homMk q (q.obj a) t₁, Functor.Fiber.homMk q (q.obj a) t₂,
    Functor.IsStronglyCartesian.fac q (q.map m₁) lam hone m₁,
    Functor.IsStronglyCartesian.fac q (q.map m₁) lam hone m₂, Functor.Fiber.hom_ext ?_⟩
  exact (fiberInclusion_map_fiberFunctorOfCompEq_map hN.comp_eq
    (Functor.Fiber.homMk q (q.obj a) t₁)).trans (hNt.trans
      (fiberInclusion_map_fiberFunctorOfCompEq_map hN.comp_eq
        (Functor.Fiber.homMk q (q.obj a) t₂)).symm)

/-- **Two morphisms of `𝒜` with the same image under `N` are locally equal.** This is the raw
form of the injectivity half of clause (1) of Stacks 02ZN, and the converse of
`CategoryTheory.Functor.isLocallyInjective_morPresheafMap`.

Both morphisms lie over one morphism `f` of the base, so each factors as a vertical morphism
followed by the chosen cartesian lift of `f`; the images of the two vertical factors agree because
`N` carries that lift to a strongly cartesian morphism. Local injectivity of the morphism
presheaves, read on the vertical factors, produces a covering sieve along whose members they agree,
and composing back with the cartesian lift gives local equality of the original morphisms. -/
theorem locallyEqual_of_map_eq (hN : q.IsFibredOneMorphism r N) (J : GrothendieckTopology 𝒞)
    (hinj : ∀ (U : 𝒞) (x y : q.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hN.morPresheafMap x y))
    {a b : 𝒜} (m₁ m₂ : a ⟶ b) (h : N.map m₁ = N.map m₂) :
    q.LocallyEqual J m₁ m₂ := by
  obtain ⟨hbase, fb, lam, n₁, n₂, hn₁, hn₂, hfiber⟩ := exists_vertical_factors hN m₁ m₂ h
  obtain ⟨R, hR, hspec⟩ := exists_covering_eq_of_baseHomUniverse hN J
    (hinj (q.obj a) (Functor.Fiber.mk (rfl : q.obj a = q.obj a)) fb) n₁ n₂ hfiber
  refine Functor.LocallyEqual.of_isStronglyCartesian hbase hR fun V f hf w φ hφ => ?_
  have hkey : Functor.IsPreFibered.pullbackMap (rfl : q.obj a = q.obj a) f ≫
        Functor.Fiber.fiberInclusion.map n₁ =
      Functor.IsPreFibered.pullbackMap (rfl : q.obj a = q.obj a) f ≫
        Functor.Fiber.fiberInclusion.map n₂ := by
    have d := congrArg (fun z => Functor.Fiber.fiberInclusion.map z ≫
      Functor.IsPreFibered.pullbackMap fb.2 f) (hspec f hf)
    exact ((Functor.pullbackFiberHom_fac n₁ f).symm.trans d).trans
      (Functor.pullbackFiberHom_fac n₂ f)
  have hcart : q.IsStronglyCartesian f
      (Functor.IsPreFibered.pullbackMap (rfl : q.obj a = q.obj a) f) := by
    have := Functor.IsPreFibered.pullbackMap.IsCartesian (rfl : q.obj a = q.obj a) f
    infer_instance
  have hφ' : q.IsHomLift f φ := hφ.toIsHomLift
  rw [← Functor.IsStronglyCartesian.fac q f
      (Functor.IsPreFibered.pullbackMap (rfl : q.obj a = q.obj a) f) (Category.id_comp f).symm φ,
    Category.assoc, Category.assoc, ← hn₁, ← hn₂]
  erw [← Category.assoc _ _ lam, hkey, Category.assoc]
  rfl

omit [r.IsFibered] in
/-- **A 1-morphism of fibred categories that is faithful on every fibre is faithful.** Two
morphisms with the same image lie over one morphism of the base, so each factors as a vertical
morphism followed by the chosen cartesian lift of that morphism; the images of the two vertical
factors agree because the image of the lift is strongly cartesian and cancels, and faithfulness on
the fibre finishes.

This is the exact counterpart of
`CategoryTheory.Functor.locallyEqual_of_map_eq`: where the morphism presheaves are only locally
injective one gets local equality, and where the induced functors on fibres are faithful one gets
equality. -/
@[sga "1 VI 6.10" "Faithfulness clause"]
theorem faithful_of_faithful_fiberFunctorOfCompEq (hN : q.IsFibredOneMorphism r N)
    (hfib : ∀ U : 𝒞, (fiberFunctorOfCompEq hN.comp_eq U).Faithful) : N.Faithful where
  map_injective {a b} m₁ m₂ h := by
    obtain ⟨-, fb, lam, n₁, n₂, hn₁, hn₂, hfiber⟩ := exists_vertical_factors hN m₁ m₂ h
    rw [← hn₁, ← hn₂, congrArg Functor.Fiber.fiberInclusion.map
      ((hfib (q.obj a)).map_injective hfiber)]

end CategoryTheory.Functor

end
