module

public import StacksFrontier.CategoryTheory.Sites.DisjointCoverSections
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyExistence

/-!
# Morphisms of a fibre over a pairwise disjoint covering family

Let `p : 𝒳 ⥤ 𝒮` be a fibred category over a site `(𝒮, J)`. Condition (2) of **Stacks 026F** says
that the presheaf `Mor(x, y)` of **Stacks 02ZB** is a sheaf on `𝒮/U`. This file draws from that
condition the two statements a local construction of a morphism of a fibre needs, for a covering
family whose members are monomorphisms with pairwise empty overlaps:

* a family of morphisms between the chosen pullbacks along the members comes from one morphism
  `x ⟶ y` of the fibre, with no compatibility hypothesis;
* two morphisms of the *total* category lying over one and the same morphism of the base agree as
  soon as they agree after composition with the chosen cartesian lifts along the members of a
  covering sieve.

The second is the separatedness statement
`CategoryTheory.Functor.eq_of_pullbackFiberHom_locally_eq` for morphisms that are not vertical:
such a morphism is the vertical morphism into the chosen pullback of its target followed by the
chosen cartesian lift, and the composite of two chosen cartesian lifts is cartesian, so the
comparison may be made downstairs.

## Main results

* `CategoryTheory.Functor.exists_fiberHom_of_disjointCover`: the gluing, with the restrictions
  of the glued morphism prescribed.
* `CategoryTheory.Functor.eq_of_comp_pullbackMap_locally_eq`: the separatedness statement for
  morphisms over an arbitrary morphism of the base.
* `CategoryTheory.Functor.eq_of_comp_isStronglyCartesian_ofArrows_eq`: the same, tested against an
  arbitrary family of strongly cartesian morphisms over a generating family of the covering sieve.

## Implementation notes

The gluing is `CategoryTheory.Presieve.IsSheaf.existsUnique_section_of_disjoint_arrows` applied to
`Mor(x, y)` on `𝒮/U`, with the covering family of `𝒮/U` taken into the terminal object `𝟙 U`
through `CategoryTheory.Functor.overArrow`; the translation between the restriction maps of
`Mor(x, y)` and base change of a morphism of a fibre is
`CategoryTheory.Functor.morRestrict_morSection`, and reading a section over `𝟙 U` as a morphism of
the fibre is the inverse of `CategoryTheory.Functor.morSection`.

## References

* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
-/

@[expose] public section

namespace CategoryTheory

open Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

-- `Fiber` and its inclusion must unfold for the endpoints of the composites below to be seen as
-- equal at `implicit` transparency, as in
-- `StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks`.
attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮}

/-- **Morphisms of a fibre glue over a pairwise disjoint covering family.** Let `x`, `y` be
objects of the fibre of a fibred category over `U`, let `{ jj i : X i ⟶ U }` be a covering family
of monomorphisms whose pairwise overlaps are covered by the empty sieve, and let `Mor(x, y)` be a
sheaf on `𝒮/U`. Then every family of morphisms `(jj i)^* x ⟶ (jj i)^* y` of the fibres over the
members is the family of base changes of a single morphism `x ⟶ y`.

No compatibility datum is needed: a disjoint covering family imposes none, because an object
mapping to two distinct members carries only one section of a sheaf. -/
theorem exists_fiberHom_of_disjointCover {J : GrothendieckTopology 𝒮} {x y : p.Fiber U}
    (hmor : p.IsMorSheaf J U x y)
    {K : Type*} (X : K → 𝒮) (jj : ∀ i, X i ⟶ U) (hm : ∀ i, Mono (jj i))
    (hj : Sieve.ofArrows X jj ∈ J U)
    (hd : ∀ i l, i ≠ l → ∀ {Y : 𝒮} (a : Y ⟶ X i) (b : Y ⟶ X l),
      a ≫ jj i = b ≫ jj l → (⊥ : Sieve Y) ∈ J Y)
    (m : ∀ i, pullbackFiber p x (jj i) ⟶ pullbackFiber p y (jj i)) :
    ∃ c : x ⟶ y, ∀ i, pullbackFiberHom c (jj i) = m i := by
  classical
  have hm' : ∀ i, Mono (overArrow (U := U) (jj i)) := by
    intro i
    have hmono : Mono ((Over.forget U).map (overArrow (U := U) (jj i))) := hm i
    exact (Over.forget U).mono_of_mono_map hmono
  have hj' : Sieve.ofArrows (fun i => (Over.mk (jj i) : Over U))
      (fun i => overArrow (U := U) (jj i)) ∈ (J.over U) (Over.mk (𝟙 U)) := by
    refine (J.mem_over_iff _).mpr ?_
    rw [Sieve.overEquiv_ofArrows]
    show Sieve.ofArrows X jj ∈ J U
    exact hj
  have hd' : ∀ i l, i ≠ l → ∀ {Y : Over U} (a : Y ⟶ (Over.mk (jj i) : Over U))
      (b : Y ⟶ (Over.mk (jj l) : Over U)),
      a ≫ overArrow (U := U) (jj i) = b ≫ overArrow (U := U) (jj l) →
        (⊥ : Sieve Y) ∈ (J.over U) Y := by
    intro i l hil Y a b hab
    refine (J.mem_over_iff _).mpr ?_
    simpa using hd i l hil a.left b.left (congrArg (fun q => q.left) hab)
  obtain ⟨t, ht, -⟩ :=
    ((isSheaf_iff_isSheaf_of_type _ _).1 hmor).existsUnique_section_of_disjoint_arrows
      (fun i => overArrow (U := U) (jj i)) hj' hm' hd' m
  refine ⟨(pullbackFiberIdIso x).inv ≫ t ≫ (pullbackFiberIdIso y).hom, fun i => ?_⟩
  have hsec : morSection p x y ((pullbackFiberIdIso x).inv ≫ t ≫ (pullbackFiberIdIso y).hom)
      = t := by
    simp only [morSection, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  rw [← morRestrict_morSection p x y _ (jj i), hsec]
  exact ht i

/-- **Two morphisms over one and the same morphism of the base which agree locally are equal.**
Let `x` be an object of the fibre over `U`, let `y` be an object of the fibre over `U'`, and let
`φ`, `ψ` be morphisms `x ⟶ y` of the total category lying over `f : U ⟶ U'`. If the presheaf
`Mor(x, f^* y)` is a sheaf on `𝒮/U` and `φ` and `ψ` agree after composition with the chosen
cartesian lift at `x` of every member of a covering sieve of `U`, then `φ = ψ`.

This is `CategoryTheory.Functor.eq_of_pullbackFiberHom_locally_eq` for morphisms that need not be
vertical: `φ` factors uniquely as a vertical morphism `x ⟶ f^* y` followed by the chosen
cartesian lift of `f`, and the composite of the chosen cartesian lifts of a member and of `f` is
cartesian, which turns the hypothesis into an equality of the base changes of the two vertical
factors. -/
lemma eq_of_comp_pullbackMap_locally_eq {J : GrothendieckTopology 𝒮} {U' : 𝒮}
    {x : p.Fiber U} {y : p.Fiber U'} (f : U ⟶ U')
    (hmor : p.IsMorSheaf J U x (pullbackFiber p y f))
    {R : Sieve U} (hR : R ∈ J U) {φ ψ : x.1 ⟶ y.1}
    (hφ : p.IsHomLift f φ) (hψ : p.IsHomLift f ψ)
    (h : ∀ ⦃V : 𝒮⦄ (g : V ⟶ U), R g →
      IsPreFibered.pullbackMap x.2 g ≫ φ = IsPreFibered.pullbackMap x.2 g ≫ ψ) :
    φ = ψ := by
  have hκ : p.IsCartesian f (IsPreFibered.pullbackMap y.2 f) :=
    IsPreFibered.pullbackMap.IsCartesian y.2 f
  have key : ∀ θ : x.1 ⟶ y.1, p.IsHomLift f θ → ∃ m : x ⟶ pullbackFiber p y f,
      Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap y.2 f = θ := fun θ hθ =>
    ⟨⟨IsCartesian.map p f (IsPreFibered.pullbackMap y.2 f) θ, inferInstance⟩,
      IsCartesian.fac p f (IsPreFibered.pullbackMap y.2 f) θ⟩
  obtain ⟨m, hmfac⟩ := key φ hφ
  obtain ⟨n, hnfac⟩ := key ψ hψ
  have hmn : m = n := by
    refine eq_of_pullbackFiberHom_locally_eq p hmor hR ?_
    intro V g hg
    have hcomp : p.IsCartesian (g ≫ f)
        (IsPreFibered.pullbackMap (pullbackFiber p y f).2 g ≫
          IsPreFibered.pullbackMap y.2 f) := by
      have h₁ : p.IsStronglyCartesian g
          (IsPreFibered.pullbackMap (pullbackFiber p y f).2 g) := by
        have : p.IsCartesian g (IsPreFibered.pullbackMap (pullbackFiber p y f).2 g) :=
          IsPreFibered.pullbackMap.IsCartesian (pullbackFiber p y f).2 g
        infer_instance
      have h₂ : p.IsStronglyCartesian f (IsPreFibered.pullbackMap y.2 f) := by
        have := hκ
        infer_instance
      have := h₁
      have := h₂
      infer_instance
    refine fiber_hom_ext_of_cartesian (g ≫ f)
      (IsPreFibered.pullbackMap (pullbackFiber p y f).2 g ≫
        IsPreFibered.pullbackMap y.2 f) hcomp _ _ ?_
    rw [← Category.assoc, ← Category.assoc, pullbackFiberHom_fac, pullbackFiberHom_fac,
      Category.assoc, Category.assoc, hmfac, hnfac]
    exact h g hg
  rw [← hmfac, ← hnfac, hmn]

/-- **Two morphisms over one and the same morphism of the base which agree on a covering family
are equal**, tested against an arbitrary family of strongly cartesian morphisms over the members
rather than against the chosen pullbacks.

This is `CategoryTheory.Functor.eq_of_comp_pullbackMap_locally_eq` in the form a geometric
argument supplies its hypothesis in: the cartesian lift at hand is rarely the chosen one, and a
covering sieve is rarely presented other than as the sieve generated by a family. A member of the
generated sieve factors through a member of the family, and the chosen pullback map of such a
factorization factors through the given cartesian morphism by its universal property. -/
lemma eq_of_comp_isStronglyCartesian_ofArrows_eq {J : GrothendieckTopology 𝒮} {U' : 𝒮}
    {x : p.Fiber U} {y : p.Fiber U'} (f : U ⟶ U')
    (hmor : p.IsMorSheaf J U x (pullbackFiber p y f))
    {K : Type*} (X : K → 𝒮) (jj : ∀ i, X i ⟶ U) (hj : Sieve.ofArrows X jj ∈ J U)
    {z : K → 𝒳} (ζ : ∀ i, z i ⟶ x.1) (hζ : ∀ i, p.IsStronglyCartesian (jj i) (ζ i))
    {φ ψ : x.1 ⟶ y.1} (hφ : p.IsHomLift f φ) (hψ : p.IsHomLift f ψ)
    (h : ∀ i, ζ i ≫ φ = ζ i ≫ ψ) : φ = ψ := by
  refine eq_of_comp_pullbackMap_locally_eq p f hmor hj hφ hψ ?_
  intro V u hu
  obtain ⟨Y, v, r, hr, hfac⟩ := hu
  obtain ⟨i⟩ := hr
  have hlift : p.IsHomLift u (IsPreFibered.pullbackMap x.2 u) :=
    (IsPreFibered.pullbackMap.IsCartesian x.2 u).toIsHomLift
  have hcart := hζ i
  have hξ : IsStronglyCartesian.map p (jj i) (ζ i) (f' := u) hfac.symm
      (IsPreFibered.pullbackMap x.2 u) ≫ ζ i = IsPreFibered.pullbackMap x.2 u :=
    IsStronglyCartesian.fac p (jj i) (ζ i) hfac.symm (IsPreFibered.pullbackMap x.2 u)
  rw [← hξ, Category.assoc, Category.assoc, h i]

end Functor

end CategoryTheory

end
