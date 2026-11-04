module

public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Reverse

/-!
# Condition (2) of Stacks 026F from condition (2) of Stacks 02ZI alone

`CategoryTheory.Functor.isMorSheaf_of_isStackInGroupoids`
(`StacksFrontier/CategoryTheory/Sites/Stack/StackBridge/Reverse.lean`) derives condition (2) of
Stacks 026F from the whole structure `CategoryTheory.Functor.IsStackInGroupoids`, hence in
particular from its clause (3). Its proof never uses clause (3), and a proof of clause (3) that
first refines the covering — `CategoryTheory.Functor.DescentDatum.isEffective_of_refinements` —
needs condition (2) of 026F as an input, so consuming the whole structure is circular there.

This file states the same implication from the two clauses that are actually used: that `p` is
fibred in groupoids, and the `isom_isSheaf` clause of
`CategoryTheory.Functor.IsStackInGroupoids` written out as a hypothesis. The second is the
family-indexed rendering `CategoryTheory.Functor.IsomIsSheafFor` of condition (2) of Stacks 02ZI;
the conclusion `CategoryTheory.Functor.IsMorSheaf` is the sieve-indexed rendering of condition (2)
of Stacks 026F, which is the shape every consumer of a morphism-sheaf hypothesis in the tree takes.

## Hypotheses

Both hypotheses of `CategoryTheory.Functor.isMorSheaf_of_isStackInGroupoids` are carried
unchanged, for the reasons recorded in the module docstring of
`StacksFrontier/CategoryTheory/Sites/Stack/StackBridge/Reverse.lean`: fibre products in the base,
because the family-indexed condition quantifies over *given* fibre products of the overlaps and so
says nothing about a covering sieve without them, and the index universe `max u₁ v₁`, because at a
smaller one the family-indexed condition constrains only the covering families indexed by a type
in that universe.

## Tagging

Nothing here carries a `@[stacks]` attribute. This is a translation between two renderings of one
clause, and Stacks 02ZJ is attached to `CategoryTheory.Functor.stackInGroupoids_tfae`, whose
clause (1) already states condition (2) of 02ZI in the sieve-indexed form, so it does not state
this translation; neither 026F nor 02ZI states it either, each stating only its own rendering.

## Main results

* `CategoryTheory.Functor.existsUnique_fiberHom_of_isomIsSheaf`: unique amalgamation of a
  compatible family of morphisms between chosen pullbacks along a covering family, from the
  `isom_isSheaf` clause alone.
* `CategoryTheory.Functor.isMorSheaf_of_isomIsSheaf`: condition (2) of Stacks 026F from the
  `isom_isSheaf` clause alone.

## References

* [Stacks 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Limits Opposite

universe w v₁ v₂ u₁ u₂

namespace Functor

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {p : 𝒳 ⥤ 𝒞} [p.IsFibered] {J : GrothendieckTopology 𝒞}

/-- **The gluing statement for the presheaf `Mor(x, y)` of Stacks 02ZB along a covering family,
from the `isom_isSheaf` clause of Stacks 02ZI alone.** This is
`CategoryTheory.Functor.existsUnique_fiberHom_of_isStackInGroupoids` with the structure
`CategoryTheory.Functor.IsStackInGroupoids` replaced by the two clauses of it that the argument
consumes: that `p` is fibred in groupoids, and condition (2) in its family-indexed form. Clause
(3) is not used.

A family of morphisms `ψ i : (f i)^* x ⟶ (f i)^* y` between the chosen pullbacks along a covering
family, whose base changes to any object mapping compatibly into two members agree, is the family
of base changes of a *unique* morphism `x ⟶ y` of the fibre over `S`.

The hypothesis `hisom` is applied with the chosen pullbacks as its restrictions
(`CategoryTheory.Functor.pullbackRestriction`) and with `CategoryTheory.Limits.pullback` as the
overlaps, which is where `HasPullbacks` is used; the compatibility it asks for over each overlap is
`CategoryTheory.Functor.isRestrictionOf_pullbackRestriction` for the base change of `ψ i` and, by
the hypothesis `hψ`, also for that of `ψ j`. Being fibred in groupoids is used only to discharge
the invertibility decorations of 02ZI: every morphism of a fibre is an isomorphism. -/
theorem existsUnique_fiberHom_of_isomIsSheaf [HasPullbacks 𝒞] (hgpd : p.IsFiberedInGroupoids)
    (hisom : ∀ {U : 𝒞} (a b : 𝒳) (ha : p.obj a = U) (hb : p.obj b = U)
      {K : Type w} (V : K → 𝒞) (g : ∀ k, V k ⟶ U),
      Sieve.ofArrows V g ∈ J U →
      ∀ (Vij : K → K → 𝒞)
        (pr₁ : ∀ k k', Vij k k' ⟶ V k) (pr₂ : ∀ k k', Vij k k' ⟶ V k')
        (hVij : ∀ k k', IsPullback (pr₁ k k') (pr₂ k k') (g k) (g k'))
        (ar : ∀ k, Restriction p (g k) a ha) (br : ∀ k, Restriction p (g k) b hb)
        (arij : ∀ k k', Restriction p (pr₁ k k' ≫ g k) a ha)
        (brij : ∀ k k', Restriction p (pr₁ k k' ≫ g k) b hb),
        IsomIsSheafFor p a b ha hb V g Vij pr₁ pr₂ hVij ar br arij brij)
    {S : 𝒞} {I : Type w} {X : I → 𝒞} (f : ∀ i, X i ⟶ S)
    (hf : Sieve.ofArrows X f ∈ J S) {x y : p.Fiber S}
    (ψ : ∀ i, pullbackFiber p x (f i) ⟶ pullbackFiber p y (f i))
    (hψ : ∀ (i j : I) {Z : 𝒞} (ε : Z ⟶ X i) (ε' : Z ⟶ X j) (q : Z ⟶ S)
      (h₁ : ε ≫ f i = q) (h₂ : ε' ≫ f j = q),
      baseChangeFiberMor (ψ i) ε q h₁ q h₁ = baseChangeFiberMor (ψ j) ε' q h₂ q h₂) :
    ∃! m : x ⟶ y, ∀ i, pullbackFiberHom m (f i) = ψ i := by
  have hVij : ∀ i j, IsPullback (Limits.pullback.fst (f i) (f j))
      (Limits.pullback.snd (f i) (f j)) (f i) (f j) :=
    fun i j => IsPullback.of_hasPullback (f i) (f j)
  have hsh := hisom (U := S) x.1 y.1 x.2 y.2 X f hf
    (fun i j => Limits.pullback (f i) (f j))
    (fun i j => Limits.pullback.fst (f i) (f j))
    (fun i j => Limits.pullback.snd (f i) (f j)) hVij
    (fun i => pullbackRestriction x (f i)) (fun i => pullbackRestriction y (f i))
    (fun i j => pullbackRestriction x (Limits.pullback.fst (f i) (f j) ≫ f i))
    (fun i j => pullbackRestriction y (Limits.pullback.fst (f i) (f j) ≫ f i))
  have hiso : ∀ {V : 𝒞} {a b : p.Fiber V} (m : a ⟶ b), IsIso (Fiber.fiberInclusion.map m) :=
    fun {V} _ _ _ => have := hgpd.fiber_isGroupoid V; inferInstance
  obtain ⟨g, ⟨hgfib, hgiso, hgr⟩, huniq⟩ := hsh (fun i => Fiber.fiberInclusion.map (ψ i))
    (fun i => fibreHom_of_fiberHom (ψ i)) (fun i => hiso (ψ i)) (by
      intro i j
      refine ⟨Fiber.fiberInclusion.map (baseChangeFiberMor (ψ i)
        (Limits.pullback.fst (f i) (f j)) _ rfl _ rfl), fibreHom_of_fiberHom _, ?_, ?_⟩
      · exact isRestrictionOf_pullbackRestriction (f i) (f i)
          (Limits.pullback.fst (f i) (f j)) rfl rfl (ψ i)
      · have hbc := hψ i j (Limits.pullback.fst (f i) (f j)) (Limits.pullback.snd (f i) (f j))
          (Limits.pullback.fst (f i) (f j) ≫ f i) rfl (hVij i j).w.symm
        rw [hbc]
        exact isRestrictionOf_pullbackRestriction (f j) (f j)
          (Limits.pullback.snd (f i) (f j)) (hVij i j).w (hVij i j).w (ψ j))
  refine ⟨fiberHomOfFibreHom hgfib, fun i => ?_, fun m' hm' => ?_⟩
  · rw [pullbackFiberHom_eq_iff_fac, fiberInclusion_map_fiberHomOfFibreHom]
    exact hgr i
  · have hinc : Fiber.fiberInclusion.map m' = g := by
      refine huniq _ ⟨fibreHom_of_fiberHom m', ?_, fun i => ?_⟩
      · exact hiso m'
      · exact ((pullbackFiberHom_eq_iff_fac (f i) m' (ψ i)).1 (hm' i))
    exact Fiber.fiberInclusion.map_injective
      (hinc.trans (fiberInclusion_map_fiberHomOfFibreHom hgfib).symm)

/-- **Condition (2) of Stacks 026F from the `isom_isSheaf` clause of Stacks 02ZI alone.** Over a
base with fibre products, and at index universe `max u₁ v₁`, the sheaf condition for the `Isom`
presheaves relative to every covering family — condition (2) of Stacks 02ZI in its family-indexed
form — gives the sheaf condition for the presheaves `Mor(x, y)` of Stacks 02ZB on the localized
sites `𝒞/U`, which is condition (2) of Stacks 026F.

This is `CategoryTheory.Functor.isMorSheaf_of_isStackInGroupoids` with
`CategoryTheory.Functor.IsStackInGroupoids` replaced by the two clauses of it that the argument
consumes. Dropping clause (3) is the whole point: a proof of clause (3) which first refines the
covering takes this conclusion as an input, so it cannot supply the structure.

Every covering sieve is the sieve generated by the family of all of its arrows
(`CategoryTheory.Sieve.ofArrows_category`), whose index type lies in `Type (max u₁ v₁)`; on that
family `CategoryTheory.Functor.existsUnique_fiberHom_of_isomIsSheaf` says that
`CategoryTheory.Pseudofunctor.toDescentData` is fully faithful, its compatibility hypothesis being
supplied by `CategoryTheory.Functor.baseChangeFiberMor_hom_eq`, and Mathlib's
`CategoryTheory.Pseudofunctor.IsPrestack.of_isPrestackFor` together with
`CategoryTheory.Functor.isPrestack_pullbackPseudofunctor_iff` passes from there to the sheaf
condition on the localized sites. -/
theorem isMorSheaf_of_isomIsSheaf [HasPullbacks 𝒞] (hgpd : p.IsFiberedInGroupoids)
    (hisom : ∀ {U : 𝒞} (a b : 𝒳) (ha : p.obj a = U) (hb : p.obj b = U)
      {K : Type max u₁ v₁} (V : K → 𝒞) (g : ∀ k, V k ⟶ U),
      Sieve.ofArrows V g ∈ J U →
      ∀ (Vij : K → K → 𝒞)
        (pr₁ : ∀ k k', Vij k k' ⟶ V k) (pr₂ : ∀ k k', Vij k k' ⟶ V k')
        (hVij : ∀ k k', IsPullback (pr₁ k k') (pr₂ k k') (g k) (g k'))
        (ar : ∀ k, Restriction p (g k) a ha) (br : ∀ k, Restriction p (g k) b hb)
        (arij : ∀ k k', Restriction p (pr₁ k k' ≫ g k) a ha)
        (brij : ∀ k k', Restriction p (pr₁ k k' ≫ g k) b hb),
        IsomIsSheafFor p a b ha hb V g Vij pr₁ pr₂ hVij ar br arij brij)
    (U : 𝒞) (x y : p.Fiber U) : IsMorSheaf p J U x y := by
  have hff : ∀ {S : 𝒞} {I : Type max u₁ v₁} {X : I → 𝒞} (f : ∀ i, X i ⟶ S),
      Sieve.ofArrows X f ∈ J S →
      Nonempty ((IsFibered.pullbackPseudofunctor p).toDescentData f).FullyFaithful := by
    intro S I X f hf
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro a b
    constructor
    · intro m m' hmm
      have key := existsUnique_fiberHom_of_isomIsSheaf hgpd hisom f hf
        (fun i => pullbackFiberHom m (f i))
        (fun i j Z ε ε' q h₁ h₂ => baseChangeFiberMor_hom_eq
          ((IsFibered.pullbackPseudofunctor p).toDescentData f |>.map m) ε ε' h₁ h₂)
      exact key.unique (fun _ => rfl)
        (fun i => (congrArg (fun ξ => Pseudofunctor.DescentData.Hom.hom ξ i) hmm).symm)
    · intro ξ
      obtain ⟨m, hm, -⟩ := existsUnique_fiberHom_of_isomIsSheaf hgpd hisom f hf
        (fun i => ξ.hom i)
        (fun i j Z ε ε' q h₁ h₂ => baseChangeFiberMor_hom_eq ξ ε ε' h₁ h₂)
      exact ⟨m, Pseudofunctor.DescentData.hom_ext hm⟩
  have hpre : (IsFibered.pullbackPseudofunctor p).IsPrestack J := by
    refine Pseudofunctor.IsPrestack.of_isPrestackFor (fun S R hR => ?_)
    rw [← Presieve.ofArrows_category R.arrows, Pseudofunctor.isPrestackFor_ofArrows_iff]
    exact hff _ (by rw [Sieve.ofArrows_category]; exact hR)
  exact (isPrestack_pullbackPseudofunctor_iff p J).1 hpre U x y

end Functor

end CategoryTheory

end
