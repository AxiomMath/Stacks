module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Defs
public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.FiberedCategory.CompFibered
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing
public import StacksFrontier.CategoryTheory.Sites.Stack.FibredOneMorphismPullback
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.StackOverStack.Preliminaries
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.StackOverStack.MorSheaf
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.StackOverStack.TransferredDatum
import all StacksFrontier.CategoryTheory.Sites.InheritedTopology.StackOverStack.TransferredDatum

/-!
# A stack over a stack is a stack over the base

Let `(𝒞, J)` be a site and let `p : 𝒳 ⥤ 𝒞` be a stack over `𝒞` (Stacks 026F,
`CategoryTheory.Functor.IsStack`). Endow `𝒳` with the topology `J𝒳` inherited from `(𝒞, J)`
(Stacks 06NV): a family of strongly `p`-cartesian morphisms of `𝒳` covers exactly when its family
of images covers in `𝒞`. Stacks 09WX says that a stack `q : 𝒴 ⥤ 𝒳` over the site `(𝒳, J𝒳)` is
again a stack over `𝒞`, along `q ⋙ p`, and that if moreover `p` and `q` are stacks in groupoids
then so is `q ⋙ p`.

## Main results

* `CategoryTheory.Functor.isStack_comp_of_isInheritedTopology`: if `p` is a stack over `(𝒞, J)`,
  `J𝒳` is inherited from `(𝒞, J)` and `q` is a stack over `(𝒳, J𝒳)`, then `q ⋙ p` is a stack over
  `(𝒞, J)`, and it is a stack in groupoids when `p` and `q` are fibred in groupoids.

## Implementation notes

The inherited topology enters as the hypothesis
`CategoryTheory.Functor.IsInheritedTopology p J J𝒳` on a given topology of `𝒳`, rather than as the
construction `CategoryTheory.Functor.inheritedTopology` (Stacks 06NV), which is one such topology.

The universe of the index types of `IsInheritedTopology` is fixed to `max u₂ v₂`, the universe in
which the family of all arrows of a sieve on `𝒳` lives.

"Stack in groupoids over `𝒞`" is read as in Stacks 02ZJ (3): a category fibred in groupoids
(Stacks 003S) which is a stack (Stacks 026F).

The private declarations of `StackOverStack.TransferredDatum` are used here through `import all`.

## References

* [Stacks 09WX](https://stacks.math.columbia.edu/tag/09WX)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃ ua ub va vb

variable {𝒞 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃} [Category.{v₁} 𝒞] [Category.{v₂} 𝒳]
  [Category.{v₃} 𝒴] {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒳} {J : GrothendieckTopology 𝒞}
  {J𝒳 : GrothendieckTopology 𝒳}

/-! ### Assembling condition (3) -/

set_option backward.isDefEq.respectTransparency false in
/-- Given an object `y` of `𝒴` descending the transferred datum, `D` is effective. -/
private lemma c3_isEffective (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered]
    [(q ⋙ p).IsFibered] {y : 𝒴} {R₀ : Sieve (p.obj (q.obj y))} (D₀ : SieveDescentDatum (q ⋙ p) R₀)
    (ζ₀ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ p.obj (q.obj y)) (hf : R₀ f), q.obj (D₀.obj f hf).1 ⟶ q.obj y)
    (hζc₀ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ p.obj (q.obj y)) (hf : R₀ f), p.IsCartesian f (ζ₀ f hf))
    (hζg₀ : c3_Compat p q D₀ ζ₀)
    (ξ : ∀ ⦃c : 𝒳⦄ (h : c ⟶ q.obj y) (hh : R₀ (p.map h)), (c3_obj p q D₀ ζ₀ hζc₀ h hh).1 ⟶ y)
    (hξc : ∀ ⦃c : 𝒳⦄ (h : c ⟶ q.obj y) (hh : R₀ (p.map h)), q.IsCartesian h (ξ h hh))
    (hξg :
      ∀ ⦃c₁ c₂ d : 𝒳⦄ ⦃h₁ : c₁ ⟶ q.obj y⦄ (hh₁ : R₀ (p.map h₁)) ⦃h₂ : c₂ ⟶ q.obj y⦄
        (hh₂ : R₀ (p.map h₂)) (ε : d ⟶ c₁) (ε' : d ⟶ c₂) (heq : ε ≫ h₁ = ε' ≫ h₂),
        Fiber.fiberInclusion.map
              (c3_gl p q D₀ ζ₀ hζc₀ h₁ hh₁ h₂ hh₂ ε ε' (p.map ε) rfl (p.map ε') rfl
                  (by rw [← p.map_comp, ← p.map_comp, heq]) hζg₀ heq).hom ≫
            IsPreFibered.pullbackMap (c3_obj p q D₀ ζ₀ hζc₀ h₂ hh₂).2 ε' ≫ ξ h₂ hh₂ =
          IsPreFibered.pullbackMap (c3_obj p q D₀ ζ₀ hζc₀ h₁ hh₁).2 ε ≫ ξ h₁ hh₁) :
    D₀.IsEffective := by
  refine ⟨⟨y, rfl⟩, fun {V} f hf => c3_zfin p q D₀ ζ₀ hζc₀ hζg₀ ξ f hf, fun {V} f hf => ?_, ?_⟩
  · have hz : p.IsCartesian f (ζ₀ f hf) := hζc₀ f hf
    have := hz
    have hx : q.IsCartesian (ζ₀ f hf) (ξ (ζ₀ f hf) (c3_hhf p q D₀ ζ₀ hζc₀ f hf)) := hξc _ _
    have := hx
    have hei := c3_ehom_isIso p q D₀ ζ₀ hζc₀ hζg₀ f hf
    have := hei
    have hehl := c3_ehom_homLift p q D₀ ζ₀ hζc₀ hζg₀ f hf
    have := hehl
    have hinv :
      q.IsHomLift (𝟙 (q.obj (D₀.obj f hf).1)) (CategoryTheory.inv (c3_ehom p q D₀ ζ₀ hζc₀ f hf)) :=
      inferInstance
    have := hinv
    have h1 :
      q.IsStronglyCartesian (𝟙 (q.obj (D₀.obj f hf).1) ≫ ζ₀ f hf)
        (CategoryTheory.inv (c3_ehom p q D₀ ζ₀ hζc₀ f hf) ≫
          ξ (ζ₀ f hf) (c3_hhf p q D₀ ζ₀ hζc₀ f hf)) :=
      inferInstance
    rw [Category.id_comp] at h1
    have := h1
    have h2 :
      (q ⋙ p).IsStronglyCartesian f
        (CategoryTheory.inv (c3_ehom p q D₀ ζ₀ hζc₀ f hf) ≫
          ξ (ζ₀ f hf) (c3_hhf p q D₀ ζ₀ hζc₀ f hf)) :=
      IsStronglyCartesian.comp_functor q p f (ζ₀ f hf) _
    have := h2
    unfold c3_zfin
    infer_instance
  · intro V W Z f hf g hg ε ε' heq
    have key : ∀ {V : 𝒞} (f : V ⟶ p.obj (q.obj y)) (hf : R₀ f)
        [IsIso (c3_ehom p q D₀ ζ₀ hζc₀ f hf)] {X : 𝒴} (P : X ⟶ (D₀.obj f hf).1),
        q.IsStronglyCartesian (q.map P) P →
        ∃ ω : X ⟶ IsPreFibered.pullbackObj
            (c3_obj p q D₀ ζ₀ hζc₀ (ζ₀ f hf) (c3_hhf p q D₀ ζ₀ hζc₀ f hf)).2 (q.map P),
          q.IsHomLift (𝟙 (q.obj X)) ω ∧
            ω ≫ IsPreFibered.pullbackMap
              (c3_obj p q D₀ ζ₀ hζc₀ (ζ₀ f hf) (c3_hhf p q D₀ ζ₀ hζc₀ f hf)).2 (q.map P) =
              P ≫ CategoryTheory.inv (c3_ehom p q D₀ ζ₀ hζc₀ f hf) ∧
            ω ≫ IsPreFibered.pullbackMap
              (c3_obj p q D₀ ζ₀ hζc₀ (ζ₀ f hf) (c3_hhf p q D₀ ζ₀ hζc₀ f hf)).2 (q.map P) ≫
              c3_ehom p q D₀ ζ₀ hζc₀ f hf = P := by
      intro V f hf _ X P hP
      have := c3_ehom_homLift p q D₀ ζ₀ hζc₀ hζg₀ f hf
      have : q.IsHomLift (𝟙 (q.obj (D₀.obj f hf).1))
          (CategoryTheory.inv (c3_ehom p q D₀ ζ₀ hζc₀ f hf)) := inferInstance
      have : q.IsHomLift (q.map P) (P ≫ CategoryTheory.inv (c3_ehom p q D₀ ζ₀ hζc₀ f hf)) :=
        c3_homLift_of_eq q (n := q.map P ≫ 𝟙 (q.obj (D₀.obj f hf).1)) inferInstance (by simp)
      have : q.IsCartesian (q.map P)
          (IsPreFibered.pullbackMap
            (c3_obj p q D₀ ζ₀ hζc₀ (ζ₀ f hf) (c3_hhf p q D₀ ζ₀ hζc₀ f hf)).2 (q.map P)) :=
        IsPreFibered.pullbackMap.IsCartesian _ _
      obtain ⟨ω, ⟨hω1, hω2⟩, -⟩ := factor_over_cart q (q.map P)
        (IsPreFibered.pullbackMap
          (c3_obj p q D₀ ζ₀ hζc₀ (ζ₀ f hf) (c3_hhf p q D₀ ζ₀ hζc₀ f hf)).2 (q.map P))
        (P ≫ CategoryTheory.inv (c3_ehom p q D₀ ζ₀ hζc₀ f hf))
      exact ⟨ω, hω1, hω2, by
        rw [← Category.assoc, hω2, Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩
    have := c3_ehom_isIso p q D₀ ζ₀ hζc₀ hζg₀ f hf
    have := c3_ehom_isIso p q D₀ ζ₀ hζc₀ hζg₀ g hg
    have := c3_ehom_homLift p q D₀ ζ₀ hζc₀ hζg₀ g hg
    have := c3_pi_sc' p q (D₀.obj f hf) ε
    have : (q ⋙ p).IsHomLift ε'
        ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
          IsPreFibered.pullbackMap (D₀.obj g hg).2 ε') := by
      have h0 :
        (q ⋙ p).IsHomLift (𝟙 Z ≫ ε')
          ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
            IsPreFibered.pullbackMap (D₀.obj g hg).2 ε') :=
        inferInstance
      rwa [Category.id_comp] at h0
    have hPgqp :
      (q ⋙ p).IsStronglyCartesian ε'
        ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
          IsPreFibered.pullbackMap (D₀.obj g hg).2 ε') := by
      have h1 :
        (q ⋙ p).IsStronglyCartesian (𝟙 Z) (Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) :=
        IsStronglyCartesian.of_isIso (q ⋙ p) (𝟙 Z) _
      have := h1
      have h0 :
        (q ⋙ p).IsStronglyCartesian (𝟙 Z ≫ ε')
          ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
            IsPreFibered.pullbackMap (D₀.obj g hg).2 ε') :=
        inferInstance
      rwa [Category.id_comp] at h0
    have hPg := (comp_cart p q ε'
          ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
            IsPreFibered.pullbackMap (D₀.obj g hg).2 ε')).2
    obtain ⟨ωf, hωf1, hωf2, hωf2'⟩ :=
      key f hf (X := (pullbackFiber (q ⋙ p) (D₀.obj f hf) ε).1)
        (IsPreFibered.pullbackMap (D₀.obj f hf).2 ε) inferInstance
    obtain ⟨ωg, hωg1, hωg2, hωg2'⟩ :=
      key g hg (X := (pullbackFiber (q ⋙ p) (D₀.obj f hf) ε).1)
        ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
          IsPreFibered.pullbackMap (D₀.obj g hg).2 ε') hPg
    have hthat := c3_om_that p q D₀ ζ₀ hζc₀ hζg₀ f hf ε ωf hωf1 hωf2'
    have hegsc :
      q.IsStronglyCartesian
        (q.map
          ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
            IsPreFibered.pullbackMap (D₀.obj g hg).2 ε'))
        (IsPreFibered.pullbackMap (c3_obj p q D₀ ζ₀ hζc₀ (ζ₀ g hg) (c3_hhf p q D₀ ζ₀ hζc₀ g hg)).2
            (q.map
              ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
                IsPreFibered.pullbackMap (D₀.obj g hg).2 ε')) ≫
          (c3_ehom p q D₀ ζ₀ hζc₀ g hg)) := by
      have hegs :
        q.IsStronglyCartesian (𝟙 (q.obj (D₀.obj g hg).1)) (c3_ehom p q D₀ ζ₀ hζc₀ g hg) :=
        IsStronglyCartesian.of_isIso q (𝟙 (q.obj (D₀.obj g hg).1)) _
      have := hegs
      have h0 :
        q.IsStronglyCartesian
          ((q.map
              ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
                IsPreFibered.pullbackMap (D₀.obj g hg).2 ε')) ≫
            𝟙 (q.obj (D₀.obj g hg).1))
          (IsPreFibered.pullbackMap
              (c3_obj p q D₀ ζ₀ hζc₀ (ζ₀ g hg) (c3_hhf p q D₀ ζ₀ hζc₀ g hg)).2
              (q.map
                ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
                  IsPreFibered.pullbackMap (D₀.obj g hg).2 ε')) ≫
            (c3_ehom p q D₀ ζ₀ hζc₀ g hg)) :=
        inferInstance
      rwa [Category.comp_id] at h0
    have := hegsc
    have hGL :
      q.IsHomLift (𝟙 (q.obj (pullbackFiber (q ⋙ p) (D₀.obj f hf) ε).1))
        (Fiber.fiberInclusion.map
          (c3_gl p q D₀ ζ₀ hζc₀ (ζ₀ f hf) (c3_hhf p q D₀ ζ₀ hζc₀ f hf) (ζ₀ g hg)
              (c3_hhf p q D₀ ζ₀ hζc₀ g hg) (q.map (IsPreFibered.pullbackMap (D₀.obj f hf).2 ε))
              (q.map
                ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
                  IsPreFibered.pullbackMap (D₀.obj g hg).2 ε'))
              (p.map (q.map (IsPreFibered.pullbackMap (D₀.obj f hf).2 ε))) rfl
              (p.map
                (q.map
                  ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
                    IsPreFibered.pullbackMap (D₀.obj g hg).2 ε')))
              rfl (c3_hcomm p q D₀ ζ₀ hζg₀ f hf g hg ε ε' heq) hζg₀
              (c3_hE p q D₀ ζ₀ hζg₀ f hf g hg ε ε' heq)).hom) :=
      inferInstance
    have := hGL
    have hfg :
      q.IsHomLift (𝟙 (q.obj (pullbackFiber (q ⋙ p) (D₀.obj f hf) ε).1))
        (ωf ≫
          Fiber.fiberInclusion.map
            (c3_gl p q D₀ ζ₀ hζc₀ (ζ₀ f hf) (c3_hhf p q D₀ ζ₀ hζc₀ f hf) (ζ₀ g hg)
                (c3_hhf p q D₀ ζ₀ hζc₀ g hg) (q.map (IsPreFibered.pullbackMap (D₀.obj f hf).2 ε))
                (q.map
                  ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
                    IsPreFibered.pullbackMap (D₀.obj g hg).2 ε'))
                (p.map (q.map (IsPreFibered.pullbackMap (D₀.obj f hf).2 ε))) rfl
                (p.map
                  (q.map
                    ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
                      IsPreFibered.pullbackMap (D₀.obj g hg).2 ε')))
                rfl (c3_hcomm p q D₀ ζ₀ hζg₀ f hf g hg ε ε' heq) hζg₀
                (c3_hE p q D₀ ζ₀ hζg₀ f hf g hg ε ε' heq)).hom) :=
      c3_homLift_of_eq q (n :=
        𝟙 (q.obj (pullbackFiber (q ⋙ p) (D₀.obj f hf) ε).1) ≫
          𝟙 (q.obj (pullbackFiber (q ⋙ p) (D₀.obj f hf) ε).1))
        inferInstance (by simp)
    have := hfg
    have hQ :
      ωg =
        ωf ≫
          Fiber.fiberInclusion.map
            (c3_gl p q D₀ ζ₀ hζc₀ (ζ₀ f hf) (c3_hhf p q D₀ ζ₀ hζc₀ f hf) (ζ₀ g hg)
                (c3_hhf p q D₀ ζ₀ hζc₀ g hg) (q.map (IsPreFibered.pullbackMap (D₀.obj f hf).2 ε))
                (q.map
                  ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
                    IsPreFibered.pullbackMap (D₀.obj g hg).2 ε'))
                (p.map (q.map (IsPreFibered.pullbackMap (D₀.obj f hf).2 ε))) rfl
                (p.map
                  (q.map
                    ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
                      IsPreFibered.pullbackMap (D₀.obj g hg).2 ε')))
                rfl (c3_hcomm p q D₀ ζ₀ hζg₀ f hf g hg ε ε' heq) hζg₀
                (c3_hE p q D₀ ζ₀ hζg₀ f hf g hg ε ε' heq)).hom := by
      refine
        IsStronglyCartesian.ext q
          (q.map
            ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
              IsPreFibered.pullbackMap (D₀.obj g hg).2 ε'))
          (IsPreFibered.pullbackMap
              (c3_obj p q D₀ ζ₀ hζc₀ (ζ₀ g hg) (c3_hhf p q D₀ ζ₀ hζc₀ g hg)).2
              (q.map
                ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
                  IsPreFibered.pullbackMap (D₀.obj g hg).2 ε')) ≫
            (c3_ehom p q D₀ ζ₀ hζc₀ g hg))
          (𝟙 (q.obj (pullbackFiber (q ⋙ p) (D₀.obj f hf) ε).1)) ?_
      rw [hωg2', Category.assoc, c3_chain p q D₀ ζ₀ hζc₀ hζg₀ f hf g hg ε ε' heq, ← Category.assoc,
        hthat]
      exact (Category.id_comp _).symm
    unfold c3_zfin
    rw [← Category.assoc, ← Category.assoc, ← hωg2, ← Category.assoc, ← hωf2]
    simp only [Category.assoc]
    rw [←
      hξg (c3_hhf p q D₀ ζ₀ hζc₀ f hf) (c3_hhf p q D₀ ζ₀ hζc₀ g hg)
        (q.map (IsPreFibered.pullbackMap (D₀.obj f hf).2 ε))
        (q.map
          ((Fiber.fiberInclusion.map (D₀.iso hf hg ε ε' heq).hom) ≫
            IsPreFibered.pullbackMap (D₀.obj g hg).2 ε'))
        (c3_hE p q D₀ ζ₀ hζg₀ f hf g hg ε ε' heq),
      hQ]
    simp [Category.assoc]

/-- **Condition (3) of Stacks 026F for `q ⋙ p`.** Let `p : 𝒳 ⥤ 𝒞` be a stack over the site
`(𝒞, J)`, let `J𝒳` be a topology of `𝒳` inherited from `(𝒞, J)` and let `q : 𝒴 ⥤ 𝒳` be a stack
over `(𝒳, J𝒳)`. Then descent along a `J`-covering sieve is effective for `q ⋙ p`. -/
private lemma comp_hasEffectiveDescent (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) {J : GrothendieckTopology 𝒞}
    {J𝒳 : GrothendieckTopology 𝒳} (hp : p.IsStack J) (hJ𝒳 : IsInheritedTopology.{max u₂ v₂} p J J𝒳)
    (hq : q.IsStack J𝒳) :
    haveI : p.IsFibered := hp.isFibered
    haveI : q.IsFibered := hq.isFibered
    haveI : (q ⋙ p).IsFibered := IsFibered.comp_functor q p
    HasEffectiveDescent (q ⋙ p) J := by
  have : p.IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  have : (q ⋙ p).IsFibered := IsFibered.comp_functor q p
  intro U R hR D
  obtain ⟨⟨a, rfl⟩, ζ', hζ'c, hζ'g⟩ :=
    hp.hasEffectiveDescent R hR (SieveDescentDatum.mapF (isFibredOneMorphism_comp p q) D)
  have hstar : c3_Compat p q D ζ' := c3_zeta_compat p q D ζ' hζ'g
  have hT : R.functorPullback p ∈ J𝒳 a := sieve_transfer p hJ𝒳 a R hR
  obtain ⟨⟨y, rfl⟩, ξ, hξc, hξg⟩ :=
    hq.hasEffectiveDescent (R.functorPullback p) hT (c3_datum p q D ζ' hζ'c hstar)
  exact c3_isEffective p q D ζ' hζ'c hstar ξ hξc hξg

/-- Let `(𝒞, J)` be a site, let `p : 𝒳 ⥤ 𝒞` be a stack over `𝒞`, endow `𝒳` with the topology `J𝒳`
inherited from `(𝒞, J)` and let `q : 𝒴 ⥤ 𝒳` be a stack over `(𝒳, J𝒳)`. Then `𝒴` is a stack over
`𝒞`, along `q ⋙ p`; and if `p` and `q` define stacks in groupoids, that is if both are fibred in
groupoids, then `𝒴` is a stack in groupoids over `𝒞`. -/
@[stacks 09WX]
public theorem isStack_comp_of_isInheritedTopology (hp : p.IsStack J)
    (hJ𝒳 : IsInheritedTopology.{max u₂ v₂} p J J𝒳) (hq : q.IsStack J𝒳) :
    (q ⋙ p).IsStack J ∧
      (p.IsFiberedInGroupoids →
        q.IsFiberedInGroupoids → (q ⋙ p).IsFiberedInGroupoids ∧ (q ⋙ p).IsStack J) := by
  have hst : (q ⋙ p).IsStack J :=
    have : p.IsFibered := hp.isFibered
    have : q.IsFibered := hq.isFibered
    { isFibered := IsFibered.comp_functor q p
      isMorSheaf := comp_isMorSheaf p q hp hJ𝒳 hq
      hasEffectiveDescent := comp_hasEffectiveDescent p q hp hJ𝒳 hq }
  exact ⟨hst, fun hpg hqg => ⟨IsFiberedInGroupoids.comp q p hqg hpg, hst⟩⟩

end CategoryTheory.Functor
