module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance

/-!
# Internal Hom carries a local cokernel in the first variable to a kernel

Let `O` be a presheaf of commutative rings on a category `C` and let `F ↦ Hom_O(F, G)` be the
internal Hom of [Stacks, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM) with a fixed
target `G`.  If `b : B ⟶ N` behaves like a cokernel of `a : A ⟶ B` *after restriction to every
slice* `C/V`, then precomposition with `b` identifies `Hom_O(N, G)` with the kernel of
precomposition with `a`:

`Hom_O(N, G) ≅ ker (Hom_O(B, G) ⟶ Hom_O(A, G))`.

This is the kernel form of left exactness of internal Hom in the first variable --- part (1) of
[Stacks, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY), equivalently assertion (1) of
[Stacks, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO) --- and it is the form in which
the proof of [Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ) uses it: dualizing a
finite presentation `𝒪_U^{⊕ m} ⟶ 𝒪_U^{⊕ n} ⟶ F|_U ⟶ 0` exhibits the dual `F^∨|_U` as the
kernel of a map between the duals of the two finite free modules.

## Why the hypotheses are stated locally, and not as an exact sequence

The section of `Hom_O(N, G)` over `V` is, by the construction of Tag 03EM, literally the module
of morphisms `N|_V ⟶ G|_V` on the slice `C/V`, and the restriction maps of the internal Hom
presheaf are reindexing.  So the two properties of `b` that the argument needs are properties of
each restriction `b|_V`, namely that precomposition with it is injective and that it is onto the
morphisms killing `a|_V`; both are recorded as hypotheses.

That matters for the intended application, where `A`, `B`, `N` and `G` are *sheaves* of modules
and `b` is a cokernel in the category of sheaves of modules.  An epimorphism of sheaves of
modules is only locally surjective, so `b|_V` is **not** an epimorphism of presheaves of
modules, and the hypothesis `hcancel` below --- cancellation against morphisms whose target is
the sheaf `G|_V` --- is exactly what a cokernel of sheaves does supply, while `Epi` is not.
Correspondingly `hdesc` is the universal property of that cokernel at the single target
`G|_V`.  No sheafification and no smallness condition appears anywhere.

## Main definitions

* `internalHomToKernel`: the comparison morphism `Hom_O(N, G) ⟶ ker (Hom_O(B, G) ⟶ Hom_O(A, G))`
  induced by precomposition with `b`.

## Main results

* `internalHomMapLeft_comp_eq_zero`: precomposition with `b` followed by precomposition with `a`
  vanishes, so the comparison morphism exists.
* `bijective_internalHomToKernel_app`: the comparison is bijective on sections over every object.
* `internalHomKernelIso`: hence it is an isomorphism `Hom_O(N, G) ≅ ker (Hom_O(a, G))`.

## Implementation notes

The comparison is `Limits.kernel.lift`, and it is shown to be an isomorphism by checking
bijectivity on each module of sections rather than by a universal property, because the
sections are where the hypotheses live.  Injectivity of the inclusion of the kernel on sections
comes from `PresheafOfModules.evaluation` preserving limits, so that the evaluated inclusion is
again a monomorphism of modules.

Assertions 0GMY (1), 01CO (1) and 03EN produce the local-cokernel property from exactness of
`A ⟶ B ⟶ N ⟶ 0`; here it is a hypothesis.  Assertion (1) of Tag 01CO for a ringed space is
`sheafHom_leftExact_fst` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHomLeftExact.lean`, in the
exact-sequence form and over the `SheafHom` package; the present file is the kernel form over an
arbitrary site.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.PresheafOfModules.InternalHom

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat)
variable {A B N G : PresheafOfModules.{max u v} (Oforget O)}

/-! ### The composite of the two precomposition maps -/

/-- Restriction to a slice is additive, so it takes the zero morphism to the zero morphism. -/
public theorem restrFun_map_zero (V : C) : (restrFun O V).map (0 : A ⟶ B) = 0 := by
  ext W
  rfl

/-- The restrictions to a slice of two composable morphisms with vanishing composite kill every
morphism out of the target. -/
public theorem restrFun_map_comp_eq_zero (a : A ⟶ B) (b : B ⟶ N) (hab : a ≫ b = 0) (V : C)
    (g : (restrFun O V).obj N ⟶ (restrFun O V).obj G) :
    (restrFun O V).map a ≫ (restrFun O V).map b ≫ g = 0 := by
  rw [← Category.assoc, ← Functor.map_comp, hab, restrFun_map_zero, Limits.zero_comp]

/-- Precomposition with `b` followed by precomposition with `a` is zero as soon as `a ≫ b = 0`. -/
public theorem internalHomMapLeft_comp_eq_zero (a : A ⟶ B) (b : B ⟶ N) (hab : a ≫ b = 0) :
    internalHomMapLeft O (G := G) b ≫ internalHomMapLeft O a = 0 := by
  ext V g
  exact restrFun_map_comp_eq_zero O a b hab V.unop g

/-! ### The comparison morphism to the kernel -/

/-- The comparison morphism `Hom_O(N, G) ⟶ ker (Hom_O(B, G) ⟶ Hom_O(A, G))` given by
precomposition with `b`. -/
public noncomputable def internalHomToKernel (a : A ⟶ B) (b : B ⟶ N) (hab : a ≫ b = 0) :
    internalHom O N G ⟶ kernel (internalHomMapLeft O (G := G) a) :=
  kernel.lift _ (internalHomMapLeft O b) (internalHomMapLeft_comp_eq_zero O a b hab)

/-- The comparison morphism, composed with the inclusion of the kernel, is precomposition
with `b`. -/
public theorem internalHomToKernel_comp_ι (a : A ⟶ B) (b : B ⟶ N) (hab : a ≫ b = 0) :
    internalHomToKernel O (G := G) a b hab ≫ kernel.ι (internalHomMapLeft O (G := G) a)
      = internalHomMapLeft O b :=
  kernel.lift_ι _ _ _

/-- The inclusion of the kernel is injective on sections over every object, the evaluation
functors of presheaves of modules preserving limits. -/
public theorem injective_kernel_ι_app (a : A ⟶ B) (V : Cᵒᵖ) :
    Function.Injective (ConcreteCategory.hom
      ((kernel.ι (internalHomMapLeft O (G := G) a)).app V)) := by
  have h : Mono ((PresheafOfModules.evaluation _ V).map
      (kernel.ι (internalHomMapLeft O (G := G) a))) := inferInstance
  rw [ModuleCat.mono_iff_injective] at h
  exact h

/-- Equal morphisms of presheaves of modules agree on every section. -/
private theorem hom_app_apply_congr {X Y : PresheafOfModules.{max u v} (Oforget O)} {f g : X ⟶ Y}
    (h : f = g) (V : Cᵒᵖ) (x : X.obj V) :
    ConcreteCategory.hom (f.app V) x = ConcreteCategory.hom (g.app V) x := by
  rw [h]

/-- The comparison morphism on sections, read as precomposition with the restriction of `b`. -/
public theorem internalHomToKernel_app_apply (a : A ⟶ B) (b : B ⟶ N) (hab : a ≫ b = 0)
    (V : Cᵒᵖ) (w : (internalHom O N G).obj V) :
    ConcreteCategory.hom ((kernel.ι (internalHomMapLeft O (G := G) a)).app V)
        (ConcreteCategory.hom ((internalHomToKernel O (G := G) a b hab).app V) w)
      = ConcreteCategory.hom ((internalHomMapLeft O (G := G) b).app V) w :=
  hom_app_apply_congr O (internalHomToKernel_comp_ι O a b hab) V w

/-- A section of the kernel over `V`, read as a morphism `B|_V ⟶ G|_V`, is killed by
precomposition with the restriction of `a`. -/
public theorem comp_kernel_ι_app_eq_zero (a : A ⟶ B) (V : Cᵒᵖ)
    (s : (kernel (internalHomMapLeft O (G := G) a)).obj V) :
    (restrFun O V.unop).map a ≫
        (ConcreteCategory.hom ((kernel.ι (internalHomMapLeft O (G := G) a)).app V) s
          : (restrFun O V.unop).obj B ⟶ (restrFun O V.unop).obj G) = 0 :=
  (hom_app_apply_congr O (kernel.condition (internalHomMapLeft O (G := G) a)) V s).trans rfl

/-! ### The comparison is an isomorphism -/

/-- Precomposition with `b` is injective on sections, as soon as its restrictions can be
cancelled against morphisms into `G`. -/
public theorem injective_internalHomMapLeft_app (b : B ⟶ N)
    (hcancel : ∀ (V : C) (w w' : (restrFun O V).obj N ⟶ (restrFun O V).obj G),
      (restrFun O V).map b ≫ w = (restrFun O V).map b ≫ w' → w = w') (V : Cᵒᵖ) :
    Function.Injective (ConcreteCategory.hom
      ((internalHomMapLeft O (G := G) b).app V)) := by
  intro w w' h
  exact hcancel V.unop w w' h

/-- **The comparison morphism is bijective on the sections over every object.** -/
public theorem bijective_internalHomToKernel_app (a : A ⟶ B) (b : B ⟶ N) (hab : a ≫ b = 0)
    (hcancel : ∀ (V : C) (w w' : (restrFun O V).obj N ⟶ (restrFun O V).obj G),
      (restrFun O V).map b ≫ w = (restrFun O V).map b ≫ w' → w = w')
    (hdesc : ∀ (V : C) (t : (restrFun O V).obj B ⟶ (restrFun O V).obj G),
      (restrFun O V).map a ≫ t = 0 → ∃ w, (restrFun O V).map b ≫ w = t) (V : Cᵒᵖ) :
    Function.Bijective (ConcreteCategory.hom
      ((internalHomToKernel O (G := G) a b hab).app V)) := by
  refine ⟨fun w w' h => ?_, fun s => ?_⟩
  · refine injective_internalHomMapLeft_app O b hcancel V ?_
    rw [← internalHomToKernel_app_apply O a b hab V w,
      ← internalHomToKernel_app_apply O a b hab V w', h]
  · obtain ⟨w, hw⟩ := hdesc V.unop _ (comp_kernel_ι_app_eq_zero O a V s)
    refine ⟨w, injective_kernel_ι_app O a V ?_⟩
    rw [internalHomToKernel_app_apply O a b hab V w]
    exact hw

/-- **Internal Hom turns a local cokernel in the first variable into a kernel.**  If
precomposition with the restriction of `b : B ⟶ N` to every slice is injective and surjects onto
the morphisms killed by the restriction of `a : A ⟶ B`, then `Hom_O(N, G)` is the kernel of
precomposition with `a`. -/
public noncomputable def internalHomKernelIso (a : A ⟶ B) (b : B ⟶ N) (hab : a ≫ b = 0)
    (hcancel : ∀ (V : C) (w w' : (restrFun O V).obj N ⟶ (restrFun O V).obj G),
      (restrFun O V).map b ≫ w = (restrFun O V).map b ≫ w' → w = w')
    (hdesc : ∀ (V : C) (t : (restrFun O V).obj B ⟶ (restrFun O V).obj G),
      (restrFun O V).map a ≫ t = 0 → ∃ w, (restrFun O V).map b ≫ w = t) :
    internalHom O N G ≅ kernel (internalHomMapLeft O (G := G) a) :=
  letI hiso : ∀ V, IsIso ((internalHomToKernel O (G := G) a b hab).app V) := fun V => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_internalHomToKernel_app O a b hab hcancel hdesc V
  PresheafOfModules.isoMk (fun V => @asIso _ _ _ _ _ (hiso V))
    (fun {_ _} f => (internalHomToKernel O (G := G) a b hab).naturality f)

end Stacks.PresheafOfModules.InternalHom

end
