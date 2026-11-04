module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Coherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticModules

/-!
# The coherator on the small étale site of a flat object (Stacks 0GQK)

Let `𝒳` be an algebraic stack and let `Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` be the coherator of
**Stacks 0778**, the right adjoint of the inclusion `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)`.  Let `x`
be an object of `𝒳` lying over a scheme `U` such that `x : U → 𝒳` is flat.  **Stacks 0GQK** says
that for `𝓕` in `LQCoh^fbc(𝒪_𝒳)` one has `Q(𝓕)|_{U_étale} = 𝓕|_{U_étale}`.

The equality is realized by the adjunction counit `ε_𝓕 : i Q(𝓕) ⟶ 𝓕`, whose restriction to the
small étale site of `U` is an isomorphism; that statement is
`AlgebraicGeometry.Stack.AlgebraicStacks.isIso_restrict_coheratorAdjunction_counit`.

The source's proof is one line: the kernel and the cokernel of `ε_𝓕` are parasitic, by
**Stacks 0779** part (2).  This file proves the step the source leaves implicit, for a map whose
kernel and cokernel are parasitic (the two hypotheses `hker` and `hcoker`), namely that
parasiticity is exactly what the restriction to `U_étale` of a *flat* object sees:

* the restriction at `x` evaluates a module at the objects of `𝒳` that the small étale site of
  `U` names, and every one of them is a flat object of `𝒳` as soon as `x` is one
  (`AlgebraicGeometry.Stack.flatObject_smallEtaleToStack_obj`), because such an object maps to
  `x` over an étale, hence flat, morphism of schemes;
* a presheaf of modules whose kernel and cokernel vanish at every flat object is therefore
  restricted to a monomorphism and an epimorphism, and `PresheafOfModules` is abelian, so the
  restriction is an isomorphism.

## Main definitions

* `AlgebraicGeometry.Stack.smallEtaleToStack`: the functor from the small étale site of the
  scheme below an object `x` of `𝒳` to `𝒳` along which **Stacks 06W1** restricts, extracted from
  `AlgebraicGeometry.Stack.restrictModuleToSmallEtale` so that its values can be named.
* `AlgebraicGeometry.Stack.restrictModuleFunctorToSmallEtale`: the restriction of
  **Stacks 06WJ** as a functor, so that it applies to maps of modules and not only to modules.

## Main results

* `AlgebraicGeometry.Stack.flatObject_smallEtaleToStack_obj`: an object of `𝒳` named by the small
  étale site of the scheme below a flat object is itself flat.
* `AlgebraicGeometry.Stack.isIso_restrictModuleFunctorToSmallEtale_map_of_isParasitic`: the step
  of **Stacks 0GQK** that is independent of the coherator.  **Stacks 0GQK** itself is
  `AlgebraicGeometry.Stack.AlgebraicStacks.isIso_restrict_coheratorAdjunction_counit`.

## Implementation notes

The hypotheses `hker` and `hcoker` are **Stacks 0779** part (2), read for the kernel and the
cokernel in the abelian category of presheaves of modules over the structure presheaf of `𝒳`.
The kernel there agrees with the kernel in `Mod(𝒪_𝒳)`, which is where the source takes it; the
cokernel there maps onto the one in `Mod(𝒪_𝒳)` by sheafification, so the hypothesis is the
presheaf-level reading of the source's, and it is the reading the one-line argument consumes —
`AlgebraicGeometry.Stack.IsParasitic` is itself a condition on an underlying presheaf of modules.

The parasitic condition is stated for the étale name of the structure sheaf, as in
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeModules`; the underlying presheaf of
rings does not depend on the name.

## References

* [Stacks Project, Tag 0GQK](https://stacks.math.columbia.edu/tag/0GQK)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0H14](https://stacks.math.columbia.edu/tag/0H14)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

universe v v₁ u₁ u w m

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M N : PresheafOfModules.{v} R} (φ : M ⟶ N)

/-- A map of presheaves of modules whose kernel has no sections at `X` is injective on sections
at `X`.  Evaluation at `X` preserves finite limits, so it carries the kernel of `φ` to the kernel
of the map of modules `φ` induces at `X`. -/
theorem injective_app_of_subsingleton_kernel (X : Cᵒᵖ)
    (hk : Subsingleton ((kernel φ).obj X)) :
    Function.Injective (ConcreteCategory.hom (φ.app X)) := by
  have hz : IsZero ((PresheafOfModules.evaluation R X).obj (kernel φ)) :=
    @ModuleCat.isZero_of_subsingleton _ _ _ hk
  have hzk : IsZero (kernel ((PresheafOfModules.evaluation R X).map φ)) :=
    hz.of_iso (PreservesKernel.iso (PresheafOfModules.evaluation R X) φ).symm
  rw [← ModuleCat.mono_iff_injective]
  exact mono_of_isZero_kernel _ hzk

/-- A map of presheaves of modules whose cokernel has no sections at `X` is surjective on
sections at `X`.  Evaluation at `X` preserves finite colimits, so it carries the cokernel of `φ`
to the cokernel of the map of modules `φ` induces at `X`. -/
theorem surjective_app_of_subsingleton_cokernel (X : Cᵒᵖ)
    (hk : Subsingleton ((cokernel φ).obj X)) :
    Function.Surjective (ConcreteCategory.hom (φ.app X)) := by
  have hz : IsZero ((PresheafOfModules.evaluation R X).obj (cokernel φ)) :=
    @ModuleCat.isZero_of_subsingleton _ _ _ hk
  have hzc : IsZero (cokernel ((PresheafOfModules.evaluation R X).map φ)) :=
    hz.of_iso (PreservesCokernel.iso (PresheafOfModules.evaluation R X) φ).symm
  rw [← ModuleCat.epi_iff_surjective]
  exact epi_of_isZero_cokernel _ hzc

end PresheafOfModules

namespace AlgebraicGeometry.Stack

/-- A morphism of schemes over a base which is isomorphic, over that base, to an étale one is
flat.  Composing with the isomorphism exhibits it as an isomorphism followed by an étale
morphism. -/
theorem flat_of_iso_of_etale (B : BigFppfSite.{u}) {Y : B.Schemes} {W Z : Over Y}
    (e : W ≅ Z) (hZ : Etale (B.inclusion.map Z.hom)) :
    Flat (B.inclusion.map W.hom) := by
  have h1 : Over.Hom.left e.hom ≫ Z.hom = W.hom := Over.w e.hom
  have hiso : IsIso (Over.Hom.left e.hom) := by
    have := (Over.forget Y).map_isIso e.hom
    simpa using this
  have hfl : Flat (B.inclusion.map (Over.Hom.left e.hom) ≫ B.inclusion.map Z.hom) :=
    inferInstance
  exact h1 ▸ (B.inclusion.map_comp (Over.Hom.left e.hom) Z.hom ▸ hfl)

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- The functor from the small étale site of the scheme `U` below an object `x` of a category
fibred in groupoids to that fibred category, along which **Stacks 06W1** restricts: transport a
small étale object of `U` across the localization equivalence of **Stacks 06W0** into the slice
of `𝒳` at `x`, and forget the structure morphism.

This is the functor `AlgebraicGeometry.Stack.presheafPullback` precomposes with; it is named here
so that the objects of `𝒳` the restriction evaluates at can be spoken about. -/
def smallEtaleToStack {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (x : 𝒳) :
    SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x) ⥤ 𝒳 :=
  letI := isEquivalence_overPost B S hS p hp x
  smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x

/-- The restriction of a presheaf to the small étale site of **Stacks 06W1** is precomposition
with `AlgebraicGeometry.Stack.smallEtaleToStack`. -/
theorem restrictToSmallEtale_eq {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    {A : Type*} [Category A] (F : 𝒳ᵒᵖ ⥤ A) :
    restrictToSmallEtale B E h S hS p hp x F =
      (smallEtaleToStack B E h S hS p hp x).op ⋙ F :=
  rfl

/-- **An object of `𝒳` named by the small étale site of the scheme below a flat object is
flat.**  Such an object comes with a morphism to `x` lying over an étale — in particular flat —
morphism of schemes, so `AlgebraicGeometry.Stack.flatObject_of_flat` applies.

This is what makes the restriction to `U_étale` see only flat objects, and hence see nothing of a
parasitic module. -/
theorem flatObject_smallEtaleToStack_obj {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (x : 𝒳.val.val.obj) (hx : flatObject B S hS 𝒳.val x)
    (V : SmallEtale E (𝒳.val.val.p.obj x).left.1
      (contains_base B E h S hS 𝒳.val.val.p x)) :
    flatObject B S hS 𝒳.val
      ((smallEtaleToStack B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x).obj V) := by
  have := isEquivalence_overPost B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x
  exact flatObject_of_flat B S hS 𝒳
    ((Over.post (X := x) (𝒳.val.val.p ⋙ Over.forget (B.obj hS))).inv.obj
      ((smallEtaleInclusion B E h (𝒳.val.val.p.obj x).left.1
        (contains_base B E h S hS 𝒳.val.val.p x)).obj V)).hom
    (flat_of_iso_of_etale B
      ((Over.post (X := x) (𝒳.val.val.p ⋙ Over.forget (B.obj hS))).asEquivalence.counitIso.app
        ((smallEtaleInclusion B E h (𝒳.val.val.p.obj x).left.1
          (contains_base B E h S hS 𝒳.val.val.p x)).obj V))
      (smallEtaleInclusion_etale B E h _ _ V))
    hx

/-- **Stacks 06WJ, as a functor.**  The restriction at an object `x` of presheaves of modules on
`𝒳` to the small étale site of the scheme below `x`.  On objects it is
`AlgebraicGeometry.Stack.restrictModuleToSmallEtale`; naming the functor makes the restriction of
a *map* of modules available. -/
def restrictModuleFunctorToSmallEtale {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj ⥤
      PresheafOfModules.{m}
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj :=
  letI := isEquivalence_overPost B S hS p hp x
  PresheafOfModules.pushforward₀ (smallEtaleToStack B E h S hS p hp x)
      (ringStructureSheafCore B S hS p hp τ hτ).obj ⋙
    PresheafOfModules.restrictScalars (localStructurePresheafIso B E h S hS p hp x τ hτ).hom

/-- On objects, `AlgebraicGeometry.Stack.restrictModuleFunctorToSmallEtale` is the restriction of
**Stacks 06WJ**. -/
theorem restrictModuleFunctorToSmallEtale_obj {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    (restrictModuleFunctorToSmallEtale B E h S hS p hp x τ hτ).obj F =
      restrictModuleToSmallEtale B E h S hS p hp x τ hτ F :=
  rfl

/-- **The restriction to the small étale site of a flat object is an isomorphism as soon as the
kernel and the cokernel of the map are parasitic.**  The restriction evaluates the two modules at
objects of `𝒳` which are flat by
`AlgebraicGeometry.Stack.flatObject_smallEtaleToStack_obj`, where the kernel and cokernel have no
sections; so the restricted map is injective and surjective on all sections, hence a
monomorphism and an epimorphism, hence an isomorphism in the abelian category of presheaves of
modules.

This is the content of the proof of **Stacks 0GQK** which is independent of the coherator. -/
theorem isIso_restrictModuleFunctorToSmallEtale_map_of_isParasitic
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {M N : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj}
    (φ : M ⟶ N)
    (hker : IsParasitic B S hS 𝒳 .etale (kernel φ))
    (hcoker : IsParasitic B S hS 𝒳 .etale (cokernel φ))
    (x : 𝒳.val.val.obj) (hx : flatObject B S hS 𝒳.val x) :
    IsIso ((restrictModuleFunctorToSmallEtale B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids x (etaleTopology B) (etaleTopology_le_topology B)).map φ) := by
  have : Mono ((restrictModuleFunctorToSmallEtale B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids x (etaleTopology B) (etaleTopology_le_topology B)).map φ) := by
    refine PresheafOfModules.mono_of_injective (fun V => ?_)
    exact PresheafOfModules.injective_app_of_subsingleton_kernel φ
      (op ((smallEtaleToStack B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids x).obj V.unop))
      (hker _ (flatObject_smallEtaleToStack_obj B E h S hS x hx V.unop))
  have : Epi ((restrictModuleFunctorToSmallEtale B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids x (etaleTopology B) (etaleTopology_le_topology B)).map φ) := by
    refine PresheafOfModules.epi_of_surjective (fun V => ?_)
    exact PresheafOfModules.surjective_app_of_subsingleton_cokernel φ
      (op ((smallEtaleToStack B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids x).obj V.unop))
      (hcoker _ (flatObject_smallEtaleToStack_obj B E h S hS x hx V.unop))
  exact isIso_of_mono_of_epi _

end AlgebraicGeometry.Stack

end
