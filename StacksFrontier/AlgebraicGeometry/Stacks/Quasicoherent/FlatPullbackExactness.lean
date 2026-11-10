module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatObjectDetection
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentDirectImage

/-!
# Exactness of flat pullback of quasi-coherent modules on algebraic stacks (Stacks 076X)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, and let
`f^* : QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)` be the inverse image of quasi-coherent modules, at the universe
of the schemes (`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentPullback`). **Stacks 076X**
says that `f^*` is exact when `f` is flat. This file proves:

* that `f^*` is right exact, and in fact preserves all small colimits, for every `f`;
* that `f^*` is left exact when `f` is flat, given that kernels of quasi-coherent modules on `𝒳`
  and on `𝒴` exist and are computed on flat objects
  (`AlgebraicGeometry.Stack.AlgebraicStacks.QuasicoherentKernelsOnFlatObjects`).

The second input is the abelian structure of `QCoh(𝒪_𝒳)`, **Stacks 06WV** (1), (2), read on the
flat objects: the kernel of a morphism `φ` of quasi-coherent modules is a quasi-coherent module
whose sections over every flat object `x : U → 𝒳` are the kernel of `φ` on the sections over
`x`. The source states it as the faithful exactness of `QCoh(𝒪_𝒳) → QCoh(𝒪_U)` for a smooth
cover `U → 𝒳` in the proof of Stacks 06WV, and that is the only place where the proof of
Stacks 076X uses it. Here it is a named hypothesis, and **no `@[stacks 076X]` registration rests
on it**: it is discharged by the canonical abelian structure of `QCoh(𝒪_𝒳)` (the coherator of
Stacks 0778 applied to the module kernel, whose counit is an isomorphism on flat objects by
Stacks 0779 (2)), which is not yet in the library.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsKernelOnFlatObjects`: a kernel fork of quasi-coherent
  modules which, on the sections over every flat object, is an injection onto the kernel.
* `AlgebraicGeometry.Stack.AlgebraicStacks.QuasicoherentKernelsOnFlatObjects`: every morphism of
  `QCoh(𝒪_𝒳)` has a kernel which is a kernel on flat objects.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.preservesColimitsOfSize_quasicoherentPullback` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.preservesFiniteColimits_quasicoherentPullback`: `f^*` is
  right exact, unconditionally.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLimit_of_isKernelOnFlatObjects` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isKernelOnFlatObjects_of_isLimit`: once kernels on flat
  objects exist, a kernel fork is a kernel exactly when it is a kernel on flat objects.
* `AlgebraicGeometry.Stack.AlgebraicStacks.preservesFiniteLimits_quasicoherentPullback_of_isFlat`
  and `AlgebraicGeometry.Stack.AlgebraicStacks.exactFunctor_quasicoherentPullback_of_isFlat`: the
  content of Stacks 076X over the kernel input.

## Implementation notes

The proof of left exactness is the source's. A flat 1-morphism carries flat objects to flat
objects (`AlgebraicGeometry.Stack.FlatFppf.flatObject_map`, **Stacks 06PX**), and `f^*` is
computed on sections: the sections of `f^*ℱ` over `x` are the sections of `ℱ` over `f(x)`. So
`f^*` carries a kernel on flat objects to a kernel on flat objects, and a kernel on flat objects
is a kernel, because the comparison map with an honest kernel on flat objects is bijective on
the sections over every flat object, hence an isomorphism of quasi-coherent modules
(`AlgebraicGeometry.Stack.isIso_of_flatObject`). This is the faithfulness of
`QCoh(𝒪_𝒳) → QCoh(𝒪_U)` the source invokes. Preservation of finite limits then follows from
preservation of kernels, `QCoh(𝒪_𝒴)` having finite biproducts (it has colimits, **Stacks 06WV**
(4)) and `f^*` being additive.

Right exactness is the argument of
`AlgebraicGeometry.Stack.preservesFiniteColimits_quasicoherentPullback` at the universes of
algebraic stacks: colimits of quasi-coherent modules are colimits of modules,
and the inverse image of modules is a left adjoint at the universe of the schemes
(`AlgebraicGeometry.Stack.fppfModulesPullbackPushforwardAdjunction`).

## References

* [Stacks Project, Tag 076X](https://stacks.math.columbia.edu/tag/076X)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Colimits

variable (B S hS) in
/-- `QCoh(𝒪_𝒳)` has finite biproducts: it is preadditive and has colimits, Stacks 06WV (4). -/
instance hasFiniteBiproducts_quasicoherentModules (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasFiniteBiproducts (quasicoherentModules B S hS 𝒳) :=
  have hc := FibredSite.hasColimitsOfSize_quasicoherentModules'.{u + 1, u, u} B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  have : HasFiniteCoproducts (quasicoherentModules B S hS 𝒳) :=
    @hasFiniteCoproducts_of_hasCoproducts.{u} _ _ (fun _ => hc.has_colimits_of_shape _)
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- The inverse image of quasi-coherent modules is additive: on sections it does nothing. -/
instance additive_quasicoherentPullback : (quasicoherentPullback B S hS f).Additive where
  map_add {_ _ _ _} := ObjectProperty.hom_ext _ (SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)))

/-- **The inverse image of quasi-coherent modules along a 1-morphism of algebraic stacks preserves
all small colimits.** Colimits of quasi-coherent modules are colimits of modules, Stacks 06WV (4);
the inverse image of modules is a left adjoint, Stacks 06WE; and the inclusion of the
quasi-coherent modules reflects colimits, being fully faithful. -/
theorem preservesColimitsOfSize_quasicoherentPullback :
    PreservesColimitsOfSize.{u, u} (quasicoherentPullback B S hS f) := by
  have hι : PreservesColimitsOfSize.{u, u} (quasicoherentInclusion B S hS 𝒴) :=
    FibredSite.preservesColimitsOfSize_quasicoherentInclusion'.{u + 1, u, u} B S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids
  have : (fppfModulesPullback B S hS f).IsLeftAdjoint :=
    (fppfModulesPullbackPushforwardAdjunction B S hS f).isLeftAdjoint
  have : PreservesColimitsOfSize.{u, u}
      (quasicoherentPullback B S hS f ⋙ quasicoherentInclusion B S hS 𝒳) :=
    preservesColimits_of_natIso (quasicoherentPullbackCompInclusionIso B S hS f).symm
  constructor
  intro K _
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (quasicoherentInclusion B S hS 𝒳)

/-- **Right exactness of the inverse image of quasi-coherent modules along a 1-morphism of
algebraic stacks.** It holds with no hypothesis on the 1-morphism, as the source notes before
Stacks 076X. -/
theorem preservesFiniteColimits_quasicoherentPullback :
    PreservesFiniteColimits (quasicoherentPullback B S hS f) :=
  have := preservesColimitsOfSize_quasicoherentPullback f
  PreservesColimitsOfSize.preservesFiniteColimits _

end Colimits

section Kernels

variable {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- A kernel fork of a morphism of quasi-coherent modules on an algebraic stack *is a kernel on
flat objects* when, on the sections over every flat object, it is an injection onto the kernel
of the morphism. -/
def IsKernelOnFlatObjects {F G : quasicoherentModules B S hS 𝒳} {φ : F ⟶ G}
    (c : KernelFork φ) : Prop :=
  ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x →
    Function.Injective (c.ι.hom.val.app (op x)) ∧
      ∀ s : F.obj.val.obj (op x), φ.hom.val.app (op x) s = 0 →
        ∃ k : c.pt.obj.val.obj (op x), c.ι.hom.val.app (op x) k = s

variable (B S hS 𝒳) in
/-- **Kernels of quasi-coherent modules exist and are computed on flat objects**: every morphism
of `QCoh(𝒪_𝒳)` has a kernel in `QCoh(𝒪_𝒳)` which is a kernel on flat objects. This is the form in
which the abelian structure of `QCoh(𝒪_𝒳)`, Stacks 06WV (1), (2), enters the proof of
Stacks 076X. -/
def QuasicoherentKernelsOnFlatObjects : Prop :=
  ∀ ⦃F G : quasicoherentModules B S hS 𝒳⦄ (φ : F ⟶ G),
    ∃ c : KernelFork φ, Nonempty (IsLimit c) ∧ IsKernelOnFlatObjects c

/-- A morphism of kernel forks commuting with the inclusions does so on the sections. -/
private theorem app_comp_ι_app {F G : quasicoherentModules B S hS 𝒳} {φ : F ⟶ G}
    {c c' : KernelFork φ} {m : c.pt ⟶ c'.pt} (hm : m ≫ c'.ι = c.ι) (x : 𝒳.val.val.obj)
    (k : c.pt.obj.val.obj (op x)) :
    c'.ι.hom.val.app (op x) (m.hom.val.app (op x) k) = c.ι.hom.val.app (op x) k :=
  congrArg (fun g => g.hom.val.app (op x) k) hm

/-- A morphism between two kernel forks which are kernels on flat objects, compatible with the
two inclusions, is an isomorphism: it is bijective on the sections over every flat object. -/
theorem isIso_of_isKernelOnFlatObjects {F G : quasicoherentModules B S hS 𝒳}
    {φ : F ⟶ G} {c c' : KernelFork φ} (hc : IsKernelOnFlatObjects c)
    (hc' : IsKernelOnFlatObjects c') (m : c.pt ⟶ c'.pt) (hm : m ≫ c'.ι = c.ι) : IsIso m := by
  have : IsIso m.hom := isIso_of_flatObject c.pt.property c'.pt.property m.hom fun x hx => by
    have hι := app_comp_ι_app hm x
    refine ⟨fun a b hab => (hc x hx).1 ?_, fun k' => ?_⟩
    · rw [← hι, ← hι, hab]
    · obtain ⟨k, hk⟩ := (hc x hx).2 (c'.ι.hom.val.app (op x) k')
        (show (c'.ι ≫ φ).hom.val.app (op x) k' = 0 by
          rw [KernelFork.condition]
          rfl)
      refine ⟨k, (hc' x hx).1 ?_⟩
      rw [hι, hk]
  have : IsIso ((ObjectProperty.ι _).map m) := this
  exact isIso_of_fully_faithful (ObjectProperty.ι _) m

/-- **A kernel on flat objects is a kernel**, once kernels on flat objects exist: the comparison
map to such a kernel is an isomorphism by
`AlgebraicGeometry.Stack.AlgebraicStacks.isIso_of_isKernelOnFlatObjects`. -/
theorem isLimit_of_isKernelOnFlatObjects (hE : QuasicoherentKernelsOnFlatObjects B S hS 𝒳)
    {F G : quasicoherentModules B S hS 𝒳} {φ : F ⟶ G} (c : KernelFork φ)
    (hc : IsKernelOnFlatObjects c) : Nonempty (IsLimit c) := by
  obtain ⟨c₀, ⟨h₀⟩, hc₀⟩ := hE φ
  let m : c.pt ⟶ c₀.pt := h₀.lift c
  have hm : m ≫ c₀.ι = c.ι := h₀.fac c WalkingParallelPair.zero
  have : IsIso m := isIso_of_isKernelOnFlatObjects hc hc₀ m hm
  exact ⟨IsLimit.ofIsoLimit h₀ (Fork.ext (asIso m) hm).symm⟩

/-- **A kernel is a kernel on flat objects**, once kernels on flat objects exist: it is isomorphic
to one, compatibly with the inclusions. -/
theorem isKernelOnFlatObjects_of_isLimit (hE : QuasicoherentKernelsOnFlatObjects B S hS 𝒳)
    {F G : quasicoherentModules B S hS 𝒳} {φ : F ⟶ G} (c : KernelFork φ) (hc : IsLimit c) :
    IsKernelOnFlatObjects c := by
  obtain ⟨c₀, ⟨h₀⟩, hc₀⟩ := hE φ
  let e : c.pt ≅ c₀.pt := hc.conePointUniqueUpToIso h₀
  have he : e.hom ≫ c₀.ι = c.ι := hc.conePointUniqueUpToIso_hom_comp h₀ WalkingParallelPair.zero
  intro x hx
  have hι := app_comp_ι_app he x
  have hbij : Function.Bijective (e.hom.hom.val.app (op x)) := by
    rw [← ConcreteCategory.isIso_iff_bijective]
    exact inferInstanceAs (IsIso (((SheafOfModules.evaluation _ (op x))).map
      ((ObjectProperty.ι _).map e.hom)))
  refine ⟨fun a b hab => hbij.1 ((hc₀ x hx).1 ?_), fun s hs => ?_⟩
  · rw [hι, hι, hab]
  · obtain ⟨k₀, hk₀⟩ := (hc₀ x hx).2 s hs
    obtain ⟨k, rfl⟩ := hbij.2 k₀
    exact ⟨k, (hι k).symm.trans hk₀⟩

end Kernels

section Flat

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **The inverse image along a flat 1-morphism carries kernels on flat objects to kernels on
flat objects.** Its sections over an object are the sections over the image of that object, and
a flat 1-morphism carries flat objects to flat objects, Stacks 06PX. -/
theorem isKernelOnFlatObjects_map (hf : AlgebraicStacks.IsFlat B S hS f)
    {F G : quasicoherentModules B S hS 𝒴} {φ : F ⟶ G} (c : KernelFork φ)
    (hc : IsKernelOnFlatObjects c) :
    IsKernelOnFlatObjects (c.map (quasicoherentPullback B S hS f)) := by
  intro x hx
  obtain ⟨h₁, h₂⟩ := hc _ (FlatFppf.flatObject_map B S hS f hf ⟨x, hx⟩)
  exact ⟨h₁, h₂⟩

/-- **Left exactness of the inverse image along a flat 1-morphism of algebraic stacks, given
kernels on flat objects.** Let `f : 𝒳 ⟶ 𝒴` be flat. If kernels in `QCoh(𝒪_𝒳)` and in
`QCoh(𝒪_𝒴)` exist and are computed on flat objects, then `f^* : QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)` preserves
finite limits. This is the content of Stacks 076X over Stacks 06WV (1), (2) read on flat
objects. -/
theorem preservesFiniteLimits_quasicoherentPullback_of_isFlat
    (hf : AlgebraicStacks.IsFlat B S hS f)
    (h𝒳 : QuasicoherentKernelsOnFlatObjects B S hS 𝒳)
    (h𝒴 : QuasicoherentKernelsOnFlatObjects B S hS 𝒴) :
    PreservesFiniteLimits (quasicoherentPullback B S hS f) := by
  have hker : ∀ {M N : quasicoherentModules B S hS 𝒴} (φ : M ⟶ N),
      PreservesLimit (parallelPair φ 0) (quasicoherentPullback B S hS f) := fun φ => by
    obtain ⟨c, ⟨hc⟩, hcf⟩ := h𝒴 φ
    obtain ⟨hmap⟩ := isLimit_of_isKernelOnFlatObjects h𝒳 _ (isKernelOnFlatObjects_map f hf c hcf)
    exact preservesLimit_of_preserves_limit_cone hc
      ((KernelFork.isLimitMapConeEquiv c _).symm hmap)
  have : HasKernels (quasicoherentModules B S hS 𝒴) :=
    ⟨fun φ => by
      obtain ⟨c, ⟨hc⟩, -⟩ := h𝒴 φ
      exact ⟨⟨⟨c, hc⟩⟩⟩⟩
  have : HasEqualizers (quasicoherentModules B S hS 𝒴) :=
    Preadditive.hasEqualizers_of_hasKernels
  have : HasBinaryBiproducts (quasicoherentModules B S hS 𝒴) :=
    hasBinaryBiproducts_of_finite_biproducts _
  have : HasFiniteProducts (quasicoherentModules B S hS 𝒴) :=
    hasFiniteProducts_of_hasFiniteBiproducts _
  have : HasZeroObject (quasicoherentModules B S hS 𝒴) :=
    hasZeroObject_of_hasFiniteBiproducts _
  have : HasZeroObject (quasicoherentModules B S hS 𝒳) :=
    hasZeroObject_of_hasFiniteBiproducts _
  exact Functor.preservesFiniteLimits_of_preservesKernels _

/-- **Exactness of the inverse image along a flat 1-morphism of algebraic stacks, given kernels on
flat objects**: `f^* : QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)` preserves finite limits and finite colimits. -/
theorem exactFunctor_quasicoherentPullback_of_isFlat (hf : AlgebraicStacks.IsFlat B S hS f)
    (h𝒳 : QuasicoherentKernelsOnFlatObjects B S hS 𝒳)
    (h𝒴 : QuasicoherentKernelsOnFlatObjects B S hS 𝒴) :
    exactFunctor (quasicoherentModules B S hS 𝒴) (quasicoherentModules B S hS 𝒳)
      (quasicoherentPullback B S hS f) :=
  (exactFunctor_iff _).mpr ⟨preservesFiniteLimits_quasicoherentPullback_of_isFlat f hf h𝒳 h𝒴,
    preservesFiniteColimits_quasicoherentPullback f⟩

end Flat

end AlgebraicGeometry.Stack.AlgebraicStacks

end
