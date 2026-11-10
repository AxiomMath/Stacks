module

public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatVanishing
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.TopologyVanishing
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologySequence
public import StacksCore.Tactic.StacksAttribute

/-!
# Comparing cohomology along a morphism with parasitic kernel and cokernel

A morphism of abelian sheaves on a site induces isomorphisms on the cohomology over an object
as soon as its kernel and its cokernel have no cohomology at all over that object. On the big
fppf site of a scheme `S` the vanishing is supplied by the cohomology of a parasitic module, so
a morphism of sheaves of `𝒪`-modules whose kernel and cokernel are parasitic induces
isomorphisms on cohomology at every object flat over `S`.

## Main results

* `Stacks.Cohomology.LongExactSequence.bijective_map_g_of_subsingleton` and
  `Stacks.Cohomology.LongExactSequence.bijective_map_f_of_subsingleton`: in a short exact
  sequence of abelian sheaves, the quotient map, resp. the inclusion, is an isomorphism on
  cohomology over an object as soon as the remaining term has no cohomology there.
* `Stacks.Cohomology.LongExactSequence.bijective_map_of_subsingleton_kernel_cokernel`: a
  morphism of abelian sheaves whose kernel and cokernel have no cohomology over an object is an
  isomorphism on the cohomology over that object.
* `AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isParasitic`: a morphism of sheaves of
  `𝒪`-modules on the big fppf site over `S` whose kernel and cokernel are parasitic induces
  isomorphisms `H^p(U, ℱ) → H^p(U, 𝒢)` at every object `U` flat over `S`.
* `AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isParasiticFor`: the same with the
  hypotheses and the conclusion of [Stacks, Tag 0756] — kernel and cokernel parasitic *for the
  fppf topology*, and `U` flat *and locally of finite presentation* over `S`.

## Implementation notes

Cohomology over an object is Mathlib's `CategoryTheory.Sheaf.H'` and the map induced by a
morphism of sheaves is `Stacks.Cohomology.LongExactSequence.map`, so the three exactness points
of `StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologySequence` apply verbatim. Vanishing
is phrased as `Subsingleton` on the cohomology group, which is what the long exact sequence
consumes; the geometric input delivers the categorical `IsZero`, and the two are interchanged by
`AddCommGrpCat.subsingleton_of_isZero`.

A general morphism is split through its coimage rather than its image: the coimage is literally
`cokernel (kernel.ι φ)`, so the short exact sequence `0 → Ker φ → ℱ → Coim φ → 0` is the
cokernel sequence of `kernel.ι φ` with no further work, and the second sequence
`0 → Coim φ → 𝒢 → Coker φ → 0` is obtained from the cokernel sequence of `φ` itself by the
epimorphism `ℱ → Coim φ`. Degree `0` of the injectivity half of the second comparison is not
covered by the long exact sequence — there is no term before `H^0` — and is supplied instead by
`CategoryTheory.Abelian.Ext.postcomp_mk₀_injective_of_mono`.

The kernel and cokernel in the geometric statement are taken in the category of sheaves of
`𝒪`-modules, as in the source, while the cohomology is that of the underlying abelian sheaves.
The two are reconciled by exactness of `SheafOfModules.toSheaf`
(`Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf` together with Mathlib's
finite-limit instance), which identifies the kernel and cokernel of the underlying morphism of
abelian sheaves with the underlying sheaves of the kernel and cokernel.

**This is the step of Stacks 0756 that rests on Stacks 0755**, namely the assertion that
`H^p(U, ℱ) → H^p(U, 𝒢)` is an isomorphism once `Ker` and `Coker` are parasitic. The source
lemma goes on to identify `H^p(U, ℱ)` with `H^p(U, 𝒢|_{U_τ})` by Stacks 03DW, and to derive
the parasitic hypotheses from quasi-coherence of `𝒢|_{S_τ}` and flat base change. Neither is
asserted here. **Both of the inputs they need exist in this development**:

* Stacks 03DW, clause (1), in *every* degree and for all five topologies at once, is
  `AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso`
  (`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.BigSiteQuasiCoherentCohomology`
  ), which carries `@[stacks 03DW]` alongside `@[stacks 03P2]`; its form over an arbitrary open of
  the base is `AlgebraicGeometry.bigOverQuasiCoherentCohomologyIso` in the same file, and the
  `q = 0` carrier is `AlgebraicGeometry.BigFppfOver.hZeroBaseAssociatedModuleAddEquiv` in
  `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModuleCohomologyDegreeZero`.
* The small-site restriction of a module on the big fppf site, as an adjoint pair, is
  `AlgebraicGeometry.BigFppfOver.baseAssociatedModule ⊣
  AlgebraicGeometry.BigFppfOver.baseRestrictModule`, with
  `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleAdjunction`
  (`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite`), for the small
  Zariski site and all five topologies; its small étale counterpart is
  `AlgebraicGeometry.BigFppfOver.smallEtaleToBaseModulePullback ⊣
  AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforward`, with
  `AlgebraicGeometry.BigFppfOver.smallEtaleToBaseModuleAdjunction`
  (`StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.QuasiCoherentPullback`).

What is absent is the assembly, and one specific piece of it; the other two of its three pieces
are in place.

* **The counit of the big-site adjunction.**
  The comparison map `φ : ℱ → 𝒢` of the source is the counit of that adjunction at `𝒢`, and the
  pair is constructed in
  `StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologyCounit`:
  `AlgebraicGeometry.BigFppfOver.zariskiComparisonModule` and
  `AlgebraicGeometry.BigFppfOver.zariskiComparisonMap` at `τ = Zar`, from
  `AlgebraicGeometry.BigFppfOver.associatedModuleAdjunction`, and
  `AlgebraicGeometry.BigFppfOver.etaleComparisonModule` and
  `AlgebraicGeometry.BigFppfOver.etaleComparisonMap` at `τ = étale`, from
  `AlgebraicGeometry.BigFppfOver.smallEtaleToBaseModuleAdjunction` at `.fppf` — the morphism
  `a_S`. Clause (1) of the source enters there through
  `AlgebraicGeometry.BigFppfOver.isIso_restrictModule_map_zariskiComparisonMap`, which makes `φ`
  bijective on sections over the opens of `S`, by the same unit-and-triangle argument as
  `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit` uses on the small
  étale site.
* **Parasiticity of a kernel and a cokernel from an isomorphism hypothesis.**
  `AlgebraicGeometry.isParasiticFor_kernel_of_isIso_sections` and
  `AlgebraicGeometry.isParasiticFor_cokernel_of_isIso_sections`
  (`StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologySectionwiseIso`) derive both
  parasitic hypotheses from the hypothesis that the morphism is an isomorphism on sections over
  every object flat and locally of finite presentation over `S`, which is what clause (2) of
  0756 says read at the identity chart of `U_τ`; the resulting comparison, with both parasitic
  hypotheses proved rather than assumed, is
  `AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isIso_sections` in the same file.  In
  the statements of *this* file parasiticity is a hypothesis on an arbitrary morphism.
* The right-hand side `H^p(U, 𝒢|_{U_τ})` is cohomology on the small site of an *object* `U` of
  the big site, so it needs the localization comparison. The abstract form of that comparison
  is `Stacks.Cohomology.OverObjectCohomology.h'AddEquivHOver`
  (`StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyOverAnObject`) and its big-site
  form for a fibred category is `AlgebraicGeometry.Stack.cohomologyOverObjectIso`
  (`StacksFrontier.AlgebraicGeometry.Stacks.ObjectCohomologyLocalization`, `@[stacks 075F]`), but
  neither is instantiated at the structure sheaf of a big fppf site — the second file's own
  documentation records that gap. The base change that would feed it,
  `(g^*𝓕)^a ≅ (𝓕^a)|_{(Sch/U)_fppf}`, is
  `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` and
  `AlgebraicGeometry.BigFppfOver.associatedModuleBaseChangeIso`
  (`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectFunctoriality`,
  `@[stacks 03LC]`), which are stated at `τ = fppf`; the same clause for an arbitrary morphism of
  schemes at all five `τ` is
  `AlgebraicGeometry.BigFppfOver.associatedModuleBasePullbackIso`
  (`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackBigSites`).

  **That last bullet is true only for a general `U`.**  At `U = S` the localization comparison is
  not needed at all, and the conclusion of 0756 at `τ = Zar` is now proved:
  `AlgebraicGeometry.BigFppfOver.zariskiSmallSiteCohomologyAddEquiv`
  (`StacksFrontier/AlgebraicGeometry/Descent/Parasitic/FlatCohomologySmallSiteComparison.lean`)
  gives `H^p((Sch/S)_fppf, 𝒢) ≅ H^p(S, 𝒢|_{S_Zar})` in every degree from clauses (1) and (2)
  alone.  Under the reading of "cohomology over `T`" that the statement of record for Stacks 0756
  fixes — global cohomology of the restriction to the big fppf site of `T` — the left-hand side
  at `U = S` is global cohomology of `(Sch/S)_fppf`, the comparison step is applied at the
  terminal object `AlgebraicGeometry.BigFppfOver.opensObj B S hS ⊤` (flat and locally of finite
  presentation over `S`, its structure morphism being the inclusion of `⊤`), and
  `Stacks.Cohomology.TerminalCohomology.h'AddEquivH` replaces `Sheaf.H'` by `Sheaf.H` on both
  sides.  What remains open is the passage from `U = S` to a general `U`, and that file states
  the single hypothesis it needs.

## References

* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 0755](https://stacks.math.columbia.edu/tag/0755)
* [Stacks Project, Tag 0159](https://stacks.math.columbia.edu/tag/0159)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe w v u t

namespace Stacks.Cohomology.LongExactSequence

variable {C : Type t} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- In a short exact sequence of abelian sheaves `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0`, if `ℱ₁` has no
cohomology over `U` in any degree then `H^n(U, ℱ₂) → H^n(U, ℱ₃)` is bijective.

Injectivity is exactness at `H^n(U, ℱ₂)` and surjectivity is exactness at `H^n(U, ℱ₃)`, the
connecting homomorphism landing in the vanishing group `H^{n+1}(U, ℱ₁)`. -/
public theorem bijective_map_g_of_subsingleton
    {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact) (U : C)
    (h₁ : ∀ q : ℕ, Subsingleton (Sheaf.H'.{w} S.X₁ q U)) (n : ℕ) :
    Function.Bijective (map.{w} S.g n U) := by
  refine ⟨?_, fun z ↦ (exact_map_δ S hS n (n + 1) rfl U z).mp ((h₁ (n + 1)).elim _ _)⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, hy⟩ := (exact_map_map S hS n U x).mp hx
  rw [← hy, (h₁ n).elim y 0, map_zero]

/-- In a short exact sequence of abelian sheaves `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0`, if `ℱ₃` has no
cohomology over `U` in any degree then `H^n(U, ℱ₁) → H^n(U, ℱ₂)` is bijective.

Surjectivity is exactness at `H^n(U, ℱ₂)`. Injectivity in positive degree is exactness at
`H^n(U, ℱ₁)`, the connecting homomorphism coming from the vanishing group `H^{n-1}(U, ℱ₃)`; in
degree `0` there is no preceding term and injectivity comes from `ℱ₁ → ℱ₂` being a
monomorphism. -/
public theorem bijective_map_f_of_subsingleton
    {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact) (U : C)
    (h₃ : ∀ q : ℕ, Subsingleton (Sheaf.H'.{w} S.X₃ q U)) (n : ℕ) :
    Function.Bijective (map.{w} S.f n U) := by
  let _ : Mono S.f := hS.mono_f
  refine ⟨?_, fun y ↦ (exact_map_map S hS n U y).mp ((h₃ n).elim _ _)⟩
  match n with
  | 0 => exact Ext.postcomp_mk₀_injective_of_mono (freeYoneda J U) S.f
  | (m + 1) =>
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨z, hz⟩ := (exact_δ_map S hS m (m + 1) rfl U x).mp hx
      rw [← hz, (h₃ m).elim z 0, map_zero]

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] in
/-- The coimage of a morphism of abelian sheaves maps to its target with zero composite into the
cokernel. -/
public theorem factorThruCoimage_comp_cokernel_π
    {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G) :
    Abelian.factorThruCoimage φ ≫ cokernel.π φ = 0 := by
  rw [← cancel_epi (Abelian.coimage.π φ), ← Category.assoc, Abelian.coimage.fac,
    cokernel.condition, comp_zero]

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] in
/-- The short exact sequence `0 → Ker φ → ℱ → Coim φ → 0` of a morphism of abelian sheaves. -/
public theorem shortExact_kernel_coimage {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G) :
    (ShortComplex.mk (kernel.ι φ) (Abelian.coimage.π φ)
      (cokernel.condition (kernel.ι φ))).ShortExact where
  exact := ShortComplex.exact_cokernel (kernel.ι φ)
  mono_f := inferInstance
  epi_g := inferInstance

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] in
/-- The short exact sequence `0 → Coim φ → 𝒢 → Coker φ → 0` of a morphism of abelian sheaves. -/
public theorem shortExact_coimage_cokernel {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G) :
    (ShortComplex.mk (Abelian.factorThruCoimage φ) (cokernel.π φ)
      (factorThruCoimage_comp_cokernel_π φ)).ShortExact where
  exact := by
    let ψ : (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)) ⟶
        (ShortComplex.mk (Abelian.factorThruCoimage φ) (cokernel.π φ)
          (factorThruCoimage_comp_cokernel_π φ)) :=
      { τ₁ := Abelian.coimage.π φ
        τ₂ := 𝟙 G
        τ₃ := 𝟙 (cokernel φ)
        comm₁₂ := by simp
        comm₂₃ := by simp }
    let _ : Epi ψ.τ₁ := by
      change Epi (Abelian.coimage.π φ)
      infer_instance
    let _ : IsIso ψ.τ₂ := by
      change IsIso (𝟙 G)
      infer_instance
    let _ : Mono ψ.τ₃ := by
      change Mono (𝟙 (cokernel φ))
      infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mp (ShortComplex.exact_cokernel φ)
  mono_f := inferInstance
  epi_g := inferInstance

/-- **A morphism of abelian sheaves whose kernel and cokernel have no cohomology over `U` is an
isomorphism on the cohomology over `U`.**

The morphism factors as the epimorphism onto its coimage followed by the monomorphism of the
coimage into its target, and each of the two is an isomorphism on cohomology by the vanishing of
one of the two outer terms. -/
public theorem bijective_map_of_subsingleton_kernel_cokernel
    {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G) (U : C)
    (hker : ∀ q : ℕ, Subsingleton (Sheaf.H'.{w} (kernel φ) q U))
    (hcoker : ∀ q : ℕ, Subsingleton (Sheaf.H'.{w} (cokernel φ) q U)) (n : ℕ) :
    Function.Bijective (map.{w} φ n U) := by
  have hb₁ : Function.Bijective (map.{w} (Abelian.coimage.π φ) n U) :=
    bijective_map_g_of_subsingleton (shortExact_kernel_coimage φ) U hker n
  have hb₂ : Function.Bijective (map.{w} (Abelian.factorThruCoimage φ) n U) :=
    bijective_map_f_of_subsingleton (shortExact_coimage_cokernel φ) U hcoker n
  have hfac : (Ext.mk₀ (Abelian.coimage.π φ)).comp
      (Ext.mk₀ (Abelian.factorThruCoimage φ)) (zero_add 0) = Ext.mk₀ φ := by
    rw [Ext.mk₀_comp_mk₀, Abelian.coimage.fac]
  have hcomp : (map.{w} φ n U : Sheaf.H'.{w} F n U → Sheaf.H'.{w} G n U) =
      (map.{w} (Abelian.factorThruCoimage φ) n U) ∘ (map.{w} (Abelian.coimage.π φ) n U) := by
    funext x
    change x.comp (Ext.mk₀ φ) (add_zero n) =
      (x.comp (Ext.mk₀ (Abelian.coimage.π φ)) (add_zero n)).comp
        (Ext.mk₀ (Abelian.factorThruCoimage φ)) (add_zero n)
    calc x.comp (Ext.mk₀ φ) (add_zero n)
        = x.comp ((Ext.mk₀ (Abelian.coimage.π φ)).comp
            (Ext.mk₀ (Abelian.factorThruCoimage φ)) (zero_add 0)) (add_zero n) := by
          rw [hfac]
      _ = (x.comp (Ext.mk₀ (Abelian.coimage.π φ)) (add_zero n)).comp
            (Ext.mk₀ (Abelian.factorThruCoimage φ)) (add_zero n) :=
          (Ext.comp_assoc x _ _ (add_zero n) (zero_add 0) (by omega)).symm
  rw [hcomp]
  exact hb₂.comp hb₁

end Stacks.Cohomology.LongExactSequence

namespace AlgebraicGeometry

/-- **A morphism of sheaves of `𝒪`-modules on the big fppf site over `S` whose kernel and
cokernel are parasitic induces isomorphisms `H^p(U, ℱ) → H^p(U, 𝒢)` at every object `U` flat
over `S`.**

This is the step of Stacks 0756 which rests on Stacks 0755: the kernel and the cokernel have
vanishing cohomology at `U` by `AlgebraicGeometry.bigFppfCohomology_isZero_of_isParasitic`, and
a morphism with that property is an isomorphism on cohomology. The source lemma then identifies
`H^p(U, ℱ)` with the small-site cohomology `H^p(U, 𝒢|_{U_τ})` by Stacks 03DW, which this
statement does not assert.

The parasitic hypotheses are the pointwise expansion of `AlgebraicGeometry.IsParasitic`, as in
`AlgebraicGeometry.bigFppfCohomology_isZero_of_isParasitic`, and the kernel and cokernel are
those of the category of sheaves of `𝒪`-modules.

The clause string says which step this is.  Its hypotheses are part (2) of [Stacks, Tag 06ZL] —
vanishing at every object flat over `S`, finite presentation not assumed — whereas 0756 derives
part (1), vanishing at the objects flat *and locally of finite presentation* over `S`.  The step
in that second form is `AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isParasiticFor`
below, which carries the same tag with a clause string naming it. -/
@[stacks 0756 "cohomology comparison step, from Tag 0755"]
public theorem bigFppfCohomology_map_bijective_of_isParasitic
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}]
    [(AlgebraicGeometry.BigFppfOver.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})]
    {𝒪 : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) RingCat.{u}}
    {F G : SheafOfModules.{u} 𝒪} (φ : F ⟶ G)
    (hker : ∀ X : AlgebraicGeometry.BigFppfOver B S hS,
      Flat ((Over.post B.inclusion).obj X).hom →
        Subsingleton ((kernel φ).val.obj (Opposite.op X)))
    (hcoker : ∀ X : AlgebraicGeometry.BigFppfOver B S hS,
      Flat ((Over.post B.inclusion).obj X).hom →
        Subsingleton ((cokernel φ).val.obj (Opposite.op X)))
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (hU : Flat ((Over.post B.inclusion).obj U).hom) (p : ℕ) :
    Function.Bijective
      (Stacks.Cohomology.LongExactSequence.map.{w}
        ((SheafOfModules.toSheaf 𝒪).map φ) p U) := by
  let T := SheafOfModules.toSheaf.{u} 𝒪
  exact Stacks.Cohomology.LongExactSequence.bijective_map_of_subsingleton_kernel_cokernel
    (T.map φ) U
    (fun q ↦ AddCommGrpCat.subsingleton_of_isZero <|
      (bigFppfCohomology_isZero_of_isParasitic B S hS (kernel φ) hker U hU q).of_iso
        (((Sheaf.cohomologyPresheafFunctor.{w} _ q).mapIso (PreservesKernel.iso T φ).symm).app
          (op U)))
    (fun q ↦ AddCommGrpCat.subsingleton_of_isZero <|
      (bigFppfCohomology_isZero_of_isParasitic B S hS (cokernel φ) hcoker U hU q).of_iso
        (((Sheaf.cohomologyPresheafFunctor.{w} _ q).mapIso (PreservesCokernel.iso T φ).symm).app
          (op U))) p

/-- **A morphism of sheaves of `𝒪`-modules on the big fppf site over `S` whose kernel and
cokernel are parasitic for the fppf topology induces isomorphisms `H^p(U, ℱ) → H^p(U, 𝒢)` at
every object `U` flat and locally of finite presentation over `S`.**

This is the step of [Stacks, Tag 0756] which rests on [Stacks, Tag 0755], in the form 0756 uses
it: the kernel and the cokernel have vanishing cohomology at `U` by
`AlgebraicGeometry.cohomology_isZero_of_isParasiticFor_fppf`, which is part (1) of 0755, and a
morphism with that property is an isomorphism on cohomology by
`Stacks.Cohomology.LongExactSequence.bijective_map_of_subsingleton_kernel_cokernel`.

The hypotheses are `AlgebraicGeometry.IsParasiticFor`, part (2) of [Stacks, Tag 06ZL], for the
fppf coverings of `S`: vanishing on the members of fppf coverings of the base, which are exactly
the objects flat and locally of finite presentation over `S`.  They are what 0756 derives from
its assumptions (1) and (2), and they are weaker than the `AlgebraicGeometry.IsParasitic` of
`AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isParasitic`, which asks for vanishing at
every flat object, finite presentation not assumed.  Correspondingly the conclusion here is at
the objects flat and locally of finite presentation, which is where 0756 states it.

This is the form with parasiticity hypothesised, which is what an arbitrary morphism needs.  For
a morphism which is an isomorphism on sections over every such object the two hypotheses are
themselves theorems, and the resulting statement is
`AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isIso_sections`
(`StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologySectionwiseIso`).  The
identification of `H^p(U, ℱ)` with the small-site cohomology `H^p(U, 𝒢|_{U_τ})`, which is the
conclusion of 0756, is established at `τ = Zariski` and `U = S` by
`AlgebraicGeometry.BigFppfOver.zariskiSmallSiteCohomologyAddEquiv`
(`StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologySmallSiteComparison`). -/
@[stacks 0756 "cohomology comparison step, from Tag 0755, at the objects flat and locally of \
finite presentation over S, which is the shape 0756 uses"]
public theorem bigFppfCohomology_map_bijective_of_isParasiticFor
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}]
    [(AlgebraicGeometry.BigFppfOver.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})]
    {𝒪 : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) RingCat.{u}}
    {F G : SheafOfModules.{u} 𝒪} (φ : F ⟶ G)
    (hker : AlgebraicGeometry.IsParasiticFor S (Over.post B.inclusion)
      (AlgebraicGeometry.BigFppfOver.IsCovering B S hS) (kernel φ).val)
    (hcoker : AlgebraicGeometry.IsParasiticFor S (Over.post B.inclusion)
      (AlgebraicGeometry.BigFppfOver.IsCovering B S hS) (cokernel φ).val)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (hU : Flat ((Over.post B.inclusion).obj U).hom ∧
      LocallyOfFinitePresentation ((Over.post B.inclusion).obj U).hom) (p : ℕ) :
    Function.Bijective
      (Stacks.Cohomology.LongExactSequence.map.{w}
        ((SheafOfModules.toSheaf 𝒪).map φ) p U) := by
  let T := SheafOfModules.toSheaf.{u} 𝒪
  exact Stacks.Cohomology.LongExactSequence.bijective_map_of_subsingleton_kernel_cokernel
    (T.map φ) U
    (fun q ↦ AddCommGrpCat.subsingleton_of_isZero <|
      (cohomology_isZero_of_isParasiticFor_fppf B S hS (kernel φ) hker U hU q).of_iso
        (((Sheaf.cohomologyPresheafFunctor.{w} _ q).mapIso (PreservesKernel.iso T φ).symm).app
          (op U)))
    (fun q ↦ AddCommGrpCat.subsingleton_of_isZero <|
      (cohomology_isZero_of_isParasiticFor_fppf B S hS (cokernel φ) hcoker U hU q).of_iso
        (((Sheaf.cohomologyPresheafFunctor.{w} _ q).mapIso (PreservesCokernel.iso T φ).symm).app
          (op U))) p

end AlgebraicGeometry

end
