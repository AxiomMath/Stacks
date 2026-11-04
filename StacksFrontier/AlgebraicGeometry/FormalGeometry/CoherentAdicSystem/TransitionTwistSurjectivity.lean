module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.TransitionKernelTwistVanishing
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.LongExactSequence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxEpiAssembly

/-!
# Surjectivity on sections of the twisted transition maps of a coherent adic system

The cohomological step of [Stacks, Tag 0885]. For `𝓕` a coherent adic system along an ideal
sheaf the transition map `𝓕_{n+1} ⟶ 𝓕_n` sits in a short exact sequence

  `0 ⟶ Ker(𝓕_{n+1} ⟶ 𝓕_n) ⟶ 𝓕_{n+1} ⟶ 𝓕_n ⟶ 0`,

and twisting by an invertible `𝒪_X`-module `N` leaves it short exact, tensoring by an invertible
module being an autoequivalence of `Mod(𝒪_X)`. The long exact cohomology sequence then makes

  `Γ(U, 𝓕_{n+1} ⊗ N) ⟶ Γ(U, 𝓕_n ⊗ N)`

surjective as soon as `H¹(U, Ker(𝓕_{n+1} ⟶ 𝓕_n) ⊗ N) = 0`. Feeding in the uniform vanishing of
[Stacks, Tag 0884] at `N = L ^⊗ d` gives one `d₀` beyond which this holds for every `n` at once.

## Main definitions

* `Stacks.Coherent.transitionShortComplex` — the short complex
  `Ker(𝓕_{n+1} ⟶ 𝓕_n) ⟶ 𝓕_{n+1} ⟶ 𝓕_n`, whose first term is `Stacks.Coherent.transitionKernel`
  at `n + 1`.
* `Stacks.Coherent.tensorRightModules` — tensoring on the right by an `𝒪_X`-module, as an
  endofunctor of `X.Modules`. Its value is the tensor product on the nose
  (`Stacks.Coherent.tensorRightModules_obj`); what it adds is the ascribed type, which is what
  lets the equivalence and additivity instances below be found.

## Main results

* `Stacks.Coherent.shortExact_transitionShortComplex` — it is short exact. Nothing beyond the
  defining properties of a coherent adic system is used: exactness and the monomorphism are
  those of a kernel, and the epimorphism is
  `Stacks.Coherent.IsCoherentAdicSystem.epi_map_succ`.
* `Stacks.Coherent.epi_secF_map_tensorRight_g_of_isZero_Hgroup` — the cohomological step, for an
  **arbitrary** short exact sequence of `𝒪_X`-modules, an arbitrary invertible twist and an
  arbitrary open: vanishing of `H¹` of the twisted first term makes the twisted third map
  surjective on sections.
* `Stacks.Coherent.epi_secF_map_tensorRight_transition_of_isZero_Hgroup` and
  `Stacks.Coherent.surjective_app_tensorRight_transition_of_isZero_Hgroup` — the same at the
  transition maps of a coherent adic system, as an epimorphism and read on elements.
* `Stacks.Coherent.exists_surjective_app_tensorRight_transition_tensorPowModule` — **the step
  [Stacks, Tag 0885] waits on**: for `f : X ⟶ Spec A` proper over a Noetherian base and `L` an
  `f`-ample invertible module, there is a `d₀` such that for every `n` and every `d ≥ d₀` the map
  `H⁰(X, 𝓕_{n+1} ⊗ L ^⊗ d) ⟶ H⁰(X, 𝓕_n ⊗ L ^⊗ d)` is surjective.

## Implementation notes

**What is needed and what is not.** Properness and relative ampleness enter *only* through
[Stacks, Tag 0884]: every result before the last assumes neither, and
`epi_secF_map_tensorRight_g_of_isZero_Hgroup` assumes nothing about `X`, about the open, or about
quasi-coherence or coherence of the sheaves — only that the sequence is short exact and the twist
invertible. The twist is not special either: the general statement is for an arbitrary short
exact sequence, and the adic system appears only in the specialisations.

**The long exact sequence is already available.**
`Stacks.SerreAffinenessCriterion.epi_secF_map_g_of_isZero_hgroup_one`
(`StacksFrontier/AlgebraicGeometry/SerreAffinenessCriterion/LongExactSequence.lean`) is exactness of
`Γ(U, ℱ₂) ⟶ Γ(U, ℱ₃) ⟶ H¹(U, ℱ₁)`, read off the right derived δ-functor of `Γ(U, -)`; nothing
about the long exact sequence is constructed here.

**Exactness of the twist is read off an equivalence.** Tensoring on the right by an invertible
sheaf of modules is an equivalence
(`Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible`), hence preserves
finite limits and finite colimits, so `CategoryTheory.ShortComplex.ShortExact.map_of_exact`
applies. Additivity is taken from preservation of binary products rather than assumed, as
`Stacks.ProjectionFormula.additive_tensorRightInvertible` does for the ringed-space tensor
product. Nothing about the tensor product itself is used: the twist enters only as an
equivalence, so the sheafification in
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, which makes that tensor product only
right exact in general, is never unfolded.

**Why `tensorRightModules` exists, rather than the twist being written out.**
`AlgebraicGeometry.Scheme.Modules` is `SheafOfModules X.ringCatSheaf`, while
`Stacks.SheafOfModules.TensorPower.tensorRightFunctor X.presheaf _ N` is an endofunctor of
`SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf _)`. The
two are definitionally equal but not syntactically so, and instance search — being syntactic —
does not bridge them: with the functor written out under a type ascription, the equivalence can
still be supplied as a term, but `PreservesZeroMorphisms` is then looked for at the instances
`ShortComplex.ShortExact.map_of_exact` fixes rather than the ones the ascription produced, and is
not found. Ascribing the functor's type at a definition, where the invertibility instance is
declared once and the rest of the chain is inferred from it, is what makes `map_of_exact` apply;
this is the discipline of `StacksFrontier/AlgebraicGeometry/TwistedSheaf/Exactness.lean` (for the
same functor folded over an exponent vector) and of
`Stacks.ProjectionFormula.tensorRightInvertible` (for the ringed-space tensor product). The
value of `tensorRightModules` and
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` agree by definition, which is why the
hypotheses can be stated with `tensorSheaf` — the spelling [Stacks, Tag 0884] produces — while
the conclusions are about the functor.

**What this does not do.** [Stacks, Tag 0885] needs two further steps, both about generation
rather than cohomology: lifting a finite generating family of `𝓕_1 ⊗ L ^⊗ d` through the tower
using the surjectivity proved here, and assembling the lifts into a morphism out of a finite sum
of negative twists, which is then an epimorphism by [Stacks, Tag 087Y]. Neither is done here, and
the generation hypothesis of the two carriers of [Stacks, Tag 0885] is untouched.

## References

* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)

universe u

namespace Stacks.Coherent

/-! ### The transition sequence of a coherent adic system -/

/-- **The short complex `Ker(𝓕_{n+1} ⟶ 𝓕_n) ⟶ 𝓕_{n+1} ⟶ 𝓕_n`** of a coherent adic system.

The indexing is that of `Stacks.Coherent.CoherentAdicSystems`, which is zero-indexed with its
term `n` the source's `𝓕_{n+1}`; the first term is therefore
`Stacks.Coherent.transitionKernel 𝓕 (n + 1)`, by definition. -/
public def transitionShortComplex {X : Scheme.{u}} {I : X.IdealSheafData}
    (𝓕 : CoherentAdicSystems I) (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι (𝓕.obj.map (homOfLE (Nat.le_succ n)).op))
    (𝓕.obj.map (homOfLE (Nat.le_succ n)).op) (kernel.condition _)

/-- **The transition sequence of a coherent adic system is short exact.** Exactness and the
monomorphism are those of a kernel; the epimorphism is
`Stacks.Coherent.IsCoherentAdicSystem.epi_map_succ`, the transition map being the projection onto
a quotient followed by an isomorphism. -/
public theorem shortExact_transitionShortComplex {X : Scheme.{u}} {I : X.IdealSheafData}
    (𝓕 : CoherentAdicSystems I) (n : ℕ) : (transitionShortComplex 𝓕 n).ShortExact :=
  { exact := ShortComplex.exact_kernel _
    mono_f := inferInstanceAs (Mono (kernel.ι (𝓕.obj.map (homOfLE (Nat.le_succ n)).op)))
    epi_g := 𝓕.property.epi_map_succ n }

/-! ### Twisting by an invertible module, at the scheme spelling -/

/-- **Tensoring an `𝒪_X`-module on the right by `N`**, as an endofunctor of `X.Modules`: this is
`Stacks.SheafOfModules.TensorPower.tensorRightFunctor` with its type ascribed at the scheme
spelling of the category of modules, so that the instances below are stated where instance search
finds them. Its value at `M` is the tensor product
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.presheaf _ M N`, by definition. -/
public def tensorRightModules (X : Scheme.{u}) (N : X.Modules) : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
    ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
      (forget₂ CommRingCat RingCat) (isSheaf_structureRingPresheaf X)⟩).flip.obj N

/-- Tensoring on the right by `N` sends `M` to `M ⊗_{𝒪_X} N`. -/
public theorem tensorRightModules_obj {X : Scheme.{u}} (N M : X.Modules) :
    (tensorRightModules X N).obj M =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
      (forget₂ CommRingCat RingCat) (isSheaf_structureRingPresheaf X)⟩).obj M).obj N :=
  rfl

/-- **Tensoring on the right by an invertible module is an equivalence**, [Stacks, Tag 01CS], at
the scheme spelling. This is
`Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible`, which instance search
does not find through the ascription and which is therefore applied here as a term. -/
public instance isEquivalence_tensorRightModules (X : Scheme.{u}) (N : X.Modules)
    [Stacks.Ample.IsInvertibleModule X N] : (tensorRightModules X N).IsEquivalence :=
  Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible X.presheaf
    (isSheaf_structureRingPresheaf X) N

/-- Tensoring on the right by an invertible module is additive, preserving binary products. -/
public instance additive_tensorRightModules (X : Scheme.{u}) (N : X.Modules)
    [Stacks.Ample.IsInvertibleModule X N] : (tensorRightModules X N).Additive :=
  (tensorRightModules X N).additive_of_preserves_binary_products

/-! ### The cohomological step -/

/-- **Twisting by an invertible module and reading the long exact sequence.** Let
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` be a short exact sequence of `𝒪_X`-modules, `N` an invertible
`𝒪_X`-module and `U` an open of `X`. If `H¹(U, ℱ₁ ⊗ N) = 0` then `Γ(U, ℱ₂ ⊗ N) ⟶ Γ(U, ℱ₃ ⊗ N)`
is an epimorphism.

No hypothesis on `X`, on `U`, or on the quasi-coherence of the sheaves: tensoring by an
invertible module is an autoequivalence of `Mod(𝒪_X)`, so the twisted sequence is again short
exact, and the conclusion is then exactness of `Γ(U, ℱ₂ ⊗ N) ⟶ Γ(U, ℱ₃ ⊗ N) ⟶ H¹(U, ℱ₁ ⊗ N)`
in the long exact cohomology sequence. -/
public theorem epi_secF_map_tensorRight_g_of_isZero_Hgroup {X : Scheme.{u}} (U : X.Opens)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N]
    (h : IsZero (Hgroup X.ringCatSheaf U 1
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
      (forget₂ CommRingCat RingCat) (isSheaf_structureRingPresheaf X)⟩).obj S.X₁).obj N))) :
    Epi ((secF X.ringCatSheaf U).map ((tensorRightModules X N).map S.g)) :=
  Stacks.SerreAffinenessCriterion.epi_secF_map_g_of_isZero_hgroup_one X U
    (hS.map_of_exact (tensorRightModules X N)) h

/-- **The cohomological step at the transition maps of a coherent adic system.** If
`H¹(U, Ker(𝓕_{n+1} ⟶ 𝓕_n) ⊗ N) = 0` for an invertible `N`, then
`Γ(U, 𝓕_{n+1} ⊗ N) ⟶ Γ(U, 𝓕_n ⊗ N)` is an epimorphism.

Neither properness nor ampleness is assumed: the hypothesis is the vanishing itself. -/
public theorem epi_secF_map_tensorRight_transition_of_isZero_Hgroup {X : Scheme.{u}}
    {I : X.IdealSheafData} (𝓕 : CoherentAdicSystems I) (n : ℕ) (U : X.Opens)
    (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N]
    (h : IsZero (Hgroup X.ringCatSheaf U 1
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
      (forget₂ CommRingCat RingCat) (isSheaf_structureRingPresheaf X)⟩).obj
        (transitionKernel 𝓕 (n + 1))).obj N))) :
    Epi ((secF X.ringCatSheaf U).map
      ((tensorRightModules X N).map (𝓕.obj.map (homOfLE (Nat.le_succ n)).op))) :=
  epi_secF_map_tensorRight_g_of_isZero_Hgroup U (shortExact_transitionShortComplex 𝓕 n) N h

/-- **`epi_secF_map_tensorRight_transition_of_isZero_Hgroup` read on elements.** Every section of
`𝓕_n ⊗ N` over `U` lifts to a section of `𝓕_{n+1} ⊗ N` over `U`. -/
public theorem surjective_app_tensorRight_transition_of_isZero_Hgroup {X : Scheme.{u}}
    {I : X.IdealSheafData} (𝓕 : CoherentAdicSystems I) (n : ℕ) (U : X.Opens)
    (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N]
    (h : IsZero (Hgroup X.ringCatSheaf U 1
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
      (forget₂ CommRingCat RingCat) (isSheaf_structureRingPresheaf X)⟩).obj
        (transitionKernel 𝓕 (n + 1))).obj N))) :
    Function.Surjective
      (((tensorRightModules X N).map
        (𝓕.obj.map (homOfLE (Nat.le_succ n)).op)).val.app (op U)) :=
  (AddCommGrpCat.epi_iff_surjective _).1
    (epi_secF_map_tensorRight_transition_of_isZero_Hgroup 𝓕 n U N h)

/-! ### The uniform statement, with Stacks 0884 supplied -/

/-- **The cohomological step of [Stacks, Tag 0885].** Let `A` be a Noetherian ring, `I ⊆ A` an
ideal, `f : X ⟶ Spec A` proper, `L` an invertible `𝒪_X`-module ample relative to `f`, and let `𝓕`
be an object of `Coh(X, 𝓘)` for `𝓘 = I · 𝒪_X`. Then there is an integer `d₀` such that

  `H⁰(X, 𝓕_{n+1} ⊗ L ^⊗ d) ⟶ H⁰(X, 𝓕_n ⊗ L ^⊗ d)`

is surjective for every `n ≥ 0` and every `d ≥ d₀` — one `d₀` for the whole system.

The `d₀` is that of [Stacks, Tag 0884]
(`Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule`), which is where
properness and relative ampleness are used; the passage from the vanishing to the surjectivity
is `Stacks.Coherent.surjective_app_tensorRight_transition_of_isZero_Hgroup`, which uses
neither. -/
public theorem exists_surjective_app_tensorRight_transition_tensorPowModule
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)) :
    ∃ d₀ : ℤ, ∀ (n : ℕ) (d : ℤ), d₀ ≤ d →
      Function.Surjective
        (((tensorRightModules X (Stacks.Ample.tensorPowModule X L d)).map
          (𝓕.obj.map (homOfLE (Nat.le_succ n)).op)).val.app (op ⊤)) := by
  obtain ⟨d₀, hd₀⟩ :=
    exists_isZero_Hgroup_transitionKernel_tensorPowModule A I f L hL 𝓕
      (hasAssociatedGradedTwistVanishing_of_isProper A I f L)
  exact ⟨d₀, fun n d hd =>
    surjective_app_tensorRight_transition_of_isZero_Hgroup 𝓕 n ⊤ _ (hd₀ (n + 1) d hd)⟩

end Stacks.Coherent

end
