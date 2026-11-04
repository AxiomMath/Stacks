module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteExtensionByZeroPresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Modules with a finite presentation by extensions by zero form a weak Serre subcategory

Let `C` be a site with a distinguished collection `B` of objects satisfying the three conditions
of Stacks 0937, and let `R` be a sheaf of rings on `C`. Let `A ⊂ Mod(R)` be the full subcategory
of sheaves of modules admitting a finite presentation by extensions by zero of the restricted
structure sheaf at distinguished objects, that is the predicate
`Stacks.SheafOfModules.HasFiniteExtensionByZeroPresentation` of Stacks 093D. **Stacks 093H** says
that if the kernel of every morphism

`⊕_{j = 1, …, m} j_{V_j!} R|_{V_j} ⟶ ⊕_{i = 1, …, n} j_{U_i!} R|_{U_i}`

between finite direct sums of such extensions by zero, with all `U_i` and `V_j` distinguished,
belongs to `A`, then `A` is a weak Serre subcategory of `Mod(R)`.

The proof is the one in the source. `StacksCore.CategoryTheory.Abelian.SerreClass.Weak` reduces a
weak Serre subcategory to five closure conditions (Stacks 0754). Closure under isomorphisms is
immediate from the shape of the predicate and the zero object has the empty presentation;
closure under cokernels is Stacks 093E and closure under extensions is Stacks 093G, both already
in the library. What remains is closure under kernels, and that is the content of the kernel
hypothesis: a module in `A` is the target of an epimorphism from a finite direct sum of
extensions by zero whose own kernel is in `A`, and the two pullback squares of the source's
argument turn the kernel of a morphism `F ⟶ G` of modules in `A` into one such kernel.

## Main results

* `Stacks.SheafOfModules.isClosedUnderKernels_of_presentations`: the abelian step, isolated. A
  property of objects of an abelian category which is closed under isomorphisms, cokernels and
  extensions, holds for a family of generators `G i`, holds for the kernel of every morphism
  between members of that family, and for which every object with the property is a cokernel of
  such a morphism, is closed under kernels.
* `Stacks.SheafOfModules.isWeakSerreClass_hasFiniteExtensionByZeroPresentation`: **Stacks
  Project, Tag 093H.**

## Implementation notes

**The abelian step is stated for an arbitrary family of generators.** What the argument uses
about the finite direct sums of extensions by zero is only that they have the property, that the
kernel of a morphism between two of them has it, and that every object with the property is a
cokernel of such a morphism. Isolating that makes the geometric part of Stacks 093H a matter of
naming the family — here indexed by a natural number together with a tuple of distinguished
objects — and of quoting Stacks 093E and 093G.

**Why the two pullbacks.** Given `f : X ⟶ Y` with `X` and `Y` in the class, choose an epimorphism
`p : G j ⟶ Y` from a generator with `ker p` in the class. Pulling `f` back along `p` gives
`ker (pullback.fst f p) ≅ ker p`, so the pullback is an extension of `X` by an object of the
class and therefore lies in it; choosing an epimorphism `q : G i ⟶ pullback f p` and applying the
kernel–cokernel sequence of the composite `q ≫ pullback.snd f p`, whose kernel is a kernel of a
morphism between two generators, gives `ker (pullback.snd f p)`, and that is `ker f` by the other
half of the same pullback square.

**The universe-lifting instances.** `HasSheafify J AddCommGrpCat` and
`J.WEqualsLocallyBijective AddCommGrpCat` are supplied as `local instance`s derived from
`UnivLE`, exactly as in `...Sheaf.ExtensionByZeroUnit` and
`...Sheaf.FiniteExtensionByZeroPresentation`, rather than assumed: they hold for every site which
is small in the enlarged value universe, which the `UnivLE` hypotheses express, so they add
nothing to the statement. The module universe is `max u₁ v₁ w t`, as it is for the extension by
zero itself.

## References

* [Stacks Project, Tag 093H](https://stacks.math.columbia.edu/tag/093H)
* [Stacks Project, Tag 0937](https://stacks.math.columbia.edu/tag/0937)
* [Stacks Project, Equation 18.30.7.2, Tag 093D](https://stacks.math.columbia.edu/tag/093D)
* [Stacks Project, Tag 093E](https://stacks.math.columbia.edu/tag/093E)
* [Stacks Project, Tag 093G](https://stacks.math.columbia.edu/tag/093G)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

universe u₂ v₂ u₁ v₁ w t

namespace Stacks.SheafOfModules

/-! ### The abelian step -/

section Abelian

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- The third term of a short exact sequence whose first two terms satisfy a property closed
under cokernels satisfies it as well: the third term is the cokernel of the first map. -/
private lemma prop_of_exact_epi (P : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderCokernels]
    (E : ShortComplex D) (hE : E.Exact) [Epi E.g] (h₁ : P E.X₁) (h₂ : P E.X₂) :
    P E.X₃ :=
  P.prop_of_iso (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel E.f)
    hE.gIsCokernel) (P.prop_cokernel E.f h₁ h₂)

/-- **Descending along an epimorphism.** If `p : X ⟶ Y` is an epimorphism and the property holds
for `ker p` and for `ker (p ≫ f)`, then it holds for `ker f`: the kernel–cokernel sequence of the
composite is exact, its last term vanishes because `p` is an epimorphism, and so `ker f` is the
cokernel of `ker p ⟶ ker (p ≫ f)`. -/
private lemma prop_kernel_of_epi (P : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderCokernels]
    {X Y Z : D} (p : X ⟶ Y) [Epi p] (f : Y ⟶ Z)
    (hp : P (kernel p)) (hpf : P (kernel (p ≫ f))) : P (kernel f) := by
  let E := kernelCokernelCompSequence p f
  have hE := kernelCokernelCompSequence_exact p f
  have : Epi (E.map' 1 2) := (ShortComplex.exact_iff_epi (E.sc' hE.toIsComplex 1 2 3)
    ((isZero_cokernel_of_epi p).eq_of_tgt _ _)).1 (hE.exact' 1 2 3)
  exact prop_of_exact_epi P (E.sc' hE.toIsComplex 0 1 2) (hE.exact' 0 1 2) hp hpf

/-- **Closure under kernels from a family of generators.** Let `P` be a property of objects of an
abelian category which is closed under isomorphisms, cokernels and extensions. Suppose given a
family `G` of objects with `P`, such that the kernel of every morphism between members of the
family has `P`, and such that every object with `P` is a cokernel of a morphism between members
of the family. Then `P` is closed under kernels.

This is the abelian content of Stacks 093H. -/
theorem isClosedUnderKernels_of_presentations (P : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    {I : Type*} (G : I → D) (hG : ∀ i, P (G i))
    (hker : ∀ i j, ∀ f : G i ⟶ G j, P (kernel f))
    (hpres : ∀ X, P X → ∃ i j, ∃ f : G i ⟶ G j, Nonempty (cokernel f ≅ X)) :
    P.IsClosedUnderKernels := by
  have hres (X : D) (hX : P X) : ∃ i, ∃ p : G i ⟶ X, Epi p ∧ P (kernel p) := by
    obtain ⟨i, j, r, ⟨e⟩⟩ := hpres X hX
    exact ⟨j, cokernel.π r ≫ e.hom, inferInstance,
      P.prop_of_iso (kernelCompMono (cokernel.π r) e.hom).symm (P.prop_of_iso
        (Abelian.coimageIsoImage r) (P.prop_cokernel _ (hker i j r) (hG i)))⟩
  constructor
  rintro X ⟨f, k, hk, hA, hB⟩
  apply P.prop_of_iso (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)
  obtain ⟨j, p, _, hkp⟩ := hres _ hB
  let sq := IsPullback.of_hasPullback f p
  have : IsIso (kernel.map (pullback.fst f p) p (pullback.snd f p) f sq.w) :=
    isIso_kernel_map_of_isPullback sq
  have hfst : P (kernel (pullback.fst f p)) :=
    P.prop_of_iso (asIso (kernel.map _ _ _ _ sq.w)).symm hkp
  have hPB : P (pullback f p) := P.prop_X₂_of_shortExact
    (ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact (pullback.fst f p))
      inferInstance (inferInstanceAs (Epi (pullback.fst f p)))) hfst hA
  obtain ⟨i, q, _, hkq⟩ := hres _ hPB
  have : IsIso (kernel.map (pullback.snd f p) f (pullback.fst f p) p sq.flip.w) :=
    isIso_kernel_map_of_isPullback sq.flip
  exact P.prop_of_iso (asIso (kernel.map _ _ _ _ sq.flip.w))
    (prop_kernel_of_epi P q _ hkq (hker i j _))

end Abelian

/-! ### The weak Serre subcategory of Stacks 093H -/

section Presentation

variable {C : Type u₁} [Category.{v₁} C]

attribute [local instance] siteHasSheafify siteWEqualsLocallyBijective

variable (S : QuasiCompactObjectsSituation C) (R : Sheaf S.topology RingCat.{w})

/-- Having a finite presentation by extensions by zero is invariant under isomorphism: compose
the comparison isomorphism of the presentation with the given one. -/
theorem hasFiniteExtensionByZeroPresentation_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun F : SheafOfModules.{max u₁ v₁ w t} R =>
        HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R F) :=
  ⟨fun e ⟨n, m, U, V, hU, hV, f, ⟨eX⟩⟩ => ⟨n, m, U, V, hU, hV, f, ⟨eX.trans e⟩⟩⟩

/-- The zero module has a finite presentation by extensions by zero: the empty direct sum is a
zero object, and the cokernel of its zero endomorphism is itself. -/
theorem hasFiniteExtensionByZeroPresentation_containsZero :
    ObjectProperty.ContainsZero
      (fun F : SheafOfModules.{max u₁ v₁ w t} R =>
        HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R F) := by
  refine ⟨0, isZero_zero _, ?_⟩
  let U : Fin 0 → C := Fin.elim0
  let A := ∐ fun i : Fin 0 => extensionByZeroUnit.{u₁, v₁, w, t} R (U i)
  have hA : IsZero A := (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun i => Fin.elim0 i)
  exact ⟨0, 0, U, U, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), (0 : A ⟶ A),
    ⟨(cokernelZeroIsoTarget (X := A) (Y := A)).trans (hA.iso (isZero_zero _))⟩⟩

/-- A finite direct sum of extensions by zero of the restricted structure sheaf at distinguished
objects has a finite presentation by extensions by zero: it is the cokernel of the zero morphism
out of the empty sum. -/
theorem hasFiniteExtensionByZeroPresentation_coproduct {n : ℕ} (U : Fin n → C)
    (hU : ∀ i, U i ∈ S.objects) :
    HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R
      (∐ fun i => extensionByZeroUnit.{u₁, v₁, w, t} R (U i)) :=
  ⟨n, 0, U, Fin.elim0, hU, fun i => Fin.elim0 i, 0, ⟨cokernelZeroIsoTarget⟩⟩

/-- **Stacks Project, Tag 093H.** On a site with a distinguished collection of objects which
covers every object, consists of quasi-compact objects and whose coverings have quasi-compact
pairwise fibre products, the sheaves of modules with a finite presentation by extensions by zero
form a **weak Serre subcategory** of the category of all sheaves of modules, as soon as the
kernel of every morphism between finite direct sums of extensions by zero of the restricted
structure sheaf at distinguished objects has such a presentation.

Closure under cokernels is Stacks 093E and closure under extensions is Stacks 093G; closure
under kernels is `Stacks.SheafOfModules.isClosedUnderKernels_of_presentations` applied to the
family of finite direct sums of extensions by zero at distinguished objects, which is exactly
where the hypothesis enters. -/
@[stacks 093H]
theorem isWeakSerreClass_hasFiniteExtensionByZeroPresentation (hEnough : S.HasEnoughObjects)
    (hqc : S.ObjectsAreQuasiCompact) (hqs : S.CoverPullbacksAreQuasiCompact)
    (hKernel : ∀ (n m : ℕ) (U : Fin n → C) (V : Fin m → C),
      (∀ i, U i ∈ S.objects) → (∀ j, V j ∈ S.objects) →
      ∀ f : (∐ fun j => extensionByZeroUnit.{u₁, v₁, w, t} R (V j)) ⟶
          (∐ fun i => extensionByZeroUnit.{u₁, v₁, w, t} R (U i)),
        HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R (kernel f)) :
    ObjectProperty.IsWeakSerreClass
      (fun F : SheafOfModules.{max u₁ v₁ w t} R =>
        HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R F) := by
  let P : ObjectProperty (SheafOfModules.{max u₁ v₁ w t} R) :=
    fun F => HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R F
  have : P.IsClosedUnderIsomorphisms :=
    hasFiniteExtensionByZeroPresentation_isClosedUnderIsomorphisms.{u₁, v₁, w, t} S R
  have : P.ContainsZero :=
    hasFiniteExtensionByZeroPresentation_containsZero.{u₁, v₁, w, t} S R
  have : P.IsClosedUnderCokernels := by
    constructor
    rintro Z ⟨f, k, hk, hF, hG⟩
    have : HasCokernel f := ⟨⟨k, hk⟩⟩
    exact P.prop_of_iso (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
      (hasFiniteExtensionByZeroPresentation_cokernel.{u₁, v₁, w, t} S R hEnough hqc f hF hG)
  have : P.IsClosedUnderExtensions := ⟨fun {E} hE h₁ h₃ =>
    hasFiniteExtensionByZeroPresentation_of_shortExact.{u₁, v₁, w, t}
      S R hEnough hqc hqs E hE h₁ h₃⟩
  have : P.IsClosedUnderKernels :=
    isClosedUnderKernels_of_presentations P
      (I := Σ n : ℕ, { U : Fin n → C // ∀ i, U i ∈ S.objects })
      (fun a => ∐ fun i => extensionByZeroUnit.{u₁, v₁, w, t} R (a.2.1 i))
      (fun a => hasFiniteExtensionByZeroPresentation_coproduct.{u₁, v₁, w, t} S R a.2.1 a.2.2)
      (fun a b f => hKernel b.1 a.1 b.2.1 a.2.1 b.2.2 a.2.2 f)
      (fun _ ⟨n, m, U, V, hU, hV, f, he⟩ => ⟨⟨m, V, hV⟩, ⟨n, U, hU⟩, f, he⟩)
  exact { }

end Presentation

end Stacks.SheafOfModules

end
