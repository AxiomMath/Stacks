module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation

/-!
# The closure theory of coherent modules, in the vocabulary the scheme-level results use

Coherence of a sheaf of modules on a ringed space is declared twice on this branch, as two
distinct constants with literally the same two fields:

* `_root_.SheafOfModules.IsCoherent` (Stacks Tag 01BW), which is the one
  every statement about `X.Modules` for a scheme `X` uses, and the one [Stacks, Tag 02O5] is
  stated with;
* `Stacks.SheafOfModules.IsCoherent`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`), which carries the whole
  closure theory of [Stacks, Tag 01BY] — kernels, cokernels, extensions, finite direct sums,
  and locality on the base.

Because the two are different constants, none of that closure theory is usable by any of the
scheme-level results, and several files of the library are blocked by its absence. This file
removes that obstruction: it transports the predicate both ways and then restates every closure
statement of [Stacks, Tag 01BY] for the first constant.

Nothing here is new mathematics; the point is that the restatements are what the scheme-level
dévissage of [Stacks, Tag 02O5] consumes, and they cannot be written down without the transport.

## Main results

* `Stacks.AlgebraicGeometry.ProperMapping.isCoherent_iff`: the two coherence predicates agree.
* `Stacks.AlgebraicGeometry.ProperMapping.isCoherent_kernel`,
  `isCoherent_cokernel`, `isCoherent_X₂_of_shortExact`, `isCoherent_X₃_of_shortExact`,
  `isCoherent_image`: [Stacks, Tag 01BY] parts (3) and (4) — coherent modules are closed under
  kernels, cokernels, images and extensions.
* `Stacks.AlgebraicGeometry.ProperMapping.isCoherent_sigma`: a finite direct sum of coherent
  modules is coherent.
* `Stacks.AlgebraicGeometry.ProperMapping.isCoherent_of_coversTop` and
  `isCoherent_iff_isCoherentOn_of_coversTop`: coherence is local on the base.

## Implementation notes

**Every occurrence of the predicate is written `_root_.SheafOfModules.IsCoherent`, and that is
not cosmetic.** These declarations live in the `Stacks.` namespace, where the unqualified name
`SheafOfModules.IsCoherent` and the dot notation `M.IsCoherent` both resolve to
`Stacks.SheafOfModules.IsCoherent`, because resolution relative to the enclosing namespace wins
over the root. Writing the predicate unqualified here silently turns every statement below into
a tautology or a duplicate of an existing lemma, with no error anywhere. Any further work in
this area must qualify it.

The two transports are *not* declared as instances. Declaring either one would make instance
search cross between the two constants silently, and declaring both would loop; a consumer that
wants the crossing asks for it by name. Inside the proofs below the crossing is introduced with
`have`, which puts it in the local instance context for exactly one statement.

`isCoherent_cokernel` is proved the way
`Stacks.SheafOfModules.coherentModules_isClosedUnderCokernels` is, rather than by invoking that
instance: `Abelian.image φ` is by definition `kernel (cokernel.π φ)`, so it is simultaneously a
finite type quotient of `M` — hence a coherent submodule of `N` by [Stacks, Tag 01BY] (1) — and
the first term of `ShortComplex.kernelSequence (cokernel.π φ)`, whose third term is the
cokernel.

Everything is equi-universe, `X : Type u` with `RingCat.{u}`-valued structure sheaf and
`SheafOfModules.{u}`, because both coherence predicates are declared that way.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace SheafOfModules

universe u

namespace Stacks.AlgebraicGeometry.ProperMapping

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-! ### The two coherence predicates agree -/

/-- The coherence predicate of Stacks Tag 01BW implies the one of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`: the two classes have the same two
fields. -/
theorem stacksIsCoherent {M : SheafOfModules.{u} R}
    (h : _root_.SheafOfModules.IsCoherent M) : Stacks.SheafOfModules.IsCoherent M :=
  ⟨h.isFiniteType, h.kernel_isFiniteType⟩

/-- The coherence predicate of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean` implies the one of
Stacks Tag 01BW: the two classes have the same two fields. -/
theorem isCoherent_of_stacks {M : SheafOfModules.{u} R}
    (h : Stacks.SheafOfModules.IsCoherent M) : _root_.SheafOfModules.IsCoherent M :=
  ⟨h.isFiniteType, h.kernel_isFiniteType⟩

/-- **The two coherence predicates on this branch are the same condition.** Both say that the
module is of finite type and that over every open the kernel of every map from a finite free
module into its restriction is of finite type. -/
theorem isCoherent_iff (M : SheafOfModules.{u} R) :
    _root_.SheafOfModules.IsCoherent M ↔ Stacks.SheafOfModules.IsCoherent M :=
  ⟨stacksIsCoherent, isCoherent_of_stacks⟩

/-! ### Kernels, images, cokernels and extensions -/

/-- **Stacks Project, Tag 01BY (2).** The kernel of a morphism from a module of finite type to a
coherent module is of finite type. -/
theorem isFiniteType_kernel_of_isCoherent {M N : SheafOfModules.{u} R} [M.IsFiniteType]
    (hN : _root_.SheafOfModules.IsCoherent N) (φ : M ⟶ N) : (kernel φ).IsFiniteType :=
  have := stacksIsCoherent hN
  Stacks.SheafOfModules.isFiniteType_kernel_of_isCoherent φ

/-- **Stacks Project, Tag 01BY (3), kernels.** The kernel of a morphism of coherent modules is
coherent. -/
theorem isCoherent_kernel {M N : SheafOfModules.{u} R}
    (hM : _root_.SheafOfModules.IsCoherent M) (hN : _root_.SheafOfModules.IsCoherent N)
    (φ : M ⟶ N) : _root_.SheafOfModules.IsCoherent (kernel φ) :=
  have := stacksIsCoherent hM
  have := stacksIsCoherent hN
  isCoherent_of_stacks (Stacks.SheafOfModules.isCoherent_kernel φ)

/-- **Stacks Project, Tag 01BY (4).** The middle term of a short exact sequence of modules whose
outer terms are coherent is coherent. -/
theorem isCoherent_X₂_of_shortExact {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact)
    (h₁ : _root_.SheafOfModules.IsCoherent S.X₁) (h₃ : _root_.SheafOfModules.IsCoherent S.X₃) :
    _root_.SheafOfModules.IsCoherent S.X₂ :=
  isCoherent_of_stacks (Stacks.SheafOfModules.isCoherent_X₂_of_shortExact hS
    (stacksIsCoherent h₁) (stacksIsCoherent h₃))

/-- **Stacks Project, Tag 01BY (3), cokernels.** The third term of a short exact sequence of
modules whose first two terms are coherent is coherent. -/
theorem isCoherent_X₃_of_shortExact {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact)
    (h₁ : _root_.SheafOfModules.IsCoherent S.X₁) (h₂ : _root_.SheafOfModules.IsCoherent S.X₂) :
    _root_.SheafOfModules.IsCoherent S.X₃ :=
  isCoherent_of_stacks (Stacks.SheafOfModules.isCoherent_X₃_of_shortExact hS
    (stacksIsCoherent h₁) (stacksIsCoherent h₂))

/-- **The image of a morphism of coherent modules is coherent.** It is a quotient of the source,
hence of finite type, and a submodule of the target, so [Stacks, Tag 01BY] (1) applies. -/
theorem isCoherent_image {M N : SheafOfModules.{u} R}
    (hM : _root_.SheafOfModules.IsCoherent M) (hN : _root_.SheafOfModules.IsCoherent N)
    (φ : M ⟶ N) : _root_.SheafOfModules.IsCoherent (Abelian.image φ) :=
  have := stacksIsCoherent hM
  have := stacksIsCoherent hN
  have : (Abelian.image φ).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_epi'.{u} (Abelian.factorThruImage φ)
  isCoherent_of_stacks (Stacks.SheafOfModules.isCoherent_of_mono (Abelian.image.ι φ))

/-- **Stacks Project, Tag 01BY (3), cokernels.** The cokernel of a morphism of coherent modules
is coherent: the image is coherent, and the cokernel is the third term of the short exact
sequence exhibiting the image as the kernel of the cokernel projection. -/
theorem isCoherent_cokernel {M N : SheafOfModules.{u} R}
    (hM : _root_.SheafOfModules.IsCoherent M) (hN : _root_.SheafOfModules.IsCoherent N)
    (φ : M ⟶ N) : _root_.SheafOfModules.IsCoherent (cokernel φ) :=
  have hse : (ShortComplex.kernelSequence (cokernel.π φ)).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact _
      mono_f := inferInstance
      epi_g := inferInstanceAs (Epi (cokernel.π φ)) }
  isCoherent_X₃_of_shortExact hse (isCoherent_image hM hN φ) hN

/-! ### Finite direct sums -/

/-- **A finite direct sum of coherent modules is coherent.** -/
theorem isCoherent_sigma {J : Type*} [Finite J] (M : J → SheafOfModules.{u} R)
    [HasCoproduct M] (hM : ∀ j, _root_.SheafOfModules.IsCoherent (M j)) :
    _root_.SheafOfModules.IsCoherent (∐ M) :=
  isCoherent_of_stacks
    (Stacks.SheafOfModules.isCoherent_sigma M fun j => stacksIsCoherent (hM j))

/-! ### Coherence is local on the base -/

/-- Coherence of a module gives the local condition
`Stacks.SheafOfModules.IsCoherentOn` on every open. -/
theorem isCoherentOn_of_isCoherent (M : SheafOfModules.{u} R)
    (hM : _root_.SheafOfModules.IsCoherent M) (W : Opens X) :
    Stacks.SheafOfModules.IsCoherentOn M W :=
  have := stacksIsCoherent hM
  Stacks.SheafOfModules.isCoherentOn_of_isCoherent M W

/-- **Coherence is local on the base.** A module that is coherent on each member of a family of
opens covering the space is coherent. This is the step "the problem is local on `S`" that opens
the proof of [Stacks, Tag 02O5]. -/
theorem isCoherent_of_coversTop (M : SheafOfModules.{u} R) {I : Type u} (V : I → Opens X)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (hM : ∀ i, Stacks.SheafOfModules.IsCoherentOn M (V i)) :
    _root_.SheafOfModules.IsCoherent M :=
  isCoherent_of_stacks (Stacks.SheafOfModules.isCoherent_of_coversTop M V hV hM)

/-- Coherence is equivalent to coherence on each member of a covering family of opens: the local
form loses nothing. -/
theorem isCoherent_iff_isCoherentOn_of_coversTop (M : SheafOfModules.{u} R) {I : Type u}
    (V : I → Opens X) (hV : (Opens.grothendieckTopology X).CoversTop V) :
    _root_.SheafOfModules.IsCoherent M ↔ ∀ i, Stacks.SheafOfModules.IsCoherentOn M (V i) :=
  ⟨fun h i => isCoherentOn_of_isCoherent M h (V i), isCoherent_of_coversTop M V hV⟩

end Stacks.AlgebraicGeometry.ProperMapping

end
