module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.AlgebraicGeometry.Cohomology.SectionsSurjective

/-!
# Sections are left exact

Let `0 ⟶ F ⟶ G ⟶ H ⟶ 0` be a short exact sequence of `𝒪_X`-modules on a scheme `X` and let `U`
be an open subscheme. Taking sections over `U` leaves the sequence

`0 ⟶ Γ(U, F) ⟶ Γ(U, G) ⟶ Γ(U, H)`

exact: a section of `F` is determined by its image in `G`, and a section of `G` killed by the map
to `H` comes from `F`. Unlike the surjectivity of `Γ(U, G) ⟶ Γ(U, H)`, which needs the vanishing
of `H¹(U, F)` (`Stacks.Cohomology.surjective_sections_of_isZero_firstCohomology`), these two
statements hold with no cohomological hypothesis whatever: they are the left exactness of
`Γ(U, -)`, which is `Stacks.Cohomology.preservesFiniteLimits_sectionsFunctor`.

The mechanism is the same in the categorical generality in which it holds. A short exact sequence
presents `F ⟶ G` as a kernel of `G ⟶ H` (`CategoryTheory.ShortComplex.ShortExact.fIsKernel`); a
functor preserving finite limits carries that kernel fork to a kernel fork
(`CategoryTheory.Limits.KernelFork.mapIsLimit`); and a morphism that is a kernel is a
monomorphism with the expected image
(`CategoryTheory.ShortComplex.exact_of_f_is_kernel`). No injective resolution and no long exact
sequence are involved, so none of the hypotheses that the derived functor needs appear.

The pair of statements is what identifies the kernel of a restriction map between the
infinitesimal thickenings of a divisor with the global sections of a twisted ideal sheaf: the
short exact sequence of [Stacks, Tag 0C4T] has that twisted sheaf as its kernel, and left
exactness turns it into an isomorphism onto the kernel of the restriction. That identification is
the graded piece of the formal neighbourhood of an exceptional curve, which is what
[Stacks, Tag 0C2K] computes.

## Main results

* `Stacks.Cohomology.mono_map_f_of_shortExact` and `Stacks.Cohomology.exact_map_of_shortExact` —
  a functor preserving finite limits carries a short exact sequence to one that is exact at its
  middle term and monomorphic on the left.
* `Stacks.Cohomology.injective_sections_of_shortExact` — sections of the kernel inject into
  sections of the middle term.
* `Stacks.Cohomology.exists_sections_of_sections_eq_zero` — a section of the middle term whose
  image vanishes comes from the kernel.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v v' u u'

namespace Stacks.Cohomology

/-! ### The categorical statement -/

variable {B : Type u} {D : Type u'} [Category.{v} B] [Category.{v'} D] [Abelian B] [Abelian D]
  (Q : B ⥤ D) [Q.Additive] [PreservesFiniteLimits Q]

/-- **A functor preserving finite limits is monomorphic on the kernel of a short exact
sequence.** For `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` short exact, `Q X₁ ⟶ Q X₂` is a monomorphism.

The short exact sequence presents `S.f` as a kernel of `S.g`, and a finite-limit-preserving
functor carries that kernel fork to a kernel fork, whose inclusion is a monomorphism. -/
theorem mono_map_f_of_shortExact {S : ShortComplex B} (hS : S.ShortExact) : Mono (Q.map S.f) :=
  mono_of_isLimit_fork (KernelFork.mapIsLimit _ hS.fIsKernel Q)

/-- **A functor preserving finite limits carries a short exact sequence to one exact in the
middle.** For `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` short exact, the image complex
`Q X₁ ⟶ Q X₂ ⟶ Q X₃` is exact at `Q X₂`. Nothing is claimed about `Q X₂ ⟶ Q X₃` being
epimorphic; that is where the first derived functor of `Q` enters, and
`Stacks.Cohomology.epi_map_of_isZero_rightDerived_one` is the statement which needs it. -/
theorem exact_map_of_shortExact {S : ShortComplex B} (hS : S.ShortExact) : (S.map Q).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ hS.fIsKernel Q)

/-! ### Sections of modules on a scheme -/

/-- **Sections of the kernel of a short exact sequence inject into sections of the middle
term.** For a short exact sequence `0 ⟶ F ⟶ G ⟶ H ⟶ 0` of `𝒪_X`-modules, a section of `F` over
`U` is determined by its image in `G`. -/
theorem injective_sections_of_shortExact (X : Scheme.{u}) (U : X.Opens)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    Function.Injective fun m : Γ(S.X₁, U) => S.f.app U m :=
  (ModuleCat.mono_iff_injective _).1 (mono_map_f_of_shortExact (sectionsFunctor X U) hS)

/-- **A section killed by the quotient map comes from the kernel.** For a short exact sequence
`0 ⟶ F ⟶ G ⟶ H ⟶ 0` of `𝒪_X`-modules, a section of `G` over `U` whose image in `H` vanishes is
the image of a section of `F`. -/
theorem exists_sections_of_sections_eq_zero (X : Scheme.{u}) (U : X.Opens)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (m : Γ(S.X₂, U))
    (hm : S.g.app U m = 0) :
    ∃ a : Γ(S.X₁, U), S.f.app U a = m :=
  (ShortComplex.moduleCat_exact_iff _).1
    (exact_map_of_shortExact (sectionsFunctor X U) hS) m hm

end Stacks.Cohomology

end
