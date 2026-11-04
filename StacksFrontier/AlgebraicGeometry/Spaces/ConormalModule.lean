module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal module of a closed subspace of an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `Z` be
a closed subspace of `X`, with inclusion `i : Z ⟶ X`.  Let `𝓘 ⊆ 𝒪_X` be the defining ideal
sheaf of `Z` on the small étale site of `X`, that is
`AlgebraicGeometry.Space.definingIdealSheaf`, the sheaf of ideals of Stacks 03MB.  The
**conormal module** of `Z` in `X` is the `𝒪_Z`-module `i^*𝓘`, the inverse image of `𝓘` along the
inclusion.

This is **1 of the 3 parts** of Stacks 04CN: the construction of the conormal module, and only
for a *closed* immersion.  Quasi-coherence, the second part, is **not** established in this
file, but it is established unconditionally in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersion.lean`, as
`AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalModule`; that file cannot be imported
here, since it imports this one.  The third part, the canonical identification with `𝓘/𝓘²`, is
not established in this file either; it is
`AlgebraicGeometry.Space.conormalIdealQuotientIso` of the same file.  The "What is not proved"
section below gives both together with the restriction to the closed case, and names the section
of Stacks 76.5 that the construction follows.

## Main definitions

* `AlgebraicGeometry.Space.conormalModule`: **Stacks 04CN, part 1 of 3**, the conormal module
  `𝒞_{Z/X}` of a closed subspace `Z` of an algebraic space `X`, as the inverse image along the
  inclusion of the defining ideal sheaf of `Z`.

## Main results

* `AlgebraicGeometry.Space.conormalModule_eq`: the defining equation of the conormal module,
  available to consumers as a rewrite without unfolding the definition.
* `AlgebraicGeometry.Space.nonempty_closedSubspaces`: `X` itself is a closed subspace of `X`, so
  the family of arguments of `conormalModule` is not empty.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalModule_of_h03DO`: the conormal module is
  quasi-coherent, **given Stacks 03DO, part (6)** for the inclusion as a named hypothesis.  The
  hypothesis is discharged, and the conclusion stated unconditionally, by
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalModule` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersion.lean`.

## Implementation notes

**Why `i^*𝓘` is the module the source describes.**  Stacks 76.5 does not construct the conormal
module as `i^*𝓘`.  It forms the short exact sequence `0 → 𝓘² → 𝓘 → 𝓘/𝓘² → 0` of `𝒪_X`-modules,
observes that `𝓘/𝓘²` is annihilated by `𝓘`, and takes the `𝒪_Z`-module corresponding to it under
the equivalence between `𝒪_Z`-modules and `𝒪_X`-modules annihilated by `𝓘`.  That `𝒪_Z`-module is
`i^*𝓘`, because `i_*i^*𝓘 = 𝓘 ⊗_{𝒪_X} 𝒪_X/𝓘 = 𝓘/𝓘²`; the identification is standard and is **not
formalized here**, since neither the ideal square `𝓘²` nor the equivalence of Stacks 04CJ is
available in this development for the small étale site of an algebraic space.  Taking `i^*𝓘` as
the realization is the convention this repository already follows one category down, at
`Stacks.Conormal.conormalSheaf` of
`StacksFrontier/AlgebraicGeometry/ConormalComparison/IdealSheafComparison.lean`, which carries
`@[stacks 01R2 "construction"]` for the identical construction on schemes and defers the
identification with `I/I²` to Stacks 01R3, part (2).  The part string on the definition below
records the same split.

**Why a closed subspace and not a morphism.**  Stacks 04CN is stated for an immersion `i : Z ⟶ X`
of algebraic spaces.  Every statement of Stacks 03MB in this library — the defining
ideal `AlgebraicGeometry.Space.definingIdealAt`, the ideal sheaf
`AlgebraicGeometry.Space.definingIdealSheaf`, its quasi-coherence, and the order isomorphism —
takes the subspace `Z : AlgebraicGeometry.Space.ClosedSubspaces B S hS X.1` rather than a
morphism with a closed-immersion hypothesis, and the inclusion is read as a morphism of algebraic
spaces by `AlgebraicGeometry.Space.subspaceInclusion`.  The definition below is in that shape, so
that the ideal sheaf and its properties apply to it with no bridge.  The three consumers of this
definition in the source — Stacks 04CO, 04CP and 04G2, part (1) — are all expressible in it: the
base change of a closed subspace along an étale chart is a closed subspace of the chart, and a
commutative square sending one subspace into another induces the morphism of subspaces that the
functoriality statement pulls back along.

**Why a `def` and not an `abbrev`.**  A convention, with no mathematical content and no
performance cost.  The scheme-level `Stacks.Conormal.conormalSheaf` is a `noncomputable abbrev`, for
a reason its own notes give: declarations stated before it existed, against the written-out
pullback, are
statements about it at reducible transparency.  That reason does not apply to a new definition
with no prior consumers, so the plain `def` is used here.  Nothing is lost by it: a `def` unfolds
at default transparency, which is why `AlgebraicGeometry.Space.conormalModule_eq` below is closed
by `rfl`, and that equation gives consumers the unfolding by name in any case.  With `abbrev` in
place of `def` this file elaborates in the same time.

## What is not proved

* **Part 2, quasi-coherence, is not proved in *this file*, but it is proved.**  Stacks 04CN
  asserts that `𝒞_{Z/X}` is a *quasi-coherent* `𝒪_Z`-module.  The ideal sheaf is quasi-coherent
  unconditionally (`AlgebraicGeometry.Space.isQuasicoherentOnSite_definingIdealSheaf`), so all
  that is needed is that the inverse image of a quasi-coherent module preserves
  quasi-coherence.  For a morphism of algebraic spaces that is Stacks 03GA, and it holds for an
  arbitrary morphism and an arbitrary quasi-coherent module:
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackQuasicoherentFromChartDiagrams.lean`.
  Applying it gives `AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalModule` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersion.lean`, and the 04CN attribute for
  this part sits there on its immersion form
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalModuleOfImmersion`.  That file imports
  this one, so the result cannot be stated here; this file keeps only the weaker
  hypothesis-carrying form
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalModule_of_h03DO`, which does **not**
  carry a `@[stacks]` attribute.

  The quasi-coherent clause of Stacks 03DO is carried, for a
  morphism of ringed *sites* presented by a left exact continuous functor, by
  `Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_of_quasicoherentData`;
  and the comparison of the two pullbacks is
  `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, which is what
  `isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite` uses.
* **Part 3, the canonical identification with `𝓘/𝓘²`, is not proved in this file**, for the
  reason given in the implementation notes above; it is
  `AlgebraicGeometry.Space.conormalIdealQuotientIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersion.lean`.
* **Part 1 is covered only in the closed case — but not for want of the open subspace.**  An
  immersion is reduced to a closed immersion into `X ∖ ∂Z` in Stacks 76.5, and that open
  subspace and the factorization through it are both available in this development:
  `AlgebraicGeometry.Space.boundarySubspace`, `AlgebraicGeometry.Space.boundaryComplement` and
  `AlgebraicGeometry.Space.exists_isClosedImmersion_comp_ι_boundaryComplement` at
  `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Immersions.lean:669`, `:374` and `:754`, the
  last of them carrying `@[stacks 04CE]`; the reduced induced subspace on a locally closed set
  of points carries `@[stacks 06EC]` at `:544` of the same file.  The factorization is also
  available free of choice, as the morphism of algebraic spaces
  `AlgebraicGeometry.Space.immersionClosedFactorization` into
  `AlgebraicGeometry.Space.immersionAmbient`, at
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebra.lean:258` and `:250`.

  What keeps the definition below in the closed case is layering and shape.  Layering:
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebra.lean`, which holds that choice-free
  factorization, imports *this* file, so the immersion case cannot be stated here.  Shape:
  `conormalModule` takes a closed subspace and returns a module on that subspace's own functor,
  whereas Stacks 04CN asks for an `𝒪_Z`-module on `Z` itself; the immersion-level object is the
  inverse image along `immersionClosedFactorization` of the defining ideal sheaf of
  `Subfunctor.range (AlgebraicGeometry.Space.boundaryComplementLift …)`, and so must live
  downstream of `ConormalAlgebra.lean`.  It lives there:
  `AlgebraicGeometry.Space.conormalModuleOfImmersion` at
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebra.lean:428` carries
  `@[stacks 04CN "construction as the pullback of the ideal sheaf, via the closed
  factorisation"]`, and
  `AlgebraicGeometry.Space.conormalModuleOfImmersion_eq_conormalAlgebraOfImmersion_piece_one`
  at `:452` identifies it with the degree-one piece of
  `AlgebraicGeometry.Space.conormalAlgebraOfImmersion` (`:271`, carrying `@[stacks 09RN]`), so
  the two are one notion rather than two.  That identification does *not* go through
  `AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf`
  (`StacksFrontier/AlgebraicGeometry/Spaces/MorphismKernelIdeal.lean:109`), which speaks only of a
  bundled subspace inclusion: it goes through the scheme-theoretic image, by Stacks 082Z at
  `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/QuasiCompactImageIdeal.lean:126` and the
  quasi-compactness of a closed immersion (Stacks 04CG).  The part string below records the
  closed case that *this* definition covers; quasi-coherence is open in both cases, for the
  reason given above.

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Every algebraic space has a closed subspace**, namely itself: the top subfunctor is the
infimum of the empty family of subfunctors, and an infimum of closed subspaces is a closed
subspace.

This is the inhabitation witness for the construction below: `conormalModule` is a construction
on a family of arguments that is not empty, and `𝒞_{X/X}` is a legitimate instance of it. -/
theorem nonempty_closedSubspaces (X : AlgebraicSpaces B S hS) :
    Nonempty (ClosedSubspaces B S hS X.1) := by
  refine ⟨⟨⊤, ?_⟩⟩
  rw [← sInf_empty]
  exact isClosedSubspace_sInf B S hS X.2 ∅ fun _ h ↦ h.elim

/-- **Stacks 04CN for a closed immersion.**  The conormal module `𝒞_{Z/X}` of a closed subspace
`Z` of an algebraic space `X`: the inverse image along the inclusion `i : Z ⟶ X` of the defining
ideal sheaf `𝓘_Z ⊆ 𝒪_X` of Stacks 03MB.

Stacks 76.5 describes this `𝒪_Z`-module as `𝓘/𝓘²`, which is `i_*i^*𝓘`; the implementation notes
of this file record why `i^*𝓘` is that module and that the identification is not formalized
here, and that this is the convention of the scheme-level `Stacks.Conormal.conormalSheaf`. -/
@[stacks 04CN "construction as the pullback of the ideal sheaf, closed immersion",
  sga "6 0 2.1" "more general"]
noncomputable def conormalModule (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    Modules.{u, u} B S hS Z.1.toFunctor Z.2.1 :=
  (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
    (definingIdealSheaf B S hS X Z).toSheafOfModules

/-- The conormal module of a closed subspace is the inverse image of its defining ideal sheaf
along the inclusion.  This is the defining equation, stated so that consumers may rewrite with
it rather than unfold the definition; see the implementation notes of this file for why the
definition is a plain `def`. -/
theorem conormalModule_eq (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1) :
    conormalModule B S hS X Z =
      (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules :=
  rfl

/-- **The quasi-coherence clause of Stacks 04CN, given Stacks 03DO, part (6).**  The defining
ideal sheaf of a closed subspace is quasi-coherent on the small étale site unconditionally, so
the conormal module is quasi-coherent as soon as the inverse image along the inclusion preserves
quasi-coherence.  That preservation is Stacks 03DO, part (6) for a morphism of ringed topoi, and
is carried here as the hypothesis `h03DO` because no statement in this development establishes
it; the "What is not proved" section of the module documentation records what it would take.

No `@[stacks]` attribute is claimed: a hypothesis-carrying form of a tag's clause must not carry
the bare tag. -/
theorem isQuasicoherentOnSite_conormalModule_of_h03DO (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1)
    (h03DO : ∀ M : Modules.{u, u} B S hS X.1 X.2, M.IsQuasicoherentOnSite →
      ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj M).IsQuasicoherentOnSite) :
    (conormalModule B S hS X Z).IsQuasicoherentOnSite :=
  h03DO _ (isQuasicoherentOnSite_definingIdealSheaf B S hS X Z)

end AlgebraicGeometry.Space

end
