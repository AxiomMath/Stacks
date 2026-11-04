module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsTriangle
import StacksCore.Tactic.StacksAttribute

/-!
# Two inputs to the vanishing of the composite of the conormal sequence

Let `B` be an algebraic space over a scheme `S`, let `Z` be a closed subspace of an algebraic
space `X` over `B` with inclusion `i : Z ⟶ X`, and let `b : X ⟶ B` be the structure morphism.
Stacks 05ZA attaches to this datum the sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0
```
of sheaves of `𝒪_Z`-modules on the small étale site of `Z`, whose first arrow
`AlgebraicGeometry.Space.conormalSequenceFirstMap` is built in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentials.lean` and whose second arrow
is the comparison map `AlgebraicGeometry.Space.pullbackDifferentialsMap` of Stacks 04CX.

Two clauses of that tag were open when this file was written: that the composite of the two
arrows is zero, and exactness at the middle term.  **Neither is proved here, and nothing below
should be read as asserting either.**  What this file contributes are two of the statements the
first of those clauses rests on, each of which is unconditional and useful on its own; the clause
itself is now proved, in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceComplex.lean`, which consumes both of
them, and, for an arbitrary sheaf of ideals in place of the defining ideal sheaf of a closed
subspace, in `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceCompositeZero.lean`, which
consumes both as well.

## The reduction, and what this file supplies

Transposed along the adjunction `i^* ⊣ i_*` of Stacks 03LU the composite-is-zero clause says
that the adjoint form `AlgebraicGeometry.Space.conormalSequenceIdealDifferential` of the first
arrow, `𝓘 ⟶ i_*i^*Ω_{X/B}`, followed by the direct image of the second arrow, is the transpose of
the zero morphism.  That reduction needs three things.

1. On a local section `a` of the defining ideal sheaf `𝓘` of `Z`, the value of the composite is
   `d_{Z/B}(i♯ a)`, and `i♯ a = 0` because `𝓘` is by definition the kernel of `i♯`
   (`AlgebraicGeometry.Space.mem_definingIdealAt_iff`).  This is
   `AlgebraicGeometry.Space.pushforwardUniversalDerivation_d_eq_zero` below, proved for an
   arbitrary commutative square.  It is the only non-formal step of the clause.
2. The transpose of the zero morphism vanishes on every local section.  This is
   `AlgebraicGeometry.Space.modulePullbackAdjunction_homEquiv_zero_val_app_apply` below, proved
   from the fact that the direct image of modules is a right adjoint and therefore annihilates
   the zero morphism.
3. The identification of `AlgebraicGeometry.Space.conormalSequenceUnitDerivation` with the
   universal derivation `d_{X/B}` followed by the unit of the adjunction — on a local section,
   `D(a) = η(d_{X/B}(a))` — together with the naturality of the transposition in its right
   argument.  The first is the defining equation of
   `AlgebraicGeometry.Space.conormalSequenceUnitDerivation` and the second is
   `CategoryTheory.Adjunction.homEquiv_naturality_right_symm`.  Both are supplied in
   `ConormalSequenceComplex.lean`, as
   `AlgebraicGeometry.Space.conormalSequenceUnitDerivation_d` and by applying that naturality at
   explicit arguments; neither is proved here.

## Main results

* `AlgebraicGeometry.Space.pushforwardUniversalDerivation_d_eq_zero`: for a commutative square
  with top edge `f : X' ⟶ X` and left edge `p' : X' ⟶ Y'`, the `Y`-derivation
  `AlgebraicGeometry.Space.pushforwardUniversalDerivation` of Stacks 04CX, which is
  `f_*d_{X'/Y'} ∘ f♯`, annihilates every local section of `𝒪_X` annihilated by the direct-image
  form `f♯ : 𝒪_X ⟶ f_*𝒪_{X'}` of the structure map.  Applied at the inclusion of a closed
  subspace and the defining ideal sheaf of Stacks 03MB this is the vanishing that the
  composite-is-zero clause of Stacks 05ZA asserts, read through the characterizing property of
  the comparison map.
* `AlgebraicGeometry.Space.modulePullbackAdjunction_homEquiv_zero_val_app_apply`: the transpose
  along `f^* ⊣ f_*` of the zero morphism is zero on local sections.

No `@[stacks]` attribute is claimed in this file.  Neither statement is a clause of a tag: the
first is a property of the derivation of Stacks 04CX that the source does not state, and the
second is a fact about the adjunction of Stacks 03LU.

## Implementation notes

**Why the vanishing is proved without a formula for `f_*d_{X'/Y'}`.**  Sections over an étale
chart of a direct image are not described by a formula in this development — the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsMap.lean` record why — so the
proof uses only that `AlgebraicGeometry.Space.pushforwardUniversalDerivation` is, by
construction, the composite of `f♯` with a morphism of sheaves of sets, and that its value map on
sections is additive.  A section that `f♯` kills therefore has the same image as the zero
section, and the derivation sends the zero section to zero.

**The import surface** is that of `ConormalSequenceDifferentials.lean` together with
`RelativeDifferentialsTriangle.lean`.  Those two files each record that their union was expected
to be too large for one process; it is not — the file that already imports both,
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceFormallyUnramified.lean`, compiles, and so
does this one.  What is costly at these concrete ringed topoi is elaborating statements about
derivations whose coefficient module is written through the composite functor `i^* ⋙ i_*`, not
the size of the environment.

## What is not proved

* **The composite of the two arrows of Stacks 05ZA is not shown to be zero here**, but it is no
  longer open: it is
  `AlgebraicGeometry.Space.conormalSequenceFirstMap_comp_pullbackDifferentialsMap` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceComplex.lean`, which is where step 3 of
  the reduction above is carried out.  Both halves of that step are cheap once the definitions
  are delta-reduced *syntactically* before the lemma is applied: `unfold` on
  `AlgebraicGeometry.Space.conormalSequenceUnitDerivation` followed by reflexivity gives
  `D(a) = η(d_{X/B}(a))`, and
  `CategoryTheory.Adjunction.homEquiv_naturality_right_symm` applied at explicit arguments gives
  the naturality.  What does not fit the default heartbeat budget is leaving either step to
  unification against a goal that mentions the definition, which is what an earlier measurement
  recorded as the obstruction; that measurement did not distinguish the two, and the conclusion
  it drew — that the kernel cannot decide
  `((i^* ⋙ i_*).obj Ω_{X/B}).val = (i_*(i^*Ω_{X/B})).val` inside the type of a derivation at all
  — is false: it is decided when the equation is stated with the coefficient module of
  `AlgebraicGeometry.Space.conormalSequenceUnitDerivation` on the left.  No compiler option is
  raised anywhere.
* **The reduction is carried out a second time**, for an arbitrary sheaf of ideals in place
  of the defining ideal sheaf of a closed subspace, in
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceCompositeZero.lean`, which consumes both
  statements of this file and instantiates the result at the tag's own datum.  There step 3 is
  arranged as follows:
  * `CategoryTheory.Adjunction.homEquiv_naturality_right_symm` at these objects goes through at
    the default budget once the transposition is named rather than written out
    (`AlgebraicGeometry.Space.submoduleTranspose`) and the lemma's arguments are left to
    unification with the goal.
  * The identity `D(a) = η(d_{X/B}(a))` for `D = conormalSequenceUnitDerivation` is an instance
    of `PresheafOfModules.Derivation.postcomp_d_apply`, and **at a concrete inclusion of a closed
    subspace that instance does not type-check within the default budget**: the kernel has to
    decide `((i^* ⋙ i_*).obj Ω_{X/B}).val = (i_*(i^*Ω_{X/B})).val` underneath
    `PresheafOfModules.Derivation.d` applied to a section, which unfolds the ring presheaf of the
    modules and so the construction of the small étale ringed site.  With the morphism of
    algebraic spaces left a *variable* the same instance is free.  So the derivation is routed
    through `AlgebraicGeometry.Space.pullbackUnitDerivation`, which is that composite at a
    variable morphism, `AlgebraicGeometry.Space.conormalSequenceUnitDerivation` is defined as its
    value at the inclusion, and the consumer is given the derivation as a datum together with its
    defining equation — an equation of derivations at one and the same type, which `rfl` decides
    at no cost.  Nothing is forced and no compiler option is raised.
* **Exactness at the middle term is not proved and no step towards it is taken here.**  The
  source obtains the clause by étale localization to the case of schemes, Morphisms, Lemma 01UZ,
  through Stacks 04CU and 04CO.  Both inputs of that reduction do exist in this tree — the scheme
  case with the conormal sheaf at the left-hand end is
  `Stacks.ConormalSequenceRight.conormalShortComplex_exact` of
  `StacksFrontier/AlgebraicGeometry/ConormalSequenceRight/SchemeShortExact.lean`, and the comparison
  with the Zariski sheaf of differentials of a morphism of schemes of the site is
  `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean` — so what is
  missing is the comparison of the two first arrows and of the two conormal modules; see the
  *What is not proved* section of `ConormalSequenceDifferentials.lean`.
* **Exactness at the right term** is proved, but elsewhere:
  `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isLocallySurjective` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentialsEpi.lean`, and
  unconditionally for an immersion as
  `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isImmersion` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceEpiImmersion.lean`.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence of
  an immersion, whose composite-is-zero clause the first result below is the non-formal input to.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and the derivation it is built from.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the adjunction
  `f^* ⊣ f_*` for modules on the small étale ringed topoi.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  of a closed subspace as the kernel of the structure map.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the morphism of small
  étale ringed topoi and its structure map.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The derivation of Stacks 04CX kills the kernel of the structure map -/

section Vanishing

variable {X X' Y Y' : AlgebraicSpaces B S hS}

/-- **The `B`-derivation of Stacks 04CX kills whatever the structure map kills.**  For a
commutative square

```
  X' --f--> X
  |         |
  p'        p
  v         v
  Y' --q--> Y
```

of algebraic spaces, the `Y`-derivation `AlgebraicGeometry.Space.pushforwardUniversalDerivation`
of `𝒪_X` with values in `f_*Ω_{X'/Y'}`, which is `f_*d_{X'/Y'} ∘ f♯`, annihilates every local
section of `𝒪_X` that the direct-image form `f♯ : 𝒪_X ⟶ f_*𝒪_{X'}` of the structure map
annihilates.

At the inclusion `i : Z ⟶ X` of a closed subspace this applies to the sections of the defining
ideal sheaf of Stacks 03MB, which are exactly the sections `i♯` kills by
`AlgebraicGeometry.Space.mem_definingIdealAt_iff`; that is the vanishing asserted by the
composite-is-zero clause of Stacks 05ZA, read through the characterizing property
`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap` of the comparison map.  The clause itself is
not proved; see the "What is not proved" section of this file's module documentation.

No formula for the effect of `f_*d_{X'/Y'}` on a section is used, and none is available here: the
derivation is by construction the structure map followed by a morphism of sheaves of sets, so a
section that `f♯` kills has the same image under it as the zero section, and the derivation's
value map on sections is additive, so its value at the zero section is zero. -/
theorem pushforwardUniversalDerivation_d_eq_zero (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : ToType ((structureRingSheaf B S hS X).obj.obj U))
    (ht : ((structureSharp B S hS f).hom.app U).hom t = 0) :
    (pushforwardUniversalDerivation B S hS f p p' q hcomm).d t = 0 := by
  have h0 : ((structureSharp B S hS f).hom.app U).hom t =
      ((structureSharp B S hS f).hom.app U).hom 0 :=
    ht.trans (map_zero ((structureSharp B S hS f).hom.app U).hom).symm
  have key : ∀ s : ToType ((structureRingSheaf B S hS X).obj.obj U),
      (pushforwardUniversalDerivation B S hS f p p' q hcomm).d s =
        ((smallEtaleDirectImage B S hS f).map (universalDerivationHom B S hS p')).hom.app U
          (((structureSharp B S hS f).hom.app U).hom s) := fun _ ↦ rfl
  refine (key t).trans (Eq.trans (congrArg _ h0) ?_)
  exact (key 0).symm.trans (map_zero (pushforwardUniversalDerivation B S hS f p p' q hcomm).d)

end Vanishing

/-! ### The transpose of the zero morphism -/

section Transpose

variable {X X' : AlgebraicSpaces B S hS}

/-- **The transpose of the zero morphism is zero on local sections.**  For a morphism
`f : X' ⟶ X` of algebraic spaces, an `𝒪_X`-module `M` and an `𝒪_{X'}`-module `N`, the morphism
`M ⟶ f_*N` corresponding to the zero morphism `f^*M ⟶ N` under the adjunction `f^* ⊣ f_*` of
Stacks 03LU carries every local section of `M` to zero.

The transpose of a morphism is the unit of the adjunction followed by the direct image of that
morphism, and the direct image of modules annihilates the zero morphism, being a right adjoint.
The statement is made on sections because that is the form in which the right-hand side of the
transposed composite-is-zero clause of Stacks 05ZA is compared with the left-hand side; the zero
morphism out of a sheaf submodule of the structure sheaf is not available as a term at the
spelling in which that clause reads it. -/
theorem modulePullbackAdjunction_homEquiv_zero_val_app_apply (f : X' ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (N : Modules.{u, u} B S hS X'.1 X'.2)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : M.val.obj U) :
    (ModuleCat.Hom.hom
        ((((modulePullbackAdjunction B S hS f).homEquiv M N) 0).val.app U)) x = 0 := by
  have hz : (modulePushforward B S hS f).map
      (0 : (modulePullback B S hS f).obj M ⟶ N) = 0 := by
    have : (modulePushforward B S hS f).IsRightAdjoint :=
      (modulePullbackAdjunction B S hS f).isRightAdjoint
    exact Functor.map_zero _ _ _
  have hu := Adjunction.homEquiv_unit (modulePullbackAdjunction B S hS f) M N
    (0 : (modulePullback B S hS f).obj M ⟶ N)
  refine (congrArg (fun m ↦ (ModuleCat.Hom.hom ((SheafOfModules.Hom.val m).app U)) x)
    (hu.trans (congrArg (fun m ↦
      (modulePullbackAdjunction B S hS f).unit.app M ≫ m) hz))).trans ?_
  rfl

end Transpose

end AlgebraicGeometry.Space

end
