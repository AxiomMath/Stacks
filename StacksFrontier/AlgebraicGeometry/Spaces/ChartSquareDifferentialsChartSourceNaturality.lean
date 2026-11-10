module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartPullbackNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackJunctionBridge

/-!
# The chart-square comparison against [Stacks Project, Tag 03LU]'s composition law

`AlgebraicGeometry.Space.chartPullbackDifferentialsAssociatedIso` is the chart-square comparison
`AlgebraicGeometry.Space.chartSquareDifferentialsAssociatedIso` pulled back along a morphism `r`
of the big fppf site and followed by
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`.  A consumer passing from a
chart of the source to a *smaller* one has to push that composite past
`AlgebraicGeometry.Space.modulePullbackCompIso` — the comparison of [Stacks Project, Tag 03LU]
along a further morphism `ρ` in front.  That step is this file: it is
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_map`, the composition law
with the inverse image of an arbitrary morphism `ξ` in front, read at
`ξ = (chartSquareDifferentialsAssociatedIso …).hom`.

## Main results

* `AlgebraicGeometry.Space.chartSquareDifferentialsRepresentedHom`: the chart-square comparison's
  `hom`, **named at the spelling of the composition law**; its codomain is the represented
  associated module written as the comparison equivalence applied to
  `AlgebraicGeometry.SmallEtale.associatedModule`, not as
  `AlgebraicGeometry.Space.representedAssociatedModule`.
* `AlgebraicGeometry.Space.chartSquareDifferentialsRepresentedHom_eq`: it *is* that `hom`, by
  `rfl`.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_chartSquare`: **the
  composition law at the chart-square comparison.**

## Implementation notes

**Instantiating the composition law at the chart-square comparison is not a substitution.**
The natural claim — that the step is
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_map` instantiated at
`ξ := (chartSquareDifferentialsAssociatedIso …).hom`, with nothing to prove — is false as stated.
Written out at the chart's own spelling, the statement elaborates in under a second and the
instantiated law elaborates in under a second, and `exact`-ing the second against the first is a
`whnf` timeout at 200 000 heartbeats.  `apply`, a preceding `have`, pinning the implicit module,
and leaving every explicit argument to unification all give the same timeout.  Printing both
types with `pp.explicit` and diffing them shows why: they differ in *hidden arguments*, in two
places, and each difference is a definitional equality whose two sides the unifier will not
cross inside a term of this size.

*The first is the codomain of `ξ`.*  The chart-square comparison lands in
`(AlgebraicGeometry.Space.representedAssociatedModule … W (schemeSpace W).property).obj 𝓕`, while
the law quantifies over a `ξ` landing in
`(representedSmallEtaleModuleEquivalence … W).functor.obj ((SmallEtale.associatedModule …).obj
𝓕)`.  The two functors are equal by `rfl`
(`AlgebraicGeometry.Space.representedAssociatedModule_eq_comp`) and the two *objects* are
identified for free in a composite — but the identification has to be made where the term is
small.  Four routes fail: restating the law with `ξ` chart-spelled (maximum recursion
depth, in the *statement*), ascribing `ξ` inline in the statement, ascribing the law's `ξ`
argument in the proof, and ascribing a bound chart-spelled `ξ` in the proof.  What works is
naming the ascription: with `ξ` an opaque constant of exactly the law's type, the law's
conclusion is the statement on the nose.  That constant is
`AlgebraicGeometry.Space.chartSquareDifferentialsRepresentedHom`, and the precedent for keeping a
reconciliation of two spellings in a declaration of its own is
`AlgebraicGeometry.Space.representedSquareDerivation_restrictRelativeDerivation_schemeSpace`.

*The second is the scheme that the chart square's Zariski differentials live on.*  The law writes
the underlying morphism of schemes as `B.inclusion.map ·.left`, so
`CategoryTheory.Functor.obj` of `AlgebraicGeometry.Scheme.Modules.pullback` at it expects a module
on `B.inclusion.obj W.left`; written there without help,
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme …).map k)` comes out
with its implicit schemes at that spelling instead of at `(BigFppfOver.toScheme …).obj W`, which
is the law's.  Hence the two type ascriptions below, at exactly the two positions whose expected
type is stated through `B.inclusion`: they are redundant as mathematics and load-bearing as
elaboration, and removing either one restores the timeout.

*What the chart-level square still needs.*  Pasting this with the head square
`AlgebraicGeometry.Space.modulePullbackCompIso_headSquare` would give the compatibility of
`AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso` — and hence, by
`AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso_eq`, of
`AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso` — with a morphism of charts of the
source.  It does not yet, and the obstruction is not any of the ones recorded in this
neighbourhood.  Four observations, all in the library build:

* *The two spellings of one morphism of represented spaces can be crossed, at the isomorphism.*
  The implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartPullbackNaturality` record
  that `AlgebraicGeometry.Space.schemeSpaceMap` and
  `AlgebraicGeometry.Space.representedSpaceMap` cannot be reconciled underneath a
  `AlgebraicGeometry.Space.modulePullbackCompIso` projection, and at the *projection* that is
  confirmed: `(modulePullbackCompIso (schemeSpaceMap r) w).inv.app N
  = (modulePullbackCompIso (representedSpaceMap … r) w).inv.app N` by `rfl` is a `whnf` timeout
  even at an arbitrary `N`, because `CategoryTheory.Iso.inv` of an adjoint-uniqueness isomorphism
  sends the unifier into the construction of the inverse image.  **At the isomorphism it is `rfl`
  in under a second**, with no projection in the term, and the component then follows by
  `congrArg (fun z ↦ z.inv.app N)`; likewise with both arguments crossed at once.  So the
  conclusion drawn there — that a consumer must write `representedSpaceMap` throughout — is too
  strong: cross at the isomorphism and project.
* *`CategoryTheory.Category.assoc` does not fire under `simp only` on these composites*, the two
  `≫`s resolving their category instance differently, so every associativity rearrangement has to
  be made by a generic lemma at variables.
* *The `_hom` equations have to be rewritten with their arguments given explicitly.*  Bare
  `rw [chartCompositeDifferentialsAssociatedIso_hom]` reports `did not find an occurrence`;
  spelled out with `q w v k hw hv hsq r (chartToSpace … ≫ a) hc` it fires.  Together with
  `CategoryTheory.Iso.app_hom`, `.symm_hom`, `.app_inv` and `CategoryTheory.eqToIso.hom` this
  brings the chain to its component spelling.
* *What blocks it is a third spelling junction, and it is in a category instance.*  Writing the
  resulting normal form out as a statement and closing it by `rfl` after those rewrites is
  accepted by the elaborator and is a **kernel** timeout.  A `pp.explicit` diff of the two sides
  of the residual goal — which print identically — puts the difference in the instance argument
  of one `≫`: `Modules B S hS (chartSpace B S hS Z A).obj …` on the written side against
  `Modules B S hS (schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A)).obj …` on the rewritten
  one, the rewritten one inheriting it from the declared domain of
  `AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso`.  The two are `rfl` on their
  own; inside the composite the kernel has to identify them with `modulePullback` unfolded to its
  sheafification, and does not.  Writing `schemeSpace ((SmallEtale.toOver …).obj A)` at the two
  positions that admit it is not enough, because `chartToSpace B S hS Z A` carries
  `chartSpace B S hS Z A` into the first factor's own type.

Hence the chart-level square is not an instantiation of what is in the library: it needs the pasting
to be done by a *generic assembler at variables* — in the manner of
`CategoryTheory.square_of_factorizations` — taking the `_hom` equations, the head square
and the law above as hypotheses, so that no chart-level composite is ever written out and the
`chartSpace`/`schemeSpace` junction is never formed.

No `@[stacks]` attribute is claimed: Tags 03LU, 04CS and 04CU are registered at the isomorphisms
whose composition law this is, and these are its engine lemmas.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable {Bb Y : AlgebraicSpaces B S hS} {W V : BigFppfOver B S hS}

variable (q : Y ⟶ Bb) (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v)

/-- **The chart-square comparison's `hom`, at the spelling of [Stacks Project, Tag 03LU]'s
composition law.**  `AlgebraicGeometry.Space.chartSquareDifferentialsAssociatedIso` lands in the
represented associated module written as
`AlgebraicGeometry.Space.representedAssociatedModule`; the composition law
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_map` quantifies over a
morphism landing in the same object written as the comparison equivalence of the two small étale
sites applied to `AlgebraicGeometry.SmallEtale.associatedModule`.  The two spellings are equal by
`rfl`, and this declaration is where that is paid: see the module's implementation notes for why
it has to be paid by *naming* the ascription rather than inside the law's instantiation. -/
def chartSquareDifferentialsRepresentedHom :
    (modulePullback B S hS w).obj (sheafOfDifferentials B S hS q) ⟶
      (representedSmallEtaleModuleEquivalence B S hS W).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj W) W.left.property).obj
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))) :=
  (chartSquareDifferentialsAssociatedIso B S hS q w v k hw hv hsq).hom

/-- `AlgebraicGeometry.Space.chartSquareDifferentialsRepresentedHom` is the chart-square
comparison's `hom`.  The two sides have the two spellings of one type, so stating the equation
is itself the reconciliation; it is affordable here, where nothing else is in the term. -/
theorem chartSquareDifferentialsRepresentedHom_eq :
    chartSquareDifferentialsRepresentedHom B S hS q w v k hw hv hsq =
      (chartSquareDifferentialsAssociatedIso B S hS q w v k hw hv hsq).hom :=
  rfl

/-- **The composition law of [Stacks Project, Tag 03LU] at the chart-square comparison.**  For
`r : T ⟶ W` and a further `ρ : T' ⟶ T` in the big fppf site, the inverse image along `ρ` of the
chart-square comparison pulled back along `r`, followed by the transport along `ρ` at the
associated module and the associated module of the Zariski composition comparison, is the
comparison of Tag 03LU along `ρ` and `r`, the chart-square comparison pulled back along the
composite, and the transport along `ρ ≫ r`.

This is `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_map` read at
`ξ = (chartSquareDifferentialsAssociatedIso …).hom`.  It is the fourth factor of the source-square
chain of `AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso_hom`, the first three
being `AlgebraicGeometry.Space.modulePullbackCompIso_headSquare`.

The two type ascriptions are not decoration: without them the two sides' hidden arguments
disagree and the instantiation does not check.  See the module's implementation notes. -/
theorem representedAssociatedModulePullbackIso_comp_chartSquare
    {T T' : BigFppfOver B S hS} (r : T ⟶ W) (ρ : T' ⟶ T) :
    (modulePullback B S hS (representedSpaceMap B S hS ρ)).map
          ((modulePullback B S hS (representedSpaceMap B S hS r)).map
              (chartSquareDifferentialsRepresentedHom B S hS q w v k hw hv hsq) ≫
            (representedAssociatedModulePullbackIso B S hS r
              (relativelyRepresentable_yoneda_map B S hS r)
              (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))).hom) ≫
        (representedAssociatedModulePullbackIso B S hS ρ
            (relativelyRepresentable_yoneda_map B S hS ρ)
            ((Scheme.Modules.pullback (B.inclusion.map r.left)).obj
              (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k) :
                ((BigFppfOver.toScheme B S hS).obj W).Modules))).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
            ((Scheme.Modules.pullbackComp (B.inclusion.map ρ.left)
                (B.inclusion.map r.left)).hom.app
              (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k) :
                ((BigFppfOver.toScheme B S hS).obj W).Modules))) =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS ρ)
            (representedSpaceMap B S hS r)).hom.app
          ((modulePullback B S hS w).obj (sheafOfDifferentials B S hS q)) ≫
        (modulePullback B S hS (representedSpaceMap B S hS ρ ≫
            representedSpaceMap B S hS r)).map
          (chartSquareDifferentialsRepresentedHom B S hS q w v k hw hv hsq) ≫
        (representedAssociatedModulePullbackIso B S hS (ρ ≫ r)
          (relativelyRepresentable_yoneda_map B S hS (ρ ≫ r))
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))).hom :=
  representedAssociatedModulePullbackIso_comp_map B S hS r ρ
    (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))
    (chartSquareDifferentialsRepresentedHom B S hS q w v k hw hv hsq)

end AlgebraicGeometry.Space

end
