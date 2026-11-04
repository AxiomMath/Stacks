module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffectiveUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage

/-!
# A covering family of the final object of `S_étale` is an fpqc covering family of `S`

The essential-surjectivity half of Stacks 03DX (2) at `τ = étale` is reduced, by
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule_of_glue`, to the
*globalization step*: a module on `S_étale` with a global presentation on each member of some
covering family of the final object is an `𝓕^a`.  The source glues the local modules with the
effectivity of descent for quasi-coherent modules, Stacks 023T, which is a statement about an
**fpqc covering family of the scheme `S`** — so the first thing the globalization step needs is
that a covering family of the final object of `S_étale` *is* such a family.

**This file proves that, with no hypothesis.**  Every object of the small étale site of `S` is
étale over `S`, hence flat and locally of finite presentation over `S`, and a covering family of
the final object is jointly surjective on the points of `S`; so the family of structure
morphisms is an fppf — hence, by `AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage`,
an fpqc — covering family of `S`, with no refinement step.  Combined with the unconditional
effectivity half of Stacks 023T, every quasi-coherent descent datum for such a family is
effective.

This is where the small étale site differs from the big fppf site.  There the corresponding
statement is *false*: the objects of `(Sch/S)_fppf` are arbitrary schemes over `S`, so their
structure morphisms need not even be flat, and only a refinement of the generated covering sieve
is an fppf covering family — the step recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.QcohGlueAssembly`.  The docstring of
`AlgebraicGeometry.SmallEtale.EssImageAssociatedModuleGlue` asserts the absence of that step; the
results below are its proof.

## Main definitions

* `AlgebraicGeometry.SmallEtale.coveringHypercover`: a family of objects of `S_étale`, read as a
  family of schemes over `S` through their structure morphisms.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_mem_arrows_mem_range`: every covering
  sieve of the small étale site is jointly surjective on the points of its target.
* `AlgebraicGeometry.SmallEtale.exists_mem_range_structureMorphism_of_coversTop`: the structure
  morphisms of a covering family of the final object of `S_étale` are jointly surjective on the
  points of `S`.
* `AlgebraicGeometry.SmallEtale.presieve₀_mem_fppfPrecoverage_coveringHypercover` and
  `AlgebraicGeometry.SmallEtale.presieve₀_mem_fpqcPrecoverage_coveringHypercover`: **a covering
  family of the final object of `S_étale` is an fppf, hence an fpqc, covering family of `S`.**
* `AlgebraicGeometry.SmallEtale.isEffective_coveringHypercover`: **the Stacks 023T input of the
  globalization step of Stacks 03DX (2) at `τ = étale`, with no hypothesis** — every
  quasi-coherent descent datum for such a family is effective.

## Implementation notes

Nothing here carries a `stacks` attribute.  Stacks 023T is tagged on
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`, which is what is
instantiated below, and Stacks 021B on the covering families of the small étale site; what is
added is the comparison of the two, which is a step in the proof of Stacks 03DX (2) and not a
clause of it.

The index type of the family is left in an arbitrary universe: the covering families that
Stacks 03DN produces on `S_étale` are indexed by `Type (u + 1)`, while
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage` is polymorphic in the
index universe, so no lifting is needed anywhere.

`AlgebraicGeometry.SmallEtale.exists_mem_arrows_mem_range` is the converse of
`AlgebraicGeometry.SmallEtale.mem_topology_of_jointlySurjective`: a covering sieve is refined by
a single covering family, the small étale precoverage being stable under composition and base
change, and a covering family of the small étale site is by definition an étale covering family
of the ambient category of schemes, which has joint surjectivity built in.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 022C](https://stacks.math.columbia.edu/tag/022C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Covering sieves of the small étale site are jointly surjective -/

/-! ### The structure morphisms of a covering family of the final object -/

/-- The unique morphism from an object of `S_étale` to the final object `S / S` is, on underlying
schemes, the structure morphism of that object. -/
public theorem toScheme_map_from_final (X : SmallEtale B S hS) :
    (toScheme B S hS).map ((finalIsTerminal B S hS).from X) = B.inclusion.map X.obj.hom := by
  have h : (finalIsTerminal B S hS).from X =
      ObjectProperty.homMk (P := BigEtaleOver.IsEtaleOver B S hS)
        (Over.homMk (U := X.obj) (V := Over.mk (𝟙 (B.obj S hS))) X.obj.hom (by simp)) :=
    (finalIsTerminal B S hS).hom_ext _ _
  rw [h]
  rfl

/-- **A family of objects of the small étale site of `S`, read as a family of schemes over
`S`.**  Its members are the underlying schemes and its morphisms the structure morphisms; this
is the shape in which `AlgebraicGeometry.QuasicoherentDescentData` and the effectivity half of
Stacks 023T consume a covering family. -/
public def coveringHypercover {I : Type w} (X : I → SmallEtale B S hS) :
    PreZeroHypercover.{w} S where
  I₀ := I
  X i := (toScheme B S hS).obj (X i)
  f i := B.inclusion.map (X i).obj.hom

/-- **The structure morphisms of a covering family of the final object of `S_étale` are jointly
surjective on the points of `S`.**

Every arrow of the sieve `Sieve.ofObjects X` at the final object factors through some member
`X i`, uniquely so, the target being final; so the image of such an arrow is contained in the
image of the structure morphism of `X i`, and the arrows are jointly surjective by
`AlgebraicGeometry.SmallEtale.exists_mem_arrows_mem_range`. -/
public theorem exists_mem_range_structureMorphism_of_coversTop {I : Type w}
    (X : I → SmallEtale B S hS) (hX : (topology B S hS).CoversTop X)
    (x : (toScheme B S hS).obj (final B S hS)) :
    ∃ i, x ∈ Set.range (B.inclusion.map (X i).obj.hom) := by
  obtain ⟨W, g, ⟨i, ⟨h⟩⟩, y, hy⟩ :=
    exists_mem_arrows_mem_range B S hS (hX (final B S hS)) x
  refine ⟨i, ?_⟩
  have hg : g = h ≫ (finalIsTerminal B S hS).from (X i) :=
    (finalIsTerminal B S hS).hom_ext _ _
  refine ⟨(toScheme B S hS).map h y, ?_⟩
  rw [← hy, hg, Functor.map_comp, ← toScheme_map_from_final B S hS (X i)]
  rfl

/-- The members of `AlgebraicGeometry.SmallEtale.coveringHypercover` are flat: they are the
structure morphisms of objects of the small étale site, which are étale. -/
public instance flat_coveringHypercover_f {I : Type w} (X : I → SmallEtale B S hS) (i : I) :
    Flat ((coveringHypercover B S hS X).f i) :=
  inferInstanceAs (Flat (B.inclusion.map (X i).obj.hom))

/-- The members of `AlgebraicGeometry.SmallEtale.coveringHypercover` are locally of finite
presentation, being étale. -/
public instance locallyOfFinitePresentation_coveringHypercover_f {I : Type w}
    (X : I → SmallEtale B S hS) (i : I) :
    LocallyOfFinitePresentation ((coveringHypercover B S hS X).f i) :=
  inferInstanceAs (LocallyOfFinitePresentation (B.inclusion.map (X i).obj.hom))

/-! ### The family is an fppf, hence an fpqc, covering family -/

/-- **A covering family of the final object of `S_étale` is an fppf covering family of `S`.**
The structure morphisms are étale, hence flat and locally of finite presentation, and they are
jointly surjective. -/
public theorem presieve₀_mem_fppfPrecoverage_coveringHypercover {I : Type w}
    (X : I → SmallEtale B S hS) (hX : (topology B S hS).CoversTop X) :
    (coveringHypercover B S hS X).presieve₀ ∈ Scheme.fppfPrecoverage.{u} S :=
  (Scheme.ofArrows_mem_precoverage_iff (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr
    ⟨exists_mem_range_structureMorphism_of_coversTop B S hS X hX,
      fun i ↦ ⟨flat_coveringHypercover_f B S hS X i,
        locallyOfFinitePresentation_coveringHypercover_f B S hS X i⟩⟩

/-- **A covering family of the final object of `S_étale` is an fpqc covering family of `S`.**
An fppf covering family is an fpqc covering family, flat morphisms locally of finite
presentation being open. -/
public theorem presieve₀_mem_fpqcPrecoverage_coveringHypercover {I : Type w}
    (X : I → SmallEtale B S hS) (hX : (topology B S hS).CoversTop X) :
    (coveringHypercover B S hS X).presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S :=
  Scheme.fppfPrecoverage_le_fpqcPrecoverage _
    (presieve₀_mem_fppfPrecoverage_coveringHypercover B S hS X hX)

/-! ### The Stacks 023T input of the globalization step -/

/-- **The Stacks 023T input of the globalization step of Stacks 03DX (2) at `τ = étale`, with no
hypothesis.**  Every quasi-coherent descent datum for the family of structure morphisms of a
covering family of the final object of `S_étale` is effective.

So the gluing of the local quasi-coherent modules `𝓕_i` to a quasi-coherent `𝓕` on `S` is
available at exactly the families that quasi-coherence produces, and what the globalization step
still has to supply is the *descent datum* itself: the transition isomorphisms
`pr₀^* 𝓕_i ≅ pr₁^* 𝓕_j` out of full faithfulness of `𝓕 ↦ 𝓕^a` over the fibre products, and
their cocycle condition. -/
public theorem isEffective_coveringHypercover {I : Type w} (X : I → SmallEtale B S hS)
    (hX : (topology B S hS).CoversTop X)
    (D : QuasicoherentDescentData (coveringHypercover B S hS X).f) : D.IsEffective :=
  QuasicoherentDescentData.isEffective_fpqcPrecoverage _
    (presieve₀_mem_fpqcPrecoverage_coveringHypercover B S hS X hX) D

end AlgebraicGeometry.SmallEtale

end
