module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.Zariski

/-!
# Comparing the covering families of algebraic spaces across the five topologies

Let `S` be a scheme contained in a big fppf site `B`. The covering families of the five
topologies of **Stacks 03YH** are ordered: a Zariski covering is étale, an étale covering is
smooth, a smooth covering is syntomic, a syntomic covering is fppf, and an fppf covering is
fpqc. The first of these five links is **Stacks 0DF1** and is already available as
`AlgebraicGeometry.Space.isEtaleCovering_of_isZariskiCovering`, and the last is
**Stacks 0DFQ** for fppf coverings, already available as
`AlgebraicGeometry.Space.isFpqcCovering_of_isFppfCovering`; this module supplies the three in
between — **Stacks 0DFA**, **0DFB** and **0DFC** — and composes all five to give the
remaining cases of 0DFA, 0DFB, 0DFC and **Stacks 0DFQ**.

Each link is an implication between the property clauses of the two covering structures, the
algebraicity and joint-surjectivity clauses being literally the same. Since the property
clauses are the chart conditions `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of
**Stacks 03MJ**, which are monotone in the tested property of scheme morphisms by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_mono`, each implication reduces to the
corresponding implication between properties of morphisms of *schemes*: étale morphisms are
smooth (already proved as **Stacks 04XX** for algebraic spaces), smooth morphisms of schemes
are syntomic (**Stacks 01VD**), and syntomic morphisms of schemes are flat and locally of
finite presentation (**Stacks 01UL**, **01UK**). No étale locality of any of the properties is
needed, which is why these links are available where the composition and base-change lemmas
for the syntomic topology are not.

## Main results

* `AlgebraicGeometry.Space.isSyntomic_of_isSmooth` (declared in `Spaces/Morphisms/Syntomic.lean`):
  a smooth morphism of algebraic spaces is
  syntomic.
* `AlgebraicGeometry.Space.isFlat_of_isSyntomic` and
  `.isLocallyOfFinitePresentation_of_isSyntomic` (declared in `Spaces/Morphisms/Syntomic.lean`):
  a syntomic morphism of algebraic spaces is flat and locally of finite presentation.
* `AlgebraicGeometry.Space.isSmoothCovering_of_isEtaleCovering`: **Stacks 0DFA**, étale case.
* `AlgebraicGeometry.Space.isSyntomicCovering_of_isSmoothCovering`,
  `.isSyntomicCovering_of_isEtaleCovering`: **Stacks 0DFB**, smooth and étale cases.
* `AlgebraicGeometry.Space.isFppfCovering_of_isSyntomicCovering`,
  `.isFppfCovering_of_isSmoothCovering`, `.isFppfCovering_of_isEtaleCovering`:
  **Stacks 0DFC**, syntomic, smooth and étale cases.
* `AlgebraicGeometry.Space.isFppfCovering_of_isIso`: **Stacks 03Y9**, the isomorphism
  clause.
* `AlgebraicGeometry.Space.isFpqcCovering_of_isSyntomicCovering`,
  `.isFpqcCovering_of_isSmoothCovering`, `.isFpqcCovering_of_isEtaleCovering`:
  **Stacks 0DFQ**, syntomic, smooth and étale cases.
* `AlgebraicGeometry.Space.isSmoothCovering_of_isZariskiCovering`,
  `.isSyntomicCovering_of_isZariskiCovering`, `.isFppfCovering_of_isZariskiCovering`,
  `.isFpqcCovering_of_isZariskiCovering`: the Zariski cases of **Stacks 0DFA**, **0DFB**,
  **0DFC** and **0DFQ**, the "a fortiori" clause of each of those four statements.
* `AlgebraicGeometry.Space.Topology.precoverage_le_of_isCovering` and the three comparisons
  `.precoverage_smooth_le_syntomic`, `.precoverage_smooth_le_fppf`,
  `.precoverage_smooth_le_fpqc`: the same links read off as inclusions of the precoverages of
  Stacks 03YH, which is the form `CategoryTheory.MorphismProperty.IsLocalAtSource.of_le` and
  `.IsLocalAtTarget.of_le` consume.

## Implementation notes

The Zariski cases go through the étale ones rather than directly: a Zariski covering is an
étale covering by Stacks 0DF1, and that implication already carries the algebraicity of the
target and of the sources as hypotheses, since they are fields of
`AlgebraicGeometry.Space.IsEtaleCovering` while `AlgebraicGeometry.Space.IsZariskiCovering` is
stated for arbitrary presheaves on the big fppf site. The four Zariski lemmas therefore take
those two hypotheses where the étale, smooth and syntomic ones do not.

These are **Chapter 74 tags**, stated here because the fpqc source-locality transfer of
Stacks 06ER — which the Chapter 103–104 flat-fppf results rest on — cannot be assembled without
them.

## References

* [Stacks Project, Tag 0DF1](https://stacks.math.columbia.edu/tag/0DF1)
* [Stacks Project, Tag 0DFA](https://stacks.math.columbia.edu/tag/0DFA)
* [Stacks Project, Tag 0DFB](https://stacks.math.columbia.edu/tag/0DFB)
* [Stacks Project, Tag 0DFC](https://stacks.math.columbia.edu/tag/0DFC)
* [Stacks Project, Tag 0DFQ](https://stacks.math.columbia.edu/tag/0DFQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Implications between the properties -/


/-! ### Syntomic morphisms are flat and locally of finite presentation

`AlgebraicGeometry.Space.isFlat_of_isSyntomic` and
`.isLocallyOfFinitePresentation_of_isSyntomic` are NOT declared here. They carry
`@[stacks 0DEZ]` and `@[stacks 0DEY]` in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Syntomic.lean`, which this module now imports.
Untagged copies lived here as well, and because both modules are reachable from the
`StacksDraft` umbrella that made the umbrella fail with `environment already contains …`; it
also made `Spaces/Morphisms/Syntomic.lean` unable to import `Spaces/Morphisms/Flat.lean`. -/

/-! ### Stacks 0DFA: étale coverings are smooth coverings -/

/-- **Stacks 0DFA**, the étale case: an étale covering of algebraic spaces over `S` is a smooth
covering. -/
@[stacks 0DFA "étale coverings"]
theorem isSmoothCovering_of_isEtaleCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ F}
    (hf : IsEtaleCovering B S hS X f) :
    IsSmoothCovering B S hS X f :=
  ⟨hf.target_isAlgebraicSpace, hf.source_isAlgebraicSpace,
    fun i => isSmooth_of_isEtale B S hS hf.target_isAlgebraicSpace (hf.etale i),
    hf.jointly_surjective⟩

/-! ### Stacks 0DFB: smooth and étale coverings are syntomic coverings -/

/-- **Stacks 0DFB**, the smooth case: a smooth covering of algebraic spaces over `S` is a
syntomic covering. -/
@[stacks 0DFB "smooth coverings"]
theorem isSyntomicCovering_of_isSmoothCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ F}
    (hf : IsSmoothCovering B S hS X f) :
    IsSyntomicCovering B S hS X f :=
  ⟨hf.target_isAlgebraicSpace, hf.source_isAlgebraicSpace,
    fun i => isSyntomic_of_isSmooth B S hS _ (hf.smooth i), hf.jointly_surjective⟩

/-- **Stacks 0DFB**, the étale case: an étale covering of algebraic spaces over `S` is a
syntomic covering. -/
@[stacks 0DFB "étale coverings"]
theorem isSyntomicCovering_of_isEtaleCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ F}
    (hf : IsEtaleCovering B S hS X f) :
    IsSyntomicCovering B S hS X f :=
  isSyntomicCovering_of_isSmoothCovering B S hS
    (isSmoothCovering_of_isEtaleCovering B S hS hf)

/-! ### Stacks 0DFC: syntomic, smooth and étale coverings are fppf coverings -/

/-- **Stacks 0DFC**, the syntomic case: a syntomic covering of algebraic spaces over `S` is an
fppf covering. -/
@[stacks 0DFC "syntomic coverings"]
theorem isFppfCovering_of_isSyntomicCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ F}
    (hf : IsSyntomicCovering B S hS X f) :
    IsFppfCovering B S hS X f :=
  ⟨hf.target_isAlgebraicSpace, hf.source_isAlgebraicSpace,
    fun i => isFlat_of_isSyntomic B S hS (hf.syntomic i),
    fun i => isLocallyOfFinitePresentation_of_isSyntomic B S hS (hf.syntomic i),
    hf.jointly_surjective⟩

/-- **Stacks 0DFC**, the smooth case: a smooth covering of algebraic spaces over `S` is an fppf
covering. -/
@[stacks 0DFC "smooth coverings"]
theorem isFppfCovering_of_isSmoothCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ F}
    (hf : IsSmoothCovering B S hS X f) :
    IsFppfCovering B S hS X f :=
  isFppfCovering_of_isSyntomicCovering B S hS
    (isSyntomicCovering_of_isSmoothCovering B S hS hf)

/-- **Stacks 0DFC**, the étale case: an étale covering of algebraic spaces over `S` is an fppf
covering. -/
@[stacks 0DFC "étale coverings"]
theorem isFppfCovering_of_isEtaleCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ F}
    (hf : IsEtaleCovering B S hS X f) :
    IsFppfCovering B S hS X f :=
  isFppfCovering_of_isSyntomicCovering B S hS
    (isSyntomicCovering_of_isEtaleCovering B S hS hf)

/-! ### Stacks 03Y9: an isomorphism is an fppf covering -/

/-- **Stacks 03Y9**, the isomorphism clause. An isomorphism of algebraic spaces over `S`,
regarded as a family indexed by a point, is an fppf covering: it is an étale covering by
**Stacks 041F**, hence an fppf covering by **Stacks 0DFC**. -/
@[stacks 03Y9 "isomorphism_cover"]
theorem isFppfCovering_of_isIso
    (X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : X' ⟶ X) [IsIso f]
    (hX : IsAlgebraicSpace B S hS X) :
    IsFppfCovering B S hS (fun _ : PUnit.{v + 1} => X') (fun _ => f) :=
  IsFppfCovering.reindex B S hS
    (isFppfCovering_of_isEtaleCovering B S hS (isEtaleCovering_of_isIso B S hS f hX))
    (σ := fun _ : PUnit.{v + 1} => ()) fun _ => ⟨PUnit.unit, rfl⟩

/-! ### Stacks 0DFQ: the remaining comparisons with fpqc coverings -/

/-- **Stacks 0DFQ**, the syntomic case: a syntomic covering of algebraic spaces over `S` is an
fpqc covering. -/
@[stacks 0DFQ "syntomic coverings"]
theorem isFpqcCovering_of_isSyntomicCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F)
    (hf : IsSyntomicCovering B S hS X f) :
    IsFpqcCovering B S hS f :=
  isFpqcCovering_of_isFppfCovering B S hS X f
    (isFppfCovering_of_isSyntomicCovering B S hS hf)

/-- **Stacks 0DFQ**, the smooth case: a smooth covering of algebraic spaces over `S` is an fpqc
covering. -/
@[stacks 0DFQ "smooth coverings"]
theorem isFpqcCovering_of_isSmoothCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F)
    (hf : IsSmoothCovering B S hS X f) :
    IsFpqcCovering B S hS f :=
  isFpqcCovering_of_isFppfCovering B S hS X f
    (isFppfCovering_of_isSmoothCovering B S hS hf)

/-- **Stacks 0DFQ**, the étale case: an étale covering of algebraic spaces over `S` is an fpqc
covering. -/
@[stacks 0DFQ "étale coverings"]
theorem isFpqcCovering_of_isEtaleCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F)
    (hf : IsEtaleCovering B S hS X f) :
    IsFpqcCovering B S hS f :=
  isFpqcCovering_of_isFppfCovering B S hS X f
    (isFppfCovering_of_isEtaleCovering B S hS hf)

/-! ### The Zariski cases -/

/-- **Stacks 0DFA**, the Zariski case: a Zariski covering of algebraic spaces over `S` is a
smooth covering, because it is an étale covering by Stacks 0DF1. -/
@[stacks 0DFA "Zariski coverings"]
theorem isSmoothCovering_of_isZariskiCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ F}
    (hF : IsAlgebraicSpace B S hS F) (hX : ∀ i, IsAlgebraicSpace B S hS (X i))
    (hf : IsZariskiCovering B S hS I X f) :
    IsSmoothCovering B S hS X f :=
  isSmoothCovering_of_isEtaleCovering B S hS
    (isEtaleCovering_of_isZariskiCovering B S hS hF hX hf)

/-- **Stacks 0DFB**, the Zariski case: a Zariski covering of algebraic spaces over `S` is a
syntomic covering. -/
@[stacks 0DFB "Zariski coverings"]
theorem isSyntomicCovering_of_isZariskiCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ F}
    (hF : IsAlgebraicSpace B S hS F) (hX : ∀ i, IsAlgebraicSpace B S hS (X i))
    (hf : IsZariskiCovering B S hS I X f) :
    IsSyntomicCovering B S hS X f :=
  isSyntomicCovering_of_isSmoothCovering B S hS
    (isSmoothCovering_of_isZariskiCovering B S hS hF hX hf)

/-- **Stacks 0DFC**, the Zariski case: a Zariski covering of algebraic spaces over `S` is an
fppf covering. -/
@[stacks 0DFC "Zariski coverings"]
theorem isFppfCovering_of_isZariskiCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ F}
    (hF : IsAlgebraicSpace B S hS F) (hX : ∀ i, IsAlgebraicSpace B S hS (X i))
    (hf : IsZariskiCovering B S hS I X f) :
    IsFppfCovering B S hS X f :=
  isFppfCovering_of_isSyntomicCovering B S hS
    (isSyntomicCovering_of_isZariskiCovering B S hS hF hX hf)

/-- **Stacks 0DFQ**, the Zariski case: a Zariski covering of algebraic spaces over `S` is an
fpqc covering. -/
@[stacks 0DFQ "Zariski coverings"]
theorem isFpqcCovering_of_isZariskiCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F)
    (hF : IsAlgebraicSpace B S hS F) (hX : ∀ i, IsAlgebraicSpace B S hS (X i))
    (hf : IsZariskiCovering B S hS I X f) :
    IsFpqcCovering B S hS f :=
  isFpqcCovering_of_isFppfCovering B S hS X f
    (isFppfCovering_of_isZariskiCovering B S hS hF hX hf)
/-! ### The comparisons as inclusions of precoverages -/

/-- A pointwise implication between the covering conditions of two of the topologies of
Stacks 03YH is an inclusion of the associated precoverages on the category of algebraic spaces
over `S`. -/
theorem Topology.precoverage_le_of_isCovering {τ σ : Topology}
    (h : ∀ {I : Type v} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (Yi : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : ∀ i, Yi i ⟶ Y),
      τ.IsCovering B S hS Yi g → σ.IsCovering B S hS Yi g) :
    Topology.precoverage.{u, v} τ B S hS ≤ Topology.precoverage.{u, v} σ B S hS := by
  rintro Y R ⟨I, Yi, g, rfl, hcover⟩
  exact ⟨I, Yi, g, rfl, h _ _ hcover⟩

/-- **Stacks 0DFB** at the precoverages: the smooth precoverage of algebraic spaces over `S` is
contained in the syntomic one. -/
theorem Topology.precoverage_smooth_le_syntomic :
    Topology.precoverage.{u, v} .smooth B S hS ≤
      Topology.precoverage.{u, v} .syntomic B S hS :=
  Topology.precoverage_le_of_isCovering B S hS fun _ _ hcover =>
    ⟨hcover.1, hcover.2.1, isSyntomicCovering_of_isSmoothCovering B S hS hcover.2.2⟩

/-- **Stacks 0DFC** at the precoverages: the smooth precoverage of algebraic spaces over `S` is
contained in the fppf one. -/
theorem Topology.precoverage_smooth_le_fppf :
    Topology.precoverage.{u, v} .smooth B S hS ≤ Topology.precoverage.{u, v} .fppf B S hS :=
  Topology.precoverage_le_of_isCovering B S hS fun _ _ hcover =>
    ⟨hcover.1, hcover.2.1, isFppfCovering_of_isSmoothCovering B S hS hcover.2.2⟩

/-- **Stacks 0DFQ** at the precoverages: the smooth precoverage of algebraic spaces over `S` is
contained in the fpqc one. -/
theorem Topology.precoverage_smooth_le_fpqc :
    Topology.precoverage.{u, v} .smooth B S hS ≤ Topology.precoverage.{u, v} .fpqc B S hS :=
  Topology.precoverage_le_of_isCovering B S hS fun Yi g hcover =>
    ⟨hcover.1, hcover.2.1, isFpqcCovering_of_isSmoothCovering B S hS Yi g hcover.2.2⟩

end AlgebraicGeometry.Space

end
