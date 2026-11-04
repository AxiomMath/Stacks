module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas

/-!
# `i_*` and `Ri_* = i_*` in the `OXMod` idiom of the pseudo-coherence development

The pseudo-coherence development
(`StacksDraft.AlgebraicGeometry.PseudoCoherent.*`) speaks about `𝒪_X`-modules through
`StrictlyPerfect.OXMod X = SheafOfModules (StrictlyPerfect.structureSheafOfRings X)`, whereas
pushforward of sheaves of modules along a morphism of ringed spaces and its exactness at a
closed immersion are stated through
`structureSheafRing X`. The two sheaves of rings are the *same*
construction — `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf` — and
`structureSheafOfRings_eq_ringSheaf` records that they are definitionally equal.

Definitional equality is however not enough to use the one development inside the other. Neither
`structureSheafOfRings` nor `structureSheafRing` is reducible, and typeclass resolution unfolds
only at reducible transparency, so a hypothesis `[HasDerivedCategory (OXMod Z)]` does *not*
discharge the instance argument `[HasDerivedCategory (SheafOfModules (structureSheafRing Z))]` that
`(RingedSpaceModuleAdjunction.modulePushforward i).mapDerivedCategory` demands. Every declaration
below has binders written at the `OXMod` spelling, so all instance synthesis happens here, where
the categories in the statement are literally the ones the pseudo-coherence development uses; the
bodies are the `structureSheafRing`-spelled declarations, for which only term-level definitional
equality is needed.

## Main definitions

* `AlgebraicGeometry.RingedSpace.pushforwardOXMod`: `i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)`.
* `AlgebraicGeometry.RingedSpace.pullbackOXMod`: `i^* : Mod(𝒪_X) ⥤ Mod(𝒪_Z)`.
* `AlgebraicGeometry.RingedSpace.pullbackPushforwardAdjunctionOXMod`: `i^* ⊣ i_*`.
* `AlgebraicGeometry.RingedSpace.pushforwardStructureModule`: `i_*𝒪_Z` as an `𝒪_X`-module.
* `AlgebraicGeometry.RingedSpace.derivedPushforwardOXMod`: `Ri_* = i_*` at a closed immersion,
  that is, the functor `D(𝒪_Z) ⥤ D(𝒪_X)` induced by the exact functor `i_*`.

## Main results

* `AlgebraicGeometry.RingedSpace.preservesFiniteColimits_pushforwardOXMod` and
  `AlgebraicGeometry.RingedSpace.exactFunctor_pushforwardOXMod`: at a closed immersion of
  ringed spaces `i_*` is exact, in the form the pseudo-coherence development can consume.
* `AlgebraicGeometry.RingedSpace.isRightDerivedFunctor_derivedPushforwardOXMod`: the induced
  functor really is a right derived functor of `i_*`, which is the content of `Ri_* = i_*`.

## Implementation notes

Exactness itself is not reproved. Left exactness is `modulePushforward_isRightAdjoint`, and
right exactness at a closed immersion is
`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward` (Stacks 08KS), which is
proved directly on stalks. The corresponding statement one level down, for sheaves of abelian
groups, is Stacks 01AX
(`Stacks.ClosedImmersion.exactFunctor_closedInclusionPushforward`); the two proofs are
independent. What is added here is exclusively the change of spelling.

`PreservesFiniteColimits` is data rather than a proposition, so there is no way to state that
`derivedPushforwardOXMod i hi` *equals* `(pushforwardOXMod i).mapDerivedCategory` for some
other choice of that instance. `derivedPushforwardOXMod` is therefore the canonical name for
`Ri_*` at these types, and consumers should use it rather than rebuilding
`mapDerivedCategory` with their own `haveI`.

Only the closed-embedding hypothesis on the underlying continuous map is used, never the
surjectivity of `i^♯` that Stacks 08KS also assumes: exactness does not need it. Accordingly
the hypothesis here is `Topology.IsClosedEmbedding i.hom.base`, exactly as in Stacks 09VA.

## References

* [Stacks Project, Lemma 17.6.1 (Tag 01AX)](https://stacks.math.columbia.edu/tag/01AX)
* [Stacks Project, Lemma 17.13.4 (Tag 08KS)](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect

universe d u

namespace AlgebraicGeometry.RingedSpace

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X)

/-- The structure sheaf of rings of a ringed space as used by the pseudo-coherence development
and the one used by the pushforward/pullback development are the same construction. -/
public theorem structureSheafOfRings_eq_ringSheaf (X : RingedSpace.{u, u}) :
    StrictlyPerfect.structureSheafOfRings X = structureSheafRing X :=
  rfl

/-! ### The functors and the adjunction -/

/-- **Pushforward of `𝒪`-modules along a morphism of ringed spaces**, `i_*`, written at the
`StrictlyPerfect.OXMod` types the pseudo-coherence development uses. This is
`RingedSpaceModuleAdjunction.modulePushforward` with no change of content. -/
public def pushforwardOXMod : OXMod.{u, u} Z ⥤ OXMod.{u, u} X := modulePushforward i

/-- **Pullback of `𝒪`-modules along a morphism of ringed spaces**, `i^*`, written at the
`StrictlyPerfect.OXMod` types. This is `RingedSpaceModuleAdjunction.modulePullback`. -/
public def pullbackOXMod : OXMod.{u, u} X ⥤ OXMod.{u, u} Z := modulePullback i

/-- The adjunction `i^* ⊣ i_*` at the `StrictlyPerfect.OXMod` types. This is what the converse
half of Stacks 09VA uses to turn a map `𝒪_X^{⊕n}[-p] ⟶ i_*ℰ^•` into a map
`𝒪_Z^{⊕n}[-p] ⟶ ℰ^•`. -/
public def pullbackPushforwardAdjunctionOXMod : pullbackOXMod i ⊣ pushforwardOXMod i :=
  modulePullbackPushforwardAdjunction i

/-- `i_*𝒪_Z`, the pushforward of the structure sheaf of `Z`, as an `𝒪_X`-module. Stacks 09VA
assumes this module is pseudo-coherent. -/
public def pushforwardStructureModule : OXMod.{u, u} X :=
  (pushforwardOXMod i).obj (structureModule Z)

/-! ### Exactness -/

/-- `i_*` is additive: on underlying presheaves of abelian groups it is precomposition with
the map of open sets. -/
public instance additive_pushforwardOXMod : (pushforwardOXMod i).Additive :=
  Stacks.ClosedImmersion.additive_modulePushforward i

/-- `i_*` is left exact, being a right adjoint. No hypothesis on `i` is needed. -/
public instance preservesFiniteLimits_pushforwardOXMod :
    PreservesFiniteLimits (pushforwardOXMod i) :=
  Stacks.ClosedImmersion.preservesFiniteLimits_modulePushforward i

/-- `i_*` is right exact when the underlying continuous map of `i` is a closed embedding.

This is Stacks 08KS (`preservesFiniteColimits_modulePushforward`), restated at the
`StrictlyPerfect.OXMod` types; the underlying abelian-sheaf fact is Stacks 01AX. -/
public theorem preservesFiniteColimits_pushforwardOXMod
    (hi : Topology.IsClosedEmbedding i.hom.base) :
    PreservesFiniteColimits (pushforwardOXMod i) :=
  Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward i hi

/-- **`i_*` is exact at a closed immersion of ringed spaces**, in the `StrictlyPerfect.OXMod`
idiom. This is the statement Stacks 09VA appeals to when it says "`i_*` is an exact functor,
and hence `Ri_* = i_*`, see Modules, Lemma 01AX". -/
public theorem exactFunctor_pushforwardOXMod (hi : Topology.IsClosedEmbedding i.hom.base) :
    exactFunctor (OXMod.{u, u} Z) (OXMod.{u, u} X) (pushforwardOXMod i) :=
  ⟨preservesFiniteLimits_pushforwardOXMod i, preservesFiniteColimits_pushforwardOXMod i hi⟩

/-! ### `Ri_* = i_*` -/

variable [HasDerivedCategory.{d} (OXMod.{u, u} Z)] [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- **`Ri_* = i_*`.** For a morphism of ringed spaces whose underlying continuous map is a
closed embedding, `i_*` is exact and therefore induces a functor on unbounded derived
categories with no resolution at all. This is the `Ri_*` of Stacks 09VA. -/
public def derivedPushforwardOXMod (hi : Topology.IsClosedEmbedding i.hom.base) :
    DerivedCategory (OXMod.{u, u} Z) ⥤ DerivedCategory (OXMod.{u, u} X) :=
  haveI := preservesFiniteColimits_pushforwardOXMod i hi
  (pushforwardOXMod i).mapDerivedCategory

/-- `derivedPushforwardOXMod` is a right derived functor of `i_*` passed to homotopy
categories, with unit `Functor.mapDerivedCategoryFactorsh.inv`. This is what justifies calling
it `Ri_*`. -/
public theorem isRightDerivedFunctor_derivedPushforwardOXMod
    (hi : Topology.IsClosedEmbedding i.hom.base) :
    haveI := preservesFiniteColimits_pushforwardOXMod i hi
    (derivedPushforwardOXMod i hi).IsRightDerivedFunctor
      (pushforwardOXMod i).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (OXMod.{u, u} Z) (ComplexShape.up ℤ)) :=
  have := preservesFiniteColimits_pushforwardOXMod i hi
  Stacks.ClosedImmersion.isRightDerivedFunctor_mapDerivedCategory (pushforwardOXMod i)

/-- `Ri_*` commutes with the shift on derived categories. -/
public instance commShift_derivedPushforwardOXMod
    (hi : Topology.IsClosedEmbedding i.hom.base) :
    (derivedPushforwardOXMod i hi).CommShift ℤ :=
  haveI := preservesFiniteColimits_pushforwardOXMod i hi
  inferInstanceAs ((pushforwardOXMod i).mapDerivedCategory.CommShift ℤ)

/-- `Ri_*` is a triangulated functor. -/
public instance isTriangulated_derivedPushforwardOXMod
    (hi : Topology.IsClosedEmbedding i.hom.base) :
    (derivedPushforwardOXMod i hi).IsTriangulated :=
  haveI := preservesFiniteColimits_pushforwardOXMod i hi
  inferInstanceAs ((pushforwardOXMod i).mapDerivedCategory.IsTriangulated)

/-- `Ri_*` carries a distinguished triangle of `D(𝒪_Z)` to a distinguished triangle of
`D(𝒪_X)`. Both halves of the Stacks 09VA induction use this: a distinguished triangle
`𝒪_Z^{⊕n}[-p] ⟶ E ⟶ C ⟶ 𝒪_Z^{⊕n}[-p+1]` is pushed forward to a distinguished triangle to
which Stacks 08CD applies. -/
public theorem map_distinguished_derivedPushforwardOXMod
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (T : Triangle (DerivedCategory (OXMod.{u, u} Z)))
    (hT : T ∈ distTriang (DerivedCategory (OXMod.{u, u} Z))) :
    (derivedPushforwardOXMod i hi).mapTriangle.obj T ∈
      distTriang (DerivedCategory (OXMod.{u, u} X)) :=
  (derivedPushforwardOXMod i hi).map_distinguished T hT

/-- `i_*(𝒪_Z^{⊕n}) ≅ (i_*𝒪_Z)^{⊕n}`: pushforward is additive, hence preserves finite
biproducts, so it carries the finite free `𝒪_Z`-module on `n` generators to the `n`-fold
biproduct of `i_*𝒪_Z`.

Stacks 09VA uses this to go from pseudo-coherence of `i_*𝒪_Z` to pseudo-coherence of
`i_*(𝒪_Z^{⊕n}[-p])`. -/
public def pushforwardFiniteFreeIso (n : ℕ) :
    (pushforwardOXMod i).obj (finiteFree Z n) ≅
      biproduct (fun _ : Fin n => pushforwardStructureModule i) :=
  Functor.mapBiproduct (pushforwardOXMod i) (fun _ : Fin n => structureModule Z)

/-- The derived pushforward of a complex of `𝒪_Z`-modules is the pushforward complex: on an
object in the image of the localization functor `Q`, `Ri_*` is computed termwise by `i_*`.

This is `Functor.mapDerivedCategoryFactors`, and it is the step that makes the induction of
Stacks 09VA possible: a distinguished triangle of complexes of `𝒪_Z`-modules is carried to a
distinguished triangle of complexes of `𝒪_X`-modules by applying `i_*` in each degree. -/
public def derivedPushforwardOXModFactors (hi : Topology.IsClosedEmbedding i.hom.base) :
    DerivedCategory.Q ⋙ derivedPushforwardOXMod i hi ≅
      (pushforwardOXMod i).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  haveI := preservesFiniteColimits_pushforwardOXMod i hi
  (pushforwardOXMod i).mapDerivedCategoryFactors

end AlgebraicGeometry.RingedSpace

end
