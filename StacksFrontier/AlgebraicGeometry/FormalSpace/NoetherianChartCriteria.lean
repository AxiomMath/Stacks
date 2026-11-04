module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertySourceCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyUpToIsoInvariance
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffineCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryDiagramNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentability
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverNoetherian
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties

/-!
# The variant of Stacks 0ANG for locally Noetherian formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0ANI** calls a property `P` of
morphisms of `WAdm^{Noeth}`, the adic topological rings whose underlying ring is Noetherian, a
local property when the three axioms of Situation 0CBA hold for morphisms of `WAdm^{Noeth}`
(`TopologicalRing.PropertyIsLocalNoetherianUpToIso`, the completed corners of the diagrams of
axioms (1) and (2) being any rings isomorphic to the inverse limits `lim A'/IA'`), and asserts
that in exactly the same way as in Stacks 0ANG one obtains the equivalence of the three
conditions of Stacks 0ANG, read at the class `WAdm^{Noeth}`, for morphisms between locally
Noetherian formal algebraic spaces over `S`.

## The class of rings

The proof of Stacks 0ANG uses four facts about its class of rings, proved here for
`WAdm^{Noeth}`, `TopologicalRing.IsNoetherianAdic`:

* `AlgebraicGeometry.FormalSpace.classIsWeaklyAdmissible_isNoetherianAdic`: an adic ring is
  weakly admissible;
* `AlgebraicGeometry.FormalSpace.classHasCountableNhdsZero_isNoetherianAdic`: an adic ring has
  a countable fundamental system of neighbourhoods of zero;
* `AlgebraicGeometry.FormalSpace.classIsStableUnderEtaleCompletion_isNoetherianAdic`: clause (5)
  of **Stacks 0ANB**, the completion of an étale algebra over a ring of `WAdm^{Noeth}` is in
  `WAdm^{Noeth}`;
* `AlgebraicGeometry.FormalSpace.classIsStableUnderFinitePi_isNoetherianAdic`: a finite product
  of rings of `WAdm^{Noeth}` is in `WAdm^{Noeth}`, which is what makes axiom (3) of
  Situation 0CBA meaningful for `WAdm^{Noeth}`.

## Main results

* `AlgebraicGeometry.FormalSpace.isChartOfClass_isNoetherianAdic_of_isLocallyNoetherian`: an
  affine formal algebraic space representable étale over a locally Noetherian formal algebraic
  space is the formal spectrum of a ring of `WAdm^{Noeth}`.
* `AlgebraicGeometry.FormalSpace.hasProperty_tfae_isNoetherianAdic_of_isInvariantUnderIso`: the
  three conditions of the variant, for a property satisfying the literal axioms
  `TopologicalRing.PropertyIsLocalNoetherian` and invariant under isomorphism of source and of
  target.
* `AlgebraicGeometry.FormalSpace.hasProperty_tfae_of_isLocallyNoetherian`: **Stacks 0ANI**, the
  variant of Stacks 0ANG for morphisms of locally Noetherian formal algebraic spaces and a local
  property of `WAdm^{Noeth}`. The invariance under isomorphism is derived from axiom (1), as in
  the source, by `propertyIsInvariantUnderSourceIso_of_propertyIsLocalNoetherianUpToIso` and
  `propertyIsInvariantUnderTargetIsoOn_of_propertyIsLocalNoetherianUpToIso`.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0ANB](https://stacks.math.columbia.edu/tag/0ANB)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-! ### The class `WAdm^{Noeth}` -/

/-- The rings of `WAdm^{Noeth}` are weakly admissible, being adic. -/
theorem classIsWeaklyAdmissible_isNoetherianAdic :
    ClassIsWeaklyAdmissible.{u} TopologicalRing.IsNoetherianAdic :=
  fun _ _ _ _ _ h ↦ h.1.isWeaklyAdmissible

/-- The rings of `WAdm^{Noeth}` have countable fundamental systems of neighbourhoods of `0`: the
powers of an ideal of definition. -/
theorem classHasCountableNhdsZero_isNoetherianAdic :
    ClassHasCountableNhdsZero.{u} TopologicalRing.IsNoetherianAdic :=
  fun _ _ _ _ _ h ↦ Rig.countablyGenerated_nhds_of_isAdicRing h.1

/-- **Stacks 0ANB (5).** The completion of an étale algebra over a ring of `WAdm^{Noeth}` along
the weak ideals of definition of that ring is again in `WAdm^{Noeth}`: an étale algebra is of
finite type, hence Noetherian over a Noetherian ring, and
`TopologicalRing.completionOver_isNoetherianAdic` applies. -/
theorem classIsStableUnderEtaleCompletion_isNoetherianAdic :
    ClassIsStableUnderEtaleCompletion.{u} TopologicalRing.IsNoetherianAdic := by
  intro R R' _ _ _ _ _ ι hR _ hι
  let : Algebra R R' := ι.toAlgebra
  have : Algebra.Etale R R' := hι
  have : IsNoetherianRing R := hR.2
  exact TopologicalRing.completionOver_isNoetherianAdic ι hR
    (Algebra.FiniteType.isNoetherianRing R R')

/-- A finite product of rings of `WAdm^{Noeth}` is in `WAdm^{Noeth}`, for the product
topology: it is adic by `Rig.isAdic_pi`, and a finite product of Noetherian rings is
Noetherian. -/
theorem classIsStableUnderFinitePi_isNoetherianAdic :
    ClassIsStableUnderFinitePi.{u} TopologicalRing.IsNoetherianAdic := by
  intro K _ A _ _ _ _ h
  have : ∀ k, IsNoetherianRing (A k) := fun k ↦ (h k).2
  exact ⟨Rig.isAdic_pi A fun k ↦ (h k).1, inferInstance⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The charts of a locally Noetherian formal algebraic space are charts of the class
`WAdm^{Noeth}`.** An affine formal algebraic space representable étale over a locally
Noetherian formal algebraic space is Noetherian, by the implication (2) ⟹ (1) of Stacks 0AKX
(`AlgebraicGeometry.FormalSpace.hasChartsPresentedByClass_of_isLocallyNoetherian`), hence the
formal spectrum of its presenting ring, which is adic and Noetherian. -/
theorem isChartOfClass_isNoetherianAdic_of_isLocallyNoetherian {X : FppfSheaf B S hS}
    (hX : IsLocallyNoetherian B S hS X) (U : FppfSheaf B S hS) (a : U ⟶ X)
    (hU : IsAffineFormalAlgebraicSpace B S hS U) (ha : IsRepresentableEtale B S hS a) :
    IsChartOfClass B S hS TopologicalRing.IsNoetherianAdic U := by
  obtain ⟨PU, hPU⟩ := hasChartsPresentedByClass_of_isLocallyNoetherian B S hS hX U a hU ha
  exact ⟨PU.ring, _, _, _, _, hPU, PU.system, PU.iso⟩

/-! ### The variant of Stacks 0ANG -/

variable (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- The three conditions of the variant of **Stacks 0ANG** for morphisms of locally Noetherian
formal algebraic spaces (**Stacks 0ANI**), for a local property `P` of morphisms of
`WAdm^{Noeth}` which is invariant under isomorphism of sources and of targets.

The implication (1) ⟹ (2) takes the fibre products of condition (2) from the étale case of
Stacks 0AJH, `AlgebraicGeometry.FormalSpace.representableEtaleOverAffineIsFormal`; (2) ⟹ (3)
holds for any class and property; and (3) ⟹ (1) is
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocal`
at the class `WAdm^{Noeth}`, whose charts over a locally Noetherian formal algebraic space are
of the class by
`AlgebraicGeometry.FormalSpace.isChartOfClass_isNoetherianAdic_of_isLocallyNoetherian`. -/
theorem hasProperty_tfae_isNoetherianAdic_of_isInvariantUnderIso
    (hP : TopologicalRing.PropertyIsLocalNoetherian.{u} P)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u} TopologicalRing.IsNoetherianAdic P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsNoetherianAdic P)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y) :
    List.TFAE
      [ HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P f,
        HasPropertyAfterTargetCover B S hS TopologicalRing.IsNoetherianAdic P f,
        HasPropertyAfterSourceCover B S hS TopologicalRing.IsNoetherianAdic P f ] := by
  have hEt : RepresentableEtaleOverAffineIsFormal B S hS :=
    representableEtaleOverAffineIsFormal B S hS
  tfae_have 1 → 2 := fun h ↦
    hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS _ P f hY.1
      (isFormalAlgebraicSpace_pullback_chart_of_etale B S hS hEt hX.1 hY.1) h
  tfae_have 2 → 3 := fun h ↦ hasPropertyAfterSourceCover_of_afterTargetCover B S hS _ P f h
  tfae_have 3 → 1 := fun h ↦
    hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocal B S hS _ P
      classIsWeaklyAdmissible_isNoetherianAdic classHasCountableNhdsZero_isNoetherianAdic
      classIsStableUnderEtaleCompletion_isNoetherianAdic
      classIsStableUnderFinitePi_isNoetherianAdic hsrc htgt hP f
      (hasEtaleRefinementOfSourceCover_of_etale B S hS hEt f)
      (hasPropertyAfterSourceCoverOfClass_of_afterSourceCover B S hS _ P f
        (isChartOfClass_isNoetherianAdic_of_isLocallyNoetherian B S hS hX)
        (isChartOfClass_isNoetherianAdic_of_isLocallyNoetherian B S hS hY) h)
  tfae_finish

/-- **Stacks 0ANI, the variant of Stacks 0ANG for locally Noetherian formal algebraic spaces.**
Let `S` be a scheme, let `f : X ⟶ Y` be a morphism of locally Noetherian formal algebraic spaces
over `S`, and let `P` be a local property of morphisms of `WAdm^{Noeth}`: axioms (1), (2) and (3)
of Situation 0CBA hold for morphisms of `WAdm^{Noeth}`
(`TopologicalRing.PropertyIsLocalNoetherianUpToIso`). The following are equivalent:

1. for every commutative diagram with `U` and `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, the morphism `U ⟶ V` corresponds to a
   morphism of `WAdm^{Noeth}` with property `P`;
2. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM such that each `Xⱼᵢ ⟶ Yⱼ` corresponds to a
   morphism of `WAdm^{Noeth}` with property `P`;
3. there are a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` with `Yᵢ` an affine formal algebraic space, `Yᵢ ⟶ Y` representable by
   algebraic spaces and étale, and `Xᵢ ⟶ Yᵢ` corresponding to a morphism of `WAdm^{Noeth}` with
   property `P`.

"Corresponds to a morphism of `WAdm^{Noeth}` with property `P`" is
`AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap` at the class
`TopologicalRing.IsNoetherianAdic`. This is
`AlgebraicGeometry.FormalSpace.hasProperty_tfae_isNoetherianAdic_of_isInvariantUnderIso`, with the
invariance of `P` under isomorphism of source and of target derived from axiom (1). -/
@[stacks 0ANI "the variant of Lemma 0ANG for morphisms between locally Noetherian formal \
algebraic spaces over S: the equivalence of its three conditions, for a local property of \
morphisms of WAdm^Noeth"]
theorem hasProperty_tfae_of_isLocallyNoetherian
    (hP : TopologicalRing.PropertyIsLocalNoetherianUpToIso.{u} P)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y) :
    List.TFAE
      [ HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P f,
        HasPropertyAfterTargetCover B S hS TopologicalRing.IsNoetherianAdic P f,
        HasPropertyAfterSourceCover B S hS TopologicalRing.IsNoetherianAdic P f ] :=
  hasProperty_tfae_isNoetherianAdic_of_isInvariantUnderIso B S hS P hP.toPropertyIsLocal
    (propertyIsInvariantUnderSourceIso_of_propertyIsLocalNoetherianUpToIso P hP)
    (propertyIsInvariantUnderTargetIsoOn_of_propertyIsLocalNoetherianUpToIso P hP) f hX hY

end AlgebraicGeometry.FormalSpace

end
