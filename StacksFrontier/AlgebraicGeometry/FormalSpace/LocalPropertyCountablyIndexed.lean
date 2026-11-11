module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineEtaleChartTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ChartLocalizationDiagram
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedPullbackProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertySourceCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffineCharts
public import StacksFrontier.RingTheory.Rig.RigSmoothStability
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdicProduct

/-!
# Stacks 0ANG for locally countably indexed formal algebraic spaces

This file instantiates the class-generic results on local properties of morphisms of formal
algebraic spaces at the class `WAdm^count` of countably indexed weakly admissible topological
rings, which is the class of **Stacks 0ANG**.

## Main results

* `AlgebraicGeometry.FormalSpace.classIsWeaklyAdmissible_isCountablyWeaklyAdmissible` and
  `AlgebraicGeometry.FormalSpace.classIsStableUnderEtaleCompletion_isCountablyWeaklyAdmissible`:
  the class `WAdm^count` consists of weakly admissible rings and is stable under completion along
  an étale ring map (Stacks 0ANB).
* `AlgebraicGeometry.FormalSpace.isCountablyWeaklyAdmissible_pi`: `WAdm^count` is stable under
  finite products.
* `AlgebraicGeometry.FormalSpace.hasProperty_tfae_of_isLocallyCountablyIndexed`:
  the equivalence of the three conditions of Stacks 0ANG, with the invariance of `P` under
  isomorphism of sources and of targets as two arguments; Stacks 0ANG itself, for Situation
  0CBA's notion of a local property, is
  `AlgebraicGeometry.FormalSpace.hasProperty_tfae_of_isLocallyCountablyIndexed_of_isLocal`.

## References

* [Stacks Project, Tag 0ANB](https://stacks.math.columbia.edu/tag/0ANB)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-- The rings of `WAdm^count` are weakly admissible. -/
theorem classIsWeaklyAdmissible_isCountablyWeaklyAdmissible :
    ClassIsWeaklyAdmissible.{u} TopologicalRing.IsCountablyWeaklyAdmissible :=
  fun _ _ _ _ _ h ↦ h.1

/-- **Stacks 0ANB** for `WAdm^count`: the completion of an étale algebra over a ring of
`WAdm^count` along the weak ideals of definition of that ring is again in `WAdm^count`. -/
theorem classIsStableUnderEtaleCompletion_isCountablyWeaklyAdmissible :
    ClassIsStableUnderEtaleCompletion.{u} TopologicalRing.IsCountablyWeaklyAdmissible :=
  fun ι hC _ _ ↦ ⟨TopologicalRing.completionOver_isWeaklyAdmissible ι hC.1,
    TopologicalRing.completionOver_isCountablyGenerated_nhds_zero ι hC.1 hC.2⟩

/-- A finite product of rings of `WAdm^count` is in `WAdm^count`, for the product topology:
weak admissibility is `TopologicalRing.isWeaklyAdmissible_pi`, and the neighbourhood filter of
`0` in a countable product is the product of the neighbourhood filters, countably generated
when each of them is. -/
theorem isCountablyWeaklyAdmissible_pi {K : Type u} [Finite K] (A : K → Type u)
    [∀ k, CommRing (A k)] [∀ k, TopologicalSpace (A k)] [∀ k, IsTopologicalRing (A k)]
    [∀ k, IsLinearTopology (A k) (A k)]
    (h : ∀ k, TopologicalRing.IsCountablyWeaklyAdmissible (A k)) :
    letI : IsLinearTopology (∀ k, A k) (∀ k, A k) := TopologicalRing.pi_isLinearTopology
    TopologicalRing.IsCountablyWeaklyAdmissible (∀ k, A k) := by
  let : IsLinearTopology (∀ k, A k) (∀ k, A k) := TopologicalRing.pi_isLinearTopology
  refine ⟨TopologicalRing.isWeaklyAdmissible_pi A fun k ↦ (h k).1, ?_⟩
  have : ∀ k, (nhds (0 : A k)).IsCountablyGenerated := fun k ↦ (h k).2
  rw [show (0 : ∀ k, A k) = fun k ↦ (0 : A k) from rfl, nhds_pi]
  infer_instance

/-- The rings of `WAdm^count` have countable fundamental systems of neighbourhoods of `0`. -/
theorem classHasCountableNhdsZero_isCountablyWeaklyAdmissible :
    ClassHasCountableNhdsZero.{u} TopologicalRing.IsCountablyWeaklyAdmissible :=
  fun _ _ _ _ _ h ↦ h.2

/-- `WAdm^count` is stable under finite products. -/
theorem classIsStableUnderFinitePi_isCountablyWeaklyAdmissible :
    ClassIsStableUnderFinitePi.{u} TopologicalRing.IsCountablyWeaklyAdmissible :=
  fun A _ _ _ _ h ↦ isCountablyWeaklyAdmissible_pi A h

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The assembly of Stacks 0ANG -/

variable (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- The three conditions of **Stacks 0ANG** for a morphism of locally countably indexed formal
algebraic spaces, a local property `P` of morphisms of `WAdm^count` invariant under isomorphism
of sources and targets, assembled from one statement about formal algebraic spaces which does not
mention `P`: the étale case of Stacks 0AJH, `hEt`. Through it the implication (2) ⟹ (1) of
Stacks 0AKX for countable indexing makes every chart of a locally countably indexed formal
algebraic space countably indexed, and the fibre products of the argument formal algebraic
spaces. -/
theorem hasProperty_tfae_isCountablyWeaklyAdmissible_of_etale
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    (hP : TopologicalRing.PropertyIsLocal P TopologicalRing.IsCountablyWeaklyAdmissible)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u} TopologicalRing.IsCountablyWeaklyAdmissible P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsCountablyWeaklyAdmissible P)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y) :
    List.TFAE
      [ HasPropertyOnEveryAffineEtaleDiagram B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible P f,
        HasPropertyAfterTargetCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P f,
        HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P f ] := by
  have hchart : ∀ {Z : FppfSheaf B S hS}, IsLocallyCountablyIndexed B S hS Z →
      ∀ (U : FppfSheaf B S hS) (a : U ⟶ Z), IsAffineFormalAlgebraicSpace B S hS U →
        IsRepresentableEtale B S hS a →
          IsChartOfClass B S hS TopologicalRing.IsCountablyWeaklyAdmissible U :=
    fun hZ U a hU ha ↦ isChartOfClass_isCountablyWeaklyAdmissible_of_isCountablyIndexed B S hS
      ((hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_of_mem B S hS _ hZ.1 _
        (Or.inl rfl)).2 hZ.2 U a hU ha)
  tfae_have 1 → 2 := fun h ↦
    hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS _ P f hY.1
      (isFormalAlgebraicSpace_pullback_chart_of_etale B S hS hEt hX.1 hY.1) h
  tfae_have 2 → 3 := fun h ↦ hasPropertyAfterSourceCover_of_afterTargetCover B S hS _ P f h
  tfae_have 3 → 1 := by
    rintro ⟨I, U, u, hcover, hfac⟩
    refine hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocal B S hS _ P
      classIsWeaklyAdmissible_isCountablyWeaklyAdmissible
      classHasCountableNhdsZero_isCountablyWeaklyAdmissible
      classIsStableUnderEtaleCompletion_isCountablyWeaklyAdmissible
      classIsStableUnderFinitePi_isCountablyWeaklyAdmissible hsrc htgt hP f
      (hasEtaleRefinementOfSourceCover_of_etale B S hS hEt f)
      ⟨I, U, u, hcover, fun i ↦ ?_⟩
    obtain ⟨V, v, t, hV, hv, hsq, hPt⟩ := hfac i
    exact ⟨V, v, t, hV, hv, hsq, hchart hX (U i) (u i) (hcover.1 i) (hcover.2.1 i),
      hchart hY V v hV hv, hPt⟩
  tfae_finish

/-- **Stacks 0ANG.** Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of locally
countably indexed formal algebraic spaces over `S`. Let `P` be a local property of morphisms of
`WAdm^count`, the countably indexed weakly admissible topological rings (Situation 0CBA: `P` is
invariant under isomorphism of source and target, and satisfies the three axioms 0AND, 0ANE and
0ANF of `TopologicalRing.PropertyIsLocal`). The following are equivalent:

1. for every commutative diagram with `U` and `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, the morphism `U ⟶ V` corresponds to a
   morphism of `WAdm^count` with property `P`;
2. there is a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Uᵢ ⟶ Vⱼ ×_Y X}` as in Definition 0AIM such that each `Uᵢ ⟶ Vⱼ` corresponds to a morphism of
   `WAdm^count` with property `P`;
3. there are a covering `{Uᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Uᵢ ⟶ Vᵢ ⟶ Y` where `Vᵢ` is an affine formal algebraic space, `Vᵢ ⟶ Y` is representable by
   algebraic spaces and étale, and `Uᵢ ⟶ Vᵢ` corresponds to a morphism of `WAdm^count` with
   property `P`.

"Corresponds to a morphism of `WAdm^count` with property `P`" is
`AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap`: `P` holds on every continuous
homomorphism presenting the morphism of formal spectra through rings of `WAdm^count`.

This is `AlgebraicGeometry.FormalSpace.hasProperty_tfae_isCountablyWeaklyAdmissible_of_etale` at
the étale case of Stacks 0AJH,
`AlgebraicGeometry.FormalSpace.representableEtaleOverAffineIsFormal`. The form taking the
invariance clause of Situation 0CBA in the single form `TopologicalRing.PropertyIsLocal'` is
`AlgebraicGeometry.FormalSpace.hasProperty_tfae_of_isLocallyCountablyIndexed_of_isLocal`. -/
theorem hasProperty_tfae_of_isLocallyCountablyIndexed
    (hP : TopologicalRing.PropertyIsLocal P TopologicalRing.IsCountablyWeaklyAdmissible)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u} TopologicalRing.IsCountablyWeaklyAdmissible P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsCountablyWeaklyAdmissible P)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y) :
    List.TFAE
      [ HasPropertyOnEveryAffineEtaleDiagram B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible P f,
        HasPropertyAfterTargetCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P f,
        HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P f ] :=
  hasProperty_tfae_isCountablyWeaklyAdmissible_of_etale B S hS P
    (representableEtaleOverAffineIsFormal B S hS) hP hsrc htgt f hX hY

end AlgebraicGeometry.FormalSpace

end
