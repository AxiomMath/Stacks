module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
public import StacksFrontier.RingTheory.AdicCompletion.KerEval

/-!
# The completion of an affine scheme along a finitely generated zero locus

Let `S` be a scheme contained in a big fppf site `B`, let `X = Spec A` be an affine scheme
over `S` lying in that site, and let `T = V(I) ⊆ X` be the zero locus of an ideal `I ⊆ A`.
When `I` is finitely generated, **Stacks 0GBA (2)** identifies the formal completion
`X_{/T}` with the affine formal spectrum `Spf (A^∧)` of the `I`-adic completion of `A`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.affineOver` is `Spec A` viewed as an object of the big fppf
  site over `S`.
* `AlgebraicGeometry.FormalSpace.zeroLocusPoints` is the zero locus `V(I)`, transported to
  the point set of the presheaf represented by `Spec A`.
* `AlgebraicGeometry.FormalSpace.AdicQuotientSystem` and
  `AlgebraicGeometry.FormalSpace.QuotientSystemCompatible` are the data presenting the
  `I`-adic completion of `A` as a topological ring over `S`, and the requirement that the
  presentation induce the structure maps coming from `Spec A`.
* `AlgebraicGeometry.FormalSpace.quotientStageToAffine` is the morphism `Spec (A^∧ ⧸ J) ⟶
  Spec A` induced by the completion homomorphism `A → A^∧`, and
  `AlgebraicGeometry.FormalSpace.quotientStageToCompletion` the resulting morphism from the
  quotient stage into the completion `X_{/T}`.
* `AlgebraicGeometry.FormalSpace.completionComparison` is the canonical morphism
  `Spf (A^∧) ⟶ X_{/T}`, assembled from the quotient stages.

## Main results

* `AlgebraicGeometry.FormalSpace.isIso_completionComparison`: **Stacks 0GBA (2)**, the
  canonical comparison `Spf (A^∧) ⟶ X_{/T}` is an isomorphism.
* `AlgebraicGeometry.FormalSpace.completionComparison_stage` and
  `AlgebraicGeometry.FormalSpace.completionComparison_overAffine` describe the comparison on
  a quotient stage: it restricts to the canonical section there, and its composite with the
  inclusion `X_{/T} ⟶ X` is the morphism induced by `A → A^∧ ⧸ J`.
* `AlgebraicGeometry.FormalSpace.quotientStage_hasImageIn`: each quotient stage of `A^∧` is
  supported on `V(I)`, which is why it maps to the completion at all.

## Implementation notes

The source's assertion is an equality of formal algebraic spaces over `S`; here it is the
statement that an explicitly constructed comparison morphism of fppf sheaves is an
isomorphism.

A quotient-system presentation `D` of `A^∧` is a hypothesis rather than a construction,
because `AlgebraicGeometry.FormalSpace.QuotientSystem` requires every quotient spectrum
`Spec (A^∧ ⧸ J)` to lie in the chosen big fppf site, which a given site need not satisfy.
The compatibility hypothesis then demands that the structure map of each stage be the one
induced by `A → A^∧ ⧸ J` followed by `Spec A ⟶ S`, which is what makes the comparison a
morphism over `Spec A`; both are site-smallness data about the base, not mathematical input.

Finite generation of `I` enters twice. It identifies the kernel of `A^∧ → A ⧸ I^n` with the
extension of `I^n` (`AdicCompletion.pow_smul_top_eq_ker_eval`), whence each quotient
`A^∧ ⧸ J` by a weak ideal of definition is already a quotient of `A`; and it turns the
set-theoretic containment of the image of an affine `U ⟶ X` in `V(I)` into an actual power
`I^n ⊆ ker (A → Γ(U))`, which is what produces the factorization through a stage. These are
`AlgebraicGeometry.FormalSpace.quotient_completionMap_surjective` and
`AlgebraicGeometry.FormalSpace.exists_quotientStage_factor`.

Surjectivity on sections is then proved by cover-density: the affine objects of the site
generate the fppf topology, so a morphism out of the sheafification `X_{/T}` is determined by
its values on sections over affines, and over an affine every supported section factors
through some quotient stage. The factorization is unique up to the stage because each
`Spec (A^∧ ⧸ J) ⟶ Spec A` is a closed immersion, hence a monomorphism, so two factorizations
agree after passing to the intersection of the two ideals.

Closedness of `T` is never used: the zero locus of any ideal is closed, and the completion is
formed for an arbitrary set of points.

## References

* [Stacks Project, Tag 0GBA](https://stacks.math.columbia.edu/tag/0GBA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Filter

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

/-- An affine scheme over the base, viewed as an object of the chosen big fppf site. -/
def affineOver (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S) :
    BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk f : B.obj hA ⟶ B.obj hS)

/-- The zero locus `V(I)`, as a set of points of the presheaf represented by `Spec A`: a
point lies in it when the underlying scheme point of every field-valued representative of it
lies in `V(I)`. -/
def zeroLocusPoints (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S)
    (I : Ideal A) :
    Set (Space.points B S hS (yoneda.obj (affineOver B S hS hA f))) :=
  {x | ∀ p : Space.FieldValuedPoint B S hS
      (yoneda.obj (affineOver B S hS hA f)),
    p.class B S hS (yoneda.obj (affineOver B S hS hA f)) = x →
      Space.schemePoint B S hS (affineOver B S hS hA f) p ∈
        PrimeSpectrum.zeroLocus (I : Set A)}

/-- A presentation of the `I`-adic completion of `A`, carrying the `I`-adic topology, as a
topological ring over the base: a structure morphism for each of its quotient spectra by a
weak ideal of definition, each such spectrum lying in the site. -/
abbrev AdicQuotientSystem (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {A : Type u} [CommRing A]
    (I : Ideal A) :=
  @QuotientSystem B S hS (AdicCompletion I A) _
    (I.adicModuleTopology (AdicCompletion I A))

/-- The requirement that a presentation of the `I`-adic completion of `A` have the structure
morphisms induced by `Spec A ⟶ S`: on each quotient stage the structure morphism is the one
coming from the ring map `A → A^∧ ⧸ J`. -/
abbrev QuotientSystemCompatible
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A : Type u} [CommRing A]
    (f : Spec (.of A) ⟶ S) (I : Ideal A)
    (D : AdicQuotientSystem B S hS I) : Prop :=
    letI : TopologicalSpace (AdicCompletion I A) :=
        I.adicModuleTopology (AdicCompletion I A);
    ∀ J : { K : Ideal (AdicCompletion I A) //
        @TopologicalRing.IsWeakIdealOfDefinition _ _
          (I.adicModuleTopology (AdicCompletion I A)) K },
      D.overS J =
        Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk J.1).comp
            (algebraMap A (AdicCompletion I A)))) ≫ f

variable (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) {A : Type u} [CommRing A]
  (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S)
  (I : Ideal A)

/-- The `I`-adic topology on the `I`-adic completion `A^∧`, viewed as an `A`-module. -/
local instance : TopologicalSpace (AdicCompletion I A) :=
  I.adicModuleTopology (AdicCompletion I A)

/-- A weak ideal of definition of `A^∧` contains the extension of some power of `I`, because
the extended powers of `I` form a neighbourhood basis of zero. -/
private theorem exists_adic_power_map_le
    (J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K }) :
    ∃ n : ℕ, Ideal.map (algebraMap A (AdicCompletion I A)) (I ^ n) ≤ J.1 := by
  let : TopologicalSpace A := I.adicTopology
  let b : ModuleFilterBasis A (AdicCompletion I A) :=
    I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis (AdicCompletion I A))
  have hopen : (J.1 : Set (AdicCompletion I A)) ∈ nhds (0 : AdicCompletion I A) :=
    J.2.1.mem_nhds J.1.zero_mem
  obtain ⟨V, hV, hsub⟩ :=
    b.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp hopen
  obtain ⟨n, rfl⟩ : ∃ n : ℕ,
      V = ((I ^ n • (⊤ : Submodule A (AdicCompletion I A)) : Submodule A _)
        : Set (AdicCompletion I A)) := by
    change V ∈ b.toAddGroupFilterBasis.sets at hV
    exact hV
  refine ⟨n, ?_⟩
  intro x hx
  apply hsub
  have hx' : x ∈ (I ^ n • (⊤ : Submodule A (AdicCompletion I A))) := by
    rw [Ideal.smul_top_eq_map]
    exact hx
  exact hx'

/-- Every point of a quotient spectrum `Spec (A^∧ ⧸ J)` maps into `V(I)` under the morphism
induced by `A → A^∧ ⧸ J`: a power of `I` dies in `A^∧ ⧸ J`, so `I` lands in every prime. -/
private theorem quotientPrime_mem_zeroLocus
    (J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K })
    (x : PrimeSpectrum (AdicCompletion I A ⧸ J.1)) :
    PrimeSpectrum.comap
        ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A))) x ∈
      PrimeSpectrum.zeroLocus (I : Set A) := by
  obtain ⟨n, hn⟩ := exists_adic_power_map_le (A := A) I J
  change ∀ a, a ∈ (I : Set A) →
    ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A))) a ∈ x.asIdeal
  intro a ha
  apply x.isPrime.mem_of_pow_mem n
  change ((Ideal.Quotient.mk J.1).comp
    (algebraMap A (AdicCompletion I A))) a ^ n ∈ x.asIdeal
  rw [← map_pow]
  have hzero : Ideal.Quotient.mk J.1 (algebraMap A (AdicCompletion I A) (a ^ n)) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).2 (hn
      (Ideal.mem_map_of_mem (algebraMap A (AdicCompletion I A))
        (Ideal.pow_mem_pow ha n)))
  change Ideal.Quotient.mk J.1 (algebraMap A (AdicCompletion I A) (a ^ n)) ∈ x.asIdeal
  rw [hzero]
  exact x.asIdeal.zero_mem

/-- A field-valued point of a represented presheaf on the site, read as a field-valued point
of the representing scheme itself. -/
private def absoluteFieldValuedPoint
    (U : BigFppfOver B S hS)
    (p : Space.FieldValuedPoint B S hS (yoneda.obj U)) :
    AlgebraicGeometry.FieldValuedPoint ((BigFppfOver.toScheme B S hS).obj U) where
  carrier := p.carrier
  field := p.field
  map := B.inclusion.map p.value.left

/-- Two field-valued points of a represented presheaf which define the same point of it have
the same underlying scheme point: a common extension over the site becomes a common extension
of the associated field-valued points of the scheme. -/
private theorem schemePoint_eq_of_class_eq
    (U : BigFppfOver B S hS)
    (p q : Space.FieldValuedPoint B S hS (yoneda.obj U))
    (h : p.class B S hS (yoneda.obj U) = q.class B S hS (yoneda.obj U)) :
    Space.schemePoint B S hS U p = Space.schemePoint B S hS U q := by
  change (absoluteFieldValuedPoint B S hS U p).point =
    (absoluteFieldValuedPoint B S hS U q).point
  obtain ⟨r, hpr, hqr⟩ :=
    (Space.FieldValuedPoint.class_eq_class_iff B S hS (yoneda.obj U) p q).1 h
  obtain ⟨f, hf⟩ := hpr
  obtain ⟨g, hg⟩ := hqr
  change f ≫ p.value = r.value at hf
  change g ≫ q.value = r.value at hg
  have hdom (s : Space.FieldValuedPoint B S hS (yoneda.obj U))
      (k : r.siteObject B S hS (yoneda.obj U) ⟶ s.siteObject B S hS (yoneda.obj U))
      (hk : k ≫ s.value = r.value) :
      (absoluteFieldValuedPoint B S hS U r).Dominates
        (absoluteFieldValuedPoint B S hS U s) := by
    refine ⟨B.inclusion.map k.left, ?_⟩
    exact congrArg (fun t => B.inclusion.map t.left) hk
  have hcommon :
      (absoluteFieldValuedPoint B S hS U p).HasCommonExtension
        (absoluteFieldValuedPoint B S hS U q) :=
    ⟨absoluteFieldValuedPoint B S hS U r, hdom p f hf, hdom q g hg⟩
  exact (AlgebraicGeometry.FieldValuedPoint.hasCommonExtension_iff_point_eq _ _).mp hcommon

/-- The morphism `Spec (A^∧ ⧸ J) ⟶ Spec A` over `S` induced by the completion homomorphism
`A → A^∧` followed by the quotient map. -/
def quotientStageToAffine (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    (J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K }) :
    ((BigAffineFppf.inclusion B S hS).obj (D.stage J)) ⟶
      affineOver B S hS hA f :=
  Over.homMk (U := (D.stage J).1)
    (V := affineOver B S hS hA f)
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A))))))
    (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A)))) ≫ f =
          D.overS J
      exact (hD J).symm)

/-- The morphisms to `Spec A` are compatible with the transition morphisms of the quotient
system. -/
private theorem quotientStageToAffine_transition
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    {J K : { L : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) L }}
    (h : K.1 ≤ J.1) :
      ((BigAffineFppf.inclusion B S hS).map (D.transition h)) ≫
        quotientStageToAffine B S hS hA f I D hD K =
      quotientStageToAffine B S hS hA f I D hD J := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
      Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk K.1).comp (algebraMap A (AdicCompletion I A)))) =
    Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A))))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change (Ideal.Quotient.factor h)
      (Ideal.Quotient.mk K.1 (algebraMap A (AdicCompletion I A) x)) =
    Ideal.Quotient.mk J.1 (algebraMap A (AdicCompletion I A) x)
  exact Ideal.Quotient.factor_mk h (algebraMap A (AdicCompletion I A) x)

/-- Each quotient stage of `A^∧` is supported on `V(I)`: its morphism to `Spec A` has
point-set image inside the zero locus of `I`. -/
theorem quotientStage_hasImageIn
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    (J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K }) :
    Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)
      ((BigAffineFppf.inclusion B S hS).obj (D.stage J))
      (quotientStageToAffine B S hS hA f I D hD J) := by
  change ∀ p : Space.FieldValuedPoint B S hS
      (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.stage J))),
    (⟨p.carrier, p.contained, p.toBase,
      (yoneda.obj (affineOver B S hS hA f)).map p.value.op
        (quotientStageToAffine B S hS hA f I D hD J)⟩ :
      Space.FieldValuedPoint B S hS (yoneda.obj (affineOver B S hS hA f))).class
        B S hS (yoneda.obj (affineOver B S hS hA f)) ∈
          zeroLocusPoints B S hS hA f I
  intro p
  let r : Space.FieldValuedPoint B S hS (yoneda.obj (affineOver B S hS hA f)) :=
    Space.FieldValuedPoint.map B S hS
      (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.stage J)))
      (yoneda.map (quotientStageToAffine B S hS hA f I D hD J)) p
  change ∀ q : Space.FieldValuedPoint B S hS
      (yoneda.obj (affineOver B S hS hA f)),
    q.class B S hS (yoneda.obj (affineOver B S hS hA f)) =
        r.class B S hS (yoneda.obj (affineOver B S hS hA f)) →
      Space.schemePoint B S hS (affineOver B S hS hA f) q ∈
        PrimeSpectrum.zeroLocus (I : Set A)
  intro q hq
  have hr : Space.schemePoint B S hS (affineOver B S hS hA f) r ∈
      PrimeSpectrum.zeroLocus (I : Set A) := by
    change (BigFppfOver.toScheme B S hS).map
        (quotientStageToAffine B S hS hA f I D hD J)
        (Space.schemePoint B S hS
          ((BigAffineFppf.inclusion B S hS).obj (D.stage J)) p) ∈ _
    change PrimeSpectrum.comap
        ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A)))
        (Space.schemePoint B S hS
          ((BigAffineFppf.inclusion B S hS).obj (D.stage J)) p) ∈ _
    exact quotientPrime_mem_zeroLocus (A := A) I J _
  have hpoint := schemePoint_eq_of_class_eq B S hS
    (affineOver B S hS hA f) q r hq
  rw [hpoint]
  exact hr

/-- The section of the completion `X_{/T}` over a quotient stage given by that stage's
morphism to `Spec A`, which is supported on `T = V(I)`. -/
def quotientStageSection
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    (J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K }) :
    (Space.completionSheaf B S hS
      (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).obj.obj
        (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (D.stage J))) :=
  (GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
    (Space.completionSubfunctor B S hS
      (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).toFunctor).app
      (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (D.stage J)))
      ⟨⟨quotientStageToAffine B S hS hA f I D hD J⟩,
        quotientStage_hasImageIn B S hS hA f I D hD J⟩

/-- Restricting the sheafification of a supported section along `k : V ⟶ U` gives the
sheafification of any supported section over `V` equal to the pullback of the original. -/
private theorem sheafify_map_toSheafify_eq {U V : BigFppfOver B S hS} (k : V ⟶ U)
    (x : (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).toFunctor.obj (Opposite.op U))
    (y : (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).toFunctor.obj (Opposite.op V))
    (h : k ≫ x.1.down = y.1.down) :
    ((BigFppfOver.topology B S hS).sheafify (Space.completionSubfunctor B S hS
      (yoneda.obj (affineOver B S hS hA f)) (zeroLocusPoints B S hS hA f I)).toFunctor).map
      k.op
      ((GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
        (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
          (zeroLocusPoints B S hS hA f I)).toFunctor).app (Opposite.op U) x) =
    (GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
      (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
        (zeroLocusPoints B S hS hA f I)).toFunctor).app (Opposite.op V) y := by
  rw [← NatTrans.naturality_apply (GrothendieckTopology.toSheafify
    (BigFppfOver.topology B S hS) (Space.completionSubfunctor B S hS
      (yoneda.obj (affineOver B S hS hA f)) (zeroLocusPoints B S hS hA f I)).toFunctor) k.op]
  congr 1
  apply Subtype.ext
  apply ULift.ext
  exact h

/-- The canonical sections over the quotient stages are compatible with restriction along the
transition morphisms. -/
private theorem quotientStageSection_transition
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    {J K : { L : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) L }}
    (h : K.1 ≤ J.1) :
    (Space.completionSheaf B S hS
      (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).obj.map
      ((BigAffineFppf.inclusion B S hS).map (D.transition h)).op
      (quotientStageSection B S hS hA f I D hD K) =
    quotientStageSection B S hS hA f I D hD J := by
  exact sheafify_map_toSheafify_eq B S hS hA f I _
    ⟨ULift.up (quotientStageToAffine B S hS hA f I D hD K),
      quotientStage_hasImageIn B S hS hA f I D hD K⟩
    ⟨ULift.up (quotientStageToAffine B S hS hA f I D hD J),
      quotientStage_hasImageIn B S hS hA f I D hD J⟩
    (quotientStageToAffine_transition B S hS hA f I D hD h)

/-- The morphism from a quotient stage of `A^∧` into the completion `X_{/T}`, corresponding
under Yoneda's lemma for sheaves to the canonical section over that stage. -/
def quotientStageToCompletion
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    (J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K }) :
    (formalSpectrumDiagram D).obj (OrderDual.toDual J) ⟶
      Space.completionSheaf B S hS
        (yoneda.obj (affineOver B S hS hA f))
        (zeroLocusPoints B S hS hA f I) :=
  (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
    (quotientStageSection B S hS hA f I D hD J)

/-- Under Yoneda for sheaves, the morphism of a quotient stage into the completion corresponds
to the canonical section over that stage. -/
private theorem sectionEquiv_quotientStageToCompletion
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    (J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K }) :
    Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        (quotientStageToCompletion B S hS hA f I D hD J) =
      quotientStageSection B S hS hA f I D hD J :=
  Equiv.apply_symm_apply _ _

/-- The morphisms from the quotient stages into the completion form a cocone on the diagram
whose colimit is `Spf (A^∧)`. -/
theorem quotientStageToCompletion_naturality
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    {J K : OrderDual { L : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) L }}
    (g : J ⟶ K) :
    (formalSpectrumDiagram D).map g ≫
      quotientStageToCompletion B S hS hA f I D hD K.ofDual =
      quotientStageToCompletion B S hS hA f I D hD J.ofDual := by
  have hsec := quotientStageSection_transition B S hS hA f I D hD
    (J := J.ofDual) (K := K.ofDual) (leOfHom g)
  have hmap := congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm hsec
  rw [Sheaf.sectionEquiv_symm_map] at hmap
  change (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map (D.transition (leOfHom g))) ≫
        (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
          (quotientStageSection B S hS hA f I D hD K.ofDual) =
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
      (quotientStageSection B S hS hA f I D hD J.ofDual)
  exact hmap

/-- The cocone on the diagram of quotient stages whose vertex is the completion `X_{/T}`. -/
def completionCocone
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D) :
    Cocone (formalSpectrumDiagram D) where
  pt := Space.completionSheaf B S hS
    (yoneda.obj (affineOver B S hS hA f))
    (zeroLocusPoints B S hS hA f I)
  ι := {
    app J := quotientStageToCompletion B S hS hA f I D hD J.ofDual
    naturality _ _ g :=
      (quotientStageToCompletion_naturality B S hS hA f I D hD g).trans
        (Category.comp_id _).symm
  }

/-- The canonical comparison morphism `Spf (A^∧) ⟶ X_{/T}` from the formal spectrum of the
`I`-adic completion to the completion of `Spec A` along `V(I)`, induced by the cocone of
quotient stages. -/
def completionComparison
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D) :
    formalSpectrum D ⟶
      Space.completionSheaf B S hS
        (yoneda.obj (affineOver B S hS hA f))
        (zeroLocusPoints B S hS hA f I) :=
  colimit.desc (formalSpectrumDiagram D)
    (completionCocone B S hS hA f I D hD)

/-- On each quotient stage the comparison restricts to that stage's canonical morphism into
the completion. -/
theorem completionComparison_stage
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    (J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K }) :
    formalSpectrumInclusion D (OrderDual.toDual J) ≫
      completionComparison B S hS hA f I D hD =
      quotientStageToCompletion B S hS hA f I D hD J :=
  colimit.ι_desc (completionCocone B S hS hA f I D hD) (OrderDual.toDual J)

/-- On each quotient stage, the comparison followed by the inclusion of the completion into
`Spec A` is the section given by the morphism `Spec (A^∧ ⧸ J) ⟶ Spec A` induced by
`A → A^∧`. -/
theorem completionComparison_overAffine
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    (J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K }) :
    Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      (formalSpectrumInclusion D (OrderDual.toDual J) ≫
        completionComparison B S hS hA f I D hD ≫
        Space.completionSheafInclusion B S hS
          (yoneda.obj (affineOver B S hS hA f))
          (zeroLocusPoints B S hS hA f I)) =
      (GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
        (yoneda.obj (affineOver B S hS hA f) ⋙ uliftFunctor.{u + 1})).app
          (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (D.stage J)))
          ⟨quotientStageToAffine B S hS hA f I D hD J⟩ := by
  have hassoc := (Category.assoc (formalSpectrumInclusion D (OrderDual.toDual J))
      (completionComparison B S hS hA f I D hD)
      (Space.completionSheafInclusion B S hS
        (yoneda.obj (affineOver B S hS hA f))
        (zeroLocusPoints B S hS hA f I))).symm.trans
    (congrArg (fun t => t ≫ Space.completionSheafInclusion B S hS
        (yoneda.obj (affineOver B S hS hA f))
        (zeroLocusPoints B S hS hA f I))
      (completionComparison_stage B S hS hA f I D hD J))
  have hsec := sectionEquiv_quotientStageToCompletion B S hS hA f I D hD J
  refine Eq.trans ((congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)) hassoc).trans
    ((Sheaf.sectionEquiv_comp (BigFppfOver.topology B S hS)
          (quotientStageToCompletion B S hS hA f I D hD J)
          (Space.completionSheafInclusion B S hS
            (yoneda.obj (affineOver B S hS hA f))
            (zeroLocusPoints B S hS hA f I))).trans
      (congrArg (fun s => (Space.completionSheafInclusion B S hS
            (yoneda.obj (affineOver B S hS hA f))
            (zeroLocusPoints B S hS hA f I)).hom.app
          (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (D.stage J))) s) hsec))) ?_
  let C := Space.completionSubfunctor B S hS
    (yoneda.obj (affineOver B S hS hA f)) (zeroLocusPoints B S hS hA f I)
  let U := (BigAffineFppf.inclusion B S hS).obj (D.stage J)
  let x : C.toFunctor.obj (Opposite.op U) :=
    ⟨ULift.up (quotientStageToAffine B S hS hA f I D hD J),
      quotientStage_hasImageIn B S hS hA f I D hD J⟩
  change ((BigFppfOver.topology B S hS).sheafifyMap C.ι).app (Opposite.op U)
      ((GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS) C.toFunctor).app
        (Opposite.op U) x) =
    (GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
      (yoneda.obj (affineOver B S hS hA f) ⋙ uliftFunctor.{u + 1})).app
        (Opposite.op U) (ULift.up (quotientStageToAffine B S hS hA f I D hD J))
  let ηC := GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS) C.toFunctor
  let ηX := GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
    (yoneda.obj (affineOver B S hS hA f) ⋙ uliftFunctor.{u + 1})
  let φ := (BigFppfOver.topology B S hS).sheafifyMap C.ι
  calc
    _ = ((ηC ≫ φ).app (Opposite.op U)) x := by
      simp [ηC, φ]
    _ = ((C.ι ≫ ηX).app (Opposite.op U)) x := by
      have hη := congrArg (fun η => η.app (Opposite.op U))
        (GrothendieckTopology.toSheafify_naturality (BigFppfOver.topology B S hS) C.ι).symm
      simp [ηC, ηX, φ, C, x]
    _ = _ := by rfl

/-- The extension of a positive power of `I` to `A^∧` is a weak ideal of definition: it is
open, and each of its elements is topologically nilpotent because its powers exhaust the
extended powers of `I`. -/
private theorem adicCompletion_pow_isWeakIdeal (n : ℕ) (hn : 0 < n) :
    TopologicalRing.IsWeakIdealOfDefinition
      (Ideal.map (algebraMap A (AdicCompletion I A)) (I ^ n)) := by
  let : TopologicalSpace A := I.adicTopology
  let b := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis (AdicCompletion I A))
  constructor
  · rw [isOpen_iff_mem_nhds]
    intro a ha
    rw [(b.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
    refine ⟨(I ^ n • (⊤ : Submodule A (AdicCompletion I A)) : Set _), ⟨n, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (I ^ n).map (algebraMap A (AdicCompletion I A)) |>.add_mem ha (by
      rw [Ideal.smul_top_eq_map] at hx
      exact hx)
  · intro x hx
    change Tendsto (fun k : ℕ => x ^ k) atTop (nhds 0)
    rw [b.toAddGroupFilterBasis.nhds_zero_hasBasis.tendsto_right_iff]
    rintro V ⟨m, rfl⟩
    filter_upwards [eventually_ge_atTop m] with k hk
    change x ^ k ∈ I ^ m • (⊤ : Submodule A (AdicCompletion I A))
    rw [Ideal.smul_top_eq_map]
    have hx' : x ∈ I.map (algebraMap A (AdicCompletion I A)) :=
      Ideal.map_mono (Ideal.pow_le_self hn.ne') hx
    rw [Ideal.map_pow]
    exact Ideal.pow_le_pow_right hk (Ideal.pow_mem_pow hx' k)

/-- For a finitely generated `I`, the quotient of `A^∧` by a weak ideal of definition is
already a quotient of `A`: the composite `A → A^∧ → A^∧ ⧸ J` is surjective. -/
private theorem quotient_completionMap_surjective (hI : I.FG)
    (J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K }) :
    Function.Surjective ((Ideal.Quotient.mk J.1).comp
      (algebraMap A (AdicCompletion I A))) := by
  obtain ⟨n, hn⟩ := exists_adic_power_map_le I J
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  refine ⟨a, ?_⟩
  change Ideal.Quotient.mk J.1 (algebraMap A (AdicCompletion I A) a) =
    Ideal.Quotient.mk J.1 x
  apply Ideal.Quotient.eq.mpr
  apply hn
  rw [← AdicCompletion.ker_evalₐ_eq_map_pow I hI n]
  change AdicCompletion.evalₐ I n (algebraMap A (AdicCompletion I A) a - x) = 0
  simpa only [map_sub, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, sub_eq_zero] using ha

/-- A section over `U` supported on `V(I)` has every scheme-theoretic point of `U` mapping
into `V(I)`: the residue field at a point gives a field-valued point of `U` inside the site,
because a morphism from the spectrum of a residue field is a quasi-compact monomorphism. -/
private theorem hasImageIn_range
    (U : BigFppfOver B S hS)
    (g : U ⟶ affineOver B S hS hA f)
    (hg : Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I) U g)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    (BigFppfOver.toScheme B S hS).map g x ∈
      PrimeSpectrum.zeroLocus (I : Set A) := by
  let X := (BigFppfOver.toScheme B S hS).obj U
  have hqc : QuasiCompact (X.fromSpecResidueField x) := by
    rw [quasiCompact_iff_forall_isAffineOpen]
    intro V hV
    exact (Set.toFinite (X.fromSpecResidueField x ⁻¹' (V : Set X))).isCompact
  let := hqc
  have hK : B.Contains (Spec (X.residueField x)) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact (X.fromSpecResidueField x))
      U.left.property
  let k : B.obj hK ⟶ U.left := ObjectProperty.homMk (X.fromSpecResidueField x)
  let p : Space.FieldValuedPoint B S hS (yoneda.obj U) :=
    { carrier := X.residueField x
      contained := hK
      toBase := B.inclusion.map (k ≫ U.hom)
      value := Over.homMk k }
  let q : Space.FieldValuedPoint B S hS (yoneda.obj (affineOver B S hS hA f)) :=
    { carrier := p.carrier
      contained := p.contained
      toBase := p.toBase
      value := p.value ≫ g }
  have hq := hg p q rfl
  change (BigFppfOver.toScheme B S hS).map g
    (X.fromSpecResidueField x (IsLocalRing.closedPoint (X.residueField x))) ∈ _ at hq
  rw [show X.fromSpecResidueField x (IsLocalRing.closedPoint (X.residueField x)) = x from
    Scheme.fromSpecResidueField_apply x _] at hq
  exact hq

/-- A section over an affine object `U` of the site supported on `V(I)` factors through some
quotient stage of `A^∧`. The morphism `U ⟶ Spec A` kills a power of `I` because `I` is
finitely generated and lies in the radical of the kernel, so the corresponding ring map
factors through `A ⧸ I^{n+1}`, hence through `A^∧ ⧸ (I^{n+1})A^∧`. -/
private theorem exists_quotientStage_factor (hI : I.FG)
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    (U : BigAffineFppf B S hS)
    (g : U.1 ⟶ affineOver B S hS hA f)
    (hg : Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I) U.1 g) :
    ∃ (J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K })
      (k : U.1 ⟶ (D.stage J).1),
      k ≫ quotientStageToAffine B S hS hA f I D hD J = g := by
  let X := (BigAffineFppf.toScheme B S hS).obj U
  let γ : X ⟶ Spec (.of A) := (BigFppfOver.toScheme B S hS).map g
  let ρ : A →+* Γ(X, ⊤) := (Spec.preimage (X.isoSpec.inv ≫ γ)).hom
  have hρ : Spec.map (CommRingCat.ofHom ρ) = X.isoSpec.inv ≫ γ :=
    Spec.map_preimage _
  have hrad : I ≤ (RingHom.ker ρ).radical := by
    intro a ha
    have hnil : IsNilpotent (ρ a) := nilpotent_iff_mem_prime.mpr fun P hP => by
      have ht := hasImageIn_range B S hS hA f I U.1 g hg
        (X.isoSpec.inv (⟨P, hP⟩ : PrimeSpectrum Γ(X, ⊤)))
      have ht' : (Spec.map (CommRingCat.ofHom ρ)) (⟨P, hP⟩ : PrimeSpectrum Γ(X, ⊤)) ∈
          PrimeSpectrum.zeroLocus (I : Set A) := by
        rw [hρ]
        exact ht
      exact ht' ha
    obtain ⟨n, hn⟩ := hnil
    exact ⟨n, by change ρ (a ^ n) = 0; simpa using hn⟩
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hI
  have hn' : I ^ (n + 1) ≤ RingHom.ker ρ :=
    (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn
  let J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K } :=
    ⟨(I ^ (n + 1)).map (algebraMap A (AdicCompletion I A)),
      adicCompletion_pow_isWeakIdeal I (n + 1) (Nat.succ_pos n)⟩
  let ρq := Ideal.Quotient.lift (I ^ (n + 1)) ρ hn'
  let φ := ρq.comp (AdicCompletion.evalₐ I (n + 1)).toRingHom
  have hφ : J.1 ≤ RingHom.ker φ := by
    intro a ha
    have ha' : AdicCompletion.evalₐ I (n + 1) a = 0 := by
      change a ∈ RingHom.ker (AdicCompletion.evalₐ I (n + 1)).toRingHom
      rw [AdicCompletion.ker_evalₐ_eq_map_pow I hI]
      exact ha
    change ρq (AdicCompletion.evalₐ I (n + 1) a) = 0
    rw [ha', map_zero]
  let ψ := Ideal.Quotient.lift J.1 φ hφ
  have hψ : ψ.comp ((Ideal.Quotient.mk J.1).comp
      (algebraMap A (AdicCompletion I A))) = ρ := by
    ext a
    change ρq (AdicCompletion.evalₐ I (n + 1) (algebraMap A (AdicCompletion I A) a)) = ρ a
    rw [AlgHom.commutes]
    rfl
  let κ : X ⟶ Spec (.of (AdicCompletion I A ⧸ J.1)) :=
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ)
  have hκ : κ ≫ Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A)))) = γ := by
    dsimp only [κ]
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, hρ,
      Iso.hom_inv_id_assoc]
  let k : U.1 ⟶ (D.stage J).1 := Over.homMk (ObjectProperty.homMk κ) (by
    apply ObjectProperty.hom_ext
    change κ ≫ D.overS J = B.inclusion.map U.1.hom
    rw [hD J, ← Category.assoc, hκ]
    exact congrArg (fun t => B.inclusion.map t) g.w)
  refine ⟨J, k, ?_⟩
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact hκ

/-- Each morphism `Spec (A^∧ ⧸ J) ⟶ Spec A` is a monomorphism, being a closed immersion: the
ring map `A → A^∧ ⧸ J` is surjective. -/
private theorem quotientStageToAffine_mono (hI : I.FG)
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    (J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K }) :
    Mono (quotientStageToAffine B S hS hA f I D hD J) := by
  let φ := ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A)))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective _ (quotient_completionMap_surjective I hI J)
  have : Mono ((BigFppfOver.toScheme B S hS).map
      (quotientStageToAffine B S hS hA f I D hD J)) :=
    inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom φ)))
  exact Functor.mono_of_mono_map (BigFppfOver.toScheme B S hS) inferInstance

/-- Two factorizations of one section through quotient stages give the same morphism into the
formal spectrum: they agree after passing to the intersection of the two ideals, because the
morphism of that smaller stage to `Spec A` is a monomorphism. -/
private theorem stageLift_eq (hI : I.FG)
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    {J K : { L : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) L }}
    {U : BigFppfOver B S hS}
    (k : U ⟶ (D.stage J).1) (l : U ⟶ (D.stage K).1)
    (h : k ≫ quotientStageToAffine B S hS hA f I D hD J =
      l ≫ quotientStageToAffine B S hS hA f I D hD K) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
        formalSpectrumInclusion D (OrderDual.toDual J) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map l ≫
        formalSpectrumInclusion D (OrderDual.toDual K) := by
  let L : { L : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) L } :=
    ⟨J.1 ⊓ K.1, J.2.1.inter K.2.1, fun x hx => J.2.2 x hx.1⟩
  let j : OrderDual.toDual J ⟶ OrderDual.toDual L := homOfLE (show L.1 ≤ J.1 from inf_le_left)
  let k' : OrderDual.toDual K ⟶ OrderDual.toDual L := homOfLE (show L.1 ≤ K.1 from inf_le_right)
  have hj : (BigAffineFppf.inclusion B S hS).map (D.diagram.map j) ≫
      quotientStageToAffine B S hS hA f I D hD L =
        quotientStageToAffine B S hS hA f I D hD J :=
    quotientStageToAffine_transition B S hS hA f I D hD inf_le_left
  have hk : (BigAffineFppf.inclusion B S hS).map (D.diagram.map k') ≫
      quotientStageToAffine B S hS hA f I D hD L =
        quotientStageToAffine B S hS hA f I D hD K :=
    quotientStageToAffine_transition B S hS hA f I D hD inf_le_right
  have := quotientStageToAffine_mono B S hS hA f I hI D hD L
  have he : k ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map j) =
      l ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map k') :=
    (cancel_mono (quotientStageToAffine B S hS hA f I D hD L)).mp <|
      calc (k ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map j)) ≫
              quotientStageToAffine B S hS hA f I D hD L
          = k ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map j) ≫
              quotientStageToAffine B S hS hA f I D hD L := Category.assoc _ _ _
        _ = k ≫ quotientStageToAffine B S hS hA f I D hD J :=
              congrArg (fun z => k ≫ z) hj
        _ = l ≫ quotientStageToAffine B S hS hA f I D hD K := h
        _ = l ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map k') ≫
              quotientStageToAffine B S hS hA f I D hD L :=
              (congrArg (fun z => l ≫ z) hk).symm
        _ = (l ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map k')) ≫
              quotientStageToAffine B S hS hA f I D hD L := (Category.assoc _ _ _).symm
  have key : ∀ (M : { L : Ideal (AdicCompletion I A) //
        @TopologicalRing.IsWeakIdealOfDefinition _ _
          (I.adicModuleTopology (AdicCompletion I A)) L })
      (m : U ⟶ (D.stage M).1) (jm : OrderDual.toDual M ⟶ OrderDual.toDual L),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map m ≫
          formalSpectrumInclusion D (OrderDual.toDual M) =
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
            (m ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map jm)) ≫
          formalSpectrumInclusion D (OrderDual.toDual L) := by
    intro M m jm
    calc (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map m ≫
            formalSpectrumInclusion D (OrderDual.toDual M)
        = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map m ≫
            ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
                ((BigAffineFppf.inclusion B S hS).map (D.diagram.map jm)) ≫
              formalSpectrumInclusion D (OrderDual.toDual L)) :=
            congrArg
              (fun z => (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map m ≫ z)
              (colimit.w (formalSpectrumDiagram D) jm).symm
      _ = ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map m ≫
            (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
              ((BigAffineFppf.inclusion B S hS).map (D.diagram.map jm))) ≫
            formalSpectrumInclusion D (OrderDual.toDual L) := (Category.assoc _ _ _).symm
      _ = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
            (m ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map jm)) ≫
            formalSpectrumInclusion D (OrderDual.toDual L) :=
            congrArg (fun z => z ≫ formalSpectrumInclusion D (OrderDual.toDual L))
              ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp m
                ((BigAffineFppf.inclusion B S hS).map (D.diagram.map jm))).symm
  exact (key J k j).trans
    ((congrArg (fun z => (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map z ≫
        formalSpectrumInclusion D (OrderDual.toDual L)) he).trans (key K l k').symm)

/-- The section of `Spf (A^∧)` over an affine object of the site attached to a section of the
completion subfunctor there, obtained from a chosen factorization through a quotient stage. -/
private def supportedSectionLift (hI : I.FG)
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    (U : BigAffineFppf B S hS)
    (x : (Space.completionSubfunctor B S hS
      (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).toFunctor.obj (Opposite.op U.1)) :
    (formalSpectrum D).obj.obj (Opposite.op U.1) :=
  let e := exists_quotientStage_factor B S hS hA f I hI D hD U x.1.down x.2
  Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map e.choose_spec.choose ≫
      formalSpectrumInclusion D e.choose)

/-- The section of `Spf (A^∧)` attached to a supported section is computed by any
factorization through a quotient stage, not just the chosen one. -/
private theorem supportedSectionLift_eq (hI : I.FG)
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    (U : BigAffineFppf B S hS)
    (x : (Space.completionSubfunctor B S hS
      (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).toFunctor.obj (Opposite.op U.1))
    (J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K })
    (k : U.1 ⟶ (D.stage J).1)
    (hk : k ≫ quotientStageToAffine B S hS hA f I D hD J = x.1.down) :
    supportedSectionLift B S hS hA f I hI D hD U x =
      Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
          formalSpectrumInclusion D (OrderDual.toDual J)) := by
  apply congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS))
  apply stageLift_eq B S hS hA f I hI D hD
  have e := exists_quotientStage_factor B S hS hA f I hI D hD U x.1.down x.2
  exact e.choose_spec.choose_spec.trans hk.symm

/-- The sections of `Spf (A^∧)` attached to supported sections are natural in the affine
object of the site. -/
private theorem supportedSectionLift_map (hI : I.FG)
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    {U V : BigAffineFppf B S hS} (g : U ⟶ V)
    (x : (Space.completionSubfunctor B S hS
      (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).toFunctor.obj (Opposite.op V.1)) :
    supportedSectionLift B S hS hA f I hI D hD U
        ((Space.completionSubfunctor B S hS
          (yoneda.obj (affineOver B S hS hA f))
          (zeroLocusPoints B S hS hA f I)).toFunctor.map g.hom.op x) =
      (formalSpectrum D).obj.map g.hom.op
        (supportedSectionLift B S hS hA f I hI D hD V x) := by
  obtain ⟨J, k, hk⟩ := exists_quotientStage_factor B S hS hA f I hI D hD V x.1.down x.2
  rw [supportedSectionLift_eq B S hS hA f I hI D hD V x J k hk,
    supportedSectionLift_eq B S hS hA f I hI D hD U _ J (g.hom ≫ k) (by
      change (g.hom ≫ k) ≫ _ = g.hom ≫ x.1.down
      rw [Category.assoc, hk])]
  exact (congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS))
      ((congrArg (fun z => z ≫ formalSpectrumInclusion D (OrderDual.toDual J))
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp g.hom k)).trans
        (Category.assoc _ _ _))).trans
    (Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS) g.hom
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
        formalSpectrumInclusion D (OrderDual.toDual J)))

/-- The comparison morphism sends the section of `Spf (A^∧)` attached to a supported section
back to that section, which is one half of its being an isomorphism. -/
private theorem supportedSectionLift_comparison (hI : I.FG)
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D)
    (U : BigAffineFppf B S hS)
    (x : (Space.completionSubfunctor B S hS
      (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).toFunctor.obj (Opposite.op U.1)) :
    (completionComparison B S hS hA f I D hD).hom.app (Opposite.op U.1)
      (supportedSectionLift B S hS hA f I hI D hD U x) =
    (GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
      (Space.completionSubfunctor B S hS
        (yoneda.obj (affineOver B S hS hA f))
        (zeroLocusPoints B S hS hA f I)).toFunctor).app (Opposite.op U.1) x := by
  obtain ⟨J, k, hk⟩ := exists_quotientStage_factor B S hS hA f I hI D hD U x.1.down x.2
  rw [supportedSectionLift_eq B S hS hA f I hI D hD U x J k hk]
  refine Eq.trans (((Sheaf.sectionEquiv_comp (BigFppfOver.topology B S hS)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
          formalSpectrumInclusion D (OrderDual.toDual J))
        (completionComparison B S hS hA f I D hD)).symm.trans
      (congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS))
        ((Category.assoc _ _ _).trans
          (congrArg
            (fun z => (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫ z)
            (completionComparison_stage B S hS hA f I D hD J))))).trans
    ((Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS) k
        (quotientStageToCompletion B S hS hA f I D hD J)).trans
      (congrArg (fun s => (Space.completionSheaf B S hS
            (yoneda.obj (affineOver B S hS hA f))
            (zeroLocusPoints B S hS hA f I)).obj.map k.op s)
        (sectionEquiv_quotientStageToCompletion B S hS hA f I D hD J)))) ?_
  exact sheafify_map_toSheafify_eq B S hS hA f I k
    ⟨ULift.up (quotientStageToAffine B S hS hA f I D hD J),
      quotientStage_hasImageIn B S hS hA f I D hD J⟩ x hk

/-- **Stacks 0GBA (2).** Let `X = Spec A` be an affine scheme over `S` in the big fppf site
and let `T = V(I)` be the zero locus of a finitely generated ideal `I ⊆ A`. Then the
canonical comparison from the formal spectrum of the `I`-adic completion of `A` to the
completion of `X` along `T` is an isomorphism, so `X_{/T} = Spf (A^∧)`. -/
@[stacks 0GBA "formal spectrum",
  ega "I 10.8.5" "affine case Spf(Â)",
  ega "I 10.10.1" "Spf(A) = X_{/X}", ega "III 5.1.1" "Spf(A) ≅ Ŷ"]
theorem isIso_completionComparison
    (hI : I.FG)
    (D : AdicQuotientSystem B S hS I)
    (hD : QuotientSystemCompatible B S hS f I D) :
    IsIso (completionComparison B S hS hA f I D hD) := by
  let C := Space.completionSubfunctor B S hS
    (yoneda.obj (affineOver B S hS hA f)) (zeroLocusPoints B S hS hA f I)
  let Q := formalSpectrum D
  let t := BigAffineFppf.inclusion B S hS
  have : t.IsCoverDense (BigFppfOver.topology B S hS) :=
    Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
  have : t.IsLocallyFull (BigFppfOver.topology B S hS) :=
    Functor.IsDenseSubsite.isLocallyFull (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
  let η := GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS) C.toFunctor
  let α₀ : t.op ⋙ C.toFunctor ⟶ t.op ⋙ Q.obj :=
    { app U := TypeCat.ofHom (supportedSectionLift B S hS hA f I hI D hD U.unop)
      naturality U V g := by
        ext x
        exact supportedSectionLift_map B S hS hA f I hI D hD g.unop x }
  let α : C.toFunctor ⟶ Q.obj := Functor.IsCoverDense.sheafHom α₀
  let β : Space.completionSheaf B S hS _ _ ⟶ Q :=
    ⟨(BigFppfOver.topology B S hS).sheafifyLift α Q.property⟩
  have hηβ : η ≫ β.hom = α :=
    GrothendieckTopology.toSheafify_sheafifyLift (BigFppfOver.topology B S hS) α Q.property
  have hβ (U : BigAffineFppf B S hS)
      (x : C.toFunctor.obj (Opposite.op U.1)) :
      β.hom.app (Opposite.op U.1) (η.app (Opposite.op U.1) x) =
        supportedSectionLift B S hS hA f I hI D hD U x := by
    change (η ≫ β.hom).app (Opposite.op U.1) x = _
    rw [hηβ]
    exact congrArg (fun z => z.app (Opposite.op U) x)
      (Functor.IsCoverDense.sheafHom_restrict_eq α₀)
  refine ⟨⟨β, ?_, ?_⟩⟩
  · apply colimit.hom_ext
    intro J
    have h1 : formalSpectrumInclusion D J ≫ completionComparison B S hS hA f I D hD ≫ β =
        quotientStageToCompletion B S hS hA f I D hD J.ofDual ≫ β :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ β) (completionComparison_stage B S hS hA f I D hD J.ofDual))
    let xJ : C.toFunctor.obj (Opposite.op (D.stage J.ofDual).1) :=
      ⟨ULift.up (quotientStageToAffine B S hS hA f I D hD J.ofDual),
        quotientStage_hasImageIn B S hS hA f I D hD J.ofDual⟩
    have hsec := sectionEquiv_quotientStageToCompletion B S hS hA f I D hD J.ofDual
    have hid : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (𝟙 (D.stage J.ofDual).1) ≫
            formalSpectrumInclusion D (OrderDual.toDual J.ofDual) =
        formalSpectrumInclusion D J :=
      (congrArg (fun z => z ≫ formalSpectrumInclusion D (OrderDual.toDual J.ofDual))
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_id
          (D.stage J.ofDual).1)).trans (Category.id_comp _)
    have hstage : quotientStageToCompletion B S hS hA f I D hD J.ofDual ≫ β =
        formalSpectrumInclusion D J :=
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
          (X := (BigAffineFppf.inclusion B S hS).obj (D.stage J.ofDual))
          (F := formalSpectrum D)).injective
        ((Sheaf.sectionEquiv_comp (BigFppfOver.topology B S hS)
              (quotientStageToCompletion B S hS hA f I D hD J.ofDual) β).trans
          ((congrArg (fun s => β.hom.app (Opposite.op (D.stage J.ofDual).1) s) hsec).trans
            (((hβ (D.stage J.ofDual) xJ).trans
                (supportedSectionLift_eq B S hS hA f I hI D hD (D.stage J.ofDual) xJ
                  J.ofDual (𝟙 _) (Category.id_comp _))).trans
              (congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)) hid))))
    exact h1.trans (hstage.trans (Category.comp_id (formalSpectrumInclusion D J)).symm)
  · apply Sheaf.hom_ext
    apply GrothendieckTopology.sheafify_hom_ext (BigFppfOver.topology B S hS) _ _
      (Space.completionSheaf B S hS _ _).property
    apply (Functor.IsCoverDense.restrictHomEquivHom (G := t)).symm.injective
    ext U x
    change (completionComparison B S hS hA f I D hD).hom.app (Opposite.op U.unop.1)
      (β.hom.app (Opposite.op U.unop.1) (η.app (Opposite.op U.unop.1) x)) =
        η.app (Opposite.op U.unop.1) x
    rw [hβ]
    exact supportedSectionLift_comparison B S hS hA f I hI D hD U.unop x

end AlgebraicGeometry.FormalSpace

end
