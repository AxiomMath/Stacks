module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureUniversal
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn
import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSchemeStructureSharp

/-!
# The pushforward of the structure sheaf along a universally closed morphism

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and universally closed morphism of
algebraic spaces.  Stacks 0A0Q asserts that the sheaf of algebras `f_*𝒪_X` on the small étale
site of `Y` is integral over `𝒪_Y`, equivalently that `f_*𝒪_X` is its own integral closure.

When `f_*𝒪_X` is integral over `𝒪_Y`, the inclusion of the integral closure `𝒪'` of `𝒪_Y` in
`f_*𝒪_X` is an isomorphism of algebra sheaves, so the normalization of `Y` in `X` is the
relative spectrum `Spec_Y(f_*𝒪_X)` of Stacks 081X.

## Main results

* `AlgebraicGeometry.Space.pushforwardAlgebra_algebraMap_apply`: on an étale chart `V` of `Y`,
  the structure-algebra map of `f_*𝒪_X` is the chartwise structure map
  `AlgebraicGeometry.Space.structureMapApp` of Stacks 03G8 followed by the comparison of the
  two forms of the small étale direct image.
* `AlgebraicGeometry.Space.bijective_directImageRanComparison` and
  `AlgebraicGeometry.Space.directImageSectionsEquiv`: that comparison is bijective on sections,
  so the two descriptions of the sections of `f_*𝒪_X` over `V` agree.
* `CategoryTheory.Sheaf.injective_map_of_singleton_covering`: restriction of the sections of a
  sheaf of types along a one-element covering is injective.
* `AlgebraicGeometry.Space.injective_chartProjection_of_singleton_covering` and
  `AlgebraicGeometry.Space.injective_chartProjection_directImageSectionsEquiv`: a section of
  `f_*𝒪_X` over `V` is determined by its restriction to a single étale scheme chart of `X`
  covering `X ×_Y V`.
* `AlgebraicGeometry.Space.AlgebraSheaf.isIso_integralClosureInclusion_of_isIntegral`: an
  integral algebra sheaf is its own integral closure, the inclusion of the integral closure
  being an isomorphism of algebra sheaves.
* `AlgebraicGeometry.Space.isIso_integralClosureInclusion_pushforwardAlgebra`: that statement
  for the direct image `f_*𝒪_X` of a morphism of algebraic spaces whose direct image is
  integral.
* `AlgebraicGeometry.Space.isIso_relativeSpecDirectImageToNormalizationIn`: the same assertion
  at the level of relative spectra, that the normalization of `Y` in `X` of Stacks 0822 is the
  relative spectrum `Spec_Y(f_*𝒪_X)` of Stacks 081X.

## References

* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
* [Stacks Project, Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 0821](https://stacks.math.columbia.edu/tag/0821)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 082Y](https://stacks.math.columbia.edu/tag/082Y)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

universe u m

/-! ### Restriction along a one-element covering -/

namespace CategoryTheory.Sheaf

/-- Restriction of the sections of a sheaf of types along a morphism whose one-element family
generates a covering sieve is injective: a section is determined by its restriction to a
covering. -/
theorem injective_map_of_singleton_covering {C : Type*} [Category C]
    {J : GrothendieckTopology C} (P : Sheaf J (Type u)) {U V : C} (a : V ⟶ U)
    (ha : Sieve.generate (Presieve.singleton a) ∈ J U) :
    Function.Injective (P.obj.map a.op) :=
  Presieve.isSeparatedFor_singleton.mp
    ((Presieve.isSheafFor_iff_generate (Presieve.singleton a)).2
      (((isSheaf_iff_isSheaf_of_type J P.obj).1 P.property) _ ha)).isSeparatedFor

/-- An isomorphism of sheaves of types is bijective on the sections over every object. -/
private theorem bijective_app_of_isIso_sheaf_hom {C : Type*} [Category C]
    {J : GrothendieckTopology C} {P Q : Sheaf J (Type u)} (φ : P ⟶ Q) [IsIso φ] (U : Cᵒᵖ) :
    Function.Bijective (φ.hom.app U) :=
  (isIso_iff_bijective _).1 inferInstance

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space

/-! ### The structure-algebra map of the pushforward, chartwise -/

section Pushforward

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The comparison of the right Kan extension form of the small étale direct image with the direct
image itself, on the sections of `𝒪_X` over an étale chart `V` of `Y`. -/
noncomputable abbrev directImageRanComparison (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    (pullbackRingSheaf (SmallEtale.topology B S hS Y.1)
        (smallEtaleDirectImageRan B S hS f) (structureRingSheaf B S hS X)).obj.obj (op V) ⟶
      (structureRingSheafDirectImage B S hS f).obj.obj (op V) :=
  (pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
    (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).inv).hom.app (op V)

/-- The structure-algebra map of `f_*𝒪_X` on an étale chart is the structure map of the morphism of
small étale ringed topoi of Stacks 03G8 on sections. -/
theorem pushforwardAlgebra_algebraMap (g : Over Y) (U : (SmallEtale B S hS Y.1)ᵒᵖ) :
    (pushforwardAlgebra B S hS g).algebraMap U =
      ((smallEtaleRingedToposHom B S hS g.hom).fSharp.hom.app U).hom :=
  rfl

/-- The structure map of the morphism of ringed topoi and the structure map of sheaves of rings
agree on sections: they differ only by forgetting commutativity of the rings. -/
theorem fSharp_app_apply (f : X ⟶ Y) (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (r : (structureSheaf B S hS Y.1 Y.2).obj.obj U) :
    ((smallEtaleRingedToposHom B S hS f).fSharp.hom.app U).hom r =
      ((structureSharp B S hS f).hom.app U).hom r := by
  have h : ((sheafCompose (SmallEtale.topology B S hS Y.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
      (smallEtaleRingedToposHom B S hS f).fSharp).hom.app U =
      (structureSharp B S hS f).hom.app U := by
    rw [forgetCommRingSheaf_map_fSharp]
  exact ConcreteCategory.congr_hom h r

/-- The structure map of sheaves of rings on an étale chart is the chartwise structure map of
Stacks 03G8 followed by the comparison of the two forms of the direct image. -/
theorem structureSharp_app_apply (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (r : (structureRingSheaf B S hS Y).obj.obj (op V)) :
    ((structureSharp B S hS f).hom.app (op V)).hom r =
      (directImageRanComparison B S hS f V).hom (structureMapApp B S hS f V r) :=
  rfl

/-- On an étale scheme chart `V` of `Y`, the structure-algebra map of `f_*𝒪_X` sends a regular
function on `V` to the family of its pullbacks to the étale scheme charts of `X` above `X ×_Y V`,
read through the comparison of the two forms of the direct image. -/
theorem pushforwardAlgebra_algebraMap_apply (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (r : (structureSheaf B S hS Y.1 Y.2).obj.obj (op V)) :
    (pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op V) r =
      (directImageRanComparison B S hS f V).hom (structureMapApp B S hS f V r) :=
  (fSharp_app_apply B S hS f (op V) r).trans (structureSharp_app_apply B S hS f V r)

/-- The comparison of the two forms of the small étale direct image is bijective on the sections
over an étale chart: it is a component of an isomorphism of functors. -/
theorem bijective_directImageRanComparison (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    Function.Bijective (directImageRanComparison B S hS f V).hom := by
  exact bijective_app_of_isIso_sheaf_hom
    ((smallEtaleDirectImageRanIso B S hS f).inv.app (structureRingSheaf B S hS X).ringSheaf) (op V)

/-- The two descriptions of the sections of `f_*𝒪_X` over an étale chart `V` of `Y` — as the
sections of the direct image, and as the limit over the étale scheme charts of `X` above `X ×_Y V`
— are identified by the comparison of the two forms of the direct image. -/
noncomputable def directImageSectionsEquiv (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    ((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj).obj
        (op (chartBaseChange B S hS f V)) ≃
      (pushforwardAlgebra B S hS (Over.mk f)).right.obj.obj (op V) :=
  Equiv.ofBijective (directImageRanComparison B S hS f V).hom
    (bijective_directImageRanComparison B S hS f V)

/-! ### Injectivity of a chart projection -/

/-- If the étale scheme chart `j` of `X` above `X ×_Y V` covers `X ×_Y V` in the spaces-étale
topology, the chart projection of Stacks 03G8 is injective on the sections of the direct image
`f_*𝒪_X` over `V`. -/
theorem injective_chartProjection_of_singleton_covering (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (hj : Sieve.generate (Presieve.singleton j.hom.unop) ∈
      SpacesEtale.topology B S hS X (chartBaseChange B S hS f V)) :
    Function.Injective ((chartProjection B S hS f V j).app (structureSetSheaf B S hS X)) := by
  have hres : Function.Injective
      (((smallEtaleComparisonRan B S hS X).obj (structureSetSheaf B S hS X)).obj.map j.hom) :=
    Sheaf.injective_map_of_singleton_covering
      ((smallEtaleComparisonRan B S hS X).obj (structureSetSheaf B S hS X)) j.hom.unop hj
  have hiso := bijective_app_of_isIso_sheaf_hom
    (((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit.app
      (structureSetSheaf B S hS X)) j.right
  exact hiso.1.comp hres

/-- The sections of the direct image `f_*𝒪_X` over an étale chart `V` of `Y` inject into the
regular functions on a single étale scheme chart of `X` covering `X ×_Y V`. -/
theorem injective_chartProjection_directImageSectionsEquiv (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (hj : Sieve.generate (Presieve.singleton j.hom.unop) ∈
      SpacesEtale.topology B S hS X (chartBaseChange B S hS f V)) :
    Function.Injective (fun a : (pushforwardAlgebra B S hS (Over.mk f)).right.obj.obj (op V) =>
      (chartProjection B S hS f V j).app (structureSetSheaf B S hS X)
        ((directImageSectionsEquiv B S hS f V).symm a)) :=
  (injective_chartProjection_of_singleton_covering B S hS f V j hj).comp
    (directImageSectionsEquiv B S hS f V).symm.injective

end Pushforward

/-! ### The integral closure of an integral algebra sheaf -/

namespace AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- The inclusion of the integral closure of an integral algebra sheaf is bijective on the sections
over every chart: it is always injective, and every section of an integral algebra sheaf is locally
integral. -/
theorem bijective_integralClosureInclusion_app {A : AlgebraSheaf.{u, m} B S hS F hF}
    (hA : A.IsIntegral) (U : (SmallEtale B S hS F)ᵒᵖ) :
    Function.Bijective ((integralClosureInclusion A).right.hom.app U).hom := by
  refine ⟨integralClosureInclusion_app_injective A U, fun a => ?_⟩
  refine ⟨⟨a, ?_⟩, rfl⟩
  rw [locallyIntegralSections_eq_top_of_isIntegral hA U]
  exact Subring.mem_top a

/-- The inclusion of the integral closure of an integral algebra sheaf is an isomorphism of the
underlying sheaves of commutative rings. -/
theorem isIso_integralClosureInclusion_right {A : AlgebraSheaf.{u, m} B S hS F hF}
    (hA : A.IsIntegral) : IsIso (integralClosureInclusion A).right := by
  have happ : ∀ U, IsIso (((sheafToPresheaf (SmallEtale.topology B S hS F)
      CommRingCat.{m}).map (integralClosureInclusion A).right).app U) := fun U =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_integralClosureInclusion_app hA U)
  have : IsIso ((sheafToPresheaf (SmallEtale.topology B S hS F) CommRingCat.{m}).map
      (integralClosureInclusion A).right) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ (sheafToPresheaf (SmallEtale.topology B S hS F) CommRingCat.{m})

/-- An integral algebra sheaf is its own integral closure: the inclusion of the subalgebra of
locally integral sections of Stacks 0820 is an isomorphism of algebra sheaves as soon as the
structure-algebra map is integral on every affine étale chart. -/
theorem isIso_integralClosureInclusion_of_isIntegral {A : AlgebraSheaf.{u, m} B S hS F hF}
    (hA : A.IsIntegral) : IsIso (integralClosureInclusion A) := by
  have hr := isIso_integralClosureInclusion_right hA
  refine ⟨⟨⟨inv (integralClosureInclusion A).right, fun U r => ?_⟩, ?_, ?_⟩⟩
  · refine integralClosureInclusion_app_injective A U ?_
    have hcomm := (integralClosureInclusion A).comm U r
    have hid := congrArg (fun φ : A.right ⟶ A.right => φ.hom.app U)
      (IsIso.inv_hom_id (integralClosureInclusion A).right)
    refine Eq.trans ?_ hcomm.symm
    exact ConcreteCategory.congr_hom hid (A.algebraMap U r)
  · exact Hom.ext (IsIso.hom_inv_id (integralClosureInclusion A).right)
  · exact Hom.ext (IsIso.inv_hom_id (integralClosureInclusion A).right)

end AlgebraSheaf

/-! ### The normalization of `Y` in `X` when `f_*𝒪_X` is integral -/

section Normalization

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- For a morphism `f : X ⟶ Y` of algebraic spaces whose direct image `f_*𝒪_X` is integral over
`𝒪_Y`, the inclusion of the integral closure `𝒪'` of `𝒪_Y` in `f_*𝒪_X` is an isomorphism of algebra
sheaves, so `𝒪' = f_*𝒪_X` and the normalization of `Y` in `X` — the relative spectrum of `𝒪'`,
Stacks 0821 — is the factorization `X ⟶ Spec_Y(f_*𝒪_X) ⟶ Y` of Stacks 081X. -/
@[stacks 0A0Q "second assertion: the normalization of Y in X is the factorization through \
Spec_Y(f_*O_X), with the integrality of f_*O_X assumed rather than proved"]
theorem isIso_integralClosureInclusion_pushforwardAlgebra (f : X ⟶ Y)
    (hf : (pushforwardAlgebra B S hS (Over.mk f)).IsIntegral) :
    IsIso (AlgebraSheaf.integralClosureInclusion (pushforwardAlgebra B S hS (Over.mk f))) :=
  AlgebraSheaf.isIso_integralClosureInclusion_of_isIntegral hf

/-- If `f_*𝒪_X` is integral over `𝒪_Y`, the morphism `Spec_Y(f_*𝒪_X) ⟶ Y'` induced by the inclusion
`𝒪' ⊂ f_*𝒪_X` is an isomorphism, so the normalization `Y'` of `Y` in `X` of Stacks 0822 *is* the
relative spectrum of `f_*𝒪_X`. -/
theorem isIso_relativeSpecDirectImageToNormalizationIn
    (E : AffineAlgebraAntiEquivalence B S hS) (f : X ⟶ Y)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    (hf : (pushforwardAlgebra B S hS (Over.mk f)).IsIntegral) :
    IsIso (relativeSpecDirectImageToNormalizationIn B S hS E f hqc hqc') := by
  have hincl : IsIso (normalizationInAlgebraInclusion B S hS f hqc hqc') :=
    (ObjectProperty.isIso_hom_iff _).1
      (isIso_integralClosureInclusion_pushforwardAlgebra B S hS f hf)
  have hmap : IsIso ((E.equivalence Y).inverse.map
      (normalizationInAlgebraInclusion B S hS f hqc hqc')) :=
    Functor.map_isIso _ _
  exact inferInstanceAs (IsIso (((E.equivalence Y).inverse.map
    (normalizationInAlgebraInclusion B S hS f hqc hqc')).unop))

end Normalization

end AlgebraicGeometry.Space

end
