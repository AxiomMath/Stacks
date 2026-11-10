module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicCodimensionZeroProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts

/-!
# Meromorphic functions are computed by a dense monomorphic chart

Let `X` be an algebraic space over a scheme `S` satisfying hypotheses (a), (b) and (c) of
Stacks 0ENA and let `P` be a presentation of its schematic locus at the codimension-zero
points.

A *generic chart* for `P` is an étale chart `C` of `X` whose structure morphism is a
monomorphism and through which every canonical morphism `j_η : Spec(𝒪_{X, η}) ⟶ X`, `η ∈ X⁰`,
factors.  The schematic chart `P.chart` presenting the dense open subspace is one.

This file proves that the sections of `𝒦_X` over a generic chart are already all the
meromorphic functions on `X`: restriction

`Γ(X, 𝒦_X) ⟶ 𝒦_X(C)`

is bijective, and in fact an isomorphism of rings.

Unless they are written in full, the names below are in the namespace
`AlgebraicGeometry.Space.CodimensionZeroPresentation`.

## Main definitions

* `IsGenericChart`: the data making an étale chart a generic chart for a presentation.
* `schematicChart`: the chart presenting the dense open subspace, as an object of the small étale
  site.
* `IsGenericChart.smallBaseChangeProdInv`: the inverse of the base change along `j_η` of the
  projection `U ×_X C ⟶ U`.
* `AlgebraicGeometry.Space.meromorphicFunctionValRingHom`: taking the value over a chart, as a
  ring homomorphism, and `IsGenericChart.genericChartSectionsRingEquiv`: the resulting
  isomorphism of rings at a generic chart.

## Main results

* `isGenericChart_schematicChart`: the schematic chart is a generic chart.
* `IsGenericChart.isIso_smallBaseChange_map_prodFst`: base change along `j_η` turns the
  projection `U ×_X C ⟶ U` into an isomorphism, for every étale chart `U` and every generic
  chart `C`.
* `bijective_pi_genericPointComparison_app_of_isIso`: the comparison of the first conclusion of
  Stacks 0ENA is bijective on the sections over *every* étale chart, not only over the affine
  ones.
* `IsGenericChart.bijective_meromorphicFunctionSheaf_map_prodFst`: restriction of meromorphic
  functions along `U ×_X C ⟶ U` is bijective.
* `IsGenericChart.bijective_val_genericChart`: a meromorphic function on `X` is determined by,
  and may be prescribed as, its restriction to a generic chart.

## Implementation notes

Everything is deduced from the first conclusion of Stacks 0ENA, namely
`AlgebraicGeometry.Space.CodimensionZeroPresentation.isIso_genericPointModuleComparisonPi`,
through one geometric input: for a generic chart `C` the base change of the projection
`U ×_X C ⟶ U` along `j_η` is an isomorphism.  That input is proved by pure universal
properties, with no topology: an inverse is produced from the factorization of `j_η` through
`C` supplied by
`AlgebraicGeometry.Space.CodimensionZeroPresentation.IsGenericChart.factors`, and the two
composites are identified by the extensionality lemmas for represented base changes, the second
of them using that `C` is a monomorphism.

Products in the small étale site are the fibre products over `X` of
`AlgebraicGeometry.Space.SmallEtale.prodObj`; the chart `U ×_X C` and its two projections are
taken from there rather than from `CategoryTheory.Limits.prod`, so that the underlying objects
of the big fppf site of `S` are the represented base changes on the nose.  For the same reason
the base change of a morphism of charts along `j_η` is repackaged as
`AlgebraicGeometry.Space.CodimensionZeroPresentation.genericBaseChangeMap`, whose source and
target are the represented base changes themselves: the composites that the proofs manipulate
are then formed from objects that are syntactically equal, which is what the rewriting tactics
require.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space


/-! ### Bijectivity on the components of a product -/

/-- **An isomorphism into a product of sheaves of modules is bijective onto the product of the
sections** over every object.  This is the converse direction of
`AlgebraicGeometry.Space.bijective_val_app_of_bijective_pi`: the sections functor preserves
products, so the family of components of an isomorphism is a bijection onto the product. -/
theorem bijective_pi_of_isIso.{m, r, v', u'}
    {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {ι : Type m} (M : ι → SheafOfModules.{m} R) [HasProduct M] {A : SheafOfModules.{m} R}
    (f : A ⟶ ∏ᶜ M) [IsIso f] (U : Cᵒᵖ)
    [PreservesLimitsOfShape (Discrete ι)
      (SheafOfModules.evaluation.{m} R U ⋙ forget (ModuleCat (R.obj.obj U)))] :
    Function.Bijective fun s : A.val.obj U =>
      fun i => (Pi.π M i).val.app U (f.val.app U s) := by
  let E := SheafOfModules.evaluation.{m} R U ⋙ forget (ModuleCat (R.obj.obj U))
  let q := piComparison E M ≫ (Types.productIso fun i => E.obj (M i)).hom
  have hqbij : Function.Bijective q := ConcreteCategory.bijective_of_isIso q
  have hfbij : Function.Bijective (E.map f) := ConcreteCategory.bijective_of_isIso (E.map f)
  have hcomp : (fun s => q (E.map f s)) =
      fun s : A.val.obj U => fun i => (Pi.π M i).val.app U (f.val.app U s) := by
    funext s i
    change (Types.productIso fun i => E.obj (M i)).hom (piComparison E M (E.map f s)) i = _
    rw [Types.productIso_hom_comp_eval_apply]
    exact ConcreteCategory.congr_hom (piComparison_comp_π E M i) (E.map f s)
  rw [← hcomp]
  exact hqbij.comp hfbij

namespace CodimensionZeroPresentation

/-! ### Generic charts -/

section Generic

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A generic chart for a presentation of the schematic locus at the codimension-zero
points.** An étale chart `C` of `X` is a *generic chart* when its structure morphism is a
monomorphism and the canonical morphism `j_η : Spec(𝒪_{X, η}) ⟶ X` factors through it for every
point `η` of codimension `0`.

The chart `P.chart` presenting the dense open subspace is one, by
`AlgebraicGeometry.Space.CodimensionZeroPresentation.isGenericChart_schematicChart`; the point
of the notion is that the conclusions below hold for any chart with these two properties. -/
structure IsGenericChart (P : CodimensionZeroPresentation B S hS X)
    (C : SmallEtale B S hS X) : Prop where
  /-- The structure morphism of the chart is a monomorphism. -/
  mono : Mono C.1.hom
  /-- Every canonical morphism `j_η : Spec(𝒪_{X, η}) ⟶ X` factors through the chart. -/
  factors : ∀ (y : points B S hS X) (hy : localRingDimension B S hS y = 0),
    ∃ σ : P.specStalk hy ⟶ C.obj.left, yoneda.map σ ≫ C.1.hom = P.fromSpecStalk hy

variable {P : CodimensionZeroPresentation B S hS X} {C : SmallEtale B S hS X}
    (hC : P.IsGenericChart C) {y : points B S hS X} (hy : localRingDimension B S hS y = 0)

/-- A choice of factorization of `j_η : Spec(𝒪_{X, η}) ⟶ X` through a generic chart. -/
noncomputable def IsGenericChart.sigma : P.specStalk hy ⟶ C.obj.left :=
  (hC.factors y hy).choose

/-- The chosen factorization of `j_η` through a generic chart does factor it. -/
theorem IsGenericChart.map_sigma_comp :
    yoneda.map (hC.sigma hy) ≫ C.1.hom = P.fromSpecStalk hy :=
  (hC.factors y hy).choose_spec

/-! ### The schematic chart -/

variable (P)

/-- **The chart presenting the dense open subspace, as an object of the small étale site of
`X`.** Its structure morphism is `AlgebraicGeometry.Space.CodimensionZeroPresentation.chart`,
which is étale. -/
noncomputable def schematicChart : SmallEtale B S hS X :=
  ⟨CostructuredArrow.mk P.chart, presheaf_etale_of_isEtale B S hS P.isEtale_chart⟩

/-- The structure morphism of the schematic chart is the presenting chart. -/
theorem schematicChart_hom : (P.schematicChart).1.hom = P.chart := rfl

/-- **The schematic chart is a generic chart.** It is a monomorphism, being an isomorphism of
presheaves followed by the inclusion of a subfunctor, and `j_η` factors through it by the very
definition of `j_η` as the composite of `Spec(𝒪_{X, η}) ⟶ P.scheme` with the chart. -/
theorem isGenericChart_schematicChart : P.IsGenericChart P.schematicChart where
  mono := by
    change Mono (P.iso.hom ≫ P.sub.ι)
    exact mono_comp' (IsIso.mono_of_iso _) (Subfunctor.instMonoFunctorTypeι _)
  factors y hy := ⟨P.specStalkToScheme hy, rfl⟩

end Generic

/-! ### Base change of charts along the canonical morphism at a codimension-zero point -/

section Projections

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (P : CodimensionZeroPresentation B S hS X.1) {y : points B S hS X.1}
    (hy : localRingDimension B S hS y = 0)

/-- The canonical morphism `j_η : Spec(𝒪_{X, η}) ⟶ X`, read as a morphism of presheaves, is the
underlying morphism of the morphism of algebraic spaces it defines. -/
theorem genericMorphism_hom : (P.genericMorphism hy X.2).hom = P.fromSpecStalk hy := rfl

/-- The projection `U ×_X Spec(𝒪_{X, η}) ⟶ Spec(𝒪_{X, η})` of the base change of an étale chart
along `j_η`, taken in the big fppf site of `S`, is the one taken in presheaves. -/
theorem map_fst'_representable_genericMorphism (U : SmallEtale B S hS X.1) :
    yoneda.map ((P.representable_genericMorphism hy).fst' U.1.hom) =
      (P.representable_genericMorphism hy).fst U.1.hom :=
  Functor.relativelyRepresentable.map_fst' _ _

/-- The base-change square of an étale chart along `j_η` commutes, written with the projection
to `Spec(𝒪_{X, η})` taken in the big fppf site of `S`. -/
theorem map_fst'_comp_fromSpecStalk (U : SmallEtale B S hS X.1) :
    yoneda.map ((P.representable_genericMorphism hy).fst' U.1.hom) ≫ P.fromSpecStalk hy =
      yoneda.map ((P.representable_genericMorphism hy).snd U.1.hom) ≫ U.1.hom := by
  rw [P.map_fst'_representable_genericMorphism hy U]
  exact (P.representable_genericMorphism hy).w U.1.hom

/-- If two morphisms agree after applying a functor and composing with `f` and `g`, so do their
precompositions with any `t`. -/
private theorem map_comp_comp_eq_of_map_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {T Q A₁ A₂ : C} {Z : D} (t : T ⟶ Q) (a : Q ⟶ A₁) (b : Q ⟶ A₂) (f : F.obj A₁ ⟶ Z)
    (g : F.obj A₂ ⟶ Z) (h : F.map a ≫ f = F.map b ≫ g) :
    F.map (t ≫ a) ≫ f = F.map (t ≫ b) ≫ g := by
  simp only [Functor.map_comp, Category.assoc, h]

/-- The base-change square of an étale chart along `j_η` commutes after precomposition with any
morphism into the base change. -/
theorem map_comp_fst'_comp_fromSpecStalk (U : SmallEtale B S hS X.1) {T : BigFppfOver B S hS}
    (t : T ⟶ (P.representable_genericMorphism hy).pullback U.1.hom) :
    yoneda.map (t ≫ (P.representable_genericMorphism hy).fst' U.1.hom) ≫ P.fromSpecStalk hy =
      yoneda.map (t ≫ (P.representable_genericMorphism hy).snd U.1.hom) ≫ U.1.hom :=
  map_comp_comp_eq_of_map_eq yoneda t _ _ _ _ (P.map_fst'_comp_fromSpecStalk hy U)

/-- **The base change along `j_η` of a morphism of étale charts**, as a morphism of the big fppf
site of `S` between the represented base changes.

This is the underlying morphism of `AlgebraicGeometry.Space.smallBaseChange` applied to `k`; it
is given a name so that its source and target are the represented base changes themselves,
which is the form the computations below compose with. -/
noncomputable def genericBaseChangeMap {U V : SmallEtale B S hS X.1} (k : U ⟶ V) :
    (P.representable_genericMorphism hy).pullback U.1.hom ⟶
      (P.representable_genericMorphism hy).pullback V.1.hom :=
  ((smallBaseChange B S hS (P.genericMorphism hy X.2)
    (P.representable_genericMorphism hy)).map k).hom.left

/-- The base change along `j_η` of a morphism of étale charts is compatible with the projections
to the charts. -/
theorem genericBaseChangeMap_snd {U V : SmallEtale B S hS X.1} (k : U ⟶ V) :
    P.genericBaseChangeMap hy k ≫ (P.representable_genericMorphism hy).snd V.1.hom =
      (P.representable_genericMorphism hy).snd U.1.hom ≫ k.hom.left :=
  smallBaseChange_map_snd B S hS _ _ _

/-- The base change along `j_η` of a morphism of étale charts is compatible with the projections
to `Spec(𝒪_{X, η})`. -/
theorem map_genericBaseChangeMap_comp_fst {U V : SmallEtale B S hS X.1} (k : U ⟶ V) :
    yoneda.map (P.genericBaseChangeMap hy k) ≫
        (P.representable_genericMorphism hy).fst V.1.hom =
      (P.representable_genericMorphism hy).fst U.1.hom :=
  CostructuredArrow.w _

end Projections

section Products

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS} (U C : SmallEtale B S hS X.1)

/-- The structure morphism of the fibre product `U ×_X C` of two étale charts is its projection
to `C` followed by the structure morphism of `C`. -/
theorem prodObj_hom : (SmallEtale.prodObj B S hS X.1 U C).1.hom =
    yoneda.map ((SmallEtale.prodSnd B S hS X.1 U C).hom.left) ≫ C.1.hom := rfl

/-- The two projections of the fibre product `U ×_X C` of two étale charts agree over `X`. -/
theorem map_prodFst_comp_hom :
    yoneda.map ((SmallEtale.prodFst B S hS X.1 U C).hom.left) ≫ U.1.hom =
      yoneda.map ((SmallEtale.prodSnd B S hS X.1 U C).hom.left) ≫ C.1.hom :=
  CostructuredArrow.w (SmallEtale.prodFst B S hS X.1 U C).hom

/-- The two projections of the fibre product `U ×_X C` of two étale charts agree over `X` after
precomposition with any morphism into the fibre product. -/
theorem map_comp_prodFst_comp_hom {T : BigFppfOver B S hS}
    (t : T ⟶ (SmallEtale.prodObj B S hS X.1 U C).obj.left) :
    yoneda.map (t ≫ (SmallEtale.prodFst B S hS X.1 U C).hom.left) ≫ U.1.hom =
      yoneda.map (t ≫ (SmallEtale.prodSnd B S hS X.1 U C).hom.left) ≫ C.1.hom :=
  map_comp_comp_eq_of_map_eq yoneda t _ _ _ _ (map_prodFst_comp_hom U C)

end Products

/-! ### Base change of the projection from a product with a generic chart -/

section BaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    {P : CodimensionZeroPresentation B S hS X.1} {C : SmallEtale B S hS X.1}
    (hC : P.IsGenericChart C) {y : points B S hS X.1}
    (hy : localRingDimension B S hS y = 0) (U : SmallEtale B S hS X.1)

include hC

/-- **Two morphisms into a generic chart agree as soon as they do over `X`**, one of them being
given as a factorization through `Spec(𝒪_{X, η})`: the structure morphism of the chart is a
monomorphism and `yoneda` is fully faithful. -/
theorem IsGenericChart.comp_sigma_eq {T : BigFppfOver B S hS} (t : T ⟶ P.specStalk hy)
    (s : T ⟶ C.obj.left)
    (h : yoneda.map t ≫ P.fromSpecStalk hy = yoneda.map s ≫ C.1.hom) :
    t ≫ hC.sigma hy = s := by
  have := hC.mono
  have e : yoneda.map (t ≫ hC.sigma hy) = yoneda.map t ≫ yoneda.map (hC.sigma hy) :=
    yoneda.map_comp _ _
  refine yoneda.map_injective ((cancel_mono C.1.hom).mp ?_)
  rw [e, Category.assoc, hC.map_sigma_comp hy]
  exact h

/-- The compatibility making `IsGenericChart.prodLift` well defined: the projection
`U ×_X Spec(𝒪_{X, η}) ⟶ U` and the composite `U ×_X Spec(𝒪_{X, η}) ⟶ Spec(𝒪_{X, η}) ⟶ C` agree
over `X`. -/
theorem IsGenericChart.prodLift_cond :
    yoneda.map ((P.representable_genericMorphism hy).snd U.1.hom) ≫ U.1.hom =
      yoneda.map ((P.representable_genericMorphism hy).fst' U.1.hom ≫ hC.sigma hy) ≫ C.1.hom := by
  have h : yoneda.map ((P.representable_genericMorphism hy).fst' U.1.hom ≫ hC.sigma hy) =
      yoneda.map ((P.representable_genericMorphism hy).fst' U.1.hom) ≫
        yoneda.map (hC.sigma hy) := yoneda.map_comp _ _
  rw [h, Category.assoc, hC.map_sigma_comp hy]
  exact (P.map_fst'_comp_fromSpecStalk hy U).symm

/-- The morphism `U ×_X Spec(𝒪_{X, η}) ⟶ U ×_X C` inverting the base change of the projection
`U ×_X C ⟶ U`, read in the fibre product `U ×_X C`: its component over `U` is the projection,
and its component over `C` is the factorization `σ_η : Spec(𝒪_{X, η}) ⟶ C` of `j_η` precomposed
with the projection to `Spec(𝒪_{X, η})`. -/
noncomputable def IsGenericChart.prodLift :
    (P.representable_genericMorphism hy).pullback U.1.hom ⟶
      (SmallEtale.prodObj B S hS X.1 U C).obj.left :=
  U.property.rep.lift' ((P.representable_genericMorphism hy).snd U.1.hom)
    ((P.representable_genericMorphism hy).fst' U.1.hom ≫ hC.sigma hy) (hC.prodLift_cond hy U)

/-- The component of `IsGenericChart.prodLift` over `U`. -/
theorem IsGenericChart.prodLift_fst :
    hC.prodLift hy U ≫ (SmallEtale.prodFst B S hS X.1 U C).hom.left =
      (P.representable_genericMorphism hy).snd U.1.hom :=
  U.property.rep.lift'_fst _ _ _

/-- The component of `IsGenericChart.prodLift` over `C`. -/
theorem IsGenericChart.prodLift_snd :
    hC.prodLift hy U ≫ (SmallEtale.prodSnd B S hS X.1 U C).hom.left =
      (P.representable_genericMorphism hy).fst' U.1.hom ≫ hC.sigma hy :=
  U.property.rep.lift'_snd _ _ _

/-- The compatibility making `IsGenericChart.prodInv` well defined. -/
theorem IsGenericChart.prodInv_cond :
    (P.representable_genericMorphism hy).fst U.1.hom ≫ (P.genericMorphism hy X.2).hom =
      yoneda.map (hC.prodLift hy U) ≫ (SmallEtale.prodObj B S hS X.1 U C).1.hom := by
  have hw := (P.representable_genericMorphism hy).w U.1.hom
  have h : yoneda.map (hC.prodLift hy U) ≫ (SmallEtale.prodObj B S hS X.1 U C).1.hom =
      yoneda.map (hC.prodLift hy U) ≫
        yoneda.map ((SmallEtale.prodSnd B S hS X.1 U C).hom.left) ≫ C.1.hom := rfl
  have hmc : yoneda.map (hC.prodLift hy U ≫ (SmallEtale.prodSnd B S hS X.1 U C).hom.left) =
      yoneda.map (hC.prodLift hy U) ≫
        yoneda.map ((SmallEtale.prodSnd B S hS X.1 U C).hom.left) := yoneda.map_comp _ _
  rw [hw, h, ← Category.assoc, ← hmc, hC.prodLift_snd hy U]
  exact hC.prodLift_cond hy U

/-- The inverse of the base change along `j_η` of the projection `U ×_X C ⟶ U`, as a morphism
of the big fppf site of `S`. -/
noncomputable def IsGenericChart.prodInv :
    (P.representable_genericMorphism hy).pullback U.1.hom ⟶
      (P.representable_genericMorphism hy).pullback
        (SmallEtale.prodObj B S hS X.1 U C).1.hom :=
  (P.representable_genericMorphism hy).lift
    ((P.representable_genericMorphism hy).fst U.1.hom) (hC.prodLift hy U)
    (hC.prodInv_cond hy U)

/-- The component of `IsGenericChart.prodInv` over `Spec(𝒪_{X, η})`. -/
theorem IsGenericChart.map_prodInv_comp_fst :
    yoneda.map (hC.prodInv hy U) ≫ (P.representable_genericMorphism hy).fst
        (SmallEtale.prodObj B S hS X.1 U C).1.hom =
      (P.representable_genericMorphism hy).fst U.1.hom :=
  (P.representable_genericMorphism hy).lift_fst _ _ _

/-- The component of `IsGenericChart.prodInv` over `U ×_X C`. -/
theorem IsGenericChart.prodInv_snd :
    hC.prodInv hy U ≫ (P.representable_genericMorphism hy).snd
        (SmallEtale.prodObj B S hS X.1 U C).1.hom = hC.prodLift hy U :=
  (P.representable_genericMorphism hy).lift_snd _ _ _

/-- The inverse of the base change along `j_η` of the projection `U ×_X C ⟶ U`, as a morphism
of the small étale site of `Spec(𝒪_{X, η})`. -/
noncomputable def IsGenericChart.smallBaseChangeProdInv :
    (smallBaseChange B S hS (P.genericMorphism hy X.2)
        (P.representable_genericMorphism hy)).obj U ⟶
      (smallBaseChange B S hS (P.genericMorphism hy X.2)
        (P.representable_genericMorphism hy)).obj (SmallEtale.prodObj B S hS X.1 U C) :=
  ObjectProperty.homMk (CostructuredArrow.homMk (hC.prodInv hy U)
    (hC.map_prodInv_comp_fst hy U))

/-- **The base change along `j_η` of the projection `U ×_X C ⟶ U`, followed by the projection to
`Spec(𝒪_{X, η})` and the factorization of `j_η` through `C`, is the projection to `C`.**

This is where the hypothesis that `C` is a monomorphism enters: both composites agree over `X`,
because `j_η` factors through `C` and both base-change squares commute. -/
theorem IsGenericChart.prodFstBaseChange_comp_sigma :
    (P.genericBaseChangeMap hy (SmallEtale.prodFst B S hS X.1 U C) ≫
        (P.representable_genericMorphism hy).fst' U.1.hom) ≫ hC.sigma hy =
      (P.representable_genericMorphism hy).snd
          (SmallEtale.prodObj B S hS X.1 U C).1.hom ≫
        (SmallEtale.prodSnd B S hS X.1 U C).hom.left := by
  refine hC.comp_sigma_eq hy _ _ ?_
  rw [P.map_comp_fst'_comp_fromSpecStalk hy U
      (P.genericBaseChangeMap hy (SmallEtale.prodFst B S hS X.1 U C)),
    P.genericBaseChangeMap_snd hy (SmallEtale.prodFst B S hS X.1 U C)]
  exact map_comp_prodFst_comp_hom U C _

/-- The base change along `j_η` of the projection `U ×_X C ⟶ U`, followed by the candidate
inverse, is the projection of `U ×_X C ×_X Spec(𝒪_{X, η})` to `U ×_X C`.

Both sides are morphisms into the fibre product `U ×_X C`, so they are compared componentwise;
the component over `C` is `IsGenericChart.prodFstBaseChange_comp_sigma`. -/
theorem IsGenericChart.map_prodFst_comp_prodLift :
    P.genericBaseChangeMap hy (SmallEtale.prodFst B S hS X.1 U C) ≫ hC.prodLift hy U =
      (P.representable_genericMorphism hy).snd
        (SmallEtale.prodObj B S hS X.1 U C).1.hom := by
  refine U.property.rep.hom_ext' ?_ ?_
  · change (P.genericBaseChangeMap hy (SmallEtale.prodFst B S hS X.1 U C) ≫ hC.prodLift hy U) ≫
        (SmallEtale.prodFst B S hS X.1 U C).hom.left =
      (P.representable_genericMorphism hy).snd
          (SmallEtale.prodObj B S hS X.1 U C).1.hom ≫
        (SmallEtale.prodFst B S hS X.1 U C).hom.left
    rw [Category.assoc, hC.prodLift_fst hy U,
      P.genericBaseChangeMap_snd hy (SmallEtale.prodFst B S hS X.1 U C)]
  · change (P.genericBaseChangeMap hy (SmallEtale.prodFst B S hS X.1 U C) ≫ hC.prodLift hy U) ≫
        (SmallEtale.prodSnd B S hS X.1 U C).hom.left =
      (P.representable_genericMorphism hy).snd
          (SmallEtale.prodObj B S hS X.1 U C).1.hom ≫
        (SmallEtale.prodSnd B S hS X.1 U C).hom.left
    rw [Category.assoc, hC.prodLift_snd hy U]
    exact (Category.assoc _ _ _).symm.trans (hC.prodFstBaseChange_comp_sigma hy U)

/-- **Base change along `j_η` turns the projection from a product with a generic chart into an
isomorphism.**  For an étale chart `U` of `X`, a generic chart `C` and a point `η` of
codimension `0`, the projection `U ×_X C ⟶ U` becomes, after base change along
`j_η : Spec(𝒪_{X, η}) ⟶ X`, an isomorphism

`U ×_X C ×_X Spec(𝒪_{X, η}) ≅ U ×_X Spec(𝒪_{X, η})`.

The inverse is `IsGenericChart.smallBaseChangeProdInv`, built from the factorization of `j_η`
through `C`; that the two composites are the identity is checked componentwise on the represented
base changes. -/
theorem IsGenericChart.isIso_smallBaseChange_map_prodFst :
    IsIso ((smallBaseChange B S hS (P.genericMorphism hy X.2)
      (P.representable_genericMorphism hy)).map (SmallEtale.prodFst B S hS X.1 U C)) := by
  refine ⟨hC.smallBaseChangeProdInv hy U, ?_, ?_⟩
  · refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    change P.genericBaseChangeMap hy (SmallEtale.prodFst B S hS X.1 U C) ≫
      hC.prodInv hy U = 𝟙 _
    refine (P.representable_genericMorphism hy).hom_ext ?_ ?_
    · have hid := yoneda.map_id ((P.representable_genericMorphism hy).pullback
        (SmallEtale.prodObj B S hS X.1 U C).1.hom)
      simp only [Functor.map_comp, Category.assoc, hid, Category.id_comp,
        hC.map_prodInv_comp_fst hy U,
        P.map_genericBaseChangeMap_comp_fst hy (SmallEtale.prodFst B S hS X.1 U C)]
    · simp only [Category.assoc, Category.id_comp, hC.prodInv_snd hy U,
        hC.map_prodFst_comp_prodLift hy U]
  · refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    change hC.prodInv hy U ≫
      P.genericBaseChangeMap hy (SmallEtale.prodFst B S hS X.1 U C) = 𝟙 _
    refine (P.representable_genericMorphism hy).hom_ext ?_ ?_
    · have hid := yoneda.map_id ((P.representable_genericMorphism hy).pullback U.1.hom)
      simp only [Functor.map_comp, Category.assoc, hid, Category.id_comp,
        P.map_genericBaseChangeMap_comp_fst hy (SmallEtale.prodFst B S hS X.1 U C),
        hC.map_prodInv_comp_fst hy U]
    · simp only [Category.assoc, Category.id_comp,
        P.genericBaseChangeMap_snd hy (SmallEtale.prodFst B S hS X.1 U C),
        reassoc_of% (hC.prodInv_snd hy U), hC.prodLift_fst hy U]

/-- **Base change along `j_η` turns the projection from a product with a generic chart into an
isomorphism**, read on the underlying objects of the big fppf site of `S`. -/
theorem IsGenericChart.isIso_toOver_map_smallBaseChange_map_prodFst :
    IsIso ((SmallEtale.toOver B S hS (P.specStalkSpace hy).1).map
      ((smallBaseChange B S hS (P.genericMorphism hy X.2)
        (P.representable_genericMorphism hy)).map
          (SmallEtale.prodFst B S hS X.1 U C))) := by
  have := hC.isIso_smallBaseChange_map_prodFst hy U
  infer_instance

end BaseChange

/-! ### Sections of the sheaf of meromorphic functions over an arbitrary chart -/

section Sections

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (P : CodimensionZeroPresentation B S hS X.1)

/-- **The comparison of the first conclusion of Stacks 0ENA is bijective on the sections over
every étale chart.**

Over an *affine* chart this is
`AlgebraicGeometry.Space.CodimensionZeroPresentation.bijective_pi_genericPointComparison_app`,
and that is what proves the comparison to be an isomorphism of sheaves of modules; being an
isomorphism, it is then bijective on the sections over *every* chart, which is the statement
here. -/
theorem bijective_pi_genericPointComparison_app_of_isIso
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) (U : SmallEtale B S hS X.1) :
    Function.Bijective (fun s : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) =>
      fun η : CodimensionZeroPoints B S hS X.1 =>
        ((P.genericPointComparison η.2).hom.app (op U)).hom s) := by
  have := P.isIso_genericPointModuleComparisonPi hwa hfin
  have hpi := bijective_pi_of_isIso
    (fun η : CodimensionZeroPoints B S hS X.1 => P.genericPointModule η.2)
    P.genericPointModuleComparisonPi (op U)
  have hgoal : (fun s : (meromorphicModule B S hS X).val.obj (op U) =>
        fun η : CodimensionZeroPoints B S hS X.1 =>
          (Pi.π (fun η : CodimensionZeroPoints B S hS X.1 => P.genericPointModule η.2) η).val.app
            (op U) (P.genericPointModuleComparisonPi.val.app (op U) s)) =
      fun s => fun η : CodimensionZeroPoints B S hS X.1 =>
        ULift.up (((P.genericPointComparison η.2).hom.app (op U)).hom s.down) := by
    refine funext fun s => funext fun η => ?_
    have h : P.genericPointModuleComparisonPi ≫
        Pi.π (fun η : CodimensionZeroPoints B S hS X.1 => P.genericPointModule η.2) η =
          P.genericPointModuleComparison η.2 := Pi.lift_comp_π _ η
    exact congrFun (congrArg
      (fun g : meromorphicModule B S hS X ⟶ P.genericPointModule η.2 =>
        fun z => g.val.app (op U) z) h) s
  rw [hgoal] at hpi
  refine ⟨fun s t h => ?_, fun t => ?_⟩
  · exact congrArg ULift.down (hpi.injective (a₁ := ULift.up s) (a₂ := ULift.up t)
      (funext fun η => congrArg ULift.up (congrFun h η)))
  · obtain ⟨s, hs⟩ := hpi.surjective fun η => ULift.up (t η)
    exact ⟨s.down, funext fun η => congrArg ULift.down (congrFun hs η)⟩

end Sections

/-! ### Restriction to a product with a generic chart -/

section Restriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    {P : CodimensionZeroPresentation B S hS X.1} {C : SmallEtale B S hS X.1}
    (hC : P.IsGenericChart C)

include hC

/-- **Restriction of the direct image `j_{η, *}𝒪_{X, η}` along the projection from a product
with a generic chart is bijective**: the sections of the direct image over a chart are the
regular functions on its base change along `j_η`, and that base change turns the projection
into an isomorphism. -/
theorem IsGenericChart.bijective_genericPointStructureSheaf_map_prodFst
    (U : SmallEtale B S hS X.1) {y : points B S hS X.1}
    (hy : localRingDimension B S hS y = 0) :
    Function.Bijective (fun t : (P.genericPointStructureSheaf hy).obj.obj (op U) =>
      ((P.genericPointStructureSheaf hy).obj.map
        (SmallEtale.prodFst B S hS X.1 U C).op).hom t) := by
  have := hC.isIso_smallBaseChange_map_prodFst hy U
  have : IsIso ((P.genericPointStructureSheaf hy).obj.map
      (SmallEtale.prodFst B S hS X.1 U C).op) := by
    change IsIso ((structureSheaf B S hS (P.specStalkSpace hy).1
      (P.specStalkSpace hy).2).obj.map
        (((smallBaseChange B S hS (P.genericMorphism hy X.2)
          (P.representable_genericMorphism hy)).map
            (SmallEtale.prodFst B S hS X.1 U C)).op))
    infer_instance
  exact ConcreteCategory.bijective_of_isIso _

omit hC in
/-- The comparison `𝒦_X ⟶ j_{η, *}𝒪_{X, η}` is natural in the chart. -/
theorem IsGenericChart.genericPointComparison_app_map_prodFst
    (U : SmallEtale B S hS X.1) {y : points B S hS X.1}
    (hy : localRingDimension B S hS y = 0)
    (s : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) :
    ((P.genericPointComparison hy).hom.app
          (op (SmallEtale.prodObj B S hS X.1 U C))).hom
        (((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
          (SmallEtale.prodFst B S hS X.1 U C).op).hom s) =
      ((P.genericPointStructureSheaf hy).obj.map
          (SmallEtale.prodFst B S hS X.1 U C).op).hom
        (((P.genericPointComparison hy).hom.app (op U)).hom s) :=
  ConcreteCategory.congr_hom
    ((P.genericPointComparison hy).hom.naturality
      (SmallEtale.prodFst B S hS X.1 U C).op) s

/-- **Restriction of meromorphic functions along the projection from a product with a generic
chart is bijective.**

Both sides are identified, by `bijective_pi_genericPointComparison_app_of_isIso`, with the
product over the codimension-zero points `η` of the sections of `j_{η, *}𝒪_{X, η}`; the
comparison is natural in the chart, so the restriction becomes the product of the restrictions
of the direct images, and those are bijective because base change along `j_η` turns the
projection into an isomorphism. -/
theorem IsGenericChart.bijective_meromorphicFunctionSheaf_map_prodFst
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) (U : SmallEtale B S hS X.1) :
    Function.Bijective (fun s : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) =>
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
        (SmallEtale.prodFst B S hS X.1 U C).op).hom s) := by
  have hU := P.bijective_pi_genericPointComparison_app_of_isIso hwa hfin U
  have hUC := P.bijective_pi_genericPointComparison_app_of_isIso hwa hfin
    (SmallEtale.prodObj B S hS X.1 U C)
  refine ⟨fun s t h => ?_, fun t => ?_⟩
  · refine hU.injective (funext fun η => ?_)
    refine (hC.bijective_genericPointStructureSheaf_map_prodFst U η.2).injective ?_
    have h' : ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
          (SmallEtale.prodFst B S hS X.1 U C).op).hom s =
        ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
          (SmallEtale.prodFst B S hS X.1 U C).op).hom t := h
    rw [← IsGenericChart.genericPointComparison_app_map_prodFst (P := P) (C := C) U η.2 s,
      ← IsGenericChart.genericPointComparison_app_map_prodFst (P := P) (C := C) U η.2 t, h']
  · obtain ⟨u, hu⟩ : ∃ u : ∀ η : CodimensionZeroPoints B S hS X.1,
        (P.genericPointStructureSheaf η.2).obj.obj (op U),
        ∀ η : CodimensionZeroPoints B S hS X.1,
          ((P.genericPointStructureSheaf η.2).obj.map
            (SmallEtale.prodFst B S hS X.1 U C).op).hom (u η) =
            ((P.genericPointComparison η.2).hom.app
              (op (SmallEtale.prodObj B S hS X.1 U C))).hom t :=
      ⟨fun η => ((hC.bijective_genericPointStructureSheaf_map_prodFst U η.2).surjective _).choose,
        fun η =>
          ((hC.bijective_genericPointStructureSheaf_map_prodFst U η.2).surjective _).choose_spec⟩
    obtain ⟨s, hs⟩ := hU.surjective u
    have hs' : ∀ η : CodimensionZeroPoints B S hS X.1,
        ((P.genericPointComparison η.2).hom.app (op U)).hom s = u η := fun η => congrFun hs η
    refine ⟨s, hUC.injective (funext fun η => ?_)⟩
    rw [IsGenericChart.genericPointComparison_app_map_prodFst (P := P) (C := C) U η.2 s, hs' η,
      hu η]

end Restriction

end CodimensionZeroPresentation

/-! ### Global sections computed by a generic chart -/

section GlobalSections

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- Restriction of meromorphic functions is functorial. -/
theorem meromorphicFunctionSheaf_map_comp_apply {U V W : SmallEtale B S hS X.1} (k : U ⟶ V)
    (l : V ⟶ W) (x : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op W)) :
    ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map (k ≫ l).op).hom x =
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map k.op).hom
        (((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map l.op).hom x) :=
  ConcreteCategory.congr_hom
    ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map_comp l.op k.op) x

/-- A meromorphic function restricts compatibly along every morphism of étale charts. -/
theorem meromorphicFunction_val_naturality (m : MeromorphicFunction B S hS X.1 X.2)
    {U V : SmallEtale B S hS X.1} (k : U ⟶ V) :
    ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map k.op).hom (m.val (op V)) =
      m.val (op U) :=
  m.property k.op

/-- **The morphism `U₁ ×_X C ⟶ U₂ ×_X C` induced by a morphism `U₁ ⟶ U₂` of étale charts**, from
the universal property of the fibre product. -/
noncomputable def prodMapFst {U₁ U₂ : SmallEtale B S hS X.1} (g : U₁ ⟶ U₂)
    (C : SmallEtale B S hS X.1) :
    SmallEtale.prodObj B S hS X.1 U₁ C ⟶ SmallEtale.prodObj B S hS X.1 U₂ C :=
  (BinaryFan.IsLimit.lift' (SmallEtale.prodIsLimit B S hS X.1 U₂ C)
    (SmallEtale.prodFst B S hS X.1 U₁ C ≫ g) (SmallEtale.prodSnd B S hS X.1 U₁ C)).1

/-- `AlgebraicGeometry.Space.prodMapFst` is compatible with the first projections. -/
theorem prodMapFst_comp_prodFst {U₁ U₂ : SmallEtale B S hS X.1} (g : U₁ ⟶ U₂)
    (C : SmallEtale B S hS X.1) :
    prodMapFst g C ≫ SmallEtale.prodFst B S hS X.1 U₂ C =
      SmallEtale.prodFst B S hS X.1 U₁ C ≫ g :=
  (BinaryFan.IsLimit.lift' (SmallEtale.prodIsLimit B S hS X.1 U₂ C)
    (SmallEtale.prodFst B S hS X.1 U₁ C ≫ g) (SmallEtale.prodSnd B S hS X.1 U₁ C)).2.1

/-- `AlgebraicGeometry.Space.prodMapFst` is compatible with the second projections. -/
theorem prodMapFst_comp_prodSnd {U₁ U₂ : SmallEtale B S hS X.1} (g : U₁ ⟶ U₂)
    (C : SmallEtale B S hS X.1) :
    prodMapFst g C ≫ SmallEtale.prodSnd B S hS X.1 U₂ C =
      SmallEtale.prodSnd B S hS X.1 U₁ C :=
  (BinaryFan.IsLimit.lift' (SmallEtale.prodIsLimit B S hS X.1 U₂ C)
    (SmallEtale.prodFst B S hS X.1 U₁ C ≫ g) (SmallEtale.prodSnd B S hS X.1 U₁ C)).2.2

/-- **Taking the value over an étale chart is a ring homomorphism** from the meromorphic
functions on `X` to the sections of `𝒦_X` over that chart: the ring structure on the meromorphic
functions is the one computed on the sections over each chart. -/
noncomputable def meromorphicFunctionValRingHom (U : SmallEtale B S hS X.1) :
    MeromorphicFunction B S hS X.1 X.2 →+*
      (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) where
  toFun m := m.val (op U)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

namespace CodimensionZeroPresentation

variable {P : CodimensionZeroPresentation B S hS X.1} {C : SmallEtale B S hS X.1}
    (hC : P.IsGenericChart C)

include hC

/-- **The two projections of `C ×_X C` agree for a generic chart `C`**, its structure morphism
being a monomorphism. -/
theorem IsGenericChart.prodFst_self_eq_prodSnd :
    SmallEtale.prodFst B S hS X.1 C C = SmallEtale.prodSnd B S hS X.1 C C := by
  have := hC.mono
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
  exact yoneda.map_injective ((cancel_mono C.1.hom).mp (map_prodFst_comp_hom C C))

variable (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (a : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op C))

include hwa hfin

/-- **The value over an étale chart `U` of the meromorphic function extending a section over a
generic chart `C`**: the unique section over `U` whose restriction to `U ×_X C` is the
restriction of the given section, which exists by
`IsGenericChart.bijective_meromorphicFunctionSheaf_map_prodFst`. -/
noncomputable def IsGenericChart.extendVal (U : SmallEtale B S hS X.1) :
    (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) :=
  ((hC.bijective_meromorphicFunctionSheaf_map_prodFst hwa hfin U).surjective
    (((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
      (SmallEtale.prodSnd B S hS X.1 U C).op).hom a)).choose

/-- The defining property of
`AlgebraicGeometry.Space.CodimensionZeroPresentation.IsGenericChart.extendVal`. -/
theorem IsGenericChart.map_prodFst_extendVal (U : SmallEtale B S hS X.1) :
    ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
          (SmallEtale.prodFst B S hS X.1 U C).op).hom (hC.extendVal hwa hfin a U) =
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
        (SmallEtale.prodSnd B S hS X.1 U C).op).hom a :=
  ((hC.bijective_meromorphicFunctionSheaf_map_prodFst hwa hfin U).surjective _).choose_spec

/-- The values of
`AlgebraicGeometry.Space.CodimensionZeroPresentation.IsGenericChart.extendVal` are compatible
with restriction, so they do define a meromorphic function.

The identity is checked after restricting to `U₁ ×_X C`, which is injective; there both sides
become the restriction of the given section along `U₁ ×_X C ⟶ C`. -/
theorem IsGenericChart.extendVal_restrict {U₁ U₂ : SmallEtale B S hS X.1} (g : U₁ ⟶ U₂) :
    ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map g.op).hom
        (hC.extendVal hwa hfin a U₂) = hC.extendVal hwa hfin a U₁ := by
  refine (hC.bijective_meromorphicFunctionSheaf_map_prodFst hwa hfin U₁).injective ?_
  rw [hC.map_prodFst_extendVal hwa hfin a U₁,
    ← meromorphicFunctionSheaf_map_comp_apply (SmallEtale.prodFst B S hS X.1 U₁ C) g,
    ← prodMapFst_comp_prodFst g C,
    meromorphicFunctionSheaf_map_comp_apply (prodMapFst g C)
      (SmallEtale.prodFst B S hS X.1 U₂ C),
    hC.map_prodFst_extendVal hwa hfin a U₂,
    ← meromorphicFunctionSheaf_map_comp_apply (prodMapFst g C)
      (SmallEtale.prodSnd B S hS X.1 U₂ C),
    prodMapFst_comp_prodSnd g C]

/-- The meromorphic function extending a section over a generic chart. -/
noncomputable def IsGenericChart.extend : MeromorphicFunction B S hS X.1 X.2 :=
  ⟨fun V => hC.extendVal hwa hfin a V.unop, fun f => hC.extendVal_restrict hwa hfin a f.unop⟩

/-- The extension of a section over a generic chart restricts to that section: the two
projections of `C ×_X C` agree. -/
theorem IsGenericChart.extendVal_self : hC.extendVal hwa hfin a C = a := by
  refine (hC.bijective_meromorphicFunctionSheaf_map_prodFst hwa hfin C).injective ?_
  rw [hC.map_prodFst_extendVal hwa hfin a C, hC.prodFst_self_eq_prodSnd]

/-- **A meromorphic function on `X` is determined by, and may be prescribed as, its restriction
to a generic chart.**

Injectivity: two meromorphic functions with the same value at `C` have the same value at
`U ×_X C` for every chart `U`, being the restriction there of that common value, hence the same
value at `U` by `IsGenericChart.bijective_meromorphicFunctionSheaf_map_prodFst`.

Surjectivity: the family of
`AlgebraicGeometry.Space.CodimensionZeroPresentation.IsGenericChart.extendVal` is a compatible
family of sections whose value at `C` is the prescribed one. -/
theorem IsGenericChart.bijective_val_genericChart :
    Function.Bijective (fun m : MeromorphicFunction B S hS X.1 X.2 => m.val (op C)) := by
  refine ⟨fun m m' h => ?_, fun b => ?_⟩
  · have h' : m.val (op C) = m'.val (op C) := h
    refine Subtype.ext (funext fun V => ?_)
    obtain ⟨U⟩ := V
    refine (hC.bijective_meromorphicFunctionSheaf_map_prodFst hwa hfin U).injective ?_
    rw [meromorphicFunction_val_naturality m (SmallEtale.prodFst B S hS X.1 U C),
      meromorphicFunction_val_naturality m' (SmallEtale.prodFst B S hS X.1 U C),
      ← meromorphicFunction_val_naturality m (SmallEtale.prodSnd B S hS X.1 U C),
      ← meromorphicFunction_val_naturality m' (SmallEtale.prodSnd B S hS X.1 U C), h']
  · exact ⟨hC.extend hwa hfin b, hC.extendVal_self hwa hfin b⟩

/-- **The meromorphic functions on `X` are the sections of `𝒦_X` over a generic chart**, as
rings. -/
noncomputable def IsGenericChart.genericChartSectionsRingEquiv :
    MeromorphicFunction B S hS X.1 X.2 ≃+*
      (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op C) :=
  RingEquiv.ofBijective (meromorphicFunctionValRingHom C)
    (hC.bijective_val_genericChart hwa hfin)

end CodimensionZeroPresentation

end GlobalSections

end AlgebraicGeometry.Space

end
