module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodCofiltered
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Rational functions at the generic point of an integral algebraic space

Let `X` be an integral algebraic space over a scheme `S`, in the sense of Tag 0AD4. Its point
space is irreducible, and it is sober because the space is decent, so it has a generic point
`η`, a point whose closure is the whole point space. Every dense open subspace of `X` contains
`η`, so the monomorphism from the spectrum of the residue field `κ(η)` of Tag 0EMW factors
uniquely through the domain of every dense-open representative of a rational function.
Pulling the coordinate of a representative back along that factorization is a well-defined
ring homomorphism from the ring `R(X)` of rational functions of Tag 0EMP to `κ(η)`: this is
the comparison of Tag 0END which does not involve the henselian local ring at `η`.

## Main definitions

* `AlgebraicGeometry.Space.genericPoint` is the generic point of an integral algebraic space
  over `S`.
* `AlgebraicGeometry.Space.factorsThroughDenseOpens_fieldMorphism` records that the presenting
  morphism of a field-valued representative of the generic point factors through every dense
  open subspace, and `AlgebraicGeometry.Space.genericLiftData` is the chosen factorization
  through a given one, together with the factorization identity.
* `AlgebraicGeometry.Space.evalRingHom` is evaluation at the generic point, as a ring
  homomorphism from the rational functions to the field of a field-valued representative of
  that point.
* `AlgebraicGeometry.Space.genericRep` is the chosen monomorphic field-valued representative
  of the generic point, whose field is the residue field of Tag 0EMW.
* `AlgebraicGeometry.Space.rationalFunctionsRingEquiv` is the identification of Tag 0END of
  the ring of rational functions with the residue field at the generic point.
* `AlgebraicGeometry.Space.residueRingEquivOfIsField` identifies a local ring which happens to
  be a field with its own residue field.
* `AlgebraicGeometry.Space.genericNeighborhood` is the elementary étale neighbourhood of the
  generic point produced by Tag 0BBP.
* `AlgebraicGeometry.Space.genericNeighborhoodFieldPoint` is the residue field of an elementary
  étale neighbourhood of the generic point at its marked point, viewed as a field-valued
  representative of that point, and `AlgebraicGeometry.Space.evalNeighborhoodRingEquiv` is the
  resulting identification of the rational functions with that residue field.
* `AlgebraicGeometry.Space.neighborhoodStalkHenselianRingEquiv` identifies the local ring of
  such a neighbourhood at its marked point with the henselian local ring of Tag 0BGW at the
  generic point, and `AlgebraicGeometry.Space.rationalFunctionsHenselianRingEquiv` and
  `AlgebraicGeometry.Space.residueFieldHenselianRingEquiv` are the two remaining
  identifications of Tag 0END, both unconditional: the neighbourhood they are built from is
  `AlgebraicGeometry.Space.genericNeighborhood`, and
  `AlgebraicGeometry.Space.rationalFunctionsHenselianRingEquivOfNeighborhood` is the comparison
  built from an arbitrary one.

## Main results

* `AlgebraicGeometry.Space.isGenericPoint_genericPoint`: the chosen point is generic.
* `AlgebraicGeometry.Space.dense_of_genericPoint_mem` and
  `AlgebraicGeometry.Space.genericPoint_mem_range_pointsMap_ι`: a set of points containing the
  generic point is dense, and the generic point lies in the point set of every dense open
  subspace.
* `AlgebraicGeometry.Space.evalPartial_eq` pins evaluation down on a representative: it is
  computed by *any* factorization of the residue-field morphism through the domain.
* `AlgebraicGeometry.Space.evalRingHom_eq_appTop` computes evaluation on a representable
  presheaf mapping into the domain of a representative, as the pullback of the coordinate of
  the representative along the induced morphism of schemes.
* `AlgebraicGeometry.Space.exists_chart`: an integral algebraic space has a representable
  open chart whose point set contains the generic point, by Tag 086U.
* `AlgebraicGeometry.Space.exists_factor_through_chart`: a morphism whose point set lies in
  that of a representable open chart factors through the chart, by Tag 03IE.
* `AlgebraicGeometry.Space.evaluation_injective_of_closure_eq_univ` and
  `AlgebraicGeometry.Space.exists_evaluation_eq`: on an integral scheme, evaluation at a point
  whose closure is the whole space is injective on sections over any open neighbourhood, and
  every element of the residue field there is the value of such a section.
* `AlgebraicGeometry.Space.isField_residueField_genericPoint`: the residue field at the
  generic point is a field.
* `AlgebraicGeometry.Space.ΓSpecIso_appLE_eq_descResidueField_evaluation`: pulling a regular
  function back along a morphism from the spectrum of a field is evaluating it at the image
  point, read through the homomorphism out of the residue field there, and
  `AlgebraicGeometry.Space.appTop_injective_of_closure_eq_univ`: on an integral scheme that
  pullback is injective as soon as the image point is dense.
* `AlgebraicGeometry.Space.exists_isDenseOpenSubspace_isRepresentable_le`: every dense open
  subspace of an integral algebraic space contains a representable dense open subspace.
* `AlgebraicGeometry.Space.evalRingHom_injective`,
  `AlgebraicGeometry.Space.evalRingHom_surjective` and
  `AlgebraicGeometry.Space.evalRingHom_bijective`: evaluation at the generic point is a
  bijection onto the field of a *monomorphic* field-valued representative of that point.
* `AlgebraicGeometry.Space.rationalFunctionsRingEquiv_toRationalMap` pins the identification
  down: on a dense-open representative it is computed by any factorization of the
  residue-field morphism through the domain.
* `AlgebraicGeometry.Space.isField_rationalFunctions`: **Stacks 0END**, the ring of rational
  functions of an integral algebraic space over `S` is a field.
* `AlgebraicGeometry.Space.isField_neighborhoodStalk_genericPoint`: the local ring of an
  elementary étale neighbourhood of the generic point at its marked point is a field.
* `AlgebraicGeometry.Space.isField_henselianLocalRing_genericPoint`: **Stacks 0END**, the
  henselian local ring at the generic point is a field, and
  `AlgebraicGeometry.Space.bijective_stalkToHenselianLocalRing_genericPoint`: the canonical map
  of Tag 0EMY into it is bijective there.
* `AlgebraicGeometry.Space.rationalFunctionsHenselianRingEquivOfNeighborhood_eq` and
  `AlgebraicGeometry.Space.rationalFunctionsHenselianRingEquivOfNeighborhood_toRationalMap` pin
  the identification with the henselian local ring down: it carries a rational function to the
  canonical image of any element of the local ring whose residue is the value of that function
  at the generic point, computed on a dense-open representative by *any* factorization of the
  residue-field morphism through the domain.
* `AlgebraicGeometry.Space.rationalFunctionsHenselianRingEquiv_eq_trans`: **Stacks 0END**, the
  three identifications are the edges of one commuting triangle, which is what the single chain
  `R(X) = O^h_{X,η} = κ(η)` of the tag asserts.

## Implementation notes

The generic point is Mathlib's `genericPoint` for the topology
`AlgebraicGeometry.Space.pointTopology` of Tag 03BX, which applies because the point space of
an integral algebraic space is irreducible by definition and quasi-sober by Tag 03K6. It is
therefore an honest construction rather than a choice out of an existence statement; the
precedent `AlgebraicGeometry.Space.PrimeDivisor.genericPoint` has to choose, because there the
generic point is only recorded existentially inside a structure.

Evaluation is characterized rather than merely constructed. The factorization of the
residue-field morphism through a dense open subspace is produced by Tag 03IE, which is an
existence statement, so `AlgebraicGeometry.Space.genericLiftData` chooses one, in the idiom of
`AlgebraicGeometry.Space.residueFieldHomData`; but the factorization is unique, the inclusion
of an open subspace being a monomorphism, and
`AlgebraicGeometry.Space.evalPartial_eq` therefore computes evaluation from any factorization
at all. That identity is what pins the comparison down.

Evaluation and its ring-homomorphism property are the general construction of
`StacksFrontier/AlgebraicGeometry/Spaces/RationalFunctionsEvaluation.lean` — pullback of rational
functions along a morphism from a site object which factors through every dense open subspace
— specialized to the field spectrum of the representative, whose presenting morphism factors
through every dense open subspace by `AlgebraicGeometry.Space.exists_genericLift`; the value
in the field is read off through `AlgebraicGeometry.Scheme.ΓSpecIso`. That general
construction is in turn built from the characterization of the ring structure in Tag 0EMP
rather than from the construction behind it, because the auxiliary direct limit of
`StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctions` is private.

Bijectivity of evaluation, the remaining step of Tag 0END, is proved on a representable dense
open chart through the generic point. Tag 086U provides such a chart inside any dense open
subspace; the scheme representing it is integral, being reduced because reducedness is an
étale-local property and an open immersion is étale, and irreducible because the point of it
below the generic point is dense; and Tag 03E1 identifies the field of a monomorphic
field-valued representative of the generic point with the residue field of the chart at that
point, because the spectrum of that residue field is a second monomorphic representative of
the same point of the chart. Injectivity is then injectivity of evaluation of regular
functions at a dense point of an integral scheme, and surjectivity comes from writing an
element of the residue field as the value of a regular function on a smaller open set and
taking a representable chart inside the dense open subspace that open set cuts out.

The comparison between a pullback of regular functions and an evaluation is stated for schemes
alone, in `AlgebraicGeometry.Space.ΓSpecIso_appLE_eq_descResidueField_evaluation`, and the
factorization of a pullback through an intermediate scheme is isolated in
`AlgebraicGeometry.Space.appTop_appLE_comp`, whose morphism equality is a hypothesis: the
restriction maps of `AlgebraicGeometry.Scheme.Hom.appLE` carry a proof that depends on the
morphism, so rewriting the morphism underneath one is only possible after that equality has
been substituted away.

Two auxiliary facts about the relative affine line are re-proved here: that a point of it is
determined by its coordinate, and that every global section is the coordinate of a point.
`StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctions` establishes both, but as private
auxiliaries of its construction of the ring structure, so they are not available to import.

The henselian half of Tag 0END needs one input beyond the comparison with the residue field:
nonemptiness of the category of elementary étale neighbourhoods of a point of a decent algebraic
space, which is Tag 0BBP. An integral algebraic space is decent, so that tag applies to the
generic point and `AlgebraicGeometry.Space.genericNeighborhood` is the neighbourhood `E` it
produces; cofilteredness of the category, which Tag 0EMY asks for, then follows from Tag 0BGV.
Over the generic point the local ring of `E` at
its marked point is a field: it is reduced, reducedness being an étale-local property of
schemes, and of Krull dimension zero, because the generic point is a point of codimension zero
by Tag 0ABV and the dimension of the local ring of an algebraic space is measured on an étale
chart by Tag 0BAM. The henselian local ring is a henselisation of that local ring by Tag 0EMY,
and a henselisation of a field is that field — its maximal ideal is generated by the zero ideal
— so the canonical map out of the local ring is bijective. The residue field of `E` at its
marked point is the residue field of that local ring, and it is a monomorphic field-valued
representative of the generic point by the data of Tag 0BGU, so evaluation onto it is bijective;
composing the three bijections identifies the rational functions with the henselian local ring.

Tag 0END is covered by several declarations here rather than one, each registered against the
tag with the clause of it that the declaration accounts for.

## References

* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0EMP](https://stacks.math.columbia.edu/tag/0EMP)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0END](https://stacks.math.columbia.edu/tag/0END)
* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0BGV](https://stacks.math.columbia.edu/tag/0BGV)
* [Stacks Project, Tag 0BGW](https://stacks.math.columbia.edu/tag/0BGW)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Formal properties of open immersions of algebraic spaces -/

/-- An open immersion of presheaves on the big fppf site of `S` is étale in the relative
sense: an open immersion of schemes is étale. -/
private theorem presheafEtale_of_isOpenImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hf : IsOpenImmersion B S hS f) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  have hmono : MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) ≤
      MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) := by
    intro A C g hg
    have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map g) := hg
    change AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g)
    infer_instance
  exact MorphismProperty.relative_monotone hmono f hf

/-- The range of an open immersion into an algebraic space is an open subspace. -/
private theorem isOpenSubspace_range {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (f : A ⟶ X) (hf : IsOpenImmersion B S hS f) :
    IsOpenSubspace B S hS (Subfunctor.range f) := by
  have : Mono f := mono_of_isOpenImmersion B S hS f hf
  have : IsIso (Subfunctor.toRange f) := inferInstance
  refine ⟨hA.of_iso (asIso (Subfunctor.toRange f)), ?_⟩
  rw [← inv_toRange_comp f]
  exact MorphismProperty.RespectsIso.precomp _ (asIso (Subfunctor.toRange f)).inv f hf

/-! ### The generic point of an integral algebraic space -/

/-- The generic point of an integral algebraic space over `S`: its point space is
irreducible, and it is quasi-sober because the space is decent. -/
noncomputable def genericPoint (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) : points B S hS X :=
  letI : QuasiSober (points B S hS X) :=
    quasiSober_points_of_isDecentSpace B S hS hX hInt.2.1
  letI : IrreducibleSpace (points B S hS X) := hInt.2.2
  _root_.genericPoint (points B S hS X)

/-- The point selected by `AlgebraicGeometry.Space.genericPoint` is a generic point of the
whole point space. -/
theorem isGenericPoint_genericPoint (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) :
    IsGenericPoint (genericPoint B S hS hX hInt) (Set.univ : Set (points B S hS X)) := by
  let : QuasiSober (points B S hS X) :=
    quasiSober_points_of_isDecentSpace B S hS hX hInt.2.1
  let : IrreducibleSpace (points B S hS X) := hInt.2.2
  exact _root_.genericPoint_spec (points B S hS X)

/-- An open set of points of an integral algebraic space containing the generic point is
dense. -/
theorem dense_of_genericPoint_mem (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) {W : Set (points B S hS X)}
    (hW : genericPoint B S hS hX hInt ∈ W) : Dense W := by
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_univ_subset ?_
  rw [← isGenericPoint_genericPoint B S hS hX hInt]
  exact closure_mono (Set.singleton_subset_iff.mpr hW)

/-- The generic point of an integral algebraic space lies in the point set of every dense
open subspace. -/
theorem genericPoint_mem_range_pointsMap_ι (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) {U : Subfunctor X}
    (hU : IsDenseOpenSubspace B S hS hX U) :
    genericPoint B S hS hX hInt ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  let : IrreducibleSpace (points B S hS X) := hInt.2.2
  have hopen : IsOpen (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.1.2
  refine ((isGenericPoint_genericPoint B S hS hX hInt).mem_open_set_iff hopen).2 ?_
  simpa using hU.2.nonempty

/-! ### Lifting the generic field-valued point into a dense open subspace -/

variable (hX : IsAlgebraicSpace B S hS X) (hInt : IsIntegralSpace B S hS X)

/-- The point space of the presheaf represented by the field spectrum of a field-valued
point has at most one element. -/
private theorem subsingleton_points_siteObject (p : FieldValuedPoint B S hS X) :
    Subsingleton (points B S hS (yoneda.obj (p.siteObject B S hS X))) :=
  ⟨fun _ _ => injective_pointsToScheme B S hS _
    (have := subsingleton_toScheme_siteObject B S hS X p; Subsingleton.elim _ _)⟩

/-- The image of the point space of the field spectrum of a field-valued point under its
presenting morphism is contained in any set containing the point it represents. -/
private theorem range_pointsMap_fieldMorphism_subset (p : FieldValuedPoint B S hS X)
    {W : Set (points B S hS X)} (hW : p.class B S hS X ∈ W) :
    Set.range (pointsMap B S hS (yoneda.obj (p.siteObject B S hS X))
      (fieldMorphism B S hS X p)) ⊆ W := by
  have := subsingleton_points_siteObject B S hS p
  rintro w ⟨r, rfl⟩
  rw [Subsingleton.elim r ((p.tautologicalPoint B S hS X).class B S hS _),
    pointsMap_fieldMorphism_tautologicalPoint]
  exact hW

/-- The presenting morphism of a field-valued representative of the generic point factors
through every dense open subspace, by Stacks 03IE. -/
theorem exists_genericLift (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt) {U : Subfunctor X}
    (hU : IsDenseOpenSubspace B S hS hX U) :
    ∃ j : yoneda.obj (p.siteObject B S hS X) ⟶ U.toFunctor,
      j ≫ U.ι = fieldMorphism B S hS X p :=
  (factorsThrough_openSubspace_iff_points B S hS hX
      (isAlgebraicSpace_yoneda B S hS _) U hU.1 (fieldMorphism B S hS X p)).2
    (range_pointsMap_fieldMorphism_subset B S hS p
      (by rw [hp]; exact genericPoint_mem_range_pointsMap_ι B S hS hX hInt hU))

/-- The presenting morphism of a field-valued representative of the generic point factors
through the dense open subspaces of `X`, in the sense of
`AlgebraicGeometry.Space.FactorsThroughDenseOpens`. -/
theorem factorsThroughDenseOpens_fieldMorphism (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt) :
    FactorsThroughDenseOpens B S hS hX (p.siteObject B S hS X) (fieldMorphism B S hS X p) :=
  fun _ hU => exists_genericLift B S hS hX hInt p hp hU

/-- The chosen factorization of the presenting morphism of a field-valued representative of
the generic point through a dense open subspace, together with the factorization
identity. -/
noncomputable def genericLiftData (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt) {U : Subfunctor X}
    (hU : IsDenseOpenSubspace B S hS hX U) :
    {j : yoneda.obj (p.siteObject B S hS X) ⟶ U.toFunctor //
      j ≫ U.ι = fieldMorphism B S hS X p} :=
  denseOpenLift B S hS hX (factorsThroughDenseOpens_fieldMorphism B S hS hX hInt p hp) hU

/-! ### Evaluation of a rational function at the generic point -/

/-- The value at the generic point of a dense-open representative of a rational function:
the coordinate of the representative pulled back along the lift of the generic field-valued
point, read through the global sections of the field spectrum. -/
noncomputable def evalPartial (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt)
    (f : PartialMap B S hS hX (affineLineFunctor B S hS)) : p.carrier :=
  (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).hom.hom
    (evalSitePartial B S hS hX (factorsThroughDenseOpens_fieldMorphism B S hS hX hInt p hp) f)

/-- Evaluation is computed by any lift of the generic field-valued point. -/
@[stacks 0END "the characterisation of evaluation at the generic point: the value on a \
  representative is its coordinate along any factorisation of the residue-field morphism \
  through the domain, independently of the factorisation"]
theorem evalPartial_eq (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt)
    (f : PartialMap B S hS hX (affineLineFunctor B S hS))
    (j : yoneda.obj (p.siteObject B S hS X) ⟶ f.domain.toFunctor)
    (hj : j ≫ f.domain.ι = fieldMorphism B S hS X p) :
    evalPartial B S hS hX hInt p hp f =
      (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).hom.hom
        (affineLineCoordinate B S hS (Opposite.op (p.siteObject B S hS X))
          (yonedaEquiv (j ≫ f.hom))) :=
  congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).hom.hom t)
    (evalSitePartial_eq B S hS hX
      (factorsThroughDenseOpens_fieldMorphism B S hS hX hInt p hp) f j hj)

/-- Equivalent dense-open representatives have the same value at the generic point. -/
theorem evalPartial_congr (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt)
    {f g : PartialMap B S hS hX (affineLineFunctor B S hS)}
    (h : PartialMap.Equivalent B S hS f g) :
    evalPartial B S hS hX hInt p hp f = evalPartial B S hS hX hInt p hp g :=
  congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).hom.hom t)
    (evalSitePartial_congr B S hS hX
      (factorsThroughDenseOpens_fieldMorphism B S hS hX hInt p hp) h)

/-- The value of a rational function at the generic point. -/
noncomputable def evalFun (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt) :
    rationalFunctions B S hS hX → p.carrier :=
  Quotient.lift (evalPartial B S hS hX hInt p hp)
    (fun _ _ h => evalPartial_congr B S hS hX hInt p hp h)

@[simp]
theorem evalFun_toRationalMap (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt)
    (f : PartialMap B S hS hX (affineLineFunctor B S hS)) :
    evalFun B S hS hX hInt p hp (f.toRationalMap B S hS) =
      evalPartial B S hS hX hInt p hp f := rfl

/-! ### Evaluation is a ring homomorphism -/

/-- Evaluation at the generic point is the general evaluation on the chart given by the field
spectrum of the representative, read through the global sections of that spectrum. -/
private theorem evalFun_eq_evalSiteFun (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt)
    (x : rationalFunctions B S hS hX) :
    evalFun B S hS hX hInt p hp x =
      (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).hom.hom
        (evalSiteFun B S hS hX
          (factorsThroughDenseOpens_fieldMorphism B S hS hX hInt p hp) x) := by
  obtain ⟨f, hf⟩ := RationalMap.exists_rep B S hS x
  subst hf
  rfl

/-- Evaluation at the generic point respects addition. -/
theorem evalFun_add (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt)
    (x y : rationalFunctions B S hS hX) :
    evalFun B S hS hX hInt p hp (x + y) =
      evalFun B S hS hX hInt p hp x + evalFun B S hS hX hInt p hp y := by
  rw [evalFun_eq_evalSiteFun, evalFun_eq_evalSiteFun, evalFun_eq_evalSiteFun,
    evalSiteFun_add, map_add]

/-- Evaluation at the generic point respects multiplication. -/
theorem evalFun_mul (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt)
    (x y : rationalFunctions B S hS hX) :
    evalFun B S hS hX hInt p hp (x * y) =
      evalFun B S hS hX hInt p hp x * evalFun B S hS hX hInt p hp y := by
  rw [evalFun_eq_evalSiteFun, evalFun_eq_evalSiteFun, evalFun_eq_evalSiteFun,
    evalSiteFun_mul, map_mul]

/-- Evaluation at the generic point sends zero to zero. -/
theorem evalFun_zero (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt) :
    evalFun B S hS hX hInt p hp 0 = 0 := by
  rw [evalFun_eq_evalSiteFun, evalSiteFun_zero, map_zero]

/-- Evaluation at the generic point sends one to one. -/
theorem evalFun_one (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt) :
    evalFun B S hS hX hInt p hp 1 = 1 := by
  rw [evalFun_eq_evalSiteFun, evalSiteFun_one, map_one]

/-- Evaluation at the generic point, as a ring homomorphism from the rational functions to
the field of a field-valued representative of that point. -/
@[stacks 0END "evaluation of rational functions at the generic point, as a ring homomorphism \
  R(X) → κ(η)"]
noncomputable def evalRingHom (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt) :
    rationalFunctions B S hS hX →+* p.carrier where
  toFun := evalFun B S hS hX hInt p hp
  map_one' := evalFun_one B S hS hX hInt p hp
  map_mul' := evalFun_mul B S hS hX hInt p hp
  map_zero' := evalFun_zero B S hS hX hInt p hp
  map_add' := evalFun_add B S hS hX hInt p hp


/-! ### Evaluation computed on a representable chart -/

/-- Evaluation at the generic point, computed on a representable presheaf mapping into the
domain of a representative: it is the pullback to the field spectrum of the coordinate of the
representative restricted to that chart. -/
theorem evalRingHom_eq_appTop (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt)
    (f : PartialMap B S hS hX (affineLineFunctor B S hS)) (C : BigFppfOver B S hS)
    (γ : yoneda.obj C ⟶ f.domain.toFunctor) (g : p.siteObject B S hS X ⟶ C)
    (hg : yoneda.map g ≫ γ ≫ f.domain.ι = fieldMorphism B S hS X p) :
    evalRingHom B S hS hX hInt p hp (f.toRationalMap B S hS) =
      (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).hom.hom
        (((BigFppfOver.toScheme B S hS).map g).appTop
          (affineLineCoordinate B S hS (Opposite.op C) (yonedaEquiv (γ ≫ f.hom)))) := by
  change evalPartial B S hS hX hInt p hp f = _
  rw [evalPartial_eq B S hS hX hInt p hp f (yoneda.map g ≫ γ)
      (by rw [Category.assoc]; exact hg),
    Category.assoc, ← yonedaEquiv_naturality, affineLineCoordinate_map]
  rfl

/-! ### Factoring through a representable open chart -/

/-- Precomposing with an isomorphism does not change the point set of a morphism. -/
private theorem range_pointsMap_iso_hom_comp {A A' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : A ≅ A') (f : A' ⟶ X) :
    Set.range (pointsMap B S hS A (e.hom ≫ f)) = Set.range (pointsMap B S hS A' f) := by
  have hsurj : Function.Surjective (pointsMap B S hS A e.hom) :=
    (pointsHomeomorphOfIso B S hS e).surjective
  rw [pointsMap_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]

/-- The point set of a monomorphism is the point set of its range. -/
private theorem range_pointsMap_eq_range_ι {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : A ⟶ X)
    [Mono f] :
    Set.range (pointsMap B S hS A f) =
      Set.range (pointsMap B S hS (Subfunctor.range f).toFunctor (Subfunctor.range f).ι) := by
  simpa using range_pointsMap_iso_hom_comp B S hS (asIso (Subfunctor.toRange f))
    (Subfunctor.range f).ι

/-- A morphism of algebraic spaces whose point set lies in that of a representable open chart
factors through the chart, by Stacks 03IE applied to the range of the chart. -/
theorem exists_factor_through_chart (hX : IsAlgebraicSpace B S hS X)
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hA : IsAlgebraicSpace B S hS A)
    (C : BigFppfOver B S hS) (α : yoneda.obj C ⟶ X) (hα : IsOpenImmersion B S hS α)
    (f : A ⟶ X)
    (hsub : Set.range (pointsMap B S hS A f) ⊆
      Set.range (pointsMap B S hS (yoneda.obj C) α)) :
    ∃ k : A ⟶ yoneda.obj C, k ≫ α = f := by
  have : Mono α := mono_of_isOpenImmersion B S hS α hα
  obtain ⟨k₀, hk₀⟩ := (factorsThrough_openSubspace_iff_points B S hS hX hA
    (Subfunctor.range α) (isOpenSubspace_range B S hS (isAlgebraicSpace_yoneda B S hS C) α hα)
    f).2 (by rw [← range_pointsMap_eq_range_ι B S hS α]; exact hsub)
  refine ⟨k₀ ≫ (asIso (Subfunctor.toRange α)).inv, ?_⟩
  rw [Category.assoc, inv_toRange_comp α]
  exact hk₀

/-- An integral algebraic space over `S` has a representable open chart whose point set
contains the generic point: Stacks 086U supplies a representable open subspace with dense
point set, and the generic point lies in the point set of every dense open subspace. -/
theorem exists_chart (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) :
    ∃ (C : BigFppfOver B S hS) (α : yoneda.obj C ⟶ X), IsOpenImmersion B S hS α ∧
      genericPoint B S hS hX hInt ∈ Set.range (pointsMap B S hS (yoneda.obj C) α) := by
  obtain ⟨G, hG, hGrep, hGdense⟩ :=
    exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace B S hS hX hInt.2.1
  have : G.toFunctor.IsRepresentable := hGrep
  refine ⟨G.toFunctor.reprX, G.toFunctor.reprW.hom ≫ G.ι,
    MorphismProperty.RespectsIso.precomp _ G.toFunctor.reprW.hom G.ι hG.2, ?_⟩
  obtain ⟨y, hy⟩ := genericPoint_mem_range_pointsMap_ι B S hS hX hInt (U := G) ⟨hG, hGdense⟩
  refine ⟨pointsMap B S hS G.toFunctor G.toFunctor.reprW.inv y, ?_⟩
  change (pointsMap B S hS _ (G.toFunctor.reprW.hom ≫ G.ι) ∘
    pointsMap B S hS _ G.toFunctor.reprW.inv) y = _
  rw [← pointsMap_comp, Iso.inv_hom_id_assoc]
  exact hy

/-! ### Evaluation at a generic point of an integral scheme -/

/-- The residue map of a local ring which is a field is injective: its kernel is the maximal
ideal, which is the zero ideal. -/
private theorem injective_residue_of_isField_aux {R : Type*} [CommRing R] [IsLocalRing R]
    (h : IsField R) : Function.Injective (IsLocalRing.residue R) := by
  let : Field R := h.toField
  exact (RingHom.injective_iff_ker_eq_bot _).2
    (by rw [IsLocalRing.ker_residue, IsLocalRing.maximalIdeal_eq_bot])

/-- On an integral scheme, evaluation at a point whose closure is the whole space is
injective on the sections over any open neighbourhood: the germ map at that point is
injective, and the stalk is a field, so its residue map is injective. -/
theorem evaluation_injective_of_closure_eq_univ {Y : Scheme.{u}} [IsIntegral Y] (y : Y)
    (hy : closure ({y} : Set Y) = Set.univ) (W : Y.Opens) (hyW : y ∈ W) :
    Function.Injective (Y.evaluation W y hyW) := by
  have hfield : IsField (Y.presheaf.stalk y) := by
    refine isField_stalk_of_closure_mem_irreducibleComponents Y y ?_
    rw [hy, irreducibleComponents_eq_singleton]
    exact rfl
  intro s t hst
  exact germ_injective_of_isIntegral Y y hyW (injective_residue_of_isField_aux hfield hst)

/-- On an integral scheme, every element of the residue field at a point whose closure is
the whole space is the value at that point of a section over some open neighbourhood. -/
theorem exists_evaluation_eq {Y : Scheme.{u}} [IsIntegral Y] (y : Y)
    (k : Y.residueField y) :
    ∃ (W : Y.Opens) (hyW : y ∈ W) (s : Γ(Y, W)), Y.evaluation W y hyW s = k := by
  obtain ⟨τ, hτ⟩ := Y.residue_surjective y k
  obtain ⟨W, hyW, s, hs⟩ := Y.presheaf.exists_germ_eq τ
  exact ⟨W, hyW, s, by rw [← hτ, ← hs]; rfl⟩

/-! ### The chosen field-valued representative of the generic point -/

/-- The chosen monomorphic field-valued representative of the generic point of an integral
algebraic space. -/
noncomputable abbrev genericRep (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) : FieldValuedPoint B S hS X :=
  (residueFieldRepresentative B S hS X hInt.2.1 (genericPoint B S hS hX hInt)).1

/-- The chosen representative represents the generic point. -/
theorem genericRep_class (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) :
    (genericRep B S hS hX hInt).class B S hS X = genericPoint B S hS hX hInt :=
  (residueFieldRepresentative B S hS X hInt.2.1 (genericPoint B S hS hX hInt)).2.1

/-! ### The rational functions at the generic point -/

/-- **Stacks 0END.** The residue field at the generic point of an integral algebraic space
over `S` is a field. -/
@[stacks 0END "the residue field at the generic point is a field"]
theorem isField_residueField_genericPoint (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) :
    IsField (residueField B S hS X hInt.2.1 (genericPoint B S hS hX hInt)) :=
  Field.toIsField _

/-! ### Comparison with the residue field of a representable chart -/

/-- The value at the closed point of a regular function pulled back along a morphism from the
spectrum of a field: it is the evaluation of the function at the image point, read through the
homomorphism out of the residue field there that the morphism determines. -/
theorem ΓSpecIso_appLE_eq_descResidueField_evaluation {K : Type u} [Field K] {Y : Scheme.{u}}
    (ρ : Spec (CommRingCat.of K) ⟶ Y) {V : Y.Opens}
    (hmem : ρ (IsLocalRing.closedPoint K) ∈ V)
    (hle : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ ρ ⁻¹ᵁ V) (s : Γ(Y, V)) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (ρ.appLE V ⊤ hle s) =
      (Y.descResidueField (Scheme.stalkClosedPointTo ρ)).hom (Y.evaluation V _ hmem s) := by
  rw [show Y.evaluation V _ hmem s = (Y.residue _).hom (Y.presheaf.germ V _ hmem s) from rfl,
    show (Y.descResidueField (Scheme.stalkClosedPointTo ρ)).hom
          ((Y.residue _).hom (Y.presheaf.germ V _ hmem s)) =
        (Y.residue _ ≫ Y.descResidueField (Scheme.stalkClosedPointTo ρ))
          (Y.presheaf.germ V _ hmem s) from rfl,
    Scheme.residue_descResidueField,
    show (Scheme.stalkClosedPointTo ρ) (Y.presheaf.germ V _ hmem s) =
        (Y.presheaf.germ V _ hmem ≫ Scheme.stalkClosedPointTo ρ) s from rfl,
    Scheme.germ_stalkClosedPointTo, Scheme.Hom.appLE,
    show (homOfLE hle).op =
        (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem ρ hmem).symm).op.hom from
      Subsingleton.elim _ _]
  rfl

/-- The global version of
`AlgebraicGeometry.Space.ΓSpecIso_appLE_eq_descResidueField_evaluation`: the pullback of a
global regular function along a morphism from the spectrum of a field is its value at the
image point. -/
theorem ΓSpecIso_appTop_eq_descResidueField_evaluation {K : Type u} [Field K] {Y : Scheme.{u}}
    (ρ : Spec (CommRingCat.of K) ⟶ Y) (s : Γ(Y, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (ρ.appTop s) =
      (Y.descResidueField (Scheme.stalkClosedPointTo ρ)).hom
        (Y.evaluation ⊤ _ trivial s) := by
  rw [← Stacks.AffineAlgebraEquivalence.appLE_top_top ρ le_top]
  exact ΓSpecIso_appLE_eq_descResidueField_evaluation ρ (V := ⊤) trivial le_top s

/-- On an integral scheme, pullback of global regular functions along a morphism from the
spectrum of a field whose image point is dense is injective: the pullback is evaluation at
that point followed by an extension of residue fields. -/
theorem appTop_injective_of_closure_eq_univ {K : Type u} [Field K] {Y : Scheme.{u}}
    [IsIntegral Y] (ρ : Spec (CommRingCat.of K) ⟶ Y)
    (hdense : closure ({ρ (IsLocalRing.closedPoint K)} : Set Y) = Set.univ) :
    Function.Injective ρ.appTop := by
  intro a b hab
  refine evaluation_injective_of_closure_eq_univ (ρ (IsLocalRing.closedPoint K)) hdense ⊤ trivial
    ((Y.descResidueField (Scheme.stalkClosedPointTo ρ)).hom.injective ?_)
  rw [← ΓSpecIso_appTop_eq_descResidueField_evaluation ρ a,
    ← ΓSpecIso_appTop_eq_descResidueField_evaluation ρ b, hab]

/-- A topological space with a dense point is irreducible. -/
private theorem irreducibleSpace_of_closure_singleton_eq_univ {T : Type*}
    [TopologicalSpace T] (t : T) (h : closure ({t} : Set T) = Set.univ) :
    IrreducibleSpace T :=
  have hirr : IsIrreducible (Set.univ : Set T) := h ▸ isIrreducible_singleton.closure
  { isPreirreducible_univ := hirr.2, toNonempty := ⟨t⟩ }

/-- A point belonging to every nonempty open set is dense. -/
private theorem closure_singleton_eq_univ_of_mem {T : Type*} [TopologicalSpace T] (t : T)
    (h : ∀ V : Set T, IsOpen V → V.Nonempty → t ∈ V) :
    closure ({t} : Set T) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro w
  by_contra hw
  exact h (closure ({t} : Set T))ᶜ (isOpen_compl_iff.2 isClosed_closure) ⟨w, hw⟩
    (subset_closure rfl)

/-! ### Representable charts through the generic point -/

/-- A dense open subspace of an integral algebraic space contains a representable dense open
subspace: Stacks 086U produces a representable open subspace of it whose point set is
nonempty, and the generic point lies in every nonempty open set of points. -/
theorem exists_isDenseOpenSubspace_isRepresentable_le (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) {U : Subfunctor X}
    (hU : IsDenseOpenSubspace B S hS hX U) :
    ∃ H : Subfunctor X, IsDenseOpenSubspace B S hS hX H ∧ H ≤ U ∧
      H.toFunctor.IsRepresentable := by
  let : IrreducibleSpace (points B S hS X) := hInt.2.2
  obtain ⟨H, hHU, hHopen, hHrep, hHne⟩ :=
    exists_isRepresentable_isOpenSubspace_nonempty_of_isDecentSpace B S hS hX hInt.2.1 U hU.1
      hU.2.nonempty
  refine ⟨H, ⟨hHopen, dense_of_genericPoint_mem B S hS hX hInt ?_⟩, hHU, hHrep⟩
  exact ((isGenericPoint_genericPoint B S hS hX hInt).mem_open_set_iff
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS H.ι hHopen.2)).2 (by simpa using hHne)

/-- The scheme point underlying the tautological point of the presheaf represented by the site
object of a field-valued point is the closed point of the field spectrum. -/
private theorem pointsToScheme_tautologicalPoint
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : FieldValuedPoint B S hS F) :
    pointsToScheme B S hS (q.siteObject B S hS F)
        ((q.tautologicalPoint B S hS F).class B S hS (yoneda.obj (q.siteObject B S hS F))) =
      IsLocalRing.closedPoint q.carrier := by
  have h := (BigFppfOver.toScheme B S hS).map_id (q.siteObject B S hS F)
  change (BigFppfOver.toScheme B S hS).map (𝟙 (q.siteObject B S hS F))
      (IsLocalRing.closedPoint q.carrier) = _
  exact congrArg (fun f ↦ f (IsLocalRing.closedPoint q.carrier)) h

/-- The map from the points of the scheme representing a chart of an algebraic space to the
point space of the space, through the identification of the points of a represented presheaf
with the points of the representing scheme. -/
private noncomputable def chartPointMap (C : BigFppfOver B S hS) (β : yoneda.obj C ⟶ X) :
    (BigFppfOver.toScheme B S hS).obj C → points B S hS X :=
  fun t ↦ pointsMap B S hS (yoneda.obj C) β ((schemePointsHomeomorph B S hS C).symm t)

/-- A chart whose morphism to the space is a monomorphism is injective on points. -/
private theorem chartPointMap_injective (C : BigFppfOver B S hS) (β : yoneda.obj C ⟶ X)
    [Mono β] : Function.Injective (chartPointMap B S hS C β) :=
  (pointsMap_injective_of_mono B S hS β).comp (schemePointsHomeomorph B S hS C).symm.injective

/-- The point set of a chart is the image of the points of its scheme. -/
private theorem range_chartPointMap (C : BigFppfOver B S hS) (β : yoneda.obj C ⟶ X) :
    Set.range (chartPointMap B S hS C β) =
      Set.range (pointsMap B S hS (yoneda.obj C) β) := by
  rw [show chartPointMap B S hS C β =
      pointsMap B S hS (yoneda.obj C) β ∘ (schemePointsHomeomorph B S hS C).symm from rfl,
    Set.range_comp, (schemePointsHomeomorph B S hS C).symm.surjective.range_eq, Set.image_univ]

/-- An open set of points of the scheme of an open chart has open image in the point space. -/
private theorem isOpen_image_chartPointMap (C : BigFppfOver B S hS) (β : yoneda.obj C ⟶ X)
    (hβ : IsOpenImmersion B S hS β)
    {V : Set ((BigFppfOver.toScheme B S hS).obj C)} (hV : IsOpen V) :
    IsOpen (chartPointMap B S hS C β '' V) := by
  rw [show chartPointMap B S hS C β '' V =
      pointsMap B S hS (yoneda.obj C) β '' ((schemePointsHomeomorph B S hS C).symm '' V) from
    Set.image_comp _ _ V]
  exact isOpenMap_pointsMap_of_isOpenImmersion B S hS β hβ _
    ((schemePointsHomeomorph B S hS C).symm.isOpenMap V hV)

/-- Composing a chart with a morphism of the site refines the chart along the induced morphism
of schemes. -/
private theorem chartPointMap_comp {C C' : BigFppfOver B S hS} (β : yoneda.obj C ⟶ X)
    (c : C' ⟶ C) :
    chartPointMap B S hS C' (yoneda.map c ≫ β) =
      chartPointMap B S hS C β ∘ (BigFppfOver.toScheme B S hS).map c := by
  funext t
  have h : (schemePointsHomeomorph B S hS C).symm
        ((BigFppfOver.toScheme B S hS).map c t) =
      pointsMap B S hS (yoneda.obj C') (yoneda.map c)
        ((schemePointsHomeomorph B S hS C').symm t) := by
    refine ((schemePointsHomeomorph B S hS C).symm_apply_eq).2 ?_
    rw [schemePointsHomeomorph_apply, pointsToScheme_pointsMap, ←
      schemePointsHomeomorph_apply, Homeomorph.apply_symm_apply]
  change pointsMap B S hS (yoneda.obj C') (yoneda.map c ≫ β) _ =
      pointsMap B S hS (yoneda.obj C) β _
  rw [h, pointsMap_comp]
  rfl

/-- The point of the scheme of a representable open chart which hits the generic point is
dense: a nonempty open set of that scheme has open nonempty image in the point space, so it
contains the generic point, which has a unique preimage. -/
private theorem closure_singleton_eq_univ_of_chartPointMap_eq
    (hX : IsAlgebraicSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (C : BigFppfOver B S hS) (β : yoneda.obj C ⟶ X) (hβ : IsOpenImmersion B S hS β)
    (z : (BigFppfOver.toScheme B S hS).obj C)
    (hz : chartPointMap B S hS C β z = genericPoint B S hS hX hInt) :
    closure ({z} : Set ((BigFppfOver.toScheme B S hS).obj C)) = Set.univ := by
  have : Mono β := mono_of_isOpenImmersion B S hS β hβ
  refine closure_singleton_eq_univ_of_mem z fun V hV hVne ↦ ?_
  obtain ⟨v, hvV, hv⟩ :=
    ((isGenericPoint_genericPoint B S hS hX hInt).mem_open_set_iff
      (isOpen_image_chartPointMap B S hS C β hβ hV)).2
      (by simpa using hVne.image (chartPointMap B S hS C β))
  rwa [chartPointMap_injective B S hS C β (hv.trans hz.symm)] at hvV

/-- The scheme of a representable open chart of an integral algebraic space through the generic
point is an integral scheme: it is reduced because reducedness is an étale-local property and
an open immersion is étale, and irreducible because the point hitting the generic point is
dense. -/
private theorem isIntegral_chart (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) (C : BigFppfOver B S hS) (β : yoneda.obj C ⟶ X)
    (hβ : IsOpenImmersion B S hS β) (z : (BigFppfOver.toScheme B S hS).obj C)
    (hz : chartPointMap B S hS C β z = genericPoint B S hS hX hInt) :
    IsIntegral ((BigFppfOver.toScheme B S hS).obj C) := by
  have : IsReduced ((BigFppfOver.toScheme B S hS).obj C) :=
    (exists_atlas_iff_forall_etale B S hS X (fun Y : Scheme.{u} => IsReduced Y) hX).1 hInt.1 C β
      (presheafEtale_of_isOpenImmersion B S hS β hβ)
  have : IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj C) :=
    irreducibleSpace_of_closure_singleton_eq_univ z
      (closure_singleton_eq_univ_of_chartPointMap_eq B S hS hX hInt C β hβ z hz)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- A representable dense open chart of an integral algebraic space inside a prescribed dense
open subspace, together with the factorization through it of the morphism presented by a
field-valued representative of the generic point, the point of the chart's scheme that
representative hits, and the integrality of that scheme. -/
private theorem exists_chart_data (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt) {U : Subfunctor X}
    (hU : IsDenseOpenSubspace B S hS hX U) :
    ∃ (H : Subfunctor X) (_hH : IsDenseOpenSubspace B S hS hX H) (_ : H ≤ U)
      (C : BigFppfOver B S hS) (e : yoneda.obj C ≅ H.toFunctor)
      (g : p.siteObject B S hS X ⟶ C),
      yoneda.map g ≫ e.hom ≫ H.ι = fieldMorphism B S hS X p ∧
        chartPointMap B S hS C (e.hom ≫ H.ι)
            ((BigFppfOver.toScheme B S hS).map g (IsLocalRing.closedPoint p.carrier)) =
          genericPoint B S hS hX hInt ∧
        IsIntegral ((BigFppfOver.toScheme B S hS).obj C) ∧
        closure ({(BigFppfOver.toScheme B S hS).map g
                    (IsLocalRing.closedPoint p.carrier)} :
          Set ((BigFppfOver.toScheme B S hS).obj C)) = Set.univ := by
  obtain ⟨H, hH, hHU, hHrep⟩ := exists_isDenseOpenSubspace_isRepresentable_le B S hS hX hInt hU
  have hrep : H.toFunctor.IsRepresentable := hHrep
  have hβopen : IsOpenImmersion B S hS (H.toFunctor.reprW.hom ≫ H.ι) :=
    MorphismProperty.RespectsIso.precomp _ H.toFunctor.reprW.hom H.ι hH.1.2
  have hmemβ : p.class B S hS X ∈
      Set.range (pointsMap B S hS (yoneda.obj H.toFunctor.reprX)
        (H.toFunctor.reprW.hom ≫ H.ι)) := by
    rw [range_pointsMap_iso_hom_comp, hp]
    exact genericPoint_mem_range_pointsMap_ι B S hS hX hInt hH
  obtain ⟨k, hk⟩ := exists_factor_through_chart B S hS hX
    (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS X)) H.toFunctor.reprX
    (H.toFunctor.reprW.hom ≫ H.ι) hβopen (fieldMorphism B S hS X p)
    (range_pointsMap_fieldMorphism_subset B S hS p hmemβ)
  have hcomp : yoneda.map (yoneda.preimage k) ≫ H.toFunctor.reprW.hom ≫ H.ι =
      fieldMorphism B S hS X p := by rw [yoneda.map_preimage]; exact hk
  have hz : chartPointMap B S hS H.toFunctor.reprX (H.toFunctor.reprW.hom ≫ H.ι)
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage k)
        (IsLocalRing.closedPoint p.carrier)) = genericPoint B S hS hX hInt := by
    have h1 : (schemePointsHomeomorph B S hS (p.siteObject B S hS X)).symm
        (IsLocalRing.closedPoint p.carrier) =
        (p.tautologicalPoint B S hS X).class B S hS _ :=
      (schemePointsHomeomorph B S hS _).symm_apply_eq.2
        (by rw [schemePointsHomeomorph_apply, pointsToScheme_tautologicalPoint])
    refine (congrFun (chartPointMap_comp B S hS (H.toFunctor.reprW.hom ≫ H.ι)
      (yoneda.preimage k)) _).symm.trans ?_
    rw [hcomp]
    change pointsMap B S hS _ _ _ = _
    rw [h1, pointsMap_fieldMorphism_tautologicalPoint, hp]
  exact ⟨H, hH, hHU, H.toFunctor.reprX, H.toFunctor.reprW, yoneda.preimage k, hcomp, hz,
    isIntegral_chart B S hS hX hInt _ _ hβopen _ hz,
    closure_singleton_eq_univ_of_chartPointMap_eq B S hS hX hInt _ _ hβopen _ hz⟩

/-! ### Injectivity of evaluation at the generic point -/

/-- A point of the relative affine line is determined by its coordinate: the two morphisms to
the affine line agree over the base and on the single coordinate function. -/
private theorem affineLineCoordinate_inj {T : (BigFppfOver B S hS)ᵒᵖ}
    {v w : (affineLineFunctor B S hS).obj T}
    (h : affineLineCoordinate B S hS T v = affineLineCoordinate B S hS T w) : v = w := by
  refine Over.OverMorphism.ext (AffineSpace.hom_ext ?_ ?_)
  · exact (Over.w v).trans (Over.w w).symm
  · intro i
    rw [show i = ULift.up (0 : Fin 1) from Subsingleton.elim _ _]
    exact h

/-- The coordinate of a representative on a representable dense open subspace at a test point
is the pullback of its coordinate at the representing object of the site. -/
private theorem affineLineCoordinate_app_eq {H : Subfunctor X} (C : BigFppfOver B S hS)
    (e : yoneda.obj C ≅ H.toFunctor) (ν : H.toFunctor ⟶ affineLineFunctor B S hS)
    (T : (BigFppfOver B S hS)ᵒᵖ) (y : H.toFunctor.obj T) :
    affineLineCoordinate B S hS T (ν.app T y) =
      ((BigFppfOver.toScheme B S hS).map (e.inv.app T y)).appTop
        (affineLineCoordinate B S hS (Opposite.op C) (yonedaEquiv (e.hom ≫ ν))) := by
  have h : e.hom.app T (e.inv.app T y) = y := by
    rw [← types_comp_apply (e.inv.app T) (e.hom.app T) y, ← NatTrans.comp_app, e.inv_hom_id]
    rfl
  rw [show ((BigFppfOver.toScheme B S hS).map (e.inv.app T y)).appTop
        (affineLineCoordinate B S hS (Opposite.op C) (yonedaEquiv (e.hom ≫ ν))) =
      affineLineCoordinate B S hS T ((affineLineFunctor B S hS).map (e.inv.app T y).op
        (yonedaEquiv (e.hom ≫ ν))) from
    (affineLineCoordinate_map B S hS (e.inv.app T y).op _).symm]
  congr 1
  rw [yonedaEquiv_naturality, ← Category.assoc, yonedaEquiv_comp, yonedaEquiv_comp,
    yonedaEquiv_yoneda_map, h]

/-- Evaluation at the generic point is injective: a rational function whose value there
vanishes has a representative on a representable dense open chart through the generic point,
and the coordinate of that representative, a regular function on an integral scheme, is
determined by its value at the dense point of that scheme. -/
@[stacks 0END "injectivity of evaluation at the generic point"]
theorem evalRingHom_injective (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt) :
    Function.Injective (evalRingHom B S hS hX hInt p hp) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨f, hf⟩ := RationalMap.exists_rep B S hS x
  obtain ⟨H, hH, hHU, C, e, g, hcomp, hzpt, hint, hclosure⟩ :=
    exists_chart_data B S hS hX hInt p hp f.dense_open_domain
  have hxν : PartialMap.toRationalMap B S hS
      (⟨H, hH, Subfunctor.homOfLe hHU ≫ f.hom⟩ :
        PartialMap B S hS hX (affineLineFunctor B S hS)) = x := by
    rw [toRationalMap_restrict B S hS hX f hH hHU, hf]
  have heval := evalRingHom_eq_appTop B S hS hX hInt p hp
    (⟨H, hH, Subfunctor.homOfLe hHU ≫ f.hom⟩ :
      PartialMap B S hS hX (affineLineFunctor B S hS)) C e.hom g hcomp
  rw [hxν, hx] at heval
  have : IsIntegral ((BigFppfOver.toScheme B S hS).obj C) := hint
  have hs : affineLineCoordinate B S hS (Opposite.op C)
      (yonedaEquiv (e.hom ≫ Subfunctor.homOfLe hHU ≫ f.hom)) = 0 := by
    refine appTop_injective_of_closure_eq_univ ((BigFppfOver.toScheme B S hS).map g) hclosure ?_
    rw [map_zero]
    refine ConcreteCategory.injective_of_mono_of_preservesPullback
      (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).hom ?_
    rw [map_zero]
    exact heval.symm
  obtain ⟨z₀, o₀, hz₀, ho₀, hz₀R, ho₀R⟩ := exists_zero_one_rep B S hS hX H hH
  rw [← hxν, ← hz₀R]
  refine (PartialMap.toRationalMap_eq_iff B S hS).2 ⟨H, hH, le_rfl, le_rfl, ?_⟩
  rw [show Subfunctor.homOfLe (le_refl H) = 𝟙 H.toFunctor from rfl, Category.id_comp,
    Category.id_comp]
  refine NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun y ↦ ?_)
  refine affineLineCoordinate_inj B S hS ?_
  rw [hz₀ T y, affineLineCoordinate_app_eq B S hS C e (Subfunctor.homOfLe hHU ≫ f.hom) T y, hs,
    map_zero]

/-! ### Surjectivity of evaluation at the generic point -/

/-- A morphism of the site presenting a field-valued point of a represented presheaf is the
Yoneda image of that morphism. -/
private theorem fieldMorphism_yoneda_eq {C : BigFppfOver B S hS}
    (q : FieldValuedPoint B S hS (yoneda.obj C)) :
    fieldMorphism B S hS (yoneda.obj C) q = yoneda.map q.value :=
  yonedaEquiv.injective (by
    rw [yonedaEquiv_fieldMorphism, yonedaEquiv_yoneda_map])

/-- The field of a field-valued point of a representable presheaf whose presenting morphism is
a monomorphism is the residue field of the representing scheme at the point it hits: the
spectrum of that residue field is another monomorphic representative of the same point, so
Stacks 03E1 identifies the two over the chart, and the identification is the morphism of
spectra induced by the canonical homomorphism out of the residue field. -/
private theorem isIso_descResidueField (C : BigFppfOver B S hS)
    (q : FieldValuedPoint B S hS (yoneda.obj C))
    (hmono : Mono (fieldMorphism B S hS (yoneda.obj C) q))
    (ρ : Spec (CommRingCat.of q.carrier) ⟶ (BigFppfOver.toScheme B S hS).obj C)
    (hρ : (BigFppfOver.toScheme B S hS).map q.value = ρ) :
    IsIso (((BigFppfOver.toScheme B S hS).obj C).descResidueField
      (Scheme.stalkClosedPointTo ρ)) := by
  have hq0value := toScheme_map_schemePointRepresentative_value B S hS C
    (ρ (IsLocalRing.closedPoint q.carrier))
  have hq0mono : Mono (fieldMorphism B S hS (yoneda.obj C)
      (schemePointRepresentative B S hS C (ρ (IsLocalRing.closedPoint q.carrier)))) := by
    rw [fieldMorphism_yoneda_eq]
    have h0 : Mono (((BigFppfOver.toScheme B S hS).obj C).fromSpecResidueField
        (ρ (IsLocalRing.closedPoint q.carrier))) := inferInstance
    have h1 : Mono ((BigFppfOver.toScheme B S hS).map
        (schemePointRepresentative B S hS C (ρ (IsLocalRing.closedPoint q.carrier))).value) := by
      rw [hq0value]; exact h0
    have h2 : Mono (schemePointRepresentative B S hS C
        (ρ (IsLocalRing.closedPoint q.carrier))).value.left :=
      B.inclusion.mono_of_mono_map h1
    have h3 : Mono (schemePointRepresentative B S hS C
        (ρ (IsLocalRing.closedPoint q.carrier))).value := Over.mono_of_mono_left _
    infer_instance
  have hclass : q.class B S hS (yoneda.obj C) =
      (schemePointRepresentative B S hS C
        (ρ (IsLocalRing.closedPoint q.carrier))).class B S hS (yoneda.obj C) := by
    refine injective_pointsToScheme B S hS C ?_
    rw [show pointsToScheme B S hS C
          ((schemePointRepresentative B S hS C
            (ρ (IsLocalRing.closedPoint q.carrier))).class B S hS (yoneda.obj C)) =
        schemePoint B S hS C (schemePointRepresentative B S hS C
          (ρ (IsLocalRing.closedPoint q.carrier))) from rfl,
      schemePointRepresentative_point]
    change (BigFppfOver.toScheme B S hS).map q.value (IsLocalRing.closedPoint q.carrier) = _
    rw [hρ]
  have := hmono
  have := hq0mono
  obtain ⟨e, he⟩ := iso_of_mono_of_point_eq B S hS (yoneda.obj C)
    (isAlgebraicSpace_yoneda B S hS C) q
    (schemePointRepresentative B S hS C (ρ (IsLocalRing.closedPoint q.carrier))) hclass
  have hcomp : (BigFppfOver.toScheme B S hS).map e.hom ≫
      ((BigFppfOver.toScheme B S hS).obj C).fromSpecResidueField
        (ρ (IsLocalRing.closedPoint q.carrier)) = ρ := by
    rw [← hq0value, ← Functor.map_comp,
      show e.hom ≫ (schemePointRepresentative B S hS C
        (ρ (IsLocalRing.closedPoint q.carrier))).value = q.value from he, hρ]
  have hmonoFrom : Mono (((BigFppfOver.toScheme B S hS).obj C).fromSpecResidueField
      (ρ (IsLocalRing.closedPoint q.carrier))) := inferInstance
  have hspec : Spec.map (((BigFppfOver.toScheme B S hS).obj C).descResidueField
      (Scheme.stalkClosedPointTo ρ)) = (BigFppfOver.toScheme B S hS).map e.hom :=
    (cancel_mono (((BigFppfOver.toScheme B S hS).obj C).fromSpecResidueField
        (ρ (IsLocalRing.closedPoint q.carrier)))).1
      ((Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField q.carrier _ ρ).trans
        hcomp.symm)
  have hiso : IsIso (Spec.map (((BigFppfOver.toScheme B S hS).obj C).descResidueField
      (Scheme.stalkClosedPointTo ρ))) := by
    rw [hspec]; exact Functor.map_isIso (BigFppfOver.toScheme B S hS) e.hom
  have h1 : IsIso (Scheme.Spec.map (((BigFppfOver.toScheme B S hS).obj C).descResidueField
      (Scheme.stalkClosedPointTo ρ)).op) := by simpa [Scheme.Spec] using hiso
  exact (isIso_op_iff _).mp
    ((Functor.FullyFaithful.ofFullyFaithful Scheme.Spec).isIso_of_isIso_map _)

/-- The point set of a subspace is contained in the point set of any larger subspace. -/
private theorem range_pointsMap_ι_mono {U V : Subfunctor X} (h : U ≤ V) :
    Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆
      Set.range (pointsMap B S hS V.toFunctor V.ι) := by
  rw [← Subfunctor.homOfLe_ι h, pointsMap_comp, Set.range_comp]
  exact Set.image_subset_range _ _

/-- Restricting a regular function to an open set and pulling it back along a factorization is
pulling it back along the composite. -/
private theorem appTop_appLE_comp {Q Z' Z : Scheme.{u}} {a : Q ⟶ Z'} {b : Z' ⟶ Z} {r : Q ⟶ Z}
    (hr : a ≫ b = r) {W : Z.Opens} (hb : (⊤ : Z'.Opens) ≤ b ⁻¹ᵁ W)
    (hrW : (⊤ : Q.Opens) ≤ r ⁻¹ᵁ W) (s : Γ(Z, W)) :
    a.appTop (b.appLE W ⊤ hb s) = r.appLE W ⊤ hrW s := by
  subst hr
  have h := Scheme.Hom.appLE_comp_appLE a b W ⊤ ⊤ hb le_top
  rw [Stacks.AffineAlgebraEquivalence.appLE_top_top a le_top] at h
  exact congrArg (fun m : Γ(Z, W) ⟶ Γ(Q, ⊤) ↦ (ConcreteCategory.hom m) s) h

/-- Evaluation at the generic point is surjective: the field of a monomorphic representative
of the generic point is the residue field of a representable dense open chart at the point
below the generic point, every element of that residue field is the value of a regular
function on a smaller open set, and that open set carries a representable dense open chart
again. -/
@[stacks 0END "surjectivity of evaluation at the generic point"]
theorem evalRingHom_surjective (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt)
    (hmono : Mono (fieldMorphism B S hS X p)) :
    Function.Surjective (evalRingHom B S hS hX hInt p hp) := by
  intro k
  obtain ⟨H, hH, -, C, e, g, hcomp, hzpt, hint, hclosure⟩ :=
    exists_chart_data B S hS hX hInt p hp (isDenseOpenSubspace_top B S hS hX)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Spec (CommRingCat.of p.carrier) ⟶ (BigFppfOver.toScheme B S hS).obj C,
      (BigFppfOver.toScheme B S hS).map g = ρ := ⟨_, rfl⟩
  rw [hρ] at hzpt hclosure
  have hβopen : IsOpenImmersion B S hS (e.hom ≫ H.ι) :=
    MorphismProperty.RespectsIso.precomp _ e.hom H.ι hH.1.2
  have hβmono : Mono (e.hom ≫ H.ι) := mono_of_isOpenImmersion B S hS _ hβopen
  have hgmono : Mono (yoneda.map g) :=
    have : Mono (yoneda.map g ≫ e.hom ≫ H.ι) := by rw [hcomp]; exact hmono
    mono_of_mono (yoneda.map g) (e.hom ≫ H.ι)
  -- the field of `p` is the residue field of the chart at the point below the generic point
  have hiso := isIso_descResidueField B S hS C
    ({ carrier := p.carrier, field := p.field, contained := p.contained, toBase := p.toBase,
        value := g } : FieldValuedPoint B S hS (yoneda.obj C))
    (by rw [fieldMorphism_yoneda_eq]; exact hgmono) ρ hρ
  obtain ⟨k', hk'⟩ := (ConcreteCategory.bijective_of_isIso
    (((BigFppfOver.toScheme B S hS).obj C).descResidueField
      (Scheme.stalkClosedPointTo ρ))).2 k
  -- a regular function on an open set of the chart with value `k'` at that point
  have : IsIntegral ((BigFppfOver.toScheme B S hS).obj C) := hint
  obtain ⟨W, hzW, s, hs⟩ := exists_evaluation_eq (ρ (IsLocalRing.closedPoint p.carrier)) k'
  -- the dense open subspace cut out by that open set
  have hWopen : IsOpen (chartPointMap B S hS C (e.hom ≫ H.ι) '' (W : Set _)) :=
    isOpen_image_chartPointMap B S hS C _ hβopen W.isOpen
  have hU'points : Set.range (pointsMap B S hS
        (openSubspaceOfPoints B S hS X
          (chartPointMap B S hS C (e.hom ≫ H.ι) '' (W : Set _))).toFunctor
        (openSubspaceOfPoints B S hS X
          (chartPointMap B S hS C (e.hom ≫ H.ι) '' (W : Set _))).ι) =
      chartPointMap B S hS C (e.hom ≫ H.ι) '' (W : Set _) :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hU' : IsDenseOpenSubspace B S hS hX (openSubspaceOfPoints B S hS X
      (chartPointMap B S hS C (e.hom ≫ H.ι) '' (W : Set _))) :=
    ⟨isOpenSubspace_openSubspaceOfPoints B S hS hX _ hWopen,
      dense_of_genericPoint_mem B S hS hX hInt (by rw [hU'points]; exact ⟨_, hzW, hzpt⟩)⟩
  have hU'H : openSubspaceOfPoints B S hS X
      (chartPointMap B S hS C (e.hom ≫ H.ι) '' (W : Set _)) ≤ H := by
    refine le_of_range_pointsMap_ι_subset B S hS hH.1 ?_
    rw [hU'points, ← range_pointsMap_iso_hom_comp B S hS e H.ι, ← range_chartPointMap]
    exact Set.image_subset_range _ _
  -- a representable dense open chart inside it
  obtain ⟨H₃, hH₃, hH₃U', C₃, e₃, g₃, hcomp₃, hzpt₃, -, -⟩ :=
    exists_chart_data B S hS hX hInt p hp hU'
  obtain ⟨c, hc⟩ : ∃ c : C₃ ⟶ C, yoneda.map c ≫ e.hom ≫ H.ι = e₃.hom ≫ H₃.ι := by
    refine ⟨yoneda.preimage (e₃.hom ≫ Subfunctor.homOfLe (hH₃U'.trans hU'H) ≫ e.inv), ?_⟩
    rw [yoneda.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Subfunctor.homOfLe_ι]
  have hg₃c : g₃ ≫ c = g := by
    refine yoneda.map_injective ((cancel_mono (e.hom ≫ H.ι)).1 ?_)
    rw [Functor.map_comp, Category.assoc, hc, hcomp₃, hcomp]
  -- the chart maps into the open set
  have himg : ∀ t : (BigFppfOver.toScheme B S hS).obj C₃,
      (BigFppfOver.toScheme B S hS).map c t ∈ (W : Set _) := by
    intro t
    have h1 : chartPointMap B S hS C (e.hom ≫ H.ι)
          ((BigFppfOver.toScheme B S hS).map c t) =
        chartPointMap B S hS C₃ (e₃.hom ≫ H₃.ι) t := by
      rw [← hc, chartPointMap_comp]
      rfl
    have h2 : chartPointMap B S hS C₃ (e₃.hom ≫ H₃.ι) t ∈
        chartPointMap B S hS C (e.hom ≫ H.ι) '' (W : Set _) := by
      rw [← hU'points]
      refine range_pointsMap_ι_mono B S hS hH₃U' ?_
      rw [← range_pointsMap_iso_hom_comp B S hS e₃ H₃.ι, ← range_chartPointMap]
      exact Set.mem_range_self t
    obtain ⟨w, hwW, hw⟩ := h2
    rw [← h1] at hw
    rwa [chartPointMap_injective B S hS C (e.hom ≫ H.ι) hw] at hwW
  have hle₃ : (⊤ : ((BigFppfOver.toScheme B S hS).obj C₃).Opens) ≤
      (BigFppfOver.toScheme B S hS).map c ⁻¹ᵁ W := fun t _ ↦ himg t
  have hleρ : (⊤ : (Spec (CommRingCat.of p.carrier)).Opens) ≤ ρ ⁻¹ᵁ W :=
    (Scheme.preimage_eq_top_of_closedPoint_mem ρ hzW).ge
  -- the rational function given by the restricted regular function
  refine ⟨PartialMap.toRationalMap B S hS
    (⟨H₃, hH₃, e₃.inv ≫ yonedaEquiv.symm (ofSection B S hS (Opposite.op C₃)
      (((BigFppfOver.toScheme B S hS).map c).appLE W ⊤ hle₃ s))⟩ :
      PartialMap B S hS hX (affineLineFunctor B S hS)), ?_⟩
  rw [evalRingHom_eq_appTop B S hS hX hInt p hp _ C₃ e₃.hom g₃ hcomp₃,
    e₃.hom_inv_id_assoc, Equiv.apply_symm_apply,
    affineLineCoordinate_ofSection,
    appTop_appLE_comp (by rw [← Functor.map_comp, hg₃c, hρ] :
      (BigFppfOver.toScheme B S hS).map g₃ ≫ (BigFppfOver.toScheme B S hS).map c = ρ)
      hle₃ hleρ s,
    ΓSpecIso_appLE_eq_descResidueField_evaluation ρ hzW hleρ s, hs, hk']

/-! ### The field of rational functions -/

/-- Evaluation at the generic point is a bijection onto the field of a monomorphic
field-valued representative of that point. -/
@[stacks 0END "bijectivity of evaluation at the generic point, on a monomorphic \
  field-valued representative"]
theorem evalRingHom_bijective (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt)
    (hmono : Mono (fieldMorphism B S hS X p)) :
    Function.Bijective (evalRingHom B S hS hX hInt p hp) :=
  ⟨evalRingHom_injective B S hS hX hInt p hp,
    evalRingHom_surjective B S hS hX hInt p hp hmono⟩

/-- **Stacks 0END.** The ring of rational functions of an integral algebraic space over `S` is
the residue field at its generic point: evaluation at the generic point is an isomorphism of
rings from the rational functions of Tag 0EMP onto the residue field of Tag 0EMW. -/
@[stacks 0END "the identification R(X) = κ(η) of the rational functions with the residue \
  field at the generic point"]
noncomputable def rationalFunctionsRingEquiv (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) :
    rationalFunctions B S hS hX ≃+*
      residueField B S hS X hInt.2.1 (genericPoint B S hS hX hInt) :=
  RingEquiv.ofBijective
    (evalRingHom B S hS hX hInt (genericRep B S hS hX hInt)
      (genericRep_class B S hS hX hInt))
    (evalRingHom_bijective B S hS hX hInt _ _
      (residueFieldRepresentative B S hS X hInt.2.1 (genericPoint B S hS hX hInt)).2.2)

@[simp]
theorem rationalFunctionsRingEquiv_apply (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) (x : rationalFunctions B S hS hX) :
    rationalFunctionsRingEquiv B S hS hX hInt x =
      evalRingHom B S hS hX hInt (genericRep B S hS hX hInt)
        (genericRep_class B S hS hX hInt) x := rfl

/-- The isomorphism is evaluation at the generic point, and is therefore pinned down on a
dense-open representative by *any* factorization of the residue-field morphism through the
domain of that representative. -/
theorem rationalFunctionsRingEquiv_toRationalMap (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (f : PartialMap B S hS hX (affineLineFunctor B S hS))
    (j : yoneda.obj ((genericRep B S hS hX hInt).siteObject B S hS X) ⟶ f.domain.toFunctor)
    (hj : j ≫ f.domain.ι = fieldMorphism B S hS X (genericRep B S hS hX hInt)) :
    rationalFunctionsRingEquiv B S hS hX hInt (f.toRationalMap B S hS) =
      (Scheme.ΓSpecIso (CommRingCat.of
          (residueField B S hS X hInt.2.1 (genericPoint B S hS hX hInt)))).hom.hom
        (affineLineCoordinate B S hS
          (Opposite.op ((genericRep B S hS hX hInt).siteObject B S hS X))
          (yonedaEquiv (j ≫ f.hom))) :=
  evalPartial_eq B S hS hX hInt (genericRep B S hS hX hInt)
    (genericRep_class B S hS hX hInt) f j hj

/-- **Stacks 0END.** The ring of rational functions of an integral algebraic space over `S` is
a field: it is the residue field at the generic point. -/
@[stacks 0END "the rational functions of an integral algebraic space form a field"]
theorem isField_rationalFunctions (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) : IsField (rationalFunctions B S hS hX) :=
  MulEquiv.isField (Field.toIsField _)
    (rationalFunctionsRingEquiv B S hS hX hInt).toMulEquiv

/-! ### A local ring which is a field, and the henselisation of a field -/

/-- The residue map of a local ring which is a field is injective: its kernel is the maximal
ideal, which is the zero ideal. -/
theorem injective_residue_of_isField {R : Type*} [CommRing R] [IsLocalRing R] (h : IsField R) :
    Function.Injective (IsLocalRing.residue R) :=
  injective_residue_of_isField_aux h

/-- A local ring which is a field is its own residue field, through the residue map: that map
is always surjective, and it is injective because the maximal ideal vanishes. -/
noncomputable def residueRingEquivOfIsField {R : Type*} [CommRing R] [IsLocalRing R]
    (h : IsField R) : R ≃+* IsLocalRing.ResidueField R :=
  RingEquiv.ofBijective (IsLocalRing.residue R)
    ⟨injective_residue_of_isField h, IsLocalRing.residue_surjective⟩

/-- A henselisation of a local ring which is a field is again a field: its maximal ideal is
generated by the maximal ideal of the base, which is the zero ideal. -/
private theorem isField_of_isHenselization {K : Type*} [CommRing K] [IsLocalRing K]
    (hK : IsField K) {Rh : Type*} [CommRing Rh] [IsLocalRing Rh] [Algebra K Rh]
    [IsLocalRing.IsHenselization K (IsLocalRing.ResidueField K) Rh] : IsField Rh := by
  let : Field K := hK.toField
  rw [IsLocalRing.isField_iff_maximalIdeal_eq,
    ← IsLocalRing.IsHenselization.map_maximalIdeal (R := K) (L := IsLocalRing.ResidueField K)
      (Rh := Rh), IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot]

/-- The structure map of a henselisation of a local ring which is a field is bijective: it is
injective because the base is a field, and surjective because both residue maps are bijective
and the residue field of the henselisation is the residue field of the base. -/
private theorem bijective_algebraMap_of_isHenselization {K : Type*} [CommRing K] [IsLocalRing K]
    (hK : IsField K) {Rh : Type*} [CommRing Rh] [IsLocalRing Rh] [Algebra K Rh]
    [IsLocalRing.IsHenselization K (IsLocalRing.ResidueField K) Rh] :
    Function.Bijective (algebraMap K Rh) := by
  have hRh : IsField Rh := isField_of_isHenselization hK
  obtain ⟨e, he⟩ := IsLocalRing.IsHenselization.exists_residueFieldEquiv
    (R := K) (L := IsLocalRing.ResidueField K) (Rh := Rh)
  refine ⟨?_, fun y ↦ ?_⟩
  · let : Field K := hK.toField
    exact (algebraMap K Rh).injective
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective
    (R := K) (e.symm (IsLocalRing.residue Rh y))
  refine ⟨r, injective_residue_of_isField hRh ?_⟩
  calc IsLocalRing.residue Rh (algebraMap K Rh r)
      = e (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField K)
          (IsLocalRing.residue K r)) := (he r).symm
    _ = e (IsLocalRing.residue K r) := by simp
    _ = e (e.symm (IsLocalRing.residue Rh y)) := by rw [hr]
    _ = IsLocalRing.residue Rh y := e.apply_symm_apply _

/-- A reduced local ring of Krull dimension zero is a field: in a local ring of dimension zero
a non-unit is nilpotent, so the maximal ideal is contained in the nilradical, which vanishes. -/
private theorem isField_of_ringKrullDim_eq_zero {R : Type*} [CommRing R] [IsLocalRing R]
    [_root_.IsReduced R] (h : ringKrullDim R = 0) : IsField R := by
  have hLE : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.2 h
  have htfae : (Ring.KrullDimLE 0 R ∧ IsLocalRing R) ↔
      ∀ a : R, IsNilpotent a ↔ ¬ IsUnit a :=
    (Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 1 3
  have hnil : ∀ a : R, IsNilpotent a ↔ ¬ IsUnit a := htfae.1 ⟨hLE, ‹_›⟩
  refine IsLocalRing.isField_iff_maximalIdeal_eq.2 (le_antisymm (fun a ha ↦ ?_) bot_le)
  have hmem : a ∈ nilradical R := (hnil a).2 ((IsLocalRing.mem_maximalIdeal a).1 ha)
  rw [nilradical_eq_zero] at hmem
  simpa using hmem

/-! ### The local ring of an elementary étale neighbourhood of the generic point -/

/-- The local ring of an elementary étale neighbourhood of the generic point of an integral
algebraic space, at the marked point of that neighbourhood, is a field: the scheme of the
neighbourhood is reduced, because reducedness is an étale-local property and the neighbourhood
is étale over the space, and the local ring has Krull dimension zero, because the generic point
is a point of codimension zero by Stacks 0ABV and the dimension of the local ring of an
algebraic space at a point is measured on any étale chart above it by Stacks 0BAM. -/
@[stacks 0END "the local ring of an elementary étale neighbourhood at its marked point, over \
  the generic point, is a field; the neighbourhood is a parameter because the statement is \
  about it, and Tag 0BBP provides one"]
theorem isField_neighborhoodStalk_genericPoint (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (E : ElementaryEtaleNeighborhood B S hS X hX (genericPoint B S hS hX hInt)) :
    IsField (E.scheme.left.1.presheaf.stalk E.point) := by
  let : IrreducibleSpace (points B S hS X) := hInt.2.2
  have hetale := ElementaryEtaleNeighborhood.presheaf_toSpace B S hS X hX _ E
  have hgen : genericPoint B S hS hX hInt ∈ genericPoints (points B S hS X) := by
    change closure {genericPoint B S hS hX hInt} ∈ irreducibleComponents (points B S hS X)
    rw [isGenericPoint_genericPoint B S hS hX hInt, irreducibleComponents_eq_singleton]
    exact rfl
  have hdim : localRingDimension B S hS (genericPoint B S hS hX hInt) = 0 :=
    (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hX hInt.2.1 _).1 hgen
  have hpt : pointsToScheme B S hS E.scheme
      (presheafPoint B S hS E.scheme E.point E.residueField_contained) = E.point :=
    Scheme.fromSpecResidueField_apply E.point _
  have hchart : ChartPoint B S hS E.scheme E.toSpace E.point
      (genericPoint B S hS hX hInt) := by
    have h := chartPoint_pointsToScheme B S hS E.scheme E.toSpace
      (presheafPoint B S hS E.scheme E.point E.residueField_contained)
    rwa [hpt, E.map_point] at h
  have hkrull : ringKrullDim (E.scheme.left.1.presheaf.stalk E.point) = 0 := by
    have h := localRingDimension_eq_of_chartPoint B S hS hX E.scheme E.toSpace hetale E.point
      (genericPoint B S hS hX hInt) hchart
    rw [hdim] at h
    exact h.symm
  have hred : IsReduced E.scheme.left.1 :=
    (exists_atlas_iff_forall_etale B S hS X (fun Y : Scheme.{u} => IsReduced Y) hX).1 hInt.1
      E.scheme E.toSpace hetale
  have : _root_.IsReduced (E.scheme.left.1.presheaf.stalk E.point) := inferInstance
  exact isField_of_ringKrullDim_eq_zero hkrull

/-! ### The henselian local ring at the generic point -/

/-- An elementary étale neighbourhood of the generic point of an integral algebraic space: an
integral algebraic space is decent, so **Stacks 0BBP** produces one — with affine scheme, even —
and this is the neighbourhood it produces. -/
noncomputable def genericNeighborhood (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) :
    ElementaryEtaleNeighborhood B S hS X hX (genericPoint B S hS hX hInt) :=
  (exists_affine_elementaryEtaleNeighborhood' B S hS hX hInt.2.1
    (genericPoint B S hS hX hInt)).choose

/-- The residue field of an elementary étale neighbourhood of the generic point at its marked
point, viewed as a field-valued representative of the generic point of the space. -/
noncomputable abbrev genericNeighborhoodFieldPoint (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (E : ElementaryEtaleNeighborhood B S hS X hX (genericPoint B S hS hX hInt)) :
    FieldValuedPoint B S hS X :=
  neighborhoodFieldPoint B S hS X hX (genericPoint B S hS hX hInt) E

/-- The ring of rational functions of an integral algebraic space is the residue field of any
elementary étale neighbourhood of the generic point at its marked point: that residue field is
a *monomorphic* field-valued representative of the generic point, by the data of Stacks 0BGU,
so evaluation at the generic point is bijective onto it. -/
@[stacks 0END "the rational functions are the residue field of an elementary étale \
  neighbourhood of the generic point at its marked point"]
noncomputable def evalNeighborhoodRingEquiv (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (E : ElementaryEtaleNeighborhood B S hS X hX (genericPoint B S hS hX hInt)) :
    rationalFunctions B S hS hX ≃+* E.scheme.left.1.residueField E.point :=
  RingEquiv.ofBijective
    (evalRingHom B S hS hX hInt (genericNeighborhoodFieldPoint B S hS hX hInt E)
      (neighborhoodFieldPoint_class B S hS X hX (genericPoint B S hS hX hInt) E))
    (evalRingHom_bijective B S hS hX hInt _ _
      (ElementaryEtaleNeighborhood.mono_neighborhoodFieldPoint B S hS X hX
        (genericPoint B S hS hX hInt) E))

/-- **Stacks 0END.** The henselian local ring of Stacks 0BGW at the generic point of an integral
algebraic space is a field: it is a henselisation of the local ring of the elementary étale
neighbourhood of Stacks 0BBP at its marked point by Stacks 0EMY, that local ring is a field, and
a henselisation of a field is a field. -/
@[stacks 0END "the henselian local ring O^h_{X,η} at the generic point is a field"]
theorem isField_henselianLocalRing_genericPoint (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) :
    IsField (henselianLocalRing B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1 :
      Type (u + 1)) := by
  let E := genericNeighborhood B S hS hX hInt
  let := henselianLocalRing_isLocalRing B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1
  let := stalkAlgebra B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1 E
  let := henselianLocalRing_isHenselization B S hS X hX (genericPoint B S hS hX hInt)
    hInt.2.1 E
  exact isField_of_isHenselization (isField_neighborhoodStalk_genericPoint B S hS hX hInt E)

/-- The canonical map of Stacks 0EMY from the local ring of an elementary étale neighbourhood of
the generic point into the henselian local ring is bijective: it is the structure map of a
henselisation of a field. -/
@[stacks 0END "bijectivity at the generic point of the canonical map O_{U,u} → O^h_{X,η} of \
  Tag 0EMY"]
theorem bijective_stalkToHenselianLocalRing_genericPoint (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (E : ElementaryEtaleNeighborhood B S hS X hX (genericPoint B S hS hX hInt)) :
    Function.Bijective (stalkToHenselianLocalRing B S hS X hX
      (genericPoint B S hS hX hInt) hInt.2.1 E) := by
  let := henselianLocalRing_isLocalRing B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1
  let := stalkAlgebra B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1 E
  let := henselianLocalRing_isHenselization B S hS X hX (genericPoint B S hS hX hInt)
    hInt.2.1 E
  have h := bijective_algebraMap_of_isHenselization
    (isField_neighborhoodStalk_genericPoint B S hS hX hInt E)
    (Rh := (henselianLocalRing B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1 :
      Type (u + 1)))
  rwa [RingHom.algebraMap_toAlgebra] at h

/-- **Stacks 0END.** The local ring of an elementary étale neighbourhood of the generic point at
its marked point is the henselian local ring of Stacks 0BGW there, through the canonical map of
Stacks 0EMY. -/
noncomputable def neighborhoodStalkHenselianRingEquiv (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (E : ElementaryEtaleNeighborhood B S hS X hX (genericPoint B S hS hX hInt)) :
    E.scheme.left.1.presheaf.stalk E.point ≃+*
      (henselianLocalRing B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1 : Type (u + 1)) :=
  RingEquiv.ofBijective
    (stalkToHenselianLocalRing B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1 E)
    (bijective_stalkToHenselianLocalRing_genericPoint B S hS hX hInt E)

/-! ### The rational functions and the henselian local ring -/

/-- The comparison homomorphism from the rational functions to the henselian local ring at the
generic point: evaluate at the generic point, read the resulting element of the residue field of
an elementary étale neighbourhood backwards through the residue map of its local ring, which is
bijective because that local ring is a field, and map it into the henselian local ring by the
canonical homomorphism of Stacks 0EMY. -/
noncomputable def rationalFunctionsHenselianRingHom (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (E : ElementaryEtaleNeighborhood B S hS X hX (genericPoint B S hS hX hInt)) :
    rationalFunctions B S hS hX →+*
      (henselianLocalRing B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1 : Type (u + 1)) :=
  (stalkToHenselianLocalRing B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1 E).comp
    ((residueRingEquivOfIsField
        (isField_neighborhoodStalk_genericPoint B S hS hX hInt E)).symm.toRingHom.comp
      (evalRingHom B S hS hX hInt (genericNeighborhoodFieldPoint B S hS hX hInt E)
        (neighborhoodFieldPoint_class B S hS X hX (genericPoint B S hS hX hInt) E)))

/-- The comparison homomorphism to the henselian local ring is bijective: it is a composite of
three bijections. -/
theorem bijective_rationalFunctionsHenselianRingHom (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (E : ElementaryEtaleNeighborhood B S hS X hX (genericPoint B S hS hX hInt)) :
    Function.Bijective (rationalFunctionsHenselianRingHom B S hS hX hInt E) :=
  (bijective_stalkToHenselianLocalRing_genericPoint B S hS hX hInt E).comp
    (((residueRingEquivOfIsField
        (isField_neighborhoodStalk_genericPoint B S hS hX hInt E)).symm.bijective).comp
      (evalRingHom_bijective B S hS hX hInt _ _
        (ElementaryEtaleNeighborhood.mono_neighborhoodFieldPoint B S hS X hX
          (genericPoint B S hS hX hInt) E)))

/-- The ring of rational functions of an integral algebraic space over `S` is the henselian local
ring of Stacks 0BGW at its generic point, through the comparison homomorphism built from a given
elementary étale neighbourhood of that point. -/
noncomputable def rationalFunctionsHenselianRingEquivOfNeighborhood
    (hX : IsAlgebraicSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (E : ElementaryEtaleNeighborhood B S hS X hX (genericPoint B S hS hX hInt)) :
    rationalFunctions B S hS hX ≃+*
      (henselianLocalRing B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1 : Type (u + 1)) :=
  RingEquiv.ofBijective (rationalFunctionsHenselianRingHom B S hS hX hInt E)
    (bijective_rationalFunctionsHenselianRingHom B S hS hX hInt E)

/-- **Stacks 0END.** The ring of rational functions of an integral algebraic space over `S` is
the henselian local ring of Stacks 0BGW at its generic point: the comparison is built from the
elementary étale neighbourhood of Stacks 0BBP. -/
@[stacks 0END "the identification R(X) = O^h_{X,η} of the rational functions with the \
  henselian local ring at the generic point"]
noncomputable def rationalFunctionsHenselianRingEquiv (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) :
    rationalFunctions B S hS hX ≃+*
      (henselianLocalRing B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1 : Type (u + 1)) :=
  rationalFunctionsHenselianRingEquivOfNeighborhood B S hS hX hInt
    (genericNeighborhood B S hS hX hInt)

/-- The unconditional identification is the one built from the neighbourhood of Stacks 0BBP, so
every statement about the identification built from an arbitrary neighbourhood applies to it. -/
theorem rationalFunctionsHenselianRingEquiv_eq_ofNeighborhood (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) :
    rationalFunctionsHenselianRingEquiv B S hS hX hInt =
      rationalFunctionsHenselianRingEquivOfNeighborhood B S hS hX hInt
        (genericNeighborhood B S hS hX hInt) :=
  rfl

@[simp]
theorem rationalFunctionsHenselianRingEquivOfNeighborhood_apply
    (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (E : ElementaryEtaleNeighborhood B S hS X hX (genericPoint B S hS hX hInt))
    (x : rationalFunctions B S hS hX) :
    rationalFunctionsHenselianRingEquivOfNeighborhood B S hS hX hInt E x =
      stalkToHenselianLocalRing B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1 E
        ((residueRingEquivOfIsField
            (isField_neighborhoodStalk_genericPoint B S hS hX hInt E)).symm
          (evalRingHom B S hS hX hInt (genericNeighborhoodFieldPoint B S hS hX hInt E)
            (neighborhoodFieldPoint_class B S hS X hX (genericPoint B S hS hX hInt) E) x)) :=
  rfl

/-- The identification with the henselian local ring is pinned down without inverses: it
carries a rational function to the canonical image of *any* element of the local ring of the
neighbourhood whose residue is the value of that function at the generic point. -/
@[stacks 0END "the characterisation of that identification: a rational function goes to the \
  canonical image of any element of the neighbourhood's local ring whose residue is its \
  value at the generic point"]
theorem rationalFunctionsHenselianRingEquivOfNeighborhood_eq (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (E : ElementaryEtaleNeighborhood B S hS X hX (genericPoint B S hS hX hInt))
    (x : rationalFunctions B S hS hX) (r : E.scheme.left.1.presheaf.stalk E.point)
    (hr : IsLocalRing.residue (E.scheme.left.1.presheaf.stalk E.point) r =
      evalRingHom B S hS hX hInt (genericNeighborhoodFieldPoint B S hS hX hInt E)
        (neighborhoodFieldPoint_class B S hS X hX (genericPoint B S hS hX hInt) E) x) :
    rationalFunctionsHenselianRingEquivOfNeighborhood B S hS hX hInt E x =
      stalkToHenselianLocalRing B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1 E r := by
  rw [rationalFunctionsHenselianRingEquivOfNeighborhood_apply,
    (RingEquiv.symm_apply_eq (residueRingEquivOfIsField
      (isField_neighborhoodStalk_genericPoint B S hS hX hInt E))).2 hr.symm]

/-- The identification with the henselian local ring, computed on a dense-open representative:
it is the canonical image of any element of the local ring of the neighbourhood whose residue is
the coordinate of the representative pulled back along *any* factorization of the residue-field
morphism through the domain. -/
theorem rationalFunctionsHenselianRingEquivOfNeighborhood_toRationalMap
    (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (E : ElementaryEtaleNeighborhood B S hS X hX (genericPoint B S hS hX hInt))
    (f : PartialMap B S hS hX (affineLineFunctor B S hS))
    (j : yoneda.obj ((genericNeighborhoodFieldPoint B S hS hX hInt E).siteObject B S hS X) ⟶
      f.domain.toFunctor)
    (hj : j ≫ f.domain.ι =
      fieldMorphism B S hS X (genericNeighborhoodFieldPoint B S hS hX hInt E))
    (r : E.scheme.left.1.presheaf.stalk E.point)
    (hr : IsLocalRing.residue (E.scheme.left.1.presheaf.stalk E.point) r =
      (Scheme.ΓSpecIso (CommRingCat.of
          (genericNeighborhoodFieldPoint B S hS hX hInt E).carrier)).hom.hom
        (affineLineCoordinate B S hS
          (Opposite.op ((genericNeighborhoodFieldPoint B S hS hX hInt E).siteObject B S hS X))
          (yonedaEquiv (j ≫ f.hom)))) :
    rationalFunctionsHenselianRingEquivOfNeighborhood B S hS hX hInt E
        (f.toRationalMap B S hS) =
      stalkToHenselianLocalRing B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1 E r :=
  rationalFunctionsHenselianRingEquivOfNeighborhood_eq B S hS hX hInt E _ r
    (hr.trans (evalPartial_eq B S hS hX hInt (genericNeighborhoodFieldPoint B S hS hX hInt E)
      (neighborhoodFieldPoint_class B S hS X hX (genericPoint B S hS hX hInt) E) f j hj).symm)

/-- **Stacks 0END.** The residue field at the generic point of an integral algebraic space over
`S` is the henselian local ring of Stacks 0BGW there: both are the ring of rational
functions. -/
@[stacks 0END "the identification O^h_{X,η} = κ(η) of the henselian local ring at the generic \
  point with the residue field there"]
noncomputable def residueFieldHenselianRingEquiv (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) :
    residueField B S hS X hInt.2.1 (genericPoint B S hS hX hInt) ≃+*
      (henselianLocalRing B S hS X hX (genericPoint B S hS hX hInt) hInt.2.1 : Type (u + 1)) :=
  (rationalFunctionsRingEquiv B S hS hX hInt).symm.trans
    (rationalFunctionsHenselianRingEquiv B S hS hX hInt)

/-- **Stacks 0END.** The tag asserts one chain of identifications `R(X) = O^h_{X,η} = κ(η)`, and
the three identifications are indeed the three edges of one commuting triangle: going from the
rational functions to the henselian local ring is going to the residue field and on from
there. -/
@[stacks 0END "the chain R(X) = O^h_{X,η} = κ(η): the three identifications commute"]
theorem rationalFunctionsHenselianRingEquiv_eq_trans (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) :
    rationalFunctionsHenselianRingEquiv B S hS hX hInt =
      (rationalFunctionsRingEquiv B S hS hX hInt).trans
        (residueFieldHenselianRingEquiv B S hS hX hInt) := by
  refine RingEquiv.ext fun x ↦ ?_
  change _ = rationalFunctionsHenselianRingEquiv B S hS hX hInt
    ((rationalFunctionsRingEquiv B S hS hX hInt).symm
      (rationalFunctionsRingEquiv B S hS hX hInt x))
  rw [RingEquiv.symm_apply_apply]

end AlgebraicGeometry.Space

end
