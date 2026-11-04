module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Curves.UniversalNode.Basic
public import StacksFrontier.RingTheory.NodalChart.Basic

/-!
# The standard family of nodal singularities and its base changes

The standard family of nodal curve singularities is the morphism
`Spec R₀[u, v, a]/(uv - a) ⟶ Spec R₀[a]` recording the smoothing parameter `a = uv`; over the
integers it is the family that appears on the right-hand side of Tag 0CBY. This file identifies
all of its base changes over an affine base: for a ring map `c : R₀ → R` and an element `h` of
`R`, the base change of the standard family along the morphism `Spec R ⟶ Spec R₀[a]` classifying
`h` is the spectrum of the nodal chart ring `R[x, y]/(xy - h)` of
`StacksFrontier.RingTheory.NodalChart.Basic`. Moreover every ring map `R₀[a] → R` extending `c` is
of that form, so over an affine base the local models of the standard family are exactly the
nodal charts.

## Main definitions

* `Stacks.NodalEtaleLocalStructure.standardNodalFamily` — the standard family
  `Spec R₀[u, v, a]/(uv - a) ⟶ Spec R₀[a]`.
* `Stacks.NodalEtaleLocalStructure.nodalParameterMap` — the morphism `Spec R ⟶ Spec R₀[a]`
  classifying an element `h` of `R`.
* `Stacks.NodalEtaleLocalStructure.chartClassify` — the ring map
  `R₀[u, v, a]/(uv - a) → R[x, y]/(xy - h)` sending `u ↦ x`, `v ↦ y`, `a ↦ h`.
* `Stacks.NodalEtaleLocalStructure.StandardNodalDiagram` — the diagram of Tag 0CBY.
* `Stacks.NodalEtaleLocalStructure.NodalChartNeighbourhood` — the same étale local structure in
  chart form: an étale neighbourhood of the point mapping étale-ly to a nodal chart
  `Spec R[x, y]/(xy - h)` over an affine étale neighbourhood `Spec R` of the image point.

## Main results

* `Stacks.NodalEtaleLocalStructure.isPushout_chartClassify` — the square of rings
  `R₀[a] → R₀[u, v, a]/(uv - a)`, `R₀[a] → R`, `R₀[u, v, a]/(uv - a) → R[x, y]/(xy - h)`,
  `R → R[x, y]/(xy - h)` is a pushout.
* `Stacks.NodalEtaleLocalStructure.isPullback_specMap_chartClassify` — consequently the
  corresponding square of affine schemes is cartesian: the nodal chart is the base change of the
  standard family along the parameter `h`.
* `Stacks.NodalEtaleLocalStructure.chartIsoOfIsPullback` — any scheme fitting into that cartesian
  square is the spectrum of the nodal chart ring.
* `Stacks.NodalEtaleLocalStructure.specMap_stalkClosedPointTo_comp_fromSpecStalk_nodalParameterMap`
  — over a local ring the parameter factors through the stalk of `Spec ℤ[a]`, which is the shape
  in which Tag 0GDX writes it.
* `Stacks.NodalEtaleLocalStructure.standardNodalDiagramOfChart` — the diagram of Tag 0CBY built
  from the chart form, the cartesian square being supplied by the previous result.
* `Stacks.NodalEtaleLocalStructure.standardNodalDiagramOfEtaleApproximation` — the diagram of
  Tag 0CBY built from an étale morphism to a base change of the standard family, which is the
  shape in which Tag 0GDX delivers its conclusion.

## Implementation notes

What this file contributes to Tag 0CBY is the right-hand half of the tag's diagram: the local
model is cut out of the standard family by a cartesian square
(`Stacks.NodalEtaleLocalStructure.isPullback_specMap_chartClassify`), over an affine base nothing
but a nodal chart can occur as the `W` of that square
(`Stacks.NodalEtaleLocalStructure.chartIsoOfIsPullback`), and the two assembly steps
`Stacks.NodalEtaleLocalStructure.standardNodalDiagramOfChart` and
`Stacks.NodalEtaleLocalStructure.standardNodalDiagramOfEtaleApproximation` build the tag's whole
diagram from the chart form and from the conclusion of Tag 0GDX for the standard family.

The *existence* of the diagram — the content of Tag 0CBY — is proved in
`StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleLocalStructureAssembly`, where the attribute
`@[stacks 0CBY]` sits on
`Stacks.NodalEtaleLocalStructure.nonempty_standardNodalDiagram_of_isAtWorstNodal`. Nothing in
this file is tagged with it, and the three declarations here that look as though they ought to
be — `isPullback_specMap_chartClassify`, `standardNodalDiagramOfChart` and
`standardNodalDiagramOfEtaleApproximation` — are each only a part or a step of the tag, so the
registration belongs on the whole statement instead.

The parameter of the standard family is handled through a bare ring map `c : R₀ → R` rather than
an algebra structure, so that the integral case `R₀ = ULift ℤ` needs no algebra instance on an
arbitrary ring; `Stacks.NodalEtaleLocalStructure.intRingHom` is the structure map used there.

## References

* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
* [Stacks Project, Tag 0CBX](https://stacks.math.columbia.edu/tag/0CBX)
* [Stacks Project, Tag 0CAU](https://stacks.math.columbia.edu/tag/0CAU)
* [Stacks Project, Tag 0CAR](https://stacks.math.columbia.edu/tag/0CAR)
* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Curves

universe u

namespace Stacks.NodalEtaleLocalStructure

section Standard

variable (R₀ : Type u) [CommRing R₀]

/-- **The standard family of nodal curve singularities**, the morphism
`Spec R₀[u, v, a]/(uv - a) ⟶ Spec R₀[a]` whose parameter `a` is the product `uv` of the two
coordinates. Over the integers this is the family of Tag 0CBY. -/
public def standardNodalFamily :
    Spec (.of (nodalQuotient R₀)) ⟶ Spec (.of (Polynomial R₀)) :=
  Spec.map (CommRingCat.ofHom (nodalParam R₀).toRingHom)

/-- Eliminating the parameter identifies the standard family over the integers with the
two-variable model `Spec ℤ[u, v] ⟶ Spec ℤ[a]`, `a ↦ uv`. -/
public theorem nodalModelIso_hom_comp_standardNodalFamily :
    (nodalModelIso (ULift.{u} ℤ)).hom ≫ standardNodalFamily (ULift.{u} ℤ) = nodalModelMap.{u} :=
  nodalModelIso_hom_comp_specMap_nodalParam_int

/-- The structure map `ℤ → R` of a commutative ring, with `ℤ` placed in the universe of `R`. It
is the coefficient map used for the standard family over the integers. -/
public def intRingHom (R : Type u) [CommRing R] : ULift.{u} ℤ →+* R :=
  (Int.castRingHom R).comp (ULift.ringEquiv (R := ℤ)).toRingHom

/-- The coordinate ring `R₀[u, v, a]/(uv - a)` of the standard family is of finite type over
`R₀`: it is a quotient of the polynomial ring in three variables. -/
public theorem finiteType_nodalQuotient : Algebra.FiniteType R₀ (nodalQuotient R₀) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R₀ (Ideal.span {nodalRelation R₀}))
    Ideal.Quotient.mk_surjective

/-- The standard family is of finite type over its base `R₀[a]`: the coordinate ring upstairs is
already of finite type over `R₀`, which maps to `R₀[a]`. -/
public theorem finiteType_nodalParam :
    letI : Algebra (Polynomial R₀) (nodalQuotient R₀) := (nodalParam R₀).toRingHom.toAlgebra
    Algebra.FiniteType (Polynomial R₀) (nodalQuotient R₀) := by
  let : Algebra (Polynomial R₀) (nodalQuotient R₀) := (nodalParam R₀).toRingHom.toAlgebra
  have : IsScalarTower R₀ (Polynomial R₀) (nodalQuotient R₀) :=
    IsScalarTower.of_algebraMap_eq fun r => ((nodalParam R₀).commutes r).symm
  have : Algebra.FiniteType R₀ (nodalQuotient R₀) := finiteType_nodalQuotient R₀
  exact Algebra.FiniteType.of_restrictScalars_finiteType R₀ (Polynomial R₀) (nodalQuotient R₀)

/-- **The standard family is locally of finite type.** -/
public instance locallyOfFiniteType_standardNodalFamily :
    LocallyOfFiniteType (standardNodalFamily R₀) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr (finiteType_nodalParam R₀)

/-- **The base `Spec ℤ[a]` of the standard family is of finite type over `Spec ℤ`.** This is the
hypothesis under which [Stacks, Tag 0GDX] may be applied to the standard family. -/
public theorem locallyOfFiniteType_from_nodalParameterBase :
    LocallyOfFiniteType
      (specULiftZIsTerminal.{u}.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) := by
  rw [specULiftZIsTerminal.hom_ext
    (specULiftZIsTerminal.{u}.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))
    (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ)))))]
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- Two ring maps out of `R₀[u, v, a]/(uv - a)` agree if they agree on the classes of the
constants and of the three variables. -/
private theorem nodalQuotient_ringHom_ext {B : Type*} [CommRing B] {f g : nodalQuotient R₀ →+* B}
    (hC : ∀ r : R₀, f (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.C r)) =
      g (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.C r)))
    (hX : ∀ i : Fin 3, f (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.X i)) =
      g (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.X i))) : f = g := by
  refine RingHom.ext fun z => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := Ideal.span ({nodalRelation R₀} : Set (MvPolynomial (Fin 3) R₀))) z
  exact RingHom.congr_fun (MvPolynomial.ringHom_ext (f := f.comp (Ideal.Quotient.mk _))
    (g := g.comp (Ideal.Quotient.mk _)) hC hX) p

end Standard

section Chart

variable {R₀ R : Type u} [CommRing R₀] [CommRing R] (c : R₀ →+* R) (h : R)

/-- A ring map out of the nodal chart ring `R[x, y]/(xy - h)` is given by a ring map `g : R → B`
together with a pair of elements of `B` whose product is `g h`. -/
public def chartLift {B : Type*} [CommRing B] (g : R →+* B) (u : Fin 2 → B)
    (hu : u 0 * u 1 = g h) : nodalChartRing R h →+* B :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom g u) <| by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    simp [nodalEquation_def, hu]

/-- The lift `chartLift h g u hu` sends the `i`-th generator of `R[x, y]/(xy - h)` to `u i`. -/
@[simp] public theorem chartLift_nodalGen {B : Type*} [CommRing B] (g : R →+* B) (u : Fin 2 → B)
    (hu : u 0 * u 1 = g h) (i : Fin 2) : chartLift h g u hu (nodalGen R h i) = u i := by
  rw [chartLift, nodalGen, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.lift_mk]
  simp

/-- The lift `chartLift h g u hu` restricts to `g` on the coefficient ring `R`. -/
@[simp] public theorem chartLift_algebraMap {B : Type*} [CommRing B] (g : R →+* B)
    (u : Fin 2 → B) (hu : u 0 * u 1 = g h) (r : R) :
    chartLift h g u hu (algebraMap R (nodalChartRing R h) r) = g r := by
  rw [chartLift, algebraMap_nodalChartRing_eq, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.lift_mk]
  simp

/-- The morphism `Spec R ⟶ Spec R₀[a]` classifying the element `h` of `R`, that is, sending the
parameter `a` of the standard family to `h`. -/
public def nodalParameterMap : Spec (.of R) ⟶ Spec (.of (Polynomial R₀)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom c h))

/-- Every ring map `R₀[a] → R` whose restriction to the coefficients is `c` is evaluation at the
image of `a`. Over an affine base the parameters of the standard family are therefore exactly the
elements of the coordinate ring. -/
public theorem eq_eval₂RingHom (φ : Polynomial R₀ →+* R) (hφ : φ.comp Polynomial.C = c) :
    φ = Polynomial.eval₂RingHom c (φ Polynomial.X) := by
  refine Polynomial.ringHom_ext (fun r => ?_) ?_
  · simpa using RingHom.congr_fun hφ r
  · simp

/-- The classifying map of a nodal chart: the ring map
`R₀[u, v, a]/(uv - a) → R[x, y]/(xy - h)` sending `u ↦ x`, `v ↦ y` and `a ↦ h`, with the
coefficients mapped along `c`. -/
public def chartClassify : nodalQuotient R₀ →+* nodalChartRing R h :=
  Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom ((algebraMap R (nodalChartRing R h)).comp c)
      ![nodalGen R h 0, nodalGen R h 1, algebraMap R (nodalChartRing R h) h]) <| by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    simp [nodalRelation, nodalGen_zero_mul_nodalGen_one]

/-- The map `chartClassify c h` sends the variables `u`, `v`, `a` to `x`, `y`, `h`. -/
@[simp] public theorem chartClassify_mk_X (i : Fin 3) :
    chartClassify c h (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.X i)) =
      ![nodalGen R h 0, nodalGen R h 1, algebraMap R (nodalChartRing R h) h] i := by
  rw [chartClassify, Ideal.Quotient.lift_mk]
  simp

/-- The map `chartClassify c h` sends a constant `r ∈ R₀` to the image of `c r`. -/
@[simp] public theorem chartClassify_mk_C (r : R₀) :
    chartClassify c h (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.C r)) =
      algebraMap R (nodalChartRing R h) (c r) := by
  rw [chartClassify, Ideal.Quotient.lift_mk]
  simp

/-- The classifying map carries the parameter of the standard family to `h`: the square of rings
whose spectrum is the right-hand square of Tag 0CBY commutes. -/
public theorem chartClassify_comp_nodalParam :
    (chartClassify c h).comp (nodalParam R₀).toRingHom =
      (algebraMap R (nodalChartRing R h)).comp (Polynomial.eval₂RingHom c h) := by
  refine Polynomial.ringHom_ext (fun r => ?_) ?_
  · change chartClassify c h ((nodalParam R₀) (Polynomial.C r)) = _
    simp [nodalParam, Ideal.Quotient.mkₐ_eq_mk]
  · change chartClassify c h ((nodalParam R₀) Polynomial.X) = _
    simp [nodalParam, Ideal.Quotient.mkₐ_eq_mk]

/-! ### The nodal chart is the base change of the standard family -/

section Cocone

variable (s : PushoutCocone (CommRingCat.ofHom (nodalParam R₀).toRingHom)
  (CommRingCat.ofHom (Polynomial.eval₂RingHom c h)))

/-- The commutativity of a cocone over the parameter square, read on elements of `R₀[a]`. -/
private theorem cocone_apply (p : Polynomial R₀) :
    s.inl.hom ((nodalParam R₀) p) = s.inr.hom (Polynomial.eval₂RingHom c h p) := by
  have hc := congrArg (fun φ : CommRingCat.of (Polynomial R₀) ⟶ s.pt => φ.hom p) s.condition
  simpa using hc

/-- On a cocone over the parameter square, the class of the coefficient `r` goes to `c r`. -/
private theorem cocone_mk_C (r : R₀) :
    s.inl.hom (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.C r)) =
      s.inr.hom (c r) := by
  have hc := cocone_apply c h s (Polynomial.C r)
  simpa [nodalParam, Ideal.Quotient.mkₐ_eq_mk] using hc

/-- On a cocone over the parameter square, the class of the parameter `a` goes to `h`. -/
private theorem cocone_mk_X_two :
    s.inl.hom (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.X 2)) =
      s.inr.hom h := by
  have hc := cocone_apply c h s Polynomial.X
  simpa [nodalParam, Ideal.Quotient.mkₐ_eq_mk] using hc

/-- The images of the two coordinates of the standard family under a cocone over the parameter
square. -/
private def coconeGens : Fin 2 → s.pt :=
  ![s.inl.hom (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.X 0)),
    s.inl.hom (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.X 1))]

/-- The first coordinate of the standard family goes to the class of `u`. -/
private theorem coconeGens_zero : coconeGens c h s 0 =
    s.inl.hom (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.X 0)) := rfl

/-- The second coordinate of the standard family goes to the class of `v`. -/
private theorem coconeGens_one : coconeGens c h s 1 =
    s.inl.hom (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.X 1)) := rfl

/-- The two coordinates multiply to the image of the parameter, by the defining relation
`uv = a` of the standard family. -/
private theorem coconeGens_mul : coconeGens c h s 0 * coconeGens c h s 1 = s.inr.hom h := by
  have hm : (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.X (0 : Fin 3))) *
      (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.X (1 : Fin 3))) =
      Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.X (2 : Fin 3)) := by
    rw [← map_mul, ← mk_X_two]
  rw [coconeGens_zero, coconeGens_one, ← map_mul, hm]
  exact cocone_mk_X_two c h s

/-- The map out of the nodal chart ring determined by a cocone over the parameter square. -/
private def coconeDesc : CommRingCat.of (nodalChartRing R h) ⟶ s.pt :=
  CommRingCat.ofHom (chartLift h s.inr.hom (coconeGens c h s) (coconeGens_mul c h s))

/-- The descent map sends the class of `u` to the class of `u`. -/
private theorem coconeDesc_apply_X_zero :
    chartLift h s.inr.hom (coconeGens c h s) (coconeGens_mul c h s)
        (chartClassify c h (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀})
          (MvPolynomial.X (0 : Fin 3)))) =
      s.inl.hom (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀})
        (MvPolynomial.X (0 : Fin 3))) := by
  rw [chartClassify_mk_X, Matrix.cons_val_zero, chartLift_nodalGen, coconeGens_zero]

/-- The descent map sends the class of `v` to the class of `v`. -/
private theorem coconeDesc_apply_X_one :
    chartLift h s.inr.hom (coconeGens c h s) (coconeGens_mul c h s)
        (chartClassify c h (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀})
          (MvPolynomial.X (1 : Fin 3)))) =
      s.inl.hom (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀})
        (MvPolynomial.X (1 : Fin 3))) := by
  rw [chartClassify_mk_X, Matrix.cons_val_one, Matrix.cons_val_zero, chartLift_nodalGen,
    coconeGens_one]

/-- The descent map sends the class of the parameter `a` to the image of `h`. -/
private theorem coconeDesc_apply_X_two :
    chartLift h s.inr.hom (coconeGens c h s) (coconeGens_mul c h s)
        (chartClassify c h (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀})
          (MvPolynomial.X (2 : Fin 3)))) =
      s.inl.hom (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀})
        (MvPolynomial.X (2 : Fin 3))) := by
  rw [chartClassify_mk_X, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    chartLift_algebraMap]
  exact (cocone_mk_X_two c h s).symm

/-- The descent map composed with the classifying map recovers the first leg of the cocone. -/
private theorem coconeDesc_comp_chartClassify :
    CommRingCat.ofHom (chartClassify c h) ≫ coconeDesc c h s = s.inl := by
  refine CommRingCat.hom_ext ?_
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  refine nodalQuotient_ringHom_ext _ (fun r => ?_) (fun i => ?_)
  · simpa [coconeDesc] using (cocone_mk_C c h s r).symm
  · fin_cases i
    · exact coconeDesc_apply_X_zero c h s
    · exact coconeDesc_apply_X_one c h s
    · exact coconeDesc_apply_X_two c h s

/-- The descent map composed with the structure map recovers the second leg of the cocone. -/
private theorem coconeDesc_comp_algebraMap :
    CommRingCat.ofHom (algebraMap R (nodalChartRing R h)) ≫ coconeDesc c h s = s.inr := by
  refine CommRingCat.hom_ext ?_
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  exact RingHom.ext fun r => by simp [coconeDesc]

/-- The descent map is the unique map compatible with both legs of the cocone. -/
private theorem coconeDesc_uniq (m : CommRingCat.of (nodalChartRing R h) ⟶ s.pt)
    (hl : CommRingCat.ofHom (chartClassify c h) ≫ m = s.inl)
    (hr : CommRingCat.ofHom (algebraMap R (nodalChartRing R h)) ≫ m = s.inr) :
    m = coconeDesc c h s := by
  have hl' := congrArg CommRingCat.Hom.hom hl
  have hr' := congrArg CommRingCat.Hom.hom hr
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hl' hr'
  refine CommRingCat.hom_ext (nodalChartRing_ringHom_ext (fun r => ?_) (fun i => ?_))
  · have := RingHom.congr_fun hr' r
    simpa [coconeDesc] using this
  · fin_cases i
    · have := RingHom.congr_fun hl'
        (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.X 0))
      simpa [coconeDesc, coconeGens_zero] using this
    · have := RingHom.congr_fun hl'
        (Ideal.Quotient.mk (Ideal.span {nodalRelation R₀}) (MvPolynomial.X 1))
      simpa [coconeDesc, coconeGens_one] using this

end Cocone

/-- **The nodal chart ring is the base change of the standard family.** The square
`R₀[a] → R₀[u, v, a]/(uv - a)`, `R₀[a] → R` (sending `a` to `h`),
`R₀[u, v, a]/(uv - a) → R[x, y]/(xy - h)`, `R → R[x, y]/(xy - h)` is a pushout of commutative
rings: an `R`-algebra map out of the nodal chart ring is the same thing as a pair of elements
with product `h`, which is the same thing as a map from the standard family compatible with the
parameter. -/
public theorem isPushout_chartClassify :
    IsPushout (CommRingCat.ofHom (nodalParam R₀).toRingHom)
      (CommRingCat.ofHom (Polynomial.eval₂RingHom c h))
      (CommRingCat.ofHom (chartClassify c h))
      (CommRingCat.ofHom (algebraMap R (nodalChartRing R h))) where
  w := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, chartClassify_comp_nodalParam]
  isColimit' :=
    ⟨PushoutCocone.IsColimit.mk _ (fun s => coconeDesc c h s)
      (fun s => coconeDesc_comp_chartClassify c h s)
      (fun s => coconeDesc_comp_algebraMap c h s)
      (fun s m hl hr => coconeDesc_uniq c h s m hl hr)⟩

/-- **The right-hand square of Tag 0CBY is cartesian for the nodal chart.** The spectrum of the
nodal chart ring `R[x, y]/(xy - h)` is the base change of the standard family
`Spec R₀[u, v, a]/(uv - a) ⟶ Spec R₀[a]` along the morphism `Spec R ⟶ Spec R₀[a]` classifying
`h`. -/
public theorem isPullback_specMap_chartClassify :
    IsPullback (Spec.map (CommRingCat.ofHom (chartClassify c h)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h))))
      (standardNodalFamily R₀) (nodalParameterMap c h) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_chartClassify c h)

/-- **The local model of the standard family over an affine base is a nodal chart.** Any scheme
fitting into the cartesian square of Tag 0CBY over the parameter `h` is the spectrum of the nodal
chart ring `R[x, y]/(xy - h)`. -/
public def chartIsoOfIsPullback {W : Scheme.{u}} {p : W ⟶ Spec (.of (nodalQuotient R₀))}
    {q : W ⟶ Spec (.of R)}
    (hW : IsPullback p q (standardNodalFamily R₀) (nodalParameterMap c h)) :
    W ≅ Spec (.of (nodalChartRing R h)) :=
  hW.isoIsPullback _ _ (isPullback_specMap_chartClassify c h)

/-- **The parameter of a nodal chart over a local ring, written through the stalk of
`Spec ℤ[a]`.** For a local ring `A` and `h : A`, the morphism `Spec A ⟶ Spec ℤ[a]` classifying
`h` factors as the spectrum of a local homomorphism out of the stalk of `Spec ℤ[a]` at the image
of the closed point, followed by `fromSpecStalk`.

That factored shape is how [Stacks, Tag 0GDX] writes the morphism along which its `Y_σ` is
formed, so this equation is what identifies `Y_σ` for the standard family with the base change
of `isPullback_specMap_chartClassify`, hence with `Spec A[u, v]/(uv - h)` through
`chartIsoOfIsPullback`. -/
public theorem specMap_stalkClosedPointTo_comp_fromSpecStalk_nodalParameterMap
    (A : Type u) [CommRing A] [IsLocalRing A] (a : A) :
    Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
          (nodalParameterMap (intRingHom A) a)).hom) ≫
        (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
          ((nodalParameterMap (intRingHom A) a).base (IsLocalRing.closedPoint A)) =
      nodalParameterMap (intRingHom A) a := by
  rw [CommRingCat.ofHom_hom]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (nodalParameterMap (intRingHom A) a)

end Chart

/-! ### A nodal chart base-changes to a nodal chart -/

section ChartBaseChange

variable {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R') (h : R)

/-- The classifying map of the base-changed nodal chart factors through the map of charts: both
send `u ↦ x`, `v ↦ y`, `a ↦ h` and the coefficients along `φ`. -/
public theorem nodalChartMap_comp_chartClassify :
    (nodalChartMap φ h).comp (chartClassify (RingHom.id R) h) = chartClassify φ (φ h) := by
  refine nodalQuotient_ringHom_ext _ (fun r => ?_) (fun i => ?_)
  · simp
  · fin_cases i <;> simp

/-- The parameter of the base-changed nodal chart is the parameter of the chart composed with the
base change. -/
public theorem specMap_comp_nodalParameterMap_id :
    Spec.map (CommRingCat.ofHom φ) ≫ nodalParameterMap (RingHom.id R) h =
      nodalParameterMap φ (φ h) := by
  have hring : Polynomial.eval₂RingHom φ (φ h) =
      φ.comp (Polynomial.eval₂RingHom (RingHom.id R) h) :=
    Polynomial.ringHom_ext (fun r => by simp) (by simp)
  rw [nodalParameterMap, nodalParameterMap, hring, CommRingCat.ofHom_comp, Spec.map_comp]

/-- **A nodal chart base-changes to a nodal chart.** For a ring map `φ : R → R'` the square
`Spec R'[x, y]/(xy - φ h) ⟶ Spec R[x, y]/(xy - h)`, `Spec R' ⟶ Spec R` is cartesian: the nodal
chart over `R'` with parameter `φ h` is the base change along `Spec R' ⟶ Spec R` of the nodal
chart over `R` with parameter `h`.

Both charts are base changes of the standard family (`isPullback_specMap_chartClassify`), the
second along a parameter which factors through the first, so this is pullback cancellation. -/
public theorem isPullback_specMap_nodalChartMap :
    IsPullback (Spec.map (CommRingCat.ofHom (nodalChartMap φ h)))
      (Spec.map (CommRingCat.ofHom (algebraMap R' (nodalChartRing R' (φ h)))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h))))
      (Spec.map (CommRingCat.ofHom φ)) := by
  refine IsPullback.of_right
    (h₁₂ := Spec.map (CommRingCat.ofHom (chartClassify (RingHom.id R) h)))
    (h₂₂ := nodalParameterMap (RingHom.id R) h) ?_ ?_
    (isPullback_specMap_chartClassify (RingHom.id R) h)
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, nodalChartMap_comp_chartClassify,
      specMap_comp_nodalParameterMap_id]
    exact isPullback_specMap_chartClassify φ (φ h)
  · rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      nodalChartMap_comp_algebraMap]

end ChartBaseChange

/-! ### The diagram of Tag 0CBY -/

/-- The diagram asked for by Tag 0CBY for a morphism `f : X ⟶ S` and a point `x` of `X`: étale
morphisms `U ⟶ X` and `V ⟶ S`, an étale morphism `U ⟶ W` over `V`, a cartesian square
exhibiting `W` as the base change of the standard family
`Spec ℤ[u, v, a]/(uv - a) ⟶ Spec ℤ[a]` along a parameter `V ⟶ Spec ℤ[a]`, and a point of `U`
lying over `x`. -/
public structure StandardNodalDiagram {X S : Scheme.{u}} (f : X ⟶ S) (x : X) where
  /-- The étale neighbourhood of `x` in `X`. -/
  U : Scheme.{u}
  /-- The étale neighbourhood of the image of `x` in `S`. -/
  V : Scheme.{u}
  /-- The local model over `V`. -/
  W : Scheme.{u}
  /-- The étale morphism to the source. -/
  toSource : U ⟶ X
  /-- The étale morphism to the base. -/
  toBase : V ⟶ S
  /-- The family over `V` induced by `f`. -/
  familyU : U ⟶ V
  /-- The local model viewed as a family over `V`. -/
  familyW : W ⟶ V
  /-- The étale morphism from the neighbourhood to the local model. -/
  toModel : U ⟶ W
  /-- The morphism to the total space of the standard family. -/
  classifyW : W ⟶ Spec (.of (nodalQuotient (ULift.{u} ℤ)))
  /-- The parameter of the local model, a morphism to `Spec ℤ[a]`. -/
  classifyV : V ⟶ Spec (.of (Polynomial (ULift.{u} ℤ)))
  /-- The chosen point of `U`. -/
  pt : U
  /-- The morphism to the source is étale. -/
  etale_toSource : Etale toSource
  /-- The morphism to the base is étale. -/
  etale_toBase : Etale toBase
  /-- The morphism to the local model is étale. -/
  etale_toModel : Etale toModel
  /-- The chosen point lies over `x`. -/
  pt_mem : toSource.base pt = x
  /-- The left-hand square commutes. -/
  comm_left : toSource ≫ f = familyU ≫ toBase
  /-- The morphism to the local model is a morphism of families over `V`. -/
  comm_model : toModel ≫ familyW = familyU
  /-- The right-hand square is cartesian. -/
  isPullback_model :
    IsPullback classifyW familyW (standardNodalFamily (ULift.{u} ℤ)) classifyV

/-- The étale local structure of Tag 0CBY in chart form: an étale neighbourhood `U ⟶ X` of the
point `x`, an affine étale neighbourhood `Spec R ⟶ S` of its image, a parameter `h` in `R`, and
an étale morphism from `U` to the nodal chart `Spec R[x, y]/(xy - h)` compatible with `f`. This
is the statement that an at-worst-nodal family is étale locally a nodal chart; it is the content
of Tag 0CBY that the formal local structure (Tag 0CBX) and Artin approximation (Tag 0CAU)
supply. -/
public structure NodalChartNeighbourhood {X S : Scheme.{u}} (f : X ⟶ S) (x : X) where
  /-- The coordinate ring of the affine étale neighbourhood of the image point. -/
  base : Type u
  /-- Its ring structure. -/
  [commRing : CommRing base]
  /-- The parameter of the nodal chart. -/
  param : base
  /-- The étale neighbourhood of `x`. -/
  U : Scheme.{u}
  /-- The étale morphism to the source. -/
  toSource : U ⟶ X
  /-- The étale morphism from the affine neighbourhood to the base. -/
  toBase : Spec (.of base) ⟶ S
  /-- The étale morphism to the nodal chart. -/
  toChart : U ⟶ Spec (.of (nodalChartRing base param))
  /-- The chosen point of `U`. -/
  pt : U
  /-- The morphism to the source is étale. -/
  etale_toSource : Etale toSource
  /-- The morphism to the base is étale. -/
  etale_toBase : Etale toBase
  /-- The morphism to the nodal chart is étale. -/
  etale_toChart : Etale toChart
  /-- The chosen point lies over `x`. -/
  pt_mem : toSource.base pt = x
  /-- The diagram commutes: the family is the nodal chart over the affine neighbourhood. -/
  comm : toSource ≫ f = toChart ≫
    Spec.map (CommRingCat.ofHom (algebraMap base (nodalChartRing base param))) ≫ toBase

attribute [instance] NodalChartNeighbourhood.commRing

/-- **Reduction of Tag 0CBY to the chart form.** Given the étale local structure in chart form,
the diagram of Tag 0CBY is obtained by taking `V` to be the affine étale neighbourhood of the
image point and `W` the nodal chart over it; the right-hand square is cartesian because the nodal
chart is the base change of the standard family along its parameter. -/
public def standardNodalDiagramOfChart {X S : Scheme.{u}} {f : X ⟶ S} {x : X}
    (d : NodalChartNeighbourhood f x) : StandardNodalDiagram f x where
  U := d.U
  V := Spec (.of d.base)
  W := Spec (.of (nodalChartRing d.base d.param))
  toSource := d.toSource
  toBase := d.toBase
  familyU := d.toChart ≫
    Spec.map (CommRingCat.ofHom (algebraMap d.base (nodalChartRing d.base d.param)))
  familyW := Spec.map (CommRingCat.ofHom (algebraMap d.base (nodalChartRing d.base d.param)))
  toModel := d.toChart
  classifyW := Spec.map (CommRingCat.ofHom (chartClassify (intRingHom d.base) d.param))
  classifyV := nodalParameterMap (intRingHom d.base) d.param
  pt := d.pt
  etale_toSource := d.etale_toSource
  etale_toBase := d.etale_toBase
  etale_toModel := d.etale_toChart
  pt_mem := d.pt_mem
  comm_left := by rw [d.comm, Category.assoc]
  comm_model := rfl
  isPullback_model := isPullback_specMap_chartClassify (intRingHom d.base) d.param

/-- **Tag 0CBY follows from the chart form.** -/
public theorem nonempty_standardNodalDiagram_of_nodalChartNeighbourhood {X S : Scheme.{u}}
    {f : X ⟶ S} {x : X} (hd : Nonempty (NodalChartNeighbourhood f x)) :
    Nonempty (StandardNodalDiagram f x) :=
  hd.map standardNodalDiagramOfChart

/-- **Tag 0CBY's diagram from an étale-local approximation over the standard family.** Suppose
given an étale `V ⟶ S`, a parameter `τ : V ⟶ Spec ℤ[a]`, and an étale morphism `U ⟶ W` to the
base change `W = Spec ℤ[u, v, a]/(uv - a) ×_{Spec ℤ[a]} V` together with an étale `U ⟶ X`
carrying a point of `U` to `x` and compatible with `f`. Then the diagram of Tag 0CBY is in hand:
the right-hand square is the cartesian square defining `W`, and nothing more is needed.

This is the shape in which [Stacks, Tag 0GDX] delivers its conclusion for the standard family,
so it is the step by which the first proof of Tag 0CBY ends: what the approximation lemma
produces is exactly the tag's diagram. Note that the point of `W` over which the point of `U`
lies plays no part — only the étale morphisms and the commutativity are used. -/
public def standardNodalDiagramOfEtaleApproximation {X S : Scheme.{u}} {f : X ⟶ S} {x : X}
    {V U : Scheme.{u}} (eV : V ⟶ S) [Etale eV]
    (τ : V ⟶ Spec (.of (Polynomial (ULift.{u} ℤ))))
    (eU : U ⟶ (pullback (standardNodalFamily (ULift.{u} ℤ)) τ : Scheme.{u})) [Etale eU]
    (p : U ⟶ X) [Etale p] (u : U) (hu : p.base u = x)
    (hcomm : p ≫ f = eU ≫ pullback.snd (standardNodalFamily (ULift.{u} ℤ)) τ ≫ eV) :
    StandardNodalDiagram f x where
  U := U
  V := V
  W := pullback (standardNodalFamily (ULift.{u} ℤ)) τ
  toSource := p
  toBase := eV
  familyU := eU ≫ pullback.snd (standardNodalFamily (ULift.{u} ℤ)) τ
  familyW := pullback.snd (standardNodalFamily (ULift.{u} ℤ)) τ
  toModel := eU
  classifyW := pullback.fst (standardNodalFamily (ULift.{u} ℤ)) τ
  classifyV := τ
  pt := u
  etale_toSource := inferInstance
  etale_toBase := inferInstance
  etale_toModel := inferInstance
  pt_mem := hu
  comm_left := by rw [hcomm, Category.assoc]
  comm_model := rfl
  isPullback_model := IsPullback.of_hasPullback _ _

end Stacks.NodalEtaleLocalStructure

end
