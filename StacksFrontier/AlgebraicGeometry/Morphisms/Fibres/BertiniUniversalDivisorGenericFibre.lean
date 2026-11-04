module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericFibreResidueFieldCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniUniversalDivisorFunctionField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generic fibre of the universal family, and Bertini irreducibility

For general `v ∈ V ⊗_k k'` the divisor `H_v` is geometrically irreducible over `k'`. The key step
is that the residue field `κ(ξ)` of the universal divisor `H_univ` at its generic point is
geometrically irreducible over the residue field `κ(η)` of `𝔸^r_k` at its generic point, so the
generic fibre of the universal family is geometrically irreducible.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.parameterSpecResidueField`: the residue field `κ(η)` of
  `Spec Γ(𝔸^r_k, ⊤)` at its generic point, with its `k[xⱼ]`-algebra and `k`-algebra structures
  `Stacks.Bertini.FamilyDivisors.parameterSpecResidueFieldAlgebra` and
  `Stacks.Bertini.FamilyDivisors.parameterSpecResidueFieldBaseAlgebra`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.residueFieldMapOfEq_evaluation`: naturality of evaluation at a
  point for the restriction maps of a morphism, with the point of the target presented as a point
  equal to the image.
* `Algebra.isGeometricallyIrreducible_of_ringEquiv_base`: geometric irreducibility transports along
  an isomorphism of the base field.
* `Stacks.Bertini.FamilyDivisors.isFractionRing_parameterSpecResidueField` and
  `Stacks.Bertini.FamilyDivisors.adjoin_range_parameterSpecResidueField_eq_top`: `κ(η)` is a
  fraction field of `k[xⱼ]`, generated over `k` by the images of the coordinates.
* `Stacks.Bertini.FamilyDivisors.residueFieldMapOfEq_universalFamily_algebraMap`: the residue field
  map of the universal family on the parameters.
* `Stacks.Bertini.FamilyDivisors.Hypotheses.base_genericPoint_universalFamily`: the universal
  family carries the generic point of `H_univ` to the generic point of `𝔸^r_k`.
* `Stacks.Bertini.FamilyDivisors.Hypotheses.isGeometricallyIrreducible_residueField_genericPoint`:
  `κ(ξ)` is geometrically irreducible over `κ(η)`.
* `Stacks.Bertini.FamilyDivisors.Hypotheses.geometricallyIrreducible_fiber_genericPoint`: the
  generic fibre of the universal family is geometrically irreducible.
* `Stacks.Bertini.FamilyDivisors.Hypotheses.forGeneral_geometricallyIrreducible`: for general `v`
  the divisor `H_v` is geometrically irreducible.

## References

* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 054Q](https://stacks.math.columbia.edu/tag/054Q)
* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

/-! ### Two general ingredients -/

/-- Evaluation at a point is natural for the restriction maps of a morphism, with the point of the
target presented as a point `y` equal to `f x`. -/
theorem AlgebraicGeometry.Scheme.Hom.residueFieldMapOfEq_evaluation {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : Y.Opens} {V : X.Opens} (hVU : V ≤ f ⁻¹ᵁ U) (x : X) (hx : x ∈ V) {y : Y} (hy : f x = y)
    (hyU : y ∈ U) (a : Γ(Y, U)) :
    f.residueFieldMapOfEq hy (Y.evaluation U y hyU a) =
      X.evaluation V x hx (f.appLE U V hVU a) := by
  subst hy
  rw [Scheme.Hom.residueFieldMapOfEq_rfl]
  exact f.evaluation_appLE_apply hVU x hx hyU a

/-- Geometric irreducibility transports along an isomorphism of the base field: if `e : k ≃+* k'`
and the structure map of `A` over `k` is that over `k'` precomposed with `e`, then `A` is
geometrically irreducible over `k` as soon as it is over `k'`. -/
theorem Algebra.isGeometricallyIrreducible_of_ringEquiv_base {k k' A : Type u} [Field k]
    [Field k'] [CommRing A] [Algebra k A] [Algebra k' A] (e : k ≃+* k')
    (he : ∀ a : k, algebraMap k' A (e a) = algebraMap k A a)
    (h : Algebra.IsGeometricallyIrreducible k' A) :
    Algebra.IsGeometricallyIrreducible k A := by
  have : MorphismProperty.RespectsIso @AlgebraicGeometry.GeometricallyIrreducible.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsIso (CommRingCat.ofHom (e : k →+* k')) := e.toCommRingCatIso.isIso_hom
  have hcomp : (algebraMap k A) = (algebraMap k' A).comp (e : k →+* k') :=
    RingHom.ext fun a ↦ (he a).symm
  show AlgebraicGeometry.GeometricallyIrreducible
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  rw [hcomp, CommRingCat.ofHom_comp, Spec.map_comp]
  exact (MorphismProperty.cancel_right_of_respectsIso _ _ _).mpr h

namespace Stacks.Bertini.FamilyDivisors

/-! ### `κ(η)` as a fraction field of the polynomial ring in the parameters -/

variable (D : FamilyDivisors.{u, v})

/-- The functions on the parameter space over the base field form a domain. -/
instance isDomain_parameterBaseΓ : IsDomain Γ(D.parameterBase, ⊤) :=
  haveI : Nontrivial Γ(D.parameterBase, ⊤) := D.parameterBaseΓEquiv.symm.toEquiv.nontrivial
  Function.Injective.isDomain
    (D.parameterBaseΓEquiv.symm : Γ(D.parameterBase, ⊤) →+* MvPolynomial D.basisIndex D.k)
    D.parameterBaseΓEquiv.symm.injective

/-- The residue field `κ(η)` of the parameter space at its generic point, written on
`Spec Γ(𝔸^r_k, ⊤)`. -/
abbrev parameterSpecResidueField : CommRingCat.{u} :=
  (Spec Γ(D.parameterBase, ⊤)).residueField (genericPoint (Spec Γ(D.parameterBase, ⊤)))

/-- The algebra structure of `κ(η)` over the polynomial ring in the parameters: the canonical map
of `Γ(𝔸^r_k, ⊤)` into the residue field, read through
`Stacks.Bertini.FamilyDivisors.parameterBaseΓEquiv`. -/
@[instance_reducible]
def parameterSpecResidueFieldAlgebra :
    Algebra (MvPolynomial D.basisIndex D.k) D.parameterSpecResidueField :=
  ((@algebraMap Γ(D.parameterBase, ⊤) D.parameterSpecResidueField _ _
      (specResidueFieldAlgebra Γ(D.parameterBase, ⊤)
        (genericPoint (Spec Γ(D.parameterBase, ⊤))))).comp
    D.parameterBaseΓEquiv.toRingHom).toAlgebra

/-- The residue field of `Spec Γ(𝔸^r_k, ⊤)` at its generic point is a fraction field of the
polynomial ring in the parameters: `κ(η) = k(xⱼ)`. -/
@[stacks 0G4F "the residue field at the generic point of the parameter space, on `Spec Γ`"]
theorem isFractionRing_parameterSpecResidueField :
    letI := D.parameterSpecResidueFieldAlgebra
    IsFractionRing (MvPolynomial D.basisIndex D.k) D.parameterSpecResidueField := by
  let := specResidueFieldAlgebra Γ(D.parameterBase, ⊤)
    (genericPoint (Spec Γ(D.parameterBase, ⊤)))
  have : IsFractionRing Γ(D.parameterBase, ⊤) D.parameterSpecResidueField :=
    isFractionRing_specResidueField_genericPoint Γ(D.parameterBase, ⊤)
  exact (IsFractionRing.isFractionRing_iff_of_base_ringEquiv
    (S := D.parameterSpecResidueField) D.parameterBaseΓEquiv.symm).mp inferInstance

/-- The algebra structure of `κ(η)` over the base field, through the constants of the polynomial
ring in the parameters. -/
@[instance_reducible]
def parameterSpecResidueFieldBaseAlgebra : Algebra D.k D.parameterSpecResidueField :=
  letI := D.parameterSpecResidueFieldAlgebra
  ((algebraMap (MvPolynomial D.basisIndex D.k) D.parameterSpecResidueField).comp
    (MvPolynomial.C : D.k →+* MvPolynomial D.basisIndex D.k)).toAlgebra

/-- `κ(η)` is generated over `k` by the images of the coordinates. -/
@[stacks 0G4F "the coordinates generate the residue field at the generic point of `𝔸^r_k`"]
theorem adjoin_range_parameterSpecResidueField_eq_top :
    letI := D.parameterSpecResidueFieldAlgebra
    letI := D.parameterSpecResidueFieldBaseAlgebra
    IntermediateField.adjoin D.k
      (Set.range fun j : D.basisIndex =>
        algebraMap (MvPolynomial D.basisIndex D.k) D.parameterSpecResidueField
          (MvPolynomial.X j)) = ⊤ := by
  let := D.parameterSpecResidueFieldAlgebra
  let := D.parameterSpecResidueFieldBaseAlgebra
  have := D.isFractionRing_parameterSpecResidueField
  have : IsScalarTower D.k (MvPolynomial D.basisIndex D.k) D.parameterSpecResidueField :=
    .of_algebraMap_eq fun _ ↦ rfl
  exact Algebra.adjoin_range_algebraMap_X_eq_top D.k D.parameterSpecResidueField

/-! ### The residue field map of the universal family on the parameters -/

variable {D}

/-- The residue field map of the universal family, computed on the parameters. Let `c` be a
trivializing affine chart on which the chart ring of the universal divisor is a domain and let
`κ(ξ)` be a fraction field of it with structure map evaluation at the generic point `ξ` of
`H_univ`. Then the residue field map `κ(η) → κ(ξ)` of `H_univ → Spec Γ(𝔸^r_k, ⊤)` carries the image
of a polynomial `p ∈ k[xⱼ]` to the image of `p` in the chart ring, its coefficients reduced.
-/
theorem residueFieldMapOfEq_universalFamily_algebraMap (c : D.Chart)
    [IrreducibleSpace D.universalDivisorScheme] [Nontrivial (reducedChartDivisorRing c)]
    [Algebra (reducedChartDivisorRing c)
      (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme))]
    (hev : ∀ a : Γ(D.universalDivisorScheme, D.chartDivisorOpen c.U),
      algebraMap (reducedChartDivisorRing c)
          (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme))
          (reducedChartDivisorReduction c (D.chartSubschemeΓEquiv c.U c.triv a)) =
        D.universalDivisorScheme.evaluation (D.chartDivisorOpen c.U)
          (genericPoint D.universalDivisorScheme)
          (D.genericPoint_mem_chartDivisorOpen c) a)
    (hη : (D.universalFamily ≫ D.parameterBase.isoSpec.hom)
        (genericPoint D.universalDivisorScheme) =
      genericPoint (Spec Γ(D.parameterBase, ⊤)))
    (p : MvPolynomial D.basisIndex D.k) :
    letI := D.parameterSpecResidueFieldAlgebra
    (D.universalFamily ≫ D.parameterBase.isoSpec.hom).residueFieldMapOfEq hη
        (algebraMap (MvPolynomial D.basisIndex D.k) D.parameterSpecResidueField p) =
      Algebra.universalDivisorChartMap (reducedChartRing c.U)
        (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme))
        (reducedChartEquation c) (MvPolynomial.map (reducedChartRingHom c.U) p) := by
  let := D.parameterSpecResidueFieldAlgebra
  have hiso : D.parameterBase.isoSpec.hom.appLE (⊤ : (Spec Γ(D.parameterBase, ⊤)).Opens)
      (⊤ : D.parameterBase.Opens) le_top = (Scheme.ΓSpecIso Γ(D.parameterBase, ⊤)).hom :=
    (Scheme.Hom.appLE_eq_app _).trans (Scheme.toSpecΓ_appTop D.parameterBase)
  have hmor : (Scheme.ΓSpecIso Γ(D.parameterBase, ⊤)).inv ≫
      (D.universalFamily ≫ D.parameterBase.isoSpec.hom).appLE ⊤
        (D.chartDivisorOpen c.U) le_top =
      D.universalFamily.appLE ⊤ (D.chartDivisorOpen c.U) le_top := by
    rw [← Scheme.Hom.appLE_comp_appLE D.universalFamily D.parameterBase.isoSpec.hom
      (⊤ : (Spec Γ(D.parameterBase, ⊤)).Opens) (⊤ : D.parameterBase.Opens)
      (D.chartDivisorOpen c.U) le_top le_top, hiso, Iso.inv_hom_id_assoc]
  have h3 : (D.universalFamily ≫ D.parameterBase.isoSpec.hom).appLE ⊤
        (D.chartDivisorOpen c.U) le_top
        ((Scheme.ΓSpecIso Γ(D.parameterBase, ⊤)).inv (D.parameterBaseΓEquiv p)) =
      D.universalFamily.appLE ⊤ (D.chartDivisorOpen c.U) le_top (D.parameterBaseΓEquiv p) :=
    (CommRingCat.comp_apply _ _ _).symm.trans
      (congrArg (fun φ : Γ(D.parameterBase, ⊤) ⟶ _ ↦ φ.hom (D.parameterBaseΓEquiv p)) hmor)
  have h2 := (D.universalFamily ≫ D.parameterBase.isoSpec.hom).residueFieldMapOfEq_evaluation
    (U := ⊤) (V := D.chartDivisorOpen c.U) le_top (genericPoint D.universalDivisorScheme)
    (D.genericPoint_mem_chartDivisorOpen c) hη trivial
    ((Scheme.ΓSpecIso Γ(D.parameterBase, ⊤)).inv (D.parameterBaseΓEquiv p))
  exact h2.trans ((congrArg _ h3).trans
    ((hev (D.universalFamily.appLE ⊤ (D.chartDivisorOpen c.U) le_top
      (D.parameterBaseΓEquiv p))).symm.trans
        (congrArg _ (D.reducedChartDivisorReduction_chartDivisorParameterMap c p))))

/-! ### Geometric irreducibility of the generic fibre -/

namespace Hypotheses

variable (h : D.Hypotheses)

include h

/-- The universal family carries the generic point of `H_univ` to the generic point of `𝔸^r_k`. -/
theorem base_genericPoint_universalFamily :
    haveI := h.irreducibleSpace_universalDivisorScheme
    D.universalFamily (genericPoint D.universalDivisorScheme) =
      genericPoint D.parameterBase := by
  have := h.irreducibleSpace_universalDivisorScheme
  have := h.isDominant_universalFamily
  exact D.universalFamily.base_genericPoint_eq_of_denseRange
    (Scheme.Hom.denseRange D.universalFamily) (by simpa using genericPoint_spec D.parameterBase)

/-- The residue field of `H_univ` at its generic point is geometrically irreducible over `κ(η)`. -/
@[stacks 0G4F "the generic fibre, read on the residue field of the universal divisor"]
theorem isGeometricallyIrreducible_residueField_genericPoint :
    haveI := h.irreducibleSpace_universalDivisorScheme
    letI := residueFieldAlgebraOfEq (D.universalFamily ≫ D.parameterBase.isoSpec.hom)
      (comp_isoSpec_genericPoint_eq D.universalFamily h.base_genericPoint_universalFamily)
    Algebra.IsGeometricallyIrreducible D.parameterSpecResidueField
      (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme)) := by
  have := h.irreducibleSpace_universalDivisorScheme
  let := D.parameterSpecResidueFieldAlgebra
  let := D.parameterSpecResidueFieldBaseAlgebra
  have := D.isFractionRing_parameterSpecResidueField
  let := residueFieldAlgebraOfEq (D.universalFamily ≫ D.parameterBase.isoSpec.hom)
    (comp_isoSpec_genericPoint_eq D.universalFamily h.base_genericPoint_universalFamily)
  obtain ⟨c, m, b, b', hbb', hb'b, hrest⟩ := h.exists_chart_substitution
  let := reducedChartAlgebra c.U
  obtain ⟨g, w, hg, hw, hcodim⟩ := hrest
  have := h.isDomain_reducedChartRing c
  have := h.algebraFiniteType_reducedChartRing c
  have := isScalarTower_reducedChartFractionRing (D := D) c.U
  have := h.isDomain_reducedChartDivisorRing c b b' hbb' hb'b g w hg hw
  obtain ⟨_, hfr, hev⟩ := isFractionRing_residueField_chartDivisorRing c
  have := hfr
  have hinj := injective_algebraMap_reducedChartDivisorRing c b b' hbb' hb'b g w hg hw
  have hcomp : Function.Injective
      ((algebraMap (reducedChartDivisorRing c)
          (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme))).comp
        (algebraMap (reducedChartRing c.U) (reducedChartDivisorRing c))) :=
    (IsFractionRing.injective (reducedChartDivisorRing c) _).comp hinj
  let : Algebra (reducedChartFractionRing c.U)
      (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme)) :=
    (IsFractionRing.lift hcomp).toAlgebra
  have hlift : ∀ a : reducedChartRing c.U,
      algebraMap (reducedChartFractionRing c.U)
          (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme))
          (algebraMap (reducedChartRing c.U) (reducedChartFractionRing c.U) a) =
        algebraMap (reducedChartDivisorRing c)
          (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme))
          (algebraMap (reducedChartRing c.U) (reducedChartDivisorRing c) a) :=
    IsFractionRing.lift_algebraMap hcomp
  let : Algebra D.k
      (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme)) :=
    ((algebraMap (reducedChartFractionRing c.U)
        (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme))).comp
      (algebraMap D.k (reducedChartFractionRing c.U))).toAlgebra
  have : IsScalarTower D.k (reducedChartFractionRing c.U)
      (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hgi := h.isGeometricallyIrreducible_reducedChartDivisor c b b' hbb' hb'b
    ↥(D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme))
    g w hg hw hcodim hlift
  have hψ := fun p ↦ residueFieldMapOfEq_universalFamily_algebraMap c hev
    (comp_isoSpec_genericPoint_eq D.universalFamily h.base_genericPoint_universalFamily) p
  have hhom := universalDivisorChartMap_comp_map_reducedChartRingHom c
    ↥(D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme)) hlift
  have : IsScalarTower D.k D.parameterSpecResidueField
      ↥(D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme)) := by
    refine IsScalarTower.of_algebraMap_eq fun a ↦ ?_
    have hX : Algebra.universalDivisorChartMap (reducedChartRing c.U)
        ↥(D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme))
          (reducedChartEquation c)
          (MvPolynomial.map (reducedChartRingHom c.U) (MvPolynomial.C a)) =
        algebraMap (reducedChartDivisorRing c) _
          (algebraMap (reducedChartRing c.U) (reducedChartDivisorRing c)
            (algebraMap D.k (reducedChartRing c.U) a)) := by
      rw [MvPolynomial.map_C]
      rfl
    exact (hlift _).trans (hX.symm.trans (hψ (MvPolynomial.C a)).symm)
  let f := IsScalarTower.toAlgHom D.k D.parameterSpecResidueField
    ↥(D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme))
  let x : D.basisIndex → ↥(D.universalDivisorScheme.residueField
      (genericPoint D.universalDivisorScheme)) := fun j ↦
    Algebra.universalDivisorChartMap (reducedChartRing c.U) _ (reducedChartEquation c)
      (MvPolynomial.X j)
  have hfield := IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq
    (F := D.k) (A := MvPolynomial D.basisIndex D.k) (K := D.parameterSpecResidueField)
    (f := f) (g := MvPolynomial.aeval x)
    (RingHom.ext fun p ↦ (hψ p).trans (DFunLike.congr_fun hhom p))
    (Algebra.adjoin_range_eq_range_aeval D.k x).symm
  exact Algebra.isGeometricallyIrreducible_of_ringEquiv_base
    ((AlgEquiv.ofInjectiveField f).trans (IntermediateField.equivOfEq hfield)).toRingEquiv
    (fun _ ↦ rfl) hgi

/-- The generic fibre of the universal family is geometrically irreducible. -/
@[stacks 0G4F "the generic fibre of the universal family",
  sga "7 XVIII 6.1.6.1" "Case s = 1 of 6.1.6.1"]
theorem geometricallyIrreducible_fiber_genericPoint :
    haveI := h.irreducibleSpace_universalDivisorScheme
    GeometricallyIrreducible
      (D.universalFamily.fiberToSpecResidueField (genericPoint D.parameterBase)) := by
  have := h.irreducibleSpace_universalDivisorScheme
  let := residueFieldAlgebraOfEq (D.universalFamily ≫ D.parameterBase.isoSpec.hom)
    (comp_isoSpec_genericPoint_eq D.universalFamily h.base_genericPoint_universalFamily)
  exact (geometricallyIrreducible_fiber_genericPoint_iff_residueField_of_isAffine
    D.universalFamily h.base_genericPoint_universalFamily).mpr
    h.isGeometricallyIrreducible_residueField_genericPoint

/-- Let `X` be a scheme of finite type over a field `k`, geometrically irreducible over `k`, let
`L` be an invertible module on `X` and let `V ⊂ Γ(X, L)` be a finite dimensional linear system.
Assume there are `v₁, v₂, v₃ ∈ V` and an irreducible component `Z` of `H_{v₂} ∩ H_{v₃}` with
`Z ⊄ H_{v₁}` and `codim(Z, X) = 2`, and assume every irreducible closed subset of the common zero
locus of `V` has codimension at least two in `X`. Then for general `v ∈ V ⊗_k k'` the divisor `H_v`
is geometrically irreducible over `k'`: there is one nonempty open `U ⊂ 𝔸^r_k`, defined over `k`,
such that `H_v` is geometrically irreducible over `k'` for every field extension `k'/k` and every
`k'`-point of `U`. -/
@[stacks 0G4F, sga "7 XVIII 6.1.6.1" "special case"]
theorem forGeneral_geometricallyIrreducible :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          GeometricallyIrreducible
            ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) := by
  have := h.locallyOfFiniteType
  have := h.quasiCompact
  have := h.irreducibleSpace_universalDivisorScheme
  exact D.forGeneral_geometricallyIrreducible_of_genericFibre (genericPoint D.parameterBase)
    (by simpa using genericPoint_spec D.parameterBase) h.geometricallyIrreducible_fiber_genericPoint

end Hypotheses

end Stacks.Bertini.FamilyDivisors

end
