module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorGeneratorUnit
public import StacksFrontier.Algebra.Polynomial.LaurentEvalBijective
public import StacksFrontier.Examples.Stacks.AffineLineQuotientDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LaurentAlgebraChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos

/-!
# The Laurent algebra over a trivializing chart is a ring of Laurent polynomials

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module and let `V` be an
étale chart of `X` over which `ℒ` is trivial.  This file proves that, when `V` is quasi-compact,
the ring of sections over `V` of the Laurent algebra `𝒜 = ⨁_{n ∈ ℤ} ℒ^{⊗ n}` is the ring of
Laurent polynomials over `𝒪(V)`:

`𝒪(V)[T, T⁻¹] ≅ 𝒜(V)`, as `𝒪(V)`-algebras.

On spectra this is the identification `T ×_X V ≅ 𝐆_m × V` of Stacks 0EQG. Consequently
`Spec 𝒜(V) ⟶ V` is surjective and smooth of relative dimension one, with irreducible fibres.

## Main definitions

* `AlgebraicGeometry.Space.laurentChartGenerator`: the generator in degree `n` of the Laurent
  algebra over a chart trivializing `ℒ`.
* `AlgebraicGeometry.Space.laurentChartUnit`: the degree-one generator, as a unit of the ring of
  sections `⨁_n Γ(V, ℒ^{⊗ n})`.
* `AlgebraicGeometry.Space.laurentChartRingEquiv`: the ring isomorphism `𝒪(V)[T, T⁻¹] ≅ 𝒜(V)`
  over a quasi-compact trivializing chart.

## Main results

* `AlgebraicGeometry.Space.isUnit_of_forall_isUnit_map_of_mem_topology`: a function on an étale
  chart which is a unit on a covering sieve is a unit.
* `AlgebraicGeometry.Space.isUnit_laurentMulUnitSection`: the product of the generators in degrees
  one and minus one is a unit.
* `AlgebraicGeometry.Space.bijective_eval₂_laurentChartUnit`: `⨁_n Γ(V, ℒ^{⊗ n})` is the ring of
  Laurent polynomials over `𝒪(V)` in the degree-one generator.
* `AlgebraicGeometry.Space.laurentChartRingEquiv_C`: `laurentChartRingEquiv` is an isomorphism of
  `𝒪(V)`-algebras.
* `AlgebraicGeometry.Space.smoothOfRelativeDimension_specChartMap_laurentAlgebraSheaf`,
  `AlgebraicGeometry.Space.surjective_specChartMap_laurentAlgebraSheaf`,
  `AlgebraicGeometry.Space.isIrreducible_preimage_singleton_specChartMap_laurentAlgebraSheaf`:
  `Spec 𝒜(V) ⟶ V` is smooth of relative dimension one and surjective, with irreducible fibres.

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 022U](https://stacks.math.columbia.edu/tag/022U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Units

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- A function on an étale chart which becomes a unit along every arrow of a covering sieve is
a unit. -/
theorem isUnit_of_forall_isUnit_map_of_mem_topology (V : SmallEtale B S hS F)
    (a : (structureSheaf' B S hS F).obj.obj (op V)) {T : Sieve V}
    (hT : T ∈ SmallEtale.topology B S hS F V)
    (h : ∀ ⦃W : SmallEtale B S hS F⦄ (g : W ⟶ V), T g →
      IsUnit (((structureSheaf' B S hS F).obj.map g.op) a)) :
    IsUnit a := by
  let Y := (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)
  let a' : Γ(Y, ⊤) := a
  have hbo : Y.basicOpen a' = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨W, g, hg, w, hw⟩ :=
      (SmallEtale.mem_topology_iff_exists_mem_range B S hS F T).1 hT z
    let gs := (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map g)
    have hu : IsUnit (gs.appTop a') := h g hg
    rw [← hw]
    change w ∈ gs ⁻¹ᵁ Y.basicOpen a'
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hu]
    trivial
  have hres := Y.toRingedSpace.isUnit_res_basicOpen a'
  have hcomp : (homOfLE hbo.ge : (⊤ : Y.Opens) ⟶ Y.basicOpen a') ≫
      homOfLE (Y.basicOpen_le a') = 𝟙 _ := Subsingleton.elim _ _
  have ha : a' = Y.presheaf.map (homOfLE hbo.ge).op
      (Y.presheaf.map (homOfLE (Y.basicOpen_le a')).op a') := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, hcomp, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  change IsUnit a'
  exact ha ▸ hres.map _

end Units

section Laurent

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)
    {V : SmallEtale D.site D.base D.base_mem X}
    (e : L.over V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over V))

/-- The generator in degree `n` of the Laurent algebra over a chart `V` trivializing `ℒ`: the
image of `1` under the induced trivialization of `ℒ^{⊗ n}` over `V`. -/
def laurentChartGenerator (n : ℤ) :
    ((laurentGradedAlgebra D p hp L hL).piece n).val.obj (op V) :=
  (laurentPieceTrivialization D p hp L hL e n).inv.val.app (op (Over.mk (𝟙 V)))
    (show (tensorStructureRingPresheaf D p hp).obj (op V) from 1)

/-- The generator in degree `n` generates `ℒ^{⊗ n}` over `V`. -/
theorem isGeneratorOver_laurentChartGenerator (n : ℤ) :
    Stacks.SheafOfModules.IsGeneratorOver (tensorStructureRingPresheaf D p hp)
      (isSheaf_tensorStructureRingPresheaf D p hp) ((laurentGradedAlgebra D p hp L hL).piece n)
      (laurentChartGenerator D p hp L hL e n) :=
  Stacks.SheafOfModules.isGeneratorOver_of_iso _ _ _ (laurentPieceTrivialization D p hp L hL e n)

include hL in
/-- The multiplication isomorphism `ℒ^{⊗ 1} ⊗ ℒ^{⊗ -1} ≅ 𝒪_X`, reindexed into degree zero. -/
def laurentMulUnitIso :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨tensorStructureRingPresheaf D p hp,
        Presheaf.isSheaf_of_isSheaf_comp _ (tensorStructureRingPresheaf D p hp)
          (forget₂ CommRingCat RingCat) (isSheaf_tensorStructureRingPresheaf D p hp)⟩).obj
        ((laurentGradedAlgebra D p hp L hL).piece 1)).obj
        ((laurentGradedAlgebra D p hp L hL).piece (-1)) ≅
      SheafOfModules.unit (tensorStructureSheaf D p hp) :=
  have : Stacks.SheafOfModules.IsInvertible (tensorStructureRingPresheaf D p hp)
      (isSheaf_tensorStructureRingPresheaf D p hp) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  have := Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor
    (tensorStructureRingPresheaf D p hp) (isSheaf_tensorStructureRingPresheaf D p hp) L
  Stacks.SheafOfModules.TensorPower.coherentMulIso (tensorStructureRingPresheaf D p hp)
      (isSheaf_tensorStructureRingPresheaf D p hp) L 1 (-1) ≪≫
    Stacks.SheafOfModules.TensorPower.tensorPowerReindex (tensorStructureRingPresheaf D p hp)
      (isSheaf_tensorStructureRingPresheaf D p hp) L (add_neg_cancel (1 : ℤ))

/-- The product of the generators in degrees one and minus one, a function on `V`. -/
def laurentMulUnitSection : (tensorStructureRingPresheaf D p hp).obj (op V) :=
  (laurentMulUnitIso D p hp L hL).hom.val.app (op V)
    (Stacks.SheafOfModules.tensorSectionsAt _ _ (op V)
      ((laurentGradedAlgebra D p hp L hL).piece 1) ((laurentGradedAlgebra D p hp L hL).piece (-1))
      (laurentChartGenerator D p hp L hL e 1) (laurentChartGenerator D p hp L hL e (-1)))

/-- The product of the generators in degrees one and minus one is a unit. -/
theorem isUnit_laurentMulUnitSection : IsUnit (laurentMulUnitSection D p hp L hL e) := by
  obtain ⟨T, hT, hunit⟩ := Stacks.SheafOfModules.exists_mem_isUnit_map_tensorSectionsAt
    (tensorStructureRingPresheaf D p hp) (isSheaf_tensorStructureRingPresheaf D p hp)
    ((laurentGradedAlgebra D p hp L hL).piece 1) ((laurentGradedAlgebra D p hp L hL).piece (-1))
    (isGeneratorOver_laurentChartGenerator D p hp L hL e 1)
    (isGeneratorOver_laurentChartGenerator D p hp L hL e (-1)) (laurentMulUnitIso D p hp L hL)
  exact isUnit_of_forall_isUnit_map_of_mem_topology D.site D.base D.base_mem X V _ hT
    fun W g hg => hunit g hg

/-! ### The graded ring of sections of the ungraded realization -/

/-- The ring of sections over `V` of the ungraded realization of the Laurent algebra: the direct
sum `⨁_n Γ(V, ℒ^{⊗ n})` with the coherent multiplication. -/
abbrev laurentChartTotal (V : SmallEtale D.site D.base D.base_mem X) : CommRingCat.{u} :=
  (laurentCommPresheaf D p hp L hL).obj (op V)

/-- A homogeneous section, read in the ring of sections of the ungraded realization. -/
abbrev laurentChartIncl (n : ℤ) (y : ((laurentGradedAlgebra D p hp L hL).piece n).val.obj (op V)) :
    laurentChartTotal D p hp L hL V :=
  (laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.incl n y

/-- The structure map `𝒪(V) → ⨁_n Γ(V, ℒ^{⊗ n})` of the ungraded realization. -/
abbrev laurentChartStructureMap :
    (tensorStructureRingPresheaf D p hp).obj (op V) →+* laurentChartTotal D p hp L hL V :=
  ((laurentCommStructureMap D p hp L hL).app (op V)).hom

/-- The product of homogeneous sections of degrees `i` and `j` is the homogeneous section of
degree `i + j` given by the multiplication of the graded algebra. -/
theorem laurentChartIncl_mul (i j : ℤ)
    (a : ((laurentGradedAlgebra D p hp L hL).piece i).val.obj (op V))
    (b : ((laurentGradedAlgebra D p hp L hL).piece j).val.obj (op V)) :
    laurentChartIncl D p hp L hL i a * laurentChartIncl D p hp L hL j b =
      laurentChartIncl D p hp L hL (i + j)
        (((laurentGradedAlgebra D p hp L hL).mul i j).app (op V) a b) :=
  (laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.incl_mul_incl i j a b

/-- The structure map sends a function `r` to the homogeneous section `r` of degree zero. -/
theorem laurentChartStructureMap_eq (r : (tensorStructureRingPresheaf D p hp).obj (op V)) :
    laurentChartStructureMap D p hp L hL r =
      laurentChartIncl D p hp L hL 0
        (show (tensorStructureRingPresheaf D p hp).obj (op V) from r) := by
  change (show (tensorStructureSheaf D p hp).obj.obj (op V) from r) •
    (1 : (laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.Total (op V)) = _
  rw [Stacks.GradedAlgebra.one_eq_incl, ← Stacks.GradedAlgebra.incl_smul]
  exact congrArg _ (mul_one r)

/-- The product of the generators in degrees one and minus one is the unit
`laurentMulUnitSection`, read in degree zero. -/
theorem laurentChartIncl_generator_mul :
    laurentChartIncl D p hp L hL 1 (laurentChartGenerator D p hp L hL e 1) *
        laurentChartIncl D p hp L hL (-1) (laurentChartGenerator D p hp L hL e (-1)) =
      laurentChartStructureMap D p hp L hL (laurentMulUnitSection D p hp L hL e) := by
  have : Stacks.SheafOfModules.IsInvertible (tensorStructureRingPresheaf D p hp)
      (isSheaf_tensorStructureRingPresheaf D p hp) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  have := Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor
    (tensorStructureRingPresheaf D p hp) (isSheaf_tensorStructureRingPresheaf D p hp) L
  rw [laurentChartIncl_mul, laurentChartStructureMap_eq]
  exact (laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.incl_congr_heq
    (add_neg_cancel (1 : ℤ)) (Stacks.SheafOfModules.TensorPower.heq_reindex
      (tensorStructureRingPresheaf D p hp) (isSheaf_tensorStructureRingPresheaf D p hp) L (op V)
      (add_neg_cancel (1 : ℤ)) _).symm

/-- The degree-one generator over a trivializing chart, as a unit of the ring of sections of the
ungraded realization; its inverse is the degree-minus-one generator divided by the unit
`laurentMulUnitSection`. -/
def laurentChartUnit : (laurentChartTotal D p hp L hL V)ˣ where
  val := laurentChartIncl D p hp L hL 1 (laurentChartGenerator D p hp L hL e 1)
  inv := laurentChartIncl D p hp L hL (-1) (laurentChartGenerator D p hp L hL e (-1)) *
    laurentChartStructureMap D p hp L hL
      (↑(isUnit_laurentMulUnitSection D p hp L hL e).unit⁻¹)
  val_inv := by
    rw [← mul_assoc, laurentChartIncl_generator_mul, ← map_mul, IsUnit.mul_val_inv, map_one]
  inv_val := by
    rw [mul_comm, ← mul_assoc, laurentChartIncl_generator_mul, ← map_mul, IsUnit.mul_val_inv,
      map_one]

/-- The additive identification of the ring of sections of the ungraded realization with the
direct sum of the sections of the tensor powers. -/
def laurentChartTotalAddEquiv :
    laurentChartTotal D p hp L hL V ≃+
      DirectSum ℤ fun n : ℤ => ((laurentGradedAlgebra D p hp L hL).piece n).val.obj (op V) :=
  AddEquiv.refl _

/-- A homogeneous section of degree `n` is homogeneous of degree `n` in the direct sum. -/
theorem isHomogeneousOf_laurentChartIncl (n : ℤ)
    (y : ((laurentGradedAlgebra D p hp L hL).piece n).val.obj (op V)) :
    LaurentPolynomial.IsHomogeneousOf (laurentChartTotalAddEquiv D p hp L hL (V := V)) n
      (laurentChartIncl D p hp L hL n y) :=
  ⟨y, rfl⟩

/-- The product of homogeneous elements of degrees `i` and `j` is homogeneous of degree
`i + j`. -/
theorem isHomogeneousOf_laurentChart_mul (i j : ℤ) (a b : laurentChartTotal D p hp L hL V)
    (ha : LaurentPolynomial.IsHomogeneousOf (laurentChartTotalAddEquiv D p hp L hL (V := V)) i a)
    (hb : LaurentPolynomial.IsHomogeneousOf (laurentChartTotalAddEquiv D p hp L hL (V := V)) j b) :
    LaurentPolynomial.IsHomogeneousOf (laurentChartTotalAddEquiv D p hp L hL (V := V)) (i + j)
      (a * b) := by
  obtain ⟨y, hy⟩ := ha
  obtain ⟨z, hz⟩ := hb
  have ha' : a = laurentChartIncl D p hp L hL i y := hy
  have hb' : b = laurentChartIncl D p hp L hL j z := hz
  rw [ha', hb', laurentChartIncl_mul]
  exact isHomogeneousOf_laurentChartIncl D p hp L hL _ _

/-- Over a chart trivializing `ℒ`, the ring of sections of the ungraded realization of the
Laurent algebra is `𝒪(V)[T, T⁻¹]`, with `T` the degree-one generator. -/
theorem bijective_eval₂_laurentChartUnit :
    Function.Bijective (LaurentPolynomial.eval₂ (laurentChartStructureMap D p hp L hL (V := V))
      (laurentChartUnit D p hp L hL e)) := by
  refine LaurentPolynomial.bijective_eval₂_of_isHomogeneousOf _ _
    (isHomogeneousOf_laurentChart_mul D p hp L hL) (AddEquiv.refl _)
    (fun r => laurentChartStructureMap_eq D p hp L hL r)
    (isHomogeneousOf_laurentChartIncl D p hp L hL 1 _) ?_
  have h0 : LaurentPolynomial.IsHomogeneousOf (laurentChartTotalAddEquiv D p hp L hL (V := V)) 0
      (laurentChartStructureMap D p hp L hL
        (↑(isUnit_laurentMulUnitSection D p hp L hL e).unit⁻¹)) := by
    rw [laurentChartStructureMap_eq]
    exact isHomogeneousOf_laurentChartIncl D p hp L hL 0 _
  have h := isHomogeneousOf_laurentChart_mul D p hp L hL (-1) 0 _ _
    (isHomogeneousOf_laurentChartIncl D p hp L hL (-1) (laurentChartGenerator D p hp L hL e (-1)))
    h0
  rwa [add_zero] at h

/-! ### The sections of the Laurent algebra sheaf -/

variable (hV : (SmallEtale.topology D.site D.base D.base_mem X).IsQuasiCompactObject V)

/-- Over a quasi-compact chart `V` trivializing `ℒ`, the sections of the Laurent algebra sheaf
form the ring `𝒪(V)[T, T⁻¹]`. -/
def laurentChartRingEquiv :
    LaurentPolynomial ((tensorStructureRingPresheaf D p hp).obj (op V)) ≃+*
      (laurentAlgebraSheaf D p hp L hL).right.obj.obj (op V) :=
  (RingEquiv.ofBijective _ (bijective_eval₂_laurentChartUnit D p hp L hL e)).trans
    (RingEquiv.ofBijective ((laurentCommUnit D p hp L hL).app (op V)).hom
      (bijective_laurentDirectSumHom_app D p hp L hL V hV))

/-- `laurentChartRingEquiv` is an isomorphism of algebras over the functions on `V`: it carries
a constant to its image under the structure map of the algebra sheaf. -/
theorem laurentChartRingEquiv_C (r : (tensorStructureRingPresheaf D p hp).obj (op V)) :
    laurentChartRingEquiv D p hp L hL e hV (LaurentPolynomial.C r) =
      (laurentAlgebraSheaf D p hp L hL).algebraMap (op V) r := by
  change ((laurentCommUnit D p hp L hL).app (op V)).hom
    (LaurentPolynomial.eval₂ (laurentChartStructureMap D p hp L hL (V := V))
      (laurentChartUnit D p hp L hL e) (LaurentPolynomial.C r)) = _
  rw [LaurentPolynomial.eval₂_C]
  rfl

/-- The structure map of the Laurent algebra sheaf at a quasi-compact trivializing chart is the
inclusion of constants into the Laurent polynomials, up to `laurentChartRingEquiv`. -/
theorem chartAlgebraMap_laurentAlgebraSheaf :
    chartAlgebraMap D.site D.base D.base_mem (X := ⟨X, hp.1⟩) (laurentAlgebraSheaf D p hp L hL) V =
      (CommRingCat.ofHom LaurentPolynomial.C :
          Γ(chartScheme V, ⊤) ⟶ CommRingCat.of (LaurentPolynomial Γ(chartScheme V, ⊤))) ≫
        (CommRingCat.ofHom (laurentChartRingEquiv D p hp L hL e hV).toRingHom :
          CommRingCat.of (LaurentPolynomial Γ(chartScheme V, ⊤)) ⟶
            (laurentAlgebraSheaf D p hp L hL).right.obj.obj (op V)) := by
  ext r
  exact (laurentChartRingEquiv_C D p hp L hL e hV r).symm

/-! ### The spectrum over a trivializing chart -/

/-- `Spec R[T, T⁻¹] ⟶ Spec R` is surjective. -/
theorem surjective_spec_map_laurentC (R : CommRingCat.{u}) :
    AlgebraicGeometry.Surjective (Spec.map (CommRingCat.ofHom
      (LaurentPolynomial.C : R →+* LaurentPolynomial R))) := by
  let ev : LaurentPolynomial R →+* R := LaurentPolynomial.eval₂ (RingHom.id R) 1
  have h : Spec.map (CommRingCat.ofHom ev) ≫ Spec.map (CommRingCat.ofHom
      (LaurentPolynomial.C : R →+* LaurentPolynomial R)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, show ev.comp LaurentPolynomial.C = RingHom.id R
      from RingHom.ext fun r => LaurentPolynomial.eval₂_C _ _ r]
    exact Spec.map_id _
  have : AlgebraicGeometry.Surjective (Spec.map (CommRingCat.ofHom ev) ≫ Spec.map
      (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R))) := by
    rw [h]
    infer_instance
  exact AlgebraicGeometry.Surjective.of_comp (Spec.map (CommRingCat.ofHom ev)) _

/-- `Spec R[T, T⁻¹] ⟶ Spec R` is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_spec_map_laurentC (R : CommRingCat.{u}) :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (LaurentPolynomial.C : R →+* LaurentPolynomial R))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    (Stacks.Examples.AffineLineQuotient.isStandardSmoothOfRelativeDimension_laurentC _)

/-- Over a quasi-compact chart `V` trivializing `ℒ`, `Spec 𝒜(V) ⟶ V` is, up to isomorphisms of
its source and target, `Spec 𝒪(V)[T, T⁻¹] ⟶ Spec 𝒪(V)`. -/
theorem specChartMap_laurentAlgebraSheaf_eq [IsAffine (chartScheme V)] :
    specChartMap D.site D.base D.base_mem (X := ⟨X, hp.1⟩) (laurentAlgebraSheaf D p hp L hL) V =
      Spec.map (CommRingCat.ofHom (laurentChartRingEquiv D p hp L hL e hV).toRingHom :
          CommRingCat.of (LaurentPolynomial Γ(chartScheme V, ⊤)) ⟶
            (laurentAlgebraSheaf D p hp L hL).right.obj.obj (op V)) ≫
        Spec.map (CommRingCat.ofHom LaurentPolynomial.C :
          Γ(chartScheme V, ⊤) ⟶ CommRingCat.of (LaurentPolynomial Γ(chartScheme V, ⊤))) ≫
        (chartScheme V).isoSpec.inv := by
  rw [specChartMap, chartAlgebraMap_laurentAlgebraSheaf D p hp L hL e hV, Spec.map_comp,
    Category.assoc]

/-- `Spec` of `laurentChartRingEquiv` is an isomorphism. -/
instance : IsIso (Spec.map (CommRingCat.ofHom (laurentChartRingEquiv D p hp L hL e hV).toRingHom :
    CommRingCat.of (LaurentPolynomial Γ(chartScheme V, ⊤)) ⟶
      (laurentAlgebraSheaf D p hp L hL).right.obj.obj (op V))) :=
  (Scheme.Spec.mapIso
    (RingEquiv.toCommRingCatIso (laurentChartRingEquiv D p hp L hL e hV)).op).isIso_hom

include e hV in
/-- Over a quasi-compact chart trivializing `ℒ`, `Spec 𝒜(V) ⟶ V` is smooth of relative
dimension one. -/
theorem smoothOfRelativeDimension_specChartMap_laurentAlgebraSheaf [IsAffine (chartScheme V)] :
    SmoothOfRelativeDimension 1
      (specChartMap D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
        (laurentAlgebraSheaf D p hp L hL) V) := by
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} 1) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).respectsIso
  rw [specChartMap_laurentAlgebraSheaf_eq D p hp L hL e hV,
    MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1),
    MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension 1)]
  exact smoothOfRelativeDimension_spec_map_laurentC _

include e hV in
/-- Over a quasi-compact chart trivializing `ℒ`, `Spec 𝒜(V) ⟶ V` is surjective. -/
theorem surjective_specChartMap_laurentAlgebraSheaf [IsAffine (chartScheme V)] :
    AlgebraicGeometry.Surjective
      (specChartMap D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
        (laurentAlgebraSheaf D p hp L hL) V) := by
  rw [specChartMap_laurentAlgebraSheaf_eq D p hp L hL e hV,
    MorphismProperty.cancel_left_of_respectsIso (P := @AlgebraicGeometry.Surjective),
    MorphismProperty.cancel_right_of_respectsIso (P := @AlgebraicGeometry.Surjective)]
  exact surjective_spec_map_laurentC _

/-- The fibres of `Spec R[T, T⁻¹] ⟶ Spec R` are irreducible: the fibre over `𝔭` is the
spectrum of `κ(𝔭) ⊗_R R[T, T⁻¹] = κ(𝔭)[T, T⁻¹]`, a domain. -/
theorem isIrreducible_preimage_singleton_spec_map_laurentC (R : CommRingCat.{u})
    (z : Spec R) :
    IsIrreducible ((Spec.map (CommRingCat.ofHom
      (LaurentPolynomial.C : R →+* LaurentPolynomial R))) ⁻¹' {z}) := by
  have hC :
      (LaurentPolynomial.C : R →+* LaurentPolynomial R) = algebraMap R (LaurentPolynomial R) :=
    RingHom.ext LaurentPolynomial.C_eq_algebraMap
  let p : PrimeSpectrum R := z
  change IsIrreducible
    (PrimeSpectrum.comap (LaurentPolynomial.C : R →+* LaurentPolynomial R) ⁻¹' {p})
  rw [hC]
  let e := PrimeSpectrum.preimageHomeomorphFiber R (LaurentPolynomial R) p
  have : IsDomain (p.asIdeal.Fiber (LaurentPolynomial R)) :=
    MulEquiv.isDomain _
      (AddMonoidAlgebra.scalarTensorEquiv R (A := p.asIdeal.ResidueField)
        (M := ℤ)).toRingEquiv.toMulEquiv
  have h := ((IrreducibleSpace.isIrreducible_univ
    (PrimeSpectrum (p.asIdeal.Fiber (LaurentPolynomial R)))).image e.symm
      e.symm.continuous.continuousOn).image Subtype.val continuous_subtype_val.continuousOn
  rwa [Set.image_univ, e.symm.range_coe, Set.image_univ, Subtype.range_coe] at h

include e hV in
/-- Over a quasi-compact chart trivializing `ℒ`, the fibres of `Spec 𝒜(V) ⟶ V` are
irreducible. -/
theorem isIrreducible_preimage_singleton_specChartMap_laurentAlgebraSheaf [IsAffine (chartScheme V)]
    (y : chartScheme V) :
    IsIrreducible ((specChartMap D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
      (laurentAlgebraSheaf D p hp L hL) V) ⁻¹' {y}) := by
  rw [specChartMap_laurentAlgebraSheaf_eq D p hp L hL e hV]
  let ψ := Spec.map (CommRingCat.ofHom (laurentChartRingEquiv D p hp L hL e hV).toRingHom :
    CommRingCat.of (LaurentPolynomial Γ(chartScheme V, ⊤)) ⟶
      (laurentAlgebraSheaf D p hp L hL).right.obj.obj (op V))
  have h := isIrreducible_preimage_singleton_spec_map_laurentC Γ(chartScheme V, ⊤)
    ((chartScheme V).isoSpec.hom y)
  have hset : ((ψ ≫ Spec.map (CommRingCat.ofHom LaurentPolynomial.C) ≫
      (chartScheme V).isoSpec.inv) ⁻¹' {y}) =
      ψ.homeomorph.symm '' ((Spec.map (CommRingCat.ofHom
        (LaurentPolynomial.C : Γ(chartScheme V, ⊤) →+* _))) ⁻¹'
          {(chartScheme V).isoSpec.hom y}) := by
    rw [ψ.homeomorph.symm.image_eq_preimage_symm, Homeomorph.symm_symm]
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply,
      Scheme.Hom.homeomorph_apply]
    exact ⟨fun hw => by rw [← hw, Scheme.inv_hom_apply], fun hw => by rw [hw, Scheme.hom_inv_apply]⟩
  exact hset ▸ h.image _ ψ.homeomorph.symm.continuous.continuousOn

end Laurent

end AlgebraicGeometry.Space

end
