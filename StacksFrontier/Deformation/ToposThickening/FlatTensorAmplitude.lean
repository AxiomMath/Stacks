module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedAbovePCellular
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Deformation.ToposThickening.DerivedTensorExtensionOfScalars
public import StacksFrontier.Deformation.ToposThickening.FlatRepresentative

/-!
# Tensoring bounded above complexes of flat modules keeps cohomological bounds

Let `R` be a sheaf of commutative rings on a site and `M` a sheaf of `R`-modules. For bounded
above complexes of flat `R`-modules the degreewise tensor product `- ⊗_R M` computes the derived
tensor product, which is right t-exact. This file records the two consequences used in the
proof of Stacks 0DIZ (2), in the form of Stacks 0DIV for bounded above complexes of flat
modules:

* if such a complex has no cohomology in degrees `≥ n`, neither has its tensor product with `M`;
* if a map `v` of such complexes induces isomorphisms on cohomology in degrees `> n` and a
  surjection in degree `n`, then so does `v ⊗ M`.

The first is proved by replacing the complex by a complex of flat modules vanishing in degrees
`≥ n` (Tag 05T7 for flat modules), the two being joined by a quasi-isomorphism of cellular
complexes, which tensoring with `M` keeps (Tag 0794). The second is the first applied to the
mapping cone of `v`, read through the long exact cohomology sequence of the cone.

## Main results

* `Deformation.ComplexLift.isFlatCellular_of_isStrictlyLE`: a bounded above complex of flat
  modules is cellular.
* `Deformation.ComplexLift.quasiIso_tensorRight_of_isPCellular`: tensoring with `M` keeps a
  quasi-isomorphism of cellular complexes.
* `Deformation.ComplexLift.exactAt_tensorRight_of_isStrictlyLE`: the vanishing statement.
* `Deformation.ComplexLift.homologyMap_tensorRight_of_isStrictlyLE`: the approximation statement.

## References

* [Stacks Project, Tag 0DIV](https://stacks.math.columbia.edu/tag/0DIV)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.UnboundedLeftDerivedFunctor

universe d v' u u'

namespace Deformation.ComplexLift

attribute [-instance] CategoryTheory.catToReflQuiver

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u})

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A bounded above complex of flat modules is cellular.** -/
theorem isFlatCellular_of_isStrictlyLE
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (a : ℤ) [K.IsStrictlyLE a] (hK : ∀ i, flatObjects R (K.X i)) :
    IsPCellular (flatObjects R) K :=
  isPCellular_of_isStrictlyLE_of_biprod_of_epi (flatObjects R) (flatObjects_biprod R)
    (flatObjects_cover R) K a hK

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The mapping cone of a map of complexes of flat modules is a complex of flat modules. -/
theorem flatObjects_mappingCone_X
    {X Y : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (v : X ⟶ Y) (hX : ∀ i, flatObjects R (X.X i)) (hY : ∀ i, flatObjects R (Y.X i)) (i : ℤ) :
    flatObjects R ((CochainComplex.mappingCone v).X i) :=
  Stacks.SheafOfModules.FlatRetract.isFlat_of_iso R
    (HomologicalComplex.homotopyCofiber.XIsoBiprod v i (i + 1) rfl).symm
    (flatObjects_biprod R _ _ (hX (i + 1)) (hY i))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The mapping cone of a map of complexes vanishing above `b` vanishes above `b`. -/
theorem isStrictlyLE_mappingCone
    {X Y : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (v : X ⟶ Y) (b : ℤ) [X.IsStrictlyLE b] [Y.IsStrictlyLE b] :
    (CochainComplex.mappingCone v).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨X.isZero_of_isStrictlyLE b (i + 1), Y.isZero_of_isStrictlyLE b i⟩

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))]
variable (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Tensoring with `M` keeps a quasi-isomorphism of cellular complexes** (Tag 0794). -/
theorem quasiIso_tensorRight_of_isPCellular
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (q : A ⟶ B) [QuasiIso q]
    (hA : IsPCellular (flatObjects R) A) (hB : IsPCellular (flatObjects R) B) :
    QuasiIso (((tensorRight R M).mapHomologicalComplex (ComplexShape.up ℤ)).map q) := by
  have h := isIso_map_tensorRightHomotopy_of_cellular.{d} R M
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 (by
      change QuasiIso q; infer_instance))
    (cellular_quotient_obj R hA) (cellular_quotient_obj R hB)
  rw [Functor.comp_map, Functor.mapHomotopyCategory_map] at h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1
    ((DerivedCategory.isIso_Qh_map_iff _).1 h)

omit [HasDerivedCategory (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R))]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- If `W` is strictly concentrated in degrees `≤ a`, then `W ⊗ M` is exact in every degree
`i > a`. -/
theorem exactAt_tensorRight_of_isStrictlyLE_aux
    (W : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (a : ℤ) [W.IsStrictlyLE a] (i : ℤ) (hi : a < i) :
    (((tensorRight R M).mapHomologicalComplex (ComplexShape.up ℤ)).obj W).ExactAt i := by
  have hz : IsZero ((tensorRight R M).obj (W.X i)) := by
    rw [IsZero.iff_id_eq_zero, ← (tensorRight R M).map_id,
      (W.isZero_of_isStrictlyLE a i hi).eq_of_src (𝟙 _) 0, (tensorRight R M).map_zero]
  exact (HomologicalComplex.exactAt_iff _ i).2 (ShortComplex.exact_of_isZero_X₂ _ hz)

/-- **Tensoring a bounded above complex of flat modules with no cohomology in degrees `≥ n`
gives a complex with no cohomology in degrees `≥ n`.** -/
theorem exactAt_tensorRight_of_isStrictlyLE
    (Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (b : ℤ) [Z.IsStrictlyLE b] (hZ : ∀ i, flatObjects R (Z.X i)) (n : ℤ)
    (h : ∀ i, n ≤ i → Z.ExactAt i) (i : ℤ) (hi : n ≤ i) :
    (((tensorRight R M).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z).ExactAt i := by
  have : Z.IsLE (n - 1) := by
    rw [CochainComplex.isLE_iff]
    intro j hj
    exact h j (by omega)
  obtain ⟨W, p, hp, hW, hWle⟩ : ∃ (W : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) (p : W ⟶ Z) (_ : QuasiIso p)
      (_ : ∀ n, flatObjects R (W.X n)), W.IsStrictlyLE (n - 1) :=
    exists_isFlat_quasiIso_isStrictlyLE_of_isLE R (n - 1) Z
  have hWc := isFlatCellular_of_isStrictlyLE R W (n - 1) hW
  have hZc := isFlatCellular_of_isStrictlyLE R Z b hZ
  have hq := quasiIso_tensorRight_of_isPCellular.{d} R M p hWc hZc
  rw [← exactAt_iff_of_quasiIsoAt
    (((tensorRight R M).mapHomologicalComplex (ComplexShape.up ℤ)).map p) i]
  exact exactAt_tensorRight_of_isStrictlyLE_aux R M W (n - 1) i (by omega)

variable {R} in
/-- If `Hⁱ(v)` is an isomorphism for `i > n` and an epimorphism for `i = n`, the mapping cone of
`v` has no cohomology in degrees `≥ n`. -/
theorem exactAt_mappingCone_of_approx {A : Type*} [Category A] [Abelian A]
    {X Y : CochainComplex A ℤ} (v : X ⟶ Y) (n : ℤ)
    (hiso : ∀ i, n < i → IsIso (HomologicalComplex.homologyMap v i))
    (hepi : ∀ i, n ≤ i → Epi (HomologicalComplex.homologyMap v i)) (i : ℤ) (hi : n ≤ i) :
    (CochainComplex.mappingCone v).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine (CochainComplex.shiftedMappingConeHomologyIso v (i + 1) i (by omega)).isZero_iff.1 ?_
  have h₁ := CochainComplex.mappingCone_homology_exact_target v i (i + 1) (by omega)
  have h₂ := CochainComplex.mappingCone_homology_exact_cone v i (i + 1) (by omega)
  have := hepi i hi
  have := hiso (i + 1) (by omega)
  have hz₁ : CochainComplex.coneHomologyConnecting v i (i + 1) (by omega) = 0 := by
    rw [← cancel_epi (HomologicalComplex.homologyMap v i), comp_zero]
    exact CochainComplex.homologyMap_comp_coneHomologyConnecting v i (i + 1) (by omega)
  have hz₂ : HomologicalComplex.homologyMap (pShift v) (i + 1) = 0 := by
    rw [← cancel_mono (HomologicalComplex.homologyMap v (i + 1)), zero_comp]
    exact CochainComplex.homologyMap_pShift_comp_homologyMap v i (i + 1) (by omega)
  have hm := h₂.mono_g hz₁
  exact IsZero.of_mono_eq_zero _ hz₂

variable {R} in
/-- If the mapping cone of `v` has no cohomology in degrees `≥ n`, then `Hⁱ(v)` is an
isomorphism for `i > n` and an epimorphism for `i = n`. -/
theorem homologyMap_of_exactAt_mappingCone {A : Type*} [Category A] [Abelian A]
    {X Y : CochainComplex A ℤ} (v : X ⟶ Y) (n : ℤ)
    (h : ∀ i, n ≤ i → (CochainComplex.mappingCone v).ExactAt i) :
    (∀ i, n < i → IsIso (HomologicalComplex.homologyMap v i)) ∧
      ∀ i, n ≤ i → Epi (HomologicalComplex.homologyMap v i) := by
  have hz : ∀ i, n ≤ i → IsZero
      (((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).obj
        (CochainComplex.mappingCone v)).homology (i + 1)) := fun i hi ↦
    (CochainComplex.shiftedMappingConeHomologyIso v (i + 1) i (by omega)).isZero_iff.2
      ((h i hi).isZero_homology)
  have hepi : ∀ i, n ≤ i → Epi (HomologicalComplex.homologyMap v i) := fun i hi ↦
    (CochainComplex.mappingCone_homology_exact_target v i (i + 1) (by omega)).epi_f
      ((hz i hi).eq_of_tgt _ _)
  refine ⟨fun i hi ↦ ?_, hepi⟩
  have := hepi i (by omega)
  have : Mono (HomologicalComplex.homologyMap v i) := by
    have hz' := hz (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at hz'
    exact (CochainComplex.mappingCone_homology_exact_source v (i - 1) i (by omega)).mono_g
      (hz'.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

/-- **Tensoring keeps cohomological approximations** (Stacks 0DIV, for bounded above complexes
of flat modules): if `v` is a map of bounded above complexes of flat modules with `Hⁱ(v)` an
isomorphism for `i > n` and an epimorphism for `i = n`, the same holds for `v ⊗ M`. -/
theorem homologyMap_tensorRight_of_isStrictlyLE
    {X Y : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (v : X ⟶ Y) (b : ℤ) [X.IsStrictlyLE b] [Y.IsStrictlyLE b]
    (hX : ∀ i, flatObjects R (X.X i)) (hY : ∀ i, flatObjects R (Y.X i)) (n : ℤ)
    (hiso : ∀ i, n < i → IsIso (HomologicalComplex.homologyMap v i))
    (hepi : ∀ i, n ≤ i → Epi (HomologicalComplex.homologyMap v i)) :
    (∀ i, n < i → IsIso (HomologicalComplex.homologyMap
        (((tensorRight R M).mapHomologicalComplex (ComplexShape.up ℤ)).map v) i)) ∧
      ∀ i, n ≤ i → Epi (HomologicalComplex.homologyMap
        (((tensorRight R M).mapHomologicalComplex (ComplexShape.up ℤ)).map v) i) := by
  have := isStrictlyLE_mappingCone R v b
  have hC := exactAt_tensorRight_of_isStrictlyLE.{d} R M (CochainComplex.mappingCone v) b
    (flatObjects_mappingCone_X R v hX hY) n (exactAt_mappingCone_of_approx v n hiso hepi)
  refine homologyMap_of_exactAt_mappingCone _ n fun i hi ↦ ?_
  rw [← exactAt_iff_of_quasiIsoAt
    (CochainComplex.mappingCone.mapHomologicalComplexIso v (tensorRight R M)).hom i]
  exact hC i hi

end Deformation.ComplexLift

end
