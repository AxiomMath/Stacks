module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseCotangentSheafification

/-!
# Towards: the cotangent complex of `A` to `B` is the sheafification of the sectionwise one

Let `A` to `B` be a homomorphism of sheaves of commutative rings on a site.
`StacksFrontier/Cotangent/SheavesOfRings/SectionwiseCotangentModules.lean` assembles the sectionwise
cotangent complexes `L_{B(U)/A(U)}` into presheaves of `B`-modules, and
`StacksFrontier/Cotangent/SheavesOfRings/SectionwiseCotangentSheafification.lean` identifies the
sheafification of each term with the corresponding term of `L_{B/A}`. This file assembles those
terms into a complex of presheaves of `B`-modules and records the degreewise identification of
its sheafification with `L_{B/A}`, in every cohomological degree.

## Main definitions

* `CategoryTheory.Sheaf.sectionwiseModuleComplex`: the complex of presheaves of `B`-modules
  `U` to `L_{B(U)/A(U)}`, whose differentials are the sectionwise differentials.
* `CategoryTheory.Sheaf.sectionwiseUnit`: the unit of the sheafification of a term.
* `CategoryTheory.Sheaf.sectionwiseDegreeComparison` and
  `CategoryTheory.Sheaf.sectionwiseDegreeComparisonIso`: the degreewise comparison of
  `StacksFrontier/Cotangent/SheavesOfRings/SectionwiseCotangentSheafification.lean`, read in
  cohomological degree `-n` of the cotangent complex.
* `CategoryTheory.Sheaf.sectionwiseComplexDegreeIso`: the degreewise identification in every
  cohomological degree, the positive degrees being handled by the vanishing of both complexes
  there.

## Main results

* `CategoryTheory.Sheaf.sectionwiseDegreeComparison_unit_d`: the comparison carries the image of
  a pure differential under the sheafification unit to the universal differential of its image
  in the standard resolution of `A` to `B`. This is what pins the comparison down, and it is the
  input from which compatibility with the differentials is to be derived.
* `CategoryTheory.Sheaf.universalSheafDerivation_face`: a face map of the simplicial sheaf of
  base-changed differentials carries a universal differential to a universal differential.
* `CategoryTheory.Sheaf.sectionwiseCotangentModules_isZero_pos`: the sectionwise cotangent
  complex vanishes in positive cohomological degrees.

## Implementation notes

A morphism out of the sheafification of the degree-`-n` term is determined by its restriction
along the sheafification unit, and there by its values on pure differentials: this is the
injectivity of `CategoryTheory.Sheaf.sheafifiedSectionwiseModulesHomEquiv`, and
`sectionwiseDegreeComparison_unit_d` computes those values.

In positive cohomological degrees both complexes vanish, so the degreewise isomorphism is the
unique map between two zero objects; the sheafification of a zero presheaf of modules is zero
because sheafification is additive.

### What comes next

The compatibility of the degreewise comparisons with the differentials, hence the isomorphism of
complexes and Tag 08SW itself, is
`StacksFrontier/Cotangent/SheavesOfRings/SectionwiseCotangentComplexIso.lean`. Its input from here
is `sectionwiseDegreeComparison_unit_d`: a morphism out of a sheafified term is determined by its
values on the images of the pure differentials, so that computation pins the comparison down, and
identifying it with the canonical map of Remark 08SX makes compatibility with the differentials
immediate, that map being a map of complexes already.

## References

* [Stacks Project, Tag 08SW](https://stacks.math.columbia.edu/tag/08SW)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-! ## The complex of presheaves of modules -/

/-- The differential of the sectionwise cotangent complex, as a morphism of presheaves of
`B`-modules. -/
noncomputable def sectionwiseModuleDifferential (i j : ℤ) :
    sectionwiseCotangentModules J f i ⟶ sectionwiseCotangentModules J f j where
  app U := (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
    (sectionsAlgebra J f U)).d i j
  naturality {_U _V} g :=
    (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J f g)).complexMap.comm i j

/-- **The complex of presheaves of `B`-modules `U ↦ L_{B(U)/A(U)}`.** -/
noncomputable def sectionwiseModuleComplex :
    CochainComplex (PresheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj) ℤ where
  X i := sectionwiseCotangentModules J f i
  d i j := sectionwiseModuleDifferential J f i j
  shape i j hij := by
    refine PresheafOfModules.hom_ext fun U => ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact ConcreteCategory.congr_hom
      ((CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).shape i j hij) x
  d_comp_d' i j k _ _ := by
    refine PresheafOfModules.hom_ext fun U => ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact ConcreteCategory.congr_hom
      ((CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).d_comp_d i j k) x

/-! ## The differential of the cotangent complex of `A ⟶ B` on pure differentials -/

/-- The universal derivation of `Ω_{P_n/A} ⊗_{P_n} B`, read in cohomological degree `-n` of the
cotangent complex. -/
noncomputable def sheafDifferential (n : ℕ) (U : Cᵒᵖ)
    (p : (resolutionTerm J f (op ⦋n⦌)).obj.obj U) :
    ((cotangentComplex J f).X (-(n : ℤ))).val.obj U :=
  (cotangentComplex_degreeIso J f n).inv.val.app U
    ((universalSheafDerivation J f (op ⦋n⦌)).d p)

/-- A face map of the simplicial sheaf of base-changed differentials carries the universal
differential of a section to the universal differential of its image. -/
theorem universalSheafDerivation_face (n : ℕ) (j : Fin (n + 2)) (U : Cᵒᵖ)
    (p : (resolutionTerm J f (op ⦋n + 1⦌)).obj.obj U) :
    ((cotangentSimplicialModule J f).object.δ j).val.app U
        ((universalSheafDerivation J f (op ⦋n + 1⦌)).d p) =
      (universalSheafDerivation J f (op ⦋n⦌)).d
        (((standardResolution J f).left.δ j).right.hom.app U p) :=
  universalSheafDerivation_naturality J f (SimplexCategory.δ j).op U p

/-! ## The degreewise comparison commutes with the differentials -/

/-- The unit of the sheafification of the degree-`i` term of the sectionwise cotangent
complex. -/
noncomputable def sectionwiseUnit (i : ℤ) :
    sectionwiseCotangentModules J f i ⟶
      ((moduleSheafification J (B := B)).obj (sectionwiseCotangentModules J f i)).val :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).unit.app
      (sectionwiseCotangentModules J f i)

/-- The sheafification unit `sectionwiseUnit` is natural with respect to maps between terms of the
sectionwise cotangent complex. -/
theorem sectionwiseUnit_naturality {i j : ℤ}
    (g : sectionwiseCotangentModules J f i ⟶ sectionwiseCotangentModules J f j) :
    sectionwiseUnit J f i ≫ ((moduleSheafification J (B := B)).map g).val =
      g ≫ sectionwiseUnit J f j :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).unit.naturality g).symm

/-- The derivation corresponding to a map `k` out of the sheafification sends a section `p` to the
image under `k` of the sheafification unit applied to the pure differential of `p`. -/
theorem sheafifiedSectionwiseModulesHomEquiv_unit_d (n : ℕ) (M : targetModules J B)
    (k : sheafifiedSectionwiseModules J f n ⟶ M) (U : Cᵒᵖ)
    (p : (sectionsResolutionPresheaf J f (op ⦋n⦌)).obj U) :
    (sheafifiedSectionwiseModulesHomEquiv J f n M k).d p =
      k.val.app U ((sectionwiseUnit J f (-(n : ℤ))).app U
        (sectionwiseDifferential J f n U p)) :=
  congrArg (fun φ => (φ.app U).hom (sectionwiseDifferential J f n U p))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).homEquiv_unit (f := k))

/-- The comparison of the degree-`-n` terms, as a map to the cotangent complex. -/
noncomputable def sectionwiseDegreeComparison (n : ℕ) :
    sheafifiedSectionwiseModules J f n ⟶ (cotangentComplex J f).X (-(n : ℤ)) :=
  cotangentTermSheafifiedComparison J f n ≫ (cotangentComplex_degreeIso J f n).inv

/-- The degreewise comparison is the isomorphism of
`CategoryTheory.Sheaf.cotangentTermSheafifiedIso` read in cohomological degree `-n`. -/
noncomputable def sectionwiseDegreeComparisonIso (n : ℕ) :
    sheafifiedSectionwiseModules J f n ≅ (cotangentComplex J f).X (-(n : ℤ)) :=
  cotangentTermSheafifiedIso J f n ≪≫ (cotangentComplex_degreeIso J f n).symm

/-- The forward map of `sectionwiseDegreeComparisonIso` is `sectionwiseDegreeComparison`. -/
theorem sectionwiseDegreeComparisonIso_hom (n : ℕ) :
    (sectionwiseDegreeComparisonIso J f n).hom = sectionwiseDegreeComparison J f n :=
  rfl

/-- The comparison carries the image of a pure differential under the sheafification unit to the
universal differential of its image in the standard resolution of `A ⟶ B`. -/
theorem sectionwiseDegreeComparison_unit_d (n : ℕ) (U : Cᵒᵖ)
    (p : (sectionsResolutionPresheaf J f (op ⦋n⦌)).obj U) :
    (sectionwiseDegreeComparison J f n).val.app U
        ((sectionwiseUnit J f (-(n : ℤ))).app U (sectionwiseDifferential J f n U p)) =
      sheafDifferential J f n U
        (((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom p) := by
  have key : sheafifiedSectionwiseModulesHomEquiv J f n _
        (cotangentTermSheafifiedComparison J f n) =
      restrictResolutionDerivation J f n _ (universalSheafDerivation J f (op ⦋n⦌)) := by
    dsimp only [cotangentTermSheafifiedComparison, cotangentTermSheafifiedHomEquiv,
      Equiv.trans_apply]
    rw [Equiv.apply_symm_apply]
    rfl
  have h := (sheafifiedSectionwiseModulesHomEquiv_unit_d J f n _
    (cotangentTermSheafifiedComparison J f n) U p).symm
  exact congrArg (fun z => (cotangentComplex_degreeIso J f n).inv.val.app U z)
    (h.trans (congrArg (fun D => D.d p) key))

/-! ## The isomorphism of complexes -/

/-- In positive cohomological degrees the sectionwise cotangent complex vanishes. -/
theorem sectionwiseCotangentModules_isZero_pos (i : ℤ) (hi : 0 < i) :
    IsZero (sectionwiseCotangentModules J f i) := by
  rw [IsZero.iff_id_eq_zero]
  refine PresheafOfModules.hom_ext fun U => ?_
  exact (CommAlgCat.cotangentComplex_isZero_pos.{max u v w, max u v w} (A.obj.obj U)
    (sectionsAlgebra J f U) i hi).eq_of_src _ _

/-- The degreewise identification of the sheafification of the sectionwise cotangent complex
with the cotangent complex of `A ⟶ B`. -/
noncomputable def sectionwiseComplexDegreeIso (i : ℤ) :
    (moduleSheafification J (B := B)).obj (sectionwiseCotangentModules J f i) ≅
      (cotangentComplex J f).X i :=
  if hi : 0 < i then
    ((moduleSheafification J (B := B)).map_isZero
      (sectionwiseCotangentModules_isZero_pos J f i hi)).iso
      (cotangentComplex_isZero_pos J f i hi)
  else
    eqToIso (congrArg (fun k => (moduleSheafification J (B := B)).obj
        (sectionwiseCotangentModules J f k))
      (Int.eq_neg_natAbs_of_nonpos (le_of_not_gt hi))) ≪≫
      sectionwiseDegreeComparisonIso J f i.natAbs ≪≫
        eqToIso (congrArg (cotangentComplex J f).X
          (Int.eq_neg_natAbs_of_nonpos (le_of_not_gt hi)).symm)

/-- In cohomological degree `-n` the identification `sectionwiseComplexDegreeIso` is
`sectionwiseDegreeComparisonIso`. -/
theorem sectionwiseComplexDegreeIso_neg (n : ℕ) :
    sectionwiseComplexDegreeIso J f (-(n : ℤ)) = sectionwiseDegreeComparisonIso J f n := by
  cases n with
  | zero => simp [sectionwiseComplexDegreeIso]
  | succ n =>
    dsimp only [sectionwiseComplexDegreeIso]
    rw [dite_eq_right (show ¬0 < -((n + 1 : ℕ) : ℤ) by omega)]
    change Iso.refl _ ≪≫ sectionwiseDegreeComparisonIso J f (n + 1) ≪≫ Iso.refl _ = _
    simp only [Iso.refl_trans, Iso.trans_refl]

end CategoryTheory.Sheaf

end
