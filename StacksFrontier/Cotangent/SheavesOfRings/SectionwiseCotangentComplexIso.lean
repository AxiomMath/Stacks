module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseCotangentComplexSheafification
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# The cotangent complex of `A ⟶ B` is the sheafification of the sectionwise one

Let `A ⟶ B` be a homomorphism of sheaves of commutative rings on a site.
`StacksFrontier/Cotangent/SheavesOfRings/SectionwiseCotangentComplexSheafification.lean` assembles
the sectionwise cotangent complexes `L_{B(U)/A(U)}` into a complex of presheaves of `B`-modules
and identifies the sheafification of each of its terms with the corresponding term of `L_{B/A}`.
This file proves that those degreewise identifications commute with the differentials, hence
that **the sheafification of the complex of presheaves `U ↦ L_{B(U)/A(U)}` is `L_{B/A}`**, and
deduces **Tag 08SW**: the cohomology sheaf `H^i(L_{B/A})` is the sheaf associated to the presheaf
of abelian groups `U ↦ H^i(L_{B(U)/A(U)})`.

## Main definitions

* `CategoryTheory.Sheaf.sectionwiseUnitDegreeComparison`: the degreewise comparison, read on
  sections over an object of the site and precomposed with the sheafification unit.
* `CategoryTheory.Sheaf.sheafifiedSectionwiseComplex`: the sheafification of the complex of
  presheaves of `B`-modules `U ↦ L_{B(U)/A(U)}`.
* `CategoryTheory.Sheaf.presheafSections` and `CategoryTheory.Sheaf.presheafSectionsAb`:
  sections over an object of the site of a presheaf of `B`-modules, as a module over the
  sections of `B` and as an abelian group.

## Main results

* `CategoryTheory.Sheaf.sectionwiseUnitDegreeComparison_eq`: **the key identification.** The
  degreewise comparison, restricted along the sheafification unit, is the comparison of Tag 08SX
  `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` in cohomological degree `-n`.
* `CategoryTheory.Sheaf.sectionwiseDegreeComparison_comm`: consequently the degreewise
  comparisons commute with the differentials.
* `CategoryTheory.Sheaf.sectionwiseComplexIso`: **the isomorphism of complexes.**
* `CategoryTheory.Sheaf.sectionwiseComplexIso_hom_unit`: that isomorphism is the one induced by
  the canonical maps `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` of Remark 08SX, so the identification is the
  canonical one and not merely some isomorphism.
* `CategoryTheory.Sheaf.sectionwiseModuleComplexHomologyObjIso`: the presheaf of `B`-modules
  `H^i` of the complex of presheaves has, over an object `U` of the site, the sections
  `H^i(L_{B(U)/A(U)})`.
* `CategoryTheory.Sheaf.cohomologySheafIso`: the cohomology sheaf `H^i(L_{B/A})` is the
  sheafification of the presheaf of `B`-modules `U ↦ H^i(L_{B(U)/A(U)})`.
* `CategoryTheory.Sheaf.sectionwiseCohomologyPresheafIso`: the presheaf of abelian groups
  underlying that presheaf of `B`-modules is
  `CategoryTheory.Sheaf.sectionwiseCotangentCohomology`, the presheaf
  `U ↦ H^i(L_{B(U)/A(U)})` of
  `StacksFrontier/Cotangent/SheavesOfRings/SectionwiseCotangentComplex.lean`.
* `CategoryTheory.Sheaf.cohomologySheafification`: **Tag 08SW.**

## Implementation notes

The whole content of the compatibility with the differentials is
`sectionwiseUnitDegreeComparison_eq`: once the degreewise comparison is known to restrict, along
the sheafification unit, to the comparison of Tag 08SX, compatibility with the differentials is
*already proved*, because that comparison is a map of complexes
(`CategoryTheory.Sheaf.sectionsCotangentComplexComparison`, whose differentials are the
alternating sums of the face maps on both sides). Nothing here expands an alternating sum. Both
maps out of the sheafified term are determined by their restrictions along the unit and there by
their values on pure differentials — `CategoryTheory.Sheaf.sectionwiseDegreeComparison_unit_d`
and `CategoryTheory.Sheaf.cotangentTermComparison_differential` compute those, and they agree.

The two cohomology sections are all exactness. `PresheafOfModules.evaluation`,
`PresheafOfModules.sheafification` and the forgetful functor to abelian groups each preserve
finite limits and finite colimits, hence homology, and
`StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso` and
`Stacks.Homology.exactHomologyIso` turn that into the comparisons. Naturality in the object of
the site of the sectionwise identification is `Stacks.Homology.exactHomologyIso_inv_naturality`
applied to the restriction natural transformation `presheafSectionsAbMap`: naturality in the
*exact functor*, not in the complex. The last step is Mathlib's
`PresheafOfModules.sheafificationCompToSheaf`, the sheafification of presheaves of modules
commuting with forgetting the module structure. The instances for `presheafSections` are
restated with `inferInstanceAs` because its target is written in the algebraic spelling below.

A `B(U)`-module appears in this development in two spellings, as an object of
`ModuleCat (sectionsAlgebra J f U)` and as an object of
`ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj U)`; they are the same up to
unfolding instances, but a composite of morphisms crossing between them is not type-correct at the
`implicit` transparency level, which is what `rw` and `simp` check when they build a motive. So the
crossing is confined to `sectionwiseUnitDegreeComparison` and to the `rfl` lemma
`sectionwiseUnitDegreeComparison_apply`, and every step that would otherwise rewrite across the
crossing is written as an explicit `Eq.trans` of lemma applications, which elaborate at the default
transparency.

## References

* [Stacks Project, Tag 08SW](https://stacks.math.columbia.edu/tag/08SW)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

attribute [local instance] moduleOfSections

/-! ## The degreewise comparison on sections -/

/-- The degreewise comparison of
`StacksFrontier/Cotangent/SheavesOfRings/SectionwiseCotangentComplexSheafification.lean`, read on
sections over an object of the site and precomposed with the sheafification unit. -/
noncomputable def sectionwiseUnitDegreeComparison (n : ℕ) (U : Cᵒᵖ) :
    (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).X (-(n : ℤ)) ⟶
      (moduleSections J f U).obj ((cotangentComplex J f).X (-(n : ℤ))) :=
  (sectionwiseUnit J f (-(n : ℤ))).app U ≫
    (moduleSections J f U).map (sectionwiseDegreeComparison J f n)

/-- `sectionwiseUnitDegreeComparison` sends `x` to the degreewise comparison applied to the image
of `x` under the sheafification unit. -/
theorem sectionwiseUnitDegreeComparison_apply (n : ℕ) (U : Cᵒᵖ)
    (x : (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).X (-(n : ℤ))) :
    sectionwiseUnitDegreeComparison J f n U x =
      (sectionwiseDegreeComparison J f n).val.app U
        ((sectionwiseUnit J f (-(n : ℤ))).app U x) :=
  rfl

/-- **The degreewise comparison is the comparison of Tag 08SX on sections.** -/
theorem sectionwiseUnitDegreeComparison_eq (n : ℕ) (U : Cᵒᵖ) :
    sectionwiseUnitDegreeComparison J f n U =
      (sectionsCotangentComplexComparison J f U).f (-(n : ℤ)) := by
  refine sectionwiseCotangentModules_hom_ext J f n U _ _ fun p => ?_
  rw [sectionwiseUnitDegreeComparison_apply]
  refine (sectionwiseDegreeComparison_unit_d J f n U p).trans ?_
  rw [sectionsCotangentComplexComparison_f]
  dsimp only [sectionwiseDifferential]
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.hom_inv_apply,
    cotangentTermComparison_differential]
  rfl

/-- The degreewise comparison, applied to the image of `x` under the sheafification unit, is the
comparison of Tag 08SX applied to `x`. -/
private theorem sectionwiseDegreeComparison_unit_apply (n : ℕ) (U : Cᵒᵖ)
    (x : (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).X (-(n : ℤ))) :
    (sectionwiseDegreeComparison J f n).val.app U ((sectionwiseUnit J f (-(n : ℤ))).app U x) =
      (sectionsCotangentComplexComparison J f U).f (-(n : ℤ)) x :=
  (sectionwiseUnitDegreeComparison_apply J f n U x).symm.trans
    (ConcreteCategory.congr_hom (sectionwiseUnitDegreeComparison_eq J f n U) x)

/-! ## Compatibility with the differentials -/

/-- The sheafification unit intertwines the sectionwise differential with the differential of the
sheafified complex. -/
theorem sectionwiseUnit_sectionwiseModuleDifferential (i j : ℤ) (U : Cᵒᵖ)
    (x : (sectionwiseCotangentModules J f i).obj U) :
    ((moduleSheafification J (B := B)).map (sectionwiseModuleDifferential J f i j)).val.app U
        ((sectionwiseUnit J f i).app U x) =
      (sectionwiseUnit J f j).app U ((sectionwiseModuleDifferential J f i j).app U x) :=
  ConcreteCategory.congr_hom
    (congrArg (fun φ : sectionwiseCotangentModules J f i ⟶
        ((moduleSheafification J (B := B)).obj (sectionwiseCotangentModules J f j)).val =>
      φ.app U) (sectionwiseUnit_naturality J f (sectionwiseModuleDifferential J f i j))) x

/-- **The degreewise comparison commutes with the differentials**, on the image of the
sheafification unit. -/
theorem sectionwiseDegreeComparison_comm_apply (n : ℕ) (U : Cᵒᵖ)
    (x : (sectionwiseCotangentModules J f (-((n + 1 : ℕ) : ℤ))).obj U) :
    (sectionwiseDegreeComparison J f n).val.app U
        (((moduleSheafification J (B := B)).map
            (sectionwiseModuleDifferential J f (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)))).val.app U
          ((sectionwiseUnit J f (-((n + 1 : ℕ) : ℤ))).app U x)) =
      ((cotangentComplex J f).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))).val.app U
        ((sectionwiseDegreeComparison J f (n + 1)).val.app U
          ((sectionwiseUnit J f (-((n + 1 : ℕ) : ℤ))).app U x)) := by
  have h₁ : (sectionwiseDegreeComparison J f n).val.app U
        (((moduleSheafification J (B := B)).map
            (sectionwiseModuleDifferential J f (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)))).val.app U
          ((sectionwiseUnit J f (-((n + 1 : ℕ) : ℤ))).app U x)) =
      (sectionsCotangentComplexComparison J f U).f (-(n : ℤ))
        ((sectionwiseModuleDifferential J f (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))).app U x) :=
    (congrArg (fun z => (sectionwiseDegreeComparison J f n).val.app U z)
          (sectionwiseUnit_sectionwiseModuleDifferential J f _ _ U x)).trans
      (sectionwiseDegreeComparison_unit_apply J f n U _)
  have h₂ : ((cotangentComplex J f).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))).val.app U
        ((sectionwiseDegreeComparison J f (n + 1)).val.app U
          ((sectionwiseUnit J f (-((n + 1 : ℕ) : ℤ))).app U x)) =
      (moduleSections J f U).map ((cotangentComplex J f).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)))
        ((sectionsCotangentComplexComparison J f U).f (-((n + 1 : ℕ) : ℤ)) x) :=
    congrArg
      (fun z => (moduleSections J f U).map
        ((cotangentComplex J f).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))) z)
      (sectionwiseDegreeComparison_unit_apply J f (n + 1) U x)
  have h₃ : (sectionsCotangentComplexComparison J f U).f (-(n : ℤ))
        ((sectionwiseModuleDifferential J f (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))).app U x) =
      (moduleSections J f U).map ((cotangentComplex J f).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)))
        ((sectionsCotangentComplexComparison J f U).f (-((n + 1 : ℕ) : ℤ)) x) :=
    (ModuleCat.comp_apply _ _ x).symm.trans
      ((ConcreteCategory.congr_hom
          (((sectionsCotangentComplexComparison J f U).comm
            (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))).symm) x).trans
        (ModuleCat.comp_apply _ _ x))
  exact h₁.trans (h₃.trans h₂.symm)

/-- **The degreewise comparison commutes with the differentials.** -/
theorem sectionwiseDegreeComparison_comm (n : ℕ) :
    (moduleSheafification J (B := B)).map
          (sectionwiseModuleDifferential J f (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))) ≫
        sectionwiseDegreeComparison J f n =
      sectionwiseDegreeComparison J f (n + 1) ≫
        (cotangentComplex J f).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) := by
  apply (sheafifiedSectionwiseModulesHomEquiv J f (n + 1)
    ((cotangentComplex J f).X (-(n : ℤ)))).injective
  refine PresheafOfModulesOfCommRing.Derivation.ext (funext fun U => AddMonoidHom.ext fun p => ?_)
  rw [sheafifiedSectionwiseModulesHomEquiv_unit_d, sheafifiedSectionwiseModulesHomEquiv_unit_d]
  exact sectionwiseDegreeComparison_comm_apply J f n U (sectionwiseDifferential J f (n + 1) U p)

/-! ## The isomorphism of complexes -/

/-- Sheafification of presheaves of `B`-modules is an additive functor. -/
instance moduleSheafification_additive : (moduleSheafification J (B := B)).Additive :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).left_adjoint_additive

/-- **The sheafification of the sectionwise cotangent complex**, as a complex of sheaves of
`B`-modules. -/
noncomputable def sheafifiedSectionwiseComplex : CochainComplex (targetModules J B) ℤ :=
  ((moduleSheafification J (B := B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (sectionwiseModuleComplex J f)

/-- **The cotangent complex of `A ⟶ B` is the sheafification of the sectionwise cotangent
complex.** -/
noncomputable def sectionwiseComplexIso :
    sheafifiedSectionwiseComplex J f ≅ cotangentComplex J f :=
  HomologicalComplex.Hom.isoOfComponents (sectionwiseComplexDegreeIso J f) (by
    intro i j hij
    change i + 1 = j at hij
    rcases le_or_gt 0 i with hi | hi
    · exact (cotangentComplex_isZero_pos J f j (by omega)).eq_of_tgt _ _
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = -((m + 1 : ℕ) : ℤ) := ⟨(-i - 1).toNat, by omega⟩
      obtain rfl : j = -(m : ℤ) := by omega
      rw [sectionwiseComplexDegreeIso_neg, sectionwiseComplexDegreeIso_neg,
        sectionwiseDegreeComparisonIso_hom, sectionwiseDegreeComparisonIso_hom]
      exact (sectionwiseDegreeComparison_comm J f m).symm)

/-- **The isomorphism of complexes is the canonical comparison.** Over every object `U` of the
site, the component of `sectionwiseComplexIso` in cohomological degree `-n`, read on the image of
the sheafification unit, is the canonical map `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` of Remark 08SX. So the
identification of `L_{B/A}` with the sheafification of `U ↦ L_{B(U)/A(U)}` is the one induced by
those canonical maps. -/
theorem sectionwiseComplexIso_hom_unit (n : ℕ) (U : Cᵒᵖ)
    (x : (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).X (-(n : ℤ))) :
    ((sectionwiseComplexIso J f).hom.f (-(n : ℤ))).val.app U
        ((sectionwiseUnit J f (-(n : ℤ))).app U x) =
      (sectionsCotangentComplexComparison J f U).f (-(n : ℤ)) x := by
  have hcomp : (sectionwiseComplexIso J f).hom.f (-(n : ℤ)) =
      sectionwiseDegreeComparison J f n := by
    show (sectionwiseComplexDegreeIso J f (-(n : ℤ))).hom = _
    rw [sectionwiseComplexDegreeIso_neg, sectionwiseDegreeComparisonIso_hom]
  rw [hcomp]
  exact sectionwiseDegreeComparison_unit_apply J f n U x

/-! ## The cohomology sheaves -/

/-- Sections over `U` of a presheaf of `B`-modules, as a module over the sections `B(U)`. -/
noncomputable abbrev presheafSections (U : Cᵒᵖ) :
    PresheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj ⥤
      ModuleCat.{max u v w} (sectionsAlgebra J f U) :=
  PresheafOfModules.evaluation _ U

/-- Taking sections over `U` is an additive functor. -/
instance presheafSections_additive (U : Cᵒᵖ) : (presheafSections J f U).Additive :=
  inferInstanceAs ((PresheafOfModules.evaluation
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj U).Additive)

/-- Taking sections over `U` preserves finite limits. -/
noncomputable instance presheafSections_preservesFiniteLimits (U : Cᵒᵖ) :
    Limits.PreservesFiniteLimits (presheafSections J f U) :=
  inferInstanceAs (Limits.PreservesFiniteLimits (PresheafOfModules.evaluation
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj U))

/-- Taking sections over `U` preserves finite colimits. -/
noncomputable instance presheafSections_preservesFiniteColimits (U : Cᵒᵖ) :
    Limits.PreservesFiniteColimits (presheafSections J f U) :=
  inferInstanceAs (Limits.PreservesFiniteColimits (PresheafOfModules.evaluation
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj U))

/-- The complex of presheaves of `B`-modules, evaluated over an object of the site, is the
cotangent complex of the ring map on sections. -/
theorem presheafSections_mapHomologicalComplex (U : Cᵒᵖ) :
    ((presheafSections J f U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sectionwiseModuleComplex J f) =
      CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U) :=
  rfl

/-- **The presheaf of `B`-modules `H^i` of the sectionwise cotangent complex has, over an object
`U` of the site, the sections `H^i(L_{B(U)/A(U)})`**, the evaluation of a presheaf of modules
being exact. -/
noncomputable def sectionwiseModuleComplexHomologyObjIso (i : ℤ) (U : Cᵒᵖ) :
    ((sectionwiseModuleComplex J f).homology i).obj U ≅
      (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).homology i :=
  ((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
    (presheafSections J f U) (ComplexShape.up ℤ) i).app (sectionwiseModuleComplex J f)).symm

/-- **The cohomology sheaf `H^i(L_{B/A})` is the sheafification of the presheaf of `B`-modules
`U ↦ H^i(L_{B(U)/A(U)})`.** -/
noncomputable def cohomologySheafIso (i : ℤ) :
    (moduleSheafification J (B := B)).obj ((sectionwiseModuleComplex J f).homology i) ≅
      (cotangentComplex J f).homology i :=
  ((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
      (moduleSheafification J (B := B)) (ComplexShape.up ℤ) i).app
        (sectionwiseModuleComplex J f)).symm ≪≫
    (HomologicalComplex.homologyFunctor (targetModules J B) (ComplexShape.up ℤ) i).mapIso
      (sectionwiseComplexIso J f)


/-! ## The cohomology sheaf of abelian groups -/

/-- Sections over `U` of a presheaf of `B`-modules, as an abelian group. -/
noncomputable abbrev presheafSectionsAb (U : Cᵒᵖ) :
    PresheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj ⥤
      AddCommGrpCat.{max u v w} :=
  presheafSections J f U ⋙
    forget₂ (ModuleCat.{max u v w} (sectionsAlgebra J f U)) AddCommGrpCat.{max u v w}

/-- The complex of presheaves of `B`-modules, evaluated over an object of the site and read on
underlying abelian groups, is the complex of abelian groups `L_{B(U)/A(U)}`. -/
theorem presheafSectionsAb_mapHomologicalComplex (U : Cᵒᵖ) :
    ((presheafSectionsAb J f U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sectionwiseModuleComplex J f) = sectionsCotangentComplexAb J f U :=
  rfl

/-- Restriction along `g`, as a natural transformation of the sections functors. -/
noncomputable def presheafSectionsAbMap {U V : Cᵒᵖ} (g : U ⟶ V) :
    presheafSectionsAb J f U ⟶ presheafSectionsAb J f V where
  app M := AddCommGrpCat.ofHom (M.map g).hom.toAddMonoidHom
  naturality M N h := by
    apply AddCommGrpCat.hom_ext
    refine AddMonoidHom.ext fun x => ?_
    exact (ConcreteCategory.congr_hom (h.naturality g) x).symm

/-- **The presheaf of abelian groups underlying `H^i` of the complex of presheaves of
`B`-modules is the sectionwise cotangent cohomology presheaf `U ↦ H^i(L_{B(U)/A(U)})`**, with
its restriction maps. -/
noncomputable def sectionwiseCohomologyPresheafIso (i : ℤ) :
    (PresheafOfModules.toPresheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj).obj
        ((sectionwiseModuleComplex J f).homology i) ≅
      sectionwiseCotangentCohomology J f i :=
  NatIso.ofComponents
    (fun U => ((Stacks.Homology.exactHomologyIso (presheafSectionsAb J f U) i).app
      (sectionwiseModuleComplex J f)).symm)
    (fun {_ _} g => congr_app
      (Stacks.Homology.exactHomologyIso_inv_naturality (presheafSectionsAbMap J f g) i)
      (sectionwiseModuleComplex J f))

/-- For a homomorphism `A ⟶ B` of sheaves of commutative rings on a site, the cohomology sheaf
`H^i(L_{B/A})` of the cotangent complex is the sheaf associated to the presheaf
`U ↦ H^i(L_{B(U)/A(U)})` formed from the cotangent complexes of the ring maps on sections.

The presheaf is `CategoryTheory.Sheaf.sectionwiseCotangentCohomology`, whose sections over `U`
are `H^i(L_{B(U)/A(U)})` by `CategoryTheory.Sheaf.sectionwiseCotangentCohomology_obj` and whose
restriction maps are those of the restriction squares; the sheafification is taken in abelian
sheaves, and `CategoryTheory.Sheaf.cohomologySheafIso` is the same identification before the
module structure over `B` is forgotten. The identification is the canonical one: it comes from
`CategoryTheory.Sheaf.sectionwiseComplexIso`, which by
`CategoryTheory.Sheaf.sectionwiseComplexIso_hom_unit` is induced by the canonical comparison maps
`L_{B(U)/A(U)} ⟶ L_{B/A}(U)` of Remark 08SX. -/
@[stacks 08SW "the whole lemma: the sheaf associated to the presheaf U ↦ H^i(L_{B(U)/A(U)}) is \
H^i(L_{B/A}), by the canonical identification — `sectionwiseComplexIso`, which \
`sectionwiseComplexIso_hom_unit` shows is induced by the comparison maps L_{B(U)/A(U)} ⟶ \
L_{B/A}(U) of Remark 08SX. CARRIES NOTHING beyond the ambient variables: arbitrary site, \
arbitrary Grothendieck topology, arbitrary homomorphism of sheaves of commutative rings, every \
i, with the section universe a free parameter. The module-level form, before the structure over \
B is forgotten, is `cohomologySheafIso`"]
noncomputable def cohomologySheafification (i : ℤ) :
    (presheafToSheaf J AddCommGrpCat.{max u v w}).obj (sectionwiseCotangentCohomology J f i) ≅
      (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B)).obj
        ((cotangentComplex J f).homology i) :=
  (presheafToSheaf J AddCommGrpCat.{max u v w}).mapIso
      (sectionwiseCohomologyPresheafIso J f i).symm ≪≫
    ((PresheafOfModules.sheafificationCompToSheaf
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).app
        ((sectionwiseModuleComplex J f).homology i)).symm ≪≫
    (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B)).mapIso
      (cohomologySheafIso J f i)

end CategoryTheory.Sheaf

end

