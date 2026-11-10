module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplexGlobalNaturality
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyPi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The global computation of derived-category morphisms, at the class of a cocycle

Let `(C, O)` be a ringed site, let `L` be a complex of `O`-modules and let `I` be a K-injective
complex of `O`-modules.  Stacks 0A94 identifies the degree-zero cohomology of the global
sections of the internal Hom complex `SheafHom(L, I)` with `Hom_{D(O)}(L, I)`; that
identification is `AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom`.

This file **evaluates it at a named element**.  A morphism of complexes `f : L ⟶ I` is a
degree-zero cocycle of `SheafHom(L, I)`, hence determines a degree-zero cohomology class of the
global section complex, and the identification sends that class to the morphism `Q(f)` of the
derived category.

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_homologyπ`: the
  identification of Stacks 0A94 sends the class of **any** degree-zero cycle of the global
  section complex whose associated cochain is `f` to `DerivedCategory.Q.map f`.
* `AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_globalHomologyClass`:
  the same statement for the cycle `AlgebraicGeometry.RingedSite.globalHomCocycle` canonically
  attached to `f`.

## Main definitions

* `AlgebraicGeometry.RingedSite.globalHomSection`: the global section of the degree-zero term of
  `SheafHom(L, I)` whose associated cochain is `f`.
* `AlgebraicGeometry.RingedSite.globalHomCocycle` and
  `AlgebraicGeometry.RingedSite.globalHomologyClass`: that section read as a cycle of the global
  section complex, and its cohomology class.

## Implementation notes

The two general ingredients are isolated first, for an arbitrary abelian category: the
degree-zero cohomology class of `Cocycle.ofHom f` is carried to the image of `f` in the homotopy
category (`homAddEquiv_mk_ofHom_comp_shiftFunctorZero`, where the degree-zero shift of the
target is normalised away exactly as
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomotopyCategoryHom` normalises it), and the
identification of homotopy-category with derived-category morphisms into a K-injective complex
carries the image of `f` in the homotopy category to `Q(f)`
(`AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv_quotient_map`).

What remains is to run `AlgebraicGeometry.RingedSite.globalHomologyClassEquiv` on the class of a
cycle.  That equivalence is the global description of the internal Hom complex read on homology
followed by the universe lift of Stacks 0A8Z, so the computation is the compatibility of
`HomologicalComplex.homologyπ` with `HomologicalComplex.homologyMap`, then its companion for
`CategoryTheory.ShortComplex.mapHomologyIso` — which is
`CategoryTheory.ShortComplex.homologyπ_comp_mapHomologyIso_hom` — and finally the description of
`CochainComplex.HomComplex.homologyAddEquiv` through the left homology datum
`CochainComplex.HomComplex.leftHomologyData`.  At each step the cycle is identified by its image
under `iCycles`, which is a monomorphism.

The statements are given on the diagonal universes `RingedSite.{u, u, u}`, as
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomotopyCategoryHom` and the naturality of
Stacks 0A94 are.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CochainComplex.HomComplex

universe u v

section General

variable {C : Type v} [Category.{u} C] [Preadditive C]

/-- The degree-zero cohomology class of the cocycle attached to a morphism of complexes
`f : K ⟶ I`, read as a morphism of the homotopy category with the degree-zero shift of the
target normalised away, is the image of `f` in the homotopy category. -/
@[sga "2 V 1.1" "Degree-zero clause"]
theorem homAddEquiv_mk_ofHom_comp_shiftFunctorZero {K I : CochainComplex C ℤ} (f : K ⟶ I) :
    CohomologyClass.homAddEquiv (CohomologyClass.mk (Cocycle.ofHom f)) ≫
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app I) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f := by
  rw [CohomologyClass.homAddEquiv_apply, CohomologyClass.toHom_mk, ← Functor.map_comp]
  congr 1
  ext p
  simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf, Cochain.rightShift_v,
    CochainComplex.shiftFunctorZero_hom_app_f]

/-- **The cohomology of a Hom complex, read through a universe lift, at the class of a
cocycle.** If a degree-zero cycle `z` of a complex `G` of abelian groups has, under an
isomorphism of `G` with the universe lift of the Hom complex of `K` and `M`, the cochain
`Cochain.ofHom f` as its image, then the class of `z` is carried to the cohomology class of the
cocycle `Cocycle.ofHom f`.

This is the computation that `AlgebraicGeometry.RingedSite.globalHomologyClassEquiv` needs, with
the ringed site removed: the compatibility of `HomologicalComplex.homologyπ` with
`HomologicalComplex.homologyMap` and with `CategoryTheory.ShortComplex.mapHomologyIso`, followed
by the description of `CochainComplex.HomComplex.homologyAddEquiv` through
`CochainComplex.HomComplex.leftHomologyData`. -/
theorem homologyAddEquiv_mapHomologyIso_homologyπ {K M : CochainComplex C ℤ}
    (G : CochainComplex AddCommGrpCat.{u} ℤ)
    (φ : G ≅ (AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (K.HomComplex M))
    (f : K ⟶ M) (z : G.cycles 0)
    (hz : φ.hom.f 0 (G.iCycles 0 z) = ULift.up (Cochain.ofHom f)) :
    homologyAddEquiv K M 0
        (AddEquiv.ulift ((((K.HomComplex M).sc 0).mapHomologyIso
          AddCommGrpCat.uliftFunctor.{u}).hom
            (HomologicalComplex.homologyMap φ.hom 0 (G.homologyπ 0 z)))) =
      CohomologyClass.mk (Cocycle.ofHom f) := by
  obtain ⟨w, hw⟩ : ∃ w, (((K.HomComplex M).sc 0).mapCyclesIso
      AddCommGrpCat.uliftFunctor.{u}).hom (HomologicalComplex.cyclesMap φ.hom 0 z) =
      ULift.up w := ⟨_, rfl⟩
  have h1 : HomologicalComplex.homologyMap φ.hom 0 (G.homologyπ 0 z) =
      ((AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.HomComplex M)).homologyπ 0 (HomologicalComplex.cyclesMap φ.hom 0 z) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ.hom 0) z
  have h2 : (((K.HomComplex M).sc 0).mapHomologyIso AddCommGrpCat.uliftFunctor.{u}).hom
        (((AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (K.HomComplex M)).homologyπ 0 (HomologicalComplex.cyclesMap φ.hom 0 z)) =
      ULift.up (((K.HomComplex M).sc 0).homologyπ w) :=
    (ConcreteCategory.congr_hom
        (ShortComplex.homologyπ_comp_mapHomologyIso_hom ((K.HomComplex M).sc 0)
          AddCommGrpCat.uliftFunctor.{u}) (HomologicalComplex.cyclesMap φ.hom 0 z)).trans
      (congrArg (ConcreteCategory.hom (AddCommGrpCat.uliftFunctor.{u}.map
        ((K.HomComplex M).sc 0).homologyπ)) hw)
  have h3 : ULift.up (((K.HomComplex M).sc 0).iCycles w) =
      ((AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.HomComplex M)).iCycles 0 (HomologicalComplex.cyclesMap φ.hom 0 z) :=
    (congrArg (ConcreteCategory.hom (AddCommGrpCat.uliftFunctor.{u}.map
          ((K.HomComplex M).sc 0).iCycles)) hw).symm.trans
      (ConcreteCategory.congr_hom
        (ShortComplex.mapCyclesIso_hom_iCycles ((K.HomComplex M).sc 0)
          AddCommGrpCat.uliftFunctor.{u}) (HomologicalComplex.cyclesMap φ.hom 0 z))
  have h4 : ((AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.HomComplex M)).iCycles 0 (HomologicalComplex.cyclesMap φ.hom 0 z) =
      φ.hom.f 0 (G.iCycles 0 z) :=
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ.hom 0) z
  have hi : ((K.HomComplex M).sc 0).iCycles w = Cochain.ofHom f :=
    congrArg ULift.down (h3.trans (h4.trans hz))
  have h5 : homologyAddEquiv K M 0 (((K.HomComplex M).sc 0).homologyπ w) =
      CohomologyClass.mk ((leftHomologyData K M 0).cyclesIso.hom w) :=
    ConcreteCategory.congr_hom
      (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom ((K.HomComplex M).sc 0)
        (leftHomologyData K M 0)) w
  have h6 : ((leftHomologyData K M 0).cyclesIso.hom w).1 = Cochain.ofHom f :=
    (ConcreteCategory.congr_hom (leftHomologyData K M 0).cyclesIso_hom_comp_i w).trans hi
  rw [h1, h2]
  exact h5.trans (congrArg CohomologyClass.mk (Subtype.ext h6))

end General

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

/-- The identification of homotopy-category with derived-category morphisms into a K-injective
complex sends the image of a morphism of complexes in the homotopy category to its image in the
derived category. -/
theorem homotopyHomDerivedCategoryEquiv_quotient_map {C : Type v} [Category.{u} C] [Abelian C]
    [HasDerivedCategory C] {K I : CochainComplex C ℤ} [I.IsKInjective] (f : K ⟶ I) :
    homotopyHomDerivedCategoryEquiv K I
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  rw [homotopyHomDerivedCategoryEquiv_apply]
  simp only [Iso.app_inv, Iso.app_hom, Category.assoc,
    DerivedCategory.quotientCompQhIso_hom_naturality, Iso.inv_hom_id_app_assoc]

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The global section of the degree-zero term of the internal Hom complex `SheafHom(L, I)`
whose associated cochain is the morphism of complexes `f`. -/
noncomputable def globalHomSection (f : L ⟶ I) :
    (globalSectionsComplex X (sheafHomComplex X L I).obj).X 0 :=
  (sheafHomComplex X L I).globalSectionsIso.inv.f 0 (ULift.up (Cochain.ofHom f))

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The global description of the internal Hom complex carries `globalHomSection X L I f` to the
cochain `Cochain.ofHom f`. -/
theorem globalSectionsIso_globalHomSection (f : L ⟶ I) :
    (sheafHomComplex X L I).globalSectionsIso.hom.f 0 (globalHomSection X L I f) =
      ULift.up (Cochain.ofHom f) :=
  ConcreteCategory.congr_hom
    (congrArg (fun ψ => HomologicalComplex.Hom.f ψ 0)
      (sheafHomComplex X L I).globalSectionsIso.inv_hom_id)
    (ULift.up (Cochain.ofHom f))

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The cochain attached to `globalHomSection X L I f` is `f`.** Together with
`AlgebraicGeometry.RingedSite.sheafHomComplex_globalSectionsIso_v_app`, which reads the cochain
attached to a global section off its sections over each object of the site, this says that
`globalHomSection X L I f` really is the global section of `SheafHom(L, I)` given by `f`. -/
theorem globalHomSection_v (f : L ⟶ I) (p : ℤ) :
    ((sheafHomComplex X L I).globalSectionsIso.hom.f 0
        (globalHomSection X L I f)).down.v p p (add_zero p) = f.f p := by
  rw [globalSectionsIso_globalHomSection]
  exact Cochain.ofHom_v f p

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `globalHomSection X L I f` is a cocycle: the cochain attached to it is `Cochain.ofHom f`,
whose differential vanishes. -/
theorem d_globalHomSection (f : L ⟶ I) :
    (globalSectionsComplex X (sheafHomComplex X L I).obj).d 0 ((ComplexShape.up ℤ).next 0)
      (globalHomSection X L I f) = 0 := by
  have hcomm : (globalSectionsComplex X (sheafHomComplex X L I).obj).d 0
        ((ComplexShape.up ℤ).next 0) (globalHomSection X L I f) =
      (sheafHomComplex X L I).globalSectionsIso.inv.f ((ComplexShape.up ℤ).next 0)
        (((AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (L.HomComplex I)).d 0 ((ComplexShape.up ℤ).next 0) (ULift.up (Cochain.ofHom f))) :=
    ConcreteCategory.congr_hom
      ((sheafHomComplex X L I).globalSectionsIso.inv.comm 0 ((ComplexShape.up ℤ).next 0))
      (ULift.up (Cochain.ofHom f))
  have hδ : ((AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (L.HomComplex I)).d 0 ((ComplexShape.up ℤ).next 0) (ULift.up (Cochain.ofHom f)) = 0 :=
    congrArg ULift.up (δ_ofHom f)
  rw [hcomm, hδ, map_zero]

/-- The degree-zero cycle of the global section complex of `SheafHom(L, I)` attached to a
morphism of complexes `f : L ⟶ I`. -/
noncomputable def globalHomCocycle (f : L ⟶ I) :
    (globalSectionsComplex X (sheafHomComplex X L I).obj).cycles 0 :=
  ((globalSectionsComplex X (sheafHomComplex X L I).obj).sc 0).abCyclesIso.inv
    ⟨globalHomSection X L I f, d_globalHomSection X L I f⟩

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `globalHomCocycle X L I f` is `globalHomSection X L I f`, read as a cycle. -/
theorem iCycles_globalHomCocycle (f : L ⟶ I) :
    (globalSectionsComplex X (sheafHomComplex X L I).obj).iCycles 0
        (globalHomCocycle X L I f) =
      globalHomSection X L I f :=
  ((globalSectionsComplex X (sheafHomComplex X L I).obj).sc 0).abCyclesIso_inv_apply_iCycles
    ⟨globalHomSection X L I f, d_globalHomSection X L I f⟩

/-- The degree-zero cohomology class of the global section complex of `SheafHom(L, I)` attached
to a morphism of complexes `f : L ⟶ I`. -/
noncomputable def globalHomologyClass (f : L ⟶ I) :
    (globalSectionsComplex X (sheafHomComplex X L I).obj).homology 0 :=
  (globalSectionsComplex X (sheafHomComplex X L I).obj).homologyπ 0 (globalHomCocycle X L I f)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Stacks 0A8Z at the class of a cocycle.** `globalHomologyClassEquiv`, followed by the
identification of the cohomology of a Hom complex with cohomology classes, sends the class of a
degree-zero cycle of the global section complex whose associated cochain is `Cochain.ofHom f` to
the cohomology class of the cocycle `Cocycle.ofHom f`. -/
theorem homologyAddEquiv_globalHomologyClassEquiv_homologyπ (f : L ⟶ I)
    (z : (globalSectionsComplex X (sheafHomComplex X L I).obj).cycles 0)
    (hz : (sheafHomComplex X L I).globalSectionsIso.hom.f 0
        ((globalSectionsComplex X (sheafHomComplex X L I).obj).iCycles 0 z) =
      ULift.up (Cochain.ofHom f)) :
    homologyAddEquiv L I 0
        (globalHomologyClassEquiv X L I 0
          ((globalSectionsComplex X (sheafHomComplex X L I).obj).homologyπ 0 z)) =
      CohomologyClass.mk (Cocycle.ofHom f) := by
  rw [globalHomologyClassEquiv_apply]
  exact homologyAddEquiv_mapHomologyIso_homologyπ _
    (sheafHomComplex X L I).globalSectionsIso f z hz

/-- **Stacks 0A94 at the class of a cocycle.** The identification of the degree-zero cohomology
of the global sections of `SheafHom(L, I)` with `Hom_{D(O)}(L, I)` sends the class of a
degree-zero cycle of the global section complex whose associated cochain is `Cochain.ofHom f` to
the image `Q(f)` of `f` in the derived category. -/
theorem sheafHomGlobalHomologyEquivDerivedCategoryHom_homologyπ [I.IsKInjective] (f : L ⟶ I)
    (z : (globalSectionsComplex X (sheafHomComplex X L I).obj).cycles 0)
    (hz : (sheafHomComplex X L I).globalSectionsIso.hom.f 0
        ((globalSectionsComplex X (sheafHomComplex X L I).obj).iCycles 0 z) =
      ULift.up (Cochain.ofHom f)) :
    sheafHomGlobalHomologyEquivDerivedCategoryHom X L I
        ((globalSectionsComplex X (sheafHomComplex X L I).obj).homologyπ 0 z) =
      DerivedCategory.Q.map f := by
  rw [sheafHomGlobalHomologyEquivDerivedCategoryHom_apply X L I _,
    sheafHomGlobalHomotopyCategoryHom_eq_globalHomologyClassEquiv X L I _,
    homologyAddEquiv_globalHomologyClassEquiv_homologyπ X L I f z hz]
  simp only [Category.id_comp, Iso.app_hom]
  rw [homAddEquiv_mk_ofHom_comp_shiftFunctorZero,
    homotopyHomDerivedCategoryEquiv_quotient_map]

/-- **Stacks 0A94 at the class of a cocycle.** The identification of the degree-zero cohomology
of the global sections of `SheafHom(L, I)` with `Hom_{D(O)}(L, I)` sends the class of the cocycle
attached to a morphism of complexes `f : L ⟶ I` to the image `Q(f)` of `f` in the derived
category. -/
theorem sheafHomGlobalHomologyEquivDerivedCategoryHom_globalHomologyClass
    [I.IsKInjective] (f : L ⟶ I) :
    sheafHomGlobalHomologyEquivDerivedCategoryHom X L I (globalHomologyClass X L I f) =
      DerivedCategory.Q.map f :=
  sheafHomGlobalHomologyEquivDerivedCategoryHom_homologyπ X L I f (globalHomCocycle X L I f)
    ((congrArg ((sheafHomComplex X L I).globalSectionsIso.hom.f 0)
      (iCycles_globalHomCocycle X L I f)).trans (globalSectionsIso_globalHomSection X L I f))

/-- **Stacks 0A94 at the class of a cocycle, inverted.** The morphism `Q(f)` of the derived
category corresponds under Stacks 0A94 to the cohomology class of the cocycle attached to `f`. -/
theorem symm_sheafHomGlobalHomologyEquivDerivedCategoryHom_Q_map
    [I.IsKInjective] (f : L ⟶ I) :
    (sheafHomGlobalHomologyEquivDerivedCategoryHom X L I).symm (DerivedCategory.Q.map f) =
      globalHomologyClass X L I f := by
  rw [← sheafHomGlobalHomologyEquivDerivedCategoryHom_globalHomologyClass X L I f,
    AddEquiv.symm_apply_apply]

end AlgebraicGeometry.RingedSite

end
