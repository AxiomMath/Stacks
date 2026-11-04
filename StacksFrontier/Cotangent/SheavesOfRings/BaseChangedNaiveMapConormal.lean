module

public import StacksFrontier.Cotangent.SheavesOfRings.BaseChangedNaiveComparison

/-!
# The map `NL_{B/A} ⊗_B D ⟶ NL_{D/A}` on conormal classes

Let `g : A ⟶ B` and `h : B ⟶ D` be homomorphisms of sheaves of commutative rings on a site, and
let `CategoryTheory.Sheaf.baseChangedNaiveMap J g h : NL_{B/A} ⊗_B D ⟶ NL_{D/A}` be the map
through which the first displayed arrow of Tag 08SZ followed by the comparison of Tag 08US
factors. This file computes it in degree `-1` on the local sections that matter for the
obstruction of Tag 08UZ: a local section `r` of `A` killed by `g` gives a relation of the
canonical presentation `A[B] ⟶ B` and a relation of the canonical presentation `A[D] ⟶ D`, and
the map carries the class of the first, extended to `D`, to the class of the second.

## Main results

* `CategoryTheory.Sheaf.baseChangedNaiveMap_extendUnit_canonicalNaiveClass`: the map carries the
  extended class of a relation of `A[B] ⟶ B` coming from `A` to the class of the same relation of
  `A[D] ⟶ D`.
* `CategoryTheory.Sheaf.baseChangedNaiveMap_naiveConormalClass`: the same statement with the
  classes read through `NL_{B/A}.X (-1) = I/I²`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

/-- The unit `M ⟶ M ⊗_B D` of extension of scalars along `h`, on local sections. -/
abbrev extendUnit (M : targetModules.{u, v, w} J B) (U : Cᵒᵖ) (m : M.val.obj U) :
    ((towerExtendScalars.{u, v, w} J h).obj M).val.obj U :=
  ((towerExtendRestrictAdjunction.{u, v, w} J h).unit.app M).val.app U m

/-- The unit of extension of scalars along `h` is natural, on local sections. -/
theorem map_extendUnit {M N : targetModules.{u, v, w} J B} (φ : M ⟶ N) (U : Cᵒᵖ)
    (m : M.val.obj U) :
    ((towerExtendScalars.{u, v, w} J h).map φ).val.app U (extendUnit J h M U m) =
      extendUnit J h N U (φ.val.app U m) :=
  congrArg (fun k => k.val.app U m)
    ((towerExtendRestrictAdjunction.{u, v, w} J h).unit_naturality φ)

/-- The comparison `L_{B/A} ⊗_B D ≅ (Ω_{P_•/A} ⊗ B) ⊗_B D` of the degreewise extension of
`L_{B/A}` with the first vertex is, in degree `-n`, the identity read through the two degree
isomorphisms. -/
theorem towerExtendScalarsCotangentComplexIso_hom_f (n : ℕ) :
    (towerExtendScalarsCotangentComplexIso.{u, v, w} J g h).hom.f (-(n : ℤ)) =
      (towerExtendScalars.{u, v, w} J h).map (cotangentComplex_degreeIso.{u, v, w} J g n).hom ≫
        (baseChangedCotangentComplex_degreeIso.{u, v, w} J g h n).inv := by
  have hn : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
  set K := (AlgebraicTopology.alternatingFaceMapComplex (targetModules.{u, v, w} J B)).obj
    (cotangentSimplicialModule.{u, v, w} J g).object
  set F := towerExtendScalars.{u, v, w} J h
  set E := HomologicalComplex.mapHomologicalComplexExtendIso F K (ComplexShape.embeddingUpIntLE 0)
  set ψ := (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso F).app
    (cotangentSimplicialModule.{u, v, w} J g).object
  have hinv : E.inv.f (-(n : ℤ)) =
      F.map (K.extendXIso (ComplexShape.embeddingUpIntLE 0) hn).hom ≫
        (((F.mapHomologicalComplex _).obj K).extendXIso
          (ComplexShape.embeddingUpIntLE 0) hn).inv := by
    rw [← cancel_epi (E.hom.f (-(n : ℤ))), ← HomologicalComplex.comp_f, Iso.hom_inv_id,
      HomologicalComplex.id_f, HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _ hn]
    simp
  have hext : (HomologicalComplex.extendMap ψ.hom (ComplexShape.embeddingUpIntLE 0)).f (-(n : ℤ)) =
      (((F.mapHomologicalComplex _).obj K).extendXIso (ComplexShape.embeddingUpIntLE 0) hn).hom ≫
        ψ.hom.f n ≫ ((((SimplicialObject.whiskering _ _).obj F).obj
          (cotangentSimplicialModule.{u, v, w} J g).object |>
            (AlgebraicTopology.alternatingFaceMapComplex
              (targetModules.{u, v, w} J D)).obj).extendXIso
              (ComplexShape.embeddingUpIntLE 0) hn).inv :=
    HomologicalComplex.extendMap_f _ _ hn
  have hψ : ψ.hom.f n = 𝟙 _ := rfl
  exact (congrArg₂ (· ≫ ·) hinv hext).trans (by
    rw [hψ, Category.assoc, Iso.inv_hom_id_assoc]
    exact congrArg (F.map (K.extendXIso (ComplexShape.embeddingUpIntLE 0) hn).hom ≫ ·)
      (Category.id_comp _))

/-- An isomorphism of sheaves of modules undoes its inverse on local sections. -/
private theorem hom_app_inv_app {E : Sheaf J CommRingCat.{max u v w}}
    {M N : targetModules.{u, v, w} J E} (e : M ≅ N) (U : Cᵒᵖ) (n : N.val.obj U) :
    e.hom.val.app U (e.inv.val.app U n) = n :=
  congrArg (fun k => k.val.app U n) e.inv_hom_id

/-- The first displayed arrow of Tag 08SZ, read on the degreewise extension of `L_{B/A}`, sends
the extension of the pure differential `d x` of a local section `x` of `P₁` to the pure
differential of the image of `x` under the map of standard resolutions. -/
theorem towerCotangentBaseChange_extendUnit (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, w} J g (op ⦋1⦌)).obj.obj U) :
    (((towerExtendScalarsCotangentComplexIso.{u, v, w} J g h).hom ≫
        towerCotangentBaseChange.{u, v, w} J g h).f (-((1 : ℕ) : ℤ))).val.app U
      (extendUnit J h _ U ((cotangentComplex_degreeIso.{u, v, w} J g 1).inv.val.app U
          (((cotangentSimplicialModule.{u, v, w} J g).universalDerivation (op ⦋1⦌)).d x))) =
      (cotangentComplex_degreeIso.{u, v, w} J (g ≫ h) 1).inv.val.app U
        (((cotangentSimplicialModule.{u, v, w} J (g ≫ h)).universalDerivation (op ⦋1⦌)).d
          (((towerBaseChangeSquare.{u, v, w} J g h).resolution (op ⦋1⦌)).hom.app U x)) := by
  rw [HomologicalComplex.comp_f, towerExtendScalarsCotangentComplexIso_hom_f,
    towerCotangentBaseChange_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h₁ : ((towerExtendScalars.{u, v, w} J h).map
        (cotangentComplex_degreeIso.{u, v, w} J g 1).hom).val.app U
        (extendUnit J h _ U ((cotangentComplex_degreeIso.{u, v, w} J g 1).inv.val.app U
          (((cotangentSimplicialModule.{u, v, w} J g).universalDerivation (op ⦋1⦌)).d x))) =
      extendUnit J h _ U (((cotangentSimplicialModule.{u, v, w} J g).universalDerivation
        (op ⦋1⦌)).d x) := by
    rw [map_extendUnit]
    exact congrArg (extendUnit J h _ U) (hom_app_inv_app _ _ _ _)
  have h₂ : ((baseChangeSimplicialMap.{u, v, w} J g h).app (op ⦋1⦌)).val.app U
        (extendUnit J h _ U (((cotangentSimplicialModule.{u, v, w} J g).universalDerivation
          (op ⦋1⦌)).d x)) =
      ((cotangentSimplicialModule.{u, v, w} J (g ≫ h)).universalDerivation (op ⦋1⦌)).d
        (((towerBaseChangeSquare.{u, v, w} J g h).resolution (op ⦋1⦌)).hom.app U x) := by
    have ht := baseChangeSimplicialMap_transpose.{u, v, w} J g h (op ⦋1⦌)
    have hv : ((towerExtendRestrictAdjunction.{u, v, w} J h).unit.app
          ((cotangentSimplicialModule.{u, v, w} J g).object.obj (op ⦋1⦌)) ≫
        (squareRestrict.{u, v, w} J h).map
          ((baseChangeSimplicialMap.{u, v, w} J g h).app (op ⦋1⦌))).val.app U
          (((cotangentSimplicialModule.{u, v, w} J g).universalDerivation (op ⦋1⦌)).d x) =
        (squareCotangentTermMap (towerBaseChangeSquare.{u, v, w} J g h) (op ⦋1⦌)).val.app U
          (((cotangentSimplicialModule.{u, v, w} J g).universalDerivation (op ⦋1⦌)).d x) := by
      rw [ht]
    refine hv.trans ?_
    exact (derivationEquiv_val_app J g (op ⦋1⦌) _ _ U x).symm.trans
      (squareCotangentTermMap_d _ (op ⦋1⦌) U x)
  show (cotangentComplex_degreeIso.{u, v, w} J (g ≫ h) 1).inv.val.app U
      (((baseChangeSimplicialMap.{u, v, w} J g h).app (op ⦋1⦌)).val.app U
        (((towerExtendScalars.{u, v, w} J h).map
          (cotangentComplex_degreeIso.{u, v, w} J g 1).hom).val.app U _)) = _
  rw [h₁, h₂]

/-! ### The comparison of Tag 08US on pure differentials -/

section Comparison

variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- The conormal class, for the canonical presentation `A[B] ⟶ B`, of a local relation, read in
degree `-1` of the naive cotangent complex `NL_{B/A}` of Tag 08TW through the identification of
`CategoryTheory.Sheaf.naiveCotangentComplexIsoCanonical`. -/
noncomputable def canonicalNaiveClass (U : Cᵒᵖ)
    (z : Stacks.Sites.Conormal.kernelIdeal
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f).hom U) :
    ((Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, u} J A B f).X (-1)).val.obj U :=
  ((naiveCotangentComplexIsoCanonical.{u, v, w} J f).hom.f (-1)).val.app U
    ((naiveCotangentComplexXNegOneIso.{u, v, w} J f).inv.val.app U
      ((naiveConormalIso.{u, v, w} J f).inv.val.app U
        (Stacks.Sites.Conormal.conormalClass.{v, u, max u v w, u} J A _ B
          (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
            (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B))
          (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f) U z)))

/-- The relation of the canonical presentation which a relation of the presentation
`P₀ ⟶ B` corresponds to under `P₀ ≅ A[B]`. -/
noncomputable def canonicalRelation (U : Cᵒᵖ)
    (y : Stacks.Sites.Conormal.kernelIdeal (resolutionAugmentation J f (op ⦋0⦌)).hom U) :
    Stacks.Sites.Conormal.kernelIdeal
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f).hom U :=
  ⟨((resolutionZeroIsoFreeAlgebra J f).hom.hom.app U) y,
    Stacks.Sites.Conormal.kernelIdeal_le_comap _ _ _
      (Stacks.Sites.Conormal.hom_of_comp_eq
        (resolutionZeroIsoFreeAlgebra_hom_comp_canonicalPresentation J f)) U y.2⟩

/-- **The comparison of Tag 08US on a pure differential**: in degree `-1` it sends `d x` to the
conormal class of `d₀ x - d₁ x`, read in the canonical presentation. -/
theorem canonicalNaiveComparison_negOne_apply (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, w} J f (op ⦋1⦌)).obj.obj U) :
    ((canonicalNaiveComparison.{u, v, w} J f).f (-1)).val.app U
        ((cotangentComplex_degreeIso.{u, v, w} J f 1).inv.val.app U
          (((cotangentSimplicialModule.{u, v, w} J f).universalDerivation (op ⦋1⦌)).d x)) =
      canonicalNaiveClass J f U (canonicalRelation J f U (faceDifference J f U x)) := by
  have h₁ : ((naiveComparison.{u, v, w} J f).f (-1)).val.app U
      ((cotangentComplex_degreeIso.{u, v, w} J f 1).inv.val.app U
        (((cotangentSimplicialModule.{u, v, w} J f).universalDerivation (op ⦋1⦌)).d x)) =
      (naiveCotangentComplexXNegOneIso.{u, v, w} J f).inv.val.app U
        (conormalClassSection J f U (faceDifference J f U x)) := by
    rw [naiveComparison_f_negOne]
    show (naiveCotangentComplexXNegOneIso.{u, v, w} J f).inv.val.app U
      ((naiveComparisonNegOne.{u, v, w} J f).val.app U
        ((cotangentComplex_degreeIso.{u, v, w} J f 1).hom.val.app U _)) = _
    erw [hom_app_inv_app]
    rw [naiveComparisonNegOne_conormalClass]
  have h₂ : (naiveConormalIso.{u, v, w} J f).hom.val.app U
      (conormalClassSection J f U (faceDifference J f U x)) =
      Stacks.Sites.Conormal.conormalClass.{v, u, max u v w, u} J A _ B
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
          (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B))
        (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f) U
        (canonicalRelation J f U (faceDifference J f U x)) :=
    Stacks.Sites.Conormal.conormalSheafMapOfFac_conormalClass _ _ _ _ _ _ _ _ _ _
      (resolutionZeroIsoFreeAlgebra_hom_comp_canonicalPresentation J f) _ _
  have h₂' :=
    (congrArg (fun y => ((naiveConormalIso.{u, v, w} J f).inv.val.app U).hom y) h₂).symm.trans
      (congrArg (fun k => (k.val.app U).hom (conormalClassSection J f U (faceDifference J f U x)))
        (naiveConormalIso.{u, v, w} J f).hom_inv_id)
  rw [show canonicalNaiveComparison.{u, v, w} J f =
      naiveComparison.{u, v, w} J f ≫ (naiveCotangentComplexIsoCanonical.{u, v, w} J f).hom
        from rfl,
    HomologicalComplex.comp_f, SheafOfModules.comp_val, PresheafOfModules.comp_app]
  refine (ModuleCat.comp_apply _ _ _).trans ?_
  exact (congrArg (fun y => (((naiveCotangentComplexIsoCanonical.{u, v, w} J f).hom.f (-1)).val.app
      U).hom y) h₁).trans (congrArg (fun y => (((naiveCotangentComplexIsoCanonical.{u, v, w} J
        f).hom.f (-1)).val.app U).hom (((naiveCotangentComplexXNegOneIso.{u, v, w} J f).inv.val.app
          U).hom y)) h₂').symm

end Comparison

/-! ### The map `NL_{B/A} ⊗_B D ⟶ NL_{D/A}` on the classes of relations coming from `A` -/

/-- A composite of maps of complexes of sheaves of modules, on local sections. -/
theorem comp_f_val_app {E : Sheaf J CommRingCat.{max u v w}}
    {K L M : CochainComplex (targetModules.{u, v, w} J E) ℤ} (φ : K ⟶ L) (ψ : L ⟶ M) (n : ℤ)
    (U : Cᵒᵖ) (z : (K.X n).val.obj U) :
    ((φ ≫ ψ).f n).val.app U z = (ψ.f n).val.app U ((φ.f n).val.app U z) :=
  rfl

/-- The structure map `A ⟶ P_n` of a term of the standard resolution of `f : A ⟶ B`, followed by
its augmentation `P_n ⟶ B`, is `f`. -/
theorem resolutionBase_comp_resolutionAugmentation {A B : Sheaf J CommRingCat.{max u v w}}
    (f : A ⟶ B) (n : SimplexCategoryᵒᵖ) :
    resolutionBase J f n ≫ resolutionAugmentation J f n = f :=
  ((standardResolution J f).hom.app n).w

/-- A local section of `A` killed by `g`, read in `P₀` through its structure map, is a relation of
the presentation `P₀ ⟶ B`. -/
theorem resolutionBase_mem_kernelIdeal (f : A ⟶ B) (U : Cᵒᵖ) (r : A.obj.obj U)
    (hr : (f.hom.app U).hom r = 0) :
    ((resolutionBase.{u, v, w} J f (op ⦋0⦌)).hom.app U).hom r ∈
      Stacks.Sites.Conormal.kernelIdeal (resolutionAugmentation.{u, v, w} J f (op ⦋0⦌)).hom U :=
  (congrArg (fun k : A ⟶ B => (k.hom.app U).hom r)
    (resolutionBase_comp_resolutionAugmentation.{u, v, w} J f (op ⦋0⦌))).trans hr

/-- The relation of `P₀ ⟶ B` given by a local section of `A` killed by `f`. -/
abbrev baseRelation (f : A ⟶ B) (U : Cᵒᵖ) (r : A.obj.obj U) (hr : (f.hom.app U).hom r = 0) :
    Stacks.Sites.Conormal.kernelIdeal (resolutionAugmentation.{u, v, w} J f (op ⦋0⦌)).hom U :=
  ⟨((resolutionBase.{u, v, w} J f (op ⦋0⦌)).hom.app U).hom r,
    resolutionBase_mem_kernelIdeal J f U r hr⟩

/-- The relation of the canonical presentation attached to a section of `A` killed by `f` is its
image under the coefficient map. -/
theorem canonicalRelation_baseRelation (f : A ⟶ B) (U : Cᵒᵖ) (r : A.obj.obj U)
    (hr : (f.hom.app U).hom r = 0) :
    ((canonicalRelation J f U (baseRelation J f U r hr) :
        Stacks.Sites.Conormal.kernelIdeal
          (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f).hom U) :
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)).obj.obj U) =
      ((Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)).hom.app U).hom r :=
  congrArg (fun k => (k.hom.app U).hom r) (resolutionBase_comp_resolutionZeroIsoFreeAlgebra_hom J f)

/-- **The map `NL_{B/A} ⊗_B D ⟶ NL_{D/A}` on the class of a relation coming from `A`.** For a
local section `r` of `A` killed by `g`, the map carries the extended conormal class of the
relation `r` of `A[B] ⟶ B` to the conormal class of the relation `r` of `A[D] ⟶ D`. -/
theorem baseChangedNaiveMap_extendUnit_canonicalNaiveClass (U : Cᵒᵖ) (r : A.obj.obj U)
    (hr : (g.hom.app U).hom r = 0) :
    ((baseChangedNaiveMap.{u, v, w} J g h).f (-1)).val.app U
        (extendUnit J h _ U (canonicalNaiveClass J g U
          (canonicalRelation J g U (baseRelation J g U r hr)))) =
      canonicalNaiveClass J (g ≫ h) U (canonicalRelation J (g ≫ h) U
        (baseRelation J (g ≫ h) U r (by
          change (h.hom.app U).hom ((g.hom.app U).hom r) = 0
          rw [hr, map_zero]))) := by
  set x := kernelLift J g U (((resolutionBase.{u, v, w} J g (op ⦋0⦌)).hom.app U).hom r)
  have hx : faceDifference J g U x = baseRelation J g U r hr :=
    faceDifference_kernelLift J g U (baseRelation J g U r hr)
  set sq := towerBaseChangeSquare.{u, v, w} J g h
  set Y := (cotangentComplex_degreeIso.{u, v, w} J g 1).inv.val.app U
    (((cotangentSimplicialModule.{u, v, w} J g).universalDerivation (op ⦋1⦌)).d x)
  have s₁ : canonicalNaiveClass J g U (canonicalRelation J g U (baseRelation J g U r hr)) =
      ((canonicalNaiveComparison.{u, v, w} J g).f (-1)).val.app U Y := by
    rw [← hx]
    exact (canonicalNaiveComparison_negOne_apply J g U x).symm
  have hcomp : extendedNaiveComparison.{u, v, w} J g h ≫ baseChangedNaiveMap.{u, v, w} J g h =
      ((towerExtendScalarsCotangentComplexIso.{u, v, w} J g h).hom ≫
        towerCotangentBaseChange.{u, v, w} J g h) ≫
          canonicalNaiveComparison.{u, v, w} J (g ≫ h) := by
    rw [← cancel_epi (towerExtendScalarsCotangentComplexIso.{u, v, w} J g h).inv,
      ← Category.assoc, ← Category.assoc, Iso.inv_hom_id_assoc, Category.assoc]
    exact baseChangedNaiveComparison_comp_baseChangedNaiveMap.{u, v, w} J g h
  have s₅ : faceDifference J (g ≫ h) U ((sq.resolution (op ⦋1⦌)).hom.app U x) =
      baseRelation J (g ≫ h) U r (by
        show (h.hom.app U).hom ((g.hom.app U).hom r) = 0
        rw [hr, map_zero]) := by
    refine Subtype.ext ?_
    have hface : ∀ k : Fin 2, faceSections J (g ≫ h) k U ((sq.resolution (op ⦋1⦌)).hom.app U x) =
        (sq.resolution (op ⦋0⦌)).hom.app U (faceSections J g k U x) := fun k =>
      (congrArg (fun t => t.hom.app U x) (sq.resolution_naturality (SimplexCategory.δ k).op)).symm
    have hbase : (sq.resolution (op ⦋0⦌)).hom.app U
        (((resolutionBase.{u, v, w} J g (op ⦋0⦌)).hom.app U).hom r) =
        ((resolutionBase.{u, v, w} J (g ≫ h) (op ⦋0⦌)).hom.app U).hom r :=
      congrArg (fun t => t.hom.app U r) (sq.resolution_base (op ⦋0⦌))
    have hx' := congrArg Subtype.val hx
    rw [faceDifference_coe] at hx' ⊢
    rw [hface 0, hface 1, ← map_sub, hx', hbase]
  rw [s₁, ← map_extendUnit J h ((canonicalNaiveComparison.{u, v, w} J g).f (-1)) U Y]
  refine ((comp_f_val_app J (extendedNaiveComparison.{u, v, w} J g h)
    (baseChangedNaiveMap.{u, v, w} J g h) (-1) U _).symm.trans ?_)
  rw [hcomp, comp_f_val_app]
  refine (congrArg (((canonicalNaiveComparison.{u, v, w} J (g ≫ h)).f (-1)).val.app U)
    (towerCotangentBaseChange_extendUnit J g h U x)).trans ?_
  rw [canonicalNaiveComparison_negOne_apply, s₅]

/-! ### The same computation with the classes read through `NL_{B/A}.X (-1) = I/I²` -/

section Classes

variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- The conormal class of a relation of the canonical presentation `A[B] ⟶ B`, read in degree
`-1` of the naive cotangent complex `NL_{B/A}` of Tag 08TW through `NL_{B/A}.X (-1) = I/I²`. -/
noncomputable abbrev naiveConormalClass (U : Cᵒᵖ)
    (z : Stacks.Sites.Conormal.kernelIdeal
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f).hom U) :
    ((Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, u} J A B f).X (-1)).val.obj U :=
  (eqToHom (Stacks.SheafOfModules.naiveCotangentComplex_X_negOne.{v, u, max u v w, u}
      J A B f).symm).val.app U
    (Stacks.Sites.Conormal.conormalClass.{v, u, max u v w, u} J A _ B
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B))
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f) U z)

/-- On the conormal sheaf of `P₀ ⟶ B`, the identification in degree `-1` of the naive cotangent
complex of `P₀ ⟶ B` with `NL_{B/A}` is the isomorphism of conormal sheaves induced by
`P₀ ≅ A[B]`, followed by `NL_{B/A}.X (-1) = I/I²`. -/
theorem naiveCotangentComplexXNegOneIso_inv_comp_isoCanonical :
    (naiveCotangentComplexXNegOneIso.{u, v, w} J f).inv ≫
        (naiveCotangentComplexIsoCanonical.{u, v, w} J f).hom.f (-1) =
      (naiveConormalIso.{u, v, w} J f).hom ≫
        eqToHom (Stacks.SheafOfModules.naiveCotangentComplex_X_negOne.{v, u, max u v w, u}
          J A B f).symm := by
  rw [naiveCotangentComplexIsoCanonical, HomologicalComplex.doubleIsoOfIso_hom,
    HomologicalComplex.doubleMap_f₀, naiveCotangentComplexXNegOneIso]
  exact (Iso.inv_hom_id_assoc (HomologicalComplex.doubleXIso₀ (naiveSequence.{u, v, w} J f).f
    ComplexShape.upIntRelNegOneZero) _).trans rfl

/-- `canonicalNaiveClass` is the conormal class read through `NL_{B/A}.X (-1) = I/I²`. -/
theorem canonicalNaiveClass_eq (U : Cᵒᵖ)
    (z : Stacks.Sites.Conormal.kernelIdeal
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f).hom U) :
    canonicalNaiveClass J f U z = naiveConormalClass J f U z := by
  set x := Stacks.Sites.Conormal.conormalClass.{v, u, max u v w, u} J A _ B
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B))
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f) U z
  have h₁ := congrArg (fun k => k.val.app U ((naiveConormalIso.{u, v, w} J f).inv.val.app U x))
    (naiveCotangentComplexXNegOneIso_inv_comp_isoCanonical J f)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at h₁
  rw [canonicalNaiveClass, h₁, hom_app_inv_app]

/-- The coefficient image of a local section of `A` killed by `f`, a relation of the canonical
presentation `A[B] ⟶ B`. -/
noncomputable def coefficientRelation (U : Cᵒᵖ) (r : A.obj.obj U) (hr : (f.hom.app U).hom r = 0) :
    Stacks.Sites.Conormal.kernelIdeal
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f).hom U :=
  canonicalRelation J f U (baseRelation J f U r hr)

/-- The relation `CategoryTheory.Sheaf.coefficientRelation` is the image of `r` under the
coefficient map `A ⟶ A[B]`. -/
theorem coefficientRelation_coe (U : Cᵒᵖ) (r : A.obj.obj U) (hr : (f.hom.app U).hom r = 0) :
    ((coefficientRelation J f U r hr : Stacks.Sites.Conormal.kernelIdeal
        (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f).hom U) :
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)).obj.obj U) =
      ((Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)).hom.app U).hom r :=
  canonicalRelation_baseRelation J f U r hr

end Classes

/-- **The map `NL_{B/A} ⊗_B D ⟶ NL_{D/A}` on conormal classes**: for a local section `r` of `A`
killed by `g`, the class of its coefficient image in `NL_{B/A}`, extended to `D`, goes to the
class of its coefficient image in `NL_{D/A}`. -/
theorem baseChangedNaiveMap_naiveConormalClass (U : Cᵒᵖ) (r : A.obj.obj U)
    (hr : (g.hom.app U).hom r = 0) :
    ((baseChangedNaiveMap.{u, v, w} J g h).f (-1)).val.app U
        (extendUnit J h _ U (naiveConormalClass J g U (coefficientRelation J g U r hr))) =
      naiveConormalClass J (g ≫ h) U (coefficientRelation J (g ≫ h) U r (by
        change (h.hom.app U).hom ((g.hom.app U).hom r) = 0
        rw [hr, map_zero])) := by
  rw [← canonicalNaiveClass_eq, ← canonicalNaiveClass_eq]
  exact baseChangedNaiveMap_extendUnit_canonicalNaiveClass J g h U r hr

end CategoryTheory.Sheaf

end
