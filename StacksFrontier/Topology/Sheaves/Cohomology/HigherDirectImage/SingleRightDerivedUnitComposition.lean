module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonAssoc
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedGlobalSectionsMap
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.ResolutionLevelFormula

/-!
# The unit `Φ(-)[0] ⟶ RΦ((-)[0])` and composition of functors

For an additive functor `Φ : 𝒜 ⥤ ℬ` between abelian categories with `𝒜` having enough
injectives, `Stacks.Cohomology.singleRightDerivedUnit` is the canonical transformation
`Φ(-)[0] ⟶ RΦ((-)[0])`, the unit of the bounded below right derived functor read on complexes
concentrated in degree zero. It is compatible with composition of the functors being derived.

## Main results

* `Stacks.Cohomology.singleRightDerivedUnit_comp_app` — the compatibility: for additive
  `Φ : 𝒜 ⥤ ℬ` and `Ψ : ℬ ⥤ 𝒞`, the unit of `R(Ψ ∘ Φ)` at `M`, followed by the canonical
  comparison `R(Ψ ∘ Φ) ⟶ RΦ ⋙ RΨ` of [Stacks, Tag 05T2], is the unit of `RΨ` at `Φ M`
  followed by `RΨ` of the unit of `RΦ` at `M`.
* `Stacks.Cohomology.singleRightDerivedUnit_comp` — the same, as an equality of natural
  transformations.
* `Stacks.Cohomology.singleMapHomologicalComplex_hom_app_comp` — the identification of
  `Φ(M[0])` with `(ΦM)[0]` is compatible with composition, on complexes.
* `Stacks.Cohomology.singleMapPlusHom_comp` — the same in the bounded below homotopy category.
* `Stacks.Cohomology.mapSingleFunctorCompQhIso_hom_app_comp_app` — the same for
  `CategoryTheory.Functor.mapSingleFunctorCompQhIso`, in `D⁺(𝒞)`.

## References

* [Stacks, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2), the comparison transformation
* [Stacks, Tag 01F8](https://stacks.math.columbia.edu/tag/01F8), the unit at a single complex
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Stacks.Cohomology.ModulePushforwardComparison

universe v v₁ v₂ w w₁ w₂ u u₁ u₂

namespace Stacks.Cohomology

-- Pointwise right derivability is found from `EnoughInjectives` before any other route.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The identification of `Φ(M[0])` with `(ΦM)[0]` under composition -/

section Complexes

variable {A : Type*} {B : Type*} {C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  (Φ : A ⥤ B) (Ψ : B ⥤ C) [Φ.Additive] [Ψ.Additive]

/-- **`HomologicalComplex.singleMapHomologicalComplex` is compatible with composition.**
Applying `Ψ` termwise to the identification of `Φ(M[0])` with `(ΦM)[0]`, and then the
identification of `Ψ((ΦM)[0])` with `(Ψ(ΦM))[0]`, is the identification for `Ψ ∘ Φ`. -/
lemma singleMapHomologicalComplex_hom_app_comp {ι : Type*} (c : ComplexShape ι)
    [DecidableEq ι] (j : ι) (M : A) :
    (Ψ.mapHomologicalComplex c).map ((singleMapHomologicalComplex Φ c j).hom.app M) ≫
        (singleMapHomologicalComplex Ψ c j).hom.app (Φ.obj M) =
      (singleMapHomologicalComplex (Φ ⋙ Ψ) c j).hom.app M := by
  ext i
  by_cases h : i = j
  · subst h
    simp
  · exact (isZero_single_obj_X c j ((Φ ⋙ Ψ).obj M) i h).eq_of_tgt _ _

/-- The image of `singleMapPlusHom` in the unbounded homotopy category is the class of
`singleMapHomologicalComplex`. -/
private lemma ι_singleMapPlusHom_eq_quotient_map (M : A) :
    (HomotopyCategory.Plus.ι B).map (singleMapPlusHom Φ M) =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).hom.app M) :=
  (ι_map_singleMapPlusHom Φ M).trans (mapHomotopyCategorySingleFunctor_hom_app Φ M)

/-- **`Stacks.Cohomology.ModulePushforwardComparison.singleMapPlusHom` is compatible with
composition**, in the bounded below homotopy category. -/
lemma singleMapPlusHom_comp (M : A) :
    Ψ.mapHomotopyCategoryPlus.map (singleMapPlusHom Φ M) ≫ singleMapPlusHom Ψ (Φ.obj M) =
      singleMapPlusHom (Φ ⋙ Ψ) M := by
  refine (HomotopyCategory.Plus.ι C).map_injective ?_
  have h1 : (HomotopyCategory.Plus.ι C).map
        (Ψ.mapHomotopyCategoryPlus.map (singleMapPlusHom Φ M)) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).hom.app M)) :=
    (congrArg ((Ψ.mapHomotopyCategory (ComplexShape.up ℤ)).map)
        (ι_singleMapPlusHom_eq_quotient_map Φ M)).trans
      (Functor.mapHomotopyCategory_map Ψ
        ((singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).hom.app M))
  refine (Functor.map_comp _ _ _).trans
    ((CategoryTheory.eq_whisker h1 _).trans
      ((CategoryTheory.whisker_eq _ (ι_singleMapPlusHom_eq_quotient_map Ψ (Φ.obj M))).trans ?_))
  exact ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_comp _ _).symm.trans
    ((congrArg _ (singleMapHomologicalComplex_hom_app_comp Φ Ψ (ComplexShape.up ℤ) 0 M)).trans
      (ι_singleMapPlusHom_eq_quotient_map (Φ ⋙ Ψ) M).symm)

end Complexes

/-! ### The coherence of the three identifications in `D⁺(𝒞)` -/

section Coherence

variable {A : Type u} {B : Type u₁} {C : Type u₂}
  [Category.{v} A] [Category.{v₁} B] [Category.{v₂} C]
  [Abelian A] [Abelian B] [Abelian C]
  (Φ : A ⥤ B) (Ψ : B ⥤ C) [Φ.Additive] [Ψ.Additive] [HasDerivedCategory.{w₂} C]

/-- **`CategoryTheory.Functor.mapSingleFunctorCompQhIso` is compatible with composition.**  The
identification of the image in `D⁺(𝒞)` of `Ψ` applied termwise to `Φ(M[0])` with `(ΨΦM)[0]` is
the image under `Ψ` of the identification for `Φ`, followed by the identification for `Ψ` at
`ΦM`. -/
lemma mapSingleFunctorCompQhIso_hom_app_comp_app (M : A) :
    DerivedCategory.Plus.Qh.map
          (Ψ.mapHomotopyCategoryPlus.map (singleMapPlusHom Φ M)) ≫
        (Functor.mapSingleFunctorCompQhIso Ψ).hom.app (Φ.obj M) =
      (Functor.mapSingleFunctorCompQhIso (Φ ⋙ Ψ)).hom.app M := by
  refine (cancel_mono ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).hom.app
    (Ψ.obj (Φ.obj M)))).1 ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (CategoryTheory.whisker_eq
    (DerivedCategory.Plus.Qh.map (Ψ.mapHomotopyCategoryPlus.map (singleMapPlusHom Φ M)))
    (mapSingleFunctorCompQhIso_hom_app_comp Ψ (Φ.obj M))).trans ?_
  refine Eq.trans ?_ (mapSingleFunctorCompQhIso_hom_app_comp (Φ ⋙ Ψ) M).symm
  exact (DerivedCategory.Plus.Qh.map_comp _ _).symm.trans
    (congrArg DerivedCategory.Plus.Qh.map (singleMapPlusHom_comp Φ Ψ M))

/-- The inverse form of `mapSingleFunctorCompQhIso_hom_app_comp_app`: the identification for
`Ψ ∘ Φ`, read backwards, is the identification for `Ψ` read backwards after the image of
`singleMapPlusHom`. -/
lemma mapSingleFunctorCompQhIso_inv_app_comp_app (M : A) :
    (Functor.mapSingleFunctorCompQhIso (Φ ⋙ Ψ)).inv.app M ≫
        DerivedCategory.Plus.Qh.map
          (Ψ.mapHomotopyCategoryPlus.map (singleMapPlusHom Φ M)) =
      (Functor.mapSingleFunctorCompQhIso Ψ).inv.app (Φ.obj M) := by
  refine (cancel_mono ((Functor.mapSingleFunctorCompQhIso Ψ).hom.app (Φ.obj M))).1 ?_
  refine Eq.trans ?_
    ((Functor.mapSingleFunctorCompQhIso Ψ).inv_hom_id_app (Φ.obj M)).symm
  refine (Category.assoc _ _ _).trans ?_
  refine (CategoryTheory.whisker_eq
    ((Functor.mapSingleFunctorCompQhIso (Φ ⋙ Ψ)).inv.app M)
    (mapSingleFunctorCompQhIso_hom_app_comp_app Φ Ψ M)).trans ?_
  exact (Functor.mapSingleFunctorCompQhIso (Φ ⋙ Ψ)).inv_hom_id_app M

end Coherence

/-! ### The compatibility of the unit with composition -/

section Unit

variable {A : Type u} {B : Type u₁} {C : Type u₂}
  [Category.{v} A] [Category.{v₁} B] [Category.{v₂} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w₁} B] [HasDerivedCategory.{w₂} C]
  (Φ : A ⥤ B) (Ψ : B ⥤ C) [Φ.Additive] [Ψ.Additive]
  [EnoughInjectives A] [EnoughInjectives B]

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] [EnoughInjectives B] in
/-- The three identifications of `(ΦM)[0]` with the image of `Φ(M[0])` cancel: the image of
`singleMapPlusHom`, followed by the identification of `(ΦM)[0]` with its image from `K⁺(ℬ)` read
backwards and by the identification for `Φ` read backwards, is the identity. -/
private lemma qh_singleMapPlusHom_comp_inv (M : A) :
    DerivedCategory.Plus.Qh.map (singleMapPlusHom Φ M) ≫
        ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).inv.app (Φ.obj M) ≫
          (Functor.mapSingleFunctorCompQhIso Φ).inv.app M) =
      𝟙 (DerivedCategory.Plus.Qh.obj (Φ.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.singleFunctor A 0).obj M))) := by
  rw [← mapSingleFunctorCompQhIso_hom_app_comp Φ M, Category.assoc,
    ← Category.assoc ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).hom.app (Φ.obj M)),
    Iso.hom_inv_id_app, Category.id_comp, Iso.hom_inv_id_app]
  rfl

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- The same under `RΨ`. -/
private lemma rΨ_qh_singleMapPlusHom_comp_inv (M : A) :
    Ψ.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map (singleMapPlusHom Φ M)) ≫
        (Ψ.rightDerivedFunctorPlus.map
            ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).inv.app (Φ.obj M)) ≫
          Ψ.rightDerivedFunctorPlus.map
            ((Functor.mapSingleFunctorCompQhIso Φ).inv.app M)) =
      𝟙 (Ψ.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
        (Φ.mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.singleFunctor A 0).obj M)))) := by
  rw [← Functor.map_comp, ← Functor.map_comp, qh_singleMapPlusHom_comp_inv Φ M,
    CategoryTheory.Functor.map_id]

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- The naturality of the unit of `RΨ` along `singleMapPlusHom`, with the three identifications
of `(ΦM)[0]` cancelled: it relates the unit of `RΨ` at `(ΦM)[0]` to the unit at `Φ(M[0])`. -/
private lemma unit_bridge (M : A) :
    DerivedCategory.Plus.Qh.map
          (Ψ.mapHomotopyCategoryPlus.map (singleMapPlusHom Φ M)) ≫
        (Ψ.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.singleFunctor B 0).obj (Φ.obj M)) ≫
          Ψ.rightDerivedFunctorPlus.map
              ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).inv.app (Φ.obj M)) ≫
            Ψ.rightDerivedFunctorPlus.map
              ((Functor.mapSingleFunctorCompQhIso Φ).inv.app M)) =
      Ψ.rightDerivedFunctorPlusUnit.app
        (Φ.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) :=
  (Category.assoc _ _ _).symm.trans
    ((CategoryTheory.eq_whisker
          (Ψ.rightDerivedFunctorPlusUnit.naturality (singleMapPlusHom Φ M))
          (Ψ.rightDerivedFunctorPlus.map
              ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).inv.app (Φ.obj M)) ≫
            Ψ.rightDerivedFunctorPlus.map
              ((Functor.mapSingleFunctorCompQhIso Φ).inv.app M))).trans
      ((Category.assoc _ _ _).trans
        ((CategoryTheory.whisker_eq _ (rΨ_qh_singleMapPlusHom_comp_inv Φ Ψ M)).trans
          (Category.comp_id _))))

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- The identification for `Ψ ∘ Φ` followed by the unit of `RΨ` at `Φ(M[0])` is
the identification for `Ψ`, the unit of `RΨ` at `(ΦM)[0]`, and the two identifications of
`(ΦM)[0]`. -/
private lemma unit_star (M : A) :
    (Functor.mapSingleFunctorCompQhIso Ψ).inv.app (Φ.obj M) ≫
        (Ψ.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.singleFunctor B 0).obj (Φ.obj M)) ≫
          Ψ.rightDerivedFunctorPlus.map
              ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).inv.app (Φ.obj M)) ≫
            Ψ.rightDerivedFunctorPlus.map
              ((Functor.mapSingleFunctorCompQhIso Φ).inv.app M)) =
      (Functor.mapSingleFunctorCompQhIso (Φ ⋙ Ψ)).inv.app M ≫
        Ψ.rightDerivedFunctorPlusUnit.app
          (Φ.mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) :=
  (CategoryTheory.eq_whisker (mapSingleFunctorCompQhIso_inv_app_comp_app Φ Ψ M).symm
        (Ψ.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.singleFunctor B 0).obj (Φ.obj M)) ≫
          Ψ.rightDerivedFunctorPlus.map
              ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).inv.app (Φ.obj M)) ≫
            Ψ.rightDerivedFunctorPlus.map
              ((Functor.mapSingleFunctorCompQhIso Φ).inv.app M))).trans
    ((Category.assoc _ _ _).trans
      (CategoryTheory.whisker_eq _ (unit_bridge Φ Ψ M)))

/-- The factorization of the comparison of [Stacks, Tag 05T2] through the unit of `R(Ψ ∘ Φ)`, at
the complex `M[0]` of `K⁺(𝒜)`, with its coherence isomorphism cancelled. -/
private lemma unit_fac (M : A) :
    (Φ ⋙ Ψ).rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.singleFunctor A 0).obj M) ≫
        (Functor.rightDerivedFunctorPlusComp Φ Ψ).app
          (DerivedCategory.Plus.Qh.obj
            ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) =
      Ψ.rightDerivedFunctorPlusUnit.app
          (Φ.mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) ≫
        Ψ.rightDerivedFunctorPlus.map
          (Φ.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) :=
  (Functor.rightDerivedFunctorPlusComp_fac_app Φ Ψ
      ((HomotopyCategory.Plus.singleFunctor A 0).obj M)).trans
    (Functor.qhMapCompIsoReflInv_comp Φ Ψ
      ((HomotopyCategory.Plus.singleFunctor A 0).obj M)
      (Ψ.rightDerivedFunctorPlusUnit.app
          (Φ.mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) ≫
        Ψ.rightDerivedFunctorPlus.map
          (Φ.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.singleFunctor A 0).obj M))))

/-- **The unit `Φ(-)[0] ⟶ RΦ((-)[0])` is compatible with composition of the functors being
derived.**  For additive `Φ : 𝒜 ⥤ ℬ` and `Ψ : ℬ ⥤ 𝒞`, with `𝒜` and `ℬ` having enough
injectives, the unit of `R(Ψ ∘ Φ)` at `M`, followed by the canonical comparison
`R(Ψ ∘ Φ) ⟶ RΦ ⋙ RΨ` of [Stacks, Tag 05T2], is the unit of `RΨ` at `ΦM` followed by `RΨ` of
the unit of `RΦ` at `M`:

`(ΨΦM)[0] ⟶ R(Ψ∘Φ)(M[0]) ⟶ RΨ(RΦ(M[0]))`  equals  `(ΨΦM)[0] ⟶ RΨ((ΦM)[0]) ⟶ RΨ(RΦ(M[0]))`.

Nothing is assumed beyond additivity and enough injectives; in particular the comparison need
not be invertible. -/
theorem singleRightDerivedUnit_comp_app (M : A) :
    (singleRightDerivedUnit (Φ ⋙ Ψ)).app M ≫
        (Functor.rightDerivedFunctorPlusComp Φ Ψ).app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) =
      (singleRightDerivedUnit Ψ).app (Φ.obj M) ≫
        Ψ.rightDerivedFunctorPlus.map ((singleRightDerivedUnit Φ).app M) := by
  have hL : ((Functor.mapSingleFunctorCompQhIso (Φ ⋙ Ψ)).inv.app M ≫
        (Φ ⋙ Ψ).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.singleFunctor A 0).obj M) ≫
          (Φ ⋙ Ψ).rightDerivedFunctorPlus.map
            ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M)) ≫
      (Functor.rightDerivedFunctorPlusComp Φ Ψ).app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) =
      (Functor.mapSingleFunctorCompQhIso (Φ ⋙ Ψ)).inv.app M ≫
        Ψ.rightDerivedFunctorPlusUnit.app
            (Φ.mapHomotopyCategoryPlus.obj
              ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) ≫
          Ψ.rightDerivedFunctorPlus.map
              (Φ.rightDerivedFunctorPlusUnit.app
                ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) ≫
            Ψ.rightDerivedFunctorPlus.map
              (Φ.rightDerivedFunctorPlus.map
                ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M)) :=
    (Category.assoc _ _ _).trans
      (CategoryTheory.whisker_eq _
        ((Category.assoc _ _ _).trans
          ((CategoryTheory.whisker_eq _
                ((Functor.rightDerivedFunctorPlusComp Φ Ψ).naturality
                  ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M))).trans
            ((Category.assoc _ _ _).symm.trans
              ((CategoryTheory.eq_whisker (unit_fac Φ Ψ M)
                    ((Φ.rightDerivedFunctorPlus ⋙
                      Ψ.rightDerivedFunctorPlus).map
                        ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M))).trans
                (Category.assoc _ _ _))))))
  have hR : ((Functor.mapSingleFunctorCompQhIso Ψ).inv.app (Φ.obj M) ≫
        Ψ.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.singleFunctor B 0).obj (Φ.obj M)) ≫
          Ψ.rightDerivedFunctorPlus.map
            ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).inv.app (Φ.obj M))) ≫
      Ψ.rightDerivedFunctorPlus.map
        ((Functor.mapSingleFunctorCompQhIso Φ).inv.app M ≫
          Φ.rightDerivedFunctorPlusUnit.app
              ((HomotopyCategory.Plus.singleFunctor A 0).obj M) ≫
            Φ.rightDerivedFunctorPlus.map
              ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M)) =
      ((Functor.mapSingleFunctorCompQhIso Ψ).inv.app (Φ.obj M) ≫
          Ψ.rightDerivedFunctorPlusUnit.app
              ((HomotopyCategory.Plus.singleFunctor B 0).obj (Φ.obj M)) ≫
            Ψ.rightDerivedFunctorPlus.map
                ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).inv.app (Φ.obj M)) ≫
              Ψ.rightDerivedFunctorPlus.map
                ((Functor.mapSingleFunctorCompQhIso Φ).inv.app M)) ≫
        Ψ.rightDerivedFunctorPlus.map
            (Φ.rightDerivedFunctorPlusUnit.app
              ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) ≫
          Ψ.rightDerivedFunctorPlus.map
            (Φ.rightDerivedFunctorPlus.map
              ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M)) := by
    simp only [Functor.map_comp, Category.assoc]
  refine hL.trans (hR.trans ?_).symm
  exact ((CategoryTheory.eq_whisker (unit_star Φ Ψ M)
        (Ψ.rightDerivedFunctorPlus.map
            (Φ.rightDerivedFunctorPlusUnit.app
              ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) ≫
          Ψ.rightDerivedFunctorPlus.map
            (Φ.rightDerivedFunctorPlus.map
              ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M)))).trans
    (Category.assoc _ _ _))

/-- **The compatibility of the unit with composition, as an equality of natural
transformations.**  This is `singleRightDerivedUnit_comp_app` read naturally in `M`. -/
theorem singleRightDerivedUnit_comp :
    singleRightDerivedUnit (Φ ⋙ Ψ) ≫
        Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
          (Functor.rightDerivedFunctorPlusComp Φ Ψ) =
      Functor.whiskerLeft Φ (singleRightDerivedUnit Ψ) ≫
        Functor.whiskerRight (singleRightDerivedUnit Φ) Ψ.rightDerivedFunctorPlus :=
  NatTrans.ext (funext fun M ↦ singleRightDerivedUnit_comp_app Φ Ψ M)

end Unit

end Stacks.Cohomology

end
