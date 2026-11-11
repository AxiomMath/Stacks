module

public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives

/-!
# Inverse limits as derived inverse limits

Let `(Fₙ)` be a countable inverse system of modules on a ringed space. If a basis of opens is
acyclic for every `Fₙ` and the first derived inverse limit of the sections over each basis open
vanishes, then the ordinary inverse limit represents the derived inverse limit. Moreover, the
ordinary inverse limit is acyclic on every member of the basis.

## Main definitions

* `Stacks.Cohomology.SpaceInverseLimits.sectionsSystem` evaluates an inverse system of modules
  on an open subset.
* `Stacks.Cohomology.SpaceInverseLimits.inverseLimitDifference` is the standard difference
  endomorphism of the product of a countable inverse system of abelian groups.

## Main results

* `Stacks.Cohomology.SpaceInverseLimits.isDerivedLimit_single_limit_of_isBasis` identifies the
  ordinary inverse limit with the derived inverse limit.
* `Stacks.Cohomology.SpaceInverseLimits.exists_distTriang_single_limit_of_isBasis` is the same
  identification with the structural morphism of the triangle named.
* `Stacks.Cohomology.SpaceInverseLimits.isZero_cohomology_limit_of_isBasis` gives the resulting
  higher-cohomology vanishing on basis opens.

## Implementation notes

The first assertion is expressed by saying that the ordinary limit, placed in degree zero, has
the defining `IsDerivedLimit` distinguished triangle. The existence of the product in the derived
category is part of that assertion rather than an additional hypothesis. For a countable inverse
system of abelian groups, `R¹ lim` is the cokernel of `inverseLimitDifference`; its vanishing is
therefore expressed by that morphism being an epimorphism. The two independent conclusions of the
source lemma are separate declarations.

Products in the derived category of sheaves of modules come from
`Stacks.Injectives.hasProducts_derivedCategory` (Tag 07D9), which supplies them as instances;
the limits of sheaves of modules used to compute sections pointwise are Mathlib's.

Several steps compare a cochain complex indexed by `ℕ` with its extension by zero to `ℤ`, where
the identification of degree-zero objects is definitional but not available at the `implicit`
transparency level that `rw` and `simp` work at. Those steps therefore state the needed
cancellation as a small lemma about abstract isomorphisms and close the goal with `exact`, whose
definitional check runs at default transparency; `invHomCancel₁` through `comp_map_id` exist for
that purpose only. The same device replaces the reducibility of `HomologicalComplex.single`,
which is made `implicit_reducible` locally for the degree-zero comparisons in
`productResolutionMap_f_zero_π` and `productResolutionMap_quasiIsoAt_zero`.

## References

* [Stacks Project, Tag 0BKS](https://stacks.math.columbia.edu/tag/0BKS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.SpaceInverseLimits

/-- The derived category of sheaves of modules on a ringed space, constructed as the standard
localization of the homotopy category. -/
noncomputable local instance modulesHasDerivedCategory (X : RingedSpace.{u, u}) :
    HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  HasDerivedCategory.standard _

/-- The inverse system of abelian groups obtained by evaluating an inverse system of modules on
an open subset. -/
public noncomputable abbrev sectionsSystem (X : RingedSpace.{u, u})
    (F : Functor ℕᵒᵖ (SheafOfModules.{u} (structureSheafRing X))) (U : Opens X.carrier) :
    Functor ℕᵒᵖ AddCommGrpCat.{u} :=
  F ⋙ SheafOfModules.toSheaf (structureSheafRing X) ⋙
    (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj (op U)

/-- The standard difference endomorphism `(aₙ) ↦ (aₙ - fₙ₊₁(aₙ₊₁))` of the product
of a countable inverse system of abelian groups. Its cokernel is `R¹ lim`. -/
public noncomputable def inverseLimitDifference (G : Functor ℕᵒᵖ AddCommGrpCat.{u}) :
    (∏ᶜ fun n : ℕ => G.obj ⟨n⟩) ⟶ (∏ᶜ fun n : ℕ => G.obj ⟨n⟩) :=
  Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => G.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ => G.obj ⟨n⟩) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op

attribute [local implicit_reducible] HomologicalComplex.single


private local instance sections_preservesLimits (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    PreservesLimitsOfSize.{u, u}
      (secF (structureSheafRing X) U :
        SheafOfModules.{u} (structureSheafRing X) ⥤ AddCommGrpCat.{u}) := by
  change PreservesLimitsOfSize.{u, u}
    (SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
      forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat.{u})
  infer_instance

private local instance sections_preservesProducts (X : RingedSpace.{u, u})
    (U : Opens X.carrier) : PreservesLimitsOfShape (Discrete ℕ)
      (secF (structureSheafRing X) U :
        SheafOfModules.{u} (structureSheafRing X) ⥤ AddCommGrpCat.{u}) := by
  change PreservesLimitsOfShape (Discrete ℕ)
    (SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
      forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat.{u})
  infer_instance

private lemma epi_of_sections_epi_on_basis (X : RingedSpace.{u, u})
    {M N : SheafOfModules.{u} (structureSheafRing X)} (f : M ⟶ N)
    (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B)
    (hf : ∀ U ∈ B, Epi ((secF (structureSheafRing X) U).map f)) : Epi f := by
  apply (SheafOfModules.toSheaf.{u} (structureSheafRing X)).epi_of_epi_map
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi (X := X.carrier)
    ((SheafOfModules.toSheaf.{u} (structureSheafRing X)).map f)).mp
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U s x hx
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨V, hVU, ?_, hxV⟩
  exact (AddCommGrpCat.epi_iff_surjective _).mp (hf V hV) _

private lemma exact_of_sections_exact_on_basis (X : RingedSpace.{u, u})
    (S : ShortComplex (SheafOfModules.{u} (structureSheafRing X)))
    (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B)
    (hS : ∀ U ∈ B, (S.map (secF (structureSheafRing X) U)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_epi_toCycles]
  apply epi_of_sections_epi_on_basis X S.toCycles B hB
  intro U hU
  let G := secF (structureSheafRing X) U
  have : PreservesFiniteLimits G := inferInstance
  have : Epi (S.map G).toCycles := (hS U hU).epi_toCycles
  have heq : G.map S.toCycles =
      (S.map G).toCycles ≫ (mapCyclesIsoClean S G).hom := by
    apply (cancel_mono (G.map S.iCycles)).mp
    simp only [Category.assoc, mapCyclesIsoClean_hom_iCycles, ShortComplex.toCycles_i,
      ← G.map_comp]
    rfl
  rw [heq]
  infer_instance

/-! The generic inverse-limit material that used to be restated here -- the product of
injective resolutions, the product and K-injective preservation lemmas, and the three-term
inverse-limit sequence -- lives in
`StacksFrontier/Algebra/Homology/DerivedCategory/InverseLimitHelpers.lean`, which this file
already imports.  None of it mentions a site or a space. -/


/-- The product of injective resolutions of a countable family of modules, as an injective
resolution of the product: `CategoryTheory.productInjectiveResolution` with exactness of the
product complex in positive degrees supplied by testing it on the basis. -/
private def productInjectiveResolutionOfBasis (X : RingedSpace.{u, u})
    (M : ℕ → SheafOfModules.{u} (structureSheafRing X)) (I : ∀ n, InjectiveResolution (M n))
    (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B)
    (hcoh : ∀ U ∈ B, ∀ n p : ℕ, 0 < p → IsZero (Hgroup (structureSheafRing X) U p (M n))) :
    InjectiveResolution (∏ᶜ M) :=
  CategoryTheory.productInjectiveResolution M I fun q hq =>
    exact_of_sections_exact_on_basis X _ B hB fun U hU =>
      (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
        (isZero_homology_mapHomologicalComplex_productResolution
          (secF (structureSheafRing X) U) M I q (fun n => hcoh U hU n q hq))

private lemma isZero_cohomology_product_of_isBasis (X : RingedSpace.{u, u})
    (M : ℕ → SheafOfModules.{u} (structureSheafRing X))
    (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B)
    (hcoh : ∀ U ∈ B, ∀ n p : ℕ, 0 < p → IsZero (Hgroup (structureSheafRing X) U p (M n)))
    (U : Opens X.carrier) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup (structureSheafRing X) U p (∏ᶜ M)) := by
  let I := fun n => InjectiveResolution.of (M n)
  exact (isZero_homology_mapHomologicalComplex_productResolution
    (secF (structureSheafRing X) U) M I p
    (fun n => hcoh U hU n p hp)).of_iso
      ((productInjectiveResolutionOfBasis X M I B hB hcoh).isoRightDerivedObj
        (secF (structureSheafRing X) U) p)


private def singleExtendIso (A : Type*) [Category A] [Abelian A] :
    CochainComplex.single₀ A ⋙ ComplexShape.embeddingUpNat.extendFunctor A ≅
      CochainComplex.singleFunctor A 0 := by
  refine NatIso.ofComponents
    (fun M => HomologicalComplex.extendSingleIso _ M 0 0 (by simp)) ?_
  intro M N f
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.extendSingleIso_hom_f,
    Functor.comp_map, ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ))
      (by simp)]
  simp only [Functor.comp_obj, CochainComplex.single₀_obj_zero,
    CochainComplex.single₀_map_f_zero, CochainComplex.single₀ObjXSelf, Iso.refl_hom,
    Category.id_comp]
  exact (invHomCancel₁ _ _ _ _).trans (invHomCancel₂ _ _ _).symm

public lemma preservesProduct_single_of_isBasis (X : RingedSpace.{u, u})
    (M : ℕ → SheafOfModules.{u} (structureSheafRing X))
    (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B)
    (hcoh : ∀ U ∈ B, ∀ n p : ℕ, 0 < p → IsZero (Hgroup (structureSheafRing X) U p (M n))) :
    PreservesLimit (Discrete.functor M)
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0) := by
  let A := SheafOfModules.{u} (structureSheafRing X)
  let I := fun n => InjectiveResolution.of (M n)
  let E := ComplexShape.embeddingUpNat.extendFunctor A
  let T := E ⋙ DerivedCategory.Q
  let J := fun n => (I n).cocomplex
  let S := fun n => (CochainComplex.single₀ A).obj (M n)
  have : PreservesLimitsOfShape (Discrete ℕ) E := preservesProducts_extend
  have : ∀ n, CochainComplex.IsKInjective ((E.obj ∘ J) n) := by
    intro n
    change CochainComplex.IsKInjective (I n).cochainComplex
    exact CochainComplex.isKInjective_of_injective _ 0
  have : PreservesLimit (Discrete.functor (E.obj ∘ J)) DerivedCategory.Q :=
    preservesProduct_Q_of_isKInjective _
  have : PreservesLimit (Discrete.functor J) T := by
    have : PreservesLimit (Discrete.functor J ⋙ E) DerivedCategory.Q :=
      preservesLimit_of_iso_diagram _ (Discrete.compNatIsoDiscrete J E).symm
    exact comp_preservesLimit _ _
  have : IsIso (T.map (productResolutionMap M I)) := by
    have : QuasiIso (productResolutionMap M I) :=
      (productInjectiveResolutionOfBasis X M I B hB hcoh).quasiIso
    change IsIso (DerivedCategory.Q.map
      (HomologicalComplex.extendMap (productResolutionMap M I) ComplexShape.embeddingUpNat))
    infer_instance
  have hη : productResolutionMap M I =
      piComparison (CochainComplex.single₀ A) M ≫ Limits.Pi.map (fun n => (I n).ι) := by
    apply Pi.hom_ext
    intro n
    simp [productResolutionMap, piComparison_comp_π_assoc]
    rfl
  have : IsIso (T.map (Limits.Pi.map (fun n => (I n).ι))) := by
    have hi : IsIso (T.map (piComparison (CochainComplex.single₀ A) M) ≫
      T.map (Limits.Pi.map (fun n => (I n).ι))) := by
      rw [← T.map_comp, ← hη]
      infer_instance
    exact IsIso.of_isIso_comp_left (T.map (piComparison (CochainComplex.single₀ A) M)) _
  have : ∀ n, IsIso (T.map (I n).ι) := by
    intro n
    change IsIso (DerivedCategory.Q.map
      (HomologicalComplex.extendMap (I n).ι ComplexShape.embeddingUpNat))
    infer_instance
  have : IsIso (piComparison T S) := by
    have hnat := Stacks.DerivedProducts.piComparison_naturality T S J (fun n => (I n).ι)
    have : IsIso (piComparison T S ≫ Limits.Pi.map (fun n => T.map (I n).ι)) := by
      rw [hnat]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Limits.Pi.map (fun n => T.map (I n).ι))
  have : PreservesLimit (Discrete.functor ((CochainComplex.single₀ A).obj ∘ M)) T :=
    PreservesProduct.of_iso_comparison T S
  have : PreservesLimit (Discrete.functor M ⋙ CochainComplex.single₀ A) T :=
    preservesLimit_of_iso_diagram _ (Discrete.compNatIsoDiscrete M _).symm
  have : PreservesLimit (Discrete.functor M) (CochainComplex.single₀ A ⋙ T) :=
    comp_preservesLimit _ _
  exact preservesLimit_of_natIso (Discrete.functor M) ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (singleExtendIso A) DerivedCategory.Q ≪≫
      (DerivedCategory.singleFunctorIsoCompQ A 0).symm)



private lemma epi_sections_inverseLimitSequence_g (X : RingedSpace.{u, u})
    (F : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing X)) (U : Opens X.carrier)
    (h : Epi (inverseLimitDifference (sectionsSystem X F U))) :
    Epi ((secF (structureSheafRing X) U).map (inverseLimitSequence F).g) := by
  let G := secF (structureSheafRing X) U
  have : Epi (inverseLimitSequence (F ⋙ G)).g := h
  have : Epi (G.map (inverseLimitSequence F).g ≫
      piComparison G (fun n : ℕ => F.obj ⟨n⟩)) := by
    rw [map_inverseLimitSequence_g]
    change Epi (piComparison G _ ≫ inverseLimitDifference (sectionsSystem X F U))
    infer_instance
  exact (epi_comp_iff_of_isIso _
    (piComparison G (fun n : ℕ => F.obj ⟨n⟩))).mp inferInstance

private lemma inverseLimitSequence_shortExact_of_isBasis (X : RingedSpace.{u, u})
    (F : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing X))
    (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B)
    (h : ∀ U ∈ B, Epi (inverseLimitDifference (sectionsSystem X F U))) :
    (inverseLimitSequence F).ShortExact where
  exact := (inverseLimitSequence_exact_and_mono F).1
  mono_f := (inverseLimitSequence_exact_and_mono F).2
  epi_g := epi_of_sections_epi_on_basis X _ B hB fun U hU =>
    epi_sections_inverseLimitSequence_g X F U (h U hU)

/-- The distinguished triangle for the limit in degree zero, shared by the two derived-limit
statements below; `G` is the degree-zero embedding. -/
private lemma exists_distTriang_single_limit_aux (X : RingedSpace.{u, u})
    (F : Functor ℕᵒᵖ (SheafOfModules.{u} (structureSheafRing X)))
    (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B)
    (hcoh : ∀ U ∈ B, ∀ n p : ℕ, 0 < p →
      IsZero (Hgroup (structureSheafRing X) U p (F.obj ⟨n⟩)))
    (hlimOne : ∀ U ∈ B, Epi (inverseLimitDifference (sectionsSystem X F U)))
    (G : SheafOfModules.{u} (structureSheafRing X) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hG : G = DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0) :
    ∃ h : HasProduct (fun n : ℕ => (F ⋙ G).obj ⟨n⟩), letI := h
      ∃ p : G.obj (limit F) ⟶ ∏ᶜ fun n : ℕ => (F ⋙ G).obj ⟨n⟩,
        (∀ n : ℕ, p ≫ Pi.π (fun n : ℕ => (F ⋙ G).obj ⟨n⟩) n = G.map (limit.π F ⟨n⟩)) ∧
        ∃ δ : (∏ᶜ fun n : ℕ => (F ⋙ G).obj ⟨n⟩) ⟶ (G.obj (limit F))⟦(1 : ℤ)⟧,
          Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => (F ⋙ G).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ => (F ⋙ G).obj ⟨n⟩) (n + 1) ≫
              (F ⋙ G).map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang _ := by
  subst hG
  let G := DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0
  let M := fun n : ℕ => F.obj ⟨n⟩
  have : PreservesLimit (Discrete.functor M) G :=
    preservesProduct_single_of_isBasis X M B hB hcoh
  have : HasProduct (fun n : ℕ => G.obj (M n)) :=
    hasLimit_of_iso (Discrete.compNatIsoDiscrete M G)
  refine ⟨inferInstance, ?_⟩
  let S := inverseLimitSequence F
  have hS : S.ShortExact := inverseLimitSequence_shortExact_of_isBasis X F B hB hlimOne
  let e := PreservesProduct.iso G M
  let d := Pi.lift (fun n : ℕ => Pi.π (fun n : ℕ => G.obj (M n)) n -
    Pi.π (fun n : ℕ => G.obj (M n)) (n + 1) ≫
      G.map (F.map (homOfLE (Nat.le_succ n)).op))
  have he : G.map S.g ≫ e.hom = e.hom ≫ d := map_inverseLimitSequence_g F G
  let Sf : limit F ⟶ ∏ᶜ M := S.f
  have hleg : ∀ n : ℕ,
      (G.map Sf ≫ piComparison G M) ≫ Pi.π (fun n : ℕ => G.obj (M n)) n =
        G.map (limit.π F ⟨n⟩) := by
    intro n
    have hπ : Sf ≫ Pi.π M n = limit.π F ⟨n⟩ :=
      Pi.lift_comp_π (fun k : ℕ => limit.π F ⟨k⟩) n
    rw [Category.assoc, piComparison_comp_π, ← G.map_comp, hπ]
  refine ⟨G.map S.f ≫ e.hom, hleg, e.inv ≫ hS.singleδ, ?_⟩
  apply isomorphic_distinguished _ hS.singleTriangle_distinguished
  refine Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_
  · exact homInvCancelId (G.map S.f) e
  · dsimp
    apply (cancel_mono e.hom).mp
    exact (invHomCancel₃ d e).trans (((Category.assoc e.inv (G.map S.g) e.hom).trans
      ((congrArg (fun m => e.inv ≫ m) he).trans (Iso.inv_hom_id_assoc e d))).symm)
  · exact comp_map_id _ _

/-- If the terms of a countable inverse system of modules are acyclic on a basis and `R¹ lim`
of their sections vanishes there, then the ordinary limit, placed in degree zero, is a derived
inverse limit of the system. -/
@[stacks 0BKS "derived limit"]
public theorem isDerivedLimit_single_limit_of_isBasis (X : RingedSpace.{u, u})
    (F : Functor ℕᵒᵖ (SheafOfModules.{u} (structureSheafRing X)))
    (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B)
    (hcoh : ∀ U ∈ B, ∀ n p : ℕ, 0 < p →
      IsZero (Hgroup (structureSheafRing X) U p (F.obj ⟨n⟩)))
    (hlimOne : ∀ U ∈ B, Epi (inverseLimitDifference (sectionsSystem X F U))) :
    ∃ h : HasProduct (fun n : ℕ =>
        (F ⋙ DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj ⟨n⟩),
      @IsDerivedLimit (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) _ _ _ _ _ _
        (F ⋙ DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0) h
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
          (limit F)) := by
  obtain ⟨h, p, -, δ, hδ⟩ := exists_distTriang_single_limit_aux X F B hB hcoh hlimOne _ rfl
  exact ⟨h, p, δ, hδ⟩

/-- The derived-limit triangle of `isDerivedLimit_single_limit_of_isBasis` with its structural
morphism named: under the same hypotheses the ordinary inverse limit, placed in degree zero,
sits in the defining triangle through a morphism whose component at `n` is the image of the
limit projection `lim Fₙ ⟶ Fₙ`.

`CategoryTheory.Pretriangulated.IsDerivedLimit` quantifies over that morphism, so which one the
triangle carries cannot be recovered from `isDerivedLimit_single_limit_of_isBasis`. A consumer
that needs to know it — one identifying the projection of the Milnor sequence with the canonical
comparison `H(lim Fₙ) ⟶ lim H(Fₙ)`, for instance — uses this form instead. -/
public theorem exists_distTriang_single_limit_of_isBasis (X : RingedSpace.{u, u})
    (F : Functor ℕᵒᵖ (SheafOfModules.{u} (structureSheafRing X)))
    (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B)
    (hcoh : ∀ U ∈ B, ∀ n p : ℕ, 0 < p →
      IsZero (Hgroup (structureSheafRing X) U p (F.obj ⟨n⟩)))
    (hlimOne : ∀ U ∈ B, Epi (inverseLimitDifference (sectionsSystem X F U))) :
    ∃ h : HasProduct (fun n : ℕ =>
        (F ⋙ DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj ⟨n⟩),
      letI := h
      ∃ p : (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
            (limit F) ⟶
          ∏ᶜ fun n : ℕ => (F ⋙ DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).obj ⟨n⟩,
        (∀ n : ℕ, p ≫ Pi.π (fun n : ℕ => (F ⋙ DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).obj ⟨n⟩) n =
            (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map
              (limit.π F ⟨n⟩)) ∧
          ∃ δ : (∏ᶜ fun n : ℕ => (F ⋙ DerivedCategory.singleFunctor
                (SheafOfModules.{u} (structureSheafRing X)) 0).obj ⟨n⟩) ⟶
              ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
                (limit F))⟦(1 : ℤ)⟧,
            Triangle.mk p (Pi.lift fun n : ℕ =>
                Pi.π (fun n : ℕ => (F ⋙ DerivedCategory.singleFunctor
                    (SheafOfModules.{u} (structureSheafRing X)) 0).obj ⟨n⟩) n -
                  Pi.π (fun n : ℕ => (F ⋙ DerivedCategory.singleFunctor
                      (SheafOfModules.{u} (structureSheafRing X)) 0).obj ⟨n⟩) (n + 1) ≫
                    (F ⋙ DerivedCategory.singleFunctor
                      (SheafOfModules.{u} (structureSheafRing X)) 0).map
                        (homOfLE (Nat.le_succ n)).op) δ ∈
              distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :=
  exists_distTriang_single_limit_aux X F B hB hcoh hlimOne _ rfl

/-! ### The right derived functor helpers used below

`CategoryTheory.rightDerivedPlusObjIso`, `CategoryTheory.rightAcyclic_iff_isZero_rightDerived`
and `CategoryTheory.isZero_rightDerived_kernel` are stated once, in
`Algebra/Homology/DerivedCategory/InverseLimitHelpers.lean`, which this file imports. -/

/-- Under the same hypotheses, the ordinary inverse limit has vanishing positive-degree
cohomology on every member of the basis. -/
@[stacks 0BKS "higher cohomology"]
public theorem isZero_cohomology_limit_of_isBasis (X : RingedSpace.{u, u})
    (F : Functor ℕᵒᵖ (SheafOfModules.{u} (structureSheafRing X)))
    (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B)
    (hcoh : ∀ U ∈ B, ∀ n p : ℕ, 0 < p →
      IsZero (Hgroup (structureSheafRing X) U p (F.obj ⟨n⟩)))
    (hlimOne : ∀ U ∈ B, Epi (inverseLimitDifference (sectionsSystem X F U)))
    (U : Opens X.carrier) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup (structureSheafRing X) U p (limit F)) := by
  let : HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _
  let S := inverseLimitSequence F
  have hS : S.ShortExact := inverseLimitSequence_shortExact_of_isBasis X F B hB hlimOne
  have hprod : ∀ q : ℕ, 0 < q →
      IsZero (Hgroup (structureSheafRing X) U q (∏ᶜ fun n : ℕ => F.obj ⟨n⟩)) :=
    fun q hq => isZero_cohomology_product_of_isBasis X _ B hB hcoh U hU q hq
  exact CategoryTheory.isZero_rightDerived_kernel (secF (structureSheafRing X) U) S hS
    (epi_sections_inverseLimitSequence_g X F U (hlimOne U hU)) hprod hprod p hp

end Stacks.Cohomology.SpaceInverseLimits

end
