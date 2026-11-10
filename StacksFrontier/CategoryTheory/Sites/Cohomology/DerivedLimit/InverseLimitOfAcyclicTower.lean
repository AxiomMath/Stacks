module

public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import Mathlib.Algebra.Category.Grp.AB
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.HomComplexAugmentation
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimBasic
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
import StacksCore.Tactic.StacksAttribute

/-!
# Inverse limits of an acyclic tower of modules on a ringed site

Let `(Fₙ)` be a countable inverse system of modules on a ringed site `(C, O)` and let `B` be a
class of objects such that every object of `C` has a covering by members of `B`. If each `Fₙ` is
acyclic on every member of `B` and the first derived inverse limit of the sections over each
member of `B` vanishes, then the ordinary inverse limit `lim Fₙ` represents the derived inverse
limit `R lim Fₙ`, and `lim Fₙ` is itself acyclic on every member of `B`.

## Main definitions

* `Stacks.Cohomology.SiteInverseLimits.sectionsFunctor` takes the sections of a module over an
  object of the site as an abelian group.
* `Stacks.Cohomology.SiteInverseLimits.sectionsSystem` evaluates an inverse system of modules on
  an object of the site, giving an inverse system of abelian groups.

## Main results

* `Stacks.Cohomology.SiteInverseLimits.isDerivedLimit_single_limit_of_acyclic_cover` identifies
  the ordinary inverse limit with the derived inverse limit.
* `Stacks.Cohomology.SiteInverseLimits.isZero_cohomology_limit_of_acyclic_cover` gives the
  resulting higher-cohomology vanishing on the members of the covering class.

## Implementation notes

The covering class `B` is an `ObjectProperty` of the underlying category and the condition that
every object has a covering by its members is `GrothendieckTopology.HasEnoughObjects`. Cohomology
`H^p(U, F)` is the right derived functor of the abelian-group-valued sections functor over `U`.
For a countable inverse system of abelian groups, `R¹ lim` is the cokernel
of the difference map `1 - shift` on the product, which is `Rlim.firstDerivedLimit`. The first
conclusion is expressed by saying that the ordinary limit, placed in degree zero, satisfies the
defining `IsDerivedLimit` distinguished-triangle predicate, with the existence of the product in
the derived category part of the assertion rather than a hypothesis. The two independent
conclusions of the source are separate declarations.

The site objects, site morphisms, structure rings and modules carry independent universes.
Sheafification of abelian-group-valued presheaves in the module universe, and Grothendieck
abelianness of the modules, are instance arguments as in the surrounding development; at
`RingedSite.{u, u, u}` with modules in `u` both are supplied by Mathlib, so nothing is added to
the hypotheses of the source.

Several steps compare a cochain complex indexed by `ℕ` with its extension by zero to `ℤ`, where
the identification of degree-zero objects is definitional but not available at the transparency
level `rw` and `simp` work at. Those steps state the needed cancellation as a small lemma about
abstract isomorphisms and close the goal with `exact`, whose definitional check runs at default
transparency; `invHomCancel₁` through `comp_map_id` exist for that purpose only.

## References

* [Stacks Project, Tag 0BKY](https://stacks.math.columbia.edu/tag/0BKY)
* [Stacks Project, Tag 0BKS](https://stacks.math.columbia.edu/tag/0BKS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite

universe u v w z g

namespace Stacks.Cohomology.SiteInverseLimits

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, v, w})

section Instances

variable [HasSheafify X.J AddCommGrpCat.{z}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- Sheaves of modules on a ringed site have enough injectives, being Grothendieck abelian. -/
local instance modulesEnoughInjectives :
    EnoughInjectives (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  IsGrothendieckAbelian.enoughInjectives.{g}

end Instances

/-- The sections over an object of a ringed site, as a functor from modules to abelian groups. -/
abbrev sectionsFunctor (U : X.C) :
    SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤ AddCommGrpCat.{z} :=
  SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U) ⋙
    forget₂ (ModuleCat.{z, w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
      AddCommGrpCat.{z}

/-- The inverse system of abelian groups obtained by evaluating an inverse system of modules on
an object of the site. -/
abbrev sectionsSystem
    (F : ℕᵒᵖ ⥤ SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{z} :=
  F ⋙ sectionsFunctor X U

private instance evaluation_additive (U : X.C) :
    (SheafOfModules.evaluation.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
  Stacks.SheafOfModules.evaluationAdditive.{z}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (op U)

private instance evaluation_preservesFiniteLimits (U : X.C) :
    PreservesFiniteLimits
      (SheafOfModules.evaluation.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) :=
  SheafOfModules.Finite.evaluationPreservesFiniteLimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (op U)

private instance evaluation_preservesLimitsOfShape_discrete (U : X.C) :
    PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.evaluation.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) :=
  SheafOfModules.evaluationPreservesLimitsOfShape.{z}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (D := Discrete ℕ) (op U)

/-! The generic inverse-limit material -- the product of injective resolutions, the product and
K-injective preservation lemmas, and the three-term inverse-limit sequence -- lives in
`StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers`, which this file already
imports.  None of it mentions a site or a space. -/


section Cover

variable [HasSheafify X.J AddCommGrpCat.{z}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

omit [HasSheafify X.J AddCommGrpCat.{z}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
private lemma epi_of_sections_epi_on_cover
    {M N : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : M ⟶ N)
    (B : ObjectProperty X.C) (hB : X.J.HasEnoughObjects B)
    (hf : ∀ U, B U → Epi ((sectionsFunctor.{u, v, w, z} X U).map f)) : Epi f := by
  let T := SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let φ := T.map f
  have hsurj : ∀ ⦃U : X.C⦄, B U →
      Function.Surjective (ConcreteCategory.hom (φ.hom.app (op U))) := fun U hU =>
    (AddCommGrpCat.epi_iff_surjective ((sectionsFunctor.{u, v, w, z} X U).map f)).mp (hf U hU)
  have hl : Presheaf.IsLocallySurjective X.J
      ((sheafToPresheaf X.J AddCommGrpCat.{z}).map φ) :=
    Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective X.J _ hB hsurj
  let _ : Sheaf.IsLocallySurjective φ := hl
  have : Epi φ := Sheaf.epi_of_isLocallySurjective φ
  refine ⟨fun g h hgh => ?_⟩
  apply T.map_injective
  apply (cancel_epi φ).1
  simpa [T, φ] using congrArg T.map hgh

omit [IsGrothendieckAbelian.{g}
  (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
private lemma exact_of_sections_exact_on_cover
    (S : ShortComplex (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (B : ObjectProperty X.C) (hB : X.J.HasEnoughObjects B)
    (hS : ∀ U, B U →
      letI : (SheafOfModules.evaluation.{z}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
        Stacks.SheafOfModules.evaluationAdditive.{z}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (op U);
      (S.map (sectionsFunctor.{u, v, w, z} X U)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_epi_toCycles]
  apply epi_of_sections_epi_on_cover X S.toCycles B hB
  intro U hU
  let G := sectionsFunctor.{u, v, w, z} X U
  have : PreservesFiniteLimits G := inferInstance
  have : Epi (S.map G).toCycles := (hS U hU).epi_toCycles
  have heq : G.map S.toCycles = (S.map G).toCycles ≫ (mapCyclesIsoClean S G).hom := by
    apply (cancel_mono (G.map S.iCycles)).mp
    simp only [Category.assoc, mapCyclesIsoClean_hom_iCycles, ShortComplex.toCycles_i,
      ← G.map_comp]
    rfl
  rw [heq]
  infer_instance

/-- The product of injective resolutions of a countable family of modules, as an injective
resolution of the product: `CategoryTheory.productInjectiveResolution` with exactness of the
product complex in positive degrees supplied by testing it on the covering class. -/
private def productInjectiveResolutionOnCover
    (M : ℕ → SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (I : ∀ n, InjectiveResolution (M n))
    (B : ObjectProperty X.C) (hB : X.J.HasEnoughObjects B)
    (hcoh : ∀ U, B U →
      letI : (SheafOfModules.evaluation.{z}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
        Stacks.SheafOfModules.evaluationAdditive.{z}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (op U);
      ∀ n p : ℕ, 0 < p →
      IsZero (((sectionsFunctor.{u, v, w, z} X U).rightDerived p).obj (M n))) :
    InjectiveResolution (∏ᶜ M) :=
  CategoryTheory.productInjectiveResolution M I fun q hq =>
    exact_of_sections_exact_on_cover X _ B hB fun U hU =>
      (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
        (isZero_homology_mapHomologicalComplex_productResolution
          (sectionsFunctor.{u, v, w, z} X U) M I q (fun n => hcoh U hU n q hq))

private lemma isZero_cohomology_product_on_cover
    (M : ℕ → SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : ObjectProperty X.C) (hB : X.J.HasEnoughObjects B)
    (hcoh : ∀ U, B U →
      letI : (SheafOfModules.evaluation.{z}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
        Stacks.SheafOfModules.evaluationAdditive.{z}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (op U);
      ∀ n p : ℕ, 0 < p →
      IsZero (((sectionsFunctor.{u, v, w, z} X U).rightDerived p).obj (M n)))
    (U : X.C) (hU : B U) (p : ℕ) (hp : 0 < p) :
    letI : (SheafOfModules.evaluation.{z}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
      Stacks.SheafOfModules.evaluationAdditive.{z}
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (op U);
    IsZero (((sectionsFunctor.{u, v, w, z} X U).rightDerived p).obj (∏ᶜ M)) := by
  let I := fun n => InjectiveResolution.of (M n)
  exact (isZero_homology_mapHomologicalComplex_productResolution
    (sectionsFunctor.{u, v, w, z} X U) M I p
    (fun n => hcoh U hU n p hp)).of_iso
      ((productInjectiveResolutionOnCover X M I B hB hcoh).isoRightDerivedObj
        (sectionsFunctor.{u, v, w, z} X U) p)

end Cover


section Cover2

variable [HasSheafify X.J AddCommGrpCat.{z}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

private lemma preservesProduct_single_of_acyclic_cover
    (M : ℕ → SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : ObjectProperty X.C) (hB : X.J.HasEnoughObjects B)
    (hcoh : ∀ U, B U →
      letI : (SheafOfModules.evaluation.{z}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
        Stacks.SheafOfModules.evaluationAdditive.{z}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (op U);
      ∀ n p : ℕ, 0 < p →
      IsZero (((sectionsFunctor.{u, v, w, z} X U).rightDerived p).obj (M n))) :
    PreservesLimit (Discrete.functor M)
      (DerivedCategory.singleFunctor
        (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0) := by
  let A := SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
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
      (productInjectiveResolutionOnCover X M I B hB hcoh).quasiIso
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
    Functor.isoWhiskerRight
        (ComplexShape.Embedding.singleUpNatCompExtendFunctorIso A) DerivedCategory.Q ≪≫
      (DerivedCategory.singleFunctorIsoCompQ A 0).symm)

end Cover2


section Cover3

variable [HasSheafify X.J AddCommGrpCat.{z}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

omit [HasSheafify X.J AddCommGrpCat.{z}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
private lemma epi_sectionsFunctor_inverseLimitSequence_g
    (F : ℕᵒᵖ ⥤ SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (h : Epi (Rlim.delta (sectionsSystem.{u, v, w, z} X F U))) :
    Epi ((sectionsFunctor.{u, v, w, z} X U).map (inverseLimitSequence F).g) := by
  let G := sectionsFunctor.{u, v, w, z} X U
  have hdiff : Epi (Pi.lift (fun n : ℕ => Pi.π (fun n : ℕ => (F ⋙ G).obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => (F ⋙ G).obj ⟨n⟩) (n + 1) ≫
        (F ⋙ G).map (homOfLE (Nat.le_succ n)).op)) := by
    rw [← Rlim.delta_eq_lift (F ⋙ G)]
    exact h
  have : Epi (G.map (inverseLimitSequence F).g ≫
      piComparison G (fun n : ℕ => F.obj ⟨n⟩)) := by
    rw [map_inverseLimitSequence_g]
    change Epi (piComparison G _ ≫ Pi.lift (fun n : ℕ =>
      Pi.π (fun n : ℕ => (F ⋙ G).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => (F ⋙ G).obj ⟨n⟩) (n + 1) ≫
          (F ⋙ G).map (homOfLE (Nat.le_succ n)).op))
    exact epi_comp' inferInstance hdiff
  exact (epi_comp_iff_of_isIso _ (piComparison G (fun n : ℕ => F.obj ⟨n⟩))).mp inferInstance

omit [IsGrothendieckAbelian.{g}
  (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
private lemma inverseLimitSequence_shortExact_of_cover
    (F : ℕᵒᵖ ⥤ SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : ObjectProperty X.C) (hB : X.J.HasEnoughObjects B)
    (h : ∀ U, B U → Epi (Rlim.delta (sectionsSystem.{u, v, w, z} X F U))) :
    (inverseLimitSequence F).ShortExact where
  exact := (inverseLimitSequence_exact_and_mono F).1
  mono_f := (inverseLimitSequence_exact_and_mono F).2
  epi_g := epi_of_sections_epi_on_cover X _ B hB fun U hU =>
    epi_sectionsFunctor_inverseLimitSequence_g X F U (h U hU)

/-- If the terms of a countable inverse system of modules on a ringed site are acyclic on a class
of objects covering every object, and the first derived inverse limit of their sections vanishes
there, then the ordinary inverse limit, placed in degree zero, is a derived inverse limit of the
system. -/
@[stacks 0BKY "ordinary limit is a derived limit"]
theorem isDerivedLimit_single_limit_of_acyclic_cover
    (F : ℕᵒᵖ ⥤ SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : ObjectProperty X.C) (hB : X.J.HasEnoughObjects B)
    (hcoh : ∀ U, B U →
      letI : (SheafOfModules.evaluation.{z}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
        Stacks.SheafOfModules.evaluationAdditive.{z}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (op U);
      ∀ n p : ℕ, 0 < p →
      IsZero (((sectionsFunctor.{u, v, w, z} X U).rightDerived p).obj (F.obj ⟨n⟩)))
    (hlimOne : ∀ U, B U →
      IsZero (Rlim.firstDerivedLimit (sectionsSystem.{u, v, w, z} X F U))) :
    ∃ h : HasProduct (fun n : ℕ =>
        (F ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj ⟨n⟩),
      @IsDerivedLimit
        (DerivedCategory (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        _ _ _ _ _ _
        (F ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0) h
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          (limit F)) := by
  let A := SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let G := DerivedCategory.singleFunctor A 0
  let M := fun n : ℕ => F.obj ⟨n⟩
  have : PreservesLimit (Discrete.functor M) G :=
    preservesProduct_single_of_acyclic_cover X M B hB hcoh
  have : HasProduct (fun n : ℕ => G.obj (M n)) :=
    hasLimit_of_iso (Discrete.compNatIsoDiscrete M G)
  refine ⟨inferInstance, ?_⟩
  let S := inverseLimitSequence F
  have hS : S.ShortExact := inverseLimitSequence_shortExact_of_cover X F B hB fun U hU =>
    (Preadditive.epi_iff_isZero_cokernel _).2 (hlimOne U hU)
  let e := PreservesProduct.iso G M
  let d := Pi.lift (fun n : ℕ => Pi.π (fun n : ℕ => G.obj (M n)) n -
    Pi.π (fun n : ℕ => G.obj (M n)) (n + 1) ≫
      G.map (F.map (homOfLE (Nat.le_succ n)).op))
  have he : G.map S.g ≫ e.hom = e.hom ≫ d := map_inverseLimitSequence_g F G
  refine ⟨G.map S.f ≫ e.hom, e.inv ≫ hS.singleδ, ?_⟩
  apply isomorphic_distinguished _ hS.singleTriangle_distinguished
  refine Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_
  · exact homInvCancelId (G.map S.f) e
  · dsimp
    apply (cancel_mono e.hom).mp
    exact (invHomCancel₃ d e).trans (((Category.assoc e.inv (G.map S.g) e.hom).trans
      ((congrArg (fun m => e.inv ≫ m) he).trans (Iso.inv_hom_id_assoc e d))).symm)
  · exact comp_map_id _ _

end Cover3

/-! ### The right derived functor helpers used below

`CategoryTheory.rightDerivedPlusObjIso`, `CategoryTheory.rightAcyclic_iff_isZero_rightDerived`
and `CategoryTheory.isZero_rightDerived_kernel` are stated once, in
`StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers`, which this file imports. -/

section Cover4

variable [HasSheafify X.J AddCommGrpCat.{z}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- Under the same hypotheses, the ordinary inverse limit has vanishing positive-degree
cohomology on every member of the covering class. -/
@[stacks 0BKY "acyclicity of the ordinary limit"]
theorem isZero_cohomology_limit_of_acyclic_cover
    (F : ℕᵒᵖ ⥤ SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : ObjectProperty X.C) (hB : X.J.HasEnoughObjects B)
    (hcoh : ∀ U, B U →
      letI : (SheafOfModules.evaluation.{z}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
        Stacks.SheafOfModules.evaluationAdditive.{z}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (op U);
      ∀ n p : ℕ, 0 < p →
      IsZero (((sectionsFunctor.{u, v, w, z} X U).rightDerived p).obj (F.obj ⟨n⟩)))
    (hlimOne : ∀ U, B U →
      IsZero (Rlim.firstDerivedLimit (sectionsSystem.{u, v, w, z} X F U)))
    (U : X.C) (hU : B U) (p : ℕ) (hp : 0 < p) :
    letI : (SheafOfModules.evaluation.{z}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
      Stacks.SheafOfModules.evaluationAdditive.{z}
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (op U);
    IsZero (((sectionsFunctor.{u, v, w, z} X U).rightDerived p).obj (limit F)) := by
  let S := inverseLimitSequence F
  have hDelta (V : X.C) (hV : B V) :
      Epi (Rlim.delta (sectionsSystem.{u, v, w, z} X F V)) :=
    (Preadditive.epi_iff_isZero_cokernel _).2 (hlimOne V hV)
  have hS : S.ShortExact := inverseLimitSequence_shortExact_of_cover X F B hB hDelta
  have hprod : ∀ q : ℕ, 0 < q →
      IsZero (((sectionsFunctor.{u, v, w, z} X U).rightDerived q).obj
        (∏ᶜ fun n : ℕ => F.obj ⟨n⟩)) :=
    isZero_cohomology_product_on_cover X _ B hB hcoh U hU
  exact CategoryTheory.isZero_rightDerived_kernel (sectionsFunctor.{u, v, w, z} X U) S hS
    (epi_sectionsFunctor_inverseLimitSequence_g X F U (hDelta U hU)) hprod hprod p hp

end Cover4

end Stacks.Cohomology.SiteInverseLimits

end
