module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.CategoryTheory.Center.Linear
public import StacksFrontier.Algebra.Homology.HomologyFunctorLinear
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.FilteredKInjectiveResolution

/-!
# Annihilation of hypercohomology by a global function that kills the complex

Let `(X, 𝒪_X)` be a ringed space and `r ∈ Γ(X, 𝒪_X)`. If multiplication by `r` is the *zero*
endomorphism of every term of a complex `K^•` of `𝒪_X`-modules, then `r` annihilates every
hypercohomology module `H^n(X, K^•)`.

Functoriality of hypercohomology alone does not give this. It gives that the map induced by the
zero endomorphism is zero; what has to be added is that the induced map *is* multiplication by
`r` on the `Γ(X, 𝒪_X)`-module `H^n(X, K^•)`, and the derived global-sections functor computing
that module is given only by its universal property, with no linear structure attached. The
bridge is `Stacks.Cohomology.FilteredComplex.hypercohomologyIsoGlobalSectionsHomology`: at a
K-injective complex hypercohomology *is* the cohomology of the complex of global sections, where
multiplication by `r` is multiplication by `r` degreewise and homology is `Γ(X, 𝒪_X)`-linear. So
the statement is proved on a K-injective resolution of `K^•` and transported back along the
comparison, which is an isomorphism because the resolution is a quasi-isomorphism.

Multiplication by `r` enters as an element `η` of the centre `End (𝟭 Mod(𝒪_X))` of the category
of module sheaves together with the hypothesis that it acts on *global* sections by `r`;
`Stacks.SheafOfModules.terminalSectionToEnd` is that element, and
`Stacks.SheafOfModules.terminalSectionToEnd_apply` that hypothesis. Working with the centre
rather than with a `CategoryTheory.Linear` structure on module sheaves keeps the statement free
of a choice of linear structure, and the scalar action of the centre on morphisms — which is
what makes `η • 𝟙 K` a map of complexes, natural in the complex — is recovered inside the proof
from `CategoryTheory.Linear.ofRingMorphism`, exactly as in
`Stacks.RegularSequence.comp_mk₀_center_eq_zero`.

Nothing here assumes the derived global-sections functor is additive: the one morphism whose
vanishing is needed, the image of the zero endomorphism of the resolution, is shown to vanish
through the same comparison isomorphism.

## Main results

* `Stacks.Cohomology.FilteredComplex.homologyMap_globalSections_center_smul_id`: on global
  sections, a central endomorphism acting by `r` induces multiplication by `r` on the cohomology
  of the complex of global sections.
* `Stacks.Cohomology.FilteredComplex.smul_id_hypercohomology_eq_zero` and
  `Stacks.Cohomology.FilteredComplex.mem_annihilator_hypercohomology_of_center_app_eq_zero`:
  **a global function killing every term of a complex annihilates its hypercohomology**, in
  morphism and in element form.

## References

* [Stacks Project, Tag 0BKK](https://stacks.math.columbia.edu/tag/0BKK)
* [Stacks Project, Tag 0GA0](https://stacks.math.columbia.edu/tag/0GA0)
* [Stacks Project, Tag 0GA1](https://stacks.math.columbia.edu/tag/0GA1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

universe u

/-! ### Homology of complexes in a linear category is linear -/

/-- **A scalar acting as zero on an object of a linear category acts as zero on every isomorphic
object.** -/
theorem CategoryTheory.Linear.smul_id_eq_zero_of_iso {R : Type*} [Semiring R] {C : Type*}
    [Category* C] [Preadditive C] [CategoryTheory.Linear R C] {M N : C} (e : M ≅ N) {r : R}
    (h : r • 𝟙 N = 0) : r • 𝟙 M = 0 := by
  rw [← cancel_mono e.hom, CategoryTheory.Linear.smul_comp, Category.id_comp,
    Limits.zero_comp, ← Category.comp_id e.hom, ← CategoryTheory.Linear.comp_smul, h,
    Limits.comp_zero]

/-- **An element of the centre vanishing at an object vanishes at every isomorphic object.** -/
theorem CategoryTheory.CatCenter.app_eq_zero_of_iso {C : Type*} [Category* C] [Preadditive C]
    (η : CatCenter C) {M N : C} (e : M ≅ N) (h : η.app N = 0) : η.app M = 0 := by
  rw [← cancel_mono e.hom, ← η.naturality e.hom, h, Limits.comp_zero, Limits.zero_comp]

namespace Stacks.Cohomology.FilteredComplex

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-- The sections of `structureSheafRing X` are commutative rings (instance search no longer
unfolds the `⋙ forget₂ CommRingCat RingCat` in its definition). -/
local instance (U : (Opens X.carrier)ᵒᵖ) : CommRing ((structureSheafRing X).obj.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

/-! ### Multiplication by a global function on the complex of global sections -/

section

variable (η : CatCenter (SheafOfModules.{u} (structureSheafRing X)))
  (r : (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))
  (hη : ∀ (M : SheafOfModules.{u} (structureSheafRing X)) (x : M.val.obj (op ⊤)),
    (η.app M).val.app (op ⊤) x = r • x)

include hη

/-- **Global sections carry a central endomorphism acting by `r` to multiplication by `r`.**
The scalar action of the centre on a map of complexes is degreewise application of `η`, and on
global sections that is multiplication by `r` by hypothesis. -/
theorem globalSections_map_center_smul_id
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    letI : CategoryTheory.Linear (CatCenter (SheafOfModules.{u} (structureSheafRing X)))
      (SheafOfModules.{u} (structureSheafRing X)) :=
      CategoryTheory.Linear.ofRingMorphism (RingHom.id _)
    (globalSectionsComplexFunctor X).map (η • 𝟙 K) =
      r • 𝟙 ((globalSectionsComplexFunctor X).obj K) := by
  ext m : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change (η.app (K.X m)).val.app (op ⊤) _ = _
  exact hη (K.X m) x

/-- **On the cohomology of the complex of global sections, a central endomorphism acting by `r`
induces multiplication by `r`.** -/
theorem homologyMap_globalSections_center_smul_id
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℤ) :
    letI : CategoryTheory.Linear (CatCenter (SheafOfModules.{u} (structureSheafRing X)))
      (SheafOfModules.{u} (structureSheafRing X)) :=
      CategoryTheory.Linear.ofRingMorphism (RingHom.id _)
    HomologicalComplex.homologyMap ((globalSectionsComplexFunctor X).map (η • 𝟙 K)) n =
      r • 𝟙 (((globalSectionsComplexFunctor X).obj K).homology n) := by
  rw [globalSections_map_center_smul_id X η r hη K,
    show HomologicalComplex.homologyMap (r • 𝟙 ((globalSectionsComplexFunctor X).obj K)) n =
        r • HomologicalComplex.homologyMap (𝟙 ((globalSectionsComplexFunctor X).obj K)) n from
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).map_smul r (𝟙 _),
    HomologicalComplex.homologyMap_id]

end

/-! ### Annihilation of hypercohomology -/

section

variable (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
  (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)
  [RΓ.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]

include α

/-- **The map on hypercohomology induced by the zero endomorphism of a K-injective complex is
zero.** No additivity of `RΓ` is used: on a K-injective complex hypercohomology is the cohomology
of the complex of global sections, and *there* the zero endomorphism induces zero. -/
theorem hypercohomologyMap_zero_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] (n : ℤ) :
    hypercohomologyMap X RΓ (0 : I ⟶ I) n = 0 := by
  have h := hypercohomologyIsoGlobalSectionsHomology_naturality X RΓ α (0 : I ⟶ I) n
  rw [CategoryTheory.Functor.map_zero, HomologicalComplex.homologyMap_zero,
    Limits.comp_zero] at h
  exact (cancel_mono (hypercohomologyIsoGlobalSectionsHomology X RΓ α I n).hom).1
    (h.trans (Limits.zero_comp).symm)

variable (η : CatCenter (SheafOfModules.{u} (structureSheafRing X)))
  (r : (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))
  (hη : ∀ (M : SheafOfModules.{u} (structureSheafRing X)) (x : M.val.obj (op ⊤)),
    (η.app M).val.app (op ⊤) x = r • x)

include hη

/-- **A global function killing every term of a complex annihilates its hypercohomology**, in
morphism form: multiplication by `r` is the zero endomorphism of `H^n(X, K^•)`.

The proof passes to the K-injective resolution `K^• ⟶ I^•`. There `η • 𝟙` is carried by the
comparison with the complex of global sections to multiplication by `r`, while it is zero in the
derived category because it is zero already on `K^•` and the resolution is a quasi-isomorphism;
and the comparison transports that back to `K^•`. -/
theorem smul_id_hypercohomology_eq_zero
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hK : ∀ m : ℤ, η.app (K.X m) = 0) (n : ℤ) :
    r • 𝟙 (hypercohomology X RΓ K n) = 0 := by
  let : CategoryTheory.Linear (CatCenter (SheafOfModules.{u} (structureSheafRing X)))
    (SheafOfModules.{u} (structureSheafRing X)) :=
    CategoryTheory.Linear.ofRingMorphism (RingHom.id _)
  obtain ⟨I, j, hj, hIinj⟩ : ∃ (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
      (j : K ⟶ I), QuasiIso j ∧ I.IsKInjective :=
    ⟨(Stacks.Injectives.kInjectiveResolutionFunctor
        (SheafOfModules.{u} (structureSheafRing X))).obj K,
      (Stacks.Injectives.kInjectiveResolutionInclusion
        (SheafOfModules.{u} (structureSheafRing X))).app K, inferInstance, inferInstance⟩
  have := hj
  have := hIinj
  have hQ : IsIso (DerivedCategory.Q.map j) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  -- `η • 𝟙` vanishes on `K`, hence on `I` after inverting the resolution.
  have hzeroK : η • 𝟙 K = 0 := by
    ext m : 1
    rw [HomologicalComplex.smul_f_apply, CategoryTheory.Linear.smulOfRingMorphism_smul_eq,
      HomologicalComplex.id_f, Category.comp_id, HomologicalComplex.zero_f]
    exact hK m
  have hcomp : j ≫ (η • 𝟙 I) = 0 := by
    rw [CategoryTheory.Linear.comp_smul, Category.comp_id, ← Category.id_comp j,
      ← CategoryTheory.Linear.smul_comp, hzeroK, Limits.zero_comp]
  have hQzero : DerivedCategory.Q.map (η • 𝟙 I) = 0 := by
    rw [← cancel_epi (DerivedCategory.Q.map j), Limits.comp_zero, ← DerivedCategory.Q.map_comp,
      hcomp, CategoryTheory.Functor.map_zero]
  -- hence the induced map on the hypercohomology of `I` is zero,
  have hmapI : hypercohomologyMap X RΓ (η • 𝟙 I) n = 0 := by
    rw [← hypercohomologyMap_zero_of_isKInjective X RΓ α I n]
    change (DerivedCategory.homologyFunctor _ n).map (RΓ.map (DerivedCategory.Q.map (η • 𝟙 I))) =
      (DerivedCategory.homologyFunctor _ n).map (RΓ.map (DerivedCategory.Q.map (0 : I ⟶ I)))
    rw [hQzero, DerivedCategory.Q.map_zero]
  -- while on global sections it is multiplication by `r`.
  have hnat := hypercohomologyIsoGlobalSectionsHomology_naturality X RΓ α (η • 𝟙 I) n
  rw [hmapI, Limits.zero_comp, homologyMap_globalSections_center_smul_id X η r hη I n,
    CategoryTheory.Linear.comp_smul, Category.comp_id] at hnat
  have htarget : r • 𝟙 (((globalSectionsComplexFunctor X).obj I).homology n) = 0 := by
    rw [← cancel_epi (hypercohomologyIsoGlobalSectionsHomology X RΓ α I n).hom,
      CategoryTheory.Linear.comp_smul, Category.comp_id, Limits.comp_zero]
    exact hnat.symm
  -- transport back along the resolution, which is invertible on hypercohomology.
  have hiso : IsIso (hypercohomologyMap X RΓ j n) := by
    have : IsIso (RΓ.map (DerivedCategory.Q.map j)) := RΓ.map_isIso _
    exact (DerivedCategory.homologyFunctor _ n).map_isIso _
  exact CategoryTheory.Linear.smul_id_eq_zero_of_iso (asIso (hypercohomologyMap X RΓ j n))
    (CategoryTheory.Linear.smul_id_eq_zero_of_iso
      (hypercohomologyIsoGlobalSectionsHomology X RΓ α I n) htarget)

/-- **A global function killing every term of a complex annihilates its hypercohomology.** If
multiplication by `r ∈ Γ(X, 𝒪_X)` is zero on every term `K^m` of a complex of `𝒪_X`-modules, then
`r` annihilates `H^n(X, K^•)` for every `n`.

This is the step the proof of [Stacks, Tag 0GA1] takes between [Stacks, Tag 0GA0], which
annihilates the cohomology *sheaves* `H^b(Lp^*M̃)` of the derived pullback on sections, and the
second page `H^a(X, H^b(Lp^*M̃)(q))` of the hypercohomology spectral sequence [Stacks, Tag 0G9Q],
which is what the filtration of the abutment is built from. -/
theorem mem_annihilator_hypercohomology_of_center_app_eq_zero
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hK : ∀ m : ℤ, η.app (K.X m) = 0) (n : ℤ) :
    r ∈ Module.annihilator ((structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))
      (hypercohomology X RΓ K n) := by
  refine Module.mem_annihilator.2 fun x => ?_
  have h := smul_id_hypercohomology_eq_zero X RΓ α η r hη K hK n
  exact congrFun (congrArg (fun f => (ModuleCat.Hom.hom f).toFun) h) x

/-- **A global function killing a module sheaf annihilates its cohomology.** If multiplication by
`r ∈ Γ(X, 𝒪_X)` is the zero endomorphism of `F`, then `r` annihilates `H^n(X, F)`, the cohomology
of the derived global sections of `F` placed in degree zero.

This is the shape in which the second page `H^a(X, H^b(K))` of the hypercohomology spectral
sequence [Stacks, Tag 0BKM] is stated, so it is the shape the proof of [Stacks, Tag 0GA1] needs:
there `F = H^b(Lp^*M̃)(q)` and the hypothesis is [Stacks, Tag 0GA0], which annihilates that sheaf
on sections over every open — hence, the sections over an open determining a morphism of sheaves,
annihilates it as an endomorphism. -/
theorem mem_annihilator_homology_RΓ_single_of_center_app_eq_zero
    (F : SheafOfModules.{u} (structureSheafRing X)) (hF : η.app F = 0) (n : ℤ) :
    r ∈ Module.annihilator ((structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))) n).obj
        (RΓ.obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X)) 0).obj F))) := by
  refine mem_annihilator_hypercohomology_of_center_app_eq_zero X RΓ α η r hη
    ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj F)
    (fun m => ?_) n
  by_cases hm : m = 0
  · subst hm
    exact CategoryTheory.CatCenter.app_eq_zero_of_iso η
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F) hF
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F m hm).eq_of_src _ 0

end

end Stacks.Cohomology.FilteredComplex

end
