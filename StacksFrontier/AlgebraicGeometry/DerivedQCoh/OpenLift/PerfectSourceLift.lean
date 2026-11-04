module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.PerfectSheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.RestrictionSpellings
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.KoszulLift
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyComparisonBijective
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.StructureSheafSpellings
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.TensorHomSectionsCurrying
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceTensorRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceTensorUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.InterfaceTensorProduct
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCategorySectionsRestriction

/-!
# Lifting a map out of a perfect complex over a quasi-compact open

Let `A` be a commutative ring, `X = Spec A` and `U ⊆ X` a quasi-compact open.  Let `E` be a
perfect object of `D(𝒪_X)` and `E'` an object of `D_QCoh(𝒪_X)`.  Every map `α : E|_U ⟶ E'|_U`
fits into a diagram

`E ←β– E₁ –γ→ E'`

of `D(𝒪_X)` with `E₁ = I ⊗^L_{𝒪_X} E` perfect for a perfect object `I`, with `β|_U` invertible
and `α = γ|_U ∘ (β|_U)⁻¹`.  This is [Stacks, Tag 08EH].

## Main results

* `Stacks.DerivedQCoh.OpenLift.exists_isPerfect_lift_of_isPerfect_slice`: the lemma with `(-)|_U`
  read as restriction to the opens contained in `U`.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfect_lift_of_isPerfect_of_isDQCoh`: the lemma with
  `(-)|_U` read as restriction to the open subspace `U`.

## References

* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 09J5](https://stacks.math.columbia.edu/tag/09J5)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Koszul.DerivedSystem Stacks.Cohomology.OpenSubspace
open Stacks.SheafOfModules (ringedSite derivedRestrict derivedTensorProductFunctor
  derivedRestrictSpellingMap)
open Stacks.SheafOfModules.DerivedMonoidal (interfaceLeftUnitIso)
open AlgebraicGeometry.RingedSite (derivedSheafHomBifunctor derivedCurrySectionsEquiv
  derivedCurryHomEquiv derivedCurrySectionsEquiv_naturality_source
  derivedCurrySectionsEquiv_restriction)

namespace Stacks.DerivedQCoh.OpenLift

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {A : CommRingCat.{u}}

/-! ### Comparing the two spellings of the restriction -/

/-- A map of `D(𝒪_X)` is invertible on the opens contained in `U` iff it is on the open
subspace `U`. -/
private theorem isIso_derivedRestrict_map_iff (U : (Spec A).Opens) {I O : derivedCat A}
    (β : I ⟶ O) :
    IsIso ((derivedRestrict (Spec A).sheaf U).map β) ↔
      IsIso ((derivedRestriction (Spec A).ringCatSheaf U).map β) := by
  rw [← Stacks.SheafOfModules.derivedRestrictSpellingMap_map (Spec A).sheaf U β]
  exact ⟨fun _ ↦ inferInstance,
    Stacks.SheafOfModules.isIso_of_isIso_derivedRestrictSpellingMap (Spec A).sheaf U _⟩

/-- The equation `β|_U ≫ g = γ|_U` holds in either spelling of the restriction to `U`. -/
private theorem derivedRestrict_map_comp_eq_iff (U : (Spec A).Opens) {I O M : derivedCat A}
    (β : I ⟶ O) (γ : I ⟶ M)
    (g : (derivedRestrict (Spec A).sheaf U).obj O ⟶ (derivedRestrict (Spec A).sheaf U).obj M) :
    (derivedRestrict (Spec A).sheaf U).map β ≫ g = (derivedRestrict (Spec A).sheaf U).map γ ↔
      (derivedRestriction (Spec A).ringCatSheaf U).map β ≫
          derivedRestrictSpellingMap (Spec A).sheaf U g =
        (derivedRestriction (Spec A).ringCatSheaf U).map γ := by
  rw [← Stacks.SheafOfModules.derivedRestrictSpellingMap_map (Spec A).sheaf U β,
    ← Stacks.SheafOfModules.derivedRestrictSpellingMap_map (Spec A).sheaf U γ,
    ← Stacks.SheafOfModules.derivedRestrictSpellingMap_comp]
  exact (Stacks.SheafOfModules.derivedRestrictSpellingMap_injective (Spec A).sheaf U).eq_iff.symm

/-! ### Tensoring the lift of the structure sheaf -/

/-- **A map down to the structure sheaf that is invertible on `U` stays invertible on `U` after
tensoring with `E` and composing with the unit constraint.**  For `β : I ⟶ 𝒪_X` whose restriction
to `U` is invertible, the composite `I ⊗^L_{𝒪_X} E ⟶ 𝒪_X ⊗^L_{𝒪_X} E ⟶ E` restricts to an
isomorphism on `U`. -/
theorem isIso_derivedRestrict_map_tensorUnitLift (U : (Spec A).Opens) (I E : derivedCat A)
    (β : I ⟶ structureSheafObject A)
    (hβ : IsIso ((derivedRestriction (Spec A).ringCatSheaf U).map β)) :
    IsIso ((derivedRestrict (Spec A).sheaf U).map
      (((derivedTensorProductFunctor (ringedSite (Spec A).sheaf)).map β).app E ≫
        (interfaceLeftUnitIso (ringedSite (Spec A).sheaf) E).hom)) := by
  have hs := (isIso_derivedRestrict_map_iff U β).2 hβ
  have h1 : IsIso ((derivedRestrict (Spec A).sheaf U).map
      (((derivedTensorProductFunctor (ringedSite (Spec A).sheaf)).map β).app E)) :=
    Stacks.SheafOfModules.DerivedMonoidal.isIso_restriction_map_interfaceTensorMap_source
      (ringedSite (Spec A).sheaf) U β E hs
  have h2 : IsIso ((derivedRestrict (Spec A).sheaf U).map
      (interfaceLeftUnitIso (ringedSite (Spec A).sheaf) E).hom) :=
    Iso.isIso_hom ((derivedRestrict (Spec A).sheaf U).mapIso
      (interfaceLeftUnitIso (ringedSite (Spec A).sheaf) E))
  exact cast (congrArg IsIso (Functor.map_comp _ _ _).symm) (IsIso.comp_isIso' h1 h2)

/-- If `c = a ≫ b` and `a ≫ b ≫ α = z` then `c ≫ α = z`. -/
private theorem comp_eq_of_eq_comp {C : Type*} [Category C] {P Q R S : C} {a : P ⟶ Q}
    {b : Q ⟶ R} {c : P ⟶ R} {α : R ⟶ S} {z : P ⟶ S} (hc : c = a ≫ b) (H : a ≫ b ≫ α = z) :
    c ≫ α = z := by
  rw [hc, Category.assoc, H]

/-! ### Transposing a factorization, over an arbitrary ringed space

The statements of this section are over a sheaf of rings `Rc` on `X`.  They pass between the
restriction functor to the opens contained in `U` and the restriction functor of the ringed site
of `Rc`, which differ only in how the structure sheaf is written. -/

section Generic

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X)

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

attribute [local instance] Koszul.DerivedSystem.hasMapBifunctorSheafTensor

attribute [local instance] Koszul.DerivedSystem.preservesFiniteLimitsOver

attribute [local instance] Koszul.DerivedSystem.preservesFiniteColimitsOver

attribute [local instance] Stacks.SheafOfModules.preservesFiniteLimitsOverRingedSite

attribute [local instance] Stacks.SheafOfModules.preservesFiniteColimitsOverRingedSite

/-- The source naturality of the bijection of [Stacks, Tag 08J8] over `U`, with the composite
named. -/
theorem derivedCurrySectionsEquiv_naturality_source_of_eq
    (O I E E' : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules Rc)) (β : I ⟶ O)
    (h : (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).mapDerivedCategory.obj O ⟶
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor (ringedSite Rc)).obj (op E)).obj E'))
    (k : (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).mapDerivedCategory.obj I ⟶
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor (ringedSite Rc)).obj (op E)).obj E'))
    (hk : (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).mapDerivedCategory.map β ≫
      h = k) :
    derivedCurrySectionsEquiv (ringedSite Rc) U I E E' k =
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).mapDerivedCategory.map
          (((derivedTensorProductFunctor (ringedSite Rc)).map β).app E) ≫
        derivedCurrySectionsEquiv (ringedSite Rc) U O E E' h := by
  subst hk
  exact derivedCurrySectionsEquiv_naturality_source (ringedSite Rc) U O I E E' β h

/-- The compatibility of the bijection of [Stacks, Tag 08J8] with restriction, with the
restriction written as restriction to the opens contained in `U`. -/
theorem derivedCurrySectionsEquiv_derivedRestrict_map
    (I E E' : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules Rc))
    (γ : I ⟶ (((derivedSheafHomBifunctor (ringedSite Rc)).obj (op E)).obj E')) :
    derivedCurrySectionsEquiv (ringedSite Rc) U I E E' ((derivedRestrict Rc U).map γ) =
      (derivedRestrict Rc U).map (derivedCurryHomEquiv (ringedSite Rc) I E E' γ) :=
  derivedCurrySectionsEquiv_restriction (ringedSite Rc) U I E E' γ

/-- **Transposing a factorization through a map.**  Let `β : I ⟶ O` and
`γ : I ⟶ R𝓗om(E, E')`, and let `g : O|_U ⟶ R𝓗om(E, E')|_U` satisfy `β|_U ≫ g = γ|_U`.  Then
the transpose of `g` along the bijection of [Stacks, Tag 08J8] over `U`, precomposed with the
restriction of `β ⊗ 1_E`, is the restriction of the transpose of `γ` over `X`. -/
theorem derivedRestrict_tensorMap_comp_derivedCurrySectionsEquiv
    (O I E E' : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules Rc)) (β : I ⟶ O)
    (γ : I ⟶ (((derivedSheafHomBifunctor (ringedSite Rc)).obj (op E)).obj E'))
    (g : (derivedRestrict Rc U).obj O ⟶
      (derivedRestrict Rc U).obj (((derivedSheafHomBifunctor (ringedSite Rc)).obj (op E)).obj E'))
    (hβγ : (derivedRestrict Rc U).map β ≫ g = (derivedRestrict Rc U).map γ) :
    (derivedRestrict Rc U).map
          (((derivedTensorProductFunctor (ringedSite Rc)).map β).app E) ≫
        derivedCurrySectionsEquiv (ringedSite Rc) U O E E' g =
      (derivedRestrict Rc U).map (derivedCurryHomEquiv (ringedSite Rc) I E E' γ) := by
  have c : (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).mapDerivedCategory.map β ≫
      (g : (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).mapDerivedCategory.obj O ⟶
        (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).mapDerivedCategory.obj
          (((derivedSheafHomBifunctor (ringedSite Rc)).obj (op E)).obj E')) =
      ((derivedRestrict Rc U).map γ : (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).mapDerivedCategory.obj I ⟶
        (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).mapDerivedCategory.obj
          (((derivedSheafHomBifunctor (ringedSite Rc)).obj (op E)).obj E')) := hβγ
  have n := derivedCurrySectionsEquiv_naturality_source_of_eq Rc U O I E E' β g _ c
  have r := derivedCurrySectionsEquiv_derivedRestrict_map Rc U I E E' γ
  have c2 : (derivedRestrict Rc U).map
          (((derivedTensorProductFunctor (ringedSite Rc)).map β).app E) ≫
        derivedCurrySectionsEquiv (ringedSite Rc) U O E E' g =
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).mapDerivedCategory.map
          (((derivedTensorProductFunctor (ringedSite Rc)).map β).app E) ≫
        derivedCurrySectionsEquiv (ringedSite Rc) U O E E' g := rfl
  exact c2.trans (n.symm.trans r)

/-- The same statement with the transpose of `g` named `a`. -/
theorem derivedRestrict_tensorMap_comp_eq_derivedCurryHomEquiv
    (O I E E' : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules Rc)) (β : I ⟶ O)
    (γ : I ⟶ (((derivedSheafHomBifunctor (ringedSite Rc)).obj (op E)).obj E'))
    (g : (derivedRestrict Rc U).obj O ⟶
      (derivedRestrict Rc U).obj (((derivedSheafHomBifunctor (ringedSite Rc)).obj (op E)).obj E'))
    (hβγ : (derivedRestrict Rc U).map β ≫ g = (derivedRestrict Rc U).map γ)
    (a : (derivedRestrict Rc U).obj
        (((derivedTensorProductFunctor (ringedSite Rc)).obj O).obj E) ⟶
      (derivedRestrict Rc U).obj E')
    (hg : derivedCurrySectionsEquiv (ringedSite Rc) U O E E' g = a) :
    (derivedRestrict Rc U).map
          (((derivedTensorProductFunctor (ringedSite Rc)).map β).app E) ≫ a =
      (derivedRestrict Rc U).map (derivedCurryHomEquiv (ringedSite Rc) I E E' γ) := by
  have t := derivedRestrict_tensorMap_comp_derivedCurrySectionsEquiv Rc U O I E E' β γ g hβγ
  exact (congrArg (fun t : (derivedRestrict Rc U).obj
        (((derivedTensorProductFunctor (ringedSite Rc)).obj O).obj E) ⟶
      (derivedRestrict Rc U).obj E' ↦ (derivedRestrict Rc U).map
        (((derivedTensorProductFunctor (ringedSite Rc)).map β).app E) ≫ t) hg).symm.trans t

end Generic

/-- **Transposing a factorization through a map, on `Spec A`.**  With `ι : O ⊗^L E ⟶ E`, a map
`g : O|_U ⟶ R𝓗om(E, E')|_U` whose transpose is `ι|_U ≫ α`, and `γ` restricting to `β|_U ≫ g`, the
restriction of `(β ⊗ 1_E) ≫ ι` followed by `α` is the restriction of the transpose of `γ`. -/
theorem derivedRestrict_tensorMap_comp_comp_eq_derivedCurryHomEquiv
    (V : (Spec A).Opens) (O I E E' : derivedCat A) (β : I ⟶ O)
    (ι : ((derivedTensorProductFunctor (ringedSite (Spec A).sheaf)).obj O).obj E ⟶ E)
    (γ : I ⟶ (((derivedSheafHomBifunctor (ringedSite (Spec A).sheaf)).obj (op E)).obj E'))
    (α : (derivedRestrict (Spec A).sheaf V).obj E ⟶ (derivedRestrict (Spec A).sheaf V).obj E')
    (g : (derivedRestrict (Spec A).sheaf V).obj O ⟶ (derivedRestrict (Spec A).sheaf V).obj
      (((derivedSheafHomBifunctor (ringedSite (Spec A).sheaf)).obj (op E)).obj E'))
    (hg : derivedCurrySectionsEquiv (ringedSite (Spec A).sheaf) V O E E' g =
      (derivedRestrict (Spec A).sheaf V).map ι ≫ α)
    (hβγ : (derivedRestrict (Spec A).sheaf V).map β ≫ g =
      (derivedRestrict (Spec A).sheaf V).map γ) :
    (derivedRestrict (Spec A).sheaf V).map
        (((derivedTensorProductFunctor (ringedSite (Spec A).sheaf)).map β).app E ≫ ι) ≫ α =
      (derivedRestrict (Spec A).sheaf V).map
        (derivedCurryHomEquiv (ringedSite (Spec A).sheaf) I E E' γ) := by
  have heq : (derivedRestrict (Spec A).sheaf V).map
        (((derivedTensorProductFunctor (ringedSite (Spec A).sheaf)).map β).app E ≫ ι) =
      (derivedRestrict (Spec A).sheaf V).map
          (((derivedTensorProductFunctor (ringedSite (Spec A).sheaf)).map β).app E) ≫
        (derivedRestrict (Spec A).sheaf V).map ι :=
    Functor.map_comp _ _ _
  have k := derivedRestrict_tensorMap_comp_eq_derivedCurryHomEquiv (Spec A).sheaf V O I E E' β γ
    g hβγ ((derivedRestrict (Spec A).sheaf V).map ι ≫ α) hg
  have k1 : (derivedRestrict (Spec A).sheaf V).map
        (((derivedTensorProductFunctor (ringedSite (Spec A).sheaf)).map β).app E) ≫
        ((derivedRestrict (Spec A).sheaf V).map ι ≫ α) =
      (derivedRestrict (Spec A).sheaf V).map
        (derivedCurryHomEquiv (ringedSite (Spec A).sheaf) I E E' γ) := by
    convert k using 3
  exact comp_eq_of_eq_comp heq k1

/-! ### The case `E = 𝒪_X`, in the slice spelling -/

/-- **The case `E = 𝒪_X` of [Stacks, Tag 08EH], with the restriction to `U` read as restriction
to the opens contained in `U`.**  On `X = Spec A`, for a quasi-compact open `U ⊆ X` and an object
`M` of `D_QCoh(𝒪_X)`, every map `g : 𝒪_X|_U ⟶ M|_U` satisfies `β|_U ≫ g = γ|_U` for a perfect
object `I` of `D(𝒪_X)` and maps `β : I ⟶ 𝒪_X` and `γ : I ⟶ M`, with `β` invertible on the open
subspace `U`. -/
theorem exists_isPerfect_lift_of_structureSheaf_slice (U : (Spec A).Opens)
    (hU : IsCompact (U : Set (Spec A))) (M : derivedCat A)
    (hM : Stacks.DerivedQCoh.IsDQCoh (R := (Spec A).ringCatSheaf) M)
    (g : (derivedRestrict (Spec A).sheaf U).obj (structureSheafObject A) ⟶
      (derivedRestrict (Spec A).sheaf U).obj M) :
    ∃ I : derivedCat A,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) I ∧
      ∃ (β : I ⟶ structureSheafObject A) (γ : I ⟶ M),
        IsIso ((derivedRestriction (Spec A).ringCatSheaf U).map β) ∧
        (derivedRestrict (Spec A).sheaf U).map β ≫ g =
          (derivedRestrict (Spec A).sheaf U).map γ := by
  obtain ⟨I, hI, β, γ, hβiso, hβγ⟩ :=
    exists_isPerfect_lift_of_structureSheaf U hU M hM
      (derivedRestrictSpellingMap (Spec A).sheaf U g)
  refine ⟨I, hI, β, γ, hβiso, ?_⟩
  exact (derivedRestrict_map_comp_eq_iff U β γ g).2 hβγ

/-! ### Tag 08EH -/

/-- **[Stacks, Tag 08EH], with the restriction to `U` read as restriction to the opens contained
in `U`.**  On `X = Spec A`, for a quasi-compact open `U ⊆ X`, a perfect object `E` of `D(𝒪_X)`
and an object `E'` of `D_QCoh(𝒪_X)`, every map `α : E|_U ⟶ E'|_U` is `γ|_U ∘ (β|_U)⁻¹` for a
perfect object `I` of `D(𝒪_X)` and maps `β : I ⊗^L_{𝒪_X} E ⟶ E` and `γ : I ⊗^L_{𝒪_X} E ⟶ E'`
with `β|_U` invertible, the object `I ⊗^L_{𝒪_X} E` being perfect as well. -/
theorem exists_isPerfect_lift_of_isPerfect_slice (U : (Spec A).Opens)
    (hU : IsCompact (U : Set (Spec A))) (E E' : derivedCat A)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) E)
    (hE' : Stacks.DerivedQCoh.IsDQCoh (R := (Spec A).ringCatSheaf) E')
    (α : (derivedRestrict (Spec A).sheaf U).obj E ⟶
      (derivedRestrict (Spec A).sheaf U).obj E') :
    ∃ I : derivedCat A,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) I ∧
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace)
        (((derivedTensorProductFunctor (ringedSite (Spec A).sheaf)).obj I).obj E) ∧
      ∃ (β : ((derivedTensorProductFunctor (ringedSite (Spec A).sheaf)).obj I).obj E ⟶ E)
        (γ : ((derivedTensorProductFunctor (ringedSite (Spec A).sheaf)).obj I).obj E ⟶ E'),
        IsIso ((derivedRestrict (Spec A).sheaf U).map β) ∧
        (derivedRestrict (Spec A).sheaf U).map β ≫ α =
          (derivedRestrict (Spec A).sheaf U).map γ := by
  obtain ⟨g, hg⟩ : ∃ g : (derivedRestrict (Spec A).sheaf U).obj (structureSheafObject A) ⟶
      (derivedRestrict (Spec A).sheaf U).obj
        (((derivedSheafHomBifunctor (ringedSite (Spec A).sheaf)).obj (op E)).obj E'),
      derivedCurrySectionsEquiv (ringedSite (Spec A).sheaf) U (structureSheafObject A) E E' g =
        (derivedRestrict (Spec A).sheaf U).map
          (interfaceLeftUnitIso (ringedSite (Spec A).sheaf) E).hom ≫ α :=
    ⟨_, (derivedCurrySectionsEquiv (ringedSite (Spec A).sheaf) U
      (structureSheafObject A) E E').apply_symm_apply _⟩
  obtain ⟨I, hI, β, γ, hβiso, hβγ⟩ :=
    exists_isPerfect_lift_of_structureSheaf_slice U hU
      (((derivedSheafHomBifunctor (ringedSite (Spec A).sheaf)).obj (op E)).obj E')
      (fun n ↦ isQuasicoherent_homology_derivedSheafHom_of_isPerfect A E E' hE hE' n) g
  refine ⟨I, hI,
    RingedSpace.isPerfect_interfaceDerivedTensorProduct (Spec A).toRingedSpace I E hI hE,
    ((derivedTensorProductFunctor (ringedSite (Spec A).sheaf)).map β).app E ≫
      (interfaceLeftUnitIso (ringedSite (Spec A).sheaf) E).hom,
    derivedCurryHomEquiv (ringedSite (Spec A).sheaf) I E E' γ,
    isIso_derivedRestrict_map_tensorUnitLift U I E β hβiso, ?_⟩
  exact derivedRestrict_tensorMap_comp_comp_eq_derivedCurryHomEquiv U
    (structureSheafObject A) I E E' β (interfaceLeftUnitIso (ringedSite (Spec A).sheaf) E).hom γ α
    g hg hβγ

/-- **[Stacks, Tag 08EH], perfect source tensored on the left.**  Let `A` be a commutative ring,
`X = Spec A`, and `U ⊆ X` a quasi-compact open.  Let `E` be a perfect object of `D(𝒪_X)` and `E'`
an object of `D_QCoh(𝒪_X)`.  Every map `α : E|_U ⟶ E'|_U` fits into a diagram

`E ←β– E₁ –γ→ E'`

of `D(𝒪_X)` with `E₁ = I ⊗^L_{𝒪_X} E` perfect for a perfect object `I` of `D(𝒪_X)`, with `β|_U`
invertible and `α = γ|_U ∘ (β|_U)⁻¹`, the restriction to `U` being restriction to the open
subspace `U`. -/
theorem exists_isPerfect_lift_of_isPerfect_of_isDQCoh (U : (Spec A).Opens)
    (hU : IsCompact (U : Set (Spec A))) (E E' : derivedCat A)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) E)
    (hE' : Stacks.DerivedQCoh.IsDQCoh (R := (Spec A).ringCatSheaf) E')
    (α : (derivedRestriction (Spec A).ringCatSheaf U).obj E ⟶
      (derivedRestriction (Spec A).ringCatSheaf U).obj E') :
    ∃ I : derivedCat A,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) I ∧
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace)
        (((derivedTensorProductFunctor (ringedSite (Spec A).sheaf)).obj I).obj E) ∧
      ∃ (β : ((derivedTensorProductFunctor (ringedSite (Spec A).sheaf)).obj I).obj E ⟶ E)
        (γ : ((derivedTensorProductFunctor (ringedSite (Spec A).sheaf)).obj I).obj E ⟶ E'),
        IsIso ((derivedRestriction (Spec A).ringCatSheaf U).map β) ∧
        (derivedRestriction (Spec A).ringCatSheaf U).map β ≫ α =
          (derivedRestriction (Spec A).ringCatSheaf U).map γ := by
  obtain ⟨a, ha⟩ :=
    Stacks.SheafOfModules.derivedRestrictSpellingMap_surjective (Spec A).sheaf U α
  obtain ⟨I, hI, hIE, β, γ, hβ, hβγ⟩ :=
    exists_isPerfect_lift_of_isPerfect_slice U hU E E' hE hE' a
  refine ⟨I, hI, hIE, β, γ, ?_, ?_⟩
  · exact (isIso_derivedRestrict_map_iff U β).1 hβ
  · simpa only [ha] using (derivedRestrict_map_comp_eq_iff U β γ a).1 hβγ

end Stacks.DerivedQCoh.OpenLift

end
