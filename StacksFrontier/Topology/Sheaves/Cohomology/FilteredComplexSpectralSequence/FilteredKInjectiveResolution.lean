module

public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksCore.Algebra.Homology.SpectralSequence.PageInfinity
public import StacksCore.CategoryTheory.Abelian.Subobject
public import StacksCore.CategoryTheory.Filtration.GradedPieces
public import StacksFrontier.Algebra.Homology.SpectralSequence.Boundedness
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Canonical
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.PageInfinity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Subobject.CokernelComparisons
public import StacksFrontier.Homology.FilteredDerivedCategory.InjectiveResolutions
public import StacksFrontier.Homology.Injectives.FilteredComplex.KInjectiveResolution
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# The spectral sequence of a filtered complex of sheaves

Let `(X, O_X)` be a ringed space and let `F^•` be a filtered complex of `O_X`-modules. Applying
global sections to a filtered K-injective resolution of `F^•` produces a filtered complex of
`Γ(X, O_X)`-modules, whose filtered-complex spectral sequence is the spectral sequence of `F^•`:
a cohomological spectral sequence `(E_r, d_r)_{r ≥ 1}` of bigraded `Γ(X, O_X)`-modules with `d_r`
of bidegree `(r, -r + 1)` and
```
E_1^{p, q} = H^{p + q}(X, gr^pF^•).
```
If for every `n` the hypercohomology `H^n(X, F^pF^•)` vanishes for `p ≫ 0` and agrees with
`H^n(X, F^•)` for `p ≪ 0`, the spectral sequence is bounded and converges to `H^*(X, F^•)`.

## Main definitions

* `Stacks.Cohomology.FilteredComplex.hypercohomology` and
  `Stacks.Cohomology.FilteredComplex.hypercohomologyMap`: unbounded derived global-sections
  cohomology of a complex of module sheaves, and its functoriality.
* `Stacks.Cohomology.FilteredComplex.globalSectionsToHypercohomology`: the comparison from the
  cohomology of the complex of global sections to hypercohomology, as a natural transformation.
* `Stacks.Cohomology.FilteredComplex.globalSectionsFilteredComplex`: global sections, applied
  degreewise to a filtered complex of module sheaves.

## Main results

* `Stacks.Cohomology.FilteredComplex.isIso_globalSectionsToHypercohomology_app`: that comparison
  is invertible at a K-injective complex.
* `Stacks.Cohomology.FilteredComplex.spectralSequence_of_filteredKInjectiveResolution`: the first
  page and the conditional bounded convergence, for a supplied filtered K-injective resolution.
* `Stacks.Cohomology.FilteredComplex.exists_spectralSequence_of_filteredComplex`: such a
  resolution, a derived global-sections functor and the resulting spectral sequence exist for
  every filtered complex of module sheaves.

## References

* [Stacks Project, Tag 0BKK](https://stacks.math.columbia.edu/tag/0BKK)
* [Stacks Project, Tag 0BKI](https://stacks.math.columbia.edu/tag/0BKI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

universe u

namespace Stacks.Cohomology.FilteredComplex

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-- The `n`-th hypercohomology module of a complex of module sheaves on a ringed space, computed
by an unbounded derived global-sections functor `RΓ`. -/
abbrev hypercohomology
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℤ) :
    ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)) :=
  (DerivedCategory.homologyFunctor
    (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) n).obj
      (RΓ.obj (DerivedCategory.Q.obj K))

/-- The map on hypercohomology induced by a map of complexes. -/
abbrev hypercohomologyMap
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (f : K ⟶ L) (n : ℤ) :
    hypercohomology X RΓ K n ⟶ hypercohomology X RΓ L n :=
  (DerivedCategory.homologyFunctor
    (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) n).map
      (RΓ.map (DerivedCategory.Q.map f))

/-- Global sections of module sheaves on a ringed space, applied degreewise to complexes. -/
abbrev globalSectionsComplexFunctor :
    CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ ⥤
      CochainComplex (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) ℤ :=
  (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- The comparison from the cohomology of the complex of global sections to hypercohomology, built
from the unit `α` of the derived global-sections functor and the natural isomorphisms identifying
homology on complexes, on the homotopy category and on the derived category. -/
def globalSectionsToHypercohomology
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)
    (n : ℤ) :
    globalSectionsComplexFunctor X ⋙
        HomologicalComplex.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (ComplexShape.up ℤ) n ⟶
      DerivedCategory.Q ⋙ RΓ ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) n :=
  Functor.whiskerLeft (globalSectionsComplexFunctor X)
      (HomotopyCategory.homologyFunctorFactors
        (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (ComplexShape.up ℤ) n).inv ≫
    Functor.whiskerLeft (globalSectionsComplexFunctor X ⋙
        HomotopyCategory.quotient (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
          (ComplexShape.up ℤ))
      (DerivedCategory.homologyFunctorFactorsh
        (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) n).inv ≫
    Functor.whiskerRight
      ((SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv
      (DerivedCategory.Qh ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) n) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft
        (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
        α)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) n) ≫
    Functor.whiskerRight
      (Functor.whiskerRight
        (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom RΓ)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) n)

/-- The unit of a right-derived global-sections functor is invertible at a K-injective complex. -/
lemma isIso_unit_app_of_isKInjective
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective) :
    IsIso (α.app ((HomotopyCategory.quotient
      (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)).obj I)) := by
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing X)) := inferInstance
  exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (homotopySections (structureSheafRing X) (⊤ : Opens X.carrier))
    (fun L ↦ ⟨(Stacks.Injectives.kInjectiveResolutionFunctor
        (SheafOfModules.{u} (structureSheafRing X))).obj L,
      (Stacks.Injectives.kInjectiveResolutionInclusion
        (SheafOfModules.{u} (structureSheafRing X))).app L, inferInstance, inferInstance⟩)).2
    DerivedCategory.Qh RΓ α I hI

/-- At a K-injective complex the comparison with hypercohomology is invertible. -/
instance isIso_globalSectionsToHypercohomology_app
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] (n : ℤ) :
    IsIso ((globalSectionsToHypercohomology X RΓ α n).app I) := by
  have := isIso_unit_app_of_isKInjective X RΓ α I inferInstance
  dsimp only [globalSectionsToHypercohomology]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- At a K-injective complex, hypercohomology is the cohomology of the complex of global
sections. -/
def hypercohomologyIsoGlobalSectionsHomology
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] (n : ℤ) :
    hypercohomology X RΓ I n ≅ ((globalSectionsComplexFunctor X).obj I).homology n :=
  (asIso ((globalSectionsToHypercohomology X RΓ α n).app I)).symm

/-- The identification of hypercohomology with the cohomology of the complex of global sections
is compatible with maps of K-injective complexes. -/
lemma hypercohomologyIsoGlobalSectionsHomology_naturality
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    {I J : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J) (n : ℤ) :
    hypercohomologyMap X RΓ f n ≫
        (hypercohomologyIsoGlobalSectionsHomology X RΓ α J n).hom =
      (hypercohomologyIsoGlobalSectionsHomology X RΓ α I n).hom ≫
        HomologicalComplex.homologyMap ((globalSectionsComplexFunctor X).map f) n := by
  have h : CommSq (HomologicalComplex.homologyMap ((globalSectionsComplexFunctor X).map f) n)
      (asIso ((globalSectionsToHypercohomology X RΓ α n).app I)).hom
      (asIso ((globalSectionsToHypercohomology X RΓ α n).app J)).hom
      (hypercohomologyMap X RΓ f n) :=
    ⟨(globalSectionsToHypercohomology X RΓ α n).naturality f⟩
  exact h.vert_inv.w

/-- Hypercohomology of a composite of maps of complexes is the composite of the maps. -/
private lemma hypercohomologyMap_comp
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    {K L M : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (f : K ⟶ L) (g : L ⟶ M) (n : ℤ) :
    hypercohomologyMap X RΓ (f ≫ g) n =
      hypercohomologyMap X RΓ f n ≫ hypercohomologyMap X RΓ g n := by
  simp only [hypercohomologyMap, Functor.map_comp]

/-- The filtered complex obtained by applying global sections degreewise to a filtered complex
of module sheaves. -/
def globalSectionsFilteredComplex
    (J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) :
    CochainComplex.Filtered (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) :=
  J.mapOfMono (globalSectionsComplexFunctor X) (fun _ ↦ inferInstance)

/-- The underlying complex of `globalSectionsFilteredComplex X J` is the complex of global sections
of that of `J`. -/
@[simp]
lemma globalSectionsFilteredComplex_X
    (J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) :
    (globalSectionsFilteredComplex X J).X = (globalSectionsComplexFunctor X).obj J.X :=
  rfl

/-- The `p`-th filtration step of `globalSectionsFilteredComplex X J` is the complex of global
sections of that of `J`. -/
lemma globalSectionsFilteredComplex_filtration_obj
    (J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) (p : ℤᵒᵖ) :
    (globalSectionsFilteredComplex X J).filtration.obj p =
      (globalSectionsComplexFunctor X).obj (J.filtration.obj p) :=
  rfl

/-- The inclusion of the `p`-th filtration step of `globalSectionsFilteredComplex X J` is global
sections of that of `J`. -/
@[simp]
lemma globalSectionsFilteredComplex_filtration_ι_app
    (J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) (p : ℤᵒᵖ) :
    (globalSectionsFilteredComplex X J).filtration.ι.app p =
      (globalSectionsComplexFunctor X).map (J.filtration.ι.app p) :=
  rfl

/-- A filtered K-injective resolution of a filtered complex `K`: a filtered quasi-isomorphism
`K ⟶ obj` whose target has K-injective ambient complex, K-injective filtration steps and
K-injective graded pieces, the filtration steps being termwise injective. -/
structure FilteredKInjectiveResolution
    (K : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) where
  /-- The filtered complex resolving `K`. -/
  obj : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))
  /-- The filtered quasi-isomorphism from `K` to the resolution. -/
  map : K ⟶ obj
  /-- The map is a quasi-isomorphism on the ambient complexes. -/
  quasiIso : QuasiIso map.hom
  /-- The map is a quasi-isomorphism on every filtration step. -/
  quasiIso_step (p : ℤ) : QuasiIso (map.natTrans.app (op p))
  /-- The map is a quasi-isomorphism on every graded piece. -/
  quasiIso_gr (p : ℤ) : QuasiIso ((FilteredObject.gr p).map map)
  /-- Every filtration step of the resolution is termwise injective. -/
  injective_step (p n : ℤ) : Injective ((obj.filtration.obj (op p)).X n)
  /-- The ambient complex of the resolution is K-injective. -/
  isKInjective : obj.X.IsKInjective
  /-- Every filtration step of the resolution is K-injective. -/
  isKInjective_step (p : ℤ) : (obj.filtration.obj (op p)).IsKInjective
  /-- Every graded piece of the resolution is K-injective. -/
  isKInjective_gr (p : ℤ) : ((FilteredObject.gr p).obj obj).IsKInjective

namespace FilteredKInjectiveResolution

variable
    {X}
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    {K : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))}
    (R : FilteredKInjectiveResolution X K)

include α in
/-- The hypercohomology of a filtration step of `K` is the cohomology of the complex of global
sections of the corresponding filtration step of the resolution. -/
def cmpStep (p n : ℤ) :
    hypercohomology X RΓ (K.filtration.obj (op p)) n ≅
      ((globalSectionsFilteredComplex X R.obj).filtration.obj (op p)).homology n := by
  letI := R.isKInjective_step p
  letI : QuasiIso (R.map.natTrans.app (op p)) := R.quasiIso_step p
  exact (DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) n).mapIso
      (RΓ.mapIso (asIso (DerivedCategory.Q.map (R.map.natTrans.app (op p))))) ≪≫
    hypercohomologyIsoGlobalSectionsHomology X RΓ α (R.obj.filtration.obj (op p)) n

include α in
/-- The hypercohomology of `K` is the cohomology of the complex of global sections of the
resolution. -/
def cmpTotal (n : ℤ) :
    hypercohomology X RΓ K.X n ≅ (globalSectionsFilteredComplex X R.obj).X.homology n := by
  letI := R.isKInjective
  letI : QuasiIso R.map.hom := R.quasiIso
  exact (DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) n).mapIso
      (RΓ.mapIso (asIso (DerivedCategory.Q.map R.map.hom))) ≪≫
    hypercohomologyIsoGlobalSectionsHomology X RΓ α R.obj.X n

/-- The comparisons of hypercohomology with the cohomology of global sections are compatible with
the inclusion of a filtration step. -/
lemma cmp_square (p n : ℤ) :
    (R.cmpStep RΓ α p n).hom ≫
        HomologicalComplex.homologyMap
          ((globalSectionsFilteredComplex X R.obj).filtration.ι.app (op p)) n =
      hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n ≫ (R.cmpTotal RΓ α n).hom := by
  have := R.isKInjective
  have := R.isKInjective_step p
  have : QuasiIso (R.map.natTrans.app (op p)) := R.quasiIso_step p
  have : QuasiIso R.map.hom := R.quasiIso
  have hnat := hypercohomologyIsoGlobalSectionsHomology_naturality X RΓ α
    (I := R.obj.filtration.obj (op p)) (J := R.obj.X)
    (R.obj.filtration.ι.app (op p) : R.obj.filtration.obj (op p) ⟶ R.obj.X) n
  have hmapComm : hypercohomologyMap X RΓ (R.map.natTrans.app (op p)) n ≫
      hypercohomologyMap X RΓ (R.obj.filtration.ι.app (op p)) n =
      hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n ≫
        hypercohomologyMap X RΓ R.map.hom n := by
    rw [← hypercohomologyMap_comp, ← hypercohomologyMap_comp, R.map.comm (op p)]
  show (hypercohomologyMap X RΓ (R.map.natTrans.app (op p)) n ≫
        (hypercohomologyIsoGlobalSectionsHomology X RΓ α
          (R.obj.filtration.obj (op p)) n).hom) ≫
      HomologicalComplex.homologyMap
        ((globalSectionsComplexFunctor X).map (R.obj.filtration.ι.app (op p))) n =
    hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n ≫
      hypercohomologyMap X RΓ R.map.hom n ≫
        (hypercohomologyIsoGlobalSectionsHomology X RΓ α R.obj.X n).hom
  rw [Category.assoc, ← hnat, ← Category.assoc, hmapComm]
  simp only [Category.assoc]

include α in
/-- Eventual vanishing of the hypercohomology of the filtration steps transports to the complex
of global sections. -/
lemma eventually_isZero_homology {n p₀ : ℤ}
    (h : ∀ p : ℤ, p₀ ≤ p → IsZero (hypercohomology X RΓ (K.filtration.obj (op p)) n)) (p : ℤ)
    (hp : p₀ ≤ p) :
    IsZero (((globalSectionsFilteredComplex X R.obj).filtration.obj (op p)).homology n) :=
  IsZero.of_iso (h p hp) (R.cmpStep RΓ α p n).symm

include α in
/-- Eventual invertibility of the maps on hypercohomology transports to the complex of global
sections. -/
lemma eventually_isIso_homologyMap {n p₁ : ℤ}
    (h : ∀ p : ℤ, p ≤ p₁ → IsIso (hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n))
    (p : ℤ) (hp : p ≤ p₁) :
    IsIso (HomologicalComplex.homologyMap
      ((globalSectionsFilteredComplex X R.obj).filtration.ι.app (op p)) n) := by
  have := h p hp
  have hformula : HomologicalComplex.homologyMap
      ((globalSectionsFilteredComplex X R.obj).filtration.ι.app (op p)) n =
      (R.cmpStep RΓ α p n).inv ≫
        hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n ≫ (R.cmpTotal RΓ α n).hom := by
    rw [← R.cmp_square RΓ α p n]
    simp
  rw [hformula]
  infer_instance

include α in
/-- The first page of the spectral sequence of the complex of global sections of the resolution is
the hypercohomology of the graded pieces of `K`. -/
lemma nonempty_firstPageIso (p q : ℤ) :
    Nonempty
      (((CochainComplex.Filtered.spectralSequenceFunctor.obj
          (globalSectionsFilteredComplex X R.obj)).page 1 (by omega)).X (p, q) ≅
        hypercohomology X RΓ ((FilteredObject.gr p).obj K) (p + q)) := by
  obtain ⟨_, _, _, hgr⟩ := FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage
    (globalSectionsFilteredComplex X R.obj)
    (CochainComplex.filtrationSubobject (globalSectionsFilteredComplex X R.obj))
    (fun _ _ ↦ rfl)
    (CochainComplex.filtrationSubobject_antitone (globalSectionsFilteredComplex X R.obj))
  obtain ⟨ePage⟩ := hgr p q (p + q) rfl
  have := R.isKInjective_gr p
  have : QuasiIso ((FilteredObject.gr p).map R.map) := R.quasiIso_gr p
  have hq : IsIso (DerivedCategory.Q.map ((FilteredObject.gr p).map R.map)) := inferInstance
  let egr : (FilteredObject.gr p).obj (globalSectionsFilteredComplex X R.obj) ≅
      (globalSectionsComplexFunctor X).obj ((FilteredObject.gr p).obj R.obj) := by
    show cokernel ((globalSectionsComplexFunctor X).map
        (R.obj.filtration.step (FilteredObject.succHom p))) ≅
      (globalSectionsComplexFunctor X).obj
        (cokernel (R.obj.filtration.step (FilteredObject.succHom p)))
    exact CochainComplex.cokernelMapIsoOfInjective
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤))
      (R.obj.filtration.step (FilteredObject.succHom p))
      (fun n ↦ R.injective_step (p + 1) n)
  exact ⟨ePage ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) (p + q)).mapIso egr ≪≫
    (hypercohomologyIsoGlobalSectionsHomology X RΓ α
      ((FilteredObject.gr p).obj R.obj) (p + q)).symm ≪≫
    ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (p + q)).mapIso
      (RΓ.mapIso (asIso (DerivedCategory.Q.map ((FilteredObject.gr p).map R.map))))).symm⟩

include α in
/-- Eventual vanishing and eventual invertibility of the hypercohomology of the filtration steps,
transported to the complex of global sections of the resolution. -/
lemma eventually_homology_bounds
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero (hypercohomology X RΓ (K.filtration.obj (op p)) n))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n)) :
    (∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p → IsZero
      (((globalSectionsFilteredComplex X R.obj).filtration.obj (op p)).homology n)) ∧
      ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ → IsIso (HomologicalComplex.homologyMap
        ((globalSectionsFilteredComplex X R.obj).filtration.ι.app (op p)) n) :=
  ⟨fun n ↦ ⟨(hzero n).choose, R.eventually_isZero_homology RΓ α (hzero n).choose_spec⟩,
    fun n ↦ ⟨(hiso n).choose, R.eventually_isIso_homologyMap RΓ α (hiso n).choose_spec⟩⟩

include α in
/-- If the hypercohomology of the filtration steps of `K` eventually vanishes on the right and
eventually maps isomorphically to the hypercohomology of `K` on the left, then the spectral
sequence of the complex of global sections of the resolution is bounded, the induced filtration on
hypercohomology is finite, and the infinity page is its associated graded. -/
lemma converges
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero (hypercohomology X RΓ (K.filtration.obj (op p)) n))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n)) :
    (∀ n : ℤ, {p : ℤ | ¬ IsZero
      (((CochainComplex.Filtered.spectralSequenceFunctor.obj
        (globalSectionsFilteredComplex X R.obj)).page 1 (by omega)).X (p, n - p))}.Finite) ∧
      ∃ (F : ∀ n : ℤ, ℤ → Subobject (hypercohomology X RΓ K.X n))
        (hF : ∀ n : ℤ, Antitone (F n)),
        (∀ n p : ℤ, F n p = imageSubobject
          (hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n)) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
        (∀ p q : ℤ, (CochainComplex.Filtered.spectralSequenceFunctor.obj
          (globalSectionsFilteredComplex X R.obj)).HasPageInfinityAt (p, q)) ∧
        ∀ p q : ℤ, Nonempty
          ((CochainComplex.Filtered.spectralSequenceFunctor.obj
              (globalSectionsFilteredComplex X R.obj)).pageInfinity (p, q) ≅
            cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
              (hF (p + q) (by omega)))) := by
  classical
  obtain ⟨hzeroP, hisoP⟩ := R.eventually_homology_bounds RΓ α hzero hiso
  have hFHyp : ∀ n : ℤ, Antitone (fun p : ℤ ↦ (imageSubobject
      (hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n) :
        Subobject (hypercohomology X RΓ K.X n))) := by
    intro n p p' hpp'
    have hcomp : K.filtration.diagram.map (homOfLE hpp').op ≫ K.filtration.ι.app (op p) =
        K.filtration.ι.app (op p') := K.filtration.diagram_map_comp_ι_app _
    apply imageSubobject_le (hypercohomologyMap X RΓ (K.filtration.ι.app (op p')) n)
      (hypercohomologyMap X RΓ (K.filtration.diagram.map (homOfLE hpp').op) n ≫
        factorThruImageSubobject
          (hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n))
    rw [Category.assoc, imageSubobject_arrow_comp,
      ← hypercohomologyMap_comp, hcomp]
  refine ⟨CochainComplex.Filtered.finite_not_isZero_page_one _ hzeroP hisoP,
    (fun n p ↦ (imageSubobject (hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n) :
      Subobject (hypercohomology X RΓ K.X n))),
    hFHyp, fun _ _ ↦ rfl, ?_,
    fun p q ↦ CochainComplex.Filtered.hasPageInfinityAt_of_eventually _ hzeroP hisoP (p, q), ?_⟩
  · intro n
    obtain ⟨p₀, hp₀⟩ := hiso n
    obtain ⟨p₁, hp₁⟩ := hzero n
    refine ⟨p₀, max p₀ p₁, le_max_left _ _, ?_, ?_⟩
    · have h := hp₀ p₀ le_rfl
      show imageSubobject (hypercohomologyMap X RΓ (K.filtration.ι.app (op p₀)) n) = ⊤
      exact Subobject.imageSubobject_eq_top_of_epi _
    · have hz := hp₁ (max p₀ p₁) (le_max_right _ _)
      show imageSubobject (hypercohomologyMap X RΓ
        (K.filtration.ι.app (op (max p₀ p₁))) n) = ⊥
      rw [show hypercohomologyMap X RΓ (K.filtration.ι.app (op (max p₀ p₁))) n = 0 from
        hz.eq_of_src _ _, imageSubobject_zero]
  · intro p q
    obtain ⟨eGr⟩ := CochainComplex.Filtered.nonempty_pageInfinityIso_inducedFiltrationStep
      (globalSectionsFilteredComplex X R.obj) hzeroP hisoP p q
    have hleFH :
        (globalSectionsFilteredComplex X R.obj).inducedFiltrationStep (p + q) (p + 1) ≤
          (globalSectionsFilteredComplex X R.obj).inducedFiltrationStep (p + q) p :=
      (globalSectionsFilteredComplex X R.obj).inducedFiltrationStep_antitone (p + q) (by omega)
    have hImage (s : ℤ) :
        (Subobject.map (R.cmpTotal RΓ α (p + q)).hom).obj (imageSubobject
            (hypercohomologyMap X RΓ (K.filtration.ι.app (op s)) (p + q))) =
          (globalSectionsFilteredComplex X R.obj).inducedFiltrationStep (p + q) s := by
      rw [Subobject.map_imageSubobject
        (hypercohomologyMap X RΓ (K.filtration.ι.app (op s)) (p + q))
        (R.cmpTotal RΓ α (p + q))]
      calc
        _ = imageSubobject ((R.cmpStep RΓ α s (p + q)).hom ≫
            HomologicalComplex.homologyMap
              ((globalSectionsFilteredComplex X R.obj).filtration.ι.app (op s)) (p + q)) := by
              congr 1
              exact (R.cmp_square RΓ α s (p + q)).symm
        _ = _ := imageSubobject_iso_comp (R.cmpStep RΓ α s (p + q)).hom _
    have hImage' (s : ℤ) :
        (Subobject.mapIsoToOrderIso (R.cmpTotal RΓ α (p + q)).symm)
            ((globalSectionsFilteredComplex X R.obj).inducedFiltrationStep (p + q) s) =
          imageSubobject (hypercohomologyMap X RΓ (K.filtration.ι.app (op s)) (p + q)) := by
      have h : (Subobject.map (R.cmpTotal RΓ α (p + q)).inv).obj
          ((globalSectionsFilteredComplex X R.obj).inducedFiltrationStep (p + q) s) =
          imageSubobject (hypercohomologyMap X RΓ (K.filtration.ι.app (op s)) (p + q)) := by
        rw [← hImage s]
        simp_rw [← Subobject.map_comp, Iso.hom_inv_id, Subobject.map_id]
      exact h
    exact ⟨eGr ≪≫ Subobject.cokernelMapIso (R.cmpTotal RΓ α (p + q)).symm _ _ hleFH ≪≫
      Subobject.cokernelOfLEIsoOfEq
        ((Subobject.mapIsoToOrderIso (R.cmpTotal RΓ α (p + q)).symm).map_rel_iff'.2 hleFH)
        (hFHyp (p + q) (show p ≤ p + 1 by omega)) (hImage' (p + 1)) (hImage' p)⟩

end FilteredKInjectiveResolution

section Statement

attribute [local irreducible] globalSectionsFilteredComplex

variable
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)
    (K J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X)))

/-- The spectral sequence of a filtered complex of module sheaves, computed by a supplied filtered
K-injective resolution: its pages are presented by the cycle and boundary subobjects of the
filtered complex of global sections, its first page is the hypercohomology of the graded pieces,
and under the boundedness hypotheses it converges to the hypercohomology of the complex. -/
@[stacks 0BKK "computation by a supplied filtered K-injective resolution"]
theorem spectralSequence_of_filteredKInjectiveResolution
    (hRΓ : RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
    (j : K ⟶ J)
    (hj : QuasiIso j.hom)
    (hjStep : ∀ p : ℤ, QuasiIso (j.natTrans.app (op p)))
    (hjGraded : ∀ p : ℤ, QuasiIso ((FilteredObject.gr p).map j))
    (hStepInjective : ∀ p n : ℤ, Injective ((J.filtration.obj (op p)).X n))
    (hKInjective : J.X.IsKInjective)
    (hStepKInjective : ∀ p : ℤ, (J.filtration.obj (op p)).IsKInjective)
    (hGradedKInjective : ∀ p : ℤ, ((FilteredObject.gr p).obj J).IsKInjective) :
    let E := CochainComplex.Filtered.spectralSequenceFunctor.obj
      (globalSectionsFilteredComplex X J)
    ∃ (F : ∀ (_p n : ℤ), Subobject ((globalSectionsFilteredComplex X J).X.X n))
        (Z D : ∀ (_r _p n : ℤ),
          Subobject ((globalSectionsFilteredComplex X J).X.X n)),
        (∀ p n : ℤ, F p n = Subobject.mk
          (((globalSectionsFilteredComplex X J).filtration.ι.app (op p)).f n)) ∧
        (∀ r p n : ℤ, Z r p n = F p n ⊓
          (Subobject.pullback ((globalSectionsFilteredComplex X J).X.d n (n + 1))).obj
            (F (p + r) (n + 1))) ∧
        (∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
          (Subobject.«exists» ((globalSectionsFilteredComplex X J).X.d (n - 1) n)).obj
            (Z (r - 1) (p - r + 1) (n - 1))) ∧
        (∃ e : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q),
            (E.page r hr).X (p, q) ≅ cokernel
              (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)),
          ∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q),
            ∃ δ : (Z r p n : ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) ⟶
                (Z r (p + r) (n + 1) : ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))),
              δ ≫ (Z r (p + r) (n + 1)).arrow =
                  (Z r p n).arrow ≫ (globalSectionsFilteredComplex X J).X.d n (n + 1) ∧
              cokernel.π (Subobject.ofLE _ _
                  (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)) ≫
                    (e r p q n hr hn).inv ≫
                    (E.page r hr).d (p, q) (p + r, q - r + 1) =
                δ ≫ cokernel.π (Subobject.ofLE _ _
                    (inf_le_right : D r (p + r) (n + 1) ⊓ Z r (p + r) (n + 1) ≤
                      Z r (p + r) (n + 1))) ≫
                  (e r (p + r) (q - r + 1) (n + 1) hr (by omega)).inv) ∧
        (∀ p q : ℤ, Nonempty
          ((E.page 1 (by omega)).X (p, q) ≅
            hypercohomology X RΓ ((FilteredObject.gr p).obj K) (p + q))) ∧
        ((∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
            IsZero (hypercohomology X RΓ (K.filtration.obj (op p)) n)) →
          (∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
            IsIso (hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n)) →
          (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 1 (by omega)).X (p, n - p))}.Finite) ∧
            ∃ (F : ∀ n : ℤ, ℤ → Subobject (hypercohomology X RΓ K.X n))
              (hF : ∀ n : ℤ, Antitone (F n)),
              (∀ n p : ℤ, F n p = imageSubobject
                (hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n)) ∧
              (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
              (∀ p q : ℤ, E.HasPageInfinityAt (p, q)) ∧
              ∀ p q : ℤ, Nonempty
                (E.pageInfinity (p, q) ≅
                  cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
                    (hF (p + q) (by omega))))) := by
  have := hRΓ
  let R : FilteredKInjectiveResolution X K :=
    { obj := J, map := j, quasiIso := hj, quasiIso_step := hjStep, quasiIso_gr := hjGraded
      injective_step := hStepInjective, isKInjective := hKInjective
      isKInjective_step := hStepKInjective, isKInjective_gr := hGradedKInjective }
  exact ⟨CochainComplex.filtrationSubobject (globalSectionsFilteredComplex X J),
    FilteredComplexSpectralSequence.cycles _ _,
    FilteredComplexSpectralSequence.boundaries _ _,
    fun _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl,
    CochainComplex.Filtered.exists_pageIso_d (globalSectionsFilteredComplex X J),
    R.nonempty_firstPageIso RΓ α, R.converges RΓ α⟩

/-- A filtered complex of modules on a ringed space has a cohomological spectral sequence whose
first page is the hypercohomology of its graded pieces. If the hypercohomology of the filtration
steps eventually vanishes on the right and maps isomorphically to that of the whole complex on the
left, the spectral sequence is bounded and converges to the hypercohomology of the complex. -/
@[stacks 0BKK]
theorem exists_spectralSequence_of_filteredComplex :
    ∃ (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
        DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
      (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ),
      RΓ.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) ∧
      ∃ (J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) (j : K ⟶ J),
      QuasiIso j.hom ∧
      (∀ p : ℤ, QuasiIso (j.natTrans.app (op p))) ∧
      (∀ p : ℤ, QuasiIso ((FilteredObject.gr p).map j)) ∧
      (∀ n : ℤ, Injective (J.X.X n)) ∧
      (∀ p n : ℤ, Injective ((J.filtration.obj (op p)).X n)) ∧
      (∀ p n : ℤ, Injective (((FilteredObject.gr p).obj J).X n)) ∧
      ∃ (E : CohomologicalSpectralSequence
          (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) 0)
        (F : ∀ (_p n : ℤ), Subobject ((globalSectionsFilteredComplex X J).X.X n))
        (Z D : ∀ (_r _p n : ℤ),
          Subobject ((globalSectionsFilteredComplex X J).X.X n)),
        (∀ p n : ℤ, F p n = Subobject.mk
          (((globalSectionsFilteredComplex X J).filtration.ι.app (op p)).f n)) ∧
        (∀ r p n : ℤ, Z r p n = F p n ⊓
          (Subobject.pullback ((globalSectionsFilteredComplex X J).X.d n (n + 1))).obj
            (F (p + r) (n + 1))) ∧
        (∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
          (Subobject.«exists» ((globalSectionsFilteredComplex X J).X.d (n - 1) n)).obj
            (Z (r - 1) (p - r + 1) (n - 1))) ∧
        (∃ e : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q),
            (E.page r hr).X (p, q) ≅ cokernel
              (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)),
          ∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q),
            ∃ δ : (Z r p n : ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) ⟶
                (Z r (p + r) (n + 1) : ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))),
              δ ≫ (Z r (p + r) (n + 1)).arrow =
                  (Z r p n).arrow ≫ (globalSectionsFilteredComplex X J).X.d n (n + 1) ∧
              cokernel.π (Subobject.ofLE _ _
                  (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)) ≫
                    (e r p q n hr hn).inv ≫
                    (E.page r hr).d (p, q) (p + r, q - r + 1) =
                δ ≫ cokernel.π (Subobject.ofLE _ _
                    (inf_le_right : D r (p + r) (n + 1) ⊓ Z r (p + r) (n + 1) ≤
                      Z r (p + r) (n + 1))) ≫
                  (e r (p + r) (q - r + 1) (n + 1) hr (by omega)).inv) ∧
        (∀ p q : ℤ, Nonempty
          ((E.page 1 (by omega)).X (p, q) ≅
            hypercohomology X RΓ ((FilteredObject.gr p).obj K) (p + q))) ∧
        ((∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
            IsZero (hypercohomology X RΓ (K.filtration.obj (op p)) n)) →
          (∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
            IsIso (hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n)) →
          (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 1 (by omega)).X (p, n - p))}.Finite) ∧
            ∃ (F : ∀ n : ℤ, ℤ → Subobject (hypercohomology X RΓ K.X n))
              (hF : ∀ n : ℤ, Antitone (F n)),
              (∀ n p : ℤ, F n p = imageSubobject
                (hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n)) ∧
              (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
              (∀ p q : ℤ, E.HasPageInfinityAt (p, q)) ∧
              ∀ p q : ℤ, Nonempty
                (E.pageInfinity (p, q) ≅
                  cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
                    (hF (p + q) (by omega))))) := by
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing X)) := inferInstance
  have H := Stacks.Injectives.exists_filtered_quasiIso_isKInjective K
  obtain ⟨J, j, h⟩ := H
  have hI := h.1
  have hIStep := h.2.1
  have hISubquot := h.2.2.2.1
  have hKI := h.2.2.2.2.1
  have hKIStep := h.2.2.2.2.2.1
  have hKISubquot := h.2.2.2.2.2.2.2.1
  have hj := h.2.2.2.2.2.2.2.2.1
  have hjStep := h.2.2.2.2.2.2.2.2.2.1
  have hjSubquot := h.2.2.2.2.2.2.2.2.2.2.2
  have hIGraded (p n : ℤ) : Injective (((FilteredObject.gr p).obj J).X n) :=
    hISubquot p (p + 1) (by omega) n
  have hKIGraded (p : ℤ) : ((FilteredObject.gr p).obj J).IsKInjective :=
    hKISubquot p (p + 1) (by omega)
  have hjGraded (p : ℤ) : QuasiIso ((FilteredObject.gr p).map j) :=
    hjSubquot p (p + 1) (by omega)
  have hRΓ : (derivedSections (structureSheafRing X) (⊤ : Opens X.carrier)).IsRightDerivedFunctor
      ((homotopySections (structureSheafRing X) (⊤ : Opens X.carrier)).totalRightDerivedUnit
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :=
    inferInstance
  exact ⟨_, _, hRΓ, J, j, hj, hjStep, hjGraded, hI, hIStep, hIGraded,
    CochainComplex.Filtered.spectralSequenceFunctor.obj (globalSectionsFilteredComplex X J),
    spectralSequence_of_filteredKInjectiveResolution X _ _ K J hRΓ j hj hjStep hjGraded
      hIStep hKI hKIStep hKIGraded⟩

end Statement

end Stacks.Cohomology.FilteredComplex
