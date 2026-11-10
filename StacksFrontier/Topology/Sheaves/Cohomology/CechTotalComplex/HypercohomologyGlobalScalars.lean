module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBrutalCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyShiftedSingleCochains
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedIdempotentSplitting

/-!
# Multiplication by a global function acts on hypercohomology by scalar multiplication

Let `(X, 𝒪_X)` be a ringed space, `ℱ` an `𝒪_X`-module and `s ∈ Γ(X, 𝒪_X)`. Multiplication by `s`
is an endomorphism of `ℱ`; on the hypercohomology `H^n(X, ℱ[-a])`, a module over `Γ(X, 𝒪_X)`, it
induces multiplication by `s`, when Čech cohomology computes the cohomology of `ℱ[-a]`.

## Main results

* `Stacks.Cech.Hypercohomology.hypercohomologyMap_smulHom_cechCocycleClassAt`: multiplication by
  `s` acts on the class of a Čech cocycle by scalar multiplication.
* `Stacks.Cech.Hypercohomology.hypercohomologyMap_smulHom`: multiplication by `s` acts on
  `H^n(X, ℱ[-a])` by scalar multiplication.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing sectionsPresheafFunctor sectionsPresheaf coverObject
  abSections)
open Stacks.Cech.LinearCupProduct (cechCochainsMap ιTotalCechTo)
open Stacks.Cohomology.InvertibleDerived (smulHom)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

/-- A morphism out of the ring is determined by its value at `1`: the morphism attached to its
value at `r` is `r` times the morphism. -/
theorem toMor_apply_eq_smul {R : Type u} [CommRing R] {M : ModuleCat.{u} R}
    (z : unitModule R ⟶ M) (r : R) : toMor (z r) = r • z := by
  ext : 1
  refine LinearMap.ext_ring ?_
  rw [toMor_apply_one, ModuleCat.hom_smul, LinearMap.smul_apply, ← map_smul, smul_eq_mul, mul_one]

variable {X : AlgebraicGeometry.RingedSpace.{u, u}} (s : X.presheaf.obj (op ⊤))
  {I : Type u} (U : I → Opens X.carrier) (hU : ⊤ = ⨆ i, U i)
  (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) (a : ℤ)

/-- **On Čech cochains, multiplication by `s` is the action of `s` through the global
sections**, as morphisms out of the ring. -/
theorem sliceMor_push_smulHom {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    sliceMor U hU F (Stacks.Cohomology.CechOne.push U
        ((SheafOfModules.toSheaf _).map (smulHom s F)).hom p c) =
      toMor (show SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤ from s) ≫
        sliceMor U hU F c := by
  let : CommRing (SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤) :=
    Stacks.Cech.Refinement.sectionCommRing (O := X.sheaf) ⊤
  refine (sliceMor_map U hU (smulHom s F) c).symm.trans ?_
  refine Limits.Pi.hom_ext _ _ fun t => ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  have h1 := congrArg (fun g => (sliceMor U hU F c ≫ g).hom
      (1 : SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤))
    (Stacks.Cech.LinearCupProduct.cechCochainsMap_comp_π (coverObject U hU)
      (SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤)
      ((sectionsPresheafFunctor ⊤).map (smulHom s F)) p t)
  refine h1.trans ?_
  let π := CategoryTheory.CechComplex.π (coverObject U hU) ((sectionsPresheafFunctor ⊤).obj F) p t
  refine Eq.trans (?_ : _ =
    (show SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤ from s) •
      π.hom ((sliceMor U hU F c).hom 1)) ?_
  · rfl
  · refine (map_smul π.hom _ _).symm.trans ?_
    change π.hom _ = π.hom ((sliceMor U hU F c).hom ((toMor
      (show SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤ from s)).hom 1))
    rw [toMor_apply_one, ← map_smul]
    exact congrArg (fun z => π.hom ((sliceMor U hU F c).hom z)) (mul_one _)

/-- **On the attached cochains of the total Čech complex, multiplication by `s` is scalar
multiplication by `s`.** -/
theorem cochainOfAt_push_smulHom {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    letI : CommRing (SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤) :=
      Stacks.Cech.Refinement.sectionCommRing (O := X.sheaf) ⊤
    cochainOfAt U hU F a (Stacks.Cohomology.CechOne.push U
        ((SheafOfModules.toSheaf _).map (smulHom s F)).hom p c) =
      (show SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤ from s) •
        cochainOfAt U hU F a c := by
  let : CommRing (SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤) :=
    Stacks.Cech.Refinement.sectionCommRing (O := X.sheaf) ⊤
  have h := congrArg (· ≫ cechCochainsMap (coverObject U hU)
      (SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤)
      (singleXIsoAt X.sheaf F a a rfl).inv p ≫
    ιTotalCechTo (coverObject U hU) (SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤)
      (sectionsKAt F a) p a ((p : ℤ) + a) rfl) (sliceMor_push_smulHom s U hU F c)
  refine h.trans ((Category.assoc _ _ _).trans ?_)
  exact (toMor_comp _ _).trans (toMor_apply_eq_smul (cochainOfAt U hU F a c) _)

/-- **Multiplication by `s` acts on the class of a Čech cocycle by scalar multiplication.** -/
theorem hypercohomologyMap_smulHom_cechCocycleClassAt {p : ℕ}
    (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    hypercohomologyMap X.sheaf (singlePlusMapAt X.sheaf (smulHom s F) a) ((p : ℤ) + a)
        (cechCocycleClassAt U hU F a c hc) =
      (show SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤ from s) •
        cechCocycleClassAt U hU F a c hc := by
  let : CommRing (SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤) :=
    Stacks.Cech.Refinement.sectionCommRing (O := X.sheaf) ⊤
  refine (hypercohomologyMap_cechCocycleClassAt U hU a (smulHom s F) c hc).trans ?_
  have hz := cochainOfAt_d_eq_zero U hU F a c hc
  have h := cocycleClass_congr ((p : ℤ) + a) (cochainOfAt_push_smulHom s U hU F a c)
    (cochainOfAt_d_eq_zero U hU F a _ (by rw [← Stacks.Cohomology.CechOne.push_cechD, hc,
      map_zero]))
    (by rw [Linear.smul_comp, hz, smul_zero])
  refine (congrArg (fun φ => cechClass X.sheaf U hU (singlePlus X.sheaf F a) ((p : ℤ) + a)
    (φ (1 : SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤)))
    (h.trans (cocycleClass_smul _ _ _ hz _))).trans ?_
  exact map_smul _ _ _

variable {U hU} in
/-- **Multiplication by a global function `s` acts on hypercohomology by scalar multiplication**:
on `H^n(X, ℱ[-a])`, when Čech cohomology computes the cohomology of `ℱ[-a]`, the morphism induced
by multiplication by `s` on `ℱ` is multiplication by `s`. -/
theorem hypercohomologyMap_smulHom (hF : CechComputes X.sheaf (singlePlus X.sheaf F a)) (n : ℤ)
    (x : hypercohomology X.sheaf (singlePlus X.sheaf F a) n) :
    hypercohomologyMap X.sheaf (singlePlusMapAt X.sheaf (smulHom s F) a) n x =
      (show SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤ from s) • x := by
  by_cases hn : n < a
  · exact (ModuleCat.subsingleton_of_isZero
      (isZero_hypercohomology_singlePlus_of_lt X.sheaf F hn)).elim _ _
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = (p : ℤ) + a := ⟨(n - a).toNat, by omega⟩
    obtain ⟨J, V, hV, c, hc, rfl⟩ := exists_cechCocycleClassAt_eq F a hF p x
    exact hypercohomologyMap_smulHom_cechCocycleClassAt s V hV F a c hc

end Stacks.Cech.Hypercohomology
