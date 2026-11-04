module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.TildeUnit
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# The module `M~` is quasi-coherent

Let `U` be a scheme over `S` with ring of global functions `A`.  For an `A`-module `M`, the sheaf
`M~` on the fppf site of `U` (`AlgebraicGeometry.Stack.tildeFunctor`) is the cokernel of a map
between free sheaves of modules: `M` is the cokernel of a map of free `A`-modules, `M ↦ M~`
preserves colimits, and it carries `A` to the structure sheaf.  Hence `M~` has a global
presentation, and it is quasi-coherent.

## Main definitions

* `AlgebraicGeometry.Stack.tildeFinsupp`: `(A^{(ι)})~ ≅ 𝒪_U^{(ι)}`.
* `AlgebraicGeometry.Stack.tildePresentation`: a global presentation of `M~`.

## Main results

* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_tilde`: `M~` is quasi-coherent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] FibredSite.hasWeakSheafify_associatedTopology
  FibredSite.wEqualsLocallyBijective_associatedTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (U : BigFppfOver B S hS)

local notation "𝒪[" Y "]" => AlgebraicStacks.fppfStructureRingSheaf _ _ _ Y

/-- The fppf site of `U`, as the fibred site of the algebraic stack `Sch/U`, is essentially
small. -/
instance essentiallySmall_schemeStack :
    EssentiallySmall.{u} (schemeStack.{u, w} B S hS U).val.val.obj :=
  essentiallySmall_over_bigFppfOver U

/-- `M ↦ M~` preserves colimits indexed by small categories in the lowest universe. -/
instance preservesColimitsOfSize_zero_tildeFunctor :
    PreservesColimitsOfSize.{0, 0} (tildeFunctor.{u, w} U) :=
  preservesColimitsOfSize_shrink.{0, u, 0, u} _

/-- `M ↦ M~` preserves zero morphisms. -/
instance : (tildeFunctor.{u, w} U).PreservesZeroMorphisms := inferInstance

/-- Sheafification on the fppf site of `U` exists and is left exact, the site being essentially
small. -/
instance hasSheafify_schemeStack :
    HasSheafify (AlgebraicStacks.fppfSiteTopology B S hS (schemeStack.{u, w} B S hS U))
      AddCommGrpCat.{u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u} _

/-- **`(A^{(ι)})~ ≅ 𝒪_U^{(ι)}`**: `M ↦ M~` carries free modules to free sheaves of modules. -/
noncomputable def tildeFinsupp (ι : Type u) :
    (tildeFunctor.{u, w} U).obj (ModuleCat.of (schemeGlobalRing U) (ι →₀ schemeGlobalRing U)) ≅
      SheafOfModules.free.{u} (R := 𝒪[schemeStack.{u, w} B S hS U]) ι :=
  letI H : IsColimit <| (tildeFunctor.{u, w} U).mapCocone
      (ModuleCat.finsuppCocone (schemeGlobalRing U) (schemeGlobalRing U) ι) :=
    isColimitOfPreserves (tildeFunctor.{u, w} U)
      (ModuleCat.finsuppCoconeIsColimit (schemeGlobalRing U) (schemeGlobalRing U) ι)
  letI iso : (Discrete.functor fun (_ : ι) ↦ ModuleCat.of (schemeGlobalRing U)
      (schemeGlobalRing U)) ⋙ tildeFunctor.{u, w} U ≅
        Discrete.functor fun _ ↦ SheafOfModules.unit _ :=
    Discrete.natIso (fun _ ↦ tildeSelfIso.{u, w} U)
  IsColimit.coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv iso.symm _).symm H) (coproductIsCoproduct _)

variable {U} in
/-- **A global presentation of `M~`**, from a presentation of `M` by generators `s` and
relations `t`. -/
noncomputable def tildePresentation {M : Type u} [AddCommGroup M] [Module (schemeGlobalRing U) M]
    (s : Set M) (hs : Submodule.span (schemeGlobalRing U) s = ⊤)
    (t : Set (s →₀ schemeGlobalRing U))
    (ht : Submodule.span (schemeGlobalRing U) t =
      LinearMap.ker (Finsupp.linearCombination (schemeGlobalRing U) ((↑) : s → M))) :
    ((tildeFunctor.{u, w} U).obj (ModuleCat.of (schemeGlobalRing U) M)).Presentation := by
  haveI H₁ : Function.Exact
      (ModuleCat.ofHom (Finsupp.linearCombination (α := t) (schemeGlobalRing U) (↑)))
      (ModuleCat.ofHom (Finsupp.linearCombination (α := s) (M := M) (schemeGlobalRing U) (↑))) :=
    (LinearMap.exact_iff.mpr (by simp [Finsupp.range_linearCombination, ht]))
  refine SheafOfModules.presentationOfIsCokernelFree.{u}
      ((tildeFinsupp.{u, w} U t).inv ≫ (tildeFunctor.{u, w} U).map
        (ModuleCat.ofHom (Finsupp.linearCombination (schemeGlobalRing U) (↑))) ≫
          (tildeFinsupp.{u, w} U s).hom)
      ((tildeFinsupp.{u, w} U s).inv ≫ (tildeFunctor.{u, w} U).map
        (ModuleCat.ofHom (Finsupp.linearCombination (schemeGlobalRing U) (↑)))) (by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Preadditive.IsIso.comp_left_eq_zero]
    rw [← Functor.map_comp, ← ModuleCat.ofHom_comp]
    rw [show (Finsupp.linearCombination (schemeGlobalRing U) ((↑) : s → M)) ∘ₗ
        (Finsupp.linearCombination (α := t) (schemeGlobalRing U) (↑)) = 0 from
      H₁.linearMap_comp_eq_zero]
    exact (tildeFunctor.{u, w} U).map_zero _ _) ?_
  letI h₁ := ModuleCat.isColimitCokernelCofork _ _ H₁
    (by simp [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hs])
  refine IsCokernel.ofIso _ (CokernelCofork.mapIsColimit _ h₁ (tildeFunctor.{u, w} U)) _
    (tildeFinsupp.{u, w} U t) (tildeFinsupp.{u, w} U s) (.refl _) (by simp) (by simp)

variable {U} in
/-- **`M~` is quasi-coherent** for every module `M` over the global functions of `U`. -/
theorem isQuasicoherentOnSite_tilde (M : ModuleCat.{u} (schemeGlobalRing U)) :
    ((tildeFunctor.{u, w} U).obj M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentation
    (tildePresentation (M := M) Set.univ (by simp) _ (Submodule.span_eq _))

end AlgebraicGeometry.Stack
