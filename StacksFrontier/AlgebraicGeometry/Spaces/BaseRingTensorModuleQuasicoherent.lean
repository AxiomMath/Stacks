module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSheavesProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf

/-!
# `𝒪_X ⊗_R M` is quasi-coherent

Let `X` be an algebraic space and `R` a ring with a ring map `φ` to the global functions of the
model of the small étale site of `X`.  The `𝒪_X`-module `𝒪_X ⊗_R M` of
`AlgebraicGeometry.Space.baseRingTensorModule` is quasi-coherent for every `R`-module `M`.

## Main definitions

* `ModuleCat.freeCover` and `ModuleCat.freeRelations`: the presentation of a module by the free
  module on its elements and the free module on the kernel, with `ModuleCat.isColimitFreeCover`.
* `Stacks.Cohomology.SiteModules.baseRingTensorSelfIso`: `𝒪_X ⊗_R R ≅ 𝒪_X` on any site.
* `AlgebraicGeometry.Space.baseRingTensorModuleSelfIso`: the same on an algebraic space.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_baseRingTensorModule`: `𝒪_X ⊗_R M` is
  quasi-coherent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u v t

namespace ModuleCat

variable (R : Type t) [CommRing R] (M : ModuleCat.{t} R)

/-- The canonical surjection `R^{(M)} ⟶ M` from the free module on the elements of a module. -/
def freeCover : ModuleCat.of R (M →₀ R) ⟶ M :=
  ModuleCat.ofHom (Finsupp.linearCombination R (fun m : M => m))

/-- `ModuleCat.freeCover` sends the basis vector at `m` to `m`. -/
theorem freeCover_single (m : M) : (freeCover R M).hom (Finsupp.single m 1) = m := by
  change Finsupp.linearCombination R (fun m : M => m) (Finsupp.single m 1) = m
  rw [Finsupp.linearCombination_single, one_smul]

/-- The free module on the kernel of `ModuleCat.freeCover`, mapping to the free module on the
elements by the inclusion of that kernel. -/
def freeRelations :
    ModuleCat.of R (LinearMap.ker (freeCover R M).hom →₀ R) ⟶ ModuleCat.of R (M →₀ R) :=
  ModuleCat.ofHom (Finsupp.linearCombination R
    (fun k : LinearMap.ker (freeCover R M).hom => k.1))

/-- `ModuleCat.freeRelations` sends the basis vector at `k` to the element `k` of the free module
on the elements. -/
theorem freeRelations_single (k : LinearMap.ker (freeCover R M).hom) :
    (freeRelations R M).hom (Finsupp.single k 1) = k.1 := by
  change Finsupp.linearCombination R _ (Finsupp.single k 1) = k.1
  rw [Finsupp.linearCombination_single, one_smul]

/-- The composite of `ModuleCat.freeRelations` and `ModuleCat.freeCover` is zero. -/
theorem freeRelations_comp_freeCover : freeRelations R M ≫ freeCover R M = 0 := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun k => LinearMap.ext fun a => ?_)
  have h : (freeRelations R M).hom (Finsupp.single k a) = a • k.1 :=
    Finsupp.linearCombination_single _ _ _
  change (freeCover R M).hom ((freeRelations R M).hom (Finsupp.single k a)) = 0
  rw [h, map_smul, LinearMap.mem_ker.1 k.2, smul_zero]

/-- **Every module is the cokernel of a map of free modules**: of the free module on the kernel
of its free cover into the free module on its elements. -/
def isColimitFreeCover :
    IsColimit (CokernelCofork.ofπ (freeCover R M) (freeRelations_comp_freeCover R M)) := by
  haveI : Epi (freeCover R M) := (ModuleCat.epi_iff_surjective _).2 fun m =>
    ⟨Finsupp.single m 1, freeCover_single R M m⟩
  have hexact : (ShortComplex.mk (freeRelations R M) (freeCover R M)
      (freeRelations_comp_freeCover R M)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact ⟨Finsupp.single ⟨x, hx⟩ 1, freeRelations_single R M ⟨x, hx⟩⟩
  exact hexact.gIsCokernel

/-- Linear maps out of the ring are its values at `1`. -/
def selfHomEquiv : (ModuleCat.of R R ⟶ M) ≃ M where
  toFun g := g.hom 1
  invFun m := ModuleCat.ofHom (LinearMap.toSpanSingleton R M m)
  left_inv g := ModuleCat.hom_ext (LinearMap.ext_ring (by simp))
  right_inv m := by simp

end ModuleCat

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {O : Sheaf J CommRingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Type u} [CommRing R] (φ : R →+* GlobalFunctionRing O)

/-- `𝒪_X ⊗_R R` corepresents global sections. -/
def baseRingTensorSelfCorepresentableBy :
    (SheafOfModules.sectionsFunctor (ringSheafOfSite O)).CorepresentableBy
      ((baseRingTensorFunctor.{u, v, u, u} φ).obj (ModuleCat.of R R)) where
  homEquiv {F} := (baseRingTensorHomEquiv φ (ModuleCat.of R R) F).trans
    (ModuleCat.selfHomEquiv R _)
  homEquiv_comp {F G} g f := by
    change (baseRingTensorHomEquiv φ (ModuleCat.of R R) G (f ≫ g)).hom 1 =
      ((baseRingGlobalSectionsFunctor φ).map g).hom
        ((baseRingTensorHomEquiv φ (ModuleCat.of R R) F f).hom 1)
    rw [baseRingTensorHomEquiv, Adjunction.homEquiv_naturality_right]
    rfl

/-- **`𝒪_X ⊗_R R ≅ 𝒪_X`**. -/
def baseRingTensorSelfIso :
    (baseRingTensorFunctor.{u, v, u, u} φ).obj (ModuleCat.of R R) ≅
      SheafOfModules.unit (ringSheafOfSite O) :=
  (baseRingTensorSelfCorepresentableBy φ).uniqueUpToIso
    { homEquiv := SheafOfModules.unitHomEquiv _
      homEquiv_comp := fun _ _ => rfl }

end Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)

/-- **`𝒪_X ⊗_R R ≅ 𝒪_X` on an algebraic space.** -/
def baseRingTensorModuleSelfIso :
    (baseRingTensorModule B S hS X φ).obj (ModuleCat.of R R) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O) :=
  (smallEtaleModelModulesEquiv B S hS X).inverse.mapIso (baseRingTensorSelfIso φ) ≪≫
    ((smallEtaleModelModulesEquiv B S hS X).unitIso.app (SheafOfModules.unit _)).symm

/-- `𝒪_X ⊗_R R` is quasi-coherent. -/
theorem isQuasicoherentOnSite_baseRingTensorModule_self :
    ((baseRingTensorModule B S hS X φ).obj (ModuleCat.of R R)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (baseRingTensorModuleSelfIso B S hS X φ).symm
    (SheafOfModules.isQuasicoherentOnSite_unit _)

/-- `𝒪_X ⊗_R -` carries a colimit of `R`-modules whose terms it makes quasi-coherent to a
quasi-coherent module, for an essentially small indexing category of any size. -/
private theorem isQuasicoherentOnSite_baseRingTensorModule_of_isColimit_aux (K : Type*)
    [Category* K] [EssentiallySmall.{u} K] (D : K ⥤ ModuleCat.{u} R) (c : Cocone D)
    (hc : IsColimit c)
    (hD : ∀ k, ((baseRingTensorModule B S hS X φ).obj (D.obj k)).IsQuasicoherentOnSite) :
    ((baseRingTensorModule B S hS X φ).obj c.pt).IsQuasicoherentOnSite := by
  have : PreservesColimitsOfShape K (baseRingTensorModule B S hS X φ) :=
    (baseRingTensorModuleAdjunction B S hS X
      φ).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have := isClosedUnderColimitsOfShape_quasicoherentSheaves_of_essentiallySmall B S hS X.1 X.2 K
  exact ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (baseRingTensorModule B S hS X φ) hc) hD

/-- `𝒪_X ⊗_R -` carries a colimit of `R`-modules whose terms it makes quasi-coherent to a
quasi-coherent module. -/
theorem isQuasicoherentOnSite_baseRingTensorModule_of_isColimit (K : Type) [SmallCategory K]
    [EssentiallySmall.{u} K] (D : K ⥤ ModuleCat.{u} R) (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ k, ((baseRingTensorModule B S hS X φ).obj (D.obj k)).IsQuasicoherentOnSite) :
    ((baseRingTensorModule B S hS X φ).obj c.pt).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_baseRingTensorModule_of_isColimit_aux B S hS X φ K D c hc hD

/-- `𝒪_X ⊗_R R^{(ι)}` is quasi-coherent. -/
theorem isQuasicoherentOnSite_baseRingTensorModule_free (ι : Type u) :
    ((baseRingTensorModule B S hS X φ).obj (ModuleCat.of R (ι →₀ R))).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_baseRingTensorModule_of_isColimit_aux B S hS X φ (Discrete ι)
    (Discrete.functor fun _ => ModuleCat.of R R) (ModuleCat.finsuppCocone R R ι)
    (ModuleCat.finsuppCoconeIsColimit R R ι) fun _ =>
      isQuasicoherentOnSite_baseRingTensorModule_self B S hS X φ

/-- **`𝒪_X ⊗_R M` is quasi-coherent**, for every `R`-module `M`. -/
theorem isQuasicoherentOnSite_baseRingTensorModule (M : ModuleCat.{u} R) :
    ((baseRingTensorModule B S hS X φ).obj M).IsQuasicoherentOnSite := by
  have : EssentiallySmall.{u} WalkingParallelPair := essentiallySmall_of_small_of_locallySmall _
  have hD : ∀ k, ((baseRingTensorModule B S hS X φ).obj
      ((parallelPair (ModuleCat.freeRelations R M) 0).obj k)).IsQuasicoherentOnSite := by
    rintro (_ | _) <;> exact isQuasicoherentOnSite_baseRingTensorModule_free B S hS X φ _
  exact isQuasicoherentOnSite_baseRingTensorModule_of_isColimit B S hS X φ
    WalkingParallelPair (parallelPair (ModuleCat.freeRelations R M) 0)
    (CokernelCofork.ofπ (ModuleCat.freeCover R M) (ModuleCat.freeRelations_comp_freeCover R M))
    (ModuleCat.isColimitFreeCover R M) hD

end AlgebraicGeometry.Space

end
