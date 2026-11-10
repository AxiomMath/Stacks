module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Normality

/-!
# The levelwise kernels of a morphism of ℓ-adic sheaves

The levelwise kernels of a morphism `Φ : F ⟶ G` of ℓ-adic sheaves form an inverse system: the
transition map of `F` restricts to one between them. When `Φ` is an epimorphism that restricted
transition map is again an epimorphism, so the levelwise kernels form an inverse system of
constructible sheaves with surjective transition maps.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.rawKernelTransition`: the transition map between
  consecutive levelwise kernels.
* `Stacks.EtaleCohomology.LAdicSheaf.rawKernelReduction`: its mate, out of the scalar reduction
  of the levelwise kernel one level up.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.rawKernelReduction_epi` and `.rawKernelTransition_epi`: for
  an epimorphism of ℓ-adic sheaves both are epimorphisms.

## References

* [Stacks Project, Tag 03UO](https://stacks.math.columbia.edu/tag/03UO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u u₁ u₂ v₁ v₂

namespace Stacks.EtaleCohomology

/-- The mate of a commuting square along an adjunction commutes. -/
public theorem mate_square
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {A' B' : C} {A B : D} (f' : A' ⟶ B') (f : A ⟶ B)
    (tA : A' ⟶ R.obj A) (tB : B' ⟶ R.obj B) (w : f' ≫ tB = tA ≫ R.map f) :
    L.map f' ≫ (adj.homEquiv B' B).symm tB = (adj.homEquiv A' A).symm tA ≫ f := by
  apply (adj.homEquiv A' B).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simpa only [Equiv.apply_symm_apply] using w

/-- The kernel comparison of a left adjoint between abelian categories at an epimorphism is an
epimorphism. -/
public theorem kernelComparison_epi_of_epi
    {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (L : C ⥤ D) [L.PreservesZeroMorphisms] [L.IsLeftAdjoint]
    {A B : C} (f : A ⟶ B) [Epi f] : Epi (kernelComparison f L) := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  exact ((S.exact_of_f_is_kernel (kernelIsKernel f)).map_of_epi_of_preservesCokernel L
    inferInstance inferInstance).epi_kernelLift

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [Fact ℓ.Prime] [IsNoetherian X.1]

namespace LAdicSheaf

variable {B X ℓ}

/-- The components of a morphism of ℓ-adic sheaves commute with the reduction maps of the
compatibility condition. -/
public theorem reductionMap_naturality {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ) :
    (scalarReductionFunctor B X ℓ n).map (f.app (n + 1)) ≫
        FiniteLevelSheaf.scalarReductionMap B X ℓ n (G.level (n + 1)) (G.level n)
          (G.transition n) =
      FiniteLevelSheaf.scalarReductionMap B X ℓ n (F.level (n + 1)) (F.level n)
          (F.transition n) ≫ f.app n :=
  mate_square (scalarAdjunction B X ℓ n) (f.app (n + 1)) (f.app n) (F.transition n)
    (G.transition n) (f.naturality n)

/-- The transition map between consecutive levelwise kernels of a morphism of ℓ-adic
sheaves. -/
public def rawKernelTransition {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ) :
    kernel (f.app (n + 1)) ⟶ (restrictScalarsFunctor B X ℓ n).obj (kernel (f.app n)) := by
  haveI : (restrictScalarsFunctor B X ℓ n).IsRightAdjoint :=
    (scalarAdjunction B X ℓ n).isRightAdjoint
  refine kernel.lift ((restrictScalarsFunctor B X ℓ n).map (f.app n))
    (kernel.ι (f.app (n + 1)) ≫ F.transition n) ?_ ≫
      (PreservesKernel.iso (restrictScalarsFunctor B X ℓ n) (f.app n)).inv
  rw [Category.assoc, ← f.naturality n, ← Category.assoc, kernel.condition, zero_comp]

/-- The transition map between levelwise kernels lies over the transition map of the source. -/
public theorem rawKernelTransition_fac {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ) :
    rawKernelTransition f n ≫ (restrictScalarsFunctor B X ℓ n).map (kernel.ι (f.app n)) =
      kernel.ι (f.app (n + 1)) ≫ F.transition n := by
  have : (restrictScalarsFunctor B X ℓ n).IsRightAdjoint :=
    (scalarAdjunction B X ℓ n).isRightAdjoint
  change (kernel.lift ((restrictScalarsFunctor B X ℓ n).map (f.app n))
      (kernel.ι (f.app (n + 1)) ≫ F.transition n) _ ≫
      (PreservesKernel.iso (restrictScalarsFunctor B X ℓ n) (f.app n)).inv) ≫
      (restrictScalarsFunctor B X ℓ n).map (kernel.ι (f.app n)) = _
  rw [Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]

/-- The mate of the transition map between levelwise kernels, out of the scalar reduction of
the levelwise kernel one level up. -/
public def rawKernelReduction {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ) :
    (scalarReductionFunctor B X ℓ n).obj (kernel (f.app (n + 1))) ⟶ kernel (f.app n) :=
  ((scalarAdjunction B X ℓ n).homEquiv _ _).symm (rawKernelTransition f n)

/-- The mate of the transition map between levelwise kernels lies over the reduction map of the
compatibility condition. -/
public theorem rawKernelReduction_fac {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ) :
    rawKernelReduction f n ≫ kernel.ι (f.app n) =
      (scalarReductionFunctor B X ℓ n).map (kernel.ι (f.app (n + 1))) ≫
        FiniteLevelSheaf.scalarReductionMap B X ℓ n (F.level (n + 1)) (F.level n)
          (F.transition n) :=
  (mate_square (scalarAdjunction B X ℓ n) (kernel.ι (f.app (n + 1))) (kernel.ι (f.app n))
    (rawKernelTransition f n) (F.transition n) (rawKernelTransition_fac f n).symm).symm

/-- For an epimorphism of ℓ-adic sheaves the mate of the transition map between levelwise
kernels is an epimorphism. -/
public theorem rawKernelReduction_epi {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) [Epi f]
    (n : ℕ) : Epi (rawKernelReduction f n) := by
  have := (epi_iff_app_epi f).1 inferInstance (n + 1)
  have : (scalarReductionFunctor B X ℓ n).IsLeftAdjoint :=
    (scalarAdjunction B X ℓ n).isLeftAdjoint
  let α := FiniteLevelSheaf.scalarReductionMap B X ℓ n (F.level (n + 1)) (F.level n)
    (F.transition n)
  let β := FiniteLevelSheaf.scalarReductionMap B X ℓ n (G.level (n + 1)) (G.level n)
    (G.transition n)
  have : IsIso α := F.reduction_isIso n
  have : IsIso β := G.reduction_isIso n
  let e := kernel.mapIso ((scalarReductionFunctor B X ℓ n).map (f.app (n + 1))) (f.app n)
    (asIso α) (asIso β) (reductionMap_naturality f n)
  have heq : rawKernelReduction f n =
      kernelComparison (f.app (n + 1)) (scalarReductionFunctor B X ℓ n) ≫ e.hom := by
    apply (cancel_mono (kernel.ι (f.app n))).1
    rw [rawKernelReduction_fac]
    change _ = kernelComparison (f.app (n + 1)) (scalarReductionFunctor B X ℓ n) ≫
      kernel.map ((scalarReductionFunctor B X ℓ n).map (f.app (n + 1))) (f.app n) α β
        (reductionMap_naturality f n) ≫ _
    dsimp only [kernel.map]
    rw [kernel.lift_ι, ← Category.assoc, kernelComparison_comp_ι]
  rw [heq]
  exact epi_comp' (kernelComparison_epi_of_epi (scalarReductionFunctor B X ℓ n) (f.app (n + 1)))
    inferInstance

/-- For an epimorphism of ℓ-adic sheaves the transition map between levelwise kernels is an
epimorphism. -/
public theorem rawKernelTransition_epi {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) [Epi f]
    (n : ℕ) : Epi (rawKernelTransition f n) := by
  let adj := scalarAdjunction B X ℓ n
  have hf : adj.unit.app (kernel (f.app (n + 1))) ≫
      (restrictScalarsFunctor B X ℓ n).map (rawKernelReduction f n) = rawKernelTransition f n :=
    (adj.homEquiv_unit _ _ _).symm.trans ((adj.homEquiv _ _).apply_symm_apply _)
  have := scalarAdjunction_unit_epi B X ℓ n (kernel (f.app (n + 1)))
  have := rawKernelReduction_epi f n
  rw [← hf]
  infer_instance

end LAdicSheaf

end Stacks.EtaleCohomology

end
