module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.Resolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import StacksCore.Tactic.StacksAttribute

/-! # Tensoring a short exact sequence whose third term is flat

Let `(C, O)` be a ringed site and let `0 → F'' → F' → F → 0` be a short exact sequence of
`O`-modules whose third term `F` is flat. Then tensoring with any `O`-module `G` keeps the
sequence short exact.

## Main results

* `Stacks.SheafOfModules.exists_epi_from_isFlat`: every sheaf of modules receives an epimorphism
  from a flat one.
* `Stacks.SheafOfModules.shortExact_map_sheafTensorObj`: tensoring a short exact sequence whose
  third term is flat with any sheaf of modules gives a short exact sequence.

## References

* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Every sheaf of modules on a ringed site receives an epimorphism from a *flat* sheaf of
modules. -/
theorem exists_epi_from_isFlat
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ (N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (p : N ⟶ M),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) N ∧ Epi p := by
  obtain ⟨ι, U, p, hp⟩ := exists_epi_from_sum_extensionByZero X M
  exact ⟨_, p, isFlat_of_isSumOfExtensionByZeroStructureSheaves X ⟨ι, U, ⟨Iso.refl _⟩⟩, hp⟩

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]

section Snake

variable
    (S : ShortComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- The comparison between two rows of the snake diagram, induced by a map of the sheaves one
tensors with. -/
private def tensorRowMap
    {A B : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (q : A ⟶ B) :
    S.map ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj A) ⟶
      S.map ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj B) :=
  S.mapNatTrans ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map q)

/-- A functor preserving zero morphisms sends composable maps with zero composite to
natural transformations with zero composite. -/
private lemma map_app_comp_eq_zero
    {C D E : Type*} [Category C] [Category D] [Category E] [HasZeroMorphisms C]
    [HasZeroMorphisms E] (F : C ⥤ D ⥤ E) [F.PreservesZeroMorphisms] {A B K : C}
    (q : A ⟶ B) (r : B ⟶ K) (h : q ≫ r = 0) (Y : D) :
    (F.map q).app Y ≫ (F.map r).app Y = 0 := by
  rw [← NatTrans.comp_app, ← Functor.map_comp, h, Functor.map_zero, zero_app]

/-- Two consecutive comparisons of rows compose to zero when the two maps of coefficients do. -/
private lemma tensorRowMap_comp
    {A B D : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (q : A ⟶ B) (r : B ⟶ D) (h : q ≫ r = 0) :
    tensorRowMap X S q ≫ tensorRowMap X S r = 0 := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_ <;>
    simpa only [tensorRowMap, ShortComplex.comp_τ₁, ShortComplex.comp_τ₂, ShortComplex.comp_τ₃,
      ShortComplex.mapNatTrans_τ₁, ShortComplex.mapNatTrans_τ₂, ShortComplex.mapNatTrans_τ₃,
      ShortComplex.zero_τ₁, ShortComplex.zero_τ₂, ShortComplex.zero_τ₃] using
      map_app_comp_eq_zero _ q r h _

variable {M M' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (p : M' ⟶ M)

/-- For an epimorphism `p`, tensoring the cokernel presentation `kernel p ⟶ M' ⟶ M` on the right
with `Y` gives a cokernel presentation. -/
private noncomputable def isColimit_tensorColumn (hp : Epi p)
    (Y : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsColimit (CokernelCofork.ofπ (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map p).app Y)
      (map_app_comp_eq_zero _ (kernel.ι p) p (kernel.condition p) Y)) := by
  have hker : (ShortComplex.kernelSequence p).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact p) inferInstance hp
  have := preservesFiniteColimits_sheafTensorFlipObj.{u, u, u} X.O Y
  exact CokernelCofork.mapIsColimit _ hker.gIsCokernel
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj Y)

/-- The snake input whose rows are the sequence `S` tensored with the kernel of `p`, with its
source, and with its target, and whose top row is the kernel of the comparison of the first two. -/
private noncomputable def tensorSnakeInput (hS : S.ShortExact) (hp : Epi p)
    (hM'flat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) M') :
    ShortComplex.SnakeInput
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  have hT'ex : exactFunctor _ _ ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M') :=
    exact_sheafTensorObj_of_isFlat.{u, u, u} X.O hM'flat
  have hT'lim : PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M') :=
    ((exactFunctor_iff _).1 hT'ex).1
  have hT'col : PreservesFiniteColimits ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M') :=
    ((exactFunctor_iff _).1 hT'ex).2
  have hcolK := preservesFiniteColimits_sheafTensorObj.{u, u, u} X.O (kernel p)
  have := hS.epi_g
  exact
    { L₀ := kernel (tensorRowMap X S (kernel.ι p))
      L₁ := S.map ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (kernel p))
      L₂ := S.map ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M')
      L₃ := S.map ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M)
      v₀₁ := kernel.ι (tensorRowMap X S (kernel.ι p))
      v₁₂ := tensorRowMap X S (kernel.ι p)
      v₂₃ := tensorRowMap X S p
      w₀₂ := kernel.condition _
      w₁₃ := tensorRowMap_comp X S (kernel.ι p) p (kernel.condition p)
      h₀ := kernelIsKernel _
      h₃ := by
        refine ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ ShortComplex.π₁).symm
            (isColimit_tensorColumn X p hp S.X₁)
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ ShortComplex.π₂).symm
            (isColimit_tensorColumn X p hp S.X₂)
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ ShortComplex.π₃).symm
            (isColimit_tensorColumn X p hp S.X₃)
      L₁_exact := hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance
      epi_L₁_g := preserves_epi_of_preservesColimit
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (kernel p)) S.g
      L₂_exact := (hS.map_of_exact ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M')).exact
      mono_L₂_f := (hS.map_of_exact ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M')).mono_f
        }

/-- The third term of the kernel row of `tensorSnakeInput` vanishes when `S.X₃` is flat. -/
private lemma isZero_tensorSnakeInput_L₀_X₃ (hS : S.ShortExact) (hp : Epi p)
    (hM'flat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) M')
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) S.X₃) :
    IsZero (tensorSnakeInput X S p hS hp hM'flat).L₀.X₃ := by
  have hex : exactFunctor _ _ ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj S.X₃) :=
    exactFunctor_sheafTensorFlip_of_isFlat.{u, u, u} X.O S.X₃ hflat
  have : PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj S.X₃) :=
    ((exactFunctor_iff _).1 hex).1
  have hmono₃ : Mono (ShortComplex.π₃.map (tensorRowMap X S (kernel.ι p))) :=
    preserves_mono_of_preservesLimit ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj S.X₃)
      (kernel.ι p)
  exact KernelFork.IsLimit.isZero_of_mono
    (KernelFork.mapIsLimit _ (kernelIsKernel (tensorRowMap X S (kernel.ι p)))
      ShortComplex.π₃)

end Snake

/-- Tensoring a short exact sequence of sheaves of modules whose third term is flat with any sheaf
of modules gives a short exact sequence. -/
@[stacks 03EX "part (2)", sga "1 IV 1.1" "(i)", sga "4 XVII 4.1.1" "(ii), f = id"]
theorem shortExact_map_sheafTensorObj
    (S : ShortComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) S.X₃)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (S.map ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M)).ShortExact := by
  classical
  obtain ⟨M', p, hM'flat, hp⟩ := exists_epi_from_isFlat X M
  have hcolM := preservesFiniteColimits_sheafTensorObj.{u, u, u} X.O M
  have := hS.epi_g
  have hepiT : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).map S.g) :=
    preserves_epi_of_preservesColimit ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M) S.g
  have hexT : (S.map ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M)).Exact :=
    hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance
  have hmono : Mono (S.map ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M)).f :=
    (ShortComplex.exact_iff_mono _
        ((isZero_tensorSnakeInput_L₀_X₃ X S p hS hp hM'flat hflat).eq_of_src _ _)).1
      (tensorSnakeInput X S p hS hp hM'flat).L₂'_exact
  exact ShortComplex.ShortExact.mk' hexT hmono hepiT

end Stacks.SheafOfModules

end
