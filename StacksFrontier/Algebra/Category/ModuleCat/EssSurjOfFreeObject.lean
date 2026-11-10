module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Essential surjectivity onto modules from a lift of the free module of rank one

Let `Φ : C ⥤ Mod_A` be a full additive functor out of a preadditive category with cokernels and
coproducts indexed by `Type u`, which preserves both. If some object `O` of `C` has
`Φ(O) ≅ A`, then every `A`-module is in the essential image of `Φ`: an `A`-module `N` is the
cokernel of a map `⨁_K A ⟶ ⨁_N A` of free modules, that map is `Φ` of a map
`∐_K O ⟶ ∐_N O` by fullness, and `Φ` carries the cokernel of the latter to `N`.

## Main results

* `ModuleCat.essSurj_of_full_of_preservesColimits`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat

variable {A : Type u} [Ring A]

/-- The map onto a module `M` from the coproduct of copies of `A` indexed by the elements of `M`,
which on the copy indexed by `m` is `a ↦ a • m`. -/
abbrev sigmaFreeDesc (M : ModuleCat.{u} A) : (∐ fun _ : M => ModuleCat.of A A) ⟶ M :=
  Sigma.desc fun m : M => ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)

/-- The map onto a module from the coproduct of copies of `A` indexed by its elements is an
epimorphism. -/
instance epi_sigmaFreeDesc (M : ModuleCat.{u} A) : Epi (sigmaFreeDesc M) := by
  rw [ModuleCat.epi_iff_surjective]
  intro m
  refine ⟨(Sigma.ι (fun _ : M => ModuleCat.of A A) m) (1 : A), ?_⟩
  rw [← ConcreteCategory.comp_apply, Sigma.ι_comp_desc]
  simp

variable {C : Type v} [Category.{w} C] [Preadditive C]

/-- **A full additive functor `C ⥤ Mod_A` preserving cokernels and coproducts, which hits the
free module of rank one, is essentially surjective.** -/
theorem essSurj_of_full_of_preservesColimits [HasCokernels C] [HasCoproducts.{u} C]
    (Φ : C ⥤ ModuleCat.{u} A) [Φ.Full] [Φ.Additive]
    [PreservesColimitsOfShape WalkingParallelPair Φ]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) Φ]
    (O : C) (e : Φ.obj O ≅ ModuleCat.of A A) : Φ.EssSurj where
  mem_essImage N := by
    let k := kernel.ι (sigmaFreeDesc N)
    let f := sigmaFreeDesc (kernel (sigmaFreeDesc N)) ≫ k
    let isoX (I : Type u) : Φ.obj (∐ fun _ : I => O) ≅ ∐ fun _ : I => ModuleCat.of A A :=
      PreservesCoproduct.iso Φ _ ≪≫ Sigma.mapIso fun _ => e
    let g := Φ.preimage ((isoX _).hom ≫ f ≫ (isoX _).inv)
    let hN := Abelian.epiIsCokernelOfKernel (KernelFork.ofι k (kernel.condition _))
      (kernelIsKernel (sigmaFreeDesc N))
    exact ⟨cokernel g, ⟨PreservesCokernel.iso Φ g ≪≫
      cokernelIsoOfEq (Φ.map_preimage _) ≪≫ cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫
      cokernelEpiComp _ _ ≪≫ (colimit.isColimit _).coconePointUniqueUpToIso hN⟩⟩

end ModuleCat

end
