module

public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksFrontier.Homology.TensorComplex.SingleTensor

/-!
# Tensoring a quasi-isomorphism of bounded above flat complexes with a module

Let `R` be a commutative ring and `f : C ⟶ D` a quasi-isomorphism of bounded above cochain
complexes of flat `R`-modules. Then for every `R`-module `N` the termwise tensor product
`N ⊗_R f : N ⊗_R C ⟶ N ⊗_R D` is again a quasi-isomorphism.

Both complexes are K-flat ([Stacks, Tag 064K], `CochainComplex.KFlat.kFlat_of_flat`), a
quasi-isomorphism of K-flat complexes stays one after tensoring with any complex
([Stacks, Tag 064L], `CochainComplex.DerivedTensor.quasiIso_tleftCochain_map`), and tensoring
with `N` placed in degree zero is the termwise tensor product
(`TotalTensorComplex.SingleTensor.singleTensorIso`).

This is the step of the proof of [Stacks, Tag 0FUM] which passes from the zeroth graded piece of
the filtration to the `k`-th: there the zeroth graded piece is a bounded complex of flat modules
and the `k`-th is obtained from it by tensoring with `Ω^k_{A/R}`.

## Main results

* `CochainComplex.KFlat.quasiIso_tensorLeft_map_of_flat`: the statement above.

## References

* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 064L](https://stacks.math.columbia.edu/tag/064L)
* [Stacks Project, Tag 0FUM](https://stacks.math.columbia.edu/tag/0FUM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open TotalTensorComplex.SingleTensor

universe u

namespace CochainComplex.KFlat

/-- **Tensoring a quasi-isomorphism of K-flat complexes with a module gives a
quasi-isomorphism.** -/
theorem quasiIso_tensorLeft_map_of_kFlat {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    {C D : CochainComplex (ModuleCat.{u} R) ℤ} (f : C ⟶ D) [QuasiIso f]
    (hC : CochainComplex.KFlat.{u, u} C) (hD : CochainComplex.KFlat.{u, u} D) :
    QuasiIso (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have ht := CochainComplex.DerivedTensor.quasiIso_tleftCochain_map.{u, u} f hC hD
    ((single _ (ComplexShape.up ℤ) 0).obj N)
  have hcomp : QuasiIso ((singleTensorIso N C).inv ≫
      (TleftCochain ((single _ (ComplexShape.up ℤ) 0).obj N)).map f) := by
    have h2 : QuasiIso ((TleftCochain ((single _ (ComplexShape.up ℤ) 0).obj N)).map f) := ht
    infer_instance
  rw [singleTensorIso_naturality] at hcomp
  exact (quasiIso_iff_comp_right _ (singleTensorIso N D).inv).mp hcomp

/-- **Tensoring a quasi-isomorphism of bounded above complexes of flat modules with a module gives
a quasi-isomorphism.** -/
theorem quasiIso_tensorLeft_map_of_flat {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    {C D : CochainComplex (ModuleCat.{u} R) ℤ} (f : C ⟶ D) [QuasiIso f] (a b : ℤ)
    [C.IsStrictlyLE a] [D.IsStrictlyLE b] [∀ n : ℤ, Module.Flat R (C.X n)]
    [∀ n : ℤ, Module.Flat R (D.X n)] :
    QuasiIso (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
  quasiIso_tensorLeft_map_of_kFlat N f (kFlat_of_flat.{u, u} C a) (kFlat_of_flat.{u, u} D b)

end CochainComplex.KFlat

end
