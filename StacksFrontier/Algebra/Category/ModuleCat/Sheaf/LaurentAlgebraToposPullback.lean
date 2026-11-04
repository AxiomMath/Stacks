module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackMulComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LaurentAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerToposPullback

/-!
# The pullback of the Laurent algebra of an invertible module along a morphism of ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and `L` an invertible
`O_D`-module. The pullback of sheaves of graded algebras of Stacks 0FQX carries the Laurent
algebra `⨁_{n ∈ ℤ} L^{⊗ n}` of Tag 01CU to the Laurent algebra of the invertible module `f^*L`
(Stacks 0B8P):

`f^*(⨁_n L^{⊗ n}) ≅ ⨁_n (f^*L)^{⊗ n}`

as sheaves of graded `O_C`-algebras, the degree-`n` component being the comparison
`f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}` of
`Stacks.SheafOfModules.RingedToposPullback.pullbackIntPowIso`.

## Main definitions

* `Stacks.SheafOfModules.RingedToposPullback.laurentToposPullbackIso`: the isomorphism of
  sheaves of graded algebras `f^*(⨁_n L^{⊗ n}) ≅ ⨁_n (f^*L)^{⊗ n}`.

## Main results

* `Stacks.SheafOfModules.TensorPower.mulSheaf_laurentAlgebra`: the multiplication of the Laurent
  algebra, as a morphism out of the tensor product sheaf, is the coherent multiplication of
  Tag 01CU.
* `Stacks.SheafOfModules.RingedToposPullback.mulSheaf_laurentToposPullback_comp`: the comparison
  of tensor powers carries the multiplication of `f^*(⨁_n L^{⊗ n})` to the coherent
  multiplication of `f^*L`.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.Sheaves.RingedToposModules Stacks.SheafOfModules.TensorPower
open Stacks.Sheaves.GradedAlgebraPullback

universe w v u

namespace Stacks.SheafOfModules.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (Osharp : Sheaf J CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf Osharp.obj))
  (L : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf Osharp.obj hO))
  [IsInvertible Osharp.obj hO L]

/-- **The multiplication of the Laurent algebra is the coherent multiplication of Tag 01CU**, as
a morphism out of the tensor product sheaf `L^{⊗ n} ⊗ L^{⊗ m}`. -/
theorem mulSheaf_laurentAlgebra (n m : ℤ) :
    _root_.SheafOfModules.GradedAlgebra.mulSheaf (laurentAlgebra Osharp.obj hO L) n m =
      (coherentMulIso Osharp.obj hO L n m).hom :=
  PresheafOfModules.tensorSheaf_hom_ext fun U x y =>
    (_root_.SheafOfModules.GradedAlgebra.mulSheaf_unit (laurentAlgebra Osharp.obj hO L)
      n m U x y).trans (mulBilinear_app Osharp.obj hO L n m U x y)

end Stacks.SheafOfModules.TensorPower

namespace Stacks.SheafOfModules.RingedToposPullback

variable {X Y : AlgebraicGeometry.RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)
  (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  [IsInvertible Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L]

/-- **The comparison of tensor powers carries the multiplication of the pulled-back Laurent
algebra to the coherent multiplication of `f^*L`**:

`μ^{f^*(⨁ L^{⊗ n})}_{ij} ≫ c_{i+j} = (c_i ⊗ c_j) ≫ μ^{f^*L}_{ij}`

as morphisms `f^*(L^{⊗ i}) ⊗ f^*(L^{⊗ j}) ⟶ (f^*L)^{⊗ (i + j)}`, where `c_n` is
`pullbackIntPowIso f L n`. -/
theorem mulSheaf_laurentToposPullback_comp (i j : ℤ) :
    _root_.SheafOfModules.GradedAlgebra.mulSheaf
          (toposPullbackGradedAlgebra f
            (laurentAlgebra Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L)) i j ≫
        (pullbackIntPowIso f L (i + j)).hom =
      (tensorSheafMapIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
          (pullbackIntPowIso f L i) (pullbackIntPowIso f L j)).hom ≫
        (coherentMulIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
          (f.pullbackModules.obj L) i j).hom := by
  refine (cancel_epi (pullbackTensorComparisonIso f
    (tensorPower Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L i)
    (tensorPower Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L j)).hom).mp ?_
  refine Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans ?_ (pullbackIntPowIso_coherentMulIso f L i j))
  refine congrArg (fun m ↦ m ≫ (pullbackIntPowIso f L (i + j)).hom) ?_
  refine (pullbackTensorIso_hom_app_comp_mulSheaf f
    (laurentAlgebra Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L) i j).trans ?_
  exact congrArg f.pullbackModules.map
    (mulSheaf_laurentAlgebra Y.O (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L i j)

/-- **The pullback of the Laurent algebra of an invertible module is the Laurent algebra of the
pullback**: `f^*(⨁_n L^{⊗ n}) ≅ ⨁_n (f^*L)^{⊗ n}` as sheaves of graded `O_C`-algebras, with
the comparison `f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}` of `pullbackIntPowIso` in degree `n`. -/
def laurentToposPullbackIso :
    toposPullbackGradedAlgebra f
        (laurentAlgebra Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L) ≅
      laurentAlgebra X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
        (f.pullbackModules.obj L) :=
  _root_.SheafOfModules.GradedAlgebra.isoOfPieceIso (fun n ↦ pullbackIntPowIso f L n)
    fun i j U x y ↦ by
      have h := congrArg (fun m ↦ m.val.app U
          ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
            ((f.pullbackModules.obj (tensorPower Y.O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L i)).val ⊗
             (f.pullbackModules.obj (tensorPower Y.O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L j)).val)).app U
            (x ⊗ₜ[X.O.obj.obj U] y)))
        (mulSheaf_laurentToposPullback_comp f L i j)
      refine Eq.trans (congrArg ((pullbackIntPowIso f L (i + j)).hom.val.app U)
        (_root_.SheafOfModules.GradedAlgebra.mulSheaf_unit _ i j U x y).symm) ?_
      refine Eq.trans (CategoryTheory.comp_apply _ _ _).symm (h.trans ?_)
      refine Eq.trans (CategoryTheory.comp_apply _ _ _) ?_
      exact congrArg ((coherentMulIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
          (f.pullbackModules.obj L) i j).hom.val.app U)
        (Stacks.SheafOfModules.tensorSections_tensorProductIsoAt X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property U _ _ _ _
          (pullbackIntPowIso f L i) (pullbackIntPowIso f L j) x y)

/-- The degree-`n` component of the pullback of the Laurent algebra is the comparison of tensor
powers. -/
@[simp]
theorem laurentToposPullbackIso_hom_app (n : ℤ) :
    (laurentToposPullbackIso f L).hom.app n = (pullbackIntPowIso f L n).hom :=
  rfl

end Stacks.SheafOfModules.RingedToposPullback

end
