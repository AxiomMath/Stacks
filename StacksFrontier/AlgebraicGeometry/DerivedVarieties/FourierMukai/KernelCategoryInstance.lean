module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.BaseChangeFunctor
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ConvolutionPerfectGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# The category of Fourier-Mukai kernels, and base change on it

Let `S` be a scheme. [Stacks, Tag 0G0F] builds a category with objects the proper smooth schemes
over `S`, morphisms from `X` to `Y` the isomorphism classes of objects of `D_perf(𝒪_{X ×_S Y})`,
composition the convolution `R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*K')` and identity the class of
`Δ_{X/S,*}𝒪_X`. [Stacks, Tag 0G0G] says that base change along `S₁ ⟶ S` is a functor between these
categories.

`AlgebraicGeometry.FourierMukaiKernelObj.categoryOf` assembles the category from any proof that the
convolution of two perfect kernels is perfect, and
`AlgebraicGeometry.FourierMukaiKernelObj.baseChangeFunctorOf` the functor. That proof is
`AlgebraicGeometry.FourierMukaiKernelObj.isPerfect_convolution`, from [Stacks, Tag 0B91]; this file
instantiates both.

## Main definitions

* `AlgebraicGeometry.FourierMukaiKernelObj.category` — **[Stacks, Tag 0G0F]**.
* `AlgebraicGeometry.FourierMukaiKernelObj.baseChangeFunctor` — **[Stacks, Tag 0G0G]**.

## Main results

* `AlgebraicGeometry.FourierMukaiKernelObj.mk_comp_mk` and
  `AlgebraicGeometry.FourierMukaiKernelObj.id_eq` — composition is convolution and the identity is
  the diagonal kernel, on isomorphism classes (clauses (3) and (4) of [Stacks, Tag 0G0F]).
* `AlgebraicGeometry.FourierMukaiKernelObj.baseChangeFunctor_obj` and
  `AlgebraicGeometry.FourierMukaiKernelObj.baseChangeFunctor_map_mk` — the two rules of
  [Stacks, Tag 0G0G].

## References

* [Stacks Project, Tag 0G0F](https://stacks.math.columbia.edu/tag/0G0F)
* [Stacks Project, Tag 0G0G](https://stacks.math.columbia.edu/tag/0G0G)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

universe u

namespace AlgebraicGeometry.FourierMukaiKernelObj

attribute [local instance 100000] HasDerivedCategory.standard

variable {S S₁ : Scheme.{u}}

/-- **[Stacks, Tag 0G0F]: the category of Fourier-Mukai kernels over `S`.** Its objects are the
proper smooth schemes over `S` (`AlgebraicGeometry.FourierMukaiKernelObj`), its morphisms from `X`
to `Y` the isomorphism classes of objects of `D_perf(𝒪_{X ×_S Y})`
(`AlgebraicGeometry.FourierMukaiKernelObj.Hom`), composition of the classes of `K` and `K'` the
class of `R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*K')`, which is perfect by [Stacks, Tag 0B91]
(`AlgebraicGeometry.FourierMukaiKernelObj.isPerfect_convolution`), and identity of `X` the class of
`Δ_{X/S,*}𝒪_X`. The unit laws and associativity are proved
(`AlgebraicGeometry.diagonalKernelConvolutionIso`,
`AlgebraicGeometry.convolutionDiagonalKernelIso`,
`AlgebraicGeometry.fourierMukaiConvolutionAssocIso`). -/
@[stacks 0G0F "the category, with all four clauses of the source: objects the proper smooth \
schemes over S; morphisms X to Y the isomorphism classes of objects of D_perf(O_{X x_S Y}); \
composition the class of R pr_13,*(L pr_12^*K tensor^L L pr_23^*K'), perfect by Tag 0B91 \
(isPerfect_convolution); identity the class of Delta_{X/S,*}O_X; associativity and the unit laws \
are the category axioms, proved. Clauses (3) and (4) are mk_comp_mk and id_eq"]
instance category : Category (FourierMukaiKernelObj S) :=
  categoryOf (S := S) fun K K' => isPerfect_convolution K K'

/-- **Clause (3) of [Stacks, Tag 0G0F]**: the composite of the classes of `K` on `X ×_S Y` and `K'`
on `Y ×_S Z` is the class of their convolution `R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*K')`. -/
theorem mk_comp_mk {X Y Z : FourierMukaiKernelObj S} (K : PerfectKernel X Y)
    (K' : PerfectKernel Y Z) :
    CategoryStruct.comp (X := X) (Y := Y) (Z := Z) ⟦K⟧ ⟦K'⟧ =
      (⟦⟨fourierMukaiConvolution X.f Y.f Z.f K.obj K'.obj, isPerfect_convolution K K'⟩⟧ :
        Hom X Z) :=
  rfl

/-- **Clause (4) of [Stacks, Tag 0G0F]**: the identity of `X` is the class of `Δ_{X/S,*}𝒪_X`. -/
theorem id_eq (X : FourierMukaiKernelObj S) : 𝟙 X = (⟦diagonal X⟧ : Hom X X) :=
  rfl

/-- **[Stacks, Tag 0G0G]: base change along `s : S₁ ⟶ S` is a functor** from the category of
Fourier-Mukai kernels over `S` to the one over `S₁`. On objects it sends `X` to its base change
`X ×_S S₁ ⟶ S₁` and on morphisms the class of `K` on `X ×_S Y` to the class of
`L(X₁ ×_{S₁} Y₁ ⟶ X ×_S Y)^*K`. -/
@[stacks 0G0G "the functor between the categories of Tag 0G0F over S and over S1, both built with \
the perfectness of convolution proved (Tag 0B91): objects X go to the base change, written \
X x_S S1 (the source's S1 x_S X up to the symmetry of the fibre product), morphisms the class of K \
to the class of L(X1 x_{S1} Y1 --> X x_S Y)^*K; preservation of identities and of composition are \
the functor axioms, proved. The two rules are baseChangeFunctor_obj and baseChangeFunctor_map_mk"]
def baseChangeFunctor (s : S₁ ⟶ S) : FourierMukaiKernelObj S ⥤ FourierMukaiKernelObj S₁ :=
  baseChangeFunctorOf (fun K K' => isPerfect_convolution K K') s

/-- **Clause (1) of [Stacks, Tag 0G0G]**: the base change functor sends `X ⟶ S` to
`X ×_S S₁ ⟶ S₁`. -/
@[simp]
theorem baseChangeFunctor_obj (s : S₁ ⟶ S) (X : FourierMukaiKernelObj S) :
    (baseChangeFunctor s).obj X = X.baseChange s :=
  rfl

/-- **Clause (2) of [Stacks, Tag 0G0G]**: the base change functor sends the class of `K` to the
class of `L(X₁ ×_{S₁} Y₁ ⟶ X ×_S Y)^*K`. -/
@[simp]
theorem baseChangeFunctor_map_mk (s : S₁ ⟶ S) {X Y : FourierMukaiKernelObj S}
    (K : PerfectKernel X Y) :
    (baseChangeFunctor s).map (X := X) (Y := Y) ⟦K⟧ =
      (⟦baseChangeKernel s K⟧ : Hom (X.baseChange s) (Y.baseChange s)) :=
  rfl

end AlgebraicGeometry.FourierMukaiKernelObj

end
