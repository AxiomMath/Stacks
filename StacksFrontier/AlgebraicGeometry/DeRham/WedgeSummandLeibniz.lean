module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationDegreewise

/-!
# The Leibniz rule on a summand of the wedge map

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X`, let
`Ω^•` be the relative de Rham complex of `AlgebraicGeometry.SheafOfModules.deRhamComplex` and
let `ι : P ⟶ Ω^•` be a morphism of complexes of sheaves of `A`-modules. The wedge filtration of
`Ω^•` determined by `ι`
(`StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltration`) is cut out by the wedge map
`Tot(P ⊗_A Ω^•) ⟶ Ω^•`, whose `(i, j)` summand is

`P^i ⊗_A Ω^j ⟶ Ω^i ⊗_A Ω^j ⟶ Ω^{i+j}`,

the degree-`i` component of `ι` tensored with the identity of `Ω^j` followed by wedge
multiplication (`AlgebraicGeometry.SheafOfModules.ιMapBifunctor_comp_wedgeAlong_f`).

**This file computes the de Rham differential on that summand.** The graded Leibniz rule
`d(ω ∧ η) = dω ∧ η + (-1)^iω ∧ dη` for the components of the wedge product is
`AlgebraicGeometry.SheafOfModules.exteriorProductComponent_d`; read on the summand, `ω` is the
image under `ι` of a section of `P^i`, so `dω` is the image under `ι` of a section of `P^{i+1}`
and the first term **factors through the `(i + 1, j)` summand**, while the second is the
`(i, j + 1)` summand up to the sign `(-1)^i`.

This is the computation the identification of the graded pieces of [Stacks, Section 0FMK] rests
on: the `(i + 1, j)` summand lands in the next step of the filtration, so modulo that step the
differential on the `i`-th graded piece is `(-1)^i(1 ⊗ d)`, which is the sign
`Stacks.DeRhamSmooth.gradedTargetComplex_d` carries.

## Main results

* `AlgebraicGeometry.SheafOfModules.tensorFunctor_map_comm`: the chain-map square of `ι`,
  tensored with a term of the de Rham complex.
* `AlgebraicGeometry.SheafOfModules.summand_d`: **the Leibniz rule on the `(i, j)` summand of
  the wedge map**, with the first summand written as a morphism factoring through the
  `(i + 1, j)` summand.
* `AlgebraicGeometry.SheafOfModules.summandOfEq_d`: the same with the total degree named by a
  hypothesis `i + j = m`, which is the shape the summands of the wedge filtration are written
  in (`AlgebraicGeometry.SheafOfModules.summandOfEq_eq_laxComparison_comp`).

## Implementation notes

Nothing is assumed of `ι` beyond its being a morphism of complexes, and no hypothesis is placed
on `i` or `j`. The sign is written `(-1 : ℤ) ^ i`, the spelling
`AlgebraicGeometry.SheafOfModules.exteriorProductComponent_d` uses;
`StacksFrontier.Algebra.NegOnePowSmul` crosses between it and `Int.negOnePow`.

The proofs are in term mode. At these binders `rw [Category.assoc]` is refused — the goal is
reported as not type-correct at `implicit` transparency, the underlying mismatch being that the
ring sheaf `A` of the de Rham complex is a `TopCat.Sheaf` while `underlyingRingSheafOfSite`
expects a sheaf on the site of opens — so the associativities are applied as terms.

## References

* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct DirectSum
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)
  (P : CochainComplex (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) ℕ)
  (ι : P ⟶ deRhamComplex B D)

/-- **The chain-map square of `ι`, tensored with `Ω^j`.** Tensoring with a fixed term of the de
Rham complex is a functor, so it carries the square `ι^i ≫ d = d ≫ ι^{i+1}` of `ι` to a square;
the right-hand side is what the first term of the graded Leibniz rule becomes on the `(i, j)`
summand of the wedge map. -/
theorem tensorFunctor_map_comm (i j : ℕ) :
    ((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
        ((sheafTensor.{u,u,u,u,u} A).map ((deRhamComplex B D).d i (i + 1))).app
          ((deRhamComplex B D).X j) =
      ((sheafTensor.{u,u,u,u,u} A).map (P.d i (i + 1))).app ((deRhamComplex B D).X j) ≫
        ((sheafTensor.{u,u,u,u,u} A).map (ι.f (i + 1))).app ((deRhamComplex B D).X j) :=
  Eq.trans (NatTrans.comp_app _ _ _).symm
    (Eq.trans
      (congrArg
        (fun α : (sheafTensor.{u,u,u,u,u} A).obj (P.X i) ⟶
            (sheafTensor.{u,u,u,u,u} A).obj ((deRhamComplex B D).X (i + 1)) =>
          α.app ((deRhamComplex B D).X j))
        (Eq.trans
          ((sheafTensor.{u,u,u,u,u} A).map_comp (ι.f i) ((deRhamComplex B D).d i (i + 1))).symm
          (Eq.trans (congrArg (sheafTensor.{u,u,u,u,u} A).map (ι.comm i (i + 1)))
            ((sheafTensor.{u,u,u,u,u} A).map_comp (P.d i (i + 1)) (ι.f (i + 1))))))
      (NatTrans.comp_app _ _ _))

/-- **The Leibniz rule on the `(i, j)` summand of the wedge map.** For `ι : P ⟶ Ω^•` a morphism
of complexes, the de Rham differential on the summand

`P^i ⊗_A Ω^j ⟶ Ω^{i+j}`

of the wedge map is `dω ∧ η + (-1)^iω ∧ dη` with `ω` the image of a section of `P^i`: the first
term is the `(i + 1, j)` summand precomposed with `d_P ⊗ 1`, so it factors through the degree
`i + 1` of `P` and hence through the next step of the wedge filtration; the second is the
`(i, j + 1)` summand precomposed with `1 ⊗ d`, with the sign `(-1)^i`.

This is `AlgebraicGeometry.SheafOfModules.exteriorProductComponent_d` with `ω` restricted to
come from `P` — the restriction that makes the first term land one step further up the
filtration, which is why the graded piece sees only the second. -/
theorem summand_d (i j : ℕ) :
    (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
          exteriorProductComponent B i j) ≫
        (deRhamComplex B D).d (i + j) (i + j + 1) =
      ((sheafTensor.{u,u,u,u,u} A).map (P.d i (i + 1))).app ((deRhamComplex B D).X j) ≫
          ((sheafTensor.{u,u,u,u,u} A).map (ι.f (i + 1))).app ((deRhamComplex B D).X j) ≫
            exteriorProductComponent B (i + 1) j ≫
              ((deRhamComplex B D).XIsoOfEq (show i + 1 + j = i + j + 1 by omega)).hom +
        (-1 : ℤ) ^ i • (((sheafTensor.{u,u,u,u,u} A).obj (P.X i)).map
              ((deRhamComplex B D).d j (j + 1)) ≫
            ((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X (j + 1)) ≫
              exteriorProductComponent B i (j + 1) ≫
                ((deRhamComplex B D).XIsoOfEq
                  (show i + (j + 1) = i + j + 1 by omega)).hom) := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg
    (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫ ·)
    (exteriorProductComponent_d B D i j)) ?_
  refine Eq.trans (Preadditive.comp_add _ _ _ _ _ _) ?_
  refine Eq.trans (congrArg (· + _) ?_) (congrArg (_ + ·) ?_)
  · refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact Eq.trans (congrArg (· ≫ _) (tensorFunctor_map_comm B D P ι i j))
      (Category.assoc _ _ _)
  · refine Eq.trans (Preadditive.comp_zsmul _ _ _) ?_
    refine congrArg (((-1 : ℤ) ^ i) • ·) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact Eq.trans
      (congrArg (· ≫ _) (NatTrans.naturality ((sheafTensor.{u,u,u,u,u} A).map (ι.f i))
        ((deRhamComplex B D).d j (j + 1))).symm)
      (Category.assoc _ _ _)

/-- `AlgebraicGeometry.SheafOfModules.summand_d` with the total degree named by a hypothesis,
which is the shape the summands of the wedge filtration are written in
(`AlgebraicGeometry.SheafOfModules.summandOfEq_eq_laxComparison_comp`). -/
theorem summandOfEq_d (i j m : ℕ) (h : i + j = m) :
    (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
          exteriorProductComponent B i j ≫ ((deRhamComplex B D).XIsoOfEq h).hom) ≫
        (deRhamComplex B D).d m (m + 1) =
      ((sheafTensor.{u,u,u,u,u} A).map (P.d i (i + 1))).app ((deRhamComplex B D).X j) ≫
          ((sheafTensor.{u,u,u,u,u} A).map (ι.f (i + 1))).app ((deRhamComplex B D).X j) ≫
            exteriorProductComponent B (i + 1) j ≫
              ((deRhamComplex B D).XIsoOfEq (show i + 1 + j = m + 1 by omega)).hom +
        (-1 : ℤ) ^ i • (((sheafTensor.{u,u,u,u,u} A).obj (P.X i)).map
              ((deRhamComplex B D).d j (j + 1)) ≫
            ((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X (j + 1)) ≫
              exteriorProductComponent B i (j + 1) ≫
                ((deRhamComplex B D).XIsoOfEq (show i + (j + 1) = m + 1 by omega)).hom) := by
  subst h
  refine Eq.trans (congrArg (· ≫ (deRhamComplex B D).d (i + j) (i + j + 1))
    (congrArg (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫ ·)
      (Eq.trans (congrArg (exteriorProductComponent B i j ≫ ·)
          (congrArg Iso.hom ((deRhamComplex B D).XIsoOfEq_rfl (i + j))))
        (Category.comp_id (exteriorProductComponent B i j))))) ?_
  exact summand_d B D P ι i j

end AlgebraicGeometry.SheafOfModules

end
