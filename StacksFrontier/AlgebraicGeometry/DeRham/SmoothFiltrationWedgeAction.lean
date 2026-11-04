module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFiltration
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.UnboundedLocalization
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.CochainAction

/-!
# Left multiplication by a local form on the restricted de Rham complex

Let `𝒜` be a sheaf of differential graded algebras on a ringed space `X` (for [Stacks, Tag 0FMN],
the relative de Rham complex `Ω^•_{X/S}` of
`AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra`),
`V ⊆ X` open and `a` a homogeneous section of degree `p` of `𝒜` over `V`. Left multiplication
`x ↦ a x` is not a morphism of complexes, but it is a cochain of degree `p` on the restriction
`𝒜|_V` of the complex of `𝒜`, and the graded Leibniz rule `d(a x) = (da) x + (-1)^p a dx` says
exactly that its coboundary is left multiplication by `da`.

## Main definitions

* `Stacks.Cohomology.HigherDirectImage.restrictedLeftMul`: multiplication by a section over `V`
  through an `𝒪_X`-bilinear map, as a morphism of sheaves of modules on `V`.
* `SheafOfModules.DifferentialGradedAlgebra.restrictedLeftMulCochain`: left multiplication by a
  homogeneous section over `V`, as a cochain on `𝒜|_V`.

## Main results

* `SheafOfModules.DifferentialGradedAlgebra.leibniz_transported`: the graded Leibniz rule with the
  three products transported to a common degree.
* `SheafOfModules.DifferentialGradedAlgebra.δ_restrictedLeftMulCochain`: **the coboundary of left
  multiplication by `a` is left multiplication by `da`.**

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.Cohomology.HigherDirectImage

universe u

namespace Stacks.Cohomology.HigherDirectImage

variable {X : RingedSpace.{u, u}} (V : Opens X)
  {M N P : SheafOfModules.{u} (structureSheafRing X)}

/-- The open of `X` underlying an open of the subspace `V`. -/
abbrev openOfRestrict (W : Opens ((Opens.toTopCat (X : TopCat)).obj V)) : Opens X :=
  V.isOpenEmbedding.functor.obj W

/-- The open of `X` underlying an open of the subspace `V` is contained in `V`. -/
lemma openOfRestrict_le (W : Opens ((Opens.toTopCat (X : TopCat)).obj V)) :
    openOfRestrict V W ≤ V :=
  isOpenEmbeddingFunctor_obj_le V W

/-- For `W' ⊆ W ⊆ V`, restricting `β(a|_W, x)` to `W'` gives `β(a|_{W'}, x|_{W'})`. -/
lemma restrictedLeftMul_naturality (β : Stacks.BilinearMap M.val N.val P.val)
    (a : M.val.obj (op V)) {W W' : Opens ((Opens.toTopCat (X : TopCat)).obj V)} (i : W' ⟶ W)
    (x : N.val.obj (op (openOfRestrict V W))) :
    β.app (op (openOfRestrict V W')) (M.val.map (homOfLE (openOfRestrict_le V W')).op a)
        (N.val.map (V.isOpenEmbedding.functor.map i).op x) =
      P.val.map (V.isOpenEmbedding.functor.map i).op
        (β.app (op (openOfRestrict V W)) (M.val.map (homOfLE (openOfRestrict_le V W)).op a) x) := by
  refine Eq.trans ?_ (β.naturality (X := op (openOfRestrict V W)) (Y := op (openOfRestrict V W'))
    (V.isOpenEmbedding.functor.map i).op (M.val.map (homOfLE (openOfRestrict_le V W)).op a) x).symm
  refine congrArg (fun y => β.app (op (openOfRestrict V W')) y _) ?_
  exact (PresheafOfModules.map_comp_apply M.val _ _ a)

/-- **Multiplication by a section `a` of `M` over `V`, through an `𝒪_X`-bilinear map
`β : M × N ⟶ P`**, as a morphism `N|_V ⟶ P|_V` of sheaves of modules on the open subspace `V`:
over an open `W ⊆ V` it is `x ↦ β(a|_W, x)`. -/
def restrictedLeftMul (β : Stacks.BilinearMap M.val N.val P.val) (a : M.val.obj (op V)) :
    (moduleRestriction X V).obj N ⟶ (moduleRestriction X V).obj P where
  val := PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (β.app (op (openOfRestrict V W.unop))
        (M.val.map (homOfLE (openOfRestrict_le V W.unop)).op a))
      naturality := fun {_ _} i => AddCommGrpCat.ext fun x =>
        restrictedLeftMul_naturality V β a i.unop x }
    (fun _ r x => β.map_smul_right _ r _ x)

/-- Over an open `W ⊆ V`, `restrictedLeftMul V β a` sends `x` to `β(a|_W, x)`. -/
lemma restrictedLeftMul_app (β : Stacks.BilinearMap M.val N.val P.val) (a : M.val.obj (op V))
    (W : Opens ((Opens.toTopCat (X : TopCat)).obj V))
    (x : N.val.obj (op (openOfRestrict V W))) :
    (restrictedLeftMul V β a).val.app (op W) x =
      β.app (op (openOfRestrict V W)) (M.val.map (homOfLE (openOfRestrict_le V W)).op a) x :=
  rfl

end Stacks.Cohomology.HigherDirectImage

namespace SheafOfModules.DifferentialGradedAlgebra

open Stacks.Cohomology.HigherDirectImage CochainComplex.HomComplex

variable {X : RingedSpace.{u, u}} (V : Opens X)
  (𝒜 : SheafOfModules.DifferentialGradedAlgebra.{u, u} (structureSheafRing X))

/-- A degreewise transport between two names of the same degree is the identity up to `HEq`. -/
private lemma XIsoOfEq_hom_app_heq {i j : ℤ} (h : i = j) (U : (Opens X)ᵒᵖ)
    (x : (𝒜.complex.X i).val.obj U) : (𝒜.complex.XIsoOfEq h).hom.val.app U x ≍ x := by
  subst h
  rfl

/-- **Left multiplication by a homogeneous section `a` of degree `p` over `V`**, as a cochain of
degree `p` on the restriction of the complex of `𝒜` to `V`: in degree `n` it is
`x ↦ a|_W ∧ x` on the sections over `W ⊆ V`. -/
def restrictedLeftMulCochain {p : ℤ} (a : (𝒜.complex.X p).val.obj (op V)) :
    Cochain (((moduleRestriction X V).mapHomologicalComplex (ComplexShape.up ℤ)).obj 𝒜.complex)
      (((moduleRestriction X V).mapHomologicalComplex (ComplexShape.up ℤ)).obj 𝒜.complex) p :=
  Cochain.mk fun n m h => restrictedLeftMul V (𝒜.mul p n) a ≫
    (moduleRestriction X V).map (𝒜.complex.XIsoOfEq (show p + n = m by omega)).hom

/-- Over an open `W ⊆ V`, the component of `restrictedLeftMulCochain V 𝒜 a` from degree `n` to
degree `m` sends `x` to `a|_W ∧ x`, up to the identification of degree `p + n` with `m`. -/
lemma restrictedLeftMulCochain_v_app {p : ℤ} (a : (𝒜.complex.X p).val.obj (op V)) (n m : ℤ)
    (h : n + p = m) (W : Opens ((Opens.toTopCat (X : TopCat)).obj V))
    (x : (𝒜.complex.X n).val.obj (op (openOfRestrict V W))) :
    ((restrictedLeftMulCochain V 𝒜 a).v n m h).val.app (op W) x ≍
      (𝒜.mul p n).app (op (openOfRestrict V W))
        ((𝒜.complex.X p).val.map (homOfLE (openOfRestrict_le V W)).op a) x :=
  XIsoOfEq_hom_app_heq 𝒜 _ _ _

/-- Transporting along `gradedCast` and then `XIsoOfEq` is the same as `XIsoOfEq` alone. -/
private lemma XIsoOfEq_hom_app_gradedCast {i j m : ℤ} (hi : i = m) (hj : j = m) (c : i = j)
    (U : (Opens X)ᵒᵖ) (y : (𝒜.complex.X i).val.obj U) :
    (𝒜.complex.XIsoOfEq hj).hom.val.app U
        (gradedCast (fun q ↦ (𝒜.complex.X q).val.obj U) c y) =
      (𝒜.complex.XIsoOfEq hi).hom.val.app U y := by
  subst hi hj
  rfl

/-- **The graded Leibniz rule, read on the degrees of a cochain**: for a section `a` of degree
`p` and `x` of degree `n`, `d(a x) - (-1)^p a (dx) = (da) x`, all three products transported to
the degree `m = n + p + 1`. -/
lemma leibniz_transported {p : ℤ} (U : (Opens X)ᵒᵖ) (a : (𝒜.complex.X p).val.obj U) (n m : ℤ)
    (hm : n + (p + 1) = m) (x : (𝒜.complex.X n).val.obj U) :
    (𝒜.complex.d (n + p) m).val.app U
        ((𝒜.complex.XIsoOfEq (show p + n = n + p by omega)).hom.val.app U
          ((𝒜.mul p n).app U a x)) +
      (p + 1).negOnePow • (𝒜.complex.XIsoOfEq (show p + (n + 1) = m by omega)).hom.val.app U
        ((𝒜.mul p (n + 1)).app U a ((𝒜.complex.d n (n + 1)).val.app U x)) =
    (𝒜.complex.XIsoOfEq (show p + 1 + n = m by omega)).hom.val.app U
      ((𝒜.mul (p + 1) n).app U ((𝒜.complex.d p (p + 1)).val.app U a) x) := by
  have hd₁ : (𝒜.complex.d (n + p) m).val.app U
      ((𝒜.complex.XIsoOfEq (show p + n = n + p by omega)).hom.val.app U
        ((𝒜.mul p n).app U a x)) =
      (𝒜.complex.XIsoOfEq (show p + n + 1 = m by omega)).hom.val.app U
        ((𝒜.complex.d (p + n) (p + n + 1)).val.app U ((𝒜.mul p n).app U a x)) := by
    rw [← SheafOfModules.comp_val_app_apply, HomologicalComplex.XIsoOfEq_hom_comp_d,
      ← SheafOfModules.comp_val_app_apply, HomologicalComplex.d_comp_XIsoOfEq_hom]
  rw [hd₁, 𝒜.leibniz p n U a x, map_add, map_zsmul]
  have e₁ := XIsoOfEq_hom_app_gradedCast 𝒜 (show p + 1 + n = m by omega)
    (show p + n + 1 = m by omega) (add_right_comm p 1 n) U
    ((𝒜.mul (p + 1) n).app U ((𝒜.complex.d p (p + 1)).val.app U a) x)
  have e₂ := XIsoOfEq_hom_app_gradedCast 𝒜 (show p + (n + 1) = m by omega)
    (show p + n + 1 = m by omega) (add_assoc p n 1).symm U
    ((𝒜.mul p (n + 1)).app U a ((𝒜.complex.d n (n + 1)).val.app U x))
  rw [e₁, e₂, Int.negOnePow_succ, Units.smul_def, Units.val_neg, neg_smul]
  abel

omit 𝒜 in
private lemma units_smul_val_app {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    {M N : SheafOfModules.{u} R} (e : ℤˣ) (f : M ⟶ N) (U : (Opens X)ᵒᵖ) (x : M.val.obj U) :
    (e • f).val.app U x = (e : ℤ) • f.val.app U x := by
  rcases Int.units_eq_one_or e with rfl | rfl
  · simp
  · simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, Units.neg_smul]
    rfl

/-- **The Leibniz rule for left multiplication**: the coboundary of left multiplication by `a`
is left multiplication by `da`. -/
theorem δ_restrictedLeftMulCochain {p : ℤ} (a : (𝒜.complex.X p).val.obj (op V)) :
    δ p (p + 1) (restrictedLeftMulCochain V 𝒜 a) =
      restrictedLeftMulCochain V 𝒜 ((𝒜.complex.d p (p + 1)).val.app (op V) a) := by
  ext n m hnm W x
  rw [δ_v p (p + 1) rfl _ n m hnm (n + p) (n + 1) (by omega) rfl]
  obtain ⟨W⟩ := W
  rw [SheafOfModules.add_val, PresheafOfModules.add_app, ModuleCat.hom_add, LinearMap.add_apply,
    units_smul_val_app]
  have hda := PresheafOfModules.naturality_apply (𝒜.complex.d p (p + 1)).val
    (homOfLE (openOfRestrict_le V W)).op a
  set U : (Opens X)ᵒᵖ := op (openOfRestrict V W)
  set aU := (𝒜.complex.X p).val.map (homOfLE (openOfRestrict_le V W)).op a
  change (𝒜.complex.d (n + p) m).val.app U
      ((𝒜.complex.XIsoOfEq (show p + n = n + p by omega)).hom.val.app U
        ((𝒜.mul p n).app U aU x)) +
    ((p + 1).negOnePow : ℤ) • (𝒜.complex.XIsoOfEq (show p + (n + 1) = m by omega)).hom.val.app U
        ((𝒜.mul p (n + 1)).app U aU ((𝒜.complex.d n (n + 1)).val.app U x)) =
    (𝒜.complex.XIsoOfEq (show p + 1 + n = m by omega)).hom.val.app U
      ((𝒜.mul (p + 1) n).app U ((𝒜.complex.X (p + 1)).val.map
        (homOfLE (openOfRestrict_le V W)).op ((𝒜.complex.d p (p + 1)).val.app (op V) a)) x)
  rw [← hda]
  exact leibniz_transported 𝒜 _ _ n m hnm x

end SheafOfModules.DifferentialGradedAlgebra
