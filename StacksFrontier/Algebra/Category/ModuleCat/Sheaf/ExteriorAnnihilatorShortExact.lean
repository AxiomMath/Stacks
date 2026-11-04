module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorDeterminantTopPower
import StacksCore.Tactic.StacksAttribute

/-!
# The determinant comparison of a short exact sequence, without a rank hypothesis

Let `(X, O_X)` be a ringed space and let `E' --f--> E --g--> E''` be an exact sequence of sheaves
of `O_X`-modules with `g` an epimorphism. For any sheaf of modules `P` equipped with a morphism
`u : P ⟶ ⋀ⁿ E'` whose values wedge to zero against the degree-one sections coming from `E'`,
the wedge map `P ⊗ ⋀ᵏ⁺¹ E ⟶ ⋀ⁿ⁺ᵏ⁺¹ E` descends to

`P ⊗ ⋀ᵏ⁺¹ E'' ⟶ ⋀ⁿ⁺ᵏ⁺¹ E`.

Two instances of this construction:

* `P = ⋀ⁿ E'` and `u` the identity, where the hypothesis holds because `⋀ⁿ⁺¹ E' = 0` for `E'` of
  constant rank `n`. This recovers `Stacks.SheafOfModules.TopWedge.detComparison`.
* `P = det(E')ₙ`, the degree-`n` exterior annihilator of [Stacks, Tag 0FJN], a summand of
  `det(E')`, and `u` its inclusion, where the hypothesis holds for `E'` finite locally free with
  no constant-rank assumption (`mul_exteriorGenerator_eq_zero_of_annihilated`).

## Main definitions

* `Stacks.SheafOfModules.TopWedge.wedgeHomFrom`: the wedge map `P ⊗ ⋀ˢ E ⟶ ⋀ⁿ⁺ˢ E` attached to
  `u : P ⟶ ⋀ⁿ E'`.
* `Stacks.SheafOfModules.TopWedge.detComparisonFrom`: **the comparison**
  `P ⊗ ⋀ᵏ⁺¹ E'' ⟶ ⋀ⁿ⁺ᵏ⁺¹ E`, the descent of the wedge map along the presentation of
  [Stacks, Tag 01CJ] tensored with `P`.
* `Stacks.SheafOfModules.TopWedge.detAnnihilatorComparison`: the case `P = det(E')ₙ`, which
  carries **no rank hypothesis**.

## Main results

* `Stacks.SheafOfModules.TopWedge.mul_exteriorGenerator_eq_zero_of_annihilated`: **an exterior
  annihilated section of `⋀ⁿ E'` is killed by a degree-one section on the right as well as on
  the left**, for `E'` finite locally free of no particular rank.
* `Stacks.SheafOfModules.TopWedge.detComparisonFrom_wedge`: the wedge-and-lift formula.
* `Stacks.SheafOfModules.TopWedge.eq_detComparisonFrom`: the comparison is the only morphism
  satisfying its defining equation.
* `Stacks.SheafOfModules.TopWedge.detComparisonFrom_exteriorPower_id`: at `P = ⋀ⁿ E'` with
  `u = 𝟙` the comparison is `Stacks.SheafOfModules.TopWedge.detComparison`.
* `Stacks.SheafOfModules.TopWedge.nonempty_stalkLinearEquiv_finsupp_of_trivialization` and
  `Stacks.SheafOfModules.TopWedge.exists_nbhd_forall_nonempty_stalkLinearEquiv_finsupp`: a
  finite locally free sheaf of modules has, around every point, a **neighbourhood on which all
  its stalks are free of one and the same rank**.

## References

* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Sheaf
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules.TopWedge

/-! ### The wedge map out of an auxiliary sheaf of modules -/

section WedgeFrom

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E' E : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

variable (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  (f : E' ⟶ E) {n : ℕ}
  {P : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (u : P ⟶ A'.exteriorPower n)

/-- The wedge map `⋀ⁿ E' ⊗ ⋀ˢ E ⟶ ⋀ⁿ⁺ˢ E` of
`Stacks.SheafOfModules.TopWedge.wedgeBilinear`, read through a morphism `u : P ⟶ ⋀ⁿ E'` in the
first variable. -/
noncomputable def wedgeBilinearFrom (s : ℕ) :
    Stacks.BilinearMap P.val (A.exteriorPower s).val (A.exteriorPower (n + s)).val :=
  (wedgeBilinear A' A f n s).compLeft u.val

/-- **The wedge map `P ⊗ ⋀ˢ E ⟶ ⋀ⁿ⁺ˢ E`** attached to a morphism `u : P ⟶ ⋀ⁿ E'`: the image in
`⋀ⁿ E` of the image under `u` of a local section of `P`, multiplied by a local section of
`⋀ˢ E`. -/
noncomputable def wedgeHomFrom (s : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj P).obj (A.exteriorPower
        s) ⟶
      A.exteriorPower (n + s) :=
  PresheafOfModules.tensorSheafDesc (F := P) (G := A.exteriorPower s)
    (Q := A.exteriorPower (n + s))
    (PresheafOfModules.ofBilinear (wedgeBilinearFrom A' A f u s))

/-- The wedge map out of `P` on the image of a pure tensor of local sections. -/
theorem wedgeHomFrom_unit (s : ℕ) (U : (Opens ↥X)ᵒᵖ) (w : P.val.obj U)
    (y : (A.exteriorPower s).val.obj U) :
    (wedgeHomFrom A' A f u s).val.app U
        ((PresheafOfModules.tensorSheafUnit P (A.exteriorPower s)).app U (w ⊗ₜ y)) =
      (A.exterior.mul (n : ℤ) (s : ℤ)).app U
        (((extHom A' A f).app (n : ℤ)).val.app U (u.val.app U w)) y :=
  (PresheafOfModules.tensorSheafDesc_unit _ U w y).trans
    ((PresheafOfModules.ofBilinear_tmul (wedgeBilinearFrom A' A f u s) U w y).trans
      (Stacks.BilinearMap.compLeft_app (wedgeBilinear A' A f n s) u.val U w y))

end WedgeFrom

/-! ### The descent along the presentation of Tag 01CJ -/

section DescentFrom

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

variable (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E'')
  (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0) {n : ℕ}
  {P : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (u : P ⟶ A'.exteriorPower n)

/-- Tensoring a morphism on the left with `P`. -/
noncomputable abbrev tensorLeftMapFrom
    {Q R : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (h : Q ⟶ R) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj P).obj Q ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj P).obj R :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj P).map h

/-- Tensoring on the left with `P`, as a functor. -/
noncomputable abbrev tensorLeftFunctorFrom :
    _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) ⥤
      _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj P

/-- Tensoring on the left with `P` preserves zero morphisms. -/
instance preservesZeroMorphisms_tensorLeftFunctorFrom :
    (tensorLeftFunctorFrom (X := X) (Osharp := Osharp) (P := P)).PreservesZeroMorphisms :=
  Stacks.SheafOfModules.TensorLocalProperties.preservesZeroMorphisms_tensorSheafRight
    (Opens.grothendieckTopology ↥X) Osharp P

/-- Tensoring on the left with `P` preserves the colimit of a parallel pair. -/
instance preservesColimit_parallelPair_tensorLeftFunctorFrom
    {Q R : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (h h' : Q ⟶ R) :
    Limits.PreservesColimit (Limits.parallelPair h h')
      (tensorLeftFunctorFrom (X := X) (Osharp := Osharp) (P := P)) :=
  Stacks.SheafOfModules.TensorLocalProperties.preservesColimit_parallelPair_tensorSheafRight
    (Opens.grothendieckTopology ↥X) Osharp P h h'

/-- `P ⊗ h` sends the image of a pure tensor `w ⊗ y` to the image of `w ⊗ h(y)`. -/
private theorem tensorLeftMapFrom_unit
    {Q R : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (h : Q ⟶ R) (V : (Opens ↥X)ᵒᵖ) (w : P.val.obj V) (y : Q.val.obj V) :
    (tensorLeftMapFrom (P := P) h).val.app V
        ((PresheafOfModules.tensorSheafUnit P Q).app V (w ⊗ₜ y)) =
      (PresheafOfModules.tensorSheafUnit P R).app V (w ⊗ₜ h.val.app V y) := by
  have mapUnit :=
    Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp P _
      (@CategoryStruct.id
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) _ P)
      h V w y
  rw [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).map_id P,
    NatTrans.id_app ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj P) Q,
    Category.id_comp] at mapUnit
  exact mapUnit

/-- **The wedge map out of `P` kills the relation of [Stacks, Tag 01CJ]**, on a nested pure
tensor, provided the image in `⋀ⁿ E` of every local section of `P` is killed by the degree-one
sections coming from `E'`. -/
theorem wedgeHomFrom_tensorLeftMap_relComplex_f_unit
    (hu : ∀ (V : (Opens ↥X)ᵒᵖ) (w : P.val.obj V) (a : E'.val.obj V),
      (A.exterior.mul (n : ℤ) 1).app V
          (((extHom A' A f).app (n : ℤ)).val.app V (u.val.app V w))
        (A.exteriorGenerator.val.app V (f.val.app V a)) = 0)
    (k : ℕ) (V : (Opens ↥X)ᵒᵖ) (w : P.val.obj V) (a : E'.val.obj V)
    (b : (A.exteriorPower k).val.obj V) :
    (tensorLeftMapFrom (P := P) (relComplex A A'' f g hfg k).f ≫
          wedgeHomFrom A' A f u (k + 1)).val.app V
        ((PresheafOfModules.tensorSheafUnit P
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj E').obj
                (A.exteriorPower
                k))).app V
          (w ⊗ₜ (PresheafOfModules.tensorSheafUnit E' (A.exteriorPower k)).app V (a ⊗ₜ b))) =
      0 := by
  have hdeg : (1 : ℤ) + (k : ℤ) = ((k + 1 : ℕ) : ℤ) := by omega
  have hrel : (relComplex A A'' f g hfg k).f.val.app V
        ((PresheafOfModules.tensorSheafUnit E' (A.exteriorPower k)).app V (a ⊗ₜ b)) =
      Stacks.degCast (F := fun l : ℤ => ((A.exterior.piece l).val.obj V : Type u)) hdeg
        ((A.exterior.mul 1 (k : ℤ)).app V
          (A.exteriorGenerator.val.app V (f.val.app V a)) b) :=
    Eq.trans (_root_.SheafOfModules.GradedAlgebra.presentationShortComplex_f_unit
        A.exterior_isExteriorAlgebra.isUniversal f g _ _ (k : ℤ) ((k + 1 : ℕ) : ℤ) hdeg V a b)
      (_root_.SheafOfModules.SymPresentation.eqToHom_val_app A.exterior.piece hdeg V _)
  refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply
    (tensorLeftMapFrom (P := P) (relComplex A A'' f g hfg k).f)
    (wedgeHomFrom A' A f u (k + 1)) V _) ?_
  refine Eq.trans (congrArg ((wedgeHomFrom A' A f u (k + 1)).val.app V)
    (tensorLeftMapFrom_unit (P := P) _ V w _)) ?_
  refine Eq.trans (wedgeHomFrom_unit A' A f u (k + 1) V w _) ?_
  refine Eq.trans (congrArg
    (fun y => (A.exterior.mul (n : ℤ) ((k + 1 : ℕ) : ℤ)).app V
      (((extHom A' A f).app (n : ℤ)).val.app V (u.val.app V w)) y)
    hrel) ?_
  refine (A.exterior.toPresheafGradedAlgebra).incl_inj_of_proj
    (i := (n : ℤ) + ((k + 1 : ℕ) : ℤ)) ?_
  refine Eq.trans ((A.exterior.toPresheafGradedAlgebra).incl_mul_incl (n : ℤ)
    ((k + 1 : ℕ) : ℤ) _ _).symm ?_
  refine Eq.trans (congrArg (fun z => (A.exterior.toPresheafGradedAlgebra).incl (n : ℤ)
    (((extHom A' A f).app (n : ℤ)).val.app V (u.val.app V w)) * z)
    ((A.exterior.toPresheafGradedAlgebra).incl_degCast hdeg _)) ?_
  refine Eq.trans (congrArg (fun z => (A.exterior.toPresheafGradedAlgebra).incl (n : ℤ)
    (((extHom A' A f).app (n : ℤ)).val.app V (u.val.app V w)) * z)
    ((A.exterior.toPresheafGradedAlgebra).incl_mul_incl 1 (k : ℤ)
      (A.exteriorGenerator.val.app V (f.val.app V a)) b).symm) ?_
  refine Eq.trans (mul_assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z * (A.exterior.toPresheafGradedAlgebra).incl (k : ℤ) b)
    ((A.exterior.toPresheafGradedAlgebra).incl_mul_incl (n : ℤ) 1 _ _)) ?_
  refine Eq.trans (congrArg (fun z => (A.exterior.toPresheafGradedAlgebra).incl ((n : ℤ) + 1) z *
    (A.exterior.toPresheafGradedAlgebra).incl (k : ℤ) b) (hu V w a)) ?_
  rw [(A.exterior.toPresheafGradedAlgebra).incl_zero, zero_mul,
    (A.exterior.toPresheafGradedAlgebra).incl_zero]

/-- **The wedge map out of `P` kills the relation of [Stacks, Tag 01CJ]**, provided the image in
`⋀ⁿ E` of every local section of `P` is killed by the degree-one sections coming from `E'`. -/
theorem wedgeHomFrom_tensorLeftMap_relComplex_f
    (hu : ∀ (V : (Opens ↥X)ᵒᵖ) (w : P.val.obj V) (a : E'.val.obj V),
      (A.exterior.mul (n : ℤ) 1).app V
          (((extHom A' A f).app (n : ℤ)).val.app V (u.val.app V w))
        (A.exteriorGenerator.val.app V (f.val.app V a)) = 0)
    (k : ℕ) :
    (tensorLeftFunctorFrom (P := P)).map (relComplex A A'' f g hfg k).f ≫
      wedgeHomFrom A' A f u (k + 1) = 0 :=
  tensorSheaf_hom_ext_right (F := P) (G := E') (H := A.exteriorPower k)
    (Q := A.exteriorPower (n + (k + 1)))
    (φ := tensorLeftMapFrom (P := P) (relComplex A A'' f g hfg k).f ≫
      wedgeHomFrom A' A f u (k + 1))
    (ψ := (0 : (tensorLeftFunctorFrom (P := P)).obj (relComplex A A'' f g hfg k).X₁ ⟶
      A.exteriorPower (n + (k + 1))))
    fun V w a b =>
      (wedgeHomFrom_tensorLeftMap_relComplex_f_unit A' A A'' f g hfg u hu k V w a b).trans rfl

/-- The exactness of the tensored presentation of [Stacks, Tag 01CJ], as a colimit:
`P ⊗ ⋀ᵏ⁺¹ E''` is the cokernel of `P ⊗ (E' ⊗ ⋀ᵏ E) ⟶ P ⊗ ⋀ᵏ⁺¹ E`. -/
noncomputable def relCokernelIsColimitFrom
    (hS : (ShortComplex.mk f g hfg).Exact) [Epi g] (k : ℕ) :
    Limits.IsColimit ((Limits.CokernelCofork.ofπ (relComplex A A'' f g hfg k).g
      (relComplex A A'' f g hfg k).zero).map (tensorLeftFunctorFrom (P := P))) := by
  have hepi : Epi (relComplex A A'' f g hfg k).g :=
    (_root_.SheafOfModules.ExtPresentation.exteriorPresentation_exact A.exteriorGenerator
      A''.exteriorGenerator A.exterior_isExteriorAlgebra A''.exterior_isExteriorAlgebra g f hfg
      hS k).2
  have hbal := balanced_sheafOfModules (X := X) (Osharp := Osharp)
  exact Limits.CokernelCofork.mapIsColimit _
    (_root_.SheafOfModules.ExtPresentation.exteriorPresentation_exact A.exteriorGenerator
      A''.exteriorGenerator A.exterior_isExteriorAlgebra A''.exterior_isExteriorAlgebra g f hfg
      hS k).1.gIsCokernel (tensorLeftFunctorFrom (P := P))

/-- **The comparison `P ⊗ ⋀ᵏ⁺¹ E'' ⟶ ⋀ⁿ⁺ᵏ⁺¹ E`** attached to an exact sequence
`E' --f--> E --g--> E''` with `g` epi and to a morphism `u : P ⟶ ⋀ⁿ E'` whose values are killed
by the degree-one sections coming from `E'`.

It is the descent of the wedge map `P ⊗ ⋀ᵏ⁺¹ E ⟶ ⋀ⁿ⁺ᵏ⁺¹ E` along the presentation
`E' ⊗ ⋀ᵏ E ⟶ ⋀ᵏ⁺¹ E ⟶ ⋀ᵏ⁺¹ E'' ⟶ 0` of [Stacks, Tag 01CJ] tensored with `P`. -/
noncomputable def detComparisonFrom
    (hu : ∀ (V : (Opens ↥X)ᵒᵖ) (w : P.val.obj V) (a : E'.val.obj V),
      (A.exterior.mul (n : ℤ) 1).app V
          (((extHom A' A f).app (n : ℤ)).val.app V (u.val.app V w))
        (A.exteriorGenerator.val.app V (f.val.app V a)) = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Epi g] (k : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj P).obj (A''.exteriorPower
        (k + 1)) ⟶
      A.exteriorPower (n + (k + 1)) :=
  (relCokernelIsColimitFrom A A'' f g hfg (P := P) hS k).desc
    (Limits.CokernelCofork.ofπ (wedgeHomFrom A' A f u (k + 1))
      (wedgeHomFrom_tensorLeftMap_relComplex_f A' A A'' f g hfg u hu k))

/-- **The defining equation of the comparison**: precomposed with `P` tensored with the
degree-`k+1` exterior power of `g`, it is the wedge map. -/
theorem tensorLeftMap_comp_detComparisonFrom
    (hu : ∀ (V : (Opens ↥X)ᵒᵖ) (w : P.val.obj V) (a : E'.val.obj V),
      (A.exterior.mul (n : ℤ) 1).app V
          (((extHom A' A f).app (n : ℤ)).val.app V (u.val.app V w))
        (A.exteriorGenerator.val.app V (f.val.app V a)) = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Epi g] (k : ℕ) :
    tensorLeftMapFrom (P := P) ((extHom A A'' g).app ((k + 1 : ℕ) : ℤ)) ≫
        detComparisonFrom A' A A'' f g hfg u hu hS k =
      wedgeHomFrom A' A f u (k + 1) :=
  Limits.Cofork.IsColimit.π_desc (relCokernelIsColimitFrom A A'' f g hfg (P := P) hS k)

/-- **The comparison is the only morphism satisfying its defining equation**: a morphism
`P ⊗ ⋀ᵏ⁺¹ E'' ⟶ ⋀ⁿ⁺ᵏ⁺¹ E` whose composite with `P ⊗ ⋀ᵏ⁺¹(g)` is the wedge map is
`detComparisonFrom`. -/
theorem eq_detComparisonFrom
    (hu : ∀ (V : (Opens ↥X)ᵒᵖ) (w : P.val.obj V) (a : E'.val.obj V),
      (A.exterior.mul (n : ℤ) 1).app V
          (((extHom A' A f).app (n : ℤ)).val.app V (u.val.app V w))
        (A.exteriorGenerator.val.app V (f.val.app V a)) = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Epi g] (k : ℕ)
    (ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj P).obj
        (A''.exteriorPower (k + 1)) ⟶
      A.exteriorPower (n + (k + 1)))
    (hψ : tensorLeftMapFrom (P := P) ((extHom A A'' g).app ((k + 1 : ℕ) : ℤ)) ≫ ψ =
      wedgeHomFrom A' A f u (k + 1)) :
    ψ = detComparisonFrom A' A A'' f g hfg u hu hS k := by
  have hepi' : Epi (tensorLeftMapFrom (P := P) ((extHom A A'' g).app ((k + 1 : ℕ) : ℤ))) :=
    Limits.epi_of_isColimit_cofork (relCokernelIsColimitFrom A A'' f g hfg (P := P) hS k)
  exact (cancel_epi (tensorLeftMapFrom (P := P)
    ((extHom A A'' g).app ((k + 1 : ℕ) : ℤ)))).1
    (hψ.trans (tensorLeftMap_comp_detComparisonFrom A' A A'' f g hfg u hu hS k).symm)

end DescentFrom

/-! ### The stalks of a finite locally free sheaf of modules, of no particular rank -/

section StalkFree

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

attribute [local implicit_reducible] LocallyFreeRank.toRingSheaf

/-- **The stalks of a finite locally free sheaf of modules are finite free**, of a rank which
may vary from point to point. -/
theorem exists_nonempty_stalkLinearEquiv_finsupp
    (F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (x : ↥X) :
    ∃ r : ℕ, Nonempty (↑(TopCat.Presheaf.stalk F.val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      (Fin r →₀ ↑(TopCat.Presheaf.stalk Osharp.obj x))) := by
  obtain ⟨q, hq, hfin⟩ := hF.exists_isFiniteLocallyFreeData
  have hxcover : x ∈ ⨆ i, q.X i := by
    rw [(Opens.coversTop_iff X q.X).mp q.coversTop]; trivial
  rw [Opens.mem_iSup] at hxcover
  obtain ⟨i, hi⟩ := hxcover
  have hfinI : Finite (q.generators i).I := (hfin.isFiniteType i).finite
  obtain ⟨e⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp X Osharp F x hi
    (trivializationOfGenerators F q hq i)
  exact ⟨Nat.card (q.generators i).I,
    ⟨e.trans (Finsupp.domLCongr (Finite.equivFin (q.generators i).I))⟩⟩

/-- **A trivialisation of a sheaf of modules over an open with finite index type makes every
stalk over that open free**, of the rank given by the cardinality of its index type. -/
theorem nonempty_stalkLinearEquiv_finsupp_of_trivialization
    (F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    {U : Opens ↥X}
    (t : LocallyFreeRank.Trivialization X (LocallyFreeRank.toRingSheaf X Osharp) F U)
    (hfinI : Finite t.ι) (y : ↥X) (hy : y ∈ U) :
    Nonempty (↑(TopCat.Presheaf.stalk F.val.presheaf y)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj y)]
      (Fin (Nat.card t.ι) →₀ ↑(TopCat.Presheaf.stalk Osharp.obj y))) := by
  have := hfinI
  obtain ⟨e⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp X Osharp F y hy t
  exact ⟨e.trans (Finsupp.domLCongr (Finite.equivFin t.ι))⟩

/-- **A finite locally free sheaf of modules has, around every point, a neighbourhood on which
all its stalks are free of one and the same rank.** -/
theorem exists_nbhd_forall_nonempty_stalkLinearEquiv_finsupp
    (F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (x : ↥X) :
    ∃ (r : ℕ) (W : Opens ↥X), x ∈ W ∧ ∀ y ∈ W,
      Nonempty (↑(TopCat.Presheaf.stalk F.val.presheaf y)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj y)]
        (Fin r →₀ ↑(TopCat.Presheaf.stalk Osharp.obj y))) := by
  obtain ⟨q, hq, hfin⟩ := hF.exists_isFiniteLocallyFreeData
  have hxcover : x ∈ ⨆ i, q.X i := by
    rw [(Opens.coversTop_iff X q.X).mp q.coversTop]; trivial
  rw [Opens.mem_iSup] at hxcover
  obtain ⟨i, hi⟩ := hxcover
  have hfinI : Finite (q.generators i).I := (hfin.isFiniteType i).finite
  exact ⟨Nat.card (trivializationOfGenerators F q hq i).ι, q.X i, hi, fun y hy =>
    nonempty_stalkLinearEquiv_finsupp_of_trivialization F
      (trivializationOfGenerators F q hq i) hfinI y hy⟩

end StalkFree

end Stacks.SheafOfModules.TopWedge

/-! ### The exterior powers of a finite free module above its rank -/

namespace Stacks.ExteriorPower

/-- **The exterior powers of a finite free module above its rank vanish**: if `M` has a basis
indexed by `Fin r` and `r < n`, then `⋀ⁿ M` is a subsingleton. -/
@[sga "6 VII 4.1" "special case"]
theorem subsingleton_exteriorPower_of_lt {R : Type u} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {r : ℕ} (b : Module.Basis (Fin r) R M) {n : ℕ} (hrn : r < n) :
    Subsingleton (⋀[R]^n M) := by
  have hempty : IsEmpty ↥(Set.powersetCard (Fin r) n) := by
    refine ⟨fun s => ?_⟩
    have hs : (s : Finset (Fin r)).card = n := s.2
    have hcard : (s : Finset (Fin r)).card ≤ r := by
      simpa using (s : Finset (Fin r)).card_le_univ
    omega
  have hsub : Subsingleton (↥(Set.powersetCard (Fin r) n) →₀ R) :=
    ⟨fun a c => Finsupp.ext fun i => hempty.elim i⟩
  exact (b.exteriorPower n).repr.toEquiv.subsingleton

end Stacks.ExteriorPower

namespace Stacks.SheafOfModules.TopWedge

/-! ### An exterior annihilated section is annihilated on the right as well -/

section RightAnnihilated

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **The degreewise annihilator vanishes away from the rank of the stalk**: if the stalk of `E'`
at `x` is free of rank `r`, the degree-`n` part of the annihilator of its exterior algebra is
zero for `n ≠ r`. -/
theorem part_stalk_eq_bot_of_stalkLinearEquiv (x : ↥X) (r : ℕ)
    (e : ↑(TopCat.Presheaf.stalk E'.val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      (Fin r →₀ ↑(TopCat.Presheaf.stalk Osharp.obj x))) (n : ℕ) (hn : n ≠ r) :
    Stacks.ExteriorAnnihilator.part (ToType (TopCat.Presheaf.stalk Osharp.obj x))
      (ToType (TopCat.Presheaf.stalk E'.val.presheaf x)) n = ⊥ := by
  by_cases htriv : Subsingleton (ToType (TopCat.Presheaf.stalk Osharp.obj x))
  · have := htriv
    exact Stacks.ExteriorAnnihilator.part_eq_bot_of_subsingleton n
  · have hnt : Nontrivial (ToType (TopCat.Presheaf.stalk Osharp.obj x)) :=
      not_subsingleton_iff_nontrivial.mp htriv
    have b : Module.Basis (Fin r) (ToType (TopCat.Presheaf.stalk Osharp.obj x))
        (ToType (TopCat.Presheaf.stalk E'.val.presheaf x)) := Module.Basis.ofRepr e
    have hfree : Module.Free (ToType (TopCat.Presheaf.stalk Osharp.obj x))
        (ToType (TopCat.Presheaf.stalk E'.val.presheaf x)) := Module.Free.of_basis b
    have hfin : Module.Finite (ToType (TopCat.Presheaf.stalk Osharp.obj x))
        (ToType (TopCat.Presheaf.stalk E'.val.presheaf x)) := Module.Finite.of_basis b
    have hrank : Module.finrank (ToType (TopCat.Presheaf.stalk Osharp.obj x))
        (ToType (TopCat.Presheaf.stalk E'.val.presheaf x)) = r := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    exact Stacks.ExteriorAnnihilator.part_eq_bot_of_free_of_ne n (by rw [hrank]; exact hn)

variable (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')

/-- The germ of an exterior annihilated section of `⋀ⁿ E'` vanishes at a point where the stalk
of `E'` is free of rank `r ≠ n`. -/
theorem germ_eq_zero_of_isExteriorAnnihilated (x : ↥X) (r : ℕ)
    (e : ↑(TopCat.Presheaf.stalk E'.val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      (Fin r →₀ ↑(TopCat.Presheaf.stalk Osharp.obj x))) (n : ℕ) (hn : n ≠ r)
    {V : Opens ↥X} (hx : x ∈ V) (ω : ToType ((A'.exteriorPower n).val.obj (op V)))
    (hω : A'.IsExteriorAnnihilated n ω) :
    Stacks.SheafOfModules.germ (A'.exteriorPower n) x hx ω = 0 := by
  refine A'.germ_eq_zero_of_germWedge_eq_zero x n hx ω ?_
  have hmem : A'.exteriorPowerStalkEquiv n x
      (Stacks.SheafOfModules.germ (A'.exteriorPower n) x hx ω) ∈
      Stacks.ExteriorAnnihilator.part (ToType (TopCat.Presheaf.stalk Osharp.obj x))
        (ToType (TopCat.Presheaf.stalk E'.val.presheaf x)) n :=
    (Stacks.ExteriorAnnihilator.mem_part_iff _).mpr fun μ =>
      A'.mul_germWedge_eq_zero_of_isExteriorAnnihilated x n hx ω hω μ
  exact congrArg Subtype.val ((Submodule.mem_bot _).1
    ((part_stalk_eq_bot_of_stalkLinearEquiv x r e n hn).le hmem))

/-- Every germ of `⋀ᵐ E'` at a point whose stalk has vanishing `m`th exterior power vanishes. -/
theorem germ_eq_zero_of_subsingleton_exteriorPower (x : ↥X) (m : ℕ)
    (hsub : Subsingleton (⋀[ToType (TopCat.Presheaf.stalk Osharp.obj x)]^m
      (ToType (TopCat.Presheaf.stalk E'.val.presheaf x))))
    {V : Opens ↥X} (hx : x ∈ V) (t : ToType ((A'.exteriorPower m).val.obj (op V))) :
    Stacks.SheafOfModules.germ (A'.exteriorPower m) x hx t = 0 := by
  refine A'.germ_eq_zero_of_germWedge_eq_zero x m hx t ?_
  have := hsub
  exact congrArg Subtype.val (Subsingleton.elim
    (A'.exteriorPowerStalkEquiv m x
      (Stacks.SheafOfModules.germ (A'.exteriorPower m) x hx t)) 0)

/-- The restriction of a product of a homogeneous section with any section vanishes as soon as
the restriction of the first factor does. -/
theorem res_mul_eq_zero_of_res_eq_zero (n : ℕ) {V W : Opens ↥X} (fW : W ⟶ V)
    (ω : ToType ((A'.exteriorPower n).val.obj (op V)))
    (hω : Stacks.SheafOfModules.res (A'.exteriorPower n) fW ω = 0)
    (y : ToType ((A'.exterior.piece 1).val.obj (op V))) :
    Stacks.SheafOfModules.res (A'.exterior.piece ((n : ℤ) + 1)) fW
      ((A'.exterior.mul (n : ℤ) 1).app (op V) ω y) = 0 := by
  refine Eq.trans ((A'.exterior.mul (n : ℤ) 1).naturality fW.op ω y) ?_
  refine Eq.trans (congrArg (fun z => (A'.exterior.mul (n : ℤ) 1).app (op W) z
    (Stacks.SheafOfModules.res (A'.exterior.piece 1) fW y)) hω) ?_
  rw [map_zero]
  rfl

/-- The degree shift `n + 1` read as an equality of integer degrees. -/
theorem natCast_add_one (n : ℕ) : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring

/-- **Every germ of the right-hand product of an exterior annihilated section with a degree-one
section vanishes**, for `E'` finite locally free. -/
theorem germ_mul_exteriorGenerator_eq_zero
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E'] (n : ℕ)
    {V : Opens ↥X} (x : ↥X) (hx : x ∈ V)
    (ω : ToType ((A'.exteriorPower n).val.obj (op V)))
    (hω : A'.IsExteriorAnnihilated n ω) (a : ToType (E'.val.obj (op V))) :
    Stacks.SheafOfModules.germ (A'.exteriorPower (n + 1)) x hx
      (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.sectionCast
        (fun l : ℤ => A'.exterior.piece l) (op V) (natCast_add_one n)
        ((A'.exterior.mul (n : ℤ) 1).app (op V) ω
          (A'.exteriorGenerator.val.app (op V) a))) = 0 := by
  obtain ⟨r, ⟨e⟩⟩ := exists_nonempty_stalkLinearEquiv_finsupp E' x
  by_cases hn : n = r
  · refine germ_eq_zero_of_subsingleton_exteriorPower A' x (n + 1) ?_ hx _
    exact Stacks.ExteriorPower.subsingleton_exteriorPower_of_lt (Module.Basis.ofRepr e)
      (by omega)
  · obtain ⟨W, fW, hxW, hres⟩ := Stacks.SheafOfModules.exists_res_eq x hx ω 0
      ((germ_eq_zero_of_isExteriorAnnihilated A' x r e n hn hx ω hω).trans
        (Stacks.SheafOfModules.germ_zero x hx).symm)
    have hω0 : Stacks.SheafOfModules.res (A'.exteriorPower n) fW ω = 0 :=
      hres.trans (Stacks.SheafOfModules.res_zero (A'.exteriorPower n) fW)
    have hzero : Stacks.SheafOfModules.res (A'.exteriorPower (n + 1)) fW
        (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.sectionCast
          (fun l : ℤ => A'.exterior.piece l) (op V) (natCast_add_one n)
          ((A'.exterior.mul (n : ℤ) 1).app (op V) ω
            (A'.exteriorGenerator.val.app (op V) a))) = 0 := by
      refine Eq.trans (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.sectionCast_res
        (P := fun l : ℤ => A'.exterior.piece l) (natCast_add_one n) fW.op _) ?_
      refine Eq.trans (congrArg
        (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.sectionCast
          (fun l : ℤ => A'.exterior.piece l) (op W) (natCast_add_one n))
        (res_mul_eq_zero_of_res_eq_zero A' n fW ω hω0 _)) ?_
      exact _root_.SheafOfModules.TensorExteriorSymmetricAlgebras.sectionCast_zero
        (natCast_add_one n)
    refine Eq.trans (Stacks.SheafOfModules.germ_res x fW hxW _).symm ?_
    exact Eq.trans (congrArg (Stacks.SheafOfModules.germ (A'.exteriorPower (n + 1)) x hxW)
      hzero) (Stacks.SheafOfModules.germ_zero x hxW)

/-- **An exterior annihilated local section of `⋀ⁿ E'` is killed by a degree-one section on the
right**, for `E'` finite locally free of no particular rank. The annihilator of
[Stacks, Tag 0FJN] is defined by multiplication on the left. -/
theorem mul_exteriorGenerator_eq_zero_of_annihilated
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E'] (n : ℕ)
    (V : Opens ↥X) (ω : ToType ((A'.exteriorPower n).val.obj (op V)))
    (hω : A'.IsExteriorAnnihilated n ω) (a : ToType (E'.val.obj (op V))) :
    (A'.exterior.mul (n : ℤ) 1).app (op V) ω
      (A'.exteriorGenerator.val.app (op V) a) = 0 := by
  refine (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.sectionCast_eq_zero_iff
    (P := fun l : ℤ => A'.exterior.piece l) (natCast_add_one n) _).mp ?_
  refine TopCat.Presheaf.IsSheaf.section_ext
    (F := (A'.exteriorPower (n + 1)).val.presheaf) (A'.exteriorPower (n + 1)).isSheaf ?_
  intro x hx
  obtain ⟨W, fW, hxW, hres⟩ := Stacks.SheafOfModules.exists_res_eq x hx _ 0
    ((germ_mul_exteriorGenerator_eq_zero A' n x hx ω hω a).trans
      (Stacks.SheafOfModules.germ_zero x hx).symm)
  exact ⟨W, fW.le, hxW, hres⟩

end RightAnnihilated

/-! ### The comparison out of a determinant summand -/

section Annihilator

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

variable (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E'')
  (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)

/-- **The image in `⋀ⁿ E` of an exterior annihilated section of `⋀ⁿ E'` is killed by the
degree-one sections coming from `E'`**, for `E'` finite locally free of no particular rank. -/
theorem mul_extHom_generator_eq_zero_of_annihilated
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E'] (n : ℕ)
    (V : Opens ↥X) (ω : ToType ((A'.exteriorPower n).val.obj (op V)))
    (hω : A'.IsExteriorAnnihilated n ω) (a : ToType (E'.val.obj (op V))) :
    (A.exterior.mul (n : ℤ) 1).app (op V)
        (((extHom A' A f).app (n : ℤ)).val.app (op V) ω)
      (A.exteriorGenerator.val.app (op V) (f.val.app (op V) a)) = 0 := by
  have hz : (A'.exterior.mul (n : ℤ) 1).app (op V) ω
      (A'.exteriorGenerator.val.app (op V) a) = 0 :=
    mul_exteriorGenerator_eq_zero_of_annihilated A' n V ω hω a
  refine Eq.trans (congrArg
    ((A.exterior.mul (n : ℤ) 1).app (op V) (((extHom A' A f).app (n : ℤ)).val.app (op V) ω))
    (extHom_app_one A' A f (op V) a).symm) ?_
  refine Eq.trans ((extHom A' A f).map_mul (n : ℤ) 1 (op V) ω
    (A'.exteriorGenerator.val.app (op V) a)).symm ?_
  exact Eq.trans (congrArg (((extHom A' A f).app ((n : ℤ) + 1)).val.app (op V)) hz) (map_zero _)

/-- The image in `⋀ⁿ E` of a local section of the degree-`n` exterior annihilator of `E'` is
killed by the degree-one sections coming from `E'`, for `E'` finite locally free. -/
theorem mul_extHom_exteriorAnnihilator_ι_eq_zero
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E'] (n : ℕ)
    (V : (Opens ↥X)ᵒᵖ)
    (w : ((A'.exteriorAnnihilator n).toSheafOfModules).val.obj V)
    (a : E'.val.obj V) :
    (A.exterior.mul (n : ℤ) 1).app V
        (((extHom A' A f).app (n : ℤ)).val.app V
          ((A'.exteriorAnnihilator n).ι.val.app V w))
      (A.exteriorGenerator.val.app V (f.val.app V (a : E'.val.obj V))) = 0 :=
  mul_extHom_generator_eq_zero_of_annihilated A' A f n V.unop _ (Subtype.property w) a

/-- **The comparison `det(E')ₙ ⊗ ⋀ᵏ⁺¹ E'' ⟶ ⋀ⁿ⁺ᵏ⁺¹ E` of a short exact sequence of sheaves of
modules, with `E'` finite locally free of no particular rank.** Here `det(E')ₙ` is the
degree-`n` exterior annihilator of [Stacks, Tag 0FJN], the degree-`n` summand of `det(E')`, and
the comparison is `Stacks.SheafOfModules.TopWedge.detComparisonFrom` for the inclusion
`det(E')ₙ ⟶ ⋀ⁿ E'`. -/
noncomputable def detAnnihilatorComparison
    (hS : (ShortComplex.mk f g hfg).Exact) [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E'] (n k : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj ((A'.exteriorAnnihilator
        n).toSheafOfModules)).obj (A''.exteriorPower (k + 1)) ⟶
      A.exteriorPower (n + (k + 1)) :=
  detComparisonFrom A' A A'' f g hfg (A'.exteriorAnnihilator n).ι
    (mul_extHom_exteriorAnnihilator_ι_eq_zero A' A f n) hS k

end Annihilator

/-! ### The defining equations of the comparison -/

section Equations

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

variable (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E'')
  (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0) {n : ℕ}
  {P : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (u : P ⟶ A'.exteriorPower n)
  (hS : (ShortComplex.mk f g hfg).Exact) (k : ℕ)

/-- **The defining equation of the comparison, on local sections.** On the image of
`w ⊗ ⋀ᵏ⁺¹(g)(η)` the comparison is the image of `w` in `⋀ⁿ E` wedged with `η`. -/
theorem detComparisonFrom_unit
    (hu : ∀ (V : (Opens ↥X)ᵒᵖ) (w : P.val.obj V) (a : E'.val.obj V),
      (A.exterior.mul (n : ℤ) 1).app V
          (((extHom A' A f).app (n : ℤ)).val.app V (u.val.app V w))
        (A.exteriorGenerator.val.app V (f.val.app V a)) = 0)
    [Epi g] (V : (Opens ↥X)ᵒᵖ) (w : P.val.obj V)
    (η : (A.exteriorPower (k + 1)).val.obj V) :
    (detComparisonFrom A' A A'' f g hfg u hu hS k).val.app V
        ((PresheafOfModules.tensorSheafUnit P (A''.exteriorPower (k + 1))).app V
          (w ⊗ₜ ((extHom A A'' g).app ((k + 1 : ℕ) : ℤ)).val.app V η)) =
      (A.exterior.mul (n : ℤ) ((k + 1 : ℕ) : ℤ)).app V
        (((extHom A' A f).app (n : ℤ)).val.app V (u.val.app V w)) η := by
  have h := congrArg (fun m : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
      P).obj
      (A.exteriorPower (k + 1)) ⟶ A.exteriorPower (n + (k + 1)) =>
      m.val.app V ((PresheafOfModules.tensorSheafUnit P
        (A.exteriorPower (k + 1))).app V (w ⊗ₜ η)))
    (tensorLeftMap_comp_detComparisonFrom A' A A'' f g hfg u hu hS k)
  refine Eq.trans ?_ (h.trans (wedgeHomFrom_unit A' A f u (k + 1) V w η))
  refine Eq.trans ?_ (_root_.SheafOfModules.comp_val_app_apply _ _ V _).symm
  exact congrArg ((detComparisonFrom A' A A'' f g hfg u hu hS k).val.app V)
    (tensorLeftMapFrom_unit (P := P) _ V w η).symm

/-- **The wedge-and-lift formula for the comparison out of `P`.** The comparison carries the
image of `w ⊗ (g(l₁) ∧ ⋯ ∧ g(l_{k+1}))` to the image of `w` in `⋀ⁿ E` wedged with
`l₁ ∧ ⋯ ∧ l_{k+1}`, for arbitrary local lifts `lⱼ` ([Stacks, Tag 0B38]). -/
theorem detComparisonFrom_wedge
    (hu : ∀ (V : (Opens ↥X)ᵒᵖ) (w : P.val.obj V) (a : E'.val.obj V),
      (A.exterior.mul (n : ℤ) 1).app V
          (((extHom A' A f).app (n : ℤ)).val.app V (u.val.app V w))
        (A.exteriorGenerator.val.app V (f.val.app V a)) = 0)
    [Epi g] (V : (Opens ↥X)ᵒᵖ) (w : P.val.obj V)
    (l : Fin (k + 1) → E.val.obj V) :
    (detComparisonFrom A' A A'' f g hfg u hu hS k).val.app V
        ((PresheafOfModules.tensorSheafUnit P (A''.exteriorPower (k + 1))).app V
          (w ⊗ₜ wedgeSec A'' V (k + 1) fun i => g.val.app V (l i))) =
      (A.exterior.mul (n : ℤ) ((k + 1 : ℕ) : ℤ)).app V
        (((extHom A' A f).app (n : ℤ)).val.app V (u.val.app V w))
        (wedgeSec A V (k + 1) l) := by
  refine Eq.trans (congrArg (fun y => (detComparisonFrom A' A A'' f g hfg u hu hS k).val.app V
      ((PresheafOfModules.tensorSheafUnit P (A''.exteriorPower (k + 1))).app V (w ⊗ₜ y)))
    (extHom_wedgeSec A A'' g V (k + 1) l).symm) ?_
  exact detComparisonFrom_unit A' A A'' f g hfg u hS k hu V w (wedgeSec A V (k + 1) l)

end Equations

/-! ### Through the identity: the constant-rank comparison -/

section Identity

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

variable (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E'')
  (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0) (n : ℕ)

/-- Through the identity of `⋀ⁿ E'` the bilinear wedge map out of `P` is the bilinear wedge
map. -/
theorem wedgeBilinearFrom_id (s : ℕ) :
    wedgeBilinearFrom A' A f (𝟙 (A'.exteriorPower n)) s = wedgeBilinear A' A f n s :=
  Stacks.BilinearMap.ext fun _ _ _ => rfl

/-- Through the identity of `⋀ⁿ E'` the wedge map out of `P` is the wedge map. -/
theorem wedgeHomFrom_id (s : ℕ) :
    wedgeHomFrom A' A f (𝟙 (A'.exteriorPower n)) s = wedgeHom A' A f n s := by
  rw [wedgeHomFrom, wedgeHom, wedgeBilinearFrom_id]

/-- **At `P = ⋀ⁿ E'` and `u` the identity, the comparison is
`Stacks.SheafOfModules.TopWedge.detComparison`**, for `E'` finite locally free of rank `n`. -/
theorem detComparisonFrom_exteriorPower_id
    (hu : ∀ (V : (Opens ↥X)ᵒᵖ) (w : (A'.exteriorPower n).val.obj V) (a : E'.val.obj V),
      (A.exterior.mul (n : ℤ) 1).app V
          (((extHom A' A f).app (n : ℤ)).val.app V
            ((𝟙 (A'.exteriorPower n) :
              A'.exteriorPower n ⟶ A'.exteriorPower n).val.app V w))
        (A.exteriorGenerator.val.app V (f.val.app V a)) = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Epi g] (k : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' n] :
    detComparisonFrom A' A A'' f g hfg (𝟙 (A'.exteriorPower n)) hu hS k =
      detComparison A' A A'' f g hfg hS n k :=
  eq_detComparison A' A A'' f g hfg hS n k _
    ((tensorLeftMap_comp_detComparisonFrom A' A A'' f g hfg (𝟙 (A'.exteriorPower n)) hu hS
      k).trans (wedgeHomFrom_id A' A f n (k + 1)))

end Identity

end Stacks.SheafOfModules.TopWedge

end
