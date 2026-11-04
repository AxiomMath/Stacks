module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType

/-!
# The comparison of a fibre product of reductions with a fibre product

Let `S` be a scheme contained in a big fppf site `B`, let `f : X ⟶ Y` be a morphism of formal
algebraic spaces over `S`, let `iX : X_red ⟶ X` and `iY : Y_red ⟶ Y` be reductions and let
`f_red : X_red ⟶ Y_red` be compatible with `f`. For a morphism `η : U ⟶ Y_red` there is a
canonical morphism

  `U ×_{Y_red} X_red ⟶ U ×_Y X`

over `U`, where the right-hand fibre product is taken along the composite `U ⟶ Y_red ⟶ Y`. It
is a representable thickening, and in fact the square exhibiting it as the base change of
`iX : X_red ⟶ X` along `U ×_Y X ⟶ X` is cartesian.

## Main results

* `CategoryTheory.IsPullback.of_comp_mono_right`: in any category, the comparison square is
  cartesian as soon as `iY` is a monomorphism through which `X_red ⟶ Y` factors.
* `AlgebraicGeometry.FormalSpace.isPullback_baseChange_of_isReduction`: the same square for a
  pair of reductions of a morphism of formal algebraic spaces over `S`.
* `AlgebraicGeometry.FormalSpace.exists_isRepresentableThickeningULift_baseChange_of_isReduction`:
  the canonical morphism exists and is a representable thickening.

## References

* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AJB](https://stacks.math.columbia.edu/tag/0AJB)
* [Stacks Project, Tag 0CB9](https://stacks.math.columbia.edu/tag/0CB9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.IsPullback

universe v' u'

variable {C : Type u'} [Category.{v'} C]

/-- A morphism which factors through a monomorphism is cartesian over it: the square with the
identity on the left, `g` on top, the monomorphism on the right and `g ≫ b` on the bottom is
cartesian. -/
theorem of_id_comp_mono {Y Z W : C} {b : Z ⟶ W} [Mono b] (g : Y ⟶ Z) :
    IsPullback g (𝟙 Y) b (g ≫ b) := by
  simpa using (IsPullback.of_id_snd (f := g)).paste_horiz (IsKernelPair.id_of_mono b)

/-- **A fibre product over the source of a monomorphism is a fibre product over its target.**
Let `iY : Yred ⟶ Y` be a monomorphism, let `f : X ⟶ Y` and `iX : Xred ⟶ X` be morphisms and let
`fred : Xred ⟶ Yred` satisfy `fred ≫ iY = iX ≫ f`. Let `η : U ⟶ Yred`, let `P` be a fibre
product of `U` and `Xred` over `Yred` and let `W` be a fibre product of `U` and `X` over `Y`
along `η ≫ iY`. Then a morphism `c : P ⟶ W` compatible with the two projections exhibits `P`
as a fibre product of `W` and `Xred` over `X`. -/
theorem of_comp_mono_right {X Y Xred Yred U W P : C} {f : X ⟶ Y} {iX : Xred ⟶ X}
    {iY : Yred ⟶ Y} [Mono iY] {fred : Xred ⟶ Yred} (hfred : fred ≫ iY = iX ≫ f)
    {η : U ⟶ Yred} {pU : P ⟶ U} {pXred : P ⟶ Xred} (hP : IsPullback pU pXred η fred)
    {wU : W ⟶ U} {wX : W ⟶ X} (hW : IsPullback wU wX (η ≫ iY) f)
    {c : P ⟶ W} (hcU : c ≫ wU = pU) (hcX : c ≫ wX = pXred ≫ iX) :
    IsPullback c pXred wX iX := by
  have hbig : IsPullback pXred (c ≫ wU) (iX ≫ f) (η ≫ iY) := by
    rw [hcU, ← hfred]
    simpa using hP.flip.paste_vert (IsPullback.of_id_comp_mono (b := iY) η)
  exact (hbig.of_bot hcX.symm hW.flip).flip

end CategoryTheory.IsPullback

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y Xred Yred : FppfSheaf B S hS} {f : X ⟶ Y} {iX : Xred ⟶ X} {iY : Yred ⟶ Y}
  {fred : Xred ⟶ Yred}

/-- The compatibility of the morphism of reductions with the given morphism, read on the
underlying presheaves. -/
theorem hom_comp_eq_of_red (hfred : fred ≫ iY = iX ≫ f) :
    fred.hom ≫ iY.hom = iX.hom ≫ f.hom :=
  congrArg (fun k : Xred ⟶ Y ↦ k.hom) hfred

/-- **A fibre product of the reductions is a fibre product with the reduction of the source.**
Let `f : X ⟶ Y` be a morphism of fppf sheaves on the big fppf site of `S`, let `iX : Xred ⟶ X`
and `iY : Yred ⟶ Y` be reductions and let `fred : Xred ⟶ Yred` be compatible with `f`. Let
`η : U ⟶ Yred` be a morphism of presheaves, let `P` be a fibre product of `U` and `Xred` over
`Yred` and let `W` be a fibre product of `U` and `X` over `Y` along `η ≫ iY`. Then a morphism
`c : P ⟶ W` compatible with the projections exhibits `P` as a fibre product of `W` and `Xred`
over `X`. -/
theorem isPullback_baseChange_of_isReduction (hiY : IsReduction B S hS Y Yred iY)
    (hfred : fred ≫ iY = iX ≫ f)
    {U W P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {η : U ⟶ Yred.obj} {pU : P ⟶ U} {pXred : P ⟶ Xred.obj}
    (hP : IsPullback pU pXred η fred.hom)
    {wU : W ⟶ U} {wX : W ⟶ X.obj} (hW : IsPullback wU wX (η ≫ iY.hom) f.hom)
    {c : P ⟶ W} (hcU : c ≫ wU = pU) (hcX : c ≫ wX = pXred ≫ iX.hom) :
    IsPullback c pXred wX iX.hom :=
  have _ : Mono iY.hom := mono_hom_of_isReduction B S hS hiY
  IsPullback.of_comp_mono_right (hom_comp_eq_of_red B S hS hfred) hP hW hcU hcX

/-- **The comparison morphism from a fibre product of the reductions is a representable
thickening.** In the situation of
`AlgebraicGeometry.FormalSpace.isPullback_baseChange_of_isReduction`, the morphism `c` is a
representable thickening. -/
theorem isRepresentableThickeningULift_baseChange_of_isReduction
    (hiX : IsReduction B S hS X Xred iX) (hiY : IsReduction B S hS Y Yred iY)
    (hfred : fred ≫ iY = iX ≫ f)
    {U W P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {η : U ⟶ Yred.obj} {pU : P ⟶ U} {pXred : P ⟶ Xred.obj}
    (hP : IsPullback pU pXred η fred.hom)
    {wU : W ⟶ U} {wX : W ⟶ X.obj} (hW : IsPullback wU wX (η ≫ iY.hom) f.hom)
    {c : P ⟶ W} (hcU : c ≫ wU = pU) (hcX : c ≫ wX = pXred ≫ iX.hom) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS c :=
  Space.relative_of_isPullback B S hS
    (isPullback_baseChange_of_isReduction B S hS hiY hfred hP hW hcU hcX)
    hiX.isRepresentableThickening

/-- **The comparison morphism from a fibre product of the reductions exists and is a
representable thickening.** In the situation of
`AlgebraicGeometry.FormalSpace.isPullback_baseChange_of_isReduction`, there is a morphism
`c : P ⟶ W` compatible with the projections, and it is a representable thickening. -/
theorem exists_isRepresentableThickeningULift_baseChange_of_isReduction
    (hiX : IsReduction B S hS X Xred iX) (hiY : IsReduction B S hS Y Yred iY)
    (hfred : fred ≫ iY = iX ≫ f)
    {U W P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {η : U ⟶ Yred.obj} {pU : P ⟶ U} {pXred : P ⟶ Xred.obj}
    (hP : IsPullback pU pXred η fred.hom)
    {wU : W ⟶ U} {wX : W ⟶ X.obj} (hW : IsPullback wU wX (η ≫ iY.hom) f.hom) :
    ∃ c : P ⟶ W, c ≫ wU = pU ∧ c ≫ wX = pXred ≫ iX.hom ∧
      Space.IsRepresentableThickeningULift.{u + 1} B S hS c := by
  have hcomm : pU ≫ η ≫ iY.hom = (pXred ≫ iX.hom) ≫ f.hom := by
    rw [← Category.assoc, hP.w, Category.assoc, Category.assoc,
      hom_comp_eq_of_red B S hS hfred]
  exact ⟨hW.lift pU (pXred ≫ iX.hom) hcomm, hW.lift_fst _ _ _, hW.lift_snd _ _ _,
    isRepresentableThickeningULift_baseChange_of_isReduction B S hS hiX hiY hfred hP hW
      (hW.lift_fst _ _ _) (hW.lift_snd _ _ _)⟩

end AlgebraicGeometry.FormalSpace

end
