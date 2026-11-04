module

public import StacksFrontier.Deformation.RingedSpaceThickening.DeformationSolutionExtFibre
public import StacksFrontier.Deformation.RingedSpaceThickening.DerivedPullbackNaiveCotangentMap
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTriangleObstruction
import StacksCore.Tactic.StacksAttribute

/-!
# The two maps of Stacks 0GQ4 and the conditional obstruction

Let `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` be a first order thickening with ideal `𝒥`, let
`f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces, `𝒢` an `𝒪_X`-module and `c : f^*𝒥 ⟶ 𝒢`,
as in **Stacks 0GQ3**.  **Stacks 0GQ4** displays the two maps

`Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}`

in `D(𝒪_X)`, and says: *if* they form a distinguished triangle, then the image of `ξ` in
`Ext²_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` is the obstruction to the existence of a solution of (08U7).

The source writes the first term as `Lf^*𝖭𝖫_{S'/S}`; this is a typo for `Lf^*𝖭𝖫_{S/S'}`, the
naive cotangent complex of `𝒪_{S'} ⟶ 𝒪_S`, which is the only one of the two that maps to
`𝖭𝖫_{X/S'}` (and the one used in **Stacks 0GQ1** and **Stacks 0GQ3**).  The corrected form is
the one formalized here.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.naiveCotangentRemarkArrows`: the two maps of the
  remark as a diagram `Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}` in `D(𝒪_X)`.  The first map is the
  canonical map `derivedPullbackNaiveCotangentMap` of **Stacks 0GQ1** (the one through which
  the fibre of **Stacks 0GQ3** is taken), the second is `relativeNaiveCotangentObjMap`.

## Main results

* `DeformationSolution.nonempty_iff_obstructionExtClass_eq_zero`: for any `w` such that the two
  maps together with `w` form a distinguished triangle, a solution of (08U7) exists if and only if
  the image of `ξ` (the class of **Stacks 0GPZ** of `𝒪_{S'}`) in `Ext²_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`
  vanishes.

## References

* [Stacks Project, Tag 0GQ4](https://stacks.math.columbia.edu/tag/0GQ4)
* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction

universe u

attribute [local instance 10000] HasDerivedCategory.standard

-- The finite (co)products of the derived category are those of its triangulated structure, not
-- those of the instances of Stacks 07D9 (stated for the locally small model).
attribute [-instance] Stacks.Injectives.hasCoproducts_derivedCategory
  Stacks.Injectives.hasProducts_derivedCategory

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}}

/-- The two maps `Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}` in `D(𝒪_X)`. The first is the canonical
map of **Stacks 0GQ1** through the derived pullback of **Stacks 06YJ**, the second is induced by
the tower `(f ≫ t)^{-1}𝒪_{S'} ⟶ f^{-1}𝒪_S ⟶ 𝒪_X`. -/
@[stacks 0GQ4]
def naiveCotangentRemarkArrows (f : X ⟶ S) (t : S ⟶ S') :
    ComposableArrows (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) 2 :=
  ComposableArrows.mk₂ (derivedPullbackNaiveCotangentMap f t) (relativeNaiveCotangentObjMap f t)

/-- The first map of `naiveCotangentRemarkArrows f t` is `derivedPullbackNaiveCotangentMap f t`. -/
theorem naiveCotangentRemarkArrows_map_zero_one (f : X ⟶ S) (t : S ⟶ S') :
    (naiveCotangentRemarkArrows f t).map' 0 1 = derivedPullbackNaiveCotangentMap f t := rfl

/-- The second map of `naiveCotangentRemarkArrows f t` is `relativeNaiveCotangentObjMap f t`. -/
theorem naiveCotangentRemarkArrows_map_one_two (f : X ⟶ S) (t : S ⟶ S') :
    (naiveCotangentRemarkArrows f t).map' 1 2 = relativeNaiveCotangentObjMap f t := rfl

/-- In a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]`, a morphism `η : A ⟶ Y` extends along
`A ⟶ B` exactly when `C ⟶ A[1] ⟶ Y[1]` vanishes. -/
theorem exists_mor₁_comp_eq_iff_of_distTriang {C : Type*} [Category C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) {Y : C} (η : T.obj₁ ⟶ Y) :
    (∃ z : T.obj₂ ⟶ Y, T.mor₁ ≫ z = η) ↔ T.mor₃ ≫ η⟦(1 : ℤ)⟧' = 0 := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [Functor.map_comp, ← Category.assoc, comp_distTriang_mor_zero₃₁ T hT, zero_comp]
  · intro h
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ T.rotate (rot_of_distTriang T hT) (η⟦(1 : ℤ)⟧') h
    obtain ⟨z, hz⟩ := (shiftFunctor C (1 : ℤ)).map_surjective (X := T.obj₂) (Y := Y) g
    refine ⟨-z, (shiftFunctor C (1 : ℤ)).map_injective ?_⟩
    rw [hg, ← hz]
    simp only [Triangle.rotate_mor₃, Functor.map_comp, Functor.map_neg, Preadditive.comp_neg]
    exact (Preadditive.neg_comp _ _).symm

/-- In a distinguished triangle `Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S} ⟶` of `D(𝒪_X)` on the
remark's two maps, a class `η ∈ Ext¹(Lf^*𝖭𝖫_{S/S'}, 𝒢)` is the restriction of a class of
`Ext¹(𝖭𝖫_{X/S'}, 𝒢)` exactly when its image in `Ext²(𝖭𝖫_{X/S}, 𝒢)` vanishes. -/
theorem exists_restrictDerivedExtClass_eq_iff_obstructionExtClass_eq_zero {f : X ⟶ S}
    {t : S ⟶ S'} {G : SheafOfModules.{u} (structureSheafRing X)}
    (w : relativeNaiveCotangentObj f ⟶ (derivedPullbackNaiveCotangent f t)⟦(1 : ℤ)⟧)
    (htri : Triangle.mk (derivedPullbackNaiveCotangentMap f t)
        (relativeNaiveCotangentObjMap f t) w ∈
      distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (η : extOnePulledNaiveCotangent f t G) :
    (∃ z : extOneNaiveCotangent (f ≫ t) G,
        restrictDerivedExtClass (derivedPullbackNaiveCotangentMap f t) z = η) ↔
      obstructionExtClass w η = 0 := by
  refine (exists_mor₁_comp_eq_iff_of_distTriang _ htri η).trans ?_
  show w ≫ η⟦(1 : ℤ)⟧' = 0 ↔ ShiftedHom.comp w η _ = 0
  rw [ShiftedHom.comp, ← Category.assoc]
  refine ⟨fun h => by rw [h, zero_comp], fun h => ?_⟩
  rwa [← cancel_mono ((shiftFunctorAdd'
      (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (1 : ℤ) 1 2
        (by omega)).inv.app _), zero_comp]

variable {t : S ⟶ S'} (ht : IsFirstOrderThickening t) (f : X ⟶ S)
  (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf))
  (c' : (modulePullback f).obj ((modulePullback t).obj
    (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶
      (show SheafOfModules.{u} (structureSheafRing X) from G))

/-- In the situation of **Stacks 0GQ3** (a first order thickening `t : S ⟶ S'` with ideal `𝒥`,
`f : X ⟶ S`, an `𝒪_X`-module `𝒢` and `c : f^*𝒥 ⟶ 𝒢`, here `f^*𝒥 ≅ f^*t^*Ker(t^♯) ⟶ 𝒢` with `c'`),
let `ξ` be the class of the extension `𝒪_{S'}` of `𝒪_S` by `𝒥` under **Stacks 0GPZ** (`baseClass`).
*If* the two maps `Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}` form a distinguished triangle with some
connecting map `w`, then a solution of (08U7) exists if and only if the image of `ξ` in
`Ext²_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` — the image of `ξ` in `Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{S/S'}, 𝒢)`
(`pullbackExtClass`) composed with `w` — vanishes. -/
@[stacks 0GQ4]
theorem DeformationSolution.nonempty_iff_obstructionExtClass_eq_zero
    (w : relativeNaiveCotangentObj f ⟶ (derivedPullbackNaiveCotangent f t)⟦(1 : ℤ)⟧)
    (htri : Triangle.mk (derivedPullbackNaiveCotangentMap f t)
        (relativeNaiveCotangentObjMap f t) w ∈
      distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))) :
    Nonempty (DeformationSolution t ht f G c') ↔
      obstructionExtClass w (pullbackExtClass f t
        ((modulePullback f).map (baseIdealIsoPullback ht).hom ≫ c') (baseClass ht)) = 0 := by
  refine Iff.trans ?_ (exists_restrictDerivedExtClass_eq_iff_obstructionExtClass_eq_zero w htri _)
  refine Iff.trans ?_ nonempty_subtype
  refine Iff.trans ?_ (Equiv.nonempty_congr
    (DeformationSolution.isomorphismClassesEquivExtFibre ht f G c'))
  exact ⟨fun h => h.elim fun Q => ⟨Quotient.mk _ Q⟩, fun h => h.elim fun s => ⟨s.out⟩⟩

end AlgebraicGeometry.RingedSpaceThickening

end
