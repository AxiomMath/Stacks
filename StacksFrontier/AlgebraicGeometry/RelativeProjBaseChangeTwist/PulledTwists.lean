module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.ChartSections
public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.SectionIso

/-!
# The pulled-back twists on the base change of a relative `Proj`, on the charts

For a morphism `h : Z ⟶ Y`, a sheaf of graded algebras `G` on `Y`, and an open immersion
`k : W ⟶ Z` with `k ≫ h` factored through a chart of `Y`, this file identifies `k^*h^*G` with a
given graded family on `W`, degreewise and multiplicatively. The case of interest is the pullback
of the graded algebra of twists of Tag 01NR along the base change
`Proj_{S'}(g^*A) ⟶ Proj_S(A)`, on the charts over the members of `baseChangeBasis g`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.genChartIso`: the chart identification.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.genChartIso_hom_mul`: it carries the
  product of `h^*G` to the product of the family.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open Stacks.AlgebraicGeometry.RestrictionSections
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### `legTail` is invertible -/

/-- `legTail` is an isomorphism as soon as the morphism it pulls back is. -/
theorem isIso_legTail {W Z Y D Vv : Scheme.{u}} (k : W ⟶ Z) (h : Z ⟶ Y) (ρ : W ⟶ D)
    (hU : D ⟶ Vv) (c : Vv ⟶ Y) (ι : D ⟶ W) (e : k ≫ h = ρ ≫ hU ≫ c) (hρι : ρ ≫ ι = 𝟙 W)
    {M : Y.Modules} {N : Vv.Modules} {B : W.Modules}
    (χ : (Scheme.Modules.pullback c).obj M ≅ N)
    (tw : (Scheme.Modules.pullback hU).obj N ⟶ (Scheme.Modules.pullback ι).obj B) (htw : IsIso tw) :
    IsIso (legTail k h ρ hU c ι e hρι χ tw) := by
  unfold legTail
  infer_instance

/-! ### The chart identification of a pulled-back graded algebra, at the level of variables -/

section Generic

/-- The product of a sheaf of graded algebras on a scheme, as a morphism out of the canonical
tensor product sheaf `Stacks.SheafOfModules.Tensor.sheafTensor`. -/
abbrev gmul {Y : Scheme.{u}}
    (G : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace))
    (i j : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(Y.toRingedSpace).presheaf, (Y.toRingedSpace).IsSheaf⟩).obj (G.piece i)).obj (G.piece j)) ⟶
      G.piece (i + j) :=
  SheafOfModules.GradedAlgebra.mulSheaf G i j

variable {Y Z W D Vv : Scheme.{u}}
  (G : SheafOfModules.GradedAlgebra.{u, u} (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace))
  (h : Z ⟶ Y)
  (k : W ⟶ Z) [IsOpenImmersion k] (ρ : W ⟶ D) (hU : D ⟶ Vv) (c : Vv ⟶ Y) (ι : D ⟶ W)
  (e : k ≫ h = ρ ≫ hU ≫ c) (hρι : ρ ≫ ι = 𝟙 W)
  (N : ℤ → Vv.Modules) (Bt : ℤ → W.Modules)
  (χ : ∀ n, (Scheme.Modules.pullback c).obj (G.piece n) ≅ N n)
  (tw : ∀ n, (Scheme.Modules.pullback hU).obj (N n) ⟶ (Scheme.Modules.pullback ι).obj (Bt n))
  (htwIso : ∀ n, IsIso (tw n))

/-- **The chart identification of `h^*G` along an open immersion `k`**, from a factorization of
`k ≫ h` and identifications `χ`, `tw`: the identification of restriction with inverse image,
followed by `legTail`. -/
def genChartIso (n : ℤ) :
    Scheme.Modules.restrict
        ((Stacks.RingedSpace.pullbackGradedAlgebra h.toLRSHom.toShHom G).piece n) k ≅ Bt n :=
  (Scheme.Modules.restrictFunctorIsoPullback k).app _ ≪≫
    @asIso _ _ _ _ (legTail k h ρ hU c ι e hρι (χ n) (tw n))
      (isIso_legTail k h ρ hU c ι e hρι (χ n) (tw n) (htwIso n))

/-- The forward map of `genChartIso` is the identification of restriction with inverse image
followed by `legTail`. -/
theorem genChartIso_hom (n : ℤ) :
    (genChartIso G h k ρ hU c ι e hρι N Bt χ tw htwIso n).hom =
      (Scheme.Modules.restrictFunctorIsoPullback k).hom.app _ ≫
        legTail k h ρ hU c ι e hρι (χ n) (tw n) := rfl

/-- **The chart identification of `h^*G` is multiplicative on local sections**, as soon as `χ`
and `tw` are multiplicative. -/
theorem genChartIso_hom_mul
    (mulV : ∀ i j, (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(Vv.toRingedSpace).presheaf, (Vv.toRingedSpace).IsSheaf⟩).obj (N i)).obj (N j)) ⟶
      N (i + j))
    (mulB : ∀ i j, (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩).obj (Bt i)).obj (Bt j)) ⟶
      Bt (i + j))
    (hχ : ∀ i j, TwistMulLeg.pbMul c (gmul G i j) ≫
      (χ (i + j)).hom = ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(Vv.toRingedSpace).presheaf, (Vv.toRingedSpace).IsSheaf⟩)).map
          (((χ i).hom, (χ j).hom) : (_, _) ⟶ (_, _))) ≫ mulV i j)
    (htw : ∀ i j, TwistMulLeg.pbMul hU (mulV i j) ≫ tw (i + j) =
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(D.toRingedSpace).presheaf, (D.toRingedSpace).IsSheaf⟩)).map
          ((tw i, tw j) : (_, _) ⟶ (_, _))) ≫ TwistMulLeg.pbMul ι (mulB i j))
    (i j : ℤ) (U : W.Opens)
    (x : ((Stacks.RingedSpace.pullbackGradedAlgebra h.toLRSHom.toShHom G).piece i).val.obj
      (op (k ''ᵁ U)))
    (y : ((Stacks.RingedSpace.pullbackGradedAlgebra h.toLRSHom.toShHom G).piece j).val.obj
      (op (k ''ᵁ U))) :
    (genChartIso G h k ρ hU c ι e hρι N Bt χ tw htwIso (i + j)).hom.val.app (op U)
        (((Stacks.RingedSpace.pullbackGradedAlgebra h.toLRSHom.toShHom G).mul i j).app
          (op (k ''ᵁ U)) x y) =
      (mulB i j).val.app (op U) (PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (W.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (W.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (W.toRingedSpace).presheaf) (Bt i).val (Bt j).val))
          (op U)
        ((genChartIso G h k ρ hU c ι e hρι N Bt χ tw htwIso i).hom.val.app (op U) x ⊗ₜ
          (genChartIso G h k ρ hU c ι e hρι N Bt χ tw htwIso j).hom.val.app (op U) y)) := by
  have hP := legTail_mul k h ρ hU c ι e hρι (gmul G i j) (mulV i j)
    (mulB i j) (χ i) (χ j) (χ (i + j)) (hχ i j) (tw i) (tw j) (tw (i + j)) (htw i j)
  have hR := restrict_mul_of_pbMul k (TwistMulLeg.pbMul h (gmul G i j)) (mulB i j)
    (legTail k h ρ hU c ι e hρι (χ i) (tw i)) (legTail k h ρ hU c ι e hρι (χ j) (tw j))
    (legTail k h ρ hU c ι e hρι (χ (i + j)) (tw (i + j))) hP
  have hs := sections_mul_of_restrict k _ _ _ _ _ hR U x y
  have hu := SheafOfModules.GradedAlgebra.mulSheaf_unit
    (Stacks.RingedSpace.pullbackGradedAlgebra h.toLRSHom.toShHom G) i j (op (k ''ᵁ U)) x y
  have hm := congrArg (fun φ => φ.val.app (op (k ''ᵁ U))
      (PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (Z.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (Z.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (Z.toRingedSpace).presheaf)
            ((Scheme.Modules.pullback h).obj (G.piece i)).val
            ((Scheme.Modules.pullback h).obj (G.piece j)).val))
          (op (k ''ᵁ U)) (x ⊗ₜ y)))
    (mulSheaf_pullbackGradedAlgebra_eq_pbMul h G i j)
  rw [genChartIso_hom, genChartIso_hom, genChartIso_hom]
  refine Eq.trans ?_ hs
  exact congrArg (fun z => ((Scheme.Modules.restrictFunctorIsoPullback k).hom.app _ ≫
      legTail k h ρ hU c ι e hρι (χ (i + j)) (tw (i + j))).val.app (op U) z)
      (hu.symm.trans hm)

end Generic

variable {S S' : Scheme.{u}} (A : SheafGradedAlgebra S) (g : S' ⟶ S)

/-- Tag 01MY's comparison map of the graded ring map of sections is an isomorphism. -/
instance isIso_twistMap_chartMap (V : baseChangeBasis g) (n : ℤ) :
    IsIso (twistMap (A.grading (affOf V).1) ((A.pullback g).grading V.1) (chartMap A g V) n) :=
  isIso_twistMap_sectionBaseChange A g (baseOpen V) (siteOf V) (le_baseOpen V) n

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

end
