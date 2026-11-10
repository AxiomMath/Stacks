module

public import StacksFrontier.Topology.Sheaves.Modules.InverseImageGradedAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictTensorator
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDescentQuotientIso
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebraPullbackComp

/-!
# The inverse image of a sheaf of graded algebras presented as a direct image

Let `f : Y ⟶ X` be an inducing continuous map, `O` a sheaf of commutative rings on `X` and `A`
a sheaf of graded `O`-algebras.  Suppose every homogeneous piece of `A` is identified with the
direct image of the corresponding piece of a sheaf of graded algebras `B` on `Y`, *compatibly
with the multiplications*.  Then the inverse image `f⁻¹A` is isomorphic to `B` — read over
`f⁻¹O` by restriction of scalars — **as a sheaf of graded algebras**, the isomorphism carrying
the unit to the unit. In each degree the isomorphism is the adjoint transpose of the given
identification under `f⁻¹ ⊣ f_*`.

## Main results

* `Stacks.PullbackGradedAlgebra.mulSheaf_pullbackGradedAlgebra_eq_comparison`: the
  morphism-level multiplication of the pullback `φ^*A` of a sheaf of graded algebras along any
  morphism of ringed spaces `φ` is the pulled-back multiplication of `A` conjugated by the
  comparison of [Stacks, Tag 01CD].
* `Stacks.PullbackGradedAlgebra.homEquiv_symm_map_mul`: adjoint transposes of multiplicative
  maps into a direct image are multiplicative: if `h_n : A_n ⟶ φ_* B_n` respects products of
  local sections, so does its transpose `φ^* A_n ⟶ B_n`.
* `AlgebraicGeometry.SheafOfModules.inverseImageGradedAlgebraIsoScalarRestrict`: the
  isomorphism `f⁻¹A ≅ B` of sheaves of graded `f⁻¹O`-algebras.

## References

* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace Topology AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.PullbackTensorCoherence

universe u

namespace Stacks.PullbackGradedAlgebra

open SheafOfModules.GradedAlgebra

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y))
  (hY : Presheaf.IsSheaf (Opens.grothendieckTopology Y.carrier)
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Y.sheaf.obj))

/-- For a morphism of ringed spaces `f`, the morphism-level multiplication of `f^*A` is the
pulled-back multiplication of `A`, conjugated by the comparison of [Stacks, Tag 01CD]. -/
theorem mulSheaf_pullbackGradedAlgebra_eq_comparison (i j : ℤ) :
    mulHom (pullbackGradedAlgebra f A hY) i j =
      inv (pullbackTensorComparison f (A.piece i) (A.piece j)) ≫
        (pullbackFunctor f).map (mulHom A i j) := by
  refine (mulSheaf_ofMorphismData (Osharp := X.sheaf) (structureSheafRing X).property
    (fun n ↦ (pullbackFunctor f).obj (A.piece n)) (pullbackMul f A) (pullbackOne f A)
    (pullbackMul_assoc f A hY) (pullbackOne_mul f A hY) (pullbackMul_one f A hY) i j).trans ?_
  exact congrArg (fun z => z ≫ (pullbackFunctor f).map (mulSheaf A i j))
    (Stacks.PullbackStrictTensorator.mu_pullbackStrictMonoidal_eq f (A.piece i) (A.piece j))

variable (B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X))
  (h : ∀ n : ℤ, A.piece n ⟶ (pushforwardFunctor f).obj (B.piece n))

/-- Adjoint transposes of multiplicative maps into a direct image are multiplicative.  Let
`h_n : A_n ⟶ f_* B_n` be a family of morphisms respecting products of local sections, the
product on `f_* B` over `V` being that of `B` over `f⁻¹V`.  Then the adjoint transposes
`f^* A_n ⟶ B_n` respect the products of `f^*A` and of `B`. -/
theorem homEquiv_symm_map_mul
    (hmul : ∀ (i j : ℤ) (U : (Opens Y.carrier)ᵒᵖ) (x : (A.piece i).val.obj U)
      (y : (A.piece j).val.obj U),
      (h (i + j)).val.app U ((A.mul i j).app U x y) =
        (B.mul i j).app ((opensMap f).op.obj U) ((h i).val.app U x) ((h j).val.app U y))
    (i j : ℤ) (V : (Opens X.carrier)ᵒᵖ)
    (x : ((pullbackGradedAlgebra f A hY).piece i).val.obj V)
    (y : ((pullbackGradedAlgebra f A hY).piece j).val.obj V) :
    (((pullbackAdjunction f).homEquiv _ _).symm (h (i + j))).val.app V
        (((pullbackGradedAlgebra f A hY).mul i j).app V x y) =
      (B.mul i j).app V ((((pullbackAdjunction f).homEquiv _ _).symm (h i)).val.app V x)
        ((((pullbackAdjunction f).homEquiv _ _).symm (h j)).val.app V y) := by
  let θ : ∀ n : ℤ, (pullbackFunctor f).obj (A.piece n) ⟶ B.piece n :=
    fun n => ((pullbackAdjunction f).homEquiv _ _).symm (h n)
  have hθ (n : ℤ) (U : (Opens Y.carrier)ᵒᵖ) (z : (A.piece n).val.obj U) :
      (θ n).val.app ((opensMap f).op.obj U) (pullbackUnit f (A.piece n) U z) =
        (h n).val.app U z := by
    refine (homEquiv_val_app f (A.piece n) (B.piece n) (θ n) U z).symm.trans ?_
    change (((pullbackAdjunction f).homEquiv _ _)
      (((pullbackAdjunction f).homEquiv _ _).symm (h n))).val.app U z = _
    rw [Equiv.apply_symm_apply]
  have key : (pullbackFunctor f).map (mulHom A i j) ≫ θ (i + j) =
      pullbackTensorComparison f (A.piece i) (A.piece j) ≫ (θ i ⊗ₘ θ j) ≫ mulHom B i j := by
    refine pullback_tensor_hom_ext f fun U a b => ?_
    rw [SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
      SheafOfModules.comp_val_app_apply, pullbackTensorComparison_pullbackUnit,
      tensorHom_tmul, pullbackUnit_naturality, mulHom_tmul, hθ, hθ, hθ]
    exact (hmul i j U a b).trans (mulHom_tmul B i j _ _ _).symm
  set c := pullbackTensorComparison f (A.piece i) (A.piece j)
  set t := tmul X ((pullbackFunctor f).obj (A.piece i)) ((pullbackFunctor f).obj (A.piece j)) V x y
  have h1 : ((pullbackGradedAlgebra f A hY).mul i j).app V x y =
      (inv c ≫ (pullbackFunctor f).map (mulHom A i j)).val.app V t := by
    rw [← mulSheaf_pullbackGradedAlgebra_eq_comparison f A hY i j]
    exact (mulHom_tmul _ i j V x y).symm
  change (θ (i + j)).val.app V _ = (B.mul i j).app V ((θ i).val.app V x) ((θ j).val.app V y)
  rw [h1]
  refine (congrArg (fun φ => φ.val.app V ((inv c).val.app V t)) key).trans ?_
  change (mulHom B i j).val.app V ((θ i ⊗ₘ θ j).val.app V (c.val.app V ((inv c).val.app V t))) = _
  rw [val_app_inv_val_app]
  exact (congrArg ((mulHom B i j).val.app V)
    (tensorHom_tmul (θ i) (θ j) V x y)).trans (mulHom_tmul B i j V _ _)

end Stacks.PullbackGradedAlgebra

namespace AlgebraicGeometry.SheafOfModules

open _root_.SheafOfModules.GradedAlgebra

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (O : TopCat.Sheaf CommRingCat.{u} X)
  (A : _root_.SheafOfModules.GradedAlgebra.{u, u} (underlyingRingSheaf O))
  (hf : IsInducing (ConcreteCategory.hom f))
  {R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology Y) RingCat.{u}}
  (a : underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O) ⟶ R)
  (B : _root_.SheafOfModules.GradedAlgebra.{u, u} R)
  (e : ∀ n : ℤ, A.piece n ≅
    (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f O)).obj
      ((_root_.SheafOfModules.restrictScalars.{u} a).obj (B.piece n)))

/-- The degreewise comparison of
`AlgebraicGeometry.SheafOfModules.inverseImageGradedAlgebraPieceIsoRestrictScalars` is the
adjoint transpose of the given identification under `f⁻¹ ⊣ f_*`. -/
theorem inverseImageGradedAlgebraPieceIsoRestrictScalars_hom (n : ℤ) :
    (inverseImageGradedAlgebraPieceIsoRestrictScalars f O A hf a B.piece e n).hom =
      ((inverseImageAdjunction f O).homEquiv _ _).symm (e n).hom :=
  ((inverseImageAdjunction f O).homEquiv_counit _ _ (e n).hom).symm

/-- The degreewise comparison of `f⁻¹A` with `B` is multiplicative as soon as the given
identification of `A` with the direct image of `B` is. -/
theorem inverseImageGradedAlgebraPieceIsoRestrictScalars_map_mul
    (he : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (A.piece i).val.obj U)
      (y : (A.piece j).val.obj U),
      (e (i + j)).hom.val.app U ((A.mul i j).app U x y) =
        (B.mul i j).app ((Opens.map f).op.obj U) ((e i).hom.val.app U x)
          ((e j).hom.val.app U y))
    (i j : ℤ) (V : (Opens Y)ᵒᵖ)
    (x : ((inverseImageGradedAlgebra f O A).piece i).val.obj V)
    (y : ((inverseImageGradedAlgebra f O A).piece j).val.obj V) :
    (inverseImageGradedAlgebraPieceIsoRestrictScalars f O A hf a B.piece e (i + j)).hom.val.app V
        (((inverseImageGradedAlgebra f O A).mul i j).app V x y) =
      ((scalarRestrict a B).mul i j).app V
        ((inverseImageGradedAlgebraPieceIsoRestrictScalars f O A hf a B.piece e i).hom.val.app
          V x)
        ((inverseImageGradedAlgebraPieceIsoRestrictScalars f O A hf a B.piece e j).hom.val.app
          V y) := by
  simp only [inverseImageGradedAlgebraPieceIsoRestrictScalars_hom]
  exact Stacks.PullbackGradedAlgebra.homEquiv_symm_map_mul
    (AlgebraicGeometry.RingedSpace.inverseImageProjection (ringedSpaceOfSheaf O) f) A
    (underlyingRingSheaf O).property (scalarRestrict a B) (fun n => (e n).hom) he i j V x y

/-- For `f` inducing, the isomorphism of sheaves of graded `f⁻¹O`-algebras between `f⁻¹A` and
`B`, read over `f⁻¹O` by restriction of scalars along `a`, induced by an identification of the
homogeneous pieces of `A` with the direct images of those of `B` compatible with the
multiplications. -/
noncomputable def inverseImageGradedAlgebraIsoScalarRestrict
    (he : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (A.piece i).val.obj U)
      (y : (A.piece j).val.obj U),
      (e (i + j)).hom.val.app U ((A.mul i j).app U x y) =
        (B.mul i j).app ((Opens.map f).op.obj U) ((e i).hom.val.app U x)
          ((e j).hom.val.app U y)) :
    inverseImageGradedAlgebra f O A ≅ scalarRestrict a B :=
  isoOfPieceIso (fun n => inverseImageGradedAlgebraPieceIsoRestrictScalars f O A hf a B.piece e n)
    (inverseImageGradedAlgebraPieceIsoRestrictScalars_map_mul f O A hf a B e he)

/-- The component in degree `n` of `inverseImageGradedAlgebraIsoScalarRestrict` is the
isomorphism `inverseImageGradedAlgebraPieceIsoRestrictScalars` of homogeneous pieces. -/
@[simp] theorem inverseImageGradedAlgebraIsoScalarRestrict_hom_app
    (he : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (A.piece i).val.obj U)
      (y : (A.piece j).val.obj U),
      (e (i + j)).hom.val.app U ((A.mul i j).app U x y) =
        (B.mul i j).app ((Opens.map f).op.obj U) ((e i).hom.val.app U x)
          ((e j).hom.val.app U y)) (n : ℤ) :
    (inverseImageGradedAlgebraIsoScalarRestrict f O A hf a B e he).hom.app n =
      (inverseImageGradedAlgebraPieceIsoRestrictScalars f O A hf a B.piece e n).hom :=
  rfl

end AlgebraicGeometry.SheafOfModules

end
