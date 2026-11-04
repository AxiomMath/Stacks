module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPullbackTensorExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeDistinguished
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryTriangulated
public import StacksFrontier.CategoryTheory.Functor.Derived.LeftDerivedCounitCommShift
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTriangulated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The left derived extension of `M ↦ f^*M ⊗_A 𝒩` is an exact functor

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, let `φ : B ⟶ f_*A` be
a homomorphism of sheaves of differential graded algebras and let `𝒩` be a differential graded
`(A, A')`-bimodule. The functor `K(Mod(B, d)) ⥤ K(Mod(A', d))`, `M ↦ f^*M ⊗_A 𝒩`, is an exact
functor of triangulated categories (Tag 0FTE), so its left derived extension
`D(B, d) ⥤ D(A', d)` of Tag 0FTF commutes with the translations, and it is triangulated: every
morphism of `D(B, d)` is, up to isomorphism, the class of a homomorphism of good modules, the
cone of which is good (Tag 0FSC), and the comparison map of the derived functor is invertible at
the three vertices of the triangle of that homomorphism and its cone.

## Main results

* `SheafOfModules.DifferentialGradedModule.toposConeTriangle_distinguished`: the triangle
  `K ⟶ L ⟶ C(f) ⟶ K[1]` of a homomorphism is distinguished, over the site of a ringed topos.
* `SheafOfModules.DifferentialGradedModule.derivedToposPullbackTensor_commShift` and
  `derivedToposPullbackTensor_isTriangulated`: the functor of Tag 0FTF commutes with the
  translations and is an exact functor of triangulated categories.
* `SheafOfModules.DifferentialGradedModule.isLeftDerived_derivedPullbackTensorRingedTopos`:
  **Tag 0FTF**, with the exactness of the derived functor.

## References

* [Stacks Project, Tag 0FTF](https://stacks.math.columbia.edu/tag/0FTF)
* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Pretriangulated
open Stacks.Sheaves.RingedToposModules

universe u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
  AlgebraicGeometry.RingedTopos.hasSheafify_addCommGrpCat
  AlgebraicGeometry.RingedTopos.wEqualsLocallyBijective_addCommGrpCat

/-! ### The derived category over the site of a ringed topos -/

section Instances

variable {X : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))

/-- The quasi-isomorphisms of differential graded `A`-modules over the site of a ringed topos are
multiplicative. -/
instance toposQuasiIsomorphismsIsMultiplicative :
    (quasiIsomorphisms.{u, u, u} A).IsMultiplicative :=
  quasiIsomorphisms_isMultiplicative' (X := X.toRingedSite) A

/-- The quasi-isomorphisms of differential graded `A`-modules over the site of a ringed topos admit
a left calculus of fractions. -/
instance toposQuasiIsomorphismsHasLeftCalculusOfFractions :
    (quasiIsomorphisms.{u, u, u} A).HasLeftCalculusOfFractions :=
  quasiIsomorphisms_hasLeftCalculusOfFractions (X := X.toRingedSite) A

/-- The quasi-isomorphisms of differential graded `A`-modules over the site of a ringed topos admit
a right calculus of fractions. -/
instance toposQuasiIsomorphismsHasRightCalculusOfFractions :
    (quasiIsomorphisms.{u, u, u} A).HasRightCalculusOfFractions :=
  quasiIsomorphisms_hasRightCalculusOfFractions (X := X.toRingedSite) A

/-- The quasi-isomorphisms are compatible with the triangulation (Tag 0FT4), over the site of a
ringed topos; this puts the triangulated structure on `D(A, d)`. -/
instance toposQuasiIsomorphismsIsCompatibleWithTriangulation :
    (quasiIsomorphisms.{u, u, u} A).IsCompatibleWithTriangulation :=
  quasiIsomorphisms_isCompatibleWithTriangulation (X := X.toRingedSite) A

variable {A}

/-- The degree-one translation of `K(Mod(A, d))` is the shift of differential graded modules,
over the site of a ringed topos. -/
theorem toposShiftFunctor_obj (M : DifferentialGradedModule.{u, u, u} A) :
    (shiftFunctor (HomotopyCategory.{u, u, u} A) (1 : ℤ)).obj
        ((HomotopyCategory.quotient A).obj M) =
      (HomotopyCategory.quotient A).obj (shift M) :=
  HomotopyCategory.shiftFunctor_obj (X := X.toRingedSite) A M

/-- The triangle of the cone sequence is distinguished (Tag 09QU), over the site of a ringed
topos. -/
theorem toposConeRotatedTriangle_distinguished {K L : DifferentialGradedModule.{u, u, u} A}
    (f : K ⟶ L) :
    coneRotatedTriangle (X := X.toRingedSite) f ∈ distTriang (HomotopyCategory.{u, u, u} A) :=
  coneRotatedTriangle_distinguished (X := X.toRingedSite) f

/-- **The triangle `K ⟶ L ⟶ C(f) ⟶ K[1]` of a homomorphism**, in the homotopy category over the
site of a ringed topos. -/
def toposConeTriangle {K L : DifferentialGradedModule.{u, u, u} A} (f : K ⟶ L) :
    Triangle (HomotopyCategory.{u, u, u} A) :=
  Triangle.mk ((HomotopyCategory.quotient A).map f)
    ((HomotopyCategory.quotient A).map (conePackage f).inclusion)
    (-((HomotopyCategory.quotient A).map (conePackage f).projection ≫
      eqToHom (toposShiftFunctor_obj K).symm))

/-- **The triangle of a homomorphism and its cone is distinguished**: its rotation is the
triangle of the cone sequence (Tag 09QU), up to the sign of the third vertex. -/
theorem toposConeTriangle_distinguished {K L : DifferentialGradedModule.{u, u, u} A}
    (f : K ⟶ L) :
    toposConeTriangle f ∈ distTriang (HomotopyCategory.{u, u, u} A) := by
  rw [rotate_distinguished_triangle]
  let E : ((HomotopyCategory.quotient A).obj K)⟦(1 : ℤ)⟧ ≅
      (HomotopyCategory.quotient A).obj (shift K) :=
    eqToIso (toposShiftFunctor_obj K)
  let E' : ((HomotopyCategory.quotient A).obj K)⟦(1 : ℤ)⟧ ≅
      (HomotopyCategory.quotient A).obj (shift K) :=
    { hom := -E.hom
      inv := -E.inv
      hom_inv_id := by simp
      inv_hom_id := by simp }
  refine isomorphic_distinguished _
    (toposConeRotatedTriangle_distinguished f) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) E' ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · dsimp [Triangle.rotate, toposConeTriangle, coneRotatedTriangle, E', E]
    refine (Preadditive.neg_comp_neg _ _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (eqToHom_trans _ _)).trans ?_
    exact (congrArg (_ ≫ ·) (eqToHom_refl _ _)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  · dsimp [Triangle.rotate, toposConeTriangle, coneRotatedTriangle, E', E]
    refine ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans
      (Category.comp_id _)).trans ?_
    refine Eq.trans ?_ (Preadditive.neg_comp _ _).symm
    refine congrArg Neg.neg ?_
    exact (((Category.id_comp _).symm.trans (congrArg (· ≫ _) (eqToHom_refl _ _).symm)).trans
      (congrArg (· ≫ _) (eqToHom_trans _ _).symm)).trans (Category.assoc _ _ _)

end Instances

/-! ### The functor of Tag 0FTF is exact -/

section Exact

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  (f : RingedToposHom X Y)
  {A A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  (φ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A) (hφ : φ.IsUnital)
  (N : DifferentialGradedBimodule.{u, u, u} A A')

/-- **The functor of Tag 0FTF commutes with the translations**: it is the left derived functor
of a functor which does. -/
@[instance_reducible]
instance derivedToposPullbackTensor_commShift :
    (derivedToposPullbackTensor f φ hφ N).CommShift ℤ :=
  StacksDraft.PseudoCoherence.leftDerivedCommShift (derivedToposPullbackTensor f φ hφ N)
    (derivedToposPullbackTensorCounit f φ hφ N) (quasiIsomorphisms.{u, u, u} B) ℤ

/-- The comparison map of the functor of Tag 0FTF commutes with the translations. -/
instance derivedToposPullbackTensorCounit_commShift :
    NatTrans.CommShift (derivedToposPullbackTensorCounit f φ hφ N) ℤ :=
  Functor.IsLeftDerivedFunctor.natTrans_commShift (derivedToposPullbackTensor f φ hφ N)
    (derivedToposPullbackTensorCounit f φ hφ N) (quasiIsomorphisms.{u, u, u} B) ℤ

/-- **The functor of Tag 0FTF is an exact functor of triangulated categories.** Every morphism of
`D(B, d)` is, up to isomorphism, the class of a homomorphism `g` of good modules; the comparison
map is invertible at its source, its target and its cone, which is good by Tag 0FSC, and the
triangle of `g` and its cone is distinguished. -/
instance derivedToposPullbackTensor_isTriangulated :
    (derivedToposPullbackTensor f φ hφ N).IsTriangulated := by
  let W := quasiIsomorphisms.{u, u, u} B
  let P : ObjectProperty (HomotopyCategory.{u, u, u} B) := IsGoodObj
  have : (LeftDerivedByResolutions.inclusionLocalizerMorphism W P).HasLeftResolutions :=
    fun M => by
      obtain ⟨K, s, hs, hK⟩ := exists_quasiIso_isGoodObj B M
      exact ⟨{ X₁ := ⟨K, hK⟩, w := s, hw := hs }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism W P
  have := LeftDerivedByResolutions.hasRightCalculusOfFractions_inverseImage_ι W P
  have : (P.ι ⋙ toDerivedCategory.{u, u, u} B).IsLocalization (W.inverseImage P.ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      (LeftDerivedByResolutions.inclusionLocalizerMorphism W P) (toDerivedCategory.{u, u, u} B)
  have := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    (P.ι ⋙ toDerivedCategory.{u, u, u} B) (W.inverseImage P.ι)
  refine Functor.isTriangulated_of_rightExtension (derivedToposPullbackTensor f φ hφ N)
    (derivedToposPullbackTensorCounit f φ hφ N) (fun Z Z' g => ?_)
  obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage
    (F := (P.ι ⋙ toDerivedCategory.{u, u, u} B).mapArrow) (Arrow.mk g)
  obtain ⟨f₀, hf₀⟩ := (HomotopyCategory.quotient B).map_surjective (P.ι.map a.hom)
  refine ⟨toposConeTriangle f₀, toposConeTriangle_distinguished f₀,
    isIso_derivedToposPullbackTensorCounit_app f φ hφ N a.left.property,
    isIso_derivedToposPullbackTensorCounit_app f φ hφ N a.right.property,
    isIso_derivedToposPullbackTensorCounit_app f φ hφ N
      (cone_isGoodToposBaseChange.{u, u, u, u, u} f₀ a.left.property a.right.property), ⟨?_⟩⟩
  exact eqToIso (congrArg (fun m => Arrow.mk ((toDerivedCategory.{u, u, u} B).map m)) hf₀) ≪≫ ea

end Exact

/-! ### Tag 0FTF -/

section Tags

attribute [local instance] AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
  {A A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  (φ : B ⟶ toposPushforwardAlgebra (Osharp := X.O) (Psharp := Y.O)
    (toposDirectImageModules (X := X) (Y := Y) f) A) (hφ : φ.IsUnital)
  (N : DifferentialGradedBimodule.{u, u, u} A A')

/-- The functor of Tag 0FTF commutes with the translations. -/
@[instance_reducible]
instance derivedPullbackTensorRingedTopos_commShift :
    (derivedPullbackTensorRingedTopos f φ hφ N).CommShift ℤ :=
  derivedToposPullbackTensor_commShift f φ hφ N

/-- The functor of Tag 0FTF is an exact functor of triangulated categories. -/
instance derivedPullbackTensorRingedTopos_isTriangulated :
    (derivedPullbackTensorRingedTopos f φ hφ N).IsTriangulated :=
  derivedToposPullbackTensor_isTriangulated f φ hφ N

/-- **Stacks Project, Tag 0FTF.** Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of
ringed topoi, let `A` and `A'` be sheaves of differential graded `O_C`-algebras, let `B` be a sheaf
of differential graded `O_D`-algebras, let `φ : B ⟶ f_*A` be a homomorphism of sheaves of
differential graded algebras and let `𝒩` be a differential graded `(A, A')`-bimodule. The exact
functor `K(Mod(B, d)) ⟶ K(Mod(A', d))`, `M ↦ f^*M ⊗_A 𝒩` of Tag 0FTE (where `f^*M = f^*M ⊗_{f^*B} A`
is the pullback along `(f, A, φ)`), composed with the localization functor
`K(Mod(A', d)) → D(A', d)`, has a left derived extension `D(B, d) → D(A', d)` whose value on a good
right differential graded `B`-module `P` is `f^*P ⊗_A 𝒩`: `derivedPullbackTensorRingedTopos`, with
its comparison map, is the left derived functor, the comparison map is invertible at every good
module (so that the value there is `derivedPullbackTensorRingedToposObjIso`), and the extension is
an exact functor of triangulated categories. -/
@[stacks 0FTF, sga "4 XVII 4.2.12" "more general"]
theorem isLeftDerived_derivedPullbackTensorRingedTopos :
    (derivedPullbackTensorRingedTopos f φ hφ N).IsLeftDerivedFunctor
        (derivedPullbackTensorRingedToposCounit f φ hφ N) (quasiIsomorphisms.{u, u, u} B) ∧
      (∀ P : DifferentialGradedModule.{u, u, u} B, IsGoodToposBaseChange.{u, u, u} P →
        IsIso ((derivedPullbackTensorRingedToposCounit f φ hφ N).app
          ((HomotopyCategory.quotient B).obj P))) ∧
      ∃ (_ : (derivedPullbackTensorRingedTopos f φ hφ N).CommShift ℤ),
        (derivedPullbackTensorRingedTopos f φ hφ N).IsTriangulated :=
  ⟨inferInstance, fun _ hP => isIso_derivedToposPullbackTensorCounit_app f φ hφ N hP,
    inferInstance, inferInstance⟩

/-- The derived pullback `Lf^*` of Tag 0FTG (2) commutes with the translations. -/
@[instance_reducible]
instance derivedPullbackRingedTopos_commShift :
    (derivedPullbackRingedTopos f φ hφ).CommShift ℤ :=
  derivedPullbackTensorRingedTopos_commShift f φ hφ A.diagonalBimodule

/-- The derived pullback `Lf^*` of Tag 0FTG (2) is an exact functor of triangulated categories. -/
instance derivedPullbackRingedTopos_isTriangulated :
    (derivedPullbackRingedTopos f φ hφ).IsTriangulated :=
  derivedPullbackTensorRingedTopos_isTriangulated f φ hφ A.diagonalBimodule

end Tags

end SheafOfModules.DifferentialGradedModule

end
