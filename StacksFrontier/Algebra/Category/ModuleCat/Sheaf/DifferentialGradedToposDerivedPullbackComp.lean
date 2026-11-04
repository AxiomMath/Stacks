module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPullbackAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedTensorProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullbackTensorFactorization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorHomFunctorAdjunction

/-!
# Derived pullback followed by the derived tensor product, and along a composite

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, `𝒜` and `𝒜'` sheaves of
differential graded `O_C`-algebras, `ℬ` a sheaf of differential graded `O_D`-algebras,
`φ : ℬ ⟶ f_*𝒜` a homomorphism of differential graded algebras and `𝒩` a differential graded
`(𝒜, 𝒜')`-bimodule. This file proves the two compatibilities of
[Stacks, Section 0FT9](https://stacks.math.columbia.edu/tag/0FT9) that follow the definition of
derived pullback and derived tensor product:

* **Tag 0FTH**: the functor `D(ℬ, d) ⥤ D(𝒜', d)` of Tag 0FTF is `ℳ ↦ Lf^*ℳ ⊗^𝐋_𝒜 𝒩`;
* **Tag 0FTI**: for composable morphisms of ringed topoi, `L(g ∘ f)^* = Lf^* ∘ Lg^*`.

Both are proved as in the source, by computing on good modules: a good module `𝒫` (Tag 0FSA)
resolves every object (Tag 0FSH), the comparison map of `Lf^*` is invertible at `𝒫`, and `f^*𝒫`
is again good (Tag 0FSI (2)) — in particular flat and K-flat, where the derived tensor product is
the tensor product. A composite of two left derived functors whose comparison maps are invertible
on a resolving class and on its image is a left derived functor of the composite
(`CategoryTheory.Functor.isLeftDerivedFunctor_comp_of_isIso`), and a left derived functor is
unique up to a unique isomorphism compatible with the comparison maps.

## Main definitions

* `CategoryTheory.Functor.leftDerivedCompCounit`: the comparison map of a composite of two left
  derived functors.
* `SheafOfModules.DifferentialGradedModule.derivedToposPullbackComposeTensor`:
  `Lf^* ⋙ - ⊗^𝐋_𝒜 𝒩`, with its comparison map `derivedToposPullbackComposeTensorCounit`.
* `SheafOfModules.DifferentialGradedModule.derivedToposPullbackCompIso`:
  `L(g ∘ f)^* ≅ Lg^* ⋙ Lf^*`, and `derivedPullbackRingedToposCompIso` the same for the derived
  pullbacks `derivedPullbackRingedTopos`, on which **Tag 0FTI** is registered.

## Main results

* `CategoryTheory.Functor.isLeftDerivedFunctor_comp_of_isIso`: the composite of two left derived
  functors computed by resolutions is a left derived functor of the composite.
* `isLeftDerivedFunctor_derivedToposPullbackComposeTensorCounit`: `Lf^* ⋙ - ⊗^𝐋_𝒜 𝒩` is a left
  derived functor of `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`.
* `exists_iso_derivedToposPullback_comp_derivedTensorProduct`: every left derived functor of
  `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` is `Lf^* ⋙ - ⊗^𝐋_𝒜 𝒩`, and
  `exists_iso_derivedPullbackTensorRingedTopos_derivedPullbackRingedTopos_comp` the same for the
  functors of Tag 0FTF with the derived tensor product `derivedTensorProduct` of the ringed site.
* `exists_iso_derivedPullbackTensorRingedTopos_derivedPullbackRingedTopos_comp_topos`:
  **Tag 0FTH**: the functor `derivedPullbackTensorRingedTopos` of Tag 0FTF is
  `derivedPullbackRingedTopos` (Tag 0FTG (2)) followed by `derivedTensorProductTopos`
  (Tag 0FTG (1)).
* `SheafOfModules.DifferentialGradedModule.derivedPullbackRingedToposIso`: the tagged `Lf^*`, the
  functor of Tag 0FTF at the diagonal bimodule, is the direct `derivedToposPullback`.
* `SheafOfModules.TensorFunctorData.uniqueNatIso`: two tensor product functors with the same
  bimodule are naturally isomorphic.
* `SheafOfModules.DifferentialGradedModule.derivedToposPullbackCompIso_hom_fac`: the comparison of
  Tag 0FTI is compatible with the comparison maps.

## Implementation notes

The sites, morphisms and coefficients live in one universe `u`, the setting of
`DifferentialGradedToposDerivedPullback.lean`. The two tags are registered in the section `Tags`,
where the compatibility of sheaves with the forgetful functor from commutative rings to rings is a
local instance rather than a binder, as for Tags 0FTG (2) and 0FTF. The derived pullback along
`g ∘ f` is taken along the composite morphism of ringed topoi
`Stacks.Sheaves.RingedToposModules.RingedToposHom.comp` and the composite homomorphism
`𝒜'' ⟶ g_*𝒜' ⟶ g_*f_*𝒜 = (g ∘ f)_*𝒜` (`SheafOfModules.DifferentialGradedModule.toposCompHom`),
which is how the source composes the data `(f, φ)` and `(g, φ')`.

## References

* [Stacks Project, Tag 0FTH](https://stacks.math.columbia.edu/tag/0FTH)
* [Stacks Project, Tag 0FTI](https://stacks.math.columbia.edu/tag/0FTI)
* [Stacks Project, Tag 0FTF](https://stacks.math.columbia.edu/tag/0FTF)
* [Stacks Project, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] {D₁ : Type u₄} [Category.{v₄} D₁]
  {D₂ : Type u₅} [Category.{v₅} D₂] {D₃ : Type u₆} [Category.{v₆} D₃]
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {LF : D₁ ⥤ D₂} {LG : D₂ ⥤ D₃}

/-- The comparison map `L₁ ⋙ LF ⋙ LG ⟶ F ⋙ G ⋙ L₃` of a composite of two left derived functors:
`LG` of the comparison of `F`, followed by the comparison of `G` at the image of `F`. -/
def leftDerivedCompCounit (αF : L₁ ⋙ LF ⟶ F ⋙ L₂) (αG : L₂ ⋙ LG ⟶ G ⋙ L₃) :
    L₁ ⋙ LF ⋙ LG ⟶ (F ⋙ G) ⋙ L₃ :=
  (Functor.associator L₁ LF LG).inv ≫ Functor.whiskerRight αF LG ≫
    (Functor.associator F L₂ LG).hom ≫ Functor.whiskerLeft F αG ≫
      (Functor.associator F G L₃).inv

/-- The component of `leftDerivedCompCounit αF αG` at `X` is
`LG.map (αF.app X) ≫ αG.app (F.obj X)`. -/
@[simp]
theorem leftDerivedCompCounit_app (αF : L₁ ⋙ LF ⟶ F ⋙ L₂) (αG : L₂ ⋙ LG ⟶ G ⋙ L₃) (X : C₁) :
    (leftDerivedCompCounit αF αG).app X = LG.map (αF.app X) ≫ αG.app (F.obj X) := by
  simp [leftDerivedCompCounit]

/-- **The composite of two left derived functors.** If every object of `C₁` is the target of a
morphism of `W₁` out of a resolving object, and at every resolving object `P` the comparison map
of `F` at `P` and that of `G` at `F(P)` are invertible, then `LF ⋙ LG` with
`leftDerivedCompCounit` is a left derived functor of `F ⋙ G ⋙ L₃`. -/
theorem isLeftDerivedFunctor_comp_of_isIso (W₁ : MorphismProperty C₁)
    [W₁.HasRightCalculusOfFractions] [L₁.IsLocalization W₁]
    (αF : L₁ ⋙ LF ⟶ F ⋙ L₂) (αG : L₂ ⋙ LG ⟶ G ⋙ L₃) (P : ObjectProperty C₁)
    (hP : ∀ X : C₁, ∃ (Y : C₁) (_ : P Y) (s : Y ⟶ X), W₁ s)
    (hF : ∀ X : C₁, P X → IsIso (αF.app X)) (hG : ∀ X : C₁, P X → IsIso (αG.app (F.obj X))) :
    (LF ⋙ LG).IsLeftDerivedFunctor (leftDerivedCompCounit αF αG) W₁ := by
  have hα : ∀ X : C₁, P X → IsIso ((leftDerivedCompCounit αF αG).app X) := fun X hX => by
    have := hF X hX
    have := hG X hX
    rw [leftDerivedCompCounit_app]
    infer_instance
  refine LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions W₁ P hP _
    (fun {X Y} s hs hX hY => ?_) L₁ _ _ hα
  have := hα X hX
  have := hα Y hY
  have : IsIso (L₁.map s) := Localization.inverts L₁ W₁ s hs
  have : IsIso ((L₁ ⋙ LF ⋙ LG).map s) :=
    inferInstanceAs (IsIso ((LF ⋙ LG).map (L₁.map s)))
  have e := (leftDerivedCompCounit αF αG).naturality s
  have : IsIso ((leftDerivedCompCounit αF αG).app X ≫ ((F ⋙ G) ⋙ L₃).map s) := by
    rw [← e]; infer_instance
  exact IsIso.of_isIso_comp_left ((leftDerivedCompCounit αF αG).app X) _

end CategoryTheory.Functor

namespace SheafOfModules

universe t a w z s v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R} {N : DifferentialGradedBimodule.{t, a, z} A B}

/-- **Two tensor product functors with the same bimodule are isomorphic**, by the canonical
isomorphism `x ⊗ y ↦ x ⊗ y` (`TensorFunctorData.uniqueIso`), which is natural. -/
noncomputable def TensorFunctorData.uniqueNatIso (D D' : TensorFunctorData.{t, a, w, z, s} A B N) :
    D.functor ≅ D'.functor :=
  NatIso.ofComponents (fun M => D.uniqueIso D' M) fun {M M'} g =>
    (D.isTensorProduct M).hom_ext_tmul fun i j U x y => by
      have e1 := D.map_spec g i j (Opposite.op U) x y
      have e2 := D'.map_spec g i j (Opposite.op U) x y
      have e3 := (D.isTensorProduct M').descend_tmul (D'.isTensorProduct M') U i j (i + j)
        (add_zero (i + j)) (Over.mk (𝟙 U)) ((g.toHomologicalComplex.f i).val.app
          (Opposite.op U) x) y
      have e4 := (D.isTensorProduct M).descend_tmul (D'.isTensorProduct M) U i j (i + j)
        (add_zero (i + j)) (Over.mk (𝟙 U)) x y
      simp only [castHom_self] at e3 e4
      change ((D.uniqueIso D' M').hom.toHomologicalComplex.f (i + j)).val.app (Opposite.op U)
          (((D.functor.map g).toHomologicalComplex.f (i + j)).val.app (Opposite.op U)
            ((D.isTensorProduct M).tmul i j (Opposite.op U) x y)) =
        ((D'.functor.map g).toHomologicalComplex.f (i + j)).val.app (Opposite.op U)
          (((D.uniqueIso D' M).hom.toHomologicalComplex.f (i + j)).val.app (Opposite.op U)
            ((D.isTensorProduct M).tmul i j (Opposite.op U) x y))
      rw [e1]
      exact e3.trans (e2.symm.trans (congrArg _ e4.symm))

end SheafOfModules

universe u

namespace SheafOfModules.DifferentialGradedModule

open Stacks.Sheaves.RingedToposModules

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
  quasiIsomorphisms_hasRightCalculusOfFractions_topos

section Composite

variable {X Y Z : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [Z.J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  [Z.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
  {A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {A' : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  {A'' : DifferentialGradedAlgebra.{u, u} (toRingCat Z.J Z.O)}
  {φ : A' ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A} (hφ : φ.IsUnital)
  {φ' : A'' ⟶ toposPushforwardAlgebra (toposDirectImageModules g) A'} (hφ' : φ'.IsUnital)

/-- The pullback along a base change carries good modules to good modules. -/
theorem isGoodToposBaseChange_toposDGPullback_obj
    {P : DifferentialGradedModule.{u, u, u} A'} (hP : IsGoodToposBaseChange.{u, u, u} P) :
    IsGoodToposBaseChange.{u, u, u} ((toposDGPullback f φ hφ).obj P) :=
  isGoodToposBaseChange_of_toposCorepresentableBy f φ hφ hP
    (toposDGPullbackCorepresentableBy f φ hφ P)

/-- **The pullback along `g ∘ f` on homotopy categories** is the pullback along `g` followed by
the pullback along `f`. -/
def homotopyToposDGPullbackCompIso :
    homotopyToposDGPullback (RingedToposHom.comp g f) (toposCompHom f g A φ φ')
        (isUnital_toposCompHom f g A hφ hφ') ≅
      homotopyToposDGPullback g φ' hφ' ⋙ homotopyToposDGPullback f φ hφ :=
  HomotopyCategory.descendNatIso _
      (PreservesHomotopic.comp (preservesHomotopic_toposDGPullback g φ' hφ')
        (preservesHomotopic_toposDGPullback f φ hφ))
      (toposBaseChangeFunctorCompIso f g A hφ hφ') ≪≫
    eqToIso (HomotopyCategory.descend_comp _ _ _ _)

/-- The composite `Lg^* ⋙ Lf^*`, with the composite comparison map, is a left derived functor of
the pullback along `g` followed by the pullback along `f`: at a good module `P` the comparison
of `Lg^*` is invertible, and `g^*P` is good (Tag 0FSI (2)), so the comparison of `Lf^*` at it
is invertible. -/
theorem isLeftDerivedFunctor_derivedToposPullback_comp :
    (derivedToposPullback g φ' hφ' ⋙ derivedToposPullback f φ hφ).IsLeftDerivedFunctor
      (Functor.leftDerivedCompCounit (derivedToposPullbackCounit g φ' hφ')
        (derivedToposPullbackCounit f φ hφ)) (quasiIsomorphisms.{u, u, u} A'') :=
  Functor.isLeftDerivedFunctor_comp_of_isIso (quasiIsomorphisms.{u, u, u} A'') _ _ IsGoodObj
    (exists_isGoodObj_quasiIso (B := A''))
    (fun P hP => isIso_derivedToposPullbackCounit_app g φ' hφ' (P := P.as) hP)
    (fun P hP => isIso_derivedToposPullbackCounit_app f φ hφ
      (P := (toposDGPullback g φ' hφ').obj P.as)
      (isGoodToposBaseChange_toposDGPullback_obj g hφ' hP))

/-- **Tag 0FTI.** For composable morphisms of ringed topoi `f : X ⟶ Y`, `g : Y ⟶ Z` and
homomorphisms `φ : 𝒜' ⟶ f_*𝒜`, `φ' : 𝒜'' ⟶ g_*𝒜'` of differential graded algebras,
`L(g ∘ f)^* ≅ Lf^* ∘ Lg^* : D(𝒜'', d) ⥤ D(𝒜, d)`, the derived pullback along `g ∘ f` being taken
along the composite homomorphism `𝒜'' ⟶ g_*𝒜' ⟶ g_*f_*𝒜 = (g ∘ f)_*𝒜`. Both are left derived
functors of the pullback along `g ∘ f`, which is the pullback along `g` followed by that along
`f`. -/
def derivedToposPullbackCompIso :
    derivedToposPullback (RingedToposHom.comp g f) (toposCompHom f g A φ φ')
        (isUnital_toposCompHom f g A hφ hφ') ≅
      derivedToposPullback g φ' hφ' ⋙ derivedToposPullback f φ hφ :=
  have := isLeftDerivedFunctor_derivedToposPullback_comp f g hφ hφ'
  Functor.leftDerivedNatIso _ _ (derivedToposPullbackCounit _ _ _)
    (Functor.leftDerivedCompCounit (derivedToposPullbackCounit g φ' hφ')
      (derivedToposPullbackCounit f φ hφ)) (quasiIsomorphisms.{u, u, u} A'')
    (Functor.isoWhiskerRight (homotopyToposDGPullbackCompIso f g hφ hφ') (toDerivedCategory A))

/-- The comparison of derived pullbacks along a composite is compatible with the comparison maps:
it is the unique isomorphism carrying the comparison map of `L(g ∘ f)^*` to that of
`Lg^* ⋙ Lf^*`, read through the comparison of the pullbacks on homotopy categories. -/
theorem derivedToposPullbackCompIso_hom_fac :
    Functor.whiskerLeft (toDerivedCategory A'') (derivedToposPullbackCompIso f g hφ hφ').hom ≫
        Functor.leftDerivedCompCounit (derivedToposPullbackCounit g φ' hφ')
          (derivedToposPullbackCounit f φ hφ) =
      derivedToposPullbackCounit _ _ _ ≫
        Functor.whiskerRight (homotopyToposDGPullbackCompIso f g hφ hφ').hom
          (toDerivedCategory A) := by
  have := isLeftDerivedFunctor_derivedToposPullback_comp f g hφ hφ'
  exact Functor.leftDerivedNatTrans_fac _ _ _ _ (quasiIsomorphisms.{u, u, u} A'') _

end Composite

section Tensor

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  (f : RingedToposHom X Y) {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  {A A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  (φ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A) (hφ : φ.IsUnital)
  (N : DifferentialGradedBimodule.{u, u, u} A A')

/-- On homotopy categories, `M ↦ f^*M ⊗_A 𝒩` is the pullback followed by the tensor product
with `𝒩`. -/
theorem homotopyToposDGPullback_comp_pullbackTensor :
    homotopyToposDGPullback f φ hφ ⋙
        HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension
          (tensorData (X := X.toRingedSite) N) =
      homotopyToposPullbackTensor f φ hφ N := by
  refine HomotopyCategory.eq_descend _ _ _ ?_
  rw [← Functor.assoc, homotopyToposDGPullback, HomotopyCategory.quotient_comp_descend,
    Functor.assoc, HomotopyCategory.quotient_comp_pullbackTensor, ← Functor.assoc,
    pullbackTensorFunctor, idPullbackData_functor_eq]
  rfl

/-- **The functor `ℳ ↦ Lf^*ℳ ⊗^𝐋_𝒜 𝒩`** `D(ℬ, d) ⥤ D(𝒜', d)`: the derived pullback followed by
the derived tensor product with `𝒩`. -/
def derivedToposPullbackComposeTensor :
    derivedCategory.{u, u, u} B ⥤ derivedCategory.{u, u, u} A' :=
  derivedToposPullback f φ hφ ⋙ derivedTensorProduct (X := X.toRingedSite) N

/-- `derivedToposPullbackComposeTensor` is the derived pullback followed by the derived tensor
product. -/
theorem derivedToposPullbackComposeTensor_eq :
    derivedToposPullbackComposeTensor f φ hφ N =
      derivedToposPullback f φ hφ ⋙ derivedTensorProduct (X := X.toRingedSite) N :=
  rfl

/-- The comparison map `Lf^*M ⊗^𝐋_A 𝒩 ⟶ f^*M ⊗_A 𝒩` of the composite of the derived pullback and
the derived tensor product: `- ⊗^𝐋_A 𝒩` of the comparison map of `Lf^*`, followed by the
comparison map of `- ⊗^𝐋_A 𝒩`. -/
def derivedToposPullbackComposeTensorCounit :
    toDerivedCategory B ⋙ derivedToposPullbackComposeTensor f φ hφ N ⟶
      homotopyToposPullbackTensor f φ hφ N ⋙ toDerivedCategory A' :=
  Functor.leftDerivedCompCounit (F := homotopyToposDGPullback f φ hφ)
      (G := HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension
        (tensorData (X := X.toRingedSite) N))
      (derivedToposPullbackCounit f φ hφ) (derivedTensorProductCounit (X := X.toRingedSite) N) ≫
    Functor.whiskerRight (eqToHom (homotopyToposDGPullback_comp_pullbackTensor f φ hφ N))
      (toDerivedCategory A')

/-- `Lf^* ⋙ - ⊗^𝐋_A 𝒩`, with its comparison map, is a left derived functor of
`M ↦ f^*M ⊗_A 𝒩` followed by the localization: at a good module `P` the comparison of `Lf^*`
is invertible, and `f^*P` is flat and K-flat (condition (3) of Tag 0FSA), where the comparison
of the derived tensor product is invertible. -/
instance isLeftDerivedFunctor_derivedToposPullbackComposeTensorCounit :
    (derivedToposPullbackComposeTensor f φ hφ N).IsLeftDerivedFunctor
      (derivedToposPullbackComposeTensorCounit f φ hφ N) (quasiIsomorphisms.{u, u, u} B) := by
  have h := Functor.isLeftDerivedFunctor_comp_of_isIso (quasiIsomorphisms.{u, u, u} B)
    (F := homotopyToposDGPullback f φ hφ)
    (G := HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension
      (tensorData (X := X.toRingedSite) N))
    (derivedToposPullbackCounit f φ hφ) (derivedTensorProductCounit (X := X.toRingedSite) N)
    IsGoodObj (exists_isGoodObj_quasiIso (B := B))
    (fun P hP => isIso_derivedToposPullbackCounit_app f φ hφ (P := P.as) hP)
    (fun P hP => isIso_derivedTensorProductCounit_app (X := X.toRingedSite) N
      (P := (toposDGPullback f φ hφ).obj P.as)
      (isGradedFlat_and_isKFlat_toposDGPullback_obj f φ hφ hP))
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension] at h ⊢
  exact (Functor.isRightKanExtension_iff_of_iso₂ _ _
    (Functor.isoWhiskerRight (eqToIso (homotopyToposDGPullback_comp_pullbackTensor f φ hφ N))
      (toDerivedCategory A')) (Iso.refl _)
    (Category.id_comp _)).1 h

/-- **Tag 0FTH.** In the situation of Tag 0FTF — a morphism of ringed topoi `f`, a unital
homomorphism `φ : ℬ ⟶ f_*𝒜` of differential graded algebras and a differential graded
`(𝒜, 𝒜')`-bimodule `𝒩` — the functor `D(ℬ, d) ⥤ D(𝒜', d)` of Tag 0FTF is
`ℳ ↦ Lf^*ℳ ⊗^𝐋_𝒜 𝒩`. Precisely: any left derived functor `Λ` of `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` followed by
the localization, with comparison map `β`, is isomorphic to `Lf^* ⋙ - ⊗^𝐋_𝒜 𝒩` by an
isomorphism carrying `β` to the composite comparison map. Both functors are computed on good
modules: `Lf^*` sends a good `𝒫` to `f^*𝒫`, which is flat and K-flat over `𝒜`, where the
derived tensor product is the tensor product. -/
theorem exists_iso_derivedToposPullback_comp_derivedTensorProduct
    (Λ : derivedCategory.{u, u, u} B ⥤ derivedCategory.{u, u, u} A')
    (β : toDerivedCategory B ⋙ Λ ⟶ homotopyToposPullbackTensor f φ hφ N ⋙ toDerivedCategory A')
    [Λ.IsLeftDerivedFunctor β (quasiIsomorphisms.{u, u, u} B)] :
    ∃ e : Λ ≅ derivedToposPullbackComposeTensor f φ hφ N,
      Functor.whiskerLeft (toDerivedCategory B) e.hom ≫
          derivedToposPullbackComposeTensorCounit f φ hφ N =
        β :=
  ⟨Functor.leftDerivedNatIso Λ (derivedToposPullbackComposeTensor f φ hφ N) β
      (derivedToposPullbackComposeTensorCounit f φ hφ N) (quasiIsomorphisms.{u, u, u} B)
      (Iso.refl _),
    (Functor.leftDerivedNatTrans_fac Λ (derivedToposPullbackComposeTensor f φ hφ N) β
      (derivedToposPullbackComposeTensorCounit f φ hφ N) (quasiIsomorphisms.{u, u, u} B) _).trans
      (Category.comp_id β)⟩

/-- **Tag 0FTH at the functor constructed in Tag 0FTF**: the left derived extension
`goodLeftDerived` of `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` is `ℳ ↦ Lf^*ℳ ⊗^𝐋_𝒜 𝒩`. -/
def goodLeftDerivedToposPullbackTensorIso :
    goodLeftDerived (toposPullbackTensor f φ hφ N) (preservesHomotopic_toposPullbackTensor f φ hφ N)
        (quasiIso_toposPullbackTensor_map_of_isGood f φ hφ N) ≅
      derivedToposPullbackComposeTensor f φ hφ N :=
  have := isLeftDerivedFunctor_goodLeftDerived (toposPullbackTensor f φ hφ N)
    (preservesHomotopic_toposPullbackTensor f φ hφ N)
    (quasiIso_toposPullbackTensor_map_of_isGood f φ hφ N)
  Functor.leftDerivedNatIso _ _ (goodLeftDerivedCounit _ _ _)
    (derivedToposPullbackComposeTensorCounit f φ hφ N) (quasiIsomorphisms.{u, u, u} B) (Iso.refl _)

end Tensor

/-! ### The tags, at morphisms of ringed topoi in one universe -/

section Tags

attribute [local instance] AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat

section PullbackTensor

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
  {A A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  (φ : B ⟶ toposPushforwardAlgebra (Osharp := X.O) (Psharp := Y.O)
    (toposDirectImageModules (X := X) (Y := Y) f) A) (hφ : φ.IsUnital)
  (N : DifferentialGradedBimodule.{u, u, u} A A')

/-- On differential graded modules, `M ↦ f^*M ⊗_A {}_A A_A` is the pullback
`M ↦ f^*M ⊗_{f^*B} A`: the tensor product with the diagonal bimodule is the identity. -/
def toposPullbackTensorDiagonalNatIso :
    toposPullbackTensor f φ hφ A.diagonalBimodule ≅ toposDGPullback f φ hφ :=
  Functor.isoWhiskerLeft (toposDGPullback f φ hφ)
      (TensorFunctorData.uniqueNatIso (toposPullbackTensorData A.diagonalBimodule)
        (tensorFunctorDataDiagonal.{u, u, u} A)) ≪≫
    Functor.rightUnitor _

/-- The same on homotopy categories. -/
def homotopyToposPullbackTensorDiagonalIso :
    homotopyToposPullbackTensor f φ hφ A.diagonalBimodule ≅ homotopyToposDGPullback f φ hφ :=
  HomotopyCategory.descendNatIso (preservesHomotopic_toposPullbackTensor f φ hφ _)
    (preservesHomotopic_toposDGPullback f φ hφ) (toposPullbackTensorDiagonalNatIso f φ hφ)

/-- **The derived pullback `Lf^*` of Tag 0FTG (2) is the left derived functor of
`M ↦ f^*M ⊗_{f^*B} A`**: the functor of Tag 0FTF at the diagonal bimodule and the direct
construction `derivedToposPullback` are left derived functors of isomorphic functors. -/
def derivedPullbackRingedToposIso :
    derivedPullbackRingedTopos f φ hφ ≅ derivedToposPullback f φ hφ :=
  Functor.leftDerivedNatIso _ _ (derivedPullbackRingedToposCounit f φ hφ)
    (derivedToposPullbackCounit f φ hφ) (quasiIsomorphisms.{u, u, u} B)
    (Functor.isoWhiskerRight (homotopyToposPullbackTensorDiagonalIso f φ hφ)
      (toDerivedCategory A))

/-- Precomposing an isomorphism `e` with `i.symm` is compatible with a comparison map `c` that is
corrected by `i`. -/
private theorem whiskerLeft_trans_symm_hom_comp_eq {C₁ D₁ E₁ : Type*} [Category C₁] [Category D₁]
    [Category E₁] {L : C₁ ⥤ D₁} {F G H : D₁ ⥤ E₁} {T : C₁ ⥤ E₁} (e : F ≅ G) (i : H ≅ G)
    (c : L ⋙ G ⟶ T) {β : L ⋙ F ⟶ T} (h : Functor.whiskerLeft L e.hom ≫ c = β) :
    Functor.whiskerLeft L (e ≪≫ i.symm).hom ≫ (Functor.whiskerLeft L i.hom ≫ c) = β := by
  rw [← h]
  ext
  simp

/-- The comparison map `Lf^*M ⊗^𝐋_A 𝒩 ⟶ f^*M ⊗_A 𝒩` of `Lf^* ⋙ - ⊗^𝐋_A 𝒩`. -/
def derivedPullbackRingedToposTensorCounit :
    toDerivedCategory B ⋙ (derivedPullbackRingedTopos f φ hφ ⋙
        derivedTensorProduct (X := X.toRingedSite) N) ⟶
      homotopyToposPullbackTensor f φ hφ N ⋙ toDerivedCategory A' :=
  Functor.whiskerLeft (toDerivedCategory B)
      (Functor.isoWhiskerRight (derivedPullbackRingedToposIso f φ hφ)
        (derivedTensorProduct (X := X.toRingedSite) N)).hom ≫
    derivedToposPullbackComposeTensorCounit f φ hφ N

/-- The functor `D(B, d) ⥤ D(A', d)` of Tag 0FTF, `derivedPullbackTensorRingedTopos f φ hφ 𝒩`, is
`Lf^* ⋙ - ⊗^𝐋_A 𝒩` with the derived tensor product `derivedTensorProduct` of the ringed site:
there is an isomorphism carrying the comparison map of the former to that of the latter. -/
theorem exists_iso_derivedPullbackTensorRingedTopos_derivedPullbackRingedTopos_comp :
    ∃ e : derivedPullbackTensorRingedTopos f φ hφ N ≅
        derivedPullbackRingedTopos f φ hφ ⋙ derivedTensorProduct (X := X.toRingedSite) N,
      Functor.whiskerLeft (toDerivedCategory B) e.hom ≫
          derivedPullbackRingedToposTensorCounit f φ hφ N =
        derivedPullbackTensorRingedToposCounit f φ hφ N := by
  obtain ⟨e₀, he₀⟩ := exists_iso_derivedToposPullback_comp_derivedTensorProduct f φ hφ N
    (derivedPullbackTensorRingedTopos f φ hφ N) (derivedPullbackTensorRingedToposCounit f φ hφ N)
  exact ⟨_, whiskerLeft_trans_symm_hom_comp_eq e₀
    (Functor.isoWhiskerRight (derivedPullbackRingedToposIso f φ hφ)
      (derivedTensorProduct (X := X.toRingedSite) N)) _ he₀⟩

/-- The comparison map `Lf^*M ⊗^𝐋_A 𝒩 ⟶ f^*M ⊗_A 𝒩` of `Lf^* ⋙ - ⊗^𝐋_A 𝒩`, for the derived tensor
product `derivedTensorProductTopos` of Tag 0FTG (1). -/
def derivedPullbackRingedToposTensorToposCounit :
    toDerivedCategory B ⋙ (derivedPullbackRingedTopos f φ hφ ⋙ derivedTensorProductTopos N) ⟶
      homotopyToposPullbackTensor f φ hφ N ⋙ toDerivedCategory A' :=
  Functor.whiskerLeft (toDerivedCategory B)
      (Functor.isoWhiskerLeft (derivedPullbackRingedTopos f φ hφ)
        (derivedTensorProductToposIso N)).hom ≫
    derivedPullbackRingedToposTensorCounit f φ hφ N

/-- Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, `A`, `A'` sheaves
of differential graded `O_C`-algebras, `B` a sheaf of differential graded `O_D`-algebras,
`φ : B ⟶ f_*A` a homomorphism of differential graded algebras and `𝒩` a differential graded
`(A, A')`-bimodule. The functor `D(B, d) ⥤ D(A', d)` of Tag 0FTF,
`derivedPullbackTensorRingedTopos f φ hφ 𝒩`, is `M ↦ Lf^*M ⊗^𝐋_A 𝒩`, where `Lf^*` is the
derived pullback of Tag 0FTG (2) and `- ⊗^𝐋_A 𝒩` the derived tensor product of Tag 0FTG (1),
`derivedTensorProductTopos`: there is an isomorphism
`derivedPullbackTensorRingedTopos f φ hφ 𝒩 ≅ Lf^* ⋙ - ⊗^𝐋_A 𝒩` carrying the comparison map of
the former to that of the latter. -/
@[stacks 0FTH]
theorem exists_iso_derivedPullbackTensorRingedTopos_derivedPullbackRingedTopos_comp_topos :
    ∃ e : derivedPullbackTensorRingedTopos f φ hφ N ≅
        derivedPullbackRingedTopos f φ hφ ⋙ derivedTensorProductTopos N,
      Functor.whiskerLeft (toDerivedCategory B) e.hom ≫
          derivedPullbackRingedToposTensorToposCounit f φ hφ N =
        derivedPullbackTensorRingedToposCounit f φ hφ N := by
  obtain ⟨e₀, he₀⟩ :=
    exists_iso_derivedPullbackTensorRingedTopos_derivedPullbackRingedTopos_comp f φ hφ N
  exact ⟨_, whiskerLeft_trans_symm_hom_comp_eq e₀
    (Functor.isoWhiskerLeft (derivedPullbackRingedTopos f φ hφ)
      (derivedTensorProductToposIso N)) _ he₀⟩

end PullbackTensor

section Composite

variable {X Y Z : AlgebraicGeometry.RingedTopos.{u, u, u}}
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
  {A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {A' : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  {A'' : DifferentialGradedAlgebra.{u, u} (toRingCat Z.J Z.O)}
  {φ : A' ⟶ toposPushforwardAlgebra (Osharp := X.O) (Psharp := Y.O)
    (toposDirectImageModules (X := X) (Y := Y) f) A} (hφ : φ.IsUnital)
  {φ' : A'' ⟶ toposPushforwardAlgebra (Osharp := Y.O) (Psharp := Z.O)
    (toposDirectImageModules (X := Y) (Y := Z) g) A'} (hφ' : φ'.IsUnital)

/-- Let `(f, f♯) : (Sh(C), O) ⟶ (Sh(C'), O')` and `(g, g♯) : (Sh(C'), O') ⟶ (Sh(C''), O'')` be
morphisms of ringed topoi, `𝒜`, `𝒜'`, `𝒜''` differential graded `O`-, `O'`- and `O''`-algebras,
and `φ : 𝒜' ⟶ f_*𝒜`, `φ' : 𝒜'' ⟶ g_*𝒜'` homomorphisms of differential graded algebras. Then
`L(g ∘ f)^* = Lf^* ∘ Lg^*` as functors `D(𝒜'', d) ⥤ D(𝒜, d)`, the derived pullback along `g ∘ f`
being taken along the composite homomorphism `𝒜'' ⟶ g_*𝒜' ⟶ g_*f_*𝒜 = (g ∘ f)_*𝒜`. -/
@[stacks 0FTI]
def derivedPullbackRingedToposCompIso :
    derivedPullbackRingedTopos (X := X) (Y := Z)
        (RingedToposHom.comp (X := X) (Y := Y) (Z := Z) g f)
        (toposCompHom (X := X) (Y := Y) (Z := Z) f g A φ φ')
        (isUnital_toposCompHom (X := X) (Y := Y) (Z := Z) f g A hφ hφ') ≅
      derivedPullbackRingedTopos (X := Y) (Y := Z) g φ' hφ' ⋙
        derivedPullbackRingedTopos (X := X) (Y := Y) f φ hφ :=
  derivedPullbackRingedToposIso _ _ _ ≪≫ derivedToposPullbackCompIso f g hφ hφ' ≪≫
    (Functor.isoWhiskerRight (derivedPullbackRingedToposIso g φ' hφ') _ ≪≫
      Functor.isoWhiskerLeft _ (derivedPullbackRingedToposIso f φ hφ)).symm

end Composite

end Tags

end SheafOfModules.DifferentialGradedModule
