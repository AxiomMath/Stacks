module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPullbackGood

/-!
# The pullback of differential graded modules is left adjoint to the direct image

Let `f : (Sh(C'), O') ⟶ (Sh(C), O)` be a morphism of ringed topoi, `A` a sheaf of differential
graded `O`-algebras, `B` a sheaf of differential graded `O'`-algebras and `ψ : A ⟶ f_*B` a unital
homomorphism. The pullback `M ↦ f^*M ⊗_{f^*A} B` of right differential graded modules is a
functor `Mod(A, d) ⥤ Mod(B, d)` (`toposBaseChangeFunctor`), and its values corepresent
`Q ↦ Hom_A(M, f_{*,ψ}Q)` (`toposBaseChangeCorepresentableBy`). This file shows that the
corepresentation is natural in `M`, so that the pullback is **left adjoint** to the direct image
`f_{*,ψ}` (`toposBaseChangeAdjunction`), the adjunction of Tag 0FRU at a morphism of ringed topoi.
For composable morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` with `φ : A' ⟶ f_*A` and `φ' : A'' ⟶ g_*A'`,
uniqueness of left adjoints and the composite direct image
`(g ∘ f)_* ≅ g_* ∘ f_*` give `(g ∘ f)^* ≅ f^* ∘ g^*` (`toposBaseChangeFunctorCompIso`).

## Main definitions

* `toposBaseChangeFunctor`: `M ↦ f^*M ⊗_{f^*A} B`.
* `toposBaseChangeAdjunction`: `f^* ⊣ f_{*,ψ}`.
* `toposCompHom`: the structure homomorphism `A'' ⟶ (g ∘ f)_*A` along the composite.
* `toposPushforwardCompHomIso`: `(g ∘ f)_* ≅ g_* ∘ f_*`.
* `toposBaseChangeFunctorCompIso`: `(g ∘ f)^* ≅ f^* ∘ g^*`.

## Main results

* `toposBaseChangeCorepresentableBy_homEquiv_naturality_left`: the corepresentation is natural in
  the module.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FRG](https://stacks.math.columbia.edu/tag/0FRG)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules

universe t a m v₁ u₁ v₂ u₂

namespace SheafOfModules.DifferentialGradedModule

section Extension

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {A B : DifferentialGradedAlgebra.{t, a} R} (φ : A ⟶ B) (hφ : φ.PreservesOne)
  (D : TensorFunctorData.{t, a, m, a, m, v₁, u₁} A B (φ.toBimodule hφ))

omit [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- The transpose of `D(u) ≫ k` along extension of scalars is `u` followed by the transpose of
`k`. -/
theorem extensionUnit_comp_restriction_map {M M' : DifferentialGradedModule.{t, a, m} A}
    {L : DifferentialGradedModule.{t, a, m} B} (u : M ⟶ M') (k : D.functor.obj M' ⟶ L) :
    extensionUnit φ hφ D M ≫ (restriction.{t, a, m} φ hφ).map (D.functor.map u ≫ k) =
      u ≫ extensionUnit φ hφ D M' ≫ (restriction.{t, a, m} φ hφ).map k := by
  rw [Functor.map_comp, ← Category.assoc, ← extensionUnit_naturality, Category.assoc]

end Extension

section BaseChange

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, max u₁ v₁}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{max u₁ v₁})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max u₁ v₁})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasSheafify Y.J AddCommGrpCat.{max u₁ v₁}]
  {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, max u₁ v₁}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{max u₁ v₁})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max u₁ v₁})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasSheafify X.J AddCommGrpCat.{max u₁ v₁}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (f : RingedToposHom X Y)
  {A : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat Y.J Y.O)}
  {B : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat X.J X.O)}
  (ψ : A ⟶ toposPushforwardAlgebra (toposDirectImageModules f) B) (hψ : ψ.IsUnital)

/-- A corepresentation transported along an equality of structure homomorphisms has the same
components. -/
theorem corepresentableByOfEq_homEquiv_f {P : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁,
      max u₁ v₁} A}
    {T : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} B}
    {ψ₁ ψ₂ : A ⟶ toposPushforwardAlgebra (toposDirectImageModules f) B} (h : ψ₁ = ψ₂)
    (h₁ : ψ₁.IsUnital) (h₂ : ψ₂.IsUnital)
    (e : (toposPushforward (toposDirectImageModules f) ψ₁ h₁ ⋙
      coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    {N : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} B} (k : T ⟶ N) (q : ℤ) :
    ((corepresentableByOfEq f h h₁ h₂ e).homEquiv k).toHomologicalComplex.f q =
      (e.homEquiv k).toHomologicalComplex.f q := by
  subst h
  rfl

/-- The components of the corepresentation of `Q ↦ Hom_A(P, f_{*,ψ}Q)` by `f^*P ⊗_{f^*A} B`:
the extension unit followed by the morphism, transposed along `f^* ⊣ f_*` in each degree. -/
theorem toposBaseChangeCorepresentableBy_homEquiv_f
    (P : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A)
    {N : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} B}
    (k : (RelativeTensor.tensorFunctorDataDgTensorRight
        ((toposBaseChangeStructureMap f ψ).toBimodule
          (isUnital_toposBaseChangeStructureMap f ψ hψ))).functor.obj (toposPullbackModule f P) ⟶
      N) (q : ℤ) :
    ((toposBaseChangeCorepresentableBy f ψ hψ P).homEquiv k).toHomologicalComplex.f q =
      (toposInverseImageAdjunction f).homEquiv _ _
        ((extensionUnit (toposBaseChangeStructureMap f ψ)
            (isUnital_toposBaseChangeStructureMap f ψ hψ)
            (RelativeTensor.tensorFunctorDataDgTensorRight
              ((toposBaseChangeStructureMap f ψ).toBimodule
                (isUnital_toposBaseChangeStructureMap f ψ hψ))) (toposPullbackModule f P) ≫
          (restriction (toposBaseChangeStructureMap f ψ)
            (isUnital_toposBaseChangeStructureMap f ψ hψ)).map k).toHomologicalComplex.f q) :=
  corepresentableByOfEq_homEquiv_f f _ _ hψ _ k q

/-- **The pullback of right differential graded modules along a base change** `(f, B, ψ)`,
`M ↦ f^*M ⊗_{f^*A} B`: the pullback of sheaves of modules followed by extension of scalars along
the adjoint transpose `f^*A ⟶ B` of `ψ`. -/
abbrev toposBaseChangeFunctor :
    DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A ⥤
      DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} B :=
  transportFunctor (toposInverseImageModules f)
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Y.O)
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O) ⋙
    (RelativeTensor.tensorFunctorDataDgTensorRight
      ((toposBaseChangeStructureMap f ψ).toBimodule
        (isUnital_toposBaseChangeStructureMap f ψ hψ))).functor

/-- The corepresentation of `Q ↦ Hom_A(P, f_{*,ψ}Q)` by `f^*P ⊗_{f^*A} B` is natural in `P`. -/
theorem toposBaseChangeCorepresentableBy_homEquiv_naturality_left
    {P P' : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A} (u : P ⟶ P')
    {N : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} B}
    (k : (toposBaseChangeFunctor f ψ hψ).obj P' ⟶ N) :
    (toposBaseChangeCorepresentableBy f ψ hψ P).homEquiv
        ((toposBaseChangeFunctor f ψ hψ).map u ≫ k) =
      u ≫ (toposBaseChangeCorepresentableBy f ψ hψ P').homEquiv k := by
  refine Hom.ext fun q => ?_
  have h := congrArg (fun z => z.toHomologicalComplex.f q)
    (extensionUnit_comp_restriction_map (toposBaseChangeStructureMap f ψ)
      (isUnital_toposBaseChangeStructureMap f ψ hψ)
      (RelativeTensor.tensorFunctorDataDgTensorRight
        ((toposBaseChangeStructureMap f ψ).toBimodule
          (isUnital_toposBaseChangeStructureMap f ψ hψ)))
      ((transportFunctor (toposInverseImageModules f)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Y.O)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O)).map u) k)
  refine (toposBaseChangeCorepresentableBy_homEquiv_f f ψ hψ P _ q).trans
    ((congrArg ((toposInverseImageAdjunction f).homEquiv _ _) h).trans
      (((toposInverseImageAdjunction f).homEquiv_naturality_left _ _).trans ?_))
  exact congrArg (u.toHomologicalComplex.f q ≫ ·)
    (toposBaseChangeCorepresentableBy_homEquiv_f f ψ hψ P' k q).symm

/-- **The pullback is left adjoint to the direct image**: `M ↦ f^*M ⊗_{f^*A} B` is left adjoint
to `f_{*,ψ}`, the hom-set bijection being the corepresentation
`toposBaseChangeCorepresentableBy`. -/
def toposBaseChangeAdjunction :
    toposBaseChangeFunctor f ψ hψ ⊣ toposPushforward (toposDirectImageModules f) ψ hψ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P N => (toposBaseChangeCorepresentableBy f ψ hψ P).homEquiv
      homEquiv_naturality_left_symm := fun {P' P N} u k => by
        refine (toposBaseChangeCorepresentableBy f ψ hψ P').homEquiv.injective ?_
        refine (Equiv.apply_symm_apply _ _).trans (Eq.trans ?_
          (toposBaseChangeCorepresentableBy_homEquiv_naturality_left f ψ hψ u _).symm)
        exact congrArg (u ≫ ·) (Equiv.apply_symm_apply _ k).symm
      homEquiv_naturality_right := fun {P N N'} k l =>
        (toposBaseChangeCorepresentableBy f ψ hψ P).homEquiv_comp l k }

end BaseChange

section Composite

variable {X Y : AlgebraicGeometry.RingedTopos.{v₁, u₁, max u₁ v₁}}
  {Z : AlgebraicGeometry.RingedTopos.{v₂, u₂, max u₁ v₁}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{max u₁ v₁})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max u₁ v₁})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasSheafify X.J AddCommGrpCat.{max u₁ v₁}]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{max u₁ v₁})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max u₁ v₁})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasSheafify Y.J AddCommGrpCat.{max u₁ v₁}]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  [Z.J.HasSheafCompose (CategoryTheory.forget RingCat.{max u₁ v₁})]
  [Z.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max u₁ v₁})]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasSheafify Z.J AddCommGrpCat.{max u₁ v₁}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
  (A : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat X.J X.O))
  {A' : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat Y.J Y.O)}
  {A'' : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat Z.J Z.O)}
  (φ : A' ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A) (φ' : A'' ⟶
    toposPushforwardAlgebra (toposDirectImageModules g) A')

/-- **The structure homomorphism along the composite `g ∘ f`**: `φ' : A'' ⟶ g_*A'`, then
`g_*φ`, then the comparison `g_*f_*A ≅ (g ∘ f)_*A`. -/
abbrev toposCompHom : A'' ⟶ toposPushforwardAlgebra
    (toposDirectImageModules (RingedToposHom.comp g f)) A :=
  toposPushforwardCompAlgebraHom f g (RingedToposHom.comp g f)
    (Iso.refl (f.toToposHom.pushforward ⋙ g.toToposHom.pushforward))
    (RingedToposHom.fSharpSetComp_comp g f) A φ φ'

variable {φ φ'} (hφ : φ.IsUnital) (hφ' : φ'.IsUnital)

include hφ hφ' in
/-- The structure homomorphism along the composite is unital. -/
theorem isUnital_toposCompHom : (toposCompHom f g A φ φ').IsUnital :=
  isUnital_toposPushforwardCompAlgebraHom _ _ _ _ _ A φ φ' hφ hφ'

/-- **The direct image along `g ∘ f` is the direct image along `f` followed by that along `g`.** -/
def toposPushforwardCompHomIso :
    toposPushforward (toposDirectImageModules (RingedToposHom.comp g f))
        (toposCompHom f g A φ φ') (isUnital_toposCompHom f g A hφ hφ') ≅
      toposPushforward (toposDirectImageModules f) φ hφ ⋙
        toposPushforward (toposDirectImageModules g) φ' hφ' :=
  toposPushforwardCompIsoOfComparison _ _ _ _ _ A hφ hφ'

/-- **The pullback along `g ∘ f` is the pullback along `g` followed by that along `f`**, on
differential graded modules: both are left adjoint to the direct image along `g ∘ f`. -/
def toposBaseChangeFunctorCompIso :
    toposBaseChangeFunctor (RingedToposHom.comp g f) (toposCompHom f g A φ φ')
        (isUnital_toposCompHom f g A hφ hφ') ≅
      toposBaseChangeFunctor g φ' hφ' ⋙ toposBaseChangeFunctor f φ hφ :=
  Adjunction.leftAdjointUniq
    ((toposBaseChangeAdjunction (RingedToposHom.comp g f) (toposCompHom f g A φ φ')
      (isUnital_toposCompHom f g A hφ hφ')).ofNatIsoRight (toposPushforwardCompHomIso f g A hφ hφ'))
    ((toposBaseChangeAdjunction g φ' hφ').comp (toposBaseChangeAdjunction f φ hφ))

end Composite

end SheafOfModules.DifferentialGradedModule
