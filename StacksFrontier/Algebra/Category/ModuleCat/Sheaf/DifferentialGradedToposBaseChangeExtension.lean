module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleTransportAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestrictionAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodAcyclicDifferentialGradedPullbackTensor

/-!
# Base change along a composite `A ⟶ G(A') ⟶ G(B')`, and acyclicity

Let `G` be an additive lax monoidal functor from sheaves of modules on a site `C` to sheaves of
modules on a site `D` — for a morphism of ringed topoi, the direct image of sheaves of modules.
Let `A` be a sheaf of differential graded algebras on `D`, let `A'` and `B'` be sheaves of
differential graded algebras on `C`, let `ψ' : A ⟶ G(A')` and `φ₀ : A' ⟶ B'` be unital, and let
`ψ := ψ' ≫ G(φ₀)`. For a right differential graded `A`-module `P`, a base change of `P` along
`ψ` is an object corepresenting `Q ↦ Hom_A(P, f_{*,ψ}Q)`.

The direct image along `ψ` is the direct image along `ψ'` precomposed with restriction of
scalars along `φ₀`. If `K` is a base change of `P` along `ψ'`, the extension of scalars
`K ⊗_{A'} B'` is a base change of `P` along `ψ`; when moreover `K` is K-flat and acyclic, every
base change of `P` along `ψ` is acyclic.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.compPushforwardHom`: the composite
  `ψ' ≫ G(φ₀) : A ⟶ G(B')`.
* `SheafOfModules.DifferentialGradedModule.toposPushforwardCompHomEquiv`: the direct image along
  `ψ' ≫ G(φ₀)` is the direct image along `ψ'` of the restriction of scalars along `φ₀`, as a
  bijection of morphisms out of a right differential graded `A`-module.
* `SheafOfModules.DifferentialGradedModule.corepresentableByExtension`: a base change along
  `ψ'` followed by extension of scalars along `φ₀` is a base change along `ψ' ≫ G(φ₀)`.

## Main results

* `SheafOfModules.DifferentialGradedAlgebra.Hom.oneHom_comp_of_isUnital` and
  `SheafOfModules.DifferentialGradedAlgebra.isUnital_transportHom`: unitality at morphism level,
  and its transport along a lax monoidal functor.
* `SheafOfModules.DifferentialGradedModule.acyclic_of_corepresentableBy_comp`: if `P` has a
  K-flat acyclic base change along `ψ'`, every base change of `P` along `ψ' ≫ G(φ₀)` is
  acyclic.

## Implementation notes

The extension of scalars is the tensor product functor of
`SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight`, which lives at the module
universe `max u v` of the site `C : Type u` with `Category.{v} C`; the acyclicity section
therefore fixes the coefficient universe to `max u₁ v₁`.

## References

* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf PresheafOfModules

open scoped TensorProduct

universe v₁ v₂ u₁ u₂ w

namespace Stacks.MonoidalGraded

variable {E : Type u₁} [Category.{v₁} E] [MonoidalCategory E]
  {E' : Type u₂} [Category.{v₂} E'] [MonoidalCategory E'] (F : E ⥤ E') [F.LaxMonoidal]

/-- A lax monoidal functor transports a multiplication precomposed with a morphism on the second
factor to the transported multiplication precomposed with the image of that morphism. -/
theorem mapMul_id_tensorHom_comp {X Y Y' Z : E} (b : Y ⟶ Y') (m : X ⊗ Y' ⟶ Z) :
    mapMul F ((𝟙 X ⊗ₘ b) ≫ m) = (𝟙 (F.obj X) ⊗ₘ F.map b) ≫ mapMul F m := by
  simp only [mapMul, Functor.map_comp, ← Category.assoc]
  congr 1
  rw [← Functor.LaxMonoidal.μ_natural, CategoryTheory.Functor.map_id]

end Stacks.MonoidalGraded

namespace SheafOfModules

/-! ### Unitality at morphism level -/

section Unital

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- A unital homomorphism of sheaves of differential graded algebras carries the unit of the
source to the unit of the target at morphism level. -/
theorem DifferentialGradedAlgebra.Hom.oneHom_comp_of_isUnital
    {A B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)} (φ : A ⟶ B)
    (hφ : φ.IsUnital) :
    (GradedAlgebra.oneHom A.toGradedAlgebra : 𝟙_ _ ⟶ A.complex.X 0) ≫
        φ.toHomologicalComplex.f 0 = GradedAlgebra.oneHom B.toGradedAlgebra := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext
    (LinearMap.ext fun r => ?_))
  let r' : (toRingCat J Osharp).obj.obj U := r
  show (φ.toHomologicalComplex.f 0).val.app U (r' • A.one.eval U) = r' • B.one.eval U
  exact (map_smul (ConcreteCategory.hom ((φ.toHomologicalComplex.f 0).val.app U)) r'
    (A.one.eval U)).trans (congrArg (fun z => r' • z) (hφ U))

/-- A homomorphism of sheaves of differential graded algebras which carries the unit of the
source to the unit of the target at morphism level is unital. -/
theorem DifferentialGradedAlgebra.Hom.isUnital_of_oneHom_comp
    {A B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)} (φ : A ⟶ B)
    (h : (GradedAlgebra.oneHom A.toGradedAlgebra : 𝟙_ _ ⟶ A.complex.X 0) ≫
        φ.toHomologicalComplex.f 0 = GradedAlgebra.oneHom B.toGradedAlgebra) :
    φ.IsUnital := by
  intro U
  let one : (𝟙_ (SheafOfModules.{w} (toRingCat J Osharp))).val.obj U :=
    (1 : (toRingCat J Osharp).obj.obj U)
  have hA : (GradedAlgebra.oneHom A.toGradedAlgebra).val.app U one = A.one.eval U :=
    (GradedAlgebra.oneHom_val_app _ U 1).trans (one_smul _ _)
  have hB : (GradedAlgebra.oneHom B.toGradedAlgebra).val.app U one = B.one.eval U :=
    (GradedAlgebra.oneHom_val_app _ U 1).trans (one_smul _ _)
  rw [← hA, ← hB]
  exact SheafOfModules.hom_congr_app_apply h U one

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  (G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [G.LaxMonoidal] [G.Additive]
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))

/-- **The image of a unital homomorphism under an additive lax monoidal functor is unital.** -/
theorem DifferentialGradedAlgebra.isUnital_transportHom
    {A B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)} (φ : A ⟶ B)
    (hφ : φ.IsUnital) : (DifferentialGradedAlgebra.transportHom G hO hP φ).IsUnital := by
  intro U
  let one : (𝟙_ (SheafOfModules.{w} (toRingCat K Psharp))).val.obj U :=
    (1 : (toRingCat K Psharp).obj.obj U)
  have eA : GradedAlgebra.oneHom (DifferentialGradedAlgebra.transport G hO hP A).toGradedAlgebra =
      Stacks.MonoidalGraded.mapOne G (GradedAlgebra.oneHom A.toGradedAlgebra) :=
    GradedAlgebra.oneHom_transport G A.toGradedAlgebra hO hP
  have eB : GradedAlgebra.oneHom (DifferentialGradedAlgebra.transport G hO hP B).toGradedAlgebra =
      Stacks.MonoidalGraded.mapOne G (GradedAlgebra.oneHom B.toGradedAlgebra) :=
    GradedAlgebra.oneHom_transport G B.toGradedAlgebra hO hP
  have hφ' := DifferentialGradedAlgebra.Hom.oneHom_comp_of_isUnital φ hφ
  have e : (GradedAlgebra.oneHom (DifferentialGradedAlgebra.transport G hO hP A).toGradedAlgebra :
        𝟙_ _ ⟶ G.obj (A.complex.X 0)) ≫ G.map (φ.toHomologicalComplex.f 0) =
      GradedAlgebra.oneHom (DifferentialGradedAlgebra.transport G hO hP B).toGradedAlgebra := by
    refine (congrArg (fun z : 𝟙_ _ ⟶ G.obj (A.complex.X 0) =>
      z ≫ G.map (φ.toHomologicalComplex.f 0)) eA).trans (Eq.trans ?_ eB.symm)
    calc (Functor.LaxMonoidal.ε G ≫ G.map
            (GradedAlgebra.oneHom A.toGradedAlgebra : 𝟙_ _ ⟶ A.complex.X 0)) ≫
          G.map (φ.toHomologicalComplex.f 0)
        = Functor.LaxMonoidal.ε G ≫ (G.map
            (GradedAlgebra.oneHom A.toGradedAlgebra : 𝟙_ _ ⟶ A.complex.X 0) ≫
          G.map (φ.toHomologicalComplex.f 0)) := Category.assoc _ _ _
      _ = Functor.LaxMonoidal.ε G ≫ G.map
            ((GradedAlgebra.oneHom A.toGradedAlgebra : 𝟙_ _ ⟶ A.complex.X 0) ≫
              φ.toHomologicalComplex.f 0) :=
          congrArg (fun z => Functor.LaxMonoidal.ε G ≫ z) (G.map_comp _ _).symm
      _ = Functor.LaxMonoidal.ε G ≫ G.map
            (GradedAlgebra.oneHom B.toGradedAlgebra : 𝟙_ _ ⟶ B.complex.X 0) :=
          congrArg (fun z => Functor.LaxMonoidal.ε G ≫ G.map z) hφ'
  have hA :
      (GradedAlgebra.oneHom
        (DifferentialGradedAlgebra.transport G hO hP A).toGradedAlgebra).val.app U one =
      (DifferentialGradedAlgebra.transport G hO hP A).one.eval U :=
    (GradedAlgebra.oneHom_val_app _ U 1).trans (one_smul _ _)
  have hB :
      (GradedAlgebra.oneHom
        (DifferentialGradedAlgebra.transport G hO hP B).toGradedAlgebra).val.app U one =
      (DifferentialGradedAlgebra.transport G hO hP B).one.eval U :=
    (GradedAlgebra.oneHom_val_app _ U 1).trans (one_smul _ _)
  rw [← hA, ← hB]
  exact SheafOfModules.hom_congr_app_apply e U one

end Unital

namespace DifferentialGradedModule

/-! ### The direct image along a composite -/

section Composite

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [G.LaxMonoidal] [G.Additive]
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)}
  {A' B' : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  (ψ' : A ⟶ toposPushforwardAlgebra G A') (hψ' : ψ'.IsUnital)
  (φ₀ : A' ⟶ B') (hφ₀ : φ₀.IsUnital)

/-- The composite `A ⟶ G(A') ⟶ G(B')`. -/
noncomputable abbrev compPushforwardHom : A ⟶ toposPushforwardAlgebra G B' :=
  ψ' ≫ DifferentialGradedAlgebra.transportHom G
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp) φ₀

include hψ' hφ₀ in
/-- The composite `A ⟶ G(A') ⟶ G(B')` of two unital homomorphisms is unital. -/
theorem isUnital_compPushforwardHom : (compPushforwardHom G ψ' φ₀).IsUnital := by
  intro U
  show ((DifferentialGradedAlgebra.transportHom G _ _ φ₀).toHomologicalComplex.f 0).val.app U
      ((ψ'.toHomologicalComplex.f 0).val.app U (A.one.eval U)) = _
  rw [hψ' U]
  exact DifferentialGradedAlgebra.isUnital_transportHom G _ _ φ₀ hφ₀ U

omit [G.Additive] in
/-- The transported action of a restriction of scalars along `φ₀` is the transported action
precomposed with `G(φ₀)` on the algebra factor, at morphism level. -/
theorem transportedSmul_restrictScalarsObj (hO : Presheaf.IsSheaf J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
    (N : DifferentialGradedModule.{w, w, w} B') (n i : ℤ) :
    transportedSmul G (restrictScalarsObj φ₀ hφ₀ N) n i =
      (𝟙 (G.obj (N.complex.X n)) ⊗ₘ G.map (φ₀.toHomologicalComplex.f i)) ≫
        transportedSmul G N n i :=
  (congrArg (Stacks.MonoidalGraded.mapMul G)
    (smulSheaf_restrictScalarsObj hO φ₀ hφ₀ N n i)).trans
      (Stacks.MonoidalGraded.mapMul_id_tensorHom_comp G _ _)

/-- The transported action of a restriction of scalars along `φ₀` is the transported action
precomposed with `G(φ₀)` on the algebra factor, on local sections. -/
theorem transport_restrictScalarsObj_mul (N : DifferentialGradedModule.{w, w, w} B') (n i : ℤ)
    (U : Dᵒᵖ) (x : (G.obj (N.complex.X n)).val.obj U) (z : (G.obj (A'.complex.X i)).val.obj U) :
    ((transport G (restrictScalarsObj φ₀ hφ₀ N)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp)).mul n i).app
        U x z =
      ((transport G N
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp)).mul n i).app
        U x ((G.map (φ₀.toHomologicalComplex.f i)).val.app U z) := by
  have hO := Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp
  have hP := Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp
  have e : smulSheaf (transport G (restrictScalarsObj φ₀ hφ₀ N) hO hP) n i =
      (𝟙 (G.obj (N.complex.X n)) ⊗ₘ G.map (φ₀.toHomologicalComplex.f i)) ≫
        smulSheaf (transport G N hO hP) n i :=
    (smulSheaf_transport G _ hO hP n i).trans
      ((transportedSmul_restrictScalarsObj G φ₀ hφ₀ hO N n i).trans
        (congrArg (fun t => (𝟙 (G.obj (N.complex.X n)) ⊗ₘ
          G.map (φ₀.toHomologicalComplex.f i)) ≫ t) (smulSheaf_transport G N hO hP n i).symm))
  refine (smulSheaf_unit (transport G (restrictScalarsObj φ₀ hφ₀ N) hO hP) n i U x z).symm.trans ?_
  refine (SheafOfModules.hom_congr_app_apply e U _).trans ?_
  refine (congrArg ((smulSheaf (transport G N hO hP) n i).val.app U)
    (Stacks.TensorSheafWorld.tensorHom_val_app_tensorSheafUnit Psharp hP U
      (𝟙 (G.obj (N.complex.X n))) (G.map (φ₀.toHomologicalComplex.f i)) x z)).trans ?_
  exact smulSheaf_unit (transport G N hO hP) n i U x _

/-- The action on the direct image along `ψ' ≫ G(φ₀)` is the action on the direct image along
`ψ'` of the restriction of scalars along `φ₀`, on local sections. -/
theorem toposPushforward_compPushforwardHom_mul (N : DifferentialGradedModule.{w, w, w} B')
    (n i : ℤ) (U : Dᵒᵖ) (x : (G.obj (N.complex.X n)).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    (((toposPushforward G (compPushforwardHom G ψ' φ₀)
        (isUnital_compPushforwardHom G ψ' hψ' φ₀ hφ₀)).obj N).mul n i).app U x y =
      (((toposPushforward G ψ' hψ').obj ((restrictScalars φ₀ hφ₀).obj N)).mul n i).app U x y :=
  (transport_restrictScalarsObj_mul G φ₀ hφ₀ N n i U x
    ((ψ'.toHomologicalComplex.f i).val.app U y)).symm

/-- **The direct image along `ψ' ≫ G(φ₀)` is the direct image along `ψ'` of the restriction of
scalars along `φ₀`**, as a bijection of the morphisms out of a right differential graded
`A`-module. -/
noncomputable def toposPushforwardCompHomEquiv (P : DifferentialGradedModule.{w, w, w} A)
    (N : DifferentialGradedModule.{w, w, w} B') :
    (P ⟶ (toposPushforward G (compPushforwardHom G ψ' φ₀)
        (isUnital_compPushforwardHom G ψ' hψ' φ₀ hφ₀)).obj N) ≃
      (P ⟶ (toposPushforward G ψ' hψ').obj ((restrictScalars φ₀ hφ₀).obj N)) where
  toFun g := Hom.mk (HomologicalComplex.Hom.mk (fun q => g.toHomologicalComplex.f q)
      (fun i j hij => g.toHomologicalComplex.comm' i j hij))
    (fun n i U x y => (g.map_mul n i U x y).trans
      (toposPushforward_compPushforwardHom_mul G ψ' hψ' φ₀ hφ₀ N n i U _ y))
  invFun g := Hom.mk (HomologicalComplex.Hom.mk (fun q => g.toHomologicalComplex.f q)
      (fun i j hij => g.toHomologicalComplex.comm' i j hij))
    (fun n i U x y => (g.map_mul n i U x y).trans
      (toposPushforward_compPushforwardHom_mul G ψ' hψ' φ₀ hφ₀ N n i U _ y).symm)
  left_inv _ := Hom.ext fun _ => rfl
  right_inv _ := Hom.ext fun _ => rfl

/-- **A base change along `ψ'` followed by extension of scalars along `φ₀` is a base change
along `ψ' ≫ G(φ₀)`**: if `K` corepresents `Q ↦ Hom_A(P, f_{*,ψ'}Q)` then `K ⊗_{A'} B'`
corepresents `Q ↦ Hom_A(P, f_{*,ψ}Q)`, for any tensor product functor with the bimodule
`{}_{A'}B'_{B'}`. -/
noncomputable def corepresentableByExtension (P : DifferentialGradedModule.{w, w, w} A)
    {Kb : DifferentialGradedModule.{w, w, w} A'}
    (e : (toposPushforward G ψ' hψ' ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy Kb)
    (Dt : TensorFunctorData.{w, w, w, w, w, v₁, u₁} A' B' (φ₀.toBimodule hφ₀)) :
    (toposPushforward G (compPushforwardHom G ψ' φ₀)
        (isUnital_compPushforwardHom G ψ' hψ' φ₀ hφ₀) ⋙
      coyoneda.obj (Opposite.op P)).CorepresentableBy (Dt.functor.obj Kb) where
  homEquiv {N} :=
    (extensionRestrictionHomEquiv φ₀ hφ₀ Dt Kb N).trans
      ((e.homEquiv (Y := (restrictScalars φ₀ hφ₀).obj N)).trans
        (toposPushforwardCompHomEquiv G ψ' hψ' φ₀ hφ₀ P N).symm)
  homEquiv_comp {N N'} k g := Hom.ext fun q => by
    have h1 : extensionUnit φ₀ hφ₀ Dt Kb ≫ (restriction φ₀ hφ₀).map (g ≫ k) =
        (extensionUnit φ₀ hφ₀ Dt Kb ≫ (restriction φ₀ hφ₀).map g) ≫
          (restriction φ₀ hφ₀).map k := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
    have h2 := e.homEquiv_comp ((restriction φ₀ hφ₀).map k)
      (extensionUnit φ₀ hφ₀ Dt Kb ≫ (restriction φ₀ hφ₀).map g)
    show (e.homEquiv (extensionUnit φ₀ hφ₀ Dt Kb ≫
          (restriction φ₀ hφ₀).map (g ≫ k))).toHomologicalComplex.f q =
      (e.homEquiv (extensionUnit φ₀ hφ₀ Dt Kb ≫
          (restriction φ₀ hφ₀).map g)).toHomologicalComplex.f q ≫
        G.map (k.toHomologicalComplex.f q)
    rw [h1, h2]
    rfl

end Composite

/-! ### Acyclicity of a base change along a composite -/

section Acyclic

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  {Osharp : Sheaf J CommRingCat.{max u₁ v₁}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasWeakSheafify J AddCommGrpCat.{max u₁ v₁}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  {Psharp : Sheaf K CommRingCat.{max u₁ v₁}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasWeakSheafify K AddCommGrpCat.{max u₁ v₁}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (G : SheafOfModules.{max u₁ v₁} (toRingCat J Osharp) ⥤
    SheafOfModules.{max u₁ v₁} (toRingCat K Psharp))
  [G.LaxMonoidal] [G.Additive]
  {A : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat K Psharp)}
  {A' B' : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat J Osharp)}
  (ψ' : A ⟶ toposPushforwardAlgebra G A') (hψ' : ψ'.IsUnital)
  (φ₀ : A' ⟶ B') (hφ₀ : φ₀.IsUnital)

/-- **Every base change along a composite of a K-flat acyclic base change is acyclic.** Let
`K` be a base change of `P` along `ψ' : A ⟶ G(A')` which is K-flat and acyclic, and let `T` be a
base change of `P` along `ψ' ≫ G(φ₀)`. Then `T` is acyclic. -/
theorem acyclic_of_corepresentableBy_comp
    (P : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A)
    {Kb : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A'}
    (e : (toposPushforward G ψ' hψ' ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy Kb)
    (hK : RelativeTensor.IsKFlat Kb) (hKac : Kb.complex.Acyclic)
    {T : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} B'}
    (eT : (toposPushforward G (compPushforwardHom G ψ' φ₀)
        (isUnital_compPushforwardHom G ψ' hψ' φ₀ hφ₀) ⋙
      coyoneda.obj (Opposite.op P)).CorepresentableBy T) :
    T.complex.Acyclic := by
  let Dt := RelativeTensor.tensorFunctorDataDgTensorRight (φ₀.toBimodule hφ₀)
  have iso : Dt.functor.obj Kb ≅ T :=
    (corepresentableByExtension G ψ' hψ' φ₀ hφ₀ P e Dt).uniqueUpToIso eT
  have e' : (Dt.functor.obj Kb).complex ≅ T.complex :=
    { hom := iso.hom.toHomologicalComplex
      inv := iso.inv.toHomologicalComplex
      hom_inv_id := HomologicalComplex.hom_ext _ _ fun n =>
        congrArg (fun g : Dt.functor.obj Kb ⟶ Dt.functor.obj Kb =>
          g.toHomologicalComplex.f n) iso.hom_inv_id
      inv_hom_id := HomologicalComplex.hom_ext _ _ fun n =>
        congrArg (fun g : T ⟶ T => g.toHomologicalComplex.f n) iso.inv_hom_id }
  exact fun i => (acyclic_dgTensor_of_isKFlat_of_acyclic hK hKac
    (φ₀.toBimodule hφ₀).toLeftDifferentialGradedModule i).of_iso e'

end Acyclic

end DifferentialGradedModule

end SheafOfModules

end
