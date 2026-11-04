module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackConstruction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforward

/-!
# The direct image of a sheaf of differential graded algebras, on local sections

Let `F : C ⥤ D` be a continuous functor of sites, read as a morphism of ringed sites `f` in the
opposite direction, and let `A` be a sheaf of differential graded algebras on the target. The
direct image `f_*A` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackConstruction` is a
transport along the lax monoidal structure of the direct image of sheaves of modules, so its
multiplication is the multiplication of `A` conjugated by the tensorator of that functor. The
sections of `f_*A` over `V` are the sections of `A` over `F V`, and the content of this file is
that the multiplication of `f_*A` on two such sections is the multiplication of `A` read over
`F V` — equivalently, that a homomorphism `A' ⟶ f_*A` of sheaves of differential graded algebras
is a semilinear homomorphism `A' ⟶ A` along `f` in the sense of
`SheafOfModules.DifferentialGradedAlgebra.SemilinearHom`.

## Main definitions

* `Stacks.DifferentialGradedPullbackConstruction.IsPushforwardMuSections` and
  `IsPushforwardEpsilonSections`: the two sections formulas for the lax monoidal structure of the
  direct image of sheaves of modules, carried as hypotheses; see the implementation notes.
* `Stacks.DifferentialGradedPullbackConstruction.semilinearHomOfPushforwardHom`: **a
  homomorphism `A' ⟶ f_*A` of sheaves of differential graded algebras, read as a semilinear
  homomorphism `A' ⟶ A` along `f`.**

## Main results

* `Stacks.DifferentialGradedPullbackConstruction.pushforwardAlgebra_mul_app`: **the
  multiplication of `f_*A` on two local sections is the multiplication of `A` over `F V`.**
* `Stacks.DifferentialGradedPullbackConstruction.pushforwardAlgebra_one_eval`: the unit of
  `f_*A` over `V` is the unit of `A` over `F V`.

## Implementation notes

**Why the two sections formulas are hypotheses.** The lax monoidal structure on the direct image
of sheaves of modules is `CategoryTheory.Adjunction.rightAdjointLaxMonoidal`, so its tensorator
is the adjoint transpose of the oplax tensorator of the inverse image followed by the two
counits, and `Stacks.PullbackMonoidalSite` gives that oplax tensorator no description on local
sections: it builds the monoidal structure on the inverse image by transporting a monoidal
structure along a localization. The presheaf-level formulas
`PresheafOfModules.pushforwardMu_app_tmul` and
`Stacks.PullbackMonoidalSite.pullbackTensorIso_hom_pullbackAdjUnit_tmul` do not by themselves
determine the sheaf-level one. The two statements are therefore isolated here as hypotheses on
which everything else is proved, and they are discharged in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorSectionsSite` —
`Stacks.DifferentialGradedPullbackConstruction.isPushforwardMuSections` and
`isPushforwardEpsilonSections`, which compute the localized tensorator on local sections.

**Everything else about a semilinear homomorphism is unconditional.** Of the six fields of
`SheafOfModules.DifferentialGradedAlgebra.SemilinearHom` only `map_mul` and `map_one` use the
two hypotheses; the underlying maps, their semilinearity, their compatibility with restriction
and their commutation with the differentials come from the degreewise components of the
homomorphism `A' ⟶ f_*A` alone, because the sections of `f_*A` over `V` are the sections of `A`
over `F V` on the nose.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf Functor PresheafOfModules
open Stacks.SheafOfModules.TensorSheafification Stacks.PullbackMonoidalSite
open Stacks.DifferentialGradedInverseImage

open scoped TensorProduct

universe u

namespace Stacks.DifferentialGradedPullbackConstruction

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [Functor.IsContinuous F J K] [RepresentablyFlat F] [F.Final]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  {Osharp : Sheaf J CommRingCat.{u}} {Psharp : Sheaf K CommRingCat.{u}}
  (α : Osharp.obj ⟶ F.op ⋙ Psharp.obj)
  (hO : Presheaf.IsSheaf J (structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K (structureRingPresheaf Psharp.obj))
  [radj : (SheafOfModules.pushforward.{u} (sheafRingHom α hO hP)).IsRightAdjoint]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
attribute [local instance] inverseImageMonoidal
attribute [local instance] pushforward_additive
attribute [local instance] pushforwardLaxMonoidal

/-- The unit local section of the unit object of Tag 01CA: the section `1` of the structure
sheaf over `V`. -/
noncomputable def oneSec (V : Cᵒᵖ) :
    (𝟙_ (SheafOfModules.{u} (toRingCat J Osharp))).val.obj V :=
  (1 : (toRingCat J Osharp).obj.obj V)

/-- **The sections formula for the tensorator of the direct image of sheaves of modules**: on
the image of a pure tensor of two local sections over `V` it is the image of the pure tensor of
the same two sections, read over `F V`. -/
def IsPushforwardMuSections : Prop :=
  ∀ (X Y : SheafOfModules.{u} (toRingCat K Psharp)) (V : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj X).val.obj V)
    (y : ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj Y).val.obj V),
    (Functor.LaxMonoidal.μ (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))
          X Y).val.app V
        ((tensorSheafUnit
            ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj X)
            ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj Y)).app V
          (x ⊗ₜ y)) =
      (tensorSheafUnit X Y).app (F.op.obj V) (x ⊗ₜ y)

/-- **The sections formula for the unit morphism of the lax monoidal direct image of sheaves of
modules**: it carries the unit section of the structure sheaf over `V` to the unit section over
`F V`. -/
def IsPushforwardEpsilonSections : Prop :=
  ∀ V : Cᵒᵖ,
    (Functor.LaxMonoidal.ε
        (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))).val.app V (oneSec V) =
      (1 : (toRingCat K Psharp).obj.obj (F.op.obj V))

variable {A' : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp)}
  {A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)}

/-- **The multiplication of `f_*A` on two local sections over `V` is the multiplication of `A`
read over `F V`**, granted the sections formula for the tensorator of the direct image. -/
theorem pushforwardAlgebra_mul_app (hmu : IsPushforwardMuSections α hO hP)
    (A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)) (i j : ℤ)
    (V : Cᵒᵖ) (x : ((pushforwardAlgebra α hO hP A).complex.X i).val.obj V)
    (y : ((pushforwardAlgebra α hO hP A).complex.X j).val.obj V) :
    ((pushforwardAlgebra α hO hP A).mul i j).app V x y = (A.mul i j).app (F.op.obj V) x y := by
  have hcomp : SheafOfModules.GradedAlgebra.transportedMul
        (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)) A.toGradedAlgebra i j =
      Functor.LaxMonoidal.μ (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))
          (A.complex.X i) (A.complex.X j) ≫
        (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).map
          (SheafOfModules.GradedAlgebra.mulSheaf A.toGradedAlgebra i j) :=
    rfl
  refine Eq.trans (SheafOfModules.GradedAlgebra.transport_mul_app
    (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)) A.toGradedAlgebra hP hO
    i j V x y) ?_
  rw [hcomp]
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ V _) ?_
  refine Eq.trans (congrArg
    (((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).map
      (SheafOfModules.GradedAlgebra.mulSheaf A.toGradedAlgebra i j)).val.app V)
    (hmu (A.complex.X i) (A.complex.X j) V x y)) ?_
  exact SheafOfModules.GradedAlgebra.mulSheaf_unit A.toGradedAlgebra i j (F.op.obj V) x y

/-- **The unit of `f_*A` over `V` is the unit of `A` read over `F V`**, granted the sections
formula for the unit morphism of the direct image. -/
theorem pushforwardAlgebra_one_eval (hone : IsPushforwardEpsilonSections α hO hP)
    (A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)) (V : Cᵒᵖ) :
    (pushforwardAlgebra α hO hP A).one.eval V = A.one.eval (F.op.obj V) := by
  have hcomp : SheafOfModules.GradedAlgebra.transportedOne
        (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)) A.toGradedAlgebra =
      Functor.LaxMonoidal.ε (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)) ≫
        (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).map
          (SheafOfModules.GradedAlgebra.oneHom A.toGradedAlgebra) :=
    rfl
  have h : (pushforwardAlgebra α hO hP A).one.eval V =
      (SheafOfModules.GradedAlgebra.transportedOne
        (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))
        A.toGradedAlgebra).val.app V (oneSec V) :=
    rfl
  rw [h, hcomp, SheafOfModules.comp_val_app_apply, hone V]
  exact (SheafOfModules.GradedAlgebra.oneHom_val_app A.toGradedAlgebra (F.op.obj V) 1).trans
    (one_smul _ _)

/-- **The structure map `f⁻¹A' ⟶ A` of a homomorphism `ψ : A' ⟶ f_*A`, on the image of a local
section under the unit of the adjunction**: it is `ψ` read on that section. -/
theorem structureMap_val_app_unit (ψ : A' ⟶ pushforwardAlgebra α hO hP A) (n : ℤ) (V : Cᵒᵖ)
    (x : (A'.complex.X n).val.obj V) :
    ((structureMap α hO hP ψ).toHomologicalComplex.f n).val.app (F.op.obj V)
        (((inverseImageAdjunction α hO hP).unit.app (A'.complex.X n)).val.app V x) =
      (ψ.toHomologicalComplex.f n).val.app V x := by
  have h : ψ.toHomologicalComplex.f n =
      (inverseImageAdjunction α hO hP).unit.app (A'.complex.X n) ≫
        (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).map
          (((inverseImageAdjunction α hO hP).homEquiv (A'.complex.X n)
            (A.complex.X n)).symm (ψ.toHomologicalComplex.f n)) :=
    (((inverseImageAdjunction α hO hP).homEquiv (A'.complex.X n)
      (A.complex.X n)).apply_symm_apply (ψ.toHomologicalComplex.f n)).symm.trans
      (Adjunction.homEquiv_unit ..)
  exact (congrArg (fun z : A'.complex.X n ⟶
    (pushforwardAlgebra α hO hP A).complex.X n ↦ z.val.app V x) h).symm

/-- **A homomorphism `A' ⟶ f_*A` of sheaves of differential graded algebras, read as a
semilinear homomorphism `A' ⟶ A` along `f`.** Its underlying maps are the degreewise components
of the homomorphism on local sections, the sections of `f_*A` over `V` being the sections of `A`
over `F V`. -/
noncomputable def semilinearHomOfPushforwardHom (hmu : IsPushforwardMuSections α hO hP)
    (hone : IsPushforwardEpsilonSections α hO hP) (ψ : A' ⟶ pushforwardAlgebra α hO hP A)
    (hψ : ψ.IsUnital) :
    SheafOfModules.DifferentialGradedAlgebra.SemilinearHom F
      (Stacks.PullbackColimit.toRingCatPullback α) A' A where
  app i V := SheafOfModules.homSections (ψ.toHomologicalComplex.f i) V
  map_smul i V s x :=
    ((ψ.toHomologicalComplex.f i).val.app V).hom.map_smul s x
  naturality i {_V _W} k x :=
    PresheafOfModules.naturality_apply (ψ.toHomologicalComplex.f i).val k x
  comm_d i V x := SheafOfModules.DifferentialGradedAlgebra.Hom.comm_d_app ψ i V x
  map_mul i j V x y :=
    (ψ.map_mul i j V x y).trans (pushforwardAlgebra_mul_app α hO hP hmu A i j V _ _)
  map_one V := (hψ V).trans (pushforwardAlgebra_one_eval α hO hP hone A V)

end Stacks.DifferentialGradedPullbackConstruction

end
