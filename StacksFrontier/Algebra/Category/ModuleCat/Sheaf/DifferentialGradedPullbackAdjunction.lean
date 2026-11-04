module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleTensorUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestrictionAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraMonoidalAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorSectionsSite

/-!
# The universal property of the pullback `f^*M = f⁻¹M ⊗_{f⁻¹A'} A`

Let `F : C ⥤ D` be a continuous functor of small sites, read as the functor underlying a
morphism of ringed sites `f` in the opposite direction, and let `α : O ⟶ f_*P` be the structure
map of its sheaves of commutative rings. Let `A'` be a sheaf of differential graded `O`-algebras,
let `A` be a sheaf of differential graded `P`-algebras and let `φ₀ : f⁻¹A' ⟶ A` be a unital
homomorphism. `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/
DifferentialGradedPullbackConstruction.lean` builds the pullback
`f^*M = f⁻¹M ⊗_{f⁻¹A'} A` of a right differential graded `A'`-module `M`; this file proves that
it *is* the pullback, in the sense of
`SheafOfModules.DifferentialGradedModule.IsPullback`: the morphisms `f^*M ⟶ N` of right
differential graded `A'`-modules are the `φ`-semilinear maps `M ⟶ N`, where `φ` is `φ₀` read as
a semilinear homomorphism `A' ⟶ f_*A` along `F`.

## Main definitions

* `Stacks.DifferentialGradedPullbackConstruction.pushforwardHom` is the adjoint transpose
  `A' ⟶ f_*A` of a structure map `φ₀ : f⁻¹A' ⟶ A`, and
  `Stacks.DifferentialGradedPullbackConstruction.semilinearHom` is `φ₀` read as a semilinear
  homomorphism of sheaves of differential graded algebras along `F`.
* `Stacks.DifferentialGradedPullbackConstruction.transposeEquiv` is the degreewise adjoint
  transpose, a bijection between the morphisms `f⁻¹M ⟶ res_{φ₀} N` of right differential graded
  `f⁻¹A'`-modules and the morphisms `M ⟶ f_*N` of right differential graded `A'`-modules.
* `Stacks.DifferentialGradedPullbackConstruction.pullbackTensorFunctorData` is the relative
  tensor product with `A` as the tensor product functor datum of Tag 0FTE, whose value at the
  inverse image of `M` is the pullback.
* `Stacks.DifferentialGradedPullbackConstruction.pullbackUnit` is **the unit
  `M ⟶ f^*M`**, and `Stacks.DifferentialGradedPullbackConstruction.pullbackData` is **the
  resulting `SheafOfModules.DifferentialGradedModule.PullbackData`**, the structure that
  `DifferentialGradedPullback.lean` carries as a hypothesis.
* `Stacks.DifferentialGradedPullbackConstruction.pullbackFunctor` is **the pullback functor
  `f^* : Mod^dg(A', d) ⥤ Mod^dg(A, d)`**.

## Main results

* `Stacks.DifferentialGradedPullbackConstruction.smulSheaf_transpose_iff`: a degreewise family
  out of `f⁻¹M` intertwines the actions of `f⁻¹A'` exactly when its adjoint transpose
  intertwines the actions of `A'`; `map_mul_transpose_iff` is the same statement with both sides
  read on local sections.
* `Stacks.DifferentialGradedPullbackConstruction.pullbackHomEquiv`: **the universal property of
  the pullback**, the bijection `Hom_{Mod^dg(A, d)}(f^*M, N) ≃ SemilinearHom φ M N`, with
  `pullbackHomEquiv_comp` its naturality in the target.
* `Stacks.DifferentialGradedPullbackConstruction.isPullback_pullbackUnit`: **the unit exhibits
  `f⁻¹M ⊗_{f⁻¹A'} A` as the pullback**, that is it satisfies
  `SheafOfModules.DifferentialGradedModule.IsPullback`.
* `Stacks.DifferentialGradedPullbackConstruction.pullbackUnit_postcomp_map`: the unit is natural
  in `M`, and
  `Stacks.DifferentialGradedPullbackConstruction.pullbackPushforwardAdjunction`: **the pullback
  is left adjoint to the direct image**.

## Implementation notes

The hypotheses are those of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedInverseImage.lean`: two small
sites in one universe with `[CategoryTheory.Functor.RepresentablyFlat F]` and `[F.Final]`, which
is what makes the inverse image of sheaves of modules strong monoidal and so makes the inverse
image of a sheaf of differential graded algebras available at all.

**Why everything is at one universe `u`.** The sites, the sheaves of commutative rings, the
homogeneous pieces of the two algebras and the sections of the modules are all at `u`, so every
module here is a `SheafOfModules.DifferentialGradedModule.{u, u, u}`. The source imposes no such
restriction. Neither half of the construction is pinned to the site universe any more; what
pins this file is that the two halves are general in *incompatible spellings* of the same
condition "the module universe dominates the site's".

* The *inverse image* half wants the module universe to be a free universe parameter.
  `Stacks.DifferentialGradedInverseImage.inverseImageAlgebra` and `inverseImageModule` take the
  sheaf of rings and the module sections at a universe `w` free of the site universe, subject to
  `[UnivLE.{u, w}]`; that condition, and the smallness of the two sites, are what
  `Stacks.PullbackMonoidalSite.pullbackMonoidalStrict` needs, and
  `StacksFrontier/Algebra/Category/ModuleCat/Presheaf/PullbackColimit.lean` records why.
* The *relative tensor product* half wants the module universe to be the level `max u v z`.
  `pullbackObj` is `SheafOfModules.RelativeTensor.dgTensorRight`, a
  `SheafOfModules.DifferentialGradedModule.{t, max u v z, max u v z}` with `z` free — every
  universe at least as large as the site's, and no restriction on the sheaf of rings. `max` and
  not a `UnivLE` hypothesis because the right action is a morphism of presheaves of modules
  into the internal hom `Stacks.bilinHom`, whose sections `Stacks.BilinHomPi G P U` are indexed
  by the morphisms of the site and so form a `Type (max u v w w')`: source and target of that
  morphism must lie in one `PresheafOfModules.{·}`, which is the *level equation*
  `m = max u v m`, solved only by writing `m` as a `max`.

The two cannot be met at once here, and the obstruction is a cost. Spelling this file's module universe `max u w` — the general solution of
`m = max u m` at a small site, so what `dgTensorRight` can be applied at — makes
`pushforwardAlgebra_mul_app` and `pushforwardAlgebra_one_eval` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackUnit.lean` report a
deterministic timeout at `isDefEq` on the 200000-heartbeat limit, and they still time out at
1000000. Spelling it as a free `w` with `[UnivLE.{u, w}]` last in
the telescope, those same two proofs compile unchanged, which is what identifies the `max` as
the cause: with two universe atoms joined by `max`, the levels that occur in this layer are
`max (max (max (u + 1) (w + 1)) u w) u` and every `whnf` step renormalizes them, while a free
atom keeps them at `max (u + 1) (w + 1)`.

Reconciling the two is a change to `Stacks.bilinHom`, not to this file and not to
`gradedTensorRight`: were `Stacks.BilinHomPi` shrunk into the module universe under
`[UnivLE.{max u v, m}]`, the relative tensor product would take a free module universe too and
this file would follow the inverse image.

**How the universal property is proved.** Three bijections compose. Extension of scalars along
`φ₀` is left adjoint to restriction of scalars — `extensionRestrictionHomEquiv` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedRestrictionAdjunction.lean`,
applied to the tensor product functor datum that the relative tensor product of
`DifferentialGradedBimoduleTensorUniversal.lean` supplies — so a morphism `f^*M ⟶ N` is a
morphism `f⁻¹M ⟶ res_{φ₀} N`. The degreewise adjoint transpose `transposeEquiv` turns that into
a morphism `M ⟶ f_*N`, which `semilinearHomEquiv` of `DifferentialGradedPushforward.lean`
identifies with a `φ`-semilinear map. The only non-formal step is the middle one, and its two
halves are already stated separately: commutation with the differentials transports by
`CategoryTheory.Adjunction.homEquiv_naturality_left_square_iff`, and the module actions by
`smulSheaf_transpose_iff`, which is `Stacks.MonoidalGraded.mapMul_comp_iff` at the action of a
module with the unit of the adjunction on the algebra factor absorbed.

Because the bijection is natural in the target, `IsPullback` follows from
`SheafOfModules.DifferentialGradedModule.IsPullback.ofHomEquiv`, and the functor, the naturality
of the unit and the adjunction are then the general consequences of `PullbackData` recorded in
`DifferentialGradedPullback.lean` and `DifferentialGradedPushforward.lean`; nothing of that is
redone here.

The two sheafifications `isPushforwardMuSections` and `isPushforwardEpsilonSections` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorSectionsSite.lean` are theorems, not
hypotheses, which is why this file sits downstream of that one rather than inside
`DifferentialGradedPullbackConstruction.lean`: that file is imported by
`DifferentialGradedPullbackUnit.lean`, which is imported by `PullbackTensorSectionsSite.lean`,
so the material here cannot be added there without a cycle. The namespace is the same, so the
two files read as one development.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
* [Stacks Project, Tag 0FRT](https://stacks.math.columbia.edu/tag/0FRT)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf Functor
open Stacks.SheafOfModules.TensorSheafification Stacks.PullbackMonoidalSite
open Stacks.DifferentialGradedInverseImage

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

include radj

/-- The unit morphism of the strong monoidal inverse image undoes its oplax counterpart, on
local sections. -/
theorem epsilon_eta_apply (W : Dᵒᵖ)
    (z : ((inverseImageModules α hO hP).obj
      (𝟙_ (SheafOfModules.{u} (toRingCat J Osharp)))).val.obj W) :
    (Functor.LaxMonoidal.ε (inverseImageModules α hO hP)).val.app W
        ((Functor.OplaxMonoidal.η (inverseImageModules α hO hP)).val.app W z) = z :=
  (SheafOfModules.comp_val_app_apply (Functor.OplaxMonoidal.η (inverseImageModules α hO hP))
      (Functor.LaxMonoidal.ε (inverseImageModules α hO hP)) W z).symm.trans
    (SheafOfModules.hom_congr_app_apply
      (Functor.Monoidal.η_ε (inverseImageModules α hO hP)) W z)

/-- The unit of the adjunction carries the unit section of the structure sheaf over `V` to the
image of the unit morphism of the strong monoidal inverse image over `F V`. -/
theorem unit_val_app_oneSec (V : Cᵒᵖ) :
    (((inverseImageAdjunction α hO hP).unit.app
          (𝟙_ (SheafOfModules.{u} (toRingCat J Osharp)))).val.app V (oneSec V)) =
      (Functor.LaxMonoidal.ε (inverseImageModules α hO hP)).val.app (F.op.obj V)
        (1 : (toRingCat K Psharp).obj.obj (F.op.obj V)) :=
  (epsilon_eta_apply α hO hP (F.op.obj V) _).symm.trans
    (congrArg ((Functor.LaxMonoidal.ε (inverseImageModules α hO hP)).val.app (F.op.obj V))
      ((SheafOfModules.comp_val_app_apply
            ((inverseImageAdjunction α hO hP).unit.app
              (𝟙_ (SheafOfModules.{u} (toRingCat J Osharp))))
            ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).map
              (Functor.OplaxMonoidal.η (inverseImageModules α hO hP))) V (oneSec V)).symm.trans
        ((SheafOfModules.hom_congr_app_apply
            (Adjunction.unit_app_unit_comp_map_η (inverseImageAdjunction α hO hP)) V
            (oneSec V)).trans (isPushforwardEpsilonSections α hO hP V))))

variable {A' : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp)}
  {A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)}

/-- **The unit of `f⁻¹A'` is the unit of `A'`, read through the unit of the adjunction**: the
unit section of `A'` over `V` is carried to the unit section of `f⁻¹A'` over `F V`. -/
theorem unit_val_app_one_eval
    (A' : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp)) (V : Cᵒᵖ) :
    ((inverseImageAdjunction α hO hP).unit.app (A'.complex.X 0)).val.app V (A'.one.eval V) =
      (inverseImageAlgebra α hO hP A').one.eval (F.op.obj V) := by
  have hone : (SheafOfModules.GradedAlgebra.oneHom A'.toGradedAlgebra).val.app V (oneSec V) =
      A'.one.eval V :=
    (SheafOfModules.GradedAlgebra.oneHom_val_app A'.toGradedAlgebra V 1).trans (one_smul _ _)
  have hnat : (SheafOfModules.GradedAlgebra.oneHom A'.toGradedAlgebra ≫
        (inverseImageAdjunction α hO hP).unit.app (A'.complex.X 0)).val.app V (oneSec V) =
      ((inverseImageAdjunction α hO hP).unit.app
            (𝟙_ (SheafOfModules.{u} (toRingCat J Osharp))) ≫
          (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).map
            ((inverseImageModules α hO hP).map
              (SheafOfModules.GradedAlgebra.oneHom A'.toGradedAlgebra))).val.app V (oneSec V) :=
    SheafOfModules.hom_congr_app_apply
      ((inverseImageAdjunction α hO hP).unit.naturality
        (SheafOfModules.GradedAlgebra.oneHom A'.toGradedAlgebra)) V (oneSec V)
  refine Eq.trans (congrArg
    (((inverseImageAdjunction α hO hP).unit.app (A'.complex.X 0)).val.app V) hone.symm) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    (SheafOfModules.GradedAlgebra.oneHom A'.toGradedAlgebra)
    ((inverseImageAdjunction α hO hP).unit.app (A'.complex.X 0)) V (oneSec V)).symm ?_
  refine Eq.trans hnat ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    ((inverseImageAdjunction α hO hP).unit.app
      (𝟙_ (SheafOfModules.{u} (toRingCat J Osharp))))
    ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).map
      ((inverseImageModules α hO hP).map
        (SheafOfModules.GradedAlgebra.oneHom A'.toGradedAlgebra))) V (oneSec V)) ?_
  refine Eq.trans (congrArg
    (((inverseImageModules α hO hP).map
      (SheafOfModules.GradedAlgebra.oneHom A'.toGradedAlgebra)).val.app (F.op.obj V))
    (unit_val_app_oneSec α hO hP V)) ?_
  exact (SheafOfModules.comp_val_app_apply
    (Functor.LaxMonoidal.ε (inverseImageModules α hO hP))
    ((inverseImageModules α hO hP).map
      (SheafOfModules.GradedAlgebra.oneHom A'.toGradedAlgebra)) (F.op.obj V) _).symm

/-- **The homomorphism `A' ⟶ f_*A` attached to a structure map `φ₀ : f⁻¹A' ⟶ A`**, its adjoint
transpose. -/
noncomputable def pushforwardHom (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A) :
    A' ⟶ pushforwardAlgebra α hO hP A :=
  structureMapEquiv α hO hP A' A φ₀

/-- The structure map of `pushforwardHom φ₀` is `φ₀`. -/
theorem structureMap_pushforwardHom (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A) :
    structureMap α hO hP (pushforwardHom α hO hP φ₀) = φ₀ :=
  (structureMapEquiv α hO hP A' A).symm_apply_apply φ₀

/-- The structure map `φ₀`, applied to the image of a local section under the unit of the
adjunction, is the adjoint transpose `pushforwardHom φ₀` read on that section. -/
private theorem structureMap_val_app_unit_eq (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A) (i : ℤ)
    (V : Cᵒᵖ) (x : (A'.complex.X i).val.obj V) :
    (φ₀.toHomologicalComplex.f i).val.app (F.op.obj V)
        (((inverseImageAdjunction α hO hP).unit.app (A'.complex.X i)).val.app V x) =
      ((pushforwardHom α hO hP φ₀).toHomologicalComplex.f i).val.app V x :=
  (congrArg (fun z : inverseImageAlgebra α hO hP A' ⟶ A =>
      (z.toHomologicalComplex.f i).val.app (F.op.obj V)
        (((inverseImageAdjunction α hO hP).unit.app (A'.complex.X i)).val.app V x))
    (structureMap_pushforwardHom α hO hP φ₀).symm).trans
    (structureMap_val_app_unit α hO hP (pushforwardHom α hO hP φ₀) i V x)

/-- **A unital structure map `φ₀ : f⁻¹A' ⟶ A` has a unital adjoint transpose.** -/
theorem isUnital_pushforwardHom (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A)
    (hφ₀ : φ₀.IsUnital) : (pushforwardHom α hO hP φ₀).IsUnital := by
  intro V
  refine Eq.trans (structureMap_val_app_unit_eq α hO hP φ₀ 0 V (A'.one.eval V)).symm ?_
  refine Eq.trans (congrArg ((φ₀.toHomologicalComplex.f 0).val.app (F.op.obj V))
    (unit_val_app_one_eval α hO hP A' V)) ?_
  refine Eq.trans (hφ₀ (F.op.obj V)) ?_
  exact (pushforwardAlgebra_one_eval α hO hP (isPushforwardEpsilonSections α hO hP) A V).symm

/-- **A structure map `φ₀ : f⁻¹A' ⟶ A`, read as a semilinear homomorphism `A' ⟶ A` along
`f`.** -/
noncomputable def semilinearHom (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A)
    (hφ₀ : φ₀.IsUnital) :
    SheafOfModules.DifferentialGradedAlgebra.SemilinearHom F
      (Stacks.PullbackColimit.toRingCatPullback α) A' A :=
  semilinearHomOfPushforwardHom α hO hP (isPushforwardMuSections α hO hP)
    (isPushforwardEpsilonSections α hO hP) (pushforwardHom α hO hP φ₀)
    (isUnital_pushforwardHom α hO hP φ₀ hφ₀)

/-- **The semilinear homomorphism attached to `φ₀`, on local sections**: it is `φ₀` applied to
the image of the section under the unit of the adjunction. -/
theorem semilinearHom_app (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A) (hφ₀ : φ₀.IsUnital)
    (i : ℤ) (V : Cᵒᵖ) (x : (A'.complex.X i).val.obj V) :
    (semilinearHom α hO hP φ₀ hφ₀).app i V x =
      (φ₀.toHomologicalComplex.f i).val.app (F.op.obj V)
        (((inverseImageAdjunction α hO hP).unit.app (A'.complex.X i)).val.app V x) :=
  (structureMap_val_app_unit_eq α hO hP φ₀ i V x).symm

open SheafOfModules.DifferentialGradedModule in
/-- **The morphism-level action of the direct image `f_*Lm`**: it is the unit of the adjunction
on the algebra factor followed by the transport of the morphism-level action of `res_{φ₀} Lm`
along the lax monoidal direct image of sheaves of modules. -/
theorem smulSheaf_pushforwardObj (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A) (hφ₀ : φ₀.IsUnital)
    (Lm : SheafOfModules.DifferentialGradedModule.{u, u, u} A) (n i : ℤ) :
    smulSheaf (pushforwardObj (semilinearHom α hO hP φ₀ hφ₀) Lm) n i =
      (𝟙 ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj
            (Lm.complex.X n)) ⊗ₘ
          (inverseImageAdjunction α hO hP).unit.app (A'.complex.X i)) ≫
        Stacks.MonoidalGraded.mapMul
          (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))
          (smulSheaf ((restrictScalars φ₀ hφ₀).obj Lm) n i) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp)
    (F := (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj (Lm.complex.X n))
    (G := A'.complex.X i)
    (Q := (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj
      (Lm.complex.X (n + i))) fun V y b => ?_
  refine Eq.trans (smulSheaf_unit (pushforwardObj (semilinearHom α hO hP φ₀ hφ₀) Lm) n i
    V y b) ?_
  refine Eq.trans (congrArg ((Lm.mul n i).app (F.op.obj V) y)
    (semilinearHom_app α hO hP φ₀ hφ₀ i V b)) ?_
  refine Eq.trans (smulSheaf_unit ((restrictScalars φ₀ hφ₀).obj Lm) n i (F.op.obj V) y
    (((inverseImageAdjunction α hO hP).unit.app (A'.complex.X i)).val.app V b)).symm ?_
  refine Eq.trans (congrArg
    (((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).map
      (smulSheaf ((restrictScalars φ₀ hφ₀).obj Lm) n i)).val.app V)
    (isPushforwardMuSections α hO hP (Lm.complex.X n)
      ((inverseImageModules α hO hP).obj (A'.complex.X i)) V y
      (((inverseImageAdjunction α hO hP).unit.app (A'.complex.X i)).val.app V b)).symm) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    (Functor.LaxMonoidal.μ (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))
      (Lm.complex.X n) ((inverseImageModules α hO hP).obj (A'.complex.X i)))
    ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).map
      (smulSheaf ((restrictScalars φ₀ hφ₀).obj Lm) n i)) V _).symm ?_
  refine Eq.trans (congrArg
    ((Stacks.MonoidalGraded.mapMul
        (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))
        (smulSheaf ((restrictScalars φ₀ hφ₀).obj Lm) n i)).val.app V)
    (Stacks.TensorSheafWorld.tensorHom_val_app_tensorSheafUnit Osharp hO V
      (𝟙 ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj
        (Lm.complex.X n)))
      ((inverseImageAdjunction α hO hP).unit.app (A'.complex.X i)) y b).symm) ?_
  exact (SheafOfModules.comp_val_app_apply _ _ V _).symm

omit [RepresentablyFlat F] [F.Final] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify J AddCommGrpCat] [K.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify K AddCommGrpCat] in
/-- The adjoint transpose of an identity morphism is the unit of the adjunction. -/
theorem homEquiv_id (X : SheafOfModules.{u} (toRingCat J Osharp)) :
    (inverseImageAdjunction α hO hP).homEquiv X ((inverseImageModules α hO hP).obj X)
        (𝟙 ((inverseImageModules α hO hP).obj X)) =
      (inverseImageAdjunction α hO hP).unit.app X := by
  rw [Adjunction.homEquiv_unit]
  simp

open SheafOfModules.DifferentialGradedModule in
/-- **A degreewise family out of `f⁻¹M` intertwines the actions of `f⁻¹A'` exactly when its
adjoint transpose intertwines the actions of `A'` on `M` and on `f_*Lm`.** This is
`Stacks.MonoidalGraded.mapMul_comp_iff` at the action of a module, with the unit of the
adjunction on the algebra factor absorbed by `smulSheaf_pushforwardObj`. -/
theorem smulSheaf_transpose_iff (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A) (hφ₀ : φ₀.IsUnital)
    (M : SheafOfModules.DifferentialGradedModule.{u, u, u} A')
    (Lm : SheafOfModules.DifferentialGradedModule.{u, u, u} A)
    (gf : ∀ q : ℤ, (inverseImageModule α hO hP M).complex.X q ⟶
      ((restrictScalars φ₀ hφ₀).obj Lm).complex.X q) (n i : ℤ) :
    (smulSheaf (inverseImageModule α hO hP M) n i ≫ gf (n + i) =
        (gf n ⊗ₘ 𝟙 ((inverseImageAlgebra α hO hP A').complex.X i)) ≫
          smulSheaf ((restrictScalars φ₀ hφ₀).obj Lm) n i) ↔
      (smulSheaf M n i ≫
          (inverseImageAdjunction α hO hP).homEquiv (M.complex.X (n + i))
            (Lm.complex.X (n + i)) (gf (n + i)) =
        ((inverseImageAdjunction α hO hP).homEquiv (M.complex.X n) (Lm.complex.X n) (gf n) ⊗ₘ
            𝟙 (A'.complex.X i)) ≫
          smulSheaf (pushforwardObj (semilinearHom α hO hP φ₀ hφ₀) Lm) n i) := by
  have htensor : (((inverseImageAdjunction α hO hP).homEquiv (M.complex.X n)
            (Lm.complex.X n) (gf n) ⊗ₘ 𝟙 (A'.complex.X i)) ≫
          (𝟙 ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj
              (Lm.complex.X n)) ⊗ₘ
            (inverseImageAdjunction α hO hP).unit.app (A'.complex.X i))) =
      ((inverseImageAdjunction α hO hP).homEquiv (M.complex.X n) (Lm.complex.X n) (gf n) ⊗ₘ
        (inverseImageAdjunction α hO hP).unit.app (A'.complex.X i)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  have hRHS : (((inverseImageAdjunction α hO hP).homEquiv (M.complex.X n)
            (Lm.complex.X n) (gf n) ⊗ₘ
          (inverseImageAdjunction α hO hP).homEquiv (A'.complex.X i)
            ((inverseImageModules α hO hP).obj (A'.complex.X i))
            (𝟙 ((inverseImageModules α hO hP).obj (A'.complex.X i)))) ≫
        Stacks.MonoidalGraded.mapMul
          (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))
          (smulSheaf ((restrictScalars φ₀ hφ₀).obj Lm) n i)) =
      (((inverseImageAdjunction α hO hP).homEquiv (M.complex.X n)
            (Lm.complex.X n) (gf n) ⊗ₘ 𝟙 (A'.complex.X i)) ≫
        smulSheaf (pushforwardObj (semilinearHom α hO hP φ₀ hφ₀) Lm) n i) := by
    refine Eq.trans (congrArg (fun z =>
      ((inverseImageAdjunction α hO hP).homEquiv (M.complex.X n) (Lm.complex.X n) (gf n) ⊗ₘ z) ≫
        Stacks.MonoidalGraded.mapMul
          (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))
          (smulSheaf ((restrictScalars φ₀ hφ₀).obj Lm) n i))
      (homEquiv_id α hO hP (A'.complex.X i))) ?_
    refine Eq.trans (congrArg (fun z => z ≫ Stacks.MonoidalGraded.mapMul
      (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))
      (smulSheaf ((restrictScalars φ₀ hφ₀).obj Lm) n i)) htensor).symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact congrArg (fun z => ((inverseImageAdjunction α hO hP).homEquiv (M.complex.X n)
        (Lm.complex.X n) (gf n) ⊗ₘ 𝟙 (A'.complex.X i)) ≫ z)
      (smulSheaf_pushforwardObj α hO hP φ₀ hφ₀ Lm n i).symm
  have hL : smulSheaf (inverseImageModule α hO hP M) n i =
      Stacks.MonoidalGraded.mapMul (inverseImageModules α hO hP) (smulSheaf M n i) :=
    smulSheaf_inverseImageModule α hO hP M n i
  refine Iff.trans (Iff.of_eq (congrArg (fun z => z ≫ gf (n + i) =
      (gf n ⊗ₘ 𝟙 ((inverseImageAlgebra α hO hP A').complex.X i)) ≫
        smulSheaf ((restrictScalars φ₀ hφ₀).obj Lm) n i) hL)) ?_
  exact Iff.trans (Stacks.MonoidalGraded.mapMul_comp_iff (inverseImageAdjunction α hO hP)
      (smulSheaf M n i) (smulSheaf ((restrictScalars φ₀ hφ₀).obj Lm) n i) (gf n)
      (𝟙 ((inverseImageModules α hO hP).obj (A'.complex.X i))) (gf (n + i)))
    (Iff.of_eq (congrArg (fun z => (smulSheaf M n i ≫
        (inverseImageAdjunction α hO hP).homEquiv (M.complex.X (n + i))
          (Lm.complex.X (n + i)) (gf (n + i))) = z) hRHS))

/-! ### The adjoint transpose of a morphism out of the inverse image -/

section Transpose

open SheafOfModules.DifferentialGradedModule

variable (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A) (hφ₀ : φ₀.IsUnital)
  (M : SheafOfModules.DifferentialGradedModule.{u, u, u} A')
  (N : SheafOfModules.DifferentialGradedModule.{u, u, u} A)

/-- **A degreewise family out of `f⁻¹M` respects the action of `f⁻¹A'` exactly when its adjoint
transpose respects the action of `A'`**, both read on local sections. This is
`smulSheaf_transpose_iff` with each side returned to the `map_mul` axiom of a morphism of right
differential graded modules. -/
theorem map_mul_transpose_iff
    (gf : ∀ q : ℤ, (inverseImageModule α hO hP M).complex.X q ⟶
      ((restrictScalars φ₀ hφ₀).obj N).complex.X q)
    (h : ∀ q : ℤ, M.complex.X q ⟶
      (pushforwardObj (semilinearHom α hO hP φ₀ hφ₀) N).complex.X q)
    (hgh : ∀ q : ℤ, (inverseImageAdjunction α hO hP).homEquiv (M.complex.X q)
      (N.complex.X q) (gf q) = h q) (n i : ℤ) :
    (∀ (W : Dᵒᵖ) (x : ((inverseImageModule α hO hP M).complex.X n).val.obj W)
        (b : ((inverseImageAlgebra α hO hP A').complex.X i).val.obj W),
        (gf (n + i)).val.app W (((inverseImageModule α hO hP M).mul n i).app W x b) =
          (((restrictScalars φ₀ hφ₀).obj N).mul n i).app W ((gf n).val.app W x) b) ↔
      ∀ (V : Cᵒᵖ) (x : (M.complex.X n).val.obj V) (b : (A'.complex.X i).val.obj V),
        (h (n + i)).val.app V ((M.mul n i).app V x b) =
          ((pushforwardObj (semilinearHom α hO hP φ₀ hφ₀) N).mul n i).app V
            ((h n).val.app V x) b := by
  obtain rfl : h = fun q => (inverseImageAdjunction α hO hP).homEquiv (M.complex.X q)
      (N.complex.X q) (gf q) := funext fun q => (hgh q).symm
  exact ((smulSheaf_comp_eq_iff (inverseImageModule α hO hP M) hP
        ((restrictScalars φ₀ hφ₀).obj N) gf n i).symm.trans
      (smulSheaf_transpose_iff α hO hP φ₀ hφ₀ M N gf n i)).trans
    (smulSheaf_comp_eq_iff M hO (pushforwardObj (semilinearHom α hO hP φ₀ hφ₀) N)
      (fun q => (inverseImageAdjunction α hO hP).homEquiv (M.complex.X q) (N.complex.X q)
        (gf q)) n i)

/-- **The degreewise adjoint transpose is a bijection between the morphisms
`f⁻¹M ⟶ res_{φ₀} N` of right differential graded `f⁻¹A'`-modules and the morphisms `M ⟶ f_*N`
of right differential graded `A'`-modules.** In each degree it is the hom-set bijection of the
adjunction between the inverse image and the direct image of sheaves of modules; commutation
with the differentials transports because that bijection is natural, and compatibility with the
two actions is `map_mul_transpose_iff`. -/
noncomputable def transposeEquiv :
    (inverseImageModule α hO hP M ⟶ (restrictScalars φ₀ hφ₀).obj N) ≃
      (M ⟶ pushforwardObj (semilinearHom α hO hP φ₀ hφ₀) N) where
  toFun g :=
    { toHomologicalComplex :=
        { f := fun q => (inverseImageAdjunction α hO hP).homEquiv (M.complex.X q)
            (N.complex.X q) (g.toHomologicalComplex.f q)
          comm' := fun i j _ =>
            (Adjunction.homEquiv_naturality_left_square (inverseImageAdjunction α hO hP)
              (M.complex.d i j) (g.toHomologicalComplex.f j) (g.toHomologicalComplex.f i)
              (N.complex.d i j) (g.toHomologicalComplex.comm i j).symm).symm }
      map_mul := fun n i =>
        (map_mul_transpose_iff α hO hP φ₀ hφ₀ M N
            (fun q => g.toHomologicalComplex.f q)
            (fun q => (inverseImageAdjunction α hO hP).homEquiv (M.complex.X q)
              (N.complex.X q) (g.toHomologicalComplex.f q)) (fun _ => rfl) n i).mp
          fun W x b => g.map_mul n i W x b }
  invFun h :=
    { toHomologicalComplex :=
        { f := fun q => ((inverseImageAdjunction α hO hP).homEquiv (M.complex.X q)
            (N.complex.X q)).symm (h.toHomologicalComplex.f q)
          comm' := fun i j _ =>
            (Adjunction.homEquiv_naturality_right_square (inverseImageAdjunction α hO hP)
              (M.complex.d i j) (h.toHomologicalComplex.f j) (h.toHomologicalComplex.f i)
              (N.complex.d i j) (h.toHomologicalComplex.comm i j).symm).symm }
      map_mul := fun n i =>
        (map_mul_transpose_iff α hO hP φ₀ hφ₀ M N
            (fun q => ((inverseImageAdjunction α hO hP).homEquiv (M.complex.X q)
              (N.complex.X q)).symm (h.toHomologicalComplex.f q))
            (fun q => h.toHomologicalComplex.f q)
            (fun q => ((inverseImageAdjunction α hO hP).homEquiv (M.complex.X q)
              (N.complex.X q)).apply_symm_apply (h.toHomologicalComplex.f q)) n i).mpr
          fun V x b => h.map_mul n i V x b }
  left_inv g := SheafOfModules.DifferentialGradedModule.Hom.ext fun q =>
    ((inverseImageAdjunction α hO hP).homEquiv (M.complex.X q)
      (N.complex.X q)).symm_apply_apply (g.toHomologicalComplex.f q)
  right_inv h := SheafOfModules.DifferentialGradedModule.Hom.ext fun q =>
    ((inverseImageAdjunction α hO hP).homEquiv (M.complex.X q)
      (N.complex.X q)).apply_symm_apply (h.toHomologicalComplex.f q)

/-- The adjoint transpose of a morphism out of the inverse image, in each degree. -/
@[simp]
theorem transposeEquiv_f
    (g : inverseImageModule α hO hP M ⟶ (restrictScalars φ₀ hφ₀).obj N) (q : ℤ) :
    (transposeEquiv α hO hP φ₀ hφ₀ M N g).toHomologicalComplex.f q =
      (inverseImageAdjunction α hO hP).homEquiv (M.complex.X q) (N.complex.X q)
        (g.toHomologicalComplex.f q) :=
  rfl

/-- The adjoint transpose turns composition with a morphism on the target into composition with
its direct image. -/
theorem transposeEquiv_comp (N' : SheafOfModules.DifferentialGradedModule.{u, u, u} A)
    (g : inverseImageModule α hO hP M ⟶ (restrictScalars φ₀ hφ₀).obj N) (h : N ⟶ N') :
    transposeEquiv α hO hP φ₀ hφ₀ M N' (g ≫ (restrictScalars φ₀ hφ₀).map h) =
      transposeEquiv α hO hP φ₀ hφ₀ M N g ≫
        pushforwardMap (semilinearHom α hO hP φ₀ hφ₀) h :=
  SheafOfModules.DifferentialGradedModule.Hom.ext fun q =>
    Adjunction.homEquiv_naturality_right (inverseImageAdjunction α hO hP)
      (g.toHomologicalComplex.f q) (h.toHomologicalComplex.f q)

end Transpose

/-! ### The universal property of the pullback -/

section Universal

open SheafOfModules.DifferentialGradedModule

variable (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A) (hφ₀ : φ₀.IsUnital)

/-- The relative tensor product with `A`, read as a differential graded `(f⁻¹A', A)`-bimodule
through `φ₀`, as the tensor product functor datum of
[Stacks, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE): the pullback is its value at the
inverse image. -/
noncomputable def pullbackTensorFunctorData :
    SheafOfModules.TensorFunctorData (inverseImageAlgebra α hO hP A') A
      (SheafOfModules.DifferentialGradedAlgebra.Hom.toBimodule φ₀ hφ₀) :=
  SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight
    (pullbackBimodule α hO hP φ₀ hφ₀)

/-- The tensor product functor of `pullbackTensorFunctorData` sends `K` to the relative tensor
product of `K` with the bimodule `pullbackBimodule`. -/
@[simp]
theorem pullbackTensorFunctorData_functor_obj
    (K : SheafOfModules.DifferentialGradedModule.{u, u, u}
      (inverseImageAlgebra α hO hP A')) :
    (pullbackTensorFunctorData α hO hP φ₀ hφ₀).functor.obj K =
      SheafOfModules.RelativeTensor.dgTensorRight K (pullbackBimodule α hO hP φ₀ hφ₀) :=
  rfl

variable (M : SheafOfModules.DifferentialGradedModule.{u, u, u} A')
  (N : SheafOfModules.DifferentialGradedModule.{u, u, u} A)

/-- **The universal property of the pullback `f^*M = f⁻¹M ⊗_{f⁻¹A'} A`**: the morphisms of right
differential graded `A`-modules out of `f^*M` are the `φ`-semilinear maps out of `M`, where `φ`
is the structure map `φ₀` read as a semilinear homomorphism `A' ⟶ f_*A` along `F`.

It is the composite of three bijections: extension of scalars along `φ₀` is left adjoint to
restriction of scalars, the degreewise adjoint transpose `transposeEquiv` moves a morphism out of
the inverse image to a morphism into the direct image, and a morphism into the direct image is a
semilinear map. -/
noncomputable def pullbackHomEquiv :
    (pullbackObj α hO hP φ₀ hφ₀ M ⟶ N) ≃
      SemilinearHom (semilinearHom α hO hP φ₀ hφ₀) M N :=
  ((extensionRestrictionHomEquiv φ₀ hφ₀ (pullbackTensorFunctorData α hO hP φ₀ hφ₀)
        (inverseImageModule α hO hP M) N).trans
      (transposeEquiv α hO hP φ₀ hφ₀ M N)).trans
    (semilinearHomEquiv (semilinearHom α hO hP φ₀ hφ₀) M N).symm

/-- **The universal property is natural in the target**: a morphism out of the pullback composed
with a morphism of right differential graded `A`-modules corresponds to the semilinear map
postcomposed with it. -/
theorem pullbackHomEquiv_comp (N' : SheafOfModules.DifferentialGradedModule.{u, u, u} A)
    (g : pullbackObj α hO hP φ₀ hφ₀ M ⟶ N) (h : N ⟶ N') :
    pullbackHomEquiv α hO hP φ₀ hφ₀ M N' (g ≫ h) =
      (pullbackHomEquiv α hO hP φ₀ hφ₀ M N g).postcomp h := by
  have hext : extensionRestrictionHomEquiv φ₀ hφ₀
        (pullbackTensorFunctorData α hO hP φ₀ hφ₀) (inverseImageModule α hO hP M) N'
        (g ≫ h) =
      extensionRestrictionHomEquiv φ₀ hφ₀ (pullbackTensorFunctorData α hO hP φ₀ hφ₀)
          (inverseImageModule α hO hP M) N g ≫ (restrictScalars φ₀ hφ₀).map h :=
    (congrArg (fun z => extensionUnit φ₀ hφ₀ (pullbackTensorFunctorData α hO hP φ₀ hφ₀)
          (inverseImageModule α hO hP M) ≫ z)
        ((restriction φ₀ hφ₀).map_comp g h)).trans (Category.assoc _ _ _).symm
  refine Eq.trans (congrArg (fun z =>
    (semilinearHomEquiv (semilinearHom α hO hP φ₀ hφ₀) M N').symm
      (transposeEquiv α hO hP φ₀ hφ₀ M N' z)) hext) ?_
  refine Eq.trans (congrArg ((semilinearHomEquiv (semilinearHom α hO hP φ₀ hφ₀) M N').symm)
    (transposeEquiv_comp α hO hP φ₀ hφ₀ M N N' _ h)) ?_
  exact SemilinearHom.ext fun _ _ _ => rfl

/-- **The unit of the pullback**: the `φ`-semilinear map `M ⟶ f^*M` corresponding to the
identity of `f^*M`. On local sections it is `x ↦ x ⊗ 1`, read through the unit of the adjunction
between the inverse image and the direct image of sheaves of modules. -/
noncomputable def pullbackUnit :
    SemilinearHom (semilinearHom α hO hP φ₀ hφ₀) M (pullbackObj α hO hP φ₀ hφ₀ M) :=
  pullbackHomEquiv α hO hP φ₀ hφ₀ M (pullbackObj α hO hP φ₀ hφ₀ M)
    (𝟙 (pullbackObj α hO hP φ₀ hφ₀ M))

/-- **`f^*M = f⁻¹M ⊗_{f⁻¹A'} A` is the pullback of `M`**: its unit exhibits it as the pullback in
the sense of `SheafOfModules.DifferentialGradedModule.IsPullback`, so every `φ`-semilinear map
out of `M` factors uniquely through the unit by a morphism of right differential graded
`A`-modules. -/
noncomputable def isPullback_pullbackUnit :
    IsPullback (pullbackUnit α hO hP φ₀ hφ₀ M) :=
  IsPullback.ofHomEquiv (pullbackHomEquiv α hO hP φ₀ hφ₀ M)
    fun _ _ g h => pullbackHomEquiv_comp α hO hP φ₀ hφ₀ M _ _ g h

end Universal

/-! ### The pullback functor and its adjunction -/

section Data

open SheafOfModules.DifferentialGradedModule

variable (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A) (hφ₀ : φ₀.IsUnital)

/-- **The pullback of every right differential graded `A'`-module at once**, as the datum
`SheafOfModules.DifferentialGradedModule.PullbackData`: the construction
`f^*M = f⁻¹M ⊗_{f⁻¹A'} A`, its unit, and the universal property of the unit. -/
noncomputable def pullbackData : PullbackData (semilinearHom α hO hP φ₀ hφ₀) where
  obj M := pullbackObj α hO hP φ₀ hφ₀ M
  unit M := pullbackUnit α hO hP φ₀ hφ₀ M
  isPullback M := isPullback_pullbackUnit α hO hP φ₀ hφ₀ M

/-- The object of `pullbackData` at `M` is the pullback `pullbackObj`. -/
@[simp]
theorem pullbackData_obj (M : SheafOfModules.DifferentialGradedModule.{u, u, u} A') :
    (pullbackData α hO hP φ₀ hφ₀).obj M = pullbackObj α hO hP φ₀ hφ₀ M :=
  rfl

/-- The unit of `pullbackData` at `M` is `pullbackUnit`. -/
@[simp]
theorem pullbackData_unit (M : SheafOfModules.DifferentialGradedModule.{u, u, u} A') :
    (pullbackData α hO hP φ₀ hφ₀).unit M = pullbackUnit α hO hP φ₀ hφ₀ M :=
  rfl

/-- **The pullback functor `f^* : Mod^dg(A', d) ⥤ Mod^dg(A, d)`**. On an object it is
`f^*M = f⁻¹M ⊗_{f⁻¹A'} A`; on a morphism it is the unique morphism of the pullbacks compatible
with the two units, so the functor is determined by the universal property. -/
noncomputable def pullbackFunctor :
    SheafOfModules.DifferentialGradedModule.{u, u, u} A' ⥤
      SheafOfModules.DifferentialGradedModule.{u, u, u} A :=
  (pullbackData α hO hP φ₀ hφ₀).functor

/-- The pullback functor sends `M` to `f^*M = pullbackObj`. -/
@[simp]
theorem pullbackFunctor_obj (M : SheafOfModules.DifferentialGradedModule.{u, u, u} A') :
    (pullbackFunctor α hO hP φ₀ hφ₀).obj M = pullbackObj α hO hP φ₀ hφ₀ M :=
  rfl

/-- The pullback functor sends a morphism `g` to the morphism of pullbacks induced by
`pullbackData`. -/
@[simp]
theorem pullbackFunctor_map {M M₂ : SheafOfModules.DifferentialGradedModule.{u, u, u} A'}
    (g : M ⟶ M₂) :
    (pullbackFunctor α hO hP φ₀ hφ₀).map g = (pullbackData α hO hP φ₀ hφ₀).map g :=
  rfl

/-- **The unit of the pullback is natural**: composing the unit of `M` with `f^*g` is the same as
precomposing the unit of `M₂` with `g`. -/
theorem pullbackUnit_postcomp_map
    {M M₂ : SheafOfModules.DifferentialGradedModule.{u, u, u} A'} (g : M ⟶ M₂) :
    (pullbackUnit α hO hP φ₀ hφ₀ M).postcomp ((pullbackFunctor α hO hP φ₀ hφ₀).map g) =
      (pullbackUnit α hO hP φ₀ hφ₀ M₂).precomp g :=
  (pullbackData α hO hP φ₀ hφ₀).unit_postcomp_map g

/-- **The pullback is left adjoint to the direct image** on sheaves of differential graded
modules along a morphism of small ringed sites. -/
noncomputable def pullbackPushforwardAdjunction :
    pullbackFunctor α hO hP φ₀ hφ₀ ⊣ pushforwardFunctor (semilinearHom α hO hP φ₀ hφ₀) :=
  SheafOfModules.DifferentialGradedModule.pullbackPushforwardAdjunction
    (pullbackData α hO hP φ₀ hφ₀)

end Data

end Stacks.DifferentialGradedPullbackConstruction

end
