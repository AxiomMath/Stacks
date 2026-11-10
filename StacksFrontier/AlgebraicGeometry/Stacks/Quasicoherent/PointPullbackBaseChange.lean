module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullback
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Descent
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebraLiftedPresentation
public import StacksFrontier.RingTheory.Descent.EqualizerDescent

/-!
# Base change of the pullback of quasi-coherent modules to a point

Let `𝒳` be an algebraic stack and `φ : y ⟶ x` a morphism of `𝒳` between points lying over
affine schemes `Spec T` and `Spec R`, over a ring map `g : R → T`; in the 2-Yoneda description of
points this is a commutative triangle `Spec T ⟶ Spec R ⟶ 𝒳`.  Restriction along `φ` gives
`M(x) ⟶ M(y)` for every quasi-coherent module `M`, hence a base change map
`T ⊗_R M(x) ⟶ M(y)`.  Since `M` is quasi-coherent and both points lie over affine schemes it is
bijective (`AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`),
and it is compatible with the tensor structures.  So pulling back to a point commutes with base
change as tensor functors:

`(Spec T ⟶ Spec R ⟶ 𝒳)^* ≅ T ⊗_R (Spec R ⟶ 𝒳)^*`.

This is how the pullback functors of Stacks 0GRP and 0GRQ behave along morphisms of affine schemes;
in the proof of Stacks 0GRQ it compares the functors over `Spec C` and `Spec(C ⊗_B C)`.

The base change map is first an `A`-linear statement for the rings `A = 𝒪_𝒳(x)` and
`A' = 𝒪_𝒳(y)` of sections, and is transported to `R ≅ A`, `T ≅ A'` by
`LinearMap.bijective_liftBaseChange_of_bijective_algebraMap`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.pointPullbackRestriction`: the restriction maps
  `f_x^* ⟶ f_y^*` as `R`-linear maps, a monoidal natural transformation.
* `AlgebraicGeometry.Stack.AlgebraicStacks.pointPullbackBaseChangeIso`: the isomorphism of tensor
  functors `T ⊗_R f_x^*(-) ≅ f_y^*(-)`.

## Main results

* `LinearMap.bijective_liftBaseChange_of_bijective_algebraMap`: base change along a ring map is
  base change along any isomorphic ring map.
* `AlgebraicGeometry.Stack.AlgebraicStacks.bijective_pointPullbackBaseChange_app`.

## References

* [Stacks Project, Tag 0GRP](https://stacks.math.columbia.edu/tag/0GRP)
* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Functor.LaxMonoidal
open scoped TensorProduct

universe u w

/-- Two additive maps out of a tensor product agree if they agree on pure tensors. -/
private theorem tensorProduct_funext {R M N P F G : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [FunLike F (M ⊗[R] N) P]
    [FunLike G (M ⊗[R] N) P] [AddMonoidHomClass F (M ⊗[R] N) P] [AddMonoidHomClass G (M ⊗[R] N) P]
    (f : F) (g : G) (h : ∀ m n, f (m ⊗ₜ n) = g (m ⊗ₜ n)) : (f : M ⊗[R] N → P) = g := by
  funext z
  induction z using TensorProduct.inductionOn with
  | tmul m n => exact h m n
  | add z z' hz hz' => simp only [map_add, hz, hz']

namespace LinearMap

variable {R T A A' : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing A']
  [Algebra R T] [Algebra R A] [Algebra A A'] [Algebra T A'] [Algebra R A']
  [IsScalarTower R A A'] [IsScalarTower R T A']
  {N N' : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  [AddCommGroup N'] [Module R N'] [Module T N'] [Module A N'] [Module A' N']
  [IsScalarTower R T N'] [IsScalarTower T A' N'] [IsScalarTower A A' N'] [IsScalarTower R A N']
  [IsScalarTower R A' N']

/-- **Base change along isomorphic rings.**  Let `R → A` be surjective and `T → A'` bijective,
in a commutative square of rings `R → T → A'`, `R → A → A'`.  If an `A`-linear map `ρ : N → N'`
exhibits the `A'`-module `N'` as the base change of `N` along `A → A'`, then `ρ`, read as an
`R`-linear map, exhibits the `T`-module `N'` as the base change of `N` along `R → T`. -/
theorem bijective_liftBaseChange_of_bijective_algebraMap
    (hA : Function.Surjective (algebraMap R A)) (hA' : Function.Bijective (algebraMap T A'))
    {ρ : N →ₗ[A] N'} (hρ : Function.Bijective (ρ.liftBaseChange A')) :
    Function.Bijective ((ρ.restrictScalars R).liftBaseChange T) := by
  have h₀ : IsBaseChange A (LinearMap.id : N →ₗ[R] N) :=
    IsBaseChange.of_bijective_of_surjective_algebraMap hA Function.bijective_id
  let e : T ≃ₗ[R] A' :=
    LinearEquiv.ofBijective (IsScalarTower.toAlgHom R T A').toLinearMap hA'
  have hfun : ((ρ.restrictScalars R).liftBaseChange T : T ⊗[R] N → N') =
      (((ρ.restrictScalars R).comp LinearMap.id).liftBaseChange A').restrictScalars R ∘ₗ
        (LinearEquiv.rTensor N e).toLinearMap :=
    tensorProduct_funext _ _ fun t n => (algebraMap_smul A' t (ρ n)).symm
  rw [hfun]
  exact (h₀.comp (Stacks.FlatSectionsDescent.isBaseChange_of_bijective_liftBaseChange ρ
    hρ)).bijective_liftBaseChange.comp (LinearEquiv.rTensor N e).bijective

end LinearMap

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat
attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric
attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS) {R T : Type u} [CommRing R] [CommRing T] (g : R →+* T)
  {x y : 𝒳.val.val.obj}
  (e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x) ≅ Spec (CommRingCat.of R))
  (ey : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y) ≅ Spec (CommRingCat.of T))
  (φ : y ⟶ x)
  (hφ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ) ≫ e.hom =
    ey.hom ≫ Spec.map (CommRingCat.ofHom g))

include hφ in
/-- Restriction along a morphism `φ : y ⟶ x` of points lying over `Spec T ⟶ Spec R` carries
`R ⟶ 𝒪_𝒳(x)` to `T ⟶ 𝒪_𝒳(y)`. -/
theorem fppfStructurePresheaf_map_pointRingHom_of_comp (r : R) :
    (fppfStructurePresheaf B S hS 𝒳).map φ.op (pointRingHom B S hS 𝒳 x e r) =
      pointRingHom B S hS 𝒳 y ey (g r) := by
  have key : e.hom.op ≫ ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ)).op =
      (Spec.map (CommRingCat.ofHom g)).op ≫ ey.hom.op := by
    rw [← op_comp, ← op_comp, hφ]
  change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ)).op)
      ((Scheme.Γ.map e.hom.op) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
    (Scheme.Γ.map ey.hom.op) ((Scheme.ΓSpecIso (CommRingCat.of T)).inv (g r))
  refine (ConcreteCategory.comp_apply (Scheme.Γ.map e.hom.op)
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ)).op) _).symm.trans ?_
  refine (congrArg (fun ψ : Scheme.Γ.obj (op (Spec (CommRingCat.of R))) ⟶
      Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y))) =>
        ψ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
      ((Scheme.Γ.map_comp _ _).symm.trans ((congrArg Scheme.Γ.map key).trans
        (Scheme.Γ.map_comp _ _)))).trans ?_
  refine (ConcreteCategory.comp_apply (Scheme.Γ.map (Spec.map (CommRingCat.ofHom g)).op)
    (Scheme.Γ.map ey.hom.op) _).trans ?_
  exact congrArg (Scheme.Γ.map ey.hom.op)
    (congrArg (fun k : CommRingCat.of R ⟶ _ => k r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))).symm

include hφ in
/-- `R ⟶ T ⟶ 𝒪_𝒳(y)` is `R ⟶ 𝒪_𝒳(x)` followed by restriction along `φ`. -/
theorem pointRingHom_comp_eq_comp :
    (pointRingHom B S hS 𝒳 y ey).comp g =
      ((Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        (fppfStructurePresheaf B S hS 𝒳)).map φ.op).hom.comp (pointRingHom B S hS 𝒳 x e) :=
  RingHom.ext fun r => (fppfStructurePresheaf_map_pointRingHom_of_comp B S hS 𝒳 g e ey φ hφ r).symm

/-- The restriction maps `M(x) ⟶ M(y)` along a morphism `φ : y ⟶ x` of points lying over
`Spec T ⟶ Spec R`, as a natural transformation `f_x^* ⟶ f_y^*` of functors to `R`-modules. -/
def pointPullbackRestriction :
    pointPullback B S hS 𝒳 x e ⟶ pointPullback B S hS 𝒳 y ey ⋙ ModuleCat.restrictScalars g where
  app M := (ModuleCat.restrictScalars (pointRingHom B S hS 𝒳 x e)).map
      ((modulesPresheaf B S hS 𝒳 M).map φ.op) ≫
    (ModuleCat.restrictScalarsComp'App (pointRingHom B S hS 𝒳 x e)
      ((Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        (fppfStructurePresheaf B S hS 𝒳)).map φ.op).hom ((pointRingHom B S hS 𝒳 y ey).comp g)
      (pointRingHom_comp_eq_comp B S hS 𝒳 g e ey φ hφ)
      ((modulesPresheaf B S hS 𝒳 M).obj (op y))).inv ≫
    (ModuleCat.restrictScalarsComp'App g (pointRingHom B S hS 𝒳 y ey)
      ((pointRingHom B S hS 𝒳 y ey).comp g) rfl ((modulesPresheaf B S hS 𝒳 M).obj (op y))).hom
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext fun m =>
    (PresheafOfModules.naturality_apply f.hom.val φ.op m).symm)

/-- The component of `pointPullbackRestriction` is restriction along `φ`. -/
theorem pointPullbackRestriction_app_apply (M : quasicoherentModules B S hS 𝒳)
    (m : (pointPullback B S hS 𝒳 x e).obj M) :
    ((pointPullbackRestriction B S hS 𝒳 g e ey φ hφ).app M).hom m =
      (modulesPresheaf B S hS 𝒳 M).map φ.op m :=
  rfl

/-- The restriction along a morphism of points is a monoidal natural transformation. -/
instance isMonoidal_pointPullbackRestriction :
    NatTrans.IsMonoidal (pointPullbackRestriction B S hS 𝒳 g e ey φ hφ) where
  unit := by
    refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
    simp only [Functor.LaxMonoidal.comp_ε, ModuleCat.hom_comp, LinearMap.comp_apply]
    refine (congrArg ((pointPullbackRestriction B S hS 𝒳 g e ey φ hφ).app (𝟙_ _)).hom
      (ModuleCat.restrictScalars_η (pointRingHom B S hS 𝒳 x e) r)).trans ?_
    refine (fppfStructurePresheaf_map_pointRingHom_of_comp B S hS 𝒳 g e ey φ hφ r).trans ?_
    refine Eq.trans ?_ (congrArg (ε (pointPullback B S hS 𝒳 y ey)).hom
      (ModuleCat.restrictScalars_η g r)).symm
    exact (ModuleCat.restrictScalars_η (pointRingHom B S hS 𝒳 y ey) (g r)).symm
  tensor M N := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m n => ?_
    simp only [Functor.LaxMonoidal.comp_μ, ModuleCat.hom_comp, LinearMap.comp_apply,
      μ_pointPullback]
    rw [ModuleCat.MonoidalCategory.tensorHom_tmul, pointPullbackμ_tmul]
    refine (PresheafOfModules.naturality_apply
      (Stacks.SheafOfModules.TensorSheafification.toSheafify
      (fppfStructurePresheaf B S hS 𝒳) (fppfStructurePresheaf_isSheaf B S hS 𝒳)
        (modulesPresheaf B S hS 𝒳 M ⊗ modulesPresheaf B S hS 𝒳 N)) φ.op (m ⊗ₜ n)).symm.trans ?_
    refine Eq.trans ?_ (congrArg (pointPullbackμ B S hS 𝒳 y ey M N).hom
      (ModuleCat.restrictScalars_μ_tmul g ((pointPullback B S hS 𝒳 y ey).obj M)
        ((pointPullback B S hS 𝒳 y ey).obj N)
        (((pointPullbackRestriction B S hS 𝒳 g e ey φ hφ).app M).hom m)
        (((pointPullbackRestriction B S hS 𝒳 g e ey φ hφ).app N).hom n))).symm
    refine Eq.trans ?_ (pointPullbackμ_tmul B S hS 𝒳 y ey M N _ _).symm
    exact congrArg (pointTensorMap B S hS 𝒳 y M N).hom
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul _ _ _)

/-- **The base change map `T ⊗_R M(x) ⟶ M(y)`** along a morphism `φ : y ⟶ x` of points lying
over `Spec T ⟶ Spec R`, `t ⊗ m ↦ t • m|_y`, as a natural transformation
`f_x^* ⋙ (T ⊗_R -) ⟶ f_y^*`: the adjoint of `pointPullbackRestriction` under extension and
restriction of scalars. -/
def pointPullbackBaseChange :
    pointPullback B S hS 𝒳 x e ⋙ ModuleCat.extendScalars g ⟶ pointPullback B S hS 𝒳 y ey :=
  Functor.whiskerRight (pointPullbackRestriction B S hS 𝒳 g e ey φ hφ)
      (ModuleCat.extendScalars g) ≫ (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (pointPullback B S hS 𝒳 y ey)
      (ModuleCat.extendRestrictScalarsAdj g).counit ≫ (Functor.rightUnitor _).hom

/-- The base change map is the adjoint of the restriction map. -/
theorem pointPullbackBaseChange_app (M : quasicoherentModules B S hS 𝒳) :
    (pointPullbackBaseChange B S hS 𝒳 g e ey φ hφ).app M =
      ((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _).symm
        ((pointPullbackRestriction B S hS 𝒳 g e ey φ hφ).app M) := by
  rw [Adjunction.homEquiv_counit]
  simp [pointPullbackBaseChange]

open scoped ChangeOfRings in
/-- The base change map sends `t ⊗ m` to `t • m|_y`. -/
theorem pointPullbackBaseChange_app_tmul (M : quasicoherentModules B S hS 𝒳) (t : T)
    (m : (pointPullback B S hS 𝒳 x e).obj M) :
    ((pointPullbackBaseChange B S hS 𝒳 g e ey φ hφ).app M).hom (t ⊗ₜ[R, g] m) =
      t • (show (pointPullback B S hS 𝒳 y ey).obj M from
        ((pointPullbackRestriction B S hS 𝒳 g e ey φ hφ).app M).hom m) := by
  rw [pointPullbackBaseChange_app]
  let adj := ModuleCat.extendRestrictScalarsAdj g
  have hone : (((adj.homEquiv _ _).symm
      ((pointPullbackRestriction B S hS 𝒳 g e ey φ hφ).app M)).hom ((1 : T) ⊗ₜ[R, g] m)) =
      ((pointPullbackRestriction B S hS 𝒳 g e ey φ hφ).app M).hom m :=
    congrArg (fun k => k m)
      ((adj.homEquiv _ _).apply_symm_apply ((pointPullbackRestriction B S hS 𝒳 g e ey φ hφ).app M))
  exact (congrArg (fun c => ((adj.homEquiv _ _).symm
      ((pointPullbackRestriction B S hS 𝒳 g e ey φ hφ).app M)).hom (c ⊗ₜ[R, g] m))
      (mul_one t).symm).trans ((((adj.homEquiv _ _).symm
        ((pointPullbackRestriction B S hS 𝒳 g e ey φ hφ).app M)).hom.map_smul t
          ((1 : T) ⊗ₜ[R, g] m)).trans (congrArg (fun z => t • z) hone))

/-- The base change map is a monoidal natural transformation. -/
instance isMonoidal_pointPullbackBaseChange :
    NatTrans.IsMonoidal (pointPullbackBaseChange B S hS 𝒳 g e ey φ hφ) := by
  unfold pointPullbackBaseChange
  infer_instance

open scoped ChangeOfRings in
/-- **Quasi-coherent modules base change between points over affine schemes**: the base change
map `T ⊗_R M(x) ⟶ M(y)` is bijective. -/
theorem bijective_pointPullbackBaseChange_app (M : quasicoherentModules B S hS 𝒳) :
    Function.Bijective ((pointPullbackBaseChange B S hS 𝒳 g e ey φ hφ).app M).hom := by
  let A := (fppfStructurePresheaf B S hS 𝒳).obj (op x)
  let A' := (fppfStructurePresheaf B S hS 𝒳).obj (op y)
  let σ : A →+* A' := ((fppfStructurePresheaf B S hS 𝒳).map φ.op).hom
  let N := (modulesPresheaf B S hS 𝒳 M).obj (op x)
  let N' := (modulesPresheaf B S hS 𝒳 M).obj (op y)
  let : Algebra R T := g.toAlgebra
  let : Algebra R A := (pointRingHom B S hS 𝒳 x e).toAlgebra
  let : Algebra A A' := σ.toAlgebra
  let : Algebra T A' := (pointRingHom B S hS 𝒳 y ey).toAlgebra
  let : Algebra R A' := (σ.comp (pointRingHom B S hS 𝒳 x e)).toAlgebra
  have : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R T A' := IsScalarTower.of_algebraMap_eq fun r =>
    fppfStructurePresheaf_map_pointRingHom_of_comp B S hS 𝒳 g e ey φ hφ r
  let : Module R N := Module.compHom N (pointRingHom B S hS 𝒳 x e)
  have : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module A N' := Module.compHom N' σ
  let : Module T N' := Module.compHom N' (pointRingHom B S hS 𝒳 y ey)
  let : Module R N' := Module.compHom N' (σ.comp (pointRingHom B S hS 𝒳 x e))
  have : IsScalarTower T A' N' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A A' N' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R A N' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R A' N' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R T N' := IsScalarTower.of_algebraMap_smul fun r n =>
    congrArg (fun c => c • n)
      (fppfStructurePresheaf_map_pointRingHom_of_comp B S hS 𝒳 g e ey φ hφ r).symm
  let ρA : N →ₗ[A] N' :=
    { toFun := fun m => (modulesPresheaf B S hS 𝒳 M).map φ.op m
      map_add' := fun m m' => map_add _ m m'
      map_smul' := fun a m => (modulesPresheaf B S hS 𝒳 M).map_smul φ.op a m }
  have h₁ : Function.Bijective (ρA.liftBaseChange A') := by
    have hfun : (ρA.liftBaseChange A' : A' ⊗[A] N → N') = fun z =>
        (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u}
          (R := fppfStructurePresheaf B S hS 𝒳) M.obj.val φ.op).hom z := by
      exact tensorProduct_funext _ _ fun a m =>
        (Stacks.PresheafOfModules.restrictionBaseChange_tmul.{u + 1, u, u, u}
          (R := fppfStructurePresheaf B S hS 𝒳) M.obj.val φ.op a m).symm
    rw [hfun]
    exact (ConcreteCategory.isIso_iff_bijective _).1
      (FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite M.obj M.property φ
        (isAffine_point B S hS 𝒳 y ey) (isAffine_point B S hS 𝒳 x e))
  have h₂ := LinearMap.bijective_liftBaseChange_of_bijective_algebraMap
    (bijective_pointRingHom B S hS 𝒳 x e).surjective (bijective_pointRingHom B S hS 𝒳 y ey) h₁
  have hfun : (((pointPullbackBaseChange B S hS 𝒳 g e ey φ hφ).app M).hom :
      T ⊗[R] N → N') = (ρA.restrictScalars R).liftBaseChange T := by
    exact tensorProduct_funext _ _ fun t m =>
      pointPullbackBaseChange_app_tmul B S hS 𝒳 g e ey φ hφ M t m
  rw [show (⇑((pointPullbackBaseChange B S hS 𝒳 g e ey φ hφ).app M).hom :
      _ → _) = _ from hfun]
  exact h₂

/-- The base change transformation `T ⊗_R f_x^*(-) ⟶ f_y^*(-)` is a natural isomorphism. -/
instance isIso_pointPullbackBaseChange :
    IsIso (pointPullbackBaseChange B S hS 𝒳 g e ey φ hφ) :=
  haveI : ∀ M, IsIso ((pointPullbackBaseChange B S hS 𝒳 g e ey φ hφ).app M) := fun M =>
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_pointPullbackBaseChange_app B S hS 𝒳 g e ey φ hφ M)
  NatIso.isIso_of_isIso_app _

/-- **The pullback to a point commutes with base change**: for a morphism `φ : y ⟶ x` of points
of `𝒳` lying over `Spec T ⟶ Spec R`, the isomorphism of tensor functors
`T ⊗_R f_x^*(-) ≅ f_y^*(-)`, `t ⊗ m ↦ t • m|_y`. -/
def pointPullbackBaseChangeIso :
    pointPullback B S hS 𝒳 x e ⋙ ModuleCat.extendScalars g ≅ pointPullback B S hS 𝒳 y ey :=
  asIso (pointPullbackBaseChange B S hS 𝒳 g e ey φ hφ)

/-- The base change isomorphism is an isomorphism of tensor functors. -/
instance isMonoidal_pointPullbackBaseChangeIso :
    NatTrans.IsMonoidal (pointPullbackBaseChangeIso B S hS 𝒳 g e ey φ hφ).hom :=
  isMonoidal_pointPullbackBaseChange B S hS 𝒳 g e ey φ hφ

end AlgebraicGeometry.Stack.AlgebraicStacks

