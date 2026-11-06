module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageAction
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffineCounitBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullbackBaseChange

/-!
# `F(M) ⊗_R C ≅ Γ(U, g^*M) ⊗_A C` and the flatness of `C ⊗_R C` over `C`

Let `g : U ⟶ 𝒳` be an affine 1-morphism from an affine scheme `U = Spec A` to an algebraic stack
and `F : QCoh(𝒪_𝒳) ⥤ Mod_R` a right exact tensor functor commuting with direct sums, with
`C = F(g_{QCoh,*}𝒪_U)` and `A ⟶ C` of Stacks 0GRK. The proof of Stacks 0GRQ compares `F` after
base change to `C` with the pullback to `U` after base change along `A ⟶ C`:

  `F(M) ⊗_R C ≅ F(M) ⊗ F(g_*𝒪_U) ≅ F(M ⊗ g_*𝒪_U) ≅ F(g_*g^*M) ≅ Γ(U, g^*M) ⊗_A C`

(tensorator, projection formula, Stacks 0GRK). The comparison
`AlgebraicGeometry.Stack.AlgebraicStacks.pullbackTensorComparison` is defined directly as the
`C`-linear extension of `F(M) ⟶ F(g_*g^*M) ≅ Γ(U, g^*M) ⊗_A C`; that it is the composite above,
hence an isomorphism, is the `C`-linearity of Stacks 0GRK
(`whiskerLeft_directImageSMul_comp_affineTensorFunctorIso_hom`).

At `M = g_*𝒪_U` it gives `C ⊗_R C ≅ C ⊗_A R'` with `R' = Γ(U, g^*g_*𝒪_U) = Γ(U ×_𝒳 U)`, which is
flat over `A` when `g` is flat (the projection `U ×_𝒳 U ⟶ U` is a base change of `g`), so
`C ⊗_R C` is flat over `C`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.pullbackTensorComparisonIso`:
  `F(-) ⊗_R C ≅ Γ(U, g^*(-)) ⊗_A C`, natural, `C`-linear.
* `AlgebraicGeometry.Stack.AlgebraicStacks.selfTensorEquivBaseChange`: `C ⊗_R C ≅ C ⊗_A R'`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.pointPullbackChartIso`: the pullback along the chart
  point `g(U)` is `Γ(U, g^*(-))`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.pointPullbackTensorIso`: `F(-) ⊗_R C ≅ y^*` for a point
  `y` over `Spec C` above `g(U)`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.flat_globalSections_pullback_structureSheaf`: `R'` is
  flat over `A`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.flat_selfTensor`: `C ⊗_R C` is flat over `C`.

## References

* [Stacks Project, Tag 0GRK](https://stacks.math.columbia.edu/tag/0GRK)
* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct

universe u w

namespace ModuleCat

/-- For an `R`-algebra `C`, the extension of scalars `(extendScalars (algebraMap R C)).obj M`
(built on `C` with `R` acting through `algebraMap`) is `C ⊗[R] M`, `C`-linearly. -/
def extendScalarsAlgebraMapEquiv {R : Type u} {C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R C)).obj M ≃ₗ[C] C ⊗[R] M :=
  let e : (ModuleCat.restrictScalars (algebraMap R C)).obj (ModuleCat.of C C) ≃ₗ[R] C :=
    { AddEquiv.refl C with
      map_smul' := fun r c => (Algebra.smul_def (R := R) (A := C) r (show C from c)).symm }
  let eR := TensorProduct.congr e (LinearEquiv.refl R M)
  { __ := eR.toAddEquiv
    map_smul' := by
      intro s x
      change eR (s • x) = s • eR x
      induction x using TensorProduct.induction_on with
      | zero =>
        exact (congrArg eR (smul_zero s)).trans (eR.map_zero.trans (by rw [map_zero, smul_zero]))
      | add x y hx hy =>
        exact (congrArg eR (smul_add s x y)).trans ((map_add eR _ _).trans
          ((congrArg₂ (· + ·) hx hy).trans (by rw [map_add, smul_add])))
      | tmul a m => rfl }

end ModuleCat

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : IsAffineHom B S hS g)

/-- An `eqToHom` between presheaves of commutative rings, read on the underlying presheaves of
rings, is the same function. -/
theorem eqToHom_app_forget₂_apply {C : Type*} [Category C] {P Q : C ⥤ CommRingCat.{u}}
    (h : P = Q) (X : C) (a : P.obj X) :
    ((eqToHom (congrArg (fun K => K ⋙ forget₂ CommRingCat RingCat) h)).app X).hom a =
      ((eqToHom h).app X).hom a := by
  subst h
  rfl

/-- The ring map `A ⟶ 𝒪_U(r (g U))`: the identification `𝒪_U(U) = 𝒪_𝒳(g U)` followed by the
restriction along the counit `g (r (g U)) ⟶ g U`. -/
def selfFibreRingHom :
    schemeGlobalRing U →+* (AlgebraicStacks.fppfStructureSheaf B S hS
      (schemeStack.{u, w} B S hS U)).obj.obj
        (op ((affineRightAdjoint g hg).obj (g.hom.hom.toFunctor.obj (siteTop.{u, w} U)))) where
  toFun a := ((pushforwardRingHom g hg).hom.app (op (g.hom.hom.toFunctor.obj
    (siteTop.{u, w} U)))).hom (((pullbackRingHom g).hom.app (op (siteTop.{u, w} U))).hom a)
  map_one' := (((pushforwardRingHom g hg).hom.app _).hom.comp
    ((pullbackRingHom g).hom.app (op (siteTop.{u, w} U))).hom).map_one
  map_mul' := (((pushforwardRingHom g hg).hom.app _).hom.comp
    ((pullbackRingHom g).hom.app (op (siteTop.{u, w} U))).hom).map_mul
  map_zero' := (((pushforwardRingHom g hg).hom.app _).hom.comp
    ((pullbackRingHom g).hom.app (op (siteTop.{u, w} U))).hom).map_zero
  map_add' := (((pushforwardRingHom g hg).hom.app _).hom.comp
    ((pullbackRingHom g).hom.app (op (siteTop.{u, w} U))).hom).map_add

/-- `A ⟶ 𝒪_U(r (g U))` read on the structure presheaves of commutative rings. -/
theorem selfFibreRingHom_eq :
    selfFibreRingHom g hg =
      ((pushforwardCommRingHom g hg).app
        (op (g.hom.hom.toFunctor.obj (siteTop.{u, w} U)))).hom.comp
        ((eqToHom (structureSheaf_obj_eq_homFunctor g)).app (op (siteTop.{u, w} U))).hom :=
  RingHom.ext fun a => congrArg ((pushforwardCommRingHom g hg).app
    (op (g.hom.hom.toFunctor.obj (siteTop.{u, w} U)))).hom
      (eqToHom_app_forget₂_apply (structureSheaf_obj_eq_homFunctor g) (op (siteTop.{u, w} U)) a)

/-- `A` acts on `R' = Γ(U, g^*g_*𝒪_U) = 𝒪_U(r (g U))` through
`AlgebraicGeometry.Stack.AlgebraicStacks.selfFibreRingHom`. -/
theorem smul_eq_selfFibreRingHom (a : schemeGlobalRing U)
    (s : (quasicoherentGlobalSections.{u, w} U).obj
      (quasicoherentPullbackObj B S hS g (affineQuasicoherentStructureSheaf g hg))) :
    a • s = @HMul.hMul ((AlgebraicStacks.fppfStructureSheaf B S hS
      (schemeStack.{u, w} B S hS U)).obj.obj
        (op ((affineRightAdjoint g hg).obj (g.hom.hom.toFunctor.obj (siteTop.{u, w} U))))) _ _
          instHMul (selfFibreRingHom g hg a) s :=
  rfl

omit hg in
/-- The point `g(U)` lies over an affine scheme when `U` is affine. -/
theorem isAffine_toScheme_p_obj_siteTop (hU : IsAffineOver B S hS U) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      (𝒳.val.val.p.obj (g.hom.hom.toFunctor.obj (siteTop.{u, w} U)))) :=
  (congrArg (fun T => IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (Functor.congr_obj g.hom.hom.w (siteTop.{u, w} U))).mpr hU

/-- **`A ⟶ 𝒪_U(r (g U)) = Γ(U ×_𝒳 U)` is flat** for `g` flat: it lies over the projection
`U ×_𝒳 U ⟶ U`, a base change of `g`. -/
theorem flat_selfFibreRingHom (hfl : IsFlat B S hS g) (hU : IsAffineOver B S hS U) :
    (selfFibreRingHom g hg).Flat := by
  have h1 : Function.Bijective
      ((eqToHom (structureSheaf_obj_eq_homFunctor g)).app (op (siteTop.{u, w} U))).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hx := isAffine_toScheme_p_obj_siteTop g hU
  have hε := flat_map_affineAdjunction_counit g hg hfl
    (g.hom.hom.toFunctor.obj (siteTop.{u, w} U))
  have hεa := isAffineHom_map_affineAdjunction_counit g hg
    (g.hom.hom.toFunctor.obj (siteTop.{u, w} U))
  have hsrc := @isAffine_of_isAffineHom _ _ _ hεa hx
  have h2 := @HasRingHomProperty.appTop @Flat RingHom.Flat _ _ _ _ hε hsrc hx
  rw [selfFibreRingHom_eq]
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective h1) ?_
  show RingHom.Flat (((Functor.whiskerRight (NatTrans.op (affineAdjunction g hg).counit)
    (AlgebraicStacks.fppfStructureSheaf B S hS 𝒳).obj ≫ eqToHom _).app
      (op (g.hom.hom.toFunctor.obj (siteTop.{u, w} U)))).hom)
  rw [NatTrans.comp_app, CommRingCat.hom_comp]
  exact h2.comp (.of_bijective (ConcreteCategory.bijective_of_isIso _))

/-- **`R' = Γ(U, g^*g_*𝒪_U) = Γ(U ×_𝒳 U)` is flat over `A`** for `g` affine and flat (Stacks
0GRQ, proof). -/
theorem flat_globalSections_pullback_structureSheaf (hfl : IsFlat B S hS g)
    (hU : IsAffineOver B S hS U) :
    Module.Flat (schemeGlobalRing U) ((quasicoherentGlobalSections.{u, w} U).obj
      (quasicoherentPullbackObj B S hS g (affineQuasicoherentStructureSheaf g hg))) := by
  let := (selfFibreRingHom g hg).toAlgebra
  have : Module.Flat (schemeGlobalRing U) ((AlgebraicStacks.fppfStructureSheaf B S hS
      (schemeStack.{u, w} B S hS U)).obj.obj
        (op ((affineRightAdjoint g hg).obj (g.hom.hom.toFunctor.obj (siteTop.{u, w} U))))) :=
    flat_selfFibreRingHom g hg hfl hU
  let e : (quasicoherentGlobalSections.{u, w} U).obj
      (quasicoherentPullbackObj B S hS g (affineQuasicoherentStructureSheaf g hg))
        ≃ₗ[schemeGlobalRing U]
      (AlgebraicStacks.fppfStructureSheaf B S hS (schemeStack.{u, w} B S hS U)).obj.obj
        (op ((affineRightAdjoint g hg).obj (g.hom.hom.toFunctor.obj (siteTop.{u, w} U)))) :=
    { toFun := fun s => s
      invFun := fun s => s
      map_add' := fun _ _ => rfl
      map_smul' := fun a s => smul_eq_selfFibreRingHom g hg a s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Flat.of_linearEquiv e

section Theta

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules
  AlgebraicStacks.quasicoherentSymmetricCategory

/-- The unit `M ⟶ g_* g^* M` of `g^* ⊣ g_*` in `QCoh(𝒪_𝒳)`, as a natural transformation. -/
def affineQuasicoherentUnitNatTrans :
    𝟭 (quasicoherentModules B S hS 𝒳) ⟶
      quasicoherentPullback B S hS g ⋙ affineQuasicoherentPushforward g hg where
  app M := affineQuasicoherentUnit g hg M
  naturality _ _ f := ObjectProperty.hom_ext _
    ((affinePullbackPushforwardAdjunction.{u, w, u} g hg).unit.naturality f.hom)

variable {R : Type u} [CommRing R]
  (F : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.Braided] [F.Additive]
  [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
  (hU : IsAffineOver B S hS U)

/-- **The global-sections form of Stacks 0GRK is `C`-linear**: on
`F(g_{QCoh,*}N) ≅ Γ(U, N) ⊗_A C`, the multiplication by `c` given by the action of
`g_{QCoh,*}𝒪_U` corresponds to the multiplication by `c`. -/
theorem affineTensorFunctorGlobalSectionsIso_hom_app_directImageSMul
    (c : affineTensorAlgebra g hg F) (N : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U))
    (z : (affineQuasicoherentPushforward g hg ⋙ F).obj N) :
    ((affineTensorFunctorGlobalSectionsIso g hg F hU).hom.app N).hom
        (((directImageSMul g hg F c).app N).hom z) =
      @HSMul.hSMul (affineTensorAlgebra g hg F)
        ((ModuleCat.extendScalars (affineTensorRingHom g hg F)).obj
          ((quasicoherentGlobalSections.{u, w} U).obj N)) _ instHSMul c
        (((affineTensorFunctorGlobalSectionsIso g hg F hU).hom.app N).hom z) := by
  have hnat := congrArg (fun φ => φ.hom z)
    ((directImageSMul g hg F c).naturality ((tildeCounitIso.{u, w} U hU).inv.app N))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.comp_map] at hnat
  show ((affineTensorFunctorIso g hg F).hom.app
      ((quasicoherentGlobalSections.{u, w} U).obj N)).hom
      ((F.map ((affineQuasicoherentPushforward g hg).map
        ((tildeCounitIso.{u, w} U hU).inv.app N))).hom
        (((directImageSMul g hg F c).app N).hom z)) = _
  exact (congrArg (fun y => ((affineTensorFunctorIso g hg F).hom.app
    ((quasicoherentGlobalSections.{u, w} U).obj N)).hom y) hnat.symm).trans
      (affineTensorFunctorIso_hom_app_directImageSMul g hg F c _ _)

/-- `F(M) ⟶ Γ(U, g^*M) ⊗_A C` as `R`-modules: `F` of the unit followed by Stacks 0GRK
(global-sections form). -/
def pullbackGlobalSectionsTensorMap :
    F ⟶ quasicoherentPullback B S hS g ⋙ quasicoherentGlobalSections.{u, w} U ⋙
      ModuleCat.extendScalars (affineTensorRingHom g hg F) ⋙
        ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F)) :=
  (Functor.leftUnitor F).inv ≫ Functor.whiskerRight (affineQuasicoherentUnitNatTrans g hg) F ≫
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (quasicoherentPullback B S hS g)
        (affineTensorFunctorGlobalSectionsIso g hg F hU).hom

/-- **The comparison `F(M) ⊗_R C ⟶ Γ(U, g^*M) ⊗_A C`** of Stacks 0GRQ: the `C`-linear extension
of `AlgebraicGeometry.Stack.AlgebraicStacks.pullbackGlobalSectionsTensorMap`. -/
def pullbackTensorComparison :
    F ⋙ ModuleCat.extendScalars (algebraMap R (affineTensorAlgebra g hg F)) ⟶
      quasicoherentPullback B S hS g ⋙ quasicoherentGlobalSections.{u, w} U ⋙
        ModuleCat.extendScalars (affineTensorRingHom g hg F) :=
  Functor.whiskerRight (pullbackGlobalSectionsTensorMap g hg F hU)
      (ModuleCat.extendScalars (algebraMap R (affineTensorAlgebra g hg F))) ≫
    Functor.whiskerLeft (quasicoherentPullback B S hS g ⋙ quasicoherentGlobalSections.{u, w} U ⋙
      ModuleCat.extendScalars (affineTensorRingHom g hg F))
        (ModuleCat.extendRestrictScalarsAdj (algebraMap R (affineTensorAlgebra g hg F))).counit

/-- The comparison on pure tensors: `c ⊗ m ↦ c • κ(F(η) m)`. -/
theorem pullbackTensorComparison_app_tmul (M : quasicoherentModules B S hS 𝒳)
    (c : affineTensorAlgebra g hg F) (m : F.obj M) :
    ((pullbackTensorComparison g hg F hU).app M).hom (c ⊗ₜ[R] m) =
      @HSMul.hSMul (affineTensorAlgebra g hg F)
        ((ModuleCat.extendScalars (affineTensorRingHom g hg F)).obj
          ((quasicoherentGlobalSections.{u, w} U).obj (quasicoherentPullbackObj B S hS g M))) _
        instHSMul c (((affineTensorFunctorGlobalSectionsIso g hg F hU).hom.app
          (quasicoherentPullbackObj B S hS g M)).hom
            ((F.map (affineQuasicoherentUnit g hg M)).hom m)) :=
  rfl

/-- The isomorphism `C ⊗_R F(M) ≅ F(M) ⊗ F(G) ≅ F(M ⊗ G) ≅ F(g_*g^*M) ≅ Γ(g^*M) ⊗_A C` of
`R`-modules (braiding, tensorator, projection formula, Stacks 0GRK), `G = g_{QCoh,*}𝒪_U`. -/
def pullbackTensorFactorization (M : quasicoherentModules B S hS 𝒳) :
    (ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))).obj
        (@ModuleCat.of (affineTensorAlgebra g hg F) _ (affineTensorAlgebra g hg F) _
          Semiring.toModule) ⊗ F.obj M ⟶
      (ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))).obj
        ((ModuleCat.extendScalars (affineTensorRingHom g hg F)).obj
          ((quasicoherentGlobalSections.{u, w} U).obj (quasicoherentPullbackObj B S hS g M))) :=
  (β_ _ (F.obj M)).hom ≫ (F.obj M ◁ (affineTensorAlgebraRestrictIso g hg F).inv) ≫
    Functor.LaxMonoidal.μ F M (affineQuasicoherentStructureSheaf g hg) ≫
      F.map (affineQuasicoherentProjectionMap g hg M) ≫
        (affineTensorFunctorGlobalSectionsIso g hg F hU).hom.app
          (quasicoherentPullbackObj B S hS g M)

/-- The factorization is an isomorphism. -/
instance isIso_pullbackTensorFactorization (M : quasicoherentModules B S hS 𝒳) :
    IsIso (pullbackTensorFactorization g hg F hU M) := by
  unfold pullbackTensorFactorization
  infer_instance

/-- The comparison is the factorization, on elements. -/
theorem pullbackTensorComparison_app_apply (M : quasicoherentModules B S hS 𝒳)
    (z : (ModuleCat.extendScalars (algebraMap R (affineTensorAlgebra g hg F))).obj (F.obj M)) :
    ((pullbackTensorComparison g hg F hU).app M).hom z =
      (pullbackTensorFactorization g hg F hU M).hom z := by
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul c m =>
    refine (pullbackTensorComparison_app_tmul g hg F hU M c m).trans ?_
    refine Eq.trans ?_ (congrArg (fun y => ((affineTensorFunctorGlobalSectionsIso g hg F hU).hom.app
      (quasicoherentPullbackObj B S hS g M)).hom y)
        (map_affineQuasicoherentProjectionMap_μ g hg F M m c).symm)
    exact (affineTensorFunctorGlobalSectionsIso_hom_app_directImageSMul g hg F hU c _ _).symm
  | add x y hx hy =>
    exact ((map_add _ x y).trans (congrArg₂ (· + ·) hx hy)).trans (map_add _ x y).symm

/-- The comparison is bijective. -/
theorem bijective_pullbackTensorComparison_app (M : quasicoherentModules B S hS 𝒳) :
    Function.Bijective ((pullbackTensorComparison g hg F hU).app M).hom := by
  have h : ⇑((pullbackTensorComparison g hg F hU).app M).hom =
      ⇑(pullbackTensorFactorization g hg F hU M).hom :=
    funext (pullbackTensorComparison_app_apply g hg F hU M)
  rw [h]
  exact ConcreteCategory.bijective_of_isIso _

/-- The comparison is an isomorphism. -/
instance isIso_pullbackTensorComparison : IsIso (pullbackTensorComparison g hg F hU) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_pullbackTensorComparison_app g hg F hU M)

/-- **`F(M) ⊗_R C ≅ Γ(U, g^*M) ⊗_A C`, naturally in `M` and `C`-linearly** (Stacks 0GRQ, proof). -/
def pullbackTensorComparisonIso :
    F ⋙ ModuleCat.extendScalars (algebraMap R (affineTensorAlgebra g hg F)) ≅
      quasicoherentPullback B S hS g ⋙ quasicoherentGlobalSections.{u, w} U ⋙
        ModuleCat.extendScalars (affineTensorRingHom g hg F) :=
  asIso (pullbackTensorComparison g hg F hU)

/-- **`C ⊗_R C ≅ C ⊗_A R'` as `C`-modules** (Stacks 0GRQ, proof), `R' = Γ(U, g^*g_*𝒪_U)`: the
comparison at `g_{QCoh,*}𝒪_U`. -/
def selfTensorEquivBaseChange :
    letI := (affineTensorRingHom g hg F).toAlgebra
    (affineTensorAlgebra g hg F ⊗[R] affineTensorAlgebra g hg F) ≃ₗ[affineTensorAlgebra g hg F]
      (affineTensorAlgebra g hg F ⊗[schemeGlobalRing U] ((quasicoherentGlobalSections.{u, w} U).obj
        (quasicoherentPullbackObj B S hS g (affineQuasicoherentStructureSheaf g hg)))) :=
  letI := (affineTensorRingHom g hg F).toAlgebra
  (ModuleCat.extendScalarsAlgebraMapEquiv (C := affineTensorAlgebra g hg F)
      (F.obj (affineQuasicoherentStructureSheaf g hg))).symm ≪≫ₗ
    ((pullbackTensorComparisonIso g hg F hU).app
      (affineQuasicoherentStructureSheaf g hg)).toLinearEquiv ≪≫ₗ
    ModuleCat.extendScalarsAlgebraMapEquiv (C := affineTensorAlgebra g hg F)
      ((quasicoherentGlobalSections.{u, w} U).obj
        (quasicoherentPullbackObj B S hS g (affineQuasicoherentStructureSheaf g hg)))

include hU in
/-- **`C ⊗_R C` is flat over `C`** for `g` flat (Stacks 0GRQ, proof): it is `C ⊗_A R'` with
`R' = Γ(U ×_𝒳 U)` flat over `A`. -/
theorem flat_selfTensor (hfl : IsFlat B S hS g) :
    Module.Flat (affineTensorAlgebra g hg F)
      (affineTensorAlgebra g hg F ⊗[R] affineTensorAlgebra g hg F) := by
  let := (affineTensorRingHom g hg F).toAlgebra
  have := flat_globalSections_pullback_structureSheaf g hg hfl hU
  exact Module.Flat.of_linearEquiv (selfTensorEquivBaseChange g hg F hU)

end Theta

end AlgebraicGeometry.Stack.AlgebraicStacks

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳)

/-- The scheme under the point `g(U)` of `𝒳` is `Spec A`, `A = Γ(U, 𝒪_U)`, for `U` affine. -/
def chartPointIso (hU : IsAffineOver B S hS U) :
    (BigFppfOver.toScheme B S hS).obj
        (𝒳.val.val.p.obj (g.hom.hom.toFunctor.obj (siteTop.{u, w} U))) ≅
      Spec (CommRingCat.of (schemeGlobalRing U)) :=
  eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj
      (Functor.congr_obj g.hom.hom.w (siteTop.{u, w} U))) ≪≫
    @Scheme.isoSpec ((BigFppfOver.toScheme B S hS).obj U) hU

/-- `Γ(Spec Γ(X)) ≅ Γ(T)` along `T = X ≅ Spec Γ(X)` is the transport `eqToHom`. -/
theorem _root_.AlgebraicGeometry.Scheme.ΓSpecIso_symm_trans_mapIso_eqToIso_isoSpec
    {T X : Scheme.{u}}
    (h : T = X) [IsAffine X] :
    ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, ⊤))).symm ≪≫
      Scheme.Γ.mapIso (eqToIso h ≪≫ X.isoSpec).op).hom =
        eqToHom (by subst h; rfl) := by
  cases h
  refine Eq.trans ?_ (eqToHom_refl (CommRingCat.of Γ(T, ⊤)) rfl).symm
  ext a
  show (T.toSpecΓ.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of Γ(T, ⊤))).inv.hom a) = a
  rw [Scheme.toSpecΓ_appTop]
  exact congrArg (fun f => CommRingCat.Hom.hom f a) (Scheme.ΓSpecIso Γ(T, ⊤)).inv_hom_id

/-- The ring map `A ⟶ 𝒪_𝒳(g U)` of the chart point is the identification `𝒪_U(U) = 𝒪_𝒳(g U)`. -/
theorem pointRingHom_chartPointIso (hU : IsAffineOver B S hS U) :
    pointRingHom B S hS 𝒳 (g.hom.hom.toFunctor.obj (siteTop.{u, w} U)) (chartPointIso g hU) =
      ((eqToHom (structureSheaf_obj_eq_homFunctor g)).app (op (siteTop.{u, w} U))).hom := by
  have h := @Scheme.ΓSpecIso_symm_trans_mapIso_eqToIso_isoSpec _ _
    (congrArg (BigFppfOver.toScheme B S hS).obj
      (Functor.congr_obj g.hom.hom.w (siteTop.{u, w} U))) hU
  refine (congrArg CommRingCat.Hom.hom h).trans ?_
  rw [eqToHom_app]
  rfl

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.pointRingHom_chartPointIso` on elements, read on the
structure sheaf of rings. -/
theorem pointRingHom_chartPointIso_apply (hU : IsAffineOver B S hS U) (a : schemeGlobalRing U) :
    pointRingHom B S hS 𝒳 (g.hom.hom.toFunctor.obj (siteTop.{u, w} U)) (chartPointIso g hU) a =
      ((pullbackRingHom g).hom.app (op (siteTop.{u, w} U))).hom a :=
  (congrArg (fun f => f a) (pointRingHom_chartPointIso g hU)).trans
    (eqToHom_app_forget₂_apply (structureSheaf_obj_eq_homFunctor g) (op (siteTop.{u, w} U)) a).symm

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.pointRingHom_chartPointIso` read on the structure
sheaf of rings. -/
theorem pointRingHom_chartPointIso_eq (hU : IsAffineOver B S hS U) :
    (pointRingHom B S hS 𝒳 (g.hom.hom.toFunctor.obj (siteTop.{u, w} U)) (chartPointIso g hU) :
      schemeGlobalRing U →+* (AlgebraicStacks.fppfStructureRingSheaf B S hS 𝒳).obj.obj
        (op (g.hom.hom.toFunctor.obj (siteTop.{u, w} U)))) =
      ((pullbackRingHom g).hom.app (op (siteTop.{u, w} U))).hom :=
  RingHom.ext (pointRingHom_chartPointIso_apply g hU)

/-- **The pullback along the chart point `g(U)` is `Γ(U, g^*(-))`**: `u^* ≅ Γ(U, -) ∘ g^*` as
functors `QCoh(𝒪_𝒳) ⥤ Mod_A`, the identity on sections `M(g U)`. -/
def pointPullbackChartIso (hU : IsAffineOver B S hS U) :
    pointPullback B S hS 𝒳 (g.hom.hom.toFunctor.obj (siteTop.{u, w} U)) (chartPointIso g hU) ≅
      quasicoherentPullback B S hS g ⋙ quasicoherentGlobalSections.{u, w} U :=
  Functor.isoWhiskerLeft (quasicoherentInclusion B S hS 𝒳 ⋙ SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ (op (g.hom.hom.toFunctor.obj (siteTop.{u, w} U))))
      (ModuleCat.restrictScalarsCongr (pointRingHom_chartPointIso_eq g hU))

section Point

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules
  AlgebraicStacks.quasicoherentSymmetricCategory

variable (hg : IsAffineHom B S hS g) {R : Type u} [CommRing R]
  (F : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.Braided] [F.Additive]
  [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
  (hU : IsAffineOver B S hS U) {y : 𝒳.val.val.obj}
  (ey : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y) ≅
    Spec (CommRingCat.of (affineTensorAlgebra g hg F)))
  (ψ : y ⟶ g.hom.hom.toFunctor.obj (siteTop.{u, w} U))
  (hψ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map ψ) ≫ (chartPointIso g hU).hom =
    ey.hom ≫ Spec.map (CommRingCat.ofHom (affineTensorRingHom g hg F)))

/-- **`θ : F(-) ⊗_R C ≅ y^*`** (Stacks 0GRQ, proof) for a point `y` over `Spec C` lying over the
chart point `g(U)` along `Spec C ⟶ Spec A = U`: the comparison
`F(-) ⊗_R C ≅ Γ(U, g^*(-)) ⊗_A C`, then `Γ(U, g^*(-)) = g(U)^*`, then base change along
`A ⟶ C`. -/
def pointPullbackTensorIso :
    F ⋙ ModuleCat.extendScalars (algebraMap R (affineTensorAlgebra g hg F)) ≅
      pointPullback B S hS 𝒳 y ey :=
  pullbackTensorComparisonIso g hg F hU ≪≫
    Functor.isoWhiskerRight (pointPullbackChartIso g hU).symm
      (ModuleCat.extendScalars (affineTensorRingHom g hg F)) ≪≫
    pointPullbackBaseChangeIso B S hS 𝒳 (affineTensorRingHom g hg F) (chartPointIso g hU) ey ψ hψ

end Point

end AlgebraicGeometry.Stack.AlgebraicStacks
