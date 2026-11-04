module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctorUniversalInjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditionsCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeInternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorFlatObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatObjectDetection
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfToEtaleSquares
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearDescUnitor

/-!
# The evaluation of the dual of a coherent module, and the input `hdual` of Stacks 0GRL

Let `𝒳` be an algebraic stack and `𝓕` a coherent `𝒪_𝒳`-module.  Its dual is
`𝓕^∨ = hom(𝓕, 𝒪_𝒳) = Q(SheafHom_{𝒪_𝒳}(𝓕, 𝒪_𝒳))` of Stacks 0GQN
(`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHom`, with `Q` the coherator of
Stacks 0781), a quasi-coherent module, and it carries the evaluation `ev : 𝓕 ⊗ 𝓕^∨ ⟶ 𝒪_𝒳`,
`f ⊗ φ ↦ φ(f)`.  For a global section `s : 𝒪_𝒳 ⟶ 𝓕`, evaluation at `s` is
`s^∨ : 𝓕^∨ ⟶ 𝒪_𝒳`, `φ ↦ φ(s)`.

The proof of Stacks 0GRL shows that `s^∨` is surjective: after pulling back along the faithfully
flat `g : U ⟶ 𝒳` the section `s` splits, so `g^*(s^∨)` is surjective by the compatibility of `hom`
with restriction to `U` (Stacks 0GQS), hence `s^∨` is.  This file proves that argument in the form
in which
`AlgebraicGeometry.Stack.universallyInjective_algebraMap_tensorFunctor_of_coherentGeneration`
consumes it.  The compatibility with restriction is used in the form: over a flat object `y` the
adjunction map `Q(SheafHom(𝓕, 𝒪_𝒳)) ⟶ SheafHom(𝓕, 𝒪_𝒳)` is bijective on sections, because
`SheafHom(𝓕, 𝒪_𝒳)` lies in `LQCoh^fbc(𝒪_𝒳)` (Stacks 0GQN, its membership clause) and the kernel and
cokernel of that map are parasitic (Stacks 0779 (2)); and over an object lying over an affine
scheme the sections of `SheafHom(𝓕, 𝒪_𝒳)` are the linear maps `𝓕(y) ⟶ 𝒪(y)`.  The splitting is the
hypothesis `AlgebraicGeometry.Stack.HasFlatLocalUnitRetractions` on the algebra `G` of that
theorem: over every flat object `y` of `𝒳` lying over an affine scheme there is a faithfully flat
`y' ⟶ y` with `y'` flat over an affine scheme and an `𝒪(y')`-linear retraction of the unit
`η : 𝒪 ⟶ G` on sections over `y'`.  For `G = g_{QCoh,*}𝒪_U` with `g : U ⟶ 𝒳` affine, flat and
surjective it is given by `y' = U ×_𝒳 y` and the multiplication `𝒪(U ×_𝒳 U ×_𝒳 T) ⟶ 𝒪(U ×_𝒳 T)`
along the diagonal.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHomEvaluationBilinear`: the evaluation
  pairing `F × hom(F, G) ⟶ G` on sections, `(f, φ) ↦ ε(φ)(f)`, `ε` the adjunction map of the
  coherator.
* `AlgebraicGeometry.Stack.HasFlatLocalUnitRetractions`: the splitting hypothesis on `G`.

## Main results

* `Stack.AlgebraicStacks.bijective_coheratorAdjunction_counit_app_fppfInternalHom`: the
  adjunction map `hom(F, G) ⟶ SheafHom(F, G)` is bijective on sections over flat objects.
* `AlgebraicGeometry.Stack.exists_dual_evaluation_epi`: the input `hdual` of
  `AlgebraicGeometry.Stack.universallyInjective_algebraMap_tensorFunctor_of_coherentGeneration`,
  from `AlgebraicGeometry.Stack.HasFlatLocalUnitRetractions`.
* `AlgebraicGeometry.Stack.universallyInjective_algebraMap_tensorFunctor_of_unitRetractions`: that
  theorem with `hdual` discharged.

## References

* [Stacks Project, Tag 0GRL](https://stacks.math.columbia.edu/tag/0GRL)
* [Stacks Project, Tag 0GQN](https://stacks.math.columbia.edu/tag/0GQN)
* [Stacks Project, Tag 0GQS](https://stacks.math.columbia.edu/tag/0GQS)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj Opposite

open scoped TensorProduct

universe u w w'

namespace AlgebraicGeometry.RingedSite

universe m u₁ v₁

variable (X : RingedSite.{u₁, v₁, m}) [EssentiallySmall.{m} X.C]
  (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The sections of the internal Hom of Stacks 03EM are `m`-small, read on the underlying presheaf
of abelian groups. -/
instance (priority := high) small_internalHomSheaf_presheaf_obj (U : X.Cᵒᵖ) :
    Small.{m} ((internalHomSheaf X A B).val.presheaf.obj U) :=
  inferInstanceAs (Small.{m} ((internalHomSheaf X A B).val.obj U))

/-- The sections of the internal Hom of Stacks 03EM are `m`-small. -/
instance (priority := high) small_internalHomSheaf_val_obj (U : X.Cᵒᵖ) :
    Small.{m} ((internalHomSheaf X A B).val.obj U) :=
  small_internalHomSheaf_obj X A B U

/-- A section over `U` of the internal Hom `internalHomSheafSmall X A B` at module universe `m`,
read as a section of the internal Hom of Stacks 03EM: a morphism `A|_U ⟶ B|_U` on the slice. -/
abbrev internalHomSheafSmallSection (U : X.Cᵒᵖ) :
    (internalHomSheafSmall X A B).val.obj U ≃+
      (_root_.internalHom X.O.obj (valOf X A) (valOf X B)).obj U :=
  Shrink.addEquiv

/-- **Evaluation of a section of the internal Hom** over `U` at the final object of the slice over
`U`: the `𝒪(U)`-linear map `A(U) ⟶ B(U)` it induces. -/
abbrev internalHomSheafSmallEval (U : X.Cᵒᵖ) (k : (internalHomSheafSmall X A B).val.obj U)
    (a : A.val.obj U) : B.val.obj U :=
  PresheafOfModules.Hom.app (internalHomSheafSmallSection X A B U k) (op (Over.mk (𝟙 U.unop))) a

/-- `internalHomSheafSmallEval` is the evaluation `evalLinear` of the corresponding section of the
internal Hom of Stacks 03EM. -/
theorem internalHomSheafSmallEval_eq_evalLinear (U : X.Cᵒᵖ)
    (k : (internalHomSheafSmall X A B).val.obj U) (a : A.val.obj U) :
    internalHomSheafSmallEval X A B U k a =
      Stacks.PresheafOfModules.InternalHomSections.evalLinear X.O.obj (valOf X A) (valOf X B)
        U.unop (internalHomSheafSmallSection X A B U k) a :=
  rfl

/-- Evaluation of a section of the internal Hom is additive in the section. -/
theorem internalHomSheafSmallEval_add_left (U : X.Cᵒᵖ)
    (k k' : (internalHomSheafSmall X A B).val.obj U) (a : A.val.obj U) :
    internalHomSheafSmallEval X A B U (k + k') a =
      internalHomSheafSmallEval X A B U k a + internalHomSheafSmallEval X A B U k' a := by
  unfold internalHomSheafSmallEval
  rw [map_add]
  rfl

/-- Evaluation of a section of the internal Hom is additive in the argument. -/
theorem internalHomSheafSmallEval_add_right (U : X.Cᵒᵖ)
    (k : (internalHomSheafSmall X A B).val.obj U) (a a' : A.val.obj U) :
    internalHomSheafSmallEval X A B U k (a + a') =
      internalHomSheafSmallEval X A B U k a + internalHomSheafSmallEval X A B U k a' :=
  map_add (PresheafOfModules.Hom.app (internalHomSheafSmallSection X A B U k)
    (op (Over.mk (𝟙 U.unop)))).hom a a'

/-- Evaluation of a section of the internal Hom is `𝒪(U)`-linear in the argument. -/
theorem internalHomSheafSmallEval_smul_right (U : X.Cᵒᵖ)
    (k : (internalHomSheafSmall X A B).val.obj U)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (a : A.val.obj U) :
    internalHomSheafSmallEval X A B U k (r • a) = r • internalHomSheafSmallEval X A B U k a :=
  (PresheafOfModules.Hom.app (internalHomSheafSmallSection X A B U k)
    (op (Over.mk (𝟙 U.unop)))).hom.map_smul r a

/-- Evaluation of a section of the internal Hom is `𝒪(U)`-linear in the section. -/
theorem internalHomSheafSmallEval_smul_left (U : X.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
    (k : (internalHomSheafSmall X A B).val.obj U) (a : A.val.obj U) :
    internalHomSheafSmallEval X A B U (r • k) a = r • internalHomSheafSmallEval X A B U k a := by
  unfold internalHomSheafSmallEval
  have h : internalHomSheafSmallSection X A B U (r • k) =
      r • internalHomSheafSmallSection X A B U k :=
    Stacks.SheafOfModules.shrinkPresheaf_addEquiv_smul.{m, max u₁ v₁} _
      (internalHomSheaf X A B).val U r k
  rw [h]
  exact Stacks.PresheafOfModules.InternalHomSections.smulHom_app_overMk_id X.O.obj (valOf X A)
    (valOf X B) U.unop r (internalHomSheafSmallSection X A B U k) a

/-- Evaluation of sections of the internal Hom commutes with restriction along `g : U ⟶ V`. -/
theorem internalHomSheafSmallEval_map {U V : X.Cᵒᵖ} (g : U ⟶ V)
    (k : (internalHomSheafSmall X A B).val.obj U) (a : A.val.obj U) :
    internalHomSheafSmallEval X A B V ((internalHomSheafSmall X A B).val.map g k) (A.val.map g a) =
      B.val.map g (internalHomSheafSmallEval X A B U k a) := by
  unfold internalHomSheafSmallEval
  have h : internalHomSheafSmallSection X A B V ((internalHomSheafSmall X A B).val.map g k) =
      (_root_.internalHom X.O.obj (valOf X A) (valOf X B)).map g
        (internalHomSheafSmallSection X A B U k) :=
    Stacks.shrinkPresheaf_map_apply.{m, max u₁ v₁} _ g k
  rw [h]
  exact PresheafOfModules.naturality_apply (internalHomSheafSmallSection X A B U k)
    (Over.homMk g.unop (by simp) : Over.mk (𝟙 V.unop ≫ g.unop) ⟶ Over.mk (𝟙 U.unop)).op a

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- Evaluation of a section of `SheafHom_{𝒪_𝒳}(F, G)` over `X` at the final object of the slice
over `X`: the `𝒪(X)`-linear map `F(X) ⟶ G(X)` it induces. -/
abbrev fppfInternalHomEval (F G : Stack.fppfModules B S hS 𝒳) (X : 𝒳.val.val.objᵒᵖ)
    (k : (fppfInternalHom B S hS 𝒳 F G).val.obj X) (f : F.val.obj X) : G.val.obj X :=
  RingedSite.internalHomSheafSmallEval
    (FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf) F G X k f

/-- Over an object lying over an affine scheme, every `𝒪(y)`-linear map `F(y) ⟶ G(y)` out of a
quasi-coherent `F` is the evaluation of a section of `SheafHom_{𝒪_𝒳}(F, G)`
(`AlgebraicGeometry.FibredSite.bijective_evalLinear_of_isQuasicoherentOnSite`). -/
theorem exists_fppfInternalHomEval_eq (F G : Stack.fppfModules B S hS 𝒳)
    (hF : F.IsQuasicoherentOnSite) {y : 𝒳.val.val.obj}
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)))
    (ψ : F.val.obj (op y) →+ G.val.obj (op y))
    (hψ : ∀ (r : (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf).obj.obj (op y)) (f : F.val.obj (op y)),
      ψ (r • f) = r • ψ f) :
    ∃ k : (fppfInternalHom B S hS 𝒳 F G).val.obj (op y),
      ∀ f, fppfInternalHomEval F G (op y) k f = ψ f := by
  obtain ⟨α, hα⟩ := (FibredSite.bijective_evalLinear_of_isQuasicoherentOnSite B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F G hF hy).2
    { toFun := ψ, map_add' := map_add ψ, map_smul' := fun r f ↦ hψ r f }
  let e := RingedSite.internalHomSheafSmallSection (FibredSite.ringedSite B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids .fppf) F G (op y)
  refine ⟨e.symm α, fun f ↦ ?_⟩
  refine (RingedSite.internalHomSheafSmallEval_eq_evalLinear (FibredSite.ringedSite B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf) F G (op y) _ f).trans ?_
  exact (congrArg (fun α' ↦ Stacks.PresheafOfModules.InternalHomSections.evalLinear
    (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj F.val G.val
    y α' f) (e.apply_symm_apply α)).trans (LinearMap.congr_fun hα f)

/-- **The adjunction map of the coherator is bijective over flat objects on `SheafHom(F, G)`.**
For `F` of finite presentation and `G` quasi-coherent, `SheafHom_{𝒪_𝒳}(F, G)` lies in
`LQCoh^fbc(𝒪_𝒳)` (Stacks 0GQN), so the kernel and cokernel of `hom(F, G) ⟶ SheafHom(F, G)` are
parasitic (Stacks 0779 (2)) and the map is bijective on the sections over a flat object. -/
theorem bijective_coheratorAdjunction_counit_app_fppfInternalHom
    (F G : Stack.fppfModules B S hS 𝒳) [F.IsFinitePresentationOnSite]
    (hG : G.IsQuasicoherentOnSite) (y : 𝒳.val.val.obj) (hy : flatObject B S hS 𝒳.val y) :
    Function.Bijective (((coheratorAdjunction B S hS 𝒳).counit.app
      (fppfInternalHom B S hS 𝒳 F G)).val.app (op y)) := by
  have hK := lqcohSheafFbcFppfModules_fppfInternalHom_of_isQuasicoherentOnSite B
    (associatedBigEtaleSite B) rfl S hS 𝒳 F G hG
  have hp := isParasitic_kernel_and_cokernel_coheratorAdjunction_counit B S hS 𝒳
    (associatedBigEtaleSite B) rfl _ hK
  exact isIso_app_of_isParasitic_kernel_cokernel B S hS _ hp.1 hp.2 y hy

/-- **The evaluation pairing** `F × hom(F, G) ⟶ G`, `(f, φ) ↦ ε(φ)(f)`, with
`ε : hom(F, G) = Q(SheafHom(F, G)) ⟶ SheafHom(F, G)` the adjunction map of the coherator and a
section of `SheafHom(F, G)` evaluated at the final object of each slice. -/
def quasicoherentHomEvaluationBilinear (F G : Stack.fppfModules B S hS 𝒳) :
    Stacks.BilinearMap F.val (quasicoherentHom B S hS 𝒳 F G).obj.val G.val where
  app X := AddMonoidHom.mk' (fun f ↦ AddMonoidHom.mk' (fun d ↦ fppfInternalHomEval F G X
      (((coheratorAdjunction B S hS 𝒳).counit.app (fppfInternalHom B S hS 𝒳 F G)).val.app X d) f)
      (fun d d' ↦ (congrArg (fun k ↦ fppfInternalHomEval F G X k f) (map_add _ d d')).trans
        (RingedSite.internalHomSheafSmallEval_add_left
          (FibredSite.ringedSite B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .fppf) F G X _ _ f)))
    (fun f f' ↦ AddMonoidHom.ext fun d ↦ RingedSite.internalHomSheafSmallEval_add_right
          (FibredSite.ringedSite B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .fppf) F G X _ f f')
  map_smul_left X r f d := RingedSite.internalHomSheafSmallEval_smul_right
          (FibredSite.ringedSite B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .fppf) F G X _ r f
  map_smul_right X r f d :=
    (congrArg (fun k ↦ fppfInternalHomEval F G X k f) (map_smul _ r d)).trans
      (RingedSite.internalHomSheafSmallEval_smul_left
          (FibredSite.ringedSite B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .fppf) F G X r _ f)
  naturality {X Y} g f d := by
    have hn := congrArg (fun φ ↦ φ d) (congrArg ConcreteCategory.hom
      (((coheratorAdjunction B S hS 𝒳).counit.app (fppfInternalHom B S hS 𝒳 F G)).val.naturality
        g))
    change ((coheratorAdjunction B S hS 𝒳).counit.app (fppfInternalHom B S hS 𝒳 F G)).val.app Y
        ((quasicoherentHom B S hS 𝒳 F G).obj.val.map g d) = (fppfInternalHom B S hS 𝒳 F G).val.map g
        (((coheratorAdjunction B S hS 𝒳).counit.app (fppfInternalHom B S hS 𝒳 F G)).val.app X d)
        at hn
    change G.val.map g (fppfInternalHomEval F G X
        (((coheratorAdjunction B S hS 𝒳).counit.app (fppfInternalHom B S hS 𝒳 F G)).val.app X d)
          f) =
      fppfInternalHomEval F G Y (((coheratorAdjunction B S hS 𝒳).counit.app
        (fppfInternalHom B S hS 𝒳 F G)).val.app Y ((quasicoherentHom B S hS 𝒳 F G).obj.val.map g d))
        (F.val.map g f)
    rw [hn]
    exact (RingedSite.internalHomSheafSmallEval_map
          (FibredSite.ringedSite B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .fppf) F G g _ f).symm

end AlgebraicGeometry.Stack.AlgebraicStacks

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Restriction of a quasi-coherent module along a faithfully flat morphism of objects lying
over affine schemes is injective on sections**: it is the base change `m ↦ 1 ⊗ m` followed by
the bijective comparison of a cartesian module. -/
theorem injective_map_of_faithfullyFlat
    {M : Stack.fppfModules B S hS 𝒳}
    (hM : M.IsQuasicoherentOnSite) {y y' : 𝒳.val.val.obj} (f : y' ⟶ y)
    (hy : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y))
    (hy' : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y'))
    (hff : letI := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := 𝒳.val.val.p) f
      Module.FaithfullyFlat (fibredSectionRing B S hS 𝒳.val.val.p y)
        (fibredSectionRing B S hS 𝒳.val.val.p y')) :
    Function.Injective (M.val.map f.op) := by
  let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := 𝒳.val.val.p) f
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids M y
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids M y'
  have := hff
  have hc := isCartesianBetweenAffines_of_isQuasicoherentOnSite 𝒳.val.isFiberedInGroupoids M hM
    f hy hy'
  have he : ∀ m : M.val.obj (op y), fibredSectionsBaseChange 𝒳.val.isFiberedInGroupoids M f
      ((1 : fibredSectionRing B S hS 𝒳.val.val.p y') ⊗ₜ m) = M.val.map f.op m := fun m ↦ by
    let := fibredSectionsModuleOver 𝒳.val.isFiberedInGroupoids M f
    have : IsScalarTower (fibredSectionRing B S hS 𝒳.val.val.p y)
        (fibredSectionRing B S hS 𝒳.val.val.p y') (M.val.obj (op y')) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    show LinearMap.liftBaseChange _ (fibredSectionsRestrict 𝒳.val.isFiberedInGroupoids M f)
      ((1 : fibredSectionRing B S hS 𝒳.val.val.p y') ⊗ₜ m) = _
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  intro m m' h
  have h1 : (1 : fibredSectionRing B S hS 𝒳.val.val.p y') ⊗ₜ[fibredSectionRing B S hS
      𝒳.val.val.p y] m = (1 : fibredSectionRing B S hS 𝒳.val.val.p y') ⊗ₜ m' :=
    hc.1 ((he m).trans (h.trans (he m').symm))
  have h2 : (1 : fibredSectionRing B S hS 𝒳.val.val.p y') ⊗ₜ[fibredSectionRing B S hS
      𝒳.val.val.p y] (m - m') = 0 := by
    rw [TensorProduct.tmul_sub, h1, sub_self]
  exact sub_eq_zero.1 ((Module.FaithfullyFlat.one_tmul_eq_zero_iff
    (R := fibredSectionRing B S hS 𝒳.val.val.p y)
    (A := fibredSectionRing B S hS 𝒳.val.val.p y') (m := m - m')).1 h2)

end AlgebraicGeometry.Stack.FlatFppf

namespace AlgebraicGeometry.Stack

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules

/-- **The unit of an algebra object of `QCoh(𝒪_𝒳)` has fpqc-local retractions over the flat
objects**: over every flat object `y` of `𝒳` lying over an affine scheme there are a morphism
`y' ⟶ y` from a flat object lying over an affine scheme, whose ring map `𝒪(y) ⟶ 𝒪(y')` is
faithfully flat, and an `𝒪(y')`-linear map `G(y') ⟶ 𝒪(y')` sending the unit `η(1)` to `1`.

For `G = g_{QCoh,*}𝒪_U` with `g : U ⟶ 𝒳` affine, flat and surjective, `y' = U ×_𝒳 y` and the
retraction is restriction along the diagonal of `U ×_𝒳 U ×_𝒳 y ⟶ U ×_𝒳 y`; this is the step
"`s` becomes the inclusion of a direct summand upon pullback to `U`" of the proof of
Stacks 0GRL. -/
def HasFlatLocalUnitRetractions {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) [MonObj G] : Prop :=
  ∀ y : 𝒳.val.val.obj, flatObject B S hS 𝒳.val y →
    IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y) →
    ∃ (y' : 𝒳.val.val.obj) (f : y' ⟶ y), flatObject B S hS 𝒳.val y' ∧
      IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y') ∧
      (letI := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := 𝒳.val.val.p) f;
        Module.FaithfullyFlat (fibredSectionRing B S hS 𝒳.val.val.p y)
          (fibredSectionRing B S hS 𝒳.val.val.p y')) ∧
      ∃ ρ : (letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids G.obj y';
          G.obj.val.obj (op y') →ₗ[fibredSectionRing B S hS 𝒳.val.val.p y']
            fibredSectionRing B S hS 𝒳.val.val.p y'),
        ρ (η[G].hom.val.app (op y') (1 : fibredSectionRing B S hS 𝒳.val.val.p y')) = 1

/-- **The input `hdual` of Stacks 0GRL.**  Let `𝒳` be an algebraic stack, `G` an algebra object of
`QCoh(𝒪_𝒳)` whose unit has fpqc-local retractions over the flat objects, `𝓕` a coherent module and
`𝒪_𝒳 --s--> 𝓕 --i--> G` a factorization of the unit of `G`.  Then the dual
`𝓓 = hom(𝓕, 𝒪_𝒳) = Q(SheafHom(𝓕, 𝒪_𝒳))` of Stacks 0GQN, with its evaluation `ev : 𝓕 ⊗ 𝓓 ⟶ 𝒪_𝒳`,
has `s^∨ = λ⁻¹ ≫ s ▷ 𝓓 ≫ ev : 𝓓 ⟶ 𝒪_𝒳` an epimorphism.

The proof is the source's: over a flat `y'` the dual is `Hom(𝓕(y'), 𝒪(y'))` (the coherator does
not change the sections of `SheafHom(𝓕, 𝒪_𝒳)` over flat objects), the retraction of the unit
composed with `i` is a functional `𝓕(y') ⟶ 𝒪(y')` taking `s` to `1`, so `s^∨` hits `1` over `y'`;
faithful flatness of `y' ⟶ y` and the covering of `𝒳` by objects mapping to flat objects over
affine schemes then make `s^∨` cancellable on the right. -/
theorem exists_dual_evaluation_epi (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) [MonObj G] (hG : HasFlatLocalUnitRetractions G)
    (𝓕 : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) (h𝓕 : coherentQuasicoherent B S hS 𝒳 𝓕)
    (s : 𝟙_ _ ⟶ 𝓕) (i : 𝓕 ⟶ G) (hsi : s ≫ i = η[G]) :
    ∃ (𝓓 : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) (ev : 𝓕 ⊗ 𝓓 ⟶ 𝟙_ _),
      Epi ((λ_ 𝓓).inv ≫ s ▷ 𝓓 ≫ ev) := by
  let p := 𝒳.val.val.p
  let hp := 𝒳.val.isFiberedInGroupoids
  let O : Stack.fppfModules B S hS 𝒳 := _root_.SheafOfModules.unit _
  have hO : O.IsQuasicoherentOnSite :=
    (𝟙_ (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp)).property
  have : 𝓕.obj.IsFinitePresentationOnSite := h𝓕.2
  let K := AlgebraicStacks.fppfInternalHom B S hS 𝒳 𝓕.obj O
  let c := (AlgebraicStacks.coheratorAdjunction B S hS 𝒳).counit.app K
  let 𝓓 : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp :=
    AlgebraicStacks.quasicoherentHom B S hS 𝒳 𝓕.obj O
  let β := AlgebraicStacks.quasicoherentHomEvaluationBilinear 𝓕.obj O
  let Osh := FibredSite.structureSheaf B S hS p hp .fppf
  have hOs := FibredSite.structureRingPresheaf_isSheaf B S hS p hp .fppf
  let ev : 𝓕 ⊗ 𝓓 ⟶ 𝟙_ _ := ObjectProperty.homMk (Stacks.SheafOfModules.bilinearDesc Osh hOs β)
  refine ⟨𝓓, ev, ⟨fun {M} a b hab ↦ ?_⟩⟩
  have hc : ∀ (V : 𝒳.val.val.objᵒᵖ) (d : 𝓓.obj.val.obj V),
      ((λ_ 𝓓).inv ≫ s ▷ 𝓓 ≫ ev).hom.val.app V d =
        β.app V (s.hom.val.app V
          (1 : (FibredSite.ringStructureSheafCore B S hS p hp .fppf).obj.obj V)) d :=
    fun V d ↦ Stacks.SheafOfModules.leftUnitor_inv_whiskerRight_bilinearDesc_val_app Osh hOs β
      s.hom V d
  -- restriction of the image of `1`
  have hres : ∀ (c' : (𝟙_ (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp)) ⟶ M)
      {y z : 𝒳.val.val.obj} (f : z ⟶ y),
      M.obj.val.map f.op (c'.hom.val.app (op y) (1 : fibredSectionRing B S hS p y)) =
        c'.hom.val.app (op z) (1 : fibredSectionRing B S hS p z) := fun c' {y z} f ↦ by
    have hn := congrArg (fun φ ↦ φ (1 : fibredSectionRing B S hS p y))
      (congrArg ConcreteCategory.hom (c'.hom.val.naturality f.op))
    refine hn.symm.trans ?_
    show c'.hom.val.app (op z)
      ((FibredSite.ringStructureSheafCore B S hS p hp .fppf).obj.map f.op
        (1 : fibredSectionRing B S hS p y)) = _
    exact congrArg (fun x ↦ c'.hom.val.app (op z) x)
      ((FibredSite.ringStructureSheafCore B S hS p hp .fppf).obj.map f.op).hom.map_one
  -- equal morphisms agree on sections
  have hev : ∀ {P Q : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp}
      {u v : P ⟶ Q}, u = v → ∀ (V : 𝒳.val.val.objᵒᵖ) (x : P.obj.val.obj V),
      u.hom.val.app V x = v.hom.val.app V x := by
    rintro _ _ _ _ rfl _ _
    rfl
  -- the two maps agree at `1` over every flat object lying over an affine scheme
  have key : ∀ y : 𝒳.val.val.obj, flatObject B S hS 𝒳.val y →
      IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y) →
      a.hom.val.app (op y) (1 : fibredSectionRing B S hS p y) =
        b.hom.val.app (op y) (1 : fibredSectionRing B S hS p y) := by
    intro y hy hyaff
    obtain ⟨y', f, hy', hy'aff, hff, ρ, hρ⟩ := hG y hy hyaff
    let := fibredSectionsModule hp G.obj y'
    let ψ : 𝓕.obj.val.obj (op y') →+ O.val.obj (op y') :=
      { toFun := fun m ↦ ρ (i.hom.val.app (op y') m)
        map_zero' := (congrArg ρ (map_zero (i.hom.val.app (op y')).hom)).trans (map_zero ρ)
        map_add' := fun m m' ↦ (congrArg ρ (map_add (i.hom.val.app (op y')).hom m m')).trans
          (map_add ρ _ _) }
    obtain ⟨k, hk⟩ := AlgebraicStacks.exists_fppfInternalHomEval_eq 𝓕.obj O 𝓕.property hy'aff ψ
      (fun r m ↦ (congrArg ρ ((i.hom.val.app (op y')).hom.map_smul r m)).trans (ρ.map_smul r _))
    obtain ⟨r, hr⟩ := (AlgebraicStacks.bijective_coheratorAdjunction_counit_app_fppfInternalHom
      𝓕.obj O hO y' hy').2 k
    have hcr : ((λ_ 𝓓).inv ≫ s ▷ 𝓓 ≫ ev).hom.val.app (op y') r =
        (1 : fibredSectionRing B S hS p y') := by
      rw [hc]
      show AlgebraicStacks.fppfInternalHomEval 𝓕.obj O (op y') (c.val.app (op y') r) _ = _
      rw [hr, hk]
      exact (congrArg ρ (hev hsi (op y') (1 : fibredSectionRing B S hS p y'))).trans hρ
    have key' : a.hom.val.app (op y') (1 : fibredSectionRing B S hS p y') =
        b.hom.val.app (op y') (1 : fibredSectionRing B S hS p y') := by
      have hab' : a.hom.val.app (op y') (((λ_ 𝓓).inv ≫ s ▷ 𝓓 ≫ ev).hom.val.app (op y') r) =
          b.hom.val.app (op y') (((λ_ 𝓓).inv ≫ s ▷ 𝓓 ≫ ev).hom.val.app (op y') r) :=
        hev hab (op y') r
      rwa [hcr] at hab'
    exact FlatFppf.injective_map_of_faithfullyFlat M.property f hyaff hy'aff hff
      ((hres a f).trans (key'.trans (hres b f).symm))
  -- hence at `1` over every object
  have key₁ : ∀ y : 𝒳.val.val.obj, a.hom.val.app (op y) (1 : fibredSectionRing B S hS p y) =
      b.hom.val.app (op y) (1 : fibredSectionRing B S hS p y) := by
    intro y
    refine sections_ext_of_affineFlatFactorization M.obj (fun Y f hf ↦ ?_)
    obtain ⟨-, x, hx, hxa, ⟨n⟩⟩ := hf
    rw [hres a f, hres b f, ← hres a n, ← hres b n, key x hx hxa]
  apply ObjectProperty.hom_ext
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun y ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  exact key₁ y.unop

/-- **Stacks 0GRL's argument on a Noetherian algebraic stack, with the dual of a coherent module
supplied.**  This is
`AlgebraicGeometry.Stack.universallyInjective_algebraMap_tensorFunctor_of_coherentGeneration`
with its input `hdual` discharged by `AlgebraicGeometry.Stack.exists_dual_evaluation_epi`: the
evaluation of `hom(𝓕, 𝒪_𝒳)` (Stacks 0GQN) at a section `s` is an epimorphism as soon as the unit of
`G` has fpqc-local retractions over the flat objects. -/
theorem universallyInjective_algebraMap_tensorFunctor_of_unitRetractions
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    [BraidedCategory (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids)]
    {R : Type u} [CommRing R]
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids ⥤ ModuleCat.{u} R) [F.Braided]
    [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    (G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) [MonObj G] [IsCommMonObj G]
    (hgen : ∀ M : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids, (coherentQuasicoherent B S hS 𝒳).ind.{u} M)
    (hG : HasFlatLocalUnitRetractions G) :
    letI := Functor.tensorFunctorCommRing F G
    letI := Functor.tensorFunctorAlgebraStr F G
    Algebra.UniversallyInjective R (F.obj G) :=
  universallyInjective_algebraMap_tensorFunctor_of_coherentGeneration B S hS 𝒳 h𝒳 F G hgen
    (exists_dual_evaluation_epi 𝒳 G hG)

end AlgebraicGeometry.Stack

end
