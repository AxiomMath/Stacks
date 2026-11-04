module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.ModuleFunctorAtBase
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.Coreflection
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.InjectiveObjects
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.Vanishing

/-!
# The coreflection of an injective module-valued functor

Let `A` be a commutative ring, let `𝒫` be the category of module-valued functors on the
commutative `A`-algebras and let `Q : 𝒫 ⥤ 𝒜` be the coreflection onto the adequate functors.

## Main results

* `AdequateFunctor.bijective_counit_app_baseAlgebra` — for every module-valued functor `G`, the
  counit `Q(G) ⟶ G` is bijective at the base algebra `A`: the functor `B ↦ B` is adequate and
  corepresents evaluation at `A`.
* `AdequateFunctor.exists_moduleExtension_iso_adequateCoreflection_of_injective` — for an
  injective object `I` of `𝒫`, the coreflection `Q(I)` is the extension of scalars `E̲` of a pure
  injective `A`-module `E`, and the composite `E̲ ≅ Q(I) ⟶ I` is an isomorphism at `A`. So
  `Q(I) ≅ (I(A))̲`, with `I(A)` pure injective.
* `AdequateFunctor.moduleExtensionAdjunction` — extension of scalars `M ↦ M̲` is left adjoint
  to evaluation at the base algebra, `AdequateFunctor.baseEvaluation`.
* `AdequateFunctor.moduleExtensionToAdequateCoreflection` — a natural transformation
  `(F(A))̲ ⟶ Q(F)`, an isomorphism at every injective `F`
  (`AdequateFunctor.isIso_moduleExtensionToAdequateCoreflection_app`).
* `AdequateFunctor.coreflectionComplexIso` — for an injective resolution `G ⟶ I ⁎`, the complex
  `Q(I ⁎)` is isomorphic to the complex of extended modules `(I ⁎(A))̲`.
* `AdequateFunctor.rightDerivedAdequateCoreflectionIso` and
  `AdequateFunctor.rightDerivedAdequateCoreflectionEvaluationIso` — `R ⁿ Q(G) ≅ Hⁿ((I ⁎(A))̲)`,
  and at an algebra `B`, `R ⁿ Q(G)(B) ≅ Hⁿ(B ⊗[A] I ⁎(A))`.

## Implementation notes

The coreflection preserves injective objects, and an injective adequate functor is the
extension of a pure injective module by Tag 0708; the identification of that module with `I(A)`
is the bijectivity of the counit at the base algebra. Since `Q` is applied termwise to an
injective resolution `G ⟶ I ⁎` to compute `R ᵖ Q(G)`, `R ᵖ Q(G)` is the cohomology of the
complex `B ↦ B ⊗[A] I ⁎(A)`. For that the identification has to be natural in `I`, so it is
built as a natural transformation `(F(A))̲ ⟶ Q(F)` defined for every `F`: the extension of the
counit of `Q` at `A` (bijective for every `F`) inverted, followed by the counit
`(Q(F)(A))̲ ⟶ Q(F)` of the adjunction `M ↦ M̲ ⊣ ev_A`, which is invertible on extended modules.
The value at `B` is stated with the tensor product `B ⊗[A] I ⁿ(A)` itself, the value of the
extended module there.

## References

* [Stacks Project, Tag 06Z7](https://stacks.math.columbia.edu/tag/06Z7)
* [Stacks Project, Tag 0708](https://stacks.math.columbia.edu/tag/0708)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AdequateFunctor

variable (A : Type u) [CommRing A]

/-- The value at the base algebra of the module extension of the ring itself is free of rank one
on `1 ⊗ 1`. -/
private noncomputable def moduleExtensionSelfAtBaseEquiv :
    (moduleExtension.{max (u + 1) (v + 1) w, v} A
        (ModuleCat.of A (ULift.{max (u + 1) (v + 1) w} A))).obj (liftedBaseAlgebra.{v} A) ≃ₗ[
      ULift.{v} A] ULift.{v} A :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (ULift.{v} A) (ULift.{v} A))
    (ULift.moduleEquiv : ULift.{max (u + 1) (v + 1) w} A ≃ₗ[A] A)).trans
    (TensorProduct.AlgebraTensorModule.rid A (ULift.{v} A) (ULift.{v} A))

private lemma moduleExtensionSelfAtBaseEquiv_one :
    moduleExtensionSelfAtBaseEquiv.{u, v, w} A
      ((1 : ULift.{v} A) ⊗ₜ[A] (1 : ULift.{max (u + 1) (v + 1) w} A)) = 1 := by
  simp only [moduleExtensionSelfAtBaseEquiv, LinearEquiv.trans_apply]
  exact one_smul A (1 : ULift.{v} A)

/-- Every element of the value at the base algebra of a module-valued functor is the image of
`1 ⊗ 1` under a morphism out of the module extension of the ring itself. -/
private lemma exists_app_baseAlgebra_eq
    (H : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) (y : H.obj (liftedBaseAlgebra.{v} A)) :
    ∃ η : moduleExtension.{max (u + 1) (v + 1) w, v} A
        (ModuleCat.of A (ULift.{max (u + 1) (v + 1) w} A)) ⟶ H,
      η.app (liftedBaseAlgebra.{v} A)
        ((1 : ULift.{v} A) ⊗ₜ[A] (1 : ULift.{max (u + 1) (v + 1) w} A)) = y := by
  let ψ := ModuleCat.ofHom ((LinearMap.toSpanSingleton _ _ y).comp
    (moduleExtensionSelfAtBaseEquiv.{u, v, w} A).toLinearMap)
  refine ⟨homOfAppBase ψ, ?_⟩
  rw [homOfAppBase_app_baseAlgebra]
  show (LinearMap.toSpanSingleton _ _ y) (moduleExtensionSelfAtBaseEquiv.{u, v, w} A _) = y
  rw [moduleExtensionSelfAtBaseEquiv_one, LinearMap.toSpanSingleton_apply, one_smul]

/-- A morphism out of the module extension of the ring itself vanishes as soon as it kills
`1 ⊗ 1` at the base algebra. -/
private lemma eq_zero_of_app_baseAlgebra_one
    {H : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A}
    (η : moduleExtension.{max (u + 1) (v + 1) w, v} A
        (ModuleCat.of A (ULift.{max (u + 1) (v + 1) w} A)) ⟶ H)
    (hη : η.app (liftedBaseAlgebra.{v} A)
        ((1 : ULift.{v} A) ⊗ₜ[A] (1 : ULift.{max (u + 1) (v + 1) w} A)) = 0) :
    η = 0 := by
  refine hom_ext_of_app_baseAlgebra ?_
  rw [PresheafOfModules.zero_app]
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  have hz : z = (moduleExtensionSelfAtBaseEquiv.{u, v, w} A z) •
      ((1 : ULift.{v} A) ⊗ₜ[A] (1 : ULift.{max (u + 1) (v + 1) w} A)) := by
    apply (moduleExtensionSelfAtBaseEquiv.{u, v, w} A).injective
    rw [map_smul, moduleExtensionSelfAtBaseEquiv_one, smul_eq_mul, mul_one]
  show η.app (liftedBaseAlgebra.{v} A) z = 0
  rw [hz, map_smul, hη, smul_zero]

/-- **The counit of the coreflection is bijective at the base algebra.** For every
module-valued functor `G`, the counit `Q(G) ⟶ G` is a bijection `Q(G)(A) ≅ G(A)`: the functor
`B ↦ B` is adequate and corepresents evaluation at `A`. -/
public theorem bijective_counit_app_baseAlgebra
    (G : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) :
    Function.Bijective (((adequateCoreflectionAdjunction.{u, v, w} A).counit.app G).app
      (liftedBaseAlgebra.{v} A)) := by
  let adj := adequateCoreflectionAdjunction.{u, v, w} A
  let M : ModuleCat.{max (u + 1) (v + 1) w} A := ModuleCat.of A (ULift.{max (u + 1) (v + 1) w} A)
  let O' : (adequate.{u, v, max (u + 1) (v + 1) w} A).FullSubcategory :=
    ⟨moduleExtension.{max (u + 1) (v + 1) w, v} A M, isAdequate_moduleExtension M⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨η, hη⟩ := exists_app_baseAlgebra_eq.{u, v, w} A _ x
    have h1 : η ≫ adj.counit.app G = 0 := by
      refine eq_zero_of_app_baseAlgebra_one.{u, v, w} A _ ?_
      rw [PresheafOfModules.comp_app]
      show (adj.counit.app G).app _ (η.app _ _) = 0
      rw [hη, hx]
    have h2 : (ObjectProperty.homMk η : O' ⟶ (adequateCoreflection.{u, v, w} A).obj G) = 0 := by
      apply (adj.homEquiv O' G).symm.injective
      rwa [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_zero,
        zero_comp]
    rw [← hη, show η = 0 from congrArg InducedCategory.Hom.hom h2]
    rfl
  · intro y
    obtain ⟨η, hη⟩ := exists_app_baseAlgebra_eq.{u, v, w} A G y
    let θ := (adj.homEquiv O' G η).hom
    have hθ : θ ≫ adj.counit.app G = η :=
      (adj.homEquiv_counit (g := adj.homEquiv O' G η)).symm.trans
        ((adj.homEquiv O' G).symm_apply_apply η)
    refine ⟨θ.app (liftedBaseAlgebra.{v} A)
      ((1 : ULift.{v} A) ⊗ₜ[A] (1 : ULift.{max (u + 1) (v + 1) w} A)), ?_⟩
    rw [← hη, ← hθ, PresheafOfModules.comp_app]
    rfl

/-- **The coreflection of an injective module-valued functor is an extended module.** For an
injective object `I` of the module-valued functors, `Q(I)` is the extension of scalars `E̲` of a
pure injective `A`-module `E`, and the composite `E̲ ≅ Q(I) ⟶ I` with the counit is bijective at
the base algebra; so `E ≅ I(A)` and `Q(I) ≅ (I(A))̲`. -/
public theorem exists_moduleExtension_iso_adequateCoreflection_of_injective
    (I : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) [Injective I] :
    ∃ (E : ModuleCat.{max (u + 1) (v + 1) w} A)
      (e : moduleExtension.{max (u + 1) (v + 1) w, v} A E ≅
        ((adequateCoreflection.{u, v, w} A).obj I).obj),
      Module.PureInjective A E ∧
        Function.Bijective ((e.hom ≫ (adequateCoreflectionAdjunction.{u, v, w} A).counit.app I).app
          (liftedBaseAlgebra.{v} A)) := by
  have := preservesInjectiveObjects_adequateCoreflection.{u, v, w} A
  obtain ⟨E, hE, ⟨e⟩⟩ :=
    (injective_iff_moduleExtension_pureInjective.{u, v, max (u + 1) (v + 1) w}
      ((adequateCoreflection.{u, v, w} A).obj I)).1 inferInstance
  refine ⟨E, e.symm, hE, ?_⟩
  have hb : Function.Bijective (e.symm.hom.app (liftedBaseAlgebra.{v} A)) :=
    ((PresheafOfModules.evaluation _ (liftedBaseAlgebra.{v} A)).mapIso
      e.symm).toLinearEquiv.bijective
  rw [PresheafOfModules.comp_app]
  exact (bijective_counit_app_baseAlgebra.{u, v, w} A I).comp hb

/-! ### Extension of scalars is left adjoint to evaluation at the base algebra -/

/-- Evaluation at the base algebra, as a functor to `A`-modules. -/
public noncomputable def baseEvaluation :
    ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A ⥤ ModuleCat.{max (u + 1) (v + 1) w} A :=
  PresheafOfModules.evaluation (algebraRingDiagram.{v} A) (liftedBaseAlgebra.{v} A) ⋙
    ModuleCat.restrictScalars (algebraMap A (liftedBaseAlgebra.{v} A).unop.unop)

/-- Evaluation at the base algebra is additive. -/
public instance additive_baseEvaluation : (baseEvaluation.{u, v, w} A).Additive := by
  unfold baseEvaluation
  infer_instance

/-- The bijection `Hom(M̲, F) ≃ Hom_A(M, F(A))`: the component at the base algebra, read through
the identification of `M̲(A)` with the extension of scalars of `M` and the extension-restriction
adjunction of modules. -/
public noncomputable def moduleExtensionHomEquiv (M : ModuleCat.{max (u + 1) (v + 1) w} A)
    (F : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) :
    ((moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A).obj M ⟶ F) ≃
      (M ⟶ (baseEvaluation.{u, v, w} A).obj F) :=
  (Equiv.ofBijective _ (bijective_app_baseAlgebra.{v, u, max (u + 1) (v + 1) w} M F)).trans
    ((((moduleExtensionEvaluationIso.{max (u + 1) (v + 1) w, v, u} A
      (liftedBaseAlgebra.{v} A)).app M).homCongr (Iso.refl _)).trans
      ((ModuleCat.extendRestrictScalarsAdj.{max (u + 1) (v + 1) w, u, max u v}
        (algebraMap A (liftedBaseAlgebra.{v} A).unop.unop)).homEquiv M
          (F.obj (liftedBaseAlgebra.{v} A))))

public lemma moduleExtensionHomEquiv_apply (M : ModuleCat.{max (u + 1) (v + 1) w} A)
    (F : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A)
    (η : (moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A).obj M ⟶ F) (m : M) :
    moduleExtensionHomEquiv.{u, v, w} A M F η m =
      η.app (liftedBaseAlgebra.{v} A) ((1 : ULift.{v} A) ⊗ₜ[A] m) :=
  rfl

/-- **Extension of scalars is left adjoint to evaluation at the base algebra**, as functors
between `A`-modules and module-valued functors. -/
public noncomputable def moduleExtensionAdjunction :
    moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A ⊣ baseEvaluation.{u, v, w} A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := moduleExtensionHomEquiv.{u, v, w} A
      homEquiv_naturality_left_symm := by
        intro M M' F f g
        apply (moduleExtensionHomEquiv.{u, v, w} A M F).injective
        rw [Equiv.apply_symm_apply]
        refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
        conv_lhs => rw [← (moduleExtensionHomEquiv.{u, v, w} A M' F).apply_symm_apply g]
        rfl
      homEquiv_naturality_right := fun _ _ =>
        ModuleCat.hom_ext (LinearMap.ext fun _ => rfl) }

/-- The counit `(F(A))̲ ⟶ F` of the adjunction is an isomorphism at every functor isomorphic to
an extended module. -/
public lemma isIso_moduleExtensionAdjunction_counit_app
    {F : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A} {E : ModuleCat.{max (u + 1) (v + 1) w} A}
    (e : (moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A).obj E ≅ F) :
    IsIso ((moduleExtensionAdjunction.{u, v, w} A).counit.app F) := by
  have h := (moduleExtensionAdjunction.{u, v, w} A).counit.naturality e.hom
  dsimp only [Functor.comp_map, Functor.id_map] at h
  have : (moduleExtensionAdjunction.{u, v, w} A).counit.app F =
      inv ((moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A).map
        ((baseEvaluation.{u, v, w} A).map e.hom)) ≫
        (moduleExtensionAdjunction.{u, v, w} A).counit.app _ ≫ e.hom := by
    rw [← h, IsIso.inv_hom_id_assoc]
  rw [this]
  infer_instance

/-! ### The coreflection of an injective resolution -/

public instance isIso_whiskerRight_adequateCoreflection_counit :
    IsIso (Functor.whiskerRight (adequateCoreflectionAdjunction.{u, v, w} A).counit
      (baseEvaluation.{u, v, w} A ⋙ moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun F => ?_
  have : IsIso ((baseEvaluation.{u, v, w} A).map
      ((adequateCoreflectionAdjunction.{u, v, w} A).counit.app F)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_counit_app_baseAlgebra.{u, v, w} A F)
  exact inferInstanceAs (IsIso ((moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A).map
    ((baseEvaluation.{u, v, w} A).map
      ((adequateCoreflectionAdjunction.{u, v, w} A).counit.app F))))

/-- The comparison `(F(A))̲ ⟶ Q(F)`: the inverse of the extension of the counit of `Q` at the base
algebra, which is bijective there, followed by the counit `(Q(F)(A))̲ ⟶ Q(F)`. -/
public noncomputable def moduleExtensionToAdequateCoreflection :
    baseEvaluation.{u, v, w} A ⋙ moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A ⟶
      adequateCoreflection.{u, v, w} A ⋙ (adequate.{u, v, max (u + 1) (v + 1) w} A).ι :=
  inv (Functor.whiskerRight (adequateCoreflectionAdjunction.{u, v, w} A).counit
      (baseEvaluation.{u, v, w} A ⋙ moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A)) ≫
    Functor.whiskerLeft (adequateCoreflection.{u, v, w} A ⋙
      (adequate.{u, v, max (u + 1) (v + 1) w} A).ι) (moduleExtensionAdjunction.{u, v, w} A).counit

/-- At an injective functor `I` the comparison `(I(A))̲ ⟶ Q(I)` is an isomorphism. -/
public instance isIso_moduleExtensionToAdequateCoreflection_app
    (I : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) [Injective I] :
    IsIso ((moduleExtensionToAdequateCoreflection.{u, v, w} A).app I) := by
  obtain ⟨E, e, -, -⟩ := exists_moduleExtension_iso_adequateCoreflection_of_injective.{u, v, w} A I
  have := isIso_moduleExtensionAdjunction_counit_app.{u, v, w} A e
  rw [moduleExtensionToAdequateCoreflection, NatTrans.comp_app, Functor.whiskerLeft_app]
  exact IsIso.comp_isIso' inferInstance this

/-- **`Q` of an injective resolution is the extension of its value at the base algebra.** For
an injective resolution `G ⟶ I ⁎` of a module-valued functor, the complex `Q(I ⁎)` is
isomorphic to the complex of extended modules `B ↦ B ⊗[A] I ⁎(A)`. -/
public noncomputable def coreflectionComplexIso
    {G : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A} (R : InjectiveResolution G) :
    ((baseEvaluation.{u, v, w} A ⋙ moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A
      ).mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex ≅
      ((adequateCoreflection.{u, v, w} A ⋙ (adequate.{u, v, max (u + 1) (v + 1) w} A).ι
        ).mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex :=
  haveI : IsIso ((NatTrans.mapHomologicalComplex
      (moduleExtensionToAdequateCoreflection.{u, v, w} A) (ComplexShape.up ℕ)).app
        R.cocomplex) :=
    @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _ fun n => by
      have := R.injective n
      rw [NatTrans.mapHomologicalComplex_app_f]
      infer_instance
  asIso ((NatTrans.mapHomologicalComplex (moduleExtensionToAdequateCoreflection.{u, v, w} A)
    (ComplexShape.up ℕ)).app R.cocomplex)

/-- **`R ⁿ Q(G)` is the cohomology of the extension of `I ⁎(A)`.** For an injective resolution
`G ⟶ I ⁎`, the `n`-th right derived functor of the coreflection `Q` onto the adequate
functors, viewed as a module-valued functor, is the `n`-th cohomology of the complex of extended
modules `B ↦ B ⊗[A] I ⁎(A)`. -/
public noncomputable def rightDerivedAdequateCoreflectionIso
    {G : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A} (R : InjectiveResolution G) (n : ℕ) :
    (adequate.{u, v, max (u + 1) (v + 1) w} A).ι.obj
        (((adequateCoreflection.{u, v, w} A).rightDerived n).obj G) ≅
      (((baseEvaluation.{u, v, w} A ⋙ moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A
        ).mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex).homology n :=
  haveI := preservesFiniteLimits_adequateInclusion.{u, v, max (u + 1) (v + 1) w} A
  haveI := preservesFiniteColimits_adequateInclusion.{u, v, max (u + 1) (v + 1) w} A
  (adequate.{u, v, max (u + 1) (v + 1) w} A).ι.mapIso
      (R.isoRightDerivedObj (adequateCoreflection.{u, v, w} A) n) ≪≫
    (((((adequateCoreflection.{u, v, w} A).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      R.cocomplex).sc n).mapHomologyIso (adequate.{u, v, max (u + 1) (v + 1) w} A).ι).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (coreflectionComplexIso.{u, v, w} A R).symm

/-- **`R ⁿ Q(G)(B) = Hⁿ(B ⊗[A] I ⁎(A))`.** For an injective resolution `G ⟶ I ⁎` and an
`A`-algebra `B`, the value at `B` of the `n`-th right derived functor of the coreflection `Q` is
the `n`-th cohomology of the complex of `B`-modules `B ⊗[A] I ⁎(A)`, the values at `B` of the
extended modules of `I ⁎(A)`. -/
public noncomputable def rightDerivedAdequateCoreflectionEvaluationIso
    {G : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A} (R : InjectiveResolution G) (n : ℕ)
    (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ) :
    ((adequate.{u, v, max (u + 1) (v + 1) w} A).ι.obj
        (((adequateCoreflection.{u, v, w} A).rightDerived n).obj G)).obj X ≅
      (((baseEvaluation.{u, v, w} A ⋙ moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A ⋙
        PresheafOfModules.evaluation (algebraRingDiagram.{v} A) X).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj R.cocomplex).homology n :=
  (PresheafOfModules.evaluation (algebraRingDiagram.{v} A) X).mapIso
      (rightDerivedAdequateCoreflectionIso.{u, v, w} A R n) ≪≫
    (((((baseEvaluation.{u, v, w} A ⋙ moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A
      ).mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex).sc n).mapHomologyIso
        (PresheafOfModules.evaluation (algebraRingDiagram.{v} A) X)).symm

end AdequateFunctor

end
