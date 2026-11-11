module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.Homology.PseudoCoherent.Relative.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.BaseObjectAtAffine
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.ClosedAffineBases
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.GlobalDerivedHomBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FibreBettiGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsRepresented
public import StacksFrontier.Homology.Perfect.NilpotentLiftingResidueField
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.Homology.PseudoCoherent.BaseRingEquiv
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Examples.Algebra.SquareZeroQuotientNotPseudoCoherent

/-!
# The generalized derived existence theorem of Stacks 0DIR fails without flatness

Stacks 0DIR proposes that the derived Grothendieck existence theorem 0DIQ holds for `X` only
separated and of finite presentation over `A = lim Aₙ`, with `Kₙ` pseudo-coherent relative to
`Aₙ` and supported on closed subsets proper over `Aₙ`. For `X` flat over `A` that is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Deformations/DerivedExistenceSupported.lean` (without the
support clause of the conclusion). Without flatness it is false, and this file proves it.

Let `A = lim Aₙ` with `A₀ ⟶ ⋯` surjective with locally nilpotent kernels, each `Aₙ` Noetherian,
and `f ∈ A` vanishing in `A₀`, the kernel of `A ⟶ A₀` nilpotent and `A/(f)` not a pseudo-coherent
`A`-module. Then `X = Spec A/(f)` (a closed subscheme of `Spec A` of finite presentation) and
`Kₙ = 𝒪_{Xₙ}` satisfy every hypothesis of 0DIR, but there is no `K ∈ D_QCoh(𝒪_X)` pseudo-coherent
relative to `A` with `Lj₀^* K ≅ 𝒪_{X₀}`:

* `X₀ = Spec A₀`, since `X ⟶ Spec A` is a monomorphism through which `Spec A₀ ⟶ Spec A` factors;
* affine base change of `RΓ` along `Spec A₀ ⟶ Spec B` gives `RΓ(X, K) ⊗^L_B A₀ ≅ A₀[0]`, so
  `RΓ(X, K) ≅ B[0]` (Stacks 09AR along the nilpotent surjection `B ⟶ A₀`);
* relative pseudo-coherence on the identity charts makes `B` a pseudo-coherent `A`-module.

The data `Aₙ = 𝔽₂ ⊕ 𝔽₂ⁿ`, `f = (0, (1, 1, …))` of
`StacksFrontier/Examples/Algebra/SquareZeroQuotientNotPseudoCoherent.lean` satisfy these
conditions. The flat proof breaks because `Ljₙ^*` is `- ⊗^L_B Bₙ`, not `- ⊗^L_A Aₙ`.

## Main results

In the namespace `Stacks.Examples.DerivedExistenceNotFlat`:

* `relativeDerivedExistenceSystem`: the system `X = Spec A/(f)`, `Kₙ = 𝒪_{Xₙ}`.
* `isRelativelyPseudoCoherent_structureObject`: `𝒪_X` is pseudo-coherent relative to a
  locally Noetherian representable base.
* `not_exists_isRelativelyPseudoCoherent_stageZero_iso`: no pseudo-coherent lift exists.
* `not_forall_exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso`: **the generalization
  proposed in Stacks 0DIR is false without flatness.**

## References

* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
* [Stacks Project, Tag 0DIQ](https://stacks.math.columbia.edu/tag/0DIQ)
* [Stacks Project, Tag 09AR](https://stacks.math.columbia.edu/tag/09AR)
* [Stacks Project, Tag 067F](https://stacks.math.columbia.edu/tag/067F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt baseProjection)

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace Stacks.Examples.DerivedExistenceNotFlat

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u})
  (hFs : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom)
  (f : (limit F : CommRingCat.{u}))

/-- The ring `B = A/(f)`. -/
abbrev quotientRing : CommRingCat.{u} :=
  CommRingCat.of ((limit F : CommRingCat.{u}) ⧸ Ideal.span {f})

/-- `Spec B ⟶ Spec A`. -/
abbrev quotientSpecMap : Spec (quotientRing F f) ⟶ limitBase F :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))

/-- `Spec B ⟶ Spec A` is a closed immersion. -/
instance : IsClosedImmersion (quotientSpecMap F f) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- A big fppf site containing `Spec A`. -/
abbrev site : BigFppfSite.{u} := (BigFppfSite.exists_contains (limitBase F)).choose

/-- The chosen site contains `Spec A`. -/
theorem site_contains : (site F).Contains (limitBase F) :=
  (BigFppfSite.exists_contains (limitBase F)).choose_spec

include hFs in
/-- The chosen site contains every `Spec Aₙ`, a closed subscheme of `Spec A`. -/
theorem site_contains_baseAt (n : ℕ) : (site F).Contains (baseAt F n) :=
  have := GrothendieckExistence.isClosedImmersion_baseProjection F hFs n
  (site F).contains_of_mono (baseProjection F n) (site_contains F)

/-- The chosen site contains `Spec B`, a closed subscheme of `Spec A`. -/
theorem site_contains_quotient : (site F).Contains (Spec (quotientRing F f)) :=
  (site F).contains_of_mono (quotientSpecMap F f) (site_contains F)

/-- `Spec B`, as an object of the big fppf site over `Spec A`. -/
abbrev quotientObject : BigFppfOver (site F) (limitBase F) (site_contains F) :=
  siteObject (site F) (limitBase F) (site_contains F) (site_contains_quotient F f)
    (quotientSpecMap F f)

/-- The structure morphism `Spec B ⟶ Spec A` in the big fppf site over `Spec A`. -/
abbrev quotientObjectToBase :
    quotientObject F f ⟶ limitBaseObject F (site F) (site_contains F) :=
  Over.homMk (quotientObject F f).hom (by simp)

/-- `X = Spec B` as an algebraic space over `Spec A`. -/
abbrev space : Over (schemeSpace (limitBaseObject F (site F) (site_contains F))) :=
  Over.mk ((schemeSpaceFunctor (site F) (limitBase F) (site_contains F)).map
    (quotientObjectToBase F f))

/-- `X ⟶ Spec A` is a closed immersion. -/
theorem isClosedImmersion_space_hom :
    IsClosedImmersion (site F) (limitBase F) (site_contains F) (space F f).hom.hom :=
  (presheaf_yoneda_map_iff (site F) (limitBase F) (site_contains F)
      AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
      (quotientObjectToBase F f)).2
    (inferInstanceAs (IsClosedImmersion (quotientSpecMap F f)))

/-- `X ⟶ Spec A` is separated. -/
theorem isSeparated_space_hom :
    IsSeparated (site F) (limitBase F) (site_contains F) (space F f).hom.hom :=
  isSeparated_of_isClosedImmersion _ _ _ _ (isClosedImmersion_space_hom F f)

/-- `X ⟶ Spec A` is of finite presentation: `B = A/(f)` is cut out by one element. -/
theorem isFinitePresentation_space_hom :
    IsFinitePresentation (site F) (limitBase F) (site_contains F) (space F f).hom.hom :=
  isFinitePresentation_yoneda_map _ _ _ (quotientObjectToBase F f)
    ⟨(HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
        (RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective
          (by rw [CommRingCat.hom_ofHom, Ideal.mk_ker]; exact Submodule.fg_span_singleton f)),
      inferInstanceAs (QuasiCompact (quotientSpecMap F f)),
      inferInstanceAs (QuasiSeparated (quotientSpecMap F f))⟩

/-! ### The stage `X₀` -/

section StageZero

variable (hf : limit.π F (op 0) f = 0)

/-- The ring map `B = A/(f) ⟶ A₀`, which exists because `f` vanishes in `A₀`. -/
abbrev quotientToStageZero : quotientRing F f ⟶ F.obj (op 0) :=
  CommRingCat.ofHom (Ideal.Quotient.lift _ (limit.π F (op 0)).hom (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp [hf]))

include hf in
/-- `A ⟶ B ⟶ A₀` is the projection `A ⟶ A₀`. -/
theorem quotientToStageZero_comp :
    CommRingCat.ofHom (Ideal.Quotient.mk _) ≫ quotientToStageZero F f hf = limit.π F (op 0) := by
  ext a
  rfl

/-- `Spec A₀ ⟶ Spec B` in the big fppf site over `Spec A`. -/
abbrev stageZeroToQuotient :
    baseObjectAt F (site F) (site_contains F) (site_contains_baseAt F hFs) 0 ⟶ quotientObject F f :=
  Over.homMk (ObjectProperty.homMk (Spec.map (quotientToStageZero F f hf))) (by
    ext1
    change Spec.map (quotientToStageZero F f hf) ≫ quotientSpecMap F f = baseProjection F 0
    rw [← Spec.map_comp, quotientToStageZero_comp])

end StageZero

/-! ### The system `Kₙ = 𝒪_{Xₙ}` -/

section System

attribute [local instance] HasDerivedCategory.standard pointTopology

/-- `Kₙ = 𝒪_{Xₙ}[0]`. -/
abbrev structureObjectAt (n : ℕ) :
    derivedCategoryAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F f) n :=
  (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)

/-- `Kₙ = 𝒪_{Xₙ}[0]` lies in `D_QCoh`. -/
theorem qcohDerived_structureObjectAt (n : ℕ) :
    QcohDerived (site F) (limitBase F) (site_contains F)
      (spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F f) n)
      (structureObjectAt F hFs f n) :=
  qcohDerived_singleFunctor_structureModule
    (X := (spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F f) n).1)
    (hX := (spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F f) n).2)

/-- `Liₙ^* 𝒪_{Xₙ₊₁}[0] ≅ 𝒪_{Xₙ}[0]`. -/
abbrev structureObjectTransition (n : ℕ) :
    (transitionDerivedPullback F (site F) (site_contains F) (site_contains_baseAt F hFs)
      (space F f) n).obj (structureObjectAt F hFs f (n + 1)) ≅ structureObjectAt F hFs f n :=
  smallEtaleDerivedModulePullbackUnitIso
    (transitionSpace F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F f) n)

/-- `X ⟶ Spec A` is proper, being a closed immersion. -/
theorem isProper_space_hom :
    IsProper (site F) (limitBase F) (site_contains F) (space F f).hom.hom :=
  isProper_of_isClosedImmersion _ _ _ (space F f).left.2 (schemeSpace _).2 _
    (isClosedImmersion_space_hom F f)

/-- All of `|Xₙ|` is proper over `Spec Aₙ`: `Xₙ ⟶ Spec Aₙ` is a closed immersion. -/
theorem isProperOver_univ (n : ℕ) :
    IsProperOver (site F) (limitBase F) (site_contains F)
      (spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F f) n).2
      (schemeSpace (baseObjectAt F (site F) (site_contains F) (site_contains_baseAt F hFs) n)).2
      (spaceBaseProjection F (site F) (site_contains F) (site_contains_baseAt F hFs)
        (space F f) n).hom
      (isLocallyOfFiniteType_spaceBaseProjection F (site F) (site_contains F)
        (site_contains_baseAt F hFs) (space F f)
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation (site F) (limitBase F)
          (site_contains F) (isFinitePresentation_space_hom F f).1) n)
      Set.univ isClosed_univ :=
  isProper_comp' _ _ _ _ _ (spaceAt F (site F) (site_contains F)
      (site_contains_baseAt F hFs) (space F f) n).2 (schemeSpace _).2
    (isProper_of_isClosedImmersion _ _ _
      (isClosedSubspace_reducedClosedSubspace _ _ _ _ _ _ _).1
      (spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F f) n).2 _
      (isClosedImmersion_ι_reducedClosedSubspace _ _ _ _ _ _))
    (isProper_spaceBaseProjection F (site F) (site_contains F) (site_contains_baseAt F hFs)
      (space F f) (isProper_space_hom F f) n)

end System

/-! ### Relative pseudo-coherence of `𝒪` over a locally Noetherian base -/

section RelativePseudoCoherence

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] enoughInjectives_modules_ringUniverse
  isGrothendieckAbelian_modules_ringUniverse
attribute [local instance] hasRightDerivedFunctor_chartSections

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Every affine étale chart of a scheme `T` that is locally Noetherian has Noetherian ring of
functions. -/
theorem isNoetherianRing_structurePresheaf (T : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
    (V : SmallEtale B S hS (yoneda.obj T)) (hV : IsAffine (chartScheme V)) :
    IsNoetherianRing ((structurePresheaf B S hS (yoneda.obj T)).obj (op V)) := by
  have hT : HasEtaleLocalProperty B S hS (yoneda.obj T)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    ⟨T, 𝟙 _, presheaf_id_of_iso B S hS _ (fun _ _ f hf => by
        have : IsIso f := hf
        change Surjective ((BigFppfOver.toScheme B S hS).map f)
        infer_instance) T,
      presheaf_id_of_iso B S hS _ (fun _ _ f hf => by
        have : IsIso f := hf
        change Etale ((BigFppfOver.toScheme B S hS).map f)
        infer_instance) T, inferInstance⟩
  have hVN : IsLocallyNoetherian (chartScheme V) :=
    (exists_atlas_iff_forall_etale B S hS (yoneda.obj T) _
      (isAlgebraicSpace_yoneda B S hS T)).1 hT V.obj.left V.obj.hom V.property
  change IsNoetherianRing Γ(chartScheme V, ⊤)
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- **`𝒪_X` is pseudo-coherent relative to a locally Noetherian scheme**: for `g : X ⟶ T` locally
of finite type with `T` representable and locally Noetherian, `𝒪_X[0]` is pseudo-coherent
relative to `T`. On a square of affine étale charts `U ⟶ V`, `RΓ(U, 𝒪_X)` has cohomology `𝒪_X(U)`
in degree `0` only, a finite `𝒪_X(U)`-module, and `𝒪_T(V)` is Noetherian (Stacks 067F). -/
theorem isRelativelyPseudoCoherent_structureObject (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
    (g : X ⟶ schemeSpace T) (hg : IsLocallyOfFiniteType B S hS g.hom)
    (hE : QcohDerived B S hS X ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _))) :
    IsRelativelyPseudoCoherent B S hS X.1 X.2 g.hom hg ⟨_, hE⟩ := by
  intro m U V φ hc hU hV
  let := hU
  let := hV
  let : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map φ) :=
    hg _ _ U.obj.hom V.obj.hom φ U.property V.property hc
  let : Algebra ((structurePresheaf B S hS (schemeSpace T).1).obj (op V))
      ((structurePresheaf B S hS X.1).obj (op U)) :=
    (((BigFppfOver.toScheme B S hS).map φ).appTop.hom).toAlgebra
  let : Algebra.FiniteType ((structurePresheaf B S hS (schemeSpace T).1).obj (op V))
      ((structurePresheaf B S hS X.1).obj (op U)) :=
    HasRingHomProperty.appTop (@LocallyOfFiniteType) ((BigFppfOver.toScheme B S hS).map φ)
      inferInstance
  have : IsNoetherianRing ((structurePresheaf B S hS (schemeSpace T).1).obj (op V)) :=
    isNoetherianRing_structurePresheaf T V hV
  have hUa : IsAffineChart B S hS X.1 U := hU
  let ev := _root_.SheafOfModules.evaluation
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) (op U)
  let E : DerivedCategory (AlgebraicGeometry.Space.Modules.{u, u} B S hS X.1 X.2) :=
    (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)
  have e (i : ℤ) : (DerivedCategory.homologyFunctor
      (ModuleCat ((structurePresheaf B S hS X.1).obj (op U))) i).obj
        (chartDerivedSections B S hS X.1 X.2 U ⟨_, hE⟩) ≅
      ev.obj ((spaceDerivedHomology B S hS X i).obj E) :=
    (chartDerivedSectionsHomologyIso B S hS X _ hE U hUa i).symm
  have hz (i : ℤ) (hi : i ≠ 0) : Subsingleton ((DerivedCategory.homologyFunctor
      (ModuleCat ((structurePresheaf B S hS X.1).obj (op U))) i).obj
        (chartDerivedSections B S hS X.1 X.2 U ⟨_, hE⟩)) := by
    refine ModuleCat.subsingleton_of_isZero (IsZero.of_iso ?_ (e i))
    refine Functor.map_isZero ev ?_
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE E 0 i hi
    · exact DerivedCategory.isZero_of_isLE E 0 i hi
  refine ((PseudoCoherence.relativePseudoCoherent_iff_boundedAbove_finite_homology _ m
    PUnit).1).2 ⟨⟨0, fun i hi => ?_⟩, fun i _ => ?_⟩
  · have := hz i hi.ne'
    exact ModuleCat.isZero_of_subsingleton _
  · rcases eq_or_ne i 0 with rfl | hi
    · let R' := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      let e₀ := ev.mapIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (AlgebraicGeometry.Space.Modules.{u, u} B S hS X.1 X.2) 0).app (SheafOfModules.unit R'))
      let e₁ : (ev.obj ((spaceDerivedHomology B S hS X 0).obj E) :
          ModuleCat ((structurePresheaf B S hS X.1).obj (op U))) ≅
          ModuleCat.of ((structurePresheaf B S hS X.1).obj (op U))
            ((structurePresheaf B S hS X.1).obj (op U)) := e₀
      exact Module.Finite.equiv ((e 0) ≪≫ e₁).toLinearEquiv.symm
    · have := hz i hi
      exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩

end RelativePseudoCoherence

/-! ### `X₀ = Spec A₀` -/

section StageZeroSpace

variable (hf : limit.π F (op 0) f = 0)

/-- `Spec A₀ ⟶ X = Spec B`, as a morphism of algebraic spaces. -/
def stageZeroSpaceMap :
    schemeSpace (baseObjectAt F (site F) (site_contains F) (site_contains_baseAt F hFs) 0) ⟶
      (space F f).left :=
  ObjectProperty.homMk (yoneda.map (stageZeroToQuotient F hFs f hf))

/-- `Spec A₀ ⟶ X ⟶ Spec A` is the projection `Spec A₀ ⟶ Spec A`. -/
theorem stageZeroSpaceMap_comp :
    stageZeroSpaceMap F hFs f hf ≫ (space F f).hom =
      baseSpaceProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) 0 := by
  apply ObjectProperty.hom_ext
  change yoneda.map (stageZeroToQuotient F hFs f hf) ≫ yoneda.map (quotientObjectToBase F f) =
    yoneda.map (baseObjectProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) 0)
  rw [← yoneda.map_comp]
  exact congrArg yoneda.map (Over.OverMorphism.ext (Over.w (stageZeroToQuotient F hFs f hf)))

/-- `X ⟶ Spec A` is a monomorphism, being a closed immersion. -/
instance mono_space_hom : Mono (space F f).hom :=
  (ObjectProperty.ι _).mono_of_mono_map
    (mono_of_isClosedImmersion _ _ _ _ (isClosedImmersion_space_hom F f))

/-- `Spec A₀` is the fibre product `X ×_{Spec A} Spec A₀`, `X ⟶ Spec A` being a monomorphism
through which `Spec A₀ ⟶ Spec A` factors. -/
theorem isPullback_stageZeroSpaceMap :
    IsPullback (𝟙 _) (stageZeroSpaceMap F hFs f hf)
      (baseSpaceProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) 0)
      (space F f).hom :=
  IsPullback.of_isLimit (c := PullbackCone.mk _ _ ((Category.id_comp _).trans
      (stageZeroSpaceMap_comp F hFs f hf).symm)) <|
    PullbackCone.IsLimit.mk _ (fun s => s.fst) (fun s => Category.comp_id _)
      (fun s => (cancel_mono (space F f).hom).1 ((Category.assoc _ _ _).trans
        ((congrArg (fun t => s.fst ≫ t) (stageZeroSpaceMap_comp F hFs f hf)).trans s.condition)))
      (fun s m h₁ _ => by simpa using h₁)

/-- `Spec A₀ ≅ X₀`. -/
abbrev stageZeroIso :
    schemeSpace (baseObjectAt F (site F) (site_contains F) (site_contains_baseAt F hFs) 0) ≅
      spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F f) 0 :=
  (isPullback_stageZeroSpaceMap F hFs f hf).isoIsPullback _ _
    (isPullback_spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F f) 0)

/-- `Spec A₀ ≅ X₀ ⟶ X` is `Spec A₀ ⟶ X`. -/
theorem stageZeroIso_hom_spaceProjection :
    (stageZeroIso F hFs f hf).hom ≫
        spaceProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F f) 0 =
      stageZeroSpaceMap F hFs f hf :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

end StageZeroSpace

/-! ### The system -/

section TheSystem

attribute [local instance] pointTopology

variable (hFl : ∀ n : ℕ,
    (RingHom.ker (F.map (homOfLE (Nat.le_succ n)).op).hom).LocallyNilpotent)
  (hFn : ∀ n : ℕ, IsNoetherianRing (F.obj (op n)))

include hFn in
/-- `Spec Aₙ` is locally Noetherian. -/
theorem isLocallyNoetherian_baseObjectAt (n : ℕ) :
    IsLocallyNoetherian ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).obj
      (baseObjectAt F (site F) (site_contains F) (site_contains_baseAt F hFs) n)) := by
  have := hFn n
  change IsLocallyNoetherian (Spec (F.obj (op n)))
  infer_instance

/-- **The counterexample to Stacks 0DIR without flatness**: `X = Spec A/(f)` and `Kₙ = 𝒪_{Xₙ}`. -/
def relativeDerivedExistenceSystem : RelativeDerivedExistenceSystem.{u} where
  system := F
  transition_surjective := hFs
  transition_locallyNilpotent := hFl
  B := site F
  containsLimitBase := site_contains F
  containsBaseAt := site_contains_baseAt F hFs
  X := space F f
  separated := isSeparated_space_hom F f
  finitePresentation := isFinitePresentation_space_hom F f
  K := structureObjectAt F hFs f
  quasicoherent := qcohDerived_structureObjectAt F hFs f
  relativelyPseudoCoherent n :=
    haveI := isLocallyNoetherian_baseObjectAt F hFs hFn n
    isRelativelyPseudoCoherent_structureObject _ _ _ _ _
  support _ := Set.univ
  isClosed_support _ := isClosed_univ
  isProperOver_support := isProperOver_univ F hFs f
  supported _ _ := Set.subset_univ _
  φ n := (structureObjectTransition F hFs f n).hom
  φ_isIso _ := inferInstance

end TheSystem

/-! ### No lift exists -/

section NoLift

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] enoughInjectives_modules_ringUniverse
  isGrothendieckAbelian_modules_ringUniverse
attribute [local instance] hasRightDerivedFunctor_chartSections

variable (hf : limit.π F (op 0) f = 0)

/-- `Spec B` is affine. -/
instance isAffine_quotientObject :
    IsAffine ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).obj
      (quotientObject F f)) :=
  inferInstanceAs (IsAffine (Spec _))

/-- `Spec A` is affine. -/
instance isAffine_limitBaseObject :
    IsAffine ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).obj
      (limitBaseObject F (site F) (site_contains F))) :=
  inferInstanceAs (IsAffine (Spec _))

/-- The map of global functions of `Spec A₀ ⟶ Spec B` is `B ⟶ A₀`, read through `Γ(Spec -) ≅ -`. -/
theorem appTop_spec_quotientToStageZero :
    (Spec.map (quotientToStageZero F f hf)).appTop =
      (Scheme.ΓSpecIso _).hom ≫ quotientToStageZero F f hf ≫ (Scheme.ΓSpecIso _).inv := by
  rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

include hFs in
/-- `Γ(Spec B) ⟶ Γ(Spec A₀)` is surjective. -/
theorem surjective_representedAffineCommRingCatHom_stageZeroToQuotient :
    Function.Surjective (representedAffineCommRingCatHom (site F) (limitBase F) (site_contains F)
        (stageZeroToQuotient F hFs f hf)).hom := by
  change Function.Surjective (Spec.map (quotientToStageZero F f hf)).appTop.hom
  rw [appTop_spec_quotientToStageZero]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  refine (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.surjective.comp
    (Function.Surjective.comp ?_ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.surjective)
  exact Ideal.Quotient.lift_surjective_of_surjective _ _
    (GrothendieckExistence.surjective_limit_π F hFs 0)

/-- The kernel of `Γ(Spec B) ⟶ Γ(Spec A₀)` is nilpotent when that of `A ⟶ A₀` is. -/
theorem isNilpotent_ker_representedAffineCommRingCatHom_stageZeroToQuotient
    (hnil : IsNilpotent (RingHom.ker (limit.π F (op 0)).hom)) :
    IsNilpotent (RingHom.ker (representedAffineCommRingCatHom (site F) (limitBase F)
      (site_contains F) (stageZeroToQuotient F hFs f hf)).hom) := by
  obtain ⟨n, hn⟩ := hnil
  rw [Ideal.zero_eq_bot] at hn
  have hρ : RingHom.ker (quotientToStageZero F f hf).hom ≤
      Ideal.map (Ideal.Quotient.mk (Ideal.span {f})) (RingHom.ker (limit.π F (op 0)).hom) := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.mem_map_of_mem _ hx
  have hρn : RingHom.ker (quotientToStageZero F f hf).hom ^ n = ⊥ := by
    refine le_antisymm ((Ideal.pow_right_mono hρ n).trans ?_) bot_le
    rw [← Ideal.map_pow, hn, Ideal.map_bot]
  change IsNilpotent (RingHom.ker (Spec.map (quotientToStageZero F f hf)).appTop.hom)
  have hker : RingHom.ker (Spec.map (quotientToStageZero F f hf)).appTop.hom =
      Ideal.comap (Scheme.ΓSpecIso (quotientRing F f)).hom.hom
        (RingHom.ker (quotientToStageZero F f hf).hom) := by
    ext x
    rw [appTop_spec_quotientToStageZero, RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    exact map_eq_zero_iff _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.injective
  refine ⟨n, ?_⟩
  rw [Ideal.zero_eq_bot, eq_bot_iff, hker]
  refine (Ideal.le_comap_pow _ n).trans ?_
  rw [hρn]
  intro x hx
  rw [Ideal.mem_comap, Ideal.mem_bot] at hx
  rw [Ideal.mem_bot]
  exact (map_eq_zero_iff _
    (Scheme.ΓSpecIso (quotientRing F f)).commRingCatIsoToRingEquiv.injective).1
    hx

/-- `RΓ(U, 𝒪[0]) ≅ Γ(U, 𝒪)[0]` on an affine representable algebraic space. -/
theorem nonempty_representedAffineDerivedSections_unit_iso {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] :
    Nonempty ((representedAffineDerivedSections B S hS U).obj
        ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) := by
  let E : DerivedCategory (AlgebraicGeometry.Space.Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) :=
    (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)
  have hE : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E :=
    qcohDerived_singleFunctor_structureModule (X := yoneda.obj U)
      (hX := isAlgebraicSpace_yoneda B S hS U)
  have : (representedAffineSections B S hS U).IsRightAdjoint :=
    (representedAffineAssociatedAdjunction B S hS U).isRightAdjoint
  have hz (j : ℤ) (hj : j ≠ 0) : IsZero ((DerivedCategory.homologyFunctor _ j).obj
      ((representedAffineDerivedSections B S hS U).obj E)) := by
    refine IsZero.of_iso (Functor.map_isZero (representedAffineSections B S hS U) ?_)
      (representedAffineDerivedSectionsHomologyIso B S hS U E hE j)
    rcases lt_or_gt_of_ne hj with hj | hj
    · exact DerivedCategory.isZero_of_isGE E 0 j hj
    · exact DerivedCategory.isZero_of_isLE E 0 j hj
  obtain ⟨e⟩ := ((representedAffineDerivedSections B S hS U).obj
    E).nonempty_iso_singleFunctor_homologyFunctor_of_isZero 0 hz
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso
    (representedAffineDerivedSectionsHomologyIso B S hS U E hE 0 ≪≫
      (representedAffineSections B S hS U).mapIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _) ≪≫
      representedAffineSectionsStructureModuleIso B S hS U)⟩

/-- **`RΓ(X, K) ⊗^L_B A₀ ≅ A₀[0]`** for `K ∈ D_QCoh(𝒪_X)` with `Lj₀^* K ≅ 𝒪_{X₀}`: the affine base
change of `RΓ` along `Spec A₀ ⟶ Spec B`, `X₀` being `Spec A₀`. -/
theorem nonempty_representedAffineDerivedExtension_iso
    (K : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf (site F) (limitBase F) (site_contains F) (space F f).left)))
    (hK : QcohDerived (site F) (limitBase F) (site_contains F) (space F f).left K)
    (ψ : (smallEtaleDerivedModulePullback (site F) (limitBase F) (site_contains F)
      (spaceProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F f) 0)).obj
        K ≅ structureObjectAt F hFs f 0) :
    Nonempty ((representedAffineDerivedExtension (site F) (limitBase F) (site_contains F)
        (stageZeroToQuotient F hFs f hf)).functor.obj
          ((representedAffineDerivedSections (site F) (limitBase F) (site_contains F)
            (quotientObject F f)).obj K) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).obj
            (baseObjectAt F (site F) (site_contains F) (site_contains_baseAt F hFs) 0), ⊤)
          Γ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).obj
            (baseObjectAt F (site F) (site_contains F) (site_contains_baseAt F hFs) 0), ⊤))) := by
  have := isIso_representedAffineDerivedSectionsBaseChangeMap (site F) (limitBase F)
    (site_contains F) (stageZeroToQuotient F hFs f hf) K hK
  let ι := (stageZeroIso F hFs f hf).hom
  let j₀ := spaceProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F f) 0
  have hι : ι ≫ j₀ = representedSpaceMap (site F) (limitBase F) (site_contains F)
      (stageZeroToQuotient F hFs f hf) :=
    stageZeroIso_hom_spaceProjection F hFs f hf
  let e₂ := (smallEtaleDerivedModulePullbackCongr (site F) (limitBase F) (site_contains F)
      hι).symm.app K ≪≫
    ((smallEtaleDerivedModulePullbackCompIso (site F) (limitBase F) (site_contains F) ι j₀).app
      K).symm ≪≫
    (smallEtaleDerivedModulePullback (site F) (limitBase F) (site_contains F) ι).mapIso ψ ≪≫
    smallEtaleDerivedModulePullbackUnitIso ι
  obtain ⟨e₃⟩ := nonempty_representedAffineDerivedSections_unit_iso
    (baseObjectAt F (site F) (site_contains F) (site_contains_baseAt F hFs) 0)
  exact ⟨asIso (representedAffineDerivedSectionsBaseChangeMap (site F) (limitBase F)
      (site_contains F) (stageZeroToQuotient F hFs f hf) K) ≪≫
    (representedAffineDerivedSections (site F) (limitBase F) (site_contains F) _).mapIso e₂ ≪≫ e₃⟩

/-- A module isomorphic to a pseudo-coherent module is pseudo-coherent. -/
theorem isModulePseudoCoherent_of_linearEquiv {R : Type u} [Ring R] {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (h : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := R) M) :
    StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := R) N :=
  StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso h
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso e.toModuleIso)

/-- The map of global functions of `Spec B ⟶ Spec A` is `A ⟶ B`, read through `Γ(Spec -) ≅ -`. -/
theorem appTop_quotientSpecMap :
    (quotientSpecMap F f).appTop =
      (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk _) ≫
        (Scheme.ΓSpecIso _).inv := by
  rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The map `Γ(Spec A) ⟶ Γ(Spec B)`, read on `A` and `B`, is the quotient map. -/
theorem ΓSpecIso_hom_appTop_quotientSpecMap (a : (limit F : CommRingCat.{u})) :
    (Scheme.ΓSpecIso (quotientRing F f)).hom.hom
        ((quotientSpecMap F f).appTop.hom ((Scheme.ΓSpecIso _).inv.hom a)) =
      Ideal.Quotient.mk _ a := by
  have h : (Scheme.ΓSpecIso _).inv ≫ (quotientSpecMap F f).appTop ≫
      (Scheme.ΓSpecIso (quotientRing F f)).hom = CommRingCat.ofHom (Ideal.Quotient.mk _) := by
    rw [appTop_quotientSpecMap]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Iso.inv_hom_id_assoc _ _
  exact congrArg (fun φ => φ.hom a) h

include hFs hf in
/-- **No pseudo-coherent lift of `𝒪_{X₀}` exists**: there is no `K ∈ D_QCoh(𝒪_X)` pseudo-coherent
relative to `Spec A` with `Lj₀^* K ≅ 𝒪_{X₀}`, as soon as `f` vanishes in `A₀`, the kernel of
`A ⟶ A₀` is nilpotent and `A/(f)` is not a pseudo-coherent `A`-module. -/
theorem not_exists_isRelativelyPseudoCoherent_stageZero_iso
    (hnil : IsNilpotent (RingHom.ker (limit.π F (op 0)).hom))
    (hnpc : ¬ StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := (limit F : CommRingCat.{u}))
      ((limit F : CommRingCat.{u}) ⧸ Ideal.span {f})) :
    ¬ ∃ (K : DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf (site F) (limitBase F) (site_contains F) (space F f).left)))
      (hK : QcohDerived (site F) (limitBase F) (site_contains F) (space F f).left K),
      IsRelativelyPseudoCoherent (site F) (limitBase F) (site_contains F) (space F f).left.1
          (space F f).left.2 (space F f).hom.hom
          (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation (site F) (limitBase F)
            (site_contains F) (isFinitePresentation_space_hom F f).1) ⟨K, hK⟩ ∧
        Nonempty ((smallEtaleDerivedModulePullback (site F) (limitBase F) (site_contains F)
          (spaceProjection F (site F) (site_contains F) (site_contains_baseAt F hFs)
            (space F f) 0)).obj K ≅ structureObjectAt F hFs f 0) := by
  rintro ⟨K, hK, hpc, ⟨ψ⟩⟩
  let T := quotientObject F f
  let RT := Γ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).obj T, ⊤)
  obtain ⟨e₁⟩ := nonempty_representedAffineDerivedExtension_iso F hFs f hf K hK ψ
  obtain ⟨eM⟩ :=
    StacksDraft.Perfect.nonempty_iso_singleFunctor_self_of_totalDerivedExtensionScalars_iso
    _ (surjective_representedAffineCommRingCatHom_stageZeroToQuotient F hFs f hf)
    (isNilpotent_ker_representedAffineCommRingCatHom_stageZeroToQuotient F hFs f hf hnil) _ e₁
  let U := selfChart (site F) (limitBase F) (site_contains F) T
  let V := selfChart (site F) (limitBase F) (site_contains F)
    (limitBaseObject F (site F) (site_contains F))
  have hUa : IsAffineChart (site F) (limitBase F) (site_contains F) (space F f).left.1 U :=
    isAffine_quotientObject F f
  let R := (structurePresheaf (site F) (limitBase F) (site_contains F) (space F f).left.1).obj
    (op U)
  let N := chartDerivedSections (site F) (limitBase F) (site_contains F) (space F f).left.1
    (space F f).left.2 U ⟨K, hK⟩
  let e (i : ℤ) : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj N ≅
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} RT) i).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} RT) 0).obj (ModuleCat.of RT RT)) :
          ModuleCat R) :=
    (chartDerivedSectionsHomologyIso _ _ _ (space F f).left K hK U hUa i).symm ≪≫
      (selfChartSectionsIso (site F) (limitBase F) (site_contains F) T).app _ ≪≫
      (representedAffineDerivedSectionsHomologyIso _ _ _ T K hK i).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} RT) i).mapIso eM
  have hz (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj N) := by
    have hz' : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} RT) i).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} RT) 0).obj (ModuleCat.of RT RT))) := by
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE _ 0 i hi
      · exact DerivedCategory.isZero_of_isLE _ 0 i hi
    exact hz'.of_iso (e i)
  obtain ⟨eN⟩ := N.nonempty_iso_singleFunctor_homologyFunctor_of_isZero 0 hz
  let e₀ : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj N ≅ ModuleCat.of R R :=
    e 0 ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} RT) 0).app
      (ModuleCat.of RT RT)
  let eN' : N ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) :=
    eN ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e₀
  have hc : yoneda.map (quotientObjectToBase F f) ≫ V.obj.hom =
      U.obj.hom ≫ (space F f).hom.hom :=
    (Category.comp_id _).trans (Category.id_comp _).symm
  have hU : IsAffine (chartScheme U) := isAffine_quotientObject F f
  have hV : IsAffine (chartScheme V) := isAffine_limitBaseObject F
  let RA := (structurePresheaf (site F) (limitBase F) (site_contains F)
    (schemeSpace (limitBaseObject F (site F) (site_contains F))).1).obj (op V)
  let : Algebra RA R := (quotientSpecMap F f).appTop.hom.toAlgebra
  let α : MvPolynomial (Fin 0) RA →ₐ[RA] R :=
    (Algebra.ofId RA R).comp (MvPolynomial.isEmptyAlgEquiv RA (Fin 0)).toAlgHom
  have hsurj : Function.Surjective (quotientSpecMap F f).appTop.hom := by
    rw [appTop_quotientSpecMap]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.surjective.comp
      (Ideal.Quotient.mk_surjective.comp
        (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.surjective)
  have hα : Function.Surjective α := by
    intro y
    obtain ⟨r, rfl⟩ := hsurj y
    exact ⟨MvPolynomial.C r, α.commutes r⟩
  have hm (m : ℤ) : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars.{u} α.toRingHom).mapDerivedCategory.obj N) m :=
    hpc m U V (quotientObjectToBase F f) hc hU hV 0 α hα
  have hP : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((ModuleCat.restrictScalars.{u} α.toRingHom).mapDerivedCategory.obj N) :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).2 hm
  have hP' : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := MvPolynomial (Fin 0) RA)
      ((ModuleCat.restrictScalars.{u} α.toRingHom).obj (ModuleCat.of R R)) :=
    StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso hP
      ((ModuleCat.restrictScalars.{u} α.toRingHom).mapDerivedCategory.mapIso eN' ≪≫
        ((ModuleCat.restrictScalars.{u} α.toRingHom).mapDerivedCategorySingleFunctor 0).app _)
  let e₂ : (limit F : CommRingCat.{u}) ≃+* MvPolynomial (Fin 0) RA :=
    (Scheme.ΓSpecIso (limit F)).commRingCatIsoToRingEquiv.symm.trans
      (MvPolynomial.isEmptyAlgEquiv RA (Fin 0)).toRingEquiv.symm
  have hA :=
    StacksDraft.PseudoCoherence.isModulePseudoCoherent_restrictScalars_of_ringEquiv e₂ _ hP'
  refine hnpc (isModulePseudoCoherent_of_linearEquiv ?_ hA)
  exact
    { toFun := fun x => (Scheme.ΓSpecIso (quotientRing F f)).hom.hom (show R from x)
      invFun := fun y => (Scheme.ΓSpecIso (quotientRing F f)).inv.hom y
      map_add' := fun x y => map_add (Scheme.ΓSpecIso (quotientRing F f)).hom.hom
        (show R from x) (show R from y)
      map_smul' := fun a x => by
        have h₁ : α (e₂ a) =
            (quotientSpecMap F f).appTop.hom ((Scheme.ΓSpecIso _).inv.hom a) := by
          change α ((MvPolynomial.isEmptyAlgEquiv RA (Fin 0)).symm
            ((Scheme.ΓSpecIso _).inv.hom a)) = _
          rw [show (MvPolynomial.isEmptyAlgEquiv RA (Fin 0)).symm ((Scheme.ΓSpecIso _).inv.hom a) =
              algebraMap RA _ ((Scheme.ΓSpecIso _).inv.hom a) from
            (MvPolynomial.isEmptyAlgEquiv RA (Fin 0)).symm.commutes _]
          exact α.commutes _
        have key (y : R) : (Scheme.ΓSpecIso (quotientRing F f)).hom.hom (α (e₂ a) * y) =
            a • (Scheme.ΓSpecIso (quotientRing F f)).hom.hom y := by
          refine (map_mul (Scheme.ΓSpecIso (quotientRing F f)).hom.hom
            (α (e₂ a) : Γ(Spec (quotientRing F f), ⊤)) (y : Γ(Spec (quotientRing F f), ⊤))).trans ?_
          rw [h₁]
          refine (congrArg (· * _) (ΓSpecIso_hom_appTop_quotientSpecMap F f a)).trans ?_
          rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
          rfl
        exact key x
      left_inv := fun x => congrArg (fun φ => CommRingCat.Hom.hom φ x)
        (Iso.hom_inv_id (Scheme.ΓSpecIso (quotientRing F f)))
      right_inv := fun y => congrArg (fun φ => CommRingCat.Hom.hom φ y)
        (Iso.inv_hom_id (Scheme.ΓSpecIso (quotientRing F f))) }

end NoLift

/-! ### The tower of square-zero extensions of `𝔽₂` -/

section SquareZeroTower

open Stacks.Examples.SquareZeroQuotientNotPseudoCoherent

attribute [local instance] HasDerivedCategory.standard

/-- The element `f = (0, (1, 1, …))` of `A = lim Aₙ`. -/
abbrev towerElement : (limit tower : CommRingCat.{0}) := limitIso.inv.hom onesElement

/-- `f` vanishes in `A₀`. -/
theorem limit_π_zero_towerElement : limit.π tower (op 0) towerElement = 0 := by
  rw [← limitIso_hom_comp_ofHom_limitProj 0]
  change limitProj 0 (limitIso.hom.hom (limitIso.inv.hom onesElement)) = 0
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, limitProj_zero_onesElement]

/-- An element of the kernel of `A ⟶ A₀` has vanishing `𝔽₂` component. -/
theorem fst_limitIso_hom_eq_zero {x : (limit tower : CommRingCat.{0})}
    (hx : x ∈ RingHom.ker (limit.π tower (op 0)).hom) : (limitIso.hom.hom x).fst = 0 := by
  have h : limitProj 0 (limitIso.hom.hom x) = 0 :=
    (congrArg (fun φ => CommRingCat.Hom.hom φ x) (limitIso_hom_comp_ofHom_limitProj 0)).trans hx
  simpa using congrArg TrivSqZeroExt.fst h

/-- The kernel of `A ⟶ A₀` has square zero. -/
theorem isNilpotent_ker_limit_π_zero : IsNilpotent (RingHom.ker (limit.π tower (op 0)).hom) := by
  refine ⟨2, ?_⟩
  rw [Ideal.zero_eq_bot, eq_bot_iff, pow_two, Submodule.mul_le]
  intro x hx y hy
  rw [Ideal.mem_bot]
  apply limitIso.commRingCatIsoToRingEquiv.injective
  have h₁ := fst_limitIso_hom_eq_zero hx
  have h₂ := fst_limitIso_hom_eq_zero hy
  change limitIso.hom.hom (x * y) = limitIso.hom.hom 0
  rw [map_mul, map_zero]
  ext i
  · simp [h₁]
  · simp [h₁, h₂]

/-- `A/(f)` is not a pseudo-coherent `A`-module. -/
theorem not_isModulePseudoCoherent_quotient_towerElement :
    ¬ StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := (limit tower : CommRingCat.{0}))
      ((limit tower : CommRingCat.{0}) ⧸ Ideal.span {towerElement}) := by
  intro h
  let e : limitRing ≃+* (limit tower : CommRingCat.{0}) :=
    limitIso.commRingCatIsoToRingEquiv.symm
  have h' := StacksDraft.PseudoCoherence.isModulePseudoCoherent_restrictScalars_of_ringEquiv e
    (ModuleCat.of _ ((limit tower : CommRingCat.{0}) ⧸ Ideal.span {towerElement})) h
  have hI : Ideal.span {onesElement} = (Ideal.span {towerElement}).map e.symm := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact (e.symm_apply_apply onesElement).symm
  refine not_isModulePseudoCoherent_quotient (isModulePseudoCoherent_of_linearEquiv ?_ h')
  exact
    { toFun := fun q => Ideal.quotientMap _ e.symm.toRingHom
        (by rw [hI]; exact Ideal.le_comap_map) (show _ ⧸ Ideal.span {towerElement} from q)
      invFun := fun q => (Ideal.quotientEquiv _ _ e.symm hI).symm q
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun a q => by
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (show _ ⧸ Ideal.span {towerElement} from q)
        change Ideal.Quotient.mk _ (e.symm (e a * b)) = a • Ideal.Quotient.mk _ (e.symm b)
        rw [map_mul, e.symm_apply_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
          ← map_mul]
      left_inv := fun q => (Ideal.quotientEquiv _ _ e.symm hI).symm_apply_apply q
      right_inv := fun q => (Ideal.quotientEquiv _ _ e.symm hI).apply_symm_apply q }

/-- **The generalization of the derived existence theorem proposed in Stacks 0DIR is false
without flatness.** There is a system satisfying all of its hypotheses — `Aₙ = 𝔽₂ ⊕ 𝔽₂ⁿ`,
`X = Spec A/(f)` closed in `Spec A`, `Kₙ = 𝒪_{Xₙ}` — admitting no `K ∈ D_QCoh(𝒪_X)`
pseudo-coherent relative to `A` with `Ljₙ^* K ≅ Kₙ` for every `n` (not even for `n = 0`, and
with no compatibility asked of the isomorphisms). -/
@[stacks 0DIR "refutation of the remark with X separated and of finite presentation, not flat: \
X = Spec A/(f), K_n = O_{X_n} admits no K pseudo-coherent relative to A with Lj_n^* K = K_n \
(errata entry 0DIR(flatness dropped))"]
theorem not_forall_exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso :
    ¬ ∀ D : RelativeDerivedExistenceSystem.{0},
      ∃ (K : DerivedCategory (SheafOfModules.{0}
          (ringedToposStructureRingSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left)))
        (hK : QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left K),
        IsRelativelyPseudoCoherent D.B (limitBase D.system) D.containsLimitBase D.X.left.1
            D.X.left.2 D.X.hom.hom
            (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
              D.containsLimitBase D.finitePresentation.1) ⟨K, hK⟩ ∧
          ∀ n : ℕ, Nonempty ((smallEtaleDerivedModulePullback D.B (limitBase D.system)
            D.containsLimitBase (spaceProjection D.system D.B D.containsLimitBase
              D.containsBaseAt D.X n)).obj K ≅ D.K n) := by
  intro h
  obtain ⟨K, hK, hpc, hiso⟩ := h (relativeDerivedExistenceSystem tower surjective_tower_map_succ
    towerElement locallyNilpotent_ker_tower_map_succ
    (fun n => inferInstanceAs (IsNoetherianRing (towerRing n))))
  exact not_exists_isRelativelyPseudoCoherent_stageZero_iso tower surjective_tower_map_succ
    towerElement limit_π_zero_towerElement isNilpotent_ker_limit_π_zero
    not_isModulePseudoCoherent_quotient_towerElement ⟨K, hK, hpc, hiso 0⟩

end SquareZeroTower

end Stacks.Examples.DerivedExistenceNotFlat

end
