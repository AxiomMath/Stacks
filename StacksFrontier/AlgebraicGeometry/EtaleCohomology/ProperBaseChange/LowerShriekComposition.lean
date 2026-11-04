module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.CompactificationsUnconditional
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateCompTransfer
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import StacksFrontier.CategoryTheory.Sites.ContinuousPushforwardMates
public import StacksFrontier.RingTheory.PseudoCoherentMap.Locality

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalPaste
public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.PreservesInterior
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.Dominating
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing

/-!
# Independence of the compactification and composition for the derived lower shriek

Let `f : X ⟶ Y` be a separated morphism of finite type of quasi-compact and quasi-separated
schemes. The derived lower shriek `Rf_! = Rf̄_* ∘ Rj_!` of [Stacks, Tag 0F7H] is
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded`, on `D(-_étale, Λ)`, and depends on a
compactification `j : X ⟶ X̄` of `X` over `Y`. This file compares the functors attached to two
compactifications (the objectwise content of [Stacks, Tag 0F7I]) and composes them
([Stacks, Tag 0F7J]).

## Main definitions

* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompactificationIsoUnconditional` — for two
  compactifications `j₁`, `j₂` of `X` over `Y` and `K` bounded below with torsion cohomology,
  `Rf_!^{(1)} K ≅ Rf_!^{(2)} K`, through the compactification dominating both, granted the proper
  base change theorem.
* `AlgebraicGeometry.CompactificationOf.overCompactificationRestrict` and
  `AlgebraicGeometry.CompactificationOf.overCompactificationComp` — for a compactification
  `i : Y ⟶ Ȳ` of `g : Y ⟶ Z` and a compactification `J` of `X` over `Ȳ`, the compactifications of
  `f` and of `g ∘ f` used in the proof of Tag 0F7J.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompMap` — the map
  `Rg_! ∘ Rf_! ⟶ R(g ∘ f)_!` of Tag 0F7J for those compactifications.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIsoUniv` — Tag 0F7J for arbitrary
  compactifications, objectwise on bounded below objects with torsion cohomology, granted the
  proper base change theorem.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedThickeningIso` — **Tag 0GKQ**:
  `Rf_! ∘ i⁻¹ ≅ Rf'_!` for a thickening `i`, with the compactification induced on `X`.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedGeometricFibreIso` — Tag 0GK0,
  `RΓ(Spec k, ȳ⁻¹ Rf_! K) ≅ RΓ_c(X_ȳ, K|_{X_ȳ})`, granted the proper base change theorem.

## Main results

* `Stacks.EtaleCohomology.isIso_derivedLowerShriekUnboundedCompMap_app` — the map of Tag 0F7J
  is invertible on bounded below objects with torsion cohomology, granted the proper base change
  theorem.
* `Stacks.EtaleCohomology.isIso_etaleModuleInverseImageAdj_unit_of_universalHomeomorphism` —
  along a universal homeomorphism `F ⟶ i_* i⁻¹ F` is an isomorphism of sheaves of `Λ`-modules.

## References

* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
* [Stacks Project, Tag 0GKQ](https://stacks.math.columbia.edu/tag/0GKQ)
* [Stacks Project, Tag 0GK0](https://stacks.math.columbia.edu/tag/0GK0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.CompactificationOf

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-! ### Two compactifications -/

section Independence

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (j₁ j₂ : CompactificationOf (Over.mk f))
  (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
  (K : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) [K.IsGE n]
  (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X).obj K))

include h095T n hK in
/-- The comparison `Rf_!^{(1)} K ⟶ Rf_!^{(W)} K` of Tag 0F7G from the compactification `j₁` to
the compactification `W` dominating `j₁` and `j₂` is an isomorphism on bounded below objects with
torsion cohomology, granted the proper base change theorem. -/
theorem isIso_derivedLowerShriekCompactificationHom_dominatingFst_app :
    IsIso ((derivedLowerShriekCompactificationHom.{u, r} Λ (dominatingFst j₁ j₂)
      (isPullback_dominatingFst j₁ j₂)).app K) :=
  isIso_derivedLowerShriekCompactificationHom_app_of_cohomologyCommutesWithBaseChange.{u, r} Λ
    _ _ h095T K n hK

include h095T n hK in
/-- The comparison `Rf_!^{(2)} K ⟶ Rf_!^{(W)} K` from the compactification `j₂` to the
compactification `W` dominating `j₁` and `j₂` is an isomorphism on bounded below objects with
torsion cohomology, granted the proper base change theorem. -/
theorem isIso_derivedLowerShriekCompactificationHom_dominatingSnd_app :
    IsIso ((derivedLowerShriekCompactificationHom.{u, r} Λ (dominatingSnd j₁ j₂)
      (isPullback_dominatingSnd j₁ j₂)).app K) :=
  isIso_derivedLowerShriekCompactificationHom_app_of_cohomologyCommutesWithBaseChange.{u, r} Λ
    _ _ h095T K n hK

/-- **The derived lower shriek does not depend on the compactification**, objectwise on bounded
below objects with torsion cohomology, granted the proper base change theorem (`h095T`, Stacks
Tag 095T). For two compactifications `j₁`, `j₂` of `X` over `Y`, the isomorphism
`Rf_!^{(1)} K ≅ Rf_!^{(W)} K ≅ Rf_!^{(2)} K` through the compactification `W` of `X` dominating
both (`AlgebraicGeometry.CompactificationOf.dominating`), each step being the comparison of
Tag 0F7G along a morphism of compactifications cartesian over `X`. -/
def derivedLowerShriekUnboundedCompactificationIsoUnconditional :
    (derivedLowerShriekUnbounded.{u, r} f j₁ Λ).obj K ≅
      (derivedLowerShriekUnbounded.{u, r} f j₂ Λ).obj K :=
  haveI := isIso_derivedLowerShriekCompactificationHom_dominatingFst_app Λ j₁ j₂ h095T K n hK
  haveI := isIso_derivedLowerShriekCompactificationHom_dominatingSnd_app Λ j₁ j₂ h095T K n hK
  asIso ((derivedLowerShriekCompactificationHom.{u, r} Λ (dominatingFst j₁ j₂)
      (isPullback_dominatingFst j₁ j₂)).app K) ≪≫
    (asIso ((derivedLowerShriekCompactificationHom.{u, r} Λ (dominatingSnd j₁ j₂)
      (isPullback_dominatingSnd j₁ j₂)).app K)).symm

end Independence

end Stacks.EtaleCohomology

/-! ### The compactifications of a composite -/

namespace AlgebraicGeometry.CompactificationOf

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (jg : CompactificationOf (Over.mk g))
  (J : CompactificationOf (Over.mk (f ≫ jg.immersion)))

/-- **The compactification of `f` cut out of a compactification of `X` over `Ȳ`.** For a
compactification `i : Y ⟶ Ȳ` of `g` and a compactification `J : X ⟶ X̄` of `i ∘ f : X ⟶ Ȳ`, the
inverse image `U = X̄ ×_Ȳ Y` of `Y` in `X̄`, proper over `Y`, with the open immersion
`X ⟶ U`. -/
abbrev overCompactificationRestrict : CompactificationOf (Over.mk f) :=
  J.baseChange (show IsPullback (𝟙 X) f (f ≫ jg.immersion) jg.immersion from
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩)

/-- **The compactification of `g ∘ f` given by a compactification of `X` over `Ȳ`.** For a
compactification `i : Y ⟶ Ȳ` of `g` and a compactification `J : X ⟶ X̄` of `i ∘ f`, the open
immersion `J` itself, `X̄` being proper over `Z` through `X̄ ⟶ Ȳ ⟶ Z`. -/
def overCompactificationComp : CompactificationOf (Over.mk (f ≫ g)) :=
  ⟨StructuredArrow.mk (Y := Over.mk (J.toBase ≫ jg.toBase))
      (Over.homMk (U := Over.mk (f ≫ g)) (V := Over.mk (J.toBase ≫ jg.toBase)) J.immersion
        (by simp)),
    ⟨(inferInstance : IsOpenImmersion J.immersion),
      (inferInstance : IsProper (J.toBase ≫ jg.toBase))⟩⟩

/-- The ambient scheme of `overCompactificationComp jg J` is that of `J`. -/
@[simp]
lemma overCompactificationComp_space : (overCompactificationComp jg J).space = J.space := rfl

/-- The open immersion of `overCompactificationComp jg J` is that of `J`. -/
@[simp]
lemma overCompactificationComp_immersion :
    (overCompactificationComp jg J).immersion = J.immersion := rfl

/-- The structure morphism of `overCompactificationComp jg J` is `X̄ ⟶ Ȳ ⟶ Z`. -/
@[simp]
lemma overCompactificationComp_toBase :
    (overCompactificationComp jg J).toBase = J.toBase ≫ jg.toBase := rfl

/-- The open immersion `U = X̄ ×_Ȳ Y ⟶ X̄` of the ambient scheme of the restricted
compactification into `X̄`. -/
def overCompactificationRestrictι : (overCompactificationRestrict jg J).space ⟶ J.space :=
  pullback.fst J.toBase jg.immersion

/-- The morphism `U = X̄ ×_Ȳ Y ⟶ X̄` is an open immersion. -/
instance : IsOpenImmersion (overCompactificationRestrictι jg J) :=
  inferInstanceAs (IsOpenImmersion (pullback.fst J.toBase jg.immersion))

/-- The ambient scheme `U` of the restricted compactification is the inverse image of `Y` in
`X̄`. -/
theorem isPullback_overCompactificationRestrict :
    IsPullback (overCompactificationRestrictι jg J) (overCompactificationRestrict jg J).toBase
      J.toBase jg.immersion :=
  IsPullback.of_hasPullback J.toBase jg.immersion

/-- The open immersion of the restricted compactification followed by `U ⟶ X̄` is `J`. -/
@[reassoc (attr := simp)]
lemma overCompactificationRestrict_immersion_ι :
    (overCompactificationRestrict jg J).immersion ≫ overCompactificationRestrictι jg J =
      J.immersion :=
  (pullback.lift_fst _ _ _).trans (Category.id_comp _)

section OfComp

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (jg : CompactificationOf (Over.mk g))
  (jgf : CompactificationOf (Over.mk (f ≫ g)))

/-- The morphism `(J_{g ∘ f}, i ∘ f) : X ⟶ X̄ ×_Z Ȳ` attached to a compactification
`J_{g ∘ f} : X ⟶ X̄` of `g ∘ f` and a compactification `i : Y ⟶ Ȳ` of `g`. -/
abbrev overCompactificationOfLift : X ⟶ pullback jgf.toBase jg.toBase :=
  pullback.lift jgf.immersion (f ≫ jg.immersion) (by
    rw [immersion_toBase_general, Category.assoc, immersion_toBase_general])

variable [QuasiCompact jgf.immersion]

/-- Over the interior of `X̄`, the scheme-theoretic image of `(J_{g ∘ f}, i ∘ f)` is `X`. -/
theorem isPullback_overCompactificationOfLift :
    IsPullback (overCompactificationOfLift jg jgf).toImage (𝟙 X)
      ((overCompactificationOfLift jg jgf).imageι ≫ pullback.fst jgf.toBase jg.toBase)
      jgf.immersion :=
  isPullback_toImage_of_comp_eq_openImmersion _ _ _ (pullback.lift_fst _ _ _)

/-- The morphism from `X` to the scheme-theoretic image of `(J_{g ∘ f}, i ∘ f)` is an open
immersion. -/
instance isOpenImmersion_overCompactificationOfLift_toImage :
    IsOpenImmersion (overCompactificationOfLift jg jgf).toImage :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_overCompactificationOfLift jg jgf).flip inferInstance

/-- **A compactification of `X` over `Ȳ` built from a compactification of `g ∘ f`** (the
construction of [Stacks, Tag 0A9Z]). For a compactification `i : Y ⟶ Ȳ` of `g` and a
compactification `J_{g ∘ f} : X ⟶ X̄` of `g ∘ f`, the open immersion of `X` into the
scheme-theoretic image `X̄'` of `(J_{g ∘ f}, i ∘ f) : X ⟶ X̄ ×_Z Ȳ`, which is closed in
`X̄ ×_Z Ȳ` and hence proper over `Ȳ`. With it the composition isomorphism of Tag 0F7J needs no
appeal to Nagata's theorem (Tag 0F41). -/
def overCompactificationOf : CompactificationOf (Over.mk (f ≫ jg.immersion)) :=
  ⟨StructuredArrow.mk (Y := Over.mk ((overCompactificationOfLift jg jgf).imageι ≫
      pullback.snd jgf.toBase jg.toBase))
      (Over.homMk (U := Over.mk (f ≫ jg.immersion))
        (V := Over.mk ((overCompactificationOfLift jg jgf).imageι ≫
          pullback.snd jgf.toBase jg.toBase))
        (overCompactificationOfLift jg jgf).toImage (by
          simp only [Over.mk_hom, Scheme.Hom.toImage_imageι_assoc, pullback.lift_snd])),
    ⟨(inferInstance : IsOpenImmersion (overCompactificationOfLift jg jgf).toImage),
      (inferInstance : IsProper ((overCompactificationOfLift jg jgf).imageι ≫
        pullback.snd jgf.toBase jg.toBase))⟩⟩

/-- The open immersion of `overCompactificationOf jg jgf` is the morphism from `X` to the
scheme-theoretic image `X̄'` of `(J_{g ∘ f}, i ∘ f)`. -/
@[simp]
lemma overCompactificationOf_immersion :
    (overCompactificationOf jg jgf).immersion = (overCompactificationOfLift jg jgf).toImage :=
  rfl

/-- The structure morphism of `overCompactificationOf jg jgf` is `X̄' ⟶ X̄ ×_Z Ȳ ⟶ Ȳ`. -/
@[simp]
lemma overCompactificationOf_toBase :
    (overCompactificationOf jg jgf).toBase =
      (overCompactificationOfLift jg jgf).imageι ≫ pullback.snd jgf.toBase jg.toBase :=
  rfl

/-- The morphism from the compactification of `g ∘ f` given by `overCompactificationOf` to the
compactification `J_{g ∘ f}` it was built from: the projection `X̄' ⟶ X̄`. -/
def overCompactificationOfHom :
    overCompactificationComp jg (overCompactificationOf jg jgf) ⟶ jgf :=
  ObjectProperty.homMk (StructuredArrow.homMk
    (Over.homMk ((overCompactificationOfLift jg jgf).imageι ≫ pullback.fst jgf.toBase jg.toBase)
      (by
        change ((overCompactificationOfLift jg jgf).imageι ≫
            pullback.fst jgf.toBase jg.toBase) ≫ jgf.toBase =
          ((overCompactificationOfLift jg jgf).imageι ≫ pullback.snd jgf.toBase jg.toBase) ≫
            jg.toBase
        rw [Category.assoc, Category.assoc, pullback.condition])) (by
      ext
      change (overCompactificationOfLift jg jgf).toImage ≫
          (overCompactificationOfLift jg jgf).imageι ≫ pullback.fst jgf.toBase jg.toBase =
        jgf.immersion
      rw [Scheme.Hom.toImage_imageι_assoc, pullback.lift_fst]))

/-- The underlying morphism of `overCompactificationOfHom jg jgf` is the projection
`X̄' ⟶ X̄ ×_Z Ȳ ⟶ X̄`. -/
@[simp]
lemma overCompactificationOfHom_map :
    Hom.map (overCompactificationOfHom jg jgf) =
      (overCompactificationOfLift jg jgf).imageι ≫ pullback.fst jgf.toBase jg.toBase :=
  rfl

/-- `X` is cartesian along the morphism `overCompactificationOfHom`. -/
theorem isPullback_overCompactificationOfHom :
    IsPullback (overCompactificationComp jg (overCompactificationOf jg jgf)).immersion (𝟙 X)
      (Hom.map (overCompactificationOfHom jg jgf)) jgf.immersion :=
  isPullback_overCompactificationOfLift jg jgf

end OfComp

end AlgebraicGeometry.CompactificationOf

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-! ### Extension by zero along equal and composite morphisms -/

section ExtensionByZero

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition

/-- Extension by zero along two equal étale morphisms, on `D(-_étale, Λ)`. -/
def etaleModuleDerivedExtensionByZeroUnboundedCongr {U X : Scheme.{u}} {a b : U ⟶ X} [Etale a]
    [Etale b] (h : a = b) :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ a ≅
      etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ b := by
  subst h
  exact Iso.refl _

/-- **Derived extension by zero composes**: `R(a ≫ b)_! ≅ Ra_! ⋙ Rb_!` on `D(-_étale, Λ)` for
étale morphisms `a` and `b`, the comparison of two left adjoints of `(a ≫ b)⁻¹ ≅ b⁻¹ ⋙ a⁻¹`
(`etaleModuleDerivedInverseImageCompIsoUnconditional`). -/
def etaleModuleDerivedExtensionByZeroUnboundedCompIso {U X W : Scheme.{u}} (a : U ⟶ X)
    (b : X ⟶ W) [Etale a] [Etale b] :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ (a ≫ b) ≅
      etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ a ⋙
        etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ b :=
  (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ (a ≫ b)).leftAdjointUniq
    (((etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ a).comp
      (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ b)).ofNatIsoRight
        (etaleModuleDerivedInverseImageCompIsoUnconditional.{u, r} Λ a b).symm)

/-- **The composition isomorphism of derived extensions by zero against the units.** The unit of
`R(a ≫ b)_! ⊣ (a ≫ b)⁻¹` followed by `(a ≫ b)⁻¹` of `R(a ≫ b)_! ≅ Ra_! ⋙ Rb_!` is the unit of
`Ra_! ⊣ a⁻¹`, then `a⁻¹` of the unit of `Rb_! ⊣ b⁻¹`, then `b⁻¹ ⋙ a⁻¹ ≅ (a ≫ b)⁻¹`. -/
@[reassoc]
theorem etaleModuleDerivedExtensionByZeroUnboundedCompIso_hom_unit {U X W : Scheme.{u}}
    (a : U ⟶ X) (b : X ⟶ W) [Etale a] [Etale b] (K : DerivedCategory (EtaleModules.{u, r} Λ U)) :
    (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ (a ≫ b)).unit.app K ≫
        (etaleModuleDerivedInverseImageGeneral.{u, r} Λ (a ≫ b)).map
          ((etaleModuleDerivedExtensionByZeroUnboundedCompIso.{u, r} Λ a b).hom.app K) =
      (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ a).unit.app K ≫
        (etaleModuleDerivedInverseImageGeneral.{u, r} Λ a).map
          ((etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ b).unit.app
            ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ a).obj K)) ≫
        (etaleModuleDerivedInverseImageCompIsoUnconditional.{u, r} Λ a b).inv.app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ b).obj
            ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ a).obj K)) := by
  rw [etaleModuleDerivedExtensionByZeroUnboundedCompIso, Adjunction.unit_leftAdjointUniq_hom_app]
  simp [Adjunction.comp_unit_app]

/-- **The conjugate of the composition isomorphism of derived extensions by zero** is the
composition isomorphism of derived inverse images: under `Ra_! ⋙ Rb_! ⊣ b⁻¹ ⋙ a⁻¹` and
`R(a ≫ b)_! ⊣ (a ≫ b)⁻¹`, `R(a ≫ b)_! ⟶ Ra_! ⋙ Rb_!` corresponds to
`b⁻¹ ⋙ a⁻¹ ⟶ (a ≫ b)⁻¹`. -/
theorem conjugateEquiv_etaleModuleDerivedExtensionByZeroUnboundedCompIso_hom {U X W : Scheme.{u}}
    (a : U ⟶ X) (b : X ⟶ W) [Etale a] [Etale b] :
    conjugateEquiv ((etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ a).comp
        (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ b))
        (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ (a ≫ b))
        (etaleModuleDerivedExtensionByZeroUnboundedCompIso.{u, r} Λ a b).hom =
      (etaleModuleDerivedInverseImageCompIsoUnconditional.{u, r} Λ a b).inv := by
  have h := leftAdjointUniq_eq_conjugateEquiv_symm_id
    (((etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ a).comp
      (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ b)).ofNatIsoRight
        (etaleModuleDerivedInverseImageCompIsoUnconditional.{u, r} Λ a b).symm)
    (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ (a ≫ b))
  have h2 := Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_left
    ((etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ a).comp
      (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ b))
    (etaleModuleDerivedInverseImageCompIsoUnconditional.{u, r} Λ a b).symm
    (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ (a ≫ b))
    (etaleModuleDerivedExtensionByZeroUnboundedCompIso.{u, r} Λ a b).hom
  rw [etaleModuleDerivedExtensionByZeroUnboundedCompIso, h, Equiv.apply_symm_apply,
    Iso.symm_inv] at h2
  have h3 := h2.symm
  rw [← Iso.eq_inv_comp, Category.comp_id] at h3
  rw [etaleModuleDerivedExtensionByZeroUnboundedCompIso, h]
  exact h3

end ExtensionByZero

/-! ### Composition of derived lower shriek functors -/

section Composition

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (jg : CompactificationOf (Over.mk g))
  (J : CompactificationOf (Over.mk (f ≫ jg.immersion)))

/-- The rebracketing `Rg_! ∘ Rf_! ≅ Rj_! ⋙ ((Rf'_* ⋙ Ri_!) ⋙ Rḡ_*)` of the source of the map of
Tag 0F7J. -/
def derivedLowerShriekUnboundedCompMapSourceIso :
    derivedLowerShriekUnbounded.{u, r} f (overCompactificationRestrict jg J) Λ ⋙
        derivedLowerShriekUnbounded.{u, r} g jg Λ ≅
      etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ
          (overCompactificationRestrict jg J).immersion ⋙
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ
            (overCompactificationRestrict jg J).toBase ⋙
          etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ jg.immersion) ⋙
          etaleModuleDerivedDirectImageUnbounded.{u, r} Λ jg.toBase) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm

/-- The identification `Rj_! ⋙ ((Rj'_! ⋙ Rf̄_*) ⋙ Rḡ_*) ≅ R(g ∘ f)_!` of the target of the map of
Tag 0F7J: `j'_! ∘ j_! = J_!` and `Rḡ_* ∘ Rf̄_* = R(ḡ ∘ f̄)_*`. -/
def derivedLowerShriekUnboundedCompMapTargetIso :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ
          (overCompactificationRestrict jg J).immersion ⋙
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ (overCompactificationRestrictι jg J) ⋙
          etaleModuleDerivedDirectImageUnbounded.{u, r} Λ J.toBase) ⋙
          etaleModuleDerivedDirectImageUnbounded.{u, r} Λ jg.toBase) ≅
      derivedLowerShriekUnbounded.{u, r} (f ≫ g) (overCompactificationComp jg J) Λ :=
  Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((etaleModuleDerivedExtensionByZeroUnboundedCompIso.{u, r} Λ
          (overCompactificationRestrict jg J).immersion
          (overCompactificationRestrictι jg J)).symm ≪≫
        etaleModuleDerivedExtensionByZeroUnboundedCongr.{u, r} Λ
          (overCompactificationRestrict_immersion_ι jg J)) _ ≪≫
    Functor.isoWhiskerLeft _
      (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ J.toBase jg.toBase
        (J.toBase ≫ jg.toBase) rfl).symm

/-- **The map of [Stacks, Tag 0F7J] for compatible compactifications.** Let `i : Y ⟶ Ȳ` be a
compactification of `g` over `Z` and `J : X ⟶ X̄` a compactification of `i ∘ f` over `Ȳ`; let
`U = X̄ ×_Ȳ Y` with `f' : U ⟶ Y` and `j : X ⟶ U`, `j' : U ⟶ X̄`, so that `Rf_! = Rf'_* ∘ Rj_!`
and `R(g ∘ f)_! = R(ḡ ∘ f̄)_* ∘ RJ_!`. The map
```
Rg_! ∘ Rf_! = Rḡ_* ∘ Ri_! ∘ Rf'_* ∘ Rj_! ⟶ Rḡ_* ∘ Rf̄_* ∘ Rj'_! ∘ Rj_! ≅ R(ḡ ∘ f̄)_* ∘ RJ_!
```
on `D(-_étale, Λ)`, whose middle arrow is the map `i_! ∘ Rf'_* ⟶ Rf̄_* ∘ j'_!` of Tag 0F7B for the
cartesian square of `f̄` along `i`. -/
def derivedLowerShriekUnboundedCompMap :
    derivedLowerShriekUnbounded.{u, r} f (overCompactificationRestrict jg J) Λ ⋙
        derivedLowerShriekUnbounded.{u, r} g jg Λ ⟶
      derivedLowerShriekUnbounded.{u, r} (f ≫ g) (overCompactificationComp jg J) Λ :=
  (derivedLowerShriekUnboundedCompMapSourceIso.{u, r} Λ jg J).hom ≫
    Functor.whiskerLeft _
      (Functor.whiskerRight (extensionByZeroDerivedDirectImageMap.{u, r} Λ jg.immersion J.toBase
        (overCompactificationRestrictι jg J) (overCompactificationRestrict jg J).toBase
        (isPullback_overCompactificationRestrict jg J)) _) ≫
    (derivedLowerShriekUnboundedCompMapTargetIso.{u, r} Λ jg J).hom

/-- **[Stacks, Tag 0F7J] for compatible compactifications, granted the proper base change
theorem.** The map `Rg_! Rf_! K ⟶ R(g ∘ f)_! K` of `derivedLowerShriekUnboundedCompMap` is an
isomorphism for every `K` in `D(X_étale, Λ)` bounded below whose underlying complex of abelian
sheaves has torsion cohomology sheaves: its middle arrow is invertible there by Tag 0F7B (a),
`Rj_! K` being again bounded below with torsion cohomology. -/
theorem isIso_derivedLowerShriekUnboundedCompMap_app
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) [K.IsGE n]
    (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X).obj K)) :
    IsIso ((derivedLowerShriekUnboundedCompMap.{u, r} Λ jg J).app K) := by
  have hGE : ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ
      (overCompactificationRestrict jg J).immersion).obj K).IsGE n := by
    have := Functor.isGE_obj_mapDerivedCategory
      (etaleModuleExtensionByZero.{u, r} Λ (overCompactificationRestrict jg J).immersion) K n
      inferInstance
    exact DerivedCategory.TStructure.t.isGE_of_iso
      ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ
        (overCompactificationRestrict jg J).immersion).app K).symm n
  have hγ :=
    @isIso_extensionByZeroDerivedDirectImageMap_app_of_cohomologyCommutesWithBaseChange.{u, r}
    Λ _ _ _ _ _ jg.immersion J.toBase (overCompactificationRestrictι jg J)
    (overCompactificationRestrict jg J).toBase _ _ (isPullback_overCompactificationRestrict jg J)
    (h095T J.toBase) ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ
      (overCompactificationRestrict jg J).immersion).obj K) n hGE
    (torsionCohomologyProperty_etaleModuleForgetDerived_extensionByZero.{u, r} Λ
      (overCompactificationRestrict jg J).immersion K hK)
  simp only [derivedLowerShriekUnboundedCompMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

/-- **[Stacks, Tag 0F7J], granted the proper base change theorem.** Let `f : X ⟶ Y` and
`g : Y ⟶ Z` be separated morphisms of finite type of quasi-compact and quasi-separated schemes,
with compactifications `j_f`, `j_g` and `j_{g ∘ f}` of `f`, `g` and `g ∘ f`. For every `K` in
`D(X_étale, Λ)` bounded below whose underlying complex of abelian sheaves has torsion cohomology
sheaves there is an isomorphism `Rg_! (Rf_! K) ≅ R(g ∘ f)_! K`, the three functors computed through
`j_g`, `j_f` and `j_{g ∘ f}`.

A compactification `J` of `X` over `Ȳ` gives compatible compactifications of `f` and `g ∘ f`,
for which this is `derivedLowerShriekUnboundedCompMap`; the comparisons with `j_f` and `j_{g ∘ f}`
are the identifications `derivedLowerShriekUnboundedCompactificationIsoUnconditional` of
Tag 0F7I. The compactification `J` is
`AlgebraicGeometry.CompactificationOf.overCompactificationOf`, built from `j_g` and `j_{g ∘ f}`
(the construction of Tag 0A9Z). -/
def derivedLowerShriekUnboundedCompIsoUniv [QuasiCompact f] [QuasiCompact g]
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (jf : CompactificationOf (Over.mk f)) (jgf : CompactificationOf (Over.mk (f ≫ g)))
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) [K.IsGE n]
    (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X).obj K)) :
    (derivedLowerShriekUnbounded.{u, r} g jg Λ).obj
        ((derivedLowerShriekUnbounded.{u, r} f jf Λ).obj K) ≅
      (derivedLowerShriekUnbounded.{u, r} (f ≫ g) jgf Λ).obj K :=
  haveI := isIso_derivedLowerShriekUnboundedCompMap_app.{u, r} Λ jg (overCompactificationOf jg jgf)
    h095T K n hK
  (derivedLowerShriekUnbounded.{u, r} g jg Λ).mapIso
      (derivedLowerShriekUnboundedCompactificationIsoUnconditional.{u, r} Λ jf
        (overCompactificationRestrict jg (overCompactificationOf jg jgf)) h095T K n hK) ≪≫
    asIso ((derivedLowerShriekUnboundedCompMap.{u, r} Λ jg
      (overCompactificationOf jg jgf)).app K) ≪≫
    derivedLowerShriekUnboundedCompactificationIsoUnconditional.{u, r} Λ
      (overCompactificationComp jg (overCompactificationOf jg jgf)) jgf h095T K n hK

end Composition

/-! ### Thickenings -/

section Thickening

/-- Along a universal homeomorphism `i : X ⟶ X'` the direct image of sheaves of `Λ`-modules is an
equivalence: base change along `i` exhibits the small étale site of `X'` as a dense subsite of that
of `X` (Tag 03SI part (1)). -/
theorem isEquivalence_etaleModuleDirectImage_of_universalHomeomorphism {X X' : Scheme.{u}}
    (i : X ⟶ X') [UniversalHomeomorphism i] :
    (etaleModuleDirectImage.{u, r} Λ i).IsEquivalence :=
  have := isDenseSubsite_of_universalHomeomorphism i
  have : HasLimitsOfSize.{u, u + 1} (ModuleCat.{max (u + 1) r} Λ) :=
    moduleCat_hasLimitsOfSize.{u, u + 1, r, max (u + 1) r} Λ
  inferInstance

/-- Along a universal homeomorphism `i : X ⟶ X'` the unit `F ⟶ i_* i⁻¹ F` of the adjunction
`i⁻¹ ⊣ i_*` on sheaves of `Λ`-modules is an isomorphism. -/
theorem isIso_etaleModuleInverseImageAdj_unit_of_universalHomeomorphism {X X' : Scheme.{u}}
    (i : X ⟶ X') [UniversalHomeomorphism i] :
    IsIso (etaleModuleInverseImageAdj.{u, r} Λ i).unit :=
  have := isEquivalence_etaleModuleDirectImage_of_universalHomeomorphism.{u, r} Λ i
  have := (etaleModuleInverseImageAdj.{u, r} Λ i).isEquivalence_left_of_isEquivalence_right
  inferInstance

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- **Topological invariance for a thickening, on `D(-_étale, Λ)`.** For a closed immersion
`i : X ⟶ X'` which is surjective (a thickening), `i_* ∘ i⁻¹ ≅ 𝟭` on `D(X'_étale, Λ)`: the unit
`F ⟶ i_* i⁻¹ F` is an isomorphism of sheaves, `i` being a universal homeomorphism. -/
def etaleModuleDerivedInverseImageDirectImageIsoOfThickening {X X' : Scheme.{u}} (i : X ⟶ X')
    [IsClosedImmersion i] (hi : Function.Surjective i.base) :
    etaleModuleDerivedInverseImageGeneral.{u, r} Λ i ⋙
        (etaleModuleDirectImage.{u, r} Λ i).mapDerivedCategory ≅ 𝟭 _ :=
  haveI := Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective i hi
  haveI := isIso_etaleModuleInverseImageAdj_unit_of_universalHomeomorphism.{u, r} Λ i
  (DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
    DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (asIso (etaleModuleInverseImageAdj.{u, r} Λ i).unit).symm ≪≫
    Functor.mapDerivedCategoryId _

variable {X X' Y : Scheme.{u}} {f' : X' ⟶ Y} [QuasiCompact f']
  (j' : CompactificationOf (Over.mk f')) (i : X ⟶ X') [IsClosedImmersion i]
  (hi : Function.Surjective i.base)

/-- **Stacks Project, Tag 0GKQ.** Let `f' : X' ⟶ Y` be a separated morphism of finite type of
quasi-compact and quasi-separated schemes, `i : X ⟶ X'` a thickening (a closed immersion which is
surjective) and `f = f' ∘ i`. Let `Λ` be a ring. Then `Rf_! ∘ i⁻¹ ≅ Rf'_!` on `D(X'_étale, Λ)`,
hence on `D⁺_{tors}(X'_étale, Λ)` and, for `Λ` torsion, on `D(X'_étale, Λ)`. Here `Rf'_!` is
computed through a compactification `j'` of `f'` and `Rf_!` through the compactification
`j'.restrictClosed i` of `f` that `j'` induces on `X`, as for Tags 0GKN and 0GKP.

Here `Rf_! = Rf'_! ∘ Ri_! = Rf'_! ∘ i_*`
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedRestrictClosedIso`), and `i⁻¹` and `i_*`
are inverse equivalences by the topological invariance of the small étale site
(`Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism`). -/
@[stacks 0GKQ]
def derivedLowerShriekUnboundedThickeningIso :
    etaleModuleDerivedInverseImageGeneral.{u, r} Λ i ⋙
        derivedLowerShriekUnbounded.{u, r} (i ≫ f') (j'.restrictClosed i) Λ ≅
      derivedLowerShriekUnbounded.{u, r} f' j' Λ :=
  Functor.isoWhiskerLeft _ (derivedLowerShriekUnboundedRestrictClosedIso.{u, r} Λ j' i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etaleModuleDerivedInverseImageDirectImageIsoOfThickening.{u, r} Λ i hi)
      _ ≪≫
    Functor.leftUnitor _

/-- **[Stacks, Tag 0GKQ] for an arbitrary compactification of `f`, granted the proper base change
theorem.** For a compactification `j_f` of `f = f' ∘ i` and every `K'` in `D(X'_étale, Λ)`
bounded below whose underlying complex of abelian sheaves has torsion cohomology sheaves,
`Rf_! (i⁻¹ K') ≅ Rf'_! K'` with `Rf_!` computed through `j_f`: the comparison
`derivedLowerShriekUnboundedCompactificationIsoUnconditional` with the induced compactification,
followed by `derivedLowerShriekUnboundedThickeningIso`. -/
def derivedLowerShriekUnboundedThickeningIsoOfCompactification
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (jf : CompactificationOf (Over.mk (i ≫ f')))
    (K' : DerivedCategory (EtaleModules.{u, r} Λ X')) (n : ℤ) [K'.IsGE n]
    (hK' : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X'.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X').obj K')) :
    (derivedLowerShriekUnbounded.{u, r} (i ≫ f') jf Λ).obj
        ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ i).obj K') ≅
      (derivedLowerShriekUnbounded.{u, r} f' j' Λ).obj K' :=
  haveI := Functor.isGE_obj_mapDerivedCategory (etaleModuleInverseImage.{u, r} Λ i) K' n
    inferInstance
  derivedLowerShriekUnboundedCompactificationIsoUnconditional.{u, r} Λ jf (j'.restrictClosed i)
      h095T ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ i).obj K') n
      (torsionCohomologyProperty_etaleModuleForgetDerived_inverseImage.{u, r} Λ i K' hK') ≪≫
    (derivedLowerShriekUnboundedThickeningIso.{u, r} Λ j' i hi).app K'

end Thickening

/-! ### Geometric fibres -/

section GeometricFibre

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (y : GeometricPoint Y)

/-- **[Stacks, Tag 0GK0] for the derived lower shriek, granted the proper base change theorem.**
Let `f : X ⟶ Y` be a separated morphism of finite type with a compactification `j`, and let
`ȳ : Spec k ⟶ Y` be a geometric point, with geometric fibre `f_ȳ : X_ȳ ⟶ Spec k`. For every `K`
in `D(X_étale, Λ)` bounded below whose underlying complex of abelian sheaves has torsion cohomology
sheaves there is an isomorphism
```
RΓ(Spec k, ȳ⁻¹ Rf_! K) ≅ RΓ_c(X_ȳ, K|_{X_ȳ})
```
in `D(Λ)`, where `RΓ_c(X_ȳ, -)` is computed through the compactification of `X_ȳ` obtained from `j`
by base change: it is `RΓ(Spec k, -)` applied to the base change isomorphism
`ȳ⁻¹ Rf_! K ≅ Rf_{ȳ,!}(K|_{X_ȳ})` of Tag 0F7L. Over the algebraically closed field `k`,
`RΓ(Spec k, ȳ⁻¹ -)` is the stalk functor at `ȳ` (Tag 04JN: the stalk at a geometric point is the
global sections of the pullback, and global sections over `Spec k` are exact). -/
def derivedLowerShriekUnboundedGeometricFibreIso
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) [K.IsGE n]
    (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X).obj K)) :
    (etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ (Spec (.of y.residueField))).obj
        ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ y.hom).obj
          ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj K)) ≅
      (compactlySupportedCohomologyUnbounded.{u, r} y.residueField (pullback.snd f y.hom)
          (j.baseChange (IsPullback.of_hasPullback f y.hom)) Λ).obj
        ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ (pullback.fst f y.hom)).obj K) :=
  haveI := isIso_derivedLowerShriekBaseChange_app_of_proper_base_change.{u, r} Λ
    (IsPullback.of_hasPullback f y.hom) j h095T K n hK
  (etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ (Spec (.of y.residueField))).mapIso
    (asIso ((derivedLowerShriekBaseChangeGeneral.{u, r} Λ
      (IsPullback.of_hasPullback f y.hom) j).app K))

end GeometricFibre

end Stacks.EtaleCohomology

end
