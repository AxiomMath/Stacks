module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyDirectSums
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyLinear
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationBaseChange
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeRightExact
public import StacksFrontier.AlgebraicGeometry.Properties.GabberResult.Abelian
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderKernels
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderCokernels

/-!
# Right exactness and direct sums for the top-degree cohomology functor

For a scheme `X` and `d : ℕ`, this file studies the degree-`d` cohomology functor
`(Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived d`, valued in
`Γ(X, ⊤)`-modules. Restricted to the quasi-coherent modules, which form an abelian category
(`AlgebraicGeometry.quasicoherentModules_abelian`), it is right exact as soon as
`H^{d+1}(X, F) = 0` for every quasi-coherent `F`. On a quasi-compact quasi-separated scheme it
commutes with arbitrary direct sums. These are the right exactness and direct-sum hypotheses of
`Stacks.EilenbergWatts.iso` for the cohomological factor of the functor in the proof of
[Stacks, Tag 0EX3] (b).

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.qcohCohomology`: the degree-`d` cohomology of a
  scheme, restricted to quasi-coherent modules and valued in `Γ(X, ⊤)`-modules.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.exact_and_epi_map_rightDerived_of_isZero`: if
  `R^{d+1} F(X₁)` vanishes, then `R^d F` sends a short exact sequence `0 → X₁ → X₂ → X₃ → 0` to an
  exact sequence `R^d F(X₁) → R^d F(X₂) → R^d F(X₃) → 0`, for Mathlib's `ℕ`-indexed
  `CategoryTheory.Functor.rightDerived`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.preservesFiniteColimits_qcohCohomology`:
  `qcohCohomology X d` is right exact when `H^{d+1}(X, -)` vanishes on quasi-coherent modules.
* `preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections` and
  `preservesColimitsOfShape_discrete_qcohCohomology`, both in the same namespace: on a
  quasi-compact quasi-separated scheme, cohomology commutes with arbitrary direct sums.
* `preservesFiniteColimits_qcohCohomology_X'` and
  `preservesColimitsOfShape_discrete_qcohCohomology_X'`, in the nested
  `TopDegreeBaseChangeSituation` namespace: the same two statements for the base-changed source of
  a top-degree base-change situation over an affine base, with no further hypotheses.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 01LB](https://stacks.math.columbia.edu/tag/01LB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

/-! ### The quasi-coherent subcategory and the exactness of its inclusion -/

/-- The inclusion of the quasi-coherent modules is additive: it is the identity on morphisms. -/
instance additive_ι_isQuasicoherent (X : Scheme.{u}) :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)).Additive :=
  ⟨by intros; rfl⟩

/-- The inclusion of the quasi-coherent modules is left exact, because quasi-coherence is closed
under kernels. -/
noncomputable instance preservesFiniteLimits_ι_isQuasicoherent (X : Scheme.{u}) :
    PreservesFiniteLimits (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)) :=
  have : ∀ {A B : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (f : A ⟶ B),
      PreservesLimit (parallelPair f 0)
        (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)) :=
    fun f => ObjectProperty.preservesKernels_ι _ f
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- The inclusion of the quasi-coherent modules is right exact, because quasi-coherence is
closed under cokernels. -/
noncomputable instance preservesFiniteColimits_ι_isQuasicoherent (X : Scheme.{u}) :
    PreservesFiniteColimits (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)) :=
  have : ∀ {A B : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (f : A ⟶ B),
      PreservesColimit (parallelPair f 0)
        (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)) :=
    fun f => ObjectProperty.preservesCokernels_ι _ f
  have : HasFiniteCoproducts (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    have := @Abelian.hasFiniteBiproducts _ _ (quasicoherentModules_abelian X)
    hasFiniteCoproducts_of_hasFiniteBiproducts _
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-- **A short exact sequence of quasi-coherent modules is a short exact sequence of module
sheaves.** The inclusion of the quasi-coherent modules is exact. -/
theorem shortExact_map_ι_isQuasicoherent (X : Scheme.{u})
    {S : ShortComplex (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory}
    (hS : S.ShortExact) :
    (S.map (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))).ShortExact :=
  (show ∀ T : ShortComplex (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory,
      T.ShortExact →
        (T.map (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))).ShortExact from
    ((Functor.exact_tfae
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))).out 4 1).mp
        (And.intro (preservesFiniteLimits_ι_isQuasicoherent X)
          (preservesFiniteColimits_ι_isQuasicoherent X))) S hS

/-! ### The right-exactness step in the `rightDerived` indexing -/

section General

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

/-- **One degree of right exactness from one degree of vanishing, for `rightDerived`.** For an
additive functor `F` between abelian categories, with enough injectives in the source, and a short
exact sequence `S`, if `R^{d+1} F(X₁)` vanishes then the image of `S` under `R^d F` is exact and
`R^d F(X₂) ⟶ R^d F(X₃)` is an epimorphism. -/
theorem exact_and_epi_map_rightDerived_of_isZero (F : C ⥤ D) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (d : ℕ)
    (h₁ : IsZero ((F.rightDerivedPlus ((d : ℤ) + 1)).obj S.X₁)) :
    (S.map (F.rightDerived d)).Exact ∧ Epi ((F.rightDerived d).map S.g) := by
  obtain ⟨hex, hepi⟩ :=
    exact_and_epi_map_rightDerivedPlus_of_isZero F hS (d : ℤ) ((d : ℤ) + 1) rfl h₁
  set e := Stacks.DerivedIndexing.rightDerivedIso F d
  have iso : (S.map (F.rightDerived d)) ≅
      ShortComplex.mk ((F.rightDerivedPlus (d : ℤ)).map S.f)
        ((F.rightDerivedPlus (d : ℤ)).map S.g)
        (rightDerivedPlus_map_f_comp_map_g F hS (d : ℤ)) :=
    ShortComplex.isoMk (e.app S.X₁) (e.app S.X₂) (e.app S.X₃)
      (e.hom.naturality S.f).symm (e.hom.naturality S.g).symm
  refine ⟨ShortComplex.exact_of_iso iso.symm hex, ?_⟩
  have h2 : Epi ((F.rightDerived d).map S.g ≫ (e.app S.X₃).hom) := by
    rw [show (e.app S.X₃).hom = e.hom.app S.X₃ from rfl, e.hom.naturality S.g]
    infer_instance
  exact (epi_comp_iff_of_isIso _ _).mp h2

end General

/-! ### The two topological hypotheses of Tag 01FF, for a scheme -/

/-- **A scheme has a basis of quasi-compact opens**, namely its affine opens; that is, it is a
`PrespectralSpace`. -/
theorem hasBasisOfCompactOpens_scheme (X : Scheme.{u}) : PrespectralSpace (X : Type u) := by
  refine PrespectralSpace.of_isTopologicalBasis
    (B := (fun U : Opens (X : Type u) => (U : Set X)) ''
      {U : Opens (X : Type u) | IsAffineOpen U}) X.isBasis_affineOpens ?_
  rintro U ⟨V, hV, rfl⟩
  exact hV.isCompact

/-- **On a quasi-separated space two quasi-compact opens meet in a quasi-compact open.** This is
the definition of `QuasiSeparatedSpace`, read as hypothesis (H2) of [Stacks, Tag 0069]. -/
theorem interCompactOpenIsCompact_scheme (X : Scheme.{u}) [QuasiSeparatedSpace (X : Type u)] :
    QuasiSeparatedSpace (X : Type u) :=
  ⟨fun U V hU hUc hV hVc => QuasiSeparatedSpace.inter_isCompact U V hU hUc hV hVc⟩

/-! ### Direct sums -/

/-- **Cohomology of a quasi-compact quasi-separated scheme commutes with arbitrary direct
sums**, as a functor valued in `Γ(X, ⊤)`-modules. -/
theorem preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections (X : Scheme.{u})
    [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)] (q : ℕ) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) ((moduleGlobalSections X).rightDerived q) := by
  have h1 : PreservesColimitsOfShape (Discrete J) (Hfunctor X.ringCatSheaf ⊤ q) :=
    Stacks.Cohomology.DirectSum.preservesColimitsOfShape_discrete_Hfunctor X.ringCatSheaf
      (hasBasisOfCompactOpens_scheme X) (interCompactOpenIsCompact_scheme X) ⊤
      (by simpa using CompactSpace.isCompact_univ) q J
  have h2 : PreservesColimitsOfShape (Discrete J)
      ((moduleGlobalSections X).rightDerived q ⋙
        forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}) :=
    @preservesColimitsOfShape_of_natIso _ _ _ _ _ _ _ _
      (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
        X.ringCatSheaf ⊤ q).symm h1
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u})

/-! ### The cohomological factor of the Eilenberg-Watts functor -/

/-- **The degree-`d` cohomology of a scheme, restricted to quasi-coherent modules**, as a functor
from the quasi-coherent modules on `X` to `Γ(X, ⊤)`-modules. -/
noncomputable def qcohCohomology (X : Scheme.{u}) (d : ℕ) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
    (moduleGlobalSections X).rightDerived d

/-- `qcohCohomology` is additive: both factors are. -/
instance additive_qcohCohomology (X : Scheme.{u}) (d : ℕ) : (qcohCohomology X d).Additive where
  map_add := ((moduleGlobalSections X).rightDerived d).map_add

/-- **In the top degree, cohomology is right exact on quasi-coherent modules**: if
`H^{d+1}(X, F) = 0` for every quasi-coherent `F`, then `qcohCohomology X d` preserves finite
colimits. -/
theorem preservesFiniteColimits_qcohCohomology (X : Scheme.{u}) (d : ℕ)
    (hvan : ∀ F : X.Modules, F.IsQuasicoherent →
      IsZero (((moduleGlobalSections X).rightDerivedPlus ((d : ℤ) + 1)).obj F)) :
    PreservesFiniteColimits (qcohCohomology X d) := by
  rw [Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi]
  intro S hS
  exact exact_and_epi_map_rightDerived_of_isZero (moduleGlobalSections X)
    (shortExact_map_ι_isQuasicoherent X hS) d (hvan _ S.X₁.property)

/-- **On a quasi-compact quasi-separated scheme, cohomology restricted to quasi-coherent modules
commutes with arbitrary direct sums.** -/
theorem preservesColimitsOfShape_discrete_qcohCohomology (X : Scheme.{u})
    [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)] (d : ℕ) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (qcohCohomology X d) := by
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let _ : P.IsClosedUnderColimitsOfShape (Discrete J) :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape
      (K := Discrete J) X
  let _ : HasColimitsOfShape (Discrete J) P.FullSubcategory :=
    Limits.hasColimitsOfShape_of_closedUnderColimits (J := Discrete J) (P := P)
  let _ : CreatesColimitsOfShape (Discrete J) (ObjectProperty.ι P) := inferInstance
  let iotaP : P.FullSubcategory ⥤ X.Modules := ObjectProperty.ι P
  let H : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) := (moduleGlobalSections X).rightDerived d
  let hι : PreservesColimitsOfShape (Discrete J) iotaP :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete J) (ObjectProperty.ι P))
  let hH : PreservesColimitsOfShape (Discrete J) H :=
    preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections X d J
  exact inferInstanceAs (PreservesColimitsOfShape (Discrete J) (iotaP ⋙ H))

/-! ### Discharged in a top-degree base-change situation -/

namespace TopDegreeBaseChangeSituation

variable (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})

/-- **For the base-changed source `X'` of a top-degree base-change situation over an affine
base, `qcohCohomology X' d` is right exact.** -/
theorem preservesFiniteColimits_qcohCohomology_X' [IsAffine S.Y'] :
    PreservesFiniteColimits (qcohCohomology S.X' S.d) :=
  preservesFiniteColimits_qcohCohomology S.X' S.d fun F _ =>
    S.isZero_cohomology_of_lt ((S.d : ℤ) + 1) (lt_add_one _) F

/-- **For the base-changed source `X'` of a top-degree base-change situation over an affine
base, `qcohCohomology X' d` commutes with arbitrary direct sums.** -/
theorem preservesColimitsOfShape_discrete_qcohCohomology_X' [IsAffine S.Y'] (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (qcohCohomology S.X' S.d) :=
  have := S.compactSpace_X'
  have := S.quasiSeparatedSpace_X'
  preservesColimitsOfShape_discrete_qcohCohomology S.X' S.d J

end TopDegreeBaseChangeSituation

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
