module

public import StacksFrontier.AlgebraicGeometry.Etale.RUpperShriekCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCovariance.ModelTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.IndependenceCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.AdjointExistenceUnbounded
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
import StacksCore.Tactic.StacksAttribute

/-!
# For a quasi-finite separated morphism, the `Rf^!` of Lemma 0G2C is the `Rf^!` of Lemma 0F5N

Let `f : X ⟶ Y` be a separated quasi-finite morphism of quasi-compact and quasi-separated schemes
and let `Λ` be a torsion ring. There are two functors `D(Y_étale, Λ) ⥤ D(X_étale, Λ)` called
`Rf^!`:

* the right adjoint `Stacks.EtaleCohomology.derivedUpperShriekUnbounded Λ j hΛ` of
  `Rf_! = Rf̄_* ∘ j_!` ([Stacks, Tag 0F7H]) built from a compactification `j : X ⟶ X̄` of `X`
  over `Y`, which exists by [Stacks, Tag 0G2C];
* the total right derived functor `AlgebraicGeometry.SmallEtale.moduleRUpperShriekFunctor` of the
  upper shriek of [Stacks, Tag 0F59], right adjoint to `f_!` by [Stacks, Tag 0F5N].

[Stacks, Tag 0GL8] says they agree. This file proves it for **every** compactification `j`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.moduleSheafDerivedEquiv` — the equivalence
  `D(Sh(X_{021B}), Λ) ≌ D(X_étale, Λ)` between the derived categories of sheaves of
  `Λ`-modules on the small étale site of Tag 021B and on Mathlib's small étale site, induced
  degreewise by the equivalence `AlgebraicGeometry.SmallEtale.moduleSheafEquiv` of the two sheaf
  categories.
* `AlgebraicGeometry.SmallEtale.moduleSheafEquivExtensionByZeroDirectImageIso` — for
  `f = j₀ ≫ f̄₀` with `j₀` an open immersion and `f̄₀` finite, `f̄₀_* ∘ j₀_!` on Mathlib's small
  étale sites is the transport of `f_!` on the sites of Tag 021B.
* `AlgebraicGeometry.SmallEtale.derivedLowerShriekUnboundedIsoOfFactorization` — for an arbitrary
  compactification `j`, the functor `Rf_!` of `j` is the transport of `f_!`.
* `AlgebraicGeometry.SmallEtale.transportedModuleFShriekRUpperShriekAdjunction` — the transport of
  the adjunction `f_! ⊣ Rf^!` of [Stacks, Tag 0F5N].
* `AlgebraicGeometry.SmallEtale.derivedUpperShriekUnboundedIsoModuleRUpperShriekFunctor` —
  **[Stacks, Tag 0GL8]**.

## Implementation notes

The proof is the source's: uniqueness of adjoints. Both functors `Rf^!` are right adjoints, the
first of `Rf_!` by construction, the second (transported) of the transport of `f_!` by
[Stacks, Tag 0F5N]; so it suffices that `Rf_!` of `j` be isomorphic to the transport of `f_!`.
By [Stacks, Tag 0F7I] (`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompactificationIsoUniv`)
`Rf_!` of `j` is `Rf_!` of the compactification `f = j₀ ≫ f̄₀` with `f̄₀` finite given by
Zariski's main theorem ([Stacks, Tag 05K0]); for that compactification `Rj₀_! = j₀_!` and
`Rf̄₀_* = f̄₀_*` (both exact), and these agree with the corresponding functors on the site of
Tag 021B (`AlgebraicGeometry.SmallEtale.moduleSheafEquivExtensionByZeroIso`,
`AlgebraicGeometry.SmallEtale.etalePushforwardModSheafEquivIso`), whose composite is `f_!`
([Stacks, Tag 0F52], `AlgebraicGeometry.SmallEtale.fShriekModIsoCompactificationHom`).

The two models: `Rf^!` of [Stacks, Tag 0G2C] lives on the derived categories of
`Stacks.EtaleCohomology.EtaleModules` (sheaves on Mathlib's small étale site, standard model of
the derived category), and `Rf^!` of [Stacks, Tag 0F5N] on those of
`AlgebraicGeometry.SmallEtale.ModuleSheaf` (sheaves on the small étale site of Tag 021B of a big
étale site containing `X` and `Y`, any model of the derived categories). The comparison is stated
on the derived categories of the former, the latter transported along
`AlgebraicGeometry.SmallEtale.moduleSheafDerivedEquiv`. The coefficient ring lives in the universe
of the schemes, `Λ : Type u`, which is where `f_!` with coefficients in `Λ` is defined.

## References

* [Stacks Project, Tag 0GL8](https://stacks.math.columbia.edu/tag/0GL8)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
* [Stacks Project, Tag 0F5N](https://stacks.math.columbia.edu/tag/0F5N)
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.EtaleCohomology

universe w u

namespace AlgebraicGeometry.SmallEtale

/- `etaleModules_enoughInjectives_univZero` is stated for the coefficient ring in `Type`; instance
search would try to unify an arbitrary coefficient universe with it and fail on the universe
constraint, so it is switched off here. -/
attribute [-instance] etaleModules_enoughInjectives_univZero

attribute [local instance] HasDerivedCategory.standard comp_preservesFiniteLimits
  comp_preservesFiniteColimits

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ]

/-! ### The two models of `D(X_étale, Λ)` -/

section Equivalence

variable (S : B.Scheme)

/-- The functor `Sh(S_{021B}, Λ) ⥤ Sh(S_étale, Λ)` of `moduleSheafEquiv` is additive. -/
instance moduleSheafEquiv_functor_additive : (moduleSheafEquiv B Λ S).functor.Additive :=
  -- the limits of `Λ`-modules at these universes, so that instance search does not have to solve
  -- `max (u + 1) ?r = u + 1`
  have : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} Λ) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, u}
  Functor.additive_of_preserves_binary_products _

/-- The functor `Sh(S_étale, Λ) ⥤ Sh(S_{021B}, Λ)` of `moduleSheafEquiv` is additive. -/
instance moduleSheafEquiv_inverse_additive : (moduleSheafEquiv B Λ S).inverse.Additive :=
  -- the limits of `Λ`-modules at these universes, so that instance search does not have to solve
  -- `max (u + 1) ?r = u + 1`
  have : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} Λ) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, u}
  Functor.additive_of_preserves_binary_products _

variable [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B S Λ)]

/-- **The derived categories of sheaves of `Λ`-modules on the two small étale sites are
equivalent**: `D(Sh(S_{021B}), Λ) ≌ D(S_étale, Λ)`, the equivalence `moduleSheafEquiv` of the
sheaf categories applied degreewise. Its functor is
`(moduleSheafEquiv B Λ S).functor.mapDerivedCategory` and its inverse
`(moduleSheafEquiv B Λ S).inverse.mapDerivedCategory`. -/
def moduleSheafDerivedEquiv :
    DerivedCategory (ModuleSheaf.{u, u, u} B S Λ) ≌
      DerivedCategory (EtaleModules.{u, u} Λ S.obj) :=
  StacksDraft.DerivedRingIso.mapDerivedCategoryEquivalence (moduleSheafEquiv B Λ S).functor
    (moduleSheafEquiv B Λ S).inverse (moduleSheafEquiv B Λ S).unitIso
    (moduleSheafEquiv B Λ S).counitIso

end Equivalence

/-! ### `Rf_!` through a finite compactification, across the two models -/

section Factorization

variable {X Xb Y : B.Scheme} (j₀ : X ⟶ Xb) (fb : Xb ⟶ Y) [IsOpenImmersion (B.inclusion.map j₀)]
  [IsFinite (B.inclusion.map fb)]

/-- The direct image of sheaves of `Λ`-modules on Mathlib's small étale sites along a finite
morphism is exact, preserving finite limits: it is the transport of the direct image on the
sites of Tag 021B, which is exact. -/
instance preservesFiniteLimits_etaleModuleDirectImage_of_isFinite :
    PreservesFiniteLimits (etaleModuleDirectImage.{u, u} Λ (B.inclusion.map fb)) :=
  let E := moduleSheafEquiv B Λ Xb
  preservesFiniteLimits_of_natIso
    ((Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight E.counitIso.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft E.inverse (etalePushforwardModSheafEquivIso B Λ fb).symm :
      etaleModuleDirectImage.{u, u} Λ (B.inclusion.map fb) ≅
        E.inverse ⋙ etalePushforwardMod B Λ fb ⋙ (moduleSheafEquiv B Λ Y).functor).symm

/-- The direct image of sheaves of `Λ`-modules on Mathlib's small étale sites along a finite
morphism preserves finite colimits. -/
instance preservesFiniteColimits_etaleModuleDirectImage_of_isFinite :
    PreservesFiniteColimits (etaleModuleDirectImage.{u, u} Λ (B.inclusion.map fb)) :=
  let E := moduleSheafEquiv B Λ Xb
  preservesFiniteColimits_of_natIso
    ((Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight E.counitIso.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft E.inverse (etalePushforwardModSheafEquivIso B Λ fb).symm :
      etaleModuleDirectImage.{u, u} Λ (B.inclusion.map fb) ≅
        E.inverse ⋙ etalePushforwardMod B Λ fb ⋙ (moduleSheafEquiv B Λ Y).functor).symm

/-- A square of exact functors commuting up to isomorphism induces a square of functors on
derived categories commuting up to isomorphism. -/
def mapDerivedCategorySquareIso {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    [HasDerivedCategory C₄]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₄) (H : C₁ ⥤ C₃) (K : C₃ ⥤ C₄)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (e : F ⋙ G ≅ H ⋙ K) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory ⋙ K.mapDerivedCategory :=
  haveI := comp_preservesFiniteLimits F G
  haveI := comp_preservesFiniteColimits F G
  haveI := comp_preservesFiniteLimits H K
  haveI := comp_preservesFiniteColimits H K
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ e ≪≫
      Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso H K

/-- `j₀ ≫ f̄₀` is locally of finite type, `j₀` being an open immersion and `f̄₀` finite; stated
directly since instance search for it times out here (Lean v4.35.0). -/
local instance (priority := high) locallyOfFiniteType_inclusion_map_comp_of_isFinite :
    LocallyOfFiniteType (B.inclusion.map (j₀ ≫ fb)) :=
  @locallyOfFiniteType_comp _ _ _ (B.inclusion.map j₀) (B.inclusion.map fb)
    (locallyOfFiniteType_of_isOpenImmersion (B.inclusion.map j₀))
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType (B.inclusion.map fb)).mp ‹_›).2

/-- `j₀ ≫ f̄₀` is locally quasi-finite, `j₀` being an open immersion and `f̄₀` finite; stated
directly since instance search for it times out here (Lean v4.35.0). -/
local instance (priority := high) locallyQuasiFinite_inclusion_map_comp_of_isFinite :
    LocallyQuasiFinite (B.inclusion.map (j₀ ≫ fb)) :=
  MorphismProperty.comp_mem @LocallyQuasiFinite (B.inclusion.map j₀) (B.inclusion.map fb)
    (HasRingHomProperty.of_isOpenImmersion (P := @LocallyQuasiFinite)
      RingHom.QuasiFinite.holdsForLocalizationAway.containsIdentities)
    (instLocallyQuasiFiniteOfIsFinite (B.inclusion.map fb))

/-- On sheaves of `Λ`-modules, `(f̄₀)_* ∘ (j₀)_!` on Mathlib's small étale sites is the transport
of `f_!` on the sites of Tag 021B, for `f = j₀ ≫ f̄₀`: extension by zero and direct image commute
with the comparison of the two sites, and `f_! = f̄₀_* ∘ j₀_!` ([Stacks, Tag 0F52]). -/
def moduleSheafEquivExtensionByZeroDirectImageIso :
    (moduleSheafEquiv B Λ X).functor ⋙
        (etaleModuleExtensionByZero.{u, u} Λ (B.inclusion.map j₀) ⋙
          etaleModuleDirectImage.{u, u} Λ (B.inclusion.map fb)) ≅
      fShriekMod.{u, u, u} B Λ (j₀ ≫ fb) ⋙ (moduleSheafEquiv B Λ Y).functor :=
  -- instance search for this times out here (Lean v4.35.0): supply Mathlib's instance directly
  haveI : LocallyQuasiFinite (B.inclusion.map fb) := instLocallyQuasiFiniteOfIsFinite _
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafEquivExtensionByZeroIso B Λ j₀) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etalePushforwardModSheafEquivIso B Λ fb).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fShriekModIsoCompactificationHom B Λ j₀ fb).symm _

end Factorization

/-! ### Stacks 0GL8 -/

section Comparison

variable {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyQuasiFinite (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]

/-- The transport from the sites of Tag 021B of the adjunction `f_! ⊣ Rf^!` of
[Stacks, Tag 0F5N]. -/
def transportedModuleFShriekRUpperShriekAdjunction :
    (moduleSheafDerivedEquiv B Λ X).inverse ⋙
        moduleFShriekDerivedFunctor.{u, u, w, u} B Λ f (fShriekMod.{u, u, u} B Λ f)
          (fShriekModForgetIso.{u, u, u} B Λ f) ⋙
            (moduleSheafDerivedEquiv B Λ Y).functor ⊣
      (moduleSheafDerivedEquiv B Λ Y).inverse ⋙
        moduleRUpperShriekFunctor.{u, u, w, u} B Λ f ⋙
          (moduleSheafDerivedEquiv B Λ X).functor :=
  (moduleSheafDerivedEquiv B Λ X).symm.toAdjunction.comp
    ((moduleFShriekRUpperShriekAdjunction.{u, u, w, u} B Λ f).comp
      (moduleSheafDerivedEquiv B Λ Y).toAdjunction)

variable [IsSeparated (B.inclusion.map f)] [QuasiCompact (B.inclusion.map f)]
  [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)

include hΛ in
/-- For a factorization `f = j₀ ≫ f̄₀` with `j₀` an open immersion and `f̄₀` finite and for an
**arbitrary** compactification `j` of `X` over `Y`, the derived lower shriek
`Rf_! = Rf̄_* ∘ Rj_!` of `j` ([Stacks, Tag 0F7H]) is the transport from the sites of Tag 021B of
the functor `f_!` of [Stacks, Tag 0F5N]: by [Stacks, Tag 0F7I] it is `Rf_!` of the
compactification `(j₀, f̄₀)`, whose two factors are exact, and `f̄₀_* ∘ j₀_!` is the transport of
`f_!`. -/
def derivedLowerShriekUnboundedIsoOfFactorization
    (j : CompactificationOf (Over.mk (B.inclusion.map f)))
    {Xb : B.Scheme} (j₀ : X ⟶ Xb) (fb : Xb ⟶ Y) [IsOpenImmersion (B.inclusion.map j₀)]
    [IsFinite (B.inclusion.map fb)] (hfac : f = j₀ ≫ fb) :
    derivedLowerShriekUnbounded.{u, u} (B.inclusion.map f) j Λ ≅
      (moduleSheafDerivedEquiv B Λ X).inverse ⋙
        moduleFShriekDerivedFunctor.{u, u, w, u} B Λ f (fShriekMod.{u, u, u} B Λ f)
          (fShriekModForgetIso.{u, u, u} B Λ f) ⋙
            (moduleSheafDerivedEquiv B Λ Y).functor := by
  subst hfac
  haveI : CompactSpace (B.inclusion.obj Y) := inferInstanceAs (CompactSpace Y.obj)
  haveI : QuasiSeparatedSpace (B.inclusion.obj Y) := inferInstanceAs (QuasiSeparatedSpace Y.obj)
  haveI := preservesFiniteLimits_of_forgetModuleSheafIso.{u, u, u} B Λ (j₀ ≫ fb)
    (fShriekMod.{u, u, u} B Λ (j₀ ≫ fb)) (fShriekModForgetIso.{u, u, u} B Λ (j₀ ≫ fb))
  haveI := moduleSheafEquiv_functor_additive B Λ X
  haveI := moduleSheafEquiv_functor_additive B Λ Y
  let DX := moduleSheafDerivedEquiv B Λ X
  let DY := moduleSheafDerivedEquiv B Λ Y
  let jM := etaleModuleExtensionByZero.{u, u} Λ (B.inclusion.map j₀)
  let hM := etaleModuleDirectImage.{u, u} Λ (B.inclusion.map fb)
  let j₁ : CompactificationOf (Over.mk (B.inclusion.map (j₀ ≫ fb))) :=
    ⟨StructuredArrow.mk (Y := Over.mk (B.inclusion.map fb))
        (Over.homMk (U := Over.mk (B.inclusion.map (j₀ ≫ fb))) (B.inclusion.map j₀) rfl),
      ⟨inferInstanceAs (IsOpenImmersion (B.inclusion.map j₀)),
        inferInstanceAs (IsProper (B.inclusion.map fb))⟩⟩
  let sq : DX.functor ⋙ (jM ⋙ hM).mapDerivedCategory ≅
      (fShriekMod.{u, u, u} B Λ (j₀ ≫ fb)).mapDerivedCategory ⋙ DY.functor :=
    mapDerivedCategorySquareIso _ _ _ _ (moduleSheafEquivExtensionByZeroDirectImageIso B Λ j₀ fb)
  exact derivedLowerShriekUnboundedCompactificationIsoUniv (B.inclusion.map (j₀ ≫ fb)) j j₁ Λ hΛ ≪≫
    Functor.isoWhiskerRight
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, u} Λ (B.inclusion.map j₀)) _ ≪≫
    Functor.isoWhiskerLeft jM.mapDerivedCategory
      (Stacks.Injectives.KInjectiveResolution.isoMapDerivedCategoryOfIsRightDerivedFunctor hM
        (etaleModuleDerivedDirectImageUnbounded.{u, u} Λ (B.inclusion.map fb))
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, u} Λ (B.inclusion.map fb))) ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso jM hM).symm ≪≫
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight DX.counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft DX.inverse sq

/-- **[Stacks, Tag 0GL8].** Let `f : X ⟶ Y` be a separated quasi-finite morphism of a big étale
site with `Y` quasi-compact and quasi-separated, let `Λ` be a torsion ring, and let
`j : X ⟶ X̄` be **any** compactification of `X` over `Y`. Then the functor
`Rf^! : D(Y_étale, Λ) ⥤ D(X_étale, Λ)` of [Stacks, Tag 0G2C], the right adjoint
`Stacks.EtaleCohomology.derivedUpperShriekUnbounded Λ j hΛ` of the derived lower shriek
`Rf_! = Rf̄_* ∘ j_!` of `j` ([Stacks, Tag 0F7H]), is isomorphic to the `Rf^!` of
[Stacks, Tag 0F5N], the total right derived functor `moduleRUpperShriekFunctor B Λ f` of the
upper shriek of [Stacks, Tag 0F59].

The first functor is on Mathlib's small étale sites (`Stacks.EtaleCohomology.EtaleModules`), the
second on the small étale sites of Tag 021B of `B` (`AlgebraicGeometry.SmallEtale.ModuleSheaf`,
any model of their derived categories); the second is read on the derived categories of the first
through the equivalences `moduleSheafDerivedEquiv` induced by the equivalences of the sheaf
categories. Quasi-finiteness is [Stacks, Tag 02NG]: locally quasi-finite, locally of finite type
and quasi-compact together; `X` is then quasi-compact and quasi-separated as well. -/
@[stacks 0GL8 "for every compactification j: Rf^! of Tag 0G2C (right adjoint of Rf̄_* ∘ j_!) \
is the Rf^! of Tag 0F5N, read on Mathlib's small étale sites through the equivalence of the two \
models of D(X_étale, Λ)"]
def derivedUpperShriekUnboundedIsoModuleRUpperShriekFunctor
    (j : CompactificationOf (Over.mk (B.inclusion.map f))) :
    derivedUpperShriekUnbounded.{u, u} Λ j hΛ ≅
      (moduleSheafDerivedEquiv B Λ Y).inverse ⋙
        moduleRUpperShriekFunctor.{u, u, w, u} B Λ f ⋙
          (moduleSheafDerivedEquiv B Λ X).functor :=
  Classical.choice <| by
    obtain ⟨Xb, j₀, fb, _, _, hfac⟩ := exists_isOpenImmersion_isFinite_factorization B f
    exact ⟨(derivedLowerShriekUnboundedAdjunction Λ j hΛ).rightAdjointUniq
      ((transportedModuleFShriekRUpperShriekAdjunction B Λ f).ofNatIsoLeft
        (derivedLowerShriekUnboundedIsoOfFactorization B Λ f hΛ j j₀ fb hfac).symm)⟩

end Comparison

end AlgebraicGeometry.SmallEtale

end
