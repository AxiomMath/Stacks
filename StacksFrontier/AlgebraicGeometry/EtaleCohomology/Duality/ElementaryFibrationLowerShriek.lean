module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopLowerShriekTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopDirectImageBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.SurjectiveEtaleFaithful
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopTraceDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleForgetBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ModuleSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstantCohomology
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LisseExtVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward

/-!
# `R⁰ f_!` and `R^q f_!` of an elementary fibration, through its compactification

Let `f : U ⟶ S` be the complement of a closed `i : Z ⟶ X̄` in `f̄ : X̄ ⟶ S`, with `f̄` flat,
quasi-compact and with geometrically connected fibres, and `Z ⟶ S` étale and surjective (an
elementary fibration has these properties). For a sheaf `G` of `ℤ/N`-modules on `S`:

* `R^q f_!(f⁻¹ G) ≅ H^q(Rf̄_*(j_! j⁻¹ f̄⁻¹ G))` for every `q` and every compactification of `f`
  (`Stacks.EtaleCohomology.lowerShriekHomologyFactorizationIso`): the independence of the
  compactification (Tag 0F7I), `Rf_! = Rf̄_* ∘ j_!` for the compactification `j`, and
  `f⁻¹ = j⁻¹ f̄⁻¹`;
* the inverse image `f̄⁻¹` is full on sheaves of `ℤ/N`-modules
  (`Stacks.EtaleCohomology.full_etaleModuleInverseImage_zmod`), since it is on abelian sheaves
  and forgetting the `ℤ/N`-module structure is fully faithful; together with the faithfulness of
  the inverse image along the surjective étale `Z ⟶ S` this makes
  `f̄_* F ⟶ f̄_* i_* i⁻¹ F` a monomorphism for `F = f̄⁻¹ G`
  (`Stacks.EtaleCohomology.mono_etaleModuleDirectImage_map_inverseImageAdj_unit`);
* hence `R⁰ f_!(f⁻¹ G) = 0`
  (`Stacks.EtaleCohomology.isZero_lowerShriekHomology_zero_of_factorization`), by the long
  exact sequence of `0 → j_! j⁻¹ F → F → i_* i⁻¹ F → 0` under `Rf̄_*`;
* and if every `H^q(Rf̄_*(f̄⁻¹ G))` is locally constant of finite type and `G` is, then so is
  every `R^q f_!(f⁻¹ G)`
  (`Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_lowerShriekHomology_of_factorization`):
  `R^q f̄_*(i_* i⁻¹ F)` is `(i ≫ f̄)_* i⁻¹ F` for `q = 0` (lisse, Tag 095B) and vanishes otherwise,
  and the finite type locally constant sheaves form a weak Serre class (Tag 093U).

These are the low-degree inputs (`Stacks.EtaleCohomology.LowerShriekLowDegreeInput`) of the
fibration step of Poincaré duality in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The derived categories are those of the standard model `HasDerivedCategory.standard`, in which
`Rf_!` is defined.

## Main results

* `Stacks.EtaleCohomology.full_etaleModuleInverseImage_zmod`.
* `Stacks.EtaleCohomology.mono_etaleModuleDirectImage_map_inverseImageAdj_unit`.
* `Stacks.EtaleCohomology.lowerShriekHomologyFactorizationIso`.
* `Stacks.EtaleCohomology.isZero_lowerShriekHomology_zero_of_factorization`.
* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_lowerShriekHomology_of_factorization`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  Functor.commShiftRightDerivedFunctorPlus Functor.isTriangulated_rightDerivedFunctorPlus

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-! ### Fullness of the inverse image along a morphism with geometrically connected fibres -/

section Full

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [QuasiCompact f] [GeometricallyConnected f]
  (N : ℕ)

/-- **The inverse image along a flat quasi-compact morphism with geometrically connected fibres is
full on sheaves of `ℤ/N`-modules**: it is on abelian sheaves
(`Stacks.EtaleCohomology.etaleAbelianInverseImageFullyFaithful`), it commutes with forgetting the
module structure, and forgetting the `ℤ/N`-module structure is fully faithful. -/
theorem full_etaleModuleInverseImage_zmod : (etaleModuleInverseImage.{u, 0} (ZMod N) f).Full := by
  have : (etaleAbelianInverseImage.{u, 0} f).Full := (etaleAbelianInverseImageFullyFaithful f).full
  exact Functor.Full.of_comp_faithful_iso (G := etaleModuleForgetAb.{u, 0} (ZMod N) X)
    (etaleModuleForgetInverseImageIso.{u, 0} (ZMod N) f).symm

end Full

/-! ### The restriction to a surjective étale boundary is injective on direct images -/

section Mono

variable (N : ℕ) {Z Xbar S : Scheme.{u}} (i : Z ⟶ Xbar) (fbar : Xbar ⟶ S) [Flat fbar]
  [QuasiCompact fbar] [GeometricallyConnected fbar] [Etale (i ≫ fbar)] [Surjective (i ≫ fbar)]

/-- **`f̄_*(f̄⁻¹ G) ⟶ f̄_* i_* i⁻¹(f̄⁻¹ G)` is a monomorphism** when `f̄` is flat, quasi-compact
with geometrically connected fibres and `i ≫ f̄` is surjective étale: a map `T ⟶ f̄_*(f̄⁻¹ G)` is
the transpose of `f̄⁻¹ b` for some `b : T ⟶ G` (fullness of `f̄⁻¹`), and it is killed exactly when
`(i ≫ f̄)⁻¹ b = 0`, which forces `b = 0` since `(i ≫ f̄)⁻¹` is faithful. -/
theorem mono_etaleModuleDirectImage_map_inverseImageAdj_unit (G : EtaleModules.{u, 0} (ZMod N) S) :
    Mono ((etaleModuleDirectImage.{u, 0} (ZMod N) fbar).map
      ((etaleModuleInverseImageAdj.{u, 0} (ZMod N) i).unit.app
        ((etaleModuleInverseImage.{u, 0} (ZMod N) fbar).obj G))) := by
  have := full_etaleModuleInverseImage_zmod fbar N
  have := faithful_etaleModuleInverseImage_of_surjective (ZMod N) (i ≫ fbar)
  have : (etaleModuleInverseImage.{u, 0} (ZMod N) fbar ⋙
      etaleModuleInverseImage.{u, 0} (ZMod N) i).Faithful :=
    Functor.Faithful.of_iso (etaleModuleInverseImageCompIso.{u, 0} (ZMod N) i fbar)
  let adj := etaleModuleInverseImageAdj.{u, 0} (ZMod N) fbar
  let adji := etaleModuleInverseImageAdj.{u, 0} (ZMod N) i
  let F := (etaleModuleInverseImage.{u, 0} (ZMod N) fbar).obj G
  refine Preadditive.mono_of_cancel_zero _ fun {T} x hx => ?_
  obtain ⟨b, hb⟩ := (etaleModuleInverseImage.{u, 0} (ZMod N) fbar).map_surjective
    ((adj.homEquiv T F).symm x)
  have h₁ : adj.homEquiv _ _ ((adj.homEquiv T F).symm x ≫ adji.unit.app F) = 0 := by
    rwa [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  have h₂ : (adj.homEquiv T F).symm x ≫ adji.unit.app F = 0 := by
    apply (adj.homEquiv _ _).injective
    rw [h₁, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  have h₃ : (etaleModuleInverseImage.{u, 0} (ZMod N) i).map ((adj.homEquiv T F).symm x) = 0 := by
    apply (adji.homEquiv _ _).injective
    simpa only [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero,
      Adjunction.unit_naturality] using h₂
  have hb₀ : b = 0 := by
    apply (etaleModuleInverseImage.{u, 0} (ZMod N) fbar ⋙
      etaleModuleInverseImage.{u, 0} (ZMod N) i).map_injective
    rw [Functor.map_zero]
    change (etaleModuleInverseImage.{u, 0} (ZMod N) i).map
      ((etaleModuleInverseImage.{u, 0} (ZMod N) fbar).map b) = 0
    rwa [hb]
  have hx₀ : (adj.homEquiv T F).symm x = 0 := by
    rw [← hb, hb₀, Functor.map_zero]
  have := congrArg (adj.homEquiv T F) hx₀
  rwa [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero] at this

end Mono

/-! ### `R^q f_!` through the compactification of an elementary fibration -/

section Factorization

variable (N : ℕ) [NeZero N] {U S Xbar : Scheme.{u}} (f : U ⟶ S) (j : U ⟶ Xbar)
  [IsOpenImmersion j] (fbar : Xbar ⟶ S) (hjf : j ≫ fbar = f) [IsProper fbar]
  [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f] (jf : CompactificationOf (Over.mk f))

/-- The independence of the compactification (Tag 0F7I) inside `R^q f_!(f⁻¹ -)`. -/
def lowerShriekHomologyFactorizationIso₁ (q : ℤ) :
    etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.homologyFunctor _ q) ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        derivedLowerShriek.{u, 0} f (compactificationOfFactorization f j fbar hjf) (ZMod N) ⋙
          DerivedCategory.Plus.homologyFunctor _ q) :=
  Functor.isoWhiskerLeft (inverseImageSingleTorsion N f)
    (Functor.isoWhiskerRight (derivedLowerShriekCompactificationIso f jf
      (compactificationOfFactorization f j fbar hjf) (ZMod N))
      (DerivedCategory.Plus.homologyFunctor _ q))

/-- `Rf_! = Rf̄_* ∘ j_!` on a sheaf placed in degree zero, for the compactification `j`. -/
def lowerShriekHomologyFactorizationIso₂ (q : ℤ) :
    etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        derivedLowerShriek.{u, 0} f (compactificationOfFactorization f j fbar hjf) (ZMod N) ⋙
          DerivedCategory.Plus.homologyFunctor _ q) ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ (etaleModuleExtensionByZero.{u, 0} (ZMod N) j ⋙
        (DerivedCategory.Plus.singleFunctor _ 0 ⋙
          etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
            DerivedCategory.Plus.homologyFunctor _ q)) :=
  letI := etaleModules_enoughInjectives.{u, 0} (ZMod N) U
  Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) f)
    (Functor.isoWhiskerRight (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (etaleModuleExtensionByZero.{u, 0} (ZMod N) j) 0).symm
        (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
          DerivedCategory.Plus.homologyFunctor _ q))

/-- `f⁻¹ = j⁻¹ f̄⁻¹`, and `j⁻¹` is restriction. -/
def lowerShriekHomologyFactorizationIso₃ (q : ℤ) :
    etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ (etaleModuleExtensionByZero.{u, 0} (ZMod N) j ⋙
        (DerivedCategory.Plus.singleFunctor _ 0 ⋙
          etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
            DerivedCategory.Plus.homologyFunctor _ q)) ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) fbar ⋙ (etaleModuleRestriction.{u, 0} (ZMod N) j ⋙
        (etaleModuleExtensionByZero.{u, 0} (ZMod N) j ⋙
          (DerivedCategory.Plus.singleFunctor _ 0 ⋙
            etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
              DerivedCategory.Plus.homologyFunctor _ q))) :=
  Functor.isoWhiskerRight (eqToIso (congrArg (etaleModuleInverseImage.{u, 0} (ZMod N)) hjf.symm) ≪≫
      etaleModuleInverseImageCompIso.{u, 0} (ZMod N) j fbar ≪≫
      Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) fbar)
        (etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) j))
      (etaleModuleExtensionByZero.{u, 0} (ZMod N) j ⋙
        (DerivedCategory.Plus.singleFunctor _ 0 ⋙
          etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
            DerivedCategory.Plus.homologyFunctor _ q)) ≪≫
    Functor.associator _ _ _

/-- **`R^q f_!(f⁻¹ G) ≅ H^q(Rf̄_*(j_! j⁻¹ f̄⁻¹ G))`**, naturally in `G`, for every compactification
of `f`: the independence of the compactification (Tag 0F7I), `Rf_! = Rf̄_* ∘ j_!` for the
compactification `j` and `f⁻¹ = j⁻¹ f̄⁻¹`. -/
def lowerShriekHomologyFactorizationIso (q : ℤ) :
    etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.homologyFunctor _ q) ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) fbar ⋙ (etaleModuleRestriction.{u, 0} (ZMod N) j ⋙
        (etaleModuleExtensionByZero.{u, 0} (ZMod N) j ⋙
          (DerivedCategory.Plus.singleFunctor _ 0 ⋙
            etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
              DerivedCategory.Plus.homologyFunctor _ q))) :=
  lowerShriekHomologyFactorizationIso₁ N f j fbar hjf jf q ≪≫
    lowerShriekHomologyFactorizationIso₂ N f j fbar hjf q ≪≫
    lowerShriekHomologyFactorizationIso₃ N f j fbar hjf q

end Factorization

/-! ### `R⁰ f_! = 0` and local constancy of `R^q f_!` -/

section LowDegree

variable (N : ℕ) [NeZero N] {U S Xbar Z : Scheme.{u}} (f : U ⟶ S) (j : U ⟶ Xbar)
  [IsOpenImmersion j] (fbar : Xbar ⟶ S) (hjf : j ≫ fbar = f) [IsProper fbar]
  (i : Z ⟶ Xbar) [IsClosedImmersion i] (hij : Set.range j.base = (Set.range i.base)ᶜ)
  [IsFinite (i ≫ fbar)]
  [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f] (jf : CompactificationOf (Over.mk f))

/-- `H^q(Φ(X[0]))` is `Hᵠ` of `Φ` along `singlePlus`, for a triangulated `Φ`. -/
def singleHomologyPlusSingleIso {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    [Category* B] [Abelian B] [HasDerivedCategory B]
    (Φ : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) (q : ℤ) :
    singleHomology Φ q ≅
      DerivedCategory.Plus.singleFunctor A 0 ⋙ Φ ⋙ DerivedCategory.Plus.homologyFunctor B q :=
  Functor.isoWhiskerRight (StacksDraft.DerivedSectionsComparison.singlePlusQIso A)
    (Φ ⋙ DerivedCategory.Plus.homologyFunctor B q)

/-- The direct image of étale module sheaves preserves finite limits, being a right adjoint. -/
private theorem preservesFiniteLimits_etaleModuleDirectImage (N : ℕ) {X S : Scheme.{u}}
    (fbar : X ⟶ S) : PreservesFiniteLimits (etaleModuleDirectImage.{u, 0} (ZMod N) fbar) :=
  have : PreservesLimitsOfSize.{0, 0} (etaleModuleDirectImage.{u, 0} (ZMod N) fbar) :=
    (etaleModuleInverseImageAdj.{u, 0} (ZMod N) fbar).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

include hjf hij in
/-- **`R⁰ f_!(f⁻¹ G) = 0` for a family of curves with a surjective étale boundary**: for
`F = f̄⁻¹ G`, the long exact sequence of `0 → j_! j⁻¹ F → F → i_* i⁻¹ F → 0` under `Rf̄_*` starts
`0 → R⁰f̄_*(j_! j⁻¹ F) → f̄_* F → f̄_* i_* i⁻¹ F`, the first term on the left being
`R^{-1} f̄_*(i_* i⁻¹ F) = 0`, and the last map is a monomorphism
(`Stacks.EtaleCohomology.mono_etaleModuleDirectImage_map_inverseImageAdj_unit`). -/
theorem isZero_lowerShriekHomology_zero_of_factorization [Flat fbar] [GeometricallyConnected fbar]
    [Etale (i ≫ fbar)] [Surjective (i ≫ fbar)] (G : EtaleModules.{u, 0} (ZMod N) S) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((derivedLowerShriek.{u, 0} f jf (ZMod N)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) f).obj G)))) := by
  refine IsZero.of_iso ?_ ((lowerShriekHomologyFactorizationIso N f j fbar hjf jf 0).app G)
  let F := (etaleModuleInverseImage.{u, 0} (ZMod N) fbar).obj G
  obtain ⟨h, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage (ZMod N) i j hij F
  let Φ := etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar
  let SC := ShortComplex.mk ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j).counit.app F)
    ((etaleModuleInverseImageAdj.{u, 0} (ZMod N) i).unit.app F) h
  refine IsZero.of_iso ?_ ((singleHomologyPlusSingleIso Φ 0).app SC.X₁).symm
  -- `R⁰ f̄_* ≅ f̄_*`
  have := preservesFiniteLimits_etaleModuleDirectImage N fbar
  let ε : singleHomology Φ 0 ≅ etaleModuleDirectImage.{u, 0} (ZMod N) fbar :=
    singleHomologyPlusSingleIso Φ 0 ≪≫
      ((etaleModuleDirectImage.{u, 0} (ZMod N) fbar).isoRightDerivedPlusSingle 0).symm
  have hm : Mono ((etaleModuleDirectImage.{u, 0} (ZMod N) fbar).map SC.g) :=
    mono_etaleModuleDirectImage_map_inverseImageAdj_unit N i fbar G
  have hcomp : Mono ((singleHomology Φ 0).map SC.g ≫ ε.hom.app SC.X₃) :=
    (ε.hom.naturality SC.g).symm ▸ @mono_comp _ _ _ _ _ _ (IsIso.mono_of_iso _) _ hm
  have hg : Mono ((singleHomology Φ 0).map SC.g) :=
    @mono_of_mono _ _ _ _ _ _ _ hcomp
  have h₃ : IsZero ((singleHomology Φ (-1)).obj SC.X₃) :=
    isZero_singleHomology_directImage_of_isFinite (ZMod N) i fbar _ (-1) (by norm_num)
  have hf : Mono ((singleHomology Φ 0).map SC.f) :=
    (singleHomology_exact₁ Φ hS (-1) 0 (by norm_num)).mono_g (h₃.eq_of_src _ _)
  have hf₀ : (singleHomology Φ 0).map SC.f = 0 := by
    rw [← cancel_mono ((singleHomology Φ 0).map SC.g), zero_comp, ← Functor.map_comp, SC.zero,
      Functor.map_zero]
  exact IsZero.of_mono_eq_zero _ hf₀

include hjf hij in
/-- **`R^q f_!(f⁻¹ G)` is locally constant of finite type** for every `q`, as soon as `G` and every
`H^q(Rf̄_*(f̄⁻¹ G))` are, for a family of curves whose boundary is finite étale over the base: in
the triangle `Rf̄_*(j_! j⁻¹ F) → Rf̄_* F → Rf̄_*(i_* i⁻¹ F)` of `F = f̄⁻¹ G`, the last term is
`(i ≫ f̄)_* i⁻¹ F` in degree `0` (locally constant of finite type, Tag 095B), and the finite type
locally constant sheaves form a weak Serre class (Tag 093U). -/
theorem isFiniteTypeLocallyConstant_lowerShriekHomology_of_factorization [Etale (i ≫ fbar)]
    (G : EtaleModules.{u, 0} (ZMod N) S)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod N) S.smallEtaleTopology G)
    (hF : ∀ q : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod N) S.smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleInverseImage.{u, 0} (ZMod N) fbar).obj G)))))
    (q : ℤ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod N) S.smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((derivedLowerShriek.{u, 0} f jf (ZMod N)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod N) f).obj G)))) := by
  let P : ObjectProperty (EtaleModules.{u, 0} (ZMod N) S) :=
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      S.smallEtaleTopology (ZMod N)
  change P _
  refine P.prop_of_iso ((lowerShriekHomologyFactorizationIso N f j fbar hjf jf q).app G).symm ?_
  let F := (etaleModuleInverseImage.{u, 0} (ZMod N) fbar).obj G
  obtain ⟨h, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage (ZMod N) i j hij F
  let Φ := etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar
  let SC := ShortComplex.mk ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j).counit.app F)
    ((etaleModuleInverseImageAdj.{u, 0} (ZMod N) i).unit.app F) h
  let T := Φ.mapTriangle.obj (Pretriangulated.Triangle.mk
    ((DerivedCategory.Plus.singleFunctor _ 0).map SC.f)
    ((DerivedCategory.Plus.singleFunctor _ 0).map SC.g) (Stacks.DerivedIndexing.singleδPlus hS))
  have hT : T ∈ distTriang _ :=
    Φ.map_distinguished _ (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hS)
  refine prop_homology_obj₁_of_distTriang_plus P T hT (fun p => hF p) (fun p => ?_) q
  -- the boundary term: `(i ≫ f̄)_* i⁻¹ F` in degree `0`, and `0` in the other degrees
  change P ((DerivedCategory.Plus.homologyFunctor _ p).obj
    (Φ.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj SC.X₃)))
  by_cases hp : p = 0
  · subst hp
    have := preservesFiniteLimits_etaleModuleDirectImage N fbar
    refine P.prop_of_iso
      (((etaleModuleDirectImage.{u, 0} (ZMod N) fbar).isoRightDerivedPlusSingle 0).app SC.X₃) ?_
    exact P.prop_of_iso ((etaleModuleDirectImageComp.{u, 0} (ZMod N) i fbar (i ≫ fbar) rfl).app
      ((etaleModuleInverseImage.{u, 0} (ZMod N) i).obj F)).symm
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_finiteEtalePushforward_modules.{u, 0, 0}
        (i ≫ fbar) (ZMod N) _
        (isFiniteTypeLocallyConstant_etaleModuleInverseImage_of_hom i (ZMod N) F
          (isFiniteTypeLocallyConstant_etaleModuleInverseImage_of_hom fbar (ZMod N) G hG)))
  · exact P.prop_of_isZero (IsZero.of_iso
      (isZero_singleHomology_directImage_of_isFinite (ZMod N) i fbar _ p hp)
      ((singleHomologyPlusSingleIso Φ p).app SC.X₃).symm)

end LowDegree

end Stacks.EtaleCohomology

end
