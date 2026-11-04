module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDerivedSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineFppfDerivedModuleRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherentRestrictScalars
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EvaluationRestrictionHomotopySquare
public import StacksFrontier.Homology.Injectives.KInjective.RightAdjointOfExact

/-!
# The base change property of Stacks 0H15 is the cartesian condition of Stacks 0H0H

Let `𝒳` be an algebraic stack and `K` an object of `D(𝒳_{fppf}, 𝒪)`, with module sections in
`Type (u + 1)`. Two conditions on `K` concern the derived sections over the objects of
`𝒳_{affine}`:

* the property of Stacks 0H15
  (`AlgebraicGeometry.Stack.FlatFppf.HasAffineDerivedSectionsBaseChange`):
  `RΓ(x', K) ⊗^L_{𝒪(x')} 𝒪(x) ⟶ RΓ(x, K)` is a quasi-isomorphism for every morphism `x ⟶ x'` of
  `𝒳_{affine}`;
* membership of the subcategory `Q_𝒳` of the proof of Stacks 0H16
  (`AlgebraicGeometry.Stack.FlatFppf.quasiCoherentDerivedFppfSucc`): the restriction `K'` of `K`
  to `𝒳_{affine, fppf}` has `Rε_*K'` in `QC(𝒳)` (Stacks 0H0H, 0H0X, 0H0C), that is, the comparison
  maps of Stacks 0GYV of `Rε_*K'` on the chaotic site `𝒳_{affine}` are invertible.

This file proves that they agree
(`Stack.FlatFppf.quasiCoherentDerivedFppfSucc_iff_hasAffineDerivedSectionsBaseChange`).

## The argument

Both maps are adjoint transposes of derived restriction maps, so each is invertible exactly when
the restriction map is a universal arrow for derived restriction of scalars
(`CategoryTheory.Functor.isUniversalArrow_iff_isIso`); universality is invariant under compatible
isomorphisms. Represent `K` by a K-injective complex `I`. Then `RΓ(x, K)` is the complex `Γ(x, I)`
and its restriction maps are the termwise ones
(`AlgebraicGeometry.Stack.FlatFppf.isIso_derivedSectionsBaseChange_quotient_iff`). Restriction to
the affine subsite is an exact equivalence, so it keeps `I` K-injective, and `Rε_*K'` is the
complex of presheaves `ε_*(I|_{𝒳_{affine}})`, whose restriction maps are again termwise
(`Stacks.ModulesOnACategory.QuasiCoherentRestrictScalars.isIso_comparison_Q_iff`). Both complexes
have the sections `Γ(x, I)`, with the same restriction maps
(`AlgebraicGeometry.Stack.FlatFppf.affineFppfModuleRestrictionSuccEvaluationIso_restriction`).

## Implementation notes

The ambient derived category is the standard model, as in the statement of Stacks 0H15 at this
universe; the affine one is the locally small model
`Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory` at which `Q_𝒳` is
defined. Restriction of scalars is given exactness instances pinned to the universes at hand, the
universe-polymorphic ones leaving universe constraints unsolved.

## References

* [Stacks Project, Tag 0H15](https://stacks.math.columbia.edu/tag/0H15)
* [Stacks Project, Tag 0H16](https://stacks.math.columbia.edu/tag/0H16)
* [Stacks Project, Tag 0H0H](https://stacks.math.columbia.edu/tag/0H0H)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.HypercohomologyEdge
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.ChaoticComparison

universe u w

namespace CategoryTheory.Functor

variable {A A' : Type*} [Category* A] [Category* A'] [Abelian A] [Abelian A']
  [HasDerivedCategory A] [HasDerivedCategory A'] (R : A ⥤ A') [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- A five-fold composite followed by a right inverse of its last factor, with its first three
factors rewritten. Stated with every object a variable, so that it applies by `exact` where the
objects agree only up to unfolding. -/
private theorem five_comp_comp_eq_of_eq_of_comp_eq_id {C : Type*} [Category* C] {a b c d e f a' : C}
    {x₁ : a ⟶ b} {x₂ : b ⟶ c} {x₃ : c ⟶ d} {x₄ : d ⟶ e} {x₅ : e ⟶ f} {z : f ⟶ e}
    {α : a ⟶ a'} {q : a' ⟶ d} (h : x₁ ≫ x₂ ≫ x₃ = α ≫ q) (hz : x₅ ≫ z = 𝟙 e) :
    (x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅) ≫ z = α ≫ q ≫ x₄ := by
  calc (x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅) ≫ z = (x₁ ≫ x₂ ≫ x₃) ≫ x₄ ≫ (x₅ ≫ z) := by
        simp only [Category.assoc]
    _ = (α ≫ q) ≫ x₄ := by rw [h, hz, Category.comp_id]
    _ = α ≫ q ≫ x₄ := Category.assoc _ _ _

/-- Two arrows of the form `Q(r) ≫ α_A`, with `α : H ⋙ Q₂ ⟶ Q₁ ⋙ G` natural, are related by the
images of a square of complexes. Stated with every object a variable, so that it applies by `exact`
where the objects agree only up to unfolding. -/
theorem map_comp_app_comp_map_map_eq {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂]
    [Category* D₁] [Category* D₂] (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) (H : C₁ ⥤ C₂) (G : D₁ ⥤ D₂)
    (α : H ⋙ Q₂ ⟶ Q₁ ⋙ G) {A B : C₁} {X Y : C₂} (φ : A ⟶ B) (ψ : X ⟶ Y) (r : X ⟶ H.obj A)
    (r' : Y ⟶ H.obj B) (h : r ≫ H.map φ = ψ ≫ r') :
    (Q₂.map r ≫ α.app A) ≫ G.map (Q₁.map φ) = Q₂.map ψ ≫ Q₂.map r' ≫ α.app B := by
  have hn := α.naturality φ
  simp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← Q₂.map_comp, h, Q₂.map_comp, Category.assoc]

/-- **A morphism of complexes into a degreewise image, read on the homotopy category or on
complexes.** For `r : K ⟶ R(L)` the arrow `Q(K) ⟶ R(Q(L))` obtained from `r` through the
factorization of `R.mapDerivedCategory` on complexes is a universal arrow exactly when the arrow
obtained through the factorization on the homotopy category is; the identity in the middle is the
comparison between the degreewise images of a composite. -/
theorem isUniversalArrow_Qh_map_comp_mapDerivedCategoryFactorsh_inv_iff
    {K : CochainComplex A' ℤ} {L : CochainComplex A ℤ}
    (r : K ⟶ (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :
    R.mapDerivedCategory.IsUniversalArrow
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map r) ≫
          DerivedCategory.Qh.map (𝟙 _) ≫
          R.mapDerivedCategoryFactorsh.inv.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) ↔
      R.mapDerivedCategory.IsUniversalArrow
        (DerivedCategory.Q.map r ≫ R.mapDerivedCategoryFactors.inv.app L) := by
  have hid₀ : DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map r) ≫
      DerivedCategory.Qh.map (𝟙 _) ≫ R.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map r) ≫
        R.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L) :=
    congrArg (_ ≫ ·) ((congrArg (· ≫ _) (Functor.map_id _ _)).trans (Category.id_comp _))
  rw [hid₀]
  refine IsUniversalArrow.iff_of_iso ((DerivedCategory.quotientCompQhIso A').app K)
    ((DerivedCategory.quotientCompQhIso A).app L) ?_
  rw [Stacks.Cohomology.HypercohomologyEdge.mapDerivedCategoryFactorsh_inv_app_quotient]
  simp only [Iso.app_hom]
  have hn := (DerivedCategory.quotientCompQhIso A').hom.naturality r
  have hβ : R.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).inv.app L) ≫
      R.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app L) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  have hid : DerivedCategory.Qh.map
      ((R.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app L) = 𝟙 _ :=
    (congrArg DerivedCategory.Qh.map
      (Stacks.Cohomology.HypercohomologyEdge.mapHomotopyCategoryFactors_hom_app R L)).trans
      (Functor.map_id _ _)
  have hn' : DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map r) ≫
      DerivedCategory.Qh.map ((R.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app L) ≫
        (DerivedCategory.quotientCompQhIso A').hom.app
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) =
      (DerivedCategory.quotientCompQhIso A').hom.app K ≫ DerivedCategory.Q.map r := by
    refine Eq.trans ?_ ((congrArg (_ ≫ ·) (Category.id_comp _)).trans hn)
    exact congrArg (fun t => _ ≫ t ≫ _) hid
  exact five_comp_comp_eq_of_eq_of_comp_eq_id hn' hβ

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

section Evaluation

open Stacks.Cohomology.DerivedLowerShriek.ULift

/-- Sections over an object `x` of `𝒳_{affine}` of the restriction of a sheaf of modules `M` to
the affine subsite, read on the chaotic site, are the sections `M(x)`: the restriction changes the
module structure only through `ULift` and identities, so the identity of the underlying group is
linear. -/
def affineFppfModuleRestrictionSuccEvaluationIsoApp (x : AffineCategory B S hS 𝒳.val.val.p)
    (M : SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :
    (affineFppfModuleRestrictionSucc B S hS 𝒳 ⋙ epsilonPushforward.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O) ⋙
        PresheafOfModules.evaluation _ (op x)).obj M ≅
      (SheafOfModules.evaluation (ambientRingStructureSheaf B S hS 𝒳) (op x.obj)).obj M :=
  ModuleCat.restrictScalarsId'App
      (NatTrans.app
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O).obj)
        (op x)).hom rfl
      ((ModuleCat.restrictScalars
        (((targetRingTransport.{u + 1} (affineFppfRingedSite B S hS 𝒳).J
          (affineFppfRingedSite B S hS 𝒳).O).symm.iso (op x)).toRingHom)).obj
        ((ModuleCat.restrictScalars
          (NatTrans.app (InducedCategory.Hom.hom (𝟙 (Stacks.DenseSubsiteModules.ringRestriction
            (affineFppfRingedSite B S hS 𝒳).J
            (fppfTopology B S hS 𝒳) (AffineCategory.inclusion B S hS 𝒳.val.val.p)
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (Stacks.Cohomology.DerivedLowerShriek.ULift.liftedStructureSheaf.{u + 1}
                (fppfTopology B S hS 𝒳)
                (ambientStructureSheaf B S hS 𝒳)))))) (op x)).hom).obj
          ((ModuleCat.restrictScalars
            (((targetRingTransport.{u + 1} (fppfTopology B S hS 𝒳)
              (ambientStructureSheaf B S hS 𝒳)).iso (op x.obj)).toRingHom)).obj
            (M.val.obj (op x.obj))))) ≪≫
    (ModuleCat.restrictScalars
        (((targetRingTransport.{u + 1} (affineFppfRingedSite B S hS 𝒳).J
          (affineFppfRingedSite B S hS 𝒳).O).symm.iso (op x)).toRingHom)).mapIso
      (ModuleCat.restrictScalarsId'App
        (NatTrans.app (InducedCategory.Hom.hom (𝟙 (Stacks.DenseSubsiteModules.ringRestriction
            (affineFppfRingedSite B S hS 𝒳).J
            (fppfTopology B S hS 𝒳) (AffineCategory.inclusion B S hS 𝒳.val.val.p)
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (Stacks.Cohomology.DerivedLowerShriek.ULift.liftedStructureSheaf.{u + 1}
                (fppfTopology B S hS 𝒳)
                (ambientStructureSheaf B S hS 𝒳)))))) (op x)).hom rfl
        ((ModuleCat.restrictScalars
            (((targetRingTransport.{u + 1} (fppfTopology B S hS 𝒳)
              (ambientStructureSheaf B S hS 𝒳)).iso (op x.obj)).toRingHom)).obj
            (M.val.obj (op x.obj)))) ≪≫
    (ModuleCat.restrictScalarsComp'App
        (((targetRingTransport.{u + 1} (affineFppfRingedSite B S hS 𝒳).J
          (affineFppfRingedSite B S hS 𝒳).O).symm.iso (op x)).toRingHom)
        (((targetRingTransport.{u + 1} (fppfTopology B S hS 𝒳)
          (ambientStructureSheaf B S hS 𝒳)).iso (op x.obj)).toRingHom) _ rfl
        (M.val.obj (op x.obj))).symm ≪≫
    ModuleCat.restrictScalarsId'App _
      (RingHom.ext fun r =>
        ((targetRingTransport.{u + 1} (affineFppfRingedSite B S hS 𝒳).J
          (affineFppfRingedSite B S hS 𝒳).O).iso_symm_iso (op x) r).trans
        (ConcreteCategory.congr_hom
          ((Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O).obj.map_id
            (op x)) r))
      (M.val.obj (op x.obj))

/-- Sections over an object `x` of `𝒳_{affine}` of the restriction of a sheaf of modules to the
affine subsite, read on the chaotic site, are its sections over `x` in `𝒳`, naturally. -/
def affineFppfModuleRestrictionSuccEvaluationIso (x : AffineCategory B S hS 𝒳.val.val.p) :
    affineFppfModuleRestrictionSucc B S hS 𝒳 ⋙ epsilonPushforward.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O) ⋙
        PresheafOfModules.evaluation _ (op x) ≅
      SheafOfModules.evaluation (ambientRingStructureSheaf B S hS 𝒳) (op x.obj) :=
  NatIso.ofComponents (affineFppfModuleRestrictionSuccEvaluationIsoApp B S hS 𝒳 x)
    (fun _ => by ext; rfl)

/-- The identification `affineFppfModuleRestrictionSuccEvaluationIso` is compatible with the
restriction maps along a morphism of `𝒳_{affine}`. -/
theorem affineFppfModuleRestrictionSuccEvaluationIso_restriction
    {x y : AffineCategory B S hS 𝒳.val.val.p} (a : x ⟶ y)
    (M : SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :
    (PresheafOfModules.restriction
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O).obj a.op).app
        ((affineFppfModuleRestrictionSucc B S hS 𝒳 ⋙ epsilonPushforward.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)).obj M) ≫
      (ModuleCat.restrictScalars
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (affineFppfRingedSite B S hS 𝒳).O).obj.map a.op).hom).map
        ((affineFppfModuleRestrictionSuccEvaluationIso B S hS 𝒳 x).hom.app M) =
      (affineFppfModuleRestrictionSuccEvaluationIso B S hS 𝒳 y).hom.app M ≫
        (sectionsRestrict (ambientRingStructureSheaf B S hS 𝒳) a.hom).app M := by
  ext; rfl

end Evaluation

section Ambient

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasSheafify_fppfTopology_largeSections
  wEqualsLocallyBijective_fppfTopology_largeSections
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
attribute [local instance] isGrothendieckAbelian_ambientModulesSucc
attribute [-instance] Stacks.ModulesOnACategory.QuasiCoherentEquivalence.rsPreservesFiniteLimits
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.rsPreservesFiniteColimits
/-- Restriction of scalars of modules with sections in `Type (u + 1)` along a homomorphism of rings
in `Type u` preserves finite limits; pinned to these universes, see the instance notes of
`AffineDerivedSectionsBaseChange`. -/
local instance restrictScalarsSucc_preservesFiniteLimits {A A' : Type u} [Ring A] [Ring A']
    (φ : A →+* A') : PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} φ) :=
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits φ

/-- Restriction of scalars of modules with sections in `Type (u + 1)` along a homomorphism of rings
in `Type u` preserves finite colimits. -/
local instance restrictScalarsSucc_preservesFiniteColimits {A A' : Type u} [Ring A] [Ring A']
    (φ : A →+* A') : PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1} φ) :=
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits φ

/-- The map of Stacks 0H15 along `a` is invertible exactly when the derived restriction map
`RΓ(x', K) ⟶ RΓ(x, K)` is a universal arrow for derived restriction of scalars. -/
private theorem isIso_derivedSectionsBaseChange_iff_isUniversalArrow {x x' : 𝒳.val.val.obj}
    (a : x ⟶ x')
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))) :
    IsIso (derivedSectionsBaseChange B S hS 𝒳 a K) ↔
      (Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dRestrictScalars
        ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op)).IsUniversalArrow
        ((derivedSectionsRestrict.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳)
          a).app K) :=
  (Functor.isUniversalArrow_iff_isIso (dBaseChangeAdj.{u, u + 1}
    ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op)
    (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x')
    (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x)) _).symm

/-- **The derived base change map at a K-injective complex.** For a K-injective complex `I` of
sheaves of `𝒪_𝒳`-modules and `a : x ⟶ x'`, the map of Stacks 0H15 for `I` is a quasi-isomorphism
exactly when the termwise restriction `Γ(x', I) ⟶ Γ(x, I)`, read in the derived category of
`𝒪(x')`-modules, is a universal arrow for derived restriction of scalars. -/
theorem isIso_derivedSectionsBaseChange_quotient_iff
    (I : CochainComplex (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ)
    [I.IsKInjective] {x x' : 𝒳.val.val.obj} (a : x ⟶ x') :
    IsIso (derivedSectionsBaseChange B S hS 𝒳 a (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ↔
      (ModuleCat.restrictScalars.{u + 1}
          ((ambientRingStructureSheaf B S hS 𝒳).obj.map
            a.op).hom).mapDerivedCategory.IsUniversalArrow
        (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (sectionsRestrict (ambientRingStructureSheaf B S hS 𝒳) a) (ComplexShape.up ℤ)).app I) ≫
          (ModuleCat.restrictScalars.{u + 1}
            ((ambientRingStructureSheaf B S hS 𝒳).obj.map
              a.op).hom).mapDerivedCategoryFactors.inv.app
            (((SheafOfModules.evaluation (ambientRingStructureSheaf B S hS 𝒳)
              (op x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
  let O := ambientRingStructureSheaf B S hS 𝒳
  let X := (HomotopyCategory.quotient (SheafOfModules.{u + 1} O) (ComplexShape.up ℤ)).obj I
  have hu : ∀ y : 𝒳.val.val.obj,
      IsIso (((homotopySections.{_, _, _, u + 1} O y).totalRightDerivedUnit
        DerivedCategory.Qh (HomotopyCategory.quasiIso (SheafOfModules.{u + 1} O)
          (ComplexShape.up ℤ))).app X) := fun y =>
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ I
  refine (isIso_derivedSectionsBaseChange_iff_isUniversalArrow B S hS 𝒳 a _).trans ?_
  refine (Functor.IsUniversalArrow.iff_of_iso
    (G := Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dRestrictScalars
      (O.obj.map a.op))
    (g := (homotopySectionsRestrict O a).app X) (@asIso _ _ _ _ _ (hu x'))
    (@asIso _ _ _ _ _ (hu x)) ?_).symm.trans ?_
  · have h := congrArg (fun τ => NatTrans.app τ X) (derivedSectionsRestrict_fac O a)
    rw [sectionsRestrictUnit_eq] at h
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
    exact h.symm
  · have e0 : (homotopySectionsRestrict O a).app X =
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (sectionsRestrict O a) (ComplexShape.up ℤ)).app I)) ≫
        DerivedCategory.Qh.map (𝟙 _) ≫
        (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom).mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((SheafOfModules.evaluation.{u + 1} O (op x)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)) :=
      rfl
    rw [e0]
    exact Functor.isUniversalArrow_Qh_map_comp_mapDerivedCategoryFactorsh_inv_iff
      (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom)
      (L := ((SheafOfModules.evaluation.{u + 1} O (op x)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)
      ((NatTrans.mapHomologicalComplex (sectionsRestrict O a) (ComplexShape.up ℤ)).app I)

/-- **The comparison at a K-injective complex.** For a K-injective complex `I` of sheaves of
`𝒪_𝒳`-modules and a morphism `a : x ⟶ x'` of `𝒳_{affine}`, the map of Stacks 0H15 for `I` along `a`
is invertible exactly when the comparison map of Stacks 0GYV of the complex of presheaves
`ε_*(I|_{𝒳_{affine}})` along `a` is: both are, up to the identification of sections
`affineFppfModuleRestrictionSuccEvaluationIso`, the termwise restriction of sections read as a
universal arrow for derived restriction of scalars. -/
theorem isIso_derivedSectionsBaseChange_quotient_iff_isIso_comparison
    (I : CochainComplex (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ)
    [I.IsKInjective] {x x' : AffineCategory B S hS 𝒳.val.val.p} (a : x ⟶ x') :
    IsIso (derivedSectionsBaseChange B S hS 𝒳 a.hom (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ↔
      IsIso (Stacks.ModulesOnACategory.QuasiCoherentEquivalence.comparison
        (affineBaseChangeData.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p) a.op
        (DerivedCategory.Q.obj (((epsilonPushforward.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (affineFppfRingedSite B S hS 𝒳).O)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
              (((affineFppfModuleRestrictionSucc B S hS 𝒳).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I)))) := by
  let c : ∀ y : AffineCategory B S hS 𝒳.val.val.p,
      ((affineFppfModuleRestrictionSucc B S hS 𝒳 ⋙ epsilonPushforward.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O) ⋙
        PresheafOfModules.evaluation _ (op y)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ≅
      ((SheafOfModules.evaluation.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)
        (op y.obj)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I := fun y =>
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (affineFppfModuleRestrictionSuccEvaluationIso B S hS 𝒳 y).app (I.X i))
      (fun i j _ => ((affineFppfModuleRestrictionSuccEvaluationIso B S hS 𝒳 y).hom.naturality
        (I.d i j)).symm)
  refine (isIso_derivedSectionsBaseChange_quotient_iff B S hS 𝒳 I a.hom).trans
    (Iff.trans ?_ (Stacks.ModulesOnACategory.QuasiCoherentRestrictScalars.isIso_comparison_Q_iff
      _ _ _).symm)
  refine (Functor.IsUniversalArrow.iff_of_iso
    (G := (ModuleCat.restrictScalars.{u + 1}
      ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.hom.op).hom).mapDerivedCategory)
    (DerivedCategory.Q.mapIso (c x')) (DerivedCategory.Q.mapIso (c x)) ?_).symm
  exact Functor.map_comp_app_comp_map_map_eq DerivedCategory.Q DerivedCategory.Q
    ((ModuleCat.restrictScalars.{u + 1}
      ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.hom.op).hom).mapHomologicalComplex
        (ComplexShape.up ℤ))
    (ModuleCat.restrictScalars.{u + 1}
      ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.hom.op).hom).mapDerivedCategory
    (ModuleCat.restrictScalars.{u + 1}
      ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.hom.op).hom).mapDerivedCategoryFactors.inv
    (c x).hom (c x').hom _ _ (HomologicalComplex.hom_ext _ _ fun n =>
      affineFppfModuleRestrictionSuccEvaluationIso_restriction B S hS 𝒳 a (I.X n))

/-- The map of Stacks 0H15 along `a` is invertible at `K` exactly when it is at an isomorphic
object: the derived restriction maps are natural. -/
theorem isIso_derivedSectionsBaseChange_iff_of_iso
    {K K' : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))}
    (e : K ≅ K') {x x' : 𝒳.val.val.obj} (a : x ⟶ x') :
    IsIso (derivedSectionsBaseChange B S hS 𝒳 a K) ↔
      IsIso (derivedSectionsBaseChange B S hS 𝒳 a K') := by
  refine (isIso_derivedSectionsBaseChange_iff_isUniversalArrow B S hS 𝒳 a K).trans
    (Iff.trans ?_ (isIso_derivedSectionsBaseChange_iff_isUniversalArrow B S hS 𝒳 a K').symm)
  exact Functor.IsUniversalArrow.iff_of_iso
    ((derivedSections.{_, _, _, u + 1, u + 1} _ x').mapIso e)
    ((derivedSections.{_, _, _, u + 1, u + 1} _ x).mapIso e)
    ((derivedSectionsRestrict.{_, _, _, u + 1, u + 1} _ a).naturality e.hom).symm

/-- **The comparison of Stacks 0H15 with the cartesian condition of Stacks 0H0H.** An object `K`
of `D(𝒳_{fppf}, 𝒪)` (module universe `u + 1`, the standard model) lies in the subcategory `Q_𝒳` of
the proof of Stacks 0H16 — the objects whose restriction `K'` to `𝒳_{affine, fppf}` has `Rε_*K'`
in `QC(𝒳)` (Stacks 0H0X, 0H0C) — exactly when it has the derived base change property of
Stacks 0H15: `RΓ(x', K) ⊗^L_{𝒪(x')} 𝒪(x) ⟶ RΓ(x, K)` is a quasi-isomorphism for every morphism
`x ⟶ x'` of `𝒳_{affine}`.

Both conditions are invertibility of adjoint transposes of derived restriction maps, so of the
restriction maps as universal arrows for derived restriction of scalars. For `K` represented by a
K-injective complex `I`, `RΓ(x, K)` is the complex of sections `Γ(x, I)`, `Rε_*K'` is the complex
of presheaves `ε_*(I|_{𝒳_{affine}})` (restriction to the affine subsite being an exact equivalence,
it preserves K-injectivity) with the same sections, and under these identifications both
restriction maps are the termwise restriction of sections. -/
theorem quasiCoherentDerivedFppfSucc_iff_hasAffineDerivedSectionsBaseChange
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))) :
    quasiCoherentDerivedFppfSucc B S hS 𝒳 K ↔ HasAffineDerivedSectionsBaseChange B S hS 𝒳 K := by
  let : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)) :=
    SheafOfModules.isGrothendieckAbelian_of_univLE.{u + 1} _
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)) :=
    Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory.{u + 1} _
  -- `K` is represented by a K-injective complex
  obtain ⟨I, hI, ⟨e⟩⟩ : ∃ I : CochainComplex
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ, I.IsKInjective ∧
        Nonempty (K ≅ DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
    obtain ⟨I, f, hI, hf⟩ := Stacks.Cohomology.Localization.enoughKInjectives
      (DerivedCategory.Qh.objPreimage K).as
    have hiso : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f)) :=
      Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf)
    exact ⟨I, hI, ⟨(DerivedCategory.Qh.objObjPreimageIso K).symm ≪≫
      @asIso _ _ _ _ (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f))
        hiso⟩⟩
  -- the derived pushforward of the restriction of `I` is the complex of presheaves of sections
  have : CochainComplex.IsKInjective
      (((affineFppfModuleRestrictionSucc B S hS 𝒳).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    Stacks.Injectives.isKInjective_mapHomologicalComplex_of_isEquivalence _ I
  have : IsIso ((derivedEpsilonPushforwardUnit.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((affineFppfModuleRestrictionSucc B S hS 𝒳).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I))) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ _
  let eD : (derivedEpsilonPushforward.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)).obj
        ((affineFppfDerivedRestrictionSucc B S hS 𝒳).obj (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ≅
      DerivedCategory.Q.obj (((epsilonPushforward.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (affineFppfRingedSite B S hS 𝒳).O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (((affineFppfModuleRestrictionSucc B S hS 𝒳).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)) :=
    (derivedEpsilonPushforward.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)).mapIso
        ((affineFppfModuleRestrictionSucc B S hS 𝒳).mapDerivedCategoryFactorsh.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≪≫
      (asIso ((derivedEpsilonPushforwardUnit.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((affineFppfModuleRestrictionSucc B S hS 𝒳).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)))).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  have key : ∀ {x x' : AffineCategory B S hS 𝒳.val.val.p} (a : x ⟶ x'),
      IsIso (derivedSectionsBaseChange B S hS 𝒳 a.hom K) ↔
        IsIso (Stacks.ModulesOnACategory.QuasiCoherentEquivalence.comparison
          (affineBaseChangeData.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p) a.op
          ((derivedEpsilonPushforward.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)).obj
              ((affineFppfDerivedRestrictionSucc B S hS 𝒳).obj K))) := fun a =>
    (isIso_derivedSectionsBaseChange_iff_of_iso B S hS 𝒳 e a.hom).trans <|
      (isIso_derivedSectionsBaseChange_quotient_iff_isIso_comparison B S hS 𝒳 I a).trans <|
        (Stacks.ModulesOnACategory.QuasiCoherentRestrictScalars.isIso_comparison_iff_of_iso _ _
          eD).symm.trans
          (Stacks.ModulesOnACategory.QuasiCoherentRestrictScalars.isIso_comparison_iff_of_iso _ _
            ((derivedEpsilonPushforward.{u + 1}
              (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)).mapIso
                ((affineFppfDerivedRestrictionSucc B S hS 𝒳).mapIso e))).symm
  constructor
  · intro h x x' a hx hx'
    exact (key (x := ⟨x, hx⟩) (x' := ⟨x', hx'⟩) (ObjectProperty.homMk a)).2 (h _)
  · intro h U V a
    exact (key a.unop).1 (h a.unop.hom U.unop.property V.unop.property)

end Ambient

end AlgebraicGeometry.Stack.FlatFppf

end
