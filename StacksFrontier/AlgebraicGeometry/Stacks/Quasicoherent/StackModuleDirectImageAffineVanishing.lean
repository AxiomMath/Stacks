module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineObjectEtaleCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineObjectsFppfCovering
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EtaleAffineCovering
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleDirectImageSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesEnoughInjectives
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleRule
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.VanishingFromSectionsFormula

/-!
# Higher direct images on the `τ`-sites computed by a sections formula

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and `τ` one of the five associated
topologies.  This file records the sections formula for the direct image
`AlgebraicGeometry.Stack.stackModuleDirectImage` at module universe `u`: if `(x₀, f x₀ ⟶ y)` is
terminal in `CostructuredArrow f y`, then `Γ(y, f_* M) = Γ(x₀, M)` naturally in `M`.  From it,
and the étale affine acyclicity of
`AlgebraicGeometry.FibredSite.isZero_rightDerived_evaluation_of_isAffine_etale`, the higher
direct images on the étale sites vanish on modules cartesian along étale morphisms of affines,
as soon as every object of `𝒴` lying over an affine scheme has such a terminal arrow from an
object lying over an affine scheme.

## Main definitions

* `AlgebraicGeometry.Stack.stackModuleDirectImageSheafSectionsIsoOfIsTerminal`: the sections
  formula `AlgebraicGeometry.Stack.stackModuleDirectImageSectionsIsoOfIsTerminal`, read through
  the sections functors of the underlying abelian sheaves.

## Main results

* `AlgebraicGeometry.Stack.isZero_stackModuleHigherDirectImage_etale_of_isTerminal`: the
  vanishing of `Rⁱf_*`, `i > 0`, on the étale sites.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (τ : SiteKind)

/-- The sections formula `AlgebraicGeometry.Stack.stackModuleDirectImageSectionsIsoOfIsTerminal`
read through `SheafOfModules.toSheaf` and the sections functors. -/
def stackModuleDirectImageSheafSectionsIsoOfIsTerminal {y : 𝒴.val.val.obj}
    {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y} (ht : IsTerminal t) :
    stackModuleDirectImage B S hS f τ ⋙
      SheafOfModules.toSheaf (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids τ) ⋙
      (sheafSections (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p τ)
        AddCommGrpCat.{u}).obj (op y) ≅
    SheafOfModules.toSheaf (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ) ⋙
      (sheafSections (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
        AddCommGrpCat.{u}).obj (op t.left) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) ≪≫
    stackModuleDirectImageSectionsIsoOfIsTerminal B S hS f τ ht ≪≫
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **The higher direct images on the étale sites vanish on modules cartesian along étale
morphisms of affines**, for a 1-morphism `f : 𝒳 ⟶ 𝒴` such that every object `y` of `𝒴` lying
over an affine scheme carries a terminal arrow `(x₀ y, f (x₀ y) ⟶ y)` of
`CostructuredArrow f y` with `x₀ y` lying over an affine scheme — which is what an affine
1-morphism, for instance one between stacks represented by affine schemes, provides.

The higher direct image is computed by the sections formula
`AlgebraicGeometry.Stack.stackModuleDirectImageSectionsIsoOfIsTerminal`, and the sections over
`x₀ y` have no higher cohomology by
`AlgebraicGeometry.FibredSite.isZero_rightDerived_evaluation_of_isAffine_etale`; the dimension
shifting is `SheafOfModules.isZero_rightDerived_of_sectionsFormula`. -/
theorem isZero_stackModuleHigherDirectImage_etale_of_isTerminal
    (t : ∀ y : 𝒴.val.val.obj, IsAffine (FibredSite.schemeOf B S hS 𝒴.val.val.p y) →
      CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y)
    (ht : ∀ y hy, IsTerminal (t y hy))
    (hx₀ : ∀ y hy, IsAffine (FibredSite.schemeOf B S hS 𝒳.val.val.p (t y hy).left))
    (F : SheafOfModules.{u} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .etale))
    (hF : FibredSite.IsCartesianAlongEtaleAffines B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F)
    (i : ℕ) (hi : 0 < i) :
    IsZero ((stackModuleHigherDirectImage B S hS f .etale i).obj F) := by
  let := hasSheafify_associatedTopology_siteKind B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    .etale
  let := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒳.val.val.p .etale
  let := hasSheafify_associatedTopology_siteKind B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
    .etale
  let := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒴.val.val.p .etale
  let := enoughInjectives_moduleRingSheaf B S hS 𝒳 .etale
  let : EnoughInjectives (SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale)) :=
    enoughInjectives_moduleRingSheaf B S hS 𝒳 .etale
  let : IsGrothendieckAbelian.{u}
      (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  let : HasExt.{u}
      (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  let : HasExt.{u + 1}
      (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  let : HasExt.{u + 1} (SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale)) :=
    hasExt_of_enoughInjectives _
  have : PreservesFiniteLimits (stackModuleDirectImage B S hS f .etale) :=
    have := (stackModuleInverseDirectImageAdjunction B S hS f .etale).rightAdjoint_preservesLimits
    inferInstance
  exact SheafOfModules.isZero_rightDerived_of_sectionsFormula
    (stackModuleDirectImage B S hS f .etale)
    (fun y => IsAffine (FibredSite.schemeOf B S hS 𝒴.val.val.p y))
    (fun U T hT => FibredSite.mem_etale_of_forall_isAffine B S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids U T hT) (fun y hy => (t y hy).left)
    (fun y hy => stackModuleDirectImageSheafSectionsIsoOfIsTerminal B S hS f .etale (ht y hy)) F
    (fun y hy n hn => FibredSite.isZero_rightDerived_evaluation_of_isAffine_etale B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F hF (hx₀ y hy) n hn) i hi

end AlgebraicGeometry.Stack
