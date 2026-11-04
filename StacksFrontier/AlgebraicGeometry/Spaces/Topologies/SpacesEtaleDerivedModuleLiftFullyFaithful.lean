module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftInjectiveSeparator
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGEResolutionTower
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedLimitsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedModuleLift

/-!
# The derived transport to the spaces-étale site is fully faithful into `D_QCoh`

Let `X` be an algebraic space over a scheme `S` and let
`ι : D(𝒪_{X_étale}) ⥤ D(𝒪_{X_{spaces,étale}})` be the derived transport
`AlgebraicGeometry.Space.toSpacesEtaleDerivedModules`, induced by the exact functor
`AlgebraicGeometry.Space.toSpacesEtaleModules` (the universe lift of the sections followed by the
equivalence of Stacks 03G1). This file proves that `ι` is bijective on `Hom(A, B)` for every `A`
and every `B ∈ D_QCoh(𝒪_X)`.

The proof follows Stacks 070P/070Q: an object `B ∈ D_QCoh` is the derived limit of its
truncations `τ_{≥ -n} B` (Stacks 08F6), so the limit of a tower of bounded below injective
resolutions of the truncations is a K-injective resolution of `B`. The transport is exact, fully
faithful, preserves injective objects and countable inverse limits, so it carries that resolution
to a K-injective complex (Stacks 070L on the spaces-étale site), and morphisms into a K-injective
complex are homotopy classes of maps on both sides.

## Main results

* `AlgebraicGeometry.Space.preservesInjectiveObjects_smallEtaleModuleULift`: the universe lift
  of `𝒪_X`-modules on `X_étale` preserves injective objects.
* `AlgebraicGeometry.Space.bijective_toSpacesEtaleDerivedModules_map`: **`ι` is bijective on
  `Hom(A, B)` for `B ∈ D_QCoh(𝒪_X)`.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
-- No global `HasDerivedCategory` instance applies to modules on the small étale site, which is
-- not a `SmallCategory`; at low priority the standard model chooses nothing where a global one
-- exists. The spaces-étale model is passed explicitly.
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The universe lift of `𝒪_X`-modules on `X_étale` preserves injective objects.** -/
instance preservesInjectiveObjects_smallEtaleModuleULift :
    (smallEtaleModuleULift B S hS X).PreservesInjectiveObjects :=
  haveI : HasSeparator (Modules.{u, u} B S hS X.1 X.2) :=
    @IsGrothendieckAbelian.hasSeparator.{u} _ _ _ (isGrothendieckAbelian_modules B S hS X.1 X.2)
  Stacks.SheafOfModules.preservesInjectiveObjects_moduleULift_max.{0} _

/-- The transport `toSpacesEtaleModules` preserves injective objects: it is the universe lift
followed by an equivalence. -/
instance : (toSpacesEtaleModules B S hS X).PreservesInjectiveObjects :=
  inferInstanceAs (smallEtaleModuleULift B S hS X ⋙
    (spacesEtaleToSmallEtaleModulesEquivalence B S hS X).inverse).PreservesInjectiveObjects

/-- The transport `toSpacesEtaleModules` preserves limits of towers indexed by `ℕᵒᵖ`. -/
instance : PreservesLimitsOfShape ℕᵒᵖ (toSpacesEtaleModules B S hS X) :=
  inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ (smallEtaleModuleULift B S hS X ⋙
    (spacesEtaleToSmallEtaleModulesEquivalence B S hS X).inverse))

/-- The transport `toSpacesEtaleModules` is full. -/
instance : (toSpacesEtaleModules B S hS X).Full :=
  (fullyFaithfulToSpacesEtaleModules B S hS X).full

/-- The transport `toSpacesEtaleModules` is faithful. -/
instance : (toSpacesEtaleModules B S hS X).Faithful :=
  (fullyFaithfulToSpacesEtaleModules B S hS X).faithful

/-- **The derived transport to the spaces-étale site is bijective on morphisms into `D_QCoh`**:
for `A ∈ D(𝒪_{X_étale})` and `B ∈ D_QCoh(𝒪_{X_étale})`, `ι : Hom(A, B) ⟶ Hom(ιA, ιB)` is a
bijection. -/
theorem bijective_toSpacesEtaleDerivedModules_map
    (A K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hK : QcohDerived B S hS X K) :
    Function.Bijective ((toSpacesEtaleDerivedModules B S hS X).map : (A ⟶ K) → _) := by
  let := spacesEtaleHasDerivedCategory B S hS X
  have := enoughInjectives_modules B S hS X.1 X.2
  let K₀ := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj K₀ ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) q).obj (DerivedCategory.Q.obj K₀)).IsQuasicoherentOnSite :=
    fun q ↦ SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso eK).symm (hK q)
  have hconv : Stacks.KInjectiveTower.TruncGEConvergent (DerivedCategory.Q.obj K₀) :=
    fun L c p δ hL hc ↦
      isIso_of_isDerivedLimit_truncGETower_unconditional B S hS X.1 X.2 _ hE L c p δ hL hc
  exact (toSpacesEtaleDerivedModules B S hS X).bijective_map_of_iso (Iso.refl A) eK
    (Stacks.KInjectiveTower.bijective_mapDerivedCategory_map_of_truncGEConvergent
      (toSpacesEtaleModules B S hS X) A K₀ hconv)

end AlgebraicGeometry.Space

end
