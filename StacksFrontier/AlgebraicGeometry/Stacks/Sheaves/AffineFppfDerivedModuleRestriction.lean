module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingDerivedEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfCoherator
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ULiftModuleDerivedLowerShriek

/-!
# The equivalence of ringed topoi of Stacks 0H0C on modules and derived categories, at `u + 1`

Let `𝒳` be an algebraic stack. The inclusion of the affine subsite `𝒳_{affine, fppf}` into the
fppf site `𝒳_{fppf}` is a dense subsite (**Stacks 0H0B**), so restriction of sections along it is
an equivalence of ringed topoi (**Stacks 0H0C**). This file records that equivalence on sheaves
of modules with sections in `Type (u + 1)` — the module universe of `QC(𝒳)` (Stacks 0H0H, 0H0X)
and of `D_QCoh(𝒪_𝒳)` at module universe `u + 1` — and on their derived categories:

* `AlgebraicGeometry.Stack.FlatFppf.affineFppfModuleRestrictionEquivalenceSucc`: restriction
  `Mod(𝒳_{fppf}, 𝒪) ≌ Mod(𝒳_{affine, fppf}, O)`, by the Comparison Lemma for sheaves of modules
  `Stacks.DenseSubsiteModules.moduleRestrictionEquivalence` after raising the structure rings to
  `Type (u + 1)`, which changes no presheaf of sections;
* `AlgebraicGeometry.Stack.FlatFppf.affineFppfDerivedRestrictionSucc`: the induced functor on
  derived categories, computed degreewise, which is an equivalence
  (`AlgebraicGeometry.Stack.FlatFppf.isEquivalence_affineFppfDerivedRestrictionSucc`), for any
  models of the two derived categories;
* `AlgebraicGeometry.Stack.FlatFppf.quasiCoherentDerivedFppfSucc` and
  `AlgebraicGeometry.Stack.FlatFppf.quasiCoherentDerivedEquivalenceFppfSucc`: the full subcategory
  `Q_𝒳 ⊂ D(𝒳_{fppf}, 𝒪)` of the proof of **Stacks 0H16** and the equivalence `QC(𝒳) ≌ Q_𝒳`
  (Stacks 0H0X followed by the above).

No `@[stacks]` attribute is claimed: Stacks 0H0C is registered on the ringed topoi, and the
statements here are steps of the proof of Stacks 0H16.

## References

* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
* [Stacks Project, Tag 0H0C](https://stacks.math.columbia.edu/tag/0H0C)
* [Stacks Project, Tag 0H16](https://stacks.math.columbia.edu/tag/0H16)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w t t'

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The affine subsite `𝒳_{affine, fppf}` with the restricted structure sheaf, the ringed site of
Stacks 0H0D at the fppf topology. -/
abbrev affineFppfRingedSite : RingedSite.{u + 1, u, u} :=
  AffineCategory.siteKindRingedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf

/-- **Stacks 0H0B** at the fppf topology, with the topologies of the fppf site of `𝒳` and of the
ringed site `affineFppfRingedSite`. -/
instance isDenseSubsite_affineInclusion_fppfTopology :
    (AffineCategory.inclusion B S hS 𝒳.val.val.p).IsDenseSubsite
      (affineFppfRingedSite B S hS 𝒳).J (fppfTopology B S hS 𝒳) :=
  AffineCategory.isDenseSubsite_inclusion_siteKind B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids .fppf

/-- **Stacks 0H0C on modules at module universe `u + 1`**: restriction of sheaves of modules
with sections in `Type (u + 1)` from the fppf site of `𝒳` to its affine subsite
`𝒳_{affine, fppf}`, as an equivalence. The structure rings are raised to `Type (u + 1)` on both
sides, which changes no presheaf of sections, so that the Comparison Lemma for sheaves of modules
(`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`) applies. -/
def affineFppfModuleRestrictionEquivalenceSucc :
    SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳) ≌
      SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O) :=
  (Stacks.Cohomology.DerivedLowerShriek.ULift.targetModulesEquivalence.{u + 1}
      (fppfTopology B S hS 𝒳) (ambientStructureSheaf B S hS 𝒳)).trans
    ((Stacks.DenseSubsiteModules.moduleRestrictionEquivalence (affineFppfRingedSite B S hS 𝒳).J
      (fppfTopology B S hS 𝒳) (AffineCategory.inclusion B S hS 𝒳.val.val.p)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.DerivedLowerShriek.ULift.liftedStructureSheaf.{u + 1}
          (fppfTopology B S hS 𝒳) (ambientStructureSheaf B S hS 𝒳)))).trans
      (Stacks.Cohomology.DerivedLowerShriek.ULift.targetModulesEquivalence.{u + 1}
        (affineFppfRingedSite B S hS 𝒳).J (affineFppfRingedSite B S hS 𝒳).O).symm)

/-- The functor of `affineFppfModuleRestrictionEquivalenceSucc`: restriction of sections along
the affine inclusion, the scalars being read through `ULift` and back. -/
abbrev affineFppfModuleRestrictionSucc :
    SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳) ⥤
      SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O) :=
  (affineFppfModuleRestrictionEquivalenceSucc B S hS 𝒳).functor

/-- The restriction functor `affineFppfModuleRestrictionSucc` is additive: as an equivalence it
preserves binary products. -/
instance additive_affineFppfModuleRestrictionSucc :
    (affineFppfModuleRestrictionSucc B S hS 𝒳).Additive :=
  Functor.additive_of_preserves_binary_products _

section AnyModels

variable [HasDerivedCategory.{t} (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))]
  [HasDerivedCategory.{t'} (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O))]

/-- **Stacks 0H0C on derived categories at module universe `u + 1`**: restriction to the affine
subsite, computed degreewise, `D(𝒳_{fppf}, 𝒪) ⥤ D(𝒳_{affine, fppf}, O)`, for any models of the two
derived categories. -/
abbrev affineFppfDerivedRestrictionSucc :
    DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ⥤
      DerivedCategory (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)) :=
  (affineFppfModuleRestrictionSucc B S hS 𝒳).mapDerivedCategory

/-- **Stacks 0H0C on derived categories at module universe `u + 1`**: degreewise restriction to
the affine subsite is an equivalence `D(𝒳_{fppf}, 𝒪) ≌ D(𝒳_{affine, fppf}, O)`. -/
instance isEquivalence_affineFppfDerivedRestrictionSucc :
    (affineFppfDerivedRestrictionSucc B S hS 𝒳).IsEquivalence :=
  Stacks.DerivedCategory.mapDerivedCategory_isEquivalence
    (affineFppfModuleRestrictionEquivalenceSucc B S hS 𝒳)

end AnyModels

/-! ### `QC(𝒳)` inside `D(𝒳_{fppf}, 𝒪)`

The first paragraph of the proof of **Stacks 0H16**: by **Stacks 0H0X**, `ε^*` identifies `QC(𝒳)`
with the full subcategory of `D(𝒳_{affine, fppf}, O)` of the objects `K` with `Rε_*K` in `QC(𝒳)`;
through the equivalence of ringed topoi of **Stacks 0H0C** this is a full subcategory `Q_𝒳` of
`D(𝒳_{fppf}, 𝒪)`. The derived category `D(𝒳_{affine, fppf}, O)` is the model at which Stacks 0H0X
is stated, `Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory`; the
model of `D(𝒳_{fppf}, 𝒪)` is arbitrary. -/

section QuasiCoherent

variable [HasDerivedCategory.{t} (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))]

/-- **`Q_𝒳 ⊂ D(𝒳_{fppf}, 𝒪)`** of the proof of Stacks 0H16: the objects `K` whose restriction `K'`
to the affine subsite satisfies `Rε_* K' ∈ QC(𝒳)`. -/
abbrev quasiCoherentDerivedFppfSucc :
    ObjectProperty
      (DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))) :=
  (Stacks.ModulesOnACategory.ChaoticComparison.pushforwardProperty.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)
    (IsQuasiCoherentObject.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p)).inverseImage
      (affineFppfDerivedRestrictionSucc B S hS 𝒳)

/-- **`QC(𝒳) ≌ Q_𝒳`**, the first paragraph of the proof of Stacks 0H16: Stacks 0H0X followed by
the equivalence of derived categories induced by the equivalence of ringed topoi of
Stacks 0H0C. -/
def quasiCoherentDerivedEquivalenceFppfSucc :
    quasiCoherentDerived.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p ≌
      (quasiCoherentDerivedFppfSucc B S hS 𝒳).FullSubcategory :=
  haveI : (Stacks.ModulesOnACategory.ChaoticComparison.pushforwardProperty.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)
      (IsQuasiCoherentObject.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p)).IsClosedUnderIsomorphisms :=
    ⟨fun e hX => (Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isClosedUnderIsomorphisms
      (affineBaseChangeData.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p)).of_iso
      ((Stacks.ModulesOnACategory.ChaoticComparison.derivedEpsilonPushforward.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)).mapIso e) hX⟩
  (affineFppfQuasiCoherentEquivalence.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids).trans
    ((affineFppfDerivedRestrictionSucc B S hS 𝒳).asEquivalence.congrFullSubcategory rfl).symm

end QuasiCoherent

end AlgebraicGeometry.Stack.FlatFppf

end
