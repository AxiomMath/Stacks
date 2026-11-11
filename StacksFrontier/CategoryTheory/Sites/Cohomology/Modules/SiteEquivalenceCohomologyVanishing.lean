module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsUnit
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedVanishingAlongEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.SiteEquivalenceCohomology

/-!
# Vanishing of cohomology of modules along an equivalence of sites

Let `e : C' ≌ C` be an equivalence of categories which is continuous in both directions for
topologies `J'` on `C'` and `J` on `C`, let `R` be a sheaf of rings on `(C, J)` and `R'` its
transport to `(C', J')`, with `Φ` the induced equivalence of module categories
(`Stacks.SheafOfModules.reindexEquivalence`). The file
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/SiteEquivalenceCohomology.lean` compares the
cohomology `Hⁿ(C, M)` and `Hⁿ(C', Φ M)` for modules whose sections live in a universe large
enough to contain the site. This file records the vanishing statement for modules in any
universe for which the module categories have injective resolutions: `Hⁿ(C, M) = 0` exactly when
`Hⁿ(C', Φ M) = 0`. It also shows that `Φ` carries the structure sheaf to the structure sheaf, so
that `Hⁿ(C, 𝒪) = 0` exactly when `Hⁿ(C', 𝒪') = 0`.

## Main definitions

* `Stacks.SheafOfModules.reindexEquivalenceUnitIso`: `Φ 𝒪 ≅ 𝒪'`.

## Main results

* `Stacks.Cohomology.SiteModules.isZero_rightDerived_reindex_iff`: `Hⁿ(C, M) = 0` exactly when
  `Hⁿ(C', Φ M) = 0`.
* `Stacks.Cohomology.SiteModules.isZero_rightDerived_unit_reindex_iff`: `Hⁿ(C, 𝒪) = 0` exactly
  when `Hⁿ(C', 𝒪') = 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe u v r w

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} (J' : GrothendieckTopology C')
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{r})

namespace Stacks.SheafOfModules

/-- **Transport along an equivalence of sites carries the structure sheaf to the structure
sheaf**: the transport of `𝒪` is `𝒪'`, sections and scalars being unchanged. -/
def reindexEquivalenceUnitIso :
    (reindexEquivalence.{r, r} (J' := J') e R).functor.obj (_root_.SheafOfModules.unit R) ≅
      _root_.SheafOfModules.unit (reindexRing J' e R) :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.pushforwardUnitIso (𝟙 _))

end Stacks.SheafOfModules

namespace Stacks.Cohomology.SiteModules

section

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The vanishing of cohomology of modules is invariant under an equivalence of sites.** For a
sheaf of `R`-modules `M` and its transport `Φ M` along `e`, `Hⁿ(C, M) = 0` exactly when
`Hⁿ(C', Φ M) = 0`. The universe of the sections of the modules is arbitrary, as long as the two
module categories have injective resolutions. -/
theorem isZero_rightDerived_reindex_iff
    [HasInjectiveResolutions (SheafOfModules.{w} R)]
    [HasInjectiveResolutions (SheafOfModules.{w} (Stacks.SheafOfModules.reindexRing J' e R))]
    (M : SheafOfModules.{w} R) (n : ℕ) :
    IsZero (((globalSectionsFunctor.{u, v, r, w} R).rightDerived n).obj M) ↔
      IsZero (((globalSectionsFunctor.{u, v, r, w}
        (Stacks.SheafOfModules.reindexRing J' e R)).rightDerived n).obj
          ((Stacks.SheafOfModules.reindexEquivalence.{r, w} (J' := J') e R).functor.obj M)) := by
  let Φ := (Stacks.SheafOfModules.reindexEquivalence.{r, w} (J' := J') e R).functor
  let res := ModuleCat.restrictScalars.{max u w} (reindexGlobalSectionRingHom J' e R)
  have : Φ.IsEquivalence := inferInstance
  have : Φ.Additive := Functor.additive_of_preserves_binary_products Φ
  have hres := ((Functor.exact_tfae res).out 2 4).mp fun S hS => by
    rwa [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  have : PreservesFiniteLimits res := hres.1
  have : PreservesFiniteColimits res := hres.2
  have : res.PreservesHomology := Functor.preservesHomologyOfExact res
  exact Functor.isZero_rightDerived_obj_iff_of_iso_comp Φ _ _ res
    (fun Y hY => @ModuleCat.isZero_of_subsingleton _ _ Y
      (ModuleCat.subsingleton_of_isZero (M := res.obj Y) hY))
    (reindexGlobalSectionsIso.{u, v, r, w} J' e R) M n

end

/-- **The vanishing of the cohomology of the structure sheaf is invariant under an equivalence of
sites**: `Hⁿ(C, 𝒪) = 0` exactly when `Hⁿ(C', 𝒪') = 0`, for `𝒪'` the transport of `𝒪`. -/
theorem isZero_rightDerived_unit_reindex_iff
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J' AddCommGrpCat.{r}] [J'.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasInjectiveResolutions (SheafOfModules.{r} R)]
    [HasInjectiveResolutions (SheafOfModules.{r} (Stacks.SheafOfModules.reindexRing J' e R))]
    (n : ℕ) :
    IsZero (((globalSectionsFunctor.{u, v, r, r} R).rightDerived n).obj
        (SheafOfModules.unit R)) ↔
      IsZero (((globalSectionsFunctor.{u, v, r, r}
        (Stacks.SheafOfModules.reindexRing J' e R)).rightDerived n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.reindexRing J' e R))) := by
  rw [isZero_rightDerived_reindex_iff.{u, v, r, r} J' e R]
  exact (((globalSectionsFunctor.{u, v, r, r}
    (Stacks.SheafOfModules.reindexRing J' e R)).rightDerived n).mapIso
      (Stacks.SheafOfModules.reindexEquivalenceUnitIso J' e R)).isZero_iff

end Stacks.Cohomology.SiteModules

end
