module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDerivedSectionsAffineCase
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDerivedSectionsSheafFlatBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Composition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalMorphismOfSitesEquivalence

/-!
# Stacks 0H15 over an affine scheme

Let `𝒳` be an algebraic stack, `𝒳_{affine}` its associated affine site (Stacks 0H09) with the
chaotic topology, `ε : 𝒳_{affine, fppf} ⟶ 𝒳_{affine}` the comparison morphism and
`Φ : D(𝒳_{fppf}, 𝒪) ≌ D(𝒳_{affine, fppf}, O)` the restriction of Stacks 0H0C, all at module
universe `u + 1`. This file proves the last paragraph of the proof of **Stacks 0H15**: for
`𝒳 = (Sch/X)_{fppf}` with `X` affine and `H ∈ D_QCoh(𝒪_{𝒳_{flat, fppf}})`, the object `Lg_! H`
has the base change property `RΓ(x', Lg_! H) ⊗^L_{𝒪(x')} 𝒪(x) ≅ RΓ(x, Lg_! H)` along every
morphism `x ⟶ x'` of `𝒳_{affine}`.

## Implementation notes

Stacks 0H15 represents `RΓ(X, Lg_! H)` by a K-flat complex `M^•` of `R`-modules, `R = Γ(X, 𝒪_X)`,
and compares `Lg_! H` with the complex `M^•_{fppf} : U ↦ Γ(U, M^• ⊗_R 𝒪_U)`. Here `M^•_{fppf}` is
produced from the derived category of `R`-modules by the chain of functors

`D(R) ⟶ QC(𝒳) ⟶ D(𝒳_{affine, fppf}, O) ⟶ D(𝒳_{fppf}, 𝒪)`

made of the derived pullback `Lf^*` along the terminal object `X` of the chaotic site
`𝒳_{affine}` (Stacks 0H0R, which also says that `Lf^*` lands in `QC(𝒳)` with invertible unit),
`ε^*` (whose unit is invertible on `QC(𝒳)` by Stacks 0H0X) and `Φ⁻¹`. This composite is left
adjoint to `K ↦ RΓ(X, Rε_* Φ K)`, which is `RΓ(X, -)`
(`AlgebraicGeometry.Stack.FlatFppf.derivedSectionsChaoticIso`: both are right derived functors
of sections over `X`, the restriction to the affine subsite and `Rε_*` being computed on
K-injective complexes). For `K = Lg_! H` and `N` the image of `RΓ(X, K)`, the counit `φ : N ⟶ K`
is invertible on `RΓ(X, -)` by a triangle identity, `N` has the base change property (its
image under `Rε_* Φ` is quasi-coherent,
`quasiCoherentDerivedFppfSucc_iff_hasAffineDerivedSectionsBaseChange`), hence lies in
`D_{LQCoh^fbc}(𝒪_𝒳)`, and it is left orthogonal to `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` by
adjunction, `RΓ(X, P)` vanishing for parasitic `P` since `X` is flat. The formal half of the last
paragraph of the proof (`hasAffineDerivedSectionsBaseChange_of_isIso_derivedSections_of_flat_hom`)
then carries the base change property from `N` to `K`.

## Main results

* `derivedSectionsChaoticIso`: for an object `x` of `𝒳_{affine}`,
  `RΓ(x, K) ≅ RΓ(x, Rε_* Φ K)`, naturally in `K`.
* `hasAffineDerivedSectionsBaseChange_of_isTerminal`: an object of `𝒜` has the base change
  property as soon as `𝒳_{affine}` has a terminal object `ξ` which is flat and receives a flat
  arrow from every flat affine object.
* `hasAffineDerivedSectionsBaseChange_derivedModuleLowerShriekSucc_schemeStack`: **the case of an
  affine scheme** of Stacks 0H15.

## References

* [Stacks Project, Tag 0H15](https://stacks.math.columbia.edu/tag/0H15)
* [Stacks Project, Tag 0H0R](https://stacks.math.columbia.edu/tag/0H0R)
* [Stacks Project, Tag 0H0X](https://stacks.math.columbia.edu/tag/0H0X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.HypercohomologyEdge
open Stacks.ModulesOnACategory.ChaoticComparison
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe u w

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasSheafify_fppfTopology_largeSections
  wEqualsLocallyBijective_fppfTopology_largeSections
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
attribute [local instance] isGrothendieckAbelian_ambientModulesSucc
attribute [-instance] Stacks.ModulesOnACategory.QuasiCoherentEquivalence.rsPreservesFiniteLimits
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.rsPreservesFiniteColimits
attribute [local instance] restrictScalarsSucc_preservesFiniteLimits
  restrictScalarsSucc_preservesFiniteColimits

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The derived category of sheaves of modules on the affine subsite `𝒳_{affine, fppf}`, at module
universe `u + 1`, in the small-Hom model at which `Q_𝒳` is defined. -/
local instance hasDerivedCategory_affineFppfModulesSucc :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)) :=
  sheafOfModules_hasDerivedCategory.{u + 1} _

/-- Sheaves of modules with sections in `Type (u + 1)` on the affine subsite form a Grothendieck
abelian category, in the module universe. -/
local instance isGrothendieckAbelian_affineFppfModulesSucc :
    IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)) :=
  SheafOfModules.isGrothendieckAbelian_of_univLE.{u + 1} _

/-- **Derived sections over an object of `𝒳_{affine}` are read on the chaotic site**:
`RΓ(x, K) ≅ RΓ(x, Rε_*(Φ K))`, naturally in `K ∈ D(𝒳_{fppf}, 𝒪)`, where `Φ` is the restriction to
the affine subsite (Stacks 0H0C) and `Rε_*` the derived pushforward to the chaotic site
`𝒳_{affine}`.

Both functors are right derived functors of `K ↦ Γ(x, K)` on the homotopy category: the left one
by definition; for the right one, `Γ(x, -)` is `ev_x ∘ ε_* ∘ Φ` termwise
(`affineFppfModuleRestrictionSuccEvaluationIso`), evaluation on the chaotic site is exact, and the
unit of `Rε_*` is invertible at `Φ I` for a K-injective complex `I`, `Φ` being an exact
equivalence. -/
def derivedSectionsChaoticIso (x : AffineCategory B S hS 𝒳.val.val.p) :
    derivedSections.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳) x.obj ≅
      (affineFppfDerivedRestrictionSucc B S hS 𝒳 ⋙ derivedEpsilonPushforward.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)) ⋙
        RGamma.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O).obj
            (op x) := by
  let O := ambientRingStructureSheaf B S hS 𝒳
  let R' := Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O
  let Φ₀ := affineFppfModuleRestrictionSucc B S hS 𝒳
  let ε := epsilonPushforward.{u + 1} R'
  let ev := PresheafOfModules.evaluation.{u + 1} R'.obj (op x)
  let e₀ : Φ₀ ⋙ ε ⋙ ev ≅ SheafOfModules.evaluation.{u + 1} O (op x.obj) :=
    affineFppfModuleRestrictionSuccEvaluationIso B S hS 𝒳 x
  have hEv : (SheafOfModules.evaluation.{u + 1} O (op x.obj)).Additive :=
    Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.evaluation_additive O (op x.obj)
  have hΞ : (Φ₀ ⋙ ε ⋙ ev).Additive := inferInstance
  let d₁ : Φ₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (ε ⋙ ev).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (Φ₀ ⋙ ε ⋙ ev).mapHomotopyCategory (ComplexShape.up ℤ) :=
    Functor.mapHomotopyCategoryCompIso (Iso.refl _) _
  let d₂ : ε.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ ev.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (ε ⋙ ev).mapHomotopyCategory (ComplexShape.up ℤ) :=
    Functor.mapHomotopyCategoryCompIso (Iso.refl _) _
  let γ₂ : (ε ⋙ ev).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedEpsilonPushforward.{u + 1} R' ⋙ ev.mapDerivedCategory) :=
    Functor.whiskerRight d₂.inv DerivedCategory.Qh ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (ε.mapHomotopyCategory (ComplexShape.up ℤ))
        ev.mapDerivedCategoryFactorsh.inv ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (derivedEpsilonPushforwardUnit.{u + 1} R') ev.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom
  let γ : (Φ₀ ⋙ ε ⋙ ev).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ ((affineFppfDerivedRestrictionSucc B S hS 𝒳 ⋙
        derivedEpsilonPushforward.{u + 1} R') ⋙ RGamma.{u + 1} R'.obj (op x)) :=
    Functor.whiskerRight d₁.inv DerivedCategory.Qh ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Φ₀.mapHomotopyCategory (ComplexShape.up ℤ)) γ₂ ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight Φ₀.mapDerivedCategoryFactorsh.inv
        (derivedEpsilonPushforward.{u + 1} R' ⋙ ev.mapDerivedCategory) ≫
      (Functor.associator _ _ _).hom
  let τ : homotopySections.{_, _, _, u + 1} O x.obj ≅
      (Φ₀ ⋙ ε ⋙ ev).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
    Functor.isoWhiskerRight (@Stacks.Homology.mapHomotopyCategoryIso
      (SheafOfModules.{u + 1} O) (ModuleCat.{u + 1} (O.obj.obj (op x.obj))) _ _ _ _
      (SheafOfModules.evaluation.{u + 1} O (op x.obj)) (Φ₀ ⋙ ε ⋙ ev) hEv hΞ e₀.symm
      (ComplexShape.up ℤ)) DerivedCategory.Qh
  let G : DerivedCategory (SheafOfModules.{u + 1} O) ⥤
      DerivedCategory (ModuleCat.{u + 1} (O.obj.obj (op x.obj))) :=
    (affineFppfDerivedRestrictionSucc B S hS 𝒳 ⋙ derivedEpsilonPushforward.{u + 1} R') ⋙
      RGamma.{u + 1} R'.obj (op x)
  let β : homotopySections.{_, _, _, u + 1} O x.obj ⟶ DerivedCategory.Qh ⋙ G := τ.hom ≫ γ
  have hβ : G.IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1} O) (ComplexShape.up ℤ)) := by
    refine Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective
      _ DerivedCategory.Qh G β fun I hI => ?_
    haveI := hI
    haveI : CochainComplex.IsKInjective ((Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
      Stacks.Injectives.isKInjective_mapHomologicalComplex_of_isEquivalence _ I
    have h3 : IsIso ((derivedEpsilonPushforwardUnit.{u + 1} R').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
      Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ _
    have h3' : IsIso ((derivedEpsilonPushforwardUnit.{u + 1} R').app
        ((Φ₀.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := h3
    have hγI : IsIso (γ.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
      simp only [γ, γ₂, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
        Category.comp_id]
      infer_instance
    exact IsIso.comp_isIso' inferInstance hγI
  haveI := (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (derivedSections.{_, _, _, u + 1, u + 1} O x.obj)
    ((homotopySections.{_, _, _, u + 1} O x.obj).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1} O) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{u + 1} O) (ComplexShape.up ℤ)) G β).1 hβ
  exact asIso ((derivedSections.{_, _, _, u + 1, u + 1} O x.obj).rightDerivedDesc
    ((homotopySections.{_, _, _, u + 1} O x.obj).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1} O) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{u + 1} O) (ComplexShape.up ℤ)) G β)

/-- **The base change property of Stacks 0H15 over a stack whose affine site has a flat terminal
object.** Let `ξ` be a terminal object of `𝒳_{affine}` which is a flat object of `𝒳` and receives a
flat arrow from every flat affine object (for `(Sch/X)_{fppf}` with `X` affine, `ξ = X`). Then
every object `K` of `D_{LQCoh^fbc}(𝒪_𝒳)` left orthogonal to `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` has
the base change property.

With `Lf^*` the derived pullback along `ξ` on the chaotic site, `ε^*` and `Φ⁻¹`, the composite
`Ψ = Φ⁻¹ ε^* Lf^*` is left adjoint to `RΓ(ξ, Rε_* Φ -) ≅ RΓ(ξ, -)` with invertible unit
(Stacks 0H0R and 0H0X). For `N = Ψ(RΓ(ξ, K))` the counit `N ⟶ K` is invertible on `RΓ(ξ, -)`;
`Rε_* Φ N ≅ Lf^* RΓ(ξ, K)` is quasi-coherent, so `N` has the base change property and lies in
`D_{LQCoh^fbc}`; and `Hom(N, P) = Hom(RΓ(ξ, K), RΓ(ξ, P)) = 0` for `P` parasitic in
`D_{LQCoh^fbc}`, `ξ` being flat and affine. The property passes from `N` to `K` by
`hasAffineDerivedSectionsBaseChange_of_isIso_derivedSections_of_flat_hom`. -/
theorem hasAffineDerivedSectionsBaseChange_of_isTerminal
    {K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))}
    (hK : DerivedCategory.KernelColocalization.interLeftOrthogonal (parasiticModulesSucc B S hS 𝒳)
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K)
    (ξ : AffineCategory B S hS 𝒳.val.val.p) (hξ : IsTerminal ξ)
    (hξf : flatObject B S hS 𝒳.val ξ.obj)
    (hmap : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
      ∃ a : x ⟶ ξ.obj, Flat (B.inclusion.map (𝒳.val.val.p.map a).left)) :
    HasAffineDerivedSectionsBaseChange B S hS 𝒳 K := by
  let O := ambientRingStructureSheaf B S hS 𝒳
  let R' := Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O
  have hO : ∀ (U : (AffineCategory B S hS 𝒳.val.val.p)ᵒᵖ) (a b : R'.obj.obj U), a * b = b * a :=
    affineStructurePresheaf_comm B S hS 𝒳.val.val.p
  let mos := Stacks.ModulesOnACategory.TerminalMorphismOfSites.morphismOfSites.{u + 1} R'.obj hO hξ
  have hme := main_equivalence.{u + 1} hξ hO
  let Φ := affineFppfDerivedRestrictionSucc B S hS 𝒳
  let adjF : Φ.asEquivalence.inverse ⊣ Φ := Φ.asEquivalence.symm.toAdjunction
  let adjE := derivedEpsilonAdjunction.{u + 1} R'
  let adjT := mos.adj.comp (adjE.comp adjF)
  let G := (Φ ⋙ derivedEpsilonPushforward.{u + 1} R') ⋙ RGamma.{u + 1} R'.obj (op ξ)
  let c := derivedSectionsChaoticIso B S hS 𝒳 ξ
  let M := G.obj K
  let N := (mos.Lpullback ⋙
    (Stacks.ModulesOnACategory.ChaoticComparison.epsilonPullback.{u + 1} R').mapDerivedCategory ⋙
    Φ.asEquivalence.inverse).obj M
  let φ : N ⟶ K := adjT.counit.app K
  have hu : ∀ M' : DerivedCategory (ModuleCat.{u + 1} (R'.obj.obj (op ξ))),
      IsIso ((adjE.comp adjF).unit.app (mos.Lpullback.obj M')) := fun M' => by
    have := isIso_unit_affine B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf
      (mos.Lpullback.obj M') (hme.1 M')
    rw [Adjunction.comp_unit_app]
    infer_instance
  have hunit : ∀ M' : DerivedCategory (ModuleCat.{u + 1} (R'.obj.obj (op ξ))),
      IsIso (adjT.unit.app M') := fun M' => by
    have := hme.2.1 M'
    have := hu M'
    rw [Adjunction.comp_unit_app]
    infer_instance
  have hGφ : IsIso (G.map φ) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ (adjT.unit.app (G.obj K)) _ (hunit _) (by
      rw [adjT.right_triangle_components K]
      exact IsIso.id _)
  have hbc : HasAffineDerivedSectionsBaseChange B S hS 𝒳 N := by
    refine (quasiCoherentDerivedFppfSucc_iff_hasAffineDerivedSectionsBaseChange B S hS 𝒳 N).1 ?_
    have hq : IsQuasiCoherentObject.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p
        ((((Stacks.ModulesOnACategory.ChaoticComparison.epsilonPullback.{u + 1}
          R').mapDerivedCategory ⋙ Φ.asEquivalence.inverse) ⋙
            Φ ⋙ derivedEpsilonPushforward.{u + 1} R').obj (mos.Lpullback.obj M)) :=
      (isQC_isClosedUnderIsomorphisms
        (affineBaseChangeData.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p)).of_iso
        (@asIso _ _ _ _ _ (hu M)) (hme.1 M)
    exact @hq
  have hN : DerivedCategory.KernelColocalization.interLeftOrthogonal
      (parasiticModulesSucc B S hS 𝒳) (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) N := by
    refine ⟨fun P f hP => ?_,
      derivedCategoryB_sheafFlatBaseChangeModulesSucc_of_hasAffineDerivedSectionsBaseChange
        B S hS 𝒳 E h N hbc⟩
    have hz : IsZero ((derivedSections.{_, _, _, u + 1, u + 1} O ξ.obj).obj P) := by
      refine (DerivedCategory.isZero_iff_forall_isZero_homology _).2 fun q => ?_
      have hE := isIso_hypercohomologyEdge_app_of_sheafFlatBaseChange B S hS 𝒳 E h P
        (fun n => (hP n).2) ξ.obj ξ.property q
      exact (@ModuleCat.isZero_of_subsingleton _ _ _ ((hP q).1 ξ.obj hξf)).of_iso
        (@asIso _ _ _ _ ((hypercohomologyEdge.{_, _, _, u + 1, u + 1} O ξ.obj q).app P) hE)
    exact (adjT.homEquiv M P).injective ((hz.of_iso (c.app P).symm).eq_of_tgt _ _)
  exact hasAffineDerivedSectionsBaseChange_of_isIso_derivedSections_of_flat_hom B E h S hS 𝒳 φ
    hN hK hbc ξ.obj ξ.property hmap ((NatIso.isIso_map_iff c φ).2 hGφ)

include E h in
/-- **Stacks 0H15 for the stack of an affine scheme.** Let `X` be an affine scheme in the big fppf
site and `H` an object of `D_QCoh(𝒪_{X_{flat, fppf}})` (module universe `u + 1`). Then `Lg_! H`
has the base change property: `RΓ(x', Lg_! H) ⊗^L_{𝒪(x')} 𝒪(x) ⟶ RΓ(x, Lg_! H)` is a
quasi-isomorphism for every morphism `x ⟶ x'` of `(Sch/X)_{affine}`.

The object `𝟙 X` is terminal and flat, every object of `(Sch/X)_{flat}` is a flat arrow to it, and
`Lg_! H` lies in `D_{LQCoh^fbc}(𝒪_X)` (Stacks 07B9 (2)(c)) and is left orthogonal to
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_X)` (Stacks 07BA), so
`hasAffineDerivedSectionsBaseChange_of_isTerminal` applies. -/
theorem hasAffineDerivedSectionsBaseChange_derivedModuleLowerShriekSucc_schemeStack
    (X : BigFppfOver B S hS) (hX : IsAffine ((BigFppfOver.toScheme B S hS).obj X))
    (H : DerivedCategory (SheafOfModules.{u + 1}
      (subsiteRingStructureSheaf B S hS (schemeStack.{u, w} B S hS X))))
    (hH : DerivedCategoryB.derivedCategoryB
      (flatQuasicoherentModulesSucc B S hS (schemeStack.{u, w} B S hS X)) H) :
    HasAffineDerivedSectionsBaseChange B S hS (schemeStack.{u, w} B S hS X)
      ((derivedModuleLowerShriekSucc B S hS (schemeStack.{u, w} B S hS X)).obj H) := by
  let 𝒴 := schemeStack.{u, w} B S hS X
  let ξ : AffineCategory B S hS 𝒴.val.val.p := ⟨Over.mk.{u, u + 1} (𝟙 X), hX⟩
  have hξ : IsTerminal ξ :=
    IsTerminal.ofUniqueHom (fun Y => ObjectProperty.homMk ((Over.mkIdTerminal (X := X)).from Y.obj))
      (fun Y f => ObjectProperty.hom_ext _ ((Over.mkIdTerminal (X := X)).hom_ext _ _))
  have hξf : flatObject B S hS 𝒴.val ξ.obj :=
    (flatObject_schemeStack_iff.{u, w} B S hS X ξ.obj).2 (by
      show Flat ((BigFppfOver.toScheme B S hS).map (𝟙 X))
      have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (𝟙 X)) :=
        inferInstance
      infer_instance)
  exact hasAffineDerivedSectionsBaseChange_of_isTerminal B E h S hS 𝒴
    ⟨leftOrthogonal_derivedModuleLowerShriekSucc B E h S hS 𝒴 H,
      derivedCategoryB_derivedModuleLowerShriekSucc B E h S hS 𝒴 H hH⟩
    ξ hξ hξf (fun x hx _ => exists_flat_hom_schemeStack_id.{u, w} B S hS X x hx)

end AlgebraicGeometry.Stack.FlatFppf

end
