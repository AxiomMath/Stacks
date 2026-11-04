module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFlatBaseChangeSheafRule
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentClosureSucc
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleFlatPullbackExactSucc

/-!
# Hypothesis (1) of Stacks 076Z for `LQCoh^fbc`

**Stacks 0765** applies the criterion of **Stacks 076Z** to the rule `LQCoh^fbc` of the locally
quasi-coherent étale sheaves of modules with the flat base change property, at section universe
`u + 1`.  Hypothesis (1) of the criterion asks that `LQCoh^fbc` cut out a weak Serre subcategory
on every algebraic stack.  Its local quasi-coherence half is parts (2) and (3) of **Stacks 06WM**
(`AlgebraicGeometry.Stack.isWeakSerreClass_isLocallyQuasicoherent_succ_of_category`), and its flat
base change half is part (2) of **Stacks 0764**, whose zero, cokernel and extension clauses hold at
every section universe.  Its kernel clause needs `a_{small}^*` along a flat morphism to preserve
the kernel of a morphism between the restrictions of the two sheaves, which are quasi-coherent
because the sheaves are locally quasi-coherent; this holds since `a_{small}^*` along a flat
morphism is left exact at section universe `u + 1`.

## Main results

* `CategoryTheory.NatTrans.isIso_app_limit_of_preservesLimit`: a natural transformation between
  functors preserving the limit of one diagram is an isomorphism at that limit as soon as it is
  one at the vertices.
* `AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_kernel_of_preservesLimit`: the
  comparison map of Stacks 0761 at a kernel, from preservation of that one kernel.
* `isWeakSerreClass_locallyQuasicoherentFlatBaseChangeSheafRule_of_preservesKernel`: the weak
  Serre property of `LQCoh^fbc` on a category fibred in groupoids, from the preservation by
  `a_{small}^*` of the kernels of morphisms of quasi-coherent modules.
* `AlgebraicGeometry.Stack.preservesFiniteLimits_sheafifiedPullbackComparisonUnivLE_succ`:
  `a_{small}^*` along a flat morphism is left exact at section universe `u + 1`.
* `AlgebraicGeometry.Stack.isWeakSerre_locallyQuasicoherentFlatBaseChangeSheafRule`:
  **hypothesis (1) of Stacks 076Z for `LQCoh^fbc`.**

## References

* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_isGrothendieckAbelian
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.NatTrans

/-- A natural transformation `η : Φ ⟶ Ψ` between functors which preserve the limit of a diagram
`K` is an isomorphism at that limit as soon as it is an isomorphism at each vertex of `K`.  This
is `CategoryTheory.NatTrans.isIso_app_limit` with preservation asked of the one diagram only. -/
theorem isIso_app_limit_of_preservesLimit {C : Type*} [Category C] {D : Type*} [Category D]
    {J : Type*} [Category J] {Φ Ψ : C ⥤ D} (η : Φ ⟶ Ψ) (K : J ⥤ C) [HasLimit K]
    [PreservesLimit K Φ] [PreservesLimit K Ψ]
    (hη : ∀ i, IsIso (η.app (K.obj i))) :
    IsIso (η.app (limit K)) := by
  have hΨ : IsLimit (Ψ.mapCone (limit.cone K)) := isLimitOfPreserves Ψ (limit.isLimit K)
  have hwi : ∀ i : J, IsIso ((Functor.whiskerLeft K η).app i) := hη
  have hw : IsIso (Functor.whiskerLeft K η) := NatIso.isIso_of_isIso_app _
  let α : K ⋙ Φ ≅ K ⋙ Ψ := asIso (Functor.whiskerLeft K η)
  have hΦ' : IsLimit ((Cone.postcompose α.hom).obj (Φ.mapCone (limit.cone K))) :=
    (IsLimit.postcomposeHomEquiv α _).symm (isLimitOfPreserves Φ (limit.isLimit K))
  have heq : η.app (limit K) = (IsLimit.conePointUniqueUpToIso hΦ' hΨ).hom := by
    refine hΨ.hom_ext fun i => ?_
    rw [IsLimit.conePointUniqueUpToIso_hom_comp]
    exact (η.naturality (limit.π K i)).symm
  rw [heq]
  infer_instance

end CategoryTheory.NatTrans

universe u v w m t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The comparison map at a kernel, from preservation of that one kernel.**  The comparison map
`c_φ^{sh}` below an arrow `φ : x ⟶ y` of `𝒳` is an isomorphism at the kernel of `α : 𝒢 ⟶ 𝒢'`
as soon as it is one at `𝒢` and at `𝒢'`, provided `a_{small}^*` preserves the kernel of the
restriction of `α` to the small étale site of the scheme below `y`. -/
theorem isIso_restrictSheafPullbackComparison_kernel_of_preservesLimit [UnivLE.{u, m}]
    {x y : 𝒳} (φ : x ⟶ y)
    {F G : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} (α : F ⟶ G)
    (hpres : PreservesLimit
      (parallelPair ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp y).map α) 0)
      (sheafifiedPullbackComparisonUnivLE.{u, v, w, m} B E h S hS p hp
        (etaleTopology B) (etaleTopology_le_topology B) φ))
    (hF : IsIso (restrictSheafPullbackComparison B E h S hS p hp φ F))
    (hG : IsIso (restrictSheafPullbackComparison B E h S hS p hp φ G)) :
    IsIso (restrictSheafPullbackComparison B E h S hS p hp φ (kernel α)) := by
  let r := restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp y
  let a := sheafifiedPullbackComparisonUnivLE.{u, v, w, m} B E h S hS p hp
    (etaleTopology B) (etaleTopology_le_topology B) φ
  have : r.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have : PreservesLimit (parallelPair α 0 ⋙ r) a :=
    preservesLimit_of_iso_diagram a
      (parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp) :
        parallelPair (r.map α) 0 ≅ parallelPair α 0 ⋙ r)
  have : PreservesLimit (parallelPair α 0) (r ⋙ a) := comp_preservesLimit r a
  exact NatTrans.isIso_app_limit_of_preservesLimit
    (restrictSheafPullbackComparisonNatTrans B E h S hS p hp φ)
    (parallelPair α 0) (by rintro (_ | _) <;> assumption)

section Succ

variable {𝒴 : Type (u + 1)} [Category.{u} 𝒴] (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hq : q.IsFiberedInGroupoids)

/-- **The rule `LQCoh^fbc` cuts out a weak Serre subcategory on a category fibred in groupoids**,
at section universe `u + 1`, as soon as `a_{small}^*` along every arrow over a flat morphism
preserves the kernels of morphisms of quasi-coherent modules on the small étale site of its
target (`hker`), which always holds by
`AlgebraicGeometry.Stack.preservesFiniteLimits_sheafifiedPullbackComparisonUnivLE_succ`. -/
theorem isWeakSerreClass_locallyQuasicoherentFlatBaseChangeSheafRule_of_preservesKernel
    (hker : ∀ {x y : 𝒴} (φ : x ⟶ y), Flat (B.inclusion.map (q.map φ).left) →
      ∀ {M N : SheafOfModules.{u + 1} (SmallEtale.structureSheaf E (q.obj y).left.1
          (contains_base B E h S hS q y))} (f : M ⟶ N),
        M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
          PreservesLimit (parallelPair f 0)
            (sheafifiedPullbackComparisonUnivLE.{u, u + 1, u, u + 1} B E h S hS q hq
              (etaleTopology B) (etaleTopology_le_topology B) φ)) :
    letI := hasSheafify_associatedTopology_of_category_succ B S hS q
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS q
    ObjectProperty.IsWeakSerreClass
      (C := SheafOfModules.{u + 1} (ringStructureSheafCore B S hS q hq (etaleTopology B)
        (etaleTopology_le_topology B)))
      (fun F => locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS q hq F.val) := by
  let := hasSheafify_associatedTopology_of_category_succ B S hS q
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS q
  let P : ObjectProperty (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS q hq
      (etaleTopology B) (etaleTopology_le_topology B))) :=
    fun F => locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS q hq F.val
  have hmk : ∀ F, IsLocallyQuasicoherent B E h S hS q hq F.val →
      HasFlatBaseChangePropertySheafUnivLE.{u, u + 1, u, u + 1} B E h S hS q hq F → P F :=
    fun F h₁ h₂ => ⟨h₁, F.isSheaf, fun _ => h₂⟩
  have hfbc : ∀ F, P F →
      HasFlatBaseChangePropertySheafUnivLE.{u, u + 1, u, u + 1} B E h S hS q hq F :=
    fun F hF => hF.2.2 F.isSheaf
  have hL := isWeakSerreClass_isLocallyQuasicoherent_succ_of_category B E h S hS q hq
  have : P.ContainsZero := by
    obtain ⟨Z, hZ, hLZ⟩ := (containsZero_isLocallyQuasicoherent_succ_of_category B E h S hS q
        hq).exists_zero
    exact ⟨Z, hZ, hmk Z hLZ
      (hasFlatBaseChangePropertySheaf_initial.{u, u + 1, u, u + 1} B E h S hS q hq hZ.isInitial)⟩
  have hiso : ∀ {F G}, (F ≅ G) → P F → P G := fun {F G} e hF => hmk G
    ((isLocallyQuasicoherent.{u, u + 1, u, u + 1} B E h S hS q hq).prop_of_iso e hF.1)
    (hasFlatBaseChangePropertySheafUnivLE_of_iso.{u, u + 1, u, u + 1} B E h S hS q hq e
      (hfbc F hF))
  have : P.IsClosedUnderIsomorphisms := ⟨hiso⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, hk, hF, hG⟩
    refine hiso (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hk) (hmk _
      ((isLocallyQuasicoherent.{u, u + 1, u, u + 1} B E h S hS q hq).prop_kernel f hF.1 hG.1)
      fun φ hflat => ?_)
    exact isIso_restrictSheafPullbackComparison_kernel_of_preservesLimit B E h S hS q hq φ f
      (hker φ hflat _ ((isLocallyQuasicoherent_iff B E h S hS q hq _).1 hF.1 _)
        ((isLocallyQuasicoherent_iff B E h S hS q hq _).1 hG.1 _))
      (hfbc _ hF φ hflat) (hfbc _ hG φ hflat)⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hk, hF, hG⟩
    exact hiso (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hk) (hmk _
      ((isLocallyQuasicoherent.{u, u + 1, u, u + 1} B E h S hS q hq).prop_cokernel f hF.1 hG.1)
      (hasFlatBaseChangePropertySheaf_cokernel.{u, u + 1, u, u + 1} B E h S hS q hq f
        (hfbc _ hF) (hfbc _ hG)))⟩
  have : P.IsClosedUnderExtensions := ⟨fun hT h₁ h₃ => hmk _
    (isLocallyQuasicoherent_X₂_of_shortExact_succ B E h S hS q hq hT h₁.1 h₃.1)
    (hasFlatBaseChangePropertySheaf_of_shortExact.{u, u + 1, u, u + 1} B E h S hS q hq hT
      (hfbc _ h₁) (hfbc _ h₃))⟩
  exact {}

/-- **`a_{small}^*` along a flat morphism is left exact, at section universe `u + 1`.** -/
theorem preservesFiniteLimits_sheafifiedPullbackComparisonUnivLE_succ {𝒳 : Type v}
    [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) {x y : 𝒳} (φ : x ⟶ y)
    (hflat : Flat (B.inclusion.map (p.map φ).left)) :
    PreservesFiniteLimits (sheafifiedPullbackComparisonUnivLE.{u, v, w, u + 1} B E h S hS p hp τ hτ
      φ) :=
  have := SmallEtale.preservesFiniteLimits_sheafificationPullback_succ E
    (smallEtaleBaseMorphism B E h S hS p φ) hflat
  preservesFiniteLimits_of_natIso
    (pullbackConstructionComparisonIsoUnivLE.{u, v, w, u + 1} B E h S hS p hp τ hτ φ)

/-- **The rule `LQCoh^fbc` cuts out a weak Serre subcategory on a category fibred in groupoids**,
at section universe `u + 1`. -/
theorem isWeakSerreClass_locallyQuasicoherentFlatBaseChangeSheafRule :
    letI := hasSheafify_associatedTopology_of_category_succ B S hS q
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS q
    ObjectProperty.IsWeakSerreClass
      (C := SheafOfModules.{u + 1} (ringStructureSheafCore B S hS q hq (etaleTopology B)
        (etaleTopology_le_topology B)))
      (fun F => locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS q hq F.val) :=
  isWeakSerreClass_locallyQuasicoherentFlatBaseChangeSheafRule_of_preservesKernel B E h S hS q hq
    fun φ hflat _ _ _ =>
      have := preservesFiniteLimits_sheafifiedPullbackComparisonUnivLE_succ B E h S hS q hq
        (etaleTopology B) (etaleTopology_le_topology B) φ hflat
      inferInstance

end Succ

/-- **Hypothesis (1) of Stacks 076Z for the rule `LQCoh^fbc`.**  On every algebraic stack, the
locally quasi-coherent étale sheaves of modules with the flat base change property, with sections
in `Type (u + 1)`, form a weak Serre subcategory. -/
theorem isWeakSerre_locallyQuasicoherentFlatBaseChangeSheafRule :
    StackEtaleModuleRule.IsWeakSerre.{u, t} B S hS
      (locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS) :=
  fun 𝒳 => isWeakSerreClass_locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids

end AlgebraicGeometry.Stack

end
