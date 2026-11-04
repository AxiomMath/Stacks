module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineVanishingLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfWeakSerre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentEtaleSheafClause
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakInverseImageOfEpi

/-!
# Stacks 0771 (2) for the fppf modules at module universe `u + 1`

Let `𝒳` be a category fibred in groupoids over `(Sch/S)_{fppf}` whose objects lie in
`Type (u + 1)` and whose morphisms lie in `Type u`, the seating of an algebraic stack.  This
file proves that the faithful class `LQCoh^fbc(𝒪_𝒳)` — locally quasi-coherent (Stacks 06WJ) with
the flat base change property of Stacks 0762 read with the pullback of sheaves — is a **weak
Serre subcategory of the sheaves of modules on the fppf site at module universe `u + 1`**.

## The argument

The class is the inverse image, along the left exact comparison `ε` from fppf to étale sheaves
of modules, of the étale class, which is weak Serre by
`AlgebraicGeometry.Stack.isWeakSerreClass_isLocallyQuasicoherentWithSheafFlatBaseChange_succ`.
`CategoryTheory.ObjectProperty.isWeakSerreClass_inverseImage_of_epi` reduces the claim to the
extension step of the source: for a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of fppf modules
with `ℱ₁` in the class, `ε(ℱ₂ ⟶ ℱ₃)` is an epimorphism of étale sheaves.  Over an object `x`
lying over an affine scheme, `ℱ₂(x) ⟶ ℱ₃(x)` is surjective by the long exact cohomology sequence
of the underlying abelian sheaves, `H^1(x, ℱ₁) = 0` being
`AlgebraicGeometry.Stack.isZero_rightDerived_sheafSections_of_sheafFlatBaseChange_succ`; such
objects cover every object for the étale topology, so `ε(ℱ₂ ⟶ ℱ₃)` is locally surjective.

## Main results

* `Stack.surjective_sheafSections_map_of_sheafFlatBaseChange_succ`.
* `Stack.epi_comparisonPushforward_map_of_sheafFlatBaseChange_succ`.
* `Stack.isWeakSerreClass_isLocallyQuasicoherentWithSheafFlatBaseChange_fppf_succ`
* `Stack.isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppfModulesSucc`:
  **the instance for an algebraic stack**, on the spelling
  `SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p _ B.topology le_rfl)` of
  `Mod(𝒪_𝒳)` (the `ambientRingStructureSheaf` of the flat-fppf development).

No `@[stacks]` attribute is claimed: Stacks 0771 (2) is registered at module universe `u`.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

-- the abelian structure of the library on sheaves of modules whose sections contain the site
-- would be met first by instance search here, with a universe constraint it cannot solve
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

section Succ

variable {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

attribute [local instance] isGrothendieckAbelian_fppfAbelianSheavesSucc

/-- **Sections over an object lying over an affine scheme of a short exact sequence of fppf
modules whose kernel is in `LQCoh^fbc`**, at module universe `u + 1`: `ℱ₂(x) ⟶ ℱ₃(x)` is
surjective, by the long exact cohomology sequence and `H^1(x, ℱ₁) = 0`. -/
theorem surjective_sheafSections_map_of_sheafFlatBaseChange_succ
    {T : ShortComplex (SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS p hp B.topology le_rfl))}
    (hT : T.ShortExact)
    (h₁ : IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u + 1}
      B E h S hS p hp T.X₁.val)
    (x : 𝒳) (hx : IsAffine ((toScheme B S hS p).obj x)) :
    Function.Surjective ((((sheafSections (associatedTopology B S hS p B.topology)
      AddCommGrpCat.{u + 1}).obj (op x)).map ((SheafOfModules.toSheaf.{u + 1} _).map T.g))) := by
  let A := SheafOfModules.toSheaf.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl)
  have hT' : (T.map A).ShortExact := by
    have := hT.mono_f
    have := hT.epi_g
    have : Epi (T.map A).g := A.map_epi T.g
    have hk : IsLimit (KernelFork.ofι (T.map A).f (T.map A).zero) :=
      (KernelFork.isLimitMapConeEquiv _ A) (isLimitOfPreserves A hT.fIsKernel)
    have : Mono (T.map A).f := Fork.IsLimit.mono hk
    exact ⟨ShortComplex.exact_of_f_is_kernel _ hk⟩
  let ev := (sheafSections (associatedTopology B S hS p B.topology) AddCommGrpCat.{u + 1}).obj
    (op x)
  let : HasDerivedCategory
      (Sheaf (associatedTopology B S hS p B.topology) AddCommGrpCat.{u + 1}) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory AddCommGrpCat.{u + 1} := HasDerivedCategory.standard _
  have hvan := isZero_rightDerived_sheafSections_of_sheafFlatBaseChange_succ B E h S hS p hp
    T.X₁ h₁ x hx 1 Nat.one_pos
  have : Epi (ev.map (T.map A).g) := by
    rw [show ev.map (T.map A).g = ev.rightDerivedZeroIsoSelf.inv.app _ ≫
        (ev.rightDerived 0).map (T.map A).g ≫ ev.rightDerivedZeroIsoSelf.hom.app _ by
      rw [NatTrans.naturality, Iso.inv_hom_id_app_assoc]]
    exact epi_comp' (IsIso.epi_of_iso _) (epi_comp'
      (Stacks.TopDirectImageRightExact.epi_rightDerived_map_g ev hT' 0 hvan) (IsIso.epi_of_iso _))
  exact (AddCommGrpCat.epi_iff_surjective _).1 this

/-- **The extension step of Stacks 0771 (2) at module universe `u + 1`**: for a short exact
sequence of fppf modules whose kernel is in `LQCoh^fbc`, the quotient map is an epimorphism of
étale sheaves of modules. -/
theorem epi_comparisonPushforward_map_of_sheafFlatBaseChange_succ
    {T : ShortComplex (SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS p hp B.topology le_rfl))}
    (hT : T.ShortExact)
    (h₁ : IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u + 1}
      B E h S hS p hp T.X₁.val) :
    Epi ((Stacks.SheafOfModules.comparisonPushforward.{u + 1, u, u, u + 1}
      (associatedTopology_mono B S hS p (etaleTopology_le_topology B))
      (ringStructureSheafCore B S hS p hp B.topology le_rfl)).map T.g) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {X} s => ?_⟩
  obtain ⟨I, y, φ, hy, hcov⟩ := FibredSite.exists_affine_ofArrows_etale B S hS p hp X
  refine (associatedTopology B S hS p (etaleTopology B)).superset_covering ?_ hcov
  intro Z a ha
  rw [Sieve.mem_ofArrows_iff] at ha
  obtain ⟨j, b, rfl⟩ := ha
  refine Sieve.downward_closed _ ?_ b
  exact surjective_sheafSections_map_of_sheafFlatBaseChange_succ B E h S hS p hp hT
    h₁ (y j) (hy j) (T.X₃.val.presheaf.map (φ j).op s)

/-- **Stacks 0771 (2) for the fppf modules at module universe `u + 1`**, faithful class: the
sheaves of modules on the fppf site of `𝒳` with sections in `Type (u + 1)` which are locally
quasi-coherent and have the flat base change property of Stacks 0762, read with the pullback of
sheaves, form a weak Serre subcategory. -/
theorem isWeakSerreClass_isLocallyQuasicoherentWithSheafFlatBaseChange_fppf_succ :
    ObjectProperty.IsWeakSerreClass
      (C := SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
      (fun F => IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u + 1}
        B E h S hS p hp F.val) := by
  let R := ringStructureSheafCore B S hS p hp B.topology le_rfl
  let hle := associatedTopology_mono B S hS p (etaleTopology_le_topology B)
  let : Abelian (SheafOfModules.{u + 1} (Stacks.SheafOfModules.ringOfLe hle R)) :=
    abelian_etaleModuleSheavesSucc B S hS p hp
  let Pe : ObjectProperty (SheafOfModules.{u + 1} (Stacks.SheafOfModules.ringOfLe hle R)) :=
    fun F => IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u + 1}
      B E h S hS p hp F.val
  have hPe : Pe.IsWeakSerreClass :=
    isWeakSerreClass_isLocallyQuasicoherentWithSheafFlatBaseChange_succ B E h S hS p hp
  let ε := Stacks.SheafOfModules.comparisonPushforward.{u + 1, u, u, u + 1} hle R
  have : ε.Additive := Stacks.SheafOfModules.additive_comparisonPushforward _ _
  have : ε.IsRightAdjoint :=
    (Stacks.SheafOfModules.comparisonAdjunction.{u + 1, u, u, u + 1} hle R).isRightAdjoint
  exact ObjectProperty.isWeakSerreClass_inverseImage_of_epi Pe ε
    (epi_comparisonPushforward_map_of_sheafFlatBaseChange_succ B E h S hS p hp)

end Succ

/-- **Stacks 0771 (2) for `Mod(𝒪_𝒳)` at module universe `u + 1`, for an algebraic stack**:
`LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of the sheaves of modules on the fppf site with
sections in `Type (u + 1)`. -/
instance isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppfModulesSucc
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    ObjectProperty.IsWeakSerreClass
      (C := SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids B.topology le_rfl))
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳) :=
  isWeakSerreClass_isLocallyQuasicoherentWithSheafFlatBaseChange_fppf_succ B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids

end AlgebraicGeometry.Stack

end
