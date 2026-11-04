module

public import StacksFrontier.AlgebraicGeometry.Curves.RegularSectionGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDimension
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.ToSpecZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# A regular section does not vanish at the generic points

Let `X` be a locally Noetherian scheme, `ℒ` invertible and `σ` a regular global section of `ℒ`.
At a generic point `η` of an irreducible component the local ring is Artinian, and a nonzero
element killing its maximal ideal shows that `σ` cannot vanish at `η` without failing to be
injective on the stalk. Hence the support of `quot σ 1` contains no generic point; it is closed,
so it is nowhere dense, and on a scheme of dimension at most one it has dimension at most zero.
This is the observation "`Z` has dimension `0`" of the proof of [Stacks, Tag 0E8V]
([Stacks, Tag 056N]), read on the support of the cokernel.

## Main results

* `Stacks.RegularSectionGeneration.mem_nvLocus_of_mem_genericPoints`: a regular section does not
  vanish at any generic point of an irreducible component.
* `Stacks.RegularSectionGeneration.topologicalKrullDim_supp_quot_le_zero`: the cokernels have
  support of dimension at most zero in every positive degree.

## References

* [Stacks Project, Tag 0E8V](https://stacks.math.columbia.edu/tag/0E8V)
* [Stacks Project, Tag 056N](https://stacks.math.columbia.edu/tag/056N)
* [Stacks Project, Tag 06LH](https://stacks.math.columbia.edu/tag/06LH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Ample
open Stacks.GradedSections (powSections mulMap mul)
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.RegularSectionGeneration

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}}

/-- **In an Artinian local ring there is a nonzero element killing the maximal ideal.** -/
theorem exists_ne_zero_mul_eq_zero (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R] :
    ∃ c : R, c ≠ 0 ∧ ∀ r ∈ IsLocalRing.maximalIdeal R, c * r = 0 := by
  classical
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal R) := by
    have h := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h
  have hex : ∃ N : ℕ, IsLocalRing.maximalIdeal R ^ N = ⊥ := hnil
  set N := Nat.find hex
  have hNspec : IsLocalRing.maximalIdeal R ^ N = ⊥ := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Ideal.one_eq_top] at hNspec
    exact top_ne_bot hNspec
  obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hMne : IsLocalRing.maximalIdeal R ^ M ≠ ⊥ := Nat.find_min hex (by omega)
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMne
  refine ⟨c, hc0, fun r hr => ?_⟩
  have : c * r ∈ IsLocalRing.maximalIdeal R ^ N := by
    rw [hM, pow_succ]
    exact Ideal.mul_mem_mul hc hr
  rw [hNspec] at this
  exact Ideal.mem_bot.mp this

/-- **A monomorphism is injective on every stalk.** -/
theorem injective_mapFun_of_mono {M N : X.Modules} (f : M ⟶ N) [hf : Mono f] (x : X) :
    Function.Injective (Stacks.ModuleStalk.mapFun f x) := by
  have hf' : Mono (C := _root_.SheafOfModules.{u} X.ringCatSheaf) f :=
    ⟨fun g h hc => hf.right_cancellation g h hc⟩
  exact (AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap
    (O := X.ringCatSheaf) f).mp hf' x

/-- **The local ring at a generic point of an irreducible component of a locally Noetherian scheme
is Artinian.** -/
theorem isArtinianRing_stalk_of_mem_genericPoints [IsLocallyNoetherian X] {x : X}
    (hx : x ∈ genericPoints X) : IsArtinianRing (X.presheaf.stalk x) := by
  have hdim := Stacks.Chow.ringKrullDim_stalk_eq_zero_of_mem_genericPoints (W := X) ⟨x, hx⟩
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := by
    rw [Ring.krullDimLE_iff, hdim]
    rfl
  exact isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨inferInstance, this⟩

variable (L : X.Modules) [IsInvertibleModule X L]

/-- **A regular section does not vanish at a generic point of an irreducible component.** At such
a point `η` the local ring is Artinian, so some nonzero `c` kills its maximal ideal; if the germ of
`σ` lay in `𝔪_η ℒ_η` it would be killed by `c`, and multiplication by `σ` being injective on the
stalk would make `c` kill the stalk of `𝒪_X`, which is free on the germ of `1`. -/
theorem mem_nvLocus_of_mem_genericPoints [IsLocallyNoetherian X] (σ : powSections L 1)
    [hσ : Mono σ] {x : X} (hx : x ∈ genericPoints X) :
    x ∈ Stacks.AmpleFiniteAvoidance.nvLocus L σ := by
  have := isArtinianRing_stalk_of_mem_genericPoints hx
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_mul_eq_zero (X.presheaf.stalk x)
  by_contra hmem
  have hm : ((natTensorPow L 1).presheaf.Γgerm x).hom (Stacks.SectionProduct.globalSection X _ σ)
      ∈ Stacks.ModuleStalk.maximalSmul (natTensorPow L 1) x := by
    by_contra h
    exact hmem h
  have hkill : c • ((natTensorPow L 1).presheaf.Γgerm x).hom
      (Stacks.SectionProduct.globalSection X _ σ) = 0 := by
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro r hr y _
      rw [smul_smul, hc r hr, zero_smul]
    · intro a b ha hb
      rw [smul_add, ha, hb, add_zero]
  set e := Stacks.AmpleGlobalGeneration.unitModuleIsoUnit X
  set u0 := ((𝟙_ X.Modules).presheaf.Γgerm x).hom
    (Stacks.SectionProduct.globalSection X _ (𝟙 (𝟙_ X.Modules))) with hu0def
  have hu0 : u0 ∉ Stacks.ModuleStalk.maximalSmul (𝟙_ X.Modules) x := by
    have hxm : x ∈ Stacks.AmpleFiniteAvoidance.nvOpen L
        (Stacks.SectionRingProjMorphism.ToSpecZero.unitSec L) := by
      rw [Stacks.SectionRingProjMorphism.ToSpecZero.nvOpen_unitSec L]
      trivial
    rwa [← SetLike.mem_coe, Stacks.AmpleFiniteAvoidance.coe_nvOpen] at hxm
  set w := Stacks.ModuleStalk.mapFun e.inv x u0 with hwdef
  have hew : Stacks.ModuleStalk.mapFun e.hom x w = u0 := by
    rw [hwdef, ← Stacks.ModuleStalk.mapFun_comp, e.inv_hom_id, Stacks.ModuleStalk.mapFun_id]
  have hw : w ∉ Stacks.ModuleStalk.maximalSmul (unitModule X) x := fun h =>
    hu0 (hew ▸ Stacks.SectionProduct.mapFun_mem_maximalSmul e.hom x h)
  have hunit : IsUnit (unitStalkFun X x w) := by
    by_contra hnu
    apply hw
    have hr : unitStalkFun X x w ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hweq : w = unitStalkFun X x w • (unitStalkEquiv X x).symm 1 := by
      apply (unitStalkEquiv X x).injective
      rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one, unitStalkEquiv_apply]
    rw [hweq]
    exact Stacks.ModuleStalk.smul_mem_maximalSmul_of_mem_maximalIdeal hr _
  have hgerm : Stacks.ModuleStalk.mapFun (e.hom ≫ σ) x w =
      ((natTensorPow L 1).presheaf.Γgerm x).hom (Stacks.SectionProduct.globalSection X _ σ) := by
    rw [Stacks.ModuleStalk.mapFun_comp, hew, hu0def,
      ← Stacks.SectionProduct.Γgerm_globalSection_comp, Category.id_comp]
  have hcw : c • w = 0 := by
    apply injective_mapFun_of_mono (e.hom ≫ σ) x
    rw [Stacks.ModuleStalk.mapFun_smul, hgerm, hkill]
    exact (map_zero ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      (e.hom ≫ σ).mapPresheaf).hom).symm
  have h0 := congrArg (unitStalkFun X x) hcw
  rw [unitStalkFun_smul,
    show unitStalkFun X x 0 = 0 from map_zero (unitStalkIso X x).hom.hom] at h0
  exact hc0 (hunit.mul_left_eq_zero.mp h0)

/-- **The cokernel of multiplication by a regular section has support of dimension at most zero**
on a Noetherian scheme of dimension at most one, in every positive degree. Its support in degree
one is closed and misses every generic point of an irreducible component
(`mem_nvLocus_of_mem_genericPoints`), hence is nowhere dense, which costs one dimension; in higher
degrees the support is smaller (`supp_quot_subset_one`). -/
theorem topologicalKrullDim_supp_quot_le_zero [IsLocallyNoetherian X]
    [TopologicalSpace.NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (σ : powSections L 1) [Mono σ]
    (hfin : (natTensorPow L (1 + 1)).IsFiniteType) {n : ℕ} (hn : 1 ≤ n) :
    topologicalKrullDim (SheafOfModules.supp (quot σ n)) ≤ 0 := by
  have hclosed : IsClosed (SheafOfModules.supp (quot σ 1)) :=
    AlgebraicGeometry.Scheme.Modules.isClosed_supp_cokernel _ hfin
  have hnd : IsNowhereDense (SheafOfModules.supp (quot σ 1)) := by
    rw [IsNowhereDense, hclosed.closure_eq]
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    let η : genericPoints X := genericPoints.ofComponent ⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩
    have hηx : η.1 ⤳ x :=
      (genericPoints.isGenericPoint_ofComponent _).specializes mem_irreducibleComponent
    exact notMem_supp_quot_of_mem_nvLocus σ (mem_nvLocus_of_mem_genericPoints L σ η.2) 1
      (interior_subset (hηx.mem_open isOpen_interior hx))
  have h1 : topologicalKrullDim (SheafOfModules.supp (quot σ 1)) ≤ ((0 : ℕ) : WithBot ℕ∞) :=
    hnd.topologicalKrullDim_le_of_le_natCast_succ hclosed 0 (by simpa using hdim)
  exact ((Topology.IsEmbedding.inclusion
      (supp_quot_subset_one σ hn)).isInducing.topologicalKrullDim_le).trans
    (by simpa using h1)

end Stacks.RegularSectionGeneration

end
