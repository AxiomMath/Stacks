module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperExtSingleFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ExistenceChowReductionAux
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.AuxiliaryIdealClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardBaseScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CompletionFullyFaithfulProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.Deformation.ModuleDeformation.ExtClassFullyFaithful
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardRightExact

/-!
# Ext and Hom between coherent modules with proper support over a field

Let `k` be a field, `X` an algebraic space locally of finite type over `Spec k` and `G` a
coherent `𝒪_X`-module whose support is proper over `Spec k`. Then `Hom(G, G)` and
`Ext¹(G, G)` are finite-dimensional over `k`.

Let `𝒦` be the ideal of the scheme-theoretic support of `G` and `Z ⊆ X` the closed subspace cut
out by `𝒦²`; its points lie in the support of `G`, so `Z` is proper over `Spec k`
(Stacks 0CZC). An extension of `G` by `G` is annihilated by `𝒦²`, so it is the direct image of
an extension on `Z` (Stacks 08KS); hence the classes of `Ext¹(G, G)` come from `Ext¹_Z`, which
is finite-dimensional by Stacks 0D0T. Direct image along the closed immersion is fully faithful,
so `Hom(G, G)` is a `Hom` on `Z`, again finite-dimensional by Stacks 0D0T.

## Main results

* `AlgebraicGeometry.Space.isPowAnnihilated_two_of_shortExact`: the middle term of an extension
  of modules annihilated by `𝒦` is annihilated by `𝒦²`.
* `AlgebraicGeometry.Space.finiteDimensional_ext_one_and_hom_of_hasProperSupport`: `Hom(G, G)`
  and `Ext¹(G, G)` are finite-dimensional over `k` for `G` coherent with proper support.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Annihilation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- **The middle term of an extension of modules annihilated by `𝓘` is annihilated by `𝓘²`.** -/
theorem isPowAnnihilated_two_of_shortExact {T : ShortComplex (Modules.{u, u} B S hS F hF)}
    (hT : T.ShortExact) (h₁ : IsPowAnnihilated B S hS F hF 𝓘 1 T.X₁)
    (h₃ : IsPowAnnihilated B S hS F hF 𝓘 1 T.X₃) : IsPowAnnihilated B S hS F hF 𝓘 2 T.X₂ := by
  intro U r hr
  rw [pow_two] at hr
  refine Submodule.mul_induction_on hr (fun a ha b hb x => ?_) (fun r s ihr ihs x => ?_)
  · have hg : T.g.val.app (op U) (b • x) = 0 := by
      rw [map_smul]
      exact h₃ U b (by rwa [pow_one]) _
    obtain ⟨y, hy⟩ := (SheafOfModules.exact_val_app_of_shortExact hT (op U) (b • x)).1 hg
    rw [mul_smul, ← hy, ← map_smul, h₁ U a (by rwa [pow_one]) y, map_zero]
  · rw [add_smul, ihr x, ihs x, add_zero]

end Annihilation

section Field

attribute [local instance] modulesLinear

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
  {X : AlgebraicSpaces B (Spec (.of k)) hk} (f : X ⟶ schemeSpace (baseObject k B hk))
  (hf : IsLocallyOfFiniteType B (Spec (.of k)) hk f.hom)

/-- **Hom and Ext¹ between a coherent module with proper support and itself are
finite-dimensional over the field.** -/
theorem finiteDimensional_ext_one_and_hom_of_hasProperSupport
    (G : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) (hG : IsCoherent B (Spec (.of k)) hk X.1 X.2 G)
    (hsupp : HasProperSupport B (Spec (.of k)) hk X.2 (schemeSpace (baseObject k B hk)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj G)) :
    letI : HasExt.{u + 1} (Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) := HasExt.standard _
    FiniteDimensional k (Ext G G 1) ∧ FiniteDimensional k (G ⟶ G) := by
  let : HasExt.{u + 1} (Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) := HasExt.standard _
  let := C1573.fact_isLocallyNoetherian_of_baseObject X f hf
  have hGqc : G.IsQuasicoherentOnSite := hG.toIsQuasicoherentOnSite
  have := hG.toIsCoherentOnSite
  have hft := isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of k)) hk X G
  obtain ⟨hZ₁, hid⟩ := exists_isClosedSubspace_schemeTheoreticSupport B (Spec (.of k)) hk X G hGqc
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite G hft)
  let Z₁ : ClosedSubspaces B (Spec (.of k)) hk X.1 :=
    ⟨schemeTheoreticSupport B (Spec (.of k)) hk X G, hZ₁⟩
  let K := definingIdealSheaf B (Spec (.of k)) hk X Z₁
  have hKqc := isQuasicoherentOnSite_definingIdealSheaf B (Spec (.of k)) hk X Z₁
  have hJqc := isQuasicoherentOnSite_idealPowerMultiple B (Spec (.of k)) hk X.1 X.2 K
    (SheafOfModules.unit _) (SheafOfModules.isQuasicoherentOnSite_unit _) hKqc 2
  obtain ⟨Z₂, hZ₂⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B (Spec (.of k)) hk X
    _ hJqc
  let i := closedSubspaceInclusion B (Spec (.of k)) hk X Z₂
  have hi : IsClosedImmersion B (Spec (.of k)) hk i.hom := Z₂.2.2
  have hker : SheafOfModules.kerIdeal (structureSharp B (Spec (.of k)) hk i) =
      idealPowerMultiple B (Spec (.of k)) hk X.1 X.2 K 2 (SheafOfModules.unit _) :=
    (C1573.kerIdeal_structureSharp_ι B (Spec (.of k)) hk X Z₂).trans hZ₂
  have hpts := C1573.range_pointsMap_ι_subset_of_definingIdealSheaf_eq_idealPowerMultiple B
    (Spec (.of k)) hk X Z₁ Z₂ 2 hZ₂
  have hsuppeq := supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B (Spec (.of k)) hk X G
    hGqc hft
  obtain ⟨hcl, hprop⟩ := hsupp
  have hZ₂cl := isClosed_range_pointsMap_of_isClosedImmersion B (Spec (.of k)) hk X.2 Z₂.1.ι hi
  have hprop₂ := isProperOver_of_subset B (Spec (.of k)) hk X.2 (schemeSpace (baseObject k B hk)).2
    f.hom hf _ _ hZ₂cl hcl (hpts.trans (by rw [hsuppeq])) hprop
  have hproper : IsProper B (Spec (.of k)) hk (Z₂.1.ι ≫ f.hom) :=
    (exists_isProper_closedSubspace_iff_forall B (Spec (.of k)) hk X.2
      (schemeSpace (baseObject k B hk)).2 f.hom hf _ hZ₂cl).1
      ((isProper_reducedClosedSubspace_iff_exists B (Spec (.of k)) hk X.2
        (schemeSpace (baseObject k B hk)).2 f.hom hf _ hZ₂cl).1 hprop₂) Z₂.1 Z₂.2 rfl
  have hG₁ : IsPowAnnihilated B (Spec (.of k)) hk X.1 X.2 K 1 G := by
    intro U r hr x
    rw [pow_one] at hr
    have hd : definingIdealAt B (Spec (.of k)) hk X Z₁ (op U) =
        annihilatorIdealAt B (Spec (.of k)) hk X G (op U) := by
      rw [← definingIdealSheaf_obj B (Spec (.of k)) hk X, ← annihilatorIdealSheaf_obj B
        (Spec (.of k)) hk X, hid]
    exact smul_eq_zero_of_mem_annihilatorIdealAt B (Spec (.of k)) hk X G (op U) r
      (hd ▸ hr) x
  have hG₂ : IsPowAnnihilated B (Spec (.of k)) hk X.1 X.2 K 2 G := fun U r hr x =>
    hG₁ U r (Ideal.pow_le_pow_right (by norm_num) hr) x
  have hker₂ := C1573.annihilatedByKerIdeal_of_isPowAnnihilated i K 2 hker hKqc
  have hann : ∀ E : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2,
      IsPowAnnihilated B (Spec (.of k)) hk X.1 X.2 K 2 E →
        (modulePushforward B (Spec (.of k)) hk i).essImage E := fun E hE =>
    essImage_modulePushforward_of_annihilatedByKerIdeal B (Spec (.of k)) hk i hi E (hker₂ E hE)
  obtain ⟨G', hG'qc, ⟨eG⟩⟩ := isQuasicoherentEssImagePushforward_of_isClosedImmersion B
    (Spec (.of k)) hk X i hi G hGqc
    (hker₂ G hG₂)
  have hG' := isCoherent_of_modulePushforward_closedSubspace B (Spec (.of k)) hk X
    Fact.out G Z₂ G' hG'qc eG
  let : HasExt.{u + 1} (Modules.{u, u} B (Spec (.of k)) hk Z₂.1.toFunctor Z₂.2.1) :=
    HasExt.standard _
  have hfin := moduleFinite_ext_of_isProper k B hk Z₂.1.toFunctor Z₂.2.1 (Z₂.1.ι ≫ f.hom) hproper
    G' G' hG' hG'
  have hfin₁ := hfin 1
  have hfin₀ := hfin 0
  let L := modulePushforward B (Spec (.of k)) hk i
  have hff := fullyFaithfulModulePushforward B (Spec (.of k)) hk i hi
  have : L.Full := hff.full
  have : L.Faithful := hff.faithful
  have : PreservesFiniteLimits L := preservesFiniteLimits_modulePushforward B (Spec (.of k)) hk i
  have : PreservesFiniteColimits L :=
    preservesFiniteColimits_modulePushforward_of_isClosedImmersion B (Spec (.of k)) hk i hi
  have : L.Additive := Functor.additive_of_preserves_binary_products L
  have : L.Linear k := Stacks.SheafOfModules.linear_of_map_globalSmul _ _ L
    fun a M => modulePushforward_map_globalSmul_baseRingHom k B hk i M a
  refine ⟨?_, ?_⟩
  · have hsurj :
        Function.Surjective (Deformation.ModuleDeformation.extTransfer (k := k) L eG eG 1) := by
      intro x
      obtain ⟨E, ι, p, w, hS, rfl⟩ :=
        (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum _ G G).1 x
      have hE := isPowAnnihilated_two_of_shortExact B (Spec (.of k)) hk X.1 X.2 K hS hG₁ hG₁
      obtain ⟨E', ⟨eE⟩⟩ := hann E hE
      exact Deformation.ModuleDeformation.extClass_mem_range_extTransfer L hS eG eE eG
    exact Module.Finite.of_surjective _ hsurj
  · have : Module.Finite k (G' ⟶ G') := Module.Finite.equiv (Ext.linearEquiv₀ (R := k))
    let φ : (G' ⟶ G') →ₗ[k] (G ⟶ G) :=
      { toFun := fun a => eG.inv ≫ L.map a ≫ eG.hom
        map_add' := fun a b => by rw [L.map_add, Preadditive.add_comp, Preadditive.comp_add]
        map_smul' := fun c a => by
          rw [Functor.map_smul, Linear.smul_comp, Linear.comp_smul]
          rfl }
    refine Module.Finite.of_surjective φ fun a => ⟨L.preimage (eG.hom ≫ a ≫ eG.inv), ?_⟩
    change eG.inv ≫ L.map (L.preimage _) ≫ eG.hom = a
    rw [Functor.map_preimage]
    simp

end Field

end AlgebraicGeometry.Space

end
