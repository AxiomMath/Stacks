module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentArtinRees
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CoequalizerGlueingTowerStructureMap

/-!
# The kernel of `𝒪_X ⟶ f_* 𝒪_{X'}` meets `𝓘ⁿ` in zero for `n ≫ 0`

In the situation of Stacks 0AGH with `X` quasi-compact, let `𝒦 = Ker(𝒪_X ⟶ f_* 𝒪_{X'})` and let
`𝓘` be the ideal of `Z`. This file proves the second paragraph of the proof of Stacks 0AGK:
`𝒦 ∩ 𝓘ⁿ = 0` for all `n ≫ 0`. Since `f` is an isomorphism over `U`, `𝒦` vanishes over every
étale chart on which `𝓘` is the unit ideal, so `𝓘ᵗ 𝒦 = 0` for some `t` (Stacks 07UK); and
Artin-Rees (Stacks 07UL) gives `𝓘ⁿ ∩ 𝒦 = 𝓘ⁿ⁻ᶜ(𝓘ᶜ ∩ 𝒦) ⊆ 𝓘ⁿ⁻ᶜ 𝒦 = 0` once `n ≥ c + t`. Both
are applied in the forms
`AlgebraicGeometry.Space.exists_idealPowSmul_eq_bot_of_forall_subsingleton` and
`AlgebraicGeometry.Space.exists_idealPowSmul_inf_eq_of_isQuasiCompactSpace`, which ask only for
quasi-compactness and local Noetherianity: Stacks 0AGK does not assume `X` quasi-separated.

The source's appeal to Stacks 07UJ (stabilization of the kernels of `𝒪_X ⟶ 𝒜_n`) is not needed:
those kernels decrease with `n`, and the argument above shows directly that they vanish.

## Main results

* `CoequalizerGlueSituation.kernelIdealSheaf_modification_obj_eq_bot`: `𝒦(V) = 0` on every
  étale chart `V` with `𝓘(V) = 𝒪(V)`.
* `CoequalizerGlueSituation.eventually_modificationKernel_inf_neighbourhoodIdeal_eq_bot`:
  `𝒦 ∩ 𝓘ⁿ⁺¹ = 0` for `n ≫ 0`.
* `CoequalizerGlueSituation.exists_factorsThroughSection_of_eventually_rangeLe`: Stacks 0AGK,
  for `X` quasi-compact.

## References

* [Stacks Project, Tag 0AGK](https://stacks.math.columbia.edu/tag/0AGK)
* [Stacks Project, Tag 07UK](https://stacks.math.columbia.edu/tag/07UK)
* [Stacks Project, Tag 07UL](https://stacks.math.columbia.edu/tag/07UL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Kernel ideal sheaves of isomorphisms -/

/-- The structure map of the identity is injective on every chart: its kernel is zero. -/
theorem kernelIdealSheaf_id_obj_eq_bot (Y : AlgebraicSpaces B S hS)
    (W : (SmallEtale B S hS Y.1)ᵒᵖ) : (kernelIdealSheaf B S hS (𝟙 Y)).obj W = ⊥ := by
  have : IsIso ((structureSharp B S hS (𝟙 Y)).hom.app W) := inferInstance
  have hinj := (ConcreteCategory.bijective_of_isIso
    ((structureSharp B S hS (𝟙 Y)).hom.app W)).1
  refine le_bot_iff.1 fun r hr => ?_
  have hr' : (structureSharp B S hS (𝟙 Y)).hom.app W r = 0 := hr
  exact (Submodule.mem_bot _).2 (hinj (hr'.trans (map_zero _).symm))

/-- The kernel ideal sheaf of an isomorphism of algebraic spaces is zero. -/
theorem kernelIdealSheaf_obj_eq_bot_of_isIso {P Y : AlgebraicSpaces B S hS} (φ : P ⟶ Y)
    [IsIso φ] (W : (SmallEtale B S hS Y.1)ᵒᵖ) : (kernelIdealSheaf B S hS φ).obj W = ⊥ := by
  have h := kernelIdealSheaf_le_comp (B := B) (S := S) (hS := hS) (𝟙 Y) φ (inv φ) (𝟙 Y)
    (by rw [Category.id_comp, IsIso.inv_hom_id])
  rw [Category.comp_id] at h
  refine le_bot_iff.1 fun r hr => ?_
  have := h W hr
  rwa [kernelIdealSheaf_id_obj_eq_bot] at this

namespace CoequalizerGlueSituation

variable (T : CoequalizerGlueSituation.{u})

/-! ### The kernel vanishes where `𝓘` is the unit ideal -/

/-- The open complement `U` of `Z`, as an algebraic space. -/
abbrev openSpace : AlgebraicSpaces T.B T.S T.hS := ⟨T.U.toFunctor, T.hU.1⟩

/-- The inclusion of the open complement `U` of `Z`. -/
abbrev openIncl : T.openSpace ⟶ T.targetSpace := ObjectProperty.homMk T.U.ι

/-- The inclusion of the open complement `U` of `Z` is étale. -/
theorem isEtale_openIncl : IsEtale T.B T.S T.hS T.openIncl.hom :=
  isEtale_of_isOpenImmersion T.B T.S T.hS T.hU.2

/-- The ideal of the zeroth infinitesimal neighbourhood of `Z` is the ideal `𝓘` of `Z`. -/
theorem neighbourhoodIdeal_zero : T.neighbourhoodIdeal 0 = T.closedIdeal :=
  Stacks.Sites.idealPow_one T.closedIdeal

/-- An étale chart of `X` on which `𝓘` is the unit ideal avoids `Z`, so it maps into `U` on
points. -/
theorem range_subset_open_of_closedIdeal_obj_eq_top (V : SmallEtale T.B T.S T.hS T.X)
    (hV : T.closedIdeal.obj (op V) = ⊤) :
    Set.range (pointsMap T.B T.S T.hS (yoneda.obj ((SmallEtale.toOver T.B T.S T.hS T.X).obj V))
        V.1.hom) ⊆ Set.range (pointsMap T.B T.S T.hS T.U.toFunctor T.U.ι) := by
  rintro x ⟨v, rfl⟩
  rw [T.U_compl_Z]
  rintro ⟨z, hz⟩
  obtain ⟨l, hl⟩ := T.exists_lift_neighbourhoodSystem 0
  have hx : pointsMap T.B T.S T.hS _ V.1.hom v ∈
      Set.range (pointsMap T.B T.S T.hS (T.neighbourhood 0).1.toFunctor
        (T.neighbourhood 0).1.ι) :=
    ⟨_, (congrFun (pointsMap_comp T.B T.S T.hS _ l.hom (T.neighbourhood 0).1.ι) z).symm.trans
      ((congrArg (fun k => pointsMap T.B T.S T.hS _ k z)
        (congrArg (fun k : T.closedSpace ⟶ T.targetSpace => k.hom) hl)).trans hz)⟩
  rw [range_pointsMap_ι_eq_idealZeroLocus (B := T.B) (S := T.S) (hS := T.hS)
    (X := T.targetSpace) (Z := T.neighbourhood 0), T.definingIdealSheaf_neighbourhood 0,
    T.neighbourhoodIdeal_zero] at hx
  exact (mem_idealZeroLocus_iff T.B T.S T.hS T.targetSpace _ _).1 hx V hV ⟨v, rfl⟩

/-- The chart of `U` through which a chart of `X` factoring through `U` passes, read back as a
chart of `X`, is the chart itself. -/
theorem smallEtalePostcomp_obj_mk_eq (V : SmallEtale T.B T.S T.hS T.X)
    (g : yoneda.obj ((SmallEtale.toOver T.B T.S T.hS T.X).obj V) ⟶ T.U.toFunctor)
    (hg : g ≫ T.U.ι = V.1.hom) (hgEt : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme T.B T.S T.hS)).presheaf g) :
    (smallEtalePostcomp T.B T.S T.hS T.openIncl T.isEtale_openIncl).obj
      ⟨CostructuredArrow.mk g, hgEt⟩ = V := by
  refine ObjectProperty.FullSubcategory.ext ?_
  show CostructuredArrow.mk (g ≫ T.U.ι) = V.1
  rw [hg]
  rfl

/-- **`Ker(𝒪_X ⟶ f_* 𝒪_{X'})` vanishes on every étale chart on which `𝓘` is the unit ideal.**
Such a chart avoids `Z`, so it factors through `U`; over `U` the morphism `f` is an isomorphism,
and the kernel ideal sheaf commutes with étale localization of the target. -/
theorem kernelIdealSheaf_modification_obj_eq_bot (V : SmallEtale T.B T.S T.hS T.X)
    (hV : T.closedIdeal.obj (op V) = ⊤) :
    (kernelIdealSheaf T.B T.S T.hS (ObjectProperty.homMk T.f :
      T.modificationSpace ⟶ T.targetSpace)).obj (op V) = ⊥ := by
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points T.B T.S T.hS T.hX
    (isAlgebraicSpace_yoneda T.B T.S T.hS _) T.U T.hU V.1.hom).2
      (T.range_subset_open_of_closedIdeal_obj_eq_top V hV)
  have hgEt : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme T.B T.S T.hS)).presheaf g :=
    presheaf_etale_of_isEtale T.B T.S T.hS (isEtale_of_comp_mono T.B T.S T.hS g T.U.ι
      (by rw [hg]; exact isEtale_of_presheaf_etale T.B T.S T.hS V.2))
  have h1 := kernelIdealSheaf_fibreProduct_obj T.B T.S T.hS
    (ObjectProperty.homMk T.f : T.modificationSpace ⟶ T.targetSpace) T.openIncl
    T.isEtale_openIncl ⟨CostructuredArrow.mk g, hgEt⟩
  have hmove : ∀ A : SmallEtale T.B T.S T.hS T.X, A = V →
      (kernelIdealSheaf T.B T.S T.hS (ObjectProperty.homMk T.f :
        T.modificationSpace ⟶ T.targetSpace)).obj (op A) = ⊥ →
      (kernelIdealSheaf T.B T.S T.hS (ObjectProperty.homMk T.f :
        T.modificationSpace ⟶ T.targetSpace)).obj (op V) = ⊥ := by
    rintro A rfl h
    exact h
  refine hmove _ (T.smallEtalePostcomp_obj_mk_eq V g hg hgEt) ?_
  rw [← h1]
  let φ : AlgebraicSpaces.fiberProduct T.B T.S T.hS
      (ObjectProperty.homMk T.f : T.modificationSpace ⟶ T.targetSpace) T.openIncl ⟶
        T.openSpace :=
    ObjectProperty.homMk (pullback.snd T.f T.U.ι)
  have : IsIso ((ObjectProperty.ι _).map φ) := T.f_iso_over_U
  have : IsIso φ := isIso_of_reflects_iso φ (ObjectProperty.ι _)
  exact kernelIdealSheaf_obj_eq_bot_of_isIso φ _

/-! ### `𝒦 ∩ 𝓘ⁿ = 0` for `n ≫ 0` -/

/-- The kernel `𝒦` of `𝒪_X ⟶ f_* 𝒪_{X'}` is quasi-coherent. -/
theorem isQuasicoherentOnSite_modificationKernel :
    (kernelIdealSheaf T.B T.S T.hS (ObjectProperty.homMk T.f :
      T.modificationSpace ⟶ T.targetSpace)).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_kernelIdealSheaf T.B T.S T.hS _ T.hf.2.1.2

/-- **`𝓘ᵗ 𝒦 = 0` for some `t`** (Stacks 07UK): `𝒦` has no sections over the charts on which `𝓘` is
the unit ideal. -/
theorem exists_idealSmul_idealPow_modificationKernel_eq_bot
    (hqc : IsQuasiCompactSpace T.B T.S T.hS T.X) :
    ∃ t : ℕ, Stacks.Sites.idealSmul (M := (kernelIdealSheaf T.B T.S T.hS
        (ObjectProperty.homMk T.f : T.modificationSpace ⟶ T.targetSpace)).toSheafOfModules)
      (Stacks.Sites.idealPow (O := (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)
        T.closedIdeal t) ⊤ = ⊥ := by
  have : Fact (HasEtaleLocalProperty T.B T.S T.hS T.X
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨T.locallyNoetherian⟩
  refine exists_idealPowSmul_eq_bot_of_forall_subsingleton T.B T.S T.hS T.targetSpace hqc
    T.locallyNoetherian _ (isCoherent_idealSheaf T.B T.S T.hS T.X T.hX _
      T.isQuasicoherentOnSite_modificationKernel) T.closedIdeal
    T.isQuasicoherentOnSite_closedIdeal fun V hV => ⟨fun a b => Subtype.ext ?_⟩
  have h := T.kernelIdealSheaf_modification_obj_eq_bot V hV
  rw [(Submodule.mem_bot _).1 (h.le a.2), (Submodule.mem_bot _).1 (h.le b.2)]

/-- The submodule `𝓘ᵏ 𝒪_X` of the structure sheaf is the ideal `𝓘ᵏ`. -/
theorem idealPowSubmodule_closedIdeal_unit (k : ℕ) :
    idealPowSubmodule T.closedIdeal k (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)) =
      Stacks.Sites.idealPow (O := (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)
        T.closedIdeal k := by
  rw [idealPowSubmodule_eq_idealPowSmul]
  exact Stacks.Sites.idealSmul_top_eq (O := (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)
    (Stacks.Sites.idealPow (O := (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)
      T.closedIdeal k)

/-- **`Ker(𝒪_X ⟶ f_* 𝒪_{X'}) ∩ 𝓘ⁿ⁺¹ = 0` for `n ≫ 0`**, for `X` quasi-compact. -/
theorem eventually_modificationKernel_inf_neighbourhoodIdeal_eq_bot
    (hqc : IsQuasiCompactSpace T.B T.S T.hS T.X) :
    ∃ n₀, ∀ n, n₀ ≤ n → kernelIdealSheaf T.B T.S T.hS (ObjectProperty.homMk T.f :
        T.modificationSpace ⟶ T.targetSpace) ⊓ T.neighbourhoodIdeal n = ⊥ := by
  have : Fact (HasEtaleLocalProperty T.B T.S T.hS T.X
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨T.locallyNoetherian⟩
  obtain ⟨t, ht⟩ := T.exists_idealSmul_idealPow_modificationKernel_eq_bot hqc
  obtain ⟨c, hc⟩ := exists_idealPowSmul_inf_eq_of_isQuasiCompactSpace T.B T.S T.hS T.X T.hX hqc
    T.locallyNoetherian _ (isCoherent_structureSheaf T.B T.S T.hS T.X T.hX)
    (kernelIdealSheaf T.B T.S T.hS (ObjectProperty.homMk T.f :
      T.modificationSpace ⟶ T.targetSpace)) T.isQuasicoherentOnSite_modificationKernel
    T.closedIdeal T.isQuasicoherentOnSite_closedIdeal
  have hann := idealPowSubmodule_unit_le_annihilatorIdealSheaf T.B T.S T.hS T.targetSpace
    T.closedIdeal t _ ht
  refine ⟨c + t, fun n hn => ?_⟩
  have key : Stacks.Sites.idealPowSmul T.closedIdeal (n + 1 - c)
      (idealPowSubmodule T.closedIdeal c (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)) ⊓
        kernelIdealSheaf T.B T.S T.hS (ObjectProperty.homMk T.f :
          T.modificationSpace ⟶ T.targetSpace)) ≤ ⊥ := by
    refine (Stacks.Sites.idealSmul_mono_right
      (Stacks.Sites.idealPow (O := (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)
        T.closedIdeal (n + 1 - c)) inf_le_right).trans ?_
    refine (Stacks.Sites.idealSmul_mono_left
      (Stacks.Sites.idealPow_antitone T.closedIdeal (by omega : t ≤ n + 1 - c)) _).trans ?_
    refine Stacks.SheafOfModules.sheafifySubmodule_le
      (Stacks.Sites.presheafIdealSmul_le
        (Stacks.Sites.idealPow (O := (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)
          T.closedIdeal t) fun Y a ha m hm => ?_)
    have ha' : a ∈ (annihilatorIdealSheaf T.B T.S T.hS T.targetSpace
        (kernelIdealSheaf T.B T.S T.hS (ObjectProperty.homMk T.f :
          T.modificationSpace ⟶ T.targetSpace)).toSheafOfModules).obj Y :=
      hann Y (by rw [T.idealPowSubmodule_closedIdeal_unit t]; exact ha)
    have h0 := congrArg Subtype.val (ha' Y (𝟙 Y) ⟨m, hm⟩)
    simp only [CategoryTheory.Functor.map_id] at h0
    show a • m ∈ (⊥ : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)).Submodule).obj Y
    rw [SheafOfModules.Submodule.bot_obj]
    exact (Submodule.mem_bot _).2 h0
  rw [hc (n + 1) (by omega), T.idealPowSubmodule_closedIdeal_unit (n + 1)] at key
  exact le_bot_iff.1 (le_trans (le_inf inf_le_right inf_le_left) key)

/-- **Stacks 0AGK, from the conclusion of Stacks 0AGG and the eventual containment of images.**
For `X` quasi-compact and any choice of coequalizers `X_n` along the infinitesimal neighbourhoods
`Z_n` of `Z`: if for `n ≫ 0` some `𝒜_{n+m} ⟶ 𝒜_n` has image in that of `𝒪_X`, then for all `n`
large enough there is an `m` such that `X_n ⟶ X_{n+m}` factors through a closed immersion
`X ⟶ X_{n+m}`, a section of `X_{n+m} ⟶ X`. -/
theorem exists_factorsThroughSection_of_eventually_rangeLe
    (hAGG : ProperKernelPairCoequalizers T.B T.S T.hS)
    (hqc : IsQuasiCompactSpace T.B T.S T.hS T.X)
    (D : ∀ n, KernelPairCoequalizer T.B T.S T.hS (T.neighbourhoodSystem.glueMapAt n))
    (hrange : ∃ n₁, ∀ n, n₁ ≤ n → ∃ m, T.neighbourhoodSystem.RangeLeStructureAt D n m) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∃ m, T.neighbourhoodSystem.FactorsThroughSection D n m :=
  T.exists_factorsThroughSection_of_eventually hAGG D
    (T.eventually_modificationKernel_inf_neighbourhoodIdeal_eq_bot hqc) hrange

end CoequalizerGlueSituation

end AlgebraicGeometry.Space

end
