module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Algebra.Homology.DerivedCategory.KunnethExactFunctor
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineIntersectionComparison
public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSections
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyFilteredColimits
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsSheafSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering

/-!
# The inputs of the Künneth formula over a field

Let `k` be a field and let `g : Y ⟶ Spec k` be a quasi-compact quasi-separated scheme over `k`
with a quasi-coherent `𝒪_Y`-module `G`. The Künneth map of
`Stacks.KunnethOverField.kunnethNatTrans` is formed from an exact functor
`T : Mod(k) ⥤ Mod(𝒪_Y)` and an additive functor `E : Mod(𝒪_Y) ⥤ Mod(k)`; here
`T = (V ↦ G ⊗_k V)` (`Deformation.Artin.SectionsSheaf.tensorSheafFunctor`) and
`E = Γ(Y, -)` with its `k`-module structure (`Deformation.Artin.SectionsSheaf.sectionsOverBase`),
so that `RᵇE(T(V)) = Hᵇ(Y, G ⊗_k V)`. This file verifies the hypotheses under which that map is
an isomorphism:

* `T` is exact, because every module over `Spec k` is flat over it;
* `RᵇE ∘ T` is `k`-linear on scalars, `G ⊗_k -` and `Hᵇ(Y, -)` both being `k`-linear;
* `RᵇE ∘ T` commutes with the filtered colimits of finite sums, `G ⊗_k -` being a left adjoint
  and `Hᵇ(Y, -)` commuting with filtered colimits on a quasi-compact quasi-separated scheme,
  [Stacks, Tag 01FF];
* the cohomology of a quasi-coherent module on a quasi-compact quasi-separated scheme vanishes in
  all large degrees, [Stacks, Tag 071L].

## Main results

* `AlgebraicGeometry.KunnethQcqs.rightDerivedPlus_map_smul`: the linearity hypothesis.
* `AlgebraicGeometry.KunnethQcqs.preservesColimitsOfShape_rightDerivedPlus`: the colimit
  hypothesis.
* `AlgebraicGeometry.KunnethQcqs.exists_isZero_rightDerivedPlus`: the cohomology of `F` is
  bounded.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open Deformation.Artin.SectionsSheaf Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.KunnethQcqs

variable {k : Type u} [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) (G : Y.Modules)

/-- The functor `G ⊗_k - : Mod(k) ⥤ Mod(𝒪_Y)` is additive. -/
instance : (tensorSheafFunctor g G).Additive := additive_tensorSheafFunctor g G

/-- The functor `Γ(Y, -) : Mod(𝒪_Y) ⥤ Mod(k)` is additive. -/
instance : (sectionsOverBase g).Additive := additive_sectionsOverBase g

/-- Over a field `k`, the functor `G ⊗_k - : Mod(k) ⥤ Mod(𝒪_Y)` preserves finite limits. -/
instance : PreservesFiniteLimits (tensorSheafFunctor g G) :=
  preservesFiniteLimits_tensorSheafFunctor g G (isFlatOver_of_isField g G)

/-- Over a field `k`, the functor `G ⊗_k - : Mod(k) ⥤ Mod(𝒪_Y)` preserves finite colimits. -/
instance : PreservesFiniteColimits (tensorSheafFunctor g G) :=
  preservesFiniteColimits_tensorSheafFunctor g G (isFlatOver_of_isField g G)

/-- **`Hᵇ(Y, G ⊗_k -)` is `k`-linear on scalars**: multiplication by `c ∈ k` on `V` induces
multiplication by `c` on `Hᵇ(Y, G ⊗_k V)`. -/
theorem rightDerivedPlus_map_smul (b : ℤ) (c : k) :
    ((sectionsOverBase g).rightDerivedPlus b).map
      ((tensorSheafFunctor g G).map (c • 𝟙 (ModuleCat.of k k))) = c • 𝟙 _ := by
  rcases lt_or_ge b 0 with hb | hb
  · exact (Functor.isZero_rightDerivedPlus_of_neg _ _ b hb).eq_of_src _ _
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  let := AlgebraicGeometry.Scheme.linearOfRingHom Y ↑(CommRingCat.of k) (baseHom g)
  have := linear_tensorSheafFunctor g G
  have : Functor.Linear k ((sectionsOverBase g).rightDerived m) := linear_cohomologyDeltaFunctor g m
  let e := Stacks.DerivedIndexing.rightDerivedIso (sectionsOverBase g) m
  have h₁ : ((sectionsOverBase g).rightDerived m).map
      ((tensorSheafFunctor g G).map (c • 𝟙 (ModuleCat.of k k))) = c • 𝟙 _ := by
    rw [Functor.map_smul, (tensorSheafFunctor g G).map_id, Functor.map_smul,
      ((sectionsOverBase g).rightDerived m).map_id]
  rw [← cancel_epi (e.hom.app _), ← e.hom.naturality, h₁, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, Category.comp_id]

/-- `G ⊗_k - : Mod(k) ⥤ Mod(𝒪_Y)` commutes with all colimits: it is `M ↦ g^*M̃ ⊗ G`, a composite
of three left adjoints. -/
instance (J : Type u) [SmallCategory J] : PreservesColimitsOfShape J (tensorSheafFunctor g G) := by
  have h₁ : PreservesColimitsOfShape J (tilde.functor (CommRingCat.of k)) :=
    (tilde.adjunction (R := CommRingCat.of k)).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have h₂ : PreservesColimitsOfShape J
      (RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom) :=
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
      g.toLRSHom.toShHom).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have h₃ : PreservesColimitsOfShape J
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).flip.obj G) :=
    ⟨fun {F} ↦ SheafOfModules.preservesColimitsOfSize_sheafTensor_flip_obj (R := Y.sheaf) G F⟩
  exact @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ _ _ h₁
    (@comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ _ _ h₂ h₃)

/-- The ring map `k → Γ(Y, 𝒪_Y)` along which `Γ(Y, -)` is made `k`-linear. -/
private noncomputable abbrev baseRingHom :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom

private instance : (ModuleCat.restrictScalars.{u} (baseRingHom g)).PreservesHomology :=
  Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars _

variable [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **`Hᵇ(Y, -)` commutes with filtered colimits** on a quasi-compact quasi-separated scheme,
[Stacks, Tag 01FF], for the `k`-linear spelling `RᵇE` of cohomology. -/
theorem preservesColimitsOfShape_rightDerivedPlus_sectionsOverBase (b : ℕ) (I : Type u)
    [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I ((sectionsOverBase g).rightDerivedPlus (b : ℤ)) := by
  have : (ModuleCat.restrictScalars.{u} (baseRingHom g)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} (baseRingHom g)).isLeftAdjoint
  have := preservesColimitsOfShape_rightDerived_moduleGlobalSections_of_isFiltered Y b I
  have h₃ : PreservesColimitsOfShape I
      ((moduleGlobalSections Y ⋙ ModuleCat.restrictScalars.{u} (baseRingHom g)).rightDerived b) :=
    preservesColimitsOfShape_of_natIso
      (Functor.rightDerivedCompIso (moduleGlobalSections Y)
        (ModuleCat.restrictScalars.{u} (baseRingHom g)) b).symm
  have h₄ : PreservesColimitsOfShape I ((sectionsOverBase g).rightDerived b) := h₃
  exact preservesColimitsOfShape_of_natIso (Stacks.DerivedIndexing.rightDerivedIso _ b)

/-- **`Hᵇ(Y, G ⊗_k -)` commutes with filtered colimits.** -/
theorem preservesColimitsOfShape_rightDerivedPlus (b : ℕ) (I : Type u) [SmallCategory I]
    [IsFiltered I] :
    PreservesColimitsOfShape I
      (tensorSheafFunctor g G ⋙ (sectionsOverBase g).rightDerivedPlus (b : ℤ)) :=
  have := preservesColimitsOfShape_rightDerivedPlus_sectionsOverBase g b I
  inferInstance

omit [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- A cohomology module of `Γ(Y, -)` vanishes as soon as the corresponding cohomology group
does, for the `k`-linear spelling `RᵇE` of cohomology. -/
theorem isZero_rightDerivedPlus_of_isZero_hgroup (M : Y.Modules) (p : ℕ)
    (h : IsZero (Hgroup Y.ringCatSheaf ⊤ p M)) :
    IsZero (((sectionsOverBase g).rightDerivedPlus (p : ℤ)).obj M) := by
  have h₂ : IsZero
      (((moduleGlobalSections Y ⋙ ModuleCat.restrictScalars.{u} (baseRingHom g)).rightDerived p).obj
        M) :=
    ((ModuleCat.restrictScalars.{u} (baseRingHom g)).map_isZero
      (Stacks.Cohomology.Cech.isZero_rightDerived_evaluation_of_isZero_hgroup Y ⊤ M p h)).of_iso
      ((Functor.rightDerivedCompIso (moduleGlobalSections Y)
        (ModuleCat.restrictScalars.{u} (baseRingHom g)) p).app M)
  exact h₂.of_iso ((Stacks.DerivedIndexing.rightDerivedIso (sectionsOverBase g) p).app M).symm

/-- **The cohomology of a quasi-coherent module on a quasi-compact quasi-separated scheme is
bounded**: it vanishes in negative degrees, and in all degrees beyond a bound depending only on
the scheme, [Stacks, Tag 071L]. -/
theorem exists_isZero_rightDerivedPlus :
    ∃ I : Finset ℤ, ∀ (M : Y.Modules) [M.IsQuasicoherent] (q : ℤ), q ∉ I →
      IsZero (((sectionsOverBase g).rightDerivedPlus q).obj M) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : Y.affineOpens => ((U : Y.Opens) : Set Y)) (fun U => (U : Y.Opens).2)
    (fun x _ => by
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp
        (show x ∈ ⨆ U : Y.affineOpens, (U : Y.Opens) by
          rw [iSup_affineOpens_eq_top Y]
          trivial)
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  let U : Fin t.card → Y.Opens := fun i ↦ ((t.equivFin.symm i : t) : Y.affineOpens)
  have hU : ∀ i, IsAffineOpen (U i) := fun i ↦ ((t.equivFin.symm i : t) : Y.affineOpens).2
  have hcov : ⨆ i, U i = ⊤ := by
    refine top_unique fun x _ ↦ ?_
    obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t.equivFin ⟨V, hVt⟩, by simpa [U] using hxV⟩
  refine ⟨Finset.Ico 0 (Y.coverDegreeBound U), fun M _ q hq ↦ ?_⟩
  rcases lt_or_ge q 0 with hneg | hnn
  · exact Functor.isZero_rightDerivedPlus_of_neg _ _ q hneg
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
  have hp : Y.coverDegreeBound U ≤ p := by
    simp only [Finset.mem_Ico, not_and, not_lt] at hq
    exact_mod_cast hq hnn
  exact isZero_rightDerivedPlus_of_isZero_hgroup g M p
    (isZero_cohomology_of_coverDegreeBound_le_of_isSeparated M U hcov
      (fun i ↦ (hU i).isCompact) (fun i ↦ by have := hU i; infer_instance) p hp)

end AlgebraicGeometry.KunnethQcqs
