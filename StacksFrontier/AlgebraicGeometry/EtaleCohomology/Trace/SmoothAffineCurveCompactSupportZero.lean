module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCompactSupportZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTowerExcision
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSheafExcisionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImageRealizable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `H⁰_c` of a lisse sheaf on a smooth affine curve vanishes, connected or not

Let `X` be a smooth affine curve over a finite field `k`, not necessarily connected, with a
compactification `j`, and `k̄` an algebraically closed extension of `k`. Then
`H⁰_c(X_k̄, G) = 0` for a sheaf `G` of `Λ`-modules which is locally constant of finite type on
the connected components of `X`, and `H⁰_c(X_k̄, F ⊗ ℚ_ℓ) = 0` for a lisse ℓ-adic sheaf `F`.

On a connected component, a smooth connected affine curve, this is
`isZero_compactSupportFrobeniusCohomologyGroup_zero_of_isFiniteTypeLocallyConstant` (the last
assertion of [Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)). The connected components are
finitely many, open and closed, and they are put together by excision: for a decomposition
`W = A ⊔ B` into complementary open subschemes, the sequence
`H⁰_c(A_k̄, G|_A) → H⁰_c(W_k̄, G) → H⁰_c(B_k̄, G|_B)` is exact
(`Stacks.EtaleCohomology.exact_compactSupportSheafCohomology_openClosed`, `B` being closed as
well). The fibres of a family of smooth affine curves over the closed points of the base, in the
induction step of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), are of this kind.

The standard model `HasDerivedCategory.standard` of the derived categories is used because the
consumed compactly supported cohomology is defined there.

## Main results

* `Stacks.EtaleCohomology.isZero_compactSupportSheafCohomology_zero_of_isCompl`,
  `Stacks.EtaleCohomology.isZero_compactSupportSheafCohomology_zero_of_partition`: excision.
* `Stacks.EtaleCohomology.isZero_compactSupportSheafCohomology_zero_of_smoothOfRelativeDimension`:
  the finite levels.
* `subsingleton_rationalGeometricCompactlySupportedCohomology_zero_of_smoothOfRelativeDimension`
  in `Stacks.EtaleCohomology.LAdicSheaf`: the ℓ-adic statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section Level

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar]
  [Algebra k kbar]

/-- **`H⁰_c` along a decomposition into complementary open subschemes.** If `W = A ⊔ B` with `A`
and `B` open, and `H⁰_c` of the restrictions of a sheaf `G` to `A` and to `B` vanish for every
compactification, then `H⁰_c(W_k̄, G) = 0`: the excision sequence
`H⁰_c(A_k̄, G|_A) → H⁰_c(W_k̄, G) → H⁰_c(B_k̄, G|_B)` is exact, `B` being also closed. -/
theorem isZero_compactSupportSheafCohomology_zero_of_isCompl {W : Scheme.{u}}
    (g : W ⟶ Spec (.of k)) [QuasiCompact g] (J : CompactificationOf (Over.mk g)) (A B : W.Opens)
    (hAB : IsCompl A B)
    (G : EtaleModules.{u, 0} Λ W)
    (hA : ∀ J' : CompactificationOf (Over.mk (A.ι ≫ g)),
      IsZero ((compactSupportSheafCohomology Λ (A.ι ≫ g) J' kbar 0).obj
        ((etaleModuleRestriction.{u, 0} Λ A.ι).obj G)))
    (hB : ∀ J' : CompactificationOf (Over.mk (B.ι ≫ g)),
      IsZero ((compactSupportSheafCohomology Λ (B.ι ≫ g) J' kbar 0).obj
        ((etaleModuleRestriction.{u, 0} Λ B.ι).obj G))) :
    IsZero ((compactSupportSheafCohomology Λ g J kbar 0).obj G) := by
  have h1 : (A : Set W) ∩ B = ∅ := by
    rw [← TopologicalSpace.Opens.coe_inf, hAB.inf_eq_bot, TopologicalSpace.Opens.coe_bot]
  have h2 : (A : Set W) ∪ B = Set.univ := by
    rw [← TopologicalSpace.Opens.coe_sup, hAB.sup_eq_top, TopologicalSpace.Opens.coe_top]
  have hcompl : (B : Set W) = (A : Set W)ᶜ := eq_compl_iff_isCompl.2
    ⟨disjoint_iff.2 ((Set.inter_comm _ _).trans h1),
      codisjoint_iff.2 ((Set.union_comm _ _).trans h2)⟩
  have : IsClosedImmersion B.ι := .of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι, hcompl]
    exact A.isOpen.isClosed_compl)
  have hij : Set.range A.ι.base = (Set.range B.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι, hcompl, compl_compl]
  have hex := exact_compactSupportSheafCohomology_openClosed Λ g J kbar B.ι A.ι hij G 0
  have hL : IsZero ((compactSupportSheafCohomology Λ g J kbar 0).obj
      ((etaleModuleOpenPart Λ A.ι).obj G)) :=
    (hA (J.restrictOpen A.ι)).of_iso
      ((compactSupportSheafCohomologyRestrictOpenIso Λ g J kbar 0 A.ι).app _).symm
  have hR : IsZero ((compactSupportSheafCohomology Λ g J kbar 0).obj
      ((etaleModuleClosedPart Λ B.ι).obj G)) :=
    ((hB (J.restrictClosed B.ι)).of_iso
      ((compactSupportSheafCohomology Λ (B.ι ≫ g) (J.restrictClosed B.ι) kbar 0).mapIso
        ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ B.ι).app G))).of_iso
      ((compactSupportSheafCohomologyRestrictClosedIso Λ g J kbar 0 B.ι).app _).symm
  have := ModuleCat.subsingleton_of_isZero hL
  have := ModuleCat.subsingleton_of_isZero hR
  have hzero : ∀ z : (compactSupportSheafCohomology Λ g J kbar 0).obj G, z = 0 := fun z => by
    obtain ⟨a, ha⟩ := (hex z).1 (Subsingleton.elim _ _)
    rw [← ha, Subsingleton.elim a 0, map_zero]
  have : Subsingleton ((compactSupportSheafCohomology Λ g J kbar 0).obj G) :=
    ⟨fun x y => by rw [hzero x, hzero y]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- **`H⁰_c` on a finite union of disjoint open pieces.** Let `Z i` be pairwise disjoint opens of
`X`, and suppose that `H⁰_c` of the restriction of `G` vanishes on every open subscheme of `X`
whose image is one of the `Z i`, for every compactification. Then it vanishes on every open
subscheme whose image is the union of finitely many (at least one) of the `Z i`. -/
theorem isZero_compactSupportSheafCohomology_zero_of_partition {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of k)) [QuasiCompact fX] {ι : Type*} (Z : ι → X.Opens)
    (hdisj : Pairwise fun i j => Disjoint (Z i) (Z j)) (hclosed : ∀ i, IsClosed (Z i : Set X))
    (G : EtaleModules.{u, 0} Λ X)
    (hleaf : ∀ (V : Scheme.{u}) (e : V ⟶ X) [IsOpenImmersion e] (i : ι),
      Set.range e.base = Z i → ∀ (g : V ⟶ Spec (.of k)), g = e ≫ fX →
        ∀ J : CompactificationOf (Over.mk g),
          IsZero ((compactSupportSheafCohomology Λ g J kbar 0).obj
            ((etaleModuleRestriction.{u, 0} Λ e).obj G)))
    (s : Finset ι) (hs : s.Nonempty) :
    ∀ (V : Scheme.{u}) (e : V ⟶ X) [IsOpenImmersion e],
      Set.range e.base = ⋃ i ∈ s, (Z i : Set X) → ∀ (g : V ⟶ Spec (.of k)), g = e ≫ fX →
        ∀ J : CompactificationOf (Over.mk g),
          IsZero ((compactSupportSheafCohomology Λ g J kbar 0).obj
            ((etaleModuleRestriction.{u, 0} Λ e).obj G)) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro V e _ he g hg J
    refine hleaf V e a ?_ g hg J
    rw [he]
    ext x
    simp only [Finset.mem_singleton, Set.mem_iUnion, exists_prop, exists_eq_left]
  | cons a s ha hs ih =>
    intro V e _ he g hg J
    have : IsClosedImmersion e := .of_isPreimmersion _ (by
      rw [he]
      exact Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun i _ => hclosed i)
    have : QuasiCompact g := by rw [hg]; infer_instance
    let A : V.Opens := ⟨e ⁻¹' (Z a : Set X), (Z a).isOpen.preimage e.continuous⟩
    let B : V.Opens := ⟨e ⁻¹' (⋃ i ∈ s, (Z i : Set X)),
      (isOpen_biUnion fun i _ => (Z i).isOpen).preimage e.continuous⟩
    have hBs : (B : Set V) = e ⁻¹' (⋃ i ∈ s, (Z i : Set X)) := rfl
    have hAB : IsCompl A B := by
      constructor
      · rw [disjoint_iff, ← SetLike.coe_set_eq, TopologicalSpace.Opens.coe_inf,
          TopologicalSpace.Opens.coe_bot, hBs, Set.eq_empty_iff_forall_notMem]
        rintro v ⟨hva, hvb⟩
        simp only [Set.mem_preimage, Set.mem_iUnion] at hvb
        obtain ⟨i, hi, hvi⟩ := hvb
        have hne : a ≠ i := fun h => ha (h ▸ hi)
        have hZ : Disjoint (Z a : Set X) (Z i) := Set.disjoint_iff_inter_eq_empty.2 (by
          rw [← TopologicalSpace.Opens.coe_inf, (hdisj hne).eq_bot, TopologicalSpace.Opens.coe_bot])
        exact Set.disjoint_left.1 hZ hva hvi
      · rw [codisjoint_iff, ← SetLike.coe_set_eq, TopologicalSpace.Opens.coe_sup,
          TopologicalSpace.Opens.coe_top, hBs, Set.eq_univ_iff_forall]
        intro v
        have hv : e.base v ∈ Set.range e.base := ⟨v, rfl⟩
        rw [he] at hv
        simp only [Finset.mem_cons, Set.mem_iUnion, exists_prop] at hv
        obtain ⟨i, rfl | hi, hvi⟩ := hv
        · exact Or.inl hvi
        · exact Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, hvi⟩)
    refine isZero_compactSupportSheafCohomology_zero_of_isCompl Λ kbar g J A B hAB _
      (fun J' => ?_) (fun J' => ?_)
    · refine (hleaf A.toScheme (A.ι ≫ e) a ?_ (A.ι ≫ g) (by rw [hg, Category.assoc]) J').of_iso
        ((compactSupportSheafCohomology Λ (A.ι ≫ g) J' kbar 0).mapIso
          ((etaleModuleRestrictionCompIso.{u, 0} Λ A.ι e).app G))
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
      show (⇑e) '' ((⇑e) ⁻¹' (Z a : Set X)) = _
      rw [Set.image_preimage_eq_inter_range]
      refine Set.inter_eq_left.2 ?_
      rw [he]
      exact Set.subset_biUnion_of_mem (u := fun i => (Z i : Set X)) (Finset.mem_cons_self a s)
    · refine (ih B.toScheme (B.ι ≫ e) ?_ (B.ι ≫ g) (by rw [hg, Category.assoc]) J').of_iso
        ((compactSupportSheafCohomology Λ (B.ι ≫ g) J' kbar 0).mapIso
          ((etaleModuleRestrictionCompIso.{u, 0} Λ B.ι e).app G))
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, hBs]
      rw [Set.image_preimage_eq_inter_range]
      refine Set.inter_eq_left.2 ?_
      rw [he]
      exact Set.biUnion_subset_biUnion_left (fun i hi => Finset.mem_cons_of_mem hi)

/-- **`H⁰_c(X_k̄, G) = 0` for a smooth affine curve over a finite field, not necessarily
connected**, and a sheaf `G` of `Λ`-modules whose restriction to every open subscheme lying in a
connected component of `X` is locally constant of finite type: on each connected component, a
smooth connected affine curve, this is
`isZero_compactSupportFrobeniusCohomologyGroup_zero_of_isFiniteTypeLocallyConstant`, and the
components are put together by excision. -/
@[sga "4½ Sommes_trig 1.18" "Clause b), special case"]
theorem isZero_compactSupportSheafCohomology_zero_of_smoothOfRelativeDimension [IsAlgClosed kbar]
    {X : Scheme.{u}} [IsNoetherian X] [Nonempty X] [IsAffine X] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (J : CompactificationOf (Over.mk f)) (G : EtaleModules.{u, 0} Λ X)
    (hloc : ∀ (V : Scheme.{u}) (e : V ⟶ X) [IsOpenImmersion e], IsClosed (Set.range e.base) →
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ V.smallEtaleTopology
        ((etaleModuleRestriction.{u, 0} Λ e).obj G)) :
    IsZero ((compactSupportSheafCohomology Λ f J kbar 0).obj G) := by
  classical
  have : IsLocallyNoetherian X := (inferInstance : IsNoetherian X).toIsLocallyNoetherian
  have : LocallyConnectedSpace X := Scheme.locallyConnectedSpace_of_isLocallyNoetherian X
  let Z : _root_.ConnectedComponents X → X.Opens := X.connectedComponentOpens
  have hdisj : Pairwise fun i j => Disjoint (Z i) (Z j) := fun i j h =>
    X.disjoint_connectedComponentOpens h
  have hclosed : ∀ i, IsClosed (Z i : Set X) := X.isClosed_connectedComponentOpens
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun i => (Z i : Set X))
    (fun i => (Z i).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨ConnectedComponents.mk x, rfl⟩)
  have hsne : s.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact ⟨i, hi⟩
  have hleaf : ∀ (V : Scheme.{u}) (e : V ⟶ X) [IsOpenImmersion e]
      (i : _root_.ConnectedComponents X),
      Set.range e.base = Z i → ∀ (g : V ⟶ Spec (.of k)), g = e ≫ f →
        ∀ J' : CompactificationOf (Over.mk g),
          IsZero ((compactSupportSheafCohomology Λ g J' kbar 0).obj
            ((etaleModuleRestriction.{u, 0} Λ e).obj G)) := by
    intro V e _ i he g hg J'
    subst hg
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
    have hZ : (Z (ConnectedComponents.mk x) : Set X) = connectedComponent x := by
      show ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x} = _
      exact connectedComponents_preimage_singleton
    have : IsClosedImmersion e := .of_isPreimmersion _ (by
      rw [he]; exact hclosed _)
    have : IsAffine V := isAffine_of_isAffineHom e
    have : Nonempty V := by
      obtain ⟨v, hv⟩ : x ∈ Set.range e.base := by rw [he, hZ]; exact mem_connectedComponent
      exact ⟨v⟩
    have : ConnectedSpace V := by
      refine connectedSpace_iff_univ.2 ⟨Set.univ_nonempty, ?_⟩
      refine e.isOpenEmbedding.isInducing.isPreconnected_image.1 ?_
      rw [Set.image_univ, he, hZ]
      exact isPreconnected_connectedComponent
    have : SmoothOfRelativeDimension 1 (e ≫ f) := by
      have : SmoothOfRelativeDimension (0 + 1) (e ≫ f) := inferInstance
      rwa [zero_add] at this
    have : Smooth (e ≫ f) := SmoothOfRelativeDimension.smooth 1 _
    have : IsIntegral V := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (e ≫ f)
    have : IsCurve k (e ≫ f) :=
      { topologicalKrullDim_eq_one :=
          topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 (e ≫ f) }
    exact isZero_compactSupportFrobeniusCohomologyGroup_zero_of_isFiniteTypeLocallyConstant
      (e ≫ f) J' kbar Λ _ (hloc V e (by rw [he]; exact hclosed _))
  have h := isZero_compactSupportSheafCohomology_zero_of_partition Λ kbar f Z hdisj hclosed G
    hleaf s hsne X (𝟙 X) (by
      refine Set.Subset.antisymm (fun _ _ => hs (Set.mem_univ _)) (fun _ _ => ?_)
      exact ⟨_, rfl⟩) f (Category.id_comp f).symm J
  exact h.of_iso ((compactSupportSheafCohomology Λ f J kbar 0).mapIso
    ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ (𝟙 X)).symm.app G ≪≫
      (etaleModuleInverseImageIdIso (Λ := Λ) X).app G).symm)

end Level

section LAdic

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

/-- The levels of a lisse ℓ-adic sheaf, read on Mathlib's small étale site, restrict to locally
constant sheaves of finite type on every open subscheme with closed image: the restriction is
the level of the inverse image, which is lisse. -/
theorem LAdicSheaf.isFiniteTypeLocallyConstant_restriction_etaleLevel (F : LAdicSheaf B X ℓ)
    (hF : F.IsLisse) (n : ℕ) (V : Scheme.{u}) (e : V ⟶ X.1) [IsOpenImmersion e]
    (hcl : IsClosed (Set.range e.base)) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1))) V.smallEtaleTopology
      ((etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (n + 1))) e).obj
        (LAdicSheaf.etaleLevel B X ℓ F n)) := by
  have hV : B.Contains V := Scheme.size_lt_of_isOpenImmersion e X.2
  let VB : B.Scheme := B.obj V hV
  let eB : VB ⟶ X := ObjectProperty.homMk e
  have : IsClosedImmersion e := .of_isPreimmersion _ hcl
  have : IsLocallyNoetherian X.1 := (inferInstance : IsNoetherian X.1).toIsLocallyNoetherian
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion e
  have : CompactSpace V := e.isClosedEmbedding.compactSpace
  have : IsNoetherian VB.1 := (⟨⟩ : IsNoetherian V)
  have h1 := LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse
    (LAdicSheaf.inverseImage eB F) (hF.inverseImage eB) n
  have h2 := (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_functor_iff B VB
    (ZMod (ℓ ^ (n + 1))) _).2 h1
  refine Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ _ ?_ h2
  exact ((SmallEtale.sheafEquivPullbackBaseChangeIso B eB
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (etaleModuleInverseImageAdj.{u, 0} (ZMod (ℓ ^ (n + 1))) (B.inclusion.map eB))
      ((AlgebraicGeometry.smallEtaleBaseChange B eB).sheafAdjunctionContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) _ _)).app (F.level n)).symm ≪≫
    (etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod (ℓ ^ (n + 1))) e).app _

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

namespace LAdicSheaf

/-- **`H⁰_c(X_k̄, F ⊗ ℚ_ℓ) = 0` for a lisse ℓ-adic sheaf on a smooth affine curve over a finite
field, connected or not** ([Tag 03VL](https://stacks.math.columbia.edu/tag/03VL), last
assertion, for every component): every level `H⁰_c(X_k̄, Fₙ)` vanishes. -/
theorem subsingleton_rationalGeometricCompactlySupportedCohomology_zero_of_smoothOfRelativeDimension
    [Nonempty X.1] [IsAffine X.1] [SmoothOfRelativeDimension 1 f] [IsAlgClosed kbar]
    (F : LAdicSheaf B X ℓ) (hF : F.IsLisse) :
    Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F 0) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hlevel (n : ℕ) : IsZero
      ((LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F 0).obj (op n)) := by
    have h := isZero_compactSupportSheafCohomology_zero_of_smoothOfRelativeDimension
      (ZMod (ℓ ^ (n + 1))) kbar f j (LAdicSheaf.etaleLevel B X ℓ F n)
      (fun V e _ hcl => LAdicSheaf.isFiniteTypeLocallyConstant_restriction_etaleLevel B X ℓ F hF n
        V e hcl)
    exact ((ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).map_isZero h).of_iso
      ((compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) 0).mapIso
        (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n) ≪≫
      (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso (PadicInt.toZModPow (n + 1)) f j
        kbar (LAdicSheaf.levelComplex B X ℓ F n) 0).symm)
  have hlim : IsZero (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F 0) :=
    (IsZero.iff_id_eq_zero _).2 (limit.hom_ext fun n => (hlevel n.unop).eq_of_tgt _ _)
  exact ModuleCat.subsingleton_of_isZero (Functor.map_isZero _ hlim)

end LAdicSheaf

end LAdic

end Stacks.EtaleCohomology

end
