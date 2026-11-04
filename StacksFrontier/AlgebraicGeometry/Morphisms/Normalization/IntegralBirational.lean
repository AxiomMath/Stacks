module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme

/-!
# Normalization through an integral birational morphism

Let `α : X' ⟶ X` be an integral morphism which is birational over every quasi-compact open of
`X`, and suppose that the inverse images of such opens have finitely many irreducible
components. Then the normalization of `X` factors through `X'`, and that factorization is a
normalization of `X'`: normalizing cannot see the difference between `X` and `X'`.

Birationality over every quasi-compact open upgrades to birationality of `α` itself, because
both halves of the definition are checked at generic points and every point lies in a
quasi-compact open. Birationality then identifies the two generic-point residue spectra
compatibly with the maps to `X` and `X'`, and the universal property of relative normalization
does the rest.

## Main results

* `AlgebraicGeometry.exists_normalizationFactorization_of_isIntegralHom_of_isBirational`: the
  normalization factors through the integral birational morphism, and is isomorphic over `X'`
  to the normalization of its source.
* `AlgebraicGeometry.exists_normalizationFactorization_of_integral_of_birational`: the same
  statement with birationality assumed only over each quasi-compact open.

## Implementation notes

Being a normalization is expressed by an isomorphism to the chosen normalization which commutes
with the two normalization morphisms. The proof of the local finiteness condition for all
quasi-compact opens of `X'` is included among the existential data, since the hypotheses supply
it only for inverse images of quasi-compact opens of `X`.

## References

* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

private theorem exists_compact_affineOpen_mem (X : Scheme.{u}) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsCompact (U : Set X) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨U, hxU, hU.isCompact⟩

private theorem isBirational_resLE_of_locally_birational
    {X X' : Scheme.{u}} (α : X' ⟶ X)
    (hbirational : ∀ U : X.Opens, IsCompact (U : Set X) →
      IsBirational (α ∣_ U))
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    IsBirational (α.resLE U (α ⁻¹ᵁ U) le_rfl) := by
  simpa [Scheme.Hom.resLE_eq_morphismRestrict] using hbirational U hU

private theorem bijOn_genericPoints_of_locally_birational
    {X X' : Scheme.{u}} (α : X' ⟶ X)
    (hbirational : ∀ U : X.Opens, IsCompact (U : Set X) →
      IsBirational (α ∣_ U)) :
    Set.BijOn α (genericPoints X') (genericPoints X) := by
  classical
  let restricted (U : X.Opens) := α.resLE U (α ⁻¹ᵁ U) le_rfl
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := exists_compact_affineOpen_mem X (α x)
    have hr := isBirational_resLE_of_locally_birational α hbirational U hU
    let Es := Scheme.genericPointsInOpenEquiv X' (α ⁻¹ᵁ U)
    let Et := Scheme.genericPointsInOpenEquiv X U
    let η : genericPoints X' := ⟨x, hx⟩
    let ηU := Es ⟨η, by simpa using hxU⟩
    have hηU : restricted U ηU.1 ∈ genericPoints (U : Set X) :=
      (IsBirational.bijOn hr).1 ηU.2
    let ξ := Et.symm ⟨restricted U ηU.1, hηU⟩
    have hξ : ξ.1.1 = α x := by
      rw [Scheme.genericPointsInOpenEquiv_symm_val X U ⟨restricted U ηU.1, hηU⟩]
      show (restricted U ηU.1).1 = α ηU.1.1
      simp [restricted, Scheme.Hom.coe_resLE_apply]
    simpa [hξ] using ξ.1.2
  · intro x hx y hy hxy
    obtain ⟨U, hxyU, hU⟩ := exists_compact_affineOpen_mem X (α x)
    have hr := isBirational_resLE_of_locally_birational α hbirational U hU
    have hyU : α y ∈ U := hxy ▸ hxyU
    let Es := Scheme.genericPointsInOpenEquiv X' (α ⁻¹ᵁ U)
    let η : genericPoints X' := ⟨x, hx⟩
    let ζ : genericPoints X' := ⟨y, hy⟩
    let ηU := Es ⟨η, by simpa using hxyU⟩
    let ζU := Es ⟨ζ, by simpa using hyU⟩
    have hrEq : restricted U ηU.1 = restricted U ζU.1 := by
      apply Subtype.ext
      simp only [restricted, Scheme.Hom.coe_resLE_apply]
      exact hxy
    have hηζ : ηU = ζU :=
      Subtype.ext ((IsBirational.bijOn hr).2.1 ηU.2 ζU.2 hrEq)
    exact congrArg (·.1.1) (Es.injective hηζ)
  · intro y hy
    obtain ⟨U, hyU, hU⟩ := exists_compact_affineOpen_mem X y
    have hr := isBirational_resLE_of_locally_birational α hbirational U hU
    let Es := Scheme.genericPointsInOpenEquiv X' (α ⁻¹ᵁ U)
    let Et := Scheme.genericPointsInOpenEquiv X U
    let ηU := Et ⟨⟨y, hy⟩, hyU⟩
    obtain ⟨ξU, hξUmem, hξU⟩ := (IsBirational.bijOn hr).2.2 ηU.2
    let ξ := Es.symm ⟨ξU, hξUmem⟩
    refine ⟨ξ.1.1, ξ.1.2, ?_⟩
    rw [show ξ.1.1 = ξU.1 from Scheme.genericPointsInOpenEquiv_symm_val X' (α ⁻¹ᵁ U) _]
    show α ξU.1 = ηU.1.1
    rw [← hξU]
    exact (Scheme.Hom.coe_resLE_apply (f := α) (U := U) (V := α ⁻¹ᵁ U) (e := le_rfl) ξU).symm

private theorem isBirational_of_locally_birational
    {X X' : Scheme.{u}} (α : X' ⟶ X)
    (hbirational : ∀ U : X.Opens, IsCompact (U : Set X) →
      IsBirational (α ∣_ U)) :
    IsBirational α := by
  apply isBirational_of_bijOn_of_isIso_stalkMap α
    (bijOn_genericPoints_of_locally_birational α hbirational)
  intro x hx
  obtain ⟨U, hxU, hU⟩ := exists_compact_affineOpen_mem X (α x)
  let ηU := Scheme.genericPointsInOpenEquiv X' (α ⁻¹ᵁ U) ⟨⟨x, hx⟩, by simpa using hxU⟩
  exact (Arrow.isIso_iff_isIso_of_isIso (α.resLEStalkMap (e := le_rfl) ηU.1).hom).mp
    ((isBirational_resLE_of_locally_birational α hbirational U hU).isIso_stalkMap ηU.1 ηU.2)

private theorem finite_irreducibleComponents_of_isOpenEmbedding
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (f : A → B) (hf : Topology.IsOpenEmbedding f)
    (hB : (irreducibleComponents B).Finite) :
    (irreducibleComponents A).Finite := by
  choose D hD hsub using fun C : irreducibleComponents A =>
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure (f '' C.1)) (C.2.1.image f hf.continuous.continuousOn).closure
  have hpreimage (C : irreducibleComponents A) : f ⁻¹' D C = C.1 := by
    have hCsub : C.1 ⊆ f ⁻¹' D C := fun x hx => hsub C (subset_closure ⟨x, hx, rfl⟩)
    obtain ⟨x, hx⟩ := C.2.1.nonempty
    have hpre := preimage_mem_irreducibleComponents (hD C) hf ⟨f x, hCsub hx, x, rfl⟩
    exact (C.2.2 hpre.1 hCsub).antisymm hCsub
  have hinj : Function.Injective fun C => (⟨D C, hD C⟩ : irreducibleComponents B) :=
    fun C C' h => Subtype.ext <|
      (hpreimage C).symm.trans <| (congrArg (f ⁻¹' ·.1) h).trans (hpreimage C')
  have := hB.to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_injective _ hinj)

private theorem finite_irreducibleComponents_of_locally_finite_preimages
    {X X' : Scheme.{u}} (α : X' ⟶ X)
    (hcomponents : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents (α ⁻¹ᵁ U)).Finite)
    (V : X'.Opens) (hV : IsCompact (V : Set X')) :
    (irreducibleComponents V).Finite := by
  obtain ⟨s, hs⟩ := (hV.image α.continuous).elim_finite_subcover
    (fun i : X.affineOpens => (i : Set X)) (fun i => i.1.isOpen)
    fun x _ => Set.mem_iUnion.mpr (X.isBasis_affineOpens.isOpenCover.exists_mem x)
  let U : X.Opens := ⨆ i : s, (i.1 : X.Opens)
  have hUc : IsCompact (U : Set X) := by
    rw [Opens.coe_iSup]
    exact isCompact_iUnion fun i => i.1.2.isCompact
  let A : X'.Opens := α ⁻¹ᵁ U
  have hVA : V ≤ A := by
    intro x hx
    show α.base x ∈ (U : Set X)
    rw [Opens.coe_iSup]
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs ⟨x, hx, rfl⟩)
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  let f : V → A := fun x => ⟨x.1, hVA x.2⟩
  have hf : Topology.IsOpenEmbedding f := .of_comp f A.isOpen.isOpenEmbedding_subtypeVal
    V.isOpen.isOpenEmbedding_subtypeVal
  exact finite_irreducibleComponents_of_isOpenEmbedding f hf (hcomponents U hUc)

private theorem isIso_residueFieldMap_of_isIso_stalkMap
    {X X' : Scheme.{u}} (α : X' ⟶ X) (x : X')
    (h : IsIso (α.stalkMap x)) : IsIso (α.residueFieldMap x) :=
  (IsLocalRing.ResidueField.mapEquiv
    (asIso (α.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

private theorem genericPointResidueSpectrum_iso
    {X X' : Scheme.{u}} (α : X' ⟶ X)
    (hα : IsBirational α) :
    ∃ e : Scheme.genericPointResidueSpectrum X' ≅
        Scheme.genericPointResidueSpectrum X,
      e.hom ≫ Scheme.fromGenericPointResidueFields X =
        Scheme.fromGenericPointResidueFields X' ≫ α := by
  classical
  let hbij := IsBirational.bijOn hα
  let pointMap : genericPoints X' → genericPoints X := fun ξ =>
    ⟨α ξ.1, hbij.1 ξ.2⟩
  have pointMap_bijective : Function.Bijective pointMap := hbij.bijective
  let pointsEquiv : genericPoints X' ≃ genericPoints X :=
    Equiv.ofBijective pointMap pointMap_bijective
  let sourceFamily := fun ξ : genericPoints X' =>
    Spec (.of (X'.residueField ξ.1))
  let targetFamily := fun η : genericPoints X =>
    Spec (.of (X.residueField η.1))
  let reindex : Discrete (genericPoints X') ⥤ Discrete (genericPoints X) :=
    (Discrete.equivalence pointsEquiv).functor
  let reindexPointVal (ξ : genericPoints X') : genericPoints X :=
    (reindex.obj (Discrete.mk ξ)).as
  have pointMap_reindex (ξ : genericPoints X') : α ξ.1 = (reindexPointVal ξ).1 := rfl
  let residueIso (ξ : genericPoints X') :
      X.residueField (reindexPointVal ξ).1 ≅ X'.residueField ξ.1 := by
    have := isIso_residueFieldMap_of_isIso_stalkMap α ξ.1 (hα.isIso_stalkMap ξ.1 ξ.2)
    exact (X.residueFieldCongr (pointMap_reindex ξ)).symm ≪≫
      asIso (α.residueFieldMap ξ.1)
  let targetReindexed := fun ξ : genericPoints X' => targetFamily (reindexPointVal ξ)
  let componentIso (ξ : genericPoints X') : sourceFamily ξ ≅ targetReindexed ξ :=
    AlgebraicGeometry.Scheme.Spec.mapIso (residueIso ξ).op
  let targetDiagram := Discrete.functor targetFamily
  let targetReindexedDiagram := Discrete.functor targetReindexed
  let reindexNatIso : targetReindexedDiagram ≅ reindex ⋙ targetDiagram :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  let eComponents := Limits.Sigma.mapIso componentIso
  let eReindexCoproduct := Limits.HasColimit.isoOfNatIso reindexNatIso
  let eReindex := Functor.Final.colimitIso reindex targetDiagram
  let e : Scheme.genericPointResidueSpectrum X' ≅
      Scheme.genericPointResidueSpectrum X := by
    show (∐ sourceFamily) ≅ (∐ targetFamily)
    exact eComponents ≪≫ eReindexCoproduct ≪≫ eReindex
  have residueIso_fromSpec (ξ : genericPoints X') :
      AlgebraicGeometry.Spec.map (residueIso ξ).hom ≫
        X.fromSpecResidueField (reindexPointVal ξ).1 =
      AlgebraicGeometry.Spec.map (α.residueFieldMap ξ.1) ≫
        X.fromSpecResidueField (α ξ.1) := by
    dsimp [residueIso]
    rw [AlgebraicGeometry.Spec.map_comp, Category.assoc,
      Scheme.residueFieldCongr_fromSpecResidueField (pointMap_reindex ξ).symm]
  have hcomm : e.hom ≫ Scheme.fromGenericPointResidueFields X =
      Scheme.fromGenericPointResidueFields X' ≫ α := by
    let cover : (∐ sourceFamily).OpenCover :=
      Scheme.Cover.copy
        (Scheme.IsLocallyDirected.openCover (Discrete.functor sourceFamily))
        (genericPoints X') sourceFamily (Limits.Sigma.ι sourceFamily)
        discreteEquiv.symm (fun _ => Iso.refl _) (by intro ξ; rfl)
    apply Scheme.Cover.hom_ext cover
    intro ξ
    dsimp only [cover] at ξ
    change genericPoints X' at ξ
    show Limits.Sigma.ι sourceFamily ξ ≫ e.hom ≫
        Scheme.fromGenericPointResidueFields X =
      Limits.Sigma.ι sourceFamily ξ ≫
        Scheme.fromGenericPointResidueFields X' ≫ α
    dsimp [e, eComponents, Scheme.genericPointResidueSpectrum,
      Scheme.fromGenericPointResidueFields]
    have hreindex : reindexNatIso.hom.app (Discrete.mk ξ) = 𝟙 _ := rfl
    simp only [Category.assoc]
    rw [Limits.Sigma.ι_mapIso_hom_assoc, Limits.HasColimit.isoOfNatIso_ι_hom_assoc,
      Functor.Final.ι_colimitIso_hom_assoc, hreindex, Category.id_comp]
    simp only [Limits.Sigma.ι_desc_assoc, componentIso, Functor.mapIso_hom,
      AlgebraicGeometry.Scheme.Spec_map, Iso.op_hom, Opposite.unop_op]
    dsimp [targetDiagram]
    rw [Limits.Sigma.ι_desc, residueIso_fromSpec]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField α ξ.1
  exact ⟨e, hcomm⟩

/-- An integral birational morphism does not change the normalization. -/
theorem exists_normalizationFactorization_of_isIntegralHom_of_isBirational
    {X X' : Scheme.{u}} (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite) (α : X' ⟶ X) [IsIntegralHom α]
    (hcomponents : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents (α ⁻¹ᵁ U)).Finite)
    (hbirational : IsBirational α) :
    ∃ (hX' : ∀ V : X'.Opens, IsCompact (V : Set X') →
        (irreducibleComponents V).Finite)
      (g : Scheme.normalizationScheme X hX ⟶ X')
      (e : Scheme.normalizationScheme X hX ≅
        Scheme.normalizationScheme X' hX'),
      g ≫ α = Scheme.normalization X hX ∧
        e.hom ≫ Scheme.normalization X' hX' = g := by
  classical
  let := Scheme.quasiCompactFromGenericPointResidueFields X hX
  let := Scheme.quasiSeparatedFromGenericPointResidueFields X
  let hX' : ∀ V : X'.Opens, IsCompact (V : Set X') →
      (irreducibleComponents V).Finite := fun V hV =>
    finite_irreducibleComponents_of_locally_finite_preimages α hcomponents V hV
  let := Scheme.quasiCompactFromGenericPointResidueFields X' hX'
  let := Scheme.quasiSeparatedFromGenericPointResidueFields X'
  let f := Scheme.fromGenericPointResidueFields X
  let f' := Scheme.fromGenericPointResidueFields X'
  obtain ⟨E, hE⟩ := genericPointResidueSpectrum_iso α hbirational
  let g₀ : Scheme.genericPointResidueSpectrum X ⟶ X' := E.inv ≫ f'
  have hfactor : f = g₀ ≫ α := by simp [g₀, f, f', ← hE]
  let g := f.normalizationDesc g₀ α hfactor
  have hgComp : g ≫ α = f.fromNormalization := f.normalizationDesc_comp g₀ α hfactor
  have hi : (E.hom ≫ f.toNormalization) ≫ g = f' := by
    rw [Category.assoc, f.toNormalization_normalizationDesc g₀ α hfactor]
    simp [g₀]
  have hUP : ∀ (T : Scheme.{u}) (j : Scheme.genericPointResidueSpectrum X' ⟶ T)
      (q : T ⟶ X'), IsIntegralHom q → j ≫ q = f' →
        ∃! k : Scheme.normalizationScheme X hX ⟶ T,
          (E.hom ≫ f.toNormalization) ≫ k = j ∧ k ≫ q = g := by
    intro T j q hq hj
    let j₀ : Scheme.genericPointResidueSpectrum X ⟶ T := E.inv ≫ j
    have hj₀ : j₀ ≫ q = g₀ := by dsimp [j₀, g₀]; rw [Category.assoc, hj]
    obtain ⟨k, hk, hku⟩ :=
      Scheme.Hom.normalizationDesc_universalProperty
        f g₀ α hfactor T j₀ q hq hj₀
    refine ⟨k, ⟨?_, hk.2⟩, fun k' hk' => hku k' ⟨?_, hk'.2⟩⟩
    · rw [Category.assoc, hk.1]
      simp [j₀]
    · dsimp only [j₀]
      rw [← hk'.1]
      simp
  obtain ⟨e, he, _⟩ :=
    (Scheme.Hom.normalization_universalProperty_iff_existsUnique_iso
      f' (E.hom ≫ f.toNormalization) g hi).1 hUP
  refine ⟨hX', g, e, ?_, ?_⟩
  · simpa [Scheme.normalization, f] using hgComp
  · simpa [Scheme.normalization, f'] using he.2

/-- **Stacks Project, Tag 035Q.** An integral morphism which is birational over every
quasi-compact open does not change the normalization. -/
@[stacks 035Q "normalization_integral_birational"]
theorem exists_normalizationFactorization_of_integral_of_birational
    {X X' : Scheme.{u}} (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite) (α : X' ⟶ X) [IsIntegralHom α]
    (hcomponents : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents (α ⁻¹ᵁ U)).Finite)
    (hbirational : ∀ U : X.Opens, IsCompact (U : Set X) →
      IsBirational (α ∣_ U)) :
    ∃ (hX' : ∀ V : X'.Opens, IsCompact (V : Set X') →
        (irreducibleComponents V).Finite)
      (g : Scheme.normalizationScheme X hX ⟶ X')
      (e : Scheme.normalizationScheme X hX ≅
        Scheme.normalizationScheme X' hX'),
      g ≫ α = Scheme.normalization X hX ∧
        e.hom ≫ Scheme.normalization X' hX' = g :=
  exists_normalizationFactorization_of_isIntegralHom_of_isBirational hX α hcomponents
    (isBirational_of_locally_birational α hbirational)

end AlgebraicGeometry
