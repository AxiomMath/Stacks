module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.SecondCentreChart
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendIdealSheaf
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.FiniteTypeIdealSheaf

/-!
# The second centre of a two-step blowup, descended to the base

Let `S` be a quasi-compact and quasi-separated scheme, `ℐ` a finite type quasi-coherent sheaf of
ideals on `S` and `b : X' ⟶ S` the blowup of `S` in `ℐ`, with exceptional ideal `E = ℐ·𝒪_{X'}`.
Let `𝒦` be a finite type quasi-coherent sheaf of ideals on `X'`. This file produces a `d > 0`
and a finite type quasi-coherent sheaf of ideals `J ⊆ ℐ ^ d` on `S` with

  `J·𝒪_{X'} = E ^ d · 𝒦`,

together with the containment `Supp J ⊆ Supp ℐ ∪ b(Supp 𝒦)`.

That pair `(d, J)` is what the composition theorem for admissible blowups, [Stacks, Tag 080L],
consumes: it is the ideal-sheaf form of Stacks Lemma 31.32.5 ([Stacks, Tag 0803]) applied to the
Rees algebra `⨁ ℐⁿ`. No `@[stacks 0803]` attribute is attached here, because Tag 0803 is a
statement about a submodule of one graded piece of an arbitrary quasi-coherent graded algebra and
what is proved here is only the consequence for the Rees algebra of an ideal sheaf.

## Main results

* `Stacks.Blowup.exists_factorization`: the pair `(d, J)`, phrased with
  `Stacks.Blowup.blowUp`.
* `Stacks.Blowup.exists_factorization_blowUp`: the same, phrased with
  `AlgebraicGeometry.blowUp` and with the support clause in the stalkwise form, which is exactly
  the hypothesis `secondCentreIdeal` of
  `Stacks.Blowup.IsAdmissibleBlowup.comp_of_secondCentreIdeal`.
* `Stacks.Blowup.mem_ideal_map_of_forall_le`: a section of the base over an affine open lies in
  the direct image of an ideal sheaf as soon as its pullback to each member of a cover of the
  preimage does.
* `Stacks.Blowup.supportSet_subset_of_comap_eq`: the support clause, for any `J` whose inverse
  image is `E ^ d · 𝒦`.

## Implementation notes

The construction is local on `S` only in the sense that the *generators* of `J` are produced one
affine open at a time, by `Stacks.Blowup.exists_fg_le_pow_and_map_chartStructureMap_eq`; the
ideal sheaf `J` itself cannot be glued from them, since the local ideals do not agree on
overlaps. What makes a global `J` out of them is the ambient quasi-coherent ideal sheaf

  `𝒢 = (E ^ d · 𝒦)_* ⊓ ℐ ^ d`,

the direct image being `AlgebraicGeometry.Scheme.IdealSheafData.map`, the right adjoint of
`comap`. Being contained in `𝒢` is exactly the two inequalities `J ⊆ ℐ ^ d` and
`J·𝒪_{X'} ⊆ E ^ d · 𝒦`, the second by the Galois connection
`AlgebraicGeometry.Scheme.IdealSheafData.le_map_iff_comap_le`. Each local generator is shown to
lie in `𝒢` — this is where `Stacks.Blowup.mem_ideal_map_of_forall_le` is used, the direct image
being a kernel and the vanishing of a section being checked on the chart cover — and then
`Stacks.IdealSheaf.exists_fg_le_of_mem`, Tag 01PF for sheaves of ideals, replaces each generator
by a finite type subsheaf of `𝒢` containing it. The supremum of those finitely many subsheaves
is `J`: it is of finite type, it is contained in `𝒢`, and on each chart its ideal contains the
local ideal, which gives the reverse inclusion `J·𝒪_{X'} ⊇ E ^ d · 𝒦`.

The degrees produced over different affine opens differ, so
`Stacks.Blowup.exists_pos_forall_ge_fg_le_pow_and_map_chartStructureMap_eq` is used instead: it
allows the degree to be raised freely, and the common degree is one more than the supremum over
the finite cover.

The support clause is cheaper than it looks. Outside the support of `ℐ` the blowup morphism is an
isomorphism, hence surjective there (`Stacks.Blowup.compl_support_subset_range`), so a point of
`Supp J` outside `Supp ℐ` has a preimage; that preimage lies in
`Supp (J·𝒪_{X'}) = Supp E ∪ Supp 𝒦 = b⁻¹(Supp ℐ) ∪ Supp 𝒦` and not in the first part, so it
lies in `Supp 𝒦`.

## References

* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)
* [Stacks Project, Tag 080L](https://stacks.math.columbia.edu/tag/080L)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits CommRingCat

universe u

namespace Stacks.Blowup

variable {S : Scheme.{u}}

section MapMembership

variable {X' Y : Scheme.{u}}

/-- **Membership in the direct image of an ideal sheaf, tested on a cover.** A section of the
base over an affine open lies in the direct image of an ideal sheaf as soon as its pullback to
each member of a cover of the preimage lies in that ideal sheaf. -/
theorem mem_ideal_map_of_forall_le (f : X' ⟶ Y) [QuasiCompact f] (𝒜 : X'.IdealSheafData)
    (W : Y.affineOpens) (y : Γ(Y, W.1)) {ι : Type*} (V : ι → X'.affineOpens)
    (hV : ∀ i, (V i).1 ≤ f ⁻¹ᵁ W.1) (hcov : f ⁻¹ᵁ W.1 ≤ ⨆ i, (V i).1)
    (hy : ∀ i, (f.appLE W.1 (V i).1 (hV i)).hom y ∈ 𝒜.ideal (V i)) :
    y ∈ (𝒜.map f).ideal W := by
  change y ∈ (𝒜.subschemeι ≫ f).ker.ideal W
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  refine 𝒜.subscheme.IsSheaf.section_ext (U := Opposite.op ((𝒜.subschemeι ≫ f) ⁻¹ᵁ W.1)) ?_
  intro x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (hcov (show 𝒜.subschemeι x ∈ f ⁻¹ᵁ W.1 from hx))
  have hle : (𝒜.subschemeι ⁻¹ᵁ (V i).1) ≤ (𝒜.subschemeι ≫ f) ⁻¹ᵁ W.1 := by
    rw [Scheme.Hom.comp_preimage]
    exact ((TopologicalSpace.Opens.map 𝒜.subschemeι.base).map (homOfLE (hV i))).le
  refine ⟨_, hle, hi, ?_⟩
  have h2 : (𝒜.subschemeι ≫ f).appLE W.1 (𝒜.subschemeι ⁻¹ᵁ (V i).1) hle
      = f.appLE W.1 (V i).1 (hV i) ≫ 𝒜.subschemeι.app (V i).1 := by
    rw [← Scheme.Hom.appLE_eq_app 𝒜.subschemeι (U := (V i).1), Scheme.Hom.appLE_comp_appLE]
  rw [map_zero, ← CommRingCat.comp_apply, ← Scheme.Hom.appLE, h2, CommRingCat.comp_apply]
  exact RingHom.mem_ker.mp ((Scheme.IdealSheafData.ker_subschemeι_app 𝒜 (V i)).ge (hy i))

end MapMembership

/-- The complement of the centre is contained in the image of the blowup. -/
theorem compl_support_subset_range (ℐ : S.IdealSheafData) :
    ((ℐ.support.compl : S.Opens) : Set S) ⊆ Set.range (blowUpToBase ℐ).base := by
  intro x hx
  obtain ⟨y, hy⟩ := (blowUpToBase ℐ ∣_ ℐ.support.compl).homeomorph.surjective ⟨x, hx⟩
  refine ⟨y.1, ?_⟩
  simpa using congrArg Subtype.val hy

/-- **The support of a second centre.** If the inverse image of `J` on the blowup is
`E ^ d · 𝒦` with `d > 0`, then the support of `J` is contained in the union of the support of
the centre and the image of the support of `𝒦`. -/
theorem supportSet_subset_of_comap_eq {ℐ : S.IdealSheafData}
    {𝒦 : (blowUp ℐ).IdealSheafData} {J : S.IdealSheafData} {d : ℕ} (hd : 0 < d)
    (hcomap : J.comap (blowUpToBase ℐ) = exceptionalIdeal ℐ ^ d * 𝒦) :
    J.supportSet ⊆ ℐ.supportSet ∪ (blowUpToBase ℐ).base '' 𝒦.supportSet := by
  have hexc : exceptionalIdeal ℐ = ℐ.comap (blowUpToBase ℐ) := rfl
  intro x hx
  by_cases hxI : x ∈ ℐ.supportSet
  · exact Or.inl hxI
  refine Or.inr ?_
  obtain ⟨y, rfl⟩ := compl_support_subset_range ℐ (show x ∈ (ℐ.supportSet)ᶜ from hxI)
  have h1 : y ∈ ((J.comap (blowUpToBase ℐ)).support : Set (blowUp ℐ)) := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hx
  rw [hcomap] at h1
  have h2 : y ∈ ((exceptionalIdeal ℐ ^ d).support : Set (blowUp ℐ)) ∪
      ((𝒦.support : Set (blowUp ℐ))) := by
    rw [← TopologicalSpace.Closeds.coe_sup, ← Scheme.IdealSheafData.support_mul]
    exact h1
  rcases h2 with h2 | h2
  · rw [Scheme.IdealSheafData.support_pow _ d hd.ne', hexc,
      Scheme.IdealSheafData.support_comap] at h2
    exact absurd h2 hxI
  · exact ⟨y, h2, rfl⟩

/-- The ideal of `E ^ D · 𝒦` on a chart of the blowup. -/
theorem ideal_exceptionalIdeal_pow_mul_chartOpens (ℐ : S.IdealSheafData) (W : S.affineOpens)
    {a : Γ(S, W.1)} (ha : a ∈ ℐ.ideal W) (𝒦 : (blowUp ℐ).IdealSheafData) (D : ℕ) :
    (exceptionalIdeal ℐ ^ D * 𝒦).ideal (chartOpens ℐ W ha)
      = Ideal.map (chartStructureMap ℐ W ha).hom (ℐ.ideal W) ^ D
        * 𝒦.ideal (chartOpens ℐ W ha) := by
  change ((exceptionalIdeal ℐ).ideal (chartOpens ℐ W ha)) ^ D * _ = _
  rw [show exceptionalIdeal ℐ = ℐ.comap (blowUpToBase ℐ) from rfl,
    ideal_comap_blowUpToBase_chartOpens]

/-- **The second-centre factorization on a quasi-compact quasi-separated base.** For a finite
type quasi-coherent ideal sheaf `ℐ` on `S` and a finite type quasi-coherent ideal sheaf `𝒦` on
the blowup of `S` in `ℐ`, there are a `d > 0` and a finite type quasi-coherent ideal sheaf
`J ⊆ ℐ ^ d` whose inverse image on the blowup is `E ^ d · 𝒦`. -/
theorem exists_factorization [CompactSpace S] [QuasiSeparatedSpace S]
    (ℐ : S.IdealSheafData) (hℐ : ℐ.IsFiniteType)
    (𝒦 : (blowUp ℐ).IdealSheafData) (h𝒦 : 𝒦.IsFiniteType) :
    ∃ (d : ℕ) (J : S.IdealSheafData), 0 < d ∧ J.IsFiniteType ∧ J ≤ ℐ ^ d ∧
      J.supportSet ⊆ ℐ.supportSet ∪ (blowUpToBase ℐ).base '' 𝒦.supportSet ∧
      J.comap (blowUpToBase ℐ) = exceptionalIdeal ℐ ^ d * 𝒦 := by
  classical
  have : QuasiCompact (AlgebraicGeometry.blowUpToBase ℐ) := quasiCompact_blowUpToBase hℐ
  have : QuasiCompact (blowUpToBase ℐ) := by
    rw [← blowUpIso_hom_comp ℐ]
    infer_instance
  have hcovuniv : (Set.univ : Set S) ⊆ ⋃ W : S.affineOpens, ((W.1 : S.Opens) : Set S) := by
    intro x _
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
  obtain ⟨t, ht⟩ := (isCompact_univ (X := (S : TopCat))).elim_finite_subcover
    (fun W : S.affineOpens ↦ ((W.1 : S.Opens) : Set S)) (fun W ↦ W.1.2) hcovuniv
  choose g hg using fun W : S.affineOpens ↦ hℐ W
  have hgspan : ∀ W : S.affineOpens,
      Ideal.span (Set.range fun i : {y // y ∈ g W} ↦ (i : Γ(S, W.1))) = ℐ.ideal W := by
    intro W
    rw [← hg W]
    congr 1
    exact Subtype.range_coe (s := (g W : Set Γ(S, W.1)))
  have hga : ∀ (W : S.affineOpens) (i : {y // y ∈ g W}), (i : Γ(S, W.1)) ∈ ℐ.ideal W :=
    fun W i ↦ (hgspan W).le (Ideal.subset_span ⟨i, rfl⟩)
  choose dW hdW hJW using fun W : S.affineOpens ↦
    exists_pos_forall_ge_fg_le_pow_and_map_chartStructureMap_eq ℐ W
      (fun i : {y // y ∈ g W} ↦ (i : Γ(S, W.1))) (hga W) (hℐ W) 𝒦 h𝒦
  set D : ℕ := t.sup dW + 1 with hD
  have hDge : ∀ W ∈ t, dW W ≤ D := fun W hW ↦ (Finset.le_sup hW).trans (Nat.le_succ _)
  have hDpos : 0 < D := Nat.succ_pos _
  choose JW hJWfg hJWle hJWchart using fun W : {W : S.affineOpens // W ∈ t} ↦
    hJW W.1 D (hDge W.1 W.2)
  choose gJ hgJ using fun W : {W : S.affineOpens // W ∈ t} ↦ hJWfg W
  have hcov : ∀ W : S.affineOpens,
      ⨆ i : {z // z ∈ g W}, (chartOpens ℐ W (hga W i)).1 = blowUpToBase ℐ ⁻¹ᵁ W.1 := fun W ↦ by
    simpa only [← Scheme.Hom.image_top_eq_opensRange] using
      iSup_opensRange_blowUpAffineChart_of_span ℐ W _ (hga W) (hgspan W)
  have hchart := fun (W : {W : S.affineOpens // W ∈ t}) i ↦
    (ideal_exceptionalIdeal_pow_mul_chartOpens ℐ W.1 (hga W.1 i) 𝒦 D).trans (hJWchart W i).symm
  set 𝒢 : S.IdealSheafData :=
    (exceptionalIdeal ℐ ^ D * 𝒦).map (blowUpToBase ℐ) ⊓ ℐ ^ D with h𝒢
  have hmemG : ∀ (W : {W : S.affineOpens // W ∈ t}) (y : {z // z ∈ gJ W}),
      (y : Γ(S, (W : S.affineOpens).1)) ∈ 𝒢.ideal W.1 := by
    intro W y
    have hyJ : (y : Γ(S, (W : S.affineOpens).1)) ∈ JW W := by
      rw [← hgJ W]
      exact Ideal.subset_span y.2
    refine ⟨?_, hJWle W hyJ⟩
    refine mem_ideal_map_of_forall_le (blowUpToBase ℐ) _ W.1 _
      (fun i : {z // z ∈ g W.1} ↦ chartOpens ℐ W.1 (hga W.1 i))
      (fun i ↦ chartOpens_le ℐ W.1 (hga W.1 i)) ?_ fun i ↦ ?_
    · exact (hcov W.1).ge
    · rw [hchart W i]
      exact Ideal.mem_map_of_mem _ hyJ
  choose Jsh hJshle hJshfg hJshmem using fun (W : {W : S.affineOpens // W ∈ t})
    (y : {z // z ∈ gJ W}) ↦
      Stacks.IdealSheaf.exists_fg_le_of_mem 𝒢 (W : S.affineOpens).2 (hmemG W y)
  have hcomap : (⨆ p : Σ W : {W : S.affineOpens // W ∈ t}, {z // z ∈ gJ W},
        Jsh p.fst p.snd).comap (blowUpToBase ℐ) = exceptionalIdeal ℐ ^ D * 𝒦 := by
    refine le_antisymm ?_ ?_
    · rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
      exact iSup_le fun p ↦ (hJshle p.fst p.snd).trans inf_le_left
    · refine Scheme.IdealSheafData.le_of_iSup_eq_top
        (fun q : Σ W : {W : S.affineOpens // W ∈ t}, {z // z ∈ g (W : S.affineOpens)} ↦
          chartOpens ℐ q.fst.1 (hga q.fst.1 q.snd)) ?_ fun q ↦ ?_
      · refine top_le_iff.mp fun x _ ↦ ?_
        obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ ((blowUpToBase ℐ).base x)))
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
          (show x ∈ ⨆ i : {z // z ∈ g W}, (chartOpens ℐ W (hga W i)).1 by
            rw [hcov W]
            exact hxW)
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, i⟩, hi⟩
      · rw [hchart q.fst q.snd, ideal_comap_blowUpToBase_chartOpens]
        refine Ideal.map_mono ?_
        rw [← hgJ q.fst]
        exact Ideal.span_le.mpr fun y hy ↦
          le_iSup (fun p : Σ W : {W : S.affineOpens // W ∈ t}, {z // z ∈ gJ W} ↦
            Jsh p.fst p.snd) ⟨q.fst, ⟨y, hy⟩⟩ q.fst.1 (hJshmem q.fst ⟨y, hy⟩)
  refine ⟨D, ⨆ p : Σ W : {W : S.affineOpens // W ∈ t}, {z // z ∈ gJ W}, Jsh p.fst p.snd,
    hDpos, ?_, ?_, supportSet_subset_of_comap_eq hDpos hcomap, hcomap⟩
  · intro V
    rw [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    exact Submodule.fg_iSup _ fun p ↦ hJshfg p.fst p.snd V
  · exact iSup_le fun p ↦ (hJshle p.fst p.snd).trans inf_le_right

/-- **The second-centre factorization for `AlgebraicGeometry.blowUp`.** For finitely presented
centres `I` on `S` and `Z'` on the blowup of `I`, there are `d > 0` and a finite type ideal sheaf
`J ≤ I ^ d`, agreeing stalkwise with `I ^ d` away from `I.supportSet` and the image of
`Z'.supportSet`, whose pullback to the blowup is `exceptionalIdeal I ^ d * Z'`. -/
theorem exists_factorization_blowUp [CompactSpace S] [QuasiSeparatedSpace S]
    (I : S.IdealSheafData)
    (hI : FinitePresentation I.subschemeι)
    (Z' : (AlgebraicGeometry.blowUp I).IdealSheafData)
    (hZ' : FinitePresentation Z'.subschemeι) :
    ∃ (d : ℕ) (J : S.IdealSheafData), 0 < d ∧
      Scheme.IdealSheafData.IsFiniteType J ∧ J ≤ I ^ d ∧
      (∀ x : S, x ∉ I.supportSet ∪
          (AlgebraicGeometry.blowUpToBase I).base '' Z'.supportSet →
        AlgebraicGeometry.IdealSheafData.stalk J x =
          AlgebraicGeometry.IdealSheafData.stalk (I ^ d) x) ∧
      J.comap (AlgebraicGeometry.blowUpToBase I)
        = AlgebraicGeometry.exceptionalIdeal I ^ d * Z' := by
  have hIft : I.IsFiniteType := (Stacks.Flatness.finitePresentation_subschemeι_iff I).mp hI
  have hZft : Z'.IsFiniteType := (Stacks.Flatness.finitePresentation_subschemeι_iff Z').mp hZ'
  obtain ⟨d, J, hd, hJft, hJle, hsupp, hcomap⟩ :=
    exists_factorization I hIft (Z'.comap (blowUpIso I).hom) (hZft.comap _)
  have hsurj : Function.Surjective ⇑(blowUpIso I).hom.base :=
    (blowUpIso I).hom.homeomorph.surjective
  have himg : (blowUpToBase I).base '' (Z'.comap (blowUpIso I).hom).supportSet
      = (AlgebraicGeometry.blowUpToBase I).base '' Z'.supportSet := by
    have hsc : (Z'.comap (blowUpIso I).hom).supportSet
        = ⇑(blowUpIso I).hom.base ⁻¹' Z'.supportSet :=
      congrArg (fun C : TopologicalSpace.Closeds (blowUp I) ↦ (C : Set (blowUp I)))
        (Scheme.IdealSheafData.support_comap Z' (blowUpIso I).hom)
    have hb : ⇑(blowUpToBase I).base
        = ⇑(AlgebraicGeometry.blowUpToBase I).base ∘ ⇑(blowUpIso I).hom.base := by
      rw [← blowUpIso_hom_comp I]
      rfl
    rw [hsc, hb, Set.image_comp, Set.image_preimage_eq _ hsurj]
  have hexceptional : exceptionalIdeal I
      = (AlgebraicGeometry.exceptionalIdeal I).comap (blowUpIso I).hom := by
    change I.comap (blowUpToBase I) = (I.comap (AlgebraicGeometry.blowUpToBase I)).comap _
    rw [← Scheme.IdealSheafData.comap_comp, blowUpIso_hom_comp]
  refine ⟨d, J, hd, hJft, hJle, ?_, ?_⟩
  · intro x hx
    rw [himg] at hsupp
    have hxJ : x ∉ J.supportSet := fun hmem ↦ hx (hsupp hmem)
    have h1 : AlgebraicGeometry.IdealSheafData.stalk J x = ⊤ :=
      (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_not_mem_support J x).mpr hxJ
    have h2 : AlgebraicGeometry.IdealSheafData.stalk (I ^ d) x = ⊤ := by
      refine (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_not_mem_support _ x).mpr ?_
      intro hmem
      rw [Scheme.IdealSheafData.support_pow I d hd.ne'] at hmem
      exact hx (Or.inl hmem)
    rw [h1, h2]
  · refine comap_injective_of_iso (blowUpIso I) ?_
    rw [← Scheme.IdealSheafData.comap_comp, blowUpIso_hom_comp, hcomap,
      Stacks.IdealSheaf.comap_mul, Stacks.IdealSheaf.comap_pow, ← hexceptional]

end Stacks.Blowup

end
