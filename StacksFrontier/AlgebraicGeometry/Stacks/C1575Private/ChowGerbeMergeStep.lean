module

public import StacksFrontier.AlgebraicGeometry.Stacks.C1575Private.ChowGerbeMergeHelpers
public import StacksFrontier.AlgebraicGeometry.Stacks.C1575Private.ChowGerbeIsomSpaceTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCompactificationSection
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeIsomTotalPresheafProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.SectionExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAtClosedPointExcision
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceExtension

/-!
# The section step of the proof of Stacks 0CQ7

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism from an algebraic stack to a quasi-compact
quasi-separated algebraic space, with all values in an open subspace `W ⊆ Y`, and let `V ⊆ Y` be a
quasi-compact open subspace. Suppose `W` is covered by quasi-compact opens `W_0, …, W_n`
containing `V`, carrying sections `x_k : W_k ⟶ 𝒳` of `f`, and that `x_0|_V ≅ x_k|_V` for every
`k`. Then the conclusion of [Stacks, Tag 0CQ7] holds for `(f, V)`.

This is the last part of the source's proof, from the situation labelled (f) there. The source
extends every `φ_{ij}` by Stacks 0CPI, makes `V` scheme-theoretically dense by a further blowup
so that the extensions satisfy the cocycle condition (Stacks 084N), and glues all `x_i` at once.
Here the opens are merged one pair at a time instead: Stacks 0CPI, applied to the proper
morphism `Isom(x_0, x_1) ⟶ W_0 ∩ W_1` (Stacks 0CPL) and the section over `V` given by
`x_0|_V ≅ x_1|_V`, extends that isomorphism over the inverse image of `W_0 ∩ W_1` in a
`V`-admissible blowup; gluing two members needs no cocycle condition; the glued section over
`W_0 ∪ W_1` is again isomorphic to `x_k` over `V`. After `n` such steps a single section over the
inverse image of `W` is left, and
`AlgebraicGeometry.Stack.AlgebraicStacks.HasProperCompactifiableCover.of_section_preimage`
concludes. The successive blowups are recorded as one proper morphism `p : Y' ⟶ Y`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge.MergeData`: the situation after some
  blowups, with `n + 1` opens left to merge.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge.MergeData.nonempty_merge`: one merge.
* The section step of Stacks 0CQ7:
  `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge.hasProperCompactifiableCover_of_sections`

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 0CPI](https://stacks.math.columbia.edu/tag/0CPI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Admissible blowups and quasi-compact opens -/

section Spaces

/-- A `U`-admissible blowup is an isomorphism over `U`. -/
theorem isIso_fromPreimage_of_isAdmissibleBlowup {X X' : AlgebraicSpaces B S hS}
    {U : Space.OpenSubspaces B S hS X.1} {b : X' ⟶ X} (hb : Space.IsAdmissibleBlowup B S hS U b) :
    IsIso (U.1.fromPreimage b.hom) := by
  obtain ⟨Z, -, hdisj, hbl⟩ := hb
  have hle : U.1 ≤ (Space.openComplementOfClosedSubspace B S hS X Z).1 := by
    refine Space.le_of_range_pointsMap_ι_subset B S hS
      (Space.openComplementOfClosedSubspace B S hS X Z).2 ?_
    change Space.subspacePointSet B S hS X.1 U.1 ⊆
      Space.subspacePointSet B S hS X.1 (Space.openComplementOfClosedSubspace B S hS X Z).1
    rw [Space.subspacePointSet_openComplement]
    exact hdisj.subset_compl_right
  exact Space.isIso_fromPreimage_of_le b.hom hle (Space.isIso_fromPreimage_openComplement hbl)

/-- Every point of `U` lifts to the inverse image of `U` in a `U`-admissible blowup. -/
theorem range_pointsMap_subset_of_isAdmissibleBlowup {X X' : AlgebraicSpaces B S hS}
    {U : Space.OpenSubspaces B S hS X.1} {b : X' ⟶ X} (hb : Space.IsAdmissibleBlowup B S hS U b)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : X.1 ⟶ Y) :
    Set.range (Space.pointsMap B S hS U.1.toFunctor (U.1.ι ≫ p)) ⊆
      Set.range (Space.pointsMap B S hS (U.1.preimage b.hom).toFunctor
        ((U.1.preimage b.hom).ι ≫ b.hom ≫ p)) := by
  have := isIso_fromPreimage_of_isAdmissibleBlowup hb
  rintro _ ⟨v, rfl⟩
  refine ⟨Space.pointsMap B S hS _ (inv (U.1.fromPreimage b.hom)) v, ?_⟩
  rw [← Space.pointsMap_comp_apply, ← Subfunctor.fromPreimage_ι_assoc, IsIso.inv_hom_id_assoc]

/-- The intersection of two quasi-compact open subspaces of a quasi-separated algebraic space is
quasi-compact. -/
theorem isQuasiCompactSpace_inf {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P)
    (hPqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal P) {A₀ A₁ : Subfunctor P}
    (h₀ : Space.IsOpenSubspace B S hS A₀)
    (h₀qc : Space.IsQuasiCompactSpace B S hS A₀.toFunctor)
    (h₁qc : Space.IsQuasiCompactSpace B S hS A₁.toFunctor) :
    Space.IsQuasiCompactSpace B S hS (A₀ ⊓ A₁).toFunctor := by
  have h := Space.isQuasiCompactSpace_preimage_toFunctor B S hS B.contains_terminal hP hPqs h₀.1
    h₀qc A₁ h₁qc A₀.ι
  refine Space.isQuasiCompactSpace_of_iso B S hS ?_ h
  exact
    { hom := { app := fun T => ↾fun z => ⟨z.1.1, z.1.2, z.2⟩ }
      inv := { app := fun T => ↾fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩ } }

end Spaces

/-! ### The situation with `n + 1` opens left to merge -/

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
  (W V : Subfunctor Y)

/-- **The situation of the section step of the proof of Stacks 0CQ7, after some blowups.** A
proper morphism `p : Y' ⟶ Y` from a quasi-compact quasi-separated algebraic space, a
quasi-compact open `V' ⊆ p⁻¹(W)` whose points map onto those of `V`, quasi-compact opens `W_k`
of `Y'` containing `V'` of which the first `n + 1` cover `p⁻¹(W)`, sections `x_k : W_k ⟶ 𝒳` of `f`
over `p`, and 2-isomorphisms `x_0|_{V'} ≅ x_k|_{V'}`. The family is indexed by `ℕ`; only its first
`n + 1` members are required to cover. -/
structure MergeData (n : ℕ) where
  /-- The modification of `Y`. -/
  Y' : AlgebraicSpaces B S hS
  qc : Space.IsQuasiCompactSpace B S hS Y'.1
  qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y'.1
  /-- The proper morphism to `Y`. -/
  p : Y'.1 ⟶ Y
  hp : Space.IsProper B S hS p
  /-- The open replacing `V`. -/
  V' : Space.OpenSubspaces B S hS Y'.1
  hV'qc : Space.IsQuasiCompactSpace B S hS V'.1.toFunctor
  hV : Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ⊆
    Set.range (Space.pointsMap B S hS V'.1.toFunctor (V'.1.ι ≫ p))
  hV'W : V'.1 ≤ W.preimage p
  /-- The opens carrying sections. -/
  Wi : ℕ → Space.OpenSubspaces B S hS Y'.1
  /-- Each open `Wi k` is quasi-compact. -/
  hWiqc : ∀ k, Space.IsQuasiCompactSpace B S hS (Wi k).1.toFunctor
  hcov : W.preimage p ≤ (⨆ k : Fin (n + 1), (Wi k).1).sheafify (BigFppfOver.topology B S hS)
  hVW : ∀ k, V'.1 ≤ (Wi k).1
  /-- The sections. -/
  x : ∀ k, algebraicSpaceStack.{u, w} B S hS (Wi k).1.toFunctor (Wi k).2.1 ⟶ 𝒳
  /-- Each section `x k` lies over the inclusion of `Wi k` followed by `p`. -/
  hx : ∀ k, Nonempty (x k ≫ f ≅
    algebraicSpaceStackMap.{u, w} B S hS (Wi k).2.1 hY ((Wi k).1.ι ≫ p))
  /-- The sections agree over `V'`: the restriction of `x 0` is isomorphic to that of `x k`. -/
  φ : ∀ k, Nonempty (algebraicSpaceStackMap.{u, w} B S hS V'.2.1 (Wi 0).2.1
      (Subfunctor.homOfLe (hVW 0)) ≫ x 0 ≅
    algebraicSpaceStackMap.{u, w} B S hS V'.2.1 (Wi k).2.1 (Subfunctor.homOfLe (hVW k)) ≫ x k)

variable {hY f W V}

/-- **One open left: the section over `p⁻¹(W)` solves Stacks 0CQ7.** -/
theorem MergeData.hasProperCompactifiableCover_zero (hf : IsSeparated B S hS f)
    (hW : Space.IsOpenSubspace B S hS W)
    (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ)))
    (D : MergeData hY f W V 0) : HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  have hsheaf := (isSheaf_iff_isSheaf_of_type _ _).1 D.Y'.2.isSheaf
  have hsheaf₀ := (isSheaf_iff_isSheaf_of_type _ _).1 (D.Wi 0).2.1.isSheaf
  have hle : W.preimage D.p ≤ (D.Wi 0).1 := by
    have e : (⨆ k : Fin (0 + 1), (D.Wi k).1) = (D.Wi 0).1 :=
      le_antisymm (iSup_le fun k => by
          rcases k with ⟨_ | k, hk⟩
          · exact le_rfl
          · exact absurd hk (by omega))
        (le_iSup_of_le (⟨0, by omega⟩ : Fin (0 + 1)) le_rfl)
    have h := D.hcov
    rw [e, ← Subfunctor.eq_sheafify _ hsheaf hsheaf₀] at h
    exact h
  have hW' := Space.isOpenSubspace_preimage B S hS D.p W hY D.Y'.2 hW
  obtain ⟨k⟩ := nonempty_comp_iso_of_iso hW'.1 (D.Wi 0).2.1 hY f (Subfunctor.homOfLe hle)
    (D.x 0) _ (D.hx 0)
  refine HasProperCompactifiableCover.of_section_preimage hY D.Y'.2 f hf W hW hfW D.p D.hp
    (algebraicSpaceStackMap.{u, w} B S hS hW'.1 (D.Wi 0).2.1 (Subfunctor.homOfLe hle) ≫ D.x 0)
    ⟨k ≪≫ eqToIso (by rw [Subfunctor.homOfLe_ι_assoc])⟩ V ?_
  intro v hv
  obtain ⟨w', rfl⟩ := D.hV hv
  refine ⟨Space.pointsMap B S hS _ (Subfunctor.homOfLe D.hV'W) w', ?_⟩
  rw [← Space.pointsMap_comp_apply, Subfunctor.homOfLe_ι_assoc]

/-- **One merge.** From `n + 2` opens, Stacks 0CPI extends the isomorphism `x_0|_{V'} ≅ x_1|_{V'}`
over the inverse image of `W_0 ∩ W_1` in a `V'`-admissible blowup `b : Y'' ⟶ Y'`
(`Isom(x_0, x_1) ⟶ W_0 ∩ W_1` being proper as `f` is separated, Stacks 0CPL); the pulled back
`x_0` and `x_1` then glue over the union of the inverse images of `W_0` and `W_1`, which together
with the inverse images of `W_2, …` gives the situation with `n + 1` opens over `b ≫ p`. -/
theorem MergeData.nonempty_merge (hf : IsSeparated B S hS f) {n : ℕ}
    (D : MergeData hY f W V (n + 1)) : Nonempty (MergeData hY f W V n) := by
  have hZt := B.contains_terminal
  have hZ01 := Space.isOpenSubspace_inf B S hS D.Y'.2 (D.Wi 0).1 (D.Wi 1).1 (D.Wi 0).2 (D.Wi 1).2
  let Z01 : Space.OpenSubspaces B S hS D.Y'.1 := ⟨(D.Wi 0).1 ⊓ (D.Wi 1).1, hZ01⟩
  have hZ01qc : Space.IsQuasiCompactSpace B S hS Z01.1.toFunctor :=
    isQuasiCompactSpace_inf D.Y'.2 D.qs (D.Wi 0).2 (D.hWiqc 0) (D.hWiqc 1)
  have hVZ : D.V'.1 ≤ Z01.1 := le_inf (D.hVW 0) (D.hVW 1)
  -- the restrictions of `x_0`, `x_1` to `W_0 ∩ W_1`
  let x₀' := algebraicSpaceStackMap.{u, w} B S hS hZ01.1 (D.Wi 0).2.1
    (Subfunctor.homOfLe inf_le_left) ≫ D.x 0
  let x₁' := algebraicSpaceStackMap.{u, w} B S hS hZ01.1 (D.Wi 1).2.1
    (Subfunctor.homOfLe inf_le_right) ≫ D.x 1
  obtain ⟨αi⟩ : Nonempty (x₀' ≫ f ≅ x₁' ≫ f) := by
    obtain ⟨k₀⟩ := nonempty_comp_iso_of_iso hZ01.1 (D.Wi 0).2.1 hY f
      (Subfunctor.homOfLe inf_le_left) (D.x 0) _ (D.hx 0)
    obtain ⟨k₁⟩ := nonempty_comp_iso_of_iso hZ01.1 (D.Wi 1).2.1 hY f
      (Subfunctor.homOfLe inf_le_right) (D.x 1) _ (D.hx 1)
    exact ⟨k₀ ≪≫ eqToIso (by rw [Subfunctor.homOfLe_ι_assoc, Subfunctor.homOfLe_ι_assoc]) ≪≫
      k₁.symm⟩
  let α := αi.hom
  -- `Isom(x_0, x_1) ⟶ W_0 ∩ W_1` is proper
  let XI : AlgebraicSpaces B S hS :=
    ⟨relativeIsomorphismTotalPresheaf B S hS Z01.1.toFunctor hZ01.1 f x₀' x₁' α,
      isAlgebraicSpace_relativeIsomorphismTotalPresheaf B S hS Z01.1.toFunctor hZ01.1 f x₀' x₁' α⟩
  let fI : XI ⟶ Space.openSubspace B S hS D.Y' Z01 :=
    ObjectProperty.homMk (PresheafOfCategories.elementsTotalProj Z01.1.toFunctor _)
  have hfI : Space.IsProper B S hS fI.hom :=
    isProper_relativeIsomorphismTotalProj_of_isSeparated B S hS Z01.1.toFunctor hZ01.1 f hf
      x₀' x₁' α
  -- the section over `V'` given by `x_0|_{V'} ≅ x_1|_{V'}`
  let q := Subfunctor.homOfLe hVZ
  have heq₀ : algebraicSpaceStackMap.{u, w} B S hS D.V'.2.1 hZ01.1 q ≫ x₀' =
      algebraicSpaceStackMap.{u, w} B S hS D.V'.2.1 (D.Wi 0).2.1
        (Subfunctor.homOfLe (D.hVW 0)) ≫ D.x 0 :=
    (stackMap_comp_assoc D.V'.2.1 hZ01.1 (D.Wi 0).2.1 q _ (D.x 0)).symm
  have heq₁ : algebraicSpaceStackMap.{u, w} B S hS D.V'.2.1 hZ01.1 q ≫ x₁' =
      algebraicSpaceStackMap.{u, w} B S hS D.V'.2.1 (D.Wi 1).2.1
        (Subfunctor.homOfLe (D.hVW 1)) ≫ D.x 1 :=
    (stackMap_comp_assoc D.V'.2.1 hZ01.1 (D.Wi 1).2.1 q _ (D.x 1)).symm
  obtain ⟨φ₁⟩ := D.φ 1
  let η : algebraicSpaceStackMap.{u, w} B S hS D.V'.2.1 hZ01.1 q ≫ x₀' ⟶
      algebraicSpaceStackMap.{u, w} B S hS D.V'.2.1 hZ01.1 q ≫ x₁' :=
    eqToHom heq₀ ≫ φ₁.hom ≫ eqToHom heq₁.symm
  let σ := (ChowGerbeIsomOver.relativeIsomorphismSectionOverEquiv q hZ01.1 f x₀' x₁' α).symm
    (ChowGerbeIsomOver.relVertFamilyOfTwoMorphismOfAlgebraicSpaceStack q D.V'.2.1 hZ01.1 hY f
      x₀' x₁' α η)
  -- Stacks 0CPI
  obtain ⟨Y'', b, hb, s', hs', -⟩ :=
    Space.exists_isAdmissibleBlowup_extending_section_of_isProper
      D.qc D.qs D.V' Z01 hVZ D.hV'qc hZ01qc fI hfI σ.1 σ.2
  have hbp : Space.IsProper B S hS b.hom := hb.isProper
  have hT := Space.isOpenSubspace_preimage B S hS b.hom Z01.1 D.Y'.2 Y''.2 Z01.2
  let ψ := ChowGerbeIsomOver.twoMorphismOfRelVertFamily (Z01.1.fromPreimage b.hom) hT.1 hZ01.1 f
    x₀' x₁' α
    (ChowGerbeIsomOver.relativeIsomorphismSectionOverEquiv (Z01.1.fromPreimage b.hom) hZ01.1 f
      x₀' x₁' α ⟨s', hs'⟩)
  -- the opens and sections pulled back to `Y''`
  have hqc'' : Space.IsQuasiCompactSpace B S hS Y''.1 :=
    Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS D.Y'.2 D.qc hbp.2.1.2
  let A : ℕ → Subfunctor Y''.1 := fun k => (D.Wi k).1.preimage b.hom
  have hA : ∀ k, Space.IsOpenSubspace B S hS (A k) := fun k =>
    Space.isOpenSubspace_preimage B S hS b.hom (D.Wi k).1 D.Y'.2 Y''.2 (D.Wi k).2
  have hAqc : ∀ k, Space.IsQuasiCompactSpace B S hS (A k).toFunctor := fun k =>
    Space.isQuasiCompactSpace_preimage_toFunctor B S hS hZt D.Y'.2 D.qs Y''.2 hqc'' (D.Wi k).1
      (D.hWiqc k) b.hom
  let xA : ∀ k, algebraicSpaceStack.{u, w} B S hS (A k).toFunctor (hA k).1 ⟶ 𝒳 := fun k =>
    algebraicSpaceStackMap.{u, w} B S hS (hA k).1 (D.Wi k).2.1 ((D.Wi k).1.fromPreimage b.hom) ≫
      D.x k
  have hxA : ∀ k, Nonempty (xA k ≫ f ≅
      algebraicSpaceStackMap.{u, w} B S hS (hA k).1 hY ((A k).ι ≫ b.hom ≫ D.p)) := fun k => by
    obtain ⟨e⟩ := nonempty_comp_iso_of_iso (hA k).1 (D.Wi k).2.1 hY f _ (D.x k) _ (D.hx k)
    exact ⟨e ≪≫ eqToIso (by rw [Subfunctor.fromPreimage_ι_assoc])⟩
  -- the extended isomorphism over `b⁻¹(W_0) ∩ b⁻¹(W_1)`
  have hA01 := Space.isOpenSubspace_inf B S hS Y''.2 (A 0) (A 1) (hA 0) (hA 1)
  have hl₀ := stackMap_comp_comp_eq (𝒳 := 𝒳) hA01.1 (D.Wi 0).2.1 (hA 0).1 hZ01.1
    (Subfunctor.homOfLe inf_le_left) ((D.Wi 0).1.fromPreimage b.hom)
    (Z01.1.fromPreimage b.hom) (Subfunctor.homOfLe inf_le_left) (by ext T z; rfl) (D.x 0)
  have hl₁ := stackMap_comp_comp_eq (𝒳 := 𝒳) hA01.1 (D.Wi 1).2.1 (hA 1).1 hZ01.1
    (Subfunctor.homOfLe inf_le_right) ((D.Wi 1).1.fromPreimage b.hom)
    (Z01.1.fromPreimage b.hom) (Subfunctor.homOfLe inf_le_right) (by ext T z; rfl) (D.x 1)
  let e' : algebraicSpaceStackMap.{u, w} B S hS hA01.1 (hA 0).1 (Subfunctor.homOfLe inf_le_left) ≫
      xA 0 ⟶ algebraicSpaceStackMap.{u, w} B S hS hA01.1 (hA 1).1
        (Subfunctor.homOfLe inf_le_right) ≫ xA 1 :=
    eqToHom hl₀ ≫ ψ ≫ eqToHom hl₁.symm
  obtain ⟨y, ⟨hy₀⟩, -, hyf⟩ := exists_hom_unionOpen Y''.2 (hA 0) (hA 1) (xA 0) (xA 1) e' hY f
    (b.hom ≫ D.p) (hxA 0) (hxA 1)
  have hM := isOpenSubspace_unionOpen Y''.2 (hA 0) (hA 1)
  have hV'' := Space.isOpenSubspace_preimage B S hS b.hom D.V'.1 D.Y'.2 Y''.2 D.V'.2
  let V'' : Space.OpenSubspaces B S hS Y''.1 := ⟨D.V'.1.preimage b.hom, hV''⟩
  have hV''A : ∀ k, V''.1 ≤ A k := fun k T z hz => D.hVW k T hz
  have hV''M : V''.1 ≤ unionOpen (B := B) (S := S) (hS := hS) (A 0) (A 1) :=
    (hV''A 0).trans (le_unionOpen_left _ _)
  refine ⟨{
    Y' := Y''
    qc := hqc''
    qs := Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZt Y''.2 D.qs
      (Space.isQuasiSeparated_of_isSeparated B S hS hbp.1)
    p := b.hom ≫ D.p
    hp := Space.isProper_comp B S hS Y''.2 D.Y'.2 hY b.hom D.p hbp D.hp
    V' := V''
    hV'qc := Space.isQuasiCompactSpace_preimage_toFunctor B S hS hZt D.Y'.2 D.qs Y''.2 hqc''
      D.V'.1 D.hV'qc b.hom
    hV := D.hV.trans (range_pointsMap_subset_of_isAdmissibleBlowup hb D.p)
    hV'W := fun T z hz => D.hV'W T hz
    Wi := fun k => match k with
      | 0 => ⟨unionOpen (B := B) (S := S) (hS := hS) (A 0) (A 1), hM⟩
      | k + 1 => ⟨A (k + 2), hA (k + 2)⟩
    hWiqc := fun k => match k with
      | 0 => isQuasiCompactSpace_unionOpen Y''.2 (hA 0) (hA 1) (hAqc 0) (hAqc 1)
      | k + 1 => hAqc (k + 2)
    hcov := ?_
    hVW := fun k => match k with
      | 0 => hV''M
      | k + 1 => hV''A (k + 2)
    x := fun k => match k with
      | 0 => y
      | k + 1 => xA (k + 2)
    hx := fun k => match k with
      | 0 => hyf
      | k + 1 => hxA (k + 2)
    φ := fun k => match k with
      | 0 => ⟨Iso.refl _⟩
      | k + 1 => ?_ }⟩
  · -- the covering condition
    intro T z hz
    have hz' := D.hcov T hz
    refine (BigFppfOver.topology B S hS).superset_covering (fun V g hg => ?_) hz'
    have hg' : D.Y'.1.map g.op (b.hom.app T z) ∈
        (⨆ k : Fin (n + 1 + 1), (D.Wi k).1).obj (op V) := hg
    change Y''.1.map g.op z ∈ (⨆ k : Fin (n + 1), (_ : Subfunctor Y''.1)).obj (op V)
    rw [Subfunctor.iSup_obj, Set.mem_iUnion] at hg' ⊢
    obtain ⟨⟨k, hk⟩, hk'⟩ := hg'
    have hk'' : Y''.1.map g.op z ∈ (A k).obj (op V) := by
      change b.hom.app (op V) (Y''.1.map g.op z) ∈ (D.Wi k).1.obj (op V)
      rw [NatTrans.naturality_apply]
      exact hk'
    rcases k with _ | _ | k
    · exact ⟨⟨0, by omega⟩, le_unionOpen_left (A 0) (A 1) _ hk''⟩
    · exact ⟨⟨0, by omega⟩, le_unionOpen_right (A 0) (A 1) _ hk''⟩
    · exact ⟨⟨k + 1, by omega⟩, hk''⟩
  · -- `y|_{V''} ≅ x_{k+2}|_{V''}`
    obtain ⟨φk⟩ := D.φ (k + 2)
    refine ⟨eqToIso ?_ ≪≫ Bicategory.whiskerLeftIso
      (algebraicSpaceStackMap.{u, w} B S hS hV''.1 (hA 0).1 (Subfunctor.homOfLe (hV''A 0))) hy₀ ≪≫
      eqToIso ?_ ≪≫ Bicategory.whiskerLeftIso
      (algebraicSpaceStackMap.{u, w} B S hS hV''.1 D.V'.2.1 (D.V'.1.fromPreimage b.hom)) φk ≪≫
      eqToIso ?_⟩
    · exact stackMap_comp_assoc hV''.1 (hA 0).1 hM.1 (Subfunctor.homOfLe (hV''A 0))
        (Subfunctor.homOfLe (le_unionOpen_left _ _)) y
    · exact stackMap_comp_comp_eq hV''.1 (D.Wi 0).2.1 (hA 0).1 D.V'.2.1 _ _ _ _
        (by ext T z; rfl) (D.x 0)
    · exact (stackMap_comp_comp_eq hV''.1 (D.Wi (k + 2)).2.1 (hA (k + 2)).1 D.V'.2.1 _ _ _ _
        (by ext T z; rfl) (D.x (k + 2))).symm

/-- **The section step of the proof of Stacks 0CQ7, after blowups.** -/
theorem MergeData.hasProperCompactifiableCover (hf : IsSeparated B S hS f)
    (hW : Space.IsOpenSubspace B S hS W)
    (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ))) :
    ∀ {n : ℕ} (_ : MergeData hY f W V n), HasProperCompactifiableCover.{u, w} B S hS hY f V
  | 0, D => D.hasProperCompactifiableCover_zero hf hW hfW
  | _ + 1, D => (D.nonempty_merge hf).elim fun D' =>
      MergeData.hasProperCompactifiableCover hf hW hfW D'

/-- **The section step of the proof of [Stacks, Tag 0CQ7]** (from the situation labelled (f)
there). Let `f : 𝒳 ⟶ Y` be a separated 1-morphism from an algebraic stack to a quasi-compact
quasi-separated algebraic space all of whose values lie in an open subspace `W ⊆ Y`, and let
`V ⊆ W` be a quasi-compact open subspace. Let `W_k ⊆ Y` be quasi-compact opens containing `V`,
the first `n + 1` of which cover `W`, with sections `x_k : W_k ⟶ 𝒳` of `f` and 2-isomorphisms
`x_0|_V ≅ x_k|_V`. Then the conclusion of Stacks 0CQ7 holds for `(f, V)`. The source also asks
for the cocycle condition on the `φ_{ij}`; it is not needed when the opens are merged one pair
at a time. -/
theorem hasProperCompactifiableCover_of_sections
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hf : IsSeparated B S hS f) (hW : Space.IsOpenSubspace B S hS W)
    (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ)))
    (hV : Space.IsOpenSubspace B S hS V) (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    (hVW : V ≤ W) {n : ℕ} (Wi : ℕ → Subfunctor Y) (hWi : ∀ k, Space.IsOpenSubspace B S hS (Wi k))
    (hWiqc : ∀ k, Space.IsQuasiCompactSpace B S hS (Wi k).toFunctor)
    (hcov : W ≤ (⨆ k : Fin (n + 1), Wi k).sheafify (BigFppfOver.topology B S hS))
    (hVWi : ∀ k, V ≤ Wi k)
    (x : ∀ k, algebraicSpaceStack.{u, w} B S hS (Wi k).toFunctor (hWi k).1 ⟶ 𝒳)
    (hx : ∀ k, Nonempty (x k ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS (hWi k).1 hY (Wi k).ι))
    (φ : ∀ k, Nonempty (algebraicSpaceStackMap.{u, w} B S hS hV.1 (hWi 0).1
        (Subfunctor.homOfLe (hVWi 0)) ≫ x 0 ≅
      algebraicSpaceStackMap.{u, w} B S hS hV.1 (hWi k).1 (Subfunctor.homOfLe (hVWi k)) ≫ x k)) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V :=
  MergeData.hasProperCompactifiableCover hf hW hfW (n := n)
    { Y' := ⟨Y, hY⟩
      qc := hYqc
      qs := hYqs
      p := 𝟙 Y
      hp := Space.isProper_of_isIso B S hS (𝟙 Y)
      V' := ⟨V, hV⟩
      hV'qc := hVqc
      hV := by rw [Category.comp_id]
      hV'W := fun T _ hz => hVW T hz
      Wi := fun k => ⟨Wi k, hWi k⟩
      hWiqc := hWiqc
      hcov := fun T _ hz => hcov T hz
      hVW := hVWi
      x := x
      hx := fun k => (hx k).map fun e => e ≪≫ eqToIso (by rw [Category.comp_id])
      φ := φ }

end AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge

end
