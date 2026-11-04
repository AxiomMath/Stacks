module

public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria

/-!
# The local nonemptiness hypothesis of Tag 086U is equivalent to its conclusion

For an algebraic space `X` over a scheme `S`, the conclusion of Tag 086U, that `X` has a
representable open subspace with dense point set, is equivalent to the hypothesis that every
nonempty open subspace of `X` contains a nonempty representable open subspace. An algebraic space
also has a largest open subspace which is a scheme (Tag 03JH).

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_le_of_isRepresentable`: an open subspace
  contained in a representable subfunctor is representable.
* `AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace`:
  the schematic locus of an algebraic space is an open subspace and is representable.
* `AlgebraicGeometry.Space.exists_isGreatest_isOpenSubspace_isRepresentable`: the representable
  open subspaces of an algebraic space have a greatest element.
* `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_le_of_denseRange`: if an
  algebraic space has a representable open subspace with dense point set, then every nonempty
  open subspace contains a nonempty representable open subspace.
* `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_iff`: the two are
  equivalent over an algebraic space.

## References

* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 02YX](https://stacks.math.columbia.edu/tag/02YX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An open subspace of a presheaf on the big fppf site of `S` which is contained in a
representable subfunctor is itself representable. -/
theorem isRepresentable_of_le_of_isRepresentable
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {H L : Subfunctor X}
    (hH : IsOpenSubspace B S hS H) (hle : H ≤ L) (hL : L.toFunctor.IsRepresentable) :
    H.toFunctor.IsRepresentable := by
  have hmono : Mono (Subfunctor.homOfLe hle) := mono_of_mono_fac (Subfunctor.homOfLe_ι hle)
  set H' := Subfunctor.range (Subfunctor.homOfLe hle) with hH'def
  have hH' : IsOpenSubspace B S hS H' := isOpenSubspace_of_le B S hS H L hH hle
  set e := L.toFunctor.reprW with hedef
  have hpb := hH'.2.rep.isPullback e.hom
  have hiso : IsPullback (𝟙 H'.toFunctor) (H'.ι ≫ e.inv) H'.ι e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact Functor.IsRepresentable.mk' (hpb.isoIsPullback _ _ hiso ≪≫
    (asIso (Subfunctor.toRange (Subfunctor.homOfLe hle))).symm)

/-- The schematic locus of an algebraic space over `S` is an open subspace and is
representable. -/
@[stacks 03JH "openness and representability"]
theorem isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) :
    IsOpenSubspace B S hS (schematicLocus B S hS X) ∧
      (schematicLocus B S hS X).toFunctor.IsRepresentable := by
  classical
  obtain ⟨μ, hμ, hbound⟩ := exists_lt_cutoff_size_le_of_isOpenSubspace B S hS hX
  have hsmall := small_isRepresentable_isOpenSubspace B S hS hX
  let e := (equivShrink {G : Subfunctor X //
    IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable}).symm
  have hcof : ∀ G : Subfunctor X, IsOpenSubspace B S hS G → G.toFunctor.IsRepresentable →
      G ≤ ⨆ i, (e i).1 := fun G h1 h2 =>
    le_iSup_of_le (e.symm ⟨G, h1, h2⟩) (le_of_eq (by rw [e.apply_symm_apply]))
  have hι : Cardinal.mk (Shrink.{u} {G : Subfunctor X //
      IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable}) < B.cutoff :=
    mk_lt_cutoff_of_injective_points B S hS hX
      (fun i => Set.range (pointsMap B S hS (e i).1.toFunctor (e i).1.ι)) fun a b h =>
      e.injective (Subtype.ext (eq_of_range_pointsMap_ι_eq B S hS (e a).2.1 (e b).2.1 h))
  exact isOpenSubspace_and_isRepresentable_schematicLocus_of_size_le
    B S hS hX (fun i => (e i).1) (fun i => (e i).2.1) (fun i => (e i).2.2) hcof
    hι hμ (fun i T hT => hbound T _ (e i).2.1 hT)

/-- An algebraic space `X` over a scheme `S` has a largest open subspace which is a scheme: the
set of open subspaces of `X` that are represented by a scheme over `S` has a greatest element. -/
@[stacks 03JH]
theorem exists_isGreatest_isOpenSubspace_isRepresentable
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) :
    ∃ X' : Subfunctor X, IsGreatest
      {G : Subfunctor X | IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable} X' :=
  ⟨schematicLocus B S hS X,
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hX,
    fun _G hG => le_schematicLocus B S hS X _ hG.1 hG.2⟩

/-- If an algebraic space over `S` has a representable open subspace whose point set is dense,
then every nonempty open subspace of it contains a nonempty representable open subspace. -/
theorem exists_isRepresentable_isOpenSubspace_le_of_denseRange
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {L : Subfunctor X} (hL : IsOpenSubspace B S hS L)
    (hLrep : L.toFunctor.IsRepresentable)
    (hLdense : DenseRange (pointsMap B S hS L.toFunctor L.ι))
    (G : Subfunctor X) (hG : IsOpenSubspace B S hS G)
    (hGne : (Set.range (pointsMap B S hS G.toFunctor G.ι)).Nonempty) :
    ∃ H : Subfunctor X, H ≤ G ∧ IsOpenSubspace B S hS H ∧
      H.toFunctor.IsRepresentable ∧
      (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty := by
  have hopen {K : Subfunctor X} (hK : IsOpenSubspace B S hS K) :
      IsOpen (Set.range (pointsMap B S hS K.toFunctor K.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS K.ι hK.2
  have hne := dense_iff_inter_open.1 hLdense _ (hopen hG) hGne
  obtain ⟨H, hH, hHrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hX
    (Set.range (pointsMap B S hS G.toFunctor G.ι) ∩
      Set.range (pointsMap B S hS L.toFunctor L.ι)) ((hopen hG).inter (hopen hL))
  refine ⟨H, le_of_range_pointsMap_ι_subset B S hS hG ?_, hH, ?_, ?_⟩
  · rw [hHrange]; exact Set.inter_subset_left
  · exact isRepresentable_of_le_of_isRepresentable B S hS hH
      (le_of_range_pointsMap_ι_subset B S hS hL (by rw [hHrange]; exact Set.inter_subset_right))
      hLrep
  · rw [hHrange]; exact hne

/-- For an algebraic space `X` over `S`, the existence of a representable open subspace with dense
point set is equivalent to every nonempty open subspace of `X` containing a nonempty
representable open subspace. -/
theorem exists_denseRange_isRepresentable_isOpenSubspace_iff
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) :
    (∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
        DenseRange (pointsMap B S hS G.toFunctor G.ι)) ↔
      ∀ G : Subfunctor X, IsOpenSubspace B S hS G →
        (Set.range (pointsMap B S hS G.toFunctor G.ι)).Nonempty →
        ∃ H : Subfunctor X, H ≤ G ∧ IsOpenSubspace B S hS H ∧
          H.toFunctor.IsRepresentable ∧
          (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty :=
  ⟨fun ⟨_L, hL, hLrep, hLdense⟩ =>
      exists_isRepresentable_isOpenSubspace_le_of_denseRange B S hS hX hL hLrep hLdense,
    fun h => exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace B S hS hX h⟩

end AlgebraicGeometry.Space

end
