module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.CardinalBound
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceApproximation

/-!
# A directed system of closed subspaces is indexed by fewer stages than the cutoff

Let `Y` be an algebraic space over `S` and `p : U ⟶ Y` a surjective étale chart from an object of
the site. A closed subspace of `Y` is determined by the sheaf of ideals on `U` cutting out its
base change to `U` (`AlgebraicGeometry.Space.chartKer_injective_of_atlas`), so there are at most
`2 ^ size U` closed subspaces of `Y`, fewer than the cutoff of the site.

Consequently every directed inverse system of closed subspaces of `Y` with a given closed
subspace as its limit, as produced by Stacks 0A0U, may be reindexed by its set of stages, read
through their ideal sheaves on `U`, which has fewer elements than the cutoff:
`AlgebraicGeometry.Space.exists_mk_lt_cutoff_isLimit_closedSubspaces`. The transition morphisms
are closed immersions, hence monomorphisms, so the reindexed system is bounded by the cutoff in
the sense of `AlgebraicGeometry.Space.IsCutoffBoundedSystem`, and the cofinality-free form of
Stacks 086X applies to it.

## Main results

* `AlgebraicGeometry.Space.le_of_chartKer_le_of_atlas`: a closed subspace is recovered from its
  ideal sheaf on one surjective étale chart.
* `AlgebraicGeometry.Space.exists_mk_lt_cutoff_closedSubspaces`: an algebraic space has a
  surjective étale chart with fewer ideal sheaves than the cutoff, so, by the above, fewer closed
  subspaces than the cutoff.
* `AlgebraicGeometry.Space.exists_mk_lt_cutoff_isLimit_closedSubspaces`: a system of the shape of
  the conclusion of Stacks 0A0U can be reindexed by fewer than `B.cutoff` stages, keeping that
  shape.

Nothing here is registered.

## References

* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
* [Stacks Project, Tag 086X](https://stacks.math.columbia.edu/tag/086X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A closed subspace is determined on one surjective étale chart -/

section Chart

variable (X : AlgebraicSpaces B S hS) {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ X.1)
  (hfS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
  (hfE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)

include hfS hfE in
/-- **A closed subspace is recovered from its ideal sheaf on one surjective étale chart.** If
the ideal sheaf on `U` of the base change of `W` is contained in that of `Z`, for one surjective
étale chart `U ⟶ X`, then `Z ⊆ W`.

This is `AlgebraicGeometry.Space.le_of_forall_ker_le` with the comparison asked at the given
chart only: a point of `Z` is pushed onto the chart after a surjective étale base change, where
membership in `W` is read off the ideal sheaves, and `W` is a sheaf. -/
theorem le_of_chartKer_le_of_atlas (Z W : ClosedSubspaces B S hS X.1)
    (h : chartKer B S hS X W f ≤ chartKer B S hS X Z f) : Z.1 ≤ W.1 := by
  rw [chartKer_eq, chartKer_eq] at h
  intro T x hx
  set V : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk f, hfE⟩
  set τ : yoneda.obj T.unop ⟶ X.1 := yonedaEquiv.symm x with hτ
  refine mem_obj_of_surjective_etale B S hS X.2.isSheaf W.1 W.2.1.isSheaf
    (hfE.rep.snd τ) (hfS.property_snd τ) (hfE.property_snd τ) _ ?_
  have hw : yoneda.map (hfE.rep.fst' τ) ≫ f = yoneda.map (hfE.rep.snd τ) ≫ τ := by
    rw [hfE.rep.map_fst' τ]
    exact hfE.rep.w τ
  have hval : X.1.map (hfE.rep.snd τ).op x =
      V.1.hom.app (op (hfE.rep.pullback τ)) (hfE.rep.fst' τ) := by
    rw [show V.1.hom = f from rfl,
      ← yonedaEquiv_yoneda_map_comp B S hS f (hfE.rep.fst' τ), hw,
      ← yonedaEquiv_naturality, hτ, Equiv.apply_symm_apply]
  rw [hval, mem_obj_iff_ker_le]
  refine h.trans ((mem_obj_iff_ker_le B S hS X Z V (hfE.rep.fst' τ)).1 ?_)
  rw [← hval]
  exact Z.1.map (hfE.rep.snd τ).op hx

include hfS hfE in
/-- **A closed subspace is determined by its ideal sheaf on one surjective étale chart.** -/
theorem chartKer_injective_of_atlas :
    Function.Injective fun Z : ClosedSubspaces B S hS X.1 => chartKer B S hS X Z f :=
  fun Z W h => Subtype.ext (le_antisymm
    (le_of_chartKer_le_of_atlas B S hS X f hfS hfE Z W h.symm.le)
    (le_of_chartKer_le_of_atlas B S hS X f hfS hfE W Z h.le))

/-- The ideal sheaf on a chart is antitone in the closed subspace: a smaller closed subspace has
a larger ideal sheaf. -/
theorem chartKer_le_chartKer_of_le {Z W : ClosedSubspaces B S hS X.1} (h : Z.1 ≤ W.1) :
    chartKer B S hS X W f ≤ chartKer B S hS X Z f := by
  rw [le_chartKer_iff, chartKer_eq, idealPoints_ker_rep_snd W.2.2]
  exact fun T x hx => h _ hx

end Chart

/-- **An algebraic space has fewer closed subspaces than the cutoff of the site**, counted on a
surjective étale chart `U` of the site through their ideal sheaves on `U`. Reading a
closed subspace through its ideal sheaf on a surjective étale chart `U` of the site is injective
(`AlgebraicGeometry.Space.chartKer_injective_of_atlas`), and there are at most `2 ^ size U` ideal
sheaves on `U` (`AlgebraicGeometry.Scheme.mk_idealSheafData_le`), which lies below the cutoff
because the cutoff is a strong limit. The count is made in the universe of the site. -/
theorem exists_mk_lt_cutoff_closedSubspaces (X : AlgebraicSpaces B S hS) :
    ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X.1),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f ∧
      Function.Injective (fun Z : ClosedSubspaces B S hS X.1 => chartKer B S hS X Z f) ∧
      #((BigFppfOver.toScheme B S hS).obj U).IdealSheafData < B.cutoff := by
  obtain ⟨U, f, hfS, hfE⟩ := X.2.exists_atlas
  exact ⟨U, f, hfS, hfE, chartKer_injective_of_atlas B S hS X f hfS hfE,
    (Scheme.mk_idealSheafData_le _).trans_lt (B.cutoff_isStrongPrelimit U.left.property)⟩

/-! ### Reindexing a directed system of closed subspaces -/

/-- **A system of the shape of Stacks 0A0U can be reindexed by fewer stages than the cutoff.**
Let `f : X ⟶ Y` be a closed immersion of algebraic spaces, and let `X` be the directed limit of
an antitone family `Z` of closed subspaces of `Y` of finite presentation, in the form of the
conclusion of Stacks 0A0U. Then the same holds with an index set of fewer than `B.cutoff`
elements: the set of the ideal sheaves, on one surjective étale chart `U` of `Y`, of the members
of the family, ordered by inclusion. The member at such an ideal sheaf is any member having it,
which is well defined because a closed subspace is determined by its ideal sheaf on `U`; the
family of members is the same, so it has the same intersection, and the cone of inclusions of
the range of `f` is again limiting. -/
theorem exists_mk_lt_cutoff_isLimit_closedSubspaces (Y : AlgebraicSpaces B S hS)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y.1) (hf : IsClosedImmersion B S hS f)
    (h : ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (Z : I → ClosedSubspaces B S hS Y.1) (hZ : ∀ ⦃i j : I⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
        (hle : ∀ i, Subfunctor.range f ≤ (Z i).1),
        (∀ ⦃i j : Iᵒᵖ⦄ (g : i ⟶ j), IsClosedImmersion B S hS
          ((closedSubspaceDiagram B S hS (fun i => (Z i).1) hZ).map g)) ∧
        (∀ i, IsClosedImmersion B S hS (Z i).1.ι ∧ IsFinitePresentation B S hS (Z i).1.ι) ∧
        (∀ i, ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ (Subfunctor.range f)
          hle).extend (Subfunctor.toRange f)).π.app (op i) ≫ (Z i).1.ι = f) ∧
        Nonempty (IsLimit ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ
          (Subfunctor.range f) hle).extend (Subfunctor.toRange f)))) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (Z : I → ClosedSubspaces B S hS Y.1) (hZ : ∀ ⦃i j : I⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
      (hle : ∀ i, Subfunctor.range f ≤ (Z i).1),
      #I < B.cutoff ∧
      (∀ ⦃i j : Iᵒᵖ⦄ (g : i ⟶ j), IsClosedImmersion B S hS
        ((closedSubspaceDiagram B S hS (fun i => (Z i).1) hZ).map g)) ∧
      (∀ i, IsClosedImmersion B S hS (Z i).1.ι ∧ IsFinitePresentation B S hS (Z i).1.ι) ∧
      (∀ i, ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ (Subfunctor.range f)
        hle).extend (Subfunctor.toRange f)).π.app (op i) ≫ (Z i).1.ι = f) ∧
      Nonempty (IsLimit ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ
        (Subfunctor.range f) hle).extend (Subfunctor.toRange f))) := by
  obtain ⟨I, _, _, ⟨i₀⟩, Z, hZ, hle, -, hfp, -, ⟨hlim⟩⟩ := h
  obtain ⟨U, p, hpS, hpE, -, hcard⟩ := exists_mk_lt_cutoff_closedSubspaces B S hS Y
  have : Mono f := mono_of_isClosedImmersion B S hS f hf
  -- the intersection of the family lies in the range of `f`
  let c := closedSubspaceCone B S hS (fun i => (Z i).1) hZ (Subfunctor.range f) hle
  have hc : IsLimit c := IsLimit.ofExtendIso (Subfunctor.toRange f) hlim
  have hinf : (⨅ i, (Z i).1) ≤ Subfunctor.range f := by
    let d := closedSubspaceCone B S hS (fun i => (Z i).1) hZ (⨅ i, (Z i).1) (fun i => iInf_le _ i)
    let m := hc.lift d
    have hm : m ≫ (Subfunctor.range f).ι = (⨅ i, (Z i).1).ι := by
      simpa only [Category.assoc, c, d, Subfunctor.homOfLe_ι] using congrArg (· ≫ (Z i₀).1.ι)
        (hc.fac d (op i₀))
    intro T x hx
    have key : (m.app T ⟨x, hx⟩).1 = x := congrArg (fun φ => φ.app T ⟨x, hx⟩) hm
    exact key ▸ (m.app T ⟨x, hx⟩).2
  -- the new index: the ideal sheaves on the chart of the members
  let κ : I → ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData :=
    fun i => chartKer B S hS Y (Z i) p
  let I' := Set.range κ
  let Z' : I' → ClosedSubspaces B S hS Y.1 := fun J => Z J.2.choose
  have hκZ' : ∀ J : I', κ J.2.choose = J.1 := fun J => J.2.choose_spec
  have hZ' : ∀ ⦃J J' : I'⦄, J ≤ J' → (Z' J').1 ≤ (Z' J).1 := fun J J' hJJ' =>
    le_of_chartKer_le_of_atlas B S hS Y p hpS hpE _ _ (by
      change κ J.2.choose ≤ κ J'.2.choose
      rw [hκZ', hκZ']
      exact hJJ')
  have hZ'eq : ∀ i, Z' ⟨κ i, i, rfl⟩ = Z i := fun i =>
    chartKer_injective_of_atlas B S hS Y p hpS hpE (hκZ' ⟨κ i, i, rfl⟩)
  have hdir : IsDirected I' (· ≤ ·) := ⟨by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    exact ⟨⟨κ k, k, rfl⟩, chartKer_le_chartKer_of_le B S hS Y p (hZ hik),
      chartKer_le_chartKer_of_le B S hS Y p (hZ hjk)⟩⟩
  have hle' : ∀ J, Subfunctor.range f ≤ (Z' J).1 := fun J => hle _
  have hinf' : (⨅ J, (Z' J).1) ≤ Subfunctor.range f := by
    refine le_trans (le_iInf fun i => ?_) hinf
    rw [← hZ'eq i]
    exact iInf_le _ _
  have hlim' := isLimitClosedSubspaceCone B S hS (⟨κ i₀, i₀, rfl⟩ : I') (fun J => (Z' J).1) hZ'
    (Subfunctor.range f) hle' hinf'
  refine ⟨I', inferInstance, hdir, ⟨⟨κ i₀, i₀, rfl⟩⟩, Z', hZ', hle',
    (Cardinal.mk_subtype_le _).trans_lt hcard,
    fun _ _ g => isClosedImmersion_closedSubspaceDiagram_map B S hS Z' hZ' g,
    fun J => hfp _, fun J => ?_, ⟨IsLimit.extendIso (Subfunctor.toRange f) hlim'⟩⟩
  change (Subfunctor.toRange f ≫ Subfunctor.homOfLe (hle' J)) ≫ (Z' J).1.ι = f
  rw [Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι]

end AlgebraicGeometry.Space

end
