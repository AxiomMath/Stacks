module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryChartOfStratum
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallZariskiSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Absolute Noetherian approximation by descending induction over the strata of Stacks 07ST

The proof of absolute Noetherian approximation, Stacks 07SU, applies Stacks 07ST to a
quasi-compact quasi-separated algebraic space `X` over `Spec ℤ`, getting a filtration
`X = U_0 ⊇ U_1 ⊇ ⋯ ⊇ U_n = ∅` by open subspaces with, for each `p`, a quasi-compact separated
scheme `V_p` étale over `U_p` and an isomorphism over the closed complement `T_p` of `U_{p+1}`.
By descending induction on `p` it is then enough to solve "the problem posed in the following
paragraph" of the source: given an elementary chart `V ⟶ X` which is an isomorphism off an open
subspace `U ⊆ X` that has a Noetherian approximation, show that `X` has one.

This file performs that induction (step (i) of the proof). The problem of the source is the
proposition `AlgebraicGeometry.Space.NoetherianApproximationExtendsOverElementaryChart`; it is
taken as an explicit argument here, because its solution needs Stacks 07SK and 07SR under the
convention of Stacks 07SD. The base of the induction, the empty open subspace `U_n`, is also an
explicit argument.

## Main definitions

* `AlgebraicGeometry.Space.NoetherianApproximationExtendsOverElementaryChart`: the problem of
  the source's proof, for one stratum.

## Main results

* `AlgebraicGeometry.Space.hasNoetherianApproximation_of_extendsOverElementaryChart`: the
  descending induction.

## References

* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The problem posed in the proof of Stacks 07SU, for one stratum.** For every
quasi-compact quasi-separated algebraic space `X` over `Spec ℤ` and every elementary chart
`f : V ⟶ X` with `V` quasi-compact and separated and `f` surjective, which is an isomorphism off
an open subspace `U ⊆ X`, a Noetherian approximation of `U` gives one of `X`. -/
def NoetherianApproximationExtendsOverElementaryChart : Prop :=
  ∀ (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (V : BigFppfOver B (⊤_ Scheme.{u}) hZ) (C : ElementaryChart X V),
    IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X →
    IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X →
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X →
    CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V) →
    Scheme.IsSeparated ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V) →
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) C.f →
    IsOpenSubspace B (⊤_ Scheme.{u}) hZ C.U →
    HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ C.U.toFunctor →
    HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X

variable {B hZ}

/-- In the points of an open subspace `Y` of `X`, the inverse image of a smaller subfunctor
`U ≤ Y` and a subfunctor `T` of `Y` whose image in `X` is the complement of `U` in `Y` are
complementary. -/
theorem range_pointsMap_eq_compl_of_le {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U Y : Subfunctor X} (hle : U ≤ Y)
    (T : Subfunctor Y.toFunctor)
    (hT : Set.range (pointsMap B S hS T.toFunctor (T.ι ≫ Y.ι)) =
      Set.range (pointsMap B S hS Y.toFunctor Y.ι) \ Set.range (pointsMap B S hS U.toFunctor U.ι)) :
    Set.range (pointsMap B S hS T.toFunctor T.ι) =
      (Set.range (pointsMap B S hS (U.preimage Y.ι).toFunctor (U.preimage Y.ι).ι))ᶜ := by
  have hinj := pointsMap_injective_of_mono B S hS Y.ι
  have hU (y : points B S hS Y.toFunctor) :
      pointsMap B S hS _ Y.ι y ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) ↔
        y ∈ Set.range (pointsMap B S hS _ (U.preimage Y.ι).ι) := by
    let e := preimageIso_of_le hle
    have he : e.hom ≫ U.ι = (U.preimage Y.ι).ι ≫ Y.ι := U.fromPreimage_ι Y.ι
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨pointsMap B S hS _ e.inv w, hinj ?_⟩
      rw [← pointsMap_comp_apply, ← he, pointsMap_comp_apply,
        ← pointsMap_comp_apply (α := e.inv) (β := e.hom), e.inv_hom_id, pointsMap_id, id, hw]
    · rintro ⟨w, rfl⟩
      exact ⟨pointsMap B S hS _ e.hom w, by rw [← pointsMap_comp_apply, he, pointsMap_comp_apply]⟩
  ext y
  simp only [Set.mem_compl_iff]
  constructor
  · rintro ⟨t, rfl⟩ hy
    have hmem : pointsMap B S hS _ (T.ι ≫ Y.ι) t ∈ Set.range (pointsMap B S hS _ (T.ι ≫ Y.ι)) :=
      ⟨t, rfl⟩
    rw [hT, pointsMap_comp_apply] at hmem
    exact hmem.2 ((hU _).mpr hy)
  · intro hy
    have hmem : pointsMap B S hS _ Y.ι y ∈ Set.range (pointsMap B S hS _ Y.ι) \
        Set.range (pointsMap B S hS U.toFunctor U.ι) := ⟨⟨y, rfl⟩, fun h ↦ hy ((hU y).mp h)⟩
    rw [← hT] at hmem
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, hinj (by rw [← pointsMap_comp_apply, ht])⟩

/-- **Step (i) of Stacks 07SU: the descending induction over the strata of Stacks 07ST.** A
solution of the problem posed in the source's proof for every stratum
(`AlgebraicGeometry.Space.NoetherianApproximationExtendsOverElementaryChart`), together with a
Noetherian approximation of the empty open subspace, gives a Noetherian approximation of every
quasi-compact quasi-separated algebraic space over `Spec ℤ`. -/
theorem hasNoetherianApproximation_of_extendsOverElementaryChart
    (hstep : NoetherianApproximationExtendsOverElementaryChart B hZ)
    (hempty : ∀ X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X →
      HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ
        ((⊥ : Subfunctor X).sheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)).toFunctor)
    (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X) :
    HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X := by
  obtain ⟨n, U, -, hU0, hUn, hUopen, hUmono, T, V, f, hdata⟩ :=
    exists_finiteFiltration_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ X hX hqc hqs
  have key : ∀ k, k ≤ n →
      HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ (U (n - k)).toFunctor := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.sub_zero, hUn]
      exact hempty X hX
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hp1 : n - (k + 1) + 1 = n - k := by omega
      have hpn : n - (k + 1) < n := by omega
      rw [← hp1] at ih'
      obtain ⟨hTcl, hrange, -, hVc, hVsep, hsurj, het, hiso⟩ := hdata ⟨n - (k + 1), hpn⟩
      have hle : U (n - (k + 1) + 1) ≤ U (n - (k + 1)) := hUmono _ hpn
      have hU' := isOpenSubspace_preimage_of_le B (⊤_ Scheme.{u}) hZ hle
        (hUopen _ (by omega))
      have hX' := (hUopen (n - (k + 1)) hpn.le).1
      have hqs' := isAbsolutelyQuasiSeparated_of_mono B (⊤_ Scheme.{u}) hZ hZ hX'
        (U (n - (k + 1))).ι inferInstance hqs
      have hqc' := isQuasiCompactSpace_of_isSurjective B (⊤_ Scheme.{u}) hZ
        (isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ _) hX' _
        (isSurjective_of_presheafSurjective B (⊤_ Scheme.{u}) hZ _ hsurj)
        (isQuasiCompactSpace_yoneda B (⊤_ Scheme.{u}) hZ _ hVc)
      exact hstep _ _ (ElementaryChart.ofStratum _ hsurj het _ _ hU' hTcl
        (range_pointsMap_eq_compl_of_le hle _ hrange) hiso) hX' hqc' hqs' hVc hVsep hsurj hU'
        (ih'.ofIso (preimageIso_of_le hle).symm)
  have h0 := key n le_rfl
  rw [Nat.sub_self, hU0] at h0
  exact h0.ofIso (topSubfunctorIso B (⊤_ Scheme.{u}) hZ)

end AlgebraicGeometry.Space

end
