module

public import StacksFrontier.AlgebraicGeometry.LimitApproxJoin.Join

/-!
# Choosing the standard opens: the shrinking condition is a consequence

A quasi-compact open subscheme of an affine scheme is a finite union of standard opens.  This
supplies the shrinking hypothesis of
`AlgebraicGeometry.exists_stage_isOpenImmersion_toSpecΓ_comp_SpecMap_snd`, used in the
one-affine-open step of Tag 07RN: finitely many global sections of the affine open being added
whose standard opens lie inside the overlap and cover it.  Here that hypothesis is derived from
quasi-compactness of the overlap.

## Main results

* `AlgebraicGeometry.exists_fin_basicOpen_le_opensRange`: for an affine scheme `Y` and an open
  immersion from a quasi-compact scheme into it, finitely many global sections of `Y` have
  standard opens lying inside the image and covering it.  The conclusion is stated as the two
  inequalities rather than as an equality, because the two inequalities are used separately:
  the first makes each basic open of the overlap affine and is the hypothesis of the localization
  half, the second is used only for the covering.

* `AlgebraicGeometry.exists_fin_stage_isOpenImmersion_toSpecΓ_comp_SpecMap_snd`:
  `AlgebraicGeometry.exists_stage_isOpenImmersion_toSpecΓ_comp_SpecMap_snd` with the shrinking
  condition supplied by the statement above, quasi-compactness of the vertex coming from
  `AlgebraicGeometry.Scheme.compactSpace_of_isLimit`.  The number of sections and the sections
  themselves appear in the conclusion rather than in the hypotheses.

## Implementation notes

* The first statement feeds Mathlib's `AlgebraicGeometry.isBasis_basicOpen` (the standard opens
  of an affine scheme are a basis) to `TopologicalSpace.Opens.IsBasis.exists_iSup_eq_of_isCompact`,
  which writes a quasi-compact open as a union of finitely many basis members.  The image of an
  open immersion out of a quasi-compact scheme is compact, by `isCompact_range`.

* The index universe of the second statement is tied to the scheme universe, as in
  `AlgebraicGeometry.exists_stage_isOpenImmersion_toSpecΓ_comp_SpecMap_snd`: the colimit of the
  rings of sections lives over the opposite index category, and `CommRingCat` in one universe has
  no colimits over a larger index universe.  The first statement involves no index category and
  no ring colimit: the finite index type produced by the basis lemma lands in the universe of the
  carrier of `Y`, which is the scheme universe, and is immediately replaced by `Fin n`.

* The finite index type that `TopologicalSpace.Opens.IsBasis.exists_iSup_eq_of_isCompact`
  returns carries `Finite`, not `Fintype`; `Fintype.ofFinite` is needed before
  `Fintype.equivFin` can reindex it by `Fin n`.

* Compactness is read off the *range* of the open immersion rather than off the open it cuts
  out: the coercion of `AlgebraicGeometry.Scheme.Hom.opensRange` to a set is that range by
  definition, and `isCompact_range` applies directly.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **A quasi-compact open subscheme of an affine scheme is a finite union of standard opens.**
Stated as two inequalities: each standard open lies inside the open subscheme, and together
they cover it. -/
lemma exists_fin_basicOpen_le_opensRange {V Y : Scheme.{u}} [IsAffine Y] (jVY : V ⟶ Y)
    [IsOpenImmersion jVY] [CompactSpace V] :
    ∃ (n : ℕ) (g : Fin n → Γ(Y, ⊤)), (∀ l, Y.basicOpen (g l) ≤ jVY.opensRange) ∧
      jVY.opensRange ≤ ⨆ l, Y.basicOpen (g l) := by
  classical
  obtain ⟨κ, hκ, a, heq⟩ := (isBasis_basicOpen Y).exists_iSup_eq_of_isCompact jVY.opensRange
    (isCompact_range jVY.continuous)
  have : Fintype κ := Fintype.ofFinite κ
  refine ⟨Fintype.card κ, fun l ↦ a ((Fintype.equivFin κ).symm l), fun l ↦ ?_, ?_⟩
  · rw [heq]
    exact le_iSup (fun k ↦ Y.basicOpen (a k)) _
  · rw [heq]
    refine iSup_le fun k ↦ le_iSup_of_le (Fintype.equivFin κ k) ?_
    simp

/-- **A stage maps by an open immersion, with the shrinking hypothesis discharged.**  Let
the vertex of a limiting cone over a cofiltered diagram of qcqs schemes with affine transitions
be an open subscheme of an affine scheme `Y`.  Then some stage of the diagram maps by an open
immersion into the spectrum of the fibre product of `Γ(Y, ⊤)` with the sections of that stage
over the sections of the vertex.

This is `AlgebraicGeometry.exists_stage_isOpenImmersion_toSpecΓ_comp_SpecMap_snd` with its
shrinking hypothesis discharged: the vertex is quasi-compact, by
`AlgebraicGeometry.Scheme.compactSpace_of_isLimit`, hence a finite union of standard opens
of `Y`. -/
lemma exists_fin_stage_isOpenImmersion_toSpecΓ_comp_SpecMap_snd {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {Y : Scheme.{u}} [IsAffine Y] (jVY : c.pt ⟶ Y) [IsOpenImmersion jVY] :
    ∃ (j : I) (n : ℕ) (g : Fin n → Γ(Y, ⊤)) (f : Fin n → Γ(D.obj j, ⊤)),
      (∀ l, (c.π.app j).appTop (f l) = jVY.appTop (g l)) ∧
        IsOpenImmersion ((D.obj j).toSpecΓ ≫ Spec.map (Stacks.FibreProduct.snd jVY.appTop
          ((Scheme.Γ.mapCocone c.op).ι.app (op j)))) := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  obtain ⟨n, g, hin, hcover⟩ := exists_fin_basicOpen_le_opensRange jVY
  obtain ⟨j, f, hf, himm⟩ :=
    exists_stage_isOpenImmersion_toSpecΓ_comp_SpecMap_snd D c hc jVY g hin hcover
  exact ⟨j, n, g, f, hf, himm⟩

end AlgebraicGeometry
