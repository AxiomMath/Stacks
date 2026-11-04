module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeProper
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.DenseRationalPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# The Hilbert schemes of points of a smooth proper curve are smooth proper varieties

Let `k` be an algebraically closed field and `X` a smooth proper curve over `k`. For every
`d ≥ 0` a scheme `H_d` representing the Hilbert functor `Hilb^d_{X/k}` of degree-`d` closed
subschemes is proper, smooth of relative dimension `d` and irreducible over `k`, of dimension `d`.
This is part (1) of [Stacks, Tag 0B9I], read for any representing scheme.

## Main results

* `Stacks.Hilbert.isProper_hom_and_irreducibleSpace_of_represents`: for a family `H d` of
  representing schemes, each `H d` is proper over `k` with irreducible underlying space.
* `Stacks.Hilbert.hilbertScheme_isProper_smooth_irreducible_dim`: part (1) of
  [Stacks, Tag 0B9I] for a family `H d` of representing schemes.
* `Stacks.Hilbert.isProper_smooth_irreducible_dim_of_represents`: the same for a single
  representing scheme of degree `d`, given that every `Hilb^e_{X/k}` is representable.

## References

* [Stacks Project, Tag 0B9I](https://stacks.math.columbia.edu/tag/0B9I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

omit [IsAlgClosed k] in
/-- The structure morphism of `H ×_k X` is proper when that of `H` is and `X` is proper over
`k`. -/
private theorem isProper_prod_hom (H : Over (Spec (.of k))) [IsProper f] [IsProper H.hom] :
    IsProper (H ⨯ Over.mk f).hom := by
  have hpull : IsProper (pullback.fst H.hom (Over.mk f).hom) :=
    IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback H.hom f).flip
      (inferInstanceAs (IsProper f))
  have hsq : IsPullback (Over.prodLeftIsoPullback H (Over.mk f)).hom
      ((prod.fst : H ⨯ Over.mk f ⟶ H).left) (pullback.fst H.hom (Over.mk f).hom) (𝟙 H.left) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, Over.prodLeftIsoPullback_hom_fst]⟩
  have hfst : IsProper ((prod.fst : H ⨯ Over.mk f ⟶ H).left) :=
    IsProper.isStableUnderBaseChange.of_isPullback hsq hpull
  have hcomp : IsProper ((prod.fst : H ⨯ Over.mk f ⟶ H).left ≫ H.hom) := inferInstance
  rwa [Over.w (prod.fst : H ⨯ Over.mk f ⟶ H)] at hcomp

/-- A scheme isomorphic to one with irreducible underlying space is irreducible. -/
private theorem irreducibleSpace_of_isIso {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsIso g]
    [IrreducibleSpace Y] : IrreducibleSpace Z :=
  (asIso g).hom.surjective.irreducibleSpace g.continuous

/-- A smooth irreducible scheme of relative dimension `d` over `k` is integral of dimension
`d`. -/
private theorem isIntegral_and_krullDim_of_smooth_irreducible {K : Type u} [Field K]
    (d : ℕ) (H : Over (Spec (.of K)))
    [hsm : SmoothOfRelativeDimension d H.hom] [IrreducibleSpace H.left] :
    IsIntegral H.left ∧ topologicalKrullDim H.left = d := by
  have : Nonempty H.left := inferInstance
  have : Smooth H.hom := hsm.smooth
  have : IsReduced H.left := isReduced_of_smooth H.hom
  exact ⟨isIntegral_of_irreducibleSpace_of_isReduced _,
    topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field d H.hom⟩

/-- **The Hilbert schemes of points of a smooth proper curve are proper and irreducible.** Let
`H d` represent `Hilb^d_{X/k}` for every `d`. Then `H d` is proper over `k` with irreducible
underlying space. -/
theorem isProper_hom_and_irreducibleSpace_of_represents [IsCurve k f] [Smooth f] [IsProper f]
    (H : ℕ → Over (Spec (.of k)))
    (hH : ∀ d : ℕ, RepresentsHilbertFunctorOfRank (Over.mk f) (H d) d) (d : ℕ) :
    IsProper (H d).hom ∧ IrreducibleSpace (H d).left := by
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
    smoothOfRelativeDimension_one_of_isCurve _ f
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  induction d with
  | zero =>
    have : IsIso (H 0).hom := isIso_hom_of_representsHilbertFunctorOfRank_zero (hH 0)
    exact ⟨inferInstance, irreducibleSpace_of_isIso (inv (H 0).hom)⟩
  | succ d ih =>
    obtain ⟨_, _⟩ := ih
    let a := addPoint (hH d) (hH (d + 1))
    let p := a.left
    have hrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p (d + 1) :=
      (isPointAddition_addPoint (hH d) (hH (d + 1))).isFiniteLocallyFreeOfRank_left
    have : IsFinite p := Stacks.Morphisms.isFinite_of_isFiniteLocallyFreeOfRank p (d + 1)
    have hsurj : Surjective p := by
      obtain ⟨-, _, -⟩ :=
        (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation p).mp
          (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree p (d + 1))
      refine p.one_le_finrank_iff_surjective.mp fun y => ?_
      rw [(Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq p (d + 1)).mp
        hrank y]
      exact Nat.succ_le_succ (Nat.zero_le d)
    have hsrc : IsProper (H d ⨯ Over.mk f).hom := isProper_prod_hom f (H d)
    have : IrreducibleSpace (H d ⨯ Over.mk f).left :=
      irreducibleSpace_prod_left k (H d) (Over.mk f)
    have hpq : p ≫ (H (d + 1)).hom = (H d ⨯ Over.mk f).hom := Over.w a
    have : UniversallyClosed (p ≫ (H (d + 1)).hom) := by
      rw [hpq]
      infer_instance
    have hUC : UniversallyClosed (H (d + 1)).hom :=
      UniversallyClosed.of_comp_surjective p (H (d + 1)).hom
    have : UniversallyClosed a.left := inferInstanceAs (UniversallyClosed p)
    have : Surjective a.left := hsurj
    have hsep : IsSeparated (H (d + 1)).hom := isSeparated_of_surjective_universallyClosed a
    have : Smooth (H (d + 1)).hom :=
      (smoothOfRelativeDimension_of_represents H hH (d + 1)).smooth
    have : LocallyOfFiniteType (H (d + 1)).hom := inferInstance
    exact ⟨(isProper_iff _).2 ⟨hsep, hUC, inferInstance⟩,
      (Scheme.Hom.surjective p).irreducibleSpace p.continuous⟩

/-- **Part (1) of [Stacks, Tag 0B9I], for the representing schemes.** Let `k` be an
algebraically closed field, let `X` be a smooth proper curve over `k`, and let `H d` represent
the Hilbert functor `Hilb^d_{X/k}` for every `d`. Then `H d` is a proper variety over `k`, smooth
of relative dimension `d`, irreducible (hence connected) and of dimension `d`. -/
theorem hilbertScheme_isProper_smooth_irreducible_dim [IsCurve k f] [Smooth f] [IsProper f]
    (H : ℕ → Over (Spec (.of k)))
    (hH : ∀ d : ℕ, RepresentsHilbertFunctorOfRank (Over.mk f) (H d) d) (d : ℕ) :
    IsProper (H d).hom ∧ SmoothOfRelativeDimension d (H d).hom ∧ IrreducibleSpace (H d).left ∧
      IsIntegral (H d).left ∧ topologicalKrullDim (H d).left = d := by
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
    smoothOfRelativeDimension_one_of_isCurve _ f
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  obtain ⟨hprop, hirr⟩ := isProper_hom_and_irreducibleSpace_of_represents f H hH d
  have : SmoothOfRelativeDimension d (H d).hom := smoothOfRelativeDimension_of_represents H hH d
  have := isIntegral_and_krullDim_of_smooth_irreducible d (H d)
  exact ⟨hprop, inferInstance, hirr, this⟩

/-- **Part (1) of [Stacks, Tag 0B9I], for one representing scheme.** Let `k` be an algebraically
closed field and `X` a smooth proper curve over `k` such that every Hilbert functor
`Hilb^e_{X/k}` is representable. Then any scheme `H` representing `Hilb^d_{X/k}` is a proper
variety over `k`, smooth of relative dimension `d`, irreducible and of dimension `d`. -/
theorem isProper_smooth_irreducible_dim_of_represents [IsCurve k f] [Smooth f] [IsProper f]
    (hall : ∀ e : ℕ, ∃ H : Over (Spec (.of k)),
      Nonempty (RepresentsHilbertFunctorOfRank (Over.mk f) H e))
    {d : ℕ} {H : Over (Spec (.of k))} (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d) :
    IsProper H.hom ∧ SmoothOfRelativeDimension d H.hom ∧ IrreducibleSpace H.left ∧
      IsIntegral H.left ∧ topologicalKrullDim H.left = d := by
  choose Hs hHs using hall
  let hHs' : ∀ e, RepresentsHilbertFunctorOfRank (Over.mk f) (Hs e) e := fun e => (hHs e).some
  obtain ⟨_, _, _, -, -⟩ := hilbertScheme_isProper_smooth_irreducible_dim f Hs hHs' d
  let c := RepresentsHilbertFunctorOfRank.compare hH (hHs' d)
  let c' := RepresentsHilbertFunctorOfRank.compare (hHs' d) hH
  have : IsIso c := ⟨c', RepresentsHilbertFunctorOfRank.compare_comp_compare hH (hHs' d),
    RepresentsHilbertFunctorOfRank.compare_comp_compare (hHs' d) hH⟩
  have : IsIso c.left := (Over.forget _).map_isIso c
  have hw : c.left ≫ (Hs d).hom = H.hom := Over.w c
  have hsmH : SmoothOfRelativeDimension d H.hom := by
    have : SmoothOfRelativeDimension (0 + d) (c.left ≫ (Hs d).hom) := inferInstance
    rwa [zero_add, hw] at this
  have hirrH : IrreducibleSpace H.left := irreducibleSpace_of_isIso (inv c.left)
  have := isIntegral_and_krullDim_of_smooth_irreducible d H
  refine ⟨?_, hsmH, hirrH, this⟩
  rw [← hw]
  infer_instance

end Stacks.Hilbert

end
