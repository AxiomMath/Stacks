module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersectionOfCodimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.IteratedProjection
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LocalTranslationFamily
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyLocallyClosed
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinesMeetingAtPoint

/-!
# The Moving Lemma for a not necessarily closed subvariety, scheme theoretically

Tag 0B1T: let `C ⊆ 𝐏^N` be a closed subvariety, `X ⊆ 𝐏^N` a subvariety and `T i ⊆ X` a finite
collection of closed subvarieties, and assume that `C` and `X` intersect properly. Then there is a
closed subvariety `C' ⊆ 𝐏^N × 𝐏^1` such that

1. `C' → 𝐏^1` is dominant;
2. `C'_0 = C` scheme theoretically;
3. `C'` and `X × 𝐏^1` intersect properly;
4. `C'_∞` properly intersects each `T i`.

This file proves the lemma as stated: `X` is a *locally closed* irreducible subset of `𝐏^N`
(a subvariety), each `T i` is irreducible and closed *in `X`*, and clause (2) is the equality of
the scheme-theoretic fibre of `C'` (with its reduced structure) over `0` with `C` (with its reduced
structure), as ideal sheaves on `𝐏^N`.

## The argument, following the source

* `C = 𝐏^N`, or `C ∩ X = ∅`: the constant family `C × 𝐏^1`.
* otherwise `C' ⊆ ℓ × 𝐏^N` is the family of translates `r_g(C)` over a general line `ℓ` of the
  parameter space `𝐏 = 𝐏((End V)ᵛ)` through `[id_V]`. The bad locus of the pair `(C, X̄)` lies in a
  closed set `B` of codimension at least two at each of its points (Tag 0B1S's codimension bound,
  `…ProjectiveSpaceOfModule.exists_isClosed_clauseTwo_badLocus_of_le`, which needs only
  `dim 𝐏^N ≤ dim C + dim X`), and a general line through `[id_V]` meets `B` at most in `[id_V]`
  (`…ProjectiveSpaceOfModule.exists_isOpen_lines_inter_subset_singleton`); at `[id_V]` itself the
  translate is `C`, which meets `X` properly by hypothesis. Off `[id_V]`, `r_g(C)` meets `X̄`, and
  hence `X`, properly: `X` is open dense in `X̄`, so has its dimension. The point `∞` is chosen off
  the bad loci of the pairs `(C, T̄ i)`, which are proper closed subsets of `𝐏`.

  Clause (2) scheme theoretically is
  `…ProjectiveSpaceOfModule.comap_vanishingIdeal_lineProductSection_of_translate`: near `[id_V]`
  the family is the image of the constant family under an automorphism of `Spec R ×_k 𝐏^N` over
  the chart `Spec R` of `ℓ`, whose fibre over `0` is the identity.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.comap_vanishingIdeal_movingFamilySet`: clause (2)
  scheme theoretically for the family of translates.
* `…ProjectiveSpaceOfModule.topologicalKrullDim_criterion_movingFamilySet_of_isLocallyClosed`:
  clause (3) for a locally closed `X`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_movingFamily_of_subvariety`: the four
  clauses over some projective line with some distinct points `0, ∞`; Tag 0B1T over a given line
  with given points is
  `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_movingFamily_of_subvariety_fixed` of
  `StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemmaFixedPoints`.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V]

/-- A nonempty subset of dimension at most `n` has a natural number as dimension. -/
private theorem exists_natCast_topologicalKrullDim_of_nonempty {α : Type*} [TopologicalSpace α]
    {S : Set α} (hS : S.Nonempty) {n : ℕ} (h : topologicalKrullDim ↥S ≤ (n : WithBot ℕ∞)) :
    ∃ m : ℕ, topologicalKrullDim ↥S = (m : WithBot ℕ∞) := by
  refine exists_natCast_of_ne_bot_of_le ?_ h
  rw [ne_eq, topologicalKrullDim_eq_bot_iff_isEmpty, Set.isEmpty_coe_sort]
  exact hS.ne_empty

/-- The proper-intersection inequality holds trivially when the intersection is empty. -/
private theorem topologicalKrullDim_add_le_of_eq_empty {α : Type*} [TopologicalSpace α]
    {S : Set α} (hS : S = ∅) (a b : WithBot ℕ∞) : topologicalKrullDim ↥S + a ≤ b := by
  rw [hS, (topologicalKrullDim_eq_bot_iff_isEmpty _).mpr (by simp only [Set.isEmpty_coe_sort]),
    WithBot.bot_add]
  exact bot_le

/-- The proper-intersection inequality holds trivially when one of the sets is everything. -/
private theorem topologicalKrullDim_univ_inter_add_le {α : Type*} [TopologicalSpace α]
    (A : Set α) : topologicalKrullDim ↥(Set.univ ∩ A) + topologicalKrullDim α ≤
      topologicalKrullDim ↥(Set.univ : Set α) + topologicalKrullDim ↥A := by
  rw [Set.univ_inter, add_comm]
  refine add_le_add_left (le_of_eq ?_) _
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).symm

section Family

variable (L : Submodule k (ParameterModule k V)) [Nontrivial (lineSpace k V L)]

/-- **Clause (2) of Tag 0B1T scheme theoretically, for the family of translates.** If the
endomorphism `Λ(μ₀)` attached to the point `[μ₀]` of the line is a nonzero multiple of the
identity, the scheme-theoretic fibre of the family `C'` of translates of `C` over `[μ₀]`, with the
reduced structure on `C'`, is `C` with its reduced structure. -/
public theorem comap_vanishingIdeal_movingFamilySet {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C : Set (projectiveSpaceOfModule k V)}
    (hC : IsClosed C) (hCirr : IsIrreducible C) {μ₀ : Module.Dual k (lineSpace k V L)}
    (hμ₀ : μ₀ ≠ 0) (c : kˣ) (hc : lineEnd k V L μ₀ = (c : k) • LinearMap.id) :
    (Scheme.IdealSheafData.vanishingIdeal
        (⟨movingFamilySet k V L b C, isClosed_movingFamilySet k V L b hC⟩ :
          Closeds (movingAmbient k V L))).comap
        (lineSection k V L (linearFunctionalPoint k (lineSpace k V L) μ₀ hμ₀)
          (linearFunctionalPoint_isClosed k (lineSpace k V L) μ₀ hμ₀)) =
      Scheme.IdealSheafData.vanishingIdeal (⟨C, hC⟩ : Closeds (projectiveSpaceOfModule k V)) := by
  refine comap_vanishingIdeal_lineProductSection_of_translate (lineEndₗ k V L) C hC hCirr
    (movingFamilySet k V L b C) (isClosed_movingFamilySet k V L b hC) ?_ hμ₀ c hc
  intro μ hμ hunit
  have htop : endDomain k V (lineEnd k V L μ) = ⊤ := by
    have h := mapDomain_eq_top k V hunit.unit
    rwa [IsUnit.unit_spec] at h
  exact movingFibre_movingFamilySet k V L b hC hμ (by rw [htop]; exact Set.subset_univ _)

/-- **The dimension of the constant family on a locally closed irreducible subset** is one more
than the dimension of the subset. -/
public theorem topologicalKrullDim_constantFamily_of_isLocallyClosed
    {X : Set (projectiveSpaceOfModule k V)} (hX : IsLocallyClosed X) (hXirr : IsIrreducible X)
    (hL : Module.finrank k (lineSpace k V L) = 2) :
    topologicalKrullDim ↥(constantFamily k V L X) = topologicalKrullDim ↥X + 1 := by
  obtain ⟨O, hO, hXO⟩ := exists_isOpen_eq_closure_inter hX
  have hconst : constantFamily k V L X =
      constantFamily k V L (closure X) ∩ (ambPoint k V L).base ⁻¹' O := by
    rw [constantFamily, constantFamily, lineProductConstant, lineProductConstant]
    conv_lhs => rw [hXO]
    rw [Set.preimage_inter]
  have hne : (constantFamily k V L (closure X) ∩ (ambPoint k V L).base ⁻¹' O).Nonempty := by
    rw [← hconst]
    obtain ⟨x, hx⟩ := hXirr.nonempty
    obtain ⟨w, hw⟩ := exists_ne (0 : lineSpace k V L)
    obtain ⟨μ, hμw⟩ := Module.Projective.exists_dual_ne_zero k hw
    have hμ : μ ≠ 0 := fun h => hμw (by rw [h]; rfl)
    refine ⟨(lineSection k V L (linearFunctionalPoint k (lineSpace k V L) μ hμ)
      (linearFunctionalPoint_isClosed k (lineSpace k V L) μ hμ)).base x, ?_⟩
    show (ambPoint k V L).base _ ∈ X
    rw [ambPoint_lineSection]
    exact hx
  rw [hconst, topologicalKrullDim_inter_isOpen_eq k (movingAmbientToSpec k V L)
      (isClosed_constantFamily k V L _ isClosed_closure)
      (isIrreducible_constantFamily k V L _ isClosed_closure hXirr.closure)
      (hO.preimage (ambPoint k V L).continuous) hne,
    topologicalKrullDim_constantFamily' k V L _ isClosed_closure hL,
    ← topologicalKrullDim_eq_closure_of_isLocallyClosed k (projectiveSpaceOfModuleToSpec k V) hX
      hXirr]

/-- **Clause (3) of Tag 0B1T for a locally closed `X`.** If every translate of `C` along the line
meets `X` properly, the family `C'` meets the constant family `X × ℓ` properly. The proof is that
of `AlgebraicGeometry.ProjectiveSpaceOfModule.intersectProperly_criterion_movingFamilySet`, with
the slice bound and the dimension of the constant family taken for a locally closed `X`. -/
public theorem topologicalKrullDim_criterion_movingFamilySet_of_isLocallyClosed {ι : Type*}
    [Fintype ι] (b : Module.Basis ι k (lineSpace k V L)) {C X : Set (projectiveSpaceOfModule k V)}
    (hC : IsClosed C) (hCne : C.Nonempty) (hX : IsLocallyClosed X) (hXirr : IsIrreducible X)
    (hL : Module.finrank k (lineSpace k V L) = 2)
    (hCg : ∀ mu : Module.Dual k (lineSpace k V L), mu ≠ 0 →
      C ⊆ (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V)))
    (hgood : ∀ mu : Module.Dual k (lineSpace k V L), mu ≠ 0 →
      IsGoodEndomorphism k V C X (lineEnd k V L mu))
    (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set (movingLine k V L)))
    (hfib : movingFibre k V L lam hlam (movingFamilySet k V L b C) = C)
    (hirr : IsIrreducible (movingFamilySet k V L b C))
    (hdom : closure ((ambLine k V L).base '' movingFamilySet k V L b C) = Set.univ) :
    topologicalKrullDim ↥(movingFamilySet k V L b C ∩ constantFamily k V L X) +
        topologicalKrullDim (movingAmbient k V L) ≤
      topologicalKrullDim ↥(movingFamilySet k V L b C) +
        topologicalKrullDim ↥(constantFamily k V L X) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.finrank k V = n + 1 :=
    ⟨Module.finrank k V - 1, by have := Module.finrank_pos (R := k) (M := V); omega⟩
  have hN : topologicalKrullDim (projectiveSpaceOfModule k V) = (n : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hn
  have hfinite : ∀ {S : Set (projectiveSpaceOfModule k V)}, S.Nonempty →
      ∃ m : ℕ, topologicalKrullDim ↥S = (m : WithBot ℕ∞) := by
    intro S hSne
    refine exists_natCast_topologicalKrullDim_of_nonempty hSne (n := n) ?_
    rw [← hN]
    exact topologicalKrullDim_subspace_le _ _
  obtain ⟨c, hc⟩ := hfinite hCne
  obtain ⟨x, hx⟩ := hfinite hXirr.nonempty
  have hslice : ∀ mu : Module.Dual k (lineSpace k V L), mu ≠ 0 →
      topologicalKrullDim ↥(endProjectionImage k V (lineEnd k V L mu) C ∩ X) +
        (n : WithBot ℕ∞) ≤ (c : WithBot ℕ∞) + (x : WithBot ℕ∞) := by
    intro mu hmu
    obtain ⟨-, hdim⟩ := hgood mu hmu
    rw [← hN]
    refine le_trans hdim (add_le_add ?_ (le_of_eq hx))
    exact le_trans (topologicalKrullDim_endProjectionImage_le k V (lineEnd k V L mu) hC
      (hCg mu hmu)) (le_of_eq hc)
  have hSlc : IsLocallyClosed (movingFamilySet k V L b C ∩ constantFamily k V L X) :=
    (isClosed_movingFamilySet k V L b hC).isLocallyClosed.inter
      (hX.preimage (ambPoint k V L).continuous)
  have : JacobsonSpace (movingAmbient k V L) :=
    LocallyOfFiniteType.jacobsonSpace (movingAmbientToSpec k V L)
  by_cases hempty : (movingFamilySet k V L b C ∩ constantFamily k V L X) = ∅
  · exact topologicalKrullDim_add_le_of_eq_empty hempty _ _
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨z', hz', hz'c⟩ := exists_isClosed_singleton_mem_of_isLocallyClosed ⟨z, hz⟩ hSlc
  have hlamz : IsClosed ({(ambLine k V L).base z'} : Set (movingLine k V L)) :=
    isClosed_singleton_image_of_isClosed_singleton (ambLine k V L)
      (movingAmbientToSpec k V L) (movingLineToSpec k V L) rfl z' hz'c
  obtain ⟨mu, hmu, hmudef⟩ := exists_eq_linearFunctionalPoint k (lineSpace k V L)
    ((ambLine k V L).base z') hlamz
  have hsne : (endProjectionImage k V (lineEnd k V L mu) C ∩ X).Nonempty := by
    rw [← movingFibre_movingFamilySet_inter_constantFamily k V L b hC hmu (hCg mu hmu)]
    obtain ⟨y, hy⟩ : z' ∈ Set.range (lineSection k V L
        (linearFunctionalPoint k (lineSpace k V L) mu hmu)
        (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu)).base := by
      rw [range_lineSection]
      exact hmudef ▸ rfl
    exact ⟨y, by rw [mem_movingFibre_iff, hy]; exact hz'⟩
  have hnle : n ≤ c + x := by
    obtain ⟨d, hd⟩ : ∃ d : ℕ,
        topologicalKrullDim ↥(endProjectionImage k V (lineEnd k V L mu) C ∩ X) =
          (d : WithBot ℕ∞) := by
      exact exists_natCast_topologicalKrullDim_of_nonempty hsne (n := x)
        (le_trans (topologicalKrullDim_le_of_subset Set.inter_subset_right) (le_of_eq hx))
    have h2 := hslice mu hmu
    rw [hd] at h2
    rw [show ((d : ℕ) : WithBot ℕ∞) + ((n : ℕ) : WithBot ℕ∞) = (((d + n : ℕ)) : WithBot ℕ∞) by
      push_cast; rfl,
      show ((c : ℕ) : WithBot ℕ∞) + ((x : ℕ) : WithBot ℕ∞) = (((c + x : ℕ)) : WithBot ℕ∞) by
      push_cast; rfl, Nat.cast_le] at h2
    omega
  have hm : ∀ lam' : movingLine k V L, IsClosed ({lam'} : Set (movingLine k V L)) →
      topologicalKrullDim ↥(movingFamilySet k V L b C ∩ constantFamily k V L X ∩
        (ambLine k V L).base ⁻¹' {lam'}) ≤ ((c + x - n : ℕ) : WithBot ℕ∞) := by
    intro lam' hlam'
    obtain ⟨nu, hnu, rfl⟩ := exists_eq_linearFunctionalPoint k (lineSpace k V L) lam' hlam'
    rw [← topologicalKrullDim_movingFibre k V L _ hlam',
      movingFibre_movingFamilySet_inter_constantFamily k V L b hC hnu (hCg nu hnu)]
    refine le_natCast_of_add_natCast_le (n := n) ?_
    rw [show ((c + x - n + n : ℕ)) = c + x by omega]
    rw [show (((c + x : ℕ)) : WithBot ℕ∞) = ((c : ℕ) : WithBot ℕ∞) + ((x : ℕ) : WithBot ℕ∞) by
      push_cast; rfl]
    exact hslice nu hnu
  have hupper := topologicalKrullDim_le_of_slice_le_of_isLocallyClosed k V L hSlc hL hm
  have hlower := topologicalKrullDim_add_one_le_movingFamilySet k V L b lam hlam hfib hirr
    hdom hL
  rw [topologicalKrullDim_movingAmbient_eq k V L hL,
    topologicalKrullDim_constantFamily_of_isLocallyClosed k V L hX hXirr hL, hN, hx]
  have harith : (((c + x - n : ℕ)) : WithBot ℕ∞) + 1 + ((n : WithBot ℕ∞) + 1) =
      ((c : ℕ) : WithBot ℕ∞) + 1 + ((((x : ℕ)) : WithBot ℕ∞) + 1) := by
    have h1 : (((c + x - n : ℕ)) : WithBot ℕ∞) + 1 + ((n : WithBot ℕ∞) + 1) =
        (((c + x - n + 1 + n + 1 : ℕ)) : WithBot ℕ∞) := by push_cast; abel
    have h2 : ((c : ℕ) : WithBot ℕ∞) + 1 + ((((x : ℕ)) : WithBot ℕ∞) + 1) =
        (((c + 1 + x + 1 : ℕ)) : WithBot ℕ∞) := by push_cast; abel
    rw [h1, h2, show (c + x - n + 1 + n + 1 : ℕ) = c + 1 + x + 1 by omega]
  calc topologicalKrullDim ↥(movingFamilySet k V L b C ∩ constantFamily k V L X) +
        ((n : WithBot ℕ∞) + 1)
      ≤ (((c + x - n : ℕ)) : WithBot ℕ∞) + 1 + ((n : WithBot ℕ∞) + 1) :=
        add_le_add hupper le_rfl
    _ = ((c : ℕ) : WithBot ℕ∞) + 1 + ((((x : ℕ)) : WithBot ℕ∞) + 1) := harith
    _ ≤ topologicalKrullDim ↥(movingFamilySet k V L b C) +
          ((((x : ℕ)) : WithBot ℕ∞) + 1) := by
        refine add_le_add ?_ le_rfl
        rw [← hc]
        exact hlower

end Family

/-! ### The general-position step for a locally closed `X` -/

omit [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] in
/-- **Goodness passes to a subset of the same dimension.** If `r_g(C)` meets `Y'` properly and
`Y ⊆ Y'` has the dimension of `Y'`, then `r_g(C)` meets `Y` properly. -/
public theorem IsGoodEndomorphism.of_subset_of_topologicalKrullDim_eq
    {C Y Y' : Set (projectiveSpaceOfModule k V)} {g : V →ₗ[k] V} (hYY' : Y ⊆ Y')
    (hdim : topologicalKrullDim ↥Y = topologicalKrullDim ↥Y')
    (h : IsGoodEndomorphism k V C Y' g) : IsGoodEndomorphism k V C Y g := by
  refine ⟨h.1, le_trans (add_le_add (topologicalKrullDim_le_of_subset
    (Set.inter_subset_inter_right _ hYY')) le_rfl) ?_⟩
  rw [hdim]
  exact h.2

/-- A representative of the class `[id_V]` is a nonzero multiple of the identity. -/
public theorem exists_eq_smul_id_of_represents_identity {p : ClosedPoints k (ParameterModule k V)}
    (hp : (p : projectiveSpaceOfModule k (ParameterModule k V)) = identityParameterPoint k V)
    {g : V →ₗ[k] V} (hg : RepresentsParameterPoint k V p g) :
    ∃ c : kˣ, g = (c : k) • LinearMap.id := by
  obtain ⟨hg0, hgeq⟩ := hg
  have hpe : p = (dualEndClosedPointsEquiv k V).symm
      (Projectivization.mk k (LinearMap.id : V →ₗ[k] V) (linearMapId_ne_zero k V)) :=
    Subtype.ext hp
  have hmk : Projectivization.mk k g hg0 =
      Projectivization.mk k (LinearMap.id : V →ₗ[k] V) (linearMapId_ne_zero k V) := by
    rw [← hgeq, hpe, Equiv.apply_symm_apply]
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff k g (LinearMap.id : V →ₗ[k] V) hg0
    (linearMapId_ne_zero k V)).mp hmk
  exact ⟨c, by rw [← hc, Units.smul_def]⟩

/-- **`[id_V]` is good for every pair `(C, X)` which intersects properly**, read on subsets. -/
public theorem isGoodEndomorphism_of_represents_identity
    {C X : Set (projectiveSpaceOfModule k V)}
    (hCX : topologicalKrullDim ↥(C ∩ X) + topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥C + topologicalKrullDim ↥X)
    {p : ClosedPoints k (ParameterModule k V)}
    (hp : (p : projectiveSpaceOfModule k (ParameterModule k V)) = identityParameterPoint k V)
    {g : V →ₗ[k] V} (hg : RepresentsParameterPoint k V p g) :
    IsGoodEndomorphism k V C X g := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_id_of_represents_identity k V hp hg
  have htop : endDomain k V ((c : k) • LinearMap.id) = ⊤ := by
    rw [endDomain_smul]
    exact mapDomain_eq_top k V 1
  refine ⟨by rw [htop]; exact Set.subset_univ _, ?_⟩
  rw [endProjectionImage_of_eq_smul_id k V rfl]
  exact hCX

omit [IsAlgClosed k] in
/-- **Two distinct closed points of a projective space of dimension at least one.** -/
private theorem exists_closedPoint_ne {M : Type u} [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] (hM : 2 ≤ Module.finrank k M) (q : projectiveSpaceOfModule k M) :
    ∃ q' : projectiveSpaceOfModule k M, IsClosed ({q'} : Set _) ∧ q' ≠ q := by
  set b := Module.finBasis k M with hb
  set e0 : Fin (Module.finrank k M) := ⟨0, by omega⟩
  set e1 : Fin (Module.finrank k M) := ⟨1, by omega⟩
  have he : e0 ≠ e1 := by simp [e0, e1, Fin.ext_iff]
  have hc0 : b.coord e0 ≠ 0 := fun h => by
    have := congrArg (fun f : Module.Dual k M => f (b e0)) h
    simp at this
  have hc1 : b.coord e1 ≠ 0 := fun h => by
    have := congrArg (fun f : Module.Dual k M => f (b e1)) h
    simp at this
  have hne : linearFunctionalPoint k M (b.coord e0) hc0 ≠
      linearFunctionalPoint k M (b.coord e1) hc1 := by
    intro h
    have h1 := congrArg (pointSubmodule k M) h
    rw [pointSubmodule_linearFunctionalPoint, pointSubmodule_linearFunctionalPoint] at h1
    have hmem : b e1 ∈ LinearMap.ker (b.coord e0) := by
      simp [Module.Basis.coord_apply, he.symm]
    rw [h1] at hmem
    simp at hmem
  by_cases h0 : linearFunctionalPoint k M (b.coord e0) hc0 = q
  · exact ⟨_, linearFunctionalPoint_isClosed k M _ hc1, fun h => hne (h0.trans h.symm)⟩
  · exact ⟨_, linearFunctionalPoint_isClosed k M _ hc0, h0⟩

/-- **The general-position step of Tag 0B1T for a not necessarily closed `X`.** Let `C ≠ 𝐏(V)` be
a closed subvariety and `X` a locally closed irreducible subset meeting `C` and intersecting it
properly, and let `T i` be finitely many closed subvarieties. Then for the line through `[id_V]`
and any closed point `q ≠ [id_V]` of a nonempty Zariski open subset of `𝐏`, every representative
`g` of every closed point of that line is good for `(C, X)`, and every representative of `q` is
good for each `(C, T i)`. -/
public theorem exists_isOpen_forall_closedPoint_line_isGood_of_isLocallyClosed
    (C : IrreducibleCloseds (projectiveSpaceOfModule k V)) {X : Set (projectiveSpaceOfModule k V)}
    (hX : IsLocallyClosed X) (hXirr : IsIrreducible X)
    (hCX : topologicalKrullDim ↥((C : Set (projectiveSpaceOfModule k V)) ∩ X) +
        topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥(C : Set (projectiveSpaceOfModule k V)) + topologicalKrullDim ↥X)
    (hCne : (C : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    (hCXne : ((C : Set (projectiveSpaceOfModule k V)) ∩ X).Nonempty)
    {ι : Type*} [Finite ι] (T : ι → IrreducibleCloseds (projectiveSpaceOfModule k V)) :
    ∃ U : Set (projectiveSpaceOfModule k (ParameterModule k V)), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U, IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))) →
        q ≠ identityParameterPoint k V ∧
        ∃ L : Submodule k (ParameterModule k V),
          Module.finrank k (ParameterModule k V ⧸ L) = 2 ∧
          identityParameterPoint k V ∈ linearSubspace k (ParameterModule k V) L ∧
          q ∈ linearSubspace k (ParameterModule k V) L ∧
          (∀ p : ClosedPoints k (ParameterModule k V),
            (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
              linearSubspace k (ParameterModule k V) L →
            ∀ g : V →ₗ[k] V, RepresentsParameterPoint k V p g →
              IsGoodEndomorphism k V (C : Set (projectiveSpaceOfModule k V)) X g) ∧
          ∀ p : ClosedPoints k (ParameterModule k V),
            (p : projectiveSpaceOfModule k (ParameterModule k V)) = q →
            ∀ g : V →ₗ[k] V, RepresentsParameterPoint k V p g → ∀ i,
              IsGoodEndomorphism k V (C : Set (projectiveSpaceOfModule k V))
                (T i : Set (projectiveSpaceOfModule k V)) g := by
  have h2 : 2 ≤ Module.finrank k V :=
    two_le_finrank_of_isClosed_ne_univ k V C.isClosed' hCne C.isIrreducible'.nonempty
  have hntP : Nontrivial (ParameterModule k V) := by
    refine Module.nontrivial_of_finrank_pos (R := k) ?_
    rw [Subspace.dual_finrank_eq, Module.finrank_linearMap]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  have h3 : 3 ≤ Module.finrank k (ParameterModule k V) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_linearMap]
    nlinarith
  obtain ⟨nP, hnP⟩ : ∃ n, Module.finrank k (ParameterModule k V) = n + 1 :=
    ⟨Module.finrank k (ParameterModule k V) - 1, by omega⟩
  have : IrreducibleSpace (projectiveSpaceOfModule k (ParameterModule k V)) :=
    irreducibleSpace_projectiveSpaceOfModule_of_finrank_eq k (ParameterModule k V) hnP
  -- the closure of `X` and its dimension
  set Xb : IrreducibleCloseds (projectiveSpaceOfModule k V) :=
    ⟨closure X, hXirr.closure, isClosed_closure⟩ with hXb
  have hdimX : topologicalKrullDim ↥X = topologicalKrullDim ↥(closure X) :=
    topologicalKrullDim_eq_closure_of_isLocallyClosed k (projectiveSpaceOfModuleToSpec k V) hX
      hXirr
  have hle : topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥(C : Set (projectiveSpaceOfModule k V)) +
        topologicalKrullDim ↥(Xb : Set (projectiveSpaceOfModule k V)) := by
    obtain ⟨x₀, hx₀⟩ := hCXne
    have : Nonempty (IrreducibleCloseds ↥((C : Set (projectiveSpaceOfModule k V)) ∩ X)) :=
      ⟨⟨closure {(⟨x₀, hx₀⟩ : ↥((C : Set (projectiveSpaceOfModule k V)) ∩ X))},
        isIrreducible_singleton.closure, isClosed_closure⟩⟩
    calc topologicalKrullDim (projectiveSpaceOfModule k V)
        = 0 + topologicalKrullDim (projectiveSpaceOfModule k V) := (zero_add _).symm
      _ ≤ _ := add_le_add Order.krullDim_nonneg le_rfl
      _ ≤ _ := hCX
      _ = _ := by rw [hdimX]; rfl
  -- the bad loci
  obtain ⟨B₁, hB₁c, hB₁Z, hB₁sup, hB₁codim⟩ :=
    exists_isClosed_two_le_codimension_notMem_endDomain k V
      (C : Set (projectiveSpaceOfModule k V)) C.isClosed' hCne h2
  obtain ⟨BG, hBGc, -, hBGsup, hBGcodim⟩ :=
    exists_isClosed_clauseTwo_badLocus_of_le k V C Xb hle hCne
  obtain ⟨U₀, hU₀o, hU₀ne, hU₀⟩ := exists_isOpen_lines_inter_subset_singleton k
    (ParameterModule k V) h3 (B₁ ∪ BG) (hB₁c.union hBGc)
    (fun x hx => hx.elim (hB₁codim x) (hBGcodim x)) (identityParameterPoint k V)
    (isClosed_identityParameterPoint k V)
  choose O hOo hOne hOgood using fun i => exists_isOpen_nonempty_disjoint_badParameterLocus k V C
    (T i)
  obtain ⟨q', hq'c, hq'⟩ := exists_closedPoint_ne k (by omega) (identityParameterPoint k V)
  set s : Option ι → Set (projectiveSpaceOfModule k (ParameterModule k V)) :=
    fun o => o.elim ({identityParameterPoint k V}ᶜ) O with hs
  have hsopen : ∀ o, IsOpen (s o) := by
    rintro (_ | i)
    · exact (isClosed_identityParameterPoint k V).isOpen_compl
    · exact hOo i
  have hsne : ∀ o, (s o).Nonempty := by
    rintro (_ | i)
    · exact ⟨q', hq'⟩
    · exact hOne i
  refine ⟨U₀ ∩ ⋂ o, s o, hU₀o.inter (isOpen_iInter_of_finite hsopen),
    nonempty_inter_iInter_of_finite s hsopen hsne U₀ hU₀o hU₀ne, ?_⟩
  rintro q ⟨hqU₀, hqs⟩ hqc
  have hqid : q ≠ identityParameterPoint k V := Set.mem_iInter.mp hqs none
  refine ⟨hqid, ?_⟩
  obtain ⟨L, hL2, hidL, hqL, hLB⟩ := hU₀ q hqU₀ hqc
  refine ⟨L, hL2, hidL, hqL, fun p hpL g hg => ?_, fun p hpq g hg i => ?_⟩
  · by_cases hpid : (p : projectiveSpaceOfModule k (ParameterModule k V)) =
        identityParameterPoint k V
    · exact isGoodEndomorphism_of_represents_identity k V hCX hpid hg
    · have hpB : (p : projectiveSpaceOfModule k (ParameterModule k V)) ∉ B₁ ∪ BG := fun h =>
        hpid (hLB ⟨hpL, h⟩)
      obtain ⟨hg0, hgmk⟩ := hg
      have hdom : (C : Set (projectiveSpaceOfModule k V)) ⊆
          (endDomain k V g : Set (projectiveSpaceOfModule k V)) := by
        by_contra hcon
        exact hpB (Or.inl (hB₁sup p g hg0 hgmk hcon))
      have hgoodb : IsGoodEndomorphism k V (C : Set (projectiveSpaceOfModule k V))
          (Xb : Set (projectiveSpaceOfModule k V)) g := by
        by_contra hcon
        exact hpB (Or.inr (hBGsup p g ⟨hg0, hgmk⟩ hdom hcon))
      exact IsGoodEndomorphism.of_subset_of_topologicalKrullDim_eq k V subset_closure hdimX
        hgoodb
  · have hqO : (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ O i := by
      rw [hpq]
      exact Set.mem_iInter.mp hqs (some i)
    exact isGoodEndomorphism_of_notMem_badParameterLocus k V (hOgood i p hqO) hg

/-! ### The constant family -/

/-- **The constant family `C × 𝐏^1` over `𝐏(k²)`**, with two distinct closed points `0, ∞`: it is
dominant over `𝐏^1`, its scheme-theoretic fibre over `0` is `C`, its fibre over `∞` is `C`, and it
meets the constant family of any `X` in the constant family of `C ∩ X`. -/
private theorem exists_constantFamily_projectiveLine
    (C : IrreducibleCloseds (projectiveSpaceOfModule k V)) :
    ∃ (zero infty : projectiveSpaceOfModule k (Fin 2 → k))
      (hzero : IsClosed ({zero} : Set _)) (hinfty : IsClosed ({infty} : Set _)),
      zero ≠ infty ∧
      ∃ Cfam : IrreducibleCloseds (lineProduct k V (Fin 2 → k)),
        (Cfam : Set _) = lineProductConstant k V (Fin 2 → k) (C : Set _) ∧
        closure ((lineProductLine k V (Fin 2 → k)).base '' (Cfam : Set _)) = Set.univ ∧
        (Scheme.IdealSheafData.vanishingIdeal (⟨Cfam, Cfam.isClosed'⟩ : Closeds _)).comap
            (lineProductSection k V (Fin 2 → k) zero hzero) =
          Scheme.IdealSheafData.vanishingIdeal (⟨C, C.isClosed'⟩ : Closeds _) ∧
        lineProductFibre k V (Fin 2 → k) infty hinfty (Cfam : Set _) = (C : Set _) := by
  have : IrreducibleSpace (projectiveSpaceOfModule k (Fin 2 → k)) :=
    irreducibleSpace_projectiveSpaceOfModule_of_finrank_eq k (Fin 2 → k) (n := 1)
      (by rw [Module.finrank_fin_fun])
  obtain ⟨w, hw⟩ := exists_ne (0 : Fin 2 → k)
  obtain ⟨μ, hμw⟩ := Module.Projective.exists_dual_ne_zero k hw
  have hμ : μ ≠ 0 := fun h => hμw (by rw [h]; rfl)
  set zero := linearFunctionalPoint k (Fin 2 → k) μ hμ with hzerodef
  have hzero := linearFunctionalPoint_isClosed k (Fin 2 → k) μ hμ
  obtain ⟨infty, hinfty, hne⟩ := exists_closedPoint_ne k (M := Fin 2 → k)
    (by rw [Module.finrank_fin_fun]) zero
  refine ⟨zero, infty, hzero, hinfty, Ne.symm hne,
    ⟨lineProductConstant k V (Fin 2 → k) (C : Set _),
      isIrreducible_lineProductConstant k V (Fin 2 → k) _ C.isClosed' C.isIrreducible',
      isClosed_lineProductConstant k V (Fin 2 → k) _ C.isClosed'⟩, rfl, ?_, ?_, ?_⟩
  · refine closure_eq_univ_of_closedPoints_subset fun lam hlam => ?_
    refine mem_image_lineProductLine_of_lineProductFibre_nonempty k V (Fin 2 → k) lam
      (mem_closedPoints_iff.mp hlam) ?_
    show (lineProductFibre k V (Fin 2 → k) lam _
      (lineProductConstant k V (Fin 2 → k) (C : Set _))).Nonempty
    rw [lineProductFibre_lineProductConstant]
    exact C.isIrreducible'.nonempty
  · exact comap_vanishingIdeal_lineProductConstant k V (Fin 2 → k) _ C.isClosed'
      C.isIrreducible' zero hzero
  · exact lineProductFibre_lineProductConstant k V (Fin 2 → k) _ infty hinfty

/-! ### Tag 0B1T -/

/-- **Tag 0B1T with the line and its points chosen.** Let `C` be a closed subvariety of
`𝐏^N = 𝐏(V)`, let `X` be a
subvariety of `𝐏^N` — an irreducible locally closed subset, not necessarily closed — and let
`T i ⊆ X` be finitely many closed subvarieties of `X` (irreducible subsets of `X`, closed in `X`).
Assume that `C` and `X` intersect properly. Then there are a projective line `𝐏^1 = 𝐏(W)`,
`dim_k W = 2`, two distinct closed points `0` and `∞` of it, and a closed subvariety `C'` of
`𝐏^1 × 𝐏^N` such that

1. `C' → 𝐏^1` is dominant;
2. `C'_0 = C` scheme theoretically: pulling the ideal sheaf of the reduced closed subscheme on `C'`
   back along the section of `𝐏^1 × 𝐏^N ⟶ 𝐏^N` at `0` gives the ideal sheaf of the reduced closed
   subscheme on `C`;
3. `C'` and `X × 𝐏^1` intersect properly in `𝐏^1 × 𝐏^N`;
4. `C'_∞` properly intersects each `T i` in `𝐏^N`.

Proper intersection is the dimension criterion of Definition 0AZQ,
`dim (A ∩ B) + dim (ambient) ≤ dim A + dim B`, read on the subsets themselves, which is what the
source's "intersect properly" means for subvarieties that need not be closed. -/
public theorem exists_movingFamily_of_subvariety
    (C : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (X : Set (projectiveSpaceOfModule k V)) (hX : IsLocallyClosed X) (hXirr : IsIrreducible X)
    (hCX : topologicalKrullDim ↥((C : Set (projectiveSpaceOfModule k V)) ∩ X) +
        topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥(C : Set (projectiveSpaceOfModule k V)) + topologicalKrullDim ↥X)
    {ι : Type*} [Finite ι] (T : ι → Set (projectiveSpaceOfModule k V))
    (hTX : ∀ i, T i ⊆ X) (hTc : ∀ i, IsClosed {x : X | x.1 ∈ T i})
    (hTirr : ∀ i, IsIrreducible (T i)) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module k W) (_ : FiniteDimensional k W)
        (_ : Nontrivial W), Module.finrank k W = 2 ∧
      ∃ (zero infty : projectiveSpaceOfModule k W)
        (hzero : IsClosed ({zero} : Set (projectiveSpaceOfModule k W)))
        (hinfty : IsClosed ({infty} : Set (projectiveSpaceOfModule k W))),
        zero ≠ infty ∧
        ∃ Cfam : IrreducibleCloseds (lineProduct k V W),
          closure ((lineProductLine k V W).base '' (Cfam : Set (lineProduct k V W))) =
              Set.univ ∧
          (Scheme.IdealSheafData.vanishingIdeal
                (⟨Cfam, Cfam.isClosed'⟩ : Closeds (lineProduct k V W))).comap
              (lineProductSection k V W zero hzero) =
            Scheme.IdealSheafData.vanishingIdeal
              (⟨C, C.isClosed'⟩ : Closeds (projectiveSpaceOfModule k V)) ∧
          topologicalKrullDim ↥((Cfam : Set (lineProduct k V W)) ∩ lineProductConstant k V W X) +
              topologicalKrullDim (lineProduct k V W) ≤
            topologicalKrullDim ↥(Cfam : Set (lineProduct k V W)) +
              topologicalKrullDim ↥(lineProductConstant k V W X) ∧
          ∀ i, topologicalKrullDim
                ↥(lineProductFibre k V W infty hinfty (Cfam : Set (lineProduct k V W)) ∩ T i) +
              topologicalKrullDim (projectiveSpaceOfModule k V) ≤
            topologicalKrullDim
                ↥(lineProductFibre k V W infty hinfty (Cfam : Set (lineProduct k V W))) +
              topologicalKrullDim ↥(T i) := by
  -- each `T i` is locally closed, with the dimension of its closure
  have hTdim : ∀ i, topologicalKrullDim ↥(T i) = topologicalKrullDim ↥(closure (T i)) := by
    intro i
    obtain ⟨F, hF, hFT⟩ := isClosed_induced_iff.mp (hTc i)
    have hTXF : T i = X ∩ F := by
      ext y
      constructor
      · intro hy
        exact ⟨hTX i hy, (Set.ext_iff.mp hFT ⟨y, hTX i hy⟩).2 hy⟩
      · rintro ⟨hyX, hyF⟩
        exact (Set.ext_iff.mp hFT ⟨y, hyX⟩).1 hyF
    have hlc : IsLocallyClosed (T i) := hTXF ▸ hX.inter hF.isLocallyClosed
    exact topologicalKrullDim_eq_closure_of_isLocallyClosed k (projectiveSpaceOfModuleToSpec k V)
      hlc (hTirr i)
  by_cases hCuniv : (C : Set (projectiveSpaceOfModule k V)) = Set.univ
  · -- `C = 𝐏^N`: the constant family
    obtain ⟨zero, infty, hzero, hinfty, hzi, Cfam, hCfam, hdom, hfib0, hfibinf⟩ :=
      exists_constantFamily_projectiveLine k V C
    refine ⟨Fin 2 → k, inferInstance, inferInstance, inferInstance, inferInstance,
      Module.finrank_fin_fun k, zero, infty, hzero, hinfty, hzi, Cfam, hdom, hfib0, ?_, ?_⟩
    · have hCf : (Cfam : Set (lineProduct k V (Fin 2 → k))) = Set.univ := by
        rw [hCfam, hCuniv, lineProductConstant_univ]
      rw [hCf]
      exact topologicalKrullDim_univ_inter_add_le _
    · intro i
      rw [hfibinf, hCuniv]
      exact topologicalKrullDim_univ_inter_add_le _
  rcases Set.eq_empty_or_nonempty ((C : Set (projectiveSpaceOfModule k V)) ∩ X) with hCX0 | hCXne
  · -- `C ∩ X = ∅`: the constant family
    obtain ⟨zero, infty, hzero, hinfty, hzi, Cfam, hCfam, hdom, hfib0, hfibinf⟩ :=
      exists_constantFamily_projectiveLine k V C
    refine ⟨Fin 2 → k, inferInstance, inferInstance, inferInstance, inferInstance,
      Module.finrank_fin_fun k, zero, infty, hzero, hinfty, hzi, Cfam, hdom, hfib0, ?_, ?_⟩
    · refine topologicalKrullDim_add_le_of_eq_empty ?_ _ _
      rw [hCfam, lineProductConstant, lineProductConstant, ← Set.preimage_inter, hCX0,
        Set.preimage_empty]
    · intro i
      refine topologicalKrullDim_add_le_of_eq_empty ?_ _ _
      rw [hfibinf]
      exact Set.subset_eq_empty (Set.inter_subset_inter_right _ (hTX i)) hCX0
  -- `C` meets `X`: the family of translates over a general line through `[id_V]`
  set Tb : ι → IrreducibleCloseds (projectiveSpaceOfModule k V) :=
    fun i => ⟨closure (T i), (hTirr i).closure, isClosed_closure⟩ with hTb
  obtain ⟨U, hUo, hUne, hU⟩ :=
    exists_isOpen_forall_closedPoint_line_isGood_of_isLocallyClosed k V C hX hXirr hCX hCuniv
      hCXne Tb
  have : JacobsonSpace (projectiveSpaceOfModule k (ParameterModule k V)) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec k (ParameterModule k V))
  obtain ⟨q, hqU, hqc⟩ := exists_isClosed_singleton_mem_of_isLocallyClosed hUne hUo.isLocallyClosed
  obtain ⟨hqid, L, hL2, hidL, hqL, hgood, hTgood⟩ := hU q hqU hqc
  have hL2' : Module.finrank k (lineSpace k V L) = 2 := hL2
  have hNT : Nontrivial (lineSpace k V L) :=
    Module.nontrivial_of_finrank_pos (R := k) (by rw [hL2']; omega)
  set b := Module.finBasisOfFinrankEq k (lineSpace k V L) hL2' with hb
  obtain ⟨zero, hzero, hzeroim⟩ := exists_movingLine_point k V L hidL
    (isClosed_identityParameterPoint k V)
  obtain ⟨mu0, hmu0, hzerodef⟩ := exists_eq_linearFunctionalPoint k (lineSpace k V L) zero hzero
  subst hzerodef
  obtain ⟨infty, hinfty, hinftyim⟩ := exists_movingLine_point k V L hqL hqc
  obtain ⟨mu1, hmu1, hinftydef⟩ :=
    exists_eq_linearFunctionalPoint k (lineSpace k V L) infty hinfty
  subst hinftydef
  have hgoodmu : ∀ (mu : Module.Dual k (lineSpace k V L)), mu ≠ 0 →
      IsGoodEndomorphism k V (C : Set (projectiveSpaceOfModule k V)) X (lineEnd k V L mu) := by
    intro mu hmu
    obtain ⟨p, -, hpL, hprep⟩ := exists_representsParameterPoint_of_movingLine k V L hmu
    exact hgood p hpL (lineEnd k V L mu) hprep
  have hCg : ∀ (mu : Module.Dual k (lineSpace k V L)), mu ≠ 0 →
      (C : Set (projectiveSpaceOfModule k V)) ⊆
        (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V)) :=
    fun mu hmu => (hgoodmu mu hmu).1
  have hCclosed : IsClosed (C : Set (projectiveSpaceOfModule k V)) := C.isClosed'
  have hCirr : IsIrreducible (C : Set (projectiveSpaceOfModule k V)) := C.isIrreducible'
  have hSclosed := isClosed_movingFamilySet k V L b hCclosed
  have hSirr := isIrreducible_movingFamilySet k V L b hCclosed hCirr hCirr.nonempty hCg
  -- the point `0` is the class of a multiple of the identity
  obtain ⟨p0, hp0def, -, hp0rep⟩ := exists_representsParameterPoint_of_movingLine k V L hmu0
  have hp0id : (p0 : projectiveSpaceOfModule k (ParameterModule k V)) =
      identityParameterPoint k V := by rw [hp0def]; exact hzeroim
  obtain ⟨c, hc⟩ := exists_eq_smul_id_of_represents_identity k V hp0id hp0rep
  have hfib0 : movingFibre k V L (linearFunctionalPoint k (lineSpace k V L) mu0 hmu0) hzero
      (movingFamilySet k V L b (C : Set (projectiveSpaceOfModule k V))) =
        (C : Set (projectiveSpaceOfModule k V)) := by
    refine (movingFibre_movingFamilySet k V L b hCclosed hmu0 (hCg mu0 hmu0)).trans ?_
    exact endProjectionImage_eq_of_represents_identity k V hp0id hp0rep _
  have hdom : closure ((ambLine k V L).base ''
      movingFamilySet k V L b (C : Set (projectiveSpaceOfModule k V))) = Set.univ := by
    refine closure_image_ambLine_movingFamilySet k V L b _ fun lam hlam => ?_
    obtain ⟨mu, hmu, rfl⟩ := exists_eq_linearFunctionalPoint k (lineSpace k V L) lam hlam
    exact movingFibre_movingFamilySet_nonempty k V L b hCclosed hCirr.nonempty hmu (hCg mu hmu)
  have hzi : linearFunctionalPoint k (lineSpace k V L) mu0 hmu0 ≠
      linearFunctionalPoint k (lineSpace k V L) mu1 hmu1 := by
    intro h
    apply hqid
    rw [← hinftyim, ← h, hzeroim]
  refine ⟨lineSpace k V L, inferInstance, inferInstance, inferInstance, inferInstance, hL2',
    linearFunctionalPoint k (lineSpace k V L) mu0 hmu0,
    linearFunctionalPoint k (lineSpace k V L) mu1 hmu1, hzero, hinfty, hzi,
    ⟨movingFamilySet k V L b (C : Set (projectiveSpaceOfModule k V)), hSirr, hSclosed⟩,
    hdom, ?_, ?_, ?_⟩
  · -- clause (2), scheme theoretically
    exact comap_vanishingIdeal_movingFamilySet k V L b hCclosed hCirr hmu0 c hc
  · -- clause (3)
    exact topologicalKrullDim_criterion_movingFamilySet_of_isLocallyClosed k V L b hCclosed
      hCirr.nonempty hX hXirr hL2' hCg hgoodmu _ hzero hfib0 hSirr hdom
  · -- clause (4)
    intro i
    obtain ⟨p, hpdef, -, hprep⟩ := exists_representsParameterPoint_of_movingLine k V L hmu1
    have hinftyeq : movingFibre k V L (linearFunctionalPoint k (lineSpace k V L) mu1 hmu1)
        hinfty (movingFamilySet k V L b (C : Set (projectiveSpaceOfModule k V))) =
          endProjectionImage k V (lineEnd k V L mu1)
            (C : Set (projectiveSpaceOfModule k V)) :=
      movingFibre_movingFamilySet k V L b hCclosed hmu1 (hCg mu1 hmu1)
    have hgoodi := IsGoodEndomorphism.of_subset_of_topologicalKrullDim_eq k V subset_closure
      (hTdim i) (hTgood p (by rw [hpdef]; exact hinftyim) (lineEnd k V L mu1) hprep i)
    have h2 := hgoodi.2
    rw [← hinftyeq] at h2
    exact h2

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
