module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureAutomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteInertiaConsequences
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineRealization
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineOpenNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSeparatedChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingUnramified

/-!
# An étale cover by well-nigh affine stacks of a stack with finite inertia (Stacks 0DUE)

Let `𝒳` be an algebraic stack over `S` whose inertia `I_𝒳 ⟶ 𝒳` is finite. **Stacks 0DUE** gives
a family of 1-morphisms `g_i : 𝒳_i ⟶ 𝒳` such that

1. `|𝒳| = ⋃ |g_i|(|𝒳_i|)`,
2. each `𝒳_i` is well-nigh affine (Stacks 0DUL),
3. each `I_{𝒳_i} ⟶ 𝒳_i ×_𝒳 I_𝒳` is an isomorphism,
4. each `g_i` is representable by algebraic spaces, separated and étale.

The proof is the source's, at every point `x ∈ |𝒳|`. A finite inertia projection makes `𝒳`
quasi-DM with separated diagonal and the automorphism group at `x` finite
(`StacksFrontier.AlgebraicGeometry.Stacks.FiniteInertiaConsequences`), so Stacks 0DU4 gives an étale
`g : [U/R] ⟶ 𝒳` with `U`, `R` affine and `s`, `t` finite flat of finite presentation, inducing an
isomorphism of automorphism groups at a point `v` over `x`; `[U/R]` is well-nigh affine
(`AlgebraicGeometry.Stack.isWellNighAffine_of_equivalenceOver_quotientStack_realization`). By
Stacks 0DUA (the inertia being universally closed) the locus of `|[U/R]|` where `g` induces
isomorphisms on automorphism groups is open; it contains `v`, and inside it `v` has a well-nigh
affine open neighbourhood `𝒰''` (Stacks 0507, 01ZY and 03JE,
`AlgebraicGeometry.Stack.exists_openSubstack_isWellNighAffine_of_mem`). The restriction
`𝒰'' ⟶ 𝒳` is étale, induces isomorphisms on all automorphism groups, hence is stabilizer
preserving (Stacks 0DU9) and representable by algebraic spaces; it is separated by Stacks 050M,
part (3), because `𝒰''` is separated (Stacks 0DUM) and `Δ_{𝒳/S}` is separated (Stacks 0CL0).

## Main results

* `AlgebraicGeometry.Stack.isOpen_stabilizerPreservingLocus_of_universallyClosed`: the openness
  half of Stacks 0DUA under universal closedness of the inertia, which is all its proof uses.
* `AlgebraicGeometry.Stack.exists_isWellNighAffine_etale_cover`: **Stacks 0DUE**.

## Implementation notes

The index set of the family is the set of points of `𝒳`. Condition (3) is
`AlgebraicGeometry.Stack.IsStabilizerPreserving`; the statement also records the equivalent
pointwise form (Stacks 0DU9) that the induced isomorphism of automorphism groups at every point
of `𝒳_i` holds. "Separated" for a 1-morphism is Stacks 04YW.

## References

* [Stacks Project, Tag 0DUE](https://stacks.math.columbia.edu/tag/0DUE)
* [Stacks Project, Tag 0DU4](https://stacks.math.columbia.edu/tag/0DU4)
* [Stacks Project, Tag 0DUA](https://stacks.math.columbia.edu/tag/0DUA)
* [Stacks Project, Tag 0DUM](https://stacks.math.columbia.edu/tag/0DUM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The stabilizer-preserving locus is open when the inertia of the target is universally
closed** (the openness assertion of Stacks 0DUA). The proof of
`AlgebraicGeometry.Stack.isOpen_stabilizerPreservingLocus` uses of the properness of `I_𝒴 ⟶ 𝒴`
only its universal closedness: the complement of the locus is the image of a closed subset under
a base change of `I_𝒴 ⟶ 𝒴`. -/
theorem isOpen_stabilizerPreservingLocus_of_universallyClosed {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hu : IsUnramified B S hS f)
    (hI : AlgebraicStacks.UniversallyClosed B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒴)) :
    @IsOpen _ (pointTopology B S hS 𝒳.val) (stabilizerPreservingLocus B S hS f) := by
  let := pointTopology B S hS 𝒳.val
  let := pointTopology B S hS (inertiaPullbackSquare B S hS f).pt.val
  rw [← isClosed_compl_iff, compl_stabilizerPreservingLocus_eq_image B S hS f hf hu]
  exact hI 𝒳 f _ (OpenSubstack.isOpen_pointSet B S hS
    (liftsAutomorphismOpenSubstack B S hS f hf hu)).isClosed_compl

/-- **Stacks 0DUE.** Let `𝒳` be an algebraic stack over `S` whose inertia projection
`I_𝒳 ⟶ 𝒳` is finite. Then there are a set `I` and, for `i ∈ I`, 1-morphisms of algebraic stacks
`g_i : 𝒳_i ⟶ 𝒳` such that

1. `|𝒳| = ⋃ |g_i|(|𝒳_i|)`,
2. `𝒳_i` is well-nigh affine (Stacks 0DUL),
3. `I_{𝒳_i} ⟶ 𝒳_i ×_𝒳 I_𝒳` is an isomorphism (equivalently, by Stacks 0DU9, `g_i` induces an
   isomorphism between automorphism groups at every point of `𝒳_i`),
4. `g_i` is representable by algebraic spaces, separated (Stacks 04YW) and étale. -/
@[stacks 0DUE]
theorem exists_isWellNighAffine_etale_cover (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hI : AlgebraicStacks.IsFinite B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    ∃ (ι : Type (u + 1)) (𝒳ᵢ : ι → AlgebraicStacks.{u, w} B S hS) (g : ∀ i, 𝒳ᵢ i ⟶ 𝒳),
      (∀ x : AlgebraicStacks.points B S hS 𝒳,
        ∃ (i : ι) (y : AlgebraicStacks.points B S hS (𝒳ᵢ i)),
          AlgebraicStacks.pointsMap B S hS (g i) y = x) ∧
      (∀ i, IsWellNighAffine.{u, w} B S hS (𝒳ᵢ i)) ∧
      (∀ i, IsStabilizerPreserving B S hS (g i) ∧
        ∀ q : AlgebraicStacks.points B S hS (𝒳ᵢ i), InducesIsomorphismAt B S hS (g i) q) ∧
      (∀ i, IsRepresentableByAlgebraicSpaces B S hS (g i).hom.hom ∧
        AlgebraicStacks.IsSeparated B S hS (g i) ∧ IsEtale B S hS (g i)) := by
  classical
  have hQ := isAbsolutelyQuasiDM_of_isFinite_inertia B S hS 𝒳 hI
  have hΔ := isSeparated_relativeDiagonal_structureMorphism_of_isFinite_inertia B S hS 𝒳 hI
  have hUC := universallyClosed_inertiaProjection_of_isFinite B S hS 𝒳 hI
  -- the construction at one point
  have key : ∀ x : AlgebraicStacks.points B S hS 𝒳,
      ∃ (𝒴 : AlgebraicStacks.{u, w} B S hS) (g : 𝒴 ⟶ 𝒳),
        (∃ y, AlgebraicStacks.pointsMap B S hS g y = x) ∧
        IsWellNighAffine.{u, w} B S hS 𝒴 ∧
        (IsStabilizerPreserving B S hS g ∧
          ∀ q : AlgebraicStacks.points B S hS 𝒴, InducesIsomorphismAt B S hS g q) ∧
        (IsRepresentableByAlgebraicSpaces B S hS g.hom.hom ∧
          AlgebraicStacks.IsSeparated B S hS g ∧ IsEtale B S hS g) := by
    intro x
    obtain ⟨𝒰, g, ⟨v, hvx, hvaut⟩, ⟨hrep, het⟩, G, hU, hR, hP, hUa, -, hsf, hsfl, hslfp, -, htfl,
        htlfp, ⟨e⟩⟩ :=
      exists_etale_quotientStack_inducesIsomorphismAt B S hS 𝒳 hQ hΔ x
        (automorphismGroupHasProperty_isFiniteOverBase_of_isFinite_inertia B S hS 𝒳 hI x)
    have h𝒰 : IsWellNighAffine.{u, w} B S hS 𝒰 :=
      isWellNighAffine_of_equivalenceOver_quotientStack_realization B S hS 𝒰 G hU hR hP hUa hsf
        hsfl hslfp htfl htlfp e
    have hu : IsUnramified B S hS g := isUnramified_of_isEtale B S hS het
    -- the stabilizer-preserving locus (Stacks 0DUA) and a well-nigh affine neighbourhood in it
    obtain ⟨𝒰', h𝒰'⟩ := exists_openSubstack_pointSet_eq B S hS 𝒰 _
      (isOpen_stabilizerPreservingLocus_of_universallyClosed B S hS g hrep hu hUC)
    obtain ⟨𝒰'', hv'', hsub, hwna⟩ := exists_openSubstack_isWellNighAffine_of_mem 𝒰 h𝒰 𝒰' v
      (by rw [h𝒰']; exact hvaut)
    let g'' := 𝒰''.inclusion B S hS ≫ g
    have het'' : IsEtale B S hS g'' := FlatChart.isEtale_inclusion_comp 𝒰'' g hrep het
    have haut'' : ∀ q, InducesIsomorphismAt B S hS g'' q := fun q =>
      inducesIsomorphismAt_openSubstackInclusion_comp B S hS 𝒰'' g q
        (show _ ∈ stabilizerPreservingLocus B S hS g from h𝒰' ▸ hsub ⟨q, rfl⟩)
    have hrep'' : IsRepresentableByAlgebraicSpaces B S hS g''.hom.hom :=
      AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_isEtale_of_inducesIsomorphismAt g''
        het'' haut''
    -- separatedness: Stacks 0DUM, 0CL0 and 050M, part (3)
    have hsepOver : IsSeparatedOver.{u, w} B S hS 𝒰''.toAlgebraicStack := by
      obtain ⟨U, R, s, t, c, hG, hUa', -, hs, ht, hequiv⟩ :=
        hasAffineFiniteLocallyFreeGroupoidPresentation_of_isWellNighAffine B S hS _ hwna
      exact isSeparatedOver_of_representedGroupoid_isFiniteLocallyFree B S hS _ s t c hG hUa' hs
        ht hequiv
    have hcomp : g'' ≫ structureMorphism B S hS 𝒳 = structureMorphism B S hS _ :=
      eq_structureMorphism B S hS _ _
    have hsep'' : AlgebraicStacks.IsSeparated B S hS g'' :=
      AlgebraicStacks.isSeparated_of_comp_of_isSeparated_diagonal B S hS g''
        (structureMorphism B S hS 𝒳) (hcomp ▸ hsepOver) hΔ
    obtain ⟨y, hy⟩ := hv''
    refine ⟨_, g'', ⟨y, ?_⟩, hwna,
      ⟨(inertiaPullbackComparison_isEquivalenceOver_iff_inducesIsomorphismAt B S hS g''
        (isUnramified_of_isEtale B S hS het'')).2 haut'', haut''⟩, hrep'', hsep'', het''⟩
    rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply, hy, hvx]
  choose 𝒴 g hcov hwna hstab hprop using key
  exact ⟨AlgebraicStacks.points B S hS 𝒳, 𝒴, g, fun x => ⟨x, hcov x⟩, hwna, hstab, hprop⟩

end AlgebraicGeometry.Stack

end
