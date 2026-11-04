module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatChartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenFiltrationSeparatedNeighbourhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ReasonableDenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree induction of Stacks 03JI

Stacks 03JI, Proposition 68.10.1, says that a reasonable algebraic space over a scheme `S`
contains a dense open subspace which is a scheme.
`StacksFrontier.AlgebraicGeometry.Spaces.ReasonableDenseSchematicLocus` reduces that proposition
to one hypothesis `hchart`: *a nonempty algebraic space over `S` carrying an affine étale chart
which is surjective on points and has universally bounded fibres has a nonempty representable
open subspace.* This file proves `hchart`, modulo Tag 07S8 alone.

The proof is the induction of the source, on an integer `n` bounding the degrees of the fibres
of the chart `b : h_V ⟶ X`. Writing
`∅ = Z₋₁ ⊆ Z₀ ⊆ … ⊆ Z_n = |X|` for the stratification of Tag 07S8 attached to `b`, the top
stratum `X_n` is the open subspace cut out by the complement of `Z_{n-1}`, and either

* `X_n` has a point, and then the restriction of `b` to `X_n` is finite locally free of degree
  `n`, so `X_n` is a scheme by Tag 07S6 and Tag 01ZY — which is
  `AlgebraicGeometry.Space.isRepresentable_of_surjectiveEtale_finiteLocallyFree_of_isImmersion`
  of `StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatChartRepresentable` — and `X_n` is the
  required nonempty representable open subspace; or
* `X_n` has no point, and then `Z_{n-1} = |X|`, so no field-valued fibre of `b` has degree `n`
  and the bound drops to `n - 1`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_of_isClosed_of_restriction_flf`:
  **one step of the induction.** If the complement of a closed set `C` of points of `X` is
  nonempty and the restriction of the chart to the open subspace it cuts out is finite locally
  free, then `X` has a nonempty representable open subspace.
* `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_of_bound_of_h07S8`: **the
  degree induction.** For every `n`, an algebraic space with a nonempty point set and an affine
  étale chart surjective on points whose field-valued fibres all have degree at most `n` has a
  nonempty representable open subspace.
* `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_of_h07S8`: **the hypothesis
  `hchart` of Tag 03JI**, with the integer bound replaced by
  `AlgebraicGeometry.Space.HasUniversallyBoundedFibers`.
* `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_h07S8`:
  **the conclusion of Tag 03JI for a reasonable algebraic space over `S`, modulo Tag 07S8
  alone.**

## Implementation notes

**The one hypothesis carried.** `h07S8` is Tag 07S8 for a morphism from an object of the site
to an algebraic space, stated in the style of `h086R`: the four morphism hypotheses of the
source (flat, locally of finite presentation, separated, locally quasi-finite) in the forms
`AlgebraicGeometry.Space.IsFlat`, `AlgebraicGeometry.Space.IsLocallyOfFinitePresentation`,
`AlgebraicGeometry.Space.IsSeparated` and `AlgebraicGeometry.Space.IsLocallyQuasiFinite`, an
integer `n` bounding the degrees of the field-valued fibres, and as conclusion a chain of
closed subsets of the point set of the target with the universal property of the source. Three
deliberate weakenings make the hypothesis *easier* to discharge than the source's statement,
and nothing below needs more:

* the strata are given as closed **subsets of the point set**, not as reduced closed
  subspaces — only their point sets are used;
* the chain is asked to be `Monotone`, not strictly increasing;
* the universal property is asked only for `r ≤ n`, the range in which the source defines the
  strata.

Indexing is shifted by one so that the chain is indexed by `ℕ`: `Z r` is the source's
`Z_{r-1}`, so `Z 0 = ∅` is the source's `Z₋₁`, `Z (n+1) = |X|` is the source's `Z_n`, and the
source's stratum `X_r = Z_r ∖ Z_{r-1}` is `Z (r+1) ∖ Z r`. In particular the top stratum is
the complement of `Z n`, which is what makes the first branch of the induction available at
`n = 0` as well: there `Z 0 = ∅`, so the top stratum is the whole of `X`, which is nonempty.
No separate base case argument is needed, and in particular the degree-zero case — where the
chart would be empty — never has to be excluded.

**The fibre of a morphism of algebraic spaces.** "The projection `V ×_X T ⟶ T` is finite
locally free of degree `r`" is read as the relative property
`CategoryTheory.MorphismProperty.presheaf` of
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property r`, quantified over every cartesian
square realizing the fibre product. That is the repository's form of a property of a morphism
of algebraic spaces, and quantifying over the squares rather than over one chosen square is
not a strengthening: the relative property respects isomorphisms, and two pullbacks of one
cospan differ by an isomorphism of their sources.

**Why the density step does not appear.** The source finishes the induction by checking that
`X'' ∪ X_n` is dense, and uses Tag 03HN (the interior of `Z_{n-1}`) to make the complementary
piece open. Neither is needed here. The reduction in
`StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus` turns *local* nonemptiness of the
representable locus into global density through the schematic locus of Tag 03JH, so only the
nonemptiness statement has to be proved; and in the nonemptiness statement the second branch
of the induction is `Z_{n-1} = |X|`, which is already open, so no interior is formed. This is
why the second branch applies the induction hypothesis to `X` itself rather than to a smaller
open subspace.

**Étaleness and surjectivity of the restricted chart** are obtained by base change along the
inclusion of the open subspace, from
`CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange`, not by cancelling the
monomorphism out of a composite; surjectivity of the given chart is converted from its
point-set form by Tag 03H5,
`AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda`. The source of the
restricted chart is an open subscheme of the affine chart, so it comes with an immersion into
an affine scheme, which is the hypothesis of Tag 01ZY used by
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatChartRepresentable`.

**Nothing here carries a Stacks attribute.** Every statement below carries `h07S8`, and
Tag 03JI is not proved.

## References

* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being finite locally free of a fixed rank entails being finite locally free, read through
the forgetful functor to schemes. This is the one monotonicity used below: the universal
property of Tag 07S8 fixes the degree of the restricted chart, and Tag 07S6 only needs finite
local freeness. -/
private theorem inverseImage_isFiniteLocallyFreeOfRank_le (r : ℕ) :
    MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
        (BigFppfOver.toScheme B S hS) ≤
      MorphismProperty.inverseImage (@IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) := fun _ _ f hf =>
  IsFiniteLocallyFreeOfRank.isFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map f) r (h := hf)

/-- Being finite locally free of a fixed rank, read through the forgetful functor to schemes,
is stable under base change in the site. This is the instance which
`CategoryTheory.MorphismProperty.relative_map` needs in order to read a rank statement about a
morphism of the site as a statement about the morphism of representable presheaves it induces;
the scheme-level stability is the first assertion of Tag 02KA. -/
@[ega "I 6.4.6" "more general"]
private theorem inverseImage_isFiniteLocallyFreeOfRank_isStableUnderBaseChange (r : ℕ) :
    (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    apply comp_preservesLimitsOfShape
  constructor
  intro _ _ _ _ _ _ _ _ hsq hg
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := IsFiniteLocallyFreeOfRank.property.{u} r)
    (hsq.map (BigFppfOver.toScheme B S hS)) hg

/-! ### One step of the induction -/

/-- **One step of the degree induction of Stacks 03JI.** Let `X` be an algebraic space over `S`
with an affine étale chart `b : h_V ⟶ X` surjective on points, and let `C` be a closed set of
points of `X` whose complement is nonempty. If the restriction of `b` to the open subspace cut
out by the complement of `C` is finite locally free, then `X` has a nonempty representable open
subspace.

The open subspace is the one cut out by `Cᶜ`. Its restricted chart is étale and surjective
because those properties are stable under base change, it is finite locally free by hypothesis,
and its source is an open subscheme of the affine `V`, hence immersed in an affine scheme; so
`AlgebraicGeometry.Space.isRepresentable_of_surjectiveEtale_finiteLocallyFree_of_isImmersion`,
which is Tag 07S6 together with Tag 01ZY, makes it representable. Its point set is `Cᶜ`, by
part (1) of Tag 03BZ. -/
theorem exists_isRepresentable_isOpenSubspace_of_isClosed_of_restriction_flf
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {V : BigFppfOver B S hS} (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (b : yoneda.obj V ⟶ X)
    (hbsurj : Function.Surjective (pointsMap B S hS (yoneda.obj V) b))
    (hbetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (C : Set (points B S hS X)) (hCclosed : IsClosed C)
    (hCne : (Cᶜ : Set (points B S hS X)).Nonempty)
    (hflf : ∀ (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : P ⟶ yoneda.obj V)
      (pr₂ : P ⟶ (openSubspaceOfPoints B S hS X Cᶜ).toFunctor),
      IsPullback pr₁ pr₂ b (openSubspaceOfPoints B S hS X Cᶜ).ι →
      (MorphismProperty.inverseImage
        (@IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf pr₂) :
    ∃ H : Subfunctor X, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
      (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty := by
  have _ : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    BigFppfOver.hasSheafify_type B S hS
  set G := openSubspaceOfPoints B S hS X Cᶜ with hGdef
  have hG : IsOpenSubspace B S hS G :=
    isOpenSubspace_openSubspaceOfPoints B S hS hX _ hCclosed.isOpen_compl
  have hGrange : Set.range (pointsMap B S hS G.toFunctor G.ι) = Cᶜ :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hGrep : yoneda.relativelyRepresentable G.ι := hG.2.rep
  have hsq : IsPullback (hGrep.fst b) (yoneda.map (hGrep.snd b)) G.ι b := hGrep.isPullback b
  have _hjmopen : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hGrep.snd b)) := hG.2.property_snd b
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hVaff
  have hbase : ∀ (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange],
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf b →
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf (hGrep.fst b) :=
    fun Q _ hb => by
      have := MorphismProperty.relative_isStableUnderBaseChange
        (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)) (F := yoneda)
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip hb
  refine ⟨G, hG, isRepresentable_of_surjectiveEtale_finiteLocallyFree_of_isImmersion B S hS
    ((BigFppfOver.toScheme B S hS).map (hGrep.snd b)) hG.1 (hGrep.fst b)
    (hflf _ (yoneda.map (hGrep.snd b)) (hGrep.fst b) hsq.flip)
    (hbase _
      ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX V b).mpr hbsurj))
    (hbase _ hbetale), ?_⟩
  rw [hGrange]
  exact hCne

/-! ### The induction -/

/-- **The degree induction of Stacks 03JI, modulo Tag 07S8.** Let `h07S8` be Tag 07S8 for a
morphism from an object of the big fppf site over `S` to an algebraic space over `S`: given the
source's four morphism hypotheses and a natural number `n` bounding the degrees of the
field-valued fibres, a `Monotone` chain `Z` of closed subsets of the point set with `Z 0 = ∅`
and `Z (n + 1) = |X|` such that, for `r ≤ n`, the fibre of the morphism over a morphism from an
algebraic space `T` is finite locally free of degree `r` exactly when the image of `|T|` lies in
the stratum `Z (r + 1) ∖ Z r`.

Then every algebraic space over `S` with a nonempty point set and an affine étale chart which
is surjective on points and all of whose field-valued fibres have degree at most `n` has a
nonempty representable open subspace.

This is the source's "we will argue by induction on `n`". At each stage the top stratum is the
complement of `Z n`. If it has a point, then
`AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_of_isClosed_of_restriction_flf`
finishes, the restricted chart being finite locally free of degree `n` by the universal
property. If it has no point, then `Z n = |X|`, so no field-valued fibre can have degree `n` —
a fibre of degree `n` would force the image of a nonempty point set into the empty stratum — and
the bound drops to `n - 1`. -/
theorem exists_isRepresentable_isOpenSubspace_of_bound_of_h07S8
    (h07S8 : ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : BigFppfOver B S hS)
      (g : yoneda.obj W ⟶ X), IsAlgebraicSpace B S hS X →
      IsFlat B S hS g → IsLocallyOfFinitePresentation B S hS g → IsSeparated B S hS g →
      IsLocallyQuasiFinite B S hS g →
      ∀ n : ℕ,
        (∀ (k : Type u) [Field k] (T : BigFppfOver B S hS),
          ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k)) →
          ∀ ξ : yoneda.obj T ⟶ X,
            ∃ (P : BigFppfOver B S hS) (p : P ⟶ T) (i : yoneda.obj P ⟶ yoneda.obj W) (r : ℕ),
              r ≤ n ∧ IsFiniteLocallyFreeOfRank
                ((BigFppfOver.toScheme B S hS).map p) r ∧
              IsPullback i (yoneda.map p) g ξ) →
        ∃ Z : ℕ → Set (points B S hS X), Z 0 = ∅ ∧ (∀ r, IsClosed (Z r)) ∧ Monotone Z ∧
          Z (n + 1) = Set.univ ∧
          ∀ r : ℕ, r ≤ n → ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (h : T ⟶ X),
            IsAlgebraicSpace B S hS T →
            ∀ (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : P ⟶ yoneda.obj W) (pr₂ : P ⟶ T),
              IsPullback pr₁ pr₂ g h →
              ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
                  (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
                Set.range (pointsMap B S hS T h) ⊆ Z (r + 1) \ Z r)) :
    ∀ (n : ℕ) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (V : BigFppfOver B S hS)
      (b : yoneda.obj V ⟶ X), IsAlgebraicSpace B S hS X →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      Function.Surjective (pointsMap B S hS (yoneda.obj V) b) →
      (∀ (k : Type u) [Field k] (T : BigFppfOver B S hS),
        ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k)) →
        ∀ ξ : yoneda.obj T ⟶ X,
          ∃ (P : BigFppfOver B S hS) (p : P ⟶ T) (i : yoneda.obj P ⟶ yoneda.obj V) (r : ℕ),
            r ≤ n ∧ IsFiniteLocallyFreeOfRank
              ((BigFppfOver.toScheme B S hS).map p) r ∧
            IsPullback i (yoneda.map p) b ξ) →
      Nonempty (points B S hS X) →
      ∃ H : Subfunctor X, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty := by
  intro n
  induction n with
  | zero =>
    intro X V b hX hVaff hbetale hbsurj hbound hne
    have hEtale : IsEtale B S hS b := isEtale_of_presheaf_etale B S hS hbetale
    obtain ⟨Z, hZ0, hZc, _hZm, hZtop, hZuniv⟩ := h07S8 X V b hX
      (isFlat_of_isEtale B S hS hEtale)
      (isLocallyOfFinitePresentation_of_isEtale B S hS hEtale)
      (isSeparated_of_isEtale_of_isAffine B S hS hX V hVaff b hEtale)
      (isLocallyQuasiFinite_of_isEtale' B S hS hEtale) 0 hbound
    refine exists_isRepresentable_isOpenSubspace_of_isClosed_of_restriction_flf B S hS hX
      hVaff b hbsurj hbetale (Z 0) (hZc 0) ?_ ?_
    · rw [hZ0, Set.compl_empty]
      exact ⟨hne.some, Set.mem_univ _⟩
    · intro P pr₁ pr₂ hsq
      refine MorphismProperty.relative_monotone
        (inverseImage_isFiniteLocallyFreeOfRank_le B S hS 0) pr₂
        ((hZuniv 0 le_rfl _ (openSubspaceOfPoints B S hS X (Z 0)ᶜ).ι
          (isOpenSubspace_openSubspaceOfPoints B S hS hX _
            (hZc 0).isOpen_compl).1 P pr₁ pr₂ hsq).mpr ?_)
      rw [range_pointsMap_ι_openSubspaceOfPoints, hZtop]
      intro x hx
      exact ⟨Set.mem_univ x, hx⟩
  | succ n ih =>
    intro X V b hX hVaff hbetale hbsurj hbound hne
    have hEtale : IsEtale B S hS b := isEtale_of_presheaf_etale B S hS hbetale
    obtain ⟨Z, _hZ0, hZc, _hZm, hZtop, hZuniv⟩ := h07S8 X V b hX
      (isFlat_of_isEtale B S hS hEtale)
      (isLocallyOfFinitePresentation_of_isEtale B S hS hEtale)
      (isSeparated_of_isEtale_of_isAffine B S hS hX V hVaff b hEtale)
      (isLocallyQuasiFinite_of_isEtale' B S hS hEtale) (n + 1) hbound
    by_cases hC : ((Z (n + 1))ᶜ : Set (points B S hS X)).Nonempty
    · refine exists_isRepresentable_isOpenSubspace_of_isClosed_of_restriction_flf B S hS hX
        hVaff b hbsurj hbetale (Z (n + 1)) (hZc _) hC ?_
      intro P pr₁ pr₂ hsq
      refine MorphismProperty.relative_monotone
        (inverseImage_isFiniteLocallyFreeOfRank_le B S hS (n + 1)) pr₂
        ((hZuniv (n + 1) le_rfl _ (openSubspaceOfPoints B S hS X (Z (n + 1))ᶜ).ι
          (isOpenSubspace_openSubspaceOfPoints B S hS hX _
            (hZc _).isOpen_compl).1 P pr₁ pr₂ hsq).mpr ?_)
      rw [range_pointsMap_ι_openSubspaceOfPoints, hZtop]
      intro x hx
      exact ⟨Set.mem_univ x, hx⟩
    · rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hC
      refine ih X V b hX hVaff hbetale hbsurj ?_ hne
      intro k _ T e ξ
      obtain ⟨P, p, i, r, hrn, hr, hsq⟩ := hbound k T e ξ
      refine ⟨P, p, i, r, ?_, hr, hsq⟩
      rcases Nat.lt_or_ge r (n + 1) with hlt | hge
      · exact Nat.lt_succ_iff.mp hlt
      · exfalso
        have hrs : r = n + 1 := le_antisymm hrn hge
        have _ := inverseImage_isFiniteLocallyFreeOfRank_isStableUnderBaseChange B S hS r
        have hsub := (hZuniv r hrn _ ξ (isAlgebraicSpace_yoneda B S hS T) _ i
          (yoneda.map p) hsq).mp
          (MorphismProperty.relative_map
            (P := MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
              (BigFppfOver.toScheme B S hS)) hr)
        obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
        have hmem : pointsMap B S hS (yoneda.obj T) ξ
            ((pointsEquivScheme B S hS T).symm (e.inv.base x)) ∈ Z (r + 1) \ Z r :=
          hsub ⟨_, rfl⟩
        rw [hrs, hZtop, hC] at hmem
        exact hmem.2 (Set.mem_univ _)

/-! ### Tag 03JI modulo Tag 07S8 -/

/-- **The hypothesis `hchart` of Tag 03JI, modulo Tag 07S8.** A nonempty algebraic space over
`S` carrying an affine étale chart which is surjective on points and has universally bounded
fibres has a nonempty representable open subspace.

This is `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_of_bound_of_h07S8` with
the integer bound extracted from `AlgebraicGeometry.Space.HasUniversallyBoundedFibers`: that
condition gives a bound in `ℤ`, and a natural number bounding the same ranks is its
`Int.toNat`, which is legitimate because a rank is a natural number. -/
theorem exists_isRepresentable_isOpenSubspace_of_h07S8
    (h07S8 : ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : BigFppfOver B S hS)
      (g : yoneda.obj W ⟶ X), IsAlgebraicSpace B S hS X →
      IsFlat B S hS g → IsLocallyOfFinitePresentation B S hS g → IsSeparated B S hS g →
      IsLocallyQuasiFinite B S hS g →
      ∀ n : ℕ,
        (∀ (k : Type u) [Field k] (T : BigFppfOver B S hS),
          ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k)) →
          ∀ ξ : yoneda.obj T ⟶ X,
            ∃ (P : BigFppfOver B S hS) (p : P ⟶ T) (i : yoneda.obj P ⟶ yoneda.obj W) (r : ℕ),
              r ≤ n ∧ IsFiniteLocallyFreeOfRank
                ((BigFppfOver.toScheme B S hS).map p) r ∧
              IsPullback i (yoneda.map p) g ξ) →
        ∃ Z : ℕ → Set (points B S hS X), Z 0 = ∅ ∧ (∀ r, IsClosed (Z r)) ∧ Monotone Z ∧
          Z (n + 1) = Set.univ ∧
          ∀ r : ℕ, r ≤ n → ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (h : T ⟶ X),
            IsAlgebraicSpace B S hS T →
            ∀ (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : P ⟶ yoneda.obj W) (pr₂ : P ⟶ T),
              IsPullback pr₁ pr₂ g h →
              ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
                  (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
                Set.range (pointsMap B S hS T h) ⊆ Z (r + 1) \ Z r))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (V : BigFppfOver B S hS)
    (b : yoneda.obj V ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hbetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hbsurj : Function.Surjective (pointsMap B S hS (yoneda.obj V) b))
    (hbfib : HasUniversallyBoundedFibers B S hS V b)
    (hne : Nonempty (points B S hS X)) :
    ∃ H : Subfunctor X, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
      (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty := by
  obtain ⟨m, hm⟩ := hbfib
  refine exists_isRepresentable_isOpenSubspace_of_bound_of_h07S8 B S hS h07S8 m.toNat X V b hX
    hVaff hbetale hbsurj ?_ hne
  intro k _ T e ξ
  obtain ⟨P, p, i, r, hrm, hr, hsq⟩ := hm k T e ξ
  exact ⟨P, p, i, r, by omega, hr, hsq⟩

/-- **Tag 03JI modulo Tag 07S8.** A reasonable algebraic space over `S` has a representable
open subspace whose point set is dense, as soon as Tag 07S8 is available.

This is
`AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_chartCore` of
`StacksFrontier.AlgebraicGeometry.Spaces.ReasonableDenseSchematicLocus` with its hypothesis
`hchart` discharged by
`AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_of_h07S8`. Everything else in
the proof of Tag 03JI — the locality reduction to one affine chart, the permanence of
reasonableness under passage to an open subspace, the upward transport of an open subspace of
an open subspace, and the passage from local nonemptiness to global density through the
schematic locus of Tag 03JH — is proved there. -/
theorem exists_denseRange_isRepresentable_isOpenSubspace_of_h07S8
    (h07S8 : ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : BigFppfOver B S hS)
      (g : yoneda.obj W ⟶ X), IsAlgebraicSpace B S hS X →
      IsFlat B S hS g → IsLocallyOfFinitePresentation B S hS g → IsSeparated B S hS g →
      IsLocallyQuasiFinite B S hS g →
      ∀ n : ℕ,
        (∀ (k : Type u) [Field k] (T : BigFppfOver B S hS),
          ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k)) →
          ∀ ξ : yoneda.obj T ⟶ X,
            ∃ (P : BigFppfOver B S hS) (p : P ⟶ T) (i : yoneda.obj P ⟶ yoneda.obj W) (r : ℕ),
              r ≤ n ∧ IsFiniteLocallyFreeOfRank
                ((BigFppfOver.toScheme B S hS).map p) r ∧
              IsPullback i (yoneda.map p) g ξ) →
        ∃ Z : ℕ → Set (points B S hS X), Z 0 = ∅ ∧ (∀ r, IsClosed (Z r)) ∧ Monotone Z ∧
          Z (n + 1) = Set.univ ∧
          ∀ r : ℕ, r ≤ n → ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (h : T ⟶ X),
            IsAlgebraicSpace B S hS T →
            ∀ (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : P ⟶ yoneda.obj W) (pr₂ : P ⟶ T),
              IsPullback pr₁ pr₂ g h →
              ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
                  (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
                Set.range (pointsMap B S hS T h) ⊆ Z (r + 1) \ Z r))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hr : IsReasonableSpace B S hS X) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) :=
  exists_denseRange_isRepresentable_isOpenSubspace_of_chartCore B S hS
    (fun Y W c hY hWaff hcetale hcsurj hcfib hYne =>
      exists_isRepresentable_isOpenSubspace_of_h07S8 B S hS h07S8 Y W c hY hWaff hcetale
        hcsurj hcfib hYne)
    hX hr

end AlgebraicGeometry.Space

end
