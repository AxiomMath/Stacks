module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.DominateRationalMapDimTwo
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalSurfacesDimTwo

/-!
# Step 2 of Tag 0C5R: the chain of blowups, and its reduction to a single one

[Stacks, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R) proves that a proper birational
morphism `f : X ⟶ Y` of integral Noetherian schemes regular of dimension two is a sequence of
blowups at closed points. Its step 2 produces, at a closed point `y` outside the maximal open over
which `f` is an isomorphism, a chain of blowups
`X' = Xₙ → Xₙ₋₁ → … → X₀ = X` at closed points over the fibre `f⁻¹(y)` and a morphism
`X' ⟶ Y'` to the blowup of `Y` at `y` making the square commute, and then says: "we want to show
that the morphism `X' → Y'` factors through `X` and hence we can use induction on `n` to reduce to
the case where `X' → X` is the blowup of `X` in a closed point".

This file carries out both halves unconditionally. The chain is
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap_of_dim_two`, which
is [Stacks, Tag 0C5H], applied to the rational map from `X` to the blowup of `Y` at `y` — the
blowup is an isomorphism away from `y`, so the rational map is displayed on `f⁻¹(Y \ {y})`. The
induction on `n` is the induction principle of
`Stacks.ResolutionOfSurfaces.PointBlowupChain` itself: its `step` constructor adds the blowup
*nearest the source*, which is exactly the end the source peels, so `induction hchain` is the
whole of it.

What is left over here is the dichotomy of the source's step 3 at a single blowup,
`Stacks.ResolutionOfSurfaces.PointBlowupDichotomy`, which the declarations below carry as a
hypothesis. It is **not** an assumption of the library: it is proved in
`PointBlowupDichotomyProof.lean` of this directory, as
`Stacks.ResolutionOfSurfaces.pointBlowupDichotomy`; see "What is and is not proved" below.

## Main definitions

* `Stacks.ResolutionOfSurfaces.pointExceptionalCurve` — the exceptional curve of the blowup of a
  scheme at a reduced closed point.
* `Stacks.ResolutionOfSurfaces.PointBlowupDichotomy` — the dichotomy of step 3 of
  [Stacks, Tag 0C5R], at a *single* blowup: for every commuting square over the blowup of a surface
  at a closed point whose left edge is the blowup of another surface at a closed point, the
  exceptional curve of that blowup either collapses or maps onto the exceptional curve downstairs
  in the sense of `Stacks.ResolutionOfSurfaces.ExceptionalCurveMapsOntoOver`.

## Main results

* `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_comp_eq_pointBlowUpToBase` — **step 2 of
  [Stacks, Tag 0C5R]**: a chain of blowups at closed points of the source, with centres over the
  chosen point, carries a morphism to the blowup of the target at that point, making the square
  commute. Unconditional.
* `Stacks.ResolutionOfSurfaces.isBirational_of_pointBlowupChain` and
  `Stacks.ResolutionOfSurfaces.surjective_of_pointBlowupChain` — a chain of blowups at closed
  points of an integral Noetherian scheme of dimension two is birational and surjective.
* `Stacks.ResolutionOfSurfaces.notMem_isomorphism_open_comp` — a point outside the maximal
  isomorphism open stays outside it after precomposition with a surjection.
* `Stacks.ResolutionOfSurfaces.isIso_pointBlowUpToBase_or_ringKrullDim_stalk_eq_two` — at a closed
  point of an integral regular surface the blowup is an isomorphism or the local ring has dimension
  two, which is what the contraction of [Stacks, Tag 0C5J] needs.
* `Stacks.ResolutionOfSurfaces.blowUpToBase_subschemeι_pointExceptionalCurve` — the exceptional
  curve of a point blowup lies over the point blown up.
* `Stacks.ResolutionOfSurfaces.range_subschemeι_comp_subset_range_pointExceptionalCurve` — the
  containment half of the source's `E' = f'(E)`, unconditionally.
* `Stacks.ResolutionOfSurfaces.exists_comp_eq_pointBlowUpToBase_of_pointBlowupDichotomy` — the
  source's step at a single blowup: granted the dichotomy, a commuting square over the blowup whose
  left edge is a single blowup at a closed point factors.
* `Stacks.ResolutionOfSurfaces.exists_comp_eq_pointBlowUpToBase_of_pointBlowupChain` — **the
  induction on the length of the chain**, which peels one blowup at a time off the source end.
* `Stacks.ResolutionOfSurfaces.exists_comp_eq_pointBlowUpToBase_of_dichotomy` — the two combined:
  granted the dichotomy, a proper birational morphism onto an integral regular surface factors
  through the blowup at any closed point outside its maximal isomorphism open.
* `Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_exceptionalCurveDichotomy` —
  **[Stacks, Tag 0C5R] granted the dichotomy of step 3 alone.**
* `Stacks.ResolutionOfSurfaces.birationalOver_iff_exists_factorsAsPointBlowups_of_dichotomy` —
  [Stacks, Tag 0C5S] granted the same, which is how that tag's `h0C5R` hypothesis is fed.

## What is and is not proved

Proved here, with no hypothesis: step 2 in full (the chain from [Stacks, Tag 0C5H] together with
the commuting square), the induction that peels the chain, the choice of the contracted curve and
its contraction clause, the dimension dichotomy at the blown-up point of the source (a closed point
of an integral regular surface whose local ring is one-dimensional has its ideal sheaf an effective
Cartier divisor, so the blowup there is an isomorphism and the step is trivial), the properness,
birationality and surjectivity bookkeeping of each stage, and the transport of the chosen point out
of the maximal isomorphism open along the chain (its fibre is infinite, and the chain is
surjective, so the fibre upstairs is infinite too).

Carried as a hypothesis by the declarations *below*:
`Stacks.ResolutionOfSurfaces.PointBlowupDichotomy`, the dichotomy of the source's step 3. Its
collapsing alternative is consumed by [Stacks, Tag 0C5J] and its other alternative is refuted in
`ExceptionalCurveLocus.lean`. **It is no longer an input of the library**: it is proved in
`PointBlowupDichotomyProof.lean` of this directory, out of three pieces — the geometric half
`Stacks.ResolutionOfSurfaces.exists_isIso_pointExceptionalCurveMap_or_const`, the nonvanishing of
the conormal comparison map (the source's "the map is nonzero, as `f'` is an isomorphism in the
generic point of `E`"), which is
`Stacks.Conormal.ne_zero_immersionConormalSheafMap_of_isIso_stalkMap` of
`ExceptionalConormalNonzero.lean`, and the change of the field the two curves are presented over,
which is `AlgebraicGeometry.Scheme.IdealSheafData.isExceptionalCurveOfFirstKind_of_iso` of
`ExceptionalCurveFieldTransport.lean`. So [Stacks, Tag 0C5R] holds with nothing carried; the
unconditional carrier is
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_isProper_of_isBirational` of
`PointBlowupFactorizationStep.lean`.

Every other input of the source's steps 3 to 5 is already in the library: the presentation of the
exceptional curve as an exceptional curve of the first kind over the residue field
(`Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal`), the
isomorphy of a finite birational morphism onto a projective line
(`Stacks.ResolutionOfSurfaces.isIso_of_isFinite_of_isBirational_of_iso_projectiveLineProj`), the
two clauses of [Stacks, Tag 067L]
(`Stacks.ResolutionOfSurfaces.conormalSequenceSecondArrow`), the invertibility of a nonzero
endomorphism of a twist of the projective line
(`Stacks.ResolutionOfSurfaces.nonzeroTwistEndoIsIso`) and the vanishing of the relative
differentials that follows (`Stacks.ResolutionOfSurfaces.quasiFiniteAt_of_exceptionalCurvePair`).

The `D`-clause `D.IsExceptionalCurveOfFirstKind k e` of the second alternative is kept inside the
hypothesis even though
`Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal` proves it:
that lemma proves it for *its own* presentation over the residue field, while the alternative needs
one over the field shared with the curve downstairs. The transport of the property along a change
of presentation is
`AlgebraicGeometry.Scheme.IdealSheafData.isExceptionalCurveOfFirstKind_of_iso` of
`ExceptionalCurveFieldTransport.lean`, proved from [Stacks, Tag 0BXJ] and the cohomology of the
twists on the projective line.

## Implementation notes

The two private lemmas `ringKrullDim_stalk_eq_one_or_two` and
`isEffectiveCartierDivisor_vanishingIdeal_of_ringKrullDim_stalk_eq_one` of
`FactorizationBirationalMaps.lean` are exactly what the dimension dichotomy at the blown-up point
of the source needs; being `private` they cannot be imported, so
`Stacks.ResolutionOfSurfaces.isIso_pointBlowUpToBase_or_ringKrullDim_stalk_eq_two` below reproves
their combination. Promoting them and deleting the duplicate is the obvious cleanup once that file
is unowned.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H)
* [Stacks Project, Tag 0C5J](https://stacks.math.columbia.edu/tag/0C5J)
* [Stacks Project, Tag 0C5S](https://stacks.math.columbia.edu/tag/0C5S)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### Chains of blowups at closed points are birational and surjective -/

/-- The identity morphism is birational: it is the identity on generic points and on every local
ring. -/
private theorem isBirational_id (X : Scheme.{u}) : AlgebraicGeometry.IsBirational (𝟙 X) := by
  refine ⟨?_, fun x _ => ?_⟩
  · simpa using Set.bijOn_id (genericPoints X)
  · simp only [Scheme.Hom.stalkMap]
    infer_instance

/-- The composite of a chain of blowups at closed points of an integral Noetherian scheme of
dimension two is birational: each stage is again such a scheme, and the blowup at a closed point of
one is birational because the ideal of the point is nonzero. -/
public theorem isBirational_of_pointBlowupChain {X Z : Scheme.{u}} {T : Set X} {p : Z ⟶ X}
    (hp : PointBlowupChain X T Z p) (hint : AlgebraicGeometry.IsIntegral X)
    (hnoeth : AlgebraicGeometry.IsNoetherian X) (hdim : topologicalKrullDim X = 2) :
    IsBirational p := by
  induction hp with
  | refl => exact isBirational_id X
  | step hh w hw hwT ih =>
    obtain ⟨hWint, hWnoeth, hWdim, -⟩ :=
      isIntegral_and_topologicalKrullDim_and_isProper_of_pointBlowupChain hh hint hnoeth hdim
    have h1 := hWint
    have h2 : IsLocallyNoetherian _ := hWnoeth.toIsLocallyNoetherian
    exact (isBirational_blowUpToBase _ (vanishingIdeal_singleton_ne_bot hWdim w hw)).comp ih

/-- The composite of a chain of blowups at closed points of an integral Noetherian scheme of
dimension two is surjective: it is proper, hence has closed range, and birational, hence
dominant. -/
public theorem surjective_of_pointBlowupChain {X Z : Scheme.{u}} {T : Set X} {p : Z ⟶ X}
    (hp : PointBlowupChain X T Z p) (hint : AlgebraicGeometry.IsIntegral X)
    (hnoeth : AlgebraicGeometry.IsNoetherian X) (hdim : topologicalKrullDim X = 2) :
    Function.Surjective p.base := by
  obtain ⟨-, -, -, hproper⟩ :=
    isIntegral_and_topologicalKrullDim_and_isProper_of_pointBlowupChain hp hint hnoeth hdim
  have h1 := hproper
  have h2 := (isBirational_of_pointBlowupChain hp hint hnoeth hdim).isDominant
  exact p.surjective

/-! ### The chosen point stays outside the isomorphism locus -/

/-- **A point outside the maximal isomorphism open of `g` is outside that of `q ≫ g`** when `q` is
surjective. The fibre of `g` over the point is infinite, being a fibre over a point outside the
maximal isomorphism open of a proper birational morphism onto a regular Noetherian scheme; its
inverse image under the surjection `q` therefore has infinite image, hence is infinite; so the
fibre of `q ≫ g` is infinite too and [Stacks, Tag 0BFP] keeps the point out. -/
public theorem notMem_isomorphism_open_comp {A B C : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian A] [IsReduced B] (hA : IsRegular A) (g : B ⟶ A)
    (hg : IsProper g) (hbg : IsBirational g) {a : A}
    (haU : ∀ U : A.Opens, IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U → a ∉ U)
    (q : C ⟶ B) (hq : Function.Surjective q.base) (U' : A.Opens)
    (hU' : IsGreatest { V : A.Opens | IsIso ((q ≫ g) ∣_ V) } U') : a ∉ U' := by
  intro haU'
  have hgp := hg
  obtain ⟨U, hU⟩ := exists_maximal_isomorphism_open g
  have hfin : ((q ≫ g) ⁻¹' {a} : Set C).Finite :=
    finite_fiber_of_isIso_restrict (q ≫ g) U' hU'.1 haU'
  have hpre : ((q ≫ g) ⁻¹' {a} : Set C) = q ⁻¹' (g ⁻¹' {a} : Set B) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
  have hgfin : (g ⁻¹' {a} : Set B).Finite := by
    rw [hpre] at hfin
    have himg : q '' (q ⁻¹' (g ⁻¹' {a} : Set B)) = (g ⁻¹' {a} : Set B) :=
      Set.image_preimage_eq _ hq
    exact himg ▸ hfin.image _
  exact haU U hU (mem_isomorphismLocus_of_finite_fiber g hbg U hU hA a hgfin)

/-! ### The dimension dichotomy at the blown-up point of the source -/

/-- A point lies in the support of the vanishing ideal of a closed point iff it is that point. -/
private theorem mem_support_vanishingIdeal_singleton_iff {W : Scheme.{u}} {w : W}
    (hw : IsClosed ({w} : Set W)) {y : W} :
    y ∈ ((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).support : Set W) ↔
      y = w := by
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- **At a closed point of an integral regular surface the blowup is either an isomorphism or a
contraction of an exceptional curve.** The local ring at a closed point of such a scheme has Krull
dimension one or two: it is at most two by the dimension of the scheme and nonzero because a closed
point is not the generic point. In the first case the local ring is regular of dimension one, so
its maximal ideal is generated by a single nonzero element and the ideal sheaf of the point is an
effective Cartier divisor, which makes the blowup an isomorphism by [Stacks, Tag 02OS]; the second
case is the hypothesis of
`AlgebraicGeometry.isContractionOfExceptionalCurve_blowUpToBase`. -/
public theorem isIso_pointBlowUpToBase_or_ringKrullDim_stalk_eq_two {W : Scheme.{u}}
    (hW : IsIntegralRegularSurface W) (w : W) (hw : IsClosed ({w} : Set W)) :
    IsIso (pointBlowUpToBase hw) ∨ ringKrullDim (W.presheaf.stalk w) = 2 := by
  have hint := hW.isIntegral
  have hnoe := hW.isNoetherian
  have hLN : IsLocallyNoetherian W := hnoe.toIsLocallyNoetherian
  have hle : ringKrullDim (W.presheaf.stalk w) ≤ 2 := by
    rw [← hW.topologicalKrullDim_eq, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (W.fromSpecStalk w).isEmbedding.isInducing.topologicalKrullDim_le
  have hne : ringKrullDim (W.presheaf.stalk w) ≠ 0 := by
    intro h0
    rw [ringKrullDim_stalk_eq_coheight] at h0
    have hc : Order.coheight w = 0 := by exact_mod_cast h0
    have hs : w ⤳ genericPoint W := Order.coheight_eq_zero.mp hc (show w ≤ (⊤ : W) from le_top)
    have hwη : w = genericPoint W := (hs.antisymm (genericPoint_specializes w)).eq
    refine genericPoint_notMem_supportSet
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))
      (vanishingIdeal_singleton_ne_bot hW.topologicalKrullDim_eq w hw) ?_
    exact (mem_support_vanishingIdeal_singleton_iff hw).2 hwη.symm
  have hrl := (isRegularLocalRing_iff (W.presheaf.stalk w)).mp
    (AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hW.isRegular w)
  have hone_or_two : ringKrullDim (W.presheaf.stalk w) = 1 ∨
      ringKrullDim (W.presheaf.stalk w) = 2 := by
    rw [← hrl] at hle hne ⊢
    have hn : (IsLocalRing.maximalIdeal (W.presheaf.stalk w)).spanFinrank ≤ 2 := by
      exact_mod_cast hle
    have hn0 : (IsLocalRing.maximalIdeal (W.presheaf.stalk w)).spanFinrank ≠ 0 := by
      exact_mod_cast hne
    rcases (show (IsLocalRing.maximalIdeal (W.presheaf.stalk w)).spanFinrank = 1 ∨
        (IsLocalRing.maximalIdeal (W.presheaf.stalk w)).spanFinrank = 2 by omega) with h1 | h2
    · exact Or.inl (by exact_mod_cast h1)
    · exact Or.inr (by exact_mod_cast h2)
  refine hone_or_two.imp_left fun hdim1 => ?_
  refine Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor _ ?_
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor _
    fun y hy => ?_
  rw [(mem_support_vanishingIdeal_singleton_iff hw).1 hy]
  have hrank : (IsLocalRing.maximalIdeal (W.presheaf.stalk w)).spanFinrank = 1 := by
    exact_mod_cast hrl.trans hdim1
  obtain ⟨⟨c, hc⟩, hcne⟩ :=
    (Submodule.spanFinrank_eq_one_iff (IsLocalRing.maximalIdeal (W.presheaf.stalk w))).mp hrank
  have hc0 : c ≠ 0 := fun h => hcne (by simpa [h] using hc)
  refine ⟨c, mem_nonZeroDivisors_of_ne_zero hc0, ?_⟩
  rwa [AlgebraicGeometry.IdealSheafData.stalk_vanishingIdeal_singleton]

/-! ### Step 2: the chain and the commuting square -/

/-- **Step 2 of [Stacks, Tag 0C5R]: the chain of blowups dominating the rational map to the
blowup.** Let `g : B ⟶ A` be a proper birational morphism of integral Noetherian schemes regular of
dimension two and let `a ∈ A` be a closed point. There is a chain of blowups at closed points of
`B` with composite `p : Z ⟶ B` and a morphism `φ : Z ⟶ pointBlowUp ha` making the square over the
blowup commute. The centres of the chain lie over `a`, which is the source's "in closed points
lying over the fibre `f⁻¹(y)`".

The blowup of `A` at `a` is an isomorphism over `A \ {a}` by [Stacks, Tag 02OS], so the rational
map from `B` to it is displayed on the inverse image of that open, which is dense because `B` is
irreducible and the generic point of `B` lies over the generic point of `A`. [Stacks, Tag 0C5H]
then supplies the chain, with centres outside that domain, i.e. over `a`. -/
public theorem exists_pointBlowupChain_comp_eq_pointBlowUpToBase {A B : Scheme.{u}}
    (hA : IsIntegralRegularSurface A) (hB : IsIntegralRegularSurface B) (g : B ⟶ A)
    (_hg : IsProper g) (hbg : IsBirational g) {a : A} (ha : IsClosed ({a} : Set A)) :
    ∃ (Z : Scheme.{u}) (T : Set B) (p : Z ⟶ B) (φ : Z ⟶ pointBlowUp ha),
      (∀ b ∈ T, g.base b = a) ∧ PointBlowupChain B T Z p ∧
        φ ≫ pointBlowUpToBase ha = p ≫ g := by
  classical
  have hAint := hA.isIntegral
  have hAnoe := hA.isNoetherian
  have hALN : IsLocallyNoetherian A := hAnoe.toIsLocallyNoetherian
  have hBint := hB.isIntegral
  have hBnoe := hB.isNoetherian
  let Vc : A.Opens :=
    ⟨(Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A)).supportᶜ,
      (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A)).support.isClosed.isOpen_compl⟩
  have hbiso : IsIso (pointBlowUpToBase ha ∣_ Vc) :=
    isIso_blowUp_restrict_compl_support _
  let : B.Over A := ⟨g⟩
  let : (pointBlowUp ha).Over A := ⟨pointBlowUpToBase ha⟩
  have : IsProper (pointBlowUp ha ↘ A) := (inferInstance : IsProper (pointBlowUpToBase ha))
  have hgen : g (genericPoint B) = genericPoint A := by
    simpa [genericPoints_eq_singleton, Set.bijOn_singleton] using hbg.bijOn
  have hdense : Dense ((g ⁻¹ᵁ Vc : B.Opens) : Set B) := by
    refine (g ⁻¹ᵁ Vc : B.Opens).2.dense ⟨genericPoint B, ?_⟩
    show g (genericPoint B) ∈ Vc
    rw [hgen]
    exact genericPoint_notMem_supportSet _
      (vanishingIdeal_singleton_ne_bot hA.topologicalKrullDim_eq a ha)
  let fpm : B.PartialMap (pointBlowUp ha) :=
    { domain := g ⁻¹ᵁ Vc
      dense_domain := hdense
      hom := (g ∣_ Vc) ≫ (asIso (pointBlowUpToBase ha ∣_ Vc)).inv ≫
        (pointBlowUpToBase ha ⁻¹ᵁ Vc).ι }
  have : fpm.IsOver A := by
    refine ⟨?_⟩
    show ((g ∣_ Vc) ≫ (asIso (pointBlowUpToBase ha ∣_ Vc)).inv ≫
      (pointBlowUpToBase ha ⁻¹ᵁ Vc).ι) ≫ pointBlowUpToBase ha = (g ⁻¹ᵁ Vc).ι ≫ g
    have key : (asIso (pointBlowUpToBase ha ∣_ Vc)).inv ≫
        (pointBlowUpToBase ha ⁻¹ᵁ Vc).ι ≫ pointBlowUpToBase ha = Vc.ι := by
      rw [← morphismRestrict_ι (pointBlowUpToBase ha) Vc]
      exact (asIso (pointBlowUpToBase ha ∣_ Vc)).inv_hom_id_assoc Vc.ι
    rw [Category.assoc, Category.assoc, key, morphismRestrict_ι g Vc]
  obtain ⟨Z, p, φ, hchain, hφS, -⟩ :=
    exists_pointBlowupChain_resolving_partialMap_of_dim_two (S := A)
      (AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hB.isRegular)
      hB.topologicalKrullDim_eq fpm
  refine ⟨Z, _, p, φ, fun b hb => ?_, hchain, hφS⟩
  exact (mem_support_vanishingIdeal_singleton_iff ha).1 (not_not.mp fun h => hb h)

/-! ### The dichotomy of step 3, at a single blowup -/

/-- The exceptional curve of the blowup of a scheme at a reduced closed point. -/
public abbrev pointExceptionalCurve {W : Scheme.{u}} {w : W} (hw : IsClosed ({w} : Set W)) :
    (pointBlowUp hw).IdealSheafData :=
  exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))

/-- **The exceptional curve of a point blowup lies over the point blown up.** The exceptional ideal
is the inverse image of the centre, so its support is the inverse image of the support of the
centre, which is the point itself. -/
public theorem blowUpToBase_subschemeι_pointExceptionalCurve {W : Scheme.{u}} {w : W}
    (hw : IsClosed ({w} : Set W)) (z : (pointExceptionalCurve hw).subscheme) :
    pointBlowUpToBase hw ((pointExceptionalCurve hw).subschemeι z) = w := by
  have hmem : ((pointExceptionalCurve hw).subschemeι z) ∈
      (((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).comap
        (pointBlowUpToBase hw)).support : Set (pointBlowUp hw)) := by
    show ((pointExceptionalCurve hw).subschemeι z) ∈
      ((pointExceptionalCurve hw).support : Set (pointBlowUp hw))
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  rwa [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal] at hmem

/-- **The containment half of the source's "`E' = f'(E)`".** In a commuting square over the blowup
of `A` at a closed point `a` whose left edge is the blowup of `W` at a closed point `w` lying over
`a`, the morphism `g'` carries the exceptional curve of the blowup at `w` into the exceptional
curve of the blowup at `a`.

No non-collapsing hypothesis is needed for this: the exceptional curve upstairs lies over `w`,
hence its image under `g'` lies over `a`, hence inside the exceptional curve downstairs by
`Stacks.ResolutionOfSurfaces.preimage_singleton_subset_range_exceptionalIdeal`. What the source
adds, when `g'(E)` is not a point, is that the containment is onto and that the induced morphism is
an isomorphism; that is the part of the source's step 5 which this library does not carry, and is
why `Stacks.ResolutionOfSurfaces.PointBlowupDichotomy` is a hypothesis. -/
public theorem range_subschemeι_comp_subset_range_pointExceptionalCurve {A W : Scheme.{u}}
    (f : W ⟶ A) {a : A} (ha : IsClosed ({a} : Set A)) {w : W} (hw : IsClosed ({w} : Set W))
    (hwa : f.base w = a) (g' : pointBlowUp hw ⟶ pointBlowUp ha)
    (hsq : g' ≫ pointBlowUpToBase ha = pointBlowUpToBase hw ≫ f) :
    Set.range ((pointExceptionalCurve hw).subschemeι ≫ g').base ⊆
      Set.range (pointExceptionalCurve ha).subschemeι.base := by
  rintro - ⟨z, rfl⟩
  have h1 : pointBlowUpToBase ha (g' ((pointExceptionalCurve hw).subschemeι z)) = a := by
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply,
      blowUpToBase_subschemeι_pointExceptionalCurve hw z, hwa]
  rw [Scheme.Hom.comp_apply]
  exact preimage_singleton_subset_range_exceptionalIdeal ha h1

/-- **The dichotomy of step 3 of [Stacks, Tag 0C5R], at a single blowup.** Let `f : W ⟶ A` be a
proper birational morphism of integral Noetherian schemes regular of dimension two, let `a ∈ A` be
a closed point outside the maximal open over which `f` is an isomorphism, let `w ∈ W` be a closed
point lying over `a` and let `g'` fill in the square over the two blowups. Then the exceptional
curve of the blowup at `w` either collapses under `g'` or maps onto the exceptional curve of the
blowup at `a`, in the sense of `Stacks.ResolutionOfSurfaces.ExceptionalCurveMapsOntoOver`.

This is the source's "if `E` maps to a point in `Y'`, then we obtain the desired factorization by
Lemma 0C5J. We will prove that if this is not the case we obtain a contradiction." Both halves of
that sentence are available in this library — the first is
`Stacks.ResolutionOfSurfaces.exists_comp_eq_of_isContraction_of_const_on_exceptionalCurve` and the
second is
`Stacks.ResolutionOfSurfaces.false_of_exceptionalCurvePair_of_notMem_isomorphismLocus` — but the
dichotomy itself is not, because its second alternative asserts the nonvanishing of a conormal
comparison map that nothing in the library proves. -/
public def PointBlowupDichotomy : Prop :=
  ∀ (A W : Scheme.{u}) (f : W ⟶ A) (a : A) (ha : IsClosed ({a} : Set A)) (w : W)
      (hw : IsClosed ({w} : Set W)) (g' : pointBlowUp hw ⟶ pointBlowUp ha),
    IsIntegralRegularSurface A → IsIntegralRegularSurface W → IsProper f → IsBirational f →
      (∀ U : A.Opens, IsGreatest { V : A.Opens | IsIso (f ∣_ V) } U → a ∉ U) → f.base w = a →
        g' ≫ pointBlowUpToBase ha = pointBlowUpToBase hw ≫ f →
          ExceptionalCurveDichotomy A (pointBlowUp hw) a ha (pointExceptionalCurve hw) g'

/-- **The source's step at a single blowup.** Granted the dichotomy, a commuting square over the
blowup of `A` at a closed point `a` outside the maximal isomorphism open, whose left edge is the
blowup of `W` at a closed point `w`, yields a factorization of `f : W ⟶ A` through the blowup at
`a`.

If the local ring at `w` is one-dimensional the blowup there is already an isomorphism and the
factorization is read off the square. Otherwise the blowup is the contraction of its exceptional
curve, and the two alternatives of the dichotomy are discharged by [Stacks, Tag 0C5J] and by the
contradiction of the source's steps 5(i) to 5(iii). -/
public theorem exists_comp_eq_pointBlowUpToBase_of_pointBlowupDichotomy
    (dich : PointBlowupDichotomy.{u}) {A W : Scheme.{u}} (hA : IsIntegralRegularSurface A)
    (hW : IsIntegralRegularSurface W) (f : W ⟶ A) (hf : IsProper f) (hbf : IsBirational f)
    {a : A} (ha : IsClosed ({a} : Set A))
    (haU : ∀ U : A.Opens, IsGreatest { V : A.Opens | IsIso (f ∣_ V) } U → a ∉ U)
    (w : W) (hw : IsClosed ({w} : Set W)) (hwa : f.base w = a)
    (g' : pointBlowUp hw ⟶ pointBlowUp ha)
    (hsq : g' ≫ pointBlowUpToBase ha = pointBlowUpToBase hw ≫ f) :
    ∃ ψ : W ⟶ pointBlowUp ha, ψ ≫ pointBlowUpToBase ha = f := by
  have hAnoe := hA.isNoetherian
  have hAint := hA.isIntegral
  have hWnoe := hW.isNoetherian
  have hWint := hW.isIntegral
  have hALN : IsLocallyNoetherian A := hAnoe.toIsLocallyNoetherian
  have hWLN : IsLocallyNoetherian W := hWnoe.toIsLocallyNoetherian
  rcases isIso_pointBlowUpToBase_or_ringKrullDim_stalk_eq_two hW w hw with hiso | hdim2
  · refine ⟨(asIso (pointBlowUpToBase hw)).inv ≫ g', ?_⟩
    rw [Category.assoc, hsq, ← Category.assoc]
    simp
  · have hA' : IsIntegralRegularSurface (pointBlowUp ha) :=
      isIntegralRegularSurface_blowUp_vanishingIdeal a ha hA
    have hA'noe := hA'.isNoetherian
    have hA'int := hA'.isIntegral
    have hZsurf : IsIntegralRegularSurface (pointBlowUp hw) :=
      isIntegralRegularSurface_blowUp_vanishingIdeal w hw hW
    have hZint := hZsurf.isIntegral
    have hπbir : IsBirational (pointBlowUpToBase hw) :=
      isBirational_blowUpToBase _ (vanishingIdeal_singleton_ne_bot hW.topologicalKrullDim_eq w hw)
    have hπprop : IsProper (pointBlowUpToBase hw) := inferInstance
    have hπdom := hπbir.isDominant
    have hπsurj : Function.Surjective (pointBlowUpToBase hw).base :=
      (pointBlowUpToBase hw).surjective
    have hcompprop : IsProper (pointBlowUpToBase hw ≫ f) :=
      MorphismProperty.comp_mem _ _ _ hπprop hf
    have hcompbir : IsBirational (pointBlowUpToBase hw ≫ f) := hπbir.comp hbf
    have hg'prop : IsProper g' :=
      isProper_of_comp_pointBlowUpToBase ha hcompprop g' hsq
    have hg'bir : IsBirational g' :=
      isBirational_of_comp_pointBlowUpToBase hA.topologicalKrullDim_eq ha hcompbir g' hsq
    have hcontr : IsContractionOfExceptionalCurve (pointExceptionalCurve hw)
        (pointBlowUpToBase hw) :=
      isContractionOfExceptionalCurve_blowUpToBase w hw
        (AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hW.isRegular w) hdim2
    rcases dich A W f a ha w hw g' hA hW hf hbf haU hwa hsq with hconst | ⟨k, fk, hmaps⟩
    · obtain ⟨ψ, -, hψ⟩ := exists_comp_eq_of_isContraction_of_const_on_exceptionalCurve hcontr f
        (pointBlowUpToBase ha) g' hsq hconst
      exact ⟨ψ, hψ⟩
    · let _ : Field k := fk
      obtain ⟨D', e, e', hE, hE', hbfib, hγ⟩ := hmaps
      obtain ⟨x, hx⟩ := hcontr.exists_const_on_subscheme
      obtain ⟨U, hU⟩ := exists_maximal_isomorphism_open f
      obtain ⟨ψ, -, hψ⟩ := exists_comp_eq_of_exceptionalCurveDichotomy k
        conormalSequenceSecondArrow f hbf hA.isRegular U hU (haU U hU) (pointBlowUpToBase ha) g'
        hg'bir hA'.isRegular hsq hπsurj hcontr hE hE' hbfib x hx (Or.inr hγ)
      exact ⟨ψ, hψ⟩

/-! ### The induction on the length of the chain -/

/-- **The induction of step 2 of [Stacks, Tag 0C5R] on the length of the chain.** Granted the
dichotomy, a commuting square over the blowup of `A` at a closed point `a` whose left edge is a
chain of blowups at closed points of `B` yields a factorization of `g : B ⟶ A` through the blowup
at `a`.

The `step` constructor of `Stacks.ResolutionOfSurfaces.PointBlowupChain` adds the blowup nearest
the source, so plain induction on the chain peels exactly the end the source peels: the single
blowup at the end is handled by
`Stacks.ResolutionOfSurfaces.exists_comp_eq_pointBlowUpToBase_of_pointBlowupDichotomy`, applied to
the composite of the shorter chain with `g`, and its factorization is fed to the inductive
hypothesis. The chosen point stays outside the maximal isomorphism open of that composite by
`Stacks.ResolutionOfSurfaces.notMem_isomorphism_open_comp`. -/
public theorem exists_comp_eq_pointBlowUpToBase_of_pointBlowupChain
    (dich : PointBlowupDichotomy.{u}) {A : Scheme.{u}} (hA : IsIntegralRegularSurface A)
    {a : A} (ha : IsClosed ({a} : Set A)) {B : Scheme.{u}} (hB : IsIntegralRegularSurface B)
    (g : B ⟶ A) (hg : IsProper g) (hbg : IsBirational g)
    (haU : ∀ U : A.Opens, IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U → a ∉ U)
    {Z : Scheme.{u}} {T : Set B} {p : Z ⟶ B} (hT : ∀ b ∈ T, g.base b = a)
    (hchain : PointBlowupChain B T Z p) :
    ∀ φ : Z ⟶ pointBlowUp ha, φ ≫ pointBlowUpToBase ha = p ≫ g →
      ∃ ψ : B ⟶ pointBlowUp ha, ψ ≫ pointBlowUpToBase ha = g := by
  have hAnoe := hA.isNoetherian
  have hBint := hB.isIntegral
  induction hchain with
  | refl => exact fun φ hsq => ⟨φ, by rwa [Category.id_comp] at hsq⟩
  | @step V q hq w hw hwT ih =>
    intro φ hsq
    obtain ⟨hVsurf, hqproper⟩ := isIntegralRegularSurface_and_isProper_of_pointBlowupChain
      blowUpSurface_of_isIntegralRegularSurface hq hB
    have hqbir : IsBirational q :=
      isBirational_of_pointBlowupChain hq hB.isIntegral hB.isNoetherian hB.topologicalKrullDim_eq
    have hqsurj : Function.Surjective q.base :=
      surjective_of_pointBlowupChain hq hB.isIntegral hB.isNoetherian hB.topologicalKrullDim_eq
    have hfp : IsProper (q ≫ g) := MorphismProperty.comp_mem _ _ _ hqproper hg
    have hfb : IsBirational (q ≫ g) := hqbir.comp hbg
    have hwa : (q ≫ g).base w = a := by
      rw [Scheme.Hom.comp_apply]
      exact hT _ hwT
    have hsq' : φ ≫ pointBlowUpToBase ha = pointBlowUpToBase hw ≫ (q ≫ g) := by
      rwa [← Category.assoc]
    obtain ⟨ψ, hψ⟩ := exists_comp_eq_pointBlowUpToBase_of_pointBlowupDichotomy dich hA hVsurf
      (q ≫ g) hfp hfb ha
      (fun U' hU' => notMem_isomorphism_open_comp hA.isRegular g hg hbg haU q hqsurj U' hU')
      w hw hwa φ hsq'
    exact ih ψ hψ

/-! ### Step 2 and 3 combined -/

/-- **Steps 2 to 5 of [Stacks, Tag 0C5R], granted the dichotomy of step 3.** A proper birational
morphism `g : B ⟶ A` of integral Noetherian schemes regular of dimension two factors through the
blowup of `A` at any closed point outside the maximal open over which `g` is an isomorphism. -/
public theorem exists_comp_eq_pointBlowUpToBase_of_dichotomy
    (dich : PointBlowupDichotomy.{u}) {A B : Scheme.{u}} (hA : IsIntegralRegularSurface A)
    (hB : IsIntegralRegularSurface B) (g : B ⟶ A) (hg : IsProper g) (hbg : IsBirational g)
    {a : A} (ha : IsClosed ({a} : Set A)) (U : A.Opens)
    (hU : IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U) (haU : a ∉ U) :
    ∃ ψ : B ⟶ pointBlowUp ha, ψ ≫ pointBlowUpToBase ha = g := by
  obtain ⟨Z, T, p, φ, hT, hchain, hsq⟩ :=
    exists_pointBlowupChain_comp_eq_pointBlowUpToBase hA hB g hg hbg ha
  refine exists_comp_eq_pointBlowUpToBase_of_pointBlowupChain dich hA ha hB g hg hbg ?_ hT hchain
    φ hsq
  intro U' hU'
  rwa [le_antisymm (hU.2 hU'.1) (hU'.2 hU.1)]

/-- **The reduction of [Stacks, Tag 0C5R] to the dichotomy of its step 3 alone.** A proper
birational morphism between integral Noetherian schemes regular of dimension two is a sequence of
blowups at closed points.

Step 2 — the chain of [Stacks, Tag 0C5H] and its reduction to a single blowup — the measure and its
descent, and every other clause of the earlier `square` hypothesis are discharged; what is left is
`Stacks.ResolutionOfSurfaces.PointBlowupDichotomy`, the dichotomy of the source's step 3 at one
blowup.

This declaration deliberately carries **no** `stacks 0C5R` attribute: it takes
`PointBlowupDichotomy` as an argument, so registering the tag here would be a conditional
registration whatever the status of that argument. The argument is nevertheless *not* an
assumption of the library — `Stacks.ResolutionOfSurfaces.pointBlowupDichotomy` of
`PointBlowupDichotomyProof.lean` proves it. The unconditional carrier of the tag is
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_isProper_of_isBirational` of
`PointBlowupFactorizationStep.lean`, which states this theorem's conclusion over this theorem's
hypotheses and nothing more; Tag 0C5R is registered there and, over its own four hypotheses, on
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_proper_birational`. -/
public theorem factorsAsPointBlowups_of_exceptionalCurveDichotomy
    (dich : PointBlowupDichotomy.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsIntegralRegularSurface Y) (hX : IsIntegralRegularSurface X) (hproper : IsProper f)
    (hbirational : IsBirational f) : FactorsAsPointBlowups Y Set.univ X f :=
  factorsAsPointBlowups_of_pointBlowupFactorization
    (fun _ _ g hA hB hp hb _ _ ha U hU haU =>
      exists_comp_eq_pointBlowUpToBase_of_dichotomy dich hA hB g hp hb ha U hU haU)
    f hY hX hproper hbirational

/-- **[Stacks, Tag 0C5S] granted the dichotomy of step 3 of [Stacks, Tag 0C5R].** Two proper
integral schemes over a Noetherian base, regular of dimension two, are birational over the base if
and only if they are dominated by a common scheme by two sequences of blowups at closed points.

This is `Stacks.ResolutionOfSurfaces.birationalOver_iff_exists_factorsAsPointBlowups_of_dim_two`
with its
`h0C5R` hypothesis fed by
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_exceptionalCurveDichotomy`; the converse
direction, which the source states without proof, is unconditional there. The `@[stacks 0C5S]`
attribute stays on that theorem, this being the same statement with one hypothesis reduced. -/
public theorem birationalOver_iff_exists_factorsAsPointBlowups_of_dichotomy
    (dich : PointBlowupDichotomy.{u}) {S X Y : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian S] [X.Over S] [Y.Over S] [IsProper (X ↘ S)]
    [IsProper (Y ↘ S)] (hX : IsIntegralRegularSurface X) (hY : IsIntegralRegularSurface Y) :
    Scheme.BirationalOver (X ↘ S) (Y ↘ S) ↔
      ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
        f ≫ (X ↘ S) = g ≫ (Y ↘ S) ∧
          FactorsAsPointBlowups X Set.univ Z f ∧ FactorsAsPointBlowups Y Set.univ Z g :=
  birationalOver_iff_exists_factorsAsPointBlowups_of_dim_two
    (fun _ _ g hA hB hp hb =>
      factorsAsPointBlowups_of_exceptionalCurveDichotomy dich g hA hB hp hb)
    hX hY

end Stacks.ResolutionOfSurfaces

end
