module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBirationalIsomorphismLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.ClosedPointNeighborhoodsOfDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.DominatingExceptionalPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.DominatingNormalizationReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.DominatingNormalizedBlowupsLocal

/-!
# Dominating a modification of a surface by normalized blowups

**Stacks 0BHM.** Let `S` be a scheme and let `X` be a Noetherian Nagata algebraic space over `S`
with `dim(X) = 2`. Let `f : Y ⟶ X` be a proper birational morphism. Then there is a commutative
diagram

```
X_n ⟶ X_{n-1} ⟶ … ⟶ X_1 ⟶ X_0
 |                            |
 v                            v
 Y  ------------------------> X
```

where `X_0 ⟶ X` is the normalization and `X_{i+1} ⟶ X_i` is the normalized blowing up of `X_i`
at a closed point.

The sequence is `AlgebraicGeometry.Space.NormalizedBlowUpChain` (the sequence of Stacks 0BHX):
it starts with the normalization `X_0 ⟶ X`, continues through normalizations of blowings up at
closed points (`AlgebraicGeometry.Space.IsNormalizationOfBlowupAtClosedPoint`, the notion of
Stacks 0BHJ), and records in addition that every member is proper over `X`. Its top `X_n` comes
with the composite `g : X_n ⟶ X`, and the commutativity of the diagram is `h ≫ f = g` for the
vertical arrow `h : X_n ⟶ Y`.

## The proof

1. Replace `Y` by its normalization `Y^ν` and `X` by `X_0 = X^ν`: `Y^ν ⟶ X` factors through
   `X^ν` by a proper birational `l : Y^ν ⟶ X^ν` (Stacks 0BBG, 0BB5;
   `AlgebraicGeometry.Space.exists_normalization_lift_of_isProper_of_isBirational`).
2. By Stacks 0BBQ, `l` is an isomorphism over an open containing every point of codimension at
   most one, so it is an isomorphism away from a finite set `T` of closed points
   (`AlgebraicGeometry.Space.finite_and_isClosed_of_compl_range`).
3. Choose elementary étale neighbourhoods `(Uᵢ, uᵢ)` of the points of `T` as in Section 0BH9
   (`AlgebraicGeometry.Space.ClosedPointNeighborhoods.ofPoints`).
4. Over each `Uᵢ`, `Yᵢ = Y^ν ×_{X^ν} Uᵢ` is dominated by an admissible blowup of the scheme `Uᵢ`
   (087G), which is dominated by a sequence of normalized blowups of `Uᵢ` centred over `uᵢ`
   (0BBT); these lift to `X^ν` (0BHL) and the top dominates `Y^ν` by the equivalence of Stacks
   0BHB (`ClosedPointNeighborhoods.exists_normalizedBlowUpChain_dominating_of_isProper`).

## Main results

* `AlgebraicGeometry.Space.exists_normalizedBlowUpChain_dominating_of_dimension_le_two`: the
  statement for `dim(X) ≤ 2`.
* `AlgebraicGeometry.Space.exists_normalizedBlowUpChain_dominating`: **Stacks 0BHM**.

## References

* [Stacks Project, Tag 0BHM](https://stacks.math.columbia.edu/tag/0BHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The local ring of a normal algebraic space at every point is a normal domain. -/
theorem hasNormalLocalRingAtPoint_of_isNormal {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXn : Space.IsNormal B S hS X) (x : points B S hS X) :
    HasNormalLocalRingAtPoint B S hS X hX x := by
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS X hX x
  have : _root_.AlgebraicGeometry.IsNormal ((BigFppfOver.toScheme B S hS).obj U) :=
    (exists_atlas_iff_forall_etale B S hS X _ hX).mp hXn U a ha
  exact ⟨U, a, ha, p, hp, ⟨IsNormal.stalk_isDomain _, IsNormal.stalk_normal _⟩⟩

/-- **Stacks 0BHM for `dim(X) ≤ 2`.** Let `X` be a Noetherian Nagata algebraic space over `S`
of dimension at most two and let `f : Y ⟶ X` be a proper birational morphism. Then there is a
sequence `X_n ⟶ … ⟶ X_1 ⟶ X_0 ⟶ X` in the sense of Stacks 0BHX — `X_0 ⟶ X` the normalization,
each `X_{i+1} ⟶ X_i` the normalized blowing up of `X_i` at a closed point — with composite
`g : X_n ⟶ X`, and a morphism `h : X_n ⟶ Y` with `h ≫ f = g`. -/
theorem exists_normalizedBlowUpChain_dominating_of_dimension_le_two
    {X Y : AlgebraicSpaces B S hS} (hXN : IsNoetherian B S hS B.contains_terminal X.obj)
    (hXnag : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsNagataScheme T))
    (hXdim : dimension B S hS X.obj X.property ≤ 2) (f : Y ⟶ X)
    (hf : IsProper B S hS f.hom)
    (hbir : ∃ (hDY : IsDecentSpace B S hS Y.obj) (hDX : IsDecentSpace B S hS X.obj)
      (hCY : (irreducibleComponents (points B S hS Y.obj)).Finite)
      (hCX : (irreducibleComponents (points B S hS X.obj)).Finite),
      IsBirational B S hS Y.property X.property hDY hDX hCY hCX f.hom) :
    ∃ (A : AlgebraicSpaces B S hS) (g : A ⟶ X) (h : A ⟶ Y),
      NormalizedBlowUpChain B S hS X A g ∧ h ≫ f = g := by
  classical
  obtain ⟨-, hDX, -, -, -⟩ := id hbir
  obtain ⟨DX, DY, l, hl, hνX, hlp, hlbir, hXνN, hXνnag, hXνn, hXνdim, -, hYνred⟩ :=
    exists_normalization_lift_of_isProper_of_isBirational B.contains_terminal X.property
      Y.property hXN hXnag f.hom hf hbir
  let Xν : AlgebraicSpaces B S hS := ⟨DX.space, DX.isAlgebraicSpace⟩
  let Yν : AlgebraicSpaces B S hS := ⟨DY.space, DY.isAlgebraicSpace⟩
  let ν : Xν ⟶ X := ObjectProperty.homMk DX.hom
  let μ : Yν ⟶ Y := ObjectProperty.homMk DY.hom
  let lν : Yν ⟶ Xν := ObjectProperty.homMk l
  have hdec : IsDecentSpace B S hS Xν.obj := DX.isDecentSpace X.property hDX
  have hdim : dimension B S hS Xν.obj Xν.property ≤ 2 := hXνdim.trans hXdim
  -- the isomorphism locus of `l` (Stacks 06R2) contains the points of codimension ≤ 1 (0BBQ)
  obtain ⟨U, hU⟩ := exists_isGreatest_isIso_pullback_snd B S hS Yν.property Xν.property l
  have h1 : ∀ x : points B S hS Xν.obj, localRingDimension B S hS x ≤ 1 →
      x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
    intro x hx
    rcases hx.lt_or_eq with h | h
    · exact mem_isomorphismLocus_of_localRingDimension_eq_zero B S hS B.contains_terminal
        Xν.property Yν.property hXνN l hlbir hlp U hU x (Order.lt_one_iff.mp h)
    · exact mem_isomorphismLocus_of_localRingDimension_eq_one_of_normal B S hS
        B.contains_terminal Xν.property Yν.property hXνN l hlbir hlp hYνred U hU x h
        (hasNormalLocalRingAtPoint_of_isNormal Xν.property hXνn x)
  -- its complement `T` is a finite set of closed points
  obtain ⟨hTfin, hTcl⟩ := finite_and_isClosed_of_compl_range Xν.property hdec hXνN.1 hXνN.2.2
    hdim U hU.1.1 h1
  set T := (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ
  obtain ⟨n, pt, hrange⟩ := hTfin.fin_embedding
  have hptT : ∀ j, pt j ∈ T := fun j => hrange.subset (Set.mem_range_self j)
  -- the elementary étale neighbourhoods of Section 0BH9
  let D := ClosedPointNeighborhoods.ofPoints Xν hdec pt pt.injective fun j => hTcl _ (hptT j)
  have hl' : IsIso (pullback.snd lν.hom D.openAwayFromPoints.ι) := by
    refine isIso_pullback_snd_of_range_subset Xν.property lν.hom hU.1.1
      D.isOpenSubspace_openAwayFromPoints hU.1.2 ?_
    intro x hx
    have hx' : x ∈ (Set.range D.point)ᶜ := by rwa [← D.range_pointsMap_ι_openAwayFromPoints]
    change x ∈ (Set.range pt)ᶜ at hx'
    rw [hrange] at hx'
    exact not_not.mp hx'
  have hpt : ∀ j, 1 < localRingDimension B S hS (D.point j) := fun j =>
    lt_of_not_ge fun h => hptT j (h1 _ h)
  obtain ⟨A, g, h, hchain, hh⟩ :=
    D.exists_normalizedBlowUpChain_dominating_of_isProper ν hνX
      ⟨DX, Iso.refl _, (Category.id_comp _).symm⟩ hXνn hXνN.2.2 hXνnag hdim hpt lν hlp hl'
  refine ⟨A, g ≫ ν, h ≫ μ, hchain, ?_⟩
  ext1
  change h.hom ≫ DY.hom ≫ f.hom = g.hom ≫ DX.hom
  rw [← hl, ← Category.assoc]
  exact congrArg (· ≫ DX.hom) (congrArg (fun m => m.hom) hh)

/-- **Stacks 0BHM.** Let `S` be a scheme, let `X` be a Noetherian Nagata algebraic space over
`S` with `dim(X) = 2`, and let `f : Y ⟶ X` be a proper birational morphism. Then there is a
commutative diagram

```
X_n ⟶ X_{n-1} ⟶ … ⟶ X_1 ⟶ X_0
 |                            |
 v                            v
 Y  ------------------------> X
```

where `X_0 ⟶ X` is the normalization and `X_{i+1} ⟶ X_i` is the normalized blowing up of `X_i`
at a closed point: a sequence `NormalizedBlowUpChain B S hS X A g` with top `A = X_n` and
composite `g : X_n ⟶ X`, and `h : X_n ⟶ Y` with `h ≫ f = g`.

Being Noetherian is Stacks 03EA (quasi-compact, quasi-separated, locally Noetherian), Nagata is
the étale-local property of Stacks 03E6, `dim(X)` is Stacks 04N6, properness is Stacks 04XU, and
birationality is Stacks 0ACV, which is defined for decent spaces with finitely many irreducible
components; those witnesses are carried existentially, being consequences of the Noetherian
hypothesis and of properness rather than extra assumptions. -/
@[stacks 0BHM]
theorem exists_normalizedBlowUpChain_dominating {X Y : AlgebraicSpaces B S hS}
    (hXN : IsNoetherian B S hS B.contains_terminal X.obj)
    (hXnag : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsNagataScheme T))
    (hXdim : dimension B S hS X.obj X.property = 2) (f : Y ⟶ X)
    (hf : IsProper B S hS f.hom)
    (hbir : ∃ (hDY : IsDecentSpace B S hS Y.obj) (hDX : IsDecentSpace B S hS X.obj)
      (hCY : (irreducibleComponents (points B S hS Y.obj)).Finite)
      (hCX : (irreducibleComponents (points B S hS X.obj)).Finite),
      IsBirational B S hS Y.property X.property hDY hDX hCY hCX f.hom) :
    ∃ (A : AlgebraicSpaces B S hS) (g : A ⟶ X) (h : A ⟶ Y),
      NormalizedBlowUpChain B S hS X A g ∧ h ≫ f = g :=
  exists_normalizedBlowUpChain_dominating_of_dimension_le_two hXN hXnag hXdim.le f hf hbir

end AlgebraicGeometry.Space

end
