module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupOfEffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularLocalRings

/-!
# Making an ideal principal on an algebraic space by blowing up closed points

Let `S` be a scheme, let `X` be a Noetherian algebraic space over `S` and let `T ⊆ |X|` be a
finite set of closed points at each of which `X` is regular with local ring of dimension two.
Let `ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals with `𝒪_X/ℐ` supported on `T`.  **Stacks
0BHG** asserts that there is a sequence

`X_m ⟶ X_{m-1} ⟶ … ⟶ X_1 ⟶ X_0 = X`

in which each `X_{j+1} ⟶ X_j` is the blowing up of `X_j` at a closed point `x_j` lying above a
point of `T`, such that `ℐ𝒪_{X_m}` is an invertible ideal sheaf.

## Main results

* `AlgebraicGeometry.Space.exists_blowupFactorization_isPullbackDefined`: the induction on the
  colength of the ideal which produces the sequence of Stacks 0BHG, for every algebraic space for
  which the three inputs listed below are supplied.

Stacks 0BHG itself, with exactly the source's hypotheses, is
`AlgebraicGeometry.Space.exists_blowupFactorization_isPullbackDefined_of_isNoetherian` in
`StacksFrontier/AlgebraicGeometry/Spaces/PrincipalizationAtClosedPointsUnconditional.lean`, proved
by the source's route through the étale neighbourhoods of Section 0BH9 and the scheme case
Stacks 0AHH; it does not use the theorem here.

## How the statement is said here

A quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_X` is named by the closed subspace `Z ⊆ X` it cuts
out, under the bijection of Stacks 03MB between quasi-coherent ideals and closed subspaces;
`AlgebraicGeometry.Space.ClosedSubspaces` of Stacks 0CYZ is the library's datum for such a
subspace and `AlgebraicGeometry.Space.definingIdealSheaf` recovers `ℐ` from it.  Under that
bijection `𝒪_X/ℐ` is the structure sheaf of `Z`, so the source's "`𝒪_X/ℐ` is supported on `T`"
is the containment `|Z| ⊆ T` of point sets, with `|Z|` the library's
`AlgebraicGeometry.Space.subspacePointSet`.

"`ℐ𝒪_{X_m}` is an invertible ideal sheaf" is the statement that the inverse image of `Z` in
`X_m` is an effective Cartier divisor — `ℐ𝒪_{X_m}` is by definition the image of the pullback
of `ℐ`, which is the defining ideal of the inverse image subspace, and a sheaf of ideals is
invertible exactly when it is the ideal of an effective Cartier divisor.  That is the already
available `AlgebraicGeometry.Space.IsPullbackDefined` of Stacks 083Y, applied to the composite
`X_m ⟶ X`.

The sequence itself is `AlgebraicGeometry.Space.BlowupFactorization`, the datum introduced for
the two sides of Stacks 0BHF: a tower `X_m ⟶ … ⟶ X_0 = X` of blowings up at closed points,
every centre of which lies above a point of `T`, together with the identification of the given
morphism with the composite.  Being the blowing up at a closed point is
`AlgebraicGeometry.Space.IsBlowupAtClosedPoint` of Stacks 0BHE.  The source allows `m = 0`,
the empty sequence, and that case does occur: it is the one in which `ℐ = 𝒪_X`.  It does not
make the statement trivial, since for `m = 0` the conclusion reads that `Z` is itself an
effective Cartier divisor, which it is not in general.

## The three inputs

Three inputs are taken as explicit hypotheses, each quantified over *every* algebraic space
rather than over the Noetherian ones.  None of them mentions a sequence of blowings up of length
greater than one, and none of them mentions the finite set `T` of the conclusion for the space
`X`; the content proved here is the induction that assembles them.

* `blowupExists` is the existence of the blowing up of an algebraic space at a closed point,
  Stacks 0BHE, for every algebraic space.  The library constructs the blowing up of a locally
  Noetherian algebraic space in a closed subspace
  (`AlgebraicGeometry.Space.exists_isBlowupAlong_of_isLocallyNoetherian`), which is the case
  Stacks 0BHG needs; the hypothesis here asks for more.
* `pullbackOfEffectiveCartier` is the algebraic-space analogue of Stacks 0809, that an
  effective Cartier divisor has a defined pullback along a blowing up.  The scheme case is
  `AlgebraicGeometry.isPullbackDefined_blowUpToBase` in
  `StacksFrontier/AlgebraicGeometry/Blowup/Transform/RegularPullback.lean`; the algebraic-space
  case is carried in the same way by
  `StacksFrontier/AlgebraicGeometry/Spaces/BlowupCentreEnlargedByDivisor.lean`.
* `splitting` is the local statement of Stacks 0AGT in the form in which the source's proof of
  the scheme case, Stacks 0AHH, consumes it: after one blowing up at a closed point of the
  support, the inverse image of the ideal splits as the sum of an effective Cartier divisor —
  the multiple of the exceptional divisor — and an ideal again supported on finitely many
  closed points, lying over the old ones, which are regular of dimension two and whose
  colength is strictly smaller.  The induction of the scheme case of Stacks 0AHH,
  `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_isEffectiveCartierDivisor` in
  `StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/QuadraticTransformations/`, takes exactly
  this hypothesis, there with the concrete colength `Stacks.ResolutionOfSurfaces.totalColength`;
  `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_principalizing` discharges it.  Here the
  colength is a parameter `colength` of the theorem, universally quantified; quantifying over
  the measure strengthens the statement rather than weakening it.

The source's hypothesis that `X` is Noetherian is carried, as `_hX`, and is not used again —
its name is underscored for that reason.  The induction runs on the colength, and the
conditions it needs at each stage are supplied by `splitting`.  The hypothesis is retained
because the source fixes it.

## References

* [Stacks Project, Tag 0BHG](https://stacks.math.columbia.edu/tag/0BHG)
* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0BHE](https://stacks.math.columbia.edu/tag/0BHE)
* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
* [Stacks Project, Tag 0809](https://stacks.math.columbia.edu/tag/0809)
* [Stacks Project, Tag 0840](https://stacks.math.columbia.edu/tag/0840)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Having a defined pullback along a composite is effective Cartier-ness of the iterated inverse
image subspace. -/
private theorem isPullbackDefined_comp_iff {X Y W : AlgebraicSpaces B S hS}
    (g : W ⟶ Y) (f : Y ⟶ X) (D : ClosedSubspaces B S hS X.1) :
    IsPullbackDefined B S hS (g ≫ f) D ↔
      IsEffectiveCartierDivisor B S hS W
        (preimageClosedSubspace g (preimageClosedSubspace f D)) :=
  Iff.of_eq (congrArg (IsEffectiveCartierDivisor B S hS W)
    (Subtype.ext (Subfunctor.preimage_comp D.1 g.hom f.hom)))

/-- **The induction of Stacks 0BHG.** Let `S` be a scheme, let `X` be a Noetherian algebraic
space over `S` and let `T ⊆ |X|` be a finite set of closed points `x` such that `X` is regular at
`x` and the local ring of `X` at `x` has dimension `2`.  Let `ℐ ⊆ 𝒪_X` be a quasi-coherent
sheaf of ideals, given by the closed subspace `Z ⊆ X` it cuts out, such that `𝒪_X/ℐ` is supported
on `T`, that is, `|Z| ⊆ T`.  **Then there is a sequence**

`X_m ⟶ X_{m-1} ⟶ … ⟶ X_1 ⟶ X_0 = X`

**where `X_{j+1} ⟶ X_j` is the blowing up of `X_j` at a closed point `x_j` lying above a point
of `T`, such that `ℐ𝒪_{X_m}` is an invertible ideal sheaf** — that is, such that the inverse
image of `Z` along the composite `X_m ⟶ X` is an effective Cartier divisor.

Along the sequence produced, every effective Cartier divisor on `X` also has a defined
pullback; that is the form in which the induction uses its own output and it is recorded in the
conclusion.

Three inputs are taken as hypotheses over every algebraic space: the existence of the blowing
up of an algebraic space at a closed point (Stacks 0BHE), the algebraic-space analogue of Stacks
0809, and the local splitting of Stacks 0AGT with respect to a colength function given as a
parameter.  See the module documentation.  Stacks 0BHG with the source's hypotheses only is
`AlgebraicGeometry.Space.exists_blowupFactorization_isPullbackDefined_of_isNoetherian`. -/
theorem exists_blowupFactorization_isPullbackDefined
    (colength : ∀ Y : AlgebraicSpaces B S hS,
      ClosedSubspaces B S hS Y.1 → Set (points B S hS Y.1) → ℕ∞)
    (blowupExists : ∀ (Y : AlgebraicSpaces B S hS) (y : points B S hS Y.1)
      (hy : IsClosed ({y} : Set (points B S hS Y.1))),
      ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y), IsBlowupAtClosedPoint B S hS y hy b)
    (pullbackOfEffectiveCartier : ∀ (Y Y' : AlgebraicSpaces B S hS) (y : points B S hS Y.1)
      (hy : IsClosed ({y} : Set (points B S hS Y.1))) (b : Y' ⟶ Y),
      IsBlowupAtClosedPoint B S hS y hy b →
      ∀ D : ClosedSubspaces B S hS Y.1, IsEffectiveCartierDivisor B S hS Y D →
        IsPullbackDefined B S hS b D)
    (splitting : ∀ (Y : AlgebraicSpaces B S hS) (T : Set (points B S hS Y.1)), T.Finite →
      (∀ y ∈ T, IsClosed ({y} : Set (points B S hS Y.1))) →
      (∀ y ∈ T, IsRegularAt B S hS Y.1 y) →
      (∀ y ∈ T, localRingDimension B S hS y = 2) →
      ∀ Z : ClosedSubspaces B S hS Y.1, subspacePointSet B S hS Y.1 Z.1 ⊆ T →
      ∀ y ∈ subspacePointSet B S hS Y.1 Z.1,
      ∀ (hy : IsClosed ({y} : Set (points B S hS Y.1))) (Y' : AlgebraicSpaces B S hS)
        (b : Y' ⟶ Y), IsBlowupAtClosedPoint B S hS y hy b →
        ∃ (E Z' : ClosedSubspaces B S hS Y'.1) (T' : Set (points B S hS Y'.1)),
          preimageClosedSubspace b Z = sumClosedSubspaces B S hS Y' E Z' ∧
          IsEffectiveCartierDivisor B S hS Y' E ∧
          T'.Finite ∧
          (∀ z ∈ T', IsClosed ({z} : Set (points B S hS Y'.1))) ∧
          (∀ z ∈ T', IsRegularAt B S hS Y'.1 z) ∧
          (∀ z ∈ T', localRingDimension B S hS z = 2) ∧
          (∀ z ∈ T', pointsMap B S hS Y'.1 b.hom z ∈ T) ∧
          subspacePointSet B S hS Y'.1 Z'.1 ⊆ T' ∧
          colength Y' Z' T' < colength Y Z T)
    (hterm : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (_hX : IsNoetherian B S hS hterm X.1)
    (T : Set (points B S hS X.1)) (hTfinite : T.Finite)
    (hTclosed : ∀ x ∈ T, IsClosed ({x} : Set (points B S hS X.1)))
    (hTregular : ∀ x ∈ T, IsRegularAt B S hS X.1 x)
    (hTdim : ∀ x ∈ T, localRingDimension B S hS x = 2)
    (Z : ClosedSubspaces B S hS X.1)
    (hZsupport : subspacePointSet B S hS X.1 Z.1 ⊆ T) :
    ∃ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X),
      Nonempty (BlowupFactorization B S hS T f) ∧
        IsPullbackDefined B S hS f Z ∧
        ∀ D : ClosedSubspaces B S hS X.1, IsEffectiveCartierDivisor B S hS X D →
          IsPullbackDefined B S hS f D := by
  suffices H : ∀ (m : ℕ∞) (Y : AlgebraicSpaces B S hS) (T : Set (points B S hS Y.1)),
      T.Finite → (∀ x ∈ T, IsClosed ({x} : Set (points B S hS Y.1))) →
      (∀ x ∈ T, IsRegularAt B S hS Y.1 x) →
      (∀ x ∈ T, localRingDimension B S hS x = 2) →
      ∀ Z : ClosedSubspaces B S hS Y.1, subspacePointSet B S hS Y.1 Z.1 ⊆ T →
      colength Y Z T = m →
      ∃ (W : AlgebraicSpaces B S hS) (f : W ⟶ Y),
        Nonempty (BlowupFactorization B S hS T f) ∧
          IsPullbackDefined B S hS f Z ∧
          ∀ D : ClosedSubspaces B S hS Y.1, IsEffectiveCartierDivisor B S hS Y D →
            IsPullbackDefined B S hS f D by
    exact H _ X T hTfinite hTclosed hTregular hTdim Z hZsupport rfl
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  intro Y T hTc hTcl hTr hTd Z hZs hm
  by_cases hne : (subspacePointSet B S hS Y.1 Z.1).Nonempty
  · obtain ⟨y, hy⟩ := hne
    have hyT : y ∈ T := hZs hy
    have hycl : IsClosed ({y} : Set (points B S hS Y.1)) := hTcl y hyT
    obtain ⟨Y', b, hb⟩ := blowupExists Y y hycl
    obtain ⟨E, Z', T', hsplit, hE, hT'fin, hT'cl, hT'r, hT'd, hT'over, hZ'supp, hlt⟩ :=
      splitting Y T hTc hTcl hTr hTd Z hZs y hy hycl Y' b hb
    obtain ⟨W, f, ⟨F⟩, hfZ', hfcart⟩ :=
      ih (colength Y' Z' T') (hm ▸ hlt) Y' T' hT'fin hT'cl hT'r hT'd Z' hZ'supp rfl
    have hmono : T' ⊆ pointsMap B S hS Y'.1 b.hom ⁻¹' T := fun z hz => hT'over z hz
    refine ⟨W, f ≫ b, ⟨(BlowupFactorization.ofBlowup T hb hyT).comp (F.mono hmono)⟩, ?_, ?_⟩
    · rw [isPullbackDefined_comp_iff B S hS f b Z, hsplit]
      exact isPullbackDefined_sumClosedSubspaces B S hS f E Z' (hfcart E hE) hfZ'
    · intro D hD
      rw [isPullbackDefined_comp_iff B S hS f b D]
      exact hfcart (preimageClosedSubspace b D)
        (pullbackOfEffectiveCartier Y Y' y hycl b hb D hD)
  · have hempty : IsEmpty (points B S hS Z.1.toFunctor) := by
      rw [Set.not_nonempty_iff_eq_empty] at hne
      exact Set.range_eq_empty_iff.mp hne
    have hZcart : IsEffectiveCartierDivisor B S hS Y Z :=
      isEffectiveCartierDivisor_of_isEmpty_points B S hS Y Z hempty
    exact ⟨Y, 𝟙 Y, ⟨BlowupFactorization.ofIso T (Iso.refl Y)⟩,
      isPullbackDefined_id B S hS Y Z hZcart,
      fun D hD => isPullbackDefined_id B S hS Y D hD⟩

end AlgebraicGeometry.Space

end
