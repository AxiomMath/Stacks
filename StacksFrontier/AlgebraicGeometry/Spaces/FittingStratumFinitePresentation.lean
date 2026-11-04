module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingClosedSubspaceFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingRankStratumRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplementQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# Finite presentation of the three morphisms of Stacks 0CZ9, and the tag entire

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `G` be a
quasi-coherent `𝒪_X`-module of finite presentation, with `Z_0 ⊇ Z_1 ⊇ …` the chain of closed
subspaces cut out by the Fitting ideal sheaves of `G`.  The final assertion of Stacks 0CZ9 is
that `Z_r ⟶ X`, `X ∖ Z_r ⟶ X` and `Z_{r-1} ∖ Z_r ⟶ X` are all of finite presentation.

The first of the three is
`AlgebraicGeometry.Space.isFinitePresentation_fittingClosedSubspace`.  The second is the
open-immersion case: by Stacks 03XP finite presentation is locally of finite presentation
together with quasi-compactness and quasi-separatedness, an open immersion is locally of finite
presentation by Stacks 06CN and quasi-separated because it is a monomorphism, and
quasi-compactness is
`AlgebraicGeometry.Space.isQuasiCompact_ι_openComplement_fittingClosedSubspace`.  The third is
the intersection `Z_{r-1} ⊓ (X ∖ Z_r)`, which is the base change of `X ∖ Z_r ⟶ X` along
`Z_{r-1} ⟶ X` followed by `Z_{r-1} ⟶ X`; finite presentation is stable under base change by
Stacks 03XR and under composition by Stacks 03XQ.

With all three in hand the whole of Stacks 0CZ9 is one statement,
`AlgebraicGeometry.Space.exists_fittingClosedSubspaces_spec`, and that is where the tag is
registered.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_ι_inf`: the inclusion of the intersection of two
  subspaces whose inclusions are of finite presentation is of finite presentation.
* `AlgebraicGeometry.Space.isFinitePresentation_ι_openComplement_fittingClosedSubspace`:
  **`X ∖ Z_r ⟶ X` is of finite presentation.**
* `AlgebraicGeometry.Space.isFinitePresentation_ι_fittingRankStratum`: **`Z_{r-1} ∖ Z_r ⟶ X` is
  of finite presentation**, which is also the finite presentation of `X_r ⟶ X` asserted by
  Stacks 0CZA.
* `AlgebraicGeometry.Space.exists_fittingClosedSubspaces_spec`: **Stacks 0CZ9 entire** — the
  chain, its three properties, and the finite presentation of the three morphisms under the
  stronger hypothesis the tag makes for them.

## Implementation notes

The intersection of two subspaces is a fibre product by
`CategoryTheory.Subfunctor.isPullback_inf`, and the square is transported into the category of
algebraic spaces by `CategoryTheory.IsPullback.of_map_of_faithful` along the full embedding;
that is the only reason algebraicity of the intersection is a hypothesis of
`AlgebraicGeometry.Space.isFinitePresentation_ι_inf` rather than a conclusion.  For the stratum
it is supplied by `AlgebraicGeometry.Space.isLocallyClosedSubspace_fittingRankStratum`.

The `r = 0` stratum needs no separate argument about the inclusion of `⊤`: by
`AlgebraicGeometry.Space.fittingRankStratum_zero` it is already the open complement of `Z_0`.

Nothing here uses the chart comparison `hchart` of Stacks 084Q, and no hypothesis beyond the
tag's own is carried: clauses (1), (2) and (3) are stated from quasi-coherence and finite type,
and finite presentation of `G` enters only in the implication which the tag itself guards with
it.

## References

* [Stacks Project, Tag 0CZ9](https://stacks.math.columbia.edu/tag/0CZ9)
* [Stacks Project, Tag 0CZA](https://stacks.math.columbia.edu/tag/0CZA)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03XQ](https://stacks.math.columbia.edu/tag/03XQ)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 06CN](https://stacks.math.columbia.edu/tag/06CN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Finite presentation of the inclusion of an intersection -/

/-- **The inclusion of the intersection of two subspaces whose inclusions are of finite
presentation is of finite presentation.**

The intersection is the fibre product of the two inclusions, so its projection to the first is
the base change of the second, which is of finite presentation by Stacks 03XR; composing with
the first, of finite presentation by Stacks 03XQ, gives the inclusion of the intersection. -/
theorem isFinitePresentation_ι_inf (X : AlgebraicSpaces B S hS) (W U : Subfunctor X.1)
    (hWalg : IsAlgebraicSpace B S hS W.toFunctor)
    (hinfalg : IsAlgebraicSpace B S hS (W ⊓ U).toFunctor)
    (hUalg : IsAlgebraicSpace B S hS U.toFunctor)
    (hW : IsFinitePresentation B S hS W.ι) (hU : IsFinitePresentation B S hS U.ι) :
    IsFinitePresentation B S hS (W ⊓ U).ι := by
  let Ws : AlgebraicSpaces B S hS := ⟨W.toFunctor, hWalg⟩
  let Us : AlgebraicSpaces B S hS := ⟨U.toFunctor, hUalg⟩
  let Is : AlgebraicSpaces B S hS := ⟨(W ⊓ U).toFunctor, hinfalg⟩
  let i : Ws ⟶ X := ObjectProperty.homMk W.ι
  let k : Us ⟶ X := ObjectProperty.homMk U.ι
  let p : Is ⟶ Us := ObjectProperty.homMk (Subfunctor.homOfLe (inf_le_right : W ⊓ U ≤ U))
  let q : Is ⟶ Ws := ObjectProperty.homMk (Subfunctor.homOfLe (inf_le_left : W ⊓ U ≤ W))
  have hsq : IsPullback p q k i := IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS F)
    (Subfunctor.isPullback_inf W U)
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun {_ _} f ↦ IsFinitePresentation B S hS f.hom
  let : P.IsStableUnderBaseChange := isFinitePresentation_isStableUnderBaseChange B S hS
  have hq : IsFinitePresentation B S hS q.hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P) hsq hU
  have hmap : q.hom ≫ i.hom = (W ⊓ U).ι := by
    ext A x
    rfl
  rw [← hmap]
  exact isFinitePresentation_comp B S hS hinfalg hWalg X.2 q.hom i.hom hq hW

/-! ### The second and third morphisms of Stacks 0CZ9 -/

variable (X : AlgebraicSpaces B S hS) (G : Modules.{u, u} B S hS X.1 X.2)

/-- **The inclusion of `X ∖ Z_r` is of finite presentation**, for the Fitting closed subspaces of
a quasi-coherent `𝒪_X`-module of finite presentation.

By Stacks 03XP this is three conditions: locally of finite presentation, which holds for any open
immersion by Stacks 06CN; quasi-compact, which is
`AlgebraicGeometry.Space.isQuasiCompact_ι_openComplement_fittingClosedSubspace`; and
quasi-separated, which holds because the inclusion of a subfunctor is a monomorphism. -/
theorem isFinitePresentation_ι_openComplement_fittingClosedSubspace
    (hGqc : G.IsQuasicoherentOnSite) (hGfp : SheafOfModules.IsFinitePresentationOnSite G)
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r) (r : ℕ) :
    IsFinitePresentation B S hS (openComplement B S hS (Z r).1).ι :=
  ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS
      (isOpenSubspace_openComplement B S hS X.2 (Z r).1 (Z r).2).2,
    isQuasiCompact_ι_openComplement_fittingClosedSubspace B S hS X G hGqc hGfp Z hZ r,
    isQuasiSeparated_of_mono B S hS _ inferInstance⟩

/-- **The inclusion of the rank-`r` stratum `Z_{r-1} ∖ Z_r` is of finite presentation**, for the
Fitting closed subspaces of a quasi-coherent `𝒪_X`-module of finite presentation.  This is the
third morphism of the final assertion of Stacks 0CZ9, and also the finite presentation of
`X_r ⟶ X` asserted by Stacks 0CZA; the tag 0CZA is registered on the collected statement
`AlgebraicGeometry.Space.exists_fittingRankStratification_spec` of
`StacksFrontier/AlgebraicGeometry/Spaces/FittingStratificationFinitePresentation.lean`, which
consumes this.

For `r = 0` the stratum is the open complement of `Z_0`.  For `r + 1` it is the intersection of
`Z_r` — whose inclusion is of finite presentation by
`AlgebraicGeometry.Space.isFinitePresentation_fittingClosedSubspace` — with the open complement
of `Z_{r+1}`. -/
theorem isFinitePresentation_ι_fittingRankStratum
    (hGqc : G.IsQuasicoherentOnSite) (hGfp : SheafOfModules.IsFinitePresentationOnSite G)
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r) (r : ℕ) :
    IsFinitePresentation B S hS (fittingRankStratum B S hS X Z r).ι := by
  cases r with
  | zero =>
    rw [fittingRankStratum_zero]
    exact isFinitePresentation_ι_openComplement_fittingClosedSubspace B S hS X G hGqc hGfp Z hZ 0
  | succ n =>
    rw [fittingRankStratum_succ]
    exact isFinitePresentation_ι_inf B S hS X (Z n).1 _ (Z n).2.1
      (isLocallyClosedSubspace_fittingRankStratum B S hS X Z (n + 1)).1
      (isOpenSubspace_openComplement B S hS X.2 (Z (n + 1)).1 (Z (n + 1)).2).1
      (isFinitePresentation_fittingClosedSubspace B S hS X G hGqc hGfp (Z n) n (hZ n))
      (isFinitePresentation_ι_openComplement_fittingClosedSubspace B S hS X G hGqc hGfp Z
        hZ (n + 1))

/-! ### Stacks 0CZ9 -/

/-- **Stacks 0CZ9.**  Let `X` be an algebraic space over a scheme `S` contained in a big fppf
site `B` and let `G` be a quasi-coherent `𝒪_X`-module of finite type.  The Fitting ideal sheaves
of `G` cut out a decreasing chain of closed subspaces `X = Z_{-1} ⊇ Z_0 ⊇ Z_1 ⊇ …` such that

1. the intersection of the `Z_r` is empty;
2. for every algebraic space `T ⟶ X` the module `G_T` is locally generated by at most `r`
   sections exactly when `T ⟶ X` factors, necessarily uniquely, through `X ∖ Z_r`;
3. for every algebraic space `T ⟶ X` the module `G_T` is finite locally free of rank `r`
   exactly when `T ⟶ X` factors, necessarily uniquely, through `Z_{r-1} ∖ Z_r`;

and, if `G` is moreover of finite presentation, the three morphisms `Z_r ⟶ X`, `X ∖ Z_r ⟶ X` and
`Z_{r-1} ∖ Z_r ⟶ X` are of finite presentation.

The chain is the one cut out by `AlgebraicGeometry.Space.fittingIdeal`, the test objects of
clauses (2) and (3) are arbitrary algebraic spaces rather than only schemes over `X`, and
`Z_{r-1} ∖ Z_r` is `AlgebraicGeometry.Space.fittingRankStratum`, which for `r = 0` is
`X ∖ Z_0`. -/
@[stacks 0CZ9, ega "IV 1.4.5" "the closed subspaces"]
theorem exists_fittingClosedSubspaces_spec (hGqc : G.IsQuasicoherentOnSite)
    (hGft : SheafOfModules.IsFiniteTypeOnSite G) :
    ∃ Z : ℕ → ClosedSubspaces B S hS X.1,
      (∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r) ∧
      (Antitone fun r ↦ (Z r).1) ∧
      (⨅ r : ℕ, (Z r).1) = (⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS) ∧
      (∀ (T : AlgebraicSpaces B S hS) (r : ℕ) (f : T ⟶ X),
        (∀ x : points B S hS T.1, ∃ (U : SmallEtale B S hS T.1)
            (s : Fin r → ((modulePullback B S hS f).obj G).val.obj (op U)),
            IsAffine ((SmallEtale.toOver B S hS T.1 ⋙ BigFppfOver.toScheme B S hS).obj U) ∧
              Submodule.span (chartRing B S hS T.1 T.2 U) (Set.range s) = ⊤ ∧
                x ∈ Set.range (pointsMap B S hS
                  (yoneda.obj ((SmallEtale.toOver B S hS T.1).obj U)) U.1.hom)) ↔
          ∃! g : T.1 ⟶ (openComplement B S hS (Z r).1).toFunctor,
            g ≫ (openComplement B S hS (Z r).1).ι = f.hom) ∧
      (∀ (T : AlgebraicSpaces B S hS) (r : ℕ) (f : T ⟶ X),
        RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS T.1 T.2)
            ((modulePullback B S hS f).obj G) r ↔
          ∃! g : T.1 ⟶ (fittingRankStratum B S hS X Z r).toFunctor,
            g ≫ (fittingRankStratum B S hS X Z r).ι = f.hom) ∧
      (SheafOfModules.IsFinitePresentationOnSite G → ∀ r : ℕ,
        IsFinitePresentation B S hS (subspaceInclusion B S hS X (Z r)).hom ∧
          IsFinitePresentation B S hS (openComplement B S hS (Z r).1).ι ∧
            IsFinitePresentation B S hS (fittingRankStratum B S hS X Z r).ι) := by
  obtain ⟨Z, hZ, hanti, hbot⟩ :=
    exists_fittingClosedSubspaces_of_isFiniteTypeOnSite B S hS X G hGqc hGft
  exact ⟨Z, hZ, hanti, hbot, fun T r f ↦
    existsUnique_lift_openComplement_iff_forall_exists_fin_span B S hS G hGqc hGft Z hZ r f,
    fun T r f ↦ existsUnique_lift_fittingRankStratum_iff B S hS G hGqc hGft Z hZ r f,
    fun hGfp r ↦
      ⟨isFinitePresentation_fittingClosedSubspace B S hS X G hGqc hGfp (Z r) r (hZ r),
        isFinitePresentation_ι_openComplement_fittingClosedSubspace B S hS X G hGqc hGfp Z hZ r,
        isFinitePresentation_ι_fittingRankStratum B S hS X G hGqc hGfp Z hZ r⟩⟩

end AlgebraicGeometry.Space

end
