module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparationLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated

/-!
# Separating two disjoint quasi-compact open subspaces by a blowup

Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated algebraic space over `S`
and let `U, V ⊆ X` be disjoint quasi-compact open subspaces.  Stacks 086F asserts that there is
a `U ∪ V`-admissible blowup `b : X' ⟶ X` whose source is a disjoint union of two open subspaces
`X' = X'₁ ⊔ X'₂` with `b⁻¹(U) ⊆ X'₁` and `b⁻¹(V) ⊆ X'₂`.  This file proves it under exactly
those hypotheses.

## Main results

* `AlgebraicGeometry.Space.exists_closedSubspace_disjoint_superset`: a finitely presented closed
  subspace of `X` containing a quasi-compact open subspace and avoiding a disjoint one.
* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_disjoint_openSubspace_decomposition'`:
  **Stacks 086F**.

## Implementation notes

The source chooses finite type quasi-coherent sheaves of ideals `𝓘, 𝓙` with
`|X| ∖ |U| = |V(𝓘)|` and `|X| ∖ |V| = |V(𝓙)|` (Stacks 0855), so that `𝓘𝓙` is locally
nilpotent, and blows up in `𝓘 + 𝓙`.  What the rest of the argument uses is less: closed
subspaces `Z₁ = V(𝓘)` and `Z₂ = V(𝓙)` of finite presentation with `|Z₁|` disjoint from `|U|`,
`|Z₂|` disjoint from `|V|` and `|Z₁| ∪ |Z₂| = |X|`.  Given such a pair the conclusion is
`exists_isAdmissibleBlowup_disjoint_openSubspace_decomposition_of_closedSubspaces` of
`StacksFrontier/AlgebraicGeometry/Spaces/AdmissibleBlowupSeparationLocal.lean`: the blowup in
the scheme-theoretic intersection `Z₁ ∩ Z₂` (the sum `𝓘 + 𝓙`), with the étale-local reduction
to the scheme case of Stacks 080P carried out there.

The pair is produced by the extension of finitely presented closed subspaces from
quasi-compact open subspaces (the closed-subspace form of Stacks 0853,
`AlgebraicGeometry.Space.exists_closedSubspace_extension_disjoint`), used twice.  First extend
the whole of `V` across the empty closed subspace on `U`: this gives `Z₁` of finite
presentation with `|V| ⊆ |Z₁|` and `|Z₁| ∩ |U| = ∅`.  Its open complement `O₁` is quasi-compact
(`AlgebraicGeometry.Space.isQuasiCompactSpace_openComplement_of_isFinitePresentation`) and
disjoint from `V`, so the same extension applied to the whole of `O₁` across the empty closed
subspace on `V` gives `Z₂` with `|O₁| ⊆ |Z₂|` and `|Z₂| ∩ |V| = ∅`; then
`|Z₁| ∪ |Z₂| ⊇ |Z₁| ∪ |O₁| = |X|`.

## References

* [Stacks Project, Tag 086F](https://stacks.math.columbia.edu/tag/086F)
* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 0855](https://stacks.math.columbia.edu/tag/0855)
* [Stacks Project, Tag 080P](https://stacks.math.columbia.edu/tag/080P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A finitely presented closed subspace containing one quasi-compact open subspace and
avoiding a disjoint one.**  Let `X` be a quasi-compact and quasi-separated algebraic space and
let `U, V ⊆ X` be quasi-compact open subspaces with disjoint sets of points.  Then there is a
closed subspace `Z ⊆ X` of finite presentation whose points avoid those of `U` and contain
those of `V`.

The whole of `V`, a finitely presented closed subspace of `V`, has no points over `U ∩ V`, so
it extends to such a `Z` with `Z ∩ V = V` by
`AlgebraicGeometry.Space.exists_closedSubspace_extension_disjoint`. -/
theorem exists_closedSubspace_disjoint_superset (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS} (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (U V : Subfunctor X.1) (hU : IsOpenSubspace B S hS U) (hV : IsOpenSubspace B S hS V)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    (hUV : Disjoint (subspacePointSet B S hS X.1 U) (subspacePointSet B S hS X.1 V)) :
    ∃ Z : Subfunctor X.1, IsClosedSubspace B S hS Z ∧ IsFinitePresentation B S hS Z.ι ∧
      Disjoint (subspacePointSet B S hS X.1 U) (subspacePointSet B S hS X.1 Z) ∧
        subspacePointSet B S hS X.1 V ⊆ subspacePointSet B S hS X.1 Z := by
  have hVtop : IsClosedSubspace B S hS (⊤ : Subfunctor V.toFunctor) :=
    ⟨hV.1.of_iso (asIso (Subfunctor.ι (⊤ : Subfunctor V.toFunctor))).symm,
      isClosedImmersion_of_isIso B S hS _⟩
  have hVfp : IsFinitePresentation B S hS (⊤ : Subfunctor V.toFunctor).ι :=
    ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS (isOpenSubspace_top hV.1).2,
      isQuasiCompact_of_isClosedImmersion' B S hS hVtop.2,
      isQuasiSeparated_of_mono B S hS _ inferInstance⟩
  obtain ⟨Z, hZc, hZfp, hZU, hZV⟩ := exists_closedSubspace_extension_disjoint hZ hXqc hXqs U V
    hU hV hUqc hVqc ⊤ hVtop hVfp (by
      rw [subspacePointSet_preimage]
      exact Set.disjoint_left.2 fun p hp _ => Set.disjoint_left.1 hUV hp (Set.mem_range_self p))
  refine ⟨Z, hZc, hZfp, hZU, range_pointsMap_ι_le B S hS fun T x hx => ?_⟩
  have h : (⟨x, hx⟩ : V.toFunctor.obj T) ∈ (Z.preimage V.ι).obj T := by
    rw [hZV]
    trivial
  exact h

/-- **Stacks 086F.**  Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated
algebraic space over `S` and let `U, V ⊆ X` be quasi-compact open subspaces with disjoint sets
of points.  Then there is a `U ∪ V`-admissible blowup `b : X' ⟶ X` such that `X'` is the
disjoint union of two open subspaces `X' = X'₁ ⊔ X'₂` with `b⁻¹(U) ⊆ X'₁` and
`b⁻¹(V) ⊆ X'₂`.

"`X'` is the disjoint union of `X'₁` and `X'₂`" is recorded as follows: the two
are open and closed subspaces with complementary sets of points, whose join sheafifies to `X'`
and whose meet is the sheafification of the bottom subfunctor.

Two finitely presented closed subspaces `Z₁, Z₂` with `|Z₁| ∩ |U| = ∅`, `|Z₂| ∩ |V| = ∅` and
`|Z₁| ∪ |Z₂| = |X|` are produced by two applications of
`AlgebraicGeometry.Space.exists_closedSubspace_disjoint_superset`, the second to `V` and the
quasi-compact open complement of `Z₁`; the blowup in `Z₁ ∩ Z₂` is then the one sought, by
`exists_isAdmissibleBlowup_disjoint_openSubspace_decomposition_of_closedSubspaces`. -/
@[stacks 086F]
theorem exists_isAdmissibleBlowup_disjoint_openSubspace_decomposition'
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (U V : OpenSubspaces B S hS X.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hVqc : IsQuasiCompactSpace B S hS V.1.toFunctor)
    (hUV : Disjoint (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 V.1)) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X) (X'₁ X'₂ : OpenSubspaces B S hS X'.1),
      IsAdmissibleBlowup B S hS (openSubspaceUnion B S hS X U V) b ∧
        IsClosedSubspace B S hS X'₁.1 ∧ IsClosedSubspace B S hS X'₂.1 ∧
          Disjoint (subspacePointSet B S hS X'.1 X'₁.1)
            (subspacePointSet B S hS X'.1 X'₂.1) ∧
            subspacePointSet B S hS X'.1 X'₁.1 ∪ subspacePointSet B S hS X'.1 X'₂.1
                = Set.univ ∧
              (X'₁.1 ⊔ X'₂.1).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
                X'₁.1 ⊓ X'₂.1
                    = (⊥ : Subfunctor X'.1).sheafify (BigFppfOver.topology B S hS) ∧
                  U.1.preimage b.hom ≤ X'₁.1 ∧ V.1.preimage b.hom ≤ X'₂.1 := by
  obtain ⟨Z₁, hZ₁c, hZ₁fp, hZ₁U, hZ₁V⟩ :=
    exists_closedSubspace_disjoint_superset hZ hXqc hXqs U.1 V.1 U.2 V.2 hUqc hVqc hUV
  have hO₁ := isOpenSubspace_openComplement B S hS X.2 Z₁ hZ₁c
  have hO₁qc := isQuasiCompactSpace_openComplement_of_isFinitePresentation X.2 hXqc Z₁ hZ₁c hZ₁fp
  have hO₁pts : subspacePointSet B S hS X.1 (openComplement B S hS Z₁) =
      (subspacePointSet B S hS X.1 Z₁)ᶜ :=
    range_pointsMap_ι_openComplement B S hS Z₁
  have hVO₁ : Disjoint (subspacePointSet B S hS X.1 V.1)
      (subspacePointSet B S hS X.1 (openComplement B S hS Z₁)) := by
    rw [hO₁pts]
    exact Set.disjoint_compl_right_iff_subset.2 hZ₁V
  obtain ⟨Z₂, hZ₂c, hZ₂fp, hZ₂V, hZ₂O₁⟩ := exists_closedSubspace_disjoint_superset hZ hXqc hXqs
    V.1 (openComplement B S hS Z₁) V.2 hO₁ hVqc hO₁qc hVO₁
  refine exists_isAdmissibleBlowup_disjoint_openSubspace_decomposition_of_closedSubspaces U V
    ⟨Z₁, hZ₁c⟩ ⟨Z₂, hZ₂c⟩ hZ₁fp hZ₂fp (Set.eq_univ_of_forall fun x => ?_) hZ₁U hZ₂V
  by_cases hx : x ∈ subspacePointSet B S hS X.1 Z₁
  · exact Or.inl hx
  · exact Or.inr (hZ₂O₁ (by rw [hO₁pts]; exact hx))

end AlgebraicGeometry.Space

end
