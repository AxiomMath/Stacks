module

public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.DenseAffineCover
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Gluing
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.RelativeProduct
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma

/-!
# Chow's lemma over a Noetherian base, modulo the projective embedding of an affine chart

**Chow's lemma over a Noetherian base** (Stacks 0200) says that a separated morphism `f : X ⟶ S`
of finite type over a Noetherian `S` admits a proper surjective `π : X' ⟶ X` with `X'` immersed
in a projective space over `S`, compatibly with the maps to `S`, and that `π` may be arranged to
be an isomorphism over a dense open subscheme of `X`.

This file proves that statement in full **from two hypotheses on the base `S`**, each of which
is a single Stacks tag of Chapter 29 and neither of which this repository or Mathlib contains:

* `AlgebraicGeometry.HasAffineProjectiveChart S` — every affine scheme locally of finite type
  over `S` immerses into a projective space over `S`, over `S`. This is **Stacks 01VS** for the
  structure sheaf, the one place in the Stacks proof of 0200 where ampleness is used.
* `AlgebraicGeometry.HasSegreEmbedding S` — **Stacks 01WD**, the Segre embedding.

Everything else in the Stacks proof is discharged: the dense affine cover (Stacks 01ZX), the
dominance machinery, the iterated fibre product, the proper charts and their gluing.

## Main definitions

* `AlgebraicGeometry.HasAffineProjectiveChart` is Stacks 01VS for the trivial invertible sheaf.
* `AlgebraicGeometry.HasDenseChowModification` is the full conclusion of Stacks 0200, i.e.
  `AlgebraicGeometry.HasChowModification` together with the dense open over which the
  modification is an isomorphism.

## Main results

* `AlgebraicGeometry.hasDenseChowModification_of_hasAffineProjectiveChart`: **Chow's lemma over
  a Noetherian base**, granted the two hypotheses above.
* `AlgebraicGeometry.hasChowModification_of_hasAffineProjectiveChart`: the same, stated with the
  repository's existing `AlgebraicGeometry.HasChowModification`, which is what the proof of
  Chow's lemma for a quasi-compact quasi-separated base (Stacks 0202) consumes.

## Implementation notes

The tag `@[stacks 0200]` is deliberately **not** placed on anything here. The results are
conditional on `HasAffineProjectiveChart` and `HasSegreEmbedding`, and 0200 asserts its
conclusion outright; placing the tag on a conditional statement would record a weakening as the
tag. When those two hypotheses are supplied — both belong to Chapter 29 —
`hasDenseChowModification_of_hasAffineProjectiveChart` becomes 0200 with no further work, and
the tag belongs on it then.

`HasAffineProjectiveChart` is the *only* thing the Stacks proof of 0200 needs from ampleness.
Stacks derives it as: an affine scheme is quasi-affine, so its structure sheaf is ample
(Stacks 01QE), so a high power of that sheaf gives an immersion into a projective space
(Stacks 01VS). The first step is already in this repository —
`AlgebraicGeometry.Scheme.Modules.isAmple_unit`,
`StacksFrontier/AlgebraicGeometry/Ample/StructureSheaf.lean:220`, for `[IsAffine Y]` directly, so
01QE is *not* part of the residue — and the second is absent.

The empty case is separated out: with no affine opens in the cover `X` is empty, hence affine,
and the identity of `X` is its own modification.

## References

* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [EGA II, Theorem 5.6.1(a)]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- **Stacks 01VS for the trivial invertible sheaf.** Every affine scheme locally of finite type
over `S` admits an immersion into a projective space over `S`, over `S`.

This is the only consequence of ampleness that the Stacks proof of Chow's lemma over a
Noetherian base uses. -/
def HasAffineProjectiveChart (S : Scheme.{u}) : Prop :=
  ∀ (U : Scheme.{u}) [IsAffine U] (g : U ⟶ S) [LocallyOfFiniteType g],
    ∃ (n : ℕ) (i : U ⟶ ProjectiveSpace n S),
      IsImmersion i ∧ i ≫ (ProjectiveSpace n S ↘ S) = g

/-- **The full conclusion of Chow's lemma, Stacks 0200**: a proper surjective `π : X' ⟶ X` with
`X'` immersed in a projective space over `S` compatibly with the maps to `S`, which is moreover
an isomorphism over a dense open subscheme of `X`.

This strengthens `AlgebraicGeometry.HasChowModification` by the last clause. -/
def HasDenseChowModification (f : X ⟶ S) : Prop :=
  ∃ (n : ℕ) (X' : Scheme.{u}) (π : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n S) (U : X.Opens),
    IsProper π ∧ Surjective π ∧ IsImmersion i ∧ π ≫ f = i ≫ (ProjectiveSpace n S ↘ S) ∧
      Dense (U : Set X) ∧ IsIso (π ∣_ U)

/-- Forgetting the dense open. -/
theorem HasDenseChowModification.hasChowModification {f : X ⟶ S}
    (h : HasDenseChowModification f) : HasChowModification f := by
  obtain ⟨n, X', π, i, U, hπ, hsurj, himm, hcomm, -, -⟩ := h
  exact ⟨n, X', π, i, hπ, hsurj, himm, hcomm⟩

/-- **Chow's lemma over a Noetherian base (Stacks 0200), granted the projective embedding of an
affine chart (Stacks 01VS) and the Segre embedding (Stacks 01WD) over the base.**

A separated morphism of finite type over a Noetherian base admits a proper surjective
modification immersed in a projective space over the base, which is an isomorphism over a dense
open subscheme of the source. -/
theorem hasDenseChowModification_of_hasAffineProjectiveChart
    (hchart : HasAffineProjectiveChart S) (hsegre : HasSegreEmbedding S) (f : X ⟶ S)
    [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    HasDenseChowModification f := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian X := ⟨⟩
  obtain ⟨F, U, hAffine, hcover, hSubset, hdense⟩ := exists_finite_dense_affine_open_cover (X := X)
  have : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  by_cases hF : F.Nonempty
  · let I := {V : X.Opens // V ∈ F}
    have : Nonempty I := by
      obtain ⟨V, hV⟩ := hF
      exact ⟨⟨V, hV⟩⟩
    have hNoeth : ∀ V : I, NoetherianSpace V.val.toScheme :=
      fun V => V.val.ι.isOpenEmbedding.isInducing.noetherianSpace
    -- a projective chart for each member of the cover, by Stacks 01VS over `S`
    have hcharts (V : I) : ∃ (n : ℕ) (i : V.val.toScheme ⟶ ProjectiveSpace n S),
        IsImmersion i ∧ i ≫ (ProjectiveSpace n S ↘ S) = V.val.ι ≫ f := by
      have : IsAffine V.val.toScheme := hAffine V.val V.property
      exact hchart V.val.toScheme (V.val.ι ≫ f)
    choose n j hj hcomm using hcharts
    have hjI : ∀ V, IsImmersion (j V) := hj
    -- their restrictions to `U` are charts of `U` over `S`
    have hAimm (V : I) : IsImmersion (X.homOfLE (hSubset V.val V.property) ≫ j V) := by
      infer_instance
    have hAcomm (V : I) :
        (X.homOfLE (hSubset V.val V.property) ≫ j V) ≫ (ProjectiveSpace (n V) S ↘ S) =
          U.ι ≫ f := by
      rw [Category.assoc, hcomm, Scheme.homOfLE_ι_assoc]
    -- all the charts of `U` factor through one scheme projective over `S`, by Segre
    obtain ⟨P, q, N, c, a, hc, hcq, ha, haq, hr⟩ :=
      exists_chartEnvelope_of_finite hsegre (f := U.ι ≫ f) n
        (fun V => X.homOfLE (hSubset V.val V.property) ≫ j V) hAimm hAcomm
    have : IsClosedImmersion c := hc
    have : IsImmersion a := ha
    have hqproper : IsProper q := by rw [← hcq]; infer_instance
    have : IsSchemeTheoreticallyDominant a.toImage := isSchemeTheoreticallyDominant_toImage a
    -- a proper chart over each member of the cover
    choose r hrq har using hr
    have hlocal (V : I) := exists_chart_of_image f q U V.val (hSubset V.val V.property) a (n V)
      (j V) (hcomm V) (r V) (hrq V) (har V)
    choose W k p s hk hp hsk hsp hkbase using hlocal
    have : ∀ V, IsOpenImmersion (k V) := hk
    have : ∀ V, IsProper (p V) := hp
    -- glue them
    obtain ⟨Y, i, π, t, hi, hπ, hiq, hti, htπ, hiso⟩ :=
      exists_modification_of_dense_charts f (a.imageι ≫ q) U a.toImage
        (fun V : I => V.val)
        (fun x => by
          obtain ⟨V, hV, hxV⟩ := hcover x
          exact ⟨⟨V, hV⟩, hxV⟩)
        (fun V => hSubset V.val V.property) W k p s hsk hsp hkbase
    have : IsOpenImmersion i := hi
    have : IsProper π := hπ
    refine ⟨N, Y, π, i ≫ a.imageι ≫ c, U, hπ,
      surjective_of_isProper_of_dense_section π U t htπ hdense, inferInstance, ?_, hdense, hiso⟩
    rw [← hiq, Category.assoc, Category.assoc, hcq]
  · have : IsEmpty X := ⟨fun x => by
      obtain ⟨V, hV, -⟩ := hcover x
      exact hF ⟨V, hV⟩⟩
    have : IsAffine X := inferInstance
    obtain ⟨m, e, he, hecomm⟩ := hchart X f
    have : IsImmersion e := he
    refine ⟨m, X, 𝟙 X, e, ⊤, inferInstance, ⟨fun x => ⟨x, rfl⟩⟩, he, ?_, by simp, ?_⟩
    · rw [Category.id_comp, hecomm]
    · infer_instance

/-- **Chow's lemma over a Noetherian base (Stacks 0200), in the form consumed by the proof of
Chow's lemma over a quasi-compact quasi-separated base (Stacks 0202)**: granted Stacks 01VS for
the structure sheaf and the Segre embedding over `S`, a separated morphism of finite type over a
Noetherian base has a Chow modification. -/
theorem hasChowModification_of_hasAffineProjectiveChart
    (hchart : HasAffineProjectiveChart S) (hsegre : HasSegreEmbedding S) (f : X ⟶ S)
    [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    HasChowModification f :=
  (hasDenseChowModification_of_hasAffineProjectiveChart hchart hsegre f).hasChowModification

end AlgebraicGeometry
