module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite.TransportedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.Permanence
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianOfFiniteTypeOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSmallerBase

/-!
# Nagata's compactification theorem: reduction to a base of finite type over `Spec ℤ`

Let `Y` be a quasi-compact and quasi-separated algebraic space over `Spec ℤ` and `f : X ⟶ Y` a
separated morphism of finite type. To compactify `X` over `Y` it suffices to compactify every
separated morphism of finite type over an algebraic space which is quasi-compact,
quasi-separated and of finite type over `Spec ℤ`.

The argument is the following.

1. `X` is a closed subspace of an algebraic space `X'` separated and of finite presentation
   over `Y` (Stacks 0873); the scheme-theoretic closure of `X` in a compactification of `X'` is
   a compactification of `X`, so we may assume `f` of finite presentation.
2. `Y` is the limit of a directed system `(Y_i)` of algebraic spaces of finite type over
   `Spec ℤ`, quasi-separated, with affine transition morphisms (Stacks 07SU), satisfying the
   convention of Section 70.2.
3. `X ⟶ Y` descends to a morphism of finite presentation `X_{i₀} ⟶ Y_{i₀}` (Stacks 07SK), and
   after increasing the index its base change `X_i ⟶ Y_i` is separated (Stacks 0851), both
   under that convention.
4. A compactification of `X_i` over `Y_i` base changes to one of `X` over `Y`.

## Main results

* `AlgebraicGeometry.Space.hasCompactification_of_forall_isFiniteType_viewOverIntegers`: the
  reduction.

## Implementation notes

The base scheme is the terminal scheme `Spec ℤ`, as in the source, which replaces the base
scheme of Nagata's theorem by `Spec ℤ` before the reduction (Spaces, Section 03I3); a space over
an arbitrary base is brought here by
`AlgebraicGeometry.Space.hasCompactification_relocalize_iff`. Over a general base the step
cannot be performed: over the spectrum of a field of cardinality at least the cutoff of the
site, no nonempty algebraic space of finite type over `Spec ℤ` maps to the base, so a nonempty
space over it is the limit of no system as in Stacks 07SU.

The case of Nagata's theorem over a base of finite type over `Spec ℤ` is the hypothesis
`hNoeth`; it is the statement being reduced to. Stacks 0873 is
`AlgebraicGeometry.Space.exists_isClosedImmersion_isSeparated_isFinitePresentation_of_isFiniteType`.

Stacks 07SU is applied in the form its proof gives,
`AlgebraicGeometry.Space.hasConventionalNoetherianApproximation_of_etaleAtlas`: a
`AlgebraicGeometry.Space.NoetherianApproximation` of `Y` whose inverse system satisfies the
chapter's standing convention of Section 70.2 (tag 07SD,
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`), that the limit of the base changes of
the stages along an affine scheme-valued point lies in the site. Nothing bounds the size of the
index set, and nothing can: an approximation by spaces of finite type over `ℤ` needs at least
as many indices as the ring of an affine étale atlas of `Y` has elements. The limit `lim Y_i` is
an algebraic space of the site by Stacks 07SF under the convention
(`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits`), and the
given limit cone identifies it with `Y`. Stacks 07SK is then applied under the convention
(`AlgebraicGeometry.Space.exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits`),
and Stacks 0851 in the form proved by enlarging the site, again under the convention
(`AlgebraicGeometry.Space.exists_isSeparated_pullbackMap_of_siteContainsBaseChangeLimits`).

The convention cannot be dropped. The limit is formed in presheaves on the site, which only see
rings below the cutoff, so a system can have `Y` as its limit there while its limit among all
algebraic spaces is larger. For instance, if `K` is a field of cardinality at least the cutoff,
the spectra of the finitely generated subrings of `K × ℤ` form such a system, with affine
transition morphisms and stages of finite type over `Spec ℤ`, whose limit in presheaves on the
site is `Spec ℤ`: a nonzero ring below the cutoff receives no homomorphism from `K`, so every
homomorphism from `K × ℤ` to a ring of the site factors through the projection to `ℤ`. The
descent theorems do not apply to it; the system constructed in the proof of Stacks 07SU
satisfies the convention, which is what they use.

Quasi-separatedness of an algebraic space is the absolute notion of Stacks 03BS, part (3), and
being of finite type over `Spec ℤ` is read on the view of the space over the terminal scheme,
as in `AlgebraicGeometry.Space.NoetherianApproximation`.

## References

* [Stacks Project, Tag 0F4D](https://stacks.math.columbia.edu/tag/0F4D)
* [Stacks Project, Section 03I3](https://stacks.math.columbia.edu/tag/03I3)
* [Stacks Project, Tag 0873](https://stacks.math.columbia.edu/tag/0873)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 0851](https://stacks.math.columbia.edu/tag/0851)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}}

/-- A separated morphism followed by an isomorphism is separated. -/
private theorem isSeparated_comp_of_isIso_right (hZ : B.Contains (⊤_ Scheme.{u}))
    {P Q R : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} {f : P ⟶ Q} (g : Q ⟶ R) [IsIso g]
    (hf : IsSeparated B (⊤_ Scheme.{u}) hZ f) : IsSeparated B (⊤_ Scheme.{u}) hZ (f ≫ g) :=
  isSeparated_comp B _ hZ _ _ hf (isSeparated_of_isIso B _ hZ _)

/-- A separated morphism preceded by an isomorphism is separated. -/
private theorem isSeparated_comp_of_isIso_left (hZ : B.Contains (⊤_ Scheme.{u}))
    {P Q R : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (f : P ⟶ Q) [IsIso f] {g : Q ⟶ R}
    (hg : IsSeparated B (⊤_ Scheme.{u}) hZ g) : IsSeparated B (⊤_ Scheme.{u}) hZ (f ≫ g) :=
  isSeparated_comp B _ hZ _ _ (isSeparated_of_isIso B _ hZ _) hg

/- The theorem below is untagged: it is a step in the proof of Stacks 0F4D, whose registration
is `AlgebraicGeometry.Space.hasCompactification_of_isSeparated_of_isFiniteType`. -/

/-- **Reduction of Nagata's theorem to a base of finite type over `Spec ℤ`.** Let `Y` be a
quasi-compact and quasi-separated algebraic space over `Spec ℤ`. Suppose every separated
morphism of finite type to an algebraic space over `Spec ℤ` which is quasi-compact,
quasi-separated and of finite type over `Spec ℤ` has a compactification. Then so does every
separated morphism of finite type `f : X ⟶ Y`. -/
theorem hasCompactification_of_forall_isFiniteType_viewOverIntegers
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hNoeth : ∀ {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Y),
      IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X → IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y →
      IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Y →
      IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Y →
      IsFiniteType B (⊤_ Scheme.{u}) hZ
        (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ Y)) →
      IsSeparated B (⊤_ Scheme.{u}) hZ f → IsFiniteType B (⊤_ Scheme.{u}) hZ f →
      HasCompactification B (⊤_ Scheme.{u}) hZ f)
    {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X) (hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y)
    (hYqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Y)
    (hYqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Y)
    (hsep : IsSeparated B (⊤_ Scheme.{u}) hZ f) (hft : IsFiniteType B (⊤_ Scheme.{u}) hZ f) :
    HasCompactification B (⊤_ Scheme.{u}) hZ f := by
  obtain ⟨X', i, f', hX', hi, hf'sep, hf'fp, rfl⟩ :=
    exists_isClosedImmersion_isSeparated_isFinitePresentation_of_isFiniteType B _ hZ hX hY f hft
      hsep hYqc hYqs
  refine HasCompactification.of_isClosedImmersion i hX' hY hi ?_
  -- Stacks 07SU: a Noetherian approximation of `Y` whose system satisfies the convention.
  obtain ⟨U, a, -, has, hae⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B (⊤_ Scheme.{u}) hZ Y hY).mp
      hYqc
  obtain ⟨A, hconv⟩ := hasConventionalNoetherianApproximation_of_etaleAtlas hY hYqc hYqs U a has
    hae
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  let D := A.diagram
  have hQc : ∀ j, IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (D.obj j) := fun j =>
    isQuasiCompactSpace_of_isFiniteType_viewOverIntegers hZ (A.isFiniteTypeOverIntegers j)
  have hL : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (limit D) :=
    isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ D hconv
      A.isAlgebraicSpace A.isAffineHom_map hQc
  -- The given limit cone identifies `Y` with `lim Y_i`; replace `f'` by `X' ⟶ lim Y_i`.
  let e : Y ≅ limit D := A.isLimit.conePointUniqueUpToIso (limit.isLimit D)
  refine HasCompactification.of_isPullback (q := 𝟙 X') (f := f' ≫ e.hom) (g := e.hom)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) hL hY ?_
  have hf''sep : IsSeparated B (⊤_ Scheme.{u}) hZ (f' ≫ e.hom) :=
    isSeparated_comp_of_isIso_right hZ _ hf'sep
  have hf''fp : IsFinitePresentation B (⊤_ Scheme.{u}) hZ (f' ≫ e.hom) :=
    isFinitePresentation_of_isPullback B (⊤_ Scheme.{u}) hZ hX' hX' hL hY
      (IsPullback.of_horiz_isIso (fst := 𝟙 X') (snd := f' ≫ e.hom) (f := f') (g := e.inv)
        ⟨by simp⟩) hf'fp
  generalize f' ≫ e.hom = f'' at hf''sep hf''fp ⊢
  clear hf'sep hf'fp
  -- Stacks 07SK: `X' ⟶ lim Y_i` descends to a morphism of finite presentation over a stage.
  obtain ⟨j₀, Xi, hXi, hXifp, ⟨φ⟩⟩ :=
    exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ hZ D
      A.isAlgebraicSpace A.isAffineHom_map hQc A.isAbsolutelyQuasiSeparated hconv hL
      (Over.mk f'') hX' hf''fp
  have hφ : φ.hom.left ≫ pullback.snd Xi.hom (limit.π D j₀) = f'' := Over.w φ.hom
  have hφ' : φ.inv.left ≫ f'' = pullback.snd Xi.hom (limit.π D j₀) := Over.w φ.inv
  have : IsIso φ.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso φ).hom)
  have : IsIso φ.inv.left := inferInstanceAs (IsIso ((Over.forget _).mapIso φ).inv)
  -- Stacks 0851: separatedness descends to a later stage.
  have hXiqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Xi.left :=
    isQuasiCompactSpace_source_of_isQuasiCompact B (⊤_ Scheme.{u}) hZ (A.isAlgebraicSpace j₀)
      (hQc j₀) hXifp.2.1
  have hXiqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Xi.left :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ hXi
      (A.isAbsolutelyQuasiSeparated j₀) hXifp.2.2
  have hfst : IsSeparated B (⊤_ Scheme.{u}) hZ (pullback.fst (limit.π D j₀) Xi.hom) := by
    rw [← pullbackSymmetry_hom_comp_snd, ← hφ']
    exact isSeparated_comp_of_isIso_left hZ _ (isSeparated_comp_of_isIso_left hZ _ hf''sep)
  have hsepLim : IsSeparated B (⊤_ Scheme.{u}) hZ (pullback.map (limit.π D (op (unop j₀))) Xi.hom
      (limit.π D (op (unop j₀))) (𝟙 _) (𝟙 _) Xi.hom (𝟙 _) (by simp) (by simp)) := by
    refine isSeparated_of_comp B (⊤_ Scheme.{u}) hZ _
      (pullback.fst (limit.π D j₀) (𝟙 (D.obj j₀))) ?_
    rw [pullback.lift_fst, Category.comp_id]
    exact hfst
  obtain ⟨i, hi, hsepi⟩ :=
    exists_isSeparated_pullbackMap_of_siteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ hZ D
      A.isAlgebraicSpace A.isAffineHom_map hconv hQc (unop j₀) Xi.hom (𝟙 _) Xi.hom
      (Category.comp_id _) hXi (A.isAlgebraicSpace j₀) (A.isAbsolutelyQuasiSeparated j₀) hXiqc
      hXiqs (hQc j₀) (A.isAbsolutelyQuasiSeparated j₀) hsepLim
  let b : D.obj (op i) ⟶ D.obj j₀ := D.map (homOfLE hi).op
  let g : pullback b Xi.hom ⟶ D.obj (op i) := pullback.fst b Xi.hom
  have hgsep : IsSeparated B (⊤_ Scheme.{u}) hZ g := by
    have : IsIso (pullback.fst b (𝟙 (D.obj j₀))) := pullback_fst_iso_of_right_iso _ _
    have hw : g = pullback.map b Xi.hom b (𝟙 _) (𝟙 _) Xi.hom (𝟙 _) (by simp) (by simp) ≫
        pullback.fst b (𝟙 (D.obj j₀)) := by
      rw [pullback.lift_fst, Category.comp_id]
    rw [hw]
    exact isSeparated_comp_of_isIso_right hZ _ hsepi
  have hPi : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (pullback b Xi.hom) :=
    isAlgebraicSpace_pullback B (⊤_ Scheme.{u}) hZ _ _ (A.isAlgebraicSpace (op i)) hXi
      (A.isAlgebraicSpace j₀)
  have hgft : IsFiniteType B (⊤_ Scheme.{u}) hZ g :=
    isFiniteType_of_isFinitePresentation B (⊤_ Scheme.{u}) hZ
      (isFinitePresentation_of_isPullback B (⊤_ Scheme.{u}) hZ hPi hXi
        (A.isAlgebraicSpace (op i)) (A.isAlgebraicSpace j₀)
        (IsPullback.of_hasPullback b Xi.hom).flip hXifp)
  have hgc : HasCompactification B (⊤_ Scheme.{u}) hZ g :=
    hNoeth g hPi (A.isAlgebraicSpace (op i)) (hQc (op i))
      (A.isAbsolutelyQuasiSeparated (op i)) (A.isFiniteTypeOverIntegers (op i)) hgsep hgft
  -- Base change of the compactification of `X_i` over `Y_i` along `lim Y_i ⟶ Y_i`.
  have hb : limit.π D (op i) ≫ b = limit.π D j₀ := limit.w D (homOfLE hi).op
  have hbig : IsPullback (φ.hom.left ≫ pullback.fst Xi.hom (limit.π D j₀)) f'' Xi.hom
      (limit.π D (op i) ≫ b) := by
    rw [hb]
    have h := IsPullback.paste_horiz
      (IsPullback.of_horiz_isIso (fst := φ.hom.left) (snd := f'')
        (f := pullback.snd Xi.hom (limit.π D j₀)) (g := 𝟙 (limit D))
        ⟨by rw [hφ, Category.comp_id]⟩)
      (IsPullback.of_hasPullback Xi.hom (limit.π D j₀))
    rwa [Category.id_comp] at h
  let q : X' ⟶ pullback b Xi.hom :=
    pullback.lift (f'' ≫ limit.π D (op i)) (φ.hom.left ≫ pullback.fst Xi.hom (limit.π D j₀))
      (by rw [Category.assoc]; exact hbig.w.symm)
  have hsq : IsPullback q f'' g (limit.π D (op i)) := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback b Xi.hom).flip
    rw [pullback.lift_snd]
    exact hbig
  exact HasCompactification.of_isPullback hsq (A.isAlgebraicSpace (op i)) hL hgc

end AlgebraicGeometry.Space

end
