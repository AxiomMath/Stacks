module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.StructureSheafPullback
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic

/-!
# The twisted inverse image along the diagonal of a proper flat morphism

Let `Y` be a quasi-compact and quasi-separated scheme and `f : X ⟶ Y` a proper, flat morphism of
finite presentation, with diagonal `Δ : X ⟶ X ×_Y X` and projections `pr₁, pr₂`. Let `a`, `c` be
the right adjoints of `Rf_*` and `RΔ_*` on `D_QCoh` ([Stacks, Tag 0A9E]). Equation (0E2Q) of
[Stacks, Tag 0E2P] is

`𝒪_X = c(L pr₁^* ω_{X/Y}^•) = c(L pr₂^* ω_{X/Y}^•)`, where `ω_{X/Y}^• = a(𝒪_Y)`.

The proof is the source's: with `b` the right adjoint for `pr₂` (respectively `pr₁`), flat base
change ([Stacks, Tag 0AAB]) gives `L pr₁^* a(K) ≅ b(Lf^*K)`, and `c ∘ b` is the right adjoint for
`pr₂ ∘ Δ = id`, which is the identity. This holds for every `K`, and `K = 𝒪_Y` is the equation.

## Main results

* `Stacks.Duality.nonempty_twistedInverseImage_diagonal_fst_iso`,
  `Stacks.Duality.nonempty_twistedInverseImage_diagonal_snd_iso`:
  `c(L pr_i^* a(K)) ≅ Lf^*K` for every `K ∈ D_QCoh(𝒪_Y)`.
* `Stacks.Duality.nonempty_twistedInverseImage_diagonal_pullback_relativeDualizingComplex_iso`:
  **equation (0E2Q) of [Stacks, Tag 0E2P]**.

## References

* [Stacks Project, Tag 0E2P](https://stacks.math.columbia.edu/tag/0E2P)
* [Stacks Project, Tag 0E2Q](https://stacks.math.columbia.edu/tag/0E2Q)
* [Stacks Project, Tag 0AAB](https://stacks.math.columbia.edu/tag/0AAB)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-- The twisted inverse images along two equal morphisms are isomorphic. -/
theorem nonempty_twistedInverseImage_congr {X Y : Scheme.{u}} {g g' : X ⟶ Y} (h : g = g')
    (hg : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
    (hg' : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward g').obj K.obj)).IsQuasicoherent)
    [(quasiCoherentDerivedPushforward g hg).IsLeftAdjoint]
    [(quasiCoherentDerivedPushforward g' hg').IsLeftAdjoint] :
    Nonempty (twistedInverseImage g hg ≅ twistedInverseImage g' hg') := by
  subst h
  exact ⟨Iso.refl _⟩

/-- If `p ∘ Δ = id`, then `c(M) ≅ Lf^*K` whenever `M ≅ p^×(Lf^*K)`: the right adjoints for `Δ` and
`p` compose to the one for `p ∘ Δ = id`. -/
private theorem nonempty_twistedInverseImage_diagonal_iso_of_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace ↑(pullback f f)] [QuasiSeparatedSpace ↑(pullback f f)]
    (p : pullback f f ⟶ X) (hp : pullback.diagonal f ≫ p = 𝟙 X) [IsProper p]
    (K : quasiCoherentDerivedCategory Y) (M : quasiCoherentDerivedCategory (pullback f f))
    (e : M ≅ (twistedInverseImage p
      (isQuasicoherent_homology_derivedPushforward_of_qcqs p)).obj
        ((quasiCoherentDerivedPullback' f).obj K)) :
    Nonempty ((twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj M ≅
      (quasiCoherentDerivedPullback' f).obj K) := by
  obtain ⟨e'⟩ := nonempty_twistedInverseImage_congr hp
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f ≫ p))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X))
  exact ⟨(twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).mapIso e ≪≫
    ((twistedInverseImageCompIso (pullback.diagonal f) p
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs p)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs
        (pullback.diagonal f ≫ p))).app _).symm ≪≫
    e'.app _ ≪≫ (twistedInverseImageIdIso X _).app _⟩

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f]
  [Flat f] [LocallyOfFinitePresentation f]

/-- **`c(L pr₁^* a(K)) ≅ Lf^*K`** for a proper flat morphism `f` of finite presentation with
quasi-compact quasi-separated target, `c` the twisted inverse image along the diagonal and `a`
the one along `f`: flat base change ([Stacks, Tag 0AAB]) moves `L pr₁^*` past `a`, and the right
adjoints for `Δ` and `pr₂` compose to the one for `pr₂ ∘ Δ = id`. -/
theorem nonempty_twistedInverseImage_diagonal_fst_iso (K : quasiCoherentDerivedCategory Y) :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)
    haveI := quasiSeparatedSpace_of_quasiSeparated (pullback.snd f f)
    Nonempty ((twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj
        ((quasiCoherentDerivedPullback' (pullback.fst f f)).obj
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            K)) ≅
      (quasiCoherentDerivedPullback' f).obj K) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)
  have := quasiSeparatedSpace_of_quasiSeparated (pullback.snd f f)
  have h0 := isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat
    (IsPullback.of_hasPullback f f) K
  exact nonempty_twistedInverseImage_diagonal_iso_of_iso f (pullback.snd f f)
    (pullback.diagonal_snd f) K _ (@asIso _ _ _ _ _ h0)

/-- **`c(L pr₂^* a(K)) ≅ Lf^*K`**, the companion of
`Stacks.Duality.nonempty_twistedInverseImage_diagonal_fst_iso` with the roles of the two
projections exchanged. -/
theorem nonempty_twistedInverseImage_diagonal_snd_iso (K : quasiCoherentDerivedCategory Y) :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)
    haveI := quasiSeparatedSpace_of_quasiSeparated (pullback.snd f f)
    Nonempty ((twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj
        ((quasiCoherentDerivedPullback' (pullback.snd f f)).obj
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            K)) ≅
      (quasiCoherentDerivedPullback' f).obj K) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)
  have := quasiSeparatedSpace_of_quasiSeparated (pullback.snd f f)
  have h0 := isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat
    (IsPullback.of_hasPullback f f).flip K
  exact nonempty_twistedInverseImage_diagonal_iso_of_iso f (pullback.fst f f)
    (pullback.diagonal_fst f) K _ (@asIso _ _ _ _ _ h0)

/-- **Equation (0E2Q) of [Stacks, Tag 0E2P].** Let `Y` be quasi-compact and quasi-separated and
`f : X ⟶ Y` proper, flat and of finite presentation, with relative dualizing complex
`ω_{X/Y}^• = a(𝒪_Y)` ([Stacks, Remark 0B6S]). Then, `c` being the right adjoint of `RΔ_*` for the
diagonal `Δ : X ⟶ X ×_Y X` ([Stacks, Tag 0A9E]),

`𝒪_X ≅ c(L pr₁^* ω_{X/Y}^•)` and `𝒪_X ≅ c(L pr₂^* ω_{X/Y}^•)`. -/
@[stacks 0E2Q]
theorem nonempty_twistedInverseImage_diagonal_pullback_relativeDualizingComplex_iso :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)
    haveI := quasiSeparatedSpace_of_quasiSeparated (pullback.snd f f)
    Nonempty (DerivedPushforward.derivedStructureSheaf X ≅
      (twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj
        ((quasiCoherentDerivedPullback' (pullback.fst f f)).obj
          (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (DerivedPushforward.derivedStructureSheaf Y)))) ∧
    Nonempty (DerivedPushforward.derivedStructureSheaf X ≅
      (twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj
        ((quasiCoherentDerivedPullback' (pullback.snd f f)).obj
          (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (DerivedPushforward.derivedStructureSheaf Y)))) := by
  obtain ⟨e₁⟩ := nonempty_twistedInverseImage_diagonal_fst_iso f
    (DerivedPushforward.derivedStructureSheaf Y)
  obtain ⟨e₂⟩ := nonempty_twistedInverseImage_diagonal_snd_iso f
    (DerivedPushforward.derivedStructureSheaf Y)
  have eO : (quasiCoherentDerivedPullback' f).obj (DerivedPushforward.derivedStructureSheaf Y) ≅
      DerivedPushforward.derivedStructureSheaf X :=
    ObjectProperty.isoMk _ (derivedPullbackStructureSheafIso f)
  exact ⟨⟨(e₁ ≪≫ eO).symm⟩, ⟨(e₂ ≪≫ eO).symm⟩⟩

end Stacks.Duality
