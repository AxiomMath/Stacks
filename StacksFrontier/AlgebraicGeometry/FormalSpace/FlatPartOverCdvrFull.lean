module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartOverCdvrAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartOverCdvrDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumMapFlat

/-!
# The maximal flat closed formal subspace over a complete discrete valuation ring

**Stacks 0GD8**: let `X` be a locally Noetherian formal algebraic space over a complete discrete
valuation ring `A`. Then there is a closed immersion `X' ⟶ X` of formal algebraic spaces with
`X'` flat over `A` such that every morphism `Y ⟶ X` of locally Noetherian formal algebraic
spaces with `Y` flat over `A` factors through `X'`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_flatPart_of_isLocallyNoetherian_of_isAdicComplete`:
  **Stacks 0GD8**.

## Implementation notes

The proof is the source's. The affine flat parts of the members of a Noetherian atlas of `X` are
`AlgebraicGeometry.FormalSpace.hasAffineFlatParts`; they glue to `X' ⟶ X` by
`AlgebraicGeometry.FormalSpace.flatPartsDescend`, whose atlas by the affine flat parts exhibits
`X'` as locally Noetherian; flatness of `X'` over `A` is condition (3) of the variant of
Stacks 0ANG for locally Noetherian formal algebraic spaces, Remark 0ANI, read on that atlas,
flatness being a local property of arrows of `WAdm^{Noeth}` by Stacks 0GC9. The universal
property comes from the covering of a test object of
`AlgebraicGeometry.FormalSpace.hasFlatAffineCoverOfFlat` and the descent of factorizations of
`AlgebraicGeometry.FormalSpace.factorizationDescendsAlongAffineEtaleCover`.

"`X` is flat over `A`" is flatness of the structure morphism `X ⟶ Spf A` in the sense of
Definition 0GCC, `AlgebraicGeometry.FormalSpace.IsFlat`, and `Spf A` is the formal spectrum of
`A` with its `𝔪`-adic topology, for a quotient system `D` presenting it over `S`. As in the
source, only the existence of a factorization is asserted, not its uniqueness.

## References

* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0GC9](https://stacks.math.columbia.edu/tag/0GC9)
* [Stacks Project, Tag 0GCC](https://stacks.math.columbia.edu/tag/0GCC)
* [Stacks Project, Tag 0GD8](https://stacks.math.columbia.edu/tag/0GD8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (D : QuotientSystem B S hS A)

/-- **Stacks 0GD8.** Let `A` be a complete discrete valuation ring, carrying its `𝔪`-adic
topology, and let `X` be a locally Noetherian formal algebraic space over `S` with a structure
morphism `p : X ⟶ Spf A`. Then there is a closed immersion `ι : X' ⟶ X` of formal algebraic
spaces with `X'` locally Noetherian and flat over `A` such that every morphism `q : Y ⟶ X` with
`Y` a locally Noetherian formal algebraic space flat over `A` factors through `ι`.

The members `Uᵢ` of a Noetherian atlas of `X` carry affine flat parts `Zᵢ ⟶ Uᵢ`, the formal
spectra of the quotients by the `A`-torsion of their presenting rings; these glue to `ι`, the
`Zᵢ` forming an atlas of `X'`, on which flatness of `X'` over `A` is read off by Remark 0ANI.
A test object `Y` is covered by Noetherian affine charts flat over `A` mapping to the `Uᵢ`;
each factors through the corresponding `Zᵢ`, and the factorizations descend along the
covering because `ι` is a monomorphism. -/
@[stacks 0GD8]
theorem exists_flatPart_of_isLocallyNoetherian_of_isAdicComplete
    [IsDomain A] [IsDiscreteValuationRing A]
    (hA : _root_.IsAdic (IsLocalRing.maximalIdeal A))
    (hAc : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    {X : FppfSheaf B S hS} (hX : IsLocallyNoetherian B S hS X) (p : X ⟶ formalSpectrum D) :
    ∃ (X' : FppfSheaf B S hS) (ι : X' ⟶ X),
      IsClosedImmersion B S hS ι ∧ IsLocallyNoetherian B S hS X' ∧
        IsFlat B S hS (ι ≫ p) ∧
        ∀ (Y : FppfSheaf B S hS) (q : Y ⟶ X), IsLocallyNoetherian B S hS Y →
          IsFlat B S hS (q ≫ p) → ∃ r : Y ⟶ X', r ≫ ι = q := by
  classical
  let : IsLinearTopology A A := hA ▸ Ideal.isLinearTopology _
  have hw := TopologicalRing.isWeaklyAdmissible_of_isAdic hA hAc
  have hAadic : TopologicalRing.IsAdic A :=
    ⟨⟨_, TopologicalRing.isIdealOfDefinition_of_isAdic hA, hA⟩, hw.2.2, hw.2.1⟩
  have hXf := hX.1
  obtain ⟨-, I, U, u, hUaffine, hUetale, hUsurj, hUnoeth⟩ := hX
  choose Z z hZaffine hZnoeth hZclosed hZflat hZuniv using fun i ↦
    hasAffineFlatParts B S hS D hAadic p (U i) (u i) (hUaffine i) (hUnoeth i) (hUetale i)
  obtain ⟨X', ι, ζ, hX'fas, hιclosed, hZcover, hζ⟩ :=
    flatPartsDescend B S hS D hXf p U u ⟨hUaffine, hUetale, hUsurj⟩ Z z hZaffine hZnoeth
      hZclosed hZflat hZuniv
  have hX'ln : IsLocallyNoetherian B S hS X' :=
    ⟨hX'fas, I, Z, ζ, hZcover.1, hZcover.2.1, hZcover.2.2, hZnoeth⟩
  have hDaff :=
    isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hAadic D (Iso.refl _)
  refine ⟨X', ι, hιclosed, hX'ln, ?_, fun Y q hY hqflat ↦ ?_⟩
  · rw [isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram]
    refine hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyNoetherian B S hS
      _ TopologicalRing.flat_isLocalNoetherian (TopologicalRing.flat_isomorphismInvariant _) _
      hX'ln (isLocallyNoetherian_formalSpectrum B S hS hAadic D)
      ⟨I, Z, ζ, hZcover, fun i ↦ ⟨formalSpectrum D, 𝟙 _, ζ i ≫ ι ≫ p, hDaff,
        isRepresentableEtale_id B S hS _, by simp, ?_⟩⟩
    have hrw : ζ i ≫ ι ≫ p = z i ≫ u i ≫ p := by rw [← Category.assoc, hζ i, Category.assoc]
    rw [hrw]
    exact (isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS _).mp (hZflat i) _ _ (𝟙 _)
      (𝟙 _) _ (hZaffine i) hDaff (isRepresentableEtale_id B S hS _)
      (isRepresentableEtale_id B S hS _) (by simp)
  · obtain ⟨J, W, w, k, m, hWcover, hWnoeth, hWsq, hWflat⟩ :=
      hasFlatAffineCoverOfFlat B S hS D hXf p U u ⟨hUaffine, hUetale, hUsurj⟩ Y q hY hqflat
    refine factorizationDescendsAlongAffineEtaleCover B S hS ι q hιclosed W w hWcover
      fun j ↦ ?_
    obtain ⟨r, hr⟩ := hZuniv (k j) (W j) (m j) (hWcover.1 j) (hWnoeth j) (hWflat j)
    exact ⟨r ≫ ζ (k j), by rw [Category.assoc, hζ (k j), ← Category.assoc, hr, hWsq j]⟩

end AlgebraicGeometry.FormalSpace

end
