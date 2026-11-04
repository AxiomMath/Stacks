module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulRelativeDiagonal

/-!
# The Picard stack over the base inherits the properties of the stack of coherent sheaves

Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` which is flat, of finite presentation
and proper. Stacks 0DMB says that `Pic_{X/B} ⟶ B` is quasi-separated and locally of finite
presentation, and its proof is: `Pic_{X/B}` is an open substack of `Coh_{X/B}` (Stacks 0D03), so
this follows from the same statement for `Coh_{X/B} ⟶ B` (Stacks 0DLZ). The structure morphism
of `Pic_{X/B}` is the natural map `Pic_{X/B} ⟶ Coh_{X/B}` of Stacks 0D03 followed by the
projection of `Coh_{X/B}` to the base, so this file proves the passage from a 1-morphism
`π : Coh_{X/B} ⟶ 𝒵` to the composite `Pic_{X/B} ⟶ Coh_{X/B} ⟶ 𝒵`, for an arbitrary category
fibred in groupoids `𝒵`:

* the relative diagonal of the composite is representable by algebraic spaces, quasi-compact and
  quasi-separated whenever that of `π` is, because the natural map is fully faithful and so its
  diagonal square is 2-cartesian
  (`AlgebraicGeometry.Stack.isTwoFibreProduct_relativeDiagonalCompSquare`);
* the composite is limit preserving on objects (Stacks 06CU) whenever `π` is, because the natural
  map, being representable by open immersions, is (Stacks 06CY), and limit preservation on objects
  is stable under composition (Stacks 06CW).

These are the two halves of the source's proof, for an arbitrary `π`.

## Main results

* `AlgebraicGeometry.Space.isLimitPreservingOnObjects_picardToCoherent`: the natural map
  `Pic_{X/B} ⟶ Coh_{X/B}` is limit preserving on objects.
* `AlgebraicGeometry.Space.isLimitPreservingOnObjects_picardToCoherent_comp`: the limit
  preservation half.
* `AlgebraicGeometry.Space.relativeDiagonal_picardToCoherent_comp`: the quasi-separation half.

## Implementation notes

The base `B` enters only through the projection `π`, which is a parameter; Stacks 0DMB is the
case of the projection `Coh_{X/B} ⟶ 𝒮_B` of Stacks 08LP, with its two properties of
Stacks 0DLZ.

## References

* [Stacks Project, Tag 0DMB](https://stacks.math.columbia.edu/tag/0DMB)
* [Stacks Project, Tag 0D03](https://stacks.math.columbia.edu/tag/0D03)
* [Stacks Project, Tag 0DLZ](https://stacks.math.columbia.edu/tag/0DLZ)
* [Stacks Project, Tag 06CY](https://stacks.math.columbia.edu/tag/06CY)
* [Stacks Project, Tag 06CW](https://stacks.math.columbia.edu/tag/06CW)
* [Stacks Project, Tag 0CBB](https://stacks.math.columbia.edu/tag/0CBB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The natural map `Pic_{X/B} ⟶ Coh_{X/B}` is limit preserving on objects** (Stacks 06CU): it
is representable by algebraic spaces and an open immersion (Stacks 0D03), hence limit preserving
on objects (Stacks 06CY). -/
theorem isLimitPreservingOnObjects_picardToCoherent (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS _ _
      (picardToCoherent D hflat hproper) :=
  Stack.isLimitPreservingOnObjects_of_isOpenImmersion B S hS _
    (isRepresentableByAlgebraicSpaces_and_isOpenImmersion_picardToCoherent D hflat hproper).1
    (isRepresentableByAlgebraicSpaces_and_isOpenImmersion_picardToCoherent D hflat hproper).2

/-- **The limit preservation half of the proof of Stacks 0DMB.** If a 1-morphism
`π : Coh_{X/B} ⟶ 𝒵` is limit preserving on objects (Stacks 06CU), so is its composite with the
natural map `Pic_{X/B} ⟶ Coh_{X/B}` of Stacks 0D03 (Stacks 06CY and 06CW). -/
theorem isLimitPreservingOnObjects_picardToCoherent_comp (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom)
    {𝒵 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS)}
    (π : coherentCFG D ⟶ 𝒵)
    (hπ : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS _ _ π) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS _ _
      (picardToCoherent D hflat hproper ≫ π) :=
  BigFppfOver.isLimitPreservingOnObjects_comp B S hS _ _ _ _ _
    (isLimitPreservingOnObjects_picardToCoherent D hflat hproper) hπ

/-- **The quasi-separation half of the proof of Stacks 0DMB.** If the relative diagonal of a
1-morphism `π : Coh_{X/B} ⟶ 𝒵` is representable by algebraic spaces, quasi-compact and
quasi-separated (the condition of Stacks 04YW for `π` to be quasi-separated), then so is the
relative diagonal of its composite with the natural map `Pic_{X/B} ⟶ Coh_{X/B}` of Stacks 0D03.
The natural map is fully faithful, so the relative diagonal of the composite is a base change of
that of `π` (Stacks 0CBB). -/
theorem relativeDiagonal_picardToCoherent_comp (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom)
    {𝒵 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS)}
    (π : coherentCFG D ⟶ 𝒵)
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ π).hom)
    (hqc : Stack.IsQuasiCompact B S hS (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ π))
    (hqs : Stack.IsQuasiSeparated B S hS
      (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ π)) :
    ∃ _ : Stack.IsRepresentableByAlgebraicSpaces B S hS
        (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _
          (picardToCoherent D hflat hproper ≫ π)).hom,
      Stack.IsQuasiCompact B S hS
          (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _
            (picardToCoherent D hflat hproper ≫ π)) ∧
        Stack.IsQuasiSeparated B S hS
          (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _
            (picardToCoherent D hflat hproper ≫ π)) :=
  have hj : (CatFiberedInGroupoids.homFunctor (picardToCoherent D hflat hproper)).Full ∧
      (CatFiberedInGroupoids.homFunctor (picardToCoherent D hflat hproper)).Faithful :=
    ⟨(picardToCoherentBasedFullyFaithful D hflat hproper).full,
      (picardToCoherentBasedFullyFaithful D hflat hproper).faithful⟩
  ⟨Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_comp.{u, u + 1, u + 1} B S hS _ π hj
      hrep,
    Stack.isQuasiCompact_relativeDiagonal_comp.{u, u + 1, u + 1} B S hS _ π hj hqc,
    Stack.isQuasiSeparated_relativeDiagonal_comp.{u, u + 1, u + 1} B S hS _ π hj hqs⟩

end AlgebraicGeometry.Space

end
