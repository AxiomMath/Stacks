module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAnyCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCentreEnlargedByDivisorConstructed

/-!
# Enlarging the centre of a blowup by an effective Cartier divisor (Stacks 0867)

Let `S` be a scheme, let `𝔅` be an algebraic space over `S`, let `Z ⊆ 𝔅` be a closed subspace
and let `D ⊆ 𝔅` be an effective Cartier divisor.  Let `Z' = Z + D` be the closed subspace cut
out by the product `𝓘_Z 𝓘_D` of the two defining ideals, Stacks 083U, and let `b : B' ⟶ 𝔅` be
the blowup of `𝔅` in `Z`.  Stacks 0867 says that (1) the blowup of `𝔅` in `Z'` is `b`, and
(2) for a morphism `f : X ⟶ 𝔅` and an `𝒪_X`-module `F` with no nonzero sections supported on
`|f^{-1}D|` the strict transform of `F` is the same for the centre `Z` and for the centre `Z'`.

## Main results

* `AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces_and_strictTransformSheaf_eq` is
  **Stacks 0867**, both parts.
* `AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces_of_isEffectiveCartierDivisor` is
  part (1), and
  `AlgebraicGeometry.Space.exists_iso_blowup_sumClosedSubspaces_of_isEffectiveCartierDivisor`
  is the source's phrasing of it: every blowup of `𝔅` in `Z + D` is isomorphic over `𝔅` to `b`.

## Implementation notes

Part (1) is `AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces` of
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupCentreEnlargedByDivisor.lean` with its two inputs
discharged: `h0809`, that the inverse image of `D` along `b` is an effective Cartier divisor, is
Stacks 085X, `AlgebraicGeometry.Space.IsBlowupAlong.isPullbackDefined_of_isEffectiveCartierDivisor`
of `StacksFrontier/AlgebraicGeometry/Spaces/BlowupAnyCentre.lean`, which holds for every blowup of
every algebraic space; `h083V` is
`AlgebraicGeometry.Space.isPullbackDefined_sumClosedSubspaces_iff`.
Part (2) is `AlgebraicGeometry.Space.strictTransformSheaf_preimage_sumClosedSubspaces` of
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupCentreEnlargedByDivisorConstructed.lean`.

## References

* [Stacks Project, Tag 0867](https://stacks.math.columbia.edu/tag/0867)
* [Stacks Project, Tag 085X](https://stacks.math.columbia.edu/tag/085X)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0867, part (1).** Let `Z ⊆ 𝔅` and `D ⊆ 𝔅` be closed subspaces of an algebraic
space over `S` with `D` an effective Cartier divisor, and let `Z + D` be the closed subspace cut
out by the product of their defining ideals.  A morphism `b : B' ⟶ 𝔅` which is the blowup of
`𝔅` in `Z` is also the blowup of `𝔅` in `Z + D`.

This is `AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces` with its two inputs
discharged: that the inverse image of `D` along `b` is an effective Cartier divisor is Stacks
085X, `AlgebraicGeometry.Space.IsBlowupAlong.isPullbackDefined_of_isEffectiveCartierDivisor`,
and that the inverse image of `Z + D` along a morphism is an effective Cartier divisor exactly
when those of `Z` and of `D` are is
`AlgebraicGeometry.Space.isPullbackDefined_sumClosedSubspaces_iff`. -/
theorem isBlowupAlong_sumClosedSubspaces_of_isEffectiveCartierDivisor
    {𝔅 B' : AlgebraicSpaces B S hS} (Z D : ClosedSubspaces B S hS 𝔅.obj)
    (hD : IsEffectiveCartierDivisor B S hS 𝔅 D)
    {b : B' ⟶ 𝔅} (hb : IsBlowupAlong B S hS Z b) :
    IsBlowupAlong B S hS (sumClosedSubspaces B S hS 𝔅 Z D) b :=
  isBlowupAlong_sumClosedSubspaces B S hS Z D hD hb
    (hb.isPullbackDefined_of_isEffectiveCartierDivisor D hD)
    (fun g => isPullbackDefined_sumClosedSubspaces_iff g Z D)

/-- **Stacks 0867, part (1), in the source's phrasing.**  Every blowup of `𝔅` in `Z + D` is
isomorphic over `𝔅` to a blowup `b : B' ⟶ 𝔅` of `𝔅` in `Z`.

This is `AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces_of_isEffectiveCartierDivisor`
together with the uniqueness of blowups, `AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`. -/
theorem exists_iso_blowup_sumClosedSubspaces_of_isEffectiveCartierDivisor
    {𝔅 B' : AlgebraicSpaces B S hS} (Z D : ClosedSubspaces B S hS 𝔅.obj)
    (hD : IsEffectiveCartierDivisor B S hS 𝔅 D)
    {b : B' ⟶ 𝔅} (hb : IsBlowupAlong B S hS Z b) :
    ∀ (B'' : AlgebraicSpaces B S hS) (b'' : B'' ⟶ 𝔅),
      IsBlowupAlong B S hS (sumClosedSubspaces B S hS 𝔅 Z D) b'' →
        ∃ e : B' ≅ B'', e.hom ≫ b'' = b :=
  fun _ _ hb'' =>
    (isBlowupAlong_sumClosedSubspaces_of_isEffectiveCartierDivisor B S hS Z D hD hb).exists_iso
      hb''

/-- **Stacks 0867.** Let `S` be a scheme, let `𝔅` be an algebraic space over `S`, let
`Z ⊆ 𝔅` be a closed subspace, let `D ⊆ 𝔅` be an effective Cartier divisor, let `Z + D` be the
closed subspace cut out by the product of the ideal sheaves of `Z` and `D`, and let
`b : B' ⟶ 𝔅` be the blowup of `𝔅` in `Z`.

1. `b` is also the blowup of `𝔅` in `Z + D`; so every blowup of `𝔅` in `Z + D` is isomorphic
   to `b` over `𝔅`
   (`AlgebraicGeometry.Space.exists_iso_blowup_sumClosedSubspaces_of_isEffectiveCartierDivisor`).
2. For every morphism of algebraic spaces `f : X ⟶ 𝔅` and every `𝒪_X`-module `F` whose subsheaf
   of sections supported on `|f⁻¹D|` is zero, the strict transform of `F` relative to the
   blowup of `𝔅` in `Z` agrees with the strict transform of `F` relative to the blowup of `𝔅`
   in `Z + D`, which by (1) is the same morphism `b`.

Part (1) is
`AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces_of_isEffectiveCartierDivisor` and
part (2) is `AlgebraicGeometry.Space.strictTransformSheaf_preimage_sumClosedSubspaces`.  The
source asks `F` to be quasi-coherent; the statement holds for every `𝒪_X`-module. -/
@[stacks 0867 "both parts: (1) the blowup of the space in Z is the blowup in Z + D; (2) for \
a module on an algebraic space over the base with no nonzero sections supported on the inverse \
image of D, the strict transforms for the centres Z and Z + D agree; stated for every module, \
quasi-coherent or not"]
theorem isBlowupAlong_sumClosedSubspaces_and_strictTransformSheaf_eq
    {𝔅 B' : AlgebraicSpaces B S hS} (Z D : ClosedSubspaces B S hS 𝔅.obj)
    (hD : IsEffectiveCartierDivisor B S hS 𝔅 D)
    {b : B' ⟶ 𝔅} (hb : IsBlowupAlong B S hS Z b) :
    IsBlowupAlong B S hS (sumClosedSubspaces B S hS 𝔅 Z D) b ∧
      ∀ (X : AlgebraicSpaces B S hS) (f : X ⟶ 𝔅) (F : Modules.{u, u} B S hS X.1 X.2),
        HasNoSectionsSupportedIn B S hS X
            (pointsMap B S hS X.1 f.hom ⁻¹' subspacePointSet B S hS 𝔅.1 D.1) F →
          strictTransformSheaf B S hS f b
              (preimageClosedSubspace b (sumClosedSubspaces B S hS 𝔅 Z D)).1 F =
            strictTransformSheaf B S hS f b (preimageClosedSubspace b Z).1 F :=
  ⟨isBlowupAlong_sumClosedSubspaces_of_isEffectiveCartierDivisor B S hS Z D hD hb,
    fun _ f F hF => strictTransformSheaf_preimage_sumClosedSubspaces B S hS Z D hD hb f F hF⟩

end AlgebraicGeometry.Space

end
