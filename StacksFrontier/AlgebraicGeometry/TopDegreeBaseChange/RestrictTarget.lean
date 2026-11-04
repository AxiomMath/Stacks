module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Top-degree vanishing survives restricting the target to a quasi-compact open

The proof of [Stacks, Tag 0EX3] says, after fixing its standing data, that "we can check (a),
(b) and (c) locally on `Y'` and `Y''`", justified by the claim that if `V ⊆ Y` is a
quasi-compact open then the restricted morphism `f ∣_ V` again satisfies the two hypotheses of
the tag. The finiteness hypotheses are Mathlib's, but the vanishing hypothesis is not: it has to
be transported, and the source's reason is that "any quasi-coherent module on `f⁻¹(V)` is the
restriction of a quasi-coherent module on `X`" ([Stacks, Tag 01PE]) together with the fact that
"formation of higher direct images commutes with restriction to opens" ([Stacks, Tag 01E5]).

This file carries out that transport. It is the step that lets every conclusion of Tag 0EX3 be
proved with an affine target.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.quasiCompact_preimage_ι`: in a top-degree
  base-change situation the inclusion of `f⁻¹(V)` is quasi-compact for a quasi-compact open `V`
  of the target.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.vanishes_above_morphismRestrict`: the vanishing
  hypothesis of `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation` holds for `f ∣_ V`.

## Implementation notes

[Stacks, Tag 01PE] is available as `AlgebraicGeometry.exists_quasicoherent_extension`, which
extends a *morphism* into the restriction of a quasi-coherent module rather than extending a
module outright. Only the extension of the module is needed here, so the ambient module is taken
to be the pushforward of `F` itself — quasi-coherent by [Stacks, Tag 01LC], since the inclusion
of `f⁻¹(V)` is quasi-compact and quasi-separated — and the morphism is the zero morphism. That
avoids having to exhibit quasi-coherence of a zero object, which is not an instance.

Quasi-compactness of the inclusion of `f⁻¹(V)` is retrocompactness of its underlying set
(`AlgebraicGeometry.quasiCompact_iff_isSpectralMap` composed with
`IsRetrocompact_iff_isSpectralMap_subtypeVal`), and on a quasi-compact quasi-separated space
retrocompact open sets are exactly the quasi-compact ones
(`QuasiSeparatedSpace.isRetrocompact_iff_isCompact`). The compactness of `f⁻¹(V)` itself uses
that `f` is quasi-compact, which follows from the situation's own hypotheses: `X` is
quasi-compact and `Y` is quasi-separated.

No `@[stacks 0EX3]` attribute is placed: the tag asserts conclusions (a), (b) and (c) about the
situation, and this is one step inside their common proof.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

/-- The inclusion of the preimage of a quasi-compact open of the target is quasi-compact. The
source of a top-degree base-change situation is quasi-compact and quasi-separated and its
target is quasi-separated, so `f` is quasi-compact and `f⁻¹(V)` is a quasi-compact — hence
retrocompact — open of `X`. -/
theorem quasiCompact_preimage_ι (S : TopDegreeBaseChangeSituation.{u}) (V : S.Y.Opens)
    (hV : IsCompact (V : Set S.Y)) : QuasiCompact (S.f ⁻¹ᵁ V).ι := by
  have := S.isCompact_X
  have := S.isQuasiSeparated_X
  have := S.isQuasiSeparated_Y
  have hretro : IsRetrocompact ((S.f ⁻¹ᵁ V : S.X.Opens) : Set S.X) :=
    (QuasiSeparatedSpace.isRetrocompact_iff_isCompact (S.f ⁻¹ᵁ V).isOpen).mpr
      (S.f.isCompact_preimage hV)
  exact quasiCompact_iff_isSpectralMap.mpr
    (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hretro)

/-- **The "we may work locally on the target" step of [Stacks, Tag 0EX3].** Above the degree `d`
of a top-degree base-change situation, the higher direct images along the restriction `f ∣_ V` of
every quasi-coherent module vanish, for every quasi-compact open `V` of the target.

A quasi-coherent `F` on `f⁻¹(V)` is the restriction of a quasi-coherent `H` on `X` ([Stacks, Tag
01PE]); the situation's hypothesis kills the higher direct image of `H` along `f`; restriction to
`V` is additive, so it kills its restriction; and the restriction comparison of [Stacks, Tag
01E5] identifies that with the higher direct image of `F` along `f ∣_ V`. -/
theorem vanishes_above_morphismRestrict (S : TopDegreeBaseChangeSituation.{u}) (V : S.Y.Opens)
    (hV : IsCompact (V : Set S.Y)) (i : ℤ) (hi : (S.d : ℤ) < i)
    (F : (S.f ⁻¹ᵁ V).toScheme.Modules) (hF : F.IsQuasicoherent) :
    IsZero (((Scheme.Modules.pushforward (S.f ∣_ V)).rightDerivedPlus i).obj F) := by
  have := hF
  have hj : QuasiCompact (S.f ⁻¹ᵁ V).ι := quasiCompact_preimage_ι S V hV
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) :=
    ⟨i.toNat, (Int.toNat_of_nonneg ((Int.natCast_nonneg S.d).trans hi.le)).symm⟩
  obtain ⟨H, hH, -, e, -⟩ := AlgebraicGeometry.exists_quasicoherent_extension
    (S.f ⁻¹ᵁ V).ι ((Scheme.Modules.pushforward (S.f ⁻¹ᵁ V).ι).obj F) F 0
  have h1 : IsZero (((Scheme.Modules.pushforward (S.f ∣_ V)).rightDerivedPlus (n : ℤ)).obj
      ((Scheme.Modules.restrictFunctor (S.f ⁻¹ᵁ V).ι).obj H)) :=
    IsZero.of_iso
      (Functor.map_isZero (Scheme.Modules.restrictFunctor V.ι)
        (S.vanishes_above (n : ℤ) hi H hH))
      (rightDerivedPlusRestrictObjIso S.f V n H)
  exact h1.of_iso
    (((Scheme.Modules.pushforward (S.f ∣_ V)).rightDerivedPlus (n : ℤ)).mapIso e).symm

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
