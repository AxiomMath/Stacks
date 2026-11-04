module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SectionsIsoMultiplication
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionPaste

/-!
# Multiplication crosses the tilde comparison of the functions on `W`

The first factor of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeFunctorObjIsoCohomologyUpstairs` rewrites
the second tensor factor of the geometric part of [Stacks, Tag 0EX3] (b) at the functions on an
affine open `W` of `Y''`: the pullback along `(f' ∣_ V) ≫ V.isoSpec` of the tilde module of
`Γ(Y'', W)` becomes the pullback along `f' ∣_ V` of the associated module of the direct image
`(h ∣_ V^W)_* 𝒪_W`. That rewriting is
`…TopDegreeBaseChange.pullbackTildeSectionsIso`, and this file proves that it carries
multiplication by `a : Γ(Y'', W)` to multiplication by the function `a` becomes on `W`.

Nothing here is new mathematics: the comparison is a crossing of two spellings of the pullback
of a tilde module composed with the ring-level comparison of the two readings of the functions
on `W`, and both already have the statement needed — the first its plain naturality
(`…TopDegreeBaseChange.pullbackTildeIsoPullbackAffineTilde_naturality`), the second the
multiplication identity of
`…TopDegreeBaseChange.mulLeftRestrictScalars_comp_sectionsIsoPushforwardUnitSections`.

## Main results

* `…TopDegreeBaseChange.mulLeftRestrictScalars_comp_pullbackTildeSectionsIso`: **the tilde
  comparison of the functions on `W` intertwines multiplication by `a` with multiplication by
  the function `a` becomes on `W`.**

## Implementation notes

*The naturality is used through `CategoryTheory.Iso.inv_comp_eq`.* The naturality
statement is in the conjugated shape `A.inv ≫ u ≫ A.hom = v`, and what the pasting needs is the
square `u ≫ A.hom = A.hom ≫ v`; the two are related by that lemma and nothing else.

*The target of the comparison is spelled with `SheafOfModules.evaluation`.* The isomorphism
`…TopDegreeBaseChange.sectionsIsoPushforwardUnitSections` states its target as a restriction of
scalars, while `pullbackTildeSectionsIso` consumes it at the evaluation of the direct image at
the top open. The two are definitionally equal, so the statement below may be written at either;
it is written at the restriction of scalars, which is the spelling the multiplication identity
is stated at.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable {Y'' : Scheme.{u}} (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (h : Y'' ⟶ S.Y') {V : S.Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens}
  [IsAffine (W : Scheme)] (hWV : W ≤ h ⁻¹ᵁ V)

omit [IsAffine (W : Scheme)] in
/-- **The tilde comparison of the functions on `W` intertwines multiplication.** Multiplication
by `a : Γ(Y'', W)` on the tilde module of `Γ(Y'', W)` over `V`, pulled back along
`(f' ∣_ V) ≫ V.isoSpec`, is carried by
`…TopDegreeBaseChange.pullbackTildeSectionsIso` to multiplication by the function `a` becomes on
`W`, acting on the associated module of `(h ∣_ V^W)_* 𝒪_W` pulled back along `f' ∣_ V`.

The comparison is the crossing of the two spellings of the pullback of a tilde module followed
by the ring-level comparison of the two readings of the functions on `W`; the first contributes
its naturality and the second its multiplication identity. -/
theorem mulLeftRestrictScalars_comp_pullbackTildeSectionsIso (a : Γ(Y'', W)) :
    (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
          ((AlgebraicGeometry.tilde.functor (CommRingCat.of Γ((V : Scheme), ⊤))).map
            (mulLeftRestrictScalars ((h.appLE V W hWV).hom.comp
              (Scheme.Opens.topIso V).hom.hom) a)) ≫
        (pullbackTildeSectionsIso S h hWV).hom =
      (pullbackTildeSectionsIso S h hWV).hom ≫
        (Scheme.Modules.pullback (S.f' ∣_ V)).map
          ((Stacks.Coherent.affineTilde (V : Scheme)).map
            (mulLeftRestrictScalars (h.resLE V W hWV).appTop.hom
              ((Scheme.Opens.topIso W).symm.commRingCatIsoToRingEquiv a))) :=
  comp_two_squares
    ((Iso.inv_comp_eq _).mp
      (pullbackTildeIsoPullbackAffineTilde_naturality S.f' V
        (mulLeftRestrictScalars ((h.appLE V W hWV).hom.comp
          (Scheme.Opens.topIso V).hom.hom) a)))
    (map_comp_square (Scheme.Modules.pullback (S.f' ∣_ V))
      (map_comp_square (Stacks.Coherent.affineTilde (V : Scheme))
        (mulLeftRestrictScalars_comp_sectionsIsoPushforwardUnitSections S h hWV a)))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
