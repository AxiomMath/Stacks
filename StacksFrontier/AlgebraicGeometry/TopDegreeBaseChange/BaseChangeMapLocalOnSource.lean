module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapDegenerate

/-!
# Conclusion (c) of [Stacks, Tag 0EX3] is local on `Y'`

Invertibility of the canonical map

> `γ : h^* R^d f'_* F' ⟶ R^d f''_* (h')^* F'`

of [Stacks, Tag 0EX3] is local on `Y'`: given an open covering `W` of `S.Y'`, it suffices that
the restriction of `γ` to each preimage `h ⁻¹ᵁ (W i)` be invertible.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isOpenCover_preimage`: the preimage of an open
  covering under a morphism of schemes is an open covering.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange`
  `.isIso_topDirectImageBaseChangeMap_of_isIso_restrict_source`: conclusion (c) is local on `Y'`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

variable {X'' Y'' : Scheme.{u}}

/-- For a morphism of schemes `f : Y ⟶ X` and an open covering `U` of `X`, the family
`fun i => f ⁻¹ᵁ U i` is an open covering of `Y`. -/
theorem isOpenCover_preimage {X Y : Scheme.{u}} (f : Y ⟶ X) {ι : Type*} {U : ι → X.Opens}
    (hU : IsOpenCover U) : IsOpenCover fun i => f ⁻¹ᵁ U i := by
  refine Opens.ext (Set.eq_univ_of_forall fun y => ?_)
  obtain ⟨i, hi⟩ := hU.exists_mem (f y)
  simpa only [Opens.coe_iSup, Set.mem_iUnion] using ⟨i, hi⟩

/-- Conclusion (c) of [Stacks, Tag 0EX3] is local on `Y'`: given an open covering `W` of `S.Y'`,
if the restriction of the canonical map to the preimage `h ⁻¹ᵁ (W i)` of each member is
invertible, then the canonical map is invertible. -/
theorem isIso_topDirectImageBaseChangeMap_of_isIso_restrict_source
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom)
    {I : Type*} (W : I → S.Y'.Opens) (hW : IsOpenCover W)
    (hiso : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ (W i)).ι).map
      (topDirectImageBaseChangeMap S F' h' f'' h sq))) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h sq) :=
  isIso_topDirectImageBaseChangeMap_of_isIso_restrict S F' h' f'' h sq
    (fun i => h ⁻¹ᵁ (W i)) (isOpenCover_preimage h hW) hiso

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
