module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowSchemeCompactification
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFpSchemeCoverExistence

/-!
# Stacks 0CQ7

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism of finite type from an algebraic stack to a
quasi-compact quasi-separated algebraic space, and let `V ⊆ Y` be a quasi-compact open over which
`f` is a gerbe. Then one proper compactifiable cover of `f` covers `|V|`: this is the
conclusion of [Stacks, Tag 0CQ7], in the form `HasCompactifiableCover`.

The proof is step (a) of the source's: by [Stacks, Tag 09YC] there is a finite surjective
`π : T ⟶ Y` from a scheme; the base change `𝒳_T ⟶ T` is separated, of finite type and a gerbe
over `π⁻¹(V)` (Stacks 02XD, 06QE), so the scheme case
(`hasCompactifiableCovers_of_isGerbeOver_of_yoneda`) applies, and the covers push forward along
the proper surjective `π` (the initial remark of the proof).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.hasCompactifiableCovers_of_isGerbeOver`:
  [Stacks, Tag 0CQ7], unregistered.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_baseChange_preimage`: the base change of
  `f` along `π` is a gerbe over `π⁻¹(V)`.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A single proper compactifiable cover of `|V|` is the conclusion of [Stacks, Tag 0CQ7] in
the form `HasProperCompactifiableCover`. -/
theorem HasCompactifiableCover.hasProperCompactifiableCover {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} {V : Subfunctor Y}
    (h : HasCompactifiableCover hY f (Set.range (Space.pointsMap B S hS V.toFunctor V.ι))) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c.Zbar, c.Z, c.isAlgebraicSpace_Zbar, c.isAlgebraicSpace_Z, c.j, c.gbar, c.h,
    c.isOpenImmersion_j, c.isProper_gbar, c.isProper_h, c.iso, hc⟩

/-- **The gerbe condition over `V` passes to a base change, over the inverse image of `V`.** If
`𝒳_V ⟶ V` is a gerbe and `π : Y' ⟶ Y` is a morphism of algebraic spaces, then the base change
`𝒳 ×_Y Y' ⟶ Y'` is a gerbe over `π⁻¹(V)`: its restriction to `π⁻¹(V)` is the base change of `f`
along `π⁻¹(V) ⟶ Y` (Stacks 003Q), which factors through `V`. -/
theorem isGerbeOver_baseChange_preimage {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (π : Y' ⟶ Y) (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS
        (Space.isOpenSubspace_preimage B S hS π V hY hY' hV).1 hY' (V.preimage π).ι)
      (twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hY' hY π)
        f).fst).fst := by
  have hV' := Space.isOpenSubspace_preimage B S hS π V hY hY' hV
  let R := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hY' hY π) f
  have hR : IsTwoFibreProduct R := isTwoFibreProduct_twoFibreProductSquare B S hS _ f
  let Q := twoFibreProductSquareAlgebraicStacks B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hV'.1 hY' (V.preimage π).ι) R.fst
  let θ : algebraicSpaceStackMap.{u, w} B S hS hV'.1 hV.1 (V.fromPreimage π) ≫
      algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι ≅
        algebraicSpaceStackMap.{u, w} B S hS hV'.1 hY' (V.preimage π).ι ≫
          algebraicSpaceStackMap.{u, w} B S hS hY' hY π :=
    eqToIso (algebraicSpaceStackMap_comp_eq_of_eq hV'.1 hV.1 hY' hY _ _ _ _
      (Subfunctor.fromPreimage_ι V π))
  exact isGerbeOver_snd_of_isTwoFibreProduct hY f V hV hG _ _ θ (R.pasteFst Q).swap
    (isTwoFibreProduct_swap (isTwoFibreProduct_pasteFst R hR Q
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ R.fst)))

/-- **[Stacks, Tag 0CQ7].** Let `f : 𝒳 ⟶ Y` be a separated 1-morphism of finite type from an
algebraic stack to a quasi-compact quasi-separated algebraic space, and let `V ⊆ Y` be a
quasi-compact open such that `𝒳_V ⟶ V` is a gerbe. Then one proper compactifiable cover of `f`
covers `|V|`.

By [Stacks, Tag 09YC] there is a finite surjective `π : T ⟶ Y` from a scheme, quasi-compact and
quasi-separated since `π` is finite; the base change `𝒳_T ⟶ T` is separated (Stacks 050F), of
finite type (Stacks 06FW) and a gerbe over `π⁻¹(V)`
(`isGerbeOver_baseChange_preimage`), so the scheme case gives a cover of `|π⁻¹(V)|`, which pushes
forward along the proper `π` (`HasCompactifiableCover.of_baseChange`) onto `|V|`. -/
theorem hasCompactifiableCovers_of_isGerbeOver {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hf : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) (V : Subfunctor Y)
    (hV : Space.IsOpenSubspace B S hS V) (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    HasCompactifiableCover hY f (Set.range (Space.pointsMap B S hS V.toFunctor V.ι)) := by
  obtain ⟨T, π, hπs, hπf, -⟩ :=
    (Space.existsFiniteSurjectiveSchemeCover_and_refining B S hS Y hY hYqc hYqs).1
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hπp : Space.IsProper B S hS π :=
    ((Space.isFinite_iff_isAffineHom_and_isProper B S hS hT hY π).1 hπf).2
  have hTqc : Space.IsQuasiCompactSpace B S hS (yoneda.obj T) :=
    Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc hπp.2.1.2
  have hTqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal (yoneda.obj T) :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hT hYqs
      (Space.isQuasiSeparated_of_isSeparated B S hS hπp.1)
  let R := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hY π) f
  have hR : IsTwoFibreProduct R := isTwoFibreProduct_twoFibreProductSquare B S hS _ f
  have h := hasCompactifiableCovers_of_isGerbeOver_of_yoneda T hT hTqc hTqs R.fst
    (isSeparated_baseChange_of_isTwoFibreProduct B S hS f _ R.swap (isTwoFibreProduct_swap hR) hf)
    (isFiniteType_baseChange B S hS f _ R hR hft) (V.preimage π)
    (Space.isOpenSubspace_preimage B S hS π V hY hT hV)
    (Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY hT π hπp.2.1.2 hV hVqc)
    (isGerbeOver_baseChange_preimage hY hT f π V hV hG)
  refine HasCompactifiableCover.of_baseChange hT π hπp h ?_
  rintro _ ⟨v, rfl⟩
  obtain ⟨y, hy⟩ := hπs (Space.pointsMap B S hS _ V.ι v)
  refine ⟨y, ?_, hy⟩
  rw [Space.range_pointsMap_preimage_ι, Set.mem_preimage, hy]
  exact ⟨v, rfl⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
