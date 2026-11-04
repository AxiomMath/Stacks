module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowFlatCompactification
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowSchemeFlattening
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowSubstackGerbe

/-!
# Stacks 0CQ7 over a scheme

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism of finite type from an algebraic stack to the
algebraic space represented by a quasi-compact quasi-separated scheme, which is a gerbe over a
quasi-compact open `V ⊆ Y`. Then the conclusion of [Stacks, Tag 0CQ7] holds for `(f, V)`: finitely
many proper compactifiable covers of `f` cover `|V|`.

This is the flattening step (b) of the source's proof: the gerbe `𝒳_V ⟶ V` is flat and locally of
finite presentation (Stacks 06QI), so by [Stacks, Tag 0CQ4] (over a scheme,
`exists_isAdmissibleBlowup_isClosedSubstack_isFlat_isFinitePresentation_of_yoneda`) there are a
`V`-admissible blowup `b : Y' ⟶ Y` and a closed substack `𝒳' ⊆ 𝒳 ×_Y Y'` flat and of finite
presentation over `Y'` containing everything over `b⁻¹(V)`. Over `b⁻¹(V)` the substack is the
whole base change, so `𝒳' ⟶ Y'` is a gerbe over `b⁻¹(V)`, and the flat case
(`hasCompactifiableCovers_of_isFlat`) applies; the covers push forward along the proper `b` and
the proper `𝒳' ⟶ 𝒳`, and `b` is surjective over `V`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.hasCompactifiableCovers_of_isGerbeOver_of_yoneda`:
  [Stacks, Tag 0CQ7] over a quasi-compact quasi-separated scheme, unregistered.
* `AlgebraicGeometry.Stack.AlgebraicStacks.fiber_mem_of_twoFibreProductSquare`: an object of a
  2-fibre product with an open subspace lies over that open.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 0CQ4](https://stacks.math.columbia.edu/tag/0CQ4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An object of the 2-fibre product with a subspace lies over the subspace.** For a subfunctor
`W ⊆ Y` which is an algebraic space and a 1-morphism `g : 𝒳 ⟶ Y`, the `𝒳`-component of an object
of the 2-fibre product of `W ⟶ Y` and `g` is carried by `g` into `W`: the comparison isomorphism
of the object is vertical, hence an equality in the discrete fibres of `Y`. -/
theorem fiber_mem_of_twoFibreProductSquare {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} (W : Subfunctor Y) (hW : IsAlgebraicSpace B S hS W.toFunctor)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (s : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (algebraicSpaceStackMap.{u, w} B S hS hW hY W.ι).hom g.hom).pt.val.obj) :
    (g.hom.hom.obj s.y).fiber.as ∈ W.obj (op (g.hom.hom.obj s.y).base) := by
  have hX : ((algebraicSpaceStackMap.{u, w} B S hS hW hY W.ι).hom.hom.obj s.x).base = s.base :=
    (BasedFunctor.w_obj (algebraicSpaceStackMap.{u, w} B S hS hW hY W.ι).hom.hom s.x).trans s.hx
  have hY' : (g.hom.hom.obj s.y).base = s.base := (BasedFunctor.w_obj g.hom.hom s.y).trans s.hy
  have he := PresheafOfCategories.obj_eq_of_elementOf_eq (P := Y) hX hY'
    ((PresheafOfCategories.elementOf_eq_map (P := Y) hX hY' (𝟙 _) s.iso.hom s.vertical).trans
      (by simp))
  rw [← he]
  exact (s.x.fiber.as).2

/-- **[Stacks, Tag 0CQ7] over a quasi-compact quasi-separated scheme.** Let `f : 𝒳 ⟶ Y` be a
separated 1-morphism of finite type from an algebraic stack to the algebraic space represented by
`T`, with `Y` quasi-compact and quasi-separated, and let `V ⊆ Y` be a quasi-compact open over
which `f` is a gerbe. Then one proper compactifiable cover of `f` covers `|V|`.

The gerbe `𝒳_V ⟶ V` is flat and locally of finite presentation (Stacks 06QI); [Stacks, Tag 0CQ4]
over a scheme gives a `V`-admissible blowup `b : Y' ⟶ Y` and a closed substack `𝒳'` of
`𝒳 ×_Y Y'`, flat and of finite presentation over `Y'` and containing every object over `b⁻¹(V)`.
The 2-fibre product of `b⁻¹(V)` with `𝒳'` is then that with `𝒳 ×_Y Y'`
(`isTwoFibreProduct_substackSquare`), a base change of `𝒳_V ⟶ V` (Stacks 02XD), so `𝒳' ⟶ Y'` is
a gerbe over `b⁻¹(V)` and the flat case applies; the covers push forward along `b` and the proper
`𝒳' ⟶ 𝒳` (Stacks 0CL6), and `b⁻¹(V)` maps onto `V`. -/
theorem hasCompactifiableCovers_of_isGerbeOver_of_yoneda (T : BigFppfOver B S hS)
    (hY : IsAlgebraicSpace B S hS (yoneda.obj T))
    (hYqc : Space.IsQuasiCompactSpace B S hS (yoneda.obj T))
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal (yoneda.obj T))
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS (yoneda.obj T) hY)
    (hf : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) (V : Subfunctor (yoneda.obj T))
    (hV : Space.IsOpenSubspace B S hS V) (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    HasCompactifiableCover hY f (Set.range (Space.pointsMap B S hS V.toFunctor V.ι)) := by
  obtain ⟨hfl, hlfp⟩ := isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver B S hS _ hG
  obtain ⟨Y', b, hb, P, ⟨-, hP, hci⟩, hPV, hPfl⟩ :=
    exists_isAdmissibleBlowup_isClosedSubstack_isFlat_isFinitePresentation_of_yoneda T hY hYqc
      hYqs f hft (isQuasiSeparated_of_isSeparated B S hS hf) V hV hVqc hfl hlfp
  let R := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f
  have hR : IsTwoFibreProduct R := isTwoFibreProduct_twoFibreProductSquare B S hS _ f
  let i := fullSubcategoryInclusion R.pt P hP
  let f' := i ≫ R.fst
  obtain ⟨hf'fl, hf'fp⟩ := hPfl hP
  have hbp : Space.IsProper B S hS b.hom := hb.isProper
  have hY'qc : Space.IsQuasiCompactSpace B S hS Y'.1 :=
    Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc hbp.2.1.2
  have hY'qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y'.1 :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal Y'.2 hYqs
      (Space.isQuasiSeparated_of_isSeparated B S hS hbp.1)
  have hRsep : IsSeparated B S hS R.fst :=
    isSeparated_baseChange_of_isTwoFibreProduct B S hS f _ R.swap (isTwoFibreProduct_swap hR) hf
  have hf'sep : IsSeparated B S hS f' :=
    isSeparated_comp B S hS i R.fst (isSeparated_of_isClosedImmersion B S hS i hci) hRsep
  have hf'ft : IsFiniteType B S hS f' :=
    ⟨isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf'fp.1, hf'fp.2.1⟩
  -- the gerbe condition for `f'` over `b⁻¹(V)`
  let V' := V.preimage b.hom
  have hV' : Space.IsOpenSubspace B S hS V' :=
    Space.isOpenSubspace_preimage B S hS b.hom V hY Y'.2 hV
  have hV'qc : Space.IsQuasiCompactSpace B S hS V'.toFunctor :=
    Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY Y'.2 b.hom hbp.2.1.2 hV hVqc
  let M := substackSquare (algebraicSpaceStackMap.{u, w} B S hS hV'.1 Y'.2 V'.ι) R.fst P hP
  have hM : IsTwoFibreProduct M := isTwoFibreProduct_substackSquare _ _ P hP fun s =>
    hPV s.y (fiber_mem_of_twoFibreProductSquare V' hV'.1 R.fst s)
  have hNp : IsTwoFibreProduct (R.pasteFst M) := isTwoFibreProduct_pasteFst R hR M hM
  let θ : algebraicSpaceStackMap.{u, w} B S hS hV'.1 hV.1 (V.fromPreimage b.hom) ≫
      algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι ≅
        algebraicSpaceStackMap.{u, w} B S hS hV'.1 Y'.2 V'.ι ≫
          algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom :=
    eqToIso (algebraicSpaceStackMap_comp_eq_of_eq hV'.1 hV.1 Y'.2 hY _ _ _ _
      (Subfunctor.fromPreimage_ι V b.hom))
  have hG' : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV'.1 Y'.2 V'.ι) f').fst :=
    isGerbeOver_snd_of_isTwoFibreProduct hY f V hV hG _ _ θ (R.pasteFst M).swap
      (isTwoFibreProduct_swap hNp)
  -- the flat case, pushed forward
  have hcov := hasCompactifiableCovers_of_isFlat Y'.2 hY'qc hY'qs f' hf'sep hf'ft hf'fl hf'fp.1
    V' hV' hV'qc hG'
  have hRsnd : IsProper B S hS R.snd :=
    isProper_baseChange B S hS (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f R.swap
      (isTwoFibreProduct_swap hR)
      ((isProper_algebraicSpaceStackMap_iff.{u, w} B S hS Y'.2 hY b.hom).2 hbp)
  exact hcov.of_proper b.hom hbp (i ≫ R.snd)
    (isProper_comp B S hS i R.snd (isProper_of_isClosedImmersion B S hS i hci) hRsnd)
    (α_ _ _ _ ≪≫ whiskerLeftIso i R.iso.symm ≪≫ (α_ _ _ _).symm)
    (Space.range_pointsMap_subset_image_of_isAdmissibleBlowup (X := ⟨yoneda.obj T, hY⟩) ⟨V, hV⟩ hb)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
