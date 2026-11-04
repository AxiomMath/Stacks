module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullback

/-!
# Ramification in codimension one is invariant under isomorphism

Being unramified, respectively tamely ramified, over `X` in codimension one is a property of a
finite étale cover `f : Y ⟶ U` of an open `j : U ⟶ X`; it only depends on `j` and `f` up to
isomorphism over `X`.

## Main results

* `Stacks.FundamentalGroup.isFieldFactorAt_of_iso`: field factors transport along isomorphisms.
* `Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne.of_iso`,
  `Stacks.FundamentalGroup.IsUnramifiedInCodimensionOne.of_iso`: the two properties transport.

## References

* [Stacks Project, Tag 0EYD](https://stacks.math.columbia.edu/tag/0EYD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.FundamentalGroup

/-- A point outside the range of `j'` is outside the range of `j`. -/
private theorem not_mem_range_of_iso {X U U' : Scheme.{u}} {j : U ⟶ X} {j' : U' ⟶ X}
    (eU : U ≅ U') (hj : eU.hom ≫ j' = j) {x : X} (hx : x ∉ Set.range j'.base) :
    x ∉ Set.range j.base := fun ⟨u, hu⟩ => hx ⟨eU.hom u, by rw [← hu, ← hj]; rfl⟩

variable {X U U' Y Y' : Scheme.{u}} {j : U ⟶ X} {j' : U' ⟶ X} {f : Y ⟶ U} {f' : Y' ⟶ U'}
  (eU : U ≅ U') (eY : Y ≅ Y') (hj : eU.hom ≫ j' = j) (hf : eY.hom ≫ f' = f ≫ eU.hom)
include hj hf

/-- **Field factors transport along isomorphisms over `X`.** -/
theorem isFieldFactorAt_of_iso (x : X) (K L : Type u) [Field K] [Field L]
    [Algebra (X.presheaf.stalk x) K] [Algebra K L] (h : IsFieldFactorAt j' f' x K L) :
    IsFieldFactorAt j f x K L := by
  obtain ⟨w, v, hw, hv, e, he⟩ := h
  refine ⟨w ≫ eU.inv, v ≫ eY.inv, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hj, Iso.inv_hom_id_assoc, hw]
  · have hf' : eY.inv ≫ f = f' ≫ eU.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, hf, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [Category.assoc, hf', ← Category.assoc, hv, Category.assoc]
  · let y' := v (IsLocalRing.closedPoint L)
    let r := eY.inv.residueFieldMap y'
    refine ⟨(asIso r).commRingCatIsoToRingEquiv.trans e, ?_⟩
    calc Spec.map (CommRingCat.ofHom ((asIso r).commRingCatIsoToRingEquiv.trans e).toRingHom) ≫
          Y.fromSpecResidueField (eY.inv y')
        = Spec.map (CommRingCat.ofHom e.toRingHom) ≫ (Spec.map r ≫
            Y.fromSpecResidueField (eY.inv y')) := by
          rw [← Category.assoc, ← Spec.map_comp]
          rfl
      _ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Y'.fromSpecResidueField y' ≫ eY.inv := by
          rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField eY.inv y']
      _ = v ≫ eY.inv := by rw [← Category.assoc, he]

/-- **Tame ramification in codimension one transports along isomorphisms over `X`.** -/
theorem IsTamelyRamifiedInCodimensionOne.of_iso (h : IsTamelyRamifiedInCodimensionOne j f) :
    IsTamelyRamifiedInCodimensionOne j' f' := by
  intro Z hZ hD hV K L _ _ _ _ _ _ _ _ _ hFF
  exact h Z (not_mem_range_of_iso eU hj hZ) hD hV K L
    (isFieldFactorAt_of_iso eU eY hj hf _ K L hFF)

/-- **Unramifiedness in codimension one transports along isomorphisms over `X`.** -/
theorem IsUnramifiedInCodimensionOne.of_iso (h : IsUnramifiedInCodimensionOne j f) :
    IsUnramifiedInCodimensionOne j' f' := by
  intro Z hZ hD hV K L _ _ _ _ _ _ _ _ _ hFF
  exact h Z (not_mem_range_of_iso eU hj hZ) hD hV K L
    (isFieldFactorAt_of_iso eU eY hj hf _ K L hFF)

omit hj hf

/-- **Tame ramification in codimension one pulls back along any pullback square.** Given the
setup of [Stacks, Tag 0EYD] and the statement of that lemma (`h0EYD`), the conclusion holds for
every presentation of the pulled-back cover by pullback squares, not only for the canonical
pullbacks. -/
theorem isTamelyRamifiedInCodimensionOne_of_isPullback
    (h0EYD : ∀ S : CodimensionOnePullbackSetup.{u}, IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      IsTamelyRamifiedInCodimensionOne (Limits.pullback.fst S.g S.U.ι) S.pulledBackCover)
    (S : CodimensionOnePullbackSetup.{u}) (h : IsTamelyRamifiedInCodimensionOne S.U.ι S.f)
    {U'' Y'' : Scheme.{u}} (j'' : U'' ⟶ S.X') (gU : U'' ⟶ S.U)
    (hU : IsPullback gU j'' S.U.ι S.g) (f'' : Y'' ⟶ U'') (gY : Y'' ⟶ S.Y)
    (hY : IsPullback gY f'' S.f gU) :
    IsTamelyRamifiedInCodimensionOne j'' f'' := by
  have hYX : IsPullback gY (f'' ≫ j'') (S.f ≫ S.U.ι) S.g := hY.paste_vert hU
  refine IsTamelyRamifiedInCodimensionOne.of_iso hU.flip.isoPullback.symm hYX.isoPullback.symm
    (IsPullback.isoPullback_inv_fst _) ?_ (h0EYD S h)
  show hYX.isoPullback.inv ≫ f'' = S.pulledBackCover ≫ hU.flip.isoPullback.inv
  rw [← cancel_mono hU.flip.isoPullback.hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst,
      CodimensionOnePullbackSetup.pulledBackCover, Limits.pullback.lift_fst]
    exact hYX.isoPullback_inv_snd
  · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd,
      CodimensionOnePullbackSetup.pulledBackCover, Limits.pullback.lift_snd, ← hY.w,
      ← Category.assoc, hYX.isoPullback_inv_fst]

end Stacks.FundamentalGroup
