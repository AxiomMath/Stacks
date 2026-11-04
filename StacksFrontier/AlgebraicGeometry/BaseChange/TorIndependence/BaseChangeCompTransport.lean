module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCompAssembly
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChart

/-!
# Transporting the base-change composition along an isomorphism of squares

Let `Q₁` and `Q₂` be two commutative squares of schemes and let `Q₂ ⟶ Q₁` be a morphism of
squares all four of whose components are isomorphisms.  For a datum `(E, E', ψ)` on `Q₁`, the
composition `Lg^*Rf_*E ⟶ Rf'_*E'` of `Q₁` is invertible as soon as the composition of `Q₂` at the
pulled-back datum is.  Applied to an affine open `U` of `X` over affine opens `V ⊆ S`,
`V' ⊆ g^{-1}(V)`, and to the square of spectra of the chart on `(U, V, V')`, this reduces the
goodness of `U` to the square of spectra.

## Main results

* `Stacks.Cohomology.BaseChangeCover.isIso_comp_of_isIso_comp_of_iso`: the transport.
* `Stacks.Cohomology.BaseChangeCover.repGood_of_chart`: goodness of an affine open from the
  square of spectra of its chart.

## References

* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChangeCover

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Derived pullback along an isomorphism of schemes reflects isomorphisms. -/
theorem isIso_of_isIso_derivedPullback_map {A B : Scheme.{u}} (h : A ⟶ B) [IsIso h]
    {E F : DerivedCategory (SheafOfModules.{u} (structureSheafRing B.toSheafedSpace))}
    (x : E ⟶ F) (hx : IsIso ((derivedPullback h.toLRSHom.toShHom).map x)) : IsIso x := by
  let e : A.toSheafedSpace ≅ B.toSheafedSpace :=
    (Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace).mapIso (asIso h)
  exact @isIso_of_reflects_iso _ _ _ _ _ _ x
    (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackEquivalence e).functor hx _

/-- The derived base-change map of a square whose horizontal sides are isomorphisms is
invertible. -/
private theorem isIso_derivedBaseChangeMap_of_iso_horiz {A B C D : Scheme.{u}} (i : A ⟶ B)
    (a : A ⟶ C) (b : B ⟶ D) (k : C ⟶ D) [IsIso i] [IsIso k] (w : i ≫ b = a ≫ k)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing B.toSheafedSpace))) :
    IsIso (derivedBaseChangeMap i.toLRSHom.toShHom a.toLRSHom.toShHom b.toLRSHom.toShHom
      k.toLRSHom.toShHom (comp_toShHom_of_comm w) E) :=
  isIso_derivedBaseChangeMap_of_isOpenImmersions _ _ _ _
    (isPullback_toShHom_of_isOpenImmersion i a b k (IsPullback.of_horiz_isIso ⟨w⟩)) E

/-- **Transport of the base-change composition along an isomorphism of squares.** -/
theorem isIso_comp_of_isIso_comp_of_iso {Z₁ Z₁' T₁ T₁' Z₂ Z₂' T₂ T₂' : Scheme.{u}}
    (gZ₁ : Z₁' ⟶ Z₁) (fZ₁ : Z₁ ⟶ T₁) (fZ₁' : Z₁' ⟶ T₁') (gT₁ : T₁' ⟶ T₁)
    (hq₁ : gZ₁ ≫ fZ₁ = fZ₁' ≫ gT₁)
    (gZ₂ : Z₂' ⟶ Z₂) (fZ₂ : Z₂ ⟶ T₂) (fZ₂' : Z₂' ⟶ T₂') (gT₂ : T₂' ⟶ T₂)
    (hq₂ : gZ₂ ≫ fZ₂ = fZ₂' ≫ gT₂)
    (iZ : Z₂ ⟶ Z₁) (iZ' : Z₂' ⟶ Z₁') (iT : T₂ ⟶ T₁) (iT' : T₂' ⟶ T₁')
    [IsIso iZ] [IsIso iZ'] [IsIso iT] [IsIso iT']
    (hg : gZ₂ ≫ iZ = iZ' ≫ gZ₁) (h₁ : iZ ≫ fZ₁ = fZ₂ ≫ iT) (h₂ : iZ' ≫ fZ₁' = fZ₂' ≫ iT')
    (hT : gT₂ ≫ iT = iT' ≫ gT₁)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z₁.toSheafedSpace)))
    (E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z₁'.toSheafedSpace)))
    (ψ : (derivedPullback gZ₁.toLRSHom.toShHom).obj E ⟶ E')
    (h : IsIso (derivedBaseChangeMap gZ₂.toLRSHom.toShHom fZ₂'.toLRSHom.toShHom
        fZ₂.toLRSHom.toShHom gT₂.toLRSHom.toShHom (comp_toShHom_of_comm hq₂)
        ((derivedPullback iZ.toLRSHom.toShHom).obj E) ≫
      (derivedPushforward fZ₂'.toLRSHom.toShHom).map
        (pullDatum gZ₂.toLRSHom.toShHom iZ'.toLRSHom.toShHom iZ.toLRSHom.toShHom
          gZ₁.toLRSHom.toShHom (comp_toShHom_of_comm hg) E E' ψ))) :
    IsIso (derivedBaseChangeMap gZ₁.toLRSHom.toShHom fZ₁'.toLRSHom.toShHom fZ₁.toLRSHom.toShHom
        gT₁.toLRSHom.toShHom (comp_toShHom_of_comm hq₁) E ≫
      (derivedPushforward fZ₁'.toLRSHom.toShHom).map ψ) := by
  have := isIso_derivedBaseChangeMap_of_iso_horiz iZ fZ₂ fZ₁ iT h₁ E
  have := isIso_derivedBaseChangeMap_of_iso_horiz iZ' fZ₂' fZ₁' iT' h₂ E'
  exact isIso_of_isIso_derivedPullback_map iT' _
    (isIso_derivedPullback_map_comp_of_chart gZ₁.toLRSHom.toShHom fZ₁'.toLRSHom.toShHom
      fZ₁.toLRSHom.toShHom gT₁.toLRSHom.toShHom (comp_toShHom_of_comm hq₁) iZ.toLRSHom.toShHom
      iZ'.toLRSHom.toShHom fZ₂.toLRSHom.toShHom fZ₂'.toLRSHom.toShHom gZ₂.toLRSHom.toShHom
      gT₂.toLRSHom.toShHom iT.toLRSHom.toShHom iT'.toLRSHom.toShHom (comp_toShHom_of_comm hg)
      (comp_toShHom_of_comm hq₂) (comp_toShHom_of_comm h₁) (comp_toShHom_of_comm h₂)
      (comp_toShHom_of_comm hT) E E' ψ h)

/-- The composition attached to a pulled-back datum depends on the two morphisms it is pulled
back along only up to equality. -/
theorem isIso_comp_pullDatum_congr {W W' X X' T T' : Scheme.{u}} (gW : W' ⟶ W) (fW : W ⟶ T)
    (fW' : W' ⟶ T') (gT : T' ⟶ T) (hq : gW ≫ fW = fW' ≫ gT) (g' : X' ⟶ X) {e₁ e₂ : W ⟶ X}
    {e₁' e₂' : W' ⟶ X'} (h : e₁ = e₂) (h' : e₁' = e₂') (w₁ : gW ≫ e₁ = e₁' ≫ g')
    (w₂ : gW ≫ e₂ = e₂' ≫ g')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace)))
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K') :
    IsIso (derivedBaseChangeMap gW.toLRSHom.toShHom fW'.toLRSHom.toShHom fW.toLRSHom.toShHom
        gT.toLRSHom.toShHom (comp_toShHom_of_comm hq)
          ((derivedPullback e₁.toLRSHom.toShHom).obj K) ≫
      (derivedPushforward fW'.toLRSHom.toShHom).map
        (pullDatum gW.toLRSHom.toShHom e₁'.toLRSHom.toShHom e₁.toLRSHom.toShHom
          g'.toLRSHom.toShHom (comp_toShHom_of_comm w₁) K K' φ)) ↔
    IsIso (derivedBaseChangeMap gW.toLRSHom.toShHom fW'.toLRSHom.toShHom fW.toLRSHom.toShHom
        gT.toLRSHom.toShHom (comp_toShHom_of_comm hq)
          ((derivedPullback e₂.toLRSHom.toShHom).obj K) ≫
      (derivedPushforward fW'.toLRSHom.toShHom).map
        (pullDatum gW.toLRSHom.toShHom e₂'.toLRSHom.toShHom e₂.toLRSHom.toShHom
          g'.toLRSHom.toShHom (comp_toShHom_of_comm w₂) K K' φ)) := by
  subst h h'
  rfl

/-- The range of the canonical map from the spectrum of an affine open is the range of any open
immersion with image that open. -/
private theorem range_fromSpec_eq_of_range_eq {Y Z : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W)
    {j : Z ⟶ Y} [IsOpenImmersion j] (hr : j.opensRange = W) :
    Set.range hW.fromSpec = Set.range j := by
  rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, hr]
  exact congrArg SetLike.coe hW.opensRange_fromSpec

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **Goodness of an affine open from its chart.**  Let `U ⊆ X`, `V ⊆ S`, `V' ⊆ g^{-1}(V)` be
affine opens with `U ⊆ f^{-1}(V)`.  If the composition of the square of spectra of the chart on
`(U, V, V')` is invertible at the datum pulled back along the chart, then `U` is good. -/
theorem repGood_of_chart (sq : IsPullback g' f' f g) (V : S.Opens) (V' : S'.Opens)
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ g ⁻¹ᵁ V) (U : X.Opens)
    (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace)))
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (H : let ch := BaseChangeChart.ofAffineOpens sq U V V' hU hV hV' hUV hle
      IsIso (derivedBaseChangeMap (Spec.map ch.c).toLRSHom.toShHom
          (Spec.map ch.d).toLRSHom.toShHom (Spec.map ch.a).toLRSHom.toShHom
          (Spec.map ch.b).toLRSHom.toShHom
          (comp_toShHom_of_comm (isPullback_SpecMap_of_isPushout _ _ _ _ ch.isPushout).w)
          ((derivedPullback ch.incU.toLRSHom.toShHom).obj K) ≫
        (derivedPushforward (Spec.map ch.d).toLRSHom.toShHom).map
          (pullDatum (Spec.map ch.c).toLRSHom.toShHom ch.incU'.toLRSHom.toShHom
            ch.incU.toLRSHom.toShHom g'.toLRSHom.toShHom (comp_toShHom_of_comm ch.wU'U.symm)
            K K' φ))) :
    repGood% f f' g' V.ι V'.ι (g.resLE V V' hle) K K' φ U := by
  intro Z Z' j j' fZ fZ' gZ _ _ hr hf hf' hg hq
  let ch := BaseChangeChart.ofAffineOpens sq U V V' hU hV hV' hUV hle
  have := ch.isOpenImmersion_incU
  have := ch.isOpenImmersion_incV
  have := ch.isOpenImmersion_incV'
  have hsp := isPullback_SpecMap_of_isPushout _ _ _ _ ch.isPushout
  have eU : Set.range ch.incU = Set.range j := range_fromSpec_eq_of_range_eq hU hr
  have eV : Set.range ch.incV = Set.range V.ι := range_fromSpec_eq_of_range_eq hV V.opensRange_ι
  have eV' : Set.range ch.incV' = Set.range V'.ι :=
    range_fromSpec_eq_of_range_eq hV' V'.opensRange_ι
  let iZ := (IsOpenImmersion.isoOfRangeEq ch.incU j eU).hom
  let iT := (IsOpenImmersion.isoOfRangeEq ch.incV V.ι eV).hom
  let iT' := (IsOpenImmersion.isoOfRangeEq ch.incV' V'.ι eV').hom
  have hiZ : iZ ≫ j = ch.incU := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hiT : iT ≫ V.ι = ch.incV := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hiT' : iT' ≫ V'.ι = ch.incV' := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h₁ : iZ ≫ fZ = Spec.map ch.a ≫ iT := by
    rw [← cancel_mono V.ι, Category.assoc, hf, ← Category.assoc, hiZ, Category.assoc, hiT, ch.wU]
  have hT : Spec.map ch.b ≫ iT = iT' ≫ g.resLE V V' hle := by
    rw [← cancel_mono V.ι, Category.assoc, hiT, Category.assoc, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, hiT', ch.wV']
  have hpb : IsPullback (Spec.map ch.c ≫ iZ) (Spec.map ch.d ≫ iT') fZ (g.resLE V V' hle) :=
    hsp.of_iso (Iso.refl _) (IsOpenImmersion.isoOfRangeEq ch.incU j eU)
      (IsOpenImmersion.isoOfRangeEq ch.incV' V'.ι eV') (IsOpenImmersion.isoOfRangeEq ch.incV V.ι eV)
      (Category.id_comp _).symm (Category.id_comp _).symm h₁.symm hT
  let iZ' := (hpb.isoIsPullback _ _ hq).hom
  have hg₂ : Spec.map ch.c ≫ iZ = iZ' ≫ gZ := (hpb.isoIsPullback_hom_fst _ _ hq).symm
  have h₂ : iZ' ≫ fZ' = Spec.map ch.d ≫ iT' := hpb.isoIsPullback_hom_snd _ _ hq
  have hiZ' : iZ' ≫ j' = ch.incU' := by
    apply sq.hom_ext
    · rw [Category.assoc, ← hg, ← Category.assoc, ← hg₂, Category.assoc, hiZ, ch.wU'U]
    · rw [Category.assoc, ← hf', ← Category.assoc, h₂, Category.assoc, hiT', ch.wU'V']
  refine isIso_comp_of_isIso_comp_of_iso gZ fZ fZ' (g.resLE V V' hle) hq.w (Spec.map ch.c)
    (Spec.map ch.a) (Spec.map ch.d) (Spec.map ch.b) hsp.w iZ iZ' iT iT' hg₂ h₁ h₂ hT _ _ _ ?_
  refine (isIso_bc_iff_of_iso _ _ _ _ _ _ _ _ _
    (pullDatum_comp (Spec.map ch.c).toLRSHom.toShHom iZ'.toLRSHom.toShHom
      iZ.toLRSHom.toShHom gZ.toLRSHom.toShHom j'.toLRSHom.toShHom j.toLRSHom.toShHom
      g'.toLRSHom.toShHom (comp_toShHom_of_comm hg₂) (comp_toShHom_of_comm hg) K K' φ)).2 ?_
  exact (isIso_comp_pullDatum_congr (Spec.map ch.c) (Spec.map ch.a) (Spec.map ch.d)
    (Spec.map ch.b) hsp.w g' hiZ.symm hiZ'.symm ch.wU'U.symm
    (by rw [← Category.assoc, hg₂, Category.assoc, hg, Category.assoc]) K K' φ).1 H

end Stacks.Cohomology.BaseChangeCover
