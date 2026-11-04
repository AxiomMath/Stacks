module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionExistenceAffine
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood

/-!
# Contractions of the fibres of a family of curves spread out étale locally

Let `f : X ⟶ S` be a family of curves, `s ∈ S` a point and `h₀ : X_s ⟶ Y₀` a morphism to a
proper scheme over `κ(s)` with `h₀,*𝒪_{X_s} = 𝒪_{Y₀}` and `R¹h₀,*𝒪_{X_s} = 0`. Then, after
replacing `S` by an elementary étale neighbourhood `(U, u)` of `(S, s)`, the morphism `h₀` is the
fibre in `u` of a morphism `h : X_U ⟶ Y` over `U` to a family of curves `Y ⟶ U`
([Stacks, Tag 0E7C]).

## Main results

* `AlgebraicGeometry.CurveFamily.HasEtaleContraction.comp_etale`: the conclusion is étale local
  on the base.
* `AlgebraicGeometry.CurveFamily.hasEtaleContraction_of_scheme`: the conclusion over any scheme
  of the site, at the canonical point `Spec κ(s) ⟶ S`.
* `AlgebraicGeometry.CurveFamily.exists_elementaryEtaleNeighborhood_contraction`: the
  contraction of `h₀` spread out over an elementary étale neighbourhood of `(S, s)`.

## Implementation notes

A family of curves is `AlgebraicGeometry.CurveFamily` over the big fppf site of `Spec ℤ`. Its
fibre `X_s` over `s` is presented by a scheme `X₀` of the site together with a cartesian square
of algebraic spaces over `Spec κ(s) ⟶ S`; every fibre admits such a presentation, the fibre of a
family of curves over a field being a scheme (Stacks 0ADD). The conditions on `h₀` are that the
comparison `𝒪_{Y₀} ⟶ h₀,*𝒪_{X₀}` is an isomorphism of `𝒪_{Y₀}`-modules and that the first right
derived functor of `h₀,*` on `𝒪_{X₀}`-modules kills `𝒪_{X₀}`. The fibre of `h` in `u` being
isomorphic to `h₀` is expressed by cartesian squares presenting `X₀` and `Y₀` as the fibres of
`X_U` and `Y` over the lift `t : Spec κ(s) ⟶ U` of `u`, under which `h` restricts to `h₀`.

## References

* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 0AE7](https://stacks.math.columbia.edu/tag/0AE7)
* [Stacks Project, Tag 07QY](https://stacks.math.columbia.edu/tag/07QY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The conclusion of Stacks 0E7C is étale local on the base.** If it holds for the base change
`F_V` of `F` along an étale `j : V ⟶ S`, at a lift `s_V` of the point, then it holds for `F`. -/
theorem HasEtaleContraction.comp_etale {V S : Scheme.{u}} {hV : B.Contains V}
    {hS : B.Contains S} (j : V ⟶ S) [Etale j] {F : CurveFamily B hZ}
    {hF : F.base = integerSiteObject B hZ hS} {K : Type u} [Field K]
    {hK : B.Contains (Spec (.of K))} (sV : Spec (.of K) ⟶ V) {X₀ : Scheme.{u}}
    {hX₀ : B.Contains X₀} {pX₀ : X₀ ⟶ Spec (.of K)}
    {ι : yoneda.obj (integerSiteObject B hZ hX₀) ⟶ F.total.obj}
    {ιV : yoneda.obj (integerSiteObject B hZ hX₀) ⟶
      ((F.ofBaseEq hF).pullback (integerSiteMap B hZ hV hS j)).total.obj}
    (hιV : ιV ≫ ((F.ofBaseEq hF).pullbackHom (integerSiteMap B hZ hV hS j)).totalMap.hom = ι)
    {Y₀ : Scheme.{u}} {hY₀ : B.Contains Y₀} {pY₀ : Y₀ ⟶ Spec (.of K)} {h₀ : X₀ ⟶ Y₀}
    (H : HasEtaleContraction hV ((F.ofBaseEq hF).pullback (integerSiteMap B hZ hV hS j)) rfl hK
      sV hX₀ pX₀ ιV hY₀ pY₀ h₀) :
    HasEtaleContraction hS F hF hK (sV ≫ j) hX₀ pX₀ ι hY₀ pY₀ h₀ := by
  obtain ⟨U, hU, e, _, t, ht, G, hG, h, hh, ιU, hιUe, hιU, jj, hjj, hιj⟩ := H
  let FV := (F.ofBaseEq hF).pullback (integerSiteMap B hZ hV hS j)
  have eFV : FV.toBaseYonedaOfEq (rfl : FV.base = integerSiteObject B hZ hV) = FV.toBaseYoneda :=
    toBaseYonedaOfEq_rfl' FV
  have sq1 := F.isPullback_pullbackHom_yoneda hF (integerSiteMap B hZ hU hS (e ≫ j))
  have sqV := F.isPullback_pullbackHom_yoneda hF (integerSiteMap B hZ hV hS j)
  have sqU0 := FV.isPullback_pullbackHom_yoneda rfl (integerSiteMap B hZ hU hV e)
  have sqU : IsPullback ((FV.ofBaseEq rfl).pullbackHom (integerSiteMap B hZ hU hV e)).totalMap.hom
      ((FV.ofBaseEq rfl).pullback (integerSiteMap B hZ hU hV e)).toBaseYoneda FV.toBaseYoneda
      (yoneda.map (integerSiteMap B hZ hU hV e)) := sqU0.of_eq rfl rfl eFV rfl
  have sq2 := (sqU.paste_horiz sqV).of_eq rfl rfl rfl (yoneda_map_integerSiteMap_comp e j)
  let iso := sq1.isoIsPullback _ _ sq2
  have hiso1 := sq1.isoIsPullback_hom_fst _ _ sq2
  have hiso2 := sq1.isoIsPullback_hom_snd _ _ sq2
  have hiso2' : iso.inv ≫
      ((F.ofBaseEq hF).pullback (integerSiteMap B hZ hU hS (e ≫ j))).toBaseYoneda =
      ((FV.ofBaseEq rfl).pullback (integerSiteMap B hZ hU hV e)).toBaseYoneda :=
    (Iso.inv_comp_eq _).mpr hiso2.symm
  have hiso1' : iso.inv ≫ ((F.ofBaseEq hF).pullbackHom
      (integerSiteMap B hZ hU hS (e ≫ j))).totalMap.hom =
      ((FV.ofBaseEq rfl).pullbackHom (integerSiteMap B hZ hU hV e)).totalMap.hom ≫
        ((F.ofBaseEq hF).pullbackHom (integerSiteMap B hZ hV hS j)).totalMap.hom :=
    (Iso.inv_comp_eq _).mpr hiso1.symm
  refine ⟨U, hU, e ≫ j, inferInstance, t, by rw [← Category.assoc, ht], G, hG, iso.hom ≫ h,
    by rw [Category.assoc, hh, hiso2], ιU ≫ iso.inv, ?_, ?_, jj, hjj, ?_⟩
  · rw [Category.assoc, hiso1', reassoc_of% hιUe, hιV]
  · refine hιU.of_iso (Iso.refl _) iso.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      ((Category.comp_id _).trans hiso2'.symm) (by simp)
  · rw [Category.assoc, Iso.inv_hom_id_assoc, hιj]

/-- **Stacks 0E7C over an arbitrary scheme of the site**, in the form
`AlgebraicGeometry.CurveFamily.HasEtaleContraction`, at the canonical point
`Spec κ(s) ⟶ S` of a point `s`. -/
theorem hasEtaleContraction_of_scheme {S : Scheme.{u}}
    (hS : B.Contains S) (F : CurveFamily B hZ) (hF : F.base = integerSiteObject B hZ hS) (s : S)
    {X₀ : Scheme.{u}} (hX₀ : B.Contains X₀) (pX₀ : X₀ ⟶ Spec (.of (S.residueField s)))
    (ι : yoneda.obj (integerSiteObject B hZ hX₀) ⟶ F.total.obj)
    (hι : IsPullback ι (yoneda.map (integerSiteMap B hZ hX₀
        (BigFppfSite.residueField_spec_contains B hS s) pX₀)) (F.toBaseYonedaOfEq hF)
      (yoneda.map (integerSiteMap B hZ (BigFppfSite.residueField_spec_contains B hS s) hS
        (S.fromSpecResidueField s))))
    {Y₀ : Scheme.{u}} (hY₀ : B.Contains Y₀) (pY₀ : Y₀ ⟶ Spec (.of (S.residueField s)))
    [IsProper pY₀] (h₀ : X₀ ⟶ Y₀) (hh₀ : h₀ ≫ pY₀ = pX₀)
    (h0 : IsIso (C := Y₀.Modules) (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR1 : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit X₀.ringCatSheaf))) :
    HasEtaleContraction hS F hF (BigFppfSite.residueField_spec_contains B hS s)
      (S.fromSpecResidueField s) hX₀ pX₀ ι hY₀ pY₀ h₀ := by
  have hiso : ∀ {P X Y Y' Z : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {fst : P ⟶ X}
      {snd : P ⟶ Y'} {f : X ⟶ Z} {g : Y' ⟶ Z}, IsPullback fst snd f g → ∀ e : Y ≅ Y',
        IsPullback fst (snd ≫ e.inv) f (e.hom ≫ g) := fun h e =>
    h.of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp)
  have hκ := BigFppfSite.residueField_spec_contains B hS s
  let jx := S.affineOpenCover.idx s
  let A := S.affineOpenCover.X jx
  let j : Spec A ⟶ S := S.affineOpenCover.f jx
  have : IsOpenImmersion j := S.affineOpenCover.map_prop jx
  obtain ⟨a, ha⟩ := S.affineOpenCover.covers s
  have hA : B.Contains (Spec (.of A)) := (Scheme.size_le_of_isOpenImmersion j).trans_lt hS
  let ρ : CommRingCat.of a.asIdeal.ResidueField ⟶ S.residueField s :=
    (Scheme.Spec.residueFieldIso A a).inv ≫ inv (j.residueFieldMap a) ≫ (S.residueFieldCongr ha).hom
  have : IsIso ρ := by dsimp only [ρ]; infer_instance
  let k : Spec (.of (S.residueField s)) ⟶ Spec (.of a.asIdeal.ResidueField) := Spec.map ρ
  have : IsIso k := by dsimp only [k]; infer_instance
  have hk : (k ≫ Spec.map (CommRingCat.ofHom (algebraMap A a.asIdeal.ResidueField))) ≫ j =
      S.fromSpecResidueField s := by
    have e1 := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField A a
    have e2 := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField j a
    have e3 := S.residueFieldCongr_fromSpecResidueField ha
    show (Spec.map ((Scheme.Spec.residueFieldIso A a).inv ≫ inv (j.residueFieldMap a) ≫
      (S.residueFieldCongr ha).hom) ≫ _) ≫ j = _
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, reassoc_of% e1, ← e2,
      ← Category.assoc, Category.assoc (Spec.map (S.residueFieldCongr ha).hom),
      ← Spec.map_comp (j.residueFieldMap a), IsIso.hom_inv_id, Spec.map_id, Category.comp_id,
      e3]
  have hκp : B.Contains (Spec (.of a.asIdeal.ResidueField)) :=
    BigFppfSite.contains_spec_of_mk_lt_cutoff B ((Cardinal.mk_congr
      (asIso ρ).commRingCatIsoToRingEquiv.toEquiv).trans_lt
        (BigFppfSite.mk_lt_cutoff_of_contains_spec B hκ))
  let FA := (F.ofBaseEq hF).pullback (integerSiteMap B hZ hA hS j)
  have sqA := F.isPullback_pullbackHom_yoneda hF (integerSiteMap B hZ hA hS j)
  have es : yoneda.map (integerSiteMap B hZ hκ hS (S.fromSpecResidueField s)) =
      yoneda.map (integerSiteMap B hZ hκ hA
        (k ≫ Spec.map (CommRingCat.ofHom (algebraMap A a.asIdeal.ResidueField)))) ≫
      yoneda.map (integerSiteMap B hZ hA hS j) :=
    ((yoneda_map_integerSiteMap_comp _ _).trans
      (congrArg (fun f => yoneda.map (integerSiteMap B hZ hκ hS f)) hk)).symm
  obtain ⟨ιA, hιAe, hιA⟩ : ∃ ιA : yoneda.obj (integerSiteObject B hZ hX₀) ⟶ FA.total.obj,
      ιA ≫ ((F.ofBaseEq hF).pullbackHom (integerSiteMap B hZ hA hS j)).totalMap.hom = ι ∧
      IsPullback ιA (yoneda.map (integerSiteMap B hZ hX₀ hκ pX₀)) FA.toBaseYoneda
        (yoneda.map (integerSiteMap B hZ hκ hA
          (k ≫ Spec.map (CommRingCat.ofHom (algebraMap A a.asIdeal.ResidueField))))) :=
    ⟨_, sqA.lift_fst _ _ _, IsPullback.of_right' (hι.of_eq rfl rfl rfl es) sqA⟩
  have eFA : FA.toBaseYonedaOfEq (rfl : FA.base = integerSiteObject B hZ hA) = FA.toBaseYoneda :=
    toBaseYonedaOfEq_rfl' FA
  let Ψ := yoneda.mapIso (integerSiteIso (hZ := hZ) hκ hκp (asIso k))
  have hι₁ : IsPullback ιA (yoneda.map (integerSiteMap B hZ hX₀ hκp (pX₀ ≫ k)))
      (FA.toBaseYonedaOfEq rfl) (yoneda.map (integerSiteMap B hZ hκp hA
        (Spec.map (CommRingCat.ofHom (algebraMap A a.asIdeal.ResidueField))))) :=
    (hiso hιA Ψ.symm).of_eq rfl (yoneda_map_integerSiteMap_comp _ _) eFA.symm
      ((yoneda_map_integerSiteMap_comp _ _).trans (congrArg (fun f =>
        yoneda.map (integerSiteMap B hZ hκp hA f)) (by simp)))
  have H₁ := hasEtaleContraction_of_affine a.asIdeal hA hκp FA rfl hX₀ (pX₀ ≫ k) ιA hι₁ hY₀
    (pY₀ ≫ k) h₀ (by rw [← Category.assoc, hh₀]) h0 hR1
  have H₂ := HasEtaleContraction.baseChange (𝟙 (Spec (.of A))) (𝟙 FA.total.obj)
    (by rw [integerSiteMap_id, CategoryTheory.Functor.map_id, Category.comp_id,
      Category.id_comp]) k (Category.comp_id _) H₁ hX₀ pX₀ ιA (hιA.of_eq rfl rfl eFA.symm rfl)
    (𝟙 X₀) (Category.id_comp _)
    (by rw [integerSiteMap_id, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp])
    hY₀ pY₀ (𝟙 Y₀) (IsPullback.of_horiz_isIso ⟨by simp⟩) h₀ hh₀
    (by rw [Category.comp_id, Category.id_comp])
  have H₃ := HasEtaleContraction.comp_etale j _ hιAe H₂
  rwa [hk] at H₃

/-- A lift `t : Spec κ(s) ⟶ U` of the canonical point `Spec κ(s) ⟶ S` through an étale
`e : U ⟶ S` makes `(U, t(pt))` an elementary étale neighbourhood of `(S, s)` with structure
morphism `e`, at whose point `t` takes its value. -/
theorem exists_elementaryEtaleNeighborhood_of_lift {S U : Scheme.{u}} (s : S) (e : U ⟶ S)
    [Etale e] (t : Spec (.of (S.residueField s)) ⟶ U) (ht : t ≫ e = S.fromSpecResidueField s) :
    ∃ V : EtaleNeighborhood S s, V.IsElementary ∧ ∃ hV : V.scheme = U,
      V.toBase = eqToHom hV ≫ e ∧ ∀ x, t x = (eqToHom hV).base V.point := by
  let pt : Spec (.of (S.residueField s)) := IsLocalRing.closedPoint (S.residueField s)
  have hpt : e (t pt) = s := by
    have h1 := congrArg (fun f : Spec (.of (S.residueField s)) ⟶ S => f pt) ht
    exact h1.trans (Scheme.fromSpecResidueField_apply s pt)
  refine ⟨⟨U, t pt, e, hpt⟩, ?_, rfl, by simp, fun x => ?_⟩
  · rw [EtaleNeighborhood.isElementary_iff]
    show IsIso (e.residueFieldMap (t pt))
    have hω : IsIso ((t ≫ e).residueFieldMap pt) := by
      rw [ht]
      exact isIso_residueFieldMap_fromSpecResidueField S s pt
    rw [Scheme.residueFieldMap_comp] at hω
    have hab := (ConcreteCategory.isIso_iff_bijective _).mp hω
    change Function.Bijective ((t.residueFieldMap pt).hom ∘ (e.residueFieldMap (t pt)).hom) at hab
    have hb : Function.Bijective (t.residueFieldMap pt).hom :=
      ⟨(t.residueFieldMap pt).hom.injective, hab.2.of_comp⟩
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (Function.Bijective.of_comp_iff' hb _).mp hab
  · show t x = t pt
    exact congrArg t (Subsingleton.elim x pt)

/-- Let `F` be a family of curves (Stacks 0D4Z) over a scheme `S` of the site, `s ∈ S`, `X₀` the
fibre of `F` over `s` (the cartesian square `ι` over `Spec κ(s) ⟶ S`; the fibre of a family of
curves over a field is a scheme, Stacks 0ADD), and `h₀ : X₀ ⟶ Y₀` a morphism over `κ(s)` to a
proper scheme `Y₀` over `κ(s)` with `𝒪_{Y₀} = h₀,*𝒪_{X₀}` and `R¹h₀,*𝒪_{X₀} = 0`. Then there are an
elementary étale neighbourhood `(U, u)` of `(S, s)`, with the lift `t : Spec κ(s) ⟶ U` of `s` onto
`u` which identifies `κ(u)` with `κ(s)`, a family of curves `G` over `U` and a morphism `h` over
`U` from the total space of the base change `F_U` to that of `G` whose fibre in `u` is isomorphic
to `h₀`: `X₀` and `Y₀` are the fibres of `F_U` and `G` over `t` (the cartesian squares `ιU` and
`j`, with `ιU` lying over `ι`), and `h` restricts to `h₀`. -/
@[stacks 0E7C]
theorem exists_elementaryEtaleNeighborhood_contraction {S : Scheme.{u}} (hS : B.Contains S)
    (F : CurveFamily B hZ) (hF : F.base = integerSiteObject B hZ hS) (s : S)
    {X₀ : Scheme.{u}} (hX₀ : B.Contains X₀) (pX₀ : X₀ ⟶ Spec (.of (S.residueField s)))
    (ι : yoneda.obj (integerSiteObject B hZ hX₀) ⟶ F.total.obj)
    (hι : IsPullback ι (yoneda.map (integerSiteMap B hZ hX₀
        (BigFppfSite.residueField_spec_contains B hS s) pX₀)) (F.toBaseYonedaOfEq hF)
      (yoneda.map (integerSiteMap B hZ (BigFppfSite.residueField_spec_contains B hS s) hS
        (S.fromSpecResidueField s))))
    {Y₀ : Scheme.{u}} (pY₀ : Y₀ ⟶ Spec (.of (S.residueField s))) [IsProper pY₀]
    (h₀ : X₀ ⟶ Y₀) (hh₀ : h₀ ≫ pY₀ = pX₀)
    (h0 : IsIso (C := Y₀.Modules) (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR1 : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit X₀.ringCatSheaf))) :
    ∃ U : EtaleNeighborhood S s, U.IsElementary ∧
      ∃ (hU : B.Contains U.scheme) (t : Spec (.of (S.residueField s)) ⟶ U.scheme),
        t ≫ U.toBase = S.fromSpecResidueField s ∧ (∀ x, t x = U.point) ∧
        ∃ (G : CurveFamily B hZ) (hG : G.base = integerSiteObject B hZ hU)
          (h : ((F.ofBaseEq hF).pullback (integerSiteMap B hZ hU hS U.toBase)).total.obj ⟶
            G.total.obj),
          h ≫ G.toBaseYonedaOfEq hG =
            ((F.ofBaseEq hF).pullback (integerSiteMap B hZ hU hS U.toBase)).toBaseYoneda ∧
          ∃ ιU : yoneda.obj (integerSiteObject B hZ hX₀) ⟶
              ((F.ofBaseEq hF).pullback (integerSiteMap B hZ hU hS U.toBase)).total.obj,
            ιU ≫ ((F.ofBaseEq hF).pullbackHom
              (integerSiteMap B hZ hU hS U.toBase)).totalMap.hom = ι ∧
            IsPullback ιU (yoneda.map (integerSiteMap B hZ hX₀
                (BigFppfSite.residueField_spec_contains B hS s) pX₀))
              ((F.ofBaseEq hF).pullback (integerSiteMap B hZ hU hS U.toBase)).toBaseYoneda
              (yoneda.map (integerSiteMap B hZ (BigFppfSite.residueField_spec_contains B hS s)
                hU t)) ∧
            ∃ j : yoneda.obj (integerSiteObject B hZ
                (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact pY₀
                  (BigFppfSite.residueField_spec_contains B hS s))) ⟶ G.total.obj,
              IsPullback j (yoneda.map (integerSiteMap B hZ
                  (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact pY₀
                    (BigFppfSite.residueField_spec_contains B hS s))
                  (BigFppfSite.residueField_spec_contains B hS s) pY₀))
                (G.toBaseYonedaOfEq hG)
                (yoneda.map (integerSiteMap B hZ (BigFppfSite.residueField_spec_contains B hS s)
                  hU t)) ∧
              ιU ≫ h = yoneda.map (integerSiteMap B hZ hX₀
                (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact pY₀
                  (BigFppfSite.residueField_spec_contains B hS s)) h₀) ≫ j := by
  obtain ⟨U, hU, e, _, t, ht, G, hG, h, hh, ιU, hιUe, hιU, j, hj, hιj⟩ :=
    hasEtaleContraction_of_scheme hS F hF s hX₀ pX₀ ι hι
      (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact pY₀
        (BigFppfSite.residueField_spec_contains B hS s)) pY₀ h₀ hh₀ h0 hR1
  obtain ⟨V, hVel, hV, hVe, hVt⟩ := exists_elementaryEtaleNeighborhood_of_lift s e t ht
  subst hV
  simp only [eqToHom_refl, Category.id_comp] at hVe
  subst hVe
  exact ⟨V, hVel, hU, t, ht, hVt, G, hG, h, hh, ιU, hιUe, hιU, j, hj, hιj⟩

end CurveFamily

end AlgebraicGeometry

end
