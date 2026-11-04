module

public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilizationFibreIso
public import StacksFrontier.AlgebraicGeometry.Quot.StableLocusOpenFibreAmple
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureContractionScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedHigherDirectImageAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Terminal

/-!
# Condition (2) of Stacks 0E8A from condition (1) and stability of the target

Let `c : X ⟶ Y` be a morphism over `S` from a prestable family of curves to a stable family of
curves satisfying condition (1) of Stacks 0E8A (`𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`, universally).
Then `c` satisfies condition (2): at every field-valued point `p` of `S` the fibre
`c_p : X_p ⟶ Y_p` satisfies the three conditions of Stacks 0E7Q characterizing the contraction of
rational tails and bridges. Indeed `Y_p` is proper of dimension one with at-worst-nodal
singularities and `H⁰(Y_p, 𝒪) = k` (`Y` being prestable), condition (1) at `p` is condition (2)
of Stacks 0E7Q, and `ω_{Y_p}` is ample because `Y_p` is stable (Stacks 0E3P, in the form
`AlgebraicGeometry.hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField`).
This is the step "part (2) holds by the uniqueness in Algebraic Curves, Lemma 0E7Q" of the proof
of Stacks 0E8A.

## Main results

* `AlgebraicGeometry.CurveFamily.isStructureContraction_schemeSpaceMap_iff_unit`: for a morphism
  of schemes of the site, the conditions `𝒪 = c_*𝒪` and `R¹c_*𝒪 = 0` read on the algebraic
  spaces or on the schemes.
* `AlgebraicGeometry.CurveFamily.hasStableContractionFibres_of_isUniversalStructureContraction`:
  condition (2) from condition (1) for a contraction onto a stable family.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **`𝒪 = c_*𝒪` and `R¹c_*𝒪 = 0` for a morphism of schemes of the site**, read on the algebraic
spaces they represent or on the schemes themselves. -/
theorem isStructureContraction_schemeSpaceMap_iff_unit {T' T : BigFppfOver B integerBase hZ}
    (g : T' ⟶ T) [QuasiCompact ((𝒯).map g)] [IsSeparated ((𝒯).map g)] :
    Space.IsStructureContraction B integerBase hZ (schemeSpaceMap g) ↔
      IsIso (SheafOfModules.unitToPushforwardObjUnit ((𝒯).map g).toRingCatSheafHom) ∧
        IsZero (((Scheme.Modules.pushforward ((𝒯).map g)).rightDerived 1).obj
          (SheafOfModules.unit ((𝒯).obj T').ringCatSheaf)) := by
  rw [Space.isStructureContraction_schemeSpaceMap_iff g
    (fun g hqc hsep F hF k =>
      Space.nonempty_rightDerived_modulePushforward_representedAssociatedModule_of_isSeparated
        B integerBase hZ g hqc hsep F hF k)]
  refine and_congr Iff.rfl ?_
  let := HasDerivedCategory.standard ((𝒯).obj T').Modules
  let := HasDerivedCategory.standard ((𝒯).obj T).Modules
  exact Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    (Scheme.Modules.pushforward ((𝒯).map g)) (m := (1 : ℤ)) (n := 1) rfl _

/-- Two presentations of the same cartesian square by representables differ by an isomorphism of
the representing schemes compatible with both projections. -/
private theorem exists_iso_of_isPullback_yoneda {C : Type*} [Category C] {V V' W : C}
    {Z Z' : Cᵒᵖ ⥤ Type _} {q : yoneda.obj V ⟶ Z} {q' : yoneda.obj V' ⟶ Z} {v : V ⟶ W}
    {v' : V' ⟶ W} {f : Z ⟶ Z'} {g : yoneda.obj W ⟶ Z'}
    (hq : IsPullback q (yoneda.map v) f g) (hq' : IsPullback q' (yoneda.map v') f g) :
    ∃ e : V' ≅ V, yoneda.map e.hom ≫ q = q' ∧ e.hom ≫ v = v' := by
  let eY : yoneda.obj V' ≅ yoneda.obj V := hq'.isoIsPullback _ _ hq
  have hey : yoneda.map (Yoneda.fullyFaithful.preimageIso eY).hom = eY.hom :=
    Yoneda.fullyFaithful.map_preimage _
  refine ⟨Yoneda.fullyFaithful.preimageIso eY, ?_, yoneda.map_injective ?_⟩
  · rw [hey]; exact hq'.isoIsPullback_hom_fst _ _ hq
  · rw [Functor.map_comp, hey]; exact hq'.isoIsPullback_hom_snd _ _ hq

/-- A morphism to `Spec k` with `k`-valued global sections is bijective on global sections. -/
private theorem bijective_appTop_of_isIso_comp {k : Type u} [Field k] {V : Scheme.{u}}
    (v : V ⟶ Spec (.of k)) (h : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ v.appTop)) :
    Function.Bijective v.appTop := by
  have : IsIso v.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv v.appTop
  exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

/-- The fibre of a stable family of curves over a field-valued point of a base equal to its own
has a presentation on which it is a stable curve. -/
theorem exists_isPullback_hasGenusTwoNoRationalTailNoRationalBridge_of_base_eq
    {Y : CurveFamily B hZ} (hY : IsStableCurveFamily B hZ Y) {Q : BigFppfOver B integerBase hZ}
    (hb : Y.base = Q) (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace Q).obj) :
    ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
      (q : yoneda.obj V ⟶ Y.total.obj),
      IsPullback q (yoneda.map v) (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)).hom
          (yonedaEquiv.symm p.value) ∧
        HasGenusTwoNoRationalTailNoRationalBridge p.carrier ((𝒯).map v) := by
  subst hb
  simpa only [eqToHom_refl, Category.comp_id] using hY.2 p

/-- `AlgebraicGeometry.CurveFamily.fibre_standing_of_isPrestableCurveFamily` over a base equal to
that of the family. -/
theorem fibre_standing_of_isPrestableCurveFamily_of_base_eq {Y : CurveFamily B hZ}
    (hY : IsPrestableCurveFamily B hZ Y) {Q : BigFppfOver B integerBase hZ} (hb : Y.base = Q)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace Q).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ Y.total.obj}
    (hsq : IsPullback q (yoneda.map v) (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)).hom
      (yonedaEquiv.symm p.value)) :
    IsProper ((𝒯).map v) ∧
      IsIso ((Scheme.ΓSpecIso (.of p.carrier)).inv ≫ ((𝒯).map v).appTop) ∧
      topologicalKrullDim ((𝒯).obj V) = 1 ∧
      (letI : ((𝒯).obj V).Over (Spec (.of p.carrier)) := ⟨(𝒯).map v⟩;
        Stacks.Curves.HasAtWorstNodalSingularities p.carrier ((𝒯).obj V)) := by
  subst hb
  exact fibre_standing_of_isPrestableCurveFamily hY
    (by simpa only [eqToHom_refl, Category.comp_id] using hsq)

/-- **The stability of a fibre does not depend on its presentation.** For a prestable family of
curves and two schemes `V`, `V'` presenting its fibre over a field-valued point `p`, if `V` has
genus at least two and neither a rational tail nor a rational bridge, so has `V'`: the two are
isomorphic over `p`, and the condition is the ampleness of the dualizing sheaf (Stacks 0E3P and
its converse), which is invariant under isomorphism. -/
theorem hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback_of_isPullback
    {Y : CurveFamily B hZ} (hY : IsPrestableCurveFamily B hZ Y) {Q : BigFppfOver B integerBase hZ}
    (hb : Y.base = Q) {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace Q).obj}
    {V V' : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {v' : V' ⟶ p.siteObject}
    {q : yoneda.obj V ⟶ Y.total.obj} {q' : yoneda.obj V' ⟶ Y.total.obj}
    (hq : IsPullback q (yoneda.map v) (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)).hom
      (yonedaEquiv.symm p.value))
    (hq' : IsPullback q' (yoneda.map v') (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)).hom
      (yonedaEquiv.symm p.value))
    (h : HasGenusTwoNoRationalTailNoRationalBridge p.carrier ((𝒯).map v)) :
    HasGenusTwoNoRationalTailNoRationalBridge p.carrier ((𝒯).map v') := by
  obtain ⟨hprop, hH0, hdim, hnodal⟩ := fibre_standing_of_isPrestableCurveFamily_of_base_eq hY hb hq
  obtain ⟨hprop', hH0', hdim', hnodal'⟩ :=
    fibre_standing_of_isPrestableCurveFamily_of_base_eq hY hb hq'
  have := hprop
  have := hH0
  have := hprop'
  obtain ⟨hg, htail, _hp, hbridge⟩ := h
  -- the identity of `V` satisfies the conditions of Stacks 0E7Q
  have hid : Stacks.Curves.StableModel.IsStableContraction ((𝒯).map v) ((𝒯).map v) (𝟙 _) := by
    let : ((𝒯).obj V).Over (Spec (.of p.carrier)) := ⟨(𝒯).map v⟩
    exact (IsIteratedContractionOfRationalBridges.identity (k := p.carrier) ((𝒯).obj V)
      ((𝒯).map v)).isStableContraction hdim hnodal htail hg (fun C _ => hbridge C)
  -- the two presentations are isomorphic over `p`
  obtain ⟨e₀, -, he₀⟩ := exists_iso_of_isPullback_yoneda hq hq'
  have hst := hid.of_iso ((𝒯).mapIso e₀) ((𝒯).mapIso e₀).inv (Iso.inv_hom_id _)
  have hv' : ((𝒯).mapIso e₀).hom ≫ (𝒯).map v = (𝒯).map v' := by
    rw [Functor.mapIso_hom, ← Functor.map_comp, he₀]
  rw [hv'] at hst
  exact (hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField
    p.carrier ((𝒯).map v') hdim' (bijective_appTop_of_isIso_comp _ hH0') hnodal').2 hst.isAmple

/-- The presentation independence of stable fibres, for presentations over the base of the
family itself. -/
theorem hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback_of_isPullback_self
    {Y : CurveFamily B hZ} (hY : IsPrestableCurveFamily B hZ Y)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y.base).obj}
    {V V' : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {v' : V' ⟶ p.siteObject}
    {q : yoneda.obj V ⟶ Y.total.obj} {q' : yoneda.obj V' ⟶ Y.total.obj}
    (hq : IsPullback q (yoneda.map v) Y.toBase.hom (yonedaEquiv.symm p.value))
    (hq' : IsPullback q' (yoneda.map v') Y.toBase.hom (yonedaEquiv.symm p.value))
    (h : HasGenusTwoNoRationalTailNoRationalBridge p.carrier ((𝒯).map v)) :
    HasGenusTwoNoRationalTailNoRationalBridge p.carrier ((𝒯).map v') :=
  hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback_of_isPullback hY rfl
    (by simpa only [eqToHom_refl, Category.comp_id] using hq)
    (by simpa only [eqToHom_refl, Category.comp_id] using hq') h

/-- A presentation of a fibre by a cartesian square of presheaves over a base equal to that of
the family is a cartesian square of algebraic spaces. -/
theorem isPullback_homMk_of_isPullback_yoneda
    {F : AlgebraicSpaces B integerBase hZ}
    {Q : BigFppfOver B integerBase hZ} (f : F ⟶ schemeSpace Q)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace Q).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ F.obj}
    (hsq : IsPullback q (yoneda.map v) f.hom (yonedaEquiv.symm p.value)) :
    IsPullback (ObjectProperty.homMk q : schemeSpace V ⟶ F) (schemeSpaceMap v) f
      (schemeSpaceMap p.value) := by
  have hp : yonedaEquiv.symm p.value = yoneda.map p.value :=
    yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map p.value).symm
  rw [hp] at hsq
  exact IsPullback.of_map_of_faithful (ObjectProperty.ι _) hsq

/-- **Condition (2) of Stacks 0E8A from condition (1), for a contraction onto a stable family.**
Let `X` be a prestable family of curves, `Y` a stable family of curves over the same base and
`c : X ⟶ Y` a morphism over the base satisfying condition (1) of Stacks 0E8A. Then `c` satisfies
condition (2): at every field-valued point of the base its fibre satisfies the three conditions of
Stacks 0E7Q. -/
theorem hasStableContractionFibres_of_isUniversalStructureContraction {X Y : CurveFamily B hZ}
    {hb : Y.base = X.base} {c : X.total ⟶ Y.total}
    (hc : c ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase)
    (hX : IsPrestableCurveFamily B hZ X) (hY : IsStableCurveFamily B hZ Y)
    (h1 : X.IsUniversalStructureContraction B hZ Y hb c) :
    X.HasStableContractionFibres B hZ Y hb c := by
  intro p VX VY vX vY qX qY a hqX hqY ha hqa
  set gY := Y.toBase ≫ eqToHom (congrArg schemeSpace hb) with hgY
  obtain ⟨hpropX, hH0X, -, -⟩ := fibre_standing_of_isPrestableCurveFamily hX hqX
  -- a presentation of the fibre of `Y` on which it is a stable curve
  obtain ⟨V', v', q', hq', hst'⟩ :=
    exists_isPullback_hasGenusTwoNoRationalTailNoRationalBridge_of_base_eq hY hb p
  obtain ⟨hprop', hH0', hdim', hnodal'⟩ :=
    fibre_standing_of_isPrestableCurveFamily_of_base_eq hY.1 hb hq'
  -- the fibre of `c` on it
  have hw : (qX ≫ c.hom) ≫ gY.hom = yoneda.map vX ≫ yonedaEquiv.symm p.value := by
    have e : c.hom ≫ gY.hom = X.toBase.hom := congrArg (fun m => m.hom) hc
    rw [Category.assoc, e]
    exact hqX.w
  let a'' := hq'.lift (qX ≫ c.hom) (yoneda.map vX) hw
  let a' : VX ⟶ V' := yoneda.preimage a''
  have ha'y : yoneda.map a' = a'' := yoneda.map_preimage a''
  have ha'1 : yoneda.map a' ≫ q' = qX ≫ c.hom := by rw [ha'y]; exact hq'.lift_fst _ _ _
  have ha'2 : a' ≫ v' = vX := yoneda.map_injective (by
    rw [Functor.map_comp, ha'y]; exact hq'.lift_snd _ _ _)
  -- the two presentations of the fibre of `Y` are isomorphic
  obtain ⟨e, he1, he2⟩ := exists_iso_of_isPullback_yoneda hq' hqY
  have hae : a ≫ e.hom = a' := yoneda.map_injective (by
    apply hq'.hom_ext
    · rw [Functor.map_comp, Category.assoc, he1, ← hqa, ha'1]
    · rw [Functor.map_comp, Category.assoc, ← Functor.map_comp, he2, ← Functor.map_comp, ha,
        ← Functor.map_comp, ha'2])
  -- condition (1) at `p` on the presentation `V'`
  have := hprop'
  have : IsProper ((𝒯).map a') := by
    have : IsProper ((𝒯).map a' ≫ (𝒯).map v') := by
      rw [← Functor.map_comp, ha'2]; exact hpropX
    exact IsProper.of_comp ((𝒯).map a') ((𝒯).map v')
  have hsc : Space.IsStructureContraction B integerBase hZ (schemeSpaceMap a') := by
    refine h1 p.siteObject p.value (schemeSpace VX) (schemeSpace V') (ObjectProperty.homMk qX)
      (schemeSpaceMap vX) (ObjectProperty.homMk q') (schemeSpaceMap v') (schemeSpaceMap a')
      (isPullback_homMk_of_isPullback_yoneda X.toBase hqX)
      (isPullback_homMk_of_isPullback_yoneda gY hq') ?_ ?_
    · exact ObjectProperty.hom_ext _ ha'1
    · rw [← schemeSpaceMap_comp, ha'2]
  obtain ⟨hunit, hR1⟩ := (isStructureContraction_schemeSpaceMap_iff_unit a').1 hsc
  -- `ω` of the stable fibre is ample
  have hω := (hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField
    p.carrier ((𝒯).map v') hdim' (bijective_appTop_of_isIso_comp _ hH0') hnodal').1 hst'
  have hst : Stacks.Curves.StableModel.IsStableContraction ((𝒯).map vX) ((𝒯).map v')
      ((𝒯).map a') :=
    { comp_eq := by rw [← Functor.map_comp, ha'2]
      isProper := hprop'
      topologicalKrullDim_eq := hdim'
      hasAtWorstNodalSingularities := hnodal'
      isIso_unitToPushforwardObjUnit := hunit
      isZero_rightDerived_one := hR1
      isAmple := hω }
  have := hpropX
  have := hH0X
  have := hst.of_iso ((𝒯).mapIso e) ((𝒯).map a) (by
    rw [Functor.mapIso_hom, ← Functor.map_comp, hae])
  rwa [Functor.mapIso_hom, ← Functor.map_comp, he2] at this

end CurveFamily

end AlgebraicGeometry

end
