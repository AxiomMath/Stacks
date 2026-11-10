module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningConormalConverse
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartCocycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartMaps

/-!
# The chart thickenings of a square-zero extension form a functor to étale morphisms

Let `𝒜 ⟶ 𝒪_X` be a square-zero extension of the étale structure sheaf of an algebraic space with
quasi-coherent kernel `ℐ`. For every étale chart `U` of `X` the restriction `𝒜|_{U_Zar}` is
realized by a first-order thickening `U ⊂ U'`
(`AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedScheme`), and a morphism of charts
`g : V ⟶ U` gives `V' ⟶ U'` (`chartRealizedSchemeMap`). Here `U ↦ U'` is shown to be a functor
whose arrows are étale, which is the claim in the proof of Stacks 05ZT that `U ↦ U'` extends the
functor `U ↦ Spec 𝒜(U)` from affine charts to all of `X_étale`, with values in schemes and
étale morphisms.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeMap_id`,
  `chartRealizedSchemeMap_comp`: functoriality.
* `AlgebraicGeometry.Space.SquareZeroExtension.isBaseChange_ker_of_isAffineChart'`: the kernel
  base change `ℐ(V) = 𝒜(V) ⊗_{𝒜(U)} ℐ(U)` over a morphism of affine charts, in a form stable under
  rewriting the rings, maps and ideals.
* `AlgebraicGeometry.Space.SquareZeroExtension.isKerBaseChange_chartRealizedSchemeMap`: the same on
  every pair of affine opens of `U'` and `V'`.
* `AlgebraicGeometry.Space.SquareZeroExtension.etale_chartRealizedSchemeMap`: `V' ⟶ U'` is étale
  (Stacks 05YT at the scheme level).
* `AlgebraicGeometry.Space.SquareZeroExtension.isPullback_chartRealizedSchemeMap`:
  `V = U ×_{U'} V'`.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- `chartOpensRestrict` of the identity is the identity, up to the identification
`𝟙⁻¹ O = O`. -/
theorem eqToHom_comp_chartOpensRestrict_id (U : SmallEtale B S hS F)
    (O : (chartScheme U).Opens) (p : O = chartSchemeMap (𝟙 U) ⁻¹ᵁ O) :
    (chartOpens B S hS U).map (eqToHom p) ≫ chartOpensRestrict B S hS (𝟙 U) O = 𝟙 _ := by
  apply hom_ext_of_toScheme_map_eq
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_chartOpensRestrict]
  change (chartScheme U).homOfLE p.le ≫ _ = 𝟙 _
  rw [← cancel_mono (Scheme.Opens.ι O), Category.assoc, morphismRestrict_ι,
    Scheme.homOfLE_ι_assoc]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- `chartOpensRestrict` of a composite is the composite of the `chartOpensRestrict`s, up to the
identification `(h ≫ g)⁻¹ O = h⁻¹ (g⁻¹ O)`. -/
theorem eqToHom_comp_chartOpensRestrict_comp {U V W : SmallEtale B S hS F} (g : V ⟶ U)
    (h : W ⟶ V) (O : (chartScheme U).Opens)
    (p : chartSchemeMap h ⁻¹ᵁ (chartSchemeMap g ⁻¹ᵁ O) = chartSchemeMap (h ≫ g) ⁻¹ᵁ O) :
    (chartOpens B S hS W).map (eqToHom p) ≫ chartOpensRestrict B S hS (h ≫ g) O =
      chartOpensRestrict B S hS h (chartSchemeMap g ⁻¹ᵁ O) ≫ chartOpensRestrict B S hS g O := by
  apply hom_ext_of_toScheme_map_eq
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    toScheme_map_chartOpensRestrict, toScheme_map_chartOpensRestrict,
    toScheme_map_chartOpensRestrict]
  change (chartScheme W).homOfLE p.le ≫ _ = _
  refine (cancel_mono (Scheme.Opens.ι O)).1 ?_
  refine (Category.assoc _ _ _).trans ((congrArg ((chartScheme W).homOfLE p.le ≫ ·)
    (morphismRestrict_ι (chartSchemeMap (h ≫ g)) O)).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ chartSchemeMap (h ≫ g)) (Scheme.homOfLE_ι _ p.le)).trans ?_)))
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (chartSchemeMap h ∣_ (chartSchemeMap g ⁻¹ᵁ O) ≫ ·)
    (morphismRestrict_ι (chartSchemeMap g) O)).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ chartSchemeMap g)
    (morphismRestrict_ι (chartSchemeMap h) (chartSchemeMap g ⁻¹ᵁ O))).symm
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- On spaces, `V' ⟶ U'` is the chart morphism. -/
theorem chartRealizedSchemeMap_base {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    (E.chartRealizedSchemeMap g).base = (chartSchemeMap g).base :=
  rfl

/-- On sections, `V' ⟶ U'` is restriction in `𝒜`. -/
theorem chartRealizedSchemeMap_app {U V : SmallEtale B S hS X.1} (g : V ⟶ U)
    (O : (E.chartRealizedScheme U).Opens) :
    (E.chartRealizedSchemeMap g).app O = E.A.obj.map (chartOpensRestrict B S hS g O).op :=
  rfl

/-- **`U ↦ U'` preserves identities.** -/
theorem chartRealizedSchemeMap_id (U : SmallEtale B S hS X.1) :
    E.chartRealizedSchemeMap (𝟙 U) = 𝟙 _ := by
  refine Scheme.Hom.ext rfl fun O => ?_
  rw [chartRealizedSchemeMap_app, Scheme.Hom.id_app]
  refine (E.A.obj.map_comp _ _).symm.trans (Eq.trans ?_ (E.A.obj.map_id _))
  congr 1
  exact congrArg Quiver.Hom.op (eqToHom_comp_chartOpensRestrict_id U O rfl)

/-- **`U ↦ U'` preserves composition.** -/
theorem chartRealizedSchemeMap_comp {U V W : SmallEtale B S hS X.1} (g : V ⟶ U) (h : W ⟶ V) :
    E.chartRealizedSchemeMap (h ≫ g) = E.chartRealizedSchemeMap h ≫ E.chartRealizedSchemeMap g := by
  have hb : (E.chartRealizedSchemeMap (h ≫ g)).base =
      (E.chartRealizedSchemeMap h ≫ E.chartRealizedSchemeMap g).base := by
    rw [Scheme.Hom.comp_base, chartRealizedSchemeMap_base, chartRealizedSchemeMap_base,
      chartRealizedSchemeMap_base, chartSchemeMap_comp, Scheme.Hom.comp_base]
    rfl
  refine Scheme.Hom.ext hb fun O => ?_
  rw [Scheme.Hom.comp_app, chartRealizedSchemeMap_app, chartRealizedSchemeMap_app,
    chartRealizedSchemeMap_app]
  refine (E.A.obj.map_comp _ _).symm.trans (Eq.trans ?_ (E.A.obj.map_comp _ _))
  congr 1
  exact congrArg Quiver.Hom.op (eqToHom_comp_chartOpensRestrict_comp g h O rfl)

/-- The inclusion of a chart into its thickening is a closed immersion. -/
private instance isClosedImmersion_chartInclusion (U : SmallEtale B S hS X.1) :
    AlgebraicGeometry.IsClosedImmersion (E.chartInclusion U) :=
  (E.isFirstOrderThickening_chartInclusion U).1

/-- `isBaseChange_ker_of_isAffineChart` with the restriction map and the two kernels replaced by
equal ones. -/
theorem isBaseChange_ker_of_isAffineChart' {U V : SmallEtale B S hS X.1}
    (hU : IsAffineChart B S hS X.1 U) (hV : IsAffineChart B S hS X.1 V) (g : V ⟶ U)
    (ψ : E.A.obj.obj (op U) →+* E.A.obj.obj (op V)) (hψ : ψ = (E.A.obj.map g.op).hom)
    (KU : Ideal (E.A.obj.obj (op U))) (hKU : KU = RingHom.ker (E.π.hom.app (op U)).hom)
    (KV : Ideal (E.A.obj.obj (op V))) (hKV : KV = RingHom.ker (E.π.hom.app (op V)).hom) :
    letI : Algebra (E.A.obj.obj (op U)) (E.A.obj.obj (op V)) := ψ.toAlgebra
    ∀ κ : KU →ₗ[E.A.obj.obj (op U)] KV,
      (∀ x, (κ x : E.A.obj.obj (op V)) = ψ (x : E.A.obj.obj (op U))) →
        IsBaseChange (E.A.obj.obj (op V)) κ := by
  subst hψ hKU hKV
  exact E.isBaseChange_ker_of_isAffineChart hU hV g

/-- The ideal of `U` in `U'` over an open `O` is the kernel of `𝒜 ⟶ 𝒪_X` over the chart `O`
cuts out. -/
theorem ker_chartInclusion_app {U : SmallEtale B S hS X.1} (O : (chartScheme U).Opens) :
    RingHom.ker ((E.chartInclusion U).app O).hom =
      RingHom.ker (E.π.hom.app (op ((chartOpens B S hS U).obj O))).hom := by
  ext a
  exact RingHom.mem_ker.trans ((E.chartπ_eq_zero_iff U (op O) a).trans RingHom.mem_ker.symm)

/-- `V' ⟶ U'` on sections over an open and an open of its preimage is a restriction of `𝒜`. -/
theorem chartRealizedSchemeMap_appLE {U V : SmallEtale B S hS X.1} (g : V ⟶ U)
    (O : (chartScheme U).Opens) (O' : (chartScheme V).Opens) (e : O' ≤ chartSchemeMap g ⁻¹ᵁ O) :
    (E.chartRealizedSchemeMap g).appLE O O' e =
      E.A.obj.map ((chartOpens B S hS V).map (homOfLE e) ≫ chartOpensRestrict B S hS g O).op :=
  (E.A.obj.map_comp _ _).symm

/-- **The ideal of `V` in `V'` is the base change of the ideal of `U` in `U'`** along
`V' ⟶ U'`, on every pair of affine opens. -/
theorem isKerBaseChange_chartRealizedSchemeMap {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    Stacks.Thickenings.IsKerBaseChange (E.chartInclusion V) (E.chartRealizedSchemeMap g)
      (E.chartInclusion U) := by
  intro O hO O' hO' e
  have hU : IsAffineChart B S hS X.1 ((chartOpens B S hS U).obj O) :=
    hO.preimage (E.chartInclusion U)
  have hV : IsAffineChart B S hS X.1 ((chartOpens B S hS V).obj O') :=
    hO'.preimage (E.chartInclusion V)
  exact E.isBaseChange_ker_of_isAffineChart' hU hV
    ((chartOpens B S hS V).map (homOfLE e) ≫ chartOpensRestrict B S hS g O) _
    (congrArg CommRingCat.Hom.hom (E.chartRealizedSchemeMap_appLE g O O' e)) _
    (E.ker_chartInclusion_app O) _ (E.ker_chartInclusion_app O')

/-- **The morphism of chart thickenings `V' ⟶ U'` over a morphism of étale charts is étale**
(Stacks 05YT at the scheme level, `Stacks.Thickenings.etale_of_isKerBaseChange`). -/
theorem etale_chartRealizedSchemeMap {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    Etale (E.chartRealizedSchemeMap g) := by
  have : Etale (chartSchemeMap g) := etale_toScheme_toOver_map B S hS X.1 g
  exact Stacks.Thickenings.etale_of_isKerBaseChange (E.chartInclusion_comp_chartRealizedSchemeMap g)
    (E.isFirstOrderThickening_chartInclusion U).2 (E.isKerBaseChange_chartRealizedSchemeMap g)

/-- On a pair of affine opens, the ideal of `V` in `V'` is generated by the ideal of `U` in
`U'`. -/
theorem ker_chartInclusion_ideal_eq_map {U V : SmallEtale B S hS X.1} (g : V ⟶ U)
    (O : (chartScheme U).Opens) (hO : IsAffineOpen (X := E.chartRealizedScheme U) O)
    (O' : (chartScheme V).Opens) (hO' : IsAffineOpen (X := E.chartRealizedScheme V) O')
    (e : O' ≤ chartSchemeMap g ⁻¹ᵁ O) :
    (E.chartInclusion V).ker.ideal ⟨O', hO'⟩ =
      Ideal.map ((E.chartRealizedSchemeMap g).appLE O O' e).hom
        ((E.chartInclusion U).ker.ideal ⟨O, hO⟩) := by
  have hU : IsAffineChart B S hS X.1 ((chartOpens B S hS U).obj O) :=
    hO.preimage (E.chartInclusion U)
  have hV : IsAffineChart B S hS X.1 ((chartOpens B S hS V).obj O') :=
    hO'.preimage (E.chartInclusion V)
  let k := (chartOpens B S hS V).map (homOfLE e) ≫ chartOpensRestrict B S hS g O
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply, E.ker_chartInclusion_app,
    E.ker_chartInclusion_app, E.chartRealizedSchemeMap_appLE g O O' e]
  refine le_antisymm (E.ker_le_map_ker_of_isAffineChart hU hV k)
    (Ideal.map_le_iff_le_comap.mpr fun a ha => RingHom.mem_ker.mpr
      ((ConcreteCategory.congr_hom (E.π.hom.naturality k.op) a).trans ?_))
  change (chartRestrict (hF := X.2) k) ((E.π.hom.app _).hom a) = 0
  exact (congrArg (chartRestrict (hF := X.2) k) (RingHom.mem_ker.mp ha)).trans (map_zero _)

/-- **`V = U ×_{U'} V'`**: the square of chart thickenings over a morphism of étale charts is
cartesian (Stacks 063Y's gluing step, with the ideal of `V` generated by that of `U` and
`V' ⟶ U'` flat, being étale). -/
theorem isPullback_chartRealizedSchemeMap {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    IsPullback (E.chartInclusion V) (chartSchemeMap g) (E.chartRealizedSchemeMap g)
      (E.chartInclusion U) := by
  have : Etale (E.chartRealizedSchemeMap g) := E.etale_chartRealizedSchemeMap g
  refine (Stacks.Thickenings.flat_and_isPullback_of_affine (chartSchemeMap g)
    (E.chartRealizedSchemeMap g) (E.chartInclusion_comp_chartRealizedSchemeMap g)
    fun O hO O' hO' e => ⟨E.ker_chartInclusion_ideal_eq_map g O hO O' hO' e, ?_⟩).2
  exact HasRingHomProperty.appLE @Flat (E.chartRealizedSchemeMap g) inferInstance ⟨O, hO⟩
    ⟨O', hO'⟩ e

end AlgebraicGeometry.Space.SquareZeroExtension

end
