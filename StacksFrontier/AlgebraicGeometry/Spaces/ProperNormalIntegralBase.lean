module

public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalIntegralEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperNormalIntegralGenericFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness

/-!
# `f_* 𝒪_X = 𝒪_Y` for a proper morphism onto a normal integral algebraic space

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with `Y` normal and integral
with generic point `ξ`, `X` reduced, every generic point of an irreducible component of `|X|`
mapping to `ξ`, and `H⁰(X_ξ, 𝒪) = κ(ξ)`.  Then the structure map `𝒪_Y ⟶ f_* 𝒪_X` is an
isomorphism: this is the first conclusion of Stacks 0AYI.

The structure map is checked on the normal integral affine étale charts `W` of `Y`, which cover
every étale chart (Stacks 0AYH).  On such a chart, with `A = Γ(W, 𝒪_W)` and `K` the function
field of `W` — the residue field at its generic point —
`AlgebraicGeometry.Space.bijective_algebraMap_pushforwardAlgebra_of_genericChart` applies:

* `Γ(K) ⟶ Γ(X_K)` is bijective, by flat base change from `H⁰(X_ξ, 𝒪) = κ(ξ)`, the point
  `Spec K ⟶ Y` factoring through `Spec κ(ξ)`
  (`AlgebraicGeometry.Space.bijective_globalFunctionsMap_pullback_snd_of_factor`);
* `Γ(X ×_Y W) ⟶ Γ(X_K)` is injective, because `X` is reduced and its generic points lie over `ξ`
  (`AlgebraicGeometry.Space.injective_globalFunctionsMap_pullback_fst_of_genericPoint`).

## Main results

* `AlgebraicGeometry.Space.isFractionRing_appTop_fromSpecResidueField_genericPoint`: the global
  functions of an integral affine scheme have the residue field at the generic point as a
  fraction field.
* `AlgebraicGeometry.Space.isIso_fSharp_of_isNormal_of_isIntegralSpace`: the first conclusion of
  Stacks 0AYI.

## References

* [Stacks Project, Tag 0AYI](https://stacks.math.columbia.edu/tag/0AYI)
* [Stacks Project, Tag 0AYH](https://stacks.math.columbia.edu/tag/0AYH)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **The residue field at the generic point of an integral affine scheme is a fraction field of
its global functions**, through the canonical morphism `Spec κ(η) ⟶ T`. -/
theorem isFractionRing_appTop_fromSpecResidueField_genericPoint (T : Scheme.{u}) [IsAffine T]
    [IsIntegral T] :
    letI := (T.fromSpecResidueField (genericPoint T)).appTop.hom.toAlgebra
    IsFractionRing Γ(T, ⊤) Γ(Spec (T.residueField (genericPoint T)), ⊤) := by
  let := (T.fromSpecResidueField (genericPoint T)).appTop.hom.toAlgebra
  have : Nonempty (⊤ : T.Opens) := ⟨⟨genericPoint T, trivial⟩⟩
  have hfrac : IsFractionRing Γ(T, ⊤) T.functionField :=
    functionField_isFractionRing_of_isAffineOpen T ⊤ (isAffineOpen_top T)
  have hres : Function.Bijective (T.residue (genericPoint T)).hom := by
    refine ⟨?_, IsLocalRing.residue_surjective⟩
    exact (IsLocalRing.residue T.functionField).injective
  let e : T.functionField ≃ₐ[Γ(T, ⊤)] Γ(Spec (T.residueField (genericPoint T)), ⊤) :=
    { (RingEquiv.ofBijective _ hres).trans
        (Scheme.ΓSpecIso (T.residueField (genericPoint T))).symm.commRingCatIsoToRingEquiv with
      commutes' := fun a => by
        change (Scheme.ΓSpecIso (T.residueField (genericPoint T))).inv.hom
            ((T.residue (genericPoint T)).hom ((T.germToFunctionField ⊤).hom a)) =
          (T.fromSpecResidueField (genericPoint T)).appTop.hom a
        simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
          Scheme.germToFunctionField]
        exact congrArg (fun φ => φ.hom ((T.presheaf.germ ⊤ (genericPoint T) trivial).hom a))
          (Scheme.ΓSpecIso_inv_naturality (T.residue (genericPoint T))) }
  exact IsFractionRing.of_algEquiv e

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The normal integral affine étale charts of a normal integral algebraic space cover every
étale chart.**  Every point of an étale chart lies in an affine open of it, which is again an
étale chart, and that affine open has a normal integral affine open neighbourhood of the point
(the shrinking step of Stacks 0AYH,
`AlgebraicGeometry.Space.exists_isAffineOpen_isNormal_isIntegral_of_isAffine_etaleChart`). -/
theorem generate_isNormal_isIntegral_mem_topology {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hnormal : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsNormal T))
    (hintegral : IsIntegralSpace B S hS Y) (U : SmallEtale B S hS Y) :
    Sieve.generate (fun (V : SmallEtale B S hS Y) (_ : V ⟶ U) =>
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y).obj V)) ∧
      IsNormal ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y).obj V)) ∧
      IsIntegral ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y).obj V))) ∈
        SmallEtale.topology B S hS Y U := by
  refine smallEtale_sieve_of_pointwise_covering B S hS Y U _ fun z => ?_
  obtain ⟨T₀, ι₀, hT₀, w₀, hw₀⟩ := exists_affine_chart_at B S hS Y U z
  obtain ⟨O, hwO, hOaff, hOn, hOi⟩ :=
    exists_isAffineOpen_isNormal_isIntegral_of_isAffine_etaleChart B S hS hY hnormal hintegral
      T₀.obj.left hT₀ T₀.obj.hom T₀.property w₀
  refine ⟨openChart B S hS Y T₀ O, openChartInclusion B S hS Y T₀ O ≫ ι₀, ?_, ?_⟩
  · exact Sieve.le_generate _ _ _ (show IsAffine O.toScheme ∧ IsNormal O.toScheme ∧
      IsIntegral O.toScheme from ⟨hOaff, hOn, hOi⟩)
  refine ⟨(⟨w₀, hwO⟩ : O.toScheme), ?_⟩
  rw [Functor.map_comp, Functor.map_comp]
  change ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Y).map ι₀))
    (((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS Y).map (openChartInclusion B S hS Y T₀ O))) ⟨w₀, hwO⟩) = z
  rw [toScheme_map_toOver_map_openChartInclusion]
  exact hw₀

/-- **Stacks 0AYI, first conclusion: `f_* 𝒪_X = 𝒪_Y`.**  Let `f : X ⟶ Y` be a proper morphism of
algebraic spaces over `S` with `Y` integral (Stacks 0AD4) with generic point `ξ` and normal, `X`
reduced, every generic point of an irreducible component of `|X|` mapping to `ξ`, and
`H⁰(X_ξ, 𝒪) = κ(ξ)` — the pullback of global functions along the fibre
`X_ξ = X ×_Y Spec κ(ξ) ⟶ Spec κ(ξ)` over the residue field point at `ξ` being bijective.  Then
the structure map `𝒪_Y ⟶ f_* 𝒪_X` of Stacks 03G8 is an isomorphism.

See the module documentation for the argument. -/
theorem isIso_fSharp_of_isNormal_of_isIntegralSpace {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hYint : IsIntegralSpace B S hS Y.1)
    (hYnormal : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsNormal T))
    (hXred : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsReduced T))
    {ξ : points B S hS Y.1} (hξ : IsGenericPoint ξ Set.univ)
    (hgen : ∀ x ∈ genericPoints (points B S hS X.1), pointsMap B S hS X.1 f.hom x = ξ)
    (h6 : Function.Bijective (globalFunctionsMap B S hS (pullback.snd f
      (ObjectProperty.homMk (residueFieldMorphism B S hS Y.1 hYint.2.1 ξ) :
        schemeSpace ((residueFieldRepresentative B S hS Y.1 hYint.2.1 ξ).1.siteObject B S hS Y.1) ⟶
          Y)))) :
    IsIso (smallEtaleRingedToposHom B S hS f).fSharp := by
  classical
  have hYdec : IsDecentSpace B S hS Y.1 := hYint.2.1
  have : IrreducibleSpace (points B S hS Y.1) := hYint.2.2
  have hξgen : ξ ∈ genericPoints (points B S hS Y.1) := by
    change closure {ξ} ∈ irreducibleComponents (points B S hS Y.1)
    rw [irreducibleComponents_eq_singleton, hξ.def]
    rfl
  obtain ⟨-, hqs⟩ := isQuasiCompact_isQuasiSeparated_of_isProper B S hS f hf
  have hXdec : IsDecentSpace B S hS X.1 :=
    isDecentSpace_of_isDecent B S hS X.2 Y.2 f.hom hYdec
      (isDecent_of_isReasonable B S hS X.2 Y.2 f.hom
        (isReasonable_of_isVeryReasonable B S hS X.2 Y.2
          (isVeryReasonable_of_isQuasiSeparated B S hS X.2 Y.2 hqs)))
  let py := (residueFieldRepresentative B S hS Y.1 hYdec ξ).1
  have : Mono (yonedaEquiv.symm py.value) := (residueFieldRepresentative B S hS Y.1 hYdec ξ).2.2
  let ρ : schemeSpace (py.siteObject B S hS Y.1) ⟶ Y :=
    ObjectProperty.homMk (residueFieldMorphism B S hS Y.1 hYdec ξ)
  refine Stacks.Sites.isIso_of_locallyBijective_app (SmallEtale.topology B S hS Y.1) _
    fun U => ⟨_, generate_isNormal_isIntegral_mem_topology Y.2 hYnormal hYint U, ?_⟩
  rintro V - ⟨hVaff, hVn, hVi⟩
  let Vo := (SmallEtale.toOver B S hS Y.1).obj V
  let Vsch := (BigFppfOver.toScheme B S hS).obj Vo
  have : IsAffine Vsch := hVaff
  have : IsIntegral Vsch := hVi
  have : IsIntegrallyClosed Γ(Vsch, ⊤) :=
    (isNormal_iff_forall_affineOpen_normal Vsch).mp hVn ⟨⊤, isAffineOpen_top Vsch⟩
      ⟨⟨genericPoint Vsch, trivial⟩⟩
  let q := schemeResidueFieldPoint B S hS Vo (genericPoint Vsch)
  let ι : q.siteObject B S hS (yoneda.obj Vo) ⟶ Vo := q.value
  have hιmap :
      (BigFppfOver.toScheme B S hS).map ι = Vsch.fromSpecResidueField (genericPoint Vsch) := rfl
  have hfrac : let := ((BigFppfOver.toScheme B S hS).map ι).appTop.hom.toAlgebra
      IsFractionRing Γ(Vsch, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (q.siteObject B S hS (yoneda.obj Vo)), ⊤) := by
    rw [hιmap]
    exact isFractionRing_appTop_fromSpecResidueField_genericPoint Vsch
  have hι : ∀ z, (BigFppfOver.toScheme B S hS).map ι z = genericPoint Vsch := fun z => by
    rw [hιmap]
    exact Scheme.fromSpecResidueField_apply _ _
  have : Nonempty ((BigFppfOver.toScheme B S hS).obj (q.siteObject B S hS (yoneda.obj Vo))) :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of (Vsch.residueField (genericPoint Vsch)))))
  let qx := FieldValuedPoint.map B S hS (yoneda.obj Vo) V.obj.hom q
  have hqclass : qx.class B S hS Y.1 = ξ := by
    rw [← pointsMap_class]
    refine pointsMap_eq_of_mem_genericPoints B S hS Y.2 hYdec
      (fun y => hξ.specializes (Set.mem_univ y)) Vo V.obj.hom V.property _ ?_
    rw [genericPoints_eq_singleton]
    exact hι _
  obtain ⟨g, hg, -⟩ :=
    FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS Y.1 Y.2 py qx
      ((residueFieldRepresentative B S hS Y.1 hYdec ξ).2.1.trans hqclass.symm)
  have hgsq : schemeSpaceMap g ≫ ρ =
      schemeSpaceMap ι ≫ ((comparisonFunctor B S hS Y).obj V).obj.hom := by
    apply ObjectProperty.hom_ext
    change yoneda.map g ≫ yonedaEquiv.symm py.value = yoneda.map ι ≫ V.obj.hom
    rw [yonedaEquiv_symm_naturality_left g Y.1 py.value, hg]
    change yonedaEquiv.symm (V.obj.hom.app _ q.value) = _
    rw [← yonedaEquiv_symm_naturality_right]
    rfl
  have hbij := bijective_globalFunctionsMap_pullback_snd_of_factor f hf ρ
    (k := py.carrier) (Iso.refl _) h6 V ι g hgsq
  have hinj := injective_globalFunctionsMap_pullback_fst_of_genericPoint f hXred hXdec
    (localRingDimension_eq_zero_of_mem_genericPoints B S hS Y.2 hYdec hξgen) hgen V ι hι
  exact bijective_algebraMap_pushforwardAlgebra_of_genericChart f hf.2.2 V ι hfrac
    (pullback.fst _ _) (pullback.snd _ _) pullback.condition hbij hinj

end AlgebraicGeometry.Space

end
