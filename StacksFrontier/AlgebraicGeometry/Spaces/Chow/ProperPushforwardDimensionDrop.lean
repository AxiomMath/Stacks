module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionOnCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Catenary
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.DimensionDropSchematicFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGood
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenChartOrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenChartResidueFieldSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedProperSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicNeighborhoodOfPrimeDivisor
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction

/-!
# Proper pushforward of a principal divisor when the dimension drops

In Situation 0EDT let `W` and `W'` be good integral algebraic spaces over the base and let
`q : W ⟶ W'` be a proper dominant morphism over the base with `dim_δ(W) = dim_δ(W') + 1`. For
an invertible rational function `f` on `W` the pushforward `q_* div(f)` vanishes. This is the
case `dim_δ(p(W)) = k` of the proof of Stacks 0EQC.

The only integral closed subspace of `W'` that can occur in the `k`-cycle `q_* div(f)` is `W'`
itself, with generic point `η`, and its coefficient is the sum over the prime divisors `Z` of `W`
lying over `η` of `ord_Z(f) [R(Z) : R(W')]`. Over an open subscheme `T ⊆ W'` containing `η` whose
inverse image `V = q⁻¹(T)` is a scheme (Stacks 0ADD, 07SR), the morphism `V ⟶ T` is proper,
dominant and of relative dimension one at the generic point (Stacks 04NR); the orders of
vanishing and the degrees are read on `V` (Stacks 0ENM), and the sum vanishes by the scheme case,
Stacks 02RU on the generic fibre (Stacks 02S2).

## Main results

* `AlgebraicGeometry.Space.properCyclePushforward_eq_zero_of_deltaValue_drop`: the vanishing.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 04NR](https://stacks.math.columbia.edu/tag/04NR)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Order

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The scheme of an open chart -/

section OpenChart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {V : BigFppfOver B S hS} (β : yoneda.obj V ⟶ X) (hβ : IsOpenImmersion B S hS β)

include hX hβ in
/-- The points of the scheme of an open chart are an open subset of the points of the space. -/
theorem isOpenEmbedding_pointsMap_pointsEquivScheme_symm :
    Topology.IsOpenEmbedding
      (pointsMap B S hS (yoneda.obj V) β ∘ (pointsEquivScheme B S hS V).symm) := by
  have hβet : IsEtale B S hS β := isEtale_of_isOpenImmersion B S hS hβ
  have _ : Mono β := mono_of_isOpenImmersion B S hS _ hβ
  refine Topology.IsOpenEmbedding.comp ?_ (schemePointsHomeomorph B S hS V).symm.isOpenEmbedding
  exact .of_continuous_injective_isOpenMap (continuous_pointsMap B S hS β)
    (pointsMap_injective_of_mono B S hS β)
    (isOpenMap_pointsMap_of_isEtale B S hS β (isAlgebraicSpace_yoneda B S hS V) hX hβet)

include hX hβ in
/-- The scheme of an open chart of an integral algebraic space is integral, once nonempty. -/
theorem isIntegral_toScheme_obj_of_isOpenImmersion (hInt : IsIntegralSpace B S hS X)
    [Nonempty ((BigFppfOver.toScheme B S hS).obj V)] :
    IsIntegral ((BigFppfOver.toScheme B S hS).obj V) := by
  have _ : IrreducibleSpace (points B S hS X) := hInt.2.2
  have _ : IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj V) :=
    (isOpenEmbedding_pointsMap_pointsEquivScheme_symm B S hS hX β hβ).irreducibleSpace
  have _ : IsReduced ((BigFppfOver.toScheme B S hS).obj V) :=
    (exists_atlas_iff_forall_etale B S hS X (fun Y : Scheme.{u} => IsReduced Y) hX).mp
      hInt.1 V β (presheaf_etale_of_isOpenImmersion B S hS hβ)
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

include hX hβ in
/-- The scheme of an open chart of a locally Noetherian algebraic space is locally Noetherian. -/
theorem isLocallyNoetherian_toScheme_obj_of_isOpenImmersion
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y)) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
  (exists_atlas_iff_forall_etale B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y) hX).mp
    hN V β (presheaf_etale_of_isOpenImmersion B S hS hβ)

include hβ in
/-- The generic point of the scheme of an open chart of an integral algebraic space lies over
the generic point of the space. -/
theorem pointsMap_pointsEquivScheme_symm_genericPoint (hInt : IsIntegralSpace B S hS X)
    [IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj V)] :
    pointsMap B S hS (yoneda.obj V) β
        ((pointsEquivScheme B S hS V).symm
          (_root_.genericPoint ((BigFppfOver.toScheme B S hS).obj V))) =
      genericPoint B S hS hX hInt := by
  have _ : IrreducibleSpace (points B S hS X) := hInt.2.2
  have _ : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hInt.2.1
  set j := pointsMap B S hS (yoneda.obj V) β ∘ (pointsEquivScheme B S hS V).symm with hj
  have hjemb := isOpenEmbedding_pointsMap_pointsEquivScheme_symm B S hS hX β hβ
  have hgen : IsGenericPoint (j (_root_.genericPoint ((BigFppfOver.toScheme B S hS).obj V)))
      Set.univ := by
    have hdense : Dense (Set.range j) :=
      hjemb.isOpen_range.dense (Set.range_nonempty _)
    have hsub : Set.range j ⊆
        closure {j (_root_.genericPoint ((BigFppfOver.toScheme B S hS).obj V))} := by
      have himg := image_closure_subset_closure_image (s :=
        {_root_.genericPoint ((BigFppfOver.toScheme B S hS).obj V)}) hjemb.continuous
      rw [Set.image_singleton, (genericPoint_spec ((BigFppfOver.toScheme B S hS).obj V)).def,
        Set.image_univ] at himg
      exact himg
    show closure {j (_root_.genericPoint ((BigFppfOver.toScheme B S hS).obj V))} = Set.univ
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hdense.closure_eq]
    exact closure_minimal hsub isClosed_closure
  exact hgen.eq (isGenericPoint_genericPoint B S hS hX hInt)

include hX hβ in
/-- The coheight of a point of the scheme of an open chart is the codimension of the closure of
its image. -/
theorem coheight_eq_codimension_pointsMap (hdec : IsDecentSpace B S hS X)
    [QuasiSober ((BigFppfOver.toScheme B S hS).obj V)]
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    coheight v = codimension (IrreducibleCloseds.closureSingleton
      (pointsMap B S hS (yoneda.obj V) β ((pointsEquivScheme B S hS V).symm v))) := by
  have _ : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hdec
  set j := pointsMap B S hS (yoneda.obj V) β ∘ (pointsEquivScheme B S hS V).symm
  have hj := isOpenEmbedding_pointsMap_pointsEquivScheme_symm B S hS hX β hβ
  have hmap : IrreducibleCloseds.map j hj.continuous (IrreducibleCloseds.closureSingleton v) =
      IrreducibleCloseds.closureSingleton (j v) := by
    ext : 1
    simp only [IrreducibleCloseds.coe_map, IrreducibleCloseds.coe_closureSingleton]
    rw [closure_image_closure hj.continuous, Set.image_singleton]
  have hc := hj.coheight_map (IrreducibleCloseds.closureSingleton v)
  rw [hmap] at hc
  rw [← coheight_orderIso
    (irreducibleSetEquivPoints (α := ((BigFppfOver.toScheme B S hS).obj V))).symm v]
  exact hc.symm

end OpenChart

/-- Integral closed subspaces of a decent algebraic space with the same ambient generic point are
equal. -/
private theorem eq_of_ambientGenericPoint_eq (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) {Z Z' : IntegralClosedSubspace B S hS X}
    (h : Z.ambientGenericPoint B S hS = Z'.ambientGenericPoint B S hS) : Z = Z' := by
  rw [eq_integralClosedSubspaceOfPoint B S hS hX hdec _ Z
      (Z.isGenericPoint_ambientGenericPoint B S hS hX),
    eq_integralClosedSubspaceOfPoint B S hS hX hdec _ Z'
      (h ▸ Z'.isGenericPoint_ambientGenericPoint B S hS hX)]

/-! ### The relative transcendence degree of the generic point -/

section Transcendence

variable (D : BaseSpaceDimensionSituation.{u})
    {W W' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sW : W ⟶ D.space) (hW : D.IsGood sW) (hWint : IsIntegralSpace D.site D.base D.base_mem W)
    (sW' : W' ⟶ D.space) (hW' : D.IsGood sW')
    (hW'int : IsIntegralSpace D.site D.base D.base_mem W')
    (q : W ⟶ W') (hq : q ≫ sW' = sW)

include hq in
/-- The generic fibre has relative dimension one, read on open charts. For a morphism
`q : W ⟶ W'` locally of finite type over the base between good integral algebraic spaces with
`dim_δ(W) = dim_δ(W') + 1` and sending the generic point to the generic point, and open charts
`β : h_V ⟶ W`, `α : h_T ⟶ W'` through which `q` is induced by `π : V ⟶ T`, the residue field
of `V` at a point over the generic point of `W` has transcendence degree one over the residue
field of `T` at its image. -/
theorem toNat_trdeg_residueFieldMap_eq_one_of_deltaValue_drop
    (hqft : IsLocallyOfFiniteType D.site D.base D.base_mem q) (k : ℤ)
    (hWd : D.deltaValue sW (genericPoint D.site D.base D.base_mem hW.1 hWint) = k + 1)
    (hW'd : D.deltaValue sW' (genericPoint D.site D.base D.base_mem hW'.1 hW'int) = k)
    (hqgen : pointsMap D.site D.base D.base_mem W q
      (genericPoint D.site D.base D.base_mem hW.1 hWint) =
        genericPoint D.site D.base D.base_mem hW'.1 hW'int)
    {Vo To : BigFppfOver D.site D.base D.base_mem} (β : yoneda.obj Vo ⟶ W)
    (α : yoneda.obj To ⟶ W') (hβ : IsOpenImmersion D.site D.base D.base_mem β)
    (hα : IsOpenImmersion D.site D.base D.base_mem α) (π : Vo ⟶ To)
    (hcomm : yoneda.map π ≫ α = β ≫ q)
    (v : (BigFppfOver.toScheme D.site D.base D.base_mem).obj Vo)
    (hv : pointsMap D.site D.base D.base_mem (yoneda.obj Vo) β
      ((pointsEquivScheme D.site D.base D.base_mem Vo).symm v) =
        genericPoint D.site D.base D.base_mem hW.1 hWint) :
    letI :=
      (((BigFppfOver.toScheme D.site D.base D.base_mem).map π).residueFieldMap v).hom.toAlgebra
    Cardinal.toNat (Algebra.trdeg
      (((BigFppfOver.toScheme D.site D.base D.base_mem).obj To).residueField
        ((BigFppfOver.toScheme D.site D.base D.base_mem).map π v))
      (((BigFppfOver.toScheme D.site D.base D.base_mem).obj Vo).residueField v)) = 1 := by
  set ξ := genericPoint D.site D.base D.base_mem hW.1 hWint
  obtain ⟨t, ht⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem q hqft ξ
  obtain ⟨s, hs⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem sW' hW'.2.2
    (pointsMap D.site D.base D.base_mem W q ξ)
  have hcomp := hasTranscendenceDegreeAt_comp D.site D.base D.base_mem hW.1 hW'.1
    D.isAlgebraicSpace q sW' ξ t s ht hs
  have hft : IsLocallyOfFiniteType D.site D.base D.base_mem (q ≫ sW') := by
    rw [hq]; exact hW.2.2
  have e1 := inducedDimensionValue_eq D.site D.base D.base_mem hW.1 D.isAlgebraicSpace
    D.delta.toFun (q ≫ sW') hft ξ _ hcomp
  have e2 := inducedDimensionValue_eq D.site D.base D.base_mem hW'.1 D.isAlgebraicSpace
    D.delta.toFun sW' hW'.2.2 (pointsMap D.site D.base D.base_mem W q ξ) _ hs
  have hWd' : inducedDimensionValue D.site D.base D.base_mem D.delta.toFun (q ≫ sW') ξ =
      k + 1 := by
    rw [hq]; exact hWd
  have hW'd' : inducedDimensionValue D.site D.base D.base_mem D.delta.toFun sW'
      (pointsMap D.site D.base D.base_mem W q ξ) = k := by
    rw [hqgen]; exact hW'd
  have hpt : pointsMap D.site D.base D.base_mem W (q ≫ sW') ξ =
      pointsMap D.site D.base D.base_mem W' sW' (pointsMap D.site D.base D.base_mem W q ξ) :=
    pointsMap_comp_apply D.site D.base D.base_mem q sW' ξ
  rw [hpt] at e1
  have hcast : ((t : ℕ∞) + (s : ℕ∞)).toNat = t + s := by
    rw [← Nat.cast_add, ENat.toNat_natCast]
  rw [hcast] at e1
  rw [ENat.toNat_natCast] at e2
  have ht1 : t = 1 := by omega
  subst ht1
  have hβet := presheaf_etale_of_isOpenImmersion D.site D.base D.base_mem hβ
  have hαet := presheaf_etale_of_isOpenImmersion D.site D.base D.base_mem hα
  have key := (hasTranscendenceDegreeAt_pointsMap_iff D.site D.base D.base_mem ((1 : ℕ) : ℕ∞) q
    Vo To β α π hβet hαet hcomm v).mp (by rw [hv]; exact ht)
  rw [Nat.cast_one] at key
  exact Cardinal.toNat_eq_one.mpr (Cardinal.toENat_eq_one.mp key)

end Transcendence

/-! ### The vanishing of the pushforward of a principal divisor -/

section DimensionDrop

variable (D : BaseSpaceDimensionSituation.{u})
    {W W' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sW : W ⟶ D.space) (hW : D.IsGood sW) (hWint : IsIntegralSpace D.site D.base D.base_mem W)
    (sW' : W' ⟶ D.space) (hW' : D.IsGood sW')
    (hW'int : IsIntegralSpace D.site D.base D.base_mem W')
    (q : W ⟶ W') (hq : q ≫ sW' = sW)

include hWint hW'int in
/-- The dimension-drop case of Stacks 0EQC. Let `q : W ⟶ W'` be a proper morphism over the base
of good integral algebraic spaces sending the generic point of `W` to that of `W'`, with
`dim_δ(W) = k + 1` and `dim_δ(W') = k`. Then the proper pushforward along `q` of a principal
divisor `div(f)`, `f ∈ R(W)^*`, read at the canonical embeddings of Stacks 0ENK, is zero. -/
theorem properCyclePushforward_eq_zero_of_deltaValue_drop
    (hqp : IsProper D.site D.base D.base_mem q)
    (hqgen : pointsMap D.site D.base D.base_mem W q
      (genericPoint D.site D.base D.base_mem hW.1 hWint) =
        genericPoint D.site D.base D.base_mem hW'.1 hW'int) (k : ℤ)
    (hWd : D.deltaValue sW (genericPoint D.site D.base D.base_mem hW.1 hWint) = k + 1)
    (hW'd : D.deltaValue sW' (genericPoint D.site D.base D.base_mem hW'.1 hW'int) = k)
    (c : CycleGroup D sW k) (hc : IsPrincipalDivisorCycleOfGood D sW hW hWint k c) :
    properCyclePushforward D sW hW sW' hW' hq hqp.2.1.2 k c = 0 := by
  classical
  set ξ := genericPoint D.site D.base D.base_mem hW.1 hWint
  set ξ' := genericPoint D.site D.base D.base_mem hW'.1 hW'int
  have hdec : IsDecentSpace D.site D.base D.base_mem W := hWint.isDecentSpace
  have hdec' : IsDecentSpace D.site D.base D.base_mem W' := hW'int.isDecentSpace
  have _ : T0Space (points D.site D.base D.base_mem W) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hW.1 hdec
  have _ : T0Space (points D.site D.base D.base_mem W') :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hW'.1 hdec'
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sW hW
  have hN' := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sW' hW'
  obtain ⟨U, hU, hUrep, hξ'U, hVrep⟩ := exists_isRepresentable_preimage_of_deltaValue_drop D sW
    hW hWint sW' hW' hW'int q hq hqp k hWd hW'd
  set Vsub := U.preimage q with hVsub
  have hV : IsOpenSubspace D.site D.base D.base_mem Vsub :=
    isOpenSubspace_preimage D.site D.base D.base_mem q U hW'.1 hW.1 hU
  have _ := hUrep
  have _ := hVrep
  set To := U.toFunctor.reprX
  set eT : yoneda.obj To ≅ U.toFunctor := U.toFunctor.reprW
  set Vo := Vsub.toFunctor.reprX
  set eV : yoneda.obj Vo ≅ Vsub.toFunctor := Vsub.toFunctor.reprW
  set α : yoneda.obj To ⟶ W' := eT.hom ≫ U.ι with hαdef
  set β : yoneda.obj Vo ⟶ W := eV.hom ≫ Vsub.ι with hβdef
  have hα : IsOpenImmersion D.site D.base D.base_mem α :=
    MorphismProperty.RespectsIso.precomp _ eT.hom U.ι hU.2
  have hβ : IsOpenImmersion D.site D.base D.base_mem β :=
    MorphismProperty.RespectsIso.precomp _ eV.hom Vsub.ι hV.2
  set q₀ : Vsub.toFunctor ⟶ U.toFunctor := U.fromPreimage q
  have hsq : IsPullback q₀ Vsub.ι U.ι q := Subfunctor.isPullback_preimage q U
  have hq₀ : IsProper D.site D.base D.base_mem q₀ :=
    isProper_of_isPullback' hV.1 hW.1 hU.1 hW'.1 hsq.flip hqp
  set π : Vo ⟶ To := Yoneda.fullyFaithful.preimage (eV.hom ≫ q₀ ≫ eT.inv)
  have hπmap : yoneda.map π = eV.hom ≫ q₀ ≫ eT.inv := Yoneda.fullyFaithful.map_preimage _
  have hcomm : yoneda.map π ≫ α = β ≫ q := by
    rw [hπmap, hαdef, hβdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [hsq.w]
  have hπprop : IsProper D.site D.base D.base_mem (yoneda.map π) := by
    rw [hπmap]
    exact isProper_comp D.site D.base D.base_mem (isAlgebraicSpace_yoneda _ _ _ Vo) hV.1
      (isAlgebraicSpace_yoneda _ _ _ To) _ _ (isProper_of_isIso _ _ _ _)
      (isProper_comp D.site D.base D.base_mem hV.1 hU.1 (isAlgebraicSpace_yoneda _ _ _ To) _ _
        hq₀ (isProper_of_isIso _ _ _ _))
  set Vs := (BigFppfOver.toScheme D.site D.base D.base_mem).obj Vo
  set Ts := (BigFppfOver.toScheme D.site D.base D.base_mem).obj To
  set πs := (BigFppfOver.toScheme D.site D.base D.base_mem).map π
  set jV := pointsMap D.site D.base D.base_mem (yoneda.obj Vo) β ∘
    (pointsEquivScheme D.site D.base D.base_mem Vo).symm
  set jT := pointsMap D.site D.base D.base_mem (yoneda.obj To) α ∘
    (pointsEquivScheme D.site D.base D.base_mem To).symm
  have hjVemb := isOpenEmbedding_pointsMap_pointsEquivScheme_symm D.site D.base D.base_mem hW.1 β hβ
  have hjTemb := isOpenEmbedding_pointsMap_pointsEquivScheme_symm D.site D.base D.base_mem hW'.1
    α hα
  have hrangeβ : ∀ x : points D.site D.base D.base_mem W,
      pointsMap D.site D.base D.base_mem W q x ∈
          Set.range (pointsMap D.site D.base D.base_mem U.toFunctor U.ι) →
        ∃ v, jV v = x := by
    intro x hx
    have hxV : x ∈ Set.range (pointsMap D.site D.base D.base_mem Vsub.toFunctor Vsub.ι) := by
      rw [hVsub, range_pointsMap_subfunctor_preimage]
      exact hx
    obtain ⟨p, rfl⟩ := hxV
    refine ⟨pointsEquivScheme D.site D.base D.base_mem Vo
      (pointsMap D.site D.base D.base_mem _ eV.inv p), ?_⟩
    show pointsMap D.site D.base D.base_mem (yoneda.obj Vo) β
      ((pointsEquivScheme D.site D.base D.base_mem Vo).symm
        ((pointsEquivScheme D.site D.base D.base_mem Vo)
          (pointsMap D.site D.base D.base_mem _ eV.inv p))) = _
    have hee : pointsMap D.site D.base D.base_mem _ eV.hom
        (pointsMap D.site D.base D.base_mem _ eV.inv p) = p := by
      rw [← pointsMap_comp_apply, Iso.inv_hom_id, pointsMap_id, id_eq]
    rw [Equiv.symm_apply_apply, hβdef, pointsMap_comp_apply, hee]
  have hnat : ∀ v, jT (πs v) = pointsMap D.site D.base D.base_mem W q (jV v) := by
    intro v
    have h1 : (pointsEquivScheme D.site D.base D.base_mem To).symm (πs v) =
        pointsMap D.site D.base D.base_mem _ (yoneda.map π)
          ((pointsEquivScheme D.site D.base D.base_mem Vo).symm v) := by
      refine (pointsEquivScheme D.site D.base D.base_mem To).symm_apply_eq.2 ?_
      show πs v = pointsToScheme D.site D.base D.base_mem To _
      rw [pointsToScheme_pointsMap_yoneda]
      congr 1
      exact ((pointsEquivScheme D.site D.base D.base_mem Vo).apply_symm_apply v).symm
    show pointsMap D.site D.base D.base_mem _ α
        ((pointsEquivScheme D.site D.base D.base_mem To).symm (πs v)) = _
    rw [h1, ← pointsMap_comp_apply, hcomm, pointsMap_comp_apply]
    rfl
  obtain ⟨vξ, -⟩ := hrangeβ ξ (by rw [hqgen]; exact hξ'U)
  have _ : Nonempty Vs := ⟨vξ⟩
  have _ : Nonempty Ts := ⟨πs vξ⟩
  have _ : IsIntegral Vs := isIntegral_toScheme_obj_of_isOpenImmersion D.site D.base D.base_mem
    hW.1 β hβ hWint
  have _ : IsIntegral Ts := isIntegral_toScheme_obj_of_isOpenImmersion D.site D.base D.base_mem
    hW'.1 α hα hW'int
  have _ : IsLocallyNoetherian Vs := isLocallyNoetherian_toScheme_obj_of_isOpenImmersion
    D.site D.base D.base_mem hW.1 β hβ hN
  have _ : IsLocallyNoetherian Ts := isLocallyNoetherian_toScheme_obj_of_isOpenImmersion
    D.site D.base D.base_mem hW'.1 α hα hN'
  have _ : AlgebraicGeometry.IsProper πs :=
    isProper_toScheme_of_isProper_yoneda D.site D.base D.base_mem π hπprop
  have hgV : jV (_root_.genericPoint Vs) = ξ :=
    pointsMap_pointsEquivScheme_symm_genericPoint D.site D.base D.base_mem hW.1 β hβ hWint
  have hgT : jT (_root_.genericPoint Ts) = ξ' :=
    pointsMap_pointsEquivScheme_symm_genericPoint D.site D.base D.base_mem hW'.1 α hα hW'int
  have hlift : ∀ v, pointsMap D.site D.base D.base_mem W q (jV v) = ξ' →
      πs v = _root_.genericPoint Ts := fun v hv => hjTemb.injective (by
    show jT _ = jT _
    rw [hnat, hv, hgT])
  have hπgen : πs (_root_.genericPoint Vs) = _root_.genericPoint Ts :=
    hlift _ (by rw [hgV, hqgen])
  have _ : AlgebraicGeometry.IsDominant πs := by
    rw [AlgebraicGeometry.isDominant_iff, DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro y
    have hmem : _root_.genericPoint Ts ∈ Set.range πs := ⟨_, hπgen⟩
    refine closure_mono (Set.singleton_subset_iff.2 hmem) ?_
    exact specializes_iff_mem_closure.1 ((genericPoint_spec Ts).specializes trivial)
  have hW'uc : IsUniversallyCatenary D.site D.base D.base_mem W' :=
    isUniversallyCatenary_of_isLocallyOfFiniteType D.site D.base D.base_mem D.isAlgebraicSpace
      hW'.1 D.universallyCatenary sW' hW'.2.2
  let C : Stacks.Chow.ChowSituation.{u} :=
    { S := Ts
      isUniversallyCatenary := isUniversallyCatenary_chart_of_isUniversallyCatenary D.site D.base
        D.base_mem hW'.1 hW'uc To α (isEtale_of_isOpenImmersion D.site D.base D.base_mem hα)
      dimensionFunction := (deltaDimensionFunction D sW' hW').comp hjTemb }
  let E := genericFractionEmbedding D.site D.base D.base_mem hW.1 hWint.isDecentSpace hWint hN
  have := E.nontrivial
  have := E.isNoetherianRing
  have := E.krullDimLE
  obtain ⟨f, hf, hcf⟩ := hc
  obtain ⟨g, hg⟩ := exists_functionField_forall_openChartRationalFunction D.site D.base D.base_mem
    hW.1 β hβ f
  have hg0 : g ≠ 0 := by
    intro hg0
    obtain ⟨Ua, hUa, hvUa⟩ : ∃ Ua : Vs.Opens, IsAffineOpen Ua ∧ vξ ∈ Ua := by
      obtain ⟨-, ⟨Wa, hWa, rfl⟩, hvWa, -⟩ := Vs.isBasis_affineOpens.exists_subset_of_mem_open
        (show vξ ∈ (⊤ : Vs.Opens) from trivial) (⊤ : Vs.Opens).2
      exact ⟨Wa, hWa, hvWa⟩
    have h := hg Ua hUa (⟨vξ, hvUa⟩ : Ua)
    rw [hg0, map_zero] at h
    exact (hf.map (openChartRationalFunction D.site D.base D.base_mem hW.1 β hβ Ua hUa
      (⟨vξ, hvUa⟩ : Ua))).ne_zero h
  have htr := toNat_trdeg_residueFieldMap_eq_one_of_deltaValue_drop D sW hW hWint sW' hW' hW'int
    q hq hqp.2.1.1 k hWd hW'd hqgen β α hβ hα π hcomm (_root_.genericPoint Vs) hgV
  have _ : LocallyOfFiniteType πs := inferInstance
  have hdimV : Stacks.Chow.schemeDeltaDimension C (πs ≫ 𝟙 Ts) =
      ((C.dimensionFunction (_root_.genericPoint Ts) + 1 : ℤ) : EInt) := by
    rw [Stacks.Chow.schemeDeltaDimension_eq_genericPoint,
      Stacks.Chow.relativeDimension_comp_add_of_trdeg C.dimensionFunction πs (𝟙 Ts) _ 1 htr,
      Stacks.Chow.relativeDimension_id, hπgen]
    rfl
  have hdimT : Stacks.Chow.schemeDeltaDimension C (𝟙 Ts) =
      ((C.dimensionFunction (_root_.genericPoint Ts) + 1 - 1 : ℤ) : EInt) := by
    rw [Stacks.Chow.schemeDeltaDimension_eq_genericPoint, Stacks.Chow.relativeDimension_id]
    congr 1
    ring
  have hsum := Stacks.Chow.genericFibreDegreeVanishes C (𝟙 Ts) πs hdimV hdimT g hg0
  refine Subtype.ext (funext fun Z' => ?_)
  rw [properPushforward_apply]
  show (∑ᶠ Z, (c : IntegralClosedSubspace D.site D.base D.base_mem W → ℤ) Z *
    properCycleMult D sW hW sW' hW' q Z Z') = 0
  set Φ : Vs → IntegralClosedSubspace D.site D.base D.base_mem W := fun v =>
    integralClosedSubspaceOfPoint D.site D.base D.base_mem hW.1 hdec (jV v)
  set F : Set Vs := πs.base ⁻¹' {_root_.genericPoint Ts}
  have hΦgen : ∀ v, (Φ v).ambientGenericPoint D.site D.base D.base_mem = jV v := fun v =>
    ((Φ v).isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hW.1).eq
      (isGenericPoint_integralClosedSubspaceOfPoint D.site D.base D.base_mem hW.1 hdec (jV v))
  have hΦinj : Function.Injective Φ := fun v w h => hjVemb.injective (by
    show jV v = jV w
    rw [← hΦgen v, ← hΦgen w, h])
  have hK : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem W,
      (c : IntegralClosedSubspace D.site D.base D.base_mem W → ℤ) Z *
          properCycleMult D sW hW sW' hW' q Z Z' ≠ 0 →
        Z'.ambientGenericPoint D.site D.base D.base_mem = ξ' ∧ ∃ v ∈ F, Φ v = Z := by
    intro Z hZ
    have hcZ := left_ne_zero_of_mul hZ
    obtain ⟨himg, hdeg⟩ := (properCycleMult_ne_zero_iff D sW hW sW' hW' q Z Z').1
      (right_ne_zero_of_mul hZ)
    have hδeq := deltaDimension_closureImage_of_properCycleDegree_ne_zero D sW hW sW' hW' q hdeg
    have hδZ : deltaDimension D sW Z = k := c.2.2 Z hcZ
    have hζ : Z'.ambientGenericPoint D.site D.base D.base_mem =
        pointsMap D.site D.base D.base_mem W q
          (Z.ambientGenericPoint D.site D.base D.base_mem) := by
      rw [← himg]
      exact IntegralClosedSubspace.ambientGenericPoint_closureImage_eq D.site D.base D.base_mem
        hW.1 hW'.1 _ q Z
    have hδζ : D.deltaValue sW' (pointsMap D.site D.base D.base_mem W q
        (Z.ambientGenericPoint D.site D.base D.base_mem)) = k := by
      rw [← hζ]
      show deltaDimension D sW' Z' = k
      rw [← himg, hδeq, hδZ]
    have hqz : pointsMap D.site D.base D.base_mem W q
        (Z.ambientGenericPoint D.site D.base D.base_mem) = ξ' := by
      by_contra hne
      have hspec : ξ' ⤳ pointsMap D.site D.base D.base_mem W q
          (Z.ambientGenericPoint D.site D.base D.base_mem) :=
        (isGenericPoint_genericPoint D.site D.base D.base_mem hW'.1 hW'int).specializes
          (Set.mem_univ _)
      have hlt := (deltaDimensionFunction D sW' hW').strictAnti_specializes hspec (Ne.symm hne)
      rw [deltaDimensionFunction_apply, deltaDimensionFunction_apply, hδζ, hW'd] at hlt
      exact lt_irrefl _ hlt
    refine ⟨hζ.trans hqz, ?_⟩
    obtain ⟨v, hv⟩ := hrangeβ (Z.ambientGenericPoint D.site D.base D.base_mem) (by
      rw [hqz]; exact hξ'U)
    refine ⟨v, ?_, ?_⟩
    · exact hlift v (by rw [hv, hqz])
    · exact eq_of_ambientGenericPoint_eq D.site D.base D.base_mem hW.1 hdec (by rw [hΦgen, hv])
  by_cases hZ' : Z'.ambientGenericPoint D.site D.base D.base_mem = ξ'
  swap
  · refine finsum_eq_zero_of_forall_eq_zero fun Z => ?_
    by_contra hZ
    exact hZ' (hK Z hZ).1
  have hsupp : Function.support (fun Z => (c : IntegralClosedSubspace D.site D.base D.base_mem W →
      ℤ) Z * properCycleMult D sW hW sW' hW' q Z Z') ⊆ Φ '' F := fun Z hZ => by
    obtain ⟨-, v, hvF, rfl⟩ := hK Z hZ
    exact ⟨v, hvF, rfl⟩
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq _ Set.univ (Φ '' F)
    (by rw [Set.univ_inter, Set.inter_eq_right.2 hsupp]), finsum_mem_image hΦinj.injOn, ← hsum]
  refine finsum_mem_congr rfl fun v hvF => ?_
  have hvF' : πs v = _root_.genericPoint Ts := hvF
  have hzZ := hΦgen v
  have hqz : pointsMap D.site D.base D.base_mem W q (jV v) = ξ' := by
    rw [← hnat, hvF', hgT]
  have himg : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hW'.1
      (D.isDecentSpace_of_isGood sW' hW') q (Φ v) = Z' := by
    refine eq_of_ambientGenericPoint_eq D.site D.base D.base_mem hW'.1 hdec' ?_
    show (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hW'.1
      (D.isDecentSpace_of_isGood sW' hW') q (Φ v)).ambientGenericPoint D.site D.base D.base_mem =
        Z'.ambientGenericPoint D.site D.base D.base_mem
    rw [IntegralClosedSubspace.ambientGenericPoint_closureImage_eq D.site D.base D.base_mem
      hW.1 hW'.1 _ q (Φ v), hzZ, hqz, hZ']
  by_cases hvg : v = _root_.genericPoint Vs
  · have hcZ : (c : IntegralClosedSubspace D.site D.base D.base_mem W → ℤ) (Φ v) = 0 := by
      by_contra hne
      have h1 := c.2.2 (Φ v) hne
      have h2 : deltaDimension D sW (Φ v) = k + 1 := by
        show D.deltaValue sW ((Φ v).ambientGenericPoint D.site D.base D.base_mem) = _
        rw [hzZ, hvg, hgV]
        exact hWd
      omega
    have hord : Vs.ord g v = 0 := by
      have hcoh : coheight v ≠ 1 := by
        intro h1
        have h2 := ringKrullDim_stalk_eq_coheight v
        rw [h1, hvg] at h2
        have h3 : ringKrullDim (Vs.presheaf.stalk (_root_.genericPoint Vs)) = 0 :=
          ringKrullDim_eq_zero_of_field Vs.functionField
        rw [h3] at h2
        exact absurd h2 (by decide)
      exact Scheme.ord_eq_zero_of_coheight_neq_one hcoh g
    rw [hcZ, hord, zero_mul, zero_mul]
  have hne : jV v ≠ ξ := fun h => hvg (hjVemb.injective (h.trans hgV.symm))
  have hδz : D.deltaValue sW (jV v) = k := deltaValue_eq_of_pointsMap_eq_genericPoint D sW hW
    hWint sW' hW' hW'int q hq k hWd hW'd (jV v) hqz hne
  have hδZ : deltaDimension D sW (Φ v) = k + 1 - 1 := by
    show D.deltaValue sW ((Φ v).ambientGenericPoint D.site D.base D.base_mem) = _
    rw [hzZ, hδz]
    ring
  have hn : deltaDimensionClosed D sW hW Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) :=
    (deltaDimensionClosed_univ_eq_inducedDimensionValue_genericPoint D sW hW hWint).trans
      (congrArg (fun n : ℤ => (n : EInt)) hWd)
  have hcod : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hW.1 (Φ v)) =
      1 := ((isPrimeDivisor_tfae_of_isIntegralSpace' D sW hW hWint hn (Φ v)).out 2 3).mpr hδZ
  set Z'' := (Φ v).toPrimeDivisor D.site D.base D.base_mem hW.1 hcod
  have hcZ : (c : IntegralClosedSubspace D.site D.base D.base_mem W → ℤ) (Φ v) =
      E.ord hf.unit Z'' := by
    rw [hcf]
    exact dif_pos hcod
  have hgenZ'' : jV v = Z''.genericPoint D.site D.base D.base_mem W := by
    have h1 := Z''.isGenericPoint_genericPoint D.site D.base D.base_mem W
    have h2 := (Φ v).isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hW.1
    rw [hzZ] at h2
    exact h2.eq h1
  have hcoh : coheight v = 1 := by
    rw [coheight_eq_codimension_pointsMap D.site D.base D.base_mem hW.1 β hβ hdec v]
    have hcl : IrreducibleCloseds.closureSingleton (jV v) =
        integralClosedSubspaceSupport D.site D.base D.base_mem hW.1 (Φ v) := by
      refine IrreducibleCloseds.ext ?_
      have h2 := (Φ v).isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hW.1
      rw [hzZ] at h2
      exact h2
    exact (congrArg codimension hcl).trans hcod
  have hord := PrimeDivisor.ord_eq_scheme_ord_of_isOpenImmersion D.site D.base D.base_mem hW.1 β
    hβ hWint hN hWint.isDecentSpace Z'' v hgenZ'' hcoh hf.unit g (fun U hU w => hg U hU w)
  have hu : pointsMap D.site D.base D.base_mem (yoneda.obj Vo) β
      ((schemePointRepresentative D.site D.base D.base_mem Vo v).class D.site D.base D.base_mem
        (yoneda.obj Vo)) = (Φ v).ambientGenericPoint D.site D.base D.base_mem := by
    rw [hzZ]
    have hcl : (schemePointRepresentative D.site D.base D.base_mem Vo v).class D.site D.base
        D.base_mem (yoneda.obj Vo) = (pointsEquivScheme D.site D.base D.base_mem Vo).symm v := by
      have := class_schemePointRepresentative_pointsToScheme D.site D.base D.base_mem Vo
        ((pointsEquivScheme D.site D.base D.base_mem Vo).symm v)
      rwa [show pointsToScheme D.site D.base D.base_mem Vo
          ((pointsEquivScheme D.site D.base D.base_mem Vo).symm v) = v from
        (pointsEquivScheme D.site D.base D.base_mem Vo).apply_symm_apply v] at this
    rw [hcl]
    rfl
  have hfd : functionFieldDegree D sW hW sW' hW' q (Φ v) = πs.residueDegree v :=
    finrank_residueFieldHom_eq_residueDegree_of_isOpenImmersion D.site D.base D.base_mem hW.1
      hW'.1 (D.isDecentSpace_of_isGood sW hW) (D.isDecentSpace_of_isGood sW' hW') q
      ((Φ v).ambientGenericPoint D.site D.base D.base_mem) Vo To β α hβ hα π hcomm v hu
  have hmult : properCycleMult D sW hW sW' hW' q (Φ v) Z' = (πs.residueDegree v : ℤ) := by
    have hδ' : deltaDimension D sW' (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
        hW'.1 (D.isDecentSpace_of_isGood sW' hW') q (Φ v)) = deltaDimension D sW (Φ v) := by
      rw [himg, hδZ]
      show D.deltaValue sW' (Z'.ambientGenericPoint D.site D.base D.base_mem) = _
      rw [hZ', hW'd]
      ring
    rw [properCycleMult, if_pos himg, properCycleDegree, if_pos hδ', hfd]
  rw [hcZ, hmult, hord]

end DimensionDrop

end AlgebraicGeometry.Space

end
