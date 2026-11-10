module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.PrincipalCycle
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.ClosedCoverExactSequence
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.ReducedSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPlusStrictlyFull
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SchemeImageDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardFirstChernCapCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafCycle

/-!
# Pushing principal divisors forward on a represented space

Let `U` be a scheme of the big fppf site and `h_U` the algebraic space it represents, good over
the base `B` of Situation 0EDT, and let `(C.S, δ)` be a base situation of Chapter 42 with a
morphism `s₀ : U → C.S` locally of finite type. This file compares the summands of the two
notions of rational equivalence, Stacks 0EQ6 for `h_U` and Stacks 02RW for `U`.

An integral closed subspace `W ⊆ h_U` is represented: it is the range of a closed immersion of
schemes `j : R → U`, Stacks 03MB, and `h_R ≅ W` over `h_U`. The scheme `R` is integral, because
reducedness is étale local and the point space of `h_R` is that of `R`, and `j` carries the
generic point of `R` to the generic point of `W`; so `R` is isomorphic over `U` to the integral
closed subscheme `V ⊆ U` with that generic point, Stacks 01J3. Along these identifications

* the isomorphism `h_R ≅ W` carries `div(f)` to `div` of the transported rational function, at
  the canonical embeddings of Stacks 0ENK
  (`AlgebraicGeometry.Space.cycleClosedPushforward_principalDivisorCycleCoefficients_of_iso`);
* `div(f)` on `h_R` is the principal divisor of the reading of `f` on `R`
  (`AlgebraicGeometry.Space.principalDivisorCycleCoefficients_eq_principalCycle`);
* pushforward along `h_j` of families of coefficients is the pushforward `j_*` of cycles of
  Stacks 02R4, the weights being one along a closed immersion;
* the isomorphism `R ≅ V` carries the principal divisor on `R` to the one on `V`.

Hence the pushforward to `h_U` of a principal divisor on `W` is the pushforward to `U` of a
principal divisor on `V`, and conversely.

## Main results

* `AlgebraicGeometry.Space.exists_iso_yoneda_of_eq_range`: a subfunctor of `h_U` which is the
  range of `h_j` for a closed immersion of schemes `j : R → U` is isomorphic to `h_R` over `h_U`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.exists_iso_yoneda`: an integral closed subspace
  of `h_U` is isomorphic over `h_U` to `h_R` for a closed immersion of schemes `R → U`.
* `AlgebraicGeometry.Space.isIntegral_of_iso_integralClosedSubspace`: such an `R` is integral.
* `AlgebraicGeometry.Space.cycleClosedPushforward_yoneda_map_apply`: closed pushforward along
  `h_j` is the pushforward of cycles along `j`.
* `Stacks.Chow.map_principalCycle_eq_map_subschemeι_of_iso`: pushing a principal divisor forward
  along a closed immersion from an integral scheme isomorphic to a closed subscheme `V`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.exists_principalDivisorPushforward_eq` and
  `AlgebraicGeometry.Space.IntegralClosedSubspace.exists_cycleClosedPushforward_eq`: the
  pushforwards of principal divisors on an integral closed subspace `W ⊆ h_U` are the
  pushforwards of principal divisors on the integral closed subscheme of `U` with the same
  generic point.

## References

* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Representing

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The generic point, read in `V`, of the image of an integral closed subspace `Z ⊆ h_U` along
the closed immersion `h_j : h_U → h_V` induced by a morphism of schemes `j` is the image under
`j` of the generic point of `Z`. -/
theorem IntegralClosedSubspace.schemeGenericPoint_pushforward {U V : BigFppfOver B S hS}
    (j : U ⟶ V) (hj : IsClosedImmersion B S hS (yoneda.map j))
    (Z : IntegralClosedSubspace B S hS (yoneda.obj U)) :
    (IntegralClosedSubspace.pushforward B S hS (isAlgebraicSpace_yoneda B S hS V)
        (isAlgebraicSpace_yoneda B S hS U) (isDecentSpace_yoneda B S hS V) hj Z).schemeGenericPoint
          B S hS V =
      (BigFppfOver.toScheme B S hS).map j (Z.schemeGenericPoint B S hS U) := by
  rw [IntegralClosedSubspace.schemeGenericPoint_eq_pointsToScheme,
    IntegralClosedSubspace.ambientGenericPoint_pushforward B S hS
      (isAlgebraicSpace_yoneda B S hS V) (isAlgebraicSpace_yoneda B S hS U),
      pointsToScheme_pointsMap]
  rfl

/-- **A closed subspace of `h_U` cut out by a closed immersion of schemes is represented by its
source.** If a subfunctor `Y` of `h_U` is the range of `h_j` for a morphism of schemes `j : R → U`
of the site which is a closed immersion, then `h_R ≅ Y` over `h_U`: `h_j` is a monomorphism, and
its corestriction to its range is bijective at every object. -/
theorem exists_iso_yoneda_of_eq_range {R U : BigFppfOver B S hS} (j : R ⟶ U)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (Y : Subfunctor (yoneda.obj U)) (hY : Y = Subfunctor.range (yoneda.map j)) :
    ∃ e : yoneda.obj R ≅ Y.toFunctor, e.hom ≫ Y.ι = yoneda.map j := by
  have hmono : Mono (yoneda.map j) := mono_yoneda_map_of_mono_toScheme_map B S hS j
    (inferInstanceAs (Mono ((BigFppfOver.toScheme B S hS).map j)))
  let φ : yoneda.obj R ⟶ Y.toFunctor := Subfunctor.lift (yoneda.map j) hY.symm.le
  have hφ : φ ≫ Y.ι = yoneda.map j := Subfunctor.lift_ι _ _
  have : IsIso φ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro T
    rw [isIso_iff_bijective]
    refine ⟨fun a b hab => ?_, fun y => ?_⟩
    · have hinj := (NatTrans.mono_iff_mono_app (yoneda.map j)).1 hmono T
      rw [mono_iff_injective] at hinj
      exact hinj (congrArg Subtype.val hab)
    · obtain ⟨a, ha⟩ : y.1 ∈ (Subfunctor.range (yoneda.map j)).obj T := hY ▸ y.2
      exact ⟨a, Subtype.ext ha⟩
  exact ⟨asIso φ, hφ⟩

/-- **An integral closed subspace of a represented space is represented.** An integral closed
subspace `W` of `h_U` is the range of `h_j` for a morphism of schemes `j : R → U` of the site
which is a closed immersion, Stacks 03MB, and `h_R ≅ W` over `h_U`. -/
theorem IntegralClosedSubspace.exists_iso_yoneda {U : BigFppfOver B S hS}
    (W : IntegralClosedSubspace B S hS (yoneda.obj U)) :
    ∃ (R : BigFppfOver B S hS) (j : R ⟶ U) (e : yoneda.obj R ≅ W.subspace.toFunctor),
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
        W.subspace = Subfunctor.range (yoneda.map j) ∧ e.hom ≫ W.subspace.ι = yoneda.map j := by
  obtain ⟨R, j, hj, hW⟩ := exists_closedImmersion_range B S hS W.subspace W.isClosedSubspace
  have := hj
  obtain ⟨e, he⟩ := exists_iso_yoneda_of_eq_range B S hS j W.subspace hW
  exact ⟨R, j, e, hj, hW, he⟩

variable {B S hS}

/-- A scheme `R` of the site whose represented space is isomorphic to an integral closed
subspace of an algebraic space is integral: reducedness is étale local, Stacks 03E8, and the
point space of `h_R` is that of `R`. -/
theorem isIntegral_of_iso_integralClosedSubspace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (W : IntegralClosedSubspace B S hS X) {R : BigFppfOver B S hS}
    (e : yoneda.obj R ≅ W.subspace.toFunctor) :
    IsIntegral ((BigFppfOver.toScheme B S hS).obj R) := by
  have hred : IsReduced ((BigFppfOver.toScheme B S hS).obj R) :=
    (exists_atlas_iff_of_representable B S hS (yoneda.obj R) (fun T : Scheme.{u} => IsReduced T)
      R (Iso.refl _)).1 (hasEtaleLocalProperty_of_iso B S hS _ e.symm W.isIntegralSpace.1)
  have hirr : IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj R) :=
    (schemePointsHomeomorph B S hS R).irreducibleSpace_iff.1
      ((pointsHomeomorphOfIso B S hS e).irreducibleSpace_iff.2 W.isIntegralSpace.2.2)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Under an isomorphism `h_R ≅ W` over `h_U` with `W ⊆ h_U` an integral closed subspace, the
closed immersion `j : R → U` carries the generic point of `R` to the generic point of `W`. -/
theorem IntegralClosedSubspace.map_genericPoint_eq_schemeGenericPoint {U : BigFppfOver B S hS}
    (W : IntegralClosedSubspace B S hS (yoneda.obj U)) {R : BigFppfOver B S hS} (j : R ⟶ U)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [IsIntegral ((BigFppfOver.toScheme B S hS).obj R)]
    (e : yoneda.obj R ≅ W.subspace.toFunctor) (he : e.hom ≫ W.subspace.ι = yoneda.map j) :
    (BigFppfOver.toScheme B S hS).map j
        (_root_.genericPoint ((BigFppfOver.toScheme B S hS).obj R)) =
      W.schemeGenericPoint B S hS U := by
  have himage : pointsToScheme B S hS U '' subspacePointSet B S hS (yoneda.obj U) W.subspace =
      Set.range ((BigFppfOver.toScheme B S hS).map j) := by
    have hrange : subspacePointSet B S hS (yoneda.obj U) W.subspace =
        Set.range (pointsMap B S hS (yoneda.obj R) (yoneda.map j)) := by
      rw [← he, pointsMap_comp, Set.range_comp,
        (bijective_pointsMap_of_isIso B S hS e.hom).2.range_eq, Set.image_univ]
    rw [hrange, ← Set.range_comp]
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨pointsToScheme B S hS R p, (pointsToScheme_pointsMap B S hS j p).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨p, rfl⟩ := (pointsEquivScheme B S hS R).surjective y
      exact ⟨p, pointsToScheme_pointsMap B S hS j p⟩
  have h := IntegralClosedSubspace.image_subspacePointSet B S hS U W
  rw [himage, Stacks.Chow.range_eq_closure_singleton] at h
  exact (inseparable_iff_closure_eq.2 h).eq

end Representing

section Pushforward

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- An algebraic space over a good space `X/B` through a closed immersion `Y → X` is good. -/
theorem isGood_comp_of_isClosedImmersion (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    {i : Y ⟶ X} (hi : IsClosedImmersion D.site D.base D.base_mem i) (sX : X ⟶ D.space)
    (hX : D.IsGood sX) : D.IsGood (i ≫ sX) :=
  ⟨hY, isQuasiSeparated_comp D.site D.base D.base_mem hY hX.1 _ _
      (isQuasiSeparated_of_isClosedImmersion D.site D.base D.base_mem hi) hX.2.1,
    isLocallyOfFiniteType_comp D.site D.base D.base_mem hY hX.1 D.isAlgebraicSpace _ _
      (isLocallyOfFiniteType_of_isClosedImmersion D.site D.base D.base_mem _ hi) hX.2.2⟩

/-- **Closed pushforward on represented spaces is closed pushforward of cycles on schemes.** Let
`j : R → U` be a morphism of schemes of the site which is a closed immersion, `C` a scheme
situation with `s₀ : U → C.S` locally of finite type, `c` a cycle on `R` and `β` the family of
coefficients on the integral closed subspaces of `h_R` which is `c` at their generic points. Then
the pushforward of `β` along `h_j` has, at the integral closed subspace of `h_U` corresponding to
a point `x` of `U`, the coefficient at `x` of the pushforward `j_* c` of Stacks 02R4. -/
theorem cycleClosedPushforward_yoneda_map_apply {R U : BigFppfOver D.site D.base D.base_mem}
    (j : R ⟶ U) [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme _ _ _).map j)]
    (hj : IsClosedImmersion D.site D.base D.base_mem (yoneda.map j))
    {C : Stacks.Chow.ChowSituation.{u}} (s₀ : (BigFppfOver.toScheme _ _ _).obj U ⟶ C.S)
    [LocallyOfFiniteType s₀] (c : AlgebraicCycle ((BigFppfOver.toScheme _ _ _).obj R) ℤ)
    (β : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj R) → ℤ)
    (hβ : ∀ y, β ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem R).symm y) =
      c y)
    (x : (BigFppfOver.toScheme D.site D.base D.base_mem).obj U) :
    cycleClosedPushforward D (isAlgebraicSpace_yoneda _ _ _ U) (isAlgebraicSpace_yoneda _ _ _ R)
        (isDecentSpace_yoneda _ _ _ U) hj β
        ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm x) =
      AlgebraicCycle.map ((BigFppfOver.toScheme _ _ _).map j)
        (Stacks.Chow.relativeDimension C.dimensionFunction
          ((BigFppfOver.toScheme _ _ _).map j ≫ s₀))
        (Stacks.Chow.relativeDimension C.dimensionFunction s₀) c x := by
  set j₀ := (BigFppfOver.toScheme D.site D.base D.base_mem).map j
  by_cases hx : x ∈ Set.range j₀
  · obtain ⟨y, rfl⟩ := hx
    have h : (IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm (j₀ y) =
        IntegralClosedSubspace.pushforward D.site D.base D.base_mem
          (isAlgebraicSpace_yoneda _ _ _ U) (isAlgebraicSpace_yoneda _ _ _ R)
          (isDecentSpace_yoneda _ _ _ U) hj
          ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem R).symm y) := by
      rw [Equiv.symm_apply_eq, IntegralClosedSubspace.equivSchemePoints_apply,
        IntegralClosedSubspace.schemeGenericPoint_pushforward,
        IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm]
    rw [h, cycleClosedPushforward_apply_pushforward, hβ,
      Stacks.Chow.algebraicCycle_map_relativeDimension_apply_image C (j₀ ≫ s₀) s₀ j₀ rfl]
  · rw [cycleClosedPushforward_apply_of_forall_ne]
    · change (0 : ℤ) = ∑ᶠ z ∈ j₀.base ⁻¹' {x}, _
      rw [Set.preimage_singleton_eq_empty.2 hx, finsum_mem_empty]
    · intro Z hZ
      apply hx
      refine ⟨Z.schemeGenericPoint D.site D.base D.base_mem R, ?_⟩
      rw [← IntegralClosedSubspace.schemeGenericPoint_pushforward D.site D.base D.base_mem j hj, hZ,
        IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm]

/-- **Pushing a principal divisor forward along a closed immersion from an integral scheme.**
Let `i : Z → X` be a closed immersion with `Z` integral, isomorphic over `X` to the closed
subscheme `V` of `X`. The pushforward along `i` of the principal divisor of a rational function
`f` on `Z` is the pushforward along the inclusion of `V` of the principal divisor of the
transported rational function. -/
theorem _root_.Stacks.Chow.map_principalCycle_eq_map_subschemeι_of_iso
    (C : Stacks.Chow.ChowSituation.{u}) {Z X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] [IsIntegral Z] [IsLocallyNoetherian Z]
    (V : X.IdealSheafData) [IsIntegral V.subscheme] [IsLocallyNoetherian V.subscheme]
    (ε : Z ≅ V.subscheme) (hε : ε.hom ≫ V.subschemeι = i) (f : Z.functionField) :
    AlgebraicCycle.map i (Stacks.Chow.relativeDimension C.dimensionFunction (i ≫ p))
        (Stacks.Chow.relativeDimension C.dimensionFunction p) (Stacks.Chow.principalCycle Z f) =
      AlgebraicCycle.map V.subschemeι
        (Stacks.Chow.relativeDimension C.dimensionFunction (V.subschemeι ≫ p))
        (Stacks.Chow.relativeDimension C.dimensionFunction p)
        (Stacks.Chow.principalCycle V.subscheme (Stacks.Chow.functionFieldRingEquivOfIso ε f)) := by
  have hεs : ε.hom ≫ (V.subschemeι ≫ p) = i ≫ p := by rw [← Category.assoc, hε]
  rw [← Stacks.Chow.algebraicCycle_map_congr hε,
    ← Stacks.Chow.algebraicCycle_map_comp_relativeDimension C (i ≫ p) (V.subschemeι ≫ p) p ε.hom
      V.subschemeι hεs rfl,
    Stacks.Chow.map_principalCycle_of_iso ε _ _ (fun z => (Stacks.Chow.relativeDimension_of_iso
      C.dimensionFunction (i ≫ p) (V.subschemeι ≫ p) ε hεs z).symm)]

variable {D}

/-- **The pushforward of a principal divisor on a represented integral space.** Let `j : R → U`
be a closed immersion of schemes of the site with `R` integral, `h_R → B` good, and `V` an
integral closed subscheme of `U` isomorphic to `R` over `U`. For a unit `f` of `R(h_R)` and a
unit `g` of `R(V)` matched with it through the reading `R(h_R) ≅ R(R)` and the isomorphism
`R ≅ V`, the pushforward along `h_j` of `div(f)`, at the canonical embeddings of Stacks 0ENK, is
the cycle on `U` which is the pushforward of `div(g)` along the inclusion of `V`. -/
theorem cycleClosedPushforward_principalDivisorCycleCoefficients_yoneda_map
    {R U : BigFppfOver D.site D.base D.base_mem} (j : R ⟶ U)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme _ _ _).map j)]
    [IsIntegral ((BigFppfOver.toScheme _ _ _).obj R)]
    (hj : IsClosedImmersion D.site D.base D.base_mem (yoneda.map j))
    (sR : yoneda.obj R ⟶ D.space) (hR : D.IsGood sR)
    {C : Stacks.Chow.ChowSituation.{u}} (s₀ : (BigFppfOver.toScheme _ _ _).obj U ⟶ C.S)
    [LocallyOfFiniteType s₀] (V : ((BigFppfOver.toScheme _ _ _).obj U).IdealSheafData)
    [hV : IsIntegral V.subscheme]
    (ε : (BigFppfOver.toScheme D.site D.base D.base_mem).obj R ≅ V.subscheme)
    (hε : ε.hom ≫ V.subschemeι = (BigFppfOver.toScheme D.site D.base D.base_mem).map j)
    (f : (rationalFunctions D.site D.base D.base_mem (isAlgebraicSpace_yoneda _ _ _ R))ˣ)
    (g : (Stacks.Chow.rationalFunctions V.subscheme)ˣ)
    (hfg : haveI := isLocallyNoetherian_of_isGood_yoneda D sR hR
      (Stacks.Chow.rationalFunctionsEquivFunctionField V.subscheme).1
          (g : Stacks.Chow.rationalFunctions V.subscheme) =
        Stacks.Chow.functionFieldRingEquivOfIso ε (representedFunctionFieldMap _ _ _ R f))
    (x : (BigFppfOver.toScheme D.site D.base D.base_mem).obj U) :
    haveI := isLocallyNoetherian_of_isGood_yoneda D sR hR
    letI E := genericFractionEmbedding D.site D.base D.base_mem hR.1
      (isDecentSpace_yoneda _ _ _ R) (isIntegralSpace_yoneda _ _ _ R)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sR hR)
    letI := E.nontrivial
    letI := E.isNoetherianRing
    letI := E.krullDimLE
    cycleClosedPushforward D (isAlgebraicSpace_yoneda _ _ _ U) hR.1 (isDecentSpace_yoneda _ _ _ U)
        hj (principalDivisorCycleCoefficients D sR hR (isDecentSpace_yoneda _ _ _ R) E.emb
          (f : rationalFunctions _ _ _ hR.1) (fun W => f.isUnit.map (E.emb W)))
        ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm x) =
      Stacks.Chow.principalDivisorPushforward C s₀ V hV g x := by
  have := isLocallyNoetherian_of_isGood_yoneda D sR hR
  have : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ s₀)
  rw [cycleClosedPushforward_yoneda_map_apply D j hj s₀
    (Stacks.Chow.principalCycle _ (representedFunctionFieldMap _ _ _ R f)) _ (fun y => by
      rw [principalDivisorCycleCoefficients_eq_principalCycle D sR hR f,
        IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm])]
  change _ = AlgebraicCycle.map V.subschemeι _ _ _ x
  rw [hfg, Stacks.Chow.map_principalCycle_eq_map_subschemeι_of_iso C s₀ _ V ε hε]

end Pushforward

section IntegralClosedSubspace

variable {D : BaseSpaceDimensionSituation.{u}} {U : BigFppfOver D.site D.base D.base_mem}
    {sX : yoneda.obj U ⟶ D.space} (hX : D.IsGood sX) {C : Stacks.Chow.ChowSituation.{u}}
    (s₀ : (BigFppfOver.toScheme D.site D.base D.base_mem).obj U ⟶ C.S) [LocallyOfFiniteType s₀]

/-- An integral closed subspace `W ⊆ h_U` and the integral closed subscheme `V ⊆ U` with the same
generic point are both represented by a closed immersion of schemes `j : R → U` with `R` integral:
`h_R ≅ W` and `R ≅ V` over `U`, and `h_R` is good. -/
private theorem exists_closedImmersion_iso_subscheme (hX : D.IsGood sX)
    (W : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj U))
    (V : ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).IdealSheafData)
    (hV : IsIntegral V.subscheme)
    (hVW : Stacks.Chow.genericPointOf V hV = W.schemeGenericPoint D.site D.base D.base_mem U) :
    ∃ (R : BigFppfOver D.site D.base D.base_mem) (j : R ⟶ U)
      (e : yoneda.obj R ≅ W.subspace.toFunctor)
      (_ : IsClosedImmersion D.site D.base D.base_mem (yoneda.map j))
      (ε : (BigFppfOver.toScheme D.site D.base D.base_mem).obj R ≅ V.subscheme),
      AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme D.site D.base D.base_mem).map j) ∧
      IsIntegral ((BigFppfOver.toScheme D.site D.base D.base_mem).obj R) ∧
      e.hom ≫ W.subspace.ι = yoneda.map j ∧
      ε.hom ≫ V.subschemeι = (BigFppfOver.toScheme D.site D.base D.base_mem).map j ∧
      D.IsGood (yoneda.map j ≫ sX) := by
  obtain ⟨R, j, e, hj, -, he⟩ := W.exists_iso_yoneda D.site D.base D.base_mem
  have := hj
  have : IsIntegral ((BigFppfOver.toScheme D.site D.base D.base_mem).obj R) :=
    isIntegral_of_iso_integralClosedSubspace W e
  have hj' : IsClosedImmersion D.site D.base D.base_mem (yoneda.map j) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff D.site D.base D.base_mem
      (@AlgebraicGeometry.IsClosedImmersion.{u}) j).2 hj
  have hker : ((BigFppfOver.toScheme D.site D.base D.base_mem).map j).ker = V.subschemeι.ker := by
    rw [Stacks.Chow.ker_eq_integralComponentAt, W.map_genericPoint_eq_schemeGenericPoint j e he,
      ← hVW, Stacks.Chow.integralComponentAt_genericPointOf, V.ker_subschemeι]
  obtain ⟨ε, hε⟩ := Stacks.Chow.exists_iso_of_ker_eq _ V.subschemeι hker
  exact ⟨R, j, e, hj', ε, hj, inferInstance, he, hε,
    isGood_comp_of_isClosedImmersion D (isAlgebraicSpace_yoneda _ _ _ R) hj' sX hX⟩

/-- **Principal divisors on an integral closed subspace of `h_U` are principal divisors on the
corresponding integral closed subscheme of `U`.** Let `W ⊆ h_U` be an integral closed subspace
and `V ⊆ U` the integral closed subscheme with the same generic point. For every unit `f` of
`R(W)` there is a unit `g` of `R(V)` such that the pushforward to `h_U` of `div(f)`, at the
canonical embeddings of Stacks 0ENK, is the pushforward to `U` of `div(g)`, Stacks 02RW. -/
theorem IntegralClosedSubspace.exists_principalDivisorPushforward_eq
    (W : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj U))
    (V : ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).IdealSheafData)
    (hV : IsIntegral V.subscheme)
    (hVW : Stacks.Chow.genericPointOf V hV = W.schemeGenericPoint D.site D.base D.base_mem U)
    (f : rationalFunctions D.site D.base D.base_mem (isGood_integralClosedSubspace D sX hX W).1)
    (hf : IsUnit f) :
    letI E := genericFractionEmbedding D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX W).1 W.isIntegralSpace.isDecentSpace
      W.isIntegralSpace (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
        (isGood_integralClosedSubspace D sX hX W))
    letI := E.nontrivial
    letI := E.isNoetherianRing
    letI := E.krullDimLE
    ∃ g : (Stacks.Chow.rationalFunctions V.subscheme)ˣ, ∀ x,
      cycleClosedPushforward D hX.1 W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX)
          W.isClosedSubspace.2
          (principalDivisorCycleCoefficients D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace.isDecentSpace E.emb f
            fun P => hf.map (E.emb P))
          ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm x) =
        Stacks.Chow.principalDivisorPushforward C s₀ V hV g x := by
  obtain ⟨R, j, e, hj', ε, hj, hRint, he, hε, hR⟩ :=
    exists_closedImmersion_iso_subscheme hX W V hV hVW
  have := hj
  have := hRint
  have := isLocallyNoetherian_of_isGood_yoneda D _ hR
  have hW := isGood_integralClosedSubspace D sX hX W
  have htr := cycleClosedPushforward_principalDivisorCycleCoefficients_of_iso D (W.subspace.ι ≫ sX)
    hW (yoneda.map j ≫ sX) hR W.isIntegralSpace.isDecentSpace (isDecentSpace_yoneda _ _ _ R)
    e.symm W.isIntegralSpace (isIntegralSpace_yoneda _ _ _ R) f hf
  have hf' : IsUnit (rationalFunctionsMapIso hR.1 e.symm f) := hf.map _
  let Ψ := (representedFunctionFieldEquiv D.site D.base D.base_mem R).trans
    ((Stacks.Chow.functionFieldRingEquivOfIso ε).trans
      (Stacks.Chow.rationalFunctionsEquivFunctionField V.subscheme).1.symm)
  refine ⟨Units.map Ψ.toMonoidHom hf'.unit, fun x => ?_⟩
  have hij : e.symm.hom ≫ yoneda.map j = W.subspace.ι := by
    rw [← he, Iso.symm_hom, Iso.inv_hom_id_assoc]
  rw [← cycleClosedPushforward_cycleClosedPushforward D hX.1 hR.1 W.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) (isDecentSpace_yoneda _ _ _ R) hij
    (isClosedImmersion_of_isIso D.site D.base D.base_mem e.symm.hom) hj' W.isClosedSubspace.2, htr]
  exact cycleClosedPushforward_principalDivisorCycleCoefficients_yoneda_map j hj' _ hR s₀ V ε hε
    hf'.unit _ (by
      change (Stacks.Chow.rationalFunctionsEquivFunctionField V.subscheme).1
        (Ψ (rationalFunctionsMapIso hR.1 e.symm f)) = _
      simp only [Ψ, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
      rfl) x

/-- **Principal divisors on an integral closed subscheme of `U` are principal divisors on the
corresponding integral closed subspace of `h_U`.** Let `V ⊆ U` be an integral closed subscheme and
`W ⊆ h_U` the integral closed subspace with the same generic point. For every unit `g` of `R(V)`
there is a unit `f` of `R(W)` such that the pushforward to `U` of `div(g)`, Stacks 02RW, is the
pushforward to `h_U` of `div(f)`, at the canonical embeddings of Stacks 0ENK. -/
theorem IntegralClosedSubspace.exists_cycleClosedPushforward_eq
    (W : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj U))
    (V : ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).IdealSheafData)
    (hV : IsIntegral V.subscheme)
    (hVW : Stacks.Chow.genericPointOf V hV = W.schemeGenericPoint D.site D.base D.base_mem U)
    (g : (Stacks.Chow.rationalFunctions V.subscheme)ˣ) :
    letI E := genericFractionEmbedding D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX W).1 W.isIntegralSpace.isDecentSpace
      W.isIntegralSpace (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
        (isGood_integralClosedSubspace D sX hX W))
    letI := E.nontrivial
    letI := E.isNoetherianRing
    letI := E.krullDimLE
    ∃ (f : rationalFunctions D.site D.base D.base_mem (isGood_integralClosedSubspace D sX hX W).1)
      (hf : IsUnit f), ∀ x,
      cycleClosedPushforward D hX.1 W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX)
          W.isClosedSubspace.2
          (principalDivisorCycleCoefficients D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace.isDecentSpace E.emb f
            fun P => hf.map (E.emb P))
          ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm x) =
        Stacks.Chow.principalDivisorPushforward C s₀ V hV g x := by
  obtain ⟨R, j, e, hj', ε, hj, hRint, he, hε, hR⟩ :=
    exists_closedImmersion_iso_subscheme hX W V hV hVW
  have := hj
  have := hRint
  have := isLocallyNoetherian_of_isGood_yoneda D _ hR
  have hW := isGood_integralClosedSubspace D sX hX W
  let Ψ := (representedFunctionFieldEquiv D.site D.base D.base_mem R).trans
    ((Stacks.Chow.functionFieldRingEquivOfIso ε).trans
      (Stacks.Chow.rationalFunctionsEquivFunctionField V.subscheme).1.symm)
  let f' := Units.map Ψ.symm.toMonoidHom g
  have htr := cycleClosedPushforward_principalDivisorCycleCoefficients_of_iso D
    (yoneda.map j ≫ sX) hR (W.subspace.ι ≫ sX) hW (isDecentSpace_yoneda _ _ _ R)
    W.isIntegralSpace.isDecentSpace e (isIntegralSpace_yoneda _ _ _ R) W.isIntegralSpace
    (f' : rationalFunctions _ _ _ hR.1) f'.isUnit
  refine ⟨rationalFunctionsMapIso hW.1 e (f' : rationalFunctions _ _ _ hR.1),
    f'.isUnit.map _, fun x => ?_⟩
  rw [← htr, cycleClosedPushforward_cycleClosedPushforward D hX.1 W.isClosedSubspace.1 hR.1
    (D.isDecentSpace_of_isGood sX hX) W.isIntegralSpace.isDecentSpace he
    (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) W.isClosedSubspace.2 hj']
  exact cycleClosedPushforward_principalDivisorCycleCoefficients_yoneda_map j hj' _ hR s₀ V ε hε
    f' g (by
      change _ = Stacks.Chow.functionFieldRingEquivOfIso ε
        (representedFunctionFieldEquiv D.site D.base D.base_mem R (Ψ.symm g))
      simp only [Ψ, RingEquiv.symm_trans_apply, RingEquiv.apply_symm_apply, RingEquiv.symm_symm]) x

end IntegralClosedSubspace

end AlgebraicGeometry.Space

end
