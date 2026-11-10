module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedSectionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedClosedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaCoefficients
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapRuleIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleTrivial
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycleTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardFirstChernCapCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisorComponents

/-!
# The cap product with a first Chern class on a represented space

In Situation 0EDT let `h_Y` be a good algebraic space represented by a scheme `Y` and `ℳ` an
invertible `𝒪_{h_Y}`-module, with reading `ℳ_Y` on `Y`. The cycles of `h_Y` and of `Y` are
identified by `AlgebraicGeometry.Space.cycleGroupEquivScheme` (Stacks 02QR). This file compares
the cap product `c₁(ℳ) ∩ -` of Stacks 0EQJ on `h_Y`, at the canonical choices, with the cap
product `c₁(ℳ_Y) ∩ -` of Chapter 42 on `Y`.

## Main definitions

* `AlgebraicGeometry.Space.idealSheafSubschemeObject`: the closed subscheme cut out by an ideal
  sheaf, as an object of the site.
* `AlgebraicGeometry.Space.representedFirstChernRule`: a component rule of Chapter 42 on `Y`
  whose component cycles are, up to rational equivalence, those of the canonical rule on `h_Y`.

## Main results

* `AlgebraicGeometry.Space.exists_genericStalk_canonicalDivisorCycleAt_eq`: the Weil divisor of a
  regular meromorphic section on a represented integral space is the scheme Weil divisor of an
  element of the generic stalk.
* `AlgebraicGeometry.Space.exists_iso_yoneda_idealSheafSubschemeObject`: an integral closed
  subspace of `h_Y` is represented by the integral closed subscheme with the same generic point.
* `AlgebraicGeometry.Space.mk_cycleGroupEquivScheme_firstChernCapCycleMap`: **the class in
  `A_k(Y)` of `c₁(ℳ) ∩ β` is `c₁(ℳ_Y) ∩ β`.**

## References

* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Order

universe u

/-! ### The order of vanishing along an isomorphism of modules -/

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {L L' : X.Modules}

/-- The map on stalks induced by a morphism of `𝒪_X`-modules. -/
def Hom.stalkMap (φ : L ⟶ L') (x : X) : L.presheaf.stalk x → L'.presheaf.stalk x :=
  fun m => ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf).hom m

/-- The stalk map of a morphism of modules sends germs to germs of the image sections. -/
private theorem Hom.stalkMap_germ (φ : L ⟶ L') {U : X.Opens} {x : X} (hx : x ∈ U)
    (s : Γ(L, U)) :
    φ.stalkMap x (L.presheaf.germ U x hx s) = L'.presheaf.germ U x hx (φ.app U s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx φ.mapPresheaf s

/-- The stalk map of a morphism of `𝒪_X`-modules is linear over the local ring. -/
theorem Hom.stalkMap_smul (φ : L ⟶ L') (x : X) (r : X.presheaf.stalk x)
    (m : L.presheaf.stalk x) : φ.stalkMap x (r • m) = r • φ.stalkMap x m := by
  obtain ⟨U, hxU, ρ, hρ⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, t, ht⟩ := L.presheaf.exists_le_germ_eq m hxU
  have hρ' : X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hVU).op ρ) = r := by
    rw [← hρ]; exact X.presheaf.germ_res_apply _ x hxV ρ
  rw [← ht, ← hρ', ← germ_smul L hxV, Hom.stalkMap_germ, Hom.stalkMap_germ, Hom.app_smul,
    germ_smul L']

/-- The stalk map of an isomorphism is bijective. -/
theorem Hom.bijective_stalkMap (φ : L ≅ L') (x : X) : Function.Bijective (φ.hom.stalkMap x) :=
  have : IsIso φ.hom.mapPresheaf := inferInstanceAs (IsIso ((toPresheaf X).map φ.hom))
  ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.hom.mapPresheaf)

/-- The stalk maps of a morphism of modules commute with specialization. -/
theorem Hom.stalkMap_stalkSpecializes (φ : L ⟶ L') {x y : X} (h : x ⤳ y)
    (m : L.presheaf.stalk y) :
    φ.stalkMap x (L.presheaf.stalkSpecializes h m) =
      L'.presheaf.stalkSpecializes h (φ.stalkMap y m) :=
  congrArg (fun f => (ConcreteCategory.hom f) m)
    (TopCat.Presheaf.stalkSpecializes_stalkFunctor_map φ.mapPresheaf h)

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Divisors

variable {X : AlgebraicGeometry.Scheme.{u}} {L L' : X.Modules}

/-- A stalk basis is carried to a stalk basis by an isomorphism of modules. -/
theorem IsStalkBasis.map_iso (φ : L ≅ L') {x : X} {m : L.presheaf.stalk x}
    (hm : IsStalkBasis L x m) : IsStalkBasis L' x (φ.hom.stalkMap x m) := by
  have hfun : (fun r : X.presheaf.stalk x => r • φ.hom.stalkMap x m) =
      φ.hom.stalkMap x ∘ fun r : X.presheaf.stalk x => r • m :=
    funext fun r => (φ.hom.stalkMap_smul x r m).symm
  unfold IsStalkBasis
  rw [hfun]
  exact (AlgebraicGeometry.Scheme.Modules.Hom.bijective_stalkMap φ x).comp hm

/-- Trivializations are carried along an isomorphism of modules. -/
theorem IsTrivializedNear.map_iso (φ : L ≅ L') {x : X} (h : IsTrivializedNear L x) :
    IsTrivializedNear L' x := by
  obtain ⟨W, hxW, t, ht⟩ := h
  refine ⟨W, hxW, φ.hom.app W t, fun y hy => ?_⟩
  have := (ht y hy).map_iso φ
  rwa [AlgebraicGeometry.Scheme.Modules.Hom.stalkMap_germ] at this

variable [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]

/-- **The order of vanishing is unchanged by an isomorphism of modules.** -/
theorem orderOfVanishing_map_iso (φ : L ≅ L') (s : L.presheaf.stalk (genericPoint X))
    {Z : PrimeDivisor X} (hL : IsTrivializedNear L Z.genericPoint) :
    orderOfVanishing L' (φ.hom.stalkMap (genericPoint X) s) Z = orderOfVanishing L s Z := by
  obtain ⟨a, m, hm, hs⟩ := exists_isCoordinateAt hL s
  rw [orderOfVanishing_eq hL ⟨m, hm, hs⟩]
  refine orderOfVanishing_eq (hL.map_iso φ) ⟨_, hm.map_iso φ, ?_⟩
  rw [hs, AlgebraicGeometry.Scheme.Modules.Hom.stalkMap_smul, toGenericStalk, toGenericStalk,
    AlgebraicGeometry.Scheme.Modules.Hom.stalkMap_stalkSpecializes]

end Stacks.Divisors

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The Weil divisor of a meromorphic section on a represented integral space -/

section Divisor

variable (D : BaseSpaceDimensionSituation.{u}) {R : BigFppfOver D.site D.base D.base_mem}
    (sR : yoneda.obj R ⟶ D.space) (hR : D.IsGood sR)
    [IsIntegral ((BigFppfOver.toScheme D.site D.base D.base_mem).obj R)]
    (L : Modules.{u, u} D.site D.base D.base_mem (yoneda.obj R) hR.1)
    (hL : IsInvertibleModule (B := D.site) ⟨yoneda.obj R, hR.1⟩ L)

/-- **The Weil divisor of a meromorphic section on a represented integral space is the Weil
divisor of its generic value on the scheme.**  Let `h_R → B` be good with `R` integral, `ℒ` an
invertible module on `h_R` and `t` a regular meromorphic section of `ℒ`.  There is a nonzero
element `θ` of the generic stalk of the restriction `ℒ_R` of `ℒ` to `R`, a module trivialized
near every point, such that the coefficient of `div_ℒ(t)` of Stacks 0EQE at an integral closed
subspace `Z ⊆ h_R` is the order of vanishing of `θ` (Divisors 02SF) at the generic point of `Z`
when that point has codimension one, and zero otherwise. -/
theorem exists_genericStalk_canonicalDivisorCycleAt_eq
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem (yoneda.obj R) hR.1 L)
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem (yoneda.obj R) hR.1 L t)
    {k : ℤ} (hk : deltaDimensionClosed D sR hR Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    haveI := isLocallyNoetherian_of_isGood_yoneda D sR hR
    ∃ θ : (representedChartRestrictionSheaf D.site D.base D.base_mem R L).presheaf.stalk
        (_root_.genericPoint ((BigFppfOver.toScheme D.site D.base D.base_mem).obj R)),
      θ ≠ 0 ∧
      (∀ x, Stacks.Divisors.IsTrivializedNear
        (representedChartRestrictionSheaf D.site D.base D.base_mem R L) x) ∧
      ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj R),
        (canonicalDivisorCycleAt D sR hR (isIntegralSpace_yoneda _ _ _ R) L hL t ht hk).1 Z =
          if h : coheight (Z.schemeGenericPoint D.site D.base D.base_mem R) = 1 then
            Stacks.Divisors.orderOfVanishing
              (representedChartRestrictionSheaf D.site D.base D.base_mem R L) θ
              (Stacks.Divisors.PrimeDivisor.ofCoheightOne _ h)
          else 0 := by
  have := isLocallyNoetherian_of_isGood_yoneda D sR hR
  obtain ⟨θ, hθ, htriv, hord⟩ := exists_genericStalk_orderOfVanishing_eq D.site D.base
    D.base_mem R (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sR hR) L hL t ht
  refine ⟨θ, hθ, htriv, fun Z => ?_⟩
  have hcod := codimension_integralClosedSubspaceSupport_eq_coheight D.site D.base D.base_mem R Z
  split_ifs with h
  · have hc : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hR.1 Z) = 1 :=
      hcod.trans h
    rw [canonicalDivisorCycleAt_apply_of_codimension_eq_one D sR hR _ L hL t ht hk Z hc]
    set P := Z.toPrimeDivisor D.site D.base D.base_mem hR.1 hc
    have hgen : pointsToScheme D.site D.base D.base_mem R (P.genericPoint _ _ _ _) =
        Z.schemeGenericPoint D.site D.base D.base_mem R := by
      rw [PrimeDivisor.genericPoint_eq_of_isGenericPoint (hX := hR.1)
        (hdec := isDecentSpace_yoneda _ _ _ R) P (isGenericPoint_pointsMap_genericPoint D.site
          D.base D.base_mem hR.1 Z)]
      rfl
    refine (hord P).trans ?_
    congr 1
    exact Stacks.Divisors.PrimeDivisor.genericPoint_injective (by simp [hgen])
  · have hdec := isDecentSpace_of_isGood D sR hR
    have het := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sR hR
    have := fun W : PrimeDivisor D.site D.base D.base_mem (yoneda.obj R) =>
      W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hR.1 hdec
        (isIntegralSpace_yoneda _ _ _ R) het
    have := fun W : PrimeDivisor D.site D.base D.base_mem (yoneda.obj R) =>
      W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hR.1 hdec
        (isIntegralSpace_yoneda _ _ _ R) het
    have := fun W : PrimeDivisor D.site D.base D.base_mem (yoneda.obj R) =>
      W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hR.1 hdec
        (isIntegralSpace_yoneda _ _ _ R) het
    exact divisorCycleCoefficients_of_codimension_ne_one D sR hR hdec L t
      (canonicalLocalRatioFamily D.site D.base D.base_mem hR.1 hdec L hL
        (isIntegralSpace_yoneda _ _ _ R) het) (hcod.trans_ne h)

end Divisor

/-! ### Integral closed subspaces of a represented space as closed subschemes -/

section ClosedSubscheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData)

/-- The closed subscheme cut out of an object `U` of the site by an ideal sheaf, as an object of
the site over `U`. -/
def idealSheafSubschemeObject : BigFppfOver B S hS :=
  Over.mk (⟨V.subschemeι ≫ U.hom.hom⟩ :
    B.obj (Scheme.size_lt_of_isClosedImmersion V.subschemeι U.left.2) ⟶ B.obj hS)

/-- The inclusion of the closed subscheme cut out by an ideal sheaf, as a morphism of the site. -/
def idealSheafSubschemeObjectι : idealSheafSubschemeObject B S hS U V ⟶ U :=
  Over.homMk ⟨V.subschemeι⟩ rfl

/-- The scheme underlying `idealSheafSubschemeObject` is the closed subscheme `V.subscheme`. -/
@[simp]
theorem toScheme_obj_idealSheafSubschemeObject :
    (BigFppfOver.toScheme B S hS).obj (idealSheafSubschemeObject B S hS U V) = V.subscheme :=
  rfl

/-- The morphism of schemes underlying `idealSheafSubschemeObjectι` is `V.subschemeι`. -/
@[simp]
theorem toScheme_map_idealSheafSubschemeObjectι :
    (BigFppfOver.toScheme B S hS).map (idealSheafSubschemeObjectι B S hS U V) = V.subschemeι :=
  rfl

/-- The morphism of schemes underlying `idealSheafSubschemeObjectι` is a closed immersion. -/
instance : AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map (idealSheafSubschemeObjectι B S hS U V)) :=
  inferInstanceAs (AlgebraicGeometry.IsClosedImmersion V.subschemeι)

/-- **An integral closed subspace of `h_U` is represented by the integral closed subscheme with the
same generic point.**  For an ideal sheaf `V` of `U` with integral subscheme, the integral closed
subspace `W` of `h_U` whose generic point is the generic point of `V` is isomorphic over `h_U` to
the algebraic space represented by the closed subscheme `V`. -/
theorem exists_iso_yoneda_idealSheafSubschemeObject [hV : IsIntegral V.subscheme] :
    ∃ e : yoneda.obj (idealSheafSubschemeObject B S hS U V) ≅
        ((IntegralClosedSubspace.equivSchemePoints B S hS U).symm
          (Stacks.Chow.genericPointOf V hV)).subspace.toFunctor,
      e.hom ≫ ((IntegralClosedSubspace.equivSchemePoints B S hS U).symm
          (Stacks.Chow.genericPointOf V hV)).subspace.ι =
        yoneda.map (idealSheafSubschemeObjectι B S hS U V) := by
  set W := (IntegralClosedSubspace.equivSchemePoints B S hS U).symm
    (Stacks.Chow.genericPointOf V hV)
  obtain ⟨R, j, e, hj, -, he⟩ := W.exists_iso_yoneda B S hS
  have := hj
  have : IsIntegral ((BigFppfOver.toScheme B S hS).obj R) :=
    isIntegral_of_iso_integralClosedSubspace W e
  have hker : ((BigFppfOver.toScheme B S hS).map j).ker = V.subschemeι.ker := by
    rw [Stacks.Chow.ker_eq_integralComponentAt, W.map_genericPoint_eq_schemeGenericPoint j e he,
      IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm,
      Stacks.Chow.integralComponentAt_genericPointOf, V.ker_subschemeι]
  obtain ⟨ε, hε⟩ := Stacks.Chow.exists_iso_of_ker_eq _ V.subschemeι hker
  let εs : R ≅ idealSheafSubschemeObject B S hS U V :=
    Over.isoMk (ObjectProperty.isoMk _ ε) (by
      apply ObjectProperty.hom_ext
      change ε.hom ≫ V.subschemeι ≫ U.hom.hom = R.hom.hom
      rw [← Category.assoc, hε]
      exact congrArg (fun f => f.hom) (Over.w j))
  have hεs : εs.hom ≫ idealSheafSubschemeObjectι B S hS U V = j := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hε
  refine ⟨(yoneda.mapIso εs).symm ≪≫ e, ?_⟩
  rw [Iso.trans_hom, Category.assoc, he, Iso.symm_hom, Functor.mapIso_inv, ← Functor.map_comp,
    ← hεs, Iso.inv_hom_id_assoc]

end ClosedSubscheme

/-! ### The component cycle of the cap product on a represented space -/

section Component

variable (D : BaseSpaceDimensionSituation.{u}) {U : BigFppfOver D.site D.base D.base_mem}
    (sQ : yoneda.obj U ⟶ D.space) (hQ : D.IsGood sQ) {C : Stacks.Chow.ChowSituation.{u}}
    (s₀ : (BigFppfOver.toScheme D.site D.base D.base_mem).obj U ⟶ C.S) [LocallyOfFiniteType s₀]
    (hδ : IsDeltaCompatible D U sQ C s₀)
    (M : Modules.{u, u} D.site D.base D.base_mem (yoneda.obj U) hQ.1)
    (hM : IsInvertibleModule (B := D.site) ⟨yoneda.obj U, hQ.1⟩ M)

include hδ in
/-- **The component cycle of the cap product on a represented space is, up to rational
equivalence, the scheme component cycle.**  Let `h_U → B` be good with a δ-compatible scheme
situation `s₀ : U → C.S`, `ℳ` an invertible module on `h_U` and `V` an integral closed subscheme of
`U` of δ-dimension `k + 1`, with `W ⊆ h_U` the integral closed subspace with the same generic
point.  There is a `k`-cycle `c` on `V`, rationally equivalent to the component cycle of the scheme
cap product with the reading `ℳ_U` of `ℳ` on `U` (Stacks 02SO), whose pushforward to `U` is the
component cycle `c₁(ℳ|_W) ∩ [W]` of the cap product of Stacks 0EQJ on `h_U` at the canonical
choices, read on `U`. -/
theorem exists_rationallyEquivalent_firstChernComponentCycleRule
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).sheaf.obj
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).ringCatSheaf.property
      (representedZariskiModule D.site D.base D.base_mem U M)]
    {k : ℤ} (V : ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).IdealSheafData)
    [hV : IsIntegral V.subscheme]
    (hDim : Stacks.Chow.schemeDeltaDimension C (V.subschemeι ≫ s₀) = ((k + 1 : ℤ) : EInt)) :
    ∃ c : Stacks.Chow.CycleGroup C (V.subschemeι ≫ s₀) k,
      Stacks.Chow.RationallyEquivalent C (V.subschemeι ≫ s₀) k c
        (Stacks.Chow.firstChernComponentCycleRule C s₀ k
          (representedZariskiModule D.site D.base D.base_mem U M) V hV hDim) ∧
      ∀ x, AlgebraicCycle.map V.subschemeι
          (Stacks.Chow.relativeDimension C.dimensionFunction (V.subschemeι ≫ s₀))
          (Stacks.Chow.relativeDimension C.dimensionFunction s₀) c.1 x =
        (firstChernComponentCycle D sQ hQ k (canonicalFirstChernRule D sQ hQ M hM k)
          ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm
            (Stacks.Chow.genericPointOf V hV))).1
          ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm x) := by
  set W := (IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm
    (Stacks.Chow.genericPointOf V hV) with hWdef
  set R₀ := idealSheafSubschemeObject D.site D.base D.base_mem U V
  set j₀ := idealSheafSubschemeObjectι D.site D.base D.base_mem U V
  obtain ⟨e₀, he₀⟩ := exists_iso_yoneda_idealSheafSubschemeObject D.site D.base D.base_mem U V
  have hj₀ : IsClosedImmersion D.site D.base D.base_mem (yoneda.map j₀) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff D.site D.base D.base_mem
      (@AlgebraicGeometry.IsClosedImmersion.{u}) j₀).2 inferInstance
  have hR₀ : D.IsGood (yoneda.map j₀ ≫ sQ) :=
    isGood_comp_of_isClosedImmersion D (isAlgebraicSpace_yoneda _ _ _ R₀) hj₀ sQ hQ
  have : IsIntegral ((BigFppfOver.toScheme D.site D.base D.base_mem).obj R₀) := hV
  have hWdim : deltaDimension D sQ W = k + 1 := by
    rw [hδ.deltaDimension_eq, hWdef,
      IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm]
    have h := hDim
    rw [Stacks.Chow.schemeDeltaDimension_subschemeι_comp C s₀ V hV] at h
    exact WithBotTop.coe_injective h
  have hgW := isGood_integralClosedSubspace D sQ hQ W
  let LW := integralClosedSubspaceRestrict D sQ hQ M W
  have hLW := isInvertibleModule_integralClosedSubspaceRestrict D sQ hQ M hM W
  let tW := componentMeromorphicSection sQ hQ (subspaceDivisorSetupOfIsGood D sQ hQ) M hM W
  have htW := isRegularMeromorphicSection_componentMeromorphicSection sQ hQ
    (subspaceDivisorSetupOfIsGood D sQ hQ) M hM W
  let ψ : (⟨yoneda.obj R₀, hR₀.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ≅
      ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩ := ObjectProperty.isoMk _ e₀
  have hf := pullbacksMeromorphicSections_of_iso D.site D.base D.base_mem ψ
  let L₀ := (modulePullback D.site D.base D.base_mem ψ.hom).obj LW
  have hL₀ := modulePullbackInvertible ψ.hom LW hLW
  let t₀ := pullbackMeromorphicSection D.site D.base D.base_mem ψ.hom LW hf tW
  have ht₀ := isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem
    ψ.hom hf LW (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hLW) tW htW
  have hk : deltaDimensionClosed D (W.subspace.ι ≫ sQ) hgW Set.univ isClosed_univ =
      ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sQ hQ W, hWdim]
  have hk₀ : deltaDimensionClosed D (yoneda.map j₀ ≫ sQ) hR₀ Set.univ isClosed_univ =
      ((k + 1 : ℤ) : EInt) :=
    deltaDimensionClosed_univ_eq_of_isEtale D (yoneda.map j₀ ≫ sQ) hR₀ (W.subspace.ι ≫ sQ) hgW
      (by rw [← Category.assoc, he₀]) (isEtale_of_isIso D.site D.base D.base_mem e₀.hom)
      W.isIntegralSpace (isIntegralSpace_yoneda _ _ _ R₀) hk
  obtain ⟨θ, hθ, htriv, hdiv⟩ := exists_genericStalk_canonicalDivisorCycleAt_eq D
    (yoneda.map j₀ ≫ sQ) hR₀ L₀ hL₀ t₀ ht₀ hk₀
  have hMqc : M.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertibleModule ⟨_, hQ.1⟩ M hM
  have hcomp : ψ.hom ≫ closedSubspaceHom D.site D.base D.base_mem hQ.1 W.subspace
      W.isClosedSubspace = representedSpaceMap D.site D.base D.base_mem j₀ :=
    ObjectProperty.hom_ext _ he₀
  let β : L₀ ≅ (modulePullback D.site D.base D.base_mem
      (representedSpaceMap D.site D.base D.base_mem j₀)).obj M :=
    (modulePullbackCompIso D.site D.base D.base_mem ψ.hom
        (closedSubspaceHom D.site D.base D.base_mem hQ.1 W.subspace W.isClosedSubspace)).app M ≪≫
      eqToIso (by rw [hcomp])
  let φ : representedChartRestrictionSheaf D.site D.base D.base_mem R₀ L₀ ≅
      (Scheme.Modules.pullback V.subschemeι).obj
        (representedZariskiModule D.site D.base D.base_mem U M) :=
    (restrictToChartIsoChartRestrictionSheaf D.site D.base D.base_mem _ L₀
        (idEtaleChart D.site D.base D.base_mem R₀)).symm ≪≫
      restrictToChartIsoIdChartRestriction D.site D.base D.base_mem R₀ L₀ ≪≫
      (SmallEtale.restrictModule (associatedBigEtaleSite D.site)
          ((BigFppfOver.toScheme D.site D.base D.base_mem).obj R₀) R₀.left.property).mapIso
        ((representedSmallEtaleModuleEquivalence D.site D.base D.base_mem R₀).inverse.mapIso β) ≪≫
      (representedZariskiModulePullbackIso D.site D.base D.base_mem j₀
        (relativelyRepresentable_yoneda_map D.site D.base D.base_mem j₀) M hMqc).symm
  have : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ s₀)
  have : IsLocallyNoetherian ((BigFppfOver.toScheme D.site D.base D.base_mem).obj R₀) :=
    ‹IsLocallyNoetherian V.subscheme›
  have htriv' : ∀ x, Stacks.Divisors.IsTrivializedNear
      ((Scheme.Modules.pullback V.subschemeι).obj
        (representedZariskiModule D.site D.base D.base_mem U M)) x :=
    fun x => (htriv x).map_iso φ
  have hθ' : φ.hom.stalkMap _ θ ≠ 0 := by
    intro h
    refine hθ ((Scheme.Modules.Hom.bijective_stalkMap φ _).1 (h.trans ?_))
    exact (map_zero ((TopCat.Presheaf.stalkFunctor Ab.{u} _).map φ.hom.mapPresheaf).hom).symm
  refine ⟨Stacks.Chow.chernComponentCycle C (V.subschemeι ≫ s₀) hDim htriv'
    (φ.hom.stalkMap _ θ), ?_, ?_⟩
  · refine (QuotientAddGroup.eq_iff_sub_mem).1 ?_
    rw [← Stacks.Chow.firstChernComponentClass_eq_mk,
      Stacks.Chow.firstChernComponentClass_eq_mk_of_ne_zero C s₀ k _ V hDim hθ']
    rfl
  · intro x
    have hβ : ∀ y, (canonicalDivisorCycleAt D (yoneda.map j₀ ≫ sQ) hR₀
        (isIntegralSpace_yoneda _ _ _ R₀) L₀ hL₀ t₀ ht₀ hk₀).1
        ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem R₀).symm y) =
        (Stacks.Chow.chernComponentCycle C (V.subschemeι ≫ s₀) hDim htriv'
          (φ.hom.stalkMap _ θ)).1 y := by
      intro y
      rw [hdiv, IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm]
      split_ifs with h
      · have h1 := Stacks.Chow.chernComponentCycle_genericPoint C (V.subschemeι ≫ s₀) hDim htriv'
          (φ.hom.stalkMap _ θ) (Stacks.Divisors.PrimeDivisor.ofCoheightOne y h)
        rw [← Stacks.Divisors.orderOfVanishing_map_iso φ θ (htriv _)]
        exact h1.symm.trans
          (congrArg _ (Stacks.Divisors.PrimeDivisor.genericPoint_ofCoheightOne y h))
      · refine (Stacks.Chow.chernComponentCycle_eq_zero C (V.subschemeι ≫ s₀) hDim htriv'
          (φ.hom.stalkMap _ θ) y fun Z hZ => h ?_).symm
        rw [← hZ]
        exact Z.coheight_genericPoint
    rw [firstChernComponentCycle_of_deltaDimension_eq D sQ hQ k _ hWdim]
    refine (cycleClosedPushforward_yoneda_map_apply D j₀ hj₀ s₀ _ _ hβ x).symm.trans ?_
    have hB₂ := cycleClosedPushforward_canonicalDivisorCycle_pullbackMeromorphicSection_of_iso D
      (yoneda.map j₀ ≫ sQ) hR₀ (W.subspace.ι ≫ sQ) hgW (isIntegralSpace_yoneda _ _ _ R₀)
      W.isIntegralSpace ψ LW hLW tW htW hk₀ hk
    have hcc := cycleClosedPushforward_cycleClosedPushforward D hQ.1 W.isClosedSubspace.1 hR₀.1
      (D.isDecentSpace_of_isGood sQ hQ) (isDecentSpace_of_isGood D _ hgW) he₀
      (isClosedImmersion_of_isIso D.site D.base D.base_mem e₀.hom) W.isClosedSubspace.2 hj₀
      (canonicalDivisorCycleAt D (yoneda.map j₀ ≫ sQ) hR₀ (isIntegralSpace_yoneda _ _ _ R₀) L₀
        hL₀ t₀ ht₀ hk₀).1
    exact (congrFun hcc _).symm.trans (congrFun (congrArg _ hB₂) _)

/-- **The component rule of the scheme cap product read off the cap product on `h_U`**: at an
integral closed subscheme `V` of δ-dimension `k + 1` it is a cycle on `V` rationally equivalent to
the component cycle of Stacks 02SO for `ℳ_U`, whose pushforward is the component cycle of the cap
product of Stacks 0EQJ on `h_U` at the corresponding integral closed subspace. -/
def representedFirstChernRule
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).sheaf.obj
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).ringCatSheaf.property
      (representedZariskiModule D.site D.base D.base_mem U M)]
    (k : ℤ) : Stacks.Chow.FirstChernComponentCycleRule C s₀ k := fun V hV hDim =>
  haveI := hV
  (exists_rationallyEquivalent_firstChernComponentCycleRule D sQ hQ s₀ hδ M hM V hDim).choose

/-- The cycle `representedFirstChernRule` at `V` is rationally equivalent to the component cycle
`firstChernComponentCycleRule` of `ℳ_U` at `V`, and its pushforward along `V.subschemeι` is the
component cycle `firstChernComponentCycle` of the cap product on `h_U` at the integral closed
subspace corresponding to the generic point of `V`. -/
theorem representedFirstChernRule_spec
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).sheaf.obj
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).ringCatSheaf.property
      (representedZariskiModule D.site D.base D.base_mem U M)]
    {k : ℤ} (V : ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).IdealSheafData)
    [hV : IsIntegral V.subscheme]
    (hDim : Stacks.Chow.schemeDeltaDimension C (V.subschemeι ≫ s₀) = ((k + 1 : ℤ) : EInt)) :
      Stacks.Chow.RationallyEquivalent C (V.subschemeι ≫ s₀) k
        (representedFirstChernRule D sQ hQ s₀ hδ M hM k V hV hDim)
        (Stacks.Chow.firstChernComponentCycleRule C s₀ k
          (representedZariskiModule D.site D.base D.base_mem U M) V hV hDim) ∧
      ∀ x, AlgebraicCycle.map V.subschemeι
          (Stacks.Chow.relativeDimension C.dimensionFunction (V.subschemeι ≫ s₀))
          (Stacks.Chow.relativeDimension C.dimensionFunction s₀)
          (representedFirstChernRule D sQ hQ s₀ hδ M hM k V hV hDim).1 x =
        (firstChernComponentCycle D sQ hQ k (canonicalFirstChernRule D sQ hQ M hM k)
          ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm
            (Stacks.Chow.genericPointOf V hV))).1
          ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm x) :=
  (exists_rationallyEquivalent_firstChernComponentCycleRule D sQ hQ s₀ hδ M hM V
    hDim).choose_spec

/-- **The cap product with the first Chern class on a represented space is the scheme cap
product.**  Let `h_U → B` be good with a δ-compatible scheme situation `s₀ : U → C.S` and `ℳ` an
invertible module on `h_U` whose reading `ℳ_U` on `U` is invertible.  For every `(k+1)`-cycle `β`
on `h_U` the class in `A_k(U)` of the cap product `c₁(ℳ) ∩ β` of Stacks 0EQJ at the canonical
choices, read on `U` through `Z_k(h_U) ≅ Z_k(U)`, is the cap product `c₁(ℳ_U) ∩ β` of Stacks 02SO
on the scheme. -/
theorem mk_cycleGroupEquivScheme_firstChernCapCycleMap
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).sheaf.obj
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).ringCatSheaf.property
      (representedZariskiModule D.site D.base D.base_mem U M)]
    (k : ℤ) (β : CycleGroup D sQ (k + 1)) :
    (QuotientAddGroup.mk (cycleGroupEquivScheme sQ s₀ hδ k
        (firstChernCapCycleMap D sQ hQ k (canonicalFirstChernRule D sQ hQ M hM k) β)) :
        Stacks.Chow.chowGroup C s₀ k) =
      Stacks.Chow.firstChernClassCapOfInvertible C s₀ k
        (representedZariskiModule D.site D.base D.base_mem U M)
        (cycleGroupEquivScheme sQ s₀ hδ (k + 1) β) := by
  classical
  have hcongr := Stacks.Chow.firstChernClassCap_congr C s₀ k
    (representedFirstChernRule D sQ hQ s₀ hδ M hM k)
    (Stacks.Chow.firstChernComponentCycleRule C s₀ k
      (representedZariskiModule D.site D.base D.base_mem U M))
    (fun V hV hDim => have := hV; (representedFirstChernRule_spec D sQ hQ s₀ hδ M hM V hDim).1)
    (cycleGroupEquivScheme sQ s₀ hδ (k + 1) β)
  refine Eq.trans ?_ hcongr
  change _ = QuotientAddGroup.mk ((Stacks.Chow.firstChernCapRule C s₀ k
    (representedFirstChernRule D sQ hQ s₀ hδ M hM k)).extendCycleGroup
      (cycleGroupEquivScheme sQ s₀ hδ (k + 1) β))
  congr 1
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y => ?_)
  set e := IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U
  rw [Stacks.Chow.IntegralComponentRule.extendCycleGroup_apply,
    Stacks.Chow.ComponentRule.extend_apply, cycleGroupEquivScheme_apply,
    firstChernCapCycleMap_apply, ← finsum_comp_equiv e.symm]
  refine finsum_congr fun x => ?_
  rw [cycleGroupEquivScheme_apply]
  by_cases hβx : β.1 (e.symm x) = 0
  · rw [hβx, zero_mul, zero_mul]
  · congr 1
    have hWd : deltaDimension D sQ (e.symm x) = k + 1 := β.2.2 _ hβx
    have hDim : Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.integralComponentAt x).subschemeι ≫ s₀) = ((k + 1 : ℤ) : EInt) := by
      have h := hδ.deltaDimension_eq (e.symm x)
      rw [IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm] at h
      rw [Stacks.Chow.schemeDeltaDimension_integralComponentAt, ← h, hWd]
    have := Stacks.Chow.isIntegral_integralComponentAt x
    symm
    change (Stacks.Chow.firstChernCapRule C s₀ k
        (representedFirstChernRule D sQ hQ s₀ hδ M hM k)).totalize
          (Stacks.Chow.integralComponentAt x) y = _
    rw [Stacks.Chow.IntegralComponentRule.totalize_eq _ _ inferInstance hDim]
    refine ((representedFirstChernRule_spec D sQ hQ s₀ hδ M hM _ hDim).2 y).trans ?_
    rw [Stacks.Chow.genericPointOf_integralComponentAt]

end Component

end AlgebraicGeometry.Space
