module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.StalkBasis
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtensionInvertibleGlobal
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TensorSection
public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimensionTwoOpen
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericStalkGenerator

/-!
# Restriction of a regular meromorphic section to an open subscheme

Let `j : U ⟶ X` be a dominant open immersion of integral locally Noetherian schemes and `L` an
invertible `𝒪_X`-module.  A meromorphic section of `L` is one element of the stalk `L_η` at the
generic point, by [Stacks, Tag 01X5] part (2), and the stalk of `L|_U` at the generic point of
`U` is that same stalk.  So a meromorphic section of `L` restricts to one of `L|_U`, and the
order of vanishing is unchanged: the order is read off a generator of the stalk of `L` at the
generic point of a prime divisor and the order in the local ring there of the resulting
coordinate, and an open immersion changes neither.

## Main definitions

* `AlgebraicGeometry.genericStalkRestrictAddEquiv` — the identification
  `(L|_U)_{η_U} ≃+ L_{η_X}` of generic stalks.
* `AlgebraicGeometry.restrictMeromorphicSection` — the restriction of a meromorphic section.

## Main results

* `AlgebraicGeometry.orderOfVanishingMeromorphic_restrict` — the order of vanishing of
  [Stacks, Tag 02SF] is unchanged by restriction.
* `AlgebraicGeometry.weilDivisorOfMeromorphicSection_restrict` and
  `AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_restrict` — the Weil divisor of
  [Stacks, Tag 0BE6] part (1) and the Weil divisor class of part (2) are carried to one another
  by the restriction isomorphisms `Div(X) ≅ Div(U)` and `Cl(X) ≅ Cl(U)` of
  `StacksFrontier/AlgebraicGeometry/Divisors/WeilDivisorClass/CodimensionTwoOpen.lean`, for an open
  subscheme whose complement has codimension at least two.

## Implementation notes

The restriction is built through the generic stalk rather than as a pullback of meromorphic
sections: `AlgebraicGeometry.meromorphicSectionOfGenericStalk` turns an element of `L_η` into a
meromorphic section and `AlgebraicGeometry.meromorphicGenericValue` turns it back, and the two
are mutually inverse, so a construction made on the generic stalk comes with its generic value
computed.  That is exactly what the coordinate description of the order of vanishing in
[Stacks, Tag 02SF] reads.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Order TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveEquivalence (openImmersionStalkRingEquiv
  restrictStalkSemilinearEquiv)

universe u

namespace AlgebraicGeometry

/-! ### Generating the generic stalk -/

/-- **The generic value of a regular meromorphic section generates the generic stalk.**  The
stalk of an invertible module at the generic point of an integral scheme has a basis, the
generic value is a multiple of it by a scalar in the function field, and that scalar is nonzero
because the generic value is. -/
theorem span_singleton_meromorphicGenericValue_eq_top (X : Scheme.{u}) [IsIntegral X]
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s) :
    Submodule.span (X.presheaf.stalk (genericPoint X)) {meromorphicGenericValue X L s} = ⊤ := by
  have hq : L.IsQuasicoherent := isQuasicoherent_of_isInvertible L
  obtain ⟨e, he⟩ := exists_isStalkBasis_genericPoint X L
  have hspan : Submodule.span (X.presheaf.stalk (genericPoint X)) {e} = ⊤ :=
    (Stacks.Divisors.isStalkBasis_iff_span_eq_top L (genericPoint X) e).1 he
  have hmem : meromorphicGenericValue X L s ∈
      Submodule.span (X.presheaf.stalk (genericPoint X)) {e} :=
    hspan ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact meromorphicGenericValue_ne_zero X L s hs (by rw [← ha, zero_smul])
  rw [← ha, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 ha0), hspan]

/-! ### The generic stalk of a restriction -/

section Restrict

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [IsIntegral U] [IsIntegral X]

omit [IsIntegral X] in
/-- Scalars on a stalk are transported along an equality of points together with the stalk. -/
theorem stalkCongr_smul (L : X.Modules) {x y : X} (h : x = y) (r : X.presheaf.stalk x)
    (m : L.presheaf.stalk x) :
    (L.presheaf.stalkCongr (Inseparable.of_eq h)).hom (r • m) =
      (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom r •
        (L.presheaf.stalkCongr (Inseparable.of_eq h)).hom m := by
  subst h
  simp [TopCat.Presheaf.stalkCongr_hom]

/-- **The stalk of `L|_U` at the generic point of `U` is the stalk of `L` at the generic point of
`X`.**  An open immersion of integral schemes carries the generic point to the generic point, and
the stalk of a restriction at a point is the stalk of the module at its image. -/
def genericStalkRestrictAddEquiv (L : X.Modules) :
    (L.restrict j).presheaf.stalk (genericPoint U) ≃+ L.presheaf.stalk (genericPoint X) :=
  haveI : RingHomInvPair (openImmersionStalkRingEquiv j (genericPoint U) :
      U.presheaf.stalk (genericPoint U) →+* X.presheaf.stalk (j (genericPoint U)))
      ((openImmersionStalkRingEquiv j (genericPoint U)).symm :
        X.presheaf.stalk (j (genericPoint U)) →+* U.presheaf.stalk (genericPoint U)) :=
    RingHomInvPair.of_ringEquiv _
  haveI : RingHomInvPair ((openImmersionStalkRingEquiv j (genericPoint U)).symm :
      X.presheaf.stalk (j (genericPoint U)) →+* U.presheaf.stalk (genericPoint U))
      (openImmersionStalkRingEquiv j (genericPoint U) :
        U.presheaf.stalk (genericPoint U) →+* X.presheaf.stalk (j (genericPoint U))) :=
    RingHomInvPair.of_ringEquiv_symm _
  (restrictStalkSemilinearEquiv j L (genericPoint U)).toAddEquiv.trans
    (L.presheaf.stalkCongr
      (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion j))).addCommGroupIsoToAddEquiv

/-- `genericStalkRestrictAddEquiv j L` sends `m` to the image of
`restrictStalkSemilinearEquiv j L (genericPoint U) m` under the stalk identification along
`j (genericPoint U) = genericPoint X`. -/
theorem genericStalkRestrictAddEquiv_apply (L : X.Modules)
    (m : (L.restrict j).presheaf.stalk (genericPoint U)) :
    genericStalkRestrictAddEquiv j L m =
      haveI : RingHomInvPair (openImmersionStalkRingEquiv j (genericPoint U) :
          U.presheaf.stalk (genericPoint U) →+* X.presheaf.stalk (j (genericPoint U)))
          ((openImmersionStalkRingEquiv j (genericPoint U)).symm :
            X.presheaf.stalk (j (genericPoint U)) →+* U.presheaf.stalk (genericPoint U)) :=
        RingHomInvPair.of_ringEquiv _
      haveI : RingHomInvPair ((openImmersionStalkRingEquiv j (genericPoint U)).symm :
          X.presheaf.stalk (j (genericPoint U)) →+* U.presheaf.stalk (genericPoint U))
          (openImmersionStalkRingEquiv j (genericPoint U) :
            U.presheaf.stalk (genericPoint U) →+* X.presheaf.stalk (j (genericPoint U))) :=
        RingHomInvPair.of_ringEquiv_symm _
      (L.presheaf.stalkCongr
          (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion j))).hom
        (restrictStalkSemilinearEquiv j L (genericPoint U) m) :=
  rfl

variable [IsDominant j]

/-- The identification of generic stalks of `L` and `L|_U` is semilinear over the identification
of function fields: the composite of the comparison of local rings at the generic point with the
transport to the generic point of `X` undoes the extension of function fields. -/
theorem stalkCongr_openImmersionStalkRingEquiv_functionFieldEquiv (r : X.functionField) :
    (X.presheaf.stalkCongr
          (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion j))).hom
        (openImmersionStalkRingEquiv j (genericPoint U)
          (Stacks.Chow.functionFieldEquiv_openImmersion j r)) = r := by
  have hη : j.base (genericPoint U) = genericPoint X := genericPoint_eq_of_isOpenImmersion j
  have hval : Stacks.Chow.functionFieldEquiv_openImmersion j r =
      (j.stalkMap (genericPoint U)).hom
        ((eqToHom (congrArg X.presheaf.stalk hη.symm)).hom r) := by
    change dominantFunctionFieldMap j r = _
    change (hη ▸ j.stalkMap (genericPoint U)).hom r = _
    rw [Stacks.Chow.stalkMap_cast_target j (genericPoint U) hη, CommRingCat.comp_apply,
      Stacks.Chow.stalkCongr_eq_eqToHom hη.symm]
  rw [hval]
  have hinv := ConcreteCategory.congr_hom (IsIso.hom_inv_id (j.stalkMap (genericPoint U)))
    ((eqToHom (congrArg X.presheaf.stalk hη.symm)).hom r)
  change (X.presheaf.stalkCongr (Inseparable.of_eq hη)).hom
    ((inv (j.stalkMap (genericPoint U))).hom
      ((j.stalkMap (genericPoint U)).hom
        ((eqToHom (congrArg X.presheaf.stalk hη.symm)).hom r))) = r
  simp only [CommRingCat.comp_apply, CommRingCat.id_apply] at hinv
  rw [hinv, Stacks.Chow.eqToHom_stalkCongr X.presheaf hη.symm]
  exact ConcreteCategory.congr_hom
    (Iso.inv_hom_id (X.presheaf.stalkCongr (Inseparable.of_eq hη))) r

/-- **The identification of generic stalks is semilinear** over the identification of function
fields of [Stacks, Tag 02JU] along a dominant open immersion. -/
theorem genericStalkRestrictAddEquiv_smul (L : X.Modules) (r : X.functionField)
    (m : (L.restrict j).presheaf.stalk (genericPoint U)) :
    genericStalkRestrictAddEquiv j L (Stacks.Chow.functionFieldEquiv_openImmersion j r • m) =
      r • genericStalkRestrictAddEquiv j L m := by
  have : RingHomInvPair (openImmersionStalkRingEquiv j (genericPoint U) :
      U.presheaf.stalk (genericPoint U) →+* X.presheaf.stalk (j (genericPoint U)))
      ((openImmersionStalkRingEquiv j (genericPoint U)).symm :
        X.presheaf.stalk (j (genericPoint U)) →+* U.presheaf.stalk (genericPoint U)) :=
    RingHomInvPair.of_ringEquiv _
  have : RingHomInvPair ((openImmersionStalkRingEquiv j (genericPoint U)).symm :
      X.presheaf.stalk (j (genericPoint U)) →+* U.presheaf.stalk (genericPoint U))
      (openImmersionStalkRingEquiv j (genericPoint U) :
        U.presheaf.stalk (genericPoint U) →+* X.presheaf.stalk (j (genericPoint U))) :=
    RingHomInvPair.of_ringEquiv_symm _
  have hη : j.base (genericPoint U) = genericPoint X := genericPoint_eq_of_isOpenImmersion j
  rw [genericStalkRestrictAddEquiv_apply, genericStalkRestrictAddEquiv_apply]
  have hs : (restrictStalkSemilinearEquiv j L (genericPoint U))
        (Stacks.Chow.functionFieldEquiv_openImmersion j r • m) =
      openImmersionStalkRingEquiv j (genericPoint U)
          (Stacks.Chow.functionFieldEquiv_openImmersion j r) •
        (restrictStalkSemilinearEquiv j L (genericPoint U)) m :=
    map_smulₛₗ _ _ _
  rw [hs, stalkCongr_smul L hη, stalkCongr_openImmersionStalkRingEquiv_functionFieldEquiv j r]

omit [IsDominant j] in
/-- The identification of generic stalks is compatible with specialization from the generic
point: both sides are the germ of a section over an open neighbourhood. -/
theorem genericStalkRestrictAddEquiv_stalkSpecializes (L : X.Modules) (x : U)
    (m : (L.restrict j).presheaf.stalk x) :
    genericStalkRestrictAddEquiv j L
        ((L.restrict j).presheaf.stalkSpecializes
          ((genericPoint_spec U).specializes trivial) m) =
      L.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)
        (Stacks.AlgebraicGeometry.ReflexiveEquivalence.restrictStalkHom j L x m) := by
  have : RingHomInvPair (openImmersionStalkRingEquiv j (genericPoint U) :
      U.presheaf.stalk (genericPoint U) →+* X.presheaf.stalk (j (genericPoint U)))
      ((openImmersionStalkRingEquiv j (genericPoint U)).symm :
        X.presheaf.stalk (j (genericPoint U)) →+* U.presheaf.stalk (genericPoint U)) :=
    RingHomInvPair.of_ringEquiv _
  have : RingHomInvPair ((openImmersionStalkRingEquiv j (genericPoint U)).symm :
      X.presheaf.stalk (j (genericPoint U)) →+* U.presheaf.stalk (genericPoint U))
      (openImmersionStalkRingEquiv j (genericPoint U) :
        U.presheaf.stalk (genericPoint U) →+* X.presheaf.stalk (j (genericPoint U))) :=
    RingHomInvPair.of_ringEquiv_symm _
  obtain ⟨V, hx, t, rfl⟩ := (L.restrict j).presheaf.exists_germ_eq m
  have hg (y : U) (hy : y ∈ V) :
      Stacks.AlgebraicGeometry.ReflexiveEquivalence.restrictStalkHom j L y
          ((L.restrict j).presheaf.germ V y hy t) =
        L.presheaf.germ (j ''ᵁ V) (j y) (by simpa) t :=
    ConcreteCategory.congr_hom (Scheme.Modules.germ_restrictStalkNatIso_hom_app j y L hy) t
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, genericStalkRestrictAddEquiv_apply]
  change (L.presheaf.stalkCongr
    (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion j))).hom
      (Stacks.AlgebraicGeometry.ReflexiveEquivalence.restrictStalkHom j L (genericPoint U)
        ((L.restrict j).presheaf.germ V (genericPoint U) _ t)) = _
  have hηV : genericPoint U ∈ V :=
    ((genericPoint_spec U).specializes trivial).mem_open V.isOpen hx
  rw [hg, hg, TopCat.Presheaf.stalkCongr_hom]
  exact (ConcreteCategory.congr_hom (L.presheaf.germ_stalkSpecializes
      (U := j ''ᵁ V) (y := j (genericPoint U)) (by simpa using hηV)
      ((genericPoint_spec X).specializes trivial)) t).trans
    (ConcreteCategory.congr_hom (L.presheaf.germ_stalkSpecializes
      (U := j ''ᵁ V) (y := j x) (by simpa using hx)
      ((genericPoint_spec X).specializes trivial)) t).symm

/-- **The rank of the generic stalk is unchanged by restriction to an open subscheme.**  The
generic stalks are identified semilinearly over the identification of function fields. -/
theorem rank_genericStalk_restrict (L : X.Modules) :
    Module.rank (U.presheaf.stalk (genericPoint U))
        ((L.restrict j).presheaf.stalk (genericPoint U)) =
      Module.rank (X.presheaf.stalk (genericPoint X)) (L.presheaf.stalk (genericPoint X)) :=
  rank_eq_of_equiv_equiv (Stacks.Chow.functionFieldEquiv_openImmersion j).symm
    (genericStalkRestrictAddEquiv j L)
    (Stacks.Chow.functionFieldEquiv_openImmersion j).symm.bijective
    (fun r m => by
      have h := genericStalkRestrictAddEquiv_smul j L
        ((Stacks.Chow.functionFieldEquiv_openImmersion j).symm r) m
      rwa [RingEquiv.apply_symm_apply] at h)

/-- **The fibre rank at the generic point is unchanged by restriction to an open subscheme.** -/
theorem fiberRank_genericPoint_restrict (L : X.Modules) [L.IsFiniteType]
    [(L.restrict j).IsFiniteType] :
    Scheme.Modules.fiberRank (L.restrict j) (genericPoint U) =
      Scheme.Modules.fiberRank L (genericPoint X) := by
  rw [Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk,
    Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk]
  unfold Module.finrank
  rw [rank_genericStalk_restrict]

/-! ### Restriction of a meromorphic section -/

/-- The restriction of an invertible module along an open immersion is invertible. -/
instance isInvertible_restrict_openImmersion (L : X.Modules)
    [h : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    SheafOfModules.IsInvertible U.sheaf.obj U.ringCatSheaf.property (L.restrict j) :=
  Stacks.UFDExtensionGlobal.isInvertible_restrict j L h

variable (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The restriction of a meromorphic section** of `L` to `U`: the meromorphic section of
`L|_U` whose generic value corresponds to the generic value of `s`. -/
def restrictMeromorphicSection (s : MeromorphicSection X.sheaf L) :
    MeromorphicSection U.sheaf (L.restrict j) :=
  haveI : L.IsQuasicoherent := isQuasicoherent_of_isInvertible _
  haveI : (L.restrict j).IsQuasicoherent := isQuasicoherent_of_isInvertible _
  meromorphicSectionOfGenericStalk U (L.restrict j)
    ((genericStalkRestrictAddEquiv j L).symm (meromorphicGenericValue X L s))

omit [IsDominant j] in
/-- The generic value of the restriction of a meromorphic section corresponds to the generic
value of the section. -/
theorem meromorphicGenericValue_restrictMeromorphicSection (s : MeromorphicSection X.sheaf L) :
    haveI : L.IsQuasicoherent := isQuasicoherent_of_isInvertible _
    haveI : (L.restrict j).IsQuasicoherent := isQuasicoherent_of_isInvertible _
    meromorphicGenericValue U (L.restrict j) (restrictMeromorphicSection j L s) =
      (genericStalkRestrictAddEquiv j L).symm (meromorphicGenericValue X L s) := by
  have : L.IsQuasicoherent := isQuasicoherent_of_isInvertible _
  have : (L.restrict j).IsQuasicoherent := isQuasicoherent_of_isInvertible _
  exact meromorphicGenericValue_eq U (L.restrict j) _ _
    (meromorphicSectionSheafIsoConstant_meromorphicSectionOfGenericStalk U (L.restrict j) _)

omit [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
/-- A generator of the generic stalk of `L` corresponds to a generator of the generic stalk of
`L|_U`. -/
theorem span_singleton_genericStalkRestrictAddEquiv_symm_eq_top
    (v : L.presheaf.stalk (genericPoint X))
    (hv : Submodule.span (X.presheaf.stalk (genericPoint X)) {v} = ⊤) :
    Submodule.span (U.presheaf.stalk (genericPoint U))
      {(genericStalkRestrictAddEquiv j L).symm v} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff] at hv ⊢
  intro n
  obtain ⟨a, ha⟩ := hv (genericStalkRestrictAddEquiv j L n)
  refine ⟨Stacks.Chow.functionFieldEquiv_openImmersion j a, ?_⟩
  apply (genericStalkRestrictAddEquiv j L).injective
  rw [genericStalkRestrictAddEquiv_smul, AddEquiv.apply_symm_apply, ha]

/-- **The restriction of a regular meromorphic section is regular.** -/
theorem isRegularMeromorphicSection_restrictMeromorphicSection
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s) :
    IsRegularMeromorphicSection U.sheaf (L.restrict j) (restrictMeromorphicSection j L s) := by
  have : L.IsQuasicoherent := isQuasicoherent_of_isInvertible _
  have : (L.restrict j).IsQuasicoherent := isQuasicoherent_of_isInvertible _
  have : SheafOfModules.IsInvertible U.presheaf U.ringCatSheaf.2 (L.restrict j) :=
    isInvertible_restrict_openImmersion j L
  exact isRegularMeromorphicSection_of_span_eq_top_genericPoint U (L.restrict j)
    (span_singleton_genericStalkRestrictAddEquiv_symm_eq_top j L _
      (span_singleton_meromorphicGenericValue_eq_top X L s hs))

/-! ### The order of vanishing is unchanged -/

/-- A generator of a module transports to a generator along a semilinear equivalence. -/
theorem span_singleton_eq_top_of_semilinearEquiv {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (g : M ≃ₛₗ[σ] N) (m : M) (hm : Submodule.span R {m} = ⊤) :
    Submodule.span S {g m} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff] at hm ⊢
  intro n
  obtain ⟨r, hr⟩ := hm (g.symm n)
  exact ⟨σ r, (map_smulₛₗ g r m).symm.trans ((congrArg g hr).trans (g.apply_symm_apply n))⟩

variable [IsLocallyNoetherian U] [IsLocallyNoetherian X]

/-- **The coordinate description of the order of vanishing of [Stacks, Tag 02SF]**, with the
generic point of the prime divisor named through an equality. -/
theorem exists_coordinate_orderOfVanishingMeromorphic (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) (Z : PrimeDivisor X) (x : X)
    (hx : Z.genericPoint = x) :
    haveI : L.IsQuasicoherent := isQuasicoherent_of_isInvertible _
    ∃ (m : L.presheaf.stalk x) (a : X.functionField),
      Submodule.span (X.presheaf.stalk x) {m} = ⊤ ∧
      meromorphicGenericValue X L s =
        a • L.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) m ∧
      orderOfVanishingMeromorphic X L s hs Z = X.ord a x := by
  subst hx
  have : L.IsQuasicoherent := isQuasicoherent_of_isInvertible _
  obtain ⟨m, hm, a, ha⟩ := (orderOfVanishingMeromorphicData X L s hs Z).property.1
  exact ⟨m, a, hm, meromorphicGenericValue_eq X L s _ ha,
    (orderOfVanishingMeromorphicData X L s hs Z).property.2 m hm a ha⟩

/-- **The order of vanishing of [Stacks, Tag 02SF] is unchanged by restriction to an open
subscheme.**  A generator of the stalk of `L` at the generic point of a prime divisor of `X`
corresponds to a generator of the stalk of `L|_U` at the generic point of the matching prime
divisor of `U`, the coordinate of the restricted section with respect to it is the restriction
of the coordinate, and the order of a rational function is unchanged by restriction. -/
theorem orderOfVanishingMeromorphic_restrict (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) (Z : PrimeDivisor X) (W : PrimeDivisor U)
    (hZW : Z.genericPoint = j W.genericPoint) :
    orderOfVanishingMeromorphic U (L.restrict j) (restrictMeromorphicSection j L s)
        (isRegularMeromorphicSection_restrictMeromorphicSection j L s hs) W =
      orderOfVanishingMeromorphic X L s hs Z := by
  have : L.IsQuasicoherent := isQuasicoherent_of_isInvertible _
  have : (L.restrict j).IsQuasicoherent := isQuasicoherent_of_isInvertible _
  have : RingHomInvPair (openImmersionStalkRingEquiv j W.genericPoint :
      U.presheaf.stalk W.genericPoint →+* X.presheaf.stalk (j W.genericPoint))
      ((openImmersionStalkRingEquiv j W.genericPoint).symm :
        X.presheaf.stalk (j W.genericPoint) →+* U.presheaf.stalk W.genericPoint) :=
    RingHomInvPair.of_ringEquiv _
  have : RingHomInvPair ((openImmersionStalkRingEquiv j W.genericPoint).symm :
      X.presheaf.stalk (j W.genericPoint) →+* U.presheaf.stalk W.genericPoint)
      (openImmersionStalkRingEquiv j W.genericPoint :
        U.presheaf.stalk W.genericPoint →+* X.presheaf.stalk (j W.genericPoint)) :=
    RingHomInvPair.of_ringEquiv_symm _
  obtain ⟨m, a, hm, ha, hord⟩ :=
    exists_coordinate_orderOfVanishingMeromorphic L s hs Z _ hZW
  set f := restrictStalkSemilinearEquiv j L W.genericPoint
  set n := f.symm m
  have hn : Submodule.span (U.presheaf.stalk W.genericPoint) {n} = ⊤ :=
    span_singleton_eq_top_of_semilinearEquiv f.symm m hm
  have htval := meromorphicSectionSheafIsoConstant_meromorphicSectionOfGenericStalk U
    (L.restrict j) ((genericStalkRestrictAddEquiv j L).symm (meromorphicGenericValue X L s))
  have hnval : (genericStalkRestrictAddEquiv j L).symm (meromorphicGenericValue X L s) =
      Stacks.Chow.functionFieldEquiv_openImmersion j a •
        (L.restrict j).presheaf.stalkSpecializes
          ((genericPoint_spec U).specializes trivial) n := by
    apply (genericStalkRestrictAddEquiv j L).injective
    rw [AddEquiv.apply_symm_apply, genericStalkRestrictAddEquiv_smul,
      genericStalkRestrictAddEquiv_stalkSpecializes]
    change meromorphicGenericValue X L s =
      a • L.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) (f (f.symm m))
    rwa [f.apply_symm_apply]
  have hh := (orderOfVanishingMeromorphicData U (L.restrict j)
    (restrictMeromorphicSection j L s)
    (isRegularMeromorphicSection_restrictMeromorphicSection j L s hs) W).property.2
      n hn (Stacks.Chow.functionFieldEquiv_openImmersion j a)
      (htval.trans (congrArg _ hnval))
  exact hh.trans
    ((Stacks.Chow.ord_functionFieldEquiv_openImmersion j a W.genericPoint).trans hord.symm)

end Restrict

/-! ### The Weil divisor and its class on an open with codimension two complement -/

section CodimensionTwo

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
  (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
  (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

include hU

/-- **The Weil divisor of a regular meromorphic section restricts to the Weil divisor of the
restricted section**, under the isomorphism `Div(X) ≅ Div(U)` of [Stacks, Tag 0EBM]'s proof. -/
theorem weilDivisorOfMeromorphicSection_restrict (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    haveI : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
    haveI : IsDominant U.ι := isDominant_opensι (U := U)
    haveI : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
    weilDivisorRestrictEquiv U hU (weilDivisorOfMeromorphicSection X L s hs) =
      weilDivisorOfMeromorphicSection U.toScheme (L.restrict U.ι)
        (restrictMeromorphicSection U.ι L s)
        (isRegularMeromorphicSection_restrictMeromorphicSection U.ι L s hs) := by
  have : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  have : IsDominant U.ι := isDominant_opensι (U := U)
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  apply Subtype.ext
  funext W
  rw [weilDivisorRestrictEquiv_apply_val, weilDivisorOfMeromorphicSection_apply,
    weilDivisorOfMeromorphicSection_apply]
  exact (orderOfVanishingMeromorphic_restrict U.ι L s hs _ W
    (genericPoint_primeDivisorRestrictEquiv_symm U hU W)).symm

/-- **The Weil divisor class of an invertible module is unchanged by restriction to an open
subscheme whose complement has codimension at least two**, under the isomorphism
`Cl(X) ≅ Cl(U)`.  This is the independence clause the proof of [Stacks, Tag 0EBM] needs in order
to read the class of a rank one coherent reflexive module off its restriction. -/
theorem weilDivisorClassOfInvertibleSheaf_restrict :
    haveI : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
    haveI : IsDominant U.ι := isDominant_opensι (U := U)
    haveI : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
    weilDivisorClassRestrictEquiv U hU (weilDivisorClassOfInvertibleSheaf X L) =
      weilDivisorClassOfInvertibleSheaf U.toScheme (L.restrict U.ι) := by
  have : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  have : IsDominant U.ι := isDominant_opensι (U := U)
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_isIntegral X L
  rw [weilDivisorClassOfInvertibleSheaf_eq X L s hs,
    weilDivisorClassOfInvertibleSheaf_eq U.toScheme (L.restrict U.ι)
      (restrictMeromorphicSection U.ι L s)
      (isRegularMeromorphicSection_restrictMeromorphicSection U.ι L s hs),
    ← weilDivisorOfMeromorphicSection_restrict U hU L s hs, weilDivisorClassRestrictEquiv_mk]

end CodimensionTwo

end AlgebraicGeometry

end
