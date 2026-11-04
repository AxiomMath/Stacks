module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleSpecialization.StalkLengths

/-!
# Fibre cycles and the coefficients of specialized cycles over a discrete valuation ring

Comparison of the delta-dimensions of points of the generic and the special fibre over a discrete
valuation ring, the module `F_s` on the fibre over `s`, the dimension of its support and its
cycle `[F_s]_r`, and the coefficients of the cycles of closed subschemes as lengths of quotients
of local rings, used for the specialization formula of Stacks 0H4I.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow.ModuleSpecialization

section DimensionComparison

attribute [local instance] Classical.propDecidable

private lemma eq_genericPoint_or_closedPoint {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (p : Spec (.of R)) :
    p = genericPoint (Spec (.of R)) ∨ p = IsLocalRing.closedPoint R := by
  by_cases hp : p.asIdeal = ⊥
  · left
    exact PrimeSpectrum.ext (by rwa [genericPoint_eq_bot_of_affine])
  · right
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      (p.isPrime.isMaximal_of_ne_bot hp))

private lemma genericPoint_ne_closedPoint (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] :
    genericPoint (Spec (.of R)) ≠ IsLocalRing.closedPoint R := by
  intro h
  have he := congrArg PrimeSpectrum.asIdeal h
  have he' : IsLocalRing.maximalIdeal R = ⊥ := by
    rw [genericPoint_eq_bot_of_affine] at he
    exact he.symm
  exact IsDiscreteValuationRing.not_a_field R he'

private lemma generic_of_specializes_ne {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {x y : Spec (.of R)} (h : x ⤳ y) (hne : x ≠ y) :
    x = genericPoint (Spec (.of R)) ∧ y = IsLocalRing.closedPoint R := by
  rcases eq_genericPoint_or_closedPoint x with hx | hx
  · refine ⟨hx, ?_⟩
    rcases eq_genericPoint_or_closedPoint y with hy | hy
    · exact (hne (hx.trans hy.symm)).elim
    · exact hy
  · have hyx : y ⤳ x := by rw [hx]; exact IsLocalRing.specializes_closedPoint y
    exact (hne ((h.antisymm hyx).eq)).elim

private def dvrDimensionFunction (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : DimensionFunction (Spec (.of R)) where
  toFun p := if p = genericPoint (Spec (.of R)) then 1 else 0
  strictAnti_specializes := by
    intro x y h hne
    obtain ⟨rfl, rfl⟩ := generic_of_specializes_ne h hne
    simp only [ite_eq_right (Ne.symm (genericPoint_ne_closedPoint R))]
    norm_num
  step_immediate := by
    intro x y h
    obtain ⟨rfl, rfl⟩ := generic_of_specializes_ne h.1 h.2.1
    simp only [ite_eq_right (Ne.symm (genericPoint_ne_closedPoint R))]
    norm_num

private lemma relativeDimension_postcomp_surjectiveOnStalks
    {X Y S : Scheme.{u}} (δ : DimensionFunction S) (δY : DimensionFunction Y)
    (i : Y ⟶ S) [SurjectiveOnStalks i] (f : X ⟶ Y) (x : X) :
    relativeDimension δ (f ≫ i) x =
      δ (i (f x)) + relativeDimension δY f x - δY (f x) := by
  let K := S.residueField (i (f x))
  let K' := Y.residueField (f x)
  let L := X.residueField x
  let : Algebra K L := ((f ≫ i).residueFieldMap x).hom.toAlgebra
  let : Algebra K' L := (f.residueFieldMap x).hom.toAlgebra
  let eK : K ≃+* K' := RingEquiv.ofBijective (i.residueFieldMap (f x)).hom
    (i.bijective_residueFieldMap (f x))
  have hmap : ((f ≫ i).residueFieldMap x).hom =
      (f.residueFieldMap x).hom.comp (i.residueFieldMap (f x)).hom := by
    simp only [Scheme.residueFieldMap_comp]
    rfl
  have ht : Algebra.trdeg K L = Algebra.trdeg K' L := by
    refine Algebra.trdeg_eq_of_ringEquiv eK (RingEquiv.refl L) ?_
    intro a
    exact congrArg (fun g ↦ g a) hmap
  change δ (i (f x)) + (Cardinal.toNat (Algebra.trdeg K L) : ℤ) =
    δ (i (f x)) + (δY (f x) + (Cardinal.toNat (Algebra.trdeg K' L) : ℤ)) - δY (f x)
  rw [ht]
  omega

private lemma relativeDimension_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    (δ : DimensionFunction S) (s : S) (x : f.fiber s) :
    relativeDimension δ f (f.fiberι s x) = δ s +
      relativeDimension
        (fieldChowSituation
          (S.residueField s)).dimensionFunction (f.fiberToSpecResidueField s) x := by
  rw [← relativeDimension_comp_of_bijective_residueFieldMap δ (f.fiberι s) f x
    ((f.fiberι s).bijective_residueFieldMap x)]
  have hcomp : f.fiberι s ≫ f =
      f.fiberToSpecResidueField s ≫ S.fromSpecResidueField s := pullback.condition
  rw [hcomp, relativeDimension_postcomp_surjectiveOnStalks δ
    (fieldChowSituation
      (S.residueField s)).dimensionFunction]
  have hzero : (fieldChowSituation
      (S.residueField s)).dimensionFunction (f.fiberToSpecResidueField s x) = 0 :=
    fieldChowSituation_dimensionFunction_eq_zero (S.residueField s)
      (f.fiberToSpecResidueField s x)
  change δ (S.fromSpecResidueField s (f.fiberToSpecResidueField s x)) +
    relativeDimension
      (fieldChowSituation
        (S.residueField s)).dimensionFunction (f.fiberToSpecResidueField s) x -
    (fieldChowSituation
      (S.residueField s)).dimensionFunction (f.fiberToSpecResidueField s x) = _
  rw [S.fromSpecResidueField_apply, hzero, sub_zero]

lemma relativeDimension_generic_ge_special {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    (ξ : f.fiber (genericPoint (Spec (.of R)))) (x : f.fiber (IsLocalRing.closedPoint R))
    (h : f.fiberι (genericPoint (Spec (.of R))) ξ ⤳
      f.fiberι (IsLocalRing.closedPoint R) x) :
    fiberPointDimension f (IsLocalRing.closedPoint R) x ≤
    fiberPointDimension f (genericPoint (Spec (.of R))) ξ := by
  have hcat :=
    AlgebraicGeometry.Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_dimOneDomain
      R (IsDiscreteValuationRing.ringKrullDim_eq_one R)
      (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of R)))
  obtain ⟨d, hd⟩ :=
    Stacks.Chow.relativeDimension_isDimensionFunction hcat (dvrDimensionFunction R) f
  have hne : f.fiberι (genericPoint (Spec (.of R))) ξ ≠
      f.fiberι (IsLocalRing.closedPoint R) x := by
    intro he
    exact genericPoint_ne_closedPoint R
      ((f.apply_fiberι _ ξ).symm.trans ((congrArg f he).trans (f.apply_fiberι _ x)))
  have hlt := d.strictAnti_specializes h hne
  rw [hd, hd, relativeDimension_fiber f (dvrDimensionFunction R)
      (IsLocalRing.closedPoint R) x,
    relativeDimension_fiber f (dvrDimensionFunction R)
      (genericPoint (Spec (.of R))) ξ] at hlt
  simp only [dvrDimensionFunction,
    ite_eq_right (Ne.symm (genericPoint_ne_closedPoint R))] at hlt
  dsimp only [fiberPointDimension, fieldChowSituation]
  omega

private lemma relativeDimension_le_schemeDeltaDimension
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (x : X) :
    (relativeDimension C.dimensionFunction f x : EInt) ≤
      Stacks.Chow.schemeDeltaDimension C f := by
  obtain ⟨d, hd⟩ := Stacks.Chow.relativeDimension_isDimensionFunction
    C.isUniversallyCatenary C.dimensionFunction f
  let W : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let Z : IrreducibleCloseds X :=
    ⟨W.1, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩
  have hspec : Z.isIrreducible.genericPoint ⤳ x :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).specializes mem_irreducibleComponent
  have hle : d x ≤ d Z.isIrreducible.genericPoint := by
    by_cases heq : Z.isIrreducible.genericPoint = x
    · rw [heq]
    · exact (d.strictAnti_specializes hspec heq).le
  rw [hd, hd] at hle
  exact le_iSup_of_le W (WithBotTop.coe_le_coe.mpr hle)

lemma relativeDimension_le_of_mem_supp
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (F : X.Modules) (hF : F.IsCoherent)
    (k : ℤ) (hbound : Stacks.Chow.schemeDeltaDimension C
      ((@reducedSupport _ F hF).subschemeι ≫ f) ≤ (k : EInt))
    (x : X) (hx : x ∈ SheafOfModules.supp F) :
    relativeDimension C.dimensionFunction f x ≤ k := by
  let I := @reducedSupport _ F hF
  have hxI : x ∈ I.support := by
    change x ∈ ((@reducedSupport _ F hF).support : Set X)
    let : F.IsCoherent := hF
    rwa [coe_support_reducedSupport]
  let z : I.subscheme := ⟨x, hxI⟩
  have hle := (relativeDimension_le_schemeDeltaDimension C (I.subschemeι ≫ f) z).trans hbound
  rw [relativeDimension_comp_of_bijective_residueFieldMap _ _ _ _
    (Scheme.Hom.bijective_residueFieldMap _ _)] at hle
  exact WithBotTop.coe_le_coe.mp hle

private lemma notMem_minimal_support_of_isSMulRegular
    {A M : Type*} [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    {a : A} (ha : IsSMulRegular M a) {p : PrimeSpectrum A}
    (hp : Minimal (· ∈ Module.support A M) p) : a ∉ p.asIdeal := by
  intro hmem
  have h : a ∈ ⋃ q ∈ associatedPrimes A M, (q : Set A) :=
    Set.mem_iUnion.mpr ⟨p.asIdeal, Set.mem_iUnion.mpr
      ⟨Module.mem_associatedPrimes_of_minimal_mem_support hp, hmem⟩⟩
  rw [biUnion_associatedPrimes_eq_compl_regular] at h
  exact h ha

lemma image_minimal_support_stalk_mem_genericFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    (F : X.Modules) (x : f.fiber (IsLocalRing.closedPoint R))
    (p : PrimeSpectrum (X.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) x)))
    (a : X.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) x))
    (hker : RingHom.ker ((f.fiberι (IsLocalRing.closedPoint R)).stalkMap x).hom =
      Ideal.span {a})
    (hreg :
      letI := Stacks.ModuleStalkSpecialization.stalkModule F
        (f.fiberι (IsLocalRing.closedPoint R) x)
      IsSMulRegular (F.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) x)) a)
    (hp :
      letI := Stacks.ModuleStalkSpecialization.stalkModule F
        (f.fiberι (IsLocalRing.closedPoint R) x)
      Minimal (· ∈ Module.support (X.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) x))
        (F.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) x))) p) :
    f (X.fromSpecStalk (f.fiberι (IsLocalRing.closedPoint R) x) p) =
      genericPoint (Spec (.of R)) := by
  let := Stacks.ModuleStalkSpecialization.stalkModule F
    (f.fiberι (IsLocalRing.closedPoint R) x)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  rcases eq_genericPoint_or_closedPoint
      (f (X.fromSpecStalk (f.fiberι (IsLocalRing.closedPoint R) x) p)) with h | h
  · exact h
  · exfalso
    apply notMem_minimal_support_of_isSMulRegular hreg hp
    have hpre : ∀ y : Spec (CommRingCat.of R), IsPreimmersion (f.fiberι y) :=
      fun y ↦ inferInstance
    have := hpre (IsLocalRing.closedPoint R)
    apply ker_stalkMap_le_of_fromSpecStalk_mem_range (f.fiberι (IsLocalRing.closedPoint R)) x p
    · rwa [f.range_fiberι (IsLocalRing.closedPoint R)]
    · rw [hker]
      exact Ideal.subset_span (Set.mem_singleton a)

end DimensionComparison

theorem cycleAssociatedToCoherentSheaf_apply_of_active
    (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (g : Y ⟶ C.S) [LocallyOfFiniteType g] (G : Y.Modules) (hG : G.IsCoherent)
    (k : ℤ) (hGk : Stacks.Chow.schemeDeltaDimension C
      ((@reducedSupport _ G hG).subschemeι ≫ g) ≤ (k : EInt))
    (x : Y) (hx : x ∈ SheafOfModules.supp G)
    (hk : Stacks.Chow.deltaDimension C g (irreducibleSetEquivPoints.symm x) = k) :
    (@Stacks.Chow.cycleAssociatedToCoherentSheaf _ C g _ G hG k hGk :
      AlgebraicCycle Y ℤ) x = Stacks.Chow.sheafMultiplicity G x := by
  have hrel : relativeDimension C.dimensionFunction g x = k := by
    rwa [← deltaDimension_eq_of_isGenericPoint C g (irreducibleSetEquivPoints.symm x) x
      isGenericPoint_closure]
  rw [cycleAssociatedToCoherentSheaf_apply]
  simp [hx, hrel]

/-- The module `F_s`: the pullback of `F` to the scheme-theoretic fibre of `f` over `s`. -/
@[ega "IV 11.2.8"]
noncomputable abbrev fiberModule {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S) :
    (f.fiber s).Modules :=
  (Scheme.Modules.pullback (f.fiberι s)).obj F

/-- The dimension `dim(Supp(F_s))` of the support of `F_s`: the delta-dimension over the
residue field `κ(s)` of the canonical reduced closed subscheme of the fibre supporting
`F_s`. -/
noncomputable abbrev fiberSupportDimension {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) (hF : F.IsCoherent) (s : S) : EInt :=
  Stacks.Chow.schemeDeltaDimension
    (fieldChowSituation (S.residueField s))
    ((@reducedSupport _ (fiberModule f F s)
      (@fiberModule_isCoherent _ _ f _ F hF.isFiniteType
      (isQuasicoherent_of_isCoherent F) s)).subschemeι ≫ f.fiberToSpecResidueField s)

/-- The cycle `[F_s]_r` on the fibre over `s` associated to the coherent module `F_s`, defined
when the support of `F_s` has dimension at most `r`. -/
noncomputable def fiberCycle {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (hF : F.IsCoherent) (r : ℕ) (s : S)
    (hdim : fiberSupportDimension f F hF s ≤ ((r : ℤ) : EInt)) :
    FiberCycleGroup f s r :=
  @Stacks.Chow.cycleAssociatedToCoherentSheaf _
    (fieldChowSituation (S.residueField s))
    (f.fiberToSpecResidueField s) _ (fiberModule f F s)
    (@fiberModule_isCoherent _ _ f _ F hF.isFiniteType
      (isQuasicoherent_of_isCoherent F) s) (r : ℤ)
    hdim

lemma eq_of_mem_supp_of_specializes_of_relativeDimension_eq
    (C : ChowSituation.{u}) {Y : Scheme.{u}} (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (G : Y.Modules) (hG : G.IsCoherent) (k : ℤ)
    (hbound : Stacks.Chow.schemeDeltaDimension C
      ((@reducedSupport _ G hG).subschemeι ≫ g) ≤ (k : EInt))
    {x y : Y} (hy : y ∈ SheafOfModules.supp G)
    (hδx : relativeDimension C.dimensionFunction g x = k)
    (h : y ⤳ x) : y = x := by
  by_contra hne
  obtain ⟨d, hd⟩ := Stacks.Chow.relativeDimension_isDimensionFunction
    C.isUniversallyCatenary C.dimensionFunction g
  have hlt := d.strictAnti_specializes h hne
  rw [hd, hd, hδx] at hlt
  exact (not_lt_of_ge (relativeDimension_le_of_mem_supp C g G hG k hbound y hy)) hlt


section CycleCoefficients
attribute [local instance] RingHomInvPair.of_ringEquiv

private lemma ringLength_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : Module.length A A = Module.length B B :=
  length_eq_of_semilinearEquiv e e.toSemilinearEquiv

private lemma ringLength_eq_quotient_of_surjective {A B : Type*}
    [CommRing A] [CommRing B] (φ : A →+* B) (hφ : Function.Surjective φ) :
    Module.length B B = Module.length A (A ⧸ RingHom.ker φ) := by
  let : Algebra A B := φ.toAlgebra
  let e : (A ⧸ RingHom.ker φ) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hφ
  exact (Module.length_eq_of_surjective hφ).symm.trans e.toLinearEquiv.length_eq.symm

/-- Equal ideals give quotients of equal length. -/
private lemma ringLength_quotient_congr {A : Type*} [CommRing A] {I J : Ideal A} (h : I = J) :
    Module.length A (A ⧸ I) = Module.length A (A ⧸ J) := by
  subst h
  rfl

private lemma mem_genericPoints_of_no_proper_generalization {Y : Scheme.{u}} (x : Y)
    (hx : ∀ y : Y, y ⤳ x → y = x) : x ∈ genericPoints Y := by
  let Z : irreducibleComponents Y :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let y := genericPoints.ofComponent Z
  exact hx y.1 ((genericPoints.isGenericPoint_ofComponent Z).specializes
    mem_irreducibleComponent) ▸ y.2

private lemma closedSubschemeCycleCoeff_eq_ringLength
    (C : ChowSituation.{u}) {Y Z : Scheme.{u}} (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (G : Y.Modules) (hG : G.IsCoherent) (k : ℤ)
    (hbound : Stacks.Chow.schemeDeltaDimension C
      ((@reducedSupport _ G hG).subschemeι ≫ g) ≤ (k : EInt))
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (hsupp : Set.range i ⊆ SheafOfModules.supp G) (z : Z)
    (hδ : relativeDimension C.dimensionFunction g (i z) = k) :
    closedSubschemeCycleCoeff C g i k (i z) =
      ((Module.length (Z.presheaf.stalk z) (Z.presheaf.stalk z)).toNat : ℤ) := by
  have hz : z ∈ genericPoints Z :=
    mem_genericPoints_of_no_proper_generalization z fun y hy ↦ i.isClosedEmbedding.injective <|
      eq_of_mem_supp_of_specializes_of_relativeDimension_eq C g G hG k hbound
        (hsupp (Set.mem_range_self y)) hδ (hy.map i.continuous)
  have he := Stacks.Chow.cycleAssociatedToClosedSubscheme_apply C g i k ⟨z, hz⟩ hδ
  change closedSubschemeCycleCoeff C g i k (i z) = _ at he
  rw [he]
  unfold Stacks.Chow.componentMultiplicity
  let : Algebra (Y.presheaf.stalk (i z)) (Z.presheaf.stalk z) :=
    (i.stalkMap z).hom.toAlgebra
  rw [Module.length_eq_of_surjective (i.stalkMap_surjective z)]

end CycleCoefficients

section GenericMultiplicity

private lemma isIso_stalkMap_genericFiber {X S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) (ξ : f.fiber (genericPoint S)) :
    IsIso ((f.fiberι (genericPoint S)).stalkMap ξ) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  refine ⟨?_, (f.fiberι (genericPoint S)).stalkMap_surjective ξ⟩
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  rw [fiber_stalkMap_ker]
  have hbot :
      IsLocalRing.maximalIdeal (S.presheaf.stalk (f (f.fiberι (genericPoint S) ξ))) = ⊥ := by
    rw [f.apply_fiberι]
    exact IsLocalRing.maximalIdeal_eq_bot
  rw [hbot, Ideal.map_bot]

lemma sheafMultiplicity_genericFiber_eq_localized_length
    {X S : Scheme.{u}} [IsIntegral S] (f : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] (x : X) (ξ : f.fiber (genericPoint S))
    (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : X.fromSpecStalk x p = f.fiberι (genericPoint S) ξ) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule F x
    Stacks.Chow.sheafMultiplicity (fiberModule f F (genericPoint S)) ξ =
      ((Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl (F.presheaf.stalk x))).toNat : ℤ) := by
  have := isIso_stalkMap_genericFiber f ξ
  rw [sheafMultiplicity_pullback_of_stalkMap_isIso, ← hp]
  exact sheafMultiplicity_fromSpecStalk_eq_localized_length F x p

end GenericMultiplicity

section ComapCoefficients

private lemma closedSubschemeCycleCoeff_comap_eq_length_quotient
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (G : Y.Modules) (hG : G.IsCoherent) (k : ℤ)
    (hbound : Stacks.Chow.schemeDeltaDimension C
      ((@reducedSupport _ G hG).subschemeι ≫ g) ≤ (k : EInt))
    (i : Y ⟶ X) [SurjectiveOnStalks i] (I : X.IdealSheafData)
    [IsIntegral I.subscheme]
    (hsupp : Set.range (I.comap i).subschemeι ⊆ SheafOfModules.supp G)
    (w : (pullback i I.subschemeι).carrier)
    (hδ : relativeDimension C.dimensionFunction g (pullback.fst i I.subschemeι w) = k)
    (p : PrimeSpectrum (X.presheaf.stalk (i (pullback.fst i I.subschemeι w))))
    (hp : X.fromSpecStalk (i (pullback.fst i I.subschemeι w)) p =
      I.subschemeι (genericPoint I.subscheme))
    (a : X.presheaf.stalk (i (pullback.fst i I.subschemeι w)))
    (hker : RingHom.ker (i.stalkMap (pullback.fst i I.subschemeι w)).hom = Ideal.span {a}) :
    closedSubschemeCycleCoeff C g (I.comap i).subschemeι k
      (pullback.fst i I.subschemeι w) =
      ((Module.length (X.presheaf.stalk (i (pullback.fst i I.subschemeι w)))
        ((X.presheaf.stalk (i (pullback.fst i I.subschemeι w))) ⧸
          (Ideal.span {a} ⊔ p.asIdeal))).toNat : ℤ) := by
  let D := (I.comap i).subscheme
  let wD : D := (I.comapIso i).inv w
  have hw : (I.comap i).subschemeι wD = pullback.fst i I.subschemeι w := by
    change ((I.comapIso i).inv ≫ (I.comap i).subschemeι) w = _
    rw [Scheme.IdealSheafData.comapIso_inv_subschemeι]
  have hcoeff := closedSubschemeCycleCoeff_eq_ringLength C g G hG k hbound
    (I.comap i).subschemeι hsupp wD (by rw [hw]; exact hδ)
  rw [hw] at hcoeff
  rw [hcoeff]
  congr 2
  let : Module (X.presheaf.stalk (i (pullback.fst i I.subschemeι w)))
      ((X.presheaf.stalk (i (pullback.fst i I.subschemeι w))) ⧸
        RingHom.ker ((pullback.fst i I.subschemeι ≫ i).stalkMap w).hom) :=
    Submodule.Quotient.module _
  calc
    Module.length (D.presheaf.stalk wD) (D.presheaf.stalk wD) =
        Module.length ((pullback i I.subschemeι).presheaf.stalk w)
          ((pullback i I.subschemeι).presheaf.stalk w) :=
      ringLength_eq_of_ringEquiv
        (asIso ((I.comapIso i).inv.stalkMap w)).commRingCatIsoToRingEquiv
    _ = Module.length (X.presheaf.stalk (i (pullback.fst i I.subschemeι w)))
        ((X.presheaf.stalk (i (pullback.fst i I.subschemeι w))) ⧸
          RingHom.ker ((pullback.fst i I.subschemeι ≫ i).stalkMap w).hom) :=
      ringLength_eq_quotient_of_surjective _
        ((pullback.fst i I.subschemeι ≫ i).stalkMap_surjective w)
    _ = _ := by
      have hpk : RingHom.ker ((pullback.fst i I.subschemeι ≫ i).stalkMap w).hom =
          RingHom.ker (i.stalkMap (pullback.fst i I.subschemeι w)).hom ⊔
          RingHom.ker (eqToHom (congrArg X.presheaf.stalk
            (congrArg (fun k : pullback i I.subschemeι ⟶ X ↦ k w) pullback.condition)) ≫
            I.subschemeι.stalkMap (pullback.snd i I.subschemeι w)).hom :=
        pullback_stalkMap_ker i I.subschemeι w
      have hJ : RingHom.ker ((pullback.fst i I.subschemeι ≫ i).stalkMap w).hom =
          Ideal.span {a} ⊔ p.asIdeal :=
        hpk.trans (by
          rw [hker]
          exact congrArg
            (fun J : Ideal (X.presheaf.stalk (i (pullback.fst i I.subschemeι w))) ↦
              Ideal.span {a} ⊔ J)
            (ker_stalkMap_congr_eq_prime_of_genericPoint I.subschemeι
              (pullback.snd i I.subschemeι w) _
              (congrArg (fun k : pullback i I.subschemeι ⟶ X ↦ k w) pullback.condition) p hp))
      exact ringLength_quotient_congr hJ

end ComapCoefficients

section PointCoefficients

private lemma closedSubschemeCycleCoeff_comap_eq_length_quotient_at
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (G : Y.Modules) (hG : G.IsCoherent) (k : ℤ)
    (hbound : Stacks.Chow.schemeDeltaDimension C
      ((@reducedSupport _ G hG).subschemeι ≫ g) ≤ (k : EInt))
    (i : Y ⟶ X) [SurjectiveOnStalks i] (I : X.IdealSheafData)
    [IsIntegral I.subscheme]
    (hsupp : Set.range (I.comap i).subschemeι ⊆ SheafOfModules.supp G)
    (x : Y) (hx : i x ∈ I.support)
    (hδ : relativeDimension C.dimensionFunction g x = k)
    (p : PrimeSpectrum (X.presheaf.stalk (i x)))
    (hp : X.fromSpecStalk (i x) p = I.subschemeι (genericPoint I.subscheme))
    (a : X.presheaf.stalk (i x))
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {a}) :
    closedSubschemeCycleCoeff C g (I.comap i).subschemeι k x =
      ((Module.length (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ (Ideal.span {a} ⊔ p.asIdeal))).toNat : ℤ) := by
  have hx' : x ∈ Set.range (pullback.fst i I.subschemeι) := by
    rwa [Scheme.Pullback.range_fst, I.range_subschemeι]
  obtain ⟨w, rfl⟩ := hx'
  exact closedSubschemeCycleCoeff_comap_eq_length_quotient C g G hG k hbound i I
    hsupp w hδ p hp a hker

lemma specializationCycleCoeff_eq_length_quotient
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    (F : X.Modules) (hF : F.IsCoherent) (r : ℕ)
    (hs : fiberSupportDimension f F hF (IsLocalRing.closedPoint R) ≤ ((r : ℤ) : EInt))
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hξ : ξ ∈ SheafOfModules.supp (fiberModule f F (genericPoint (Spec (.of R)))))
    (x : f.fiber (IsLocalRing.closedPoint R))
    (hδ : fiberPointDimension f (IsLocalRing.closedPoint R) x = (r : ℤ))
    (p : PrimeSpectrum (X.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) x)))
    (hp : X.fromSpecStalk (f.fiberι (IsLocalRing.closedPoint R) x) p =
      f.fiberι (genericPoint (Spec (.of R))) ξ)
    (a : X.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) x))
    (hker : RingHom.ker ((f.fiberι (IsLocalRing.closedPoint R)).stalkMap x).hom =
      Ideal.span {a}) :
    specializationCoeff f r ξ x =
      ((Module.length (X.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) x))
        ((X.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) x)) ⧸
          (Ideal.span {a} ⊔ p.asIdeal))).toNat : ℤ) := by
  have : F.IsFiniteType := hF.isFiniteType
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  let η := genericPoint (Spec (.of R))
  let s : Spec (.of R) := IsLocalRing.closedPoint R
  let C := fieldChowSituation
    ((Spec (.of R)).residueField s)
  let g := f.fiberToSpecResidueField s
  let I := Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({f.fiberι η ξ} : Set X))
  have hsupport : (I.support : Set X) = closure ({f.fiberι η ξ} : Set X) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  let : IsReduced I.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  let : IrreducibleSpace I.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X I (by
      rw [I.range_subschemeι, hsupport]
      exact isIrreducible_singleton.closure)
  let : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hgen : I.subschemeι (genericPoint I.subscheme) = f.fiberι η ξ := by
    have hcl : closure ({I.subschemeι (genericPoint I.subscheme)} : Set X) =
        closure ({f.fiberι η ξ} : Set X) := by
      rw [← Set.image_singleton, I.subschemeι.isClosedEmbedding.closure_image_eq,
        genericPoint_closure, Set.image_univ, I.range_subschemeι, hsupport]
    exact isGenericPoint_closure.eq (hcl ▸ isGenericPoint_closure)
  have hI : ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({ξ} : Set (f.fiber η)))).subschemeι ≫ f.fiberι η).ker = I := by
    change (Scheme.IdealSheafData.vanishingIdeal _).map (f.fiberι η) = I
    rw [Scheme.IdealSheafData.map_vanishingIdeal]
    congr 1
    apply Closeds.ext
    change closure ((f.fiberι η) '' closure {ξ}) = closure {f.fiberι η ξ}
    rw [← Set.image_singleton]
    exact closure_image_closure (f.fiberι η).continuous
  change closedSubschemeCycleCoeff C g
    (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({ξ} : Set (f.fiber η)))).subschemeι ≫ f.fiberι η).ker.comap
        (f.fiberι s)).subschemeι (r : ℤ) x = _
  rw [hI]
  have hsupp : Set.range (I.comap (f.fiberι s)).subschemeι ⊆
      SheafOfModules.supp (fiberModule f F s) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
      Stacks.Modules.supp_pullback]
    intro y hy
    have hy' : f.fiberι s y ∈ closure ({f.fiberι η ξ} : Set X) :=
      hsupport ▸ hy
    apply closure_minimal (Set.singleton_subset_iff.mpr ?_)
      (SheafOfModules.isClosed_supp F) hy'
    rwa [Stacks.Modules.supp_pullback] at hξ
  refine closedSubschemeCycleCoeff_comap_eq_length_quotient_at C g
    (fiberModule f F s) (fiberModule_isCoherent f F s) (r : ℤ) hs
    (f.fiberι s) I hsupp x ?_ hδ p (hp.trans hgen.symm) a hker
  change f.fiberι s x ∈ (I.support : Set X)
  rw [hsupport, ← hp]
  exact specializes_iff_mem_closure.mp (specializes_fromSpecStalk _ p)

end PointCoefficients

end Stacks.Chow.ModuleSpecialization

end
