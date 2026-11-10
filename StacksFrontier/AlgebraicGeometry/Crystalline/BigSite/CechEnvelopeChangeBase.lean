module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.AffineSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeProducts
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeTensorAlgebra
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CrystalValuesProjective
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Functoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.SmoothFlat

/-!
# Change of base of the Čech objects of smooth lifts

Let `f : S ⟶ S'` be a morphism of affine divided power bases, `A' = Γ(S', ⊤) → A = Γ(S, ⊤)`,
with `p` nilpotent, and let `g : X ⟶ X'` be such that `X = X' ×_{S'₀} S₀`. For a smooth lift
`B'` of an affine open `U'` of `X'` the base change `A ⊗_{A'} B'` is a smooth lift of `g⁻¹ U'`
(`CechEnvelope.SmoothLift.baseChange`). This file compares the objects of the big crystalline
sites built from these lifts along the change of base functor `u = changeBase S S' f g h`, and
proves the two algebraic inputs of the Čech computation of the base change map of
[Stacks, Tag 07MU] used in [Stacks, Tag 07N5]: the Čech terms commute with base change, and they
are flat.

## Main definitions

* `CechEnvelope.changeBaseHom` — the morphism
  `u(g⁻¹ U', Spec (A ⊗_{A'} B'), γ) ⟶ (U', Spec B', γ')` of `CRIS(X'/S')` given by the divided
  power map `B' → A ⊗_{A'} B'`, `b ↦ 1 ⊗ b`.
* `CechEnvelope.envelopeChangeBaseHom` — for a family `B'_0, …, B'_n` of smooth lifts of affine
  opens of the separated scheme `X'`, the induced morphism `u(D_s) ⟶ D'_s` of envelope objects
  ([Stacks, Tag 07N5]), compatible with the projections (`envelopeChangeBaseHom_proj`).
* `CechEnvelope.changeBaseValuesMap` — restriction `N(T') → N(u T)` along `m : u(T) ⟶ T'`,
  as a map of `A'`-modules.

## Main results

* `CechEnvelope.bijective_envelopeBaseChangeRingHom` — **`A ⊗_{A'} D' ≅ D`**: the divided power
  envelope of the base-changed Čech data is the base change of the envelope. The base change
  `A ⊗_{A'} ⨂ B'_k ≅ ⨂ (A ⊗_{A'} B'_k)` matches the two kernels, because
  `g⁻¹(U'_0 ∩ ⋯ ∩ U'_n)` is the fibre product `(U'_0 ∩ ⋯ ∩ U'_n) ×_{S'₀} S₀`
  (`CechEnvelope.tensorMap_baseChange_eq`), and the envelope of a smooth presentation commutes
  with base change (`Crystalline.bijective_envelopeBaseChangeHom_of_smooth_ker`).
* `CechEnvelope.envelopeChangeBaseHom_appTop` — on global sections `u(D_s) ⟶ D'_s` is the
  divided power morphism `D' → D` of envelopes over `A' → A`.
* `CechEnvelope.isBaseChange_changeBaseValuesMap` — termwise base change criterion: if
  `Γ(u T) = A ⊗_{A'} Γ(T')` then `N(u T) = A ⊗_{A'} N(T')` for every quasi-coherent `N`.
* **`CechEnvelope.isBaseChange_changeBaseValuesMap_of_isLimit`** — for products `P'` of the
  smooth-lift objects, `P` of those of the base-changed lifts, and `m : u(P) ⟶ P'` compatible
  with the projections, `A ⊗_{A'} N(P') → N(u P)`, `a ⊗ s ↦ a · m^* s`, is bijective for every
  quasi-coherent `N`.
* **`CechEnvelope.flat_values_of_isLimit`** — the values on such products of a crystal in finite
  locally free modules are flat over `A'`.

## References

* [Stacks Project, Tag 07MU](https://stacks.math.columbia.edu/tag/07MU)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07H1](https://stacks.math.columbia.edu/tag/07H1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

open SmallSite

/-! ### Global sections along an isomorphism -/

section Iso

variable {T : GlobalCrystallineSituation.{u}} {P Q : Thickening T}

/-- The global sections of a morphism of `CRIS(X/S)` on the ambient schemes compose. -/
theorem targetHom_appTop_comp {R : Thickening T} (a : P ⟶ Q) (b : Q ⟶ R)
    (x : Γ(R.thickening.target.scheme, ⊤)) :
    (a ≫ b).targetHom.hom.appTop.hom x =
      a.targetHom.hom.appTop.hom (b.targetHom.hom.appTop.hom x) :=
  ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop a.targetHom.hom b.targetHom.hom) x

/-- **An isomorphism of `CRIS(X/S)` on the global sections of the ambient schemes.** -/
def targetSectionsEquivOfIso (i : P ≅ Q) :
    Γ(Q.thickening.target.scheme, ⊤) ≃+* Γ(P.thickening.target.scheme, ⊤) :=
  RingEquiv.ofRingHom i.hom.targetHom.hom.appTop.hom i.inv.targetHom.hom.appTop.hom
    (RingHom.ext fun x ↦ ((targetHom_appTop_comp i.hom i.inv x).symm.trans
      (congrArg (fun k : P ⟶ P ↦ k.targetHom.hom.appTop.hom x) i.hom_inv_id)))
    (RingHom.ext fun x ↦ ((targetHom_appTop_comp i.inv i.hom x).symm.trans
      (congrArg (fun k : Q ⟶ Q ↦ k.targetHom.hom.appTop.hom x) i.inv_hom_id)))

/-- The value of `targetSectionsEquivOfIso`. -/
theorem targetSectionsEquivOfIso_apply (i : P ≅ Q) (x : Γ(Q.thickening.target.scheme, ⊤)) :
    targetSectionsEquivOfIso i x = i.hom.targetHom.hom.appTop.hom x := rfl

/-- The ambient scheme of an object isomorphic to one with affine ambient scheme is affine. -/
theorem isAffine_target_of_iso (i : P ≅ Q) [IsAffine Q.thickening.target.scheme] :
    IsAffine P.thickening.target.scheme :=
  have : IsIso i.hom.targetHom.hom :=
    ⟨i.inv.targetHom.hom, congrArg (fun k : P ⟶ P ↦ k.targetHom.hom) i.hom_inv_id,
      congrArg (fun k : Q ⟶ Q ↦ k.targetHom.hom) i.inv_hom_id⟩
  IsAffine.of_isIso i.hom.targetHom.hom

private theorem targetHom_appTop_toBase (a : P ⟶ Q) (x : Γ(T.S.scheme, ⊤)) :
    a.targetHom.hom.appTop.hom (Q.toBase.hom.appTop.hom x) = P.toBase.hom.appTop.hom x := by
  have h := congrArg (fun φ : P.thickening.target ⟶ T.S ↦ φ.hom.appTop.hom x) a.base_naturality
  simp only [DividedPowerScheme.Hom.comp_hom, Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  exact h

end Iso

/-! ### One smooth lift -/

section Single

variable {S S' : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme] [IsAffine S'.S.scheme]
  {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  (hpb : IsPullback g S.toClosedFiber S'.toClosedFiber (DividedPowerScheme.closedFiberMap f))
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) (hp' : IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤)))
  {U' : S'.X.Opens} [IsAffine U'] [IsAffine (g ⁻¹ᵁ U')] (L' : SmoothLift S' U'.ι)

/-- The object `(g⁻¹ U', Spec (A ⊗_{A'} B'), γ)` of the base change of a smooth lift, rebased to
`CRIS(X'/S')`. -/
abbrev changeBaseObject : Thickening S' :=
  (changeBase S S' f g h).obj ((L'.baseChange hpb).object hp)

/-- The map of the thickened scheme of `changeBaseObject` to `U'`. -/
def changeBaseObjectToOpen :
    (changeBaseObject hpb h hp L').thickening.source ⟶ U'.toScheme :=
  specToX (isNilpotent_prime_over S (g ⁻¹ᵁ U').ι hp) ((L'.baseChange hpb).thickening hp) ≫
    g ∣_ U'

/-- `changeBaseObjectToOpen` followed by the inclusion of `U'` is the map to `X'`. -/
theorem changeBaseObjectToOpen_ι :
    changeBaseObjectToOpen hpb h hp L' ≫ U'.ι = (changeBaseObject hpb h hp L').toX :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ specToX (isNilpotent_prime_over S (g ⁻¹ᵁ U').ι hp)
      ((L'.baseChange hpb).thickening hp) ≫ k) (morphismRestrict_ι g U')).trans
      (Category.assoc _ _ _).symm)

/-- `changeBaseObject` read over `U'`. -/
abbrev changeBaseOver : Thickening (overSituation S' U'.ι) :=
  overLift S' U'.ι (changeBaseObject hpb h hp L') (changeBaseObjectToOpen hpb h hp L')
    (changeBaseObjectToOpen_ι hpb h hp L')

/-- The thickened scheme of `changeBaseOver` is affine. -/
instance isAffine_changeBaseOver_source :
    IsAffine (changeBaseOver hpb h hp L').thickening.source :=
  inferInstanceAs (IsAffine (Spec _))

/-- The ring map `B' → A ⊗_{A'} B' → Γ(Spec (A ⊗_{A'} B'), ⊤)`. -/
def changeBaseRingHom :
    L'.ring →+* Γ((changeBaseObject hpb h hp L').thickening.target.scheme, ⊤) :=
  letI := baseSectionsAlgebra f
  (Scheme.ΓSpecIso (CommRingCat.of (L'.baseChange hpb).dividedPowerRing)).inv.hom.comp
    (Algebra.TensorProduct.includeRight (R := ↥(baseSectionsRing S'))
      (A := ↥(baseSectionsRing S)) (B := L'.ring)).toRingHom

/-- The value of `changeBaseRingHom`: `b ↦ 1 ⊗ b`. -/
theorem changeBaseRingHom_apply (b : L'.ring) :
    letI := baseSectionsAlgebra f
    changeBaseRingHom hpb h hp L' b =
      (Scheme.ΓSpecIso (CommRingCat.of (L'.baseChange hpb).dividedPowerRing)).inv.hom
        ((1 : baseSectionsRing S) ⊗ₜ[baseSectionsRing S'] b) :=
  rfl

/-- `changeBaseRingHom` lies over `A' → A`. -/
theorem changeBaseRingHom_comp_algebraMap :
    (changeBaseRingHom hpb h hp L').comp (algebraMap (baseSectionsRing S') L'.ring) =
      (Scheme.ΓSpecIso (CommRingCat.of (L'.baseChange hpb).dividedPowerRing)).inv.hom.comp
        ((algebraMap (baseSectionsRing S) (L'.baseChange hpb).ring).comp
          (baseSectionsRingHom f)) := by
  let := baseSectionsAlgebra f
  exact RingHom.ext fun a ↦ congrArg
    (Scheme.ΓSpecIso (CommRingCat.of (L'.baseChange hpb).dividedPowerRing)).inv.hom
    (RingHom.congr_fun (includeRight_comp_algebraMap (A' := ↥(baseSectionsRing S'))
      (A := ↥(baseSectionsRing S)) (B' := L'.ring)) a)

/-- `B' → Γ(Spec (A ⊗_{A'} B'), ⊤)` is a divided power morphism: `I'B'` is generated by the image
of `I'`, on which both divided power structures restrict those of the bases. -/
theorem isDPMorphism_changeBaseRingHom :
    DividedPowers.IsDPMorphism L'.dividedPowerRing.dividedPowers
      (changeBaseObject hpb h hp L').thickening.sectionsRing.dividedPowers
      (changeBaseRingHom hpb h hp L') := by
  refine DividedPowers.IsDPMorphism.of_comp (baseSectionsRing S').dividedPowers _ _
    (algebraMap (baseSectionsRing S') L'.ring) (changeBaseRingHom hpb h hp L') rfl
    L'.isDPMorphism_algebraMap ?_
  rw [changeBaseRingHom_comp_algebraMap]
  exact ((DividedPowerScheme.specSectionsRingIso (L'.baseChange hpb).dividedPowerRing).hom.comp
    ((DividedPowers.DPMorphism.mk' (L'.baseChange hpb).isDPMorphism_algebraMap).comp
      (globalSectionsDPMorphism f))).isDPMorphism

/-- `changeBaseRingHom` as a divided power morphism. -/
def changeBaseDPMorphism :
    L'.dividedPowerRing ⟶ (changeBaseObject hpb h hp L').thickening.sectionsRing :=
  DividedPowers.DPMorphism.mk' (isDPMorphism_changeBaseRingHom hpb h hp L')

/-- The value of `changeBaseDPMorphism`. -/
theorem changeBaseDPMorphism_apply (b : L'.ring) :
    changeBaseDPMorphism hpb h hp L' b = changeBaseRingHom hpb h hp L' b := rfl

omit [IsAffine ↑(g ⁻¹ᵁ U')] in
/-- The identification `Γ(g⁻¹ U') ≅ (A ⊗_{A'} B') / I` restricted to `Γ(U')` is `b ↦ 1 ⊗ b`. -/
theorem baseChangeSectionsIso_restrict (c : Γ(U'.toScheme, ⊤)) :
    letI := baseSectionsAlgebra f
    (baseChangeSectionsIso hpb L').hom.hom ((g ∣_ U').appTop.hom c) =
      reducedTensorLeft (A := ↥(baseSectionsRing S)) (map_ideal_le f) (L'.equiv c) :=
  ConcreteCategory.congr_hom (IsPushout.inl_isoIsPushout_hom _ _ (isPushout_sections hpb U')
    (isPushout_reducedTensor_sections L')) c

/-- The image of `1 ⊗ b` in the thickened scheme `g⁻¹ U'` is the pullback along `g` of the
section of `U'` which `b` lifts. -/
theorem immersion_appTop_changeBaseRingHom (c : Γ(U'.toScheme, ⊤)) (b : L'.ring)
    (hb : Ideal.Quotient.mk _ b = L'.equiv c) :
    (changeBaseObject hpb h hp L').thickening.immersion.appTop.hom
        (changeBaseRingHom hpb h hp L' b) =
      (specToX (isNilpotent_prime_over S (g ⁻¹ᵁ U').ι hp)
        ((L'.baseChange hpb).thickening hp)).appTop.hom ((g ∣_ U').appTop.hom c) := by
  let := baseSectionsAlgebra f
  refine appTop_specQuotientImmersion_eq (isNilpotent_prime_over S (g ⁻¹ᵁ U').ι hp)
    ((L'.baseChange hpb).thickening hp) (β := (1 : baseSectionsRing S) ⊗ₜ[baseSectionsRing S'] b)
    ?_
  change _ = (baseChangeSectionsIso hpb L').hom.hom ((g ∣_ U').appTop.hom c)
  rw [baseChangeSectionsIso_restrict, ← hb]
  rfl

/-- The map to the base of `changeBaseObject`, on global sections. -/
theorem changeBaseObject_toBase_appTop (a : baseSectionsRing S') :
    (changeBaseObject hpb h hp L').toBase.hom.appTop.hom a =
      (Scheme.ΓSpecIso (CommRingCat.of (L'.baseChange hpb).dividedPowerRing)).inv.hom
        (algebraMap (baseSectionsRing S) (L'.baseChange hpb).ring (baseSectionsRingHom f a)) := by
  have h1 : (changeBaseObject hpb h hp L').toBase.hom.appTop.hom a =
      ((L'.baseChange hpb).object hp).toBase.hom.appTop.hom (f.hom.appTop.hom a) :=
    ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop ((L'.baseChange hpb).object hp).toBase.hom
      f.hom) a
  refine h1.trans ?_
  exact ConcreteCategory.congr_hom (DividedPowerScheme.homOfSectionsDPMorphism_hom_appTop
    (specFromBase (isNilpotent_prime_over S (g ⁻¹ᵁ U').ι hp) ((L'.baseChange hpb).thickening hp)))
    (f.hom.appTop.hom a)

/-- The compatibility with the structural maps from `Γ(U')` of `changeBaseThickeningHom`. -/
theorem changeBase_toQuotient_comp (c : Γ(U'.toScheme, ⊤)) :
    DividedPowerRing.quotientRingHom (changeBaseDPMorphism hpb h hp L')
        ((L'.thickening hp').toQuotient c) =
      wholeSectionsToQuotient (changeBaseOver hpb h hp L') c := by
  refine (changeBaseOver hpb h hp L').thickening.sectionsQuotientEquiv.injective ?_
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (L'.equiv c)
  rw [sectionsQuotientEquiv_wholeSectionsToQuotient]
  have e1 : (L'.thickening hp').toQuotient c =
      Ideal.Quotient.mk L'.dividedPowerRing.ideal b := hb.symm
  refine (congrArg (fun q ↦ (changeBaseOver hpb h hp L').thickening.sectionsQuotientEquiv
    (DividedPowerRing.quotientRingHom (changeBaseDPMorphism hpb h hp L') q)) e1).trans ?_
  refine (congrArg (changeBaseOver hpb h hp L').thickening.sectionsQuotientEquiv
    (DividedPowerRing.quotientRingHom_mk (changeBaseDPMorphism hpb h hp L') b)).trans ?_
  refine (SchemeThickening.sectionsQuotientEquiv_mk _ _).trans ?_
  refine (immersion_appTop_changeBaseRingHom hpb h hp L' c b hb).trans ?_
  exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop
    (specToX (isNilpotent_prime_over S (g ⁻¹ᵁ U').ι hp) ((L'.baseChange hpb).thickening hp))
    (g ∣_ U')) c).symm

/-- **The morphism `(B', I'B', γ_{B'}) ⟶ Γ(Spec (A ⊗_{A'} B'), ⊤)` of divided power thickenings
of `Γ(U')` over `A'`.** -/
def changeBaseThickeningHom :
    L'.thickening hp' ⟶ wholeThickeningToAffine (isNilpotent_prime_over S' U'.ι hp')
      (changeBaseOver hpb h hp L') where
  hom := changeBaseDPMorphism hpb h hp L'
  fromBase_comp := by
    ext a
    exact (RingHom.congr_fun (changeBaseRingHom_comp_algebraMap hpb h hp L') a).trans
      (changeBaseObject_toBase_appTop hpb h hp L' a).symm
  toQuotient_comp := RingHom.ext fun c ↦ changeBase_toQuotient_comp hpb h hp hp' L' c

/-- **The change-of-base map of a smooth lift.**  For `X = X' ×_{S'₀} S₀`, a smooth lift `B'` of
an affine open `U'` of `X'` and its base change `A ⊗_{A'} B'`, the morphism
`(g⁻¹ U', Spec (A ⊗_{A'} B'), γ) ⟶ (U', Spec B', γ')` of `CRIS(X'/S')` given by the divided
power map `B' → A ⊗_{A'} B'`, `b ↦ 1 ⊗ b`. -/
def changeBaseHom : changeBaseObject hpb h hp L' ⟶ L'.object hp' :=
  haveI := L'.isIso_specToX hp'
  haveI : IsIso (specThickeningOfAffine (isNilpotent_prime_over S' U'.ι hp')
    (L'.thickening hp')).toX := L'.isIso_specToX hp'
  haveI : IsAffine (specThickeningOfAffine (isNilpotent_prime_over S' U'.ι hp')
    (L'.thickening hp')).thickening.source := inferInstanceAs (IsAffine (Spec _))
  homOfOverLift S' U'.ι (homOfAffineSections (isNilpotent_prime_over S' U'.ι hp')
    ((wholeThickeningToAffineSpecIso (isNilpotent_prime_over S' U'.ι hp')
      (L'.thickening hp')).hom ≫ changeBaseThickeningHom hpb h hp hp' L'))

/-- The change-of-base map on global sections of the ambient schemes: `b ↦ 1 ⊗ b`. -/
theorem changeBaseHom_targetHom_appTop (x : Γ((L'.object hp').thickening.target.scheme, ⊤)) :
    (changeBaseHom hpb h hp hp' L').targetHom.hom.appTop.hom x =
      changeBaseRingHom hpb h hp L'
        ((Scheme.ΓSpecIso (CommRingCat.of L'.dividedPowerRing)).hom.hom x) :=
  ConcreteCategory.congr_hom (DividedPowerScheme.homOfSectionsDPMorphism_hom_appTop _) x

end Single

/-! ### The intersection as an algebra over `A / I` -/

section QuotientAlgebra

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]

/-- The map `A / I ≅ Γ(S₀) → Γ(V)` of a scheme `V` over `S₀`. -/
abbrev quotientSectionsMap {V : Scheme.{u}} (j : V ⟶ DividedPowerScheme.closedFiber S.S) :
    ↥(baseSectionsRing S) ⧸ (baseSectionsRing S).ideal →+* Γ(V, ⊤) :=
  j.appTop.hom.comp (closedFiberSectionsEquiv S).symm.toRingHom

/-- `A / I ≅ Γ(S₀)` on the class of an element of `A`. -/
theorem closedFiberSectionsEquiv_symm_mk (a : baseSectionsRing S) :
    (closedFiberSectionsEquiv S).symm (Ideal.Quotient.mk _ a) = closedFiberSectionsMap S a :=
  (RingEquiv.symm_apply_eq _).2 (closedFiberSectionsEquiv_apply S a).symm

/-- `quotientSectionsMap` on the class of an element of `A`. -/
theorem quotientSectionsMap_mk {V : Scheme.{u}} (j : V ⟶ DividedPowerScheme.closedFiber S.S)
    (a : baseSectionsRing S) :
    quotientSectionsMap j (Ideal.Quotient.mk _ a) =
      (j ≫ DividedPowerScheme.closedFiberι S.S).appTop.hom a := by
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    closedFiberSectionsEquiv_symm_mk]
  exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop j
    (DividedPowerScheme.closedFiberι S.S)) a).symm

/-- `B / IB` is smooth over `A / I` for a smooth `A`-algebra `B`. -/
theorem smooth_quotient {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (I : Ideal A) : Algebra.Smooth (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm

section Lift

variable {U : S.X.Opens} [IsAffine U] (L : SmoothLift S U.ι)

omit [IsAffine ↑U] in
/-- The map `Γ(S₀) → Γ(U)` of an affine open with a smooth lift is `A / I → B / IB`. -/
theorem appTop_toClosedFiber_eq :
    (U.ι ≫ S.toClosedFiber).appTop.hom =
      (L.equiv.symm.toRingHom.comp (algebraMap (↥(baseSectionsRing S) ⧸
        (baseSectionsRing S).ideal) (L.ring ⧸ (baseSectionsRing S).ideal.map
          (algebraMap (baseSectionsRing S) L.ring)))).comp
        (closedFiberSectionsEquiv S).toRingHom := by
  refine RingHom.ext fun z ↦ ?_
  obtain ⟨a, rfl⟩ := surjective_closedFiberSectionsMap S z
  change _ = L.equiv.symm (algebraMap _ _ (closedFiberSectionsEquiv S (closedFiberSectionsMap S a)))
  rw [closedFiberSectionsEquiv_apply]
  exact (RingEquiv.eq_symm_apply _).2 (L.equiv_sourceToBase a)

include L in
/-- **An affine open with a smooth lift is smooth over `S₀`.** -/
theorem smooth_toClosedFiber : Smooth (U.ι ≫ S.toClosedFiber) := by
  have := L.smooth
  refine (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mpr ?_
  rw [appTop_toClosedFiber_eq L]
  have := smooth_quotient (A := ↥(baseSectionsRing S)) (B := L.ring) (baseSectionsRing S).ideal
  exact (RingHom.Smooth.of_bijective (closedFiberSectionsEquiv S).bijective).comp
    ((RingHom.smooth_algebraMap.mpr inferInstance).comp
      (RingHom.Smooth.of_bijective L.equiv.symm.bijective))

end Lift

section Inter

variable {n : ℕ} {U : Fin (n + 1) → S.X.Opens} [∀ k, IsAffine (U k)] [S.X.IsSeparated]
  (L : ∀ k, SmoothLift S (U k).ι)

omit [S.X.IsSeparated] in
include L in
/-- **The intersection of affine opens with smooth lifts is smooth over `S₀`.** -/
theorem smooth_inter_toClosedFiber : Smooth ((inter U).ι ≫ S.toClosedFiber) := by
  have := smooth_toClosedFiber (L 0)
  rw [← Scheme.homOfLE_ι S.X (inter_le U 0), Category.assoc]
  infer_instance

variable (U) in
/-- `Γ(U_0 ∩ ⋯ ∩ U_n)` as an `A / I`-algebra, through `A / I ≅ Γ(S₀)`. -/
abbrev interQuotientAlgebra :
    Algebra (↥(baseSectionsRing S) ⧸ (baseSectionsRing S).ideal) Γ((inter U).toScheme, ⊤) :=
  (quotientSectionsMap ((inter U).ι ≫ S.toClosedFiber)).toAlgebra

omit [∀ (k : Fin (n + 1)), IsAffine ↑(U k)] [S.X.IsSeparated] in
variable (U) in
/-- The `A`- and `A / I`-algebra structures of `Γ(U_0 ∩ ⋯ ∩ U_n)` are compatible. -/
theorem isScalarTower_interQuotient :
    letI := interAlgebra U
    letI := interQuotientAlgebra U
    IsScalarTower ↥(baseSectionsRing S) (↥(baseSectionsRing S) ⧸ (baseSectionsRing S).ideal)
      Γ((inter U).toScheme, ⊤) := by
  let := interAlgebra U
  let := interQuotientAlgebra U
  refine IsScalarTower.of_algebraMap_eq fun a ↦ ?_
  change (sourceToBase (overSituation S (inter U).ι)).appTop.hom a =
    quotientSectionsMap ((inter U).ι ≫ S.toClosedFiber) (Ideal.Quotient.mk _ a)
  rw [quotientSectionsMap_mk]

include L in
/-- **`Γ(U_0 ∩ ⋯ ∩ U_n)` is smooth over `A / I`.** -/
theorem smooth_interQuotient :
    letI := interQuotientAlgebra U
    Algebra.Smooth (↥(baseSectionsRing S) ⧸ (baseSectionsRing S).ideal)
      Γ((inter U).toScheme, ⊤) :=
  (RingHom.Smooth.of_bijective (closedFiberSectionsEquiv S).symm.bijective).comp
    ((HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp (smooth_inter_toClosedFiber L))

end Inter

end QuotientAlgebra

/-! ### Divided power envelopes along an isomorphism of algebras -/

section EnvelopeTransport

variable {A : DividedPowerRing.{u}} {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂] [Algebra A B₁]
  [Algebra A B₂] (e : B₁ ≃ₐ[A] B₂) {J₁ : Ideal B₁} {J₂ : Ideal B₂}
  {hJ₁ : A.ideal.map (algebraMap A B₁) ≤ J₁} {hJ₂ : A.ideal.map (algebraMap A B₂) ≤ J₂}
  (h₁₂ : J₁.map e.toRingHom ≤ J₂) (D₁ : DividedPowerEnvelope A (algebraMap A B₁) J₁ hJ₁)
  (D₂ : DividedPowerEnvelope A (algebraMap A B₂) J₂ hJ₂)

/-- An isomorphism of algebras is compatible with the structure maps. -/
theorem algEquiv_comp_algebraMap :
    e.toRingHom.comp (algebraMap A B₁) =
      (algebraMap A B₂).comp (DividedPowers.DPMorphism.id A.dividedPowers).toRingHom :=
  RingHom.ext e.commutes

/-- The divided power morphism of envelopes along an isomorphism of algebras. -/
def envelopeTransport : DividedPowers.DPMorphism D₁.object.dividedPowers D₂.object.dividedPowers :=
  (envelopePairMap D₁ D₂ (DividedPowers.DPMorphism.id A.dividedPowers) e.toRingHom h₁₂
    (algEquiv_comp_algebraMap e)).1

/-- `envelopeTransport` restricts to the isomorphism of algebras. -/
theorem envelopeTransport_algebraMap (x : B₁) :
    (envelopeTransport e h₁₂ D₁ D₂).toRingHom (D₁.algebraMap.toRingHom x) =
      D₂.algebraMap.toRingHom (e x) :=
  envelopePairMap_algebraMap D₁ D₂ _ _ h₁₂ _ x

/-- `envelopeTransport` is a map over the base. -/
theorem envelopeTransport_structureMap (a : A) :
    (envelopeTransport e h₁₂ D₁ D₂).toRingHom (D₁.structureMap.toRingHom a) =
      D₂.structureMap.toRingHom a :=
  envelopePairMap_structureMap D₁ D₂ _ _ h₁₂ _ a

/-- `envelopeTransport` along the inverse isomorphism is a left inverse. -/
theorem envelopeTransport_symm_comp (h₂₁ : J₂.map e.symm.toRingHom ≤ J₁) :
    (envelopeTransport e.symm h₂₁ D₂ D₁).comp (envelopeTransport e h₁₂ D₁ D₂) =
      DividedPowers.DPMorphism.id D₁.object.dividedPowers := by
  refine envelopeHom_ext D₁ D₁.object _ _ ?_ ?_
  · refine DividedPowers.DPMorphism.ext (funext fun a ↦ ?_)
    change (envelopeTransport e.symm h₂₁ D₂ D₁).toRingHom
      ((envelopeTransport e h₁₂ D₁ D₂).toRingHom (D₁.structureMap.toRingHom a)) =
        D₁.structureMap.toRingHom a
    rw [envelopeTransport_structureMap, envelopeTransport_structureMap]
  · refine RingHom.ext fun x ↦ ?_
    change (envelopeTransport e.symm h₂₁ D₂ D₁).toRingHom
      ((envelopeTransport e h₁₂ D₁ D₂).toRingHom (D₁.algebraMap.toRingHom x)) =
        D₁.algebraMap.toRingHom x
    rw [envelopeTransport_algebraMap, envelopeTransport_algebraMap, AlgEquiv.symm_apply_apply]

/-- **The envelopes of two ideals matched by an isomorphism of algebras are isomorphic.** -/
theorem bijective_envelopeTransport (h₂₁ : J₂.map e.symm.toRingHom ≤ J₁) :
    Function.Bijective (envelopeTransport e h₁₂ D₁ D₂).toRingHom := by
  have h₂₁' : J₁.map e.symm.symm.toRingHom ≤ J₂ := h₁₂
  refine ⟨Function.LeftInverse.injective (g := (envelopeTransport e.symm h₂₁ D₂ D₁).toRingHom)
    fun x ↦ ?_, Function.RightInverse.surjective
      (g := (envelopeTransport e.symm h₂₁ D₂ D₁).toRingHom) fun y ↦ ?_⟩
  · exact congrArg (fun φ : DividedPowers.DPMorphism D₁.object.dividedPowers
      D₁.object.dividedPowers ↦ φ.toRingHom x) (envelopeTransport_symm_comp e h₁₂ D₁ D₂ h₂₁)
  · exact congrArg (fun φ : DividedPowers.DPMorphism D₂.object.dividedPowers
      D₂.object.dividedPowers ↦ φ.toRingHom y)
        (envelopeTransport_symm_comp e.symm h₂₁ D₂ D₁ h₂₁')

end EnvelopeTransport

/-! ### Base change of the values of a quasi-coherent module along a change-of-base map -/

section Values

variable {S S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}
  {P : Thickening S} {P' : Thickening S'} (m : (changeBase S S' f g h).obj P ⟶ P')

/-- `m` on global sections is compatible with the maps from `A'` and `A`. -/
theorem changeBase_targetHom_appTop_toBase (a : Γ(S'.S.scheme, ⊤)) :
    m.targetHom.hom.appTop.hom (P'.toBase.hom.appTop.hom a) =
      P.toBase.hom.appTop.hom (baseChangeRingHom f a) := by
  refine (targetHom_appTop_toBase m a).trans ?_
  change ((P.toBase ≫ f).hom.appTop.hom a) = _
  simp only [DividedPowerScheme.Hom.comp_hom, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]
  rfl

variable (N : SheafOfModules.{u} (crystallineStructureSheaf S'))

/-- **The restriction `N(T') → N(u T)` along `m : u(T) ⟶ T'`, as a map of `A'`-modules**, `A'`
acting on `N(T')` through `T' ⟶ S'` and on `N(u T)` through `A' → A` and `T ⟶ S`. -/
def changeBaseValuesMap :
    letI : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op P')) :=
      Module.compHom (R := crysSheafRing S' P') _ P'.toBase.hom.appTop.hom
    letI : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
      Module.compHom (R := crysSheafRing S' ((changeBase S S' f g h).obj P)) _
        (P.toBase.hom.appTop.hom.comp (baseChangeRingHom f))
    N.val.obj (op P') →ₗ[Γ(S'.S.scheme, ⊤)] N.val.obj (op ((changeBase S S' f g h).obj P)) :=
  letI : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op P')) :=
    Module.compHom (R := crysSheafRing S' P') _ P'.toBase.hom.appTop.hom
  letI : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
    Module.compHom (R := crysSheafRing S' ((changeBase S S' f g h).obj P)) _
      (P.toBase.hom.appTop.hom.comp (baseChangeRingHom f))
  { toFun := moduleSiteRestrict N m
    map_add' := map_add _
    map_smul' := fun a x ↦ by
      change moduleSiteRestrict N m ((show crysSheafRing S' P' from
        P'.toBase.hom.appTop.hom a) • x) = (show crysSheafRing S' ((changeBase S S' f g h).obj P)
          from P.toBase.hom.appTop.hom (baseChangeRingHom f a)) • moduleSiteRestrict N m x
      rw [LinearMap.map_smulₛₗ]
      exact congrArg (fun r : crysSheafRing S' ((changeBase S S' f g h).obj P) ↦
        r • moduleSiteRestrict N m x) (changeBase_targetHom_appTop_toBase m a) }

/-- The value of `changeBaseValuesMap`. -/
theorem changeBaseValuesMap_apply (x : N.val.obj (op P')) :
    changeBaseValuesMap m N x = moduleSiteRestrict N m x := rfl

variable [IsAffine P.thickening.target.scheme] [IsAffine P'.thickening.target.scheme]

/-- **Termwise base change criterion.**  If `Γ(u T) = A ⊗_{A'} Γ(T')` along `m`, then
`N(u T) = A ⊗_{A'} N(T')` for every quasi-coherent `N`: the base change of sections
`Γ(u T) ⊗_{Γ(T')} N(T') ≅ N(u T)` ([Stacks, Tag 07IT]) composed with the pushout of rings. -/
theorem isBaseChange_changeBaseValuesMap (hN : N.IsQuasicoherentOnSite)
    (hring :
      letI : Algebra Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤) := (baseChangeRingHom f).toAlgebra
      letI : Algebra Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') :=
        RingHom.toAlgebra (S := crysSheafRing S' P') P'.toBase.hom.appTop.hom
      letI : Algebra Γ(S.S.scheme, ⊤) (ringAlong m) :=
        RingHom.toAlgebra (S := ringAlong m) P.toBase.hom.appTop.hom
      letI : Algebra Γ(S'.S.scheme, ⊤) (ringAlong m) :=
        RingHom.toAlgebra (S := ringAlong m)
          (P.toBase.hom.appTop.hom.comp (baseChangeRingHom f))
      haveI : IsScalarTower Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤) (ringAlong m) :=
        IsScalarTower.of_algebraMap_eq' rfl
      haveI : IsScalarTower Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') (ringAlong m) :=
        IsScalarTower.of_algebraMap_eq fun a ↦ (changeBase_targetHom_appTop_toBase m a).symm
      Algebra.IsPushout Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤) (crysSheafRing S' P') (ringAlong m)) :
    letI : Algebra Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤) := (baseChangeRingHom f).toAlgebra
    letI : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op P')) :=
      Module.compHom (R := crysSheafRing S' P') _ P'.toBase.hom.appTop.hom
    letI : Module Γ(S.S.scheme, ⊤) (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
      Module.compHom (R := crysSheafRing S' ((changeBase S S' f g h).obj P)) _
        P.toBase.hom.appTop.hom
    letI : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
      Module.compHom (R := crysSheafRing S' ((changeBase S S' f g h).obj P)) _
        (P.toBase.hom.appTop.hom.comp (baseChangeRingHom f))
    haveI : IsScalarTower Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤)
        (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange Γ(S.S.scheme, ⊤) (changeBaseValuesMap m N) := by
  have : IsAffine ((changeBase S S' f g h).obj P).thickening.target.scheme :=
    inferInstanceAs (IsAffine P.thickening.target.scheme)
  let : Algebra Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤) := (baseChangeRingHom f).toAlgebra
  let : Algebra Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') :=
    RingHom.toAlgebra (S := crysSheafRing S' P') P'.toBase.hom.appTop.hom
  let : Algebra Γ(S.S.scheme, ⊤) (ringAlong m) :=
    RingHom.toAlgebra (S := ringAlong m) P.toBase.hom.appTop.hom
  let : Algebra Γ(S'.S.scheme, ⊤) (ringAlong m) :=
    RingHom.toAlgebra (S := ringAlong m)
      (P.toBase.hom.appTop.hom.comp (baseChangeRingHom f))
  have : IsScalarTower Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤) (ringAlong m) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') (ringAlong m) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (changeBase_targetHom_appTop_toBase m a).symm
  have := hring
  let : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op P')) :=
    Module.compHom (R := crysSheafRing S' P') _ P'.toBase.hom.appTop.hom
  have : IsScalarTower Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') (N.val.obj (op P')) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module (crysSheafRing S' P') (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
    Module.compHom _ (algebraMap (crysSheafRing S' P') (ringAlong m))
  have : IsScalarTower (crysSheafRing S' P') (ringAlong m)
      (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module Γ(S.S.scheme, ⊤) (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
    Module.compHom (R := crysSheafRing S' ((changeBase S S' f g h).obj P)) _
      P.toBase.hom.appTop.hom
  have : IsScalarTower Γ(S.S.scheme, ⊤) (ringAlong m)
      (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
    Module.compHom (R := crysSheafRing S' ((changeBase S S' f g h).obj P)) _
      (P.toBase.hom.appTop.hom.comp (baseChangeRingHom f))
  have : IsScalarTower Γ(S'.S.scheme, ⊤) (crysSheafRing S' P')
      (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
    IsScalarTower.of_algebraMap_smul fun a x ↦
      congrArg (fun r : crysSheafRing S' ((changeBase S S' f g h).obj P) ↦ r • x)
        (changeBase_targetHom_appTop_toBase m a)
  have : IsScalarTower Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤)
      (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let ρ : N.val.obj (op P') →ₗ[crysSheafRing S' P']
      N.val.obj (op ((changeBase S S' f g h).obj P)) :=
    { toFun := moduleSiteRestrict N m
      map_add' := map_add _
      map_smul' := fun r x ↦ LinearMap.map_smulₛₗ (moduleSiteRestrict N m) r x }
  have hR'R : IsScalarTower (crysSheafRing S' P') (ringAlong m)
      (N.val.obj (op ((changeBase S S' f g h).obj P))) := inferInstance
  have hρ : IsBaseChange (ringAlong m) ρ :=
    IsBaseChange.of_equiv (extensionSectionsLinearEquivAlong N m hN) fun x ↦ by
      rw [extensionSectionsLinearEquivAlong_tmul]
      change (1 : ringAlong m) • moduleSiteRestrict N m x = _
      exact one_smul _ _
  exact isBaseChange_restrictScalars_of_isPushout (A' := Γ(S'.S.scheme, ⊤))
    (A := Γ(S.S.scheme, ⊤)) (R' := crysSheafRing S' P') (R := ringAlong m) (towR'RN := hR'R) hρ

end Values

/-! ### Families of smooth lifts -/

section Family

variable {S S' : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme] [IsAffine S'.S.scheme]
  {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  (hpb : IsPullback g S.toClosedFiber S'.toClosedFiber (DividedPowerScheme.closedFiberMap f))

include hpb in
/-- `X = X' ×_{S'₀} S₀` is separated when `X'` is: `X ⟶ X'` is a base change of the affine, hence
separated, morphism `S₀ ⟶ S'₀`. -/
theorem isSeparated_of_isPullback [S'.X.IsSeparated] : S.X.IsSeparated := by
  have hg : IsSeparated g := MorphismProperty.of_isPullback hpb.flip
    (inferInstance : IsSeparated (DividedPowerScheme.closedFiberMap f))
  refine ⟨?_⟩
  rw [show terminal.from S.X = g ≫ terminal.from S'.X from (terminal.comp_from g).symm]
  infer_instance

variable (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) (hp' : IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤)))
  {n : ℕ} {U' : Fin (n + 1) → S'.X.Opens} [∀ k, IsAffine (U' k)] [∀ k, IsAffine (g ⁻¹ᵁ U' k)]
  [S'.X.IsSeparated] [S.X.IsSeparated] (L' : ∀ k, SmoothLift S' (U' k).ι)

/-- The base change `A ⊗_{A'} B'_k` of a family of smooth lifts, a family of smooth lifts of the
affine opens `g⁻¹ U'_k` of `X`. -/
abbrev baseChangeFamily : ∀ k, SmoothLift S (g ⁻¹ᵁ U' k).ι :=
  fun k ↦ (L' k).baseChange hpb

/-- **The change-of-base map of the Čech envelope objects.**  The envelope object
`(⋂ g⁻¹ U'_k, Spec D, δ)` of the base-changed family, rebased to `CRIS(X'/S')`, maps to the
envelope object `(⋂ U'_k, Spec D', δ')` of the family: its composite with the `k`-th projection
is the rebased `k`-th projection followed by the change-of-base map of the `k`-th lift. -/
def envelopeChangeBaseHom :
    (changeBase S S' f g h).obj (envelopeObject hp (baseChangeFamily hpb L')) ⟶
      envelopeObject hp' L' :=
  lift hp' L' fun k ↦ (changeBase S S' f g h).map (proj hp (baseChangeFamily hpb L') k) ≫
    changeBaseHom hpb h hp hp' (L' k)

/-- `envelopeChangeBaseHom` is compatible with the projections of the two envelope objects. -/
@[reassoc]
theorem envelopeChangeBaseHom_proj (k : Fin (n + 1)) :
    envelopeChangeBaseHom hpb h hp hp' L' ≫ proj hp' L' k =
      (changeBase S S' f g h).map (proj hp (baseChangeFamily hpb L') k) ≫
        changeBaseHom hpb h hp hp' (L' k) :=
  lift_proj hp' L' _ k

/-- `envelopeChangeBaseHom` is the only morphism compatible with the projections. -/
theorem eq_envelopeChangeBaseHom
    (m : (changeBase S S' f g h).obj (envelopeObject hp (baseChangeFamily hpb L')) ⟶
      envelopeObject hp' L')
    (hm : ∀ k, m ≫ proj hp' L' k = (changeBase S S' f g h).map
      (proj hp (baseChangeFamily hpb L') k) ≫ changeBaseHom hpb h hp hp' (L' k)) :
    m = envelopeChangeBaseHom hpb h hp hp' L' :=
  eq_lift hp' L' _ m hm

/-! ### The fibre product of the intersection -/

attribute [local instance] interAlgebra interQuotientAlgebra

omit [S'.X.IsSeparated] [S.X.IsSeparated] in
variable (f) in
/-- `I' ⊆ A' ∩ I`. -/
theorem ideal_le_comap :
    letI := baseSectionsAlgebra f
    (baseSectionsRing S').ideal ≤ (baseSectionsRing S).ideal.comap
      (algebraMap (baseSectionsRing S') (baseSectionsRing S)) :=
  let := baseSectionsAlgebra f
  Ideal.map_le_iff_le_comap.mp (map_ideal_le f)

omit [∀ (k : Fin (n + 1)), IsAffine ↑(U' k)] [S'.X.IsSeparated] [S.X.IsSeparated] in
variable (U') in
/-- `(A / I) ⊗_{A' / I'} Γ(U'_0 ∩ ⋯ ∩ U'_n)` is the pushout of
`Γ(U'_0 ∩ ⋯ ∩ U'_n) ← Γ(S'₀) → Γ(S₀)`. -/
theorem isPushout_interTensorQuotient :
    letI := baseSectionsAlgebra f
    letI := quotientAlgebraOfLE (ideal_le_comap f)
    IsPushout ((inter U').ι ≫ S'.toClosedFiber).appTop (DividedPowerScheme.closedFiberMap f).appTop
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Γ((inter U').toScheme, ⊤) →ₐ[↥(baseSectionsRing S') ⧸ (baseSectionsRing S').ideal]
          (↥(baseSectionsRing S) ⧸ (baseSectionsRing S).ideal) ⊗[↥(baseSectionsRing S') ⧸
            (baseSectionsRing S').ideal] Γ((inter U').toScheme, ⊤)).toRingHom)
      ((closedFiberSectionsEquiv S).toCommRingCatIso.hom ≫
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R :=
          ↥(baseSectionsRing S') ⧸ (baseSectionsRing S').ideal)
          (A := ↥(baseSectionsRing S) ⧸ (baseSectionsRing S).ideal)
          (B := Γ((inter U').toScheme, ⊤)))) := by
  let := baseSectionsAlgebra f
  let := quotientAlgebraOfLE (ideal_le_comap f)
  refine (CommRingCat.isPushout_tensorProduct
    (↥(baseSectionsRing S') ⧸ (baseSectionsRing S').ideal)
    (↥(baseSectionsRing S) ⧸ (baseSectionsRing S).ideal) Γ((inter U').toScheme, ⊤)).flip.of_iso
    (closedFiberSectionsEquiv S').symm.toCommRingCatIso (Iso.refl _)
    (closedFiberSectionsEquiv S).symm.toCommRingCatIso (Iso.refl _) ?_ ?_ ?_ ?_
  · rfl
  · ext a
    change (closedFiberSectionsEquiv S).symm (Ideal.Quotient.mk _ (baseSectionsRingHom f a)) =
      (DividedPowerScheme.closedFiberMap f).appTop.hom
        ((closedFiberSectionsEquiv S').symm (Ideal.Quotient.mk _ a))
    rw [closedFiberSectionsEquiv_symm_mk, closedFiberSectionsEquiv_symm_mk,
      closedFiberMap_appTop_closedFiberSectionsMap]
  · rfl
  · refine CommRingCat.hom_ext (RingHom.ext fun z ↦ ?_)
    change Algebra.TensorProduct.includeLeftRingHom z = Algebra.TensorProduct.includeLeftRingHom
      ((closedFiberSectionsEquiv S) ((closedFiberSectionsEquiv S).symm z))
    rw [RingEquiv.apply_symm_apply]

include hpb in
variable (U') in
/-- **`(A / I) ⊗_{A' / I'} Γ(U'_0 ∩ ⋯ ∩ U'_n) ≅ Γ(g⁻¹(U'_0 ∩ ⋯ ∩ U'_n))`.** -/
def interTensorQuotientIso :
    letI := baseSectionsAlgebra f
    letI := quotientAlgebraOfLE (ideal_le_comap f)
    CommRingCat.of ((↥(baseSectionsRing S) ⧸ (baseSectionsRing S).ideal) ⊗[↥(baseSectionsRing S') ⧸
        (baseSectionsRing S').ideal] Γ((inter U').toScheme, ⊤)) ≅
      Γ((g ⁻¹ᵁ inter U').toScheme, ⊤) :=
  (isPushout_interTensorQuotient U').isoIsPushout _ _ (isPushout_sections hpb (inter U'))

omit [∀ (k : Fin (n + 1)), IsAffine ↑(g ⁻¹ᵁ U' k)] [S.X.IsSeparated] in
/-- `interTensorQuotientIso` on `1 ⊗ c` is the pullback of `c` along `g`. -/
theorem interTensorQuotientIso_one_tmul (c : Γ((inter U').toScheme, ⊤)) :
    letI := baseSectionsAlgebra f
    letI := quotientAlgebraOfLE (ideal_le_comap f)
    (interTensorQuotientIso hpb U').hom.hom (1 ⊗ₜ c) = (g ∣_ inter U').appTop.hom c :=
  ConcreteCategory.congr_hom (IsPushout.inl_isoIsPushout_hom _ _
    (isPushout_interTensorQuotient U') (isPushout_sections hpb (inter U'))) c

omit [∀ (k : Fin (n + 1)), IsAffine ↑(g ⁻¹ᵁ U' k)] [S.X.IsSeparated] in
/-- `interTensorQuotientIso` on `z ⊗ 1` is the image of `z ∈ Γ(S₀)`. -/
theorem interTensorQuotientIso_tmul_one
    (z : ↥(baseSectionsRing S) ⧸ (baseSectionsRing S).ideal) :
    letI := baseSectionsAlgebra f
    letI := quotientAlgebraOfLE (ideal_le_comap f)
    (interTensorQuotientIso hpb U').hom.hom (z ⊗ₜ 1) =
      ((g ⁻¹ᵁ inter U').ι ≫ S.toClosedFiber).appTop.hom ((closedFiberSectionsEquiv S).symm z) := by
  let := baseSectionsAlgebra f
  let := quotientAlgebraOfLE (ideal_le_comap f)
  have h := ConcreteCategory.congr_hom (IsPushout.inr_isoIsPushout_hom _ _
    (isPushout_interTensorQuotient U') (isPushout_sections hpb (inter U')))
    ((closedFiberSectionsEquiv S).symm z)
  refine Eq.trans ?_ h
  change _ = (interTensorQuotientIso hpb U').hom.hom
    (((closedFiberSectionsEquiv S) ((closedFiberSectionsEquiv S).symm z)) ⊗ₜ 1)
  rw [RingEquiv.apply_symm_apply]

omit [IsAffine S.S.scheme] [IsAffine S'.S.scheme] in
omit [∀ k, IsAffine (U' k)] [∀ k, IsAffine (g ⁻¹ᵁ U' k)] [S'.X.IsSeparated] [S.X.IsSeparated] in
variable (g U') in
/-- The intersection of the preimages is the preimage of the intersection. -/
theorem inter_preimage : (inter fun k ↦ g ⁻¹ᵁ U' k) = g ⁻¹ᵁ inter U' := by
  refine SetLike.coe_injective ?_
  rw [TopologicalSpace.Opens.coe_iInf]
  ext x
  simp only [Set.mem_iInter]
  change (∀ k, g.base x ∈ U' k) ↔ g.base x ∈ ((⨅ k, U' k : S'.X.Opens) : Set S'.X)
  rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  rfl

omit [∀ k, IsAffine (U' k)] [∀ k, IsAffine (g ⁻¹ᵁ U' k)] [S'.X.IsSeparated] [S.X.IsSeparated] in
variable (g U') in
/-- Restriction `Γ(g⁻¹(U'_0 ∩ ⋯ ∩ U'_n)) → Γ(g⁻¹ U'_0 ∩ ⋯ ∩ g⁻¹ U'_n)`, an isomorphism. -/
abbrev interPreimageRestrict :
    Γ((g ⁻¹ᵁ inter U').toScheme, ⊤) →+* Γ((inter fun k ↦ g ⁻¹ᵁ U' k).toScheme, ⊤) :=
  (S.X.homOfLE (inter_preimage g U').le).appTop.hom

omit [IsAffine S.S.scheme] [IsAffine S'.S.scheme] in
omit [∀ k, IsAffine (U' k)] [∀ k, IsAffine (g ⁻¹ᵁ U' k)] [S'.X.IsSeparated] [S.X.IsSeparated] in
/-- `interPreimageRestrict` is injective. -/
theorem injective_interPreimageRestrict : Function.Injective (interPreimageRestrict g U') := by
  refine Function.LeftInverse.injective (g := (S.X.homOfLE (inter_preimage g U').ge).appTop.hom)
    fun x ↦ ?_
  have h := congrArg (fun k ↦ k.appTop.hom x)
    (S.X.homOfLE_homOfLE (inter_preimage g U').ge (inter_preimage g U').le)
  simp only [Scheme.homOfLE_rfl, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply] at h
  exact h

omit [IsAffine S.S.scheme] [IsAffine S'.S.scheme] in
omit [∀ k, IsAffine (U' k)] [∀ k, IsAffine (g ⁻¹ᵁ U' k)] [S'.X.IsSeparated] [S.X.IsSeparated] in
/-- The restriction of `g` to the intersection, compared with its restriction to `U'_k`. -/
theorem homOfLE_morphismRestrict (k : Fin (n + 1)) :
    S.X.homOfLE (inter_le (fun k ↦ g ⁻¹ᵁ U' k) k) ≫ g ∣_ U' k =
      S.X.homOfLE (inter_preimage g U').le ≫ g ∣_ inter U' ≫
        S'.X.homOfLE (inter_le U' k) := by
  rw [← cancel_mono (U' k).ι]
  simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc]

omit [IsAffine S.S.scheme] [IsAffine S'.S.scheme] in
omit [∀ (k : Fin (n + 1)), IsAffine ↑(U' k)] [S'.X.IsSeparated] in
omit [∀ k, IsAffine (g ⁻¹ᵁ U' k)] [S.X.IsSeparated] in
/-- The structure map to `S` of the intersection, through `g⁻¹(U'_0 ∩ ⋯ ∩ U'_n)`. -/
theorem interPreimageRestrict_toBase (a : baseSectionsRing S) :
    interPreimageRestrict g U' (((g ⁻¹ᵁ inter U').ι ≫ S.toClosedFiber).appTop.hom
      (closedFiberSectionsMap S a)) =
      (sourceToBase (overSituation S (inter fun k ↦ g ⁻¹ᵁ U' k).ι)).appTop.hom a := by
  have hs : S.X.homOfLE (inter_preimage g U').le ≫ (g ⁻¹ᵁ inter U').ι ≫ S.toClosedFiber ≫
      DividedPowerScheme.closedFiberι S.S =
      (inter fun k ↦ g ⁻¹ᵁ U' k).ι ≫ S.toClosedFiber ≫ DividedPowerScheme.closedFiberι S.S := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have h := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop hs) a
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  exact h

omit [∀ (k : Fin (n + 1)), IsAffine ↑(g ⁻¹ᵁ U' k)] [S.X.IsSeparated] in
/-- **`(A ⊗_{A'} ⨂ B'_k) → ⨂ (A ⊗_{A'} B'_k) → Γ(g⁻¹ U'_0 ∩ ⋯ ∩ g⁻¹ U'_n)` is the base change
`A ⊗_{A'} ⨂ B'_k → (A / I) ⊗_{A' / I'} Γ(U'_0 ∩ ⋯ ∩ U'_n)` followed by the fibre product
identification.** -/
theorem tensorMap_baseChange_eq :
    letI := baseSectionsAlgebra f
    letI := quotientAlgebraOfLE (ideal_le_comap f)
    haveI := isScalarTower_interQuotient U'
    (tensorMap (baseChangeFamily hpb L')).toRingHom.comp
        (piTensorBaseChangeEquiv ↥(baseSectionsRing S') ↥(baseSectionsRing S)
          fun k ↦ (L' k).ring).toRingHom =
      ((interPreimageRestrict g U').comp (interTensorQuotientIso hpb U').hom.hom).comp
        (tensorQuotientMap (tensorMap L') (ideal_le_comap f)) := by
  let := baseSectionsAlgebra f
  let := quotientAlgebraOfLE (ideal_le_comap f)
  have := isScalarTower_interQuotient U'
  have hA : ∀ a : baseSectionsRing S,
      tensorMap (baseChangeFamily hpb L') (piTensorBaseChangeEquiv ↥(baseSectionsRing S')
        ↥(baseSectionsRing S) (fun k ↦ (L' k).ring) (a ⊗ₜ 1)) =
      interPreimageRestrict g U' ((interTensorQuotientIso hpb U').hom.hom
        (tensorQuotientMap (tensorMap L') (ideal_le_comap f) (a ⊗ₜ 1))) := fun a ↦ by
    rw [tensorQuotientMap_tmul, map_one, interTensorQuotientIso_tmul_one,
      closedFiberSectionsEquiv_symm_mk, interPreimageRestrict_toBase]
    change tensorMap (baseChangeFamily hpb L') (piTensorBaseChangeEquiv ↥(baseSectionsRing S')
        ↥(baseSectionsRing S) (fun k ↦ (L' k).ring) (algebraMap _ _ a)) = _
    rw [AlgEquiv.commutes]
    exact (tensorMap (baseChangeFamily hpb L')).commutes a
  refine Algebra.TensorProduct.ringHom_ext (RingHom.ext hA)
    (piTensor_ringHom_ext (RingHom.ext fun a' ↦ ?_) fun k ↦ RingHom.ext fun b ↦ ?_)
  · have e : (1 : baseSectionsRing S) ⊗ₜ[baseSectionsRing S']
        algebraMap (baseSectionsRing S') (tensorRing L') a' =
        algebraMap (baseSectionsRing S') (baseSectionsRing S) a' ⊗ₜ 1 :=
      (Algebra.TensorProduct.tmul_one_eq_one_tmul a').symm
    change tensorMap (baseChangeFamily hpb L') (piTensorBaseChangeEquiv ↥(baseSectionsRing S')
        ↥(baseSectionsRing S) (fun k ↦ (L' k).ring) (1 ⊗ₜ algebraMap _ _ a')) =
      interPreimageRestrict g U' ((interTensorQuotientIso hpb U').hom.hom
        (tensorQuotientMap (tensorMap L') (ideal_le_comap f) (1 ⊗ₜ algebraMap _ _ a')))
    rw [e]
    exact hA _
  · change tensorMap (baseChangeFamily hpb L') (piTensorBaseChangeEquiv ↥(baseSectionsRing S')
        ↥(baseSectionsRing S) (fun k ↦ (L' k).ring) (1 ⊗ₜ PiTensorProduct.singleAlgHom k b)) =
      interPreimageRestrict g U' ((interTensorQuotientIso hpb U').hom.hom
        (tensorQuotientMap (tensorMap L') (ideal_le_comap f)
          (1 ⊗ₜ PiTensorProduct.singleAlgHom k b)))
    rw [piTensorBaseChangeEquiv_one_tmul_single]
    refine ((tensorMap_single (baseChangeFamily hpb L') k (1 ⊗ₜ b)).trans
      (component_apply _ k _)).trans ?_
    rw [tensorQuotientMap_tmul, map_one, tensorMap_single, component_apply,
      interTensorQuotientIso_one_tmul]
    set c := (L' k).equiv.symm (Ideal.Quotient.mk _ b) with hc
    have hc' : ((baseChangeFamily hpb L') k).equiv.symm (Ideal.Quotient.mk _ (1 ⊗ₜ b)) =
        (g ∣_ U' k).appTop.hom c := by
      refine (RingEquiv.symm_apply_eq _).2 ?_
      change _ = (baseChangeSectionsIso hpb (L' k)).hom.hom ((g ∣_ U' k).appTop.hom c)
      rw [baseChangeSectionsIso_restrict, hc, RingEquiv.apply_symm_apply]
      rfl
    rw [hc']
    have h := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop
      (homOfLE_morphismRestrict (g := g) (U' := U') k)) c
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using h

/-! ### The envelope of the base change is the base change of the envelope -/

omit [∀ (k : Fin (n + 1)), IsAffine ↑(g ⁻¹ᵁ U' k)] [S.X.IsSeparated] in
/-- The fibre product identification followed by `interPreimageRestrict` is
injective. -/
theorem injective_interPreimageRestrict_comp :
    Function.Injective
      ((interPreimageRestrict g U').comp (interTensorQuotientIso hpb U').hom.hom) :=
  injective_interPreimageRestrict.comp
    (interTensorQuotientIso hpb U').commRingCatIsoToRingEquiv.injective

omit [∀ (k : Fin (n + 1)), IsAffine ↑(g ⁻¹ᵁ U' k)] [S.X.IsSeparated] in
/-- **The kernel of `A ⊗_{A'} ⨂ B'_k → Γ(g⁻¹ U'_0 ∩ ⋯ ∩ g⁻¹ U'_n)` is that of the base change
`A ⊗_{A'} ⨂ B'_k → (A / I) ⊗_{A' / I'} Γ(U'_0 ∩ ⋯ ∩ U'_n)`.** -/
theorem tensorMap_baseChange_eq_zero_iff :
    letI := baseSectionsAlgebra f
    letI := quotientAlgebraOfLE (ideal_le_comap f)
    haveI := isScalarTower_interQuotient U'
    ∀ x : ↥(baseSectionsRing S) ⊗[↥(baseSectionsRing S')] tensorRing L',
    tensorMap (baseChangeFamily hpb L') (piTensorBaseChangeEquiv ↥(baseSectionsRing S')
        ↥(baseSectionsRing S) (fun k ↦ (L' k).ring) x) = 0 ↔
      tensorQuotientMap (tensorMap L') (ideal_le_comap f) x = 0 := by
  let := baseSectionsAlgebra f
  let := quotientAlgebraOfLE (ideal_le_comap f)
  have := isScalarTower_interQuotient U'
  intro x
  have h := RingHom.congr_fun (tensorMap_baseChange_eq hpb L') x
  refine ⟨fun hx ↦ injective_interPreimageRestrict_comp hpb ?_, fun hx ↦ ?_⟩
  · exact ((RingHom.comp_apply _ _ _).symm.trans h.symm).trans (hx.trans (map_zero _).symm)
  · exact h.trans (by rw [RingHom.comp_apply, hx, map_zero])

variable (f) in
/-- The divided power envelope of `ker(A ⊗_{A'} ⨂ B'_k → (A / I) ⊗_{A' / I'} Γ(U'_∩))`. -/
def baseChangeTensorEnvelope :
    letI := baseSectionsAlgebra f
    letI := quotientAlgebraOfLE (ideal_le_comap f)
    haveI := isScalarTower_interQuotient U'
    DividedPowerEnvelope (baseSectionsRing S)
      (algebraMap ↥(baseSectionsRing S) (↥(baseSectionsRing S) ⊗[↥(baseSectionsRing S')]
        tensorRing L')) (RingHom.ker (tensorQuotientMap (tensorMap L') (ideal_le_comap f)))
      ((ker_tensorQuotientMap (tensorMap L') (ideal_le_comap f) (surjective_tensorMap L')).symm ▸
        le_sup_right) :=
  dividedPowerEnvelope _ _ _ _

omit [S.X.IsSeparated] in
variable (f) in
/-- `K'` maps into the kernel of the base-changed presentation. -/
theorem includeRight_tensorIdeal_le :
    letI := baseSectionsAlgebra f
    letI := quotientAlgebraOfLE (ideal_le_comap f)
    haveI := isScalarTower_interQuotient U'
    (tensorIdeal L').map (Algebra.TensorProduct.includeRight :
        tensorRing L' →ₐ[baseSectionsRing S'] ↥(baseSectionsRing S) ⊗[↥(baseSectionsRing S')]
          tensorRing L').toRingHom ≤
      RingHom.ker (tensorQuotientMap (tensorMap L') (ideal_le_comap f)) := by
  let := baseSectionsAlgebra f
  let := quotientAlgebraOfLE (ideal_le_comap f)
  have := isScalarTower_interQuotient U'
  rw [ker_tensorQuotientMap (tensorMap L') (ideal_le_comap f) (surjective_tensorMap L')]
  exact le_sup_left

omit [S.X.IsSeparated] in
variable (f) in
include hp' in
/-- **Base change of the Čech envelope** ([Stacks, Tag 07MU], the hints): the canonical map
`A ⊗_{A'} D' → D_{A ⊗_{A'} ⨂ B'_k}` is bijective. -/
theorem bijective_baseChangeTensorEnvelope :
    letI := baseSectionsAlgebra f
    letI := quotientAlgebraOfLE (ideal_le_comap f)
    haveI := isScalarTower_interQuotient U'
    Function.Bijective (envelopeBaseChangeHom (globalSectionsDPMorphism f) rfl
      (includeRight_tensorIdeal_le f L') (envelope L') (baseChangeTensorEnvelope f L')) := by
  let := baseSectionsAlgebra f
  let := quotientAlgebraOfLE (ideal_le_comap f)
  have := isScalarTower_interQuotient U'
  have : ∀ k, Algebra.Smooth (baseSectionsRing S') (L' k).ring := fun k ↦ (L' k).smooth
  have := smooth_piTensorProduct (baseSectionsRing S') n fun k ↦ (L' k).ring
  have := smooth_interQuotient L'
  exact bijective_envelopeBaseChangeHom_of_smooth_ker (tensorMap L') (surjective_tensorMap L')
    S'.prime.out hp' (globalSectionsDPMorphism f) rfl (ideal_le_comap f)
    (includeRight_tensorIdeal_le f L') (envelope L') (baseChangeTensorEnvelope f L')

omit [∀ (k : Fin (n + 1)), IsAffine ↑(g ⁻¹ᵁ U' k)] [S.X.IsSeparated] in
/-- `A ⊗_{A'} ⨂ B'_k ≅ ⨂ (A ⊗_{A'} B'_k)` carries the kernel of the base-changed presentation
into `K`. -/
theorem map_ker_le_tensorIdeal :
    letI := baseSectionsAlgebra f
    letI := quotientAlgebraOfLE (ideal_le_comap f)
    haveI := isScalarTower_interQuotient U'
    (RingHom.ker (tensorQuotientMap (tensorMap L') (ideal_le_comap f))).map
        (piTensorBaseChangeEquiv ↥(baseSectionsRing S') ↥(baseSectionsRing S)
          fun k ↦ (L' k).ring).toRingHom ≤
      tensorIdeal (baseChangeFamily hpb L') := by
  let := baseSectionsAlgebra f
  let := quotientAlgebraOfLE (ideal_le_comap f)
  have := isScalarTower_interQuotient U'
  exact Ideal.map_le_iff_le_comap.mpr fun x hx ↦ (tensorMap_baseChange_eq_zero_iff hpb L' x).mpr hx

omit [∀ (k : Fin (n + 1)), IsAffine ↑(g ⁻¹ᵁ U' k)] [S.X.IsSeparated] in
/-- The inverse isomorphism carries `K` into the kernel of the base-changed presentation. -/
theorem tensorIdeal_map_le_ker :
    letI := baseSectionsAlgebra f
    letI := quotientAlgebraOfLE (ideal_le_comap f)
    haveI := isScalarTower_interQuotient U'
    (tensorIdeal (baseChangeFamily hpb L')).map
        (piTensorBaseChangeEquiv ↥(baseSectionsRing S') ↥(baseSectionsRing S)
          fun k ↦ (L' k).ring).symm.toRingHom ≤
      RingHom.ker (tensorQuotientMap (tensorMap L') (ideal_le_comap f)) := by
  let := baseSectionsAlgebra f
  let := quotientAlgebraOfLE (ideal_le_comap f)
  have := isScalarTower_interQuotient U'
  refine Ideal.map_le_iff_le_comap.mpr fun y hy ↦ ?_
  refine (tensorMap_baseChange_eq_zero_iff hpb L' _).mp ?_
  change tensorMap (baseChangeFamily hpb L') ((piTensorBaseChangeEquiv ↥(baseSectionsRing S')
    ↥(baseSectionsRing S) fun k ↦ (L' k).ring) ((piTensorBaseChangeEquiv ↥(baseSectionsRing S')
      ↥(baseSectionsRing S) fun k ↦ (L' k).ring).symm y)) = 0
  exact (congrArg (tensorMap (baseChangeFamily hpb L'))
    (AlgEquiv.apply_symm_apply _ y)).trans hy

/-- The divided power isomorphism `D_{A ⊗_{A'} ⨂ B'_k} ≅ D` along
`A ⊗_{A'} ⨂ B'_k ≅ ⨂ (A ⊗_{A'} B'_k)`. -/
def baseChangeEnvelopeTransport :
    DividedPowers.DPMorphism (baseChangeTensorEnvelope f L').object.dividedPowers
      (envelope (baseChangeFamily hpb L')).object.dividedPowers :=
  letI := baseSectionsAlgebra f
  letI := quotientAlgebraOfLE (ideal_le_comap f)
  haveI := isScalarTower_interQuotient U'
  envelopeTransport _ (map_ker_le_tensorIdeal hpb L') (baseChangeTensorEnvelope f L')
    (envelope (baseChangeFamily hpb L'))

/-- **The canonical map `A ⊗_{A'} D' → D`**, `a ⊗ d ↦ a · ψ(d)`, `ψ : D' → D` the divided power
morphism of envelopes over `A' → A`. -/
def envelopeBaseChangeRingHom :
    letI := baseSectionsAlgebra f
    letI : Algebra (baseSectionsRing S') (envelope L').object :=
      (envelope L').structureMap.toRingHom.toAlgebra
    ↥(baseSectionsRing S) ⊗[↥(baseSectionsRing S')] (envelope L').object →+*
      (envelope (baseChangeFamily hpb L')).object :=
  letI := baseSectionsAlgebra f
  letI := quotientAlgebraOfLE (ideal_le_comap f)
  haveI := isScalarTower_interQuotient U'
  (baseChangeEnvelopeTransport hpb L').toRingHom.comp
    (envelopeBaseChangeHom (globalSectionsDPMorphism f) rfl (includeRight_tensorIdeal_le f L')
      (envelope L') (baseChangeTensorEnvelope f L'))

omit [∀ (k : Fin (n + 1)), IsAffine ↑(g ⁻¹ᵁ U' k)] [S.X.IsSeparated] in
include hp' in
/-- **`A ⊗_{A'} D' ≅ D`**: the divided power envelope of the base-changed Čech data is the base
change of the divided power envelope. -/
theorem bijective_envelopeBaseChangeRingHom :
    Function.Bijective (envelopeBaseChangeRingHom hpb L') := by
  let := baseSectionsAlgebra f
  let := quotientAlgebraOfLE (ideal_le_comap f)
  have := isScalarTower_interQuotient U'
  change Function.Bijective (_ ∘ _)
  exact (bijective_envelopeTransport _ (map_ker_le_tensorIdeal hpb L') _ _
    (tensorIdeal_map_le_ker hpb L')).comp (bijective_baseChangeTensorEnvelope f hp' L')

/-- The divided power morphism `ψ : D' → D` of envelopes over `A' → A`. -/
def envelopeBaseChangePsi :
    DividedPowers.DPMorphism (envelope L').object.dividedPowers
      (envelope (baseChangeFamily hpb L')).object.dividedPowers :=
  letI := baseSectionsAlgebra f
  letI := quotientAlgebraOfLE (ideal_le_comap f)
  haveI := isScalarTower_interQuotient U'
  (baseChangeEnvelopeTransport hpb L').comp (envelopeBaseChangePairMap (globalSectionsDPMorphism f)
    rfl (includeRight_tensorIdeal_le f L') (envelope L') (baseChangeTensorEnvelope f L'))

omit [∀ (k : Fin (n + 1)), IsAffine ↑(g ⁻¹ᵁ U' k)] [S.X.IsSeparated] in
/-- `envelopeBaseChangeRingHom` on a pure tensor. -/
theorem envelopeBaseChangeRingHom_tmul (a : baseSectionsRing S) (d : (envelope L').object) :
    letI := baseSectionsAlgebra f
    letI : Algebra (baseSectionsRing S') (envelope L').object :=
      (envelope L').structureMap.toRingHom.toAlgebra
    envelopeBaseChangeRingHom hpb L' (a ⊗ₜ d) =
      (envelope (baseChangeFamily hpb L')).structureMap.toRingHom a *
        (envelopeBaseChangePsi hpb L').toRingHom d := by
  let := baseSectionsAlgebra f
  let := quotientAlgebraOfLE (ideal_le_comap f)
  have := isScalarTower_interQuotient U'
  change (baseChangeEnvelopeTransport hpb L').toRingHom
    ((baseChangeTensorEnvelope f L').structureMap.toRingHom a * _) = _
  rw [map_mul]
  exact congrArg (· * _) (envelopeTransport_structureMap _ _ _ _ a)

omit [∀ (k : Fin (n + 1)), IsAffine ↑(g ⁻¹ᵁ U' k)] [S.X.IsSeparated] in
/-- `ψ` lies over `A' → A`. -/
theorem envelopeBaseChangePsi_structureMap (a : baseSectionsRing S') :
    (envelopeBaseChangePsi hpb L').toRingHom ((envelope L').structureMap.toRingHom a) =
      (envelope (baseChangeFamily hpb L')).structureMap.toRingHom (baseSectionsRingHom f a) := by
  let := baseSectionsAlgebra f
  let := quotientAlgebraOfLE (ideal_le_comap f)
  have := isScalarTower_interQuotient U'
  change (baseChangeEnvelopeTransport hpb L').toRingHom ((envelopeBaseChangePairMap
    (globalSectionsDPMorphism f) rfl (includeRight_tensorIdeal_le f L') (envelope L')
      (baseChangeTensorEnvelope f L')).toRingHom ((envelope L').structureMap.toRingHom a)) = _
  refine (congrArg (baseChangeEnvelopeTransport hpb L').toRingHom
    (envelopeBaseChangePairMap_structureMap (globalSectionsDPMorphism f) rfl
      (includeRight_tensorIdeal_le f L') (envelope L') (baseChangeTensorEnvelope f L') a)).trans ?_
  exact envelopeTransport_structureMap _ _ _ _ _

omit [∀ (k : Fin (n + 1)), IsAffine ↑(g ⁻¹ᵁ U' k)] [S.X.IsSeparated] in
/-- `ψ` restricts to `x ↦ 1 ⊗ x` on `⨂ B'_k`. -/
theorem envelopeBaseChangePsi_algebraMap (x : tensorRing L') :
    letI := baseSectionsAlgebra f
    (envelopeBaseChangePsi hpb L').toRingHom ((envelope L').algebraMap.toRingHom x) =
      (envelope (baseChangeFamily hpb L')).algebraMap.toRingHom
        (piTensorBaseChangeEquiv ↥(baseSectionsRing S') ↥(baseSectionsRing S)
          (fun k ↦ (L' k).ring) (1 ⊗ₜ x)) := by
  let := baseSectionsAlgebra f
  let := quotientAlgebraOfLE (ideal_le_comap f)
  have := isScalarTower_interQuotient U'
  change (baseChangeEnvelopeTransport hpb L').toRingHom ((envelopeBaseChangePairMap
    (globalSectionsDPMorphism f) rfl (includeRight_tensorIdeal_le f L') (envelope L')
      (baseChangeTensorEnvelope f L')).toRingHom ((envelope L').algebraMap.toRingHom x)) = _
  refine (congrArg (baseChangeEnvelopeTransport hpb L').toRingHom
    (envelopeBaseChangePairMap_algebraMap (globalSectionsDPMorphism f) rfl
      (includeRight_tensorIdeal_le f L') (envelope L') (baseChangeTensorEnvelope f L') x)).trans ?_
  exact envelopeTransport_algebraMap _ _ _ _ _

/-! ### The change-of-base map of the envelope objects on global sections -/

attribute [local instance] targetAlgebra

/-- The legs `u(D) ⟶ D'_k` of the change-of-base map of the envelope objects. -/
abbrev envelopeChangeBaseLegs (k : Fin (n + 1)) :
    (changeBase S S' f g h).obj (envelopeObject hp (baseChangeFamily hpb L')) ⟶
      (L' k).object hp' :=
  (changeBase S S' f g h).map (proj hp (baseChangeFamily hpb L') k) ≫
    changeBaseHom hpb h hp hp' (L' k)

omit [S'.X.IsSeparated] in
/-- The map to the base of the rebased envelope object, on global sections. -/
theorem changeBaseObject_envelope_toBase_appTop (a : baseSectionsRing S') :
    ((changeBase S S' f g h).obj
        (envelopeObject hp (baseChangeFamily hpb L'))).toBase.hom.appTop.hom a =
      (Scheme.ΓSpecIso (CommRingCat.of (envelope (baseChangeFamily hpb L')).object)).inv.hom
        ((envelope (baseChangeFamily hpb L')).structureMap.toRingHom (baseSectionsRingHom f a)) :=
  (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop
    (envelopeObject hp (baseChangeFamily hpb L')).toBase.hom f.hom) a).trans
    (envelopeObject_toBase_appTop hp (baseChangeFamily hpb L') (f.hom.appTop.hom a))

omit [S'.X.IsSeparated] in
/-- The legs `B'_k → Γ(Spec D)` of the change-of-base map of the envelope objects are
`b ↦ 1 ⊗ b` in the `k`-th factor. -/
theorem legTensorMap_envelopeChangeBase :
    letI := baseSectionsAlgebra f
    (legTensorMap hp' L' (envelopeChangeBaseLegs hpb h hp hp' L')).toRingHom =
      (Scheme.ΓSpecIso (CommRingCat.of (envelope (baseChangeFamily hpb L')).object)).inv.hom.comp
        ((envelope (baseChangeFamily hpb L')).algebraMap.toRingHom.comp
          ((piTensorBaseChangeEquiv ↥(baseSectionsRing S') ↥(baseSectionsRing S)
            fun k ↦ (L' k).ring).toRingHom.comp
              (Algebra.TensorProduct.includeRight (R := ↥(baseSectionsRing S'))
                (A := ↥(baseSectionsRing S)) (B := tensorRing L')).toRingHom)) := by
  let := baseSectionsAlgebra f
  refine piTensor_ringHom_ext (RingHom.ext fun a' ↦ ?_) fun k ↦ RingHom.ext fun b ↦ ?_
  · have e : (1 : baseSectionsRing S) ⊗ₜ[baseSectionsRing S']
        algebraMap (baseSectionsRing S') (tensorRing L') a' =
        algebraMap (baseSectionsRing S) (↥(baseSectionsRing S) ⊗[↥(baseSectionsRing S')]
          tensorRing L') (algebraMap (baseSectionsRing S') (baseSectionsRing S) a') :=
      (Algebra.TensorProduct.tmul_one_eq_one_tmul a').symm
    change (legTensorMap hp' L' (envelopeChangeBaseLegs hpb h hp hp' L')) (algebraMap _ _ a') =
      (Scheme.ΓSpecIso _).inv.hom
      ((envelope (baseChangeFamily hpb L')).algebraMap.toRingHom
        ((piTensorBaseChangeEquiv ↥(baseSectionsRing S') ↥(baseSectionsRing S)
          fun k ↦ (L' k).ring) (1 ⊗ₜ algebraMap _ _ a')))
    rw [AlgHom.commutes, e, AlgEquiv.commutes]
    refine Eq.trans ?_ (congrArg (Scheme.ΓSpecIso _).inv.hom
      (RingHom.congr_fun (envelope (baseChangeFamily hpb L')).algebraMap_comp _).symm)
    exact changeBaseObject_envelope_toBase_appTop hpb h hp L' a'
  · change (legTensorMap hp' L' (envelopeChangeBaseLegs hpb h hp hp' L'))
      (PiTensorProduct.singleAlgHom k b) = (Scheme.ΓSpecIso _).inv.hom
      ((envelope (baseChangeFamily hpb L')).algebraMap.toRingHom
        ((piTensorBaseChangeEquiv ↥(baseSectionsRing S') ↥(baseSectionsRing S)
          fun k ↦ (L' k).ring) (1 ⊗ₜ PiTensorProduct.singleAlgHom k b)))
    rw [legTensorMap_single, legAlgHom_apply, piTensorBaseChangeEquiv_one_tmul_single]
    have h1 : (changeBaseHom hpb h hp hp' (L' k)).targetHom.hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (L' k).dividedPowerRing)).inv.hom b) =
        changeBaseRingHom hpb h hp (L' k) b :=
      (changeBaseHom_targetHom_appTop hpb h hp hp' (L' k) _).trans
        (congrArg (changeBaseRingHom hpb h hp (L' k))
          (DividedPowerScheme.ΓSpecIso_hom_inv_apply (CommRingCat.of (L' k).dividedPowerRing)
            (show (L' k).dividedPowerRing from b)))
    refine (targetHom_appTop_comp ((changeBase S S' f g h).map
      (proj hp (baseChangeFamily hpb L') k)) (changeBaseHom hpb h hp hp' (L' k)) _).trans ?_
    rw [h1]
    change (proj hp (baseChangeFamily hpb L') k).targetHom.hom.appTop.hom
      ((Scheme.ΓSpecIso _).inv.hom (1 ⊗ₜ b)) = _
    refine (proj_targetHom_appTop hp _ k _).trans ?_
    refine (congrArg (projRingHom hp _ k) (DividedPowerScheme.ΓSpecIso_hom_inv_apply
      (CommRingCat.of ((baseChangeFamily hpb L') k).dividedPowerRing)
      (show ((baseChangeFamily hpb L') k).dividedPowerRing from 1 ⊗ₜ b))).trans ?_
    rfl

/-- **The change-of-base map of the envelope objects on global sections is `ψ : D' → D`.** -/
theorem envelopeChangeBaseHom_appTop
    (z : Γ((envelopeObject hp' L').thickening.target.scheme, ⊤)) :
    (envelopeChangeBaseHom hpb h hp hp' L').targetHom.hom.appTop.hom z =
      (Scheme.ΓSpecIso (CommRingCat.of (envelope (baseChangeFamily hpb L')).object)).inv.hom
        ((envelopeBaseChangePsi hpb L').toRingHom
          ((Scheme.ΓSpecIso (CommRingCat.of (envelope L').object)).hom.hom z)) := by
  let := baseSectionsAlgebra f
  refine (liftTargetHom_appTop hp' L' _ z).trans ?_
  rw [liftSectionsMap_apply]
  generalize (Scheme.ΓSpecIso (CommRingCat.of (envelope L').object)).hom.hom z = d
  have key : legEnvelopeMap hp' L' (fun k ↦ (changeBase S S' f g h).map
      (proj hp (baseChangeFamily hpb L') k) ≫ changeBaseHom hpb h hp hp' (L' k)) =
      (DividedPowerScheme.specSectionsRingIso (envelope (baseChangeFamily hpb L')).object).hom.comp
        (envelopeBaseChangePsi hpb L') := by
    refine envelopeHom_ext (envelope L') _ _ _ ?_ ?_
    · refine DividedPowers.DPMorphism.ext (funext fun a ↦ ?_)
      refine (legEnvelopeMap_structureMap hp' L' _ a).trans ?_
      refine (changeBaseObject_envelope_toBase_appTop hpb h hp L' a).trans ?_
      exact congrArg (Scheme.ΓSpecIso _).inv.hom (envelopeBaseChangePsi_structureMap hpb L' a).symm
    · refine RingHom.ext fun x ↦ ?_
      refine (legEnvelopeMap_algebraMap hp' L' _ x).trans ?_
      refine (RingHom.congr_fun (legTensorMap_envelopeChangeBase hpb h hp hp' L') x).trans ?_
      exact congrArg (Scheme.ΓSpecIso _).inv.hom (envelopeBaseChangePsi_algebraMap hpb L' x).symm
  exact congrArg (fun φ : DividedPowers.DPMorphism _ _ ↦ φ.toRingHom d) key

/-! ### Objects isomorphic to the envelope objects -/

section Objects

variable {P : Thickening S} {P' : Thickening S'}
  (iP : P ≅ envelopeObject hp (baseChangeFamily hpb L')) (iP' : P' ≅ envelopeObject hp' L')

/-- `Γ(P') ≅ Γ(Spec D') ≅ D'`. -/
def sectionsEnvelopeEquiv' : Γ(P'.thickening.target.scheme, ⊤) ≃+* (envelope L').object :=
  (targetSectionsEquivOfIso iP'.symm).trans
    (Scheme.ΓSpecIso (CommRingCat.of (envelope L').object)).commRingCatIsoToRingEquiv

/-- `D ≅ Γ(Spec D) ≅ Γ(P)`. -/
def sectionsEnvelopeEquiv :
    (envelope (baseChangeFamily hpb L')).object ≃+* Γ(P.thickening.target.scheme, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of
    (envelope (baseChangeFamily hpb L')).object)).commRingCatIsoToRingEquiv.symm.trans
      (targetSectionsEquivOfIso iP)

omit [S'.X.IsSeparated] in
/-- `D ≅ Γ(P)` is compatible with the maps from `A`. -/
theorem sectionsEnvelopeEquiv_structureMap (a : baseSectionsRing S) :
    sectionsEnvelopeEquiv hpb hp L' iP
        ((envelope (baseChangeFamily hpb L')).structureMap.toRingHom a) =
      P.toBase.hom.appTop.hom a := by
  change iP.hom.targetHom.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom
    ((envelope (baseChangeFamily hpb L')).structureMap a)) = _
  refine (congrArg iP.hom.targetHom.hom.appTop.hom
    (envelopeObject_toBase_appTop hp (baseChangeFamily hpb L') a).symm).trans ?_
  exact targetHom_appTop_toBase iP.hom a

/-- `Γ(P') ≅ D'` is compatible with the maps from `A'`. -/
theorem sectionsEnvelopeEquiv'_toBase (a : baseSectionsRing S') :
    sectionsEnvelopeEquiv' hp' L' iP' (P'.toBase.hom.appTop.hom a) =
      (envelope L').structureMap.toRingHom a := by
  have h1 : iP'.inv.targetHom.hom.appTop.hom (P'.toBase.hom.appTop.hom a) =
      (envelopeObject hp' L').toBase.hom.appTop.hom a := targetHom_appTop_toBase iP'.inv a
  change (Scheme.ΓSpecIso (CommRingCat.of (envelope L').object)).hom.hom
    (iP'.inv.targetHom.hom.appTop.hom (P'.toBase.hom.appTop.hom a)) = _
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (envelope L').object)).hom.hom
    (h1.trans (envelopeObject_toBase_appTop hp' L' a))).trans ?_
  exact DividedPowerScheme.ΓSpecIso_hom_inv_apply _ _

variable {iP iP'} {m : (changeBase S S' f g h).obj P ⟶ P'}
  (hm : m ≫ iP'.hom = (changeBase S S' f g h).map iP.hom ≫ envelopeChangeBaseHom hpb h hp hp' L')

include hm in
/-- Under `Γ(P') ≅ D'` and `D ≅ Γ(P)`, `ψ : D' → D` is `m` on global sections. -/
theorem sectionsEnvelopeEquiv_psi (r : Γ(P'.thickening.target.scheme, ⊤)) :
    sectionsEnvelopeEquiv hpb hp L' iP ((envelopeBaseChangePsi hpb L').toRingHom
        (sectionsEnvelopeEquiv' hp' L' iP' r)) = m.targetHom.hom.appTop.hom r := by
  have h1 := envelopeChangeBaseHom_appTop hpb h hp hp' L' (iP'.inv.targetHom.hom.appTop.hom r)
  have h2 : (envelopeBaseChangePsi hpb L').toRingHom (sectionsEnvelopeEquiv' hp' L' iP' r) =
      (Scheme.ΓSpecIso (CommRingCat.of (envelope (baseChangeFamily hpb L')).object)).hom.hom
        ((envelopeChangeBaseHom hpb h hp hp' L').targetHom.hom.appTop.hom
          (iP'.inv.targetHom.hom.appTop.hom r)) :=
    ((congrArg (Scheme.ΓSpecIso
      (CommRingCat.of (envelope (baseChangeFamily hpb L')).object)).hom.hom h1).trans
        (DividedPowerScheme.ΓSpecIso_hom_inv_apply _ _)).symm
  have hm' : (changeBase S S' f g h).map iP.hom ≫ envelopeChangeBaseHom hpb h hp hp' L' ≫
      iP'.inv = m := by
    rw [← Category.assoc, ← hm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine (congrArg (sectionsEnvelopeEquiv hpb hp L' iP) h2).trans ?_
  refine (congrArg iP.hom.targetHom.hom.appTop.hom (ΓSpecIso_inv_hom_apply _ _)).trans ?_
  refine Eq.trans ?_ (congrArg (fun k ↦ k.targetHom.hom.appTop.hom r) hm')
  refine Eq.trans ?_ (targetHom_appTop_comp ((changeBase S S' f g h).map iP.hom)
    (envelopeChangeBaseHom hpb h hp hp' L' ≫ iP'.inv) r).symm
  exact congrArg iP.hom.targetHom.hom.appTop.hom
    (targetHom_appTop_comp (envelopeChangeBaseHom hpb h hp hp' L') iP'.inv r).symm

/-- `Γ(P') ≅ D'` as a map of `A'`-modules. -/
def sectionsEnvelopeLinearEquiv' :
    letI : Algebra Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') :=
      RingHom.toAlgebra (S := crysSheafRing S' P') P'.toBase.hom.appTop.hom
    letI : Algebra Γ(S'.S.scheme, ⊤) (envelope L').object :=
      RingHom.toAlgebra (R := Γ(S'.S.scheme, ⊤)) (envelope L').structureMap.toRingHom
    crysSheafRing S' P' ≃ₗ[Γ(S'.S.scheme, ⊤)] (envelope L').object :=
  letI : Algebra Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') :=
    RingHom.toAlgebra (S := crysSheafRing S' P') P'.toBase.hom.appTop.hom
  letI : Algebra Γ(S'.S.scheme, ⊤) (envelope L').object :=
    RingHom.toAlgebra (R := Γ(S'.S.scheme, ⊤)) (envelope L').structureMap.toRingHom
  { (sectionsEnvelopeEquiv' hp' L' iP').toAddEquiv with
    map_smul' := fun a r ↦ by
      change sectionsEnvelopeEquiv' hp' L' iP'
        ((show crysSheafRing S' P' from P'.toBase.hom.appTop.hom a) * r) =
        (envelope L').structureMap.toRingHom a * sectionsEnvelopeEquiv' hp' L' iP' r
      refine (map_mul (sectionsEnvelopeEquiv' hp' L' iP') _ _).trans ?_
      exact congrArg (· * sectionsEnvelopeEquiv' hp' L' iP' r)
        (sectionsEnvelopeEquiv'_toBase hp' L' iP' a) }

include hm in
/-- **`Γ(P) = A ⊗_{A'} Γ(P')` along `m`**, for `P`, `P'` isomorphic to the envelope objects
compatibly with the change-of-base map. -/
theorem isPushout_changeBase_of_iso :
    letI : Algebra Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤) := (baseChangeRingHom f).toAlgebra
    letI : Algebra Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') :=
      RingHom.toAlgebra (S := crysSheafRing S' P') P'.toBase.hom.appTop.hom
    letI : Algebra Γ(S.S.scheme, ⊤) (ringAlong m) :=
      RingHom.toAlgebra (S := ringAlong m) P.toBase.hom.appTop.hom
    letI : Algebra Γ(S'.S.scheme, ⊤) (ringAlong m) :=
      RingHom.toAlgebra (S := ringAlong m) (P.toBase.hom.appTop.hom.comp (baseChangeRingHom f))
    haveI : IsScalarTower Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤) (ringAlong m) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') (ringAlong m) :=
      IsScalarTower.of_algebraMap_eq fun a ↦ (changeBase_targetHom_appTop_toBase m a).symm
    Algebra.IsPushout Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤) (crysSheafRing S' P') (ringAlong m) := by
  let : Algebra Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤) := (baseChangeRingHom f).toAlgebra
  let : Algebra Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') :=
    RingHom.toAlgebra (S := crysSheafRing S' P') P'.toBase.hom.appTop.hom
  let : Algebra Γ(S.S.scheme, ⊤) (ringAlong m) :=
    RingHom.toAlgebra (S := ringAlong m) P.toBase.hom.appTop.hom
  let : Algebra Γ(S'.S.scheme, ⊤) (ringAlong m) :=
    RingHom.toAlgebra (S := ringAlong m) (P.toBase.hom.appTop.hom.comp (baseChangeRingHom f))
  have : IsScalarTower Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤) (ringAlong m) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') (ringAlong m) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (changeBase_targetHom_appTop_toBase m a).symm
  let : Algebra Γ(S'.S.scheme, ⊤) (envelope L').object :=
    RingHom.toAlgebra (R := Γ(S'.S.scheme, ⊤)) (envelope L').structureMap.toRingHom
  refine ⟨?_⟩
  let G : Γ(S.S.scheme, ⊤) ⊗[Γ(S'.S.scheme, ⊤)] crysSheafRing S' P' →+ ringAlong m :=
    ((sectionsEnvelopeEquiv hpb hp L' iP).toAddEquiv.toAddMonoidHom.comp
      (envelopeBaseChangeRingHom hpb L').toAddMonoidHom).comp
        (TensorProduct.congr (LinearEquiv.refl Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤))
          (sectionsEnvelopeLinearEquiv' hp' L' (iP' := iP'))).toAddEquiv.toAddMonoidHom
  have hG : Function.Bijective G :=
    (sectionsEnvelopeEquiv hpb hp L' iP).bijective.comp
      ((bijective_envelopeBaseChangeRingHom hpb hp' L').comp (TensorProduct.congr
        (LinearEquiv.refl Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤))
        (sectionsEnvelopeLinearEquiv' hp' L' (iP' := iP'))).bijective)
  refine (congrArg Function.Bijective (funext fun z ↦ ?_)).mpr hG
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a r =>
    rw [TensorProduct.lift.tmul]
    change a • algebraMap (crysSheafRing S' P') (ringAlong m) r = _
    rw [Algebra.smul_def]
    refine Eq.trans ?_ (congrArg (sectionsEnvelopeEquiv hpb hp L' iP)
      (envelopeBaseChangeRingHom_tmul hpb L' a
        (sectionsEnvelopeLinearEquiv' hp' L' (iP' := iP') r))).symm
    rw [map_mul]
    exact congrArg₂ (· * ·) (sectionsEnvelopeEquiv_structureMap hpb hp L' iP a).symm
      (sectionsEnvelopeEquiv_psi hpb h hp hp' L' hm r).symm

end Objects

end Family


/-! ### Products of the smooth-lift objects -/

section Products

variable {S S' : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme] [IsAffine S'.S.scheme]
  {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  (hpb : IsPullback g S.toClosedFiber S'.toClosedFiber (DividedPowerScheme.closedFiberMap f))
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) (hp' : IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤)))
  {n : ℕ} {U' : Fin (n + 1) → S'.X.Opens} [∀ k, IsAffine (U' k)] [∀ k, IsAffine (g ⁻¹ᵁ U' k)]
  [S'.X.IsSeparated] [S.X.IsSeparated] (L' : ∀ k, SmoothLift S' (U' k).ι)
  {P : Thickening S} {πP : ∀ k, P ⟶ ((L' k).baseChange hpb).object hp}
  (hP : IsLimit (Fan.mk P πP)) {P' : Thickening S'} {πP' : ∀ k, P' ⟶ (L' k).object hp'}
  (hP' : IsLimit (Fan.mk P' πP')) {m : (changeBase S S' f g h).obj P ⟶ P'}
  (hm : ∀ k, m ≫ πP' k = (changeBase S S' f g h).map (πP k) ≫ changeBaseHom hpb h hp hp' (L' k))

attribute [local instance] interAlgebra interQuotientAlgebra

/-- A product of the base-changed smooth-lift objects is the envelope object. -/
abbrev productIso : P ≅ envelopeObject hp (baseChangeFamily hpb L') :=
  hP.conePointUniqueUpToIso (isLimitFan hp (baseChangeFamily hpb L'))

/-- A product of the smooth-lift objects is the envelope object. -/
abbrev productIso' : P' ≅ envelopeObject hp' L' :=
  hP'.conePointUniqueUpToIso (isLimitFan hp' L')

omit [S'.X.IsSeparated] in
/-- `productIso` is compatible with the projections. -/
theorem productIso_hom_proj (k : Fin (n + 1)) :
    (productIso hpb hp L' hP).hom ≫ proj hp (baseChangeFamily hpb L') k = πP k :=
  hP.conePointUniqueUpToIso_hom_comp (isLimitFan hp (baseChangeFamily hpb L')) ⟨k⟩

/-- `productIso'` is compatible with the projections. -/
theorem productIso'_hom_proj (k : Fin (n + 1)) :
    (productIso' hp' L' hP').hom ≫ proj hp' L' k = πP' k :=
  hP'.conePointUniqueUpToIso_hom_comp (isLimitFan hp' L') ⟨k⟩

include hm in
/-- A morphism of products compatible with the projections is the change-of-base map of the
envelope objects. -/
theorem comp_productIso'_hom :
    m ≫ (productIso' hp' L' hP').hom =
      (changeBase S S' f g h).map (productIso hpb hp L' hP).hom ≫
        envelopeChangeBaseHom hpb h hp hp' L' := by
  refine (eq_lift hp' L' (fun k ↦ (changeBase S S' f g h).map (πP k) ≫
    changeBaseHom hpb h hp hp' (L' k)) _ fun k ↦ ?_).trans (eq_lift hp' L' _ _ fun k ↦ ?_).symm
  · rw [Category.assoc, productIso'_hom_proj, hm]
  · rw [Category.assoc, envelopeChangeBaseHom_proj, ← Category.assoc, ← Functor.map_comp,
      productIso_hom_proj]

include hm hP hP' in
/-- **Termwise base change of the Čech terms** ([Stacks, Tag 07MU], the hints, for
[Stacks, Tag 07N5]).  Let `X = X' ×_{S'₀} S₀`, `p` nilpotent, `B'_0, …, B'_n` smooth lifts of
affine opens of the separated scheme `X'`, `P'` a product of their objects of `CRIS(X'/S')`, `P`
a product of the objects of their base changes `A ⊗_{A'} B'_k` in `CRIS(X/S)`, and
`m : u(P) ⟶ P'` compatible with the projections and the change-of-base maps of the lifts.  For
every quasi-coherent `N` on `CRIS(X'/S')` the map `A ⊗_{A'} N(P') → N(u P)`,
`a ⊗ s ↦ a · m^* s`, is bijective. -/
theorem isBaseChange_changeBaseValuesMap_of_isLimit
    (N : SheafOfModules.{u} (crystallineStructureSheaf S')) (hN : N.IsQuasicoherentOnSite) :
    letI : Algebra Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤) := (baseChangeRingHom f).toAlgebra
    letI : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op P')) :=
      Module.compHom (R := crysSheafRing S' P') _ P'.toBase.hom.appTop.hom
    letI : Module Γ(S.S.scheme, ⊤) (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
      Module.compHom (R := crysSheafRing S' ((changeBase S S' f g h).obj P)) _
        P.toBase.hom.appTop.hom
    letI : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
      Module.compHom (R := crysSheafRing S' ((changeBase S S' f g h).obj P)) _
        (P.toBase.hom.appTop.hom.comp (baseChangeRingHom f))
    haveI : IsScalarTower Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤)
        (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange Γ(S.S.scheme, ⊤) (changeBaseValuesMap m N) := by
  have := isAffine_target_of_iso (productIso hpb hp L' hP)
  have := isAffine_target_of_iso (productIso' hp' L' hP')
  exact isBaseChange_changeBaseValuesMap m N hN
    (isPushout_changeBase_of_iso hpb h hp hp' L' (comp_productIso'_hom hpb h hp hp' L' hP hP' hm))

omit [∀ k, IsAffine (g ⁻¹ᵁ U' k)] [S.X.IsSeparated] in
include hP' in
/-- **The values of a crystal in finite locally free modules on a product of smooth-lift objects
are flat over `A'`**: the product is the envelope object, whose ring of sections is flat over
`A'` by [Stacks, Tag 07MU], the hints, and the values are flat over it by [Stacks, Tag 07IU]. -/
theorem flat_values_of_isLimit (N : SheafOfModules.{u} (crystallineStructureSheaf S'))
    (hN : IsFiniteLocallyFreeQuasicoherentCrystal N) :
    letI : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op P')) :=
      Module.compHom (R := crysSheafRing S' P') _ P'.toBase.hom.appTop.hom
    Module.Flat Γ(S'.S.scheme, ⊤) (N.val.obj (op P')) := by
  have := isAffine_target_of_iso (productIso' hp' L' hP')
  let : Algebra Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') :=
    RingHom.toAlgebra (S := crysSheafRing S' P') P'.toBase.hom.appTop.hom
  let : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op P')) :=
    Module.compHom (R := crysSheafRing S' P') _ P'.toBase.hom.appTop.hom
  have : IsScalarTower Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') (N.val.obj (op P')) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have := hN.flat_val_obj P'
  have := isScalarTower_interQuotient U'
  have : ∀ k, Algebra.Smooth (baseSectionsRing S') (L' k).ring := fun k ↦ (L' k).smooth
  have := smooth_piTensorProduct (baseSectionsRing S') n fun k ↦ (L' k).ring
  have := smooth_interQuotient L'
  have hD := flat_structureMap_dividedPowerEnvelope_of_smooth (tensorMap L')
    (surjective_tensorMap L') S'.prime.out hp' (envelope L')
  have he : algebraMap Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') =
      (sectionsEnvelopeEquiv' hp' L' (productIso' hp' L' hP')).symm.toRingHom.comp
        (envelope L').structureMap.toRingHom :=
    RingHom.ext fun a ↦ ((RingEquiv.eq_symm_apply _).mpr
      (sectionsEnvelopeEquiv'_toBase hp' L' (productIso' hp' L' hP') a))
  have : Module.Flat Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') := by
    refine RingHom.flat_algebraMap_iff.mp ?_
    rw [he]
    exact hD.comp (RingHom.Flat.of_bijective
      (sectionsEnvelopeEquiv' hp' L' (productIso' hp' L' hP')).symm.bijective)
  exact Module.Flat.trans Γ(S'.S.scheme, ⊤) (crysSheafRing S' P') (N.val.obj (op P'))

end Products

end Crystalline.GlobalCrystallineSituation.CechEnvelope
