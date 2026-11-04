module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Functoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusCrystalSituation
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist

/-!
# The Frobenius morphism of crystalline topoi

Let `(S, I, γ)` be an affine divided power scheme whose divided power ideal contains the prime
`p`, let `σ` be a divided power endomorphism of its ring of global sections with
`σ(x) ≡ x ^ p mod p`, and let `X` be a scheme over the closed fibre `S₀ = V(I)` on which `p` is
locally nilpotent.  This is the Frobenius-crystal situation `Crystalline.FCrystalSituation`.

Taking spectra turns `σ` into an endomorphism `Spec(σ) : S → S` of the divided power base: the
base being affine, the underlying morphism of schemes is transported along the canonical
isomorphism `S ≅ Spec Γ(S, ⊤)`, and it is a morphism of divided power schemes because on an
affine open the divided power ideal is the image of the ideal of global sections, so
compatibility over `Γ(S, ⊤)` propagates to every affine open and then, by the sheaf axiom, to
every open.

Since `p` lies in the divided power ideal it vanishes on `S₀`, hence on `X`; so `X` is a scheme
in characteristic `p` and has an absolute Frobenius `F_X : X → X`.  Modulo `p` the endomorphism
`σ` is the `p`-th power map, so the map that `Spec(σ)` induces on the closed fibre is exactly the
absolute Frobenius of `S₀`: `Spec(σ)` is a *lift* of `F_{S₀}`.  Naturality of the absolute
Frobenius then makes the square

```
  X  --F_X-->  X
  |            |
  v            v
  S₀ --F_{S₀}--> S₀
```

commute, which is precisely the datum that change of divided power base consumes.  Feeding
`Spec(σ)`, `F_X` and this square into `Crystalline.GlobalCrystallineSituation.changeBase` and
`Crystalline.GlobalCrystallineSituation.changeBaseMorphism` produces the Frobenius endofunctor of
the big crystalline category and the Frobenius morphism `(F_X)_cris` of crystalline topoi.

## Main definitions

* `Crystalline.FCrystalSituation.specSigmaScheme` — the endomorphism `Spec(σ)` of the underlying
  scheme of the divided power base.
* `Crystalline.FCrystalSituation.specSigma` — `Spec(σ)` as an endomorphism of the divided power
  base.
* `Crystalline.FCrystalSituation.frobenius` — the absolute Frobenius `F_X` of the source scheme.
* `Crystalline.FCrystalSituation.frobeniusChangeBase` — the Frobenius endofunctor of the big
  crystalline category of `X/S`.
* `Crystalline.FCrystalSituation.crystallineFrobenius` — the Frobenius morphism `(F_X)_cris` of
  crystalline topoi.

## Main results

* `Crystalline.FCrystalSituation.specSigma_appTop` — on global sections `Spec(σ)` is `σ`.
* `Crystalline.FCrystalSituation.isInCharacteristic` — the source scheme is in characteristic
  `p`.
* `Crystalline.FCrystalSituation.closedFiberMap_specSigma` — `Spec(σ)` lifts the absolute
  Frobenius of the closed fibre.
* `Crystalline.FCrystalSituation.toClosedFiber_comp_closedFiberMap_specSigma` — the Frobenius
  square over the closed fibre commutes.

## Implementation notes

The divided power compatibility of `Spec(σ)` is first proved over an affine open `V`, where
`Crystalline.DividedPowerScheme.map_ideal_top` presents the divided power ideal of `V` as the
image of the ideal of global sections and `DividedPowers.IsDPMorphism.of_comp` reduces the
assertion to the global one; both ideals and all divided powers are then local, so the general
case follows from the sheaf axiom on the structure sheaf and on the ideal subsheaf.

The closed fibre of an affine divided power scheme is affine and its ring of global sections is
a quotient of `Γ(S, ⊤)`, so two morphisms out of it agree as soon as they agree on the image of
`Γ(S, ⊤)`; that is how `Spec(σ)` is identified with the absolute Frobenius of `S₀`.

The prose of Stacks Section 60.26 lying between Situation 07N2 and Definition 07N3 carries no tag
of its own, so only the declarations instantiating Tag 07IC are tagged here.

## References

* [Stacks Project, Tag 07N2](https://stacks.math.columbia.edu/tag/07N2)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 03SM](https://stacks.math.columbia.edu/tag/03SM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.Frobenius

universe u

namespace Crystalline

/-- If `a` and `b ^ p` differ by a multiple of `p`, then a ring homomorphism killing `p` sends
`a` to the `p`-th power of the image of `b`. -/
private theorem apply_eq_pow_of_sub_eq {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    {p : ℕ} (hp : φ (p : A) = 0) {a b : A} (y : A) (hy : a - b ^ p = (p : A) * y) :
    φ a = φ b ^ p := by
  have h : φ a - φ (b ^ p) = 0 := by rw [← map_sub, hy, map_mul, hp, zero_mul]
  exact (sub_eq_zero.mp h).trans (map_pow φ b p)

namespace DividedPowerScheme

/-- **On an affine divided power scheme the divided power ideal is generated by global sections.**
Over an affine open `V` of a divided power scheme with affine ambient scheme, the divided power
ideal is the ideal generated by the image of the ideal of global sections: the ideal subsheaf is
quasi-coherent, hence an `AlgebraicGeometry.Scheme.IdealSheafData`, for which this is
`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal` applied to `V ≤ ⊤`. -/
theorem map_ideal_top (X : DividedPowerScheme.{u}) [IsAffine X.scheme]
    (V : X.scheme.affineOpens) :
    Ideal.map (X.scheme.presheaf.map (homOfLE (show V.1 ≤ ⊤ from le_top)).op).hom
        (X.ideal.obj (op ⊤)) = X.ideal.obj (op V.1) := by
  have h := (Stacks.Divisors.idealSheafDataOfSubmodule X.ideal).map_ideal
    (U := V) (V := ⟨⊤, isAffineOpen_top X.scheme⟩) (show V.1 ≤ ⊤ from le_top)
  rw [Stacks.Divisors.ideal_idealSheafDataOfSubmodule,
    Stacks.Divisors.ideal_idealSheafDataOfSubmodule] at h
  exact h

end DividedPowerScheme

namespace FCrystalSituation

variable (T : FCrystalSituation.{u})

/-- **The endomorphism `Spec(σ)` of the underlying scheme of the divided power base.**  The base
is affine, so it is canonically the spectrum of its ring of global sections, and the divided power
endomorphism `σ` of that ring is transported along this isomorphism. -/
def specSigmaScheme : T.global.S.scheme ⟶ T.global.S.scheme :=
  T.global.S.scheme.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom T.sigma.toRingHom) ≫ T.global.S.scheme.isoSpec.inv

/-- On global sections `Spec(σ)` is `σ`. -/
theorem specSigmaScheme_appTop :
    T.specSigmaScheme.appTop = CommRingCat.ofHom T.sigma.toRingHom := by
  have h := Scheme.isoSpec_inv_naturality T.specSigmaScheme
  apply Spec.map_injective
  refine (cancel_mono T.global.S.scheme.isoSpec.inv).1 ?_
  rw [h, specSigmaScheme]
  simp only [Iso.inv_hom_id_assoc]
  rfl

/-- Over an affine open of the base, `Spec(σ)` preserves the divided power ideal and commutes
with the divided powers: the ideal over an affine open is the image of the ideal of global
sections, so the assertion descends from the one over `Γ(S, ⊤)`, which is the hypothesis that `σ`
is a divided power endomorphism. -/
theorem specSigmaScheme_isDPMorphism_affine (V : T.global.S.scheme.affineOpens) :
    DividedPowers.IsDPMorphism (T.global.S.dividedPowers.dividedPowers (op V.1))
      (T.global.S.dividedPowers.dividedPowers (op (T.specSigmaScheme ⁻¹ᵁ V.1)))
      (T.specSigmaScheme.app V.1).hom := by
  apply DividedPowers.IsDPMorphism.of_comp
    (f := (T.global.S.scheme.presheaf.map (homOfLE (show V.1 ≤ ⊤ from le_top)).op).hom)
  · exact (DividedPowerScheme.map_ideal_top T.global.S V).symm
  · exact T.global.S.dividedPowers.naturality (homOfLE (show V.1 ≤ ⊤ from le_top)).op
  · refine isDPMorphism_of_eq (congrArg CommRingCat.Hom.hom
      (T.specSigmaScheme.naturality (homOfLE (show V.1 ≤ ⊤ from le_top)).op)).symm ?_
    refine DividedPowers.IsDPMorphism.comp _
      (T.global.S.dividedPowers.naturality
        (homOfLE (show T.specSigmaScheme ⁻¹ᵁ V.1 ≤ ⊤ from le_top)).op) ?_
    exact isDPMorphism_of_eq
      (congrArg CommRingCat.Hom.hom T.specSigmaScheme_appTop).symm T.sigma.isDPMorphism

/-- Over every open of the base, `Spec(σ)` preserves the divided power ideal and commutes with
the divided powers.  The affine opens form a basis, the ideal subsheaf is a sheaf and the divided
powers commute with restriction, so the affine case
`Crystalline.FCrystalSituation.specSigmaScheme_isDPMorphism_affine` suffices. -/
theorem specSigmaScheme_isDPMorphism (U : T.global.S.scheme.Opens) :
    DividedPowers.IsDPMorphism (T.global.S.dividedPowers.dividedPowers (op U))
      (T.global.S.dividedPowers.dividedPowers (op (T.specSigmaScheme ⁻¹ᵁ U)))
      (T.specSigmaScheme.app U).hom := by
  set f := T.specSigmaScheme with hf
  set I := T.global.S.ideal with hI
  set gamma := T.global.S.dividedPowers with hgamma
  have app_res {V W : T.global.S.scheme.Opens} (h : V ≤ W) (a : Γ(T.global.S.scheme, W)) :
      T.global.S.scheme.presheaf.map (homOfLE (f.preimage_mono h)).op (f.app W a) =
        f.app V (T.global.S.scheme.presheaf.map (homOfLE h).op a) :=
    (ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) a).symm
  have local_affine (z : T.global.S.scheme) (hz : z ∈ f ⁻¹ᵁ U) :
      ∃ V : T.global.S.scheme.affineOpens, V.1 ≤ U ∧ z ∈ f ⁻¹ᵁ V.1 := by
    obtain ⟨V, hV, hzV, hVU⟩ := Opens.isBasis_iff_nbhd.mp
      T.global.S.scheme.isBasis_affineOpens (show f.base z ∈ U from hz)
    exact ⟨⟨V, hV⟩, hVU, hzV⟩
  have app_mem (a : Γ(T.global.S.scheme, U)) (ha : a ∈ I.obj (op U)) :
      f.app U a ∈ I.obj (op (f ⁻¹ᵁ U)) := by
    apply I.isSheaf
    intro z hz
    obtain ⟨V, hVU, hzV⟩ := local_affine z hz
    refine ⟨f ⁻¹ᵁ V.1, homOfLE (f.preimage_mono hVU), ?_, hzV⟩
    change T.global.S.scheme.presheaf.map (homOfLE (f.preimage_mono hVU)).op (f.app U a) ∈
      I.obj (op (f ⁻¹ᵁ V.1))
    rw [app_res hVU a]
    exact (T.specSigmaScheme_isDPMorphism_affine V).ideal_comp
      (Ideal.mem_map_of_mem _ (I.map_mem (homOfLE hVU).op ha))
  refine ⟨Ideal.map_le_iff_le_comap.mpr fun a ha ↦ app_mem a ha, ?_⟩
  intro n a ha
  apply TopCat.Presheaf.IsSheaf.section_ext T.global.S.scheme.sheaf.property
  intro z hz
  obtain ⟨V, hVU, hzV⟩ := local_affine z hz
  refine ⟨f ⁻¹ᵁ V.1, f.preimage_mono hVU, hzV, ?_⟩
  have e₁ : T.global.S.scheme.presheaf.map (homOfLE (f.preimage_mono hVU)).op
        ((gamma.dividedPowers (op (f ⁻¹ᵁ U))).dpow n (f.app U a)) =
      (gamma.dividedPowers (op (f ⁻¹ᵁ V.1))).dpow n
        (T.global.S.scheme.presheaf.map (homOfLE (f.preimage_mono hVU)).op (f.app U a)) :=
    ((gamma.naturality (homOfLE (f.preimage_mono hVU)).op).dpow_comp _ (app_mem a ha)).symm
  have e₂ : (gamma.dividedPowers (op (f ⁻¹ᵁ V.1))).dpow n
        (T.global.S.scheme.presheaf.map (homOfLE (f.preimage_mono hVU)).op (f.app U a)) =
      (gamma.dividedPowers (op (f ⁻¹ᵁ V.1))).dpow n
        (f.app V.1 (T.global.S.scheme.presheaf.map (homOfLE hVU).op a)) :=
    congrArg _ (app_res hVU a)
  have e₃ : (gamma.dividedPowers (op (f ⁻¹ᵁ V.1))).dpow n
        (f.app V.1 (T.global.S.scheme.presheaf.map (homOfLE hVU).op a)) =
      f.app V.1 ((gamma.dividedPowers (op V.1)).dpow n
        (T.global.S.scheme.presheaf.map (homOfLE hVU).op a)) :=
    (T.specSigmaScheme_isDPMorphism_affine V).dpow_comp _ (I.map_mem (homOfLE hVU).op ha)
  have e₄ : f.app V.1 ((gamma.dividedPowers (op V.1)).dpow n
        (T.global.S.scheme.presheaf.map (homOfLE hVU).op a)) =
      f.app V.1 (T.global.S.scheme.presheaf.map (homOfLE hVU).op
        ((gamma.dividedPowers (op U)).dpow n a)) :=
    congrArg _ ((gamma.naturality (homOfLE hVU).op).dpow_comp a ha)
  have e₅ : f.app V.1 (T.global.S.scheme.presheaf.map (homOfLE hVU).op
        ((gamma.dividedPowers (op U)).dpow n a)) =
      T.global.S.scheme.presheaf.map (homOfLE (f.preimage_mono hVU)).op
        (f.app U ((gamma.dividedPowers (op U)).dpow n a)) :=
    (app_res hVU _).symm
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))

/-- **`Spec(σ)` as an endomorphism of the divided power base.** -/
def specSigma : T.global.S ⟶ T.global.S where
  hom := T.specSigmaScheme
  compatible := T.specSigmaScheme_isDPMorphism

/-- The underlying morphism of schemes of `Spec(σ)`. -/
@[simp]
theorem specSigma_hom : T.specSigma.hom = T.specSigmaScheme := rfl

/-- On global sections the divided power endomorphism `Spec(σ)` is `σ`. -/
theorem specSigma_appTop :
    T.specSigma.hom.appTop = CommRingCat.ofHom T.sigma.toRingHom :=
  T.specSigmaScheme_appTop

/-- The prime vanishes on global sections of the base after restriction to the closed fibre: it
belongs to the divided power ideal, which the closed immersion of the closed fibre kills. -/
theorem closedFiberι_appTop_prime :
    (DividedPowerScheme.closedFiberι T.global.S).appTop
        (T.global.p : Γ(T.global.S.scheme, ⊤)) = 0 :=
  (DividedPowerScheme.closedFiberPresentation T.global.S).app_eq_zero_of_mem ⊤
    (T.global.p : Γ(T.global.S.scheme, ⊤)) T.prime_mem

/-- The closed fibre `S₀ = V(I)` is a scheme in characteristic `p`, the prime belonging to the
divided power ideal. -/
theorem isInCharacteristic_closedFiber :
    IsInCharacteristic (DividedPowerScheme.closedFiber T.global.S) T.global.p := by
  have h := T.closedFiberι_appTop_prime
  rw [map_natCast] at h
  exact h

/-- **The source scheme is in characteristic `p`.**  The prime lies in the divided power ideal,
hence vanishes on the closed fibre `S₀`, over which `X` lives. -/
theorem isInCharacteristic : IsInCharacteristic T.global.X T.global.p :=
  isInCharacteristic_of_hom T.global.toClosedFiber T.global.p T.isInCharacteristic_closedFiber

/-- The closed fibre of an affine divided power base is affine: it is a closed subscheme of an
affine scheme. -/
instance isAffine_closedFiber : IsAffine (DividedPowerScheme.closedFiber T.global.S) :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine
    (DividedPowerScheme.closedFiberι T.global.S)).1

/-- **The absolute Frobenius `F_X` of the source scheme.**  It is the identity on points and the
`p`-th power map on the structure sheaf. -/
def frobenius : T.global.X ⟶ T.global.X :=
  absoluteFrobenius T.global.X T.global.p T.isInCharacteristic

/-- On the closed fibre, `σ` becomes the `p`-th power map: `σ(x) - x ^ p` is a multiple of `p`,
and `p` vanishes on the closed fibre. -/
theorem closedFiberι_appTop_sigma (x : Γ(T.global.S.scheme, ⊤)) :
    (DividedPowerScheme.closedFiberι T.global.S).appTop (T.sigma x) =
      (DividedPowerScheme.closedFiberι T.global.S).appTop x ^ T.global.p := by
  obtain ⟨y, hy⟩ := T.sigma_mod_prime x
  exact apply_eq_pow_of_sub_eq (DividedPowerScheme.closedFiberι T.global.S).appTop.hom
    T.closedFiberι_appTop_prime y hy

/-- **`Spec(σ)` is a lift of the absolute Frobenius of the closed fibre.**  The ring of global
sections of `S₀` is a quotient of `Γ(S, ⊤)`, on whose image both maps agree: `Spec(σ)` acts by
`σ`, the absolute Frobenius by the `p`-th power map, and `σ(x) - x ^ p` is a multiple of `p`,
which vanishes on `S₀`. -/
theorem closedFiberMap_specSigma :
    DividedPowerScheme.closedFiberMap T.specSigma =
      absoluteFrobenius (DividedPowerScheme.closedFiber T.global.S) T.global.p
        T.isInCharacteristic_closedFiber := by
  have hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine
    (DividedPowerScheme.closedFiberι T.global.S)).2
  have hleft (x : Γ(T.global.S.scheme, ⊤)) :
      (DividedPowerScheme.closedFiberMap T.specSigma).appTop
          ((DividedPowerScheme.closedFiberι T.global.S).appTop x) =
        (DividedPowerScheme.closedFiberι T.global.S).appTop (T.specSigma.hom.appTop x) := by
    have h := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop
      (DividedPowerScheme.closedFiberMap_comp_closedFiberι T.specSigma)) x
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using h
  have hsigma (x : Γ(T.global.S.scheme, ⊤)) : T.specSigma.hom.appTop x = T.sigma x :=
    ConcreteCategory.congr_hom T.specSigma_appTop x
  refine ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun z ↦ ?_))
  obtain ⟨x, rfl⟩ := hsurj z
  exact (hleft x).trans ((congrArg _ (hsigma x)).trans
    ((T.closedFiberι_appTop_sigma x).trans
      (absoluteFrobenius_app_apply _ T.global.p T.isInCharacteristic_closedFiber ⊤ _).symm))

/-- **The Frobenius square over the closed fibre commutes.**  The map induced by `Spec(σ)` on
closed fibres is the absolute Frobenius of `S₀`, and the absolute Frobenius is natural. -/
theorem toClosedFiber_comp_closedFiberMap_specSigma :
    T.global.toClosedFiber ≫ DividedPowerScheme.closedFiberMap T.specSigma =
      T.frobenius ≫ T.global.toClosedFiber := by
  rw [T.closedFiberMap_specSigma, frobenius]
  exact (absoluteFrobenius_naturality T.global.toClosedFiber T.global.p T.isInCharacteristic
    T.isInCharacteristic_closedFiber).symm

/-- **The Frobenius endofunctor of the big crystalline category of `X/S`.**  Change of divided
power base along `Spec(σ)` and the absolute Frobenius of `X`. -/
@[stacks 07IC "the functor, for the Frobenius of a Frobenius-crystal situation"]
def frobeniusChangeBase :
    GlobalCrystallineSituation.Thickening T.global ⥤
      GlobalCrystallineSituation.Thickening T.global :=
  GlobalCrystallineSituation.changeBase T.global T.global T.specSigma T.frobenius
    T.toClosedFiber_comp_closedFiberMap_specSigma

/-- **The Frobenius morphism `(F_X)_cris : (X/S)_cris ⟶ (X/S)_cris` of crystalline topoi.**  It
is the morphism of topoi induced by change of divided power base along `Spec(σ)` and the absolute
Frobenius of `X`. -/
@[stacks 07IC "the morphism of topoi, for the Frobenius of a Frobenius-crystal situation"]
def crystallineFrobenius :
    MorphismOfTopoi (GlobalCrystallineSituation.topos T.global)
      (GlobalCrystallineSituation.topos T.global) :=
  GlobalCrystallineSituation.changeBaseMorphism T.global T.global T.specSigma T.frobenius
    T.toClosedFiber_comp_closedFiberMap_specSigma

end FCrystalSituation

end Crystalline

end
