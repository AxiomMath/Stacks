module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.AddVariables
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeFunctoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.StrongLiftingEnvelope
public import StacksFrontier.RingTheory.Tor.Flatness

/-!
# Divided power envelopes and flat extensions of the algebra

Fix a divided power ring `(A, I, γ)`, a ring map `A → B` and an ideal `J ⊆ B` containing `I B`.
This file collects the consequences of Stacks 07HD (`Crystalline.dividedPowerEnvelope_baseChange`)
for a *flat* ring map `B → B'`: the divided power envelope of `J B'` is `D_B(J) ⊗_B B'`, and in
particular envelopes commute with localization.

## Main results

* `Crystalline.DividedPowerEnvelope.copy` — an envelope for some data is an envelope for any data
  equal to them, with the same divided power ring.
* `Crystalline.exists_envelope_tensor_equiv_of_flat` — `D_B(J) ⊗_B B' ≅ D_{B'}(J B')` for `B → B'`
  flat, by the canonical map.
* `Crystalline.isLocalization_away_envelopeAlgebraMapHom` — the envelope over `B_r` is the
  localization of the envelope over `B` away from `r`.
* `Crystalline.isNilpotent_envelope_algebraMap_of_mem` — if `p` is nilpotent in `A`, the elements
  of `J` become nilpotent in the envelope.

## References

* [Stacks Project, Tag 07HD](https://stacks.math.columbia.edu/tag/07HD)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Crystalline

open DividedPowers CategoryTheory

section Copy

variable {A : DividedPowerRing.{u}} {B : Type u} [CommRing B]

/-- An envelope of `J` relative to `f` is an envelope of any `J'` relative to any `f'` equal to
them: the same divided power ring with the same structural maps. -/
noncomputable def DividedPowerEnvelope.copy {f f' : A →+* B} {J J' : Ideal B}
    {hJ : A.ideal.map f ≤ J} (D : DividedPowerEnvelope A f J hJ) (hf : f' = f) (hJ' : J' = J)
    (h : A.ideal.map f' ≤ J') : DividedPowerEnvelope A f' J' h where
  object := D.object
  structureMap := D.structureMap
  algebraMap := IdealPair.Hom.ofRingHom D.algebraMap.toRingHom (by
    subst hJ'; exact D.algebraMap.ideal_comp)
  algebraMap_comp := by subst hf; exact D.algebraMap_comp
  homEquiv C a := by subst hf; subst hJ'; exact D.homEquiv C a
  homEquiv_apply C a q := by subst hf; subst hJ'; exact D.homEquiv_apply C a q

end Copy

section FlatBaseChange

variable {A : DividedPowerRing.{u}} {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B B']

/-- Stacks 07HD for a flat ring map `B → B'`: the envelope of `J B'` is `D_B(J) ⊗_B B'`, by the
ring isomorphism `x ⊗ y ↦ κ(x) · y`, where `κ` is the base-change morphism of envelopes. -/
theorem dividedPowerEnvelope_baseChange_of_flat [Module.Flat B B'] (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ)
    (D' : DividedPowerEnvelope A ((algebraMap B B').comp f)
      (J.map (algebraMap B B'))
      (map_baseIdeal_le_map f (algebraMap B B') J hJ)) :
    letI : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra;
    ∃ e : (D.object ⊗[B] B') ≃+* D'.object,
      ∀ x y, e (x ⊗ₜ[B] y) =
        (baseChangeDPMorphism f (algebraMap B B') J hJ D D').toRingHom x *
          D'.algebraMap.toRingHom y := by
  refine dividedPowerEnvelope_baseChange f J hJ D D' ?_ ?_
  · exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B' (A.ideal.map f)).toLinearEquiv
  · have h := (Module.Flat.tfae_isZero_Tor' (ModuleCat.of B B')).out 1 4
    exact h.mp (inferInstanceAs (Module.Flat B B')) (A.ideal.map f)

/-- The canonical morphism of envelopes along `B → B'`. -/
noncomputable def envelopeAlgebraMapHom {f : A →+* B} {J : Ideal B} {hJ : A.ideal.map f ≤ J}
    (D : DividedPowerEnvelope A f J hJ) {f' : A →+* B'} {J' : Ideal B'}
    {hJ' : A.ideal.map f' ≤ J'} (D' : DividedPowerEnvelope A f' J' hJ')
    (hf : f' = (algebraMap B B').comp f) (hJJ : J.map (algebraMap B B') ≤ J') :
    DividedPowers.DPMorphism D.object.dividedPowers D'.object.dividedPowers :=
  (envelopePairMap D D' (DividedPowers.DPMorphism.id A.dividedPowers) (algebraMap B B') hJJ
    (by rw [hf]; rfl)).1

/-- The morphism of envelopes along `B → B'` restricts to `B → B'` on the image of `B`. -/
theorem envelopeAlgebraMapHom_algebraMap {f : A →+* B} {J : Ideal B}
    {hJ : A.ideal.map f ≤ J}
    (D : DividedPowerEnvelope A f J hJ) {f' : A →+* B'} {J' : Ideal B'}
    {hJ' : A.ideal.map f' ≤ J'} (D' : DividedPowerEnvelope A f' J' hJ')
    (hf : f' = (algebraMap B B').comp f) (hJJ : J.map (algebraMap B B') ≤ J') (x : B) :
    (envelopeAlgebraMapHom D D' hf hJJ).toRingHom (D.algebraMap.toRingHom x) =
      D'.algebraMap.toRingHom (algebraMap B B' x) :=
  envelopePairMap_algebraMap D D' _ _ hJJ _ x

/-- The morphism of envelopes along `B → B'` is compatible with the structure maps. -/
theorem envelopeAlgebraMapHom_structureMap {f : A →+* B} {J : Ideal B}
    {hJ : A.ideal.map f ≤ J}
    (D : DividedPowerEnvelope A f J hJ) {f' : A →+* B'} {J' : Ideal B'}
    {hJ' : A.ideal.map f' ≤ J'} (D' : DividedPowerEnvelope A f' J' hJ')
    (hf : f' = (algebraMap B B').comp f) (hJJ : J.map (algebraMap B B') ≤ J') (z : A) :
    (envelopeAlgebraMapHom D D' hf hJJ).toRingHom (D.structureMap.toRingHom z) =
      D'.structureMap.toRingHom z :=
  envelopePairMap_structureMap D D' _ _ hJJ _ z

/-- **Flat base change of a divided power envelope.** For `B → B'` flat, the envelope of
`J B' ⊆ B'` is `D_B(J) ⊗_B B'`, by the ring isomorphism `x ⊗ y ↦ κ(x) · y`, where `κ` is the
morphism of envelopes along `B → B'`. The data of the second envelope only have to be equal to
the base-changed data. -/
theorem exists_envelope_tensor_equiv_of_flat [Module.Flat B B'] {f : A →+* B} {J : Ideal B}
    {hJ : A.ideal.map f ≤ J}
    (D : DividedPowerEnvelope A f J hJ) {f' : A →+* B'} {J' : Ideal B'}
    {hJ' : A.ideal.map f' ≤ J'} (D' : DividedPowerEnvelope A f' J' hJ')
    (hf : f' = (algebraMap B B').comp f) (hJJ : J' = J.map (algebraMap B B')) :
    letI : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra;
    ∃ e : (D.object ⊗[B] B') ≃+* D'.object,
      ∀ x y, e (x ⊗ₜ[B] y) =
        (envelopeAlgebraMapHom D D' hf hJJ.ge).toRingHom x * D'.algebraMap.toRingHom y := by
  let : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra
  let D'' := D'.copy (f' := (algebraMap B B').comp f) (J' := J.map (algebraMap B B')) hf.symm
    hJJ.symm (map_baseIdeal_le_map f (algebraMap B B') J hJ)
  obtain ⟨e, he⟩ := dividedPowerEnvelope_baseChange_of_flat f J hJ D D''
  have hκ : baseChangeDPMorphism f (algebraMap B B') J hJ D D'' =
      envelopeAlgebraMapHom D D' hf hJJ.ge := by
    refine eq_envelopePairMap D D' (DividedPowers.DPMorphism.id A.dividedPowers)
      (algebraMap B B') hJJ.ge (by rw [hf]; rfl) _ ?_ ?_
    · exact DividedPowers.DPMorphism.ext
        (funext (envelopeAlgebraMapHom_structureMap D D'' rfl le_rfl))
    · exact envelopeAlgebraMapHom_algebraMap D D'' rfl le_rfl
  refine ⟨e, fun x y => (he x y).trans ?_⟩
  rw [hκ]
  rfl

/-- **Envelopes commute with localization.** If `B'` is the localization of `B` away from `r`, the
envelope of `J B'` is the localization of the envelope of `J` away from the image of `r`. -/
theorem isLocalization_away_envelopeAlgebraMapHom (r : B) [IsLocalization.Away r B']
    {f : A →+* B} {J : Ideal B} {hJ : A.ideal.map f ≤ J}
    (D : DividedPowerEnvelope A f J hJ) {f' : A →+* B'} {J' : Ideal B'}
    {hJ' : A.ideal.map f' ≤ J'} (D' : DividedPowerEnvelope A f' J' hJ')
    (hf : f' = (algebraMap B B').comp f) (hJJ : J' = J.map (algebraMap B B')) :
    letI : Algebra D.object D'.object :=
      (envelopeAlgebraMapHom D D' hf hJJ.ge).toRingHom.toAlgebra
    IsLocalization.Away (D.algebraMap.toRingHom r) D'.object := by
  let : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra
  let : Algebra D.object D'.object :=
    (envelopeAlgebraMapHom D D' hf hJJ.ge).toRingHom.toAlgebra
  have : Module.Flat B B' := IsLocalization.flat B' (Submonoid.powers r)
  obtain ⟨e, he⟩ := exists_envelope_tensor_equiv_of_flat D D' hf hJJ
  let e' : (D.object ⊗[B] B') ≃ₐ[D.object] D'.object :=
    AlgEquiv.ofRingEquiv (f := e) (fun x => by
      change e (x ⊗ₜ[B] 1) = _
      rw [he, map_one, mul_one]
      rfl)
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap B D.object r)) e'

/-- If `p` is nilpotent in the base, every element of `J` becomes nilpotent in the envelope. -/
theorem isNilpotent_envelope_algebraMap_of_mem {p : ℕ} (hp : p.Prime)
    (hpA : IsNilpotent (p : A)) {f : A →+* B} {J : Ideal B} {hJ : A.ideal.map f ≤ J}
    (D : DividedPowerEnvelope A f J hJ) {j : B} (hj : j ∈ J) :
    IsNilpotent (D.algebraMap.toRingHom j) := by
  have hpD : IsNilpotent (p : D.object) := by simpa using hpA.map D.structureMap.toRingHom
  exact locallyNilpotent_dpIdeal hp D.object hpD _
    (D.algebraMap.ideal_comp (Ideal.mem_map_of_mem _ hj))

end FlatBaseChange

section Coordinates

variable {A : DividedPowerRing.{u}}

/-- The envelope of the divided power ideal of `A` itself is `A`: its structure map is
bijective. -/
theorem bijective_structureMap_envelope_self
    (D : DividedPowerEnvelope A (RingHom.id A) A.ideal (by rw [Ideal.map_id])) :
    Function.Bijective D.structureMap.toRingHom := by
  let r := ((D.homEquiv A (DividedPowers.DPMorphism.id A.dividedPowers)).symm
    ⟨IdealPair.Hom.ofRingHom (RingHom.id A) (by rw [Ideal.map_id]),
      IdealPair.Hom.ext_toRingHom _ _ rfl⟩)
  have hr (z : A) : r.1.toRingHom (D.structureMap.toRingHom z) = z :=
    congrArg (fun q => q.toRingHom z) r.2
  have hsr (y : D.object) : D.structureMap.toRingHom (r.1.toRingHom y) = y := by
    have halg : D.algebraMap.toRingHom = D.structureMap.toRingHom := by
      simpa using D.algebraMap_comp
    have hz (z : A) : D.structureMap.toRingHom (r.1.toRingHom (D.structureMap.toRingHom z)) =
        D.structureMap.toRingHom z := by rw [hr]
    have h := envelopeHom_ext D D.object (D.structureMap.comp r.1)
      (DividedPowers.DPMorphism.id D.object.dividedPowers)
      (DividedPowers.DPMorphism.ext (funext hz)) (by rw [halg]; exact RingHom.ext hz)
    exact congrArg (fun q => q.toRingHom y) h
  exact Function.bijective_iff_has_inverse.mpr ⟨r.1.toRingHom, hr, hsr⟩

end Coordinates

end Crystalline
