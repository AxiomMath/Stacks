module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.StalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Models.Basic
public import StacksFrontier.AlgebraicGeometry.Normalization.BaseChangeToCompletion
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.Regular.AscentAlongRegularRingHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normalization of a model of a geometrically normal variety

Let `R` be a discrete valuation ring with fraction field `K` and let `X` be a model over `R` of a
`K`-scheme `V` which is geometrically normal, that is, a flat finite-type `R`-scheme together with
an identification of its generic fibre with `V`.  Three things are true of the normalization
`ν : X^ν → X`: it is a finite morphism, its base change to the completion `R^∧` is the
normalization of the base change of `X`, and the completion of the local ring of `X^ν` at every
point is a normal ring.

## Main results

* `Stacks.Models.isFinite_normalization_of_isModel`: the normalization of a model of a
  geometrically normal variety is finite.
* `Stacks.Models.exists_iso_baseChange_normalization_adicCompletion_of_isModel`: the base change
  of the normalization to `Spec R^∧` is the normalization of the base change of the model,
  compatibly with the two normalization morphisms.
* `Stacks.Models.isNormalRing_adicCompletion_stalk_normalization_of_isModel`: the completion of
  the local ring of the normalization at any point is normal.
* `Stacks.Models.isNormalRing_stalk`: the local rings of a normal scheme are normal rings. An
  auxiliary step of the above, exported because it is the library's only statement of this fact.

## Implementation notes

The first two assertions are the two halves of Tag 0BG9, specialized to the completion of a
discrete valuation ring: `isNormal_complementSpecialFiber_baseChange_adicCompletion` turns
geometric normality of the generic fibre into normality of the complement of the special fibre
after completion, which is exactly the hypothesis of
`isFinite_normalization_of_isNormal_complementSpecialFiber_completion` and of
`exists_iso_pullback_normalization_completion_of_isNormal_complementSpecialFiber`.  Only local
finite type and the generic-fibre identification of a model are used for these two; flatness and
quasi-compactness play no role, and the generic fibre need not be a variety.

Tag 0BG9 compares `X^ν ×_X Y` with the normalization of `Y = X ×_{Spec R} Spec R^∧`.  Since the
source statement speaks of the base change of `X^ν` to `Spec R^∧`, the comparison is transported
along the pasting isomorphism `X^ν ×_X (X ×_{Spec R} Spec R^∧) ≅ X^ν ×_{Spec R} Spec R^∧`; the
identity this needs is isolated as `pullbackRightPullbackFstIso_inv_snd_eq_map`.

For the third assertion the point `x ∈ X^ν` is separated into the two cases of the source proof,
according to whether it lies in the generic or in the special fibre.  Both reduce to: a normal
local ring essentially of finite type over an excellent ring has normal completion, because such a
ring is excellent, hence a G-ring, so the map to its completion is regular and normality ascends
along a regular map.  In the generic-fibre case the base is the local ring of `Spec R` at the zero
ideal, which is the fraction field of `R`; in the special-fibre case `R` itself need not be
excellent, so the point is moved to the base change `X^ν ×_{Spec R} Spec R^∧`, whose base
`R^∧` is a complete Noetherian local ring and therefore excellent, and whose local rings have the
same completions as those of `X^ν` at points of the special fibre (Tag 0BG5).  Normality of the
base-changed scheme is supplied by the second assertion.

## References

* [Stacks Project, Tag 0C2T](https://stacks.math.columbia.edu/tag/0C2T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.SemistableReduction

namespace Stacks.Models

universe u

/-! ### Auxiliary results -/

/-- The pasting isomorphism `W ×_X (X ×_Z Y) ≅ W ×_Z Y` carries the second projection of the
left-hand pullback to the comparison morphism `W ×_Z Y → X ×_Z Y`. -/
private theorem pullbackRightPullbackFstIso_inv_snd_eq_map {W X Y Z : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) (f' : W ⟶ X) :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd f' (pullback.fst f g) =
      pullback.map (f' ≫ f) g f g f' (𝟙 _) (𝟙 _) (by simp) (by simp) := by
  apply pullback.hom_ext <;> simp [pullback.map]

/-- The local rings of a normal scheme are normal rings. -/
theorem isNormalRing_stalk {Y : Scheme.{u}} (hY : IsNormal Y) (y : Y) :
    IsNormalRing (Y.presheaf.stalk y) := by
  let : IsDomain (Y.presheaf.stalk y) := hY.stalk_isDomain y
  let : IsIntegrallyClosed (Y.presheaf.stalk y) := hY.stalk_normal y
  exact IsNormalRing.of_isIntegrallyClosed _

/-- The local ring of the spectrum of a ring at a point is excellent as soon as the corresponding
localization of the ring is, the two being isomorphic. -/
private theorem isExcellent_stalk_spec_of_localization {A : Type u} [CommRing A]
    (q : PrimeSpectrum A) (h : IsExcellent (Localization.AtPrime q.asIdeal)) :
    IsExcellent ((Spec (.of A)).presheaf.stalk q) := by
  let e := (Spec.stalkIso (.of A) q).commRingCatIsoToRingEquiv.symm
  let : Algebra (Localization.AtPrime q.asIdeal) ((Spec (.of A)).presheaf.stalk q) :=
    e.toRingHom.toAlgebra
  have : Algebra.EssFiniteType (Localization.AtPrime q.asIdeal)
      ((Spec (.of A)).presheaf.stalk q) :=
    Algebra.EssFiniteType.of_surjective (Algebra.ofId _ _) e.surjective
  exact (isQuasiExcellent_and_isExcellent_of_essFiniteType.{u, u}).2 h

/-- The local ring of the spectrum of an excellent ring at a point is excellent, being a
localization and hence essentially of finite type. -/
@[ega "IV 7.8.3" "(ii), special case"]
private theorem isExcellent_stalk_spec {A : Type u} [CommRing A] (hA : IsExcellent A)
    (q : PrimeSpectrum A) : IsExcellent ((Spec (.of A)).presheaf.stalk q) := by
  let : q.asIdeal.IsPrime := q.isPrime
  refine isExcellent_stalk_spec_of_localization q ?_
  let : Algebra.EssFiniteType A (Localization.AtPrime q.asIdeal) :=
    Algebra.EssFiniteType.of_isLocalization _ q.asIdeal.primeCompl
  exact (isQuasiExcellent_and_isExcellent_of_essFiniteType.{u, u}).2 hA

/-- The local ring of the spectrum of a domain at its zero ideal is the fraction field, hence
excellent. -/
private theorem isExcellent_stalk_spec_of_eq_bot {A : Type u} [CommRing A] [IsDomain A]
    (q : PrimeSpectrum A) (hq : q.asIdeal = ⊥) :
    IsExcellent ((Spec (.of A)).presheaf.stalk q) := by
  let : q.asIdeal.IsPrime := q.isPrime
  refine isExcellent_stalk_spec_of_localization q ?_
  have hM : q.asIdeal.primeCompl = nonZeroDivisors A := by
    ext a
    change a ∉ q.asIdeal ↔ a ∈ nonZeroDivisors A
    rw [hq]
    simp [mem_nonZeroDivisors_iff_ne_zero]
  let : IsLocalization (nonZeroDivisors A) (Localization.AtPrime q.asIdeal) := by
    rw [← hM]
    infer_instance
  let : Field (Localization.AtPrime q.asIdeal) := IsFractionRing.toField A
  exact (isExcellent_of_standard_classes_and_finiteType.{u, u}).1 _

/-- The local rings of a scheme locally of finite type over an affine base are essentially of
finite type over the local rings of the base, so they are excellent as soon as the latter are. -/
@[ega "IV 7.8.3" "(ii)"]
private theorem isExcellent_stalk_of_locallyOfFiniteType {A : Type u} [CommRing A]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of A)) [LocallyOfFiniteType f] (z : Z)
    (hS : IsExcellent ((Spec (.of A)).presheaf.stalk (f.base z))) :
    IsExcellent (Z.presheaf.stalk z) := by
  algebraize [(f.stalkMap z).hom]
  have hess : Algebra.EssFiniteType ((Spec (.of A)).presheaf.stalk (f.base z))
      (Z.presheaf.stalk z) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f z
  exact (isQuasiExcellent_and_isExcellent_of_essFiniteType.{u, u}).2 hS

/-- The completion of an excellent normal Noetherian local ring is normal: an excellent ring is a
G-ring, so the map to the completion is regular, and normality ascends along a regular map. -/
@[ega "IV 7.8.3" "(v), special case"]
private theorem isNormalRing_adicCompletion_of_isExcellent (A : Type u) [CommRing A]
    [IsLocalRing A] (hA : IsNormalRing A) (hExcellent : IsExcellent A) :
    IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  let : IsNoetherianRing A := hExcellent.1.1
  have hreg : IsRegularRingHom (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) :=
    isRegularRingHom_algebraMap_adicCompletion hExcellent.1.2.1 (IsLocalRing.maximalIdeal A)
  rw [isRegularRingHom_iff_of_eq_algebraMap _ rfl] at hreg
  exact isNormalRing_of_flat_of_isGeometricallyRegular_fiber A
    (AdicCompletion (IsLocalRing.maximalIdeal A) A) hA (fun q _ => (hreg.2 q).2)

/-- The nonzero primes of a discrete valuation ring are its maximal ideal. -/
private theorem eq_maximalIdeal_of_ne_bot {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (q : PrimeSpectrum A) (hq : q.asIdeal ≠ ⊥) :
    q.asIdeal = IsLocalRing.maximalIdeal A := by
  obtain ⟨_, P, _, hP⟩ :=
    (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime A).mp inferInstance
  have h₁ := hP _ ⟨hq, q.isPrime⟩
  have h₂ := hP _ ⟨IsDiscreteValuationRing.not_a_field A,
    (IsLocalRing.maximalIdeal.isMaximal A).isPrime⟩
  exact h₁.trans h₂.symm

/-- The completed local rings of a finite normal cover of a scheme locally of finite type over a
discrete valuation ring are normal, provided the base change of the cover to the completion of the
valuation ring is normal.

This is the content of the third assertion of Tag 0C2T, stated for an abstract finite morphism
`ν : N ⟶ X` so that no normalization data appears in the induction on the two cases. -/
private theorem isNormalRing_adicCompletion_stalk_of_isNormal_baseChange
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X N : Scheme.{u}} (p : X ⟶ Spec (.of R)) [LocallyOfFiniteType p]
    (ν : N ⟶ X) [IsFinite ν] (hN : IsNormal N)
    (hNhat : IsNormal (pullback (ν ≫ p) (Spec.map (CommRingCat.ofHom
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))))))
    (x : N) :
    IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal (N.presheaf.stalk x))
      (N.presheaf.stalk x)) := by
  have hνp : LocallyOfFiniteType (ν ≫ p) := inferInstance
  by_cases hg : ((ν ≫ p).base x).asIdeal = ⊥
  · exact isNormalRing_adicCompletion_of_isExcellent _ (isNormalRing_stalk hN x)
      (isExcellent_stalk_of_locallyOfFiniteType (ν ≫ p) x
        (isExcellent_stalk_spec_of_eq_bot _ hg))
  · -- The point lies in the special fibre: move it to the base change to `R^∧`.
    have hclosed : (ν ≫ p).base x =
        (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) :=
      PrimeSpectrum.ext (eq_maximalIdeal_of_ne_bot _ hg)
    let Rhat : Type u := AdicCompletion (IsLocalRing.maximalIdeal R) R
    let i : Spec (.of Rhat) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R Rhat))
    let : Module.FaithfullyFlat R Rhat :=
      AdicCompletion.faithfullyFlat_of_le_ringJacobson _
        (by rw [← Ideal.jacobson_bot]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥)
    obtain ⟨z, hz⟩ :=
      (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := Rhat))
        ((ν ≫ p).base x)
    obtain ⟨y, hyν, -⟩ :=
      Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback (ν ≫ p) i) x z
        (by
          change (ν ≫ p).base x = PrimeSpectrum.comap (algebraMap R Rhat) z
          exact hz.symm)
    have hNoeth : IsNoetherianRing Rhat := inferInstance
    have hRhat : IsExcellent Rhat := by
      let : IsPrecomplete (IsLocalRing.maximalIdeal Rhat) Rhat := inferInstance
      exact (isExcellent_of_standard_classes_and_finiteType.{u, u}).2.1 Rhat
    have hA'normal : IsNormalRing ((pullback (ν ≫ p) i).presheaf.stalk y) :=
      isNormalRing_stalk hNhat y
    have hA'excellent : IsExcellent ((pullback (ν ≫ p) i).presheaf.stalk y) :=
      isExcellent_stalk_of_locallyOfFiniteType (pullback.snd (ν ≫ p) i) y
        (isExcellent_stalk_spec hRhat _)
    have hcompleted := isNormalRing_adicCompletion_of_isExcellent _ hA'normal hA'excellent
    obtain ⟨c, -⟩ := AlgebraicGeometry.stalkMap_adicCompletion_isomorphism R
      (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing N (ν ≫ p) y
      (by rw [hyν]; exact hclosed)
    rw [← hyν]
    exact IsNormalRing.congr c.symm hcompleted

/-! ### The normalization of a model -/

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Stacks Project, Tag 0C2T (finiteness of the normalization).** The normalization of a model,
over a discrete valuation ring, of a geometrically normal scheme over its fraction field is a
finite morphism. -/
@[stacks 0C2T "finiteness of the normalization"]
theorem isFinite_normalization_of_isModel {V X : Scheme.{u}}
    (v : V ⟶ Spec (CommRingCat.of K)) (hV : IsGeometricallyNormal v)
    (p : X ⟶ Spec (CommRingCat.of R))
    (e : V ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : IsModel v p e)
    (hfinX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsFinite (Scheme.normalization X hfinX) := by
  let : LocallyOfFiniteType p := hX.2.1
  exact isFinite_normalization_of_isNormal_complementSpecialFiber_completion R p
    (isNormal_complementSpecialFiber_baseChange_adicCompletion R K V X v hV p e hX.2.2.2)

/-- **Stacks Project, Tag 0C2T (normalization commutes with completion).** For a model, over a
discrete valuation ring `R`, of a geometrically normal scheme over the fraction field of `R`, the
base change of the normalization to the completion `R^∧` is the normalization of the base change
of the model, compatibly with the two normalization morphisms. -/
@[stacks 0C2T "normalization commutes with completion"]
theorem exists_iso_baseChange_normalization_adicCompletion_of_isModel {V X : Scheme.{u}}
    (v : V ⟶ Spec (CommRingCat.of K)) (hV : IsGeometricallyNormal v)
    (p : X ⟶ Spec (CommRingCat.of R))
    (e : V ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : IsModel v p e)
    (hfinX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    let ν := Scheme.normalization X hfinX
    let Rhat := AdicCompletion (IsLocalRing.maximalIdeal R) R
    let i : Spec (CommRingCat.of Rhat) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R Rhat))
    let Y : Scheme.{u} := pullback p i
    let νhat : pullback (ν ≫ p) i ⟶ Y :=
      pullback.map (ν ≫ p) i p i ν (𝟙 _) (𝟙 _) (by simp) (by simp)
    ∀ hfinY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite,
      ∃ α : pullback (ν ≫ p) i ≅ Scheme.normalizationScheme Y hfinY,
        α.hom ≫ Scheme.normalization Y hfinY = νhat := by
  let : LocallyOfFiniteType p := hX.2.1
  intro ν Rhat i Y νhat hfinY
  obtain ⟨α, hα⟩ :=
    exists_iso_pullback_normalization_completion_of_isNormal_complementSpecialFiber R p
      (isNormal_complementSpecialFiber_baseChange_adicCompletion R K V X v hV p e hX.2.2.2)
  change α.hom ≫ Scheme.normalization Y hfinY = pullback.snd ν (pullback.fst p i) at hα
  refine ⟨(pullbackRightPullbackFstIso p i ν).symm ≪≫ α, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hα]
  exact pullbackRightPullbackFstIso_inv_snd_eq_map p i ν

/-- **Stacks Project, Tag 0C2T (completions of the local rings are normal).** At every point of
the normalization of a model, over a discrete valuation ring, of a geometrically normal scheme
over the fraction field, the completion of the local ring is a normal ring. -/
@[stacks 0C2T "completions of the local rings are normal"]
theorem isNormalRing_adicCompletion_stalk_normalization_of_isModel {V X : Scheme.{u}}
    (v : V ⟶ Spec (CommRingCat.of K)) (hV : IsGeometricallyNormal v)
    (p : X ⟶ Spec (CommRingCat.of R))
    (e : V ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : IsModel v p e)
    (hfinX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : Scheme.normalizationScheme X hfinX) :
    IsNormalRing (AdicCompletion
      (IsLocalRing.maximalIdeal ((Scheme.normalizationScheme X hfinX).presheaf.stalk x))
      ((Scheme.normalizationScheme X hfinX).presheaf.stalk x)) := by
  let : LocallyOfFiniteType p := hX.2.1
  let : IsFinite (Scheme.normalization X hfinX) :=
    isFinite_normalization_of_isModel v hV p e hX hfinX
  refine isNormalRing_adicCompletion_stalk_of_isNormal_baseChange R p
    (Scheme.normalization X hfinX) (Scheme.isNormal_normalizationScheme X hfinX) ?_ x
  -- Normality of the base change of the normalization to the completion, from the second
  -- assertion: it is isomorphic to the normalization of the base change.
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsLocallyNoetherian (pullback p (Spec.map (CommRingCat.ofHom
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))))) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p (Spec.map (CommRingCat.ofHom
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))))
  let hfinY := finite_irreducibleComponents_of_isCompact (pullback p (Spec.map
    (CommRingCat.ofHom (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))))
  obtain ⟨α, -⟩ :=
    exists_iso_baseChange_normalization_adicCompletion_of_isModel v hV p e hX hfinX hfinY
  let : IsNormal (Scheme.normalizationScheme (pullback p (Spec.map (CommRingCat.ofHom
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))))) hfinY) :=
    Scheme.isNormal_normalizationScheme _ hfinY
  exact isNormal_of_iso α

end Stacks.Models

end
