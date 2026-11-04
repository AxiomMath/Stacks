module

public import Mathlib.RingTheory.LocalProperties.Reduced
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Flat.NormalFibres
public import StacksFrontier.RingTheory.Flat.ReducedFibres
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.Regular.RegularRingHom
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.Serre.FlatAscent

open Stacks.Smooth.RegularRingAscent

@[expose] public section

/-!
# Ascending properties along regular ring maps

Let `f : R →+* S` be a regular homomorphism of Noetherian rings: `S` is flat over `R` and every
fibre `p.Fiber S = κ(p) ⊗[R] S` is Noetherian and geometrically regular over `κ(p)`. Then `S` is
reduced, normal, regular or Cohen–Macaulay when `R` is.

## Main results

* `isReduced_of_isRegularRingHom`: the target of a regular ring homomorphism of Noetherian rings
  is reduced when the source is reduced.
* `isNormalRing_of_flat_of_isGeometricallyRegular_fiber`: if `R → S` is flat with geometrically
  regular fibres, `R` and `S` are Noetherian and `R` is normal, then `S` is normal.
* `isRegularRing_of_isRegularRingHom`: the Noetherian target of a regular ring homomorphism from
  a regular ring is regular.
* `isCohenMacaulayRing_of_isRegularRingHom`: the Noetherian target of a regular ring homomorphism
  from a Noetherian Cohen–Macaulay ring is Cohen–Macaulay.
* `depth_eq_ringKrullDim_of_isRegularLocalRing`: a regular local ring has self-depth equal to its
  Krull dimension.

## References

* [Stacks Project, Tag 07QK](https://stacks.math.columbia.edu/tag/07QK)
* [Stacks Project, Tag 0BFK](https://stacks.math.columbia.edu/tag/0BFK)
* [Stacks Project, Tag 0H7S](https://stacks.math.columbia.edu/tag/0H7S)
* [Stacks Project, Tag 0H7T](https://stacks.math.columbia.edu/tag/0H7T)
-/

/-! ### Reducedness -/

section

section

set_option maxRecDepth 4096

@[expose] public section

open scoped TensorProduct

universe u v w

/-- A geometrically regular algebra over a field is a regular ring. -/
private theorem isRegularRing_of_isGeometricallyRegular (K A : Type*) [Field K] [CommRing A]
    [Algebra K A] [Algebra.IsGeometricallyRegular K A] : IsRegularRing A :=
  IsRegularRing.of_ringEquiv (Algebra.TensorProduct.lid K A).toRingEquiv

private theorem isReduced_of_isGeometricallyRegular (k A : Type*) [Field k] [CommRing A]
    [Algebra k A] [Algebra.IsGeometricallyRegular k A] : IsReduced A := by
  have := isRegularRing_of_isGeometricallyRegular k A
  exact isReduced_ofLocalizationMaximal A fun J hJ ↦ by
    let : J.IsPrime := hJ.isPrime
    have : IsRegularLocalRing (Localization.AtPrime J) := inferInstance
    have : IsDomain (Localization.AtPrime J) := IsRegularLocalRing.isDomain _
    infer_instance

/-- If `f : R →+* S` is regular, `R` and `S` are Noetherian, and `R` is
reduced, then `S` is reduced. -/
@[stacks 07QK]
public theorem isReduced_of_isRegularRingHom {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : IsRegularRingHom f) [IsNoetherianRing R]
    [IsReduced R] : IsReduced S := by
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hf.1
  have : Finite {q : Ideal R // q ∈ minimalPrimes R} :=
    (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
  refine Stacks.Flatness.ReducedFibreAscent.isReduced_of_flat_of_forall_isReduced_fiber (S := S)
    (ι := {q : Ideal R // q ∈ minimalPrimes R}) Subtype.val
    (hp := fun i ↦ Ideal.IsMinimalPrime.isPrime i.2)
    (fun r hr ↦ Stacks.Flatness.ReducedFibreAscent.eq_zero_of_forall_mem_minimalPrimes
      fun q hq ↦ hr ⟨q, hq⟩) ?_
  intro i
  have : i.1.IsPrime := Ideal.IsMinimalPrime.isPrime i.2
  have : Algebra.IsGeometricallyRegular i.1.ResidueField (i.1.Fiber S) := (hf.2 i.1).2
  exact isReduced_of_isGeometricallyRegular i.1.ResidueField (i.1.Fiber S)

end

end

end

/-! ### Normality -/

section

section

@[expose] public section

universe u v

/-- Let `R → S` be a regular map of Noetherian rings. If `R` is normal, then `S` is normal. -/
@[stacks 0BFK, ega "IV 6.5.4" "(ii), regular fibres"]
public theorem isNormalRing_of_flat_of_isGeometricallyRegular_fiber
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (hR : IsNormalRing R)
    (hfiber : ∀ (p : Ideal R) [p.IsPrime],
      Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber S)) :
    IsNormalRing S := by
  apply isNormalRing_of_flat_of_isNormalRing_fiber hR
  intro p _
  have := hfiber p
  have := isRegularRing_of_isGeometricallyRegular p.ResidueField (p.Fiber S)
  exact main_theorem0567 _

end

end

end

/-! ### Regularity -/

section

section

universe u v

/-- The Noetherian target of a regular ring homomorphism from a regular ring is regular. -/
@[stacks 0H7S]
public theorem isRegularRing_of_isRegularRingHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : IsRegularRingHom f)
    [IsNoetherianRing S] [IsRegularRing R] : IsRegularRing S := by
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hf.1
  refine isRegularRing_of_forall_hasPropertyRk S fun k ↦
    property_Rk_of_flat_of_fibre_of_base R S k (fun p _ ↦ ?_) (hasPropertyRk_of_isRegularRing R k)
  have : IsNoetherianRing (p.Fiber S) := (hf.2 p).1
  have := (hf.2 p).2
  have : IsRegularRing (p.Fiber S) :=
    isRegularRing_of_isGeometricallyRegular p.ResidueField (p.Fiber S)
  have hFibreRing : IsRegularRing (fibreRing R S p) :=
    IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm R p.ResidueField S).toRingEquiv
  exact @hasPropertyRk_of_isRegularRing (fibreRing R S p) _ hFibreRing k

end

end

/-! ### Cohen–Macaulayness -/

section

section

@[expose] public section

open IsLocalRing

universe u v

/-- The sequence definition of local-ring depth agrees with `Module.depth` at the maximal
ideal. -/
private lemma localRingDepth_eq_moduleDepth (A : Type*) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] :
    (localRingDepth A : WithBot ℕ∞) =
      (Module.depth A (maximalIdeal A) A : WithBot ℕ∞) := by
  have hne : maximalIdeal A • (⊤ : Submodule A A) ≠ ⊤ := by
    simpa using (maximalIdeal.isMaximal A).ne_top
  have h : localRingDepth A = Module.depth A (maximalIdeal A) A := by
    rw [localRingDepth, Module.depth, ite_eq_right hne]
    exact le_antisymm
      (iSup_le fun s ↦ le_iSup₂_of_le s.val s.property le_rfl)
      (iSup_le fun rs ↦ iSup_le fun hrs ↦ le_iSup_of_le ⟨rs, hrs⟩ le_rfl)
  exact_mod_cast h

/-- A regular local ring has self-depth equal to its Krull dimension. -/
@[sga "2 IV 5.3"]
lemma depth_eq_ringKrullDim_of_isRegularLocalRing (A : Type*) [CommRing A]
    [IsRegularLocalRing A] :
    (Module.depth A (maximalIdeal A) A : WithBot ℕ∞) = ringKrullDim A := by
  have : IsNoetherianRing A := IsRegularLocalRing.toIsNoetherian
  have h :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay A).2
  rw [Module.IsMaximalCohenMacaulay] at h
  exact_mod_cast h

/-- Self-depth of a local ring is at most its Krull dimension. -/
private lemma depth_le_ringKrullDim (A : Type*) [CommRing A] [IsLocalRing A] :
    (Module.depth A (maximalIdeal A) A : WithBot ℕ∞) ≤ ringKrullDim A := by
  rw [← Module.supportDim_self_eq_ringKrullDim]
  refine Module.depth_le_supportDim A _ A ?_
  simpa using (maximalIdeal.isMaximal A).ne_top

/-- If `f : R →+* S` is regular, `S` is Noetherian, and `R` is Noetherian and
Cohen–Macaulay, then `S` is Cohen–Macaulay. -/
@[stacks 0H7T]
public theorem isCohenMacaulayRing_of_isRegularRingHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] (f : R →+* S)
    (hf : IsRegularRingHom f) (hR : IsCohenMacaulayRing R) :
    IsCohenMacaulayRing S := by
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hf.1
  have hSk : ∀ k : ℕ, ∀ (q : Ideal S) [q.IsPrime],
      min (k : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime q)) ≤
        (Module.depth (Localization.AtPrime q)
          (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) : WithBot ℕ∞) := by
    intro k
    apply min_le_depth_atPrime_of_flat (R := R)
    · intro p _ Q _
      have := (hf.2 p).2
      have : IsRegularRing (p.Fiber S) :=
        isRegularRing_of_isGeometricallyRegular p.ResidueField (p.Fiber S)
      have : IsRegularLocalRing (Localization.AtPrime Q) :=
        IsRegularRing.isRegularLocalRing_localization Q
      rw [depth_eq_ringKrullDim_of_isRegularLocalRing]
      exact min_le_right _ _
    · intro p _
      rw [← localRingDepth_eq_moduleDepth]
      exact (min_le_right _ _).trans_eq (hR p).symm
  intro q _
  rw [IsCohenMacaulayLocalRingPropForm, localRingDepth_eq_moduleDepth]
  apply le_antisymm
  · exact depth_le_ringKrullDim (Localization.AtPrime q)
  · have h := hSk q.height.toNat q
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)] at h
    have heq : (q.height.toNat : WithBot ℕ∞) = (q.height : WithBot ℕ∞) := by
      exact_mod_cast ENat.natCast_toNat Ideal.height_ne_top_of_isPrime
    rw [heq, min_self] at h
    simpa [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)] using h

end

end

end

end
