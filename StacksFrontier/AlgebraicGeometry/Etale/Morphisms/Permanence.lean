module

public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.Etale.Height
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Flat.ReducedFibres
public import StacksFrontier.RingTheory.QuasiFinite.Dimension
public import Mathlib.RingTheory.Unramified.LocalRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Permanence properties of étale local homomorphisms

An étale homomorphism of Noetherian local rings leaves the invariants of the local ring
unchanged: it preserves Krull dimension and depth, and it preserves and reflects both
reducedness and Cohen-Macaulayness.

## Main results

* `RingHom.ringKrullDim_eq_of_isEtaleLocalHom`: the source and target of an étale local
  homomorphism have equal Krull dimension.
* `RingHom.depth_eq_of_isEtaleLocalHom`: the source and target of an étale local homomorphism
  have equal depth.
* `RingHom.isReduced_iff_of_isEtaleLocalHom`: the source of an étale local homomorphism is
  reduced if and only if its target is.
* `RingHom.isCohenMacaulayLocalRing_iff_of_isEtaleLocalHom`: the source of an étale local
  homomorphism is Cohen-Macaulay if and only if its target is.

## References

* [Stacks Project, Tag 025L](https://stacks.math.columbia.edu/tag/025L)
* [Stacks Project, Tag 025O](https://stacks.math.columbia.edu/tag/025O)
* [Stacks Project, Tag 025Q](https://stacks.math.columbia.edu/tag/025Q)
* [Stacks Project, Tag 039S](https://stacks.math.columbia.edu/tag/039S)
* [Stacks Project, Tag 039T](https://stacks.math.columbia.edu/tag/039T)
-/

@[expose] public section

universe u v

namespace RingHom

/-- The residue field of a local ring has depth zero over that ring. -/
private lemma depth_quotient_maximalIdeal_eq_zero
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Module.depth A (IsLocalRing.maximalIdeal A)
      (A ⧸ IsLocalRing.maximalIdeal A) = 0 := by
  rw [Module.depth]
  simp only [Ideal.smul_top_eq_map, Ideal.Quotient.algebraMap_eq, Ideal.map_quotient_self,
    Submodule.restrictScalars_bot, bot_ne_top, ↓reduceIte, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, Set.mem_ofPred_eq, ENat.iSup_eq_zero, Nat.cast_eq_zero,
    List.length_eq_zero_iff, and_imp]
  intro xs hmem hreg
  cases xs with
  | nil => rfl
  | cons f t =>
      exfalso
      exact (one_ne_zero : (1 : A ⧸ IsLocalRing.maximalIdeal A) ≠ 0)
        (((RingTheory.Sequence.isRegular_cons_iff
          (A ⧸ IsLocalRing.maximalIdeal A) f t).mp hreg).1 (by
            simp [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem,
              IsLocalRing.mem_maximalIdeal, hmem f (by simp)]))

/-- An étale local homomorphism between Noetherian local rings
preserves depth. -/
@[stacks 039T]
theorem depth_eq_of_isEtaleLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hf : IsEtaleLocalHom f) :
    Module.depth A (IsLocalRing.maximalIdeal A) A =
      Module.depth B (IsLocalRing.maximalIdeal B) B := by
  let : Algebra A B := f.toAlgebra
  have : Module.Flat A B := hf.1
  have : Algebra.FormallyUnramified A B := hf.2.1
  have : Algebra.EssFiniteType A B := hf.2.2
  have h := Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal A B
  rw [((Algebra.FormallyUnramified.iff_map_maximalIdeal_eq
    (R := A) (S := B)).mp inferInstance).2,
    depth_quotient_maximalIdeal_eq_zero, add_zero] at h
  exact h.symm

attribute [stacks 025L "Proposition 039T of the section: for an étale homomorphism `A → B` of
Noetherian local rings, `depth(A) = depth(B)`."]
  RingHom.depth_eq_of_isEtaleLocalHom

/-- An étale local homomorphism between Noetherian local rings
preserves and reflects reducedness. -/
@[stacks 025O, sga "1 I 9.3" "Noetherian case"]
theorem isReduced_iff_of_isEtaleLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hf : IsEtaleLocalHom f) :
    IsReduced A ↔ IsReduced B := by
  let : Algebra A B := f.toAlgebra
  have : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hf.1
  have : Algebra.FormallyUnramified A B := RingHom.formallyUnramified_algebraMap.mp hf.2.1
  have : Algebra.EssFiniteType A B := RingHom.essFiniteType_algebraMap.mp hf.2.2
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · exact isReduced_of_flat_of_isReduced_fiber (R := A) (S := B) fun p _ ↦
      Algebra.FormallyUnramified.isReduced_of_field p.ResidueField (p.Fiber B)
  · exact RingHom.FaithfullyFlat.isReduced
      (RingHom.faithfullyFlat_algebraMap_iff.mpr
        (Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)))

attribute [stacks 025L "Proposition 025O of the section: for an étale homomorphism `A → B` of
Noetherian local rings, `A` is reduced if and only if `B` is reduced."]
  RingHom.isReduced_iff_of_isEtaleLocalHom

/-- The supremum form of depth agrees with `Module.depth` for a local ring over its own
maximal ideal. -/
private lemma depthSup_self_eq_depth {R : Type u} [CommRing R] [IsLocalRing R] :
    Module.depthSup R (IsLocalRing.maximalIdeal R) R =
      Module.depth R (IsLocalRing.maximalIdeal R) R := by
  rw [Module.depth, Module.depthSup_eq_iSup]
  split_ifs with hc
  · exact absurd hc (by simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top)
  · rfl

/-- An étale local homomorphism of Noetherian local rings preserves Krull dimension. -/
private lemma ringKrullDim_eq_aux
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hf : IsEtaleLocalHom f) :
    ringKrullDim A = ringKrullDim B := by
  let : Algebra A B := f.toAlgebra
  have : Module.Flat A B := hf.1
  have : Algebra.FormallyUnramified A B := hf.2.1
  have : Algebra.EssFiniteType A B := hf.2.2
  have : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have hlo : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞))
    (le_antisymm (Ideal.height_le_height_of_liesOver_of_hasGoingDown _ _)
      (Ideal.height_le_height_of_liesOver_of_quasiFiniteAt _ _))

/-- Cohen-Macaulayness is preserved and reflected by an étale
local homomorphism of Noetherian local rings. -/
@[stacks 025Q]
theorem isCohenMacaulayLocalRing_iff_of_isEtaleLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hf : IsEtaleLocalHom f) :
    IsCohenMacaulayLocalRing A ↔ IsCohenMacaulayLocalRing B := by
  show (Module.depthSup A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞) =
      Module.supportDim A A ↔
    (Module.depthSup B (IsLocalRing.maximalIdeal B) B : WithBot ℕ∞) =
      Module.supportDim B B
  rw [Module.supportDim_self_eq_ringKrullDim, Module.supportDim_self_eq_ringKrullDim]
  rw [depthSup_self_eq_depth (R := A), depthSup_self_eq_depth (R := B),
    depth_eq_of_isEtaleLocalHom f hf, ringKrullDim_eq_aux f hf]

attribute [stacks 025L "Proposition 025Q of the section: for an étale homomorphism `A → B` of
Noetherian local rings, `A` is Cohen-Macaulay if and only if `B` is Cohen-Macaulay."]
  RingHom.isCohenMacaulayLocalRing_iff_of_isEtaleLocalHom

/-- An étale homomorphism of Noetherian local rings preserves the
Krull dimension: the dimension of the source equals the dimension of the target. -/
@[stacks 039S, ega "IV 6.1.3" "special case"]
theorem ringKrullDim_eq_of_isEtaleLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hf : IsEtaleLocalHom f) :
    ringKrullDim A = ringKrullDim B :=
  ringKrullDim_eq_aux f hf

attribute [stacks 025L "Lemma 039S of the section: for an étale homomorphism `A → B` of
Noetherian local rings, `dim(A) = dim(B)`."]
  RingHom.ringKrullDim_eq_of_isEtaleLocalHom

end RingHom
