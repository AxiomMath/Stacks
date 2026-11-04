module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Criterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.RingTheory.CompleteIntersection.Local
public import StacksFrontier.RingTheory.Serre.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.Serre.FlatAscent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Serre's condition `(Sₖ)` is local in the syntomic topology

For every natural number `k`, being locally Noetherian and satisfying Serre's condition
`(Sₖ)` is local for syntomic coverings of schemes.

## Main results

* `AlgebraicGeometry.minDepth_iff_of_stalkMap` transports the `(Sₖ)` inequality at a point
  along a morphism which is an isomorphism on the stalk there.
* `AlgebraicGeometry.isLocallyNoetherian_and_hasPropertySk_isLocal_syntomic` gives syntomic
  locality of the combined property.

## Implementation notes

The witness of local Noetherianity is bundled into the property as an existential, since
`AlgebraicGeometry.HasPropertySk` takes it as an instance argument. On an affine scheme the
condition is the inequality at every prime of the ring of global sections; ascent is then the
flat ascent criterion applied to the complete-intersection fibres of a syntomic ring map, and
descent is the faithfully flat descent of `(Sₖ)`.

## References

* [Stacks Project, Tag 036A](https://stacks.math.columbia.edu/tag/036A)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Serre's condition `(Sₖ)` at every prime of a commutative ring. -/
@[ega "IV 7.5.3"]
private def MinDepthAtPrimes (R : Type*) [CommRing R] (k : ℕ) : Prop :=
  ∀ (q : Ideal R) [q.IsPrime],
    min (k : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime q)) ≤
      (Module.depth (Localization.AtPrime q)
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) :
          WithBot ℕ∞)

/-- The `(Sₖ)` inequality for a local ring is invariant under ring isomorphism. -/
lemma minDepth_iff_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (k : ℕ) (e : A ≃+* B) :
    (min (k : WithBot ℕ∞) (ringKrullDim A) ≤
        (Module.depth A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞)) ↔
      min (k : WithBot ℕ∞) (ringKrullDim B) ≤
        (Module.depth B (IsLocalRing.maximalIdeal B) B : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv e, Module.depth_self_eq_of_ringEquiv e]

/-- Serre's condition `(Sₖ)` at a point is read through any morphism inducing an isomorphism
on the stalk there. -/
theorem minDepth_iff_of_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] (k : ℕ) :
    (min (k : WithBot ℕ∞) (ringKrullDim (X.presheaf.stalk x)) ≤
        (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) : WithBot ℕ∞)) ↔
      min (k : WithBot ℕ∞) (ringKrullDim (Y.presheaf.stalk (f x))) ≤
        (Module.depth (Y.presheaf.stalk (f x))
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))
            (Y.presheaf.stalk (f x)) : WithBot ℕ∞) :=
  minDepth_iff_of_ringEquiv k (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm

/-- On an affine scheme, condition `(Sₖ)` is the inequality at every prime of the ring of
global sections. -/
private lemma hasPropertySk_iff_minDepthAtPrimes (X : Scheme.{u}) [IsAffine X]
    [IsLocallyNoetherian X] (k : ℕ) :
    HasPropertySk X k ↔ MinDepthAtPrimes Γ(X, ⊤) k := by
  have hU : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  rw [hasPropertySk_iff]
  constructor
  · intro h q hq
    let x : X := hU.fromSpec ⟨q, hq⟩
    let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
      X.presheaf.algebra_section_stalk ⟨x, by simp⟩
    let : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
      hU.isLocalization_stalk' ⟨q, hq⟩ (by simp)
    exact (minDepth_iff_of_ringEquiv k
      (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
        (X.presheaf.stalk x)).toRingEquiv.symm).mp (h x)
  · intro h x
    let xU : (⊤ : X.Opens) := ⟨x, trivial⟩
    let q : Ideal Γ(X, ⊤) := (hU.primeIdealOf xU).asIdeal
    let : q.IsPrime := (hU.primeIdealOf xU).2
    let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
      X.presheaf.algebra_section_stalk ⟨x, by simp⟩
    let : IsLocalization.AtPrime (X.presheaf.stalk x) q := hU.isLocalization_stalk xU
    exact (minDepth_iff_of_ringEquiv k
      (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
        (X.presheaf.stalk x)).toRingEquiv).mp (h q)

/-- Condition `(Sₖ)` passes from the target to the source of a morphism that is an isomorphism
on all stalks. -/
private lemma hasPropertySk_of_isIso_stalkMap {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [∀ x, IsIso (f.stalkMap x)] (k : ℕ)
    (h : HasPropertySk Y k) : HasPropertySk X k :=
  hasPropertySk_iff X k |>.2 fun x =>
    (minDepth_iff_of_stalkMap f x k).mpr (hasPropertySk_iff Y k |>.1 h (f x))

private instance hasPropertySk_isClosedUnderIsomorphisms (k : ℕ) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun X : Scheme.{u} => ∃ h : IsLocallyNoetherian X, @HasPropertySk X h k) where
  of_iso {X Y} e hX := by
    have : IsLocallyNoetherian X := hX.1
    have hY : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion e.inv
    exact ⟨hY, hasPropertySk_of_isIso_stalkMap e.inv k hX.2⟩

private instance hasPropertySk_isLocal_zariski (k : ℕ) :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} => ∃ h : IsLocallyNoetherian X, @HasPropertySk X h k)
      Scheme.zariskiPrecoverage := by
  refine isLocal_zariskiPrecoverage_of_openCover _ ?_ ?_
  · intro X U hX
    have : IsLocallyNoetherian X := hX.1
    have hU : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
    exact ⟨hU, hasPropertySk_of_isIso_stalkMap U.ι k hX.2⟩
  · intro X U hU h
    have hN : IsLocallyNoetherian X :=
      (isLocallyNoetherian_iff_openCover (X.openCoverOfIsOpenCover U hU)).2 fun x => (h x).1
    refine ⟨hN, hasPropertySk_iff X k |>.2 fun x => ?_⟩
    obtain ⟨i, hxi⟩ := hU.exists_mem x
    let y : (U i).toScheme := ⟨x, hxi⟩
    have : IsLocallyNoetherian (U i).toScheme := (h i).1
    exact (minDepth_iff_of_stalkMap (U i).ι y k).mp (hasPropertySk_iff _ k |>.1 (h i).2 y)

/-- Every localization of a local complete intersection over a field is maximal
Cohen–Macaulay, hence satisfies the `(Sₖ)` inequality. -/
private lemma minDepth_of_isLocalCompleteIntersection {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] (hA : _root_.IsLocalCompleteIntersection K A) (Q : Ideal A) [Q.IsPrime]
    (k : ℕ) :
    min (k : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime Q)) ≤
      (Module.depth (Localization.AtPrime Q)
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q) :
          WithBot ℕ∞) := by
  convert min_le_right (k : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime Q)) using 1
  exact hA.isMaximalCohenMacaulay_localization Q

/-- **Stacks Project, Tag 036A.** Being locally Noetherian and satisfying `(Sₖ)` is local
for syntomic coverings. -/
@[stacks 036A]
instance isLocallyNoetherian_and_hasPropertySk_isLocal_syntomic (k : ℕ) :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} => ∃ h : IsLocallyNoetherian X, @HasPropertySk X h k)
      (Scheme.precoverage @Syntomic) := by
  refine isLocal_syntomicPrecoverage_of_affine
    (fun X : Scheme.{u} => ∃ h : IsLocallyNoetherian X, @HasPropertySk X h k) ?_ ?_
  · intro X S hX hS f hf hSprop
    let : IsAffine X := hX
    let : IsAffine S := hS
    let : IsLocallyNoetherian S := hSprop.1
    let : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf
    let : LocallyOfFiniteType f :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mp inferInstance
    have hNoethX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    have : IsNoetherianRing Γ(X, ⊤) := hNoethX.component_noetherian ⟨⊤, isAffineOpen_top X⟩
    have : IsNoetherianRing Γ(S, ⊤) := hSprop.1.component_noetherian ⟨⊤, isAffineOpen_top S⟩
    have hUV : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens) := by simp
    let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ hUV).hom.toAlgebra
    have hAlg : Algebra.Syntomic Γ(S, ⊤) Γ(X, ⊤) := by
      have hiff : Syntomic f ↔ ∀ (U : X.Opens) (_ : IsAffineOpen U) (V : S.Opens)
          (_ : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V),
            letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
            Algebra.Syntomic Γ(S, V) Γ(X, U) := (syntomic_tfae f).out 1 2
      exact hiff.mp hf ⊤ (isAffineOpen_top X) ⊤ (isAffineOpen_top S) hUV
    refine ⟨hNoethX, hasPropertySk_iff_minDepthAtPrimes X k |>.2 ?_⟩
    refine min_le_depth_atPrime_of_flat (fun p hp Q hQ => ?_)
      (hasPropertySk_iff_minDepthAtPrimes S k |>.1 hSprop.2)
    exact minDepth_of_isLocalCompleteIntersection
      (Algebra.Syntomic.isLocalCompleteIntersection_fiber (R := Γ(S, ⊤)) (S := Γ(X, ⊤)) p) Q k
  · intro X S hX hS f hf hsurj hXprop
    let : IsAffine X := hX
    let : IsAffine S := hS
    let : IsLocallyNoetherian X := hXprop.1
    have hff : (f.appTop).hom.FaithfullyFlat :=
      (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨flat hf, hsurj⟩
    let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appTop).hom.toAlgebra
    have : IsNoetherianRing Γ(X, ⊤) := hXprop.1.component_noetherian ⟨⊤, isAffineOpen_top X⟩
    have : Module.FaithfullyFlat Γ(S, ⊤) Γ(X, ⊤) := by
      rw [← RingHom.faithfullyFlat_algebraMap_iff]
      simpa [RingHom.algebraMap_toAlgebra] using hff
    obtain ⟨hNoethR, hRsk⟩ :=
      isNoetherianRing_and_min_le_depth_atPrime_of_faithfullyFlat
        (R := Γ(S, ⊤)) (S := Γ(X, ⊤)) (k := k)
        (hasPropertySk_iff_minDepthAtPrimes X k |>.1 hXprop.2)
    have hNoethS : IsLocallyNoetherian S :=
      (isLocallyNoetherian_iff_of_iSup_eq_top
        (S := fun _ : Unit => ⟨⊤, isAffineOpen_top S⟩) (by simp)).2 fun _ => by
          simpa using hNoethR
    exact ⟨hNoethS, hasPropertySk_iff_minDepthAtPrimes S k |>.2 hRsk⟩

end AlgebraicGeometry
