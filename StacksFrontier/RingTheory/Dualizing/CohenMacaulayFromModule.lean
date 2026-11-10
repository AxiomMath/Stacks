module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayCriterion
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
public import StacksFrontier.RingTheory.Dualizing.DimensionFunction
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift

/-!
# Cohen--Macaulayness from a dualizing module

A Noetherian ring `A` carrying a finite module `ω_A` whose degree-zero complex `ω_A[0]` is a
dualizing complex is Cohen--Macaulay. The condition is local: a dualizing complex localizes
(`Dualizing.isDualizingComplex_localizationAtPrime`), and derived extension of scalars along the
flat map `A → A_𝔭` keeps the cohomology concentrated in degree zero, so each `A_𝔭` has a
dualizing complex with cohomology in a single degree. Exactly one shift of that complex is
normalized, and the shift moves the single degree but does not create a second one; the
criterion of [Stacks, Tag 0B5A] applied to the ring itself then reads off
`depth(A_𝔭) = dim(A_𝔭)`, because derived Hom out of the ring in degree zero is the identity, so
`Ext^i_{A_𝔭}(A_𝔭, ω)` is `H^i(ω)` and vanishes outside that one degree.

## Main results

* `Dualizing.isCohenMacaulayLocalRingPropForm_iff_isCohenMacaulayAtMaximalIdeal` reconciles the
  two spellings of Cohen--Macaulayness of a Noetherian local ring used below.
* `Dualizing.extULiftRingLinearEquiv` identifies `Ext^i` out of the ring in degree zero with
  degree-`i` cohomology.
* `Dualizing.isCohenMacaulayAtMaximalIdeal_self_of_homology_concentrated`: a Noetherian local
  ring whose dualizing complex has cohomology in at most one degree is Cohen--Macaulay.
* `Dualizing.isCohenMacaulayRing_of_dualizingModule` is Tag 0DW5.

## Implementation notes

Cohen--Macaulayness of a Noetherian local ring is `IsCohenMacaulayLocalRingPropForm`, which is
what `IsCohenMacaulayRing` (Definition 00NC) quantifies over primes, whereas the dualizing-complex
criterion of [Stacks, Tag 0B5A] concludes `Module.IsCohenMacaulayAtMaximalIdeal`. The first is
`localRingDepth`-and-`ringKrullDim`, the second `Module.depth`-and-`Module.supportDim`; the two
agree for the ring over itself, and the bridge is proved here because the existing copies of it
are `private` to their files.

The criterion's module lives in `Type (max v u)` over a ring in `Type u`, so it is applied to
`ULift.{v} A` rather than to `A`, and the conclusion is carried back along `ULift.moduleEquiv`.
That universe lift is also what the derived-Hom computation wants:
`Dualizing.derivedHomULiftRingIso` identifies derived Hom out of `(ULift.{v} A)[0]` with the
identity, that module being the monoidal unit of `ModuleCat.{max u v} A`.

Finiteness of `ω_A` is the source's hypothesis and is recorded as such, although it also follows
from the dualizing condition, whose second clause is finiteness of every cohomology module.

## References

* [Stacks Project, Tag 0DW5](https://stacks.math.columbia.edu/tag/0DW5)
* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
* [Stacks Project, Tag 0B5A](https://stacks.math.columbia.edu/tag/0B5A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-! ### The two spellings of Cohen--Macaulayness of a local ring -/

/-- On a local ring the depth of the ring along its maximal ideal is the supremum of the lengths
of the regular sequences contained in that ideal: the exceptional branch of `Module.depth` is
never taken, because a maximal ideal `𝔪` has `𝔪 • R ≠ R`. -/
theorem localRingDepth_eq_depth_self (R : Type*) [CommRing R] [IsLocalRing R] :
    localRingDepth R = Module.depth R (IsLocalRing.maximalIdeal R) R := by
  rw [Module.depth,
    ite_eq_right (by simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top),
    ← Module.depthSup_eq_iSup]
  unfold localRingDepth Module.depthSup
  refine le_antisymm (iSup_le fun s => le_sSup ⟨s.val, rfl, s.property⟩) (sSup_le ?_)
  rintro n ⟨rs, rfl, hmem, hreg⟩
  exact le_iSup_of_le ⟨rs, hmem, hreg⟩ le_rfl

/-- Cohen--Macaulayness of a Noetherian local ring, in the `localRingDepth`-equals-`ringKrullDim`
form that Definition 00NC quantifies over primes, agrees with Cohen--Macaulayness of the ring as a
module over itself. -/
theorem isCohenMacaulayLocalRingPropForm_iff_isCohenMacaulayAtMaximalIdeal
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    IsCohenMacaulayLocalRingPropForm R ↔ Module.IsCohenMacaulayAtMaximalIdeal R R := by
  change (localRingDepth R : WithBot ℕ∞) = ringKrullDim R ↔
    (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) = Module.supportDim R R
  rw [Module.supportDim_self_eq_ringKrullDim, localRingDepth_eq_depth_self]

/-! ### `Ext` out of the ring is cohomology -/

/-- **`Ext^i` out of the ring in degree zero is degree-`i` cohomology.** The universe-lifted ring
is the monoidal unit of `ModuleCat.{max u v} A`, so derived Hom out of it in degree zero is the
identity; combined with the `Ext`--cohomology comparison this reads `Ext^i_A(A, ω) = H^i(ω)`. No
hypothesis on `ω` is needed. -/
def extULiftRingLinearEquiv (A : Type u) [CommRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A (ULift.{v} A))) omega i ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj omega) :=
  let unit := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
    (ModuleCat.of A (ULift.{v} A))
  let e : (dualizingDerivedHomFunctor.{u, v} A omega).obj (.op unit) ≅ omega :=
    derivedHomULiftRingIso.{u, v} A omega
  (extDerivedHomLinearEquiv.{u, v} A omega i unit).trans
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso e).toLinearEquiv

/-! ### The local statement -/

/-- **A dualizing complex with cohomology in one degree forces Cohen--Macaulayness.** This is the
implication (2) ⇒ (1) of [Stacks, Tag 0AWS], stated for an arbitrary — not necessarily
normalized — dualizing complex, since being concentrated in a single degree is invariant under
the normalizing shift. -/
theorem isCohenMacaulayAtMaximalIdeal_self_of_homology_concentrated
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max u v} A)) (hK : IsDualizingComplex K) (d : ℤ)
    (hconc : ∀ i : ℤ, i ≠ d →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) :
    Module.IsCohenMacaulayAtMaximalIdeal A A := by
  obtain ⟨m, hm⟩ := exists_isNormalizedDualizingComplex_shift.{u, v} K hK
  have hshift : ∀ i : ℤ, i ≠ d + m →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj (K⟦-m⟧)) := by
    intro i hi
    exact (hconc (-m + i) (by omega)).of_iso
      (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).shiftIso
        (-m) i (-m + i) rfl).app K)
  have hunique : ∀ k : ℤ, Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        (ModuleCat.of A (ULift.{v} A))) (K⟦-m⟧) k) → k = d + m := by
    intro k hk
    by_contra hne
    have hsub : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) k).obj
        (K⟦-m⟧)) := ModuleCat.isZero_iff_subsingleton.mp (hshift k hne)
    exact not_subsingleton _ (extULiftRingLinearEquiv.{u, v} A (K⟦-m⟧) k).toEquiv.subsingleton
  have hlift : Module.IsCohenMacaulayAtMaximalIdeal A (ULift.{v} A) :=
    ((isCohenMacaulay_iff_ext_concentrated.{u, v} (M := ULift.{v} A) (K⟦-m⟧) hm).out 2 1).mp
      fun i j hi hj => by rw [hunique i hi, hunique j hj]
  change (Module.depth A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞) = Module.supportDim A A
  rw [← Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal A)
      (ULift.moduleEquiv (R := A) (M := A)),
    ← Module.supportDim_eq_of_equiv (ULift.moduleEquiv (R := A) (M := A))]
  exact hlift

/-! ### Localizing a module in degree zero -/

/-- Derived extension of scalars along a localization carries a module placed in degree zero to
an object whose cohomology is concentrated in degree zero. A localization is flat, so the
extension commutes with cohomology, and the universe lift in front of it is exact. -/
theorem isZero_homology_derivedExtensionScalars_single
    {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (S : Submonoid A) [IsLocalization S B]
    (M : ModuleCat.{max u v} A) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i).obj
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A B)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M))) := by
  have hf : (algebraMap A B).Flat := RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B S)
  let U := ModuleCat.uliftFunctor.{u, max u v, u} A
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M
  have hX : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj X) := by
    rcases lt_or_gt_of_ne hi with h | h
    · exact DerivedCategory.isZero_of_isGE X 0 i h
    · exact DerivedCategory.isZero_of_isLE X 0 i h
  have hKU : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
      (U.mapDerivedCategory.obj X)) :=
    (Functor.map_isZero U hX).of_iso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso U i).app X)
  exact (Functor.map_isZero
    (ModuleCat.extendScalars.{u, u, max u v} (algebraMap A B)) hKU).of_iso
    ((CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, u, max u v}
      (algebraMap A B) hf i).app (U.mapDerivedCategory.obj X))

/-! ### The global statement -/

/-- **Stacks Project, Tag 0DW5.** A Noetherian ring admitting a finite module whose degree-zero
complex is a dualizing complex is Cohen--Macaulay. -/
@[stacks 0DW5]
theorem isCohenMacaulayRing_of_dualizingModule {A : Type u} [CommRing A] [IsNoetherianRing A]
    (omega : ModuleCat.{max u v} A) [Module.Finite A omega]
    (homega : IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj omega)) :
    IsCohenMacaulayRing A := by
  intro p hp
  have hK : IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
          (algebraMap A (Localization.AtPrime p))).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj omega)) :=
    isDualizingComplex_localizationAtPrime.{u, v} _ homega ⟨p, hp⟩
  exact (isCohenMacaulayLocalRingPropForm_iff_isCohenMacaulayAtMaximalIdeal
    (Localization.AtPrime p)).mpr
    (isCohenMacaulayAtMaximalIdeal_self_of_homology_concentrated.{u, v} _ hK 0 fun i hi =>
      isZero_homology_derivedExtensionScalars_single.{u, v}
        (Localization.AtPrime p) p.primeCompl omega i hi)

end Dualizing

end
