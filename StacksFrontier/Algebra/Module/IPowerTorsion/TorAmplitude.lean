module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.Homology.DerivedComplete.TorsionAmplitude
public import StacksFrontier.Homology.Tor.DerivedTensor

@[expose] public noncomputable section

/-!
# Vanishing of derived tensor products with power-torsion objects

Let `I` be an ideal of a commutative ring `R`. If the derived tensor product of an object `K`
of `D(R)` with `R / I` vanishes, then it also vanishes after tensoring with every quotient
`R / I ^ n` for `n > 0`, every `I`-power-torsion module, and every bounded derived object whose
cohomology is `I`-power torsion.

## Main results

* `IPowerTorsionDerivedTensor.derivedTensorProduct_isZero_of_mod_ideal`: the three vanishing
  conclusions, Stacks 0G1T.

## Implementation notes

Modules are regarded as derived objects concentrated in degree zero. The bounded derived
category is `DerivedCategory.Bounded`, and ideal-power torsion is the elementwise predicate
`IsIPowerTorsion`. The positive-degree half of each conclusion is Stacks 0H82; applying it to
all shifts of `K` upgrades the vanishing of positive cohomology to the vanishing of the object.

## References

* [The Stacks Project, Tag 0G1T](https://stacks.math.columbia.edu/tag/0G1T)
-/

open CategoryTheory CategoryTheory.Limits StacksDraft.PowerTorsionVanishing

attribute [local instance] HasDerivedCategory.standard

namespace IPowerTorsionDerivedTensor

universe u

/-- If a shift-compatible endofunctor of `D(R)` kills the positive cohomology of every shift of
`K`, then it kills `K` itself. -/
private lemma isZero_of_positive_homology_of_shifts
    {R : Type u} [CommRing R]
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    [F.CommShift ℤ]
    (K : DerivedCategory (ModuleCat.{u} R))
    (h : ∀ (a j : ℤ), 0 < j →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj (F.obj (K⟦a⟧)))) :
    IsZero (F.obj K) := by
  let X := F.obj K
  have hhom (i : ℤ) : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj X) :=
    (h (i - 1) 1 one_pos).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 1).mapIso
          ((Functor.commShiftIso F (i - 1)).app K) ≪≫
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).shiftIso (i - 1) 1 i
          (by omega)).app X).symm
  have : X.IsLE (-1) := (DerivedCategory.isLE_iff X (-1)).2 fun i _ ↦ hhom i
  have : X.IsGE 0 := (DerivedCategory.isGE_iff X 0).2 fun i _ ↦ hhom i
  exact DerivedCategory.TStructure.t.isZero X (-1) 0

/-- Ideal-power torsion transports along an isomorphism of modules. -/
private lemma isIPowerTorsion_of_iso {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (I : Ideal R) (e : M ≅ N) (hN : IsIPowerTorsion R N I) :
    IsIPowerTorsion R M I := by
  intro x
  obtain ⟨n, hn, hnx⟩ := hN (e.hom x)
  refine ⟨n, hn, fun a ha ↦ ?_⟩
  have h := congrArg (fun y : N ↦ e.inv y) (hnx a ha)
  have hid : e.inv (e.hom x) = x := by
    calc
      e.inv (e.hom x) = (e.hom ≫ e.inv) x := (ModuleCat.comp_apply e.hom e.inv x).symm
      _ = x := by rw [e.hom_inv_id, ModuleCat.id_apply]
  simpa only [map_smul, map_zero, hid] using h

/-- If `K ⊗ᴸ[R] R / I` vanishes, then so does the homology of `K⟦a⟧ ⊗ᴸ[R] R / I` in every
positive degree, for every shift `a`. -/
private lemma derivedTensorProduct_shift_isZero_of_mod_ideal
    {R : Type u} [CommRing R] (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : IsZero
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R (R ⧸ I))))) (a : ℤ) :
    ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj (K⟦a⟧)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R (R ⧸ I))))) :=
  fun i _ ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map_isZero
    (((shiftFunctor (DerivedCategory (ModuleCat.{u} R)) a).map_isZero hK).of_iso
      ((Functor.commShiftIso
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R (R ⧸ I)))) a).app K))

/-- If `K ⊗ᴸ[R] R / I` vanishes, then so does the derived tensor product of `K` with every
bounded derived object with `I`-power-torsion cohomology. -/
private lemma derivedTensorProduct_bounded_isZero_of_mod_ideal
    {R : Type u} [CommRing R] (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : IsZero
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R (R ⧸ I)))))
    (M : DerivedCategory.Bounded (ModuleCat.{u} R))
    (hM : ∀ i : ℤ, IsIPowerTorsion R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M.obj) I) :
    IsZero
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
        M.obj) := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R
  obtain ⟨n, hn⟩ := M.property.2
  let Ms : DerivedCategory.Bounded (ModuleCat.{u} R) :=
    ⟨M.obj⟦n⟧, DerivedCategory.TStructure.t.bounded.le_shift n M.obj M.property⟩
  have : Ms.obj.IsLE 0 := DerivedCategory.TStructure.t.isLE_shift M.obj n n 0 (by omega)
  have hMs : ∀ i : ℤ, IsIPowerTorsion R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj Ms.obj) I := fun i ↦
    isIPowerTorsion_of_iso I
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).shiftIso n i (n + i) rfl).app M.obj)
      (hM (n + i))
  have hTMs : IsZero (T.obj K |>.obj Ms.obj) :=
    isZero_of_positive_homology_of_shifts (T.flip.obj Ms.obj) K fun a j hj ↦
      (positive_homology_derivedTensorProduct_isZero_of_mod_ideal I (K⟦a⟧)
        (derivedTensorProduct_shift_isZero_of_mod_ideal I K hK a)).2.2 Ms hMs
        (fun i hi ↦ DerivedCategory.isZero_of_isLE Ms.obj 0 i hi) j hj
  exact ((shiftEquiv (DerivedCategory (ModuleCat.{u} R)) n).inverse.map_isZero hTMs).of_iso
    ((shiftEquiv (DerivedCategory (ModuleCat.{u} R)) n).unitIso.app _ ≪≫
      ((shiftEquiv (DerivedCategory (ModuleCat.{u} R)) n).inverse.mapIso
        ((Functor.commShiftIso (T.obj K) n).app M.obj)).symm)

/-- **Stacks 0G1T.** If `K ⊗ᴸ[R] R / I` vanishes, then so does the derived tensor product of `K`
with every positive-power quotient of `R`, every `I`-power-torsion module, and every bounded
derived object with `I`-power-torsion cohomology. -/
@[stacks 0G1T]
public theorem derivedTensorProduct_isZero_of_mod_ideal
    {R : Type u} [CommRing R] (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : IsZero
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R (R ⧸ I))))) :
    (∀ (n : ℕ), 0 < n →
      IsZero
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R (R ⧸ I ^ n))))) ∧
    (∀ (N : ModuleCat.{u} R), IsIPowerTorsion R N I →
      IsZero
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N))) ∧
    (∀ (M : DerivedCategory.Bounded (ModuleCat.{u} R)),
      (∀ i : ℤ, IsIPowerTorsion R
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M.obj) I) →
      IsZero
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
          M.obj)) := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R
  have hKpos (a : ℤ) := positive_homology_derivedTensorProduct_isZero_of_mod_ideal I (K⟦a⟧)
    (derivedTensorProduct_shift_isZero_of_mod_ideal I K hK a)
  refine ⟨fun n hn ↦ ?_, fun N hN ↦ ?_, derivedTensorProduct_bounded_isZero_of_mod_ideal I K hK⟩
  · exact isZero_of_positive_homology_of_shifts
      (T.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (R ⧸ I ^ n)))) K fun a j hj ↦ (hKpos a).1 n hn j hj
  · exact isZero_of_positive_homology_of_shifts
      (T.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)) K
      fun a j hj ↦ (hKpos a).2.1 N hN j hj

end IPowerTorsionDerivedTensor

end
