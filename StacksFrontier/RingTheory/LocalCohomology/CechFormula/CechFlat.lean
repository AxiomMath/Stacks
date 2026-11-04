module

public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.Flatness
public import StacksFrontier.RingTheory.LocalCohomology.CechModel

/-!
# The Čech complex of the regular module is K-flat, and kills torsion

The extended alternating Čech complex of a finite family `f₁, …, f_r` on the regular module is a
bounded complex of flat modules, hence K-flat: each of its terms is a finite direct sum of
localizations of the ring, and a localization is flat. So the derived tensor product with it may
be computed by tensoring complexes directly.

Its terms in *positive* degree have a stronger property. The summand of `C^p` indexed by a
`p`-element set `s` is a localization at a product of generators, so every generator occurring
in `s` acts invertibly on it; tensoring it with an `I`-power-torsion module therefore gives
zero. Since a positive-degree index set is nonempty, this kills the whole term. That is the
input which, fed through the stupid filtration of `BoundedFunctor`, makes the Čech augmentation
universal among morphisms out of the power-torsion subcategory — the content of the Čech formula
of Stacks 0A6R.

## Main results

* `Stacks.LocalCohomology.CechFormula.cechRegular_isKFlat` — the Čech complex of the regular
  module is K-flat.
* `Stacks.LocalCohomology.CechFormula.cechTerm_tensor_isZero` — a positive-degree Čech term
  tensored with a power-torsion module vanishes.
* `Stacks.LocalCohomology.CechFormula.cechTerm_derivedTensor_isZero` — the derived form, for an
  object of `D(A)` with power-torsion cohomology.
* `Stacks.LocalCohomology.CechFormula.cechRegular_derivedPowerTorsion` — the Čech object has
  power-torsion cohomology.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0G6K](https://stacks.math.columbia.edu/tag/0G6K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology.CechFormula

open CochainComplex.DerivedTensor
open Dualizing.Coreflection (isZero_iff_homology)

variable {A : Type u} [CommRing A] {r : ℕ}

/-- The regular module, lifted into the module universe. -/
abbrev regularModule (A : Type u) [CommRing A] : ModuleCat.{max u v} A :=
  ModuleCat.of A (ULift.{v} A)

/-- The extended alternating Čech complex of `f` on the regular module, in integer degrees. -/
abbrev cechRegularComplex (f : Fin r → A) : CochainComplex (ModuleCat.{max u v} A) ℤ :=
  extendedCechComplex f (regularModule.{u, v} A)

/-- The Čech complex of `f` on the regular module as an object of `D(A)`. -/
abbrev cechRegularObject (f : Fin r → A) : DerivedCategory (ModuleCat.{max u v} A) :=
  extendedCechObject f (regularModule.{u, v} A)

/-- Every term of the integer-indexed Čech complex of the regular module is flat: in
nonnegative degrees it is a finite direct sum of localizations of `A`, and elsewhere it is
zero. -/
theorem flat_cechRegularComplex_X (f : Fin r → A) (q : ℤ) :
    Module.Flat A ((cechRegularComplex.{u, v} f).X q) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = (n : ℤ) := ⟨q.toNat, by omega⟩
    have : Module.Flat A ((Cech.cechComplex f (regularModule.{u, v} A)).X n) :=
      cechTerm_flat.{u, v} f n
    exact Module.Flat.of_linearEquiv
      (HomologicalComplex.extendXIso (Cech.cechComplex f (regularModule.{u, v} A))
        ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) (by simp)).toLinearEquiv
  · exact Module.Flat.of_linearEquiv
      (isZero_extendedCechComplex_X f (regularModule.{u, v} A) q
        (Or.inl (lt_of_not_ge hq))).isoZero.toLinearEquiv

/-- **The Čech complex of the regular module is K-flat.** It is a complex of flat modules
concentrated in the degrees `0, …, r`, and a bounded complex of flat modules is K-flat. -/
theorem cechRegular_isKFlat (f : Fin r → A) : (cechRegularComplex.{u, v} f).KFlat := by
  have hbound : (cechRegularComplex.{u, v} f).IsStrictlyLE r := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro q hq
    exact isZero_extendedCechComplex_X f (regularModule.{u, v} A) q (Or.inr (by omega))
  have : ∀ q : ℤ, Module.Flat A ((cechRegularComplex.{u, v} f).X q) :=
    flat_cechRegularComplex_X.{u, v} f
  exact CochainComplex.KFlat.kFlat_of_flat (cechRegularComplex.{u, v} f) r

/-- **A positive-degree Čech term kills torsion.** Every index set of a term in degree `p > 0`
is nonempty, so some generator acts invertibly on each of its summands; tensoring with a module
all of whose elements are killed by a power of the ideal therefore gives zero. -/
theorem cechTerm_tensor_isZero (f : Fin r → A) (p : ℕ) (hp : 0 < p)
    (M : ModuleCat.{max u v} A)
    (hM : IsIPowerTorsion A M (Ideal.span (Set.range f))) :
    IsZero (ModuleCat.of A
      (TensorProduct A (Cech.cechTerm f (ULift.{v} A) p) M)) := by
  classical
  have h (s : {s : Finset (Fin r) // s.card = p}) :
      Subsingleton (TensorProduct A (Cech.cechMod f (ULift.{v} A) s.1) M) := by
    apply (ModuleCat.isZero_iff_subsingleton (M := ModuleCat.of A
      (TensorProduct A (Cech.cechMod f (ULift.{v} A) s.1) M))).mp
    apply (localizedTensor_isZero_iff (Cech.cechSub f s.1) M).2
    intro x
    obtain ⟨n, _, hn⟩ := hM x
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (s.2 ▸ hp)
    exact ⟨⟨(∏ j ∈ s.1, f j) ^ n, ⟨n, rfl⟩⟩,
      hn _ (Ideal.pow_mem_pow
        (Ideal.prod_mem _ hj (Ideal.subset_span (Set.mem_range_self j))) n)⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr (TensorProduct.directSumLeft A A
    (fun s : {s : Finset (Fin r) // s.card = p} =>
      Cech.cechMod f (ULift.{v} A) s.1) M).injective.subsingleton

/-- **The derived form.** For `X` with `I`-power-torsion cohomology, the derived tensor product of
`X` with a positive-degree Čech term, placed in any degree, vanishes. The term is flat, so
`flatTensorHomologyIso` reduces this to the module-level statement in every degree. -/
theorem cechTerm_derivedTensor_isZero
    (T : DerivedTensorProductGeneral.{u, v} A) (f : Fin r → A)
    (X : DerivedCategory (ModuleCat.{max u v} A))
    (hX : ∀ i, IsIPowerTorsion A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj X)
      (Ideal.span (Set.range f))) (p : ℕ) (hp : 0 < p) (q : ℤ) :
    IsZero ((T.tensor.flip.obj X).obj ((DerivedCategory.singleFunctor _ q).obj
      (ModuleCat.of A (Cech.cechTerm f (ULift.{v} A) p)))) := by
  let M := ModuleCat.of A (Cech.cechTerm f (ULift.{v} A) p)
  let F := T.tensor.flip.obj X
  have : Module.Flat A M := cechTerm_flat f p
  have hz : IsZero (F.obj ((DerivedCategory.singleFunctor _ 0).obj M)) := by
    refine (isZero_iff_homology _).2 fun i => ?_
    exact (cechTerm_tensor_isZero f p hp _ (hX i)).of_iso (flatTensorHomologyIso T M X i)
  exact ((shiftFunctor _ (-q)).map_isZero hz).of_iso
    (F.mapIso (((DerivedCategory.singleFunctors _).shiftIso (-q) q 0 (by simp)).app M).symm ≪≫
      (F.commShiftIso (-q)).app _)

/-- **Tag 0G6K for the regular module.** The Čech object has `I`-power-torsion cohomology. This
is the computation of `CechModel`, read at the regular module. -/
theorem cechRegular_derivedPowerTorsion (f : Fin r → A) (I : Ideal A) (hI : I.FG)
    (hIf : Ideal.span (Set.range f) = I) :
    Dualizing.derivedPowerTorsionProperty A I hI (cechRegularObject.{u, v} f) :=
  derivedPowerTorsionProperty_extendedCechObject f (regularModule.{u, v} A) I hI hIf

end Stacks.LocalCohomology.CechFormula
