module

public import StacksFrontier.Homology.Perfect.DerivedTensorFibre
public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.PseudoCoherent.Tensor
public import StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessPerfectionChain
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessResidueWindow
import all StacksFrontier.Homology.Perfect.DerivedTensorFibre
import all StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible

/-!
# The local computation at a maximal ideal for [stacks 0E2D]

Let `A` be a commutative ring and `P` an object of `D(A)`. All derived tensor products here are
the tensor of the tensor--Hom adjunction of [stacks 0A63]. If `P ⊗ᴸ_A T ≅ T` for a bounded object
`T` whose cohomology is finite and killed by a maximal ideal `m`, then the derived fibre
`P ⊗ᴸ_A κ(m)` is the residue field `κ(m)` in degree zero, provided it is bounded. A
pseudo-coherent `P` whose derived fibre at every maximal ideal is `κ(m)` in degree zero, and with
`RHom_A(P, A) ≅ A`, is isomorphic to `A`.

## Main definitions

* `Dualizing.canonicalTensorIsoDerivedHomTensor`: the canonical derived tensor product of
  [stacks 068I] is isomorphic to the tensor of the tensor--Hom adjunction of [stacks 0A63].
* `Dualizing.residueSingle`: the residue field `A / m` as an object of `D(A)` in degree zero.
* `Dualizing.derivedFibre`: the derived fibre `P ⊗ᴸ_A (A / m)[0]`.
* `Dualizing.tensorResidueIso`: `P ⊗ᴸ ω ≅ ω` gives `P ⊗ᴸ (ω ⊗ᴸ κ) ≅ ω ⊗ᴸ κ`.

## Main results

* `Dualizing.isPerfect_of_fibre_window`: a pseudo-coherent object whose derived fibres at the
  maximal ideals lie in a fixed finite window is perfect ([stacks 068V]).
* `Dualizing.nonempty_iso_derivedTensorUnit_of_fibre_concentrated`: a pseudo-coherent `P` whose
  derived fibre at every maximal ideal is the residue field in degree zero, and with
  `RHom_A(P, A) ≅ A`, is isomorphic to `A`.
* `Dualizing.fibre_eq_residueField_of_derivedTensor_iso_of_isTorsionBySet`: if `P ⊗ᴸ_A T ≅ T`,
  then `P ⊗ᴸ_A κ(m)` is `κ(m)` in degree zero.
* `Dualizing.isTorsionBySet_homology_derivedFibre`: the cohomology of the derived fibre of a
  pseudo-coherent object at `m` is killed by `m`.
* `Dualizing.finite_homology_derivedFibre_and_exists_isLE`: over a Noetherian ring, the cohomology
  of the derived fibre of a pseudo-coherent object is finite and vanishes above some degree.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 068V](https://stacks.math.columbia.edu/tag/068V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedTensor CochainComplex.DerivedExtensionScalars

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

section FibreSpelling

variable (A : Type u) [CommRing A]

/-- The canonical derived tensor product of [stacks 068I] and the tensor of the tensor--Hom
adjunction of [stacks 0A63] agree at every pair of objects of `D(A)`. -/
@[no_expose] def canonicalTensorIsoDerivedHomTensor (P Q : DerivedCategory (ModuleCat.{u} A)) :
    ((canonicalDerivedTensorProduct A).tensor.obj P).obj Q ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj (P, Q) :=
  derivedTensorGeneralObjIso (canonicalDerivedTensorProduct A).toGeneral
      (canonicalDerivedTensorProductGeneral.{u, u} A) P Q ≪≫
    (derivedHomAdjunctionTensorNatIsoGeneral.{u, u} A).app (P, Q)

/-- The quotient `A / m` by an ideal `m`, as an object of `D(A)` in degree zero. -/
abbrev residueSingle (m : Ideal A) : DerivedCategory (ModuleCat.{u} A) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ m))

/-- The derived fibre `P ⊗ᴸ_A (A / m)[0]`, taken at the tensor of the tensor--Hom adjunction of
[stacks 0A63]. -/
abbrev derivedFibre (P : DerivedCategory (ModuleCat.{u} A)) (m : Ideal A) :
    DerivedCategory (ModuleCat.{u} A) :=
  (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
    (P, residueSingle A m)

variable {A}

/-- The degree-`i` cohomology of the derived fibre at `m` is that of the canonical derived tensor
product of `P` with `(A / m)[0]`. -/
private def homologyDerivedFibreIso (m : Ideal A) (P : DerivedCategory (ModuleCat.{u} A))
    (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (((canonicalDerivedTensorProduct A).tensor.obj P).obj (residueSingle A m)) ≅
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (derivedFibre A P m) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
    (canonicalTensorIsoDerivedHomTensor A P (residueSingle A m))

/-- A vanishing range for the degrees of `X.IsGE a` and `X.IsLE b` kills the cohomology. -/
private theorem isZero_homology_of_lt_or_lt (X : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ)
    (hGE : X.IsGE a) (hLE : X.IsLE b) (i : ℤ) (hi : i < a ∨ b < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X) := by
  rcases hi with hi | hi
  · exact (DerivedCategory.isGE_iff _ a).1 hGE i hi
  · exact (DerivedCategory.isLE_iff _ b).1 hLE i hi

/-- Let `m` be a maximal ideal and `P` a pseudo-coherent object of `D(A)`. If the degree-`i`
cohomology of the derived fibre `P ⊗ᴸ_A (A / m)[0]`, taken at the tensor of [stacks 0A63], is
`A / m` as an `A`-module, then the degree-`i` cohomology of the derived fibre of `P` at `m` taken
in `D(κ(m))` is one-dimensional over `κ(m)`. -/
theorem finrank_homology_fibre_eq_one_of_nonempty_iso_quotient (m : Ideal A) [m.IsMaximal]
    (P : DerivedCategory (ModuleCat.{u} A))
    (hP : StacksDraft.PseudoCoherence.IsPseudoCoherent P) (i : ℤ)
    (h : Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (derivedFibre A P m) ≅ ModuleCat.of A (A ⧸ m))) :
    Module.finrank m.ResidueField
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} m.ResidueField) i).obj
        ((totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A m.ResidueField)).functor.obj P)) = 1 :=
  StacksDraft.Perfect.finrank_homology_totalDerivedExtensionScalars_eq_one_of_nonempty_iso_quotient
    m P hP i (h.map fun e ↦ homologyDerivedFibreIso m P i ≪≫ e)

/-- Let `m` be a maximal ideal and `P` a pseudo-coherent object of `D(A)`. If the degree-`i`
cohomology of `P ⊗ᴸ_A (A / m)[0]` vanishes then the degree-`i` cohomology of the derived fibre of
`P` at `m` taken in `D(κ(m))` is zero-dimensional over `κ(m)`. -/
theorem finrank_homology_fibre_eq_zero_of_isZero (m : Ideal A) [m.IsMaximal]
    (P : DerivedCategory (ModuleCat.{u} A))
    (hP : StacksDraft.PseudoCoherence.IsPseudoCoherent P) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (derivedFibre A P m))) :
    Module.finrank m.ResidueField
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} m.ResidueField) i).obj
        ((totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A m.ResidueField)).functor.obj P)) = 0 :=
  StacksDraft.Perfect.finrank_homology_totalDerivedExtensionScalars_eq_zero_of_isZero
    m P hP i (h.of_iso (homologyDerivedFibreIso m P i))

/-- Let `P` be a pseudo-coherent object of `D(A)`. If at every maximal ideal `m` the derived fibre
`P ⊗ᴸ_A (A / m)[0]` is concentrated in degree zero with cohomology `A / m` there, then at every
maximal ideal the derived fibre of `P` taken in `D(κ(m))` has a single nonzero cohomology module,
of dimension one over `κ(m)`. -/
theorem maximalFibre_finrank_of_fibre_concentrated (P : DerivedCategory (ModuleCat.{u} A))
    (hP : StacksDraft.PseudoCoherence.IsPseudoCoherent P)
    (hGE : ∀ (m : Ideal A) (_ : m.IsMaximal), (derivedFibre A P m).IsGE 0)
    (hLE : ∀ (m : Ideal A) (_ : m.IsMaximal), (derivedFibre A P m).IsLE 0)
    (hone : ∀ (m : Ideal A) (_ : m.IsMaximal),
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (derivedFibre A P m) ≅ ModuleCat.of A (A ⧸ m))) :
    ∀ (m : Ideal A) (_ : m.IsMaximal), ∃ n : ℤ, ∀ i : ℤ,
      Module.finrank m.ResidueField
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} m.ResidueField) i).obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (algebraMap A m.ResidueField)).functor.obj P)) = if i = n then 1 else 0 := by
  intro m hm
  refine ⟨0, fun i ↦ ?_⟩
  split_ifs with hi
  · subst hi
    exact finrank_homology_fibre_eq_one_of_nonempty_iso_quotient m P hP 0 (hone m hm)
  · exact finrank_homology_fibre_eq_zero_of_isZero m P hP i
      (isZero_homology_of_lt_or_lt _ 0 0 (hGE m hm) (hLE m hm) i (lt_or_gt_of_ne hi))

end FibreSpelling

section Perfection

variable {A : Type u} [CommRing A]

/-- A pseudo-coherent object of `D(A)` whose derived fibre lies in a fixed window `[a, b]` at every
maximal ideal is perfect: the backward half of [stacks 068V], tested at the maximal ideals and read
for the tensor of the tensor--Hom adjunction of [stacks 0A63]. -/
theorem isPerfect_of_fibre_window (P : DerivedCategory (ModuleCat.{u} A))
    (hP : StacksDraft.PseudoCoherence.IsPseudoCoherent P) (a b : ℤ)
    (hGE : ∀ (m : Ideal A) (_ : m.IsMaximal), (derivedFibre A P m).IsGE a)
    (hLE : ∀ (m : Ideal A) (_ : m.IsMaximal), (derivedFibre A P m).IsLE b) :
    StacksDraft.Perfect.IsPerfect P := by
  have h := StacksDraft.Perfect.isPerfect_and_torAmplitude_iff_fibreCohomologyVanishes.{u, u}
    P hP a b
  refine (h.1.mpr (h.2.mpr ?_)).1
  intro mm i hi
  have := mm.isMaximal
  have hz := isZero_homology_of_lt_or_lt _ a b (hGE mm.asIdeal mm.isMaximal)
    (hLE mm.asIdeal mm.isMaximal) i hi
  refine
    StacksDraft.Perfect.fibreCohomologyVanishes_of_isZero_homology_derivedTensor_single_residueField
      mm.asIdeal P hP i ?_
  exact ((hz.of_iso (homologyDerivedFibreIso mm.asIdeal P i)).of_iso
      (StacksDraft.Perfect.homologyDerivedTensorQuotientIsoResidueField mm.asIdeal P i).symm)

/-- A pseudo-coherent object of `D(A)` whose derived fibre at every maximal ideal is concentrated
in degree zero is perfect. -/
theorem isPerfect_of_fibre_concentrated (P : DerivedCategory (ModuleCat.{u} A))
    (hP : StacksDraft.PseudoCoherence.IsPseudoCoherent P)
    (hGE : ∀ (m : Ideal A) (_ : m.IsMaximal), (derivedFibre A P m).IsGE 0)
    (hLE : ∀ (m : Ideal A) (_ : m.IsMaximal), (derivedFibre A P m).IsLE 0) :
    StacksDraft.Perfect.IsPerfect P :=
  isPerfect_of_fibre_window P hP 0 0 hGE hLE

/-- Let `P` be a pseudo-coherent object of `D(A)` whose derived fibre `P ⊗ᴸ_A (A / m)[0]` is, at
every maximal ideal `m`, concentrated in degree zero with cohomology `A / m` there. If derived Hom
from `P` into the tensor unit is the tensor unit, then `P` is the tensor unit. -/
theorem nonempty_iso_derivedTensorUnit_of_fibre_concentrated
    (P : DerivedCategory (ModuleCat.{u} A))
    (hP : StacksDraft.PseudoCoherence.IsPseudoCoherent P)
    (hGE : ∀ (m : Ideal A) (_ : m.IsMaximal), (derivedFibre A P m).IsGE 0)
    (hLE : ∀ (m : Ideal A) (_ : m.IsMaximal), (derivedFibre A P m).IsLE 0)
    (hone : ∀ (m : Ideal A) (_ : m.IsMaximal),
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (derivedFibre A P m) ≅ ModuleCat.of A (A ⧸ m)))
    (h : (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).hom.obj
        (Opposite.op P, StacksDraft.DerivedHom.derivedTensorUnit.{u, u, u + 1} A) ≅
      StacksDraft.DerivedHom.derivedTensorUnit.{u, u, u + 1} A) :
    Nonempty (P ≅ StacksDraft.DerivedHom.derivedTensorUnit.{u, u, u + 1} A) :=
  nonempty_iso_derivedTensorUnit_of_maximalFibre_finrank P
    (isPerfect_of_fibre_concentrated P hP hGE hLE)
    (maximalFibre_finrank_of_fibre_concentrated P hP hGE hLE hone) h

end Perfection

section Abstract

universe u₁ v₁ w₁

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
    (d : StacksDraft.DerivedHom.DerivedHomAdjunction R)

/-- For the tensor of a derived tensor--Hom adjunction `d`, an isomorphism `P ⊗ᴸ ω ≅ ω` gives
`P ⊗ᴸ (ω ⊗ᴸ κ) ≅ ω ⊗ᴸ κ` for every `κ`. -/
def tensorResidueIso {P ω : DerivedCategory (ModuleCat.{v₁} R)}
    (e : d.tensor.obj (P, ω) ≅ ω) (κ : DerivedCategory (ModuleCat.{v₁} R)) :
    d.tensor.obj (P, d.tensor.obj (ω, κ)) ≅ d.tensor.obj (ω, κ) :=
  (d.tensorAssoc P ω κ).symm ≪≫ tensorIso d e (Iso.refl κ)

end Abstract

section LocalComputation

variable {A : Type u} [CommRing A]

/-- Let `m` be a maximal ideal, `κ = A / m`, and let `T` be an object of `D(A)` with cohomology
concentrated in `[a, b]`, every cohomology module finite and killed by `m`, and `H^a(T)` and
`H^b(T)` nonzero.  Suppose `P ⊗ᴸ_A T ≅ T`, and suppose `P ⊗ᴸ_A κ` has cohomology concentrated in
`[c, d]` and nonvanishing in those two degrees.  Then

`c = 0`,  `d = 0`  and  `H⁰(P ⊗ᴸ_A κ) ≅ κ`,

so `P ⊗ᴸ_A κ` is the residue field in degree zero. -/
theorem fibre_eq_residueField_of_derivedTensor_iso_of_isTorsionBySet
    (m : Ideal A) [m.IsMaximal] (P T : DerivedCategory (ModuleCat.{u} A)) (a b c d : ℤ)
    (ha : T.IsGE a) (hb : T.IsLE b)
    (hkill : ∀ i : ℤ, Module.IsTorsionBySet A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T) (m : Set A))
    (hfin : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T))
    (hGE : (derivedFibre A P m).IsGE c) (hLE : (derivedFibre A P m).IsLE d)
    (hc : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) c).obj
      (derivedFibre A P m)))
    (hd : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) d).obj
      (derivedFibre A P m)))
    (hbot : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) a).obj T))
    (htop : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) b).obj T))
    (e : (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
      (P, T) ≅ T) :
    c = 0 ∧ d = 0 ∧ Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      (derivedFibre A P m) ≅ ModuleCat.of A (A ⧸ m)) := by
  obtain ⟨hc0, hd0⟩ := eq_zero_of_derivedTensor_iso_of_isTorsionBySet A m P T a b c d ha hb hkill
    hfin hGE hLE hc hd hbot htop e
  subst hc0
  exact ⟨rfl, hd0, nonempty_homology_derivedTensor_iso_residueField_of_isTorsionBySet A m P T a b
    ha hb hkill hfin hGE hbot e⟩

end LocalComputation

/-! ### Cohomology of derived fibres

The cohomology of the derived fibre `Dualizing.derivedFibre A X m` of a pseudo-coherent `X` at a
maximal ideal `m` is killed by `m`; over a Noetherian ring it is finite and vanishes above some
degree. -/

section FixedObject

variable {A : Type u} [CommRing A]

/-- For a pseudo-coherent `X` and a maximal ideal `m`, every cohomology module of the derived fibre
`X ⊗ᴸ_A (A / m)[0]` is killed by `m`. -/
theorem isTorsionBySet_homology_derivedFibre (m : Ideal A) [m.IsMaximal]
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : StacksDraft.PseudoCoherence.IsPseudoCoherent X) (i : ℤ) :
    Module.IsTorsionBySet A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (derivedFibre A X m))
      (m : Set A) := by
  obtain ⟨e⟩ :=
    StacksDraft.Perfect.nonempty_restrictScalars_homology_totalDerivedExtensionScalars_iso_homology_derivedTensor_single_residueField
      m X hX i
  refine StacksDraft.ResidueLength.isTorsionBySet_of_iso (m : Set A)
    (e ≪≫ (StacksDraft.Perfect.homologyDerivedTensorQuotientIsoResidueField m X i).symm ≪≫
      homologyDerivedFibreIso m X i) ?_
  intro x a
  rw [ModuleCat.restrictScalars.smul_def (algebraMap A m.ResidueField),
    Ideal.algebraMap_residueField_eq_zero.mpr a.2, zero_smul]
  rfl

/-- Over a Noetherian ring, the derived fibre of a pseudo-coherent object at a maximal ideal is
pseudo-coherent. -/
theorem isPseudoCoherent_derivedFibre [IsNoetherianRing A] (m : Ideal A) [m.IsMaximal]
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : StacksDraft.PseudoCoherence.IsPseudoCoherent X) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent (derivedFibre A X m) :=
  ((StacksDraft.PseudoCoherence.pseudoCoherent_canonicalDerivedTensorProduct X
    (residueSingle A m)).2 hX
      (isPseudoCoherent_singleFunctor_obj (ModuleCat.of A (A ⧸ m)))).ofIso
    (canonicalTensorIsoDerivedHomTensor A X (residueSingle A m))

/-- Over a Noetherian ring, the cohomology modules of the derived fibre of a pseudo-coherent object
at a maximal ideal are finite, and vanish above some degree. -/
theorem finite_homology_derivedFibre_and_exists_isLE [IsNoetherianRing A] (m : Ideal A)
    [m.IsMaximal] (X : DerivedCategory (ModuleCat.{u} A))
    (hX : StacksDraft.PseudoCoherence.IsPseudoCoherent X) :
    (∀ i : ℤ, Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (derivedFibre A X m))) ∧
      ∃ b : ℤ, (derivedFibre A X m).IsLE b := by
  obtain ⟨⟨b, hb⟩, hfin⟩ :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      (derivedFibre A X m) 0 A).2.1.mp (isPseudoCoherent_derivedFibre m X hX)
  exact ⟨hfin, b, (DerivedCategory.isLE_iff _ b).2 hb⟩

end FixedObject

end Dualizing

end
