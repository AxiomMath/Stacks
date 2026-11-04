module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard

/-!
# The bounded-below standard model of a quasi-coherent complex on an affine scheme

Let `R` be a commutative ring. `AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`
presents every object of `D_QCoh(𝒪_{Spec R})` as a derived sheafification `M̃^•`, with `M` an
object of the *unbounded* derived category `D(R)`. This file refines that presentation on the
bounded-below part of the category: if `E` lies in `D⁺_QCoh(𝒪_{Spec R})`, the object `M` of
`D(R)` may be taken bounded below, so that `E` has a *standard model in `D⁺(R)`*.

The refinement is the statement that derived sheafification *reflects* cohomological
boundedness below, which in turn is the statement that it reflects the vanishing of a single
cohomology object: `Hⁿ(M̃^•) ≅ (Hⁿ(M^•))^~` because `~` is exact, and `M̃ = 0` forces `M = 0`
because `~` is faithful and additive. The forward implication — derived sheafification preserves
boundedness below — is already
`AlgebraicGeometry.isBoundedBelow_tilde_mapDerivedCategory_obj`.

## Main results

* `AlgebraicGeometry.StandardModel.isZero_homology_mapDerivedCategory_obj_iff` — derived
  sheafification both preserves and reflects the vanishing of a cohomology object.
* `AlgebraicGeometry.StandardModel.isBoundedBelow_mapDerivedCategory_obj_iff` — derived
  sheafification both preserves and reflects cohomological boundedness below.
* `AlgebraicGeometry.StandardModel.exists_isBoundedBelow_iso_mapDerivedCategory` — **the
  bounded-below standard model.** An object of `D⁺_QCoh(𝒪_{Spec R})` is isomorphic to `L̃^•` for
  some bounded-below object `L` of `D(R)`.
* `AlgebraicGeometry.StandardModel.derivedCategoryBPlus_iff_exists_isBoundedBelow_iso` — the
  essential image of `D⁺(R)` under derived sheafification is exactly `D⁺_QCoh(𝒪_{Spec R})`.

## Implementation notes

The derived categories are the standard model, as in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean`, and that
file's implementation notes require of its importers that the attribute selecting it carry
priority `10000`: the import closure installs the locally small model as a *global* instance,
which beats a default-priority local attribute.

The general form of the reflection statements proved here — for an arbitrary faithful exact
additive functor between abelian categories — is
`CategoryTheory.Functor.isZero_homologyFunctor_obj_mapDerivedCategory_obj_iff` and
`DerivedCategoryB.isBoundedBelow_mapDerivedCategory_obj_iff` of
`StacksFrontier/AlgebraicGeometry/DerivedCoherent/Modules.lean`. They are not used here, and the
proofs below are the same three lines specialized to `~`: that file is the derived category of
coherent modules on a Noetherian scheme, whose import closure carries the coherator equivalence
of [Stacks, Tag 09T4] and the Noetherian extension equivalence, none of which the present
statement has anything to do with. Importing it to borrow two general lemmas stated in
`CategoryTheory.Functor` and `DerivedCategoryB` would make a statement about `Spec R` depend on
all of that. The general lemmas belong next to
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, which is their only real input; moving
them there is a change to an existing interface and is left alone.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.StandardModel

variable (R : CommRingCat.{u})

/-- **Derived sheafification reflects the vanishing of a cohomology object.** For `M` an object
of `D(R)` the cohomology sheaf `Hⁿ(M̃^•)` is zero exactly when the cohomology module `Hⁿ(M^•)`
is.

Sheafification is exact, so `Hⁿ(M̃^•) ≅ (Hⁿ(M^•))^~`; and `~` is additive and faithful, so a
module whose associated sheaf is zero has `𝟙` mapping to `0`, hence has `𝟙 = 0`. -/
theorem isZero_homology_mapDerivedCategory_obj_iff (M : DerivedCategory (ModuleCat.{u} R))
    (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        ((tilde.functor R).mapDerivedCategory.obj M)) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M) := by
  refine ⟨fun h => ?_, fun h => ((tilde.functor R).map_isZero h).of_iso
    (((tilde.functor R).mapDerivedCategoryHomologyIso n).app M)⟩
  have hz : IsZero ((tilde.functor R).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M)) :=
    h.of_iso (((tilde.functor R).mapDerivedCategoryHomologyIso n).app M).symm
  refine (IsZero.iff_id_eq_zero _).2 (Functor.map_injective (tilde.functor R) ?_)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hz.eq_of_src _ _

/-- **Derived sheafification preserves and reflects cohomological boundedness below.** For `M`
an object of `D(R)`, the complex `M̃^•` of `𝒪_{Spec R}`-modules is cohomologically bounded below
exactly when `M` is, the two having the same vanishing degrees by
`AlgebraicGeometry.StandardModel.isZero_homology_mapDerivedCategory_obj_iff`. -/
theorem isBoundedBelow_mapDerivedCategory_obj_iff (M : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategoryB.IsBoundedBelow ((tilde.functor R).mapDerivedCategory.obj M) ↔
      DerivedCategoryB.IsBoundedBelow M := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, fun i hi => (isZero_homology_mapDerivedCategory_obj_iff R M i).1 (hn i hi)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, fun i hi => (isZero_homology_mapDerivedCategory_obj_iff R M i).2 (hn i hi)⟩

/-- **A bounded-below standard model for an object of `D⁺_QCoh(𝒪_{Spec R})`.** A complex of
`𝒪_{Spec R}`-modules which is cohomologically bounded below and has quasi-coherent cohomology
sheaves is isomorphic to `L̃^•` for some **bounded-below** object `L` of `D(R)`.

`AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory` supplies the object `L` of
`D(R)` and the isomorphism from quasi-coherence alone; the boundedness below of `L` is then read
off the boundedness below of `E` across the isomorphism, derived sheafification reflecting it. -/
theorem exists_isBoundedBelow_iso_mapDerivedCategory (E : DerivedCategory (Spec R).Modules)
    (hE : DerivedCategoryB.derivedCategoryBPlus (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) E) :
    ∃ L : DerivedCategory (ModuleCat.{u} R), DerivedCategoryB.IsBoundedBelow L ∧
      Nonempty ((tilde.functor R).mapDerivedCategory.obj L ≅ E) := by
  obtain ⟨L, ⟨e⟩⟩ := exists_iso_mapDerivedCategory R E hE.2
  exact ⟨L, (isBoundedBelow_mapDerivedCategory_obj_iff R L).1
    (DerivedCategoryB.isBoundedBelow_of_iso e.symm hE.1), ⟨e⟩⟩

/-- **The essential image of `D⁺(R)` under derived sheafification is `D⁺_QCoh(𝒪_{Spec R})`.** A
complex of `𝒪_{Spec R}`-modules is cohomologically bounded below with quasi-coherent cohomology
sheaves if and only if it is isomorphic to `L̃^•` for some bounded-below object `L` of `D(R)`.

This is
`AlgebraicGeometry.StandardModel.isQuasicoherent_homology_iff_exists_iso_mapDerivedCategory` with
both sides intersected with boundedness below. -/
theorem derivedCategoryBPlus_iff_exists_isBoundedBelow_iso
    (E : DerivedCategory (Spec R).Modules) :
    DerivedCategoryB.derivedCategoryBPlus (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) E ↔
      ∃ L : DerivedCategory (ModuleCat.{u} R), DerivedCategoryB.IsBoundedBelow L ∧
        Nonempty ((tilde.functor R).mapDerivedCategory.obj L ≅ E) := by
  refine ⟨exists_isBoundedBelow_iso_mapDerivedCategory R E, fun ⟨L, hL, ⟨e⟩⟩ => ?_⟩
  refine ⟨DerivedCategoryB.isBoundedBelow_of_iso e
    ((isBoundedBelow_mapDerivedCategory_obj_iff R L).2 hL), fun n => ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso e)
    (isQuasicoherent_homology_mapDerivedCategory_obj R L n)

end AlgebraicGeometry.StandardModel

end
