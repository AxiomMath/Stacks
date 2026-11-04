module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard

/-!
# Derived sheafification on `Spec R` and boundedness below

Results on derived sheafification of bounded-below complexes over an affine scheme `Spec R`.

Everything here is stated for arbitrary models `HasDerivedCategory.{w}` of `D(R)` and
`HasDerivedCategory.{w'}` of `D(𝒪_{Spec R})`, not only for the standard ones the base module
fixes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

universe w w'

namespace AlgebraicGeometry.StandardModel

variable (R : CommRingCat.{u})

/-- **Derived sheafification reflects the vanishing of a cohomology object.** For `M` an object
of `D(R)` the cohomology sheaf `Hⁿ(M̃^•)` is zero exactly when the cohomology module `Hⁿ(M^•)`
is. -/
theorem isZero_homology_mapDerivedCategory_obj_iff_univ
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (Spec R).Modules]
    (M : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
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
exactly when `M` is. -/
theorem isBoundedBelow_mapDerivedCategory_obj_iff_univ
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (Spec R).Modules]
    (M : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategoryB.IsBoundedBelow ((tilde.functor R).mapDerivedCategory.obj M) ↔
      DerivedCategoryB.IsBoundedBelow M := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, fun i hi => (isZero_homology_mapDerivedCategory_obj_iff_univ R M i).1 (hn i hi)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, fun i hi => (isZero_homology_mapDerivedCategory_obj_iff_univ R M i).2 (hn i hi)⟩

/-- **A bounded-below standard model for an object of `D⁺_QCoh(𝒪_{Spec R})`.** A complex of
`𝒪_{Spec R}`-modules which is cohomologically bounded below and has quasi-coherent cohomology
sheaves is isomorphic to `L̃^•` for some **bounded-below** object `L` of `D(R)`. -/
theorem exists_isBoundedBelow_iso_mapDerivedCategory_univ
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (Spec R).Modules]
    [(derivedTilde R).IsEquivalence]
    (E : DerivedCategory (Spec R).Modules)
    (hE : DerivedCategoryB.derivedCategoryBPlus (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) E) :
    ∃ L : DerivedCategory (ModuleCat.{u} R), DerivedCategoryB.IsBoundedBelow L ∧
      Nonempty ((tilde.functor R).mapDerivedCategory.obj L ≅ E) := by
  obtain ⟨L, ⟨eL⟩⟩ := Functor.EssSurj.mem_essImage (F := derivedTilde R)
    (⟨E, hE.2⟩ : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory)
  have e : (tilde.functor R).mapDerivedCategory.obj L ≅ E :=
    ((derivedTildeCompι R).app L).symm ≪≫
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.mapIso eL
  exact ⟨L, (isBoundedBelow_mapDerivedCategory_obj_iff_univ R L).1
    (DerivedCategoryB.isBoundedBelow_of_iso e.symm hE.1), ⟨e⟩⟩

/-- **The essential image of `D⁺(R)` under derived sheafification is `D⁺_QCoh(𝒪_{Spec R})`.** A
complex of `𝒪_{Spec R}`-modules is cohomologically bounded below with quasi-coherent cohomology
sheaves if and only if it is isomorphic to `L̃^•` for some bounded-below object `L` of `D(R)`. -/
theorem derivedCategoryBPlus_iff_exists_isBoundedBelow_iso_univ
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (Spec R).Modules]
    [(derivedTilde R).IsEquivalence]
    (E : DerivedCategory (Spec R).Modules) :
    DerivedCategoryB.derivedCategoryBPlus (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) E ↔
      ∃ L : DerivedCategory (ModuleCat.{u} R), DerivedCategoryB.IsBoundedBelow L ∧
        Nonempty ((tilde.functor R).mapDerivedCategory.obj L ≅ E) := by
  refine ⟨exists_isBoundedBelow_iso_mapDerivedCategory_univ R E, fun ⟨L, hL, ⟨e⟩⟩ => ?_⟩
  refine ⟨DerivedCategoryB.isBoundedBelow_of_iso e
    ((isBoundedBelow_mapDerivedCategory_obj_iff_univ R L).2 hL), fun n => ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso e)
    (isQuasicoherent_homology_mapDerivedCategory_obj R L n)

end AlgebraicGeometry.StandardModel

end
