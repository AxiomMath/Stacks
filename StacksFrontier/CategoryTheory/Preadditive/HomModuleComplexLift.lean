module

public import StacksFrontier.CategoryTheory.Preadditive.RetractsOfFiniteFree

/-!
# Lifting complexes of modules along `Hom(O, -)`

Let `C` be a preadditive category with finite biproducts, `O` an object of `C` and
`ρ : R →+* End O` a ring isomorphism. A complex `M` of `R`-modules whose terms are identified
with `Hom(O, F i)` for retracts `F i` of finite free objects lifts to a complex of `C` with
terms `F i`: `Hom(O, -)` is fully faithful on such objects.

## Main definitions

* `CategoryTheory.homModuleLiftComplex`: the lifted complex.
* `CategoryTheory.homModuleLiftComplexIso`: `Hom(O, -)` of the lifted complex is `M`.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe v w u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {R : Type w} [CommRing R] {O : C} {ρ : R →+* End O} (hρ : Function.Bijective ρ)
  {ι : Type*} {c : ComplexShape ι} (M : HomologicalComplex (ModuleCat.{v} R) c) (F : ι → C)
  (hF : ∀ i, IsRetractOfFiniteFree O (F i)) (e : ∀ i, (homModule O ρ).obj (F i) ≅ M.X i)

/-- The complex of `C` with terms `F i` whose image under `Hom(O, -)` is `M`, along the
identifications `e i : Hom(O, F i) ≅ M^i`. -/
def homModuleLiftComplex : HomologicalComplex C c where
  X := F
  d i j := homModulePreimage hρ (hF i) ((e i).hom ≫ M.d i j ≫ (e j).inv)
  shape i j h := homModule_map_injective hρ (hF i) (by simp [M.shape i j h])
  d_comp_d' i j k _ _ := homModule_map_injective hρ (hF i) (by simp)

/-- `Hom(O, -)` of the lifted complex is `M`. -/
def homModuleLiftComplexIso :
    ((homModule O ρ).mapHomologicalComplex c).obj (homModuleLiftComplex hρ M F hF e) ≅ M :=
  HomologicalComplex.Hom.isoOfComponents e (fun i j _ => by simp [homModuleLiftComplex])

/-- A term of the lifted complex vanishes where the corresponding term of `M` does. -/
lemma isZero_homModuleLiftComplex_X {i : ι} (h : IsZero (M.X i)) :
    IsZero ((homModuleLiftComplex hρ M F hF e).X i) :=
  (IsZero.iff_id_eq_zero _).2 (homModule_map_injective hρ (hF i)
    ((h.of_iso (e i)).eq_of_src _ _))

end CategoryTheory

end
