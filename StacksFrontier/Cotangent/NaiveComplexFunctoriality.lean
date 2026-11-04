module

public import StacksFrontier.Cotangent.NaiveComparison

/-!
# The naive cotangent complex is functorial in the presentation

A morphism of extensions `θ : P ⟶ P'` of the same algebra `S` over the same base `R` induces a
map `NL(P → S) ⟶ NL(P' → S)` of the two-term complexes `Algebra.Extension.naiveComplex`: it is
`Algebra.Extension.Cotangent.map` in cohomological degree `-1`, it is
`Algebra.Extension.CotangentSpace.map` in degree `0`, and the square commutes by
`Algebra.Extension.CotangentSpace.map_cotangentComplex`.

## Main definitions

* `Algebra.Extension.naiveComplexMap`: the induced map of complexes.

## Main results

* `Algebra.Extension.naiveComplexMap_f_negOne`, `Algebra.Extension.naiveComplexMap_f_zero` and
  `Algebra.Extension.naiveComplexMap_f_eq_zero`: its components.
* `Algebra.Extension.naiveComplexMap_id` and `Algebra.Extension.naiveComplexMap_comp`:
  functoriality.
* `Algebra.Extension.isIso_naiveComplexMap`: a morphism of extensions with a two-sided inverse
  induces an isomorphism of the two-term complexes.

## References

* [Stacks Project, Tag 08R9](https://stacks.math.columbia.edu/tag/08R9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Algebra.Extension

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The conormal module of an extension is functorial, read on an element. -/
theorem Cotangent.map_id_apply (P : Extension.{v} R S) (x : P.Cotangent) :
    Cotangent.map (Hom.id P) x = x := by
  obtain ⟨y, rfl⟩ := Cotangent.mk_surjective x
  simp only [Cotangent.map_mk]
  rfl

/-- The conormal module of an extension is functorial, read on an element. -/
theorem Cotangent.map_comp_apply {P P' P'' : Extension.{v} R S} (f : P.Hom P')
    (g : P'.Hom P'') (x : P.Cotangent) :
    Cotangent.map (g.comp f) x = Cotangent.map g (Cotangent.map f x) := by
  obtain ⟨y, rfl⟩ := Cotangent.mk_surjective x
  simp only [Cotangent.map_mk]
  rfl

/-- The cotangent space of an extension is functorial, read on an element. -/
theorem cotangentSpace_map_id_apply (P : Extension.{v} R S) (x : P.CotangentSpace) :
    CotangentSpace.map (Hom.id P) x = x := by
  simp only [CotangentSpace.map_id, LinearMap.id_coe, id_eq]

/-- The cotangent space of an extension is functorial, read on an element. -/
theorem cotangentSpace_map_comp_apply {P P' P'' : Extension.{v} R S} (f : P.Hom P')
    (g : P'.Hom P'') (x : P.CotangentSpace) :
    CotangentSpace.map (g.comp f) x = CotangentSpace.map g (CotangentSpace.map f x) := by
  have h := LinearMap.congr_fun (CotangentSpace.map_comp f g) x
  simpa using h

section

variable {P P' : Extension.{v} R S} (θ : P.Hom P')

/-- The degree `-1` component of the induced map of naive cotangent complexes: the map
`J/J² → J'/J'²` of conormal modules. -/
def naiveComplexMapNegOne : (naiveComplex P).X (-1) ⟶ (naiveComplex P').X (-1) :=
  (naiveComplexXNegOneIso P).hom ≫ ModuleCat.ofHom (Cotangent.map θ) ≫
    (naiveComplexXNegOneIso P').inv

/-- The degree `0` component of the induced map of naive cotangent complexes: the map
`Ω[P⁄R] ⊗[P] S → Ω[P'⁄R] ⊗[P'] S` of cotangent spaces. -/
def naiveComplexMapZero : (naiveComplex P).X 0 ⟶ (naiveComplex P').X 0 :=
  (naiveComplexXZeroIso P).hom ≫ ModuleCat.ofHom (CotangentSpace.map θ) ≫
    (naiveComplexXZeroIso P').inv

/-- The component of the induced map in an arbitrary cohomological degree. -/
def naiveComplexMapComponent (i : ℤ) : (naiveComplex P).X i ⟶ (naiveComplex P').X i :=
  if h : i = -1 then
    eqToHom (by rw [h]) ≫ naiveComplexMapNegOne θ ≫ eqToHom (by rw [h])
  else if h' : i = 0 then
    eqToHom (by rw [h']) ≫ naiveComplexMapZero θ ≫ eqToHom (by rw [h'])
  else 0

/-- In degree `-1` the component of the induced map is `naiveComplexMapNegOne`. -/
theorem naiveComplexMapComponent_negOne :
    naiveComplexMapComponent θ (-1) = naiveComplexMapNegOne θ := by
  rw [naiveComplexMapComponent, dif_pos rfl, eqToHom_refl, eqToHom_refl, Category.id_comp,
    Category.comp_id]

/-- In degree `0` the component of the induced map is `naiveComplexMapZero`. -/
theorem naiveComplexMapComponent_zero :
    naiveComplexMapComponent θ 0 = naiveComplexMapZero θ := by
  rw [naiveComplexMapComponent, dif_neg (by decide), dif_pos rfl, eqToHom_refl, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- In cohomological degrees other than `-1` and `0`, the component of the induced map is zero. -/
theorem naiveComplexMapComponent_eq_zero (i : ℤ) (h : i ≠ -1) (h' : i ≠ 0) :
    naiveComplexMapComponent θ i = 0 := by
  rw [naiveComplexMapComponent, dif_neg h, dif_neg h']

/-- **The map of naive cotangent complexes induced by a morphism of extensions.** -/
def naiveComplexMap : naiveComplex P ⟶ naiveComplex P' where
  f := naiveComplexMapComponent θ
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases h1 : i = -1
    · have hj : j = 0 := by omega
      subst hj; subst h1
      rw [naiveComplexMapComponent_negOne, naiveComplexMapComponent_zero,
        naiveComplexMapNegOne, naiveComplexMapZero, naiveComplex_d, naiveComplex_d]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
      rw [CotangentSpace.map_cotangentComplex]
    · by_cases h2 : i = 0
      · have hj : j = 1 := by omega
        subst hj; subst h2
        exact (isZero_naiveComplex_X P' 1 (by decide) (by decide)).eq_of_tgt _ _
      · exact (isZero_naiveComplex_X P i h1 h2).eq_of_src _ _

/-- The component of `naiveComplexMap θ` in degree `i` is `naiveComplexMapComponent θ i`. -/
@[simp]
theorem naiveComplexMap_f (i : ℤ) :
    (naiveComplexMap θ).f i = naiveComplexMapComponent θ i := rfl

/-- In degree `-1` the induced map of naive cotangent complexes is `naiveComplexMapNegOne`. -/
theorem naiveComplexMap_f_negOne :
    (naiveComplexMap θ).f (-1) = naiveComplexMapNegOne θ :=
  naiveComplexMapComponent_negOne θ

/-- In degree `0` the induced map of naive cotangent complexes is `naiveComplexMapZero`. -/
theorem naiveComplexMap_f_zero :
    (naiveComplexMap θ).f 0 = naiveComplexMapZero θ :=
  naiveComplexMapComponent_zero θ

/-- Outside degrees `-1` and `0` the induced map of naive cotangent complexes is zero. -/
theorem naiveComplexMap_f_eq_zero (i : ℤ) (h : i ≠ -1) (h' : i ≠ 0) :
    (naiveComplexMap θ).f i = 0 :=
  naiveComplexMapComponent_eq_zero θ i h h'

end

/-- Morphisms of naive cotangent complexes are determined by their components in degrees `-1`
and `0`. -/
private theorem naiveComplex_hom_ext {P P' : Extension.{v} R S}
    {f g : naiveComplex P ⟶ naiveComplex P'}
    (h1 : f.f (-1) = g.f (-1)) (h0 : f.f 0 = g.f 0) : f = g := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases h1' : i = -1
  · subst h1'
    exact h1
  · by_cases h2 : i = 0
    · subst h2
      exact h0
    · exact (isZero_naiveComplex_X P i h1' h2).eq_of_src _ _

/-- The identity morphism of extensions induces the identity of naive cotangent complexes. -/
theorem naiveComplexMap_id (P : Extension.{v} R S) :
    naiveComplexMap (Hom.id P) = 𝟙 (naiveComplex P) := by
  refine naiveComplex_hom_ext ?_ ?_
  · rw [naiveComplexMap_f_negOne, naiveComplexMapNegOne, HomologicalComplex.id_f]
    simp only [Cotangent.map_id, ModuleCat.ofHom_id, Category.id_comp, Iso.hom_inv_id]
  · rw [naiveComplexMap_f_zero, naiveComplexMapZero, HomologicalComplex.id_f]
    simp only [CotangentSpace.map_id, ModuleCat.ofHom_id, Category.id_comp, Iso.hom_inv_id]

/-- The induced maps of naive cotangent complexes compose. -/
theorem naiveComplexMap_comp {P P' P'' : Extension.{v} R S} (θ : P.Hom P') (θ' : P'.Hom P'') :
    naiveComplexMap (θ'.comp θ) = naiveComplexMap θ ≫ naiveComplexMap θ' := by
  refine naiveComplex_hom_ext ?_ ?_
  · rw [HomologicalComplex.comp_f, naiveComplexMap_f_negOne, naiveComplexMap_f_negOne,
      naiveComplexMap_f_negOne, naiveComplexMapNegOne, naiveComplexMapNegOne,
      naiveComplexMapNegOne]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    rw [Cotangent.map_comp_apply]
  · rw [HomologicalComplex.comp_f, naiveComplexMap_f_zero, naiveComplexMap_f_zero,
      naiveComplexMap_f_zero, naiveComplexMapZero, naiveComplexMapZero, naiveComplexMapZero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    rw [cotangentSpace_map_comp_apply]

/-- A morphism of extensions with a two-sided inverse induces an isomorphism of the naive
cotangent complexes. -/
theorem isIso_naiveComplexMap {P P' : Extension.{v} R S} (θ : P.Hom P') (θ' : P'.Hom P)
    (h : θ'.comp θ = Hom.id P) (h' : θ.comp θ' = Hom.id P') :
    IsIso (naiveComplexMap θ) := by
  refine ⟨naiveComplexMap θ', ?_, ?_⟩
  · rw [← naiveComplexMap_comp, h, naiveComplexMap_id]
  · rw [← naiveComplexMap_comp, h', naiveComplexMap_id]

end Algebra.Extension

end
