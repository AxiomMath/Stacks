module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-!
# The distinguished triangles relating two successive truncations

For an object `E` of the derived category of an abelian category and an integer `a`, the two
successive truncations from below sit in a distinguished triangle
```
H^a(E)[-a] ⟶ τ^{≥a} E ⟶ τ^{≥a+1} E ⟶ (H^a(E)[-a])[1]
```
whose second map is the canonical comparison of truncations
`TStructure.natTransTruncGEOfLE a (a+1)`, and dually the two successive truncations from above sit
in a distinguished triangle
```
τ^{≤a} E ⟶ τ^{≤a+1} E ⟶ H^{a+1}(E)[-a-1] ⟶ (τ^{≤a} E)[1]
```
whose first map is `TStructure.natTransTruncLEOfLE a (a+1)`. These are the t-structure forms of
the canonical triangles of Stacks 08J5, which are formalized for the truncations of a complex,
with all their maps, in `StacksFrontier.Algebra.Homology.DerivedCategory.TruncationTriangles`.

The triangle of truncations from below is the step that turns the tower `n ↦ τ^{≥-n} E` of
`truncGETower` into something a cohomological functor can analyse one degree at a time: applying
derived sections to it expresses the difference between consecutive terms of the tower through
the cohomology sheaves of `E`, which is exactly the shape in which the hypotheses of the
convergence statements Stacks 0D62 and Stacks 0D6M are given.

## Main results

* `DerivedCategory.exists_truncLESucc_triangle`: existence of the triangle of truncations from
  above, with its first map the canonical comparison of truncations.
* `DerivedCategory.exists_truncGESucc_triangle`: existence of the triangle of truncations from
  below, with its second map the canonical comparison of truncations.

## Implementation notes

The triangle of truncations from below is produced from Mathlib's truncation triangle
`τ^{<a+1} ⟶ id ⟶ τ^{≥a+1}` applied to `τ^{≥a} E`.  Its first vertex `τ^{<a+1} τ^{≥a} E` is both
`≥ a` and `≤ a`, hence isomorphic to a complex concentrated in degree `a`
(`DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`), and
`DerivedCategory.isIso_homologyMap_truncLTι_app` and
`DerivedCategory.isIso_homologyMap_truncGEπ_app` identify its cohomology in degree `a` with
`H^a(E)`, so that complex is `H^a(E)[-a]`.
Its third vertex is identified with `τ^{≥a+1} E` through
`TStructure.isIso_truncGE_map_truncGEπ_app`, and the resulting square is checked by the extension
property `TStructure.from_truncGE_obj_ext` rather than by rewriting, since the two sides are
morphisms out of a truncation. The triangle of truncations from above is obtained the same way
from `TStructure.triangleLEGE_distinguished` applied to `τ^{≤a+1} E`, with
`TStructure.to_truncLE_obj_ext` checking its square.

Only the existence of the triangles is asserted: their remaining maps are not canonical.

## References

* [Stacks Project, Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An object that is both `≥ a` and `≤ a` is isomorphic to `Y` placed in degree `a` as soon as its
cohomology in degree `a` is isomorphic to `Y`. -/
private theorem nonempty_iso_singleFunctor_obj_of_iso_homology
    (X : DerivedCategory C) (a : ℤ) [TStructure.t.IsGE X a] [TStructure.t.IsLE X a] (Y : C)
    (e : (homologyFunctor C a).obj X ≅ Y) : Nonempty (X ≅ (singleFunctor C a).obj Y) := by
  obtain ⟨M, ⟨eM⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE X a
  exact ⟨eM ≪≫ (singleFunctor C a).mapIso
    (((homologyFunctor C a).mapIso eM ≪≫
      (singleFunctorCompHomologyFunctorIso C a).app M).symm ≪≫ e)⟩

/-- The t-structure form of the second triangle of Stacks 08J5. Two successive truncations from above of an
object of the derived category differ by its cohomology in the newly retained degree, placed in
that degree: there is a distinguished triangle
`τ^{≤a} E ⟶ τ^{≤a+1} E ⟶ H^{a+1}(E)[-a-1] ⟶ (τ^{≤a} E)[1]` whose first map is the canonical
comparison of truncations. -/
public theorem exists_truncLESucc_triangle (E : DerivedCategory C) (a : ℤ) :
    ∃ (g : (TStructure.t.truncLE (a + 1)).obj E ⟶
        (singleFunctor C (a + 1)).obj ((homologyFunctor C (a + 1)).obj E))
      (δ : (singleFunctor C (a + 1)).obj ((homologyFunctor C (a + 1)).obj E) ⟶
        ((TStructure.t.truncLE a).obj E)⟦(1 : ℤ)⟧),
      Triangle.mk ((TStructure.t.natTransTruncLEOfLE a (a + 1) (by omega)).app E) g δ ∈
        distTriang (DerivedCategory C) := by
  have hT := TStructure.t.triangleLEGE_distinguished a (a + 1) rfl
    ((TStructure.t.truncLE (a + 1)).obj E)
  have hX := TStructure.t.isIso_truncLE_map_truncLEι_app a (a + 1) (by omega) E
  let eX : (TStructure.t.truncLE a).obj ((TStructure.t.truncLE (a + 1)).obj E) ≅
      (TStructure.t.truncLE a).obj E :=
    asIso ((TStructure.t.truncLE a).map ((TStructure.t.truncLEι (a + 1)).app E))
  let Z := (TStructure.t.truncGE (a + 1)).obj ((TStructure.t.truncLE (a + 1)).obj E)
  have h₁ : TStructure.t.IsGE Z (a + 1) :=
    TStructure.t.isGE_truncGE_obj _ (a + 1) (a + 1)
  have hπ := isIso_homologyMap_truncGEπ_app (C := C) (a + 1) (a + 1) le_rfl
    ((TStructure.t.truncLE (a + 1)).obj E)
  have : IsIso ((homologyFunctor C (a + 1)).map
      ((TStructure.t.truncLEι (a + 1)).app E)) := by
    change IsIso ((homologyFunctor C (a + 1)).map
      ((TStructure.t.truncLTι ((a + 1) + 1)).app E))
    exact isIso_homologyMap_truncLTι_app (C := C) ((a + 1) + 1) (a + 1)
      (by omega) E
  let eH : (homologyFunctor C (a + 1)).obj Z ≅ (homologyFunctor C (a + 1)).obj E :=
    (asIso ((homologyFunctor C (a + 1)).map
      ((TStructure.t.truncGEπ (a + 1)).app ((TStructure.t.truncLE (a + 1)).obj E)))).symm ≪≫
      asIso ((homologyFunctor C (a + 1)).map ((TStructure.t.truncLEι (a + 1)).app E))
  obtain ⟨eZ⟩ := nonempty_iso_singleFunctor_obj_of_iso_homology Z (a + 1) _ eH
  let : TStructure.t.IsLE ((TStructure.t.truncLE a).obj E) (a + 1) :=
    TStructure.t.isLE_of_le _ a (a + 1) (by omega)
  have hw : eX.inv ≫
      (TStructure.t.truncLEι a).app ((TStructure.t.truncLE (a + 1)).obj E) =
      (TStructure.t.natTransTruncLEOfLE a (a + 1) (by omega)).app E := by
    apply TStructure.t.to_truncLE_obj_ext
    rw [Category.assoc, TStructure.t.natTransTruncLEOfLE_ι_app]
    change inv ((TStructure.t.truncLE a).map ((TStructure.t.truncLEι (a + 1)).app E)) ≫
      ((TStructure.t.truncLEι a).app ((TStructure.t.truncLE (a + 1)).obj E) ≫
        (𝟭 (DerivedCategory C)).map ((TStructure.t.truncLEι (a + 1)).app E)) = _
    rw [← (TStructure.t.truncLEι a).naturality, IsIso.inv_hom_id_assoc]
    rfl
  refine ⟨(TStructure.t.truncGEπ (a + 1)).app ((TStructure.t.truncLE (a + 1)).obj E) ≫
      eZ.hom,
    eZ.inv ≫ (TStructure.t.truncGEδLE a (a + 1) rfl).app
      ((TStructure.t.truncLE (a + 1)).obj E) ≫
        (shiftFunctor _ (1 : ℤ)).map eX.hom, ?_⟩
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk
      ((TStructure.t.triangleLEGE a (a + 1) rfl).obj
        ((TStructure.t.truncLE (a + 1)).obj E))
      (Triangle.mk ((TStructure.t.natTransTruncLEOfLE a (a + 1) (by omega)).app E)
        ((TStructure.t.truncGEπ (a + 1)).app ((TStructure.t.truncLE (a + 1)).obj E) ≫ eZ.hom)
        (eZ.inv ≫ (TStructure.t.truncGEδLE a (a + 1) rfl).app
          ((TStructure.t.truncLE (a + 1)).obj E) ≫
            (shiftFunctor _ (1 : ℤ)).map eX.hom))
      eX (Iso.refl _) eZ ?_ ?_ ?_).symm
  · change (TStructure.t.truncLEι a).app ((TStructure.t.truncLE (a + 1)).obj E) ≫
      𝟙 _ = eX.hom ≫
        (TStructure.t.natTransTruncLEOfLE a (a + 1) (by omega)).app E
    rw [Category.comp_id, ← hw, eX.hom_inv_id_assoc]
  · exact (Category.id_comp _).symm
  · exact (eZ.hom_inv_id_assoc _).symm

/-- The t-structure form of the third triangle of Stacks 08J5.  Two successive truncations from below of an
object of the derived category differ by its cohomology in the lower degree, placed in that
degree: there is a distinguished triangle
`H^a(E)[-a] ⟶ τ^{≥a} E ⟶ τ^{≥a+1} E ⟶ (H^a(E)[-a])[1]` whose second map is the canonical
comparison of truncations. -/
public theorem exists_truncGESucc_triangle (E : DerivedCategory C) (a : ℤ) :
    ∃ (f : (singleFunctor C a).obj ((homologyFunctor C a).obj E) ⟶
        (TStructure.t.truncGE a).obj E)
      (δ : (TStructure.t.truncGE (a + 1)).obj E ⟶
        ((singleFunctor C a).obj ((homologyFunctor C a).obj E))⟦(1 : ℤ)⟧),
      Triangle.mk f ((TStructure.t.natTransTruncGEOfLE a (a + 1) (by omega)).app E) δ ∈
        distTriang (DerivedCategory C) := by
  have hT := TStructure.t.triangleLTGE_distinguished (a + 1)
    ((TStructure.t (C := C)).truncGE a |>.obj E)
  have h₁ : TStructure.t.IsGE
      ((TStructure.t.truncLT (a + 1)).obj ((TStructure.t.truncGE a).obj E)) a :=
    TStructure.t.isGE_of_iso ((TStructure.t.truncGELTIsoLTGE a (a + 1)).app E) a
  have h₂ : TStructure.t.IsLE
      ((TStructure.t.truncLT (a + 1)).obj ((TStructure.t.truncGE a).obj E)) a :=
    TStructure.t.isLE_truncLT_obj ((TStructure.t.truncGE a).obj E) (a + 1) a (by omega)
  have hι := isIso_homologyMap_truncLTι_app (C := C) (a + 1) a (by omega)
    ((TStructure.t.truncGE a).obj E)
  have hπ := isIso_homologyMap_truncGEπ_app (C := C) a a le_rfl E
  let eH : (homologyFunctor C a).obj
      ((TStructure.t.truncLT (a + 1)).obj ((TStructure.t.truncGE a).obj E)) ≅
        (homologyFunctor C a).obj E :=
    asIso ((homologyFunctor C a).map
        ((TStructure.t.truncLTι (a + 1)).app ((TStructure.t.truncGE a).obj E))) ≪≫
      (asIso ((homologyFunctor C a).map ((TStructure.t.truncGEπ a).app E))).symm
  obtain ⟨eX⟩ := nonempty_iso_singleFunctor_obj_of_iso_homology _ a _ eH
  have hZ := TStructure.t.isIso_truncGE_map_truncGEπ_app (a + 1) a (by omega) E
  let eZ : (TStructure.t.truncGE (a + 1)).obj ((TStructure.t.truncGE a).obj E) ≅
      (TStructure.t.truncGE (a + 1)).obj E :=
    (asIso ((TStructure.t.truncGE (a + 1)).map ((TStructure.t.truncGEπ a).app E))).symm
  have hw : (TStructure.t.truncGEπ (a + 1)).app ((TStructure.t.truncGE a).obj E) ≫ eZ.hom =
      (TStructure.t.natTransTruncGEOfLE a (a + 1) (by omega)).app E := by
    have hge : TStructure.t.IsGE ((TStructure.t.truncGE (a + 1)).obj E) a :=
      TStructure.t.isGE_of_ge _ a (a + 1) (by omega)
    apply TStructure.t.from_truncGE_obj_ext
    change (TStructure.t.truncGEπ a).app E ≫
      (TStructure.t.truncGEπ (a + 1)).app ((TStructure.t.truncGE a).obj E) ≫
        inv ((TStructure.t.truncGE (a + 1)).map ((TStructure.t.truncGEπ a).app E)) = _
    rw [← Category.assoc, ← TStructure.t.truncGEπ_naturality, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id, TStructure.t.π_natTransTruncGEOfLE_app]
    rfl
  refine ⟨eX.inv ≫ (TStructure.t.truncLTι (a + 1)).app ((TStructure.t.truncGE a).obj E),
    eZ.inv ≫ (TStructure.t.truncGEδLT (a + 1)).app ((TStructure.t.truncGE a).obj E) ≫
      (shiftFunctor _ (1 : ℤ)).map eX.hom, ?_⟩
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk ((TStructure.t.triangleLTGE (a + 1)).obj ((TStructure.t.truncGE a).obj E))
      (Triangle.mk (eX.inv ≫ (TStructure.t.truncLTι (a + 1)).app ((TStructure.t.truncGE a).obj E))
        ((TStructure.t.natTransTruncGEOfLE a (a + 1) (by omega)).app E)
        (eZ.inv ≫ (TStructure.t.truncGEδLT (a + 1)).app ((TStructure.t.truncGE a).obj E) ≫
          (shiftFunctor _ (1 : ℤ)).map eX.hom))
      eX (Iso.refl _) eZ ?_ ?_ ?_).symm
  · exact (Category.comp_id _).trans (eX.hom_inv_id_assoc _).symm
  · exact hw.trans (Category.id_comp _).symm
  · exact (eZ.hom_inv_id_assoc _).symm

end DerivedCategory

end
