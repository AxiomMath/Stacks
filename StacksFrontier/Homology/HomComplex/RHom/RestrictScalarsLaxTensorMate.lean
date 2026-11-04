module

public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsModelIsoRestrictedEvaluation

/-!
# The lax--strong mate square for extension and restriction of scalars

`CochainComplex.ExtendScalars.restrictScalarsLaxTensor` is the lax monoidal structure map

`ρ : X|_R ⊗_R Y|_R ⟶ (X ⊗_S Y)|_R`

of restriction of scalars on cochain complexes, built in
`StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsModelIsoRestrictedEvaluation` as the transpose
of the inverse of the **strong** monoidality isomorphism
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` of extension of scalars. This file proves
the **mate square** relating the two structures -- equivalently, that the unit of the
extension--restriction adjunction is a monoidal natural transformation:

`(η_K ⊗_R η_L) ≫ ρ_{S ⊗ K, S ⊗ L} ≫ (m_{K,L})|_R = η_{K ⊗ L}`,

where `m_{K,L} : (S ⊗_R K) ⊗_S (S ⊗_R L) ≅ S ⊗_R (K ⊗_R L)` is the strong monoidality
isomorphism. Since `m_{K,L}` is invertible this is the same as

`(η_K ⊗_R η_L) ≫ ρ_{S ⊗ K, S ⊗ L} = η_{K ⊗ L} ≫ (m_{K,L}⁻¹)|_R`,

and there is a one-sided variant whose first factor is `η_K ⊗_R 𝟙_L`.

## Main results

* `CategoryTheory.Adjunction.unit_tensorHom_comp_homEquiv` -- **the abstract mate square.**  Over
  variable monoidal categories: whiskering the unit into both variables and following with the
  transpose of `m⁻¹ ≫ (ε ⊗ ε) ≫ m` recovers the unit at the tensor product.  The two components
  of the monoidality comparison and their naturality square are hypotheses.
* `CochainComplex.ExtendScalars.unit_tensorHom_comp_restrictScalarsLaxTensor` -- **the mate
  square for cochain complexes**, the instance of the above at
  `CochainComplex.ExtendScalars.extendScalarsMonoidalIso`.
* `CochainComplex.ExtendScalars.unit_tensorHom_comp_restrictScalarsLaxTensor_eq` -- the same
  identity with the strong comparison moved to the other side.
* `CochainComplex.ExtendScalars.unit_tensorHom_id_comp_restrictScalarsLaxTensor` -- the one-sided
  form, whose leading factor is the unit in the first variable alone.

## Implementation notes

No coherence law of either structure is used. Transposing the left-hand side across the
adjunction turns it into the transpose of

`L (η_K ⊗ η_L) ≫ m_{L U L K, L U L L}⁻¹ ≫ (ε ⊗ ε) ≫ m_{K,L}`,

and there the two-variable inverse naturality square
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso_inv_naturality` moves the extended units
past the inverse comparison, the left triangle identity of the adjunction cancels them against
the two counits, and the comparison cancels against its own inverse.

As in `StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsModelIsoRestrictedEvaluation`, the
abstract content is stated over variable monoidal categories with the two components of the
monoidality comparison and their naturality square taken as **data**, since
`extendScalarsMonoidalIso` carries no `CategoryTheory.Functor.Monoidal` instance.

No tag is registered here. Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` are still open: the mate square
is a structural compatibility used by the identification `μ' = μ` of its `hmu`, and says nothing
about its comparison identity `h`, whose frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`. The coherence laws of `ρ` are unproved;
the mate square does not need them.

## References

* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars

universe u

namespace CategoryTheory.Adjunction

/-- **The mate square of a strong monoidal left adjoint and its lax monoidal right adjoint.**

Let `L ⊣ U` be an adjunction between monoidal categories and let `mKM`, `mU` be the components at
`(K, M)` and at `(U (L K), U (L M))` of a monoidality comparison for `L` -- that is, isomorphisms
`L X ⊗ L Y ≅ L (X ⊗ Y)` -- whose inverse naturality square along the two units is `hm`.  Then
whiskering the units into both variables and following with the transpose of

`mU⁻¹ ≫ (ε ⊗ ε) ≫ mKM`

recovers the unit at `K ⊗ M`.  Equivalently: the unit is a monoidal natural transformation from
the identity to `L ⋙ U` with its induced lax structure, which is the compatibility between the
**lax** structure of `U` and the **strong** structure of `L`. -/
theorem unit_tensorHom_comp_homEquiv {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] {L : C ⥤ D} {U : D ⥤ C} (adj : L ⊣ U)
    {K M : C}
    (mKM : L.obj K ⊗ L.obj M ≅ L.obj (K ⊗ M))
    (mU : L.obj (U.obj (L.obj K)) ⊗ L.obj (U.obj (L.obj M)) ≅
      L.obj (U.obj (L.obj K) ⊗ U.obj (L.obj M)))
    (hm : L.map (adj.unit.app K ⊗ₘ adj.unit.app M) ≫ mU.inv =
      mKM.inv ≫ (L.map (adj.unit.app K) ⊗ₘ L.map (adj.unit.app M))) :
    (adj.unit.app K ⊗ₘ adj.unit.app M) ≫
        adj.homEquiv (U.obj (L.obj K) ⊗ U.obj (L.obj M)) (L.obj (K ⊗ M))
          (mU.inv ≫ (adj.counit.app (L.obj K) ⊗ₘ adj.counit.app (L.obj M)) ≫ mKM.hom) =
      adj.unit.app (K ⊗ M) := by
  have htri : (L.map (adj.unit.app K) ⊗ₘ L.map (adj.unit.app M)) ≫
      (adj.counit.app (L.obj K) ⊗ₘ adj.counit.app (L.obj M)) = 𝟙 (L.obj K ⊗ L.obj M) := by
    rw [tensorHom_comp_tensorHom, adj.left_triangle_components K,
      adj.left_triangle_components M]
    simp
  have hkey : L.map (adj.unit.app K ⊗ₘ adj.unit.app M) ≫
      mU.inv ≫ (adj.counit.app (L.obj K) ⊗ₘ adj.counit.app (L.obj M)) ≫ mKM.hom =
      𝟙 (L.obj (K ⊗ M)) := by
    rw [← Category.assoc, hm, Category.assoc, reassoc_of% htri, mKM.inv_hom_id]
  exact ((adj.homEquiv_naturality_left _ _).symm.trans
    (congrArg (adj.homEquiv (K ⊗ M) (L.obj (K ⊗ M))) hkey)).trans (adj.homEquiv_id (K ⊗ M))

end CategoryTheory.Adjunction

namespace CategoryTheory

/-- **An isomorphism in the source of a functor, cancelled off a composite in its image.**  If
`a` followed by the image of `e.hom` is `b`, then `a` is `b` followed by the image of `e.inv`. -/
theorem eq_comp_map_inv_of_comp_map_hom_eq {C D : Type*} [Category* C] [Category* D]
    (U : D ⥤ C) {W : C} {X Y : D} (e : X ≅ Y) (a : W ⟶ U.obj X) (b : W ⟶ U.obj Y)
    (h : a ≫ U.map e.hom = b) : a = b ≫ U.map e.inv := by
  rw [← h, Category.assoc, ← U.map_comp, e.hom_inv_id, U.map_id, Category.comp_id]

end CategoryTheory

namespace CategoryTheory.MonoidalCategory

/-- **A tensor of two morphisms split into one variable at a time.**  Tensoring with the identity
on the right and then with the identity on the left is the tensor of the two morphisms. -/
theorem tensorHom_id_comp_id_tensorHom {C : Type*} [Category* C] [MonoidalCategory C]
    {K K' M M' : C} (a : K ⟶ K') (b : M ⟶ M') :
    (a ⊗ₘ 𝟙 M) ≫ (𝟙 K' ⊗ₘ b) = a ⊗ₘ b := by
  rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

end CategoryTheory.MonoidalCategory

namespace CochainComplex.ExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

local instance extendScalarsAdditiveLaxTensorMate :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- **The mate square for extension and restriction of scalars on cochain complexes.**

Whiskering the unit of degreewise extension--restriction into both variables, following with the
lax monoidal structure map `CochainComplex.ExtendScalars.restrictScalarsLaxTensor` of restriction
of scalars at the pair of extensions, and then with the restriction of the strong monoidality
isomorphism `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` at `(K, M)`, recovers the unit
at `K ⊗ M`.

The adjunction is spelled as
`(ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex (ComplexShape.up ℤ)` rather than as
`CochainComplex.ExtendScalars.extendRestrictScalarsComplexAdj`, matching
`Stacks.DerivedHom.BaseChangeIso.homEquiv_monoidalIso_inv_uncurry_counit`, because keyed matching
does not unfold the abbreviation. -/
public theorem unit_tensorHom_comp_restrictScalarsLaxTensor
    (K M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app K ⊗ₘ
          ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app M) ≫
        restrictScalarsLaxTensor f ((mapCochainComplex f).obj K) ((mapCochainComplex f).obj M) ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
            (extendScalarsMonoidalIso f K M).hom =
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app (K ⊗ M) := by
  set adj := extendRestrictScalarsComplexAdj f
  have h1 := restrictScalarsLaxTensor_comp_map f ((mapCochainComplex f).obj K)
    ((mapCochainComplex f).obj M) (extendScalarsMonoidalIso f K M).hom
  have h2 := Adjunction.unit_tensorHom_comp_homEquiv adj (extendScalarsMonoidalIso f K M)
    (extendScalarsMonoidalIso f
      ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj ((mapCochainComplex f).obj K))
      ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj ((mapCochainComplex f).obj M)))
    (extendScalarsMonoidalIso_inv_naturality f (adj.unit.app K) (adj.unit.app M))
  exact (congrArg (fun w => (adj.unit.app K ⊗ₘ adj.unit.app M) ≫ w) h1).trans h2

/-- **The lax structure map pushed across the strong monoidality comparison.**
`CochainComplex.ExtendScalars.unit_tensorHom_comp_restrictScalarsLaxTensor` with the restricted
comparison moved to the other side. -/
public theorem unit_tensorHom_comp_restrictScalarsLaxTensor_eq
    (K M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app K ⊗ₘ
          ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app M) ≫
        restrictScalarsLaxTensor f ((mapCochainComplex f).obj K) ((mapCochainComplex f).obj M) =
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app (K ⊗ M) ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
          (extendScalarsMonoidalIso f K M).inv :=
  CategoryTheory.eq_comp_map_inv_of_comp_map_hom_eq (CochainComplex.restrictScalarsLarge f)
    (extendScalarsMonoidalIso f K M) _ _
    ((Category.assoc _ _ _).trans (unit_tensorHom_comp_restrictScalarsLaxTensor f K M))

/-- **The mate square with the unit whiskered into one variable at a time.**
`CochainComplex.ExtendScalars.unit_tensorHom_comp_restrictScalarsLaxTensor` with the leading
factor `η_K ⊗ η_M` split as `(η_K ⊗ 𝟙) ≫ (𝟙 ⊗ η_M)`. -/
public theorem unit_tensorHom_id_comp_restrictScalarsLaxTensor
    (K M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app K ⊗ₘ 𝟙 M) ≫
        (𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj
              ((mapCochainComplex f).obj K)) ⊗ₘ
            ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app M) ≫
          restrictScalarsLaxTensor f ((mapCochainComplex f).obj K)
              ((mapCochainComplex f).obj M) ≫
            (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
              (extendScalarsMonoidalIso f K M).hom =
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app (K ⊗ M) :=
  ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ restrictScalarsLaxTensor f ((mapCochainComplex f).obj K)
          ((mapCochainComplex f).obj M) ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
          (extendScalarsMonoidalIso f K M).hom)
      (MonoidalCategory.tensorHom_id_comp_id_tensorHom _ _))).trans
    (unit_tensorHom_comp_restrictScalarsLaxTensor f K M)

end CochainComplex.ExtendScalars

end
