module

public import StacksFrontier.CategoryTheory.Triangulated.Generators
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimitFactorization
import StacksCore.Tactic.StacksAttribute

/-!
# Factoring a map out of a compact object through a compact generator of a subcategory

Let `Φ : D' ⥤ D` be an exact, direct-sum-preserving functor of triangulated categories with
direct sums, let `G` be a compact weak generator of `D'` and let `A` be a compact object of `D`.
Then every morphism `A ⟶ Φ K` into the image of an object of `D'` factors through an object of
the triangulated envelope of a finite direct sum of copies of `Φ G`; in particular through an
object satisfying any strictly full, saturated, triangulated property of objects of `D` that
`Φ G` satisfies.

## Main results

* `CategoryTheory.Pretriangulated.exists_fac_of_isWeakTriangulatedGenerator`: the factorization.
* `CategoryTheory.Pretriangulated.prop_shiftClosure_map_ofObj` and
  `CategoryTheory.Pretriangulated.prop_iSup_colimitsOfShape_map`: a shift-commuting,
  direct-sum-preserving functor carries shifts and direct sums of a family of objects to shifts and
  direct sums of the image family.

## Implementation notes

The generating family is indexed by `PUnit.{v + 1}`, a type of the morphism universe `v` of `D`
and `D'`, rather than by `Unit`: [Stacks, Tag 09SN] indexes its family by a type of that
universe, and the index type of `CategoryTheory.ObjectProperty.singleton` is `Unit : Type 0`.
The two properties of objects agree, which is `ofObj_punit_eq_singleton`.

## References

* [Stacks Project, Tag 09SN](https://stacks.math.columbia.edu/tag/09SN)
* [Stacks Project, Tag 094A](https://stacks.math.columbia.edu/tag/094A)
* [Stacks Project, Tag 09SP](https://stacks.math.columbia.edu/tag/09SP)
* [Stacks Project, Tag 0A9C](https://stacks.math.columbia.edu/tag/0A9C)
-/

@[expose] public section

universe v u u'

namespace CategoryTheory.Pretriangulated

open Limits ObjectProperty

section Transport

variable {D : Type u} [Category.{v} D] {D' : Type u'} [Category.{v} D']

/-- The one-element family indexed by a type of the morphism universe spans the same property of
objects as `CategoryTheory.ObjectProperty.singleton`, whose index type is `Unit`. -/
theorem ofObj_punit_eq_singleton (G : D') :
    ObjectProperty.ofObj (fun _ : PUnit.{v + 1} ↦ G) = ObjectProperty.singleton G := by
  ext Y
  simp [ObjectProperty.ofObj_iff]

variable [HasShift D ℤ] [HasShift D' ℤ]

/-- A functor commuting with the shift carries the shift-closure of a family of objects into the
shift-closure of the image family. -/
theorem prop_shiftClosure_map_ofObj (Φ : D' ⥤ D) [Φ.CommShift ℤ] {ι : Type*} (E : ι → D')
    {Z : D'} (hZ : ((ObjectProperty.ofObj E).shiftClosure ℤ) Z) :
    ((ObjectProperty.ofObj fun i ↦ Φ.obj (E i)).shiftClosure ℤ) (Φ.obj Z) := by
  obtain ⟨Y, a, e, hY⟩ := hZ
  obtain ⟨i, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hY
  exact ⟨Φ.obj (E i), a, Φ.mapIso e ≪≫ (Φ.commShiftIso a).app (E i),
    ObjectProperty.ofObj_apply _ i⟩

omit [HasShift D ℤ] [HasShift D' ℤ] in
/-- A functor preserving direct sums of every shape of the morphism universe carries an object
that is such a direct sum of objects satisfying `P` to one that is such a direct sum of objects
satisfying `Q`, whenever `Φ` carries `P` into `Q`. -/
theorem prop_iSup_colimitsOfShape_map (Φ : D' ⥤ D)
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) Φ]
    {P : ObjectProperty D'} {Q : ObjectProperty D} (hPQ : ∀ Y : D', P Y → Q (Φ.obj Y)) {Z : D'}
    (hZ : (⨆ J : Type v, P.colimitsOfShape (Discrete J)) Z) :
    (⨆ J : Type v, Q.colimitsOfShape (Discrete J)) (Φ.obj Z) := by
  rw [ObjectProperty.prop_iSup_iff] at hZ ⊢
  obtain ⟨J, ⟨h⟩⟩ := hZ
  exact ⟨J, ⟨{ toColimitPresentation := h.toColimitPresentation.map Φ
               prop_diag_obj j := hPQ _ (h.prop_diag_obj j) }⟩⟩

end Transport

section Main

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{v} D]
  {D' : Type u'} [Category.{v} D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D'] [HasCoproducts.{v} D']

/-- **A map from a compact object into an object of a compactly generated subcategory factors
through a compact object of that subcategory.** Let `Φ : D' ⥤ D` be an exact functor of
triangulated categories with direct sums which preserves the direct sums, let `G` be an object
of `D'` which is compact there, whose image is compact in `D`, and which weakly generates `D'`,
and let `A` be a compact object of `D`. Let `P` be a strictly full, saturated, triangulated
property of objects of `D` satisfied by `Φ G`. Then every morphism `A ⟶ Φ K` factors through an
object satisfying `P`. -/
theorem exists_fac_of_isWeakTriangulatedGenerator (Φ : D' ⥤ D) [Φ.Additive] [Φ.CommShift ℤ]
    [Φ.IsTriangulated] [∀ J : Type v, PreservesColimitsOfShape (Discrete J) Φ] (G : D')
    (hGc : IsCompactObject.{v} G) (hGc' : IsCompactObject.{v} (Φ.obj G))
    (hG : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator) {A : D}
    (hAc : IsCompactObject.{v} A) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    [P.IsStableUnderRetracts] [P.IsTriangulated] (hPG : P (Φ.obj G)) (K : D')
    (ζ : A ⟶ Φ.obj K) :
    ∃ (Q : D) (a : A ⟶ Q) (b : Q ⟶ Φ.obj K), P Q ∧ a ≫ b = ζ := by
  classical
  have := hGc
  have := hGc'
  have := hAc
  have hnat : PreservesColimitsOfShape (Discrete ℕ) Φ :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence (Equiv.ulift.{v})) Φ
  have hgen : ∀ Y : D',
      ((ObjectProperty.ofObj fun _ : PUnit.{v + 1} ↦ G).shiftClosure ℤ).rightOrthogonal Y →
        IsZero Y := by
    rw [ofObj_punit_eq_singleton]
    exact hG
  obtain ⟨F, hF, h0, hcell⟩ :=
    exists_isHomotopyColimit_of_compactlyGenerated (fun _ : PUnit.{v + 1} ↦ G) hgen K
  obtain ⟨n, ρ, σ, hρσ⟩ := exists_fac_obj_of_isHomotopyColimit (hF.map Φ) A ζ
  have htr : ∀ Z : D', ((ObjectProperty.ofObj fun _ : PUnit.{v + 1} ↦ G).shiftClosure ℤ) Z →
      ((ObjectProperty.ofObj fun _ : PUnit.{v + 1} ↦ Φ.obj G).shiftClosure ℤ) (Φ.obj Z) :=
    fun _ ↦ prop_shiftClosure_map_ofObj Φ _
  have hX : ∀ m : ℕ, ∃ Y : D,
      (⨆ J : Type v, ((ObjectProperty.ofObj fun _ : PUnit.{v + 1} ↦ Φ.obj G).shiftClosure
        ℤ).colimitsOfShape (Discrete J)) Y ∧
      ∃ (f : Y ⟶ Φ.obj (F.obj m)) (g : Φ.obj (F.obj m) ⟶ Φ.obj (F.obj (m + 1)))
        (h : Φ.obj (F.obj (m + 1)) ⟶ Y⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang D := by
    intro m
    obtain ⟨Y, hY, f, g, hT⟩ := hcell m
    exact ⟨Φ.obj Y, prop_iSup_colimitsOfShape_map Φ htr hY, Φ.map f,
      Φ.map (F.map (homOfLE (Nat.le_succ m))),
      Φ.map g ≫ (Φ.commShiftIso (1 : ℤ)).hom.app Y, Φ.map_distinguished _ hT⟩
  obtain ⟨s, Z, hZ, a, b, hab⟩ :=
    exists_fac_triangEnvelope_of_isCompactObject (fun _ : PUnit.{v + 1} ↦ Φ.obj G)
      (X := fun m ↦ Φ.obj (F.obj m)) (prop_iSup_colimitsOfShape_map Φ htr h0) hX ρ
  have hfin : P.IsClosedUnderFiniteCoproducts :=
    ⟨fun _ _ ↦ P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _⟩
  have hPZ : P Z := by
    refine (ObjectProperty.triangEnvelope_le_iff _).2 ?_ Z hZ
    rw [ObjectProperty.singleton_le_iff]
    exact P.prop_coproduct fun _ ↦ hPG
  exact ⟨Z, a, b ≫ σ, hPZ, by rw [← Category.assoc, hab, hρσ]⟩

end Main

end CategoryTheory.Pretriangulated

end
