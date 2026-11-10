module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GlobalSectionsCompletionWhole

/-!
# A triangulated functor carries a reflection to a reflection, given the display at every object

Let `𝒯` and `𝒯'` be pretriangulated categories, let `P ⊂ 𝒯` and `P' ⊂ 𝒯'` be shift-stable classes
of objects admitting reflectors `L` and `L'`, and let `F : 𝒯 ⥤ 𝒯'` be a triangulated functor.
Suppose that for *every* object `E` of `𝒯` the two objects `F(L E)` and `L'(F E)` are isomorphic —
an isomorphism of objects, not asked to be canonical or natural. Then `F(L K)`, together with
`F(η_K)`, **is** a reflection of `F K`:

`Hom(F (L K), N) ⟶ Hom(F K, N)`, `g ↦ F(η_K) ≫ g`, is bijective for every `N` in `P'`,

and consequently there is an isomorphism `L'(F K) ≅ F(L K)` *compatible with the two units*.

## Main results

* `CategoryTheory.ObjectProperty.isoOfUniversal` — object-level uniqueness of a reflection: an
  object of `P` receiving a map from `X` with the reflection property is the reflection of `X`,
  compatibly with the unit. This is the object-level companion of
  `CategoryTheory.ObjectProperty.isoOfReflection`, which compares two reflectors as functors.
* `CategoryTheory.ObjectProperty.isoReflectionShift` and
  `CategoryTheory.ObjectProperty.unit_comp_isoReflectionShift_hom` — a reflection onto a
  shift-stable class commutes with the shift, compatibly with the unit.
* `CategoryTheory.ObjectProperty.leftOrthogonal_iff_isZero_reflection` — an object admits no
  nonzero map into `P` exactly when its reflection vanishes.
* `CategoryTheory.ObjectProperty.leftOrthogonal_cone_unit` — the cone of a unit admits no nonzero
  map into `P`.
* `CategoryTheory.ObjectProperty.bijective_precomp_map_unit_of_nonempty_iso` — if
  `F(L E) ≅ L'(F E)` for every object `E`, then `F(η_K)` is a reflection.
* `CategoryTheory.ObjectProperty.isoReflectionMap_of_nonempty_iso` and
  `CategoryTheory.ObjectProperty.unit_comp_isoReflectionMap_hom` — the resulting isomorphism
  `L'(F K) ≅ F(L K)` and its compatibility with the units.

## Implementation notes

The membership of `F(L K)` in `P'` is not assumed: it follows from the isomorphism
`F(L K) ≅ L'(F K)`, since `L'(F K)` lies in `P'`. The comparison isomorphism is produced by the
object-level uniqueness of a reflection, `CategoryTheory.ObjectProperty.isoOfUniversal`, rather
than as a natural transformation, so its compatibility with the units is part of its construction.

## References

* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
* [Stacks Project, Tag 0FXB](https://stacks.math.columbia.edu/tag/0FXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.ObjectProperty

universe v u v' u'

/-! ### Object-level uniqueness of a reflection -/

section Uniqueness

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  {L : C ⥤ P.FullSubcategory} (adj : L ⊣ P.ι)

/-- The map out of the reflection of `X` whose restriction along the unit is a given
`u : X ⟶ Z` with `Z` in `P`. -/
def universalHom {X Z : C} (hZ : P Z) (u : X ⟶ Z) : (L ⋙ P.ι).obj X ⟶ Z :=
  ((bijective_precomp_adjunction_unit P adj X Z hZ).surjective u).choose

/-- The map `CategoryTheory.ObjectProperty.universalHom P adj hZ u` restricts along the unit to
`u`. -/
theorem unit_comp_universalHom {X Z : C} (hZ : P Z) (u : X ⟶ Z) :
    adj.unit.app X ≫ universalHom P adj hZ u = u :=
  ((bijective_precomp_adjunction_unit P adj X Z hZ).surjective u).choose_spec

/-- The map into the reflection of `X` whose restriction along `u` is the unit, available when
precomposition with `u` has the reflection property. -/
def universalInv {X Z : C} (u : X ⟶ Z)
    (hu : ∀ N : C, P N → Function.Bijective (fun g : Z ⟶ N ↦ u ≫ g)) :
    Z ⟶ (L ⋙ P.ι).obj X :=
  ((hu ((L ⋙ P.ι).obj X) (L.obj X).property).surjective (adj.unit.app X)).choose

/-- Precomposing `CategoryTheory.ObjectProperty.universalInv P adj u hu` with `u` gives the unit.
-/
theorem comp_universalInv {X Z : C} (u : X ⟶ Z)
    (hu : ∀ N : C, P N → Function.Bijective (fun g : Z ⟶ N ↦ u ≫ g)) :
    u ≫ universalInv P adj u hu = adj.unit.app X :=
  ((hu ((L ⋙ P.ι).obj X) (L.obj X).property).surjective (adj.unit.app X)).choose_spec

/-- **An object of `P` receiving a map with the reflection property is the reflection.** Given
`u : X ⟶ Z` with `Z` in `P` such that precomposition with `u` is a bijection onto the maps from
`X` into any object of `P`, the reflection of `X` is isomorphic to `Z`. -/
def isoOfUniversal {X Z : C} (hZ : P Z) (u : X ⟶ Z)
    (hu : ∀ N : C, P N → Function.Bijective (fun g : Z ⟶ N ↦ u ≫ g)) :
    (L ⋙ P.ι).obj X ≅ Z where
  hom := universalHom P adj hZ u
  inv := universalInv P adj u hu
  hom_inv_id := by
    refine (bijective_precomp_adjunction_unit P adj X _ (L.obj X).property).injective ?_
    change adj.unit.app X ≫ universalHom P adj hZ u ≫ universalInv P adj u hu =
      adj.unit.app X ≫ 𝟙 _
    rw [← Category.assoc, unit_comp_universalHom, comp_universalInv, Category.comp_id]
    exact rfl
  inv_hom_id := by
    refine (hu Z hZ).injective ?_
    show u ≫ universalInv P adj u hu ≫ universalHom P adj hZ u = u ≫ 𝟙 _
    rw [← Category.assoc, comp_universalInv, unit_comp_universalHom, Category.comp_id]

/-- The isomorphism of `CategoryTheory.ObjectProperty.isoOfUniversal` carries the unit to the
given map. -/
theorem unit_comp_isoOfUniversal_hom {X Z : C} (hZ : P Z) (u : X ⟶ Z)
    (hu : ∀ N : C, P N → Function.Bijective (fun g : Z ⟶ N ↦ u ≫ g)) :
    adj.unit.app X ≫ (isoOfUniversal P adj hZ u hu).hom = u :=
  unit_comp_universalHom P adj hZ u

end Uniqueness

/-! ### A reflection onto a shift-stable class commutes with the shift -/

section Shift

variable {C : Type u} [Category.{v} C] [HasShift C ℤ] (P : ObjectProperty C)
  [P.IsStableUnderShift ℤ] {L : C ⥤ P.FullSubcategory} (adj : L ⊣ P.ι)

include adj in
/-- **The shifted unit has the reflection property.** The shift is an equivalence, so
precomposition with `(η_X)⟦q⟧` is conjugate, by the two hom-set bijections of the shift
adjunction, to precomposition with `η_X` against the target `N⟦-q⟧`, which lies in `P` by shift
stability. -/
theorem bijective_precomp_shift_unit (X : C) (q : ℤ) {N : C} (hN : P N) :
    Function.Bijective
      (fun g : ((L ⋙ P.ι).obj X)⟦q⟧ ⟶ N ↦ (adj.unit.app X)⟦q⟧' ≫ g) := by
  have sadj : shiftFunctor C q ⊣ shiftFunctor C (-q) := (shiftEquiv C q).toAdjunction
  have hrw : (fun g : ((L ⋙ P.ι).obj X)⟦q⟧ ⟶ N ↦ (adj.unit.app X)⟦q⟧' ≫ g) =
      (sadj.homEquiv X N).symm ∘
        (fun k : (L ⋙ P.ι).obj X ⟶ N⟦(-q : ℤ)⟧ ↦ adj.unit.app X ≫ k) ∘
        (sadj.homEquiv ((L ⋙ P.ι).obj X) N) := by
    funext g
    change (adj.unit.app X)⟦q⟧' ≫ g =
      (sadj.homEquiv X N).symm (adj.unit.app X ≫ sadj.homEquiv ((L ⋙ P.ι).obj X) N g)
    rw [← sadj.homEquiv_naturality_left (adj.unit.app X) g]
    exact (Equiv.symm_apply_apply _ _).symm
  rw [hrw]
  exact (sadj.homEquiv X N).symm.bijective.comp
    ((bijective_precomp_adjunction_unit P adj X _ (P.le_shift (-q) N hN)).comp
      (sadj.homEquiv ((L ⋙ P.ι).obj X) N).bijective)

include adj in
/-- **The reflection of a shift is the shift of the reflection**, compatibly with the unit. The
shifted reflection lies in `P` by shift stability and the shifted unit has the reflection
property, so `CategoryTheory.ObjectProperty.isoOfUniversal` applies. -/
def isoReflectionShift (X : C) (q : ℤ) :
    (L ⋙ P.ι).obj (X⟦q⟧) ≅ ((L ⋙ P.ι).obj X)⟦q⟧ :=
  isoOfUniversal P adj (P.le_shift q _ (L.obj X).property) ((adj.unit.app X)⟦q⟧')
    fun _ hN => bijective_precomp_shift_unit P adj X q hN

include adj in
/-- The isomorphism of `CategoryTheory.ObjectProperty.isoReflectionShift` carries the unit at
`X⟦q⟧` to the shift of the unit at `X`. -/
theorem unit_comp_isoReflectionShift_hom (X : C) (q : ℤ) :
    adj.unit.app (X⟦q⟧) ≫ (isoReflectionShift P adj X q).hom = (adj.unit.app X)⟦q⟧' :=
  unit_comp_isoOfUniversal_hom P adj _ _ _

end Shift

/-! ### Orthogonality to a reflective class -/

section Orthogonal

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) {L : C ⥤ P.FullSubcategory} (adj : L ⊣ P.ι)

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
include adj in
/-- **An object admits no nonzero map into `P` exactly when its reflection vanishes.** Every map
`X ⟶ Z` with `Z` in `P` factors through the reflection, so it vanishes when the reflection does;
and conversely the identity of the reflection, being determined by its restriction along the
unit, is zero as soon as that restriction is. -/
theorem leftOrthogonal_iff_isZero_reflection (X : C) :
    P.leftOrthogonal X ↔ IsZero ((L ⋙ P.ι).obj X) := by
  constructor
  · intro h
    rw [IsZero.iff_id_eq_zero]
    refine (bijective_precomp_adjunction_unit P adj X _ (L.obj X).property).1 ?_
    change adj.unit.app X ≫ 𝟙 _ = adj.unit.app X ≫ 0
    rw [Category.comp_id, comp_zero]
    exact h _ (L.obj X).property
  · intro h Z φ hZ
    obtain ⟨g, hg⟩ := (bijective_precomp_adjunction_unit P adj X Z hZ).2 φ
    have hg' : adj.unit.app X ≫ g = φ := hg
    rw [← hg', h.eq_of_src g 0, comp_zero]

variable [P.IsStableUnderShift ℤ]

omit [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
include adj in
/-- **Every map `X⟦1⟧ ⟶ Z` into an object of `P` factors through the shifted reflection.** The
shift is an equivalence, so such a map is a map `X ⟶ Z⟦-1⟧`; `Z⟦-1⟧` is in `P` by shift
stability, so that map factors along the unit, and the factorisation is carried back along the
shift adjunction, whose hom-set bijection is natural in the source. -/
theorem exists_comp_shift_unit {X Z : C} (hZ : P Z) (ψ : X⟦(1 : ℤ)⟧ ⟶ Z) :
    ∃ χ : ((L ⋙ P.ι).obj X)⟦(1 : ℤ)⟧ ⟶ Z, (adj.unit.app X)⟦(1 : ℤ)⟧' ≫ χ = ψ := by
  exact (bijective_precomp_shift_unit P adj X 1 hZ).2 ψ

include adj in
/-- **The cone of a unit admits no nonzero map into `P`.** A map `φ : Cn ⟶ Z` with `Z` in `P` is
killed by the second map of the triangle, because its restriction along the unit is, so it
factors through `X⟦1⟧`; that factorisation in turn factors through the shifted reflection by
`CategoryTheory.ObjectProperty.exists_comp_shift_unit`, and the composite of two consecutive maps
of a distinguished triangle vanishes. -/
theorem leftOrthogonal_cone_unit {X Cn : C} (v : (L ⋙ P.ι).obj X ⟶ Cn) (w : Cn ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (adj.unit.app X) v w ∈ distTriang C) :
    P.leftOrthogonal Cn := by
  intro Z φ hZ
  have h12 : adj.unit.app X ≫ v = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have h31 : w ≫ (adj.unit.app X)⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
  have ha : v ≫ φ = 0 := by
    refine (bijective_precomp_adjunction_unit P adj X Z hZ).1 ?_
    change adj.unit.app X ≫ v ≫ φ = adj.unit.app X ≫ 0
    rw [← Category.assoc, h12, zero_comp, comp_zero]
  obtain ⟨ψ, hψ⟩ := Triangle.yoneda_exact₃ _ hT φ ha
  have hψ' : φ = w ≫ ψ := hψ
  obtain ⟨χ, hχ⟩ := exists_comp_shift_unit (X := X) P adj hZ ψ
  rw [hψ', ← hχ, ← Category.assoc, h31, zero_comp]

end Orthogonal

/-! ### Reflections along a triangulated functor -/

section Engine

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [hCa : ∀ n : ℤ, (shiftFunctor C n).Additive] [hCt : Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [hDa : ∀ n : ℤ, (shiftFunctor D n).Additive] [hDt : Pretriangulated D]
  (P : ObjectProperty C) (P' : ObjectProperty D)
  [P.IsStableUnderShift ℤ] [P'.IsStableUnderShift ℤ]
  {L : C ⥤ P.FullSubcategory} (adj : L ⊣ P.ι)
  {L' : D ⥤ P'.FullSubcategory} (adj' : L' ⊣ P'.ι)
  (F : C ⥤ D) [hFs : F.CommShift ℤ] [hFt : F.IsTriangulated]

omit [P.IsStableUnderShift ℤ] [P'.IsStableUnderShift ℤ] in
include adj adj' in
/-- **`F` carries an object orthogonal to `P` to one orthogonal to `P'`**, as soon as the display
`F(L E) ≅ L'(F E)` holds at the level of objects. Orthogonality is vanishing of the reflection
(`CategoryTheory.ObjectProperty.leftOrthogonal_iff_isZero_reflection`), so the hypothesis says
`L E = 0`, whence `F(L E) = 0`, and the display transports that vanishing to `L'(F E)`. -/
theorem leftOrthogonal_map_of_nonempty_iso
    (habs : ∀ E : C,
      Nonempty ((L' ⋙ P'.ι).obj (F.obj E) ≅ F.obj ((L ⋙ P.ι).obj E)))
    {E : C} (hE : P.leftOrthogonal E) :
    P'.leftOrthogonal (F.obj E) := by
  rw [leftOrthogonal_iff_isZero_reflection P adj] at hE
  rw [leftOrthogonal_iff_isZero_reflection P' adj']
  obtain ⟨e⟩ := habs E
  exact (F.map_isZero hE).of_iso e

include adj adj' in
/-- **The display at the level of objects, for every object, makes `F(η_K)` a reflection.** If
`F(L E) ≅ L'(F E)` for every object `E` of `𝒯` — an isomorphism of objects, not asked to be
canonical or natural — then for every `K` and every `N` in `P'` precomposition with
`F(η_K) : F K ⟶ F(L K)` is a bijection `Hom(F(L K), N) ≃ Hom(F K, N)`.

The argument applies the display at the cone `Cn` of the unit `K ⟶ L K`: that cone is orthogonal
to `P` by `CategoryTheory.ObjectProperty.leftOrthogonal_cone_unit`, so `F Cn` is orthogonal to
`P'`, and so is `(F Cn)⟦-1⟧` because the left orthogonal of a shift-stable class is shift
stable. `F` is triangulated, hence carries the triangle `K ⟶ L K ⟶ Cn` to a distinguished one,
and a triangle whose third object is orthogonal to `N` in both shifts makes composition with
`F(η_K)` a bijection. -/
theorem bijective_precomp_map_unit_of_nonempty_iso
    (habs : ∀ E : C,
      Nonempty ((L' ⋙ P'.ι).obj (F.obj E) ≅ F.obj ((L ⋙ P.ι).obj E)))
    (K : C) {N : D} (hN : P' N) :
    Function.Bijective
      (fun g : F.obj ((L ⋙ P.ι).obj K) ⟶ N ↦ F.map (adj.unit.app K) ≫ g) := by
  obtain ⟨Cn, v, w, hT⟩ := distinguished_cocone_triangle (adj.unit.app K)
  have hFC : P'.leftOrthogonal (F.obj Cn) := leftOrthogonal_map_of_nonempty_iso P P' adj adj' F
    habs (leftOrthogonal_cone_unit P adj v w hT)
  have hFC' : P'.leftOrthogonal ((F.obj Cn)⟦(-1 : ℤ)⟧) :=
    P'.leftOrthogonal.le_shift (-1 : ℤ) _ hFC
  have hS := F.map_distinguished _ hT
  have key : ∀ φ : F.obj ((L ⋙ P.ι).obj K) ⟶ N,
      F.map (adj.unit.app K) ≫ φ = 0 → φ = 0 := by
    intro φ hφ0
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ hS φ hφ0
    rw [hg, hFC g hN]
    exact comp_zero
  refine ⟨fun φ₁ φ₂ hφ ↦ sub_eq_zero.mp (key _ ?_), fun h ↦ ?_⟩
  · rwa [Preadditive.comp_sub, sub_eq_zero]
  · obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hS) h (hFC' _ hN)
    exact ⟨g, hg.symm⟩

/-- **The resulting isomorphism `L'(F K) ≅ F(L K)`**, produced by the object-level uniqueness of
a reflection from `CategoryTheory.ObjectProperty.bijective_precomp_map_unit_of_nonempty_iso`. The
membership `P' (F(L K))` is the display at `K`, transported along `hclosed`. Unlike the
isomorphisms the display supplies, this one is compatible with the two units. -/
def isoReflectionMap_of_nonempty_iso
    (hclosed : ∀ {Y Z : D}, (Y ≅ Z) → P' Y → P' Z)
    (habs : ∀ E : C,
      Nonempty ((L' ⋙ P'.ι).obj (F.obj E) ≅ F.obj ((L ⋙ P.ι).obj E)))
    (K : C) :
    (L' ⋙ P'.ι).obj (F.obj K) ≅ F.obj ((L ⋙ P.ι).obj K) :=
  isoOfUniversal P' adj' (hclosed (habs K).some (L'.obj (F.obj K)).property)
    (F.map (adj.unit.app K))
    fun _ hN => bijective_precomp_map_unit_of_nonempty_iso P P' adj adj' F habs K hN

/-- The isomorphism of `CategoryTheory.ObjectProperty.isoReflectionMap_of_nonempty_iso` carries
the unit of `L'` at `F K` to `F` applied to the unit of `L` at `K`. -/
theorem unit_comp_isoReflectionMap_hom
    (hclosed : ∀ {Y Z : D}, (Y ≅ Z) → P' Y → P' Z)
    (habs : ∀ E : C,
      Nonempty ((L' ⋙ P'.ι).obj (F.obj E) ≅ F.obj ((L ⋙ P.ι).obj E)))
    (K : C) :
    adj'.unit.app (F.obj K) ≫
        (isoReflectionMap_of_nonempty_iso P P' adj adj' F hclosed habs K).hom =
      F.map (adj.unit.app K) :=
  unit_comp_isoOfUniversal_hom P' adj' _ _ _

end Engine

end CategoryTheory.ObjectProperty

end
