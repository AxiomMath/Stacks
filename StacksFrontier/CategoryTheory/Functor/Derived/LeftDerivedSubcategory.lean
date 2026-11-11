module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import StacksFrontier.CategoryTheory.Functor.Derived.Biprod
public import StacksFrontier.CategoryTheory.Functor.Derived.Morphisms
public import StacksFrontier.CategoryTheory.Functor.Derived.Subcategory
public import StacksFrontier.CategoryTheory.Functor.Derived.Triangle.LeftDerived
import StacksFrontier.CategoryTheory.Triangulated.Localization

/-!
# The left derived functor lives on a triangulated subcategory

Let `F : 𝒟 ⥤ 𝒟'` be an exact functor of pre-triangulated categories and let `S` be a saturated
multiplicative system in `𝒟` compatible with the triangulated structure (Situation 05S8). The
left derived functor `LF` is *defined at* an object `X` when the pro-object
$$ S/X ⟶ 𝒟', \qquad (s : X' ⟶ X) ⟼ F(X'), $$
is essentially constant; its value is then `LF(X)` (Tag 05S9(2)). Write `ℰ` for the full
subcategory of `𝒟` spanned by the objects at which `LF` is defined, and
`S_ℰ = Arrows(ℰ) ∩ S`. Stacks 05SE closes with "a similar result holds for `LF`": `ℰ` is a strictly
full triangulated subcategory of `𝒟`, `LF` is an exact functor `ℰ ⥤ 𝒟'`, every element of `S`
with source *or* target in `ℰ` is a morphism of `ℰ`, `S_ℰ` is a saturated multiplicative system
in `ℰ` compatible with the triangulated structure which `LF` inverts, the induced functor
`S_ℰ^{-1}ℰ ⥤ S^{-1}𝒟` is fully faithful and exact, `LF` factors through an exact functor
`S_ℰ^{-1}ℰ ⥤ 𝒟'`, and `ℰ` is saturated as soon as `𝒟'` is Karoubian. This file states and proves
that counterpart; the statement for `RF` is
`CategoryTheory.Functor.isTriangulated_and_exists_rightDerivedFunctor`.

## Main results

* `CategoryTheory.Functor.isTriangulated_and_exists_leftDerivedFunctor` (Tag 05SE, for `LF`):
  the eight assertions of the tag for the left derived functor, as one conjunction over the
  subcategory `ℰ` and one left derived functor `LF` on it.

## Implementation notes

The proof is the dual of the one for `RF`. The functor `LF` is built from a chosen value at each
object of `ℰ` together with the morphism of Stacks 05SA(2), which is unique because a value cone
is a limit cone. Its commutation with the shift compares the chosen value at `X⟦n⟧` with the cone
on the pro-object at `X⟦n⟧` obtained by shifting a value at `X` and extending it along the
equivalence `W/X ≌ W/(X⟦n⟧)`, `s ↦ s⟦n⟧`, of index categories (Stacks 05SU); the comparison is
the map of Stacks 05SA(2) along an isomorphism, hence an isomorphism. Exactness is the second
half of Stacks 05SC at the chosen values. Parts (3) and (4) are Stacks 05SB(2), part (8) is
Stacks 05SD(2) for `LF`, and parts (5) and (6) are the statements for a subcategory closed along
`W`, which are shared with `RF`.

## References

* [StacksProject 05SE](https://stacks.math.columbia.edu/tag/05SE), Proposition 13.14.6, last
  sentence; the situation is Tag 05S8, definedness and values are Tag 05S9, the map `LF(f)` is
  Tag 05SA, the inputs are Tags 05SB, 05SC, 05SU and 05SD, the localization of a
  pre-triangulated category is Tag 05R6, the factorization is Tag 05R7, and saturated
  subcategories are Tag 05RB.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated Localization ZeroObject

namespace DerivedFunctorSubcategoryLeft

open DerivedFunctorBiprodComputes (mem_of_isIso)

-- An index of `W/X` and its shift are the same object under two spellings, and the shift
-- sections cross between them constantly; these are the structure literal and forgetful functors
-- the crossings go through, as in `StacksFrontier.CategoryTheory.Functor.Derived.Subcategory`.
attribute [local implicit_reducible] MorphismProperty.Over.mk MorphismProperty.Comma.forget

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-! ### Values of the left derived functor and the morphism of Stacks 05SA(2) -/

section Values

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]
  (F : C ⥤ H) (W : MorphismProperty C)

/-- The pro-object `W/X ⟶ H`, `(s : X' ⟶ X) ↦ F(X')`, of Stacks 05S9(2). -/
private abbrev proDiagram (X : C) : W.Over ⊤ X ⥤ H :=
  MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F

/-- `LF` is defined at every zero object, with value `F(0)`. -/
private lemma exists_value_of_isZero [W.ContainsIdentities] {Z : C} (hZ : IsZero Z)
    (hFZ : IsZero (F.obj Z)) : ∃ c, F.IsLeftDerivedValueAt W Z c := by
  refine ⟨Cone.mk (F.obj Z)
    { app := fun _ => hFZ.to_ _
      naturality := fun _ _ _ => hFZ.eq_of_src _ _ },
    MorphismProperty.Over.mk ⊤ (𝟙 Z) (W.id_mem Z), hFZ.to_ _, hFZ.eq_of_src _ _, fun s => ?_⟩
  exact ⟨MorphismProperty.Over.mk ⊤ (𝟙 Z) (W.id_mem Z),
    MorphismProperty.Over.homMk (hZ.to_ s.left) (hZ.eq_of_src _ _), 𝟙 _,
    hFZ.eq_of_src _ _⟩

variable {F W}

/-- **Stacks 05SA(2).** The characterisation of the morphism `LF(f) : c.pt ⟶ d.pt` induced by
`f : X ⟶ Y` between a cone `c` on the pro-object at `X` and a cone `d` on the pro-object at `Y`:
compatibility with the projections along every commutative square `a.hom ≫ f = g ≫ b.hom` whose
vertical sides are indices of `W/X` and of `W/Y`. -/
private def IsLeftDerivedMap {X Y : C} (f : X ⟶ Y) {c : Cone (proDiagram F W X)}
    {d : Cone (proDiagram F W Y)} (u : c.pt ⟶ d.pt) : Prop :=
  ∀ (a : W.Over ⊤ X) (b : W.Over ⊤ Y) (g : a.left ⟶ b.left),
    a.hom ≫ f = g ≫ b.hom → u ≫ d.π.app b = c.π.app a ≫ F.map g

/-- The characterisation of Stacks 05SA(2) for the identity. -/
private lemma isLeftDerivedMap_id {X : C} (c : Cone (proDiagram F W X)) :
    IsLeftDerivedMap (𝟙 X) (𝟙 c.pt) := by
  intro a b g h
  rw [Category.id_comp]
  exact (StacksDerivedFunctor.overS_cone_nat W F c (s := a) (t := b) g
    (by simpa using h.symm)).symm

/-- The characterisation of Stacks 05SA(2) for a morphism that is the identity. -/
private lemma isLeftDerivedMap_of_eq_id {X : C} {c : Cone (proDiagram F W X)} {f : X ⟶ X}
    (hf : f = 𝟙 X) : IsLeftDerivedMap f (𝟙 c.pt) := by
  subst hf; exact isLeftDerivedMap_id c

/-- **Stacks 05SA(2)**, uniqueness: a morphism into a value of `LF` is determined by its
composites with the projections. -/
private lemma eq_of_isLeftDerivedMap [W.HasRightCalculusOfFractions] {X Y : C} (f : X ⟶ Y)
    {c : Cone (proDiagram F W X)} {d : Cone (proDiagram F W Y)}
    (hd : F.IsLeftDerivedValueAt W Y d) {u u' : c.pt ⟶ d.pt}
    (hu : IsLeftDerivedMap f u) (hu' : IsLeftDerivedMap f u') : u = u' := by
  refine hd.isLimit.hom_ext fun b => ?_
  obtain ⟨X₀, g, t, ht, hsq⟩ := StacksDerivedFunctor.exists_ore_square_right W b.hom f b.prop
  rw [hu (MorphismProperty.Over.mk ⊤ t ht) b g hsq.symm,
    hu' (MorphismProperty.Over.mk ⊤ t ht) b g hsq.symm]

/-- **Stacks 05SA(2)**, existence. -/
private lemma exists_isLeftDerivedMap [W.HasRightCalculusOfFractions] {X Y : C} (f : X ⟶ Y)
    (c : Cone (proDiagram F W X)) {d : Cone (proDiagram F W Y)}
    (hd : F.IsLeftDerivedValueAt W Y d) : ∃ u : c.pt ⟶ d.pt, IsLeftDerivedMap f u := by
  obtain ⟨φ, hφ, -⟩ := StacksDerivedFunctor.main_LF_map_of_rightCalculus F W f c hd
  exact ⟨φ, fun a b g h => hφ a.left b.left a.hom b.hom g a.prop b.prop h⟩

/-- One square per index of the target suffices in the characterisation of Stacks 05SA(2): for a
fixed index of `W/Y` the composite `c.pt ⟶ F(X') ⟶ F(Y')` does not depend on the chosen square,
by `StacksDerivedFunctor.indep_LF`. -/
private lemma isLeftDerivedMap_of_forall_exists [W.HasRightCalculusOfFractions] {X Y : C}
    (f : X ⟶ Y) {c : Cone (proDiagram F W X)} {d : Cone (proDiagram F W Y)} {u : c.pt ⟶ d.pt}
    (h : ∀ b : W.Over ⊤ Y, ∃ (a : W.Over ⊤ X) (g : a.left ⟶ b.left),
      a.hom ≫ f = g ≫ b.hom ∧ u ≫ d.π.app b = c.π.app a ≫ F.map g) :
    IsLeftDerivedMap f u := by
  intro a b g hsq
  obtain ⟨a', g', hsq', he⟩ := h b
  rw [he]
  exact StacksDerivedFunctor.indep_LF W F f c b.hom b.prop a'.hom a.hom a'.prop a.prop g' g
    hsq' hsq

/-- The characterisation of Stacks 05SA(2) is compatible with composition. -/
private lemma IsLeftDerivedMap.comp [W.HasRightCalculusOfFractions] {X Y Z : C} {f : X ⟶ Y}
    {g : Y ⟶ Z} {c : Cone (proDiagram F W X)} {d : Cone (proDiagram F W Y)}
    {e : Cone (proDiagram F W Z)} {u : c.pt ⟶ d.pt} {v : d.pt ⟶ e.pt}
    (hu : IsLeftDerivedMap f u) (hv : IsLeftDerivedMap g v) :
    IsLeftDerivedMap (f ≫ g) (u ≫ v) := by
  intro a b k hsq
  obtain ⟨Y₀, g₁, t₁, ht₁, h₁⟩ := StacksDerivedFunctor.exists_ore_square_right W b.hom g b.prop
  obtain ⟨X₀, f₁, t₀, ht₀, h₀⟩ := StacksDerivedFunctor.exists_ore_square_right W t₁ f ht₁
  have hv' := hv (MorphismProperty.Over.mk ⊤ t₁ ht₁) b g₁ h₁.symm
  have hu' := hu (MorphismProperty.Over.mk ⊤ t₀ ht₀) (MorphismProperty.Over.mk ⊤ t₁ ht₁) f₁
    h₀.symm
  have hind := StacksDerivedFunctor.indep_LF W F (f ≫ g) c b.hom b.prop a.hom t₀ a.prop ht₀ k
    (f₁ ≫ g₁) hsq (by rw [Category.assoc, h₁, ← Category.assoc f₁ t₁ g, h₀, Category.assoc])
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => u ≫ z) hv').trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ F.map g₁) hu').trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => c.π.app (MorphismProperty.Over.mk ⊤ t₀ ht₀) ≫ z)
    (F.map_comp f₁ g₁).symm).trans ?_
  exact hind.symm

/-- The characterisation of Stacks 05SA(2) for a morphism that is a composite. -/
private lemma IsLeftDerivedMap.comp_of_eq [W.HasRightCalculusOfFractions] {X Y Z : C}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} {c : Cone (proDiagram F W X)}
    {d : Cone (proDiagram F W Y)} {e : Cone (proDiagram F W Z)} {u : c.pt ⟶ d.pt}
    {v : d.pt ⟶ e.pt} (hu : IsLeftDerivedMap f u) (hv : IsLeftDerivedMap g v)
    (hh : h = f ≫ g) : IsLeftDerivedMap h (u ≫ v) := by
  subst hh; exact hu.comp hv

/-- The map of Stacks 05SA(2) along an isomorphism, between two values, is an isomorphism. -/
private lemma isIso_of_isLeftDerivedMap [W.HasRightCalculusOfFractions] {X Y : C} (e : X ≅ Y)
    {c : Cone (proDiagram F W X)} (hc : F.IsLeftDerivedValueAt W X c)
    {d : Cone (proDiagram F W Y)} (hd : F.IsLeftDerivedValueAt W Y d) {u : c.pt ⟶ d.pt}
    (hu : IsLeftDerivedMap e.hom u) : IsIso u := by
  obtain ⟨v, hv⟩ := exists_isLeftDerivedMap e.inv d hc
  exact ⟨v, eq_of_isLeftDerivedMap (𝟙 X) hc (hu.comp_of_eq hv e.hom_inv_id.symm)
      (isLeftDerivedMap_id c),
    eq_of_isLeftDerivedMap (𝟙 Y) hd (hv.comp_of_eq hu e.inv_hom_id.symm)
      (isLeftDerivedMap_id d)⟩

variable (F W)

/-- **Stacks 05SE(3)** for `LF`, which is the first half of Stacks 05SB(2): an element of `W`
with either source or target in `ℰ` has both in `ℰ`. -/
private lemma prop_iff_of_mem (E : ObjectProperty C) (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsLeftDerivedValueAt W X c) {X Y : C} {s : X ⟶ Y} (hs : W s) :
    E X ↔ E Y := by
  let := hW.hasRightCalculusOfFractions
  rw [hE X, hE Y]
  exact (F.exists_isLeftDerivedValueAt_iff_and_isIso_of_mem W hs).1

/-- `ℰ` is strictly full: a saturated multiplicative system contains every isomorphism. -/
private lemma isClosedUnderIsomorphisms (E : ObjectProperty C) (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsLeftDerivedValueAt W X c) : E.IsClosedUnderIsomorphisms :=
  ⟨fun {_ _} e hX => (prop_iff_of_mem F W E hW hE (mem_of_isIso hW e.hom)).1 hX⟩

end Values

/-! ### The left derived functor on `ℰ` -/

section Derived

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]
  (F : C ⥤ H) (W : MorphismProperty C) (E : ObjectProperty C)
  (hE : ∀ X, E X ↔ ∃ c, F.IsLeftDerivedValueAt W X c)

/-- A value of `LF` at an object of `ℰ`, chosen once and for all (Stacks 05S9(2)). -/
private noncomputable def valueCone (X : E.FullSubcategory) : Cone (proDiagram F W X.obj) :=
  ((hE X.obj).1 X.property).choose

private lemma isLeftDerivedValueAt_valueCone (X : E.FullSubcategory) :
    F.IsLeftDerivedValueAt W X.obj (valueCone F W E hE X) :=
  ((hE X.obj).1 X.property).choose_spec

variable [W.HasRightCalculusOfFractions]

/-- The morphism of Stacks 05SA(2) between the chosen values, i.e. `LF(f)`. -/
private noncomputable def derivedMap {X Y : E.FullSubcategory} (f : X ⟶ Y) :
    (valueCone F W E hE X).pt ⟶ (valueCone F W E hE Y).pt :=
  (exists_isLeftDerivedMap f.hom (valueCone F W E hE X)
    (isLeftDerivedValueAt_valueCone F W E hE Y)).choose

private lemma isLeftDerivedMap_derivedMap {X Y : E.FullSubcategory} (f : X ⟶ Y) :
    IsLeftDerivedMap f.hom (derivedMap F W E hE f) :=
  (exists_isLeftDerivedMap f.hom (valueCone F W E hE X)
    (isLeftDerivedValueAt_valueCone F W E hE Y)).choose_spec

private lemma derivedMap_eq {X Y : E.FullSubcategory} (f : X ⟶ Y)
    {u : (valueCone F W E hE X).pt ⟶ (valueCone F W E hE Y).pt}
    (hu : IsLeftDerivedMap f.hom u) : derivedMap F W E hE f = u :=
  eq_of_isLeftDerivedMap _ (isLeftDerivedValueAt_valueCone F W E hE Y)
    (isLeftDerivedMap_derivedMap F W E hE f) hu

/-- **Stacks 05SE(2)** for `LF`, as a functor: the left derived functor `LF : ℰ ⥤ 𝒟'`, sending
an object of `ℰ` to the vertex of its chosen value and a morphism to the map of Stacks 05SA(2),
which is unique, so that functoriality is `isLeftDerivedMap_id` and `IsLeftDerivedMap.comp`. -/
private noncomputable def leftDerived : E.FullSubcategory ⥤ H where
  obj X := (valueCone F W E hE X).pt
  map f := derivedMap F W E hE f
  map_id X := derivedMap_eq F W E hE (𝟙 X) (isLeftDerivedMap_of_eq_id (by simp))
  map_comp f g := derivedMap_eq F W E hE (f ≫ g)
    ((isLeftDerivedMap_derivedMap F W E hE f).comp_of_eq
      (isLeftDerivedMap_derivedMap F W E hE g) (by simp))

private lemma leftDerived_obj (X : E.FullSubcategory) :
    (leftDerived F W E hE).obj X = (valueCone F W E hE X).pt := rfl

private lemma leftDerived_map {X Y : E.FullSubcategory} (f : X ⟶ Y) :
    (leftDerived F W E hE).map f = derivedMap F W E hE f := rfl

/-- **Stacks 05SE(4)** for `LF`: `LF` maps every element of `S_ℰ` to an isomorphism. This is the
second half of Stacks 05SB(2), together with the uniqueness of the map of Stacks 05SA(2). -/
private lemma isInvertedBy :
    (W.inverseImage E.ι).IsInvertedBy (leftDerived F W E hE) := by
  intro X Y s hs
  obtain ⟨φ, hφ, hiso⟩ := (F.exists_isLeftDerivedValueAt_iff_and_isIso_of_mem W
    (s := s.hom) (by simpa using hs)).2 (isLeftDerivedValueAt_valueCone F W E hE X)
    (isLeftDerivedValueAt_valueCone F W E hE Y)
  rw [leftDerived_map, derivedMap_eq F W E hE s (fun a b f h => hφ a b f h)]
  exact hiso

end Derived

/-! ### The subcategory of objects at which `LF` is defined -/

section Defined

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

/-- `LF` is defined at the zero object, with value `F(0)`. -/
private lemma prop_zero (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated] (W : MorphismProperty C)
    (E : ObjectProperty C) (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsLeftDerivedValueAt W X c) : E (0 : C) := by
  let := hW.isMultiplicative
  exact (hE 0).2 (exists_value_of_isZero F W (isZero_zero C)
    (Functor.map_isZero _ (isZero_zero C)))

variable (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
  (W : MorphismProperty C) [W.IsCompatibleWithTriangulation] (E : ObjectProperty C)

/-- **Stacks 05SU(2)** for `n = 1`, in its definedness half: `LF` is defined at `X⟦1⟧` if and
only if it is defined at `X`. This is Stacks 05SC for `LF` applied to the rotation `(X, 0, X⟦1⟧)`
of the contractible triangle at `X`. -/
private lemma prop_shift_iff (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsLeftDerivedValueAt W X c) (X : C) :
    E (X⟦(1 : ℤ)⟧) ↔ E X := by
  obtain ⟨h₁₂₃, h₂₃₁, -⟩ :=
    (F.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished
      W hW _ (rot_of_distTriang _ (contractible_distinguished X))).2
  have hz := (hE (0 : C)).1 (prop_zero F W E hW hE)
  exact ⟨fun h => (hE X).2 (h₂₃₁ hz ((hE _).1 h)), fun h => (hE _).2 (h₁₂₃ ((hE X).1 h) hz)⟩

/-- Two of three: `ℰ` is closed under extensions, by Stacks 05SC for `LF`. -/
private lemma isTriangulatedClosed₂ (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsLeftDerivedValueAt W X c) : E.IsTriangulatedClosed₂ := by
  let := isClosedUnderIsomorphisms F W E hW hE
  refine ObjectProperty.IsTriangulatedClosed₂.mk' fun T hT h₁ h₃ => (hE _).2 ?_
  exact (F.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished
    W hW T hT).2.2.2.1 ((hE _).1 h₃) ((hE _).1 h₁)

/-- **Stacks 05SU(2)**, definedness half: `LF` is defined at `X⟦n⟧` if and only if it is defined
at `X`, for every `n : ℤ`, by induction on `n` from `prop_shift_iff`. -/
private lemma prop_shift_iff_int (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsLeftDerivedValueAt W X c) (n : ℤ) (X : C) :
    E (X⟦n⟧) ↔ E X := by
  let := isClosedUnderIsomorphisms F W E hW hE
  induction n using Int.induction_on with
  | zero => exact E.prop_iff_of_iso ((shiftFunctorZero C ℤ).app X)
  | succ n ih =>
    refine Iff.trans (E.prop_iff_of_iso
      ((shiftFunctorAdd' C (n : ℤ) 1 ((n : ℤ) + 1) rfl).app X)) (Iff.trans ?_ ih)
    exact prop_shift_iff F W E hW hE (X⟦(n : ℤ)⟧)
  | pred n ih =>
    refine Iff.trans (Iff.trans (prop_shift_iff F W E hW hE (X⟦(-(n : ℤ) - 1)⟧)).symm ?_) ih
    exact (E.prop_iff_of_iso
      ((shiftFunctorAdd' C (-(n : ℤ) - 1) 1 (-(n : ℤ)) (by omega)).app X)).symm

/-- **Stacks 05SE(1)** for `LF`: `ℰ` is a triangulated subcategory of `C`. -/
private lemma isTriangulated (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsLeftDerivedValueAt W X c) : E.IsTriangulated := by
  let : E.ContainsZero := ⟨0, isZero_zero C, prop_zero F W E hW hE⟩
  let : E.IsStableUnderShift ℤ :=
    ⟨fun n => ⟨fun X hX => (prop_shift_iff_int F W E hW hE n X).2 hX⟩⟩
  let := isTriangulatedClosed₂ F W E hW hE
  constructor

/-- **Stacks 05SE(8)** for `LF`: over a Karoubian target, `ℰ` is a saturated (thick)
subcategory. This is Stacks 05SD(2) for `LF` together with strict fullness. -/
private lemma isSaturated_of_isIdempotentComplete (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsLeftDerivedValueAt W X c) (hH : IsIdempotentComplete H) :
    E.IsSaturated := by
  let := isClosedUnderIsomorphisms F W E hW hE
  have hself : ∀ Z : C, E.isoClosure Z → E Z := fun Z hZ => by
    rwa [E.isoClosure_eq_self] at hZ
  have key : ∀ X Y : C, E (X ⊞ Y) → E X ∧ E Y := fun X Y h => by
    obtain ⟨hX, hY⟩ := (F.exists_isDerivedValueAt_biprod_and_isIso_biprod_lift W hW X
      Y).2.2.2.1 hH ((hE _).1 h)
    exact ⟨(hE X).2 hX, (hE Y).2 hY⟩
  constructor
  · intro X Y _ h
    exact E.le_isoClosure _ (key X Y (hself _ h)).1
  · intro X Y _ h
    exact E.le_isoClosure _ (key X Y (hself _ h)).2

end Defined

/-! ### The shift on the index categories -/

section ShiftIndex

variable {C : Type u₁} [Category.{v₁} C] [HasShift C ℤ] (W : MorphismProperty C)
  [W.IsCompatibleWithShift ℤ]

/-- The shift of indices, as a functor `W/X ⥤ W/(X⟦n⟧)`, `s ↦ s⟦n⟧`. -/
@[implicit_reducible]
private def overShift (X : C) (n : ℤ) : W.Over ⊤ X ⥤ W.Over ⊤ (X⟦n⟧) where
  obj s := MorphismProperty.Over.mk ⊤ (s.hom⟦n⟧')
    ((MorphismProperty.IsCompatibleWithShift.iff W s.hom n).2 s.prop)
  map {_s t} α := MorphismProperty.Over.homMk (α.left⟦n⟧')
    (((shiftFunctor C n).map_comp α.left t.hom).symm.trans
      (congrArg (shiftFunctor C n).map (MorphismProperty.Over.w α)))
  map_id _ := MorphismProperty.Over.Hom.ext ((shiftFunctor C n).map_id _)
  map_comp _ _ := MorphismProperty.Over.Hom.ext ((shiftFunctor C n).map_comp _ _)

private lemma overShift_map_left (X : C) (n : ℤ) {s t : W.Over ⊤ X} (u : s ⟶ t) :
    ((overShift W X n).map u).left = u.left⟦n⟧' := rfl

/-- The shift on index categories is faithful, because the shift of `C` is. -/
private lemma faithful_overShift (X : C) (n : ℤ) : (overShift W X n).Faithful where
  map_injective {s t} u v h := by
    apply MorphismProperty.Over.Hom.ext
    apply (shiftFunctor C n).map_injective
    have h2 : ((overShift W X n).map u).left = ((overShift W X n).map v).left := by rw [h]
    exact h2

/-- The shift on index categories is full, because the shift of `C` is. -/
private lemma full_overShift (X : C) (n : ℤ) : (overShift W X n).Full where
  map_surjective {s t} β := by
    have hw : β.left ≫ t.hom⟦n⟧' = s.hom⟦n⟧' := MorphismProperty.Over.w β
    have hp := (shiftFunctor C n).map_preimage β.left
    refine ⟨MorphismProperty.Over.homMk ((shiftFunctor C n).preimage β.left) ?_, ?_⟩
    · apply (shiftFunctor C n).map_injective
      rwa [Functor.map_comp, hp]
    · exact MorphismProperty.Over.Hom.ext hp

/-- The shift on index categories is essentially surjective, since `W` respects isomorphisms. -/
private lemma essSurj_overShift [W.IsMultiplicative]
    (hiso : MorphismProperty.isomorphisms C ≤ W) (X : C) (n : ℤ) :
    (overShift W X n).EssSurj where
  mem_essImage t := by
    have := MorphismProperty.respectsIso_of_isStableUnderComposition hiso
    refine ⟨MorphismProperty.Over.mk ⊤
      (t.hom⟦-n⟧' ≫ (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app X)
      ((W.cancel_right_of_respectsIso _ _).2
        ((MorphismProperty.IsCompatibleWithShift.iff W t.hom (-n)).2 t.prop)), ⟨?_⟩⟩
    refine MorphismProperty.Over.isoMk
      ((shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).app t.left) ?_
    change _ ≫ t.hom =
      (t.hom⟦-n⟧' ≫ (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app X)⟦n⟧'
    rw [Functor.map_comp, shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app]
    exact ((shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).hom.naturality t.hom).symm

/-- **The index categories of `X` and of `X⟦n⟧` are equivalent**, by the shift by `n`. -/
private lemma isEquivalence_overShift [W.IsMultiplicative]
    (hiso : MorphismProperty.isomorphisms C ≤ W) (X : C) (n : ℤ) :
    (overShift W X n).IsEquivalence :=
  have := faithful_overShift W X n
  have := full_overShift W X n
  have := essSurj_overShift W hiso X n
  { }

/-- Every index of `W/(X⟦n⟧)` receives a morphism from the shift of an index of `W/X`. -/
private lemma exists_hom_overShift [W.IsMultiplicative]
    (hiso : MorphismProperty.isomorphisms C ≤ W) (n : ℤ) {X : C} (t : W.Over ⊤ (X⟦n⟧)) :
    ∃ σ : W.Over ⊤ X, Nonempty ((overShift W X n).obj σ ⟶ t) := by
  have := essSurj_overShift W hiso X n
  exact ⟨_, ⟨((overShift W X n).objObjPreimageIso t).hom⟩⟩

end ShiftIndex

/-! ### The value of `LF` at a shifted object -/

section ShiftValue

variable {C : Type u₁} [Category.{v₁} C] [HasShift C ℤ] {H : Type u₂} [Category.{v₂} H]
  [HasShift H ℤ] (F : C ⥤ H) [F.CommShift ℤ] (W : MorphismProperty C) [W.IsMultiplicative]
  [W.IsCompatibleWithShift ℤ]

/-- The cone on the pro-object at `X⟦n⟧` restricted along `overShift W X n`, with vertex
`c.pt⟦n⟧`, obtained from a cone `c` on the pro-object at `X` by shifting. -/
@[implicit_reducible]
private def preShiftCone (n : ℤ) {X : C} (c : Cone (proDiagram F W X)) :
    Cone (overShift W X n ⋙ proDiagram F W (X⟦n⟧)) where
  pt := c.pt⟦n⟧
  π :=
    { app := fun s => (c.π.app s)⟦n⟧' ≫ (F.commShiftIso n).inv.app s.left
      naturality := fun s t u => by
        have hw : (c.π.app s)⟦n⟧' ≫ (F.map u.left)⟦n⟧' = (c.π.app t)⟦n⟧' :=
          ((shiftFunctor H n).map_comp (c.π.app s) (F.map u.left)).symm.trans
            (congrArg (shiftFunctor H n).map (c.w u))
        have h1 := F.commShiftIso_inv_naturality u.left n
        refine (Category.id_comp _).trans ?_
        exact ((congrArg (fun z => z ≫ (F.commShiftIso n).inv.app t.left) hw).symm.trans
          (Category.assoc _ _ _)).trans ((congrArg (fun z => (c.π.app s)⟦n⟧' ≫ z) h1).trans
            (Category.assoc _ _ _).symm) }

/-- The value of `LF` at `X⟦n⟧` attached to a cone `c` on the pro-object at `X`: the cone with
vertex `c.pt⟦n⟧` extended from `preShiftCone` along the equivalence `overShift` of index
categories. -/
@[implicit_reducible]
private noncomputable def shiftCone (hiso : MorphismProperty.isomorphisms C ≤ W) (n : ℤ)
    {X : C} (c : Cone (proDiagram F W X)) : Cone (proDiagram F W (X⟦n⟧)) where
  pt := c.pt⟦n⟧
  π :=
    haveI := isEquivalence_overShift W hiso X n
    (Functor.Initial.extendCone.obj (preShiftCone F W n c)).π

/-- The projections of `shiftCone`: at an index `t` of `W/(X⟦n⟧)` receiving *any* morphism `g`
from the shift of an index `s` of `W/X`, the projection is the shift of the projection of `c` at
`s`, followed by `F.commShiftIso n` and `F(g)`. -/
private lemma shiftCone_π_app (hiso : MorphismProperty.isomorphisms C ≤ W) (n : ℤ) {X : C}
    (c : Cone (proDiagram F W X)) (t : W.Over ⊤ (X⟦n⟧)) (s : W.Over ⊤ X)
    (g : (overShift W X n).obj s ⟶ t) :
    (shiftCone F W hiso n c).π.app t
      = ((c.π.app s)⟦n⟧' ≫ (F.commShiftIso n).inv.app s.left) ≫ F.map g.left := by
  have := isEquivalence_overShift W hiso X n
  exact Functor.Initial.extendCone_obj_π_app' (preShiftCone F W n c) g

/-- The projection of `shiftCone` at the shift of an index of `W/X`. -/
private lemma shiftCone_π_app_shift (hiso : MorphismProperty.isomorphisms C ≤ W) (n : ℤ)
    {X : C} (c : Cone (proDiagram F W X)) (s : W.Over ⊤ X) :
    (shiftCone F W hiso n c).π.app ((overShift W X n).obj s)
      = (c.π.app s)⟦n⟧' ≫ (F.commShiftIso n).inv.app s.left := by
  rw [shiftCone_π_app F W hiso n c _ s (𝟙 _)]
  exact (congrArg (fun z => ((c.π.app s)⟦n⟧' ≫ (F.commShiftIso n).inv.app s.left) ≫ z)
    (F.map_id (s.left⟦n⟧))).trans (Category.comp_id _)

/-- **Stacks 05SU(2)**, value half. If `c` is a value of `LF` at `X` (Stacks 05S9(2)), then
`c.pt⟦n⟧` is a value of `LF` at `X⟦n⟧`, at the cone `shiftCone`. -/
private lemma isLeftDerivedValueAt_shiftCone (hiso : MorphismProperty.isomorphisms C ≤ W)
    (n : ℤ) {X : C} {c : Cone (proDiagram F W X)} (hc : F.IsLeftDerivedValueAt W X c) :
    F.IsLeftDerivedValueAt W (X⟦n⟧) (shiftCone F W hiso n c) := by
  obtain ⟨s₀, r, hr, hcof⟩ := hc
  refine ⟨(overShift W X n).obj s₀, (F.commShiftIso n).hom.app s₀.left ≫ r⟦n⟧', ?_,
    fun t => ?_⟩
  · rw [shiftCone_π_app_shift F W hiso n c s₀, Category.assoc,
      ← Category.assoc ((F.commShiftIso n).inv.app s₀.left), Iso.inv_hom_id_app,
      Category.id_comp, ← Functor.map_comp, hr]
    exact (shiftFunctor H n).map_id c.pt
  · obtain ⟨σ, ⟨e⟩⟩ := exists_hom_overShift W hiso n t
    obtain ⟨t₀, u₀, v₀, hu₀⟩ := hcof σ
    refine ⟨(overShift W X n).obj t₀, (overShift W X n).map u₀ ≫ e,
      (overShift W X n).map v₀, ?_⟩
    have key : ∀ {V : H} (w : (F.obj σ.left)⟦n⟧ ⟶ V),
        (F.map v₀.left)⟦n⟧' ≫ r⟦n⟧' ≫ (c.π.app σ)⟦n⟧' ≫ w = (F.map u₀.left)⟦n⟧' ≫ w := by
      intro V w
      have h : (F.map u₀.left)⟦n⟧' = (F.map v₀.left)⟦n⟧' ≫ r⟦n⟧' ≫ (c.π.app σ)⟦n⟧' := by
        rw [hu₀, Functor.map_comp, Functor.map_comp]
      rw [h]
      simp only [Category.assoc]
    rw [shiftCone_π_app F W hiso n c t σ e]
    change F.map (u₀.left⟦n⟧' ≫ e.left) = F.map (v₀.left⟦n⟧') ≫
      ((F.commShiftIso n).hom.app s₀.left ≫ r⟦n⟧') ≫
        ((c.π.app σ)⟦n⟧' ≫ (F.commShiftIso n).inv.app σ.left) ≫ F.map e.left
    simp only [Category.assoc, F.map_comp]
    rw [F.commShiftIso_hom_naturality_assoc, key, ← F.commShiftIso_hom_naturality_assoc,
      Iso.hom_inv_id_app_assoc]

end ShiftValue

/-! ### Derived maps and the shift -/

section ShiftDerivedMap

variable {C : Type u₁} [Category.{v₁} C] [HasShift C ℤ] {H : Type u₂} [Category.{v₂} H]
  [HasShift H ℤ] (F : C ⥤ H) [F.CommShift ℤ] (W : MorphismProperty C)
  [W.IsCompatibleWithShift ℤ] [W.HasRightCalculusOfFractions]

/-- The shift of the map of Stacks 05SA(2) attached to `g` is the map of Stacks 05SA(2) attached
to `g⟦n⟧'`, between the cones of `shiftCone`. -/
private lemma isLeftDerivedMap_shift (hiso : MorphismProperty.isomorphisms C ≤ W) (n : ℤ)
    {X Y : C} {g : X ⟶ Y} {c : Cone (proDiagram F W X)} {d : Cone (proDiagram F W Y)}
    {u : c.pt ⟶ d.pt} (hu : IsLeftDerivedMap g u) :
    IsLeftDerivedMap (c := shiftCone F W hiso n c) (d := shiftCone F W hiso n d)
      (g⟦n⟧') (u⟦n⟧') := by
  refine isLeftDerivedMap_of_forall_exists _ fun b => ?_
  obtain ⟨σ, ⟨e⟩⟩ := exists_hom_overShift W hiso n b
  obtain ⟨X₀, k, t, ht, hk⟩ := StacksDerivedFunctor.exists_ore_square_right W σ.hom g σ.prop
  have he : e.left ≫ b.hom = σ.hom⟦n⟧' := MorphismProperty.Over.w e
  refine ⟨(overShift W X n).obj (MorphismProperty.Over.mk ⊤ t ht), k⟦n⟧' ≫ e.left, ?_, ?_⟩
  · change t⟦n⟧' ≫ g⟦n⟧' = (k⟦n⟧' ≫ e.left) ≫ b.hom
    rw [Category.assoc, he, ← Functor.map_comp, ← Functor.map_comp, hk]
  · have h1 := hu (MorphismProperty.Over.mk ⊤ t ht) σ k hk.symm
    have h2 : u⟦n⟧' ≫ (d.π.app σ)⟦n⟧' =
        (c.π.app (MorphismProperty.Over.mk ⊤ t ht))⟦n⟧' ≫ (F.map k)⟦n⟧' := by
      rw [← Functor.map_comp, h1, Functor.map_comp]
    rw [shiftCone_π_app F W hiso n d b σ e,
      shiftCone_π_app_shift F W hiso n c (MorphismProperty.Over.mk ⊤ t ht)]
    simp only [Category.assoc, F.map_comp]
    rw [reassoc_of% h2, F.commShiftIso_inv_naturality_assoc]
    rfl

/-- A morphism into the vertex of `shiftCone` is the map of Stacks 05SA(2) as soon as it is
compatible with the projections at the *shifted* indices — the form in which the third clause of
Stacks 05SC for `LF` produces it. -/
private lemma isLeftDerivedMap_shiftCone_of_forall (hiso : MorphismProperty.isomorphisms C ≤ W)
    (n : ℤ) {Y X : C} (g : Y ⟶ X⟦n⟧) {c : Cone (proDiagram F W Y)}
    {d : Cone (proDiagram F W X)} {u : c.pt ⟶ d.pt⟦n⟧}
    (h : ∀ (r : W.Over ⊤ Y) (s : W.Over ⊤ X) (h' : r.left ⟶ s.left⟦n⟧),
      r.hom ≫ g = h' ≫ s.hom⟦n⟧' →
        u ≫ (d.π.app s)⟦n⟧' = c.π.app r ≫ F.map h' ≫ (F.commShiftIso n).hom.app s.left) :
    IsLeftDerivedMap (c := c) (d := shiftCone F W hiso n d) g u := by
  refine isLeftDerivedMap_of_forall_exists _ fun b => ?_
  obtain ⟨σ, ⟨e⟩⟩ := exists_hom_overShift W hiso n b
  have he : e.left ≫ b.hom = σ.hom⟦n⟧' := MorphismProperty.Over.w e
  obtain ⟨Y₀, h', t, ht, hsq⟩ := StacksDerivedFunctor.exists_ore_square_right W (σ.hom⟦n⟧') g
    ((MorphismProperty.IsCompatibleWithShift.iff W σ.hom n).2 σ.prop)
  refine ⟨MorphismProperty.Over.mk ⊤ t ht, h' ≫ e.left, ?_, ?_⟩
  · change t ≫ g = (h' ≫ e.left) ≫ b.hom
    rw [Category.assoc, he]
    exact hsq.symm
  · rw [shiftCone_π_app F W hiso n d b σ e]
    simp only [Category.assoc, F.map_comp]
    rw [reassoc_of% (h (MorphismProperty.Over.mk ⊤ t ht) σ h' hsq.symm)]
    simp only [Iso.hom_inv_id_app_assoc]

/-- The unitor of the shift is the map of Stacks 05SA(2) between a value and its zeroth
shift. -/
private lemma isLeftDerivedMap_shiftFunctorZero_inv (hiso : MorphismProperty.isomorphisms C ≤ W)
    {X : C} (c : Cone (proDiagram F W X)) :
    IsLeftDerivedMap (c := c) (d := shiftCone F W hiso 0 c)
      ((shiftFunctorZero C ℤ).inv.app X) ((shiftFunctorZero H ℤ).inv.app c.pt) := by
  refine isLeftDerivedMap_of_forall_exists _ fun b => ?_
  obtain ⟨σ, ⟨e⟩⟩ := exists_hom_overShift W hiso 0 b
  have he : e.left ≫ b.hom = σ.hom⟦(0 : ℤ)⟧' := MorphismProperty.Over.w e
  refine ⟨σ, (shiftFunctorZero C ℤ).inv.app σ.left ≫ e.left, ?_, ?_⟩
  · rw [Category.assoc, he]
    exact (shiftFunctorZero C ℤ).inv.naturality σ.hom
  · have h2 : (shiftFunctorZero H ℤ).inv.app c.pt ≫ (c.π.app σ)⟦(0 : ℤ)⟧' =
        c.π.app σ ≫ (shiftFunctorZero H ℤ).inv.app (F.obj σ.left) :=
      ((shiftFunctorZero H ℤ).inv.naturality (c.π.app σ)).symm
    rw [shiftCone_π_app F W hiso 0 c b σ e, F.commShiftIso_zero,
      Functor.CommShift.isoZero_inv_app]
    simp only [Category.assoc, F.map_comp]
    rw [reassoc_of% h2, Iso.inv_hom_id_app_assoc]

/-- The associator of the shift is the map of Stacks 05SA(2) between the twice-shifted and the
once-shifted cones of `shiftCone`. -/
private lemma isLeftDerivedMap_shiftFunctorAdd_inv (hiso : MorphismProperty.isomorphisms C ≤ W)
    (a b : ℤ) {X : C} (c : Cone (proDiagram F W X)) :
    IsLeftDerivedMap (c := shiftCone F W hiso b (shiftCone F W hiso a c))
      (d := shiftCone F W hiso (a + b) c)
      ((shiftFunctorAdd C a b).inv.app X) ((shiftFunctorAdd H a b).inv.app c.pt) := by
  refine isLeftDerivedMap_of_forall_exists _ fun b' => ?_
  obtain ⟨σ, ⟨ε⟩⟩ := exists_hom_overShift W hiso (a + b) b'
  have he : ε.left ≫ b'.hom = σ.hom⟦a + b⟧' := MorphismProperty.Over.w ε
  refine ⟨(overShift W (X⟦a⟧) b).obj ((overShift W X a).obj σ),
    (shiftFunctorAdd C a b).inv.app σ.left ≫ ε.left, ?_, ?_⟩
  · change (σ.hom⟦a⟧')⟦b⟧' ≫ _ = _
    rw [Category.assoc, he]
    exact (shiftFunctorAdd C a b).inv.naturality σ.hom
  · have h2 : (shiftFunctorAdd H a b).inv.app c.pt ≫ (c.π.app σ)⟦a + b⟧' =
        ((c.π.app σ)⟦a⟧')⟦b⟧' ≫ (shiftFunctorAdd H a b).inv.app (F.obj σ.left) :=
      ((shiftFunctorAdd H a b).inv.naturality (c.π.app σ)).symm
    rw [shiftCone_π_app F W hiso (a + b) c b' σ ε,
      shiftCone_π_app_shift F W hiso b (shiftCone F W hiso a c) ((overShift W X a).obj σ),
      shiftCone_π_app_shift F W hiso a c σ, F.commShiftIso_add a b,
      Functor.CommShift.isoAdd_inv_app]
    simp only [Category.assoc, F.map_comp, Functor.map_comp]
    rw [reassoc_of% h2, Iso.inv_hom_id_app_assoc]
    rfl

end ShiftDerivedMap

/-! ### The left derived functor commutes with the shift and is exact -/

section Exact

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]
  (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
  (W : MorphismProperty C) [W.IsCompatibleWithTriangulation] [W.HasRightCalculusOfFractions]
  (E : ObjectProperty C) [E.IsTriangulated]
  (hE : ∀ X, E X ↔ ∃ c, F.IsLeftDerivedValueAt W X c)

/-- The comparison morphism `LF(X⟦n⟧) ⟶ LF(X)⟦n⟧`: the map of Stacks 05SA(2) along the
isomorphism `ι(X⟦n⟧) ≅ ι(X)⟦n⟧`, from the chosen value at `X⟦n⟧` to the value at `ι(X)⟦n⟧`
provided by Stacks 05SU(2) (`isLeftDerivedValueAt_shiftCone`). -/
private noncomputable def shiftComparison (hW : W.IsSaturated) (n : ℤ)
    (X : E.FullSubcategory) :
    (leftDerived F W E hE).obj (X⟦n⟧) ⟶ ((leftDerived F W E hE).obj X)⟦n⟧ :=
  (exists_isLeftDerivedMap ((E.ι.commShiftIso n).hom.app X) (valueCone F W E hE (X⟦n⟧))
    (isLeftDerivedValueAt_shiftCone F W (DerivedFunctorValues.isomorphisms_le_of_isSaturated hW)
      n (isLeftDerivedValueAt_valueCone F W E hE X))).choose

omit [HasZeroObject H] [Preadditive H] [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]
  [F.IsTriangulated] in
private lemma isLeftDerivedMap_shiftComparison (hW : W.IsSaturated) (n : ℤ)
    (X : E.FullSubcategory) :
    IsLeftDerivedMap (c := valueCone F W E hE (X⟦n⟧))
      (d := shiftCone F W (DerivedFunctorValues.isomorphisms_le_of_isSaturated hW) n
        (valueCone F W E hE X))
      ((E.ι.commShiftIso n).hom.app X) (shiftComparison F W E hE hW n X) :=
  (exists_isLeftDerivedMap ((E.ι.commShiftIso n).hom.app X) (valueCone F W E hE (X⟦n⟧))
    (isLeftDerivedValueAt_shiftCone F W (DerivedFunctorValues.isomorphisms_le_of_isSaturated hW)
      n (isLeftDerivedValueAt_valueCone F W E hE X))).choose_spec

/-- The natural isomorphism `LF(-⟦n⟧) ≅ LF(-)⟦n⟧`. Each component `shiftComparison` is an
isomorphism, being the map of Stacks 05SA(2) along an isomorphism; the family is natural because
both sides are the map of Stacks 05SA(2) along the two sides of the naturality square of
`E.ι.commShiftIso n`. -/
private noncomputable def shiftIso (hW : W.IsSaturated) (n : ℤ) :
    shiftFunctor E.FullSubcategory n ⋙ leftDerived F W E hE ≅
      leftDerived F W E hE ⋙ shiftFunctor H n :=
  haveI : ∀ (m : ℤ) (Y : E.FullSubcategory), IsIso (shiftComparison F W E hE hW m Y) :=
    fun m Y => isIso_of_isLeftDerivedMap ((E.ι.commShiftIso m).app Y)
      (isLeftDerivedValueAt_valueCone F W E hE (Y⟦m⟧))
      (isLeftDerivedValueAt_shiftCone F W
        (DerivedFunctorValues.isomorphisms_le_of_isSaturated hW) m
        (isLeftDerivedValueAt_valueCone F W E hE Y))
      (isLeftDerivedMap_shiftComparison F W E hE hW m Y)
  NatIso.ofComponents (fun X => asIso (shiftComparison F W E hE hW n X)) fun {X Y} f =>
    eq_of_isLeftDerivedMap _
      (isLeftDerivedValueAt_shiftCone F W
        (DerivedFunctorValues.isomorphisms_le_of_isSaturated hW) n
        (isLeftDerivedValueAt_valueCone F W E hE Y))
      ((isLeftDerivedMap_derivedMap F W E hE ((shiftFunctor E.FullSubcategory n).map f)).comp_of_eq
        (isLeftDerivedMap_shiftComparison F W E hE hW n Y) rfl)
      ((isLeftDerivedMap_shiftComparison F W E hE hW n X).comp_of_eq
        (isLeftDerivedMap_shift F W (DerivedFunctorValues.isomorphisms_le_of_isSaturated hW) n
          (isLeftDerivedMap_derivedMap F W E hE f))
        (by simpa using E.ι.commShiftIso_hom_naturality f n))

/-- **Stacks 05SU(2)**, value half: the left derived functor commutes with the shift. The
isomorphisms are `shiftIso`; the two coherence axioms hold because each side is the map of
Stacks 05SA(2) along the corresponding structural morphism of `C`, and that map is unique. -/
@[instance_reducible]
private noncomputable def leftDerivedCommShift (hW : W.IsSaturated) :
    (leftDerived F W E hE).CommShift ℤ where
  commShiftIso n := shiftIso F W E hE hW n
  commShiftIso_zero := by
    ext X
    rw [Functor.CommShift.isoZero_hom_app]
    simp only [shiftIso]
    refine eq_of_isLeftDerivedMap _
      (isLeftDerivedValueAt_shiftCone F W
        (DerivedFunctorValues.isomorphisms_le_of_isSaturated hW) 0
        (isLeftDerivedValueAt_valueCone F W E hE X))
      (isLeftDerivedMap_shiftComparison F W E hE hW 0 X)
      ((isLeftDerivedMap_derivedMap F W E hE
        ((shiftFunctorZero E.FullSubcategory ℤ).hom.app X)).comp_of_eq
        (isLeftDerivedMap_shiftFunctorZero_inv F W
          (DerivedFunctorValues.isomorphisms_le_of_isSaturated hW)
          (valueCone F W E hE X)) ?_)
    rw [E.ι.commShiftIso_zero, Functor.CommShift.isoZero_hom_app]
    rfl
  commShiftIso_add a b := by
    ext X
    rw [Functor.CommShift.isoAdd_hom_app]
    simp only [shiftIso]
    refine eq_of_isLeftDerivedMap _
      (isLeftDerivedValueAt_shiftCone F W
        (DerivedFunctorValues.isomorphisms_le_of_isSaturated hW) (a + b)
        (isLeftDerivedValueAt_valueCone F W E hE X))
      (isLeftDerivedMap_shiftComparison F W E hE hW (a + b) X)
      ((isLeftDerivedMap_derivedMap F W E hE
        ((shiftFunctorAdd E.FullSubcategory a b).hom.app X)).comp_of_eq
        ((isLeftDerivedMap_shiftComparison F W E hE hW b (X⟦a⟧)).comp_of_eq
          ((isLeftDerivedMap_shift F W (DerivedFunctorValues.isomorphisms_le_of_isSaturated hW) b
            (isLeftDerivedMap_shiftComparison F W E hE hW a X)).comp_of_eq
            (isLeftDerivedMap_shiftFunctorAdd_inv F W
              (DerivedFunctorValues.isomorphisms_le_of_isSaturated hW) a b
              (valueCone F W E hE X)) rfl) rfl) ?_)
    rw [E.ι.commShiftIso_add a b, Functor.CommShift.isoAdd_hom_app]
    rfl

/-- **Stacks 05SE(2)** for `LF`: `LF : ℰ ⥤ 𝒟'` is exact. This is the last conjunct of Stacks
05SC for `LF` applied to the image of a distinguished triangle of `ℰ` in `𝒟`, at the chosen
values: the three morphisms it produces are the maps of Stacks 05SA(2) along the three morphisms
of the triangle, hence, by uniqueness, are `LF` of them — the third after the isomorphism of
`leftDerivedCommShift`. -/
private lemma leftDerived_isTriangulated (hW : W.IsSaturated) :
    letI := leftDerivedCommShift F W E hE hW
    (leftDerived F W E hE).IsTriangulated := by
  let := leftDerivedCommShift F W E hE hW
  constructor
  intro T hT
  obtain ⟨u, v, w, hdist, hu, hv, hw⟩ :=
    (F.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished W hW
        (E.ι.mapTriangle.obj T) (E.ι.map_distinguished T hT)).2.2.2.2
      (valueCone F W E hE T.obj₁) (isLeftDerivedValueAt_valueCone F W E hE T.obj₁)
      (valueCone F W E hE T.obj₂) (isLeftDerivedValueAt_valueCone F W E hE T.obj₂)
      (valueCone F W E hE T.obj₃) (isLeftDerivedValueAt_valueCone F W E hE T.obj₃)
  have hcs : ((leftDerived F W E hE).commShiftIso (1 : ℤ)).hom.app T.obj₁
      = shiftComparison F W E hE hW 1 T.obj₁ := rfl
  have heu : u = (leftDerived F W E hE).map T.mor₁ :=
    eq_of_isLeftDerivedMap T.mor₁.hom (isLeftDerivedValueAt_valueCone F W E hE T.obj₂)
      (fun s t f' h => hu s t f' h) (isLeftDerivedMap_derivedMap F W E hE T.mor₁)
  have hev : v = (leftDerived F W E hE).map T.mor₂ :=
    eq_of_isLeftDerivedMap T.mor₂.hom (isLeftDerivedValueAt_valueCone F W E hE T.obj₃)
      (fun s t f' h => hv s t f' h) (isLeftDerivedMap_derivedMap F W E hE T.mor₂)
  have hew : w = (leftDerived F W E hE).map T.mor₃ ≫
      ((leftDerived F W E hE).commShiftIso (1 : ℤ)).hom.app T.obj₁ := by
    rw [hcs]
    exact eq_of_isLeftDerivedMap _
      (isLeftDerivedValueAt_shiftCone F W
        (DerivedFunctorValues.isomorphisms_le_of_isSaturated hW) 1
        (isLeftDerivedValueAt_valueCone F W E hE T.obj₁))
      (isLeftDerivedMap_shiftCone_of_forall F W
        (DerivedFunctorValues.isomorphisms_le_of_isSaturated hW) 1 _ hw)
      ((isLeftDerivedMap_derivedMap F W E hE T.mor₃).comp_of_eq
        (isLeftDerivedMap_shiftComparison F W E hE hW 1 T.obj₁) rfl)
  have hmk : Pretriangulated.Triangle.mk u v w = (leftDerived F W E hE).mapTriangle.obj T := by
    rw [heu, hev, hew]
    exact (Functor.mapTriangle_obj (leftDerived F W E hE) T).symm
  exact hmk ▸ hdist

end Exact

end DerivedFunctorSubcategoryLeft

/-! ### Tag 05SE for the left derived functor -/

namespace CategoryTheory.Functor

open DerivedFunctorSubcategoryLeft

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]
  {D : Type u₃} [Category.{v₃} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive]

/-- **Stacks 05SE**, the statement for the left derived functor ("a similar result holds for
`LF`"). Let `F : C ⥤ H` be an exact functor of pre-triangulated categories, let `W` be a
saturated multiplicative system in `C` (Stacks 05Q8) compatible with the triangulation, and let
`E` be the full subcategory of `C` spanned by the objects at which the left derived functor `LF`
is defined, i.e. at which the pro-object `(s : X' ⟶ X) ↦ F(X')` on `W/X` has a value in the sense
of Stacks 05S9(2). Let `L : C ⥤ D` be a localization functor for `W`, so that `D` is a model of
`W⁻¹C`, pre-triangulated by Stacks 05R6. Then, writing `S_E = W.inverseImage E.ι` for the
morphisms of `E` lying in `W`:

1. `E` is a strictly full triangulated subcategory of `C`;
2. `LF` is an exact functor `E ⥤ H`;
3. an element of `W` with source or target in `E` has both in `E`, hence is a morphism of `E`;
4. `LF` inverts every element of `S_E`;
5. `S_E` is a saturated multiplicative system in `E` compatible with the triangulation;
6. the induced functor `S_E⁻¹E ⥤ W⁻¹C` is fully faithful and exact;
7. `LF` factors through an exact functor `S_E⁻¹E ⥤ H`;
8. if `H` is Karoubian, `E` is a saturated (thick) triangulated subcategory of `C`.

The functor `LF` is pinned by its values: `LF.obj X` is the vertex of a value cone `π X` of the
pro-object at `X` (Stacks 05S9(2)), and `LF.map f` is the unique map compatible with the
projections along every commutative square with sides in `W` (Stacks 05SA(2)). The functors of
(6) and (7) are pinned as lifts through a localization functor `LE` of `E` at `S_E`. The
statement for `RF` is `isTriangulated_and_exists_rightDerivedFunctor`. -/
@[stacks 05SE "LF: items (1)-(8) for the subcategory on which the left derived functor is \
  defined ('a similar result holds for LF'); the RF statement is \
  isTriangulated_and_exists_rightDerivedFunctor"]
public theorem isTriangulated_and_exists_leftDerivedFunctor
    (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
    (W : MorphismProperty C) (hW : W.IsSaturated) [W.IsCompatibleWithTriangulation]
    (E : ObjectProperty C) (hE : ∀ X, E X ↔ ∃ c, F.IsLeftDerivedValueAt W X c)
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift ℤ] [L.Additive] :
    letI := hW.hasLeftCalculusOfFractions
    letI := Triangulated.Localization.pretriangulated L W
    -- (1) `E` is a strictly full triangulated subcategory of `C`
    ∃ (_ : E.IsClosedUnderIsomorphisms) (_ : E.IsTriangulated),
      -- (3) an element of `W` with source or target in `E` has both in `E`
      (∀ {X Y : C} (s : X ⟶ Y), W s → (E X ↔ E Y)) ∧
      -- (8) over a Karoubian target, `E` is saturated
      (IsIdempotentComplete H → E.IsSaturated) ∧
      -- (5) `S_E` is a saturated multiplicative system compatible with the triangulation
      ∃ (hSE : (W.inverseImage E.ι).IsSaturated)
        (_ : (W.inverseImage E.ι).IsCompatibleWithTriangulation)
        (LF : E.FullSubcategory ⥤ H) (_ : LF.CommShift ℤ)
        (π : ∀ X : E.FullSubcategory, (Functor.const (W.Over ⊤ X.obj)).obj (LF.obj X) ⟶
          MorphismProperty.Over.forget W ⊤ X.obj ⋙ Over.forget X.obj ⋙ F),
        -- (2) `LF : E ⥤ H` is exact
        LF.IsTriangulated ∧
        -- its value at `X` is a value of `LF` at `X` (Stacks 05S9(2))
        (∀ X : E.FullSubcategory,
          F.IsLeftDerivedValueAt W X.obj (Cone.mk (LF.obj X) (π X))) ∧
        -- and its action on morphisms is the map of Stacks 05SA(2)
        (∀ {X Y : E.FullSubcategory} (f : X ⟶ Y) (a : W.Over ⊤ X.obj) (b : W.Over ⊤ Y.obj)
          (g : a.left ⟶ b.left), a.hom ≫ E.ι.map f = g ≫ b.hom →
            LF.map f ≫ (π Y).app b = (π X).app a ≫ F.map g) ∧
        -- (4) `LF` inverts `S_E`
        (W.inverseImage E.ι).IsInvertedBy LF ∧
        letI := hSE.hasLeftCalculusOfFractions
        ∀ (EL : Type u₄) [Category.{v₄} EL] [HasZeroObject EL] [HasShift EL ℤ] [Preadditive EL]
          [∀ n : ℤ, (shiftFunctor EL n).Additive] (LE : E.FullSubcategory ⥤ EL)
          [LE.IsLocalization (W.inverseImage E.ι)] [LE.CommShift ℤ] [LE.Additive],
          letI := Triangulated.Localization.pretriangulated LE (W.inverseImage E.ι)
          -- (6) `S_E⁻¹E ⥤ W⁻¹C` is fully faithful and exact
          (∀ (Φ : EL ⥤ D) [Lifting LE (W.inverseImage E.ι) (E.ι ⋙ L) Φ],
            Φ.Full ∧ Φ.Faithful ∧
              (letI := Functor.commShiftOfLocalization LE (W.inverseImage E.ι) ℤ (E.ι ⋙ L) Φ;
                Φ.IsTriangulated)) ∧
            -- (7) `LF` factors through an exact functor `S_E⁻¹E ⥤ H`
            ∀ (LF' : EL ⥤ H) [Lifting LE (W.inverseImage E.ι) LF LF'],
              letI := Functor.commShiftOfLocalization LE (W.inverseImage E.ι) ℤ LF LF';
              LF'.IsTriangulated := by
  let := hW.hasLeftCalculusOfFractions
  let := hW.hasRightCalculusOfFractions
  let := Triangulated.Localization.pretriangulated L W
  let := isClosedUnderIsomorphisms F W E hW hE
  let := isTriangulated F W E hW hE
  let := leftDerivedCommShift F W E hE hW
  let := leftDerived_isTriangulated F W E hE hW
  have hEW : ∀ {X Y : C} (s : X ⟶ Y), W s → (E X ↔ E Y) :=
    fun s hs => prop_iff_of_mem F W E hW hE hs
  have hSE := DerivedFunctorSubcategory.isSaturated_inverseImage_ι W E hW hEW
  refine ⟨inferInstance, inferInstance, hEW,
    fun hH => isSaturated_of_isIdempotentComplete F W E hW hE hH, hSE,
    DerivedFunctorSubcategory.isCompatibleWithTriangulation_inverseImage_ι W E hW,
    leftDerived F W E hE, inferInstance,
    fun X => (valueCone F W E hE X).π, inferInstance,
    isLeftDerivedValueAt_valueCone F W E hE,
    fun {X Y} f a b g h => isLeftDerivedMap_derivedMap F W E hE f a b g (by simpa using h),
    isInvertedBy F W E hE, ?_⟩
  intro EL _ _ _ _ _ LE _ _ _
  let := hSE.hasLeftCalculusOfFractions
  let := DerivedFunctorSubcategory.isCompatibleWithTriangulation_inverseImage_ι W E hW
  let := Triangulated.Localization.pretriangulated LE (W.inverseImage E.ι)
  let := Localization.essSurj_mapArrow LE (W.inverseImage E.ι)
  let := (Triangulated.Localization.existsUnique_pretriangulated_and_isTriangulated LE
    (W.inverseImage E.ι)).1
  refine ⟨fun Φ _ => ⟨(DerivedFunctorSubcategory.full_and_faithful_of_lifting_inverseImage_ι W E
      hSE.hasLeftCalculusOfFractions hEW L EL LE Φ).1,
    (DerivedFunctorSubcategory.full_and_faithful_of_lifting_inverseImage_ι W E
      hSE.hasLeftCalculusOfFractions hEW L EL LE Φ).2,
    Functor.isTriangulated_of_localization LE (W.inverseImage E.ι) (E.ι ⋙ L) Φ⟩,
    fun LF' _ => Functor.isTriangulated_of_localization LE (W.inverseImage E.ι)
      (leftDerived F W E hE) LF'⟩

end CategoryTheory.Functor

end
