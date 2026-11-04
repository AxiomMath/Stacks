module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedSetsToposInverseImage
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# The degree fibres of a sheaf of graded sets concentrated in one degree

`Stacks.constDeg F k` is the sheaf of sets `F` regarded as a sheaf of graded sets all of whose
local sections are declared to have degree `k`. This file computes its sheaves of degree-`i`
local sections: the degree-`k` one is `F` itself, and every other one is an initial sheaf.

## Main results

* `Stacks.constDegSelfIso`: `degreeFiberSheaf (constDeg F k) k ≅ F`.
* `Stacks.isInitial_degreeFiberSheaf_constDeg`: for `k ≠ i` the sheaf
  `degreeFiberSheaf (constDeg F k) i` is initial.
* `Stacks.hom_degreeFiberSheaf_constDeg_ext`: consequently a morphism out of that sheaf into any
  sheaf of sets is unique.

## Implementation notes

The degree-`i` fibre is *not* empty objectwise. `Stacks.SheafOfGradedSets.HasDegree S V s i` asks
that the degree of `s` agree with the image of the constant integer `i` in the constant sheaf, and
on an object `V` covered by the empty sieve the constant sheaf is a point, so there every section
has every degree. This is the phenomenon recorded in the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExtensionByZero.lean`. What is true is that such a
`V` carries no information: the sheaf of degree-`i` sections is *initial*, not empty.

The proof says this without ever mentioning the empty sieve. Write `L` for sheafification. In
presheaves, the equalizer of the two constant maps `⋆ ⇉ ℤ` at distinct integers `k ≠ i` is the
empty presheaf — `Stacks.isLimitEmptyFork`, a two-line computation, because a section of the apex
of any fork would force `k = i`. Sheafification preserves finite limits and, being a left
adjoint, initial objects, so in sheaves the equalizer of `L⋆ ⇉ Lℤ` is initial. The degree-`i`
fibre of `constDeg F k` maps to that equalizer: the condition `HasDegree V s i` does not involve
`s` at all, it says precisely that the two constants `k` and `i` have the same image in the
constant sheaf over `V`. Finally a sheaf of sets admitting a morphism to an initial object is
itself initial, because `Sheaf J (Type m)` has strict initial objects — it is finitary extensive,
which Mathlib has for sheaves of types.

The universe arguments of `Stacks.constDeg` are written out at each use. Its declared order is
`(morphisms of the site, objects of the site, sections)`, which is not the order in which
`Stacks.degreeFiberSheaf` declares its own, and leaving them to unification makes the two
sheaves of graded sets fail to unify.

## References

* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe m v u

namespace Stacks

section ConstantPresheaves

variable (C : Type u) [Category.{v} C]

/-- The presheaf constant at a one-point set. -/
abbrev constUnitPresheaf : Cᵒᵖ ⥤ Type m := (Functor.const Cᵒᵖ).obj PUnit.{m + 1}

/-- The presheaf constant at the empty set. -/
abbrev constEmptyPresheaf : Cᵒᵖ ⥤ Type m := (Functor.const Cᵒᵖ).obj PEmpty.{m + 1}

/-- The map of constant presheaves picking out the integer `j`. -/
def constDegreeMapPre (j : ℤ) :
    constUnitPresheaf.{m} C ⟶ (Functor.const Cᵒᵖ).obj (ULift.{m} ℤ) where
  app _ := ↾fun _ => ULift.up j
  naturality _ _ _ := rfl

/-- The unique map from the empty constant presheaf to the one-point constant presheaf. -/
def constEmptyToUnit : constEmptyPresheaf.{m} C ⟶ constUnitPresheaf.{m} C where
  app _ := ↾fun x => x.elim
  naturality _ _ _ := by ext x; exact x.elim

variable {C}

/-- A fork of two constant degree maps has empty sections as soon as the two degrees differ: a
section of the apex would force the two integers to be equal. -/
theorem isEmpty_fork_pt_of_ne {k i : ℤ} (h : k ≠ i)
    (t : Fork (constDegreeMapPre.{m} C k) (constDegreeMapPre.{m} C i)) (V : Cᵒᵖ) :
    IsEmpty (t.pt.obj V) :=
  ⟨fun w => h (congrArg ULift.down (congrArg (fun φ => φ.app V w) t.condition))⟩

variable (C) in
/-- The map out of the empty constant presheaf equalizes any two constant degree maps. -/
theorem constEmptyToUnit_condition (k i : ℤ) :
    constEmptyToUnit.{m} C ≫ constDegreeMapPre.{m} C k =
      constEmptyToUnit.{m} C ≫ constDegreeMapPre.{m} C i := by
  ext V x; exact x.elim

variable (C) in
/-- **The equalizer of two distinct constant degree maps of presheaves is empty.** -/
def isLimitEmptyFork {k i : ℤ} (h : k ≠ i) :
    IsLimit (Fork.ofι (constEmptyToUnit.{m} C) (constEmptyToUnit_condition.{m} C k i)) :=
  Fork.IsLimit.mk _
    (fun t =>
      { app V := ↾fun w => (isEmpty_fork_pt_of_ne h t V).elim w
        naturality _ _ _ := by ext w; exact (isEmpty_fork_pt_of_ne h t _).elim w })
    (fun t => by ext V w; exact (isEmpty_fork_pt_of_ne h t V).elim w)
    (fun t _ _ => by ext V w; exact (isEmpty_fork_pt_of_ne h t V).elim w)

end ConstantPresheaves

section Sheafified

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasSheafify J (Type m)]

variable (C J) in
/-- **The sheafification of the empty presheaf is an initial sheaf of sets.** -/
noncomputable def isInitialSheafifyEmpty :
    IsInitial ((presheafToSheaf J (Type m)).obj (constEmptyPresheaf.{m} C)) :=
  IsInitial.ofUniqueHom
    (fun G => ((sheafificationAdjunction J (Type m)).homEquiv _ G).symm
      { app _ := ↾fun x => x.elim
        naturality _ _ _ := by ext x; exact x.elim })
    (fun G g => by
      refine Eq.trans ?_ (congrArg ((sheafificationAdjunction J (Type m)).homEquiv _ G).symm
        (show (sheafificationAdjunction J (Type m)).homEquiv _ G g = _ by
          ext V x; exact x.elim))
      exact (Equiv.symm_apply_apply _ g).symm)

variable (F : Sheaf J (Type m))

/-- **The degree-`k` sections of `constDeg F k` are all of `F`.** Every local section of
`constDeg F k` has degree `k`, so the degree-`k` fibre is the whole sheaf. -/
noncomputable def constDegSelfIso (k : ℤ) :
    degreeFiberSheaf (constDeg.{v, u, m} F k) k ≅ F where
  hom := eqFiberι (constDeg.{v, u, m} F k).degree
    (constantDegreeMap (constDeg.{v, u, m} F k) k)
  inv :=
    ⟨{ app V := ↾fun s => ⟨s, constDeg_hasDegree F k V s⟩
       naturality _ _ _ := rfl }⟩
  hom_inv_id := by apply Sheaf.hom_ext; ext V s; exact Subtype.ext rfl
  inv_hom_id := by apply Sheaf.hom_ext; ext V s; rfl

/-- The forward map of `constDegSelfIso F k` sends a degree-`k` local section to its underlying
section of `F`. -/
@[simp]
theorem constDegSelfIso_hom_app (k : ℤ) (V : Cᵒᵖ)
    (s : (degreeFiberSheaf (constDeg.{v, u, m} F k) k).obj.obj V) :
    (constDegSelfIso F k).hom.hom.app V s = s.1 :=
  rfl

/-- The inverse map of `constDegSelfIso F k` sends a local section of `F` to the degree-`k`
section with the same underlying section. -/
@[simp]
theorem constDegSelfIso_inv_app (k : ℤ) (V : Cᵒᵖ) (s : F.obj.obj V) :
    ((constDegSelfIso F k).inv.hom.app V s).1 = s :=
  rfl

/-- The presheaf map from a degree fibre of `constDeg F k` to the one-point constant presheaf. -/
def constDegFiberToUnitPre (k i : ℤ) :
    (degreeFiberSheaf (constDeg.{v, u, m} F k) i).obj ⟶ constUnitPresheaf.{m} C where
  app _ := ↾fun _ => PUnit.unit
  naturality _ _ _ := rfl

/-- The degree-`i` fibre of `constDeg F k` maps to the sheafified one-point presheaf. -/
noncomputable def constDegFiberToUnit (k i : ℤ) :
    degreeFiberSheaf (constDeg.{v, u, m} F k) i ⟶
      (presheafToSheaf J (Type m)).obj (constUnitPresheaf.{m} C) :=
  ⟨constDegFiberToUnitPre F k i ≫ toSheafify J (constUnitPresheaf.{m} C)⟩

/-- The map to the sheafified one-point presheaf equalizes the two constant degree maps: a local
section of degree `i` of `constDeg F k` witnesses that the constants `k` and `i` have the same
image in the constant sheaf over that object. -/
theorem constDegFiberToUnit_condition (k i : ℤ) :
    constDegFiberToUnit F k i ≫
        (presheafToSheaf J (Type m)).map (constDegreeMapPre.{m} C k) =
      constDegFiberToUnit F k i ≫
        (presheafToSheaf J (Type m)).map (constDegreeMapPre.{m} C i) := by
  apply Sheaf.hom_ext
  ext V s
  have h (j : ℤ) := congrArg (fun φ => φ.app V PUnit.unit)
    (toSheafify_naturality J (constDegreeMapPre.{m} C j))
  exact ((h k).symm.trans s.2).trans (h i)

/-- **For `k ≠ i` the sheaf of degree-`i` local sections of `constDeg F k` is initial.** -/
noncomputable def isInitial_degreeFiberSheaf_constDeg {k i : ℤ} (h : k ≠ i) :
    IsInitial (degreeFiberSheaf (constDeg.{v, u, m} F k) i) :=
  IsInitial.ofStrict
    ((isLimitForkMapOfIsLimit (presheafToSheaf J (Type m))
          (constEmptyToUnit_condition.{m} C k i) (isLimitEmptyFork.{m} C h)).lift
      (Fork.ofι (constDegFiberToUnit F k i) (constDegFiberToUnit_condition F k i)))
    (isInitialSheafifyEmpty C J)

/-- Two morphisms out of a degree-`i` fibre of `constDeg F k` with `k ≠ i` agree. -/
theorem hom_degreeFiberSheaf_constDeg_ext {k i : ℤ} (h : k ≠ i) {G : Sheaf J (Type m)}
    (a b : degreeFiberSheaf (constDeg.{v, u, m} F k) i ⟶ G) : a = b :=
  (isInitial_degreeFiberSheaf_constDeg F h).hom_ext a b

end Sheafified

end Stacks

end
