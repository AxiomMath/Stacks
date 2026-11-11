module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
public import StacksFrontier.CategoryTheory.Localization.Saturated.Defs

/-!
# Derived functors on morphisms, on the multiplicative system, and everywhere-definedness

This file collects the formalizations of [Stacks, Tag 05SA], [Stacks, Tag 05SB],
[Stacks, Tag 05T1].

## References

* [Stacks, Tag 05SA](https://stacks.math.columbia.edu/tag/05SA)
* [Stacks, Tag 05SB](https://stacks.math.columbia.edu/tag/05SB)
* [Stacks, Tag 05T1](https://stacks.math.columbia.edu/tag/05T1)
-/

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This is a formalization of **Stacks project, Lemma 13.14.3 (tag 05SA)**, in the
setting of Situation 13.14.1 (tag 05S8):

> `F : D ⥤ D'` is an exact functor of triangulated categories, and `S` is a
> saturated multiplicative system in `D` compatible with the triangulated
> structure.

The *compatibility with the triangulated structure* and even *saturation* are not
used in the construction of the main lemma; only the relevant one-sided
calculus-of-fractions axioms (MS1)-(MS3) and the chosen essential-constancy data
are used. We therefore work with a general category `C` (playing the role of
`D`), a general category `D'`, a functor `F : C ⥤ D'`, and a morphism property
`S` satisfying the relevant one-sided calculus of fractions.

The lemma asserts that, when the right derived functor `RF` is defined at two
objects `X` and `Y` (i.e. the ind-object `(s : X ⟶ X') ↦ F X'` over the filtered
category `X/S` is essentially constant), then any morphism `f : X ⟶ Y` induces a
unique morphism `RF f : RF X ⟶ RF Y` compatible with all the structural cocone
maps. The dual statement holds for the left derived functor `LF`.
-/

open CategoryTheory CategoryTheory.MorphismProperty Limits

namespace StacksDerivedFunctor

variable {C : Type*} [Category C]

/-! ## Definition 1 (Multiplicative system; tag 04VC)

A multiplicative system is a `MorphismProperty` satisfying (MS1), (MS2), (MS3).
That is `S.HasLeftCalculusOfFractions` together with `S.HasRightCalculusOfFractions`,
each of which already carries (MS1) through its `IsMultiplicative` parent. The right
derived functor below uses only the left calculus and the left derived functor only
the right one, so the two are assumed separately.

Throughout, recall that in Lean diagrammatic order `f ≫ g` denotes "`g` after `f`",
i.e. `g ∘ f` in classical notation. We keep each square exactly as drawn in the
source; the commuting condition of the (MS2) square is written `g ≫ s = t ≫ h` in
diagrammatic order. -/

/-! ## Saturation and compatibility with the triangulated structure (tags 05Q8, 05R2)

Situation 13.14.1 further asks that `S` be saturated and compatible with the
triangulated structure. Both notions already exist: `MorphismProperty.IsSaturated`
(tag 05Q8) bundles the two calculi of fractions together with MS4, and
`MorphismProperty.IsCompatibleWithTriangulation` (tag 05R2) bundles stability under
shifts with the completion property for distinguished triangles. Neither is needed
for the construction below; they enter only in the tagged statements, which record
the full situation. -/

/-! ## Definition 2 (The categories `X/S` and `S/X`; tags 05Q0, 05Q4)

We use Mathlib's canonical `S.Under ⊤ X` and `S.Over ⊤ X`: the structural
arrow must lie in `S`, while morphisms in the comma category are unrestricted. -/

variable (S : MorphismProperty C)

/-! ## `RF` and `LF` defined at `X`; the value (tag 05S9)

These are `CategoryTheory.Functor.IsRightDerivedValueAt` and
`CategoryTheory.Functor.IsLeftDerivedValueAt` (Tag 05S9): a value of `RF` at `X` is a cocone `c`
on the ind-object `(s : X ⟶ X') ↦ F(X')` over `S.Under ⊤ X` satisfying the two clauses of
essential constancy of Tag 05PU, its summit `c.pt` is `RF(X)`, and its legs
`c.ι.app s : F(X') ⟶ RF(X)` are the structural maps `c_s`. Dually for `LF`. -/

/-! ## Ore squares, and naturality of the structural cocone and cone -/

/-- The Ore condition of a left calculus of fractions, in the (MS2) square shape used
below: a span `g`, `t` with `t ∈ S` completes to a commuting square whose right
vertical lies in `S`. -/
lemma exists_ore_square_left [S.HasLeftCalculusOfFractions] {X Y Z : C} (g : X ⟶ Y)
    (t : X ⟶ Z) (ht : S t) :
    ∃ (W : C) (s : Y ⟶ W) (h : Z ⟶ W), S s ∧ g ≫ s = t ≫ h :=
  let φ : S.RightFraction Z Y := { s := t, hs := ht, f := g }
  ⟨_, φ.leftFraction.s, φ.leftFraction.f, φ.leftFraction.hs, φ.leftFraction_fac⟩

/-- The Ore condition of a right calculus of fractions: a cospan `s`, `h` with `s ∈ S`
completes to a commuting square whose left vertical lies in `S`. -/
lemma exists_ore_square_right [S.HasRightCalculusOfFractions] {Y Z W : C} (s : Y ⟶ W)
    (h : Z ⟶ W) (hs : S s) :
    ∃ (X : C) (g : X ⟶ Y) (t : X ⟶ Z), S t ∧ g ≫ s = t ≫ h :=
  let φ : S.LeftFraction Z Y := { f := h, s := s, hs := hs }
  ⟨_, φ.rightFraction.f, φ.rightFraction.s, φ.rightFraction.hs, φ.rightFraction_fac.symm⟩

/-- Cocone naturality for the ind-object diagram, packaged for an explicit
underlying morphism `a` with `s.hom ≫ a = t.hom`. -/
lemma underS_cocone_nat {Y : C} {D' : Type*} [Category D'] (F : C ⥤ D')
    (c : Cocone (MorphismProperty.Under.forget S ⊤ Y ⋙ Under.forget Y ⋙ F)) {s t : S.Under ⊤ Y}
    (a : s.right ⟶ t.right) (ha : s.hom ≫ a = t.hom) :
    F.map a ≫ c.ι.app t = c.ι.app s := by
  have := c.ι.naturality (Under.homMk a ha)
  simpa using this

/-- Cone naturality for the pro-object diagram, packaged for an explicit
underlying morphism `a` with `a ≫ t.hom = s.hom`. -/
lemma overS_cone_nat {Y : C} {D' : Type*} [Category D'] (F : C ⥤ D')
    (c : Cone (MorphismProperty.Over.forget S ⊤ Y ⋙ Over.forget Y ⋙ F)) {s t : S.Over ⊤ Y}
    (a : s.left ⟶ t.left) (ha : a ≫ t.hom = s.hom) :
    c.π.app s ≫ F.map a = c.π.app t := by
  have := c.π.naturality (Over.homMk a ha)
  simpa using this.symm

/-- **Independence lemma (RF).** With a cocone `c` on the ind-object diagram of
`Y`, and a multiplicative system `S`, the value `F f' ≫ c_{s'}` of a square
over a fixed `s : X ⟶ X'` (in `S`) does not depend on the chosen square.

Mathematical argument: given two completing squares for the same `s`, with
right verticals `s'₁, s'₂ ∈ S` and diagonals `f'₁, f'₂`, use (MS2-left) to find
`σ₁, σ₂` (with `σ₁ ∈ S`) coequalizing `s'₁, s'₂` into a common `τ = s'₁ ≫ σ₁`,
so both squares push forward to squares over `τ`. The two pushed-forward
diagonals `f'₁ ≫ σ₁` and `f'₂ ≫ σ₂` then satisfy `s ≫ (f'₁ ≫ σ₁) = f ≫ τ =
s ≫ (f'₂ ≫ σ₂)`; applying (MS3-left) yields `w ∈ S` with
`(f'₁ ≫ σ₁) ≫ w = (f'₂ ≫ σ₂) ≫ w`, and cocone naturality (the legs are
compatible with the transition morphisms `σᵢ` and `w`) transports both values
to the common object `τ ≫ w`, where the two coincide by the (MS3-left)
equality. -/
lemma indep_RF {D' : Type*} [Category D'] (F : C ⥤ D')
    [S.HasLeftCalculusOfFractions] {X Y : C} (f : X ⟶ Y)
    (c : Cocone (MorphismProperty.Under.forget S ⊤ Y ⋙ Under.forget Y ⋙ F))
    {X' : C} (s : X ⟶ X') (hs : S s)
    {Y₁ Y₂ : C} (s'₁ : Y ⟶ Y₁) (s'₂ : Y ⟶ Y₂) (hs'₁ : S s'₁) (hs'₂ : S s'₂)
    (f'₁ : X' ⟶ Y₁) (f'₂ : X' ⟶ Y₂)
    (hsq₁ : f ≫ s'₁ = s ≫ f'₁) (hsq₂ : f ≫ s'₂ = s ≫ f'₂) :
    F.map f'₁ ≫ c.ι.app (Under.mk ⊤ s'₁ hs'₁) = F.map f'₂ ≫ c.ι.app (Under.mk ⊤ s'₂ hs'₂) := by
  -- Step 1: connect s'₁ and s'₂ via MS2-left.
  obtain ⟨V, σ₁, σ₂, hσ₁, hcomm⟩ := exists_ore_square_left S s'₁ s'₂ hs'₂
  -- hcomm : s'₁ ≫ σ₁ = s'₂ ≫ σ₂
  set τ : Y ⟶ V := s'₁ ≫ σ₁ with hτ
  have hτmem : S τ := S.comp_mem _ _ hs'₁ hσ₁
  -- cocone naturality, pushed forward along `a`
  have push : ∀ (s t : S.Under ⊤ Y) {Z : C} (p : Z ⟶ s.right) (a : s.right ⟶ t.right),
      s.hom ≫ a = t.hom → F.map p ≫ c.ι.app s = F.map (p ≫ a) ≫ c.ι.app t :=
    fun s t _ p a ha => by rw [F.map_comp, Category.assoc, underS_cocone_nat S F c a ha]
  -- Step 2: s ≫ (f'₁ ≫ σ₁) = s ≫ (f'₂ ≫ σ₂) = f ≫ τ, then MS3-left.
  have hp : s ≫ (f'₁ ≫ σ₁) = s ≫ (f'₂ ≫ σ₂) := by
    have e1 : s ≫ (f'₁ ≫ σ₁) = f ≫ τ := by
      rw [← Category.assoc, ← hsq₁, Category.assoc]
    have e2 : s ≫ (f'₂ ≫ σ₂) = f ≫ τ := by
      rw [← Category.assoc, ← hsq₂, Category.assoc, ← hcomm]
    rw [e1, e2]
  obtain ⟨U, w, hw, hpq⟩ :=
    MorphismProperty.HasLeftCalculusOfFractions.ext (W := S) (f'₁ ≫ σ₁) (f'₂ ≫ σ₂) s hs hp
  -- hpq : (f'₁ ≫ σ₁) ≫ w = (f'₂ ≫ σ₂) ≫ w
  have hτwmem : S (τ ≫ w) := S.comp_mem _ _ hτmem hw
  calc F.map f'₁ ≫ c.ι.app (Under.mk ⊤ s'₁ hs'₁)
      = F.map (f'₁ ≫ σ₁) ≫ c.ι.app (Under.mk ⊤ τ hτmem) :=
        push (Under.mk ⊤ s'₁ hs'₁) (Under.mk ⊤ τ hτmem) f'₁ σ₁ rfl
    _ = F.map ((f'₁ ≫ σ₁) ≫ w) ≫ c.ι.app (Under.mk ⊤ (τ ≫ w) hτwmem) :=
        push (Under.mk ⊤ τ hτmem) (Under.mk ⊤ (τ ≫ w) hτwmem) _ w rfl
    _ = F.map ((f'₂ ≫ σ₂) ≫ w) ≫ c.ι.app (Under.mk ⊤ (τ ≫ w) hτwmem) := by rw [hpq]
    _ = F.map (f'₂ ≫ σ₂) ≫ c.ι.app (Under.mk ⊤ τ hτmem) :=
        (push (Under.mk ⊤ τ hτmem) (Under.mk ⊤ (τ ≫ w) hτwmem) _ w rfl).symm
    _ = F.map f'₂ ≫ c.ι.app (Under.mk ⊤ s'₂ hs'₂) :=
        (push (Under.mk ⊤ s'₂ hs'₂) (Under.mk ⊤ τ hτmem) f'₂ σ₂ hcomm.symm).symm

/-- **Independence lemma (LF).** With a cone `c` on the pro-object diagram of
`X`, and a multiplicative system `S`, the value `c_s ≫ F f'` of a square over a
fixed `s' : Y' ⟶ Y` (in `S`) does not depend on the chosen square.

Mathematical argument: formal dual of `indep_RF`. Given two completing squares
for the same `s'`, with left verticals `s₁, s₂ ∈ S` and diagonals `f'₁, f'₂`,
use (MS2-right) to find `g, t` (with `t ∈ S`) equalizing `s₁, s₂` into a common
`τ = g ≫ s₁`. The pulled-back diagonals `g ≫ f'₁` and `t ≫ f'₂` satisfy
`(g ≫ f'₁) ≫ s' = τ ≫ f = (t ≫ f'₂) ≫ s'`; (MS3-right) yields `w ∈ S` with
`w ≫ (g ≫ f'₁) = w ≫ (t ≫ f'₂)`, and cone naturality transports both values to
the common object `w ≫ τ`, where they coincide. -/
lemma indep_LF {D' : Type*} [Category D'] (F : C ⥤ D')
    [S.HasRightCalculusOfFractions] {X Y : C} (f : X ⟶ Y)
    (c : Cone (MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F))
    {Y' : C} (s' : Y' ⟶ Y) (hs' : S s')
    {X₁ X₂ : C} (s₁ : X₁ ⟶ X) (s₂ : X₂ ⟶ X) (hs₁ : S s₁) (hs₂ : S s₂)
    (f'₁ : X₁ ⟶ Y') (f'₂ : X₂ ⟶ Y')
    (hsq₁ : s₁ ≫ f = f'₁ ≫ s') (hsq₂ : s₂ ≫ f = f'₂ ≫ s') :
    c.π.app (Over.mk ⊤ s₁ hs₁) ≫ F.map f'₁ = c.π.app (Over.mk ⊤ s₂ hs₂) ≫ F.map f'₂ := by
  -- Step 1: connect s₁ and s₂ via MS2-right.
  obtain ⟨V, g, t, ht, hcomm⟩ := exists_ore_square_right S s₁ s₂ hs₁
  -- hcomm : g ≫ s₁ = t ≫ s₂
  set τ : V ⟶ X := g ≫ s₁ with hτ
  have hτmem : S τ := by rw [hcomm]; exact S.comp_mem _ _ ht hs₂
  -- cone naturality, pulled back along `a`
  have push : ∀ (s t : S.Over ⊤ X) {Z : C} (p : t.left ⟶ Z) (a : s.left ⟶ t.left),
      a ≫ t.hom = s.hom → c.π.app s ≫ F.map (a ≫ p) = c.π.app t ≫ F.map p :=
    fun s t _ p a ha => by rw [F.map_comp, ← Category.assoc, overS_cone_nat S F c a ha]
  -- Step 2: (g ≫ f'₁) ≫ s' = (t ≫ f'₂) ≫ s' = τ ≫ f, then MS3-right.
  have hp : (g ≫ f'₁) ≫ s' = (t ≫ f'₂) ≫ s' := by
    have e1 : (g ≫ f'₁) ≫ s' = τ ≫ f := by
      rw [Category.assoc, ← hsq₁, ← Category.assoc]
    have e2 : (t ≫ f'₂) ≫ s' = τ ≫ f := by
      rw [Category.assoc, ← hsq₂, ← Category.assoc, ← hcomm]
    rw [e1, e2]
  obtain ⟨Z, w, hw, hpq⟩ :=
    MorphismProperty.HasRightCalculusOfFractions.ext (W := S) (g ≫ f'₁) (t ≫ f'₂) s' hs' hp
  -- hpq : w ≫ (g ≫ f'₁) = w ≫ (t ≫ f'₂)
  have hwτmem : S (w ≫ τ) := S.comp_mem _ _ hw hτmem
  calc c.π.app (Over.mk ⊤ s₁ hs₁) ≫ F.map f'₁
      = c.π.app (Over.mk ⊤ τ hτmem) ≫ F.map (g ≫ f'₁) :=
        (push (Over.mk ⊤ τ hτmem) (Over.mk ⊤ s₁ hs₁) f'₁ g rfl).symm
    _ = c.π.app (Over.mk ⊤ (w ≫ τ) hwτmem) ≫ F.map (w ≫ (g ≫ f'₁)) :=
        (push (Over.mk ⊤ (w ≫ τ) hwτmem) (Over.mk ⊤ τ hτmem) _ w rfl).symm
    _ = c.π.app (Over.mk ⊤ (w ≫ τ) hwτmem) ≫ F.map (w ≫ (t ≫ f'₂)) := by rw [hpq]
    _ = c.π.app (Over.mk ⊤ τ hτmem) ≫ F.map (t ≫ f'₂) :=
        push (Over.mk ⊤ (w ≫ τ) hwτmem) (Over.mk ⊤ τ hτmem) _ w rfl
    _ = c.π.app (Over.mk ⊤ s₂ hs₂) ≫ F.map f'₂ :=
        push (Over.mk ⊤ τ hτmem) (Over.mk ⊤ s₂ hs₂) f'₂ t hcomm.symm

/-! ## Main Statement(s): Stacks Lemma 13.14.3 (tag 05SA) -/

/-- **Statement 1 (Right derived functor).** Assume `S` is a multiplicative
system and that `RF` is defined at `X` and at `Y`. Then for every morphism
`f : X ⟶ Y` there is a *unique* morphism `RF f : RF X ⟶ RF Y` such that for every
commutative square
```
  X --s--> X'
  |        |
  f        f'
  |        |
  v        v
  Y --s'-> Y'
```
with `s ∈ Ob(X/S)`, `s' ∈ Ob(Y/S)` and `f ≫ s' = s ≫ f'`, the right-hand square
```
  F X' --c_s--> RF X
   |             |
  F f'          RF f
   |             |
   v             v
  F Y' --c_s'-> RF Y
```
commutes, i.e. `c_s ≫ RF f = F f' ≫ c_{s'}`. -/
theorem main_RF_map_of_leftCalculus
    {D' : Type*} [Category D'] (F : C ⥤ D') (S : MorphismProperty C)
    [S.HasLeftCalculusOfFractions]
    {X Y : C} (f : X ⟶ Y)
    {cX : Cocone (MorphismProperty.Under.forget S ⊤ X ⋙ Under.forget X ⋙ F)}
    (cY : Cocone (MorphismProperty.Under.forget S ⊤ Y ⋙ Under.forget Y ⋙ F))
    (hX : F.IsRightDerivedValueAt S X cX) :
    ∃! φ : cX.pt ⟶ cY.pt,
      ∀ (X' Y' : C) (s : X ⟶ X') (s' : Y ⟶ Y') (f' : X' ⟶ Y')
        (hs : S s) (hs' : S s') (_ : f ≫ s' = s ≫ f'),
        cX.ι.app (Under.mk ⊤ s hs) ≫ φ = F.map f' ≫ cY.ι.app (Under.mk ⊤ s' hs') := by
  -- Essential constancy on `X` provides `iX`, `rX`, and Fact A / Fact B.
  obtain ⟨iX, rX, hretr, hB⟩ := hX
  -- A square over the canonical object `iX` (via MS2-left at `g = f`, `t = iX.hom`).
  obtain ⟨YI, sI, fI, hsI, hsqI⟩ := exists_ore_square_left S f iX.hom iX.prop
  -- Define the candidate morphism.
  refine ⟨rX ≫ F.map fI ≫ cY.ι.app (Under.mk ⊤ sI hsI), ?_, ?_⟩
  · -- Existence: the property holds for every square.
    intro X' Y' s s' f' hs hs' hsq
    -- Fact B at the object `⟨X', s⟩`.
    obtain ⟨k, v, u, hBk⟩ := hB (Under.mk ⊤ s hs)
    -- A square over `k.hom : X ⟶ k.right` (MS2-left at `g = f`, `t = k.hom`).
    obtain ⟨YK, sK, fK, hsK, hsqK⟩ := exists_ore_square_left S f k.hom k.prop
    -- `u : iX ⟶ k`, so `iX.hom ≫ u.right = k.hom`.
    have hu : iX.hom ≫ u.right = k.hom := StructuredArrow.w u.hom
    -- `v : ⟨X',s⟩ ⟶ k`, so `s ≫ v.right = k.hom`.
    have hv : s ≫ v.right = k.hom := StructuredArrow.w v.hom
    -- Identify the value at `iX` with a value at `k` (cocone-compat + indep).
    have sqK : ∀ {Z : C} (z : X ⟶ Z) (m : Z ⟶ k.right), z ≫ m = k.hom → f ≫ sK = z ≫ m ≫ fK :=
      fun z m h => by rw [hsqK, ← Category.assoc, h]
    have step1 : F.map fI ≫ cY.ι.app (Under.mk ⊤ sI hsI)
        = F.map u.right ≫ F.map fK ≫ cY.ι.app (Under.mk ⊤ sK hsK) := by
      rw [← Category.assoc, ← F.map_comp]
      exact indep_RF S F f cY iX.hom iX.prop sI sK hsI hsK fI (u.right ≫ fK)
        hsqI (sqK _ _ hu)
    -- Now compute the left-hand side.
    have hBk' : F.map v.right = cX.ι.app (Under.mk ⊤ s hs) ≫ rX ≫ F.map u.right := hBk
    calc cX.ι.app (Under.mk ⊤ s hs) ≫ rX ≫ F.map fI ≫ cY.ι.app (Under.mk ⊤ sI hsI)
        = cX.ι.app (Under.mk ⊤ s hs) ≫ rX ≫ F.map u.right ≫ F.map fK ≫
            cY.ι.app (Under.mk ⊤ sK hsK) := by
          rw [step1]
      _ = (cX.ι.app (Under.mk ⊤ s hs) ≫ rX ≫ F.map u.right) ≫ F.map fK ≫
            cY.ι.app (Under.mk ⊤ sK hsK) := by
          rw [Category.assoc, Category.assoc]
      _ = F.map v.right ≫ F.map fK ≫ cY.ι.app (Under.mk ⊤ sK hsK) := by rw [hBk']
      _ = F.map (v.right ≫ fK) ≫ cY.ι.app (Under.mk ⊤ sK hsK) := by
          rw [F.map_comp, Category.assoc]
      _ = F.map f' ≫ cY.ι.app (Under.mk ⊤ s' hs') :=
          indep_RF S F f cY s hs sK s' hsK hs' (v.right ≫ fK) f' (sqK _ _ hv) hsq
  · -- Uniqueness.
    intro φ' hφ'
    -- For every object `s` of `X/S`, `cX.ι.app s ≫ φ' = ψ_s`.
    -- Use Fact A: `rX ≫ cX.ι.app iX = 𝟙`.
    have hψiX : cX.ι.app iX ≫ φ' = F.map fI ≫ cY.ι.app (Under.mk ⊤ sI hsI) :=
      hφ' iX.right YI iX.hom sI fI iX.prop hsI hsqI
    rw [← hψiX, ← Category.assoc, hretr, Category.id_comp]

/-- **Statement 2 (Left derived functor).** Assume `S` is a multiplicative
system and that `LF` is defined at `X` and at `Y`. Then for every morphism
`f : X ⟶ Y` there is a *unique* morphism `LF f : LF X ⟶ LF Y` such that for every
commutative square
```
  X' --s--> X
  |         |
  f'        f
  |         |
  v         v
  Y' --s'-> Y
```
with `s ∈ Ob(S/X)`, `s' ∈ Ob(S/Y)` and `s ≫ f = f' ≫ s'`, the left-hand square
```
  LF X --c_s--> F X'
   |             |
  LF f          F f'
   |             |
   v             v
  LF Y --c_s'-> F Y'
```
commutes, i.e. `LF f ≫ c_{s'} = c_s ≫ F f'`. -/
theorem main_LF_map_of_rightCalculus
    {D' : Type*} [Category D'] (F : C ⥤ D') (S : MorphismProperty C)
    [S.HasRightCalculusOfFractions]
    {X Y : C} (f : X ⟶ Y)
    (cX : Cone (MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F))
    {cY : Cone (MorphismProperty.Over.forget S ⊤ Y ⋙ Over.forget Y ⋙ F)}
    (hY : F.IsLeftDerivedValueAt S Y cY) :
    ∃! φ : cX.pt ⟶ cY.pt,
      ∀ (X' Y' : C) (s : X' ⟶ X) (s' : Y' ⟶ Y) (f' : X' ⟶ Y')
        (hs : S s) (hs' : S s') (_ : s ≫ f = f' ≫ s'),
        φ ≫ cY.π.app (Over.mk ⊤ s' hs') = cX.π.app (Over.mk ⊤ s hs) ≫ F.map f' := by
  -- Essential constancy on `Y` provides `iY`, `rY`, and Fact A / Fact B.
  obtain ⟨iY, rY, hretr, hB⟩ := hY
  -- A square over the canonical object `iY` (via MS2-right on the cospan
  -- `iY.left →[iY.hom] Y ←[f] X`).
  obtain ⟨XI, gI, tI, htI, hsqI⟩ := exists_ore_square_right S iY.hom f iY.prop
  -- hsqI : gI ≫ iY.hom = tI ≫ f
  refine ⟨(cX.π.app (Over.mk ⊤ tI htI) ≫ F.map gI) ≫ rY, ?_, ?_⟩
  · -- Existence.
    intro X' Y' s s' f' hs hs' hsq
    -- Fact B at the object `⟨Y', s'⟩`.
    obtain ⟨k, v, u, hBk⟩ := hB (Over.mk ⊤ s' hs')
    -- A square over `k.hom` (MS2-right on the cospan
    -- `k.left →[k.hom] Y ←[f] X`).
    obtain ⟨XK, gK, tK, htK, hsqK⟩ := exists_ore_square_right S k.hom f k.prop
    -- hsqK : gK ≫ k.hom = tK ≫ f
    have hu : u.left ≫ iY.hom = k.hom := CostructuredArrow.w u.hom
    have hv : v.left ≫ s' = k.hom := CostructuredArrow.w v.hom
    -- Identify the value at `iY` with a value at `k` (cone-compat + indep).
    have sqK : ∀ {Z : C} (m : k.left ⟶ Z) (z : Z ⟶ Y), m ≫ z = k.hom → tK ≫ f = (gK ≫ m) ≫ z :=
      fun m z h => by rw [Category.assoc, h, hsqK]
    have step1 : cX.π.app (Over.mk ⊤ tI htI) ≫ F.map gI
        = cX.π.app (Over.mk ⊤ tK htK) ≫ F.map (gK ≫ u.left) :=
      indep_LF S F f cX iY.hom iY.prop tI tK htI htK gI (gK ≫ u.left) hsqI.symm
        (sqK _ _ hu)
    have hBk' : F.map v.left = F.map u.left ≫ rY ≫ cY.π.app (Over.mk ⊤ s' hs') := hBk
    calc ((cX.π.app (Over.mk ⊤ tI htI) ≫ F.map gI) ≫ rY) ≫ cY.π.app (Over.mk ⊤ s' hs')
        = (cX.π.app (Over.mk ⊤ tI htI) ≫ F.map gI) ≫ rY ≫ cY.π.app (Over.mk ⊤ s' hs') := by
          rw [Category.assoc]
      _ = (cX.π.app (Over.mk ⊤ tK htK) ≫ F.map (gK ≫ u.left)) ≫ rY ≫
            cY.π.app (Over.mk ⊤ s' hs') := by
          rw [step1]
      _ = cX.π.app (Over.mk ⊤ tK htK) ≫ F.map gK ≫
            (F.map u.left ≫ rY ≫ cY.π.app (Over.mk ⊤ s' hs')) := by
          simp only [F.map_comp, Category.assoc]
      _ = cX.π.app (Over.mk ⊤ tK htK) ≫ F.map gK ≫ F.map v.left := by rw [← hBk']
      _ = cX.π.app (Over.mk ⊤ tK htK) ≫ F.map (gK ≫ v.left) := by
          rw [F.map_comp]
      _ = cX.π.app (Over.mk ⊤ s hs) ≫ F.map f' :=
          indep_LF S F f cX s' hs' tK s htK hs (gK ≫ v.left) f' (sqK _ _ hv) hsq
  · -- Uniqueness.
    intro φ' hφ'
    have hψiY : φ' ≫ cY.π.app iY = cX.π.app (Over.mk ⊤ tI htI) ≫ F.map gI :=
      hφ' XI iY.left tI iY.hom gI htI iY.prop (by rw [hsqI])
    rw [← hψiY, Category.assoc, hretr, Category.comp_id]

/-! ## The induced maps `RF(f)` and `LF(f)`: Stacks Lemma 13.14.3 (tag 05SA)

A morphism `f : X ⟶ Y` of `C` induces a morphism `RF(f)` between the values of `RF` at `X` and at
`Y`, namely the unique morphism compatible with all the structural cocone maps, and dually a
morphism `LF(f)` between the values of `LF`, compatible with all the structural cone maps. -/

section InducedMaps

variable {D' : Type*} [Category D'] (F : C ⥤ D') {X Y : C}
variable {cX : Cocone (MorphismProperty.Under.forget S ⊤ X ⋙ Under.forget X ⋙ F)}
  {cY : Cocone (MorphismProperty.Under.forget S ⊤ Y ⋙ Under.forget Y ⋙ F)}
  {dX : Cone (MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F)}
  {dY : Cone (MorphismProperty.Over.forget S ⊤ Y ⋙ Over.forget Y ⋙ F)}

/-- The morphism `RF(f) : RF X ⟶ RF Y` induced by `f : X ⟶ Y` between two values, characterised
by `rightDerivedMap_spec` together with `rightDerivedMap_unique`. -/
@[stacks 05SA "(1), the morphism itself; `rightDerivedMap_spec` is its defining property and
`rightDerivedMap_unique` is its uniqueness"]
noncomputable def rightDerivedMap [S.HasLeftCalculusOfFractions]
    (hX : F.IsRightDerivedValueAt S X cX) (_hY : F.IsRightDerivedValueAt S Y cY) (f : X ⟶ Y) :
    cX.pt ⟶ cY.pt :=
  (main_RF_map_of_leftCalculus F S f cY hX).choose

/-- `RF(f)` makes each square of Statement 1 commute. -/
@[stacks 05SA "(1), the defining property of `rightDerivedMap`"]
lemma rightDerivedMap_spec [S.HasLeftCalculusOfFractions]
    (hX : F.IsRightDerivedValueAt S X cX) (hY : F.IsRightDerivedValueAt S Y cY) (f : X ⟶ Y)
    (X' Y' : C) (s : X ⟶ X') (s' : Y ⟶ Y') (f' : X' ⟶ Y') (hs : S s) (hs' : S s')
    (hsq : f ≫ s' = s ≫ f') :
    cX.ι.app (Under.mk ⊤ s hs) ≫ rightDerivedMap S F hX hY f =
      F.map f' ≫ cY.ι.app (Under.mk ⊤ s' hs') :=
  (main_RF_map_of_leftCalculus F S f cY hX).choose_spec.left X' Y' s s' f' hs hs' hsq

/-- `RF(f)` is the only morphism with that property. -/
@[stacks 05SA "(1), uniqueness of `rightDerivedMap`"]
lemma rightDerivedMap_unique [S.HasLeftCalculusOfFractions]
    (hX : F.IsRightDerivedValueAt S X cX) (hY : F.IsRightDerivedValueAt S Y cY) (f : X ⟶ Y)
    (φ : cX.pt ⟶ cY.pt)
    (hφ : ∀ (X' Y' : C) (s : X ⟶ X') (s' : Y ⟶ Y') (f' : X' ⟶ Y')
      (hs : S s) (hs' : S s') (_ : f ≫ s' = s ≫ f'),
      cX.ι.app (Under.mk ⊤ s hs) ≫ φ = F.map f' ≫ cY.ι.app (Under.mk ⊤ s' hs')) :
    φ = rightDerivedMap S F hX hY f :=
  (main_RF_map_of_leftCalculus F S f cY hX).choose_spec.right φ hφ

/-- The morphism `LF(f) : LF X ⟶ LF Y` induced by `f : X ⟶ Y` between two values, characterised
by `leftDerivedMap_spec` together with `leftDerivedMap_unique`. -/
@[stacks 05SA "(2), the morphism itself; `leftDerivedMap_spec` is its defining property and
`leftDerivedMap_unique` is its uniqueness"]
noncomputable def leftDerivedMap [S.HasRightCalculusOfFractions]
    (_hX : F.IsLeftDerivedValueAt S X dX) (hY : F.IsLeftDerivedValueAt S Y dY) (f : X ⟶ Y) :
    dX.pt ⟶ dY.pt :=
  (main_LF_map_of_rightCalculus F S f dX hY).choose

/-- `LF(f)` makes each square of Statement 2 commute. -/
@[stacks 05SA "(2), the defining property of `leftDerivedMap`"]
lemma leftDerivedMap_spec [S.HasRightCalculusOfFractions]
    (hX : F.IsLeftDerivedValueAt S X dX) (hY : F.IsLeftDerivedValueAt S Y dY) (f : X ⟶ Y)
    (X' Y' : C) (s : X' ⟶ X) (s' : Y' ⟶ Y) (f' : X' ⟶ Y') (hs : S s) (hs' : S s')
    (hsq : s ≫ f = f' ≫ s') :
    leftDerivedMap S F hX hY f ≫ dY.π.app (Over.mk ⊤ s' hs') =
      dX.π.app (Over.mk ⊤ s hs) ≫ F.map f' :=
  (main_LF_map_of_rightCalculus F S f dX hY).choose_spec.left X' Y' s s' f' hs hs' hsq

/-- `LF(f)` is the only morphism with that property. -/
@[stacks 05SA "(2), uniqueness of `leftDerivedMap`"]
lemma leftDerivedMap_unique [S.HasRightCalculusOfFractions]
    (hX : F.IsLeftDerivedValueAt S X dX) (hY : F.IsLeftDerivedValueAt S Y dY) (f : X ⟶ Y)
    (φ : dX.pt ⟶ dY.pt)
    (hφ : ∀ (X' Y' : C) (s : X' ⟶ X) (s' : Y' ⟶ Y) (f' : X' ⟶ Y')
      (hs : S s) (hs' : S s') (_ : s ≫ f = f' ≫ s'),
      φ ≫ dY.π.app (Over.mk ⊤ s' hs') = dX.π.app (Over.mk ⊤ s hs) ≫ F.map f') :
    φ = leftDerivedMap S F hX hY f :=
  (main_LF_map_of_rightCalculus F S f dX hY).choose_spec.right φ hφ

end InducedMaps

end StacksDerivedFunctor

end

end

section

/-!
# Derived functors and morphisms of the multiplicative system

Let `F : C ⥤ H` be a functor and let `W` be a class of morphisms of `C`. Following
Deligne, the *right derived functor* `RF` is said to be *defined at* an object `X`
of `C` when the ind-object
$$ X/W ⟶ H, \quad (a : X ⟶ X') ⟼ F(X') $$
is essentially constant, and its value is then the value `RF(X)`; this is the
notion stated in `CategoryTheory.Functor.IsRightDerivedValueAt`. Dually the *left
derived functor* `LF` is defined at `X` when the pro-object `(a : X' ⟶ X) ↦ F(X')`
on `W/X` is essentially constant, which is the same condition for `F.op`, `W.op`
and `Xᵒᵖ`.

If `s : X ⟶ Y` lies in `W`, then precomposition with `s` is a cofinal functor
`Y/W ⟶ X/W`, so the two ind-objects have the same essential-constancy behaviour:
`RF` is defined at `X` if and only if it is defined at `Y`, and the comparison map
`RF(s) : RF(X) ⟶ RF(Y)` between the values is an isomorphism. Likewise for `LF`.

## Main results

* `CategoryTheory.Functor.exists_isRightDerivedValueAt_iff_and_isIso_of_mem`: for
  `s : X ⟶ Y` in a class `W` with left calculus of fractions, the right derived
  functor of `F` is defined at `X` if and only if it is defined at `Y`, and for
  values `c` at `X` and `d` at `Y` the comparison map `c.pt ⟶ d.pt` between them
  exists and is an isomorphism.
* `CategoryTheory.Functor.exists_isLeftDerivedValueAt_iff_and_isIso_of_mem`: dually, for
  `s : X ⟶ Y` in a class `W` with right calculus of fractions, the left derived functor of `F`
  is defined at `X` if and only if it is defined at `Y`, and the comparison map between values
  exists and is an isomorphism.

## Proof outline

The proof rests on three consequences of the axioms of a left calculus of fractions, each
recorded below. Writing `Φ` for the map `Y/W ⟶ X/W` that precomposes with `s`:

* every `a : X/W` admits a morphism `a ⟶ Φ b` for some `b : Y/W` (this is MS2, applied to the
  right fraction `a.right ← X → Y` whose two legs are `a.hom` and `s`);
* any two objects of `Y/W` admit a common target (again MS2);
* two morphisms into an object of `Y/W` that agree after precomposition with a morphism of `W`
  agree after enlarging the object of `Y/W` (this is MS3).

Together the first two say that `Φ` is cofinal, and the third repairs the failure of `Φ` to be
full. From them, a value `d` at `Y` transports to a value at `X` on the same vertex, whose
coprojection at `a` is `F(f) ≫ d.ι.app b` for any morphism `f : a ⟶ Φ b` — the content of the
first two bullet points being exactly that this is defined and independent of the choice. In the
other direction a value `c` at `X` restricts along `Φ` to a value at `Y`, again on the same
vertex, and here the third bullet point is what turns the witnesses of essential constancy at
`X` into witnesses at `Y`. Finally two values of the same ind-object are canonically isomorphic,
so the map `RF(s)` of Tag 05SA, which is the canonical map from `c` to the transport of `d`, is
an isomorphism.

## Implementation notes

*Which notion of "defined at".* The condition used is the source's, as stated in
Tag 05S9: essential constancy of the ind-object on `X/W`, with the value a retract
of some `F(X')`. It is not Mathlib's
`CategoryTheory.Functor.HasPointwiseRightDerivedFunctorAt`, which asks instead
that the colimit computing the pointwise left Kan extension of `F` along a
localization functor exist at `L X`. The two conditions are inequivalent, and not
merely in presentation: for `W = ⊥` Mathlib's condition holds for every `F` and
every `X` (the localization inverts `⊥` vacuously) while no cocone is a value in
the source's sense, `X/⊥` being empty; and in general the existence of a filtered
colimit does not make it a retract of a term of the diagram. Mathlib's lemmas
`hasPointwiseRightDerivedFunctorAt_iff_of_mem` and
`hasPointwiseLeftDerivedFunctorAt_iff_of_mem` are the analogues of the two
equivalences below for its own condition; they are not this statement, and no
bridge between the two conditions is claimed here.

*Hypotheses.* The source states this in Situation 05S8: `F : D ⥤ D'` an exact
functor of triangulated categories and `S` a saturated multiplicative system
compatible with the triangulated structure. Triangulatedness, exactness and
saturation are used by neither conclusion, so the statement is made for an
arbitrary functor `F : C ⥤ H`. What is used is that `S` is a multiplicative
system, in the form the ind-object on `X/W` needs: `W.HasLeftCalculusOfFractions`,
whose `RightFraction.exists_leftFraction` is MS2 (it completes `X' ← X → Y` to a
square with both legs of the far side in `W`, which is what makes precomposition
with `s` cofinal) and whose `ext` is MS3. Some such hypothesis is necessary: for
`W` the property of being equal to a single `s : X ⟶ Y` with `X ≠ Y`, the
ind-object on `X/W` is essentially constant while `Y/W` is empty, so the first
equivalence fails.

*Part (2).* `LF` is defined at `X` exactly when `F.op` has a right derived value at
`Xᵒᵖ` for `W.op` (the cone/cocone bridge of section `OpBridge`), and `W.op` has left
calculus of fractions as soon as `W` has right calculus of fractions, so item (2) of
the source, `exists_isLeftDerivedValueAt_iff_and_isIso_of_mem`, is proved by applying
item (1) to `F.op`, `W.op` and `s.op` and reading the result back in `C` and `H`.

*The comparison map.* The source's second sentence in each item speaks of the map
`RF(s)` between values, constructed in Tag 05SA from the hypothesis that `RF` is
defined at both ends; that construction has no name in this development yet, so
the map is pinned here by the property that characterises it in 05SA: `φ` is
compatible with the coprojections of the two values along every commutative square
`a.hom ≫ f = s ≫ b.hom` with `a ∈ X/W` and `b ∈ Y/W`. That property determines
`φ` uniquely, which is 05SA's content and is not restated. Asserting the existence
of such a `φ` rather than quantifying over an unnamed morphism keeps the clause
non-vacuous while `RF(s)` is unnamed.

*Precomposition.* Precomposition with `s` is used only as a map on objects,
`precompUnder`, together with `CategoryTheory.MorphismProperty.Under.homMk` on morphisms;
the functor `CategoryTheory.MorphismProperty.Under.map` would do as well, but nothing here
needs its functoriality, and the object map keeps the ind-object at `X` restricted along it
equal to the ind-object at `Y` by definition rather than up to an isomorphism of functors.

*Uniqueness of a value.* `exists_isIso_comp_coprj` is proved for two arbitrary cocones on
the ind-object at a single object; it is the statement that a value is unique up to a unique
isomorphism compatible with the coprojections, and it is where the isomorphism asserted by
Stacks 05SB comes from.

*Named coprojections.* Every coprojection is named: `coprj` at an object of `X/W`, whose
source is written `F(a.right)`, and `coprjPrecomp` at an object of the form `s ≫ b.hom` for
`b : Y/W`, whose source is written `F(b.right)`. The point of the second name is that the
coprojections of the restriction of a cocone along `Φ` are then indexed by `Y/W` with sources
depending on `b` alone, so that each equality proved below is between morphisms whose sources
and targets are projections of the variables in play; the same equalities written at `Φ b`
directly have sources `F((Φ b).right)`, equal to `F(b.right)` only after unfolding the
construction of `Φ b`, which `rw` and `simp` do not do.

## References

* [Stacks project, Tag 05SB](https://stacks.math.columbia.edu/tag/05SB); the source omits
  the proof. Essential constancy is Tag 05PU, the notion of a value is Tag 05S9 and the
  comparison map is Tag 05SA.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} {H : Type u₂} [Category.{v₁} C] [Category.{v₂} H]

/-- Precomposition with a morphism `s : X ⟶ Y` of `W`, as a map from the objects of `Y/W` to
the objects of `X/W`. -/
private abbrev precompUnder {W : MorphismProperty C} [W.IsStableUnderComposition] {X Y : C}
    {s : X ⟶ Y} (hs : W s) (b : W.Under ⊤ Y) : W.Under ⊤ X :=
  MorphismProperty.Under.mk ⊤ (s ≫ b.hom) (W.comp_mem _ _ hs b.prop)

/-- The coprojection of a cocone on the ind-object at `X`, with its source written as
`F(a.right)`. -/
public abbrev coprj {W : MorphismProperty C} {X : C} {F : C ⥤ H}
    (c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F))
    (a : W.Under ⊤ X) : F.obj a.right ⟶ c.pt := c.ι.app a

/-- Cocone compatibility on the ind-object at `X`, in terms of morphisms of `C`. -/
public lemma map_comp_coprj {W : MorphismProperty C} {X : C} (F : C ⥤ H)
    (c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F))
    {a a' : W.Under ⊤ X} (g : a.right ⟶ a'.right) (hg : a.hom ≫ g = a'.hom) :
    F.map g ≫ coprj c a' = coprj c a :=
  c.w (MorphismProperty.Under.homMk g hg)

/-- A morphism of `Y/W` is a morphism of `X/W` between the objects obtained from its source and
its target by precomposition with `s`. -/
private lemma precompUnder_w {W : MorphismProperty C} [W.IsStableUnderComposition] {X Y : C}
    {s : X ⟶ Y} (hs : W s) {b b' : W.Under ⊤ Y} (g : b.right ⟶ b'.right)
    (hg : b.hom ≫ g = b'.hom) : (precompUnder hs b).hom ≫ g = (precompUnder hs b').hom := by
  change (s ≫ b.hom) ≫ g = s ≫ b'.hom
  rw [Category.assoc, hg]

/-- The coprojection of a cocone on the ind-object at `X` at the object `s ≫ b.hom` of `X/W`
attached to `b : Y/W`, with its source written as `F(b.right)`. -/
private abbrev coprjPrecomp {W : MorphismProperty C} [W.IsStableUnderComposition] {X Y : C}
    {s : X ⟶ Y} (hs : W s) {F : C ⥤ H}
    (c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F))
    (b : W.Under ⊤ Y) : F.obj b.right ⟶ c.pt := coprj c (precompUnder hs b)

section
variable {W : MorphismProperty C} [W.IsStableUnderComposition] {X Y : C} {s : X ⟶ Y}

/-- Cocone compatibility on the ind-object at `X` along a morphism of `Y/W`. -/
private lemma map_comp_coprjPrecomp (hs : W s) (F : C ⥤ H)
    (c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F))
    {b b' : W.Under ⊤ Y} (g : b.right ⟶ b'.right) (hg : b.hom ≫ g = b'.hom) :
    F.map g ≫ coprjPrecomp hs c b' = coprjPrecomp hs c b :=
  map_comp_coprj (a := precompUnder hs b) (a' := precompUnder hs b') F c g (precompUnder_w hs g hg)

/-- Cocone compatibility on the ind-object at `X` along a square `a.hom ≫ f = s ≫ b.hom`. -/
private lemma map_comp_coprjPrecomp_sq (hs : W s) (F : C ⥤ H)
    (c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F))
    (a : W.Under ⊤ X) (b : W.Under ⊤ Y) (f : a.right ⟶ b.right)
    (hf : a.hom ≫ f = s ≫ b.hom) : F.map f ≫ coprjPrecomp hs c b = coprj c a :=
  map_comp_coprj (a := a) (a' := precompUnder hs b) F c f hf

end

/-- **MS2**, first use: any `s : X ⟶ Y` and any `a : X/W` fit into a square
`a.hom ≫ f = s ≫ b.hom` with `b : Y/W`. -/
private lemma exists_under_sq {W : MorphismProperty C} [W.HasLeftCalculusOfFractions]
    {X Y : C} (s : X ⟶ Y) (a : W.Under ⊤ X) :
    ∃ (b : W.Under ⊤ Y) (f : a.right ⟶ b.right), a.hom ≫ f = s ≫ b.hom := by
  obtain ⟨ψ, hψ⟩ := (MorphismProperty.RightFraction.mk a.hom a.prop s).exists_leftFraction
  exact ⟨MorphismProperty.Under.mk ⊤ ψ.s ψ.hs, ψ.f, hψ.symm⟩

/-- **MS2**, second use: any two objects of `Y/W` admit a common target. -/
private lemma exists_under_common {W : MorphismProperty C} [W.HasLeftCalculusOfFractions]
    {Y : C} (b₁ b₂ : W.Under ⊤ Y) :
    ∃ (b : W.Under ⊤ Y) (g₁ : b₁.right ⟶ b.right) (g₂ : b₂.right ⟶ b.right),
      b₁.hom ≫ g₁ = b.hom ∧ b₂.hom ≫ g₂ = b.hom := by
  obtain ⟨ψ, hψ⟩ := (MorphismProperty.RightFraction.mk b₁.hom b₁.prop b₂.hom).exists_leftFraction
  exact ⟨MorphismProperty.Under.mk ⊤ (b₂.hom ≫ ψ.s) (W.comp_mem _ _ b₂.prop ψ.hs), ψ.f, ψ.s,
    hψ.symm, rfl⟩

/-- **MS3**: two morphisms into an object of `Y/W` that agree after precomposition with a
morphism of `W` agree after enlarging the object of `Y/W`. -/
private lemma exists_under_postcomp_eq {W : MorphismProperty C} [W.HasLeftCalculusOfFractions]
    {Y : C} (b : W.Under ⊤ Y) {Z Z' : C} (σ : Z' ⟶ Z) (hσ : W σ) (h₁ h₂ : Z ⟶ b.right)
    (h : σ ≫ h₁ = σ ≫ h₂) :
    ∃ (b' : W.Under ⊤ Y) (q : b.right ⟶ b'.right),
      b.hom ≫ q = b'.hom ∧ h₁ ≫ q = h₂ ≫ q := by
  obtain ⟨V, t, ht, hteq⟩ :=
    MorphismProperty.HasLeftCalculusOfFractions.ext h₁ h₂ σ hσ h
  exact ⟨MorphismProperty.Under.mk ⊤ (b.hom ≫ t) (W.comp_mem _ _ b.prop ht), t, rfl, hteq⟩

section Uniqueness

/-- The retraction data of a value of `RF` at `X` computes the canonical map to the vertex of an
arbitrary cocone on the ind-object at `X`. -/
private lemma coprj_comp_retraction {W : MorphismProperty C} {X : C} (F : C ⥤ H)
    {c c' : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
    {a₀ : W.Under ⊤ X} {r : c.pt ⟶ F.obj a₀.right}
    (h : ∀ a : W.Under ⊤ X, ∃ (t : W.Under ⊤ X) (u : a ⟶ t) (v : a₀ ⟶ t),
      F.map u.right = coprj c a ≫ r ≫ F.map v.right)
    (a : W.Under ⊤ X) : coprj c a ≫ r ≫ coprj c' a₀ = coprj c' a := by
  obtain ⟨t, u, v, huv⟩ := h a
  rw [← map_comp_coprj F c' v.right (MorphismProperty.Under.w v),
    ← map_comp_coprj F c' u.right (MorphismProperty.Under.w u), huv]
  simp

/-- Two values of `RF` at `X` are isomorphic by a unique isomorphism compatible with the
coprojections; this is where the isomorphism asserted by Tag 05SB comes from. -/
private lemma exists_isIso_comp_coprj {W : MorphismProperty C} {X : C} (F : C ⥤ H)
    {c c' : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
    (h : F.IsRightDerivedValueAt W X c) (h' : F.IsRightDerivedValueAt W X c') :
    ∃ α : c.pt ⟶ c'.pt, (∀ a, coprj c a ≫ α = coprj c' a) ∧ IsIso α := by
  obtain ⟨a₀, r, hr, hb⟩ := h
  obtain ⟨a₀', r', hr', hb'⟩ := h'
  have hr₁ : r ≫ coprj c a₀ = 𝟙 c.pt := hr
  have hr₂ : r' ≫ coprj c' a₀' = 𝟙 c'.pt := hr'
  have hb₁ : ∀ a : W.Under ⊤ X, ∃ (t : W.Under ⊤ X) (u : a ⟶ t) (v : a₀ ⟶ t),
    F.map u.right = coprj c a ≫ r ≫ F.map v.right := hb
  have hb₂ : ∀ a : W.Under ⊤ X, ∃ (t : W.Under ⊤ X) (u : a ⟶ t) (v : a₀' ⟶ t),
    F.map u.right = coprj c' a ≫ r' ≫ F.map v.right := hb'
  refine ⟨r ≫ coprj c' a₀, fun a => coprj_comp_retraction F hb₁ a,
    ⟨⟨r' ≫ coprj c a₀', ?_, ?_⟩⟩⟩
  · rwa [Category.assoc, coprj_comp_retraction (c := c') (c' := c) F hb₂ a₀]
  · rwa [Category.assoc, coprj_comp_retraction (c := c) (c' := c') F hb₁ a₀']

end Uniqueness

section Transport

variable {W : MorphismProperty C} [W.HasLeftCalculusOfFractions] {X Y : C}

/-- The transported coprojection does not depend on the chosen square. -/
private lemma map_comp_coprj_eq {s : X ⟶ Y} (F : C ⥤ H)
    (d : Cocone (MorphismProperty.Under.forget W ⊤ Y ⋙ Under.forget Y ⋙ F))
    {a : W.Under ⊤ X} {b₁ b₂ : W.Under ⊤ Y}
    (f₁ : a.right ⟶ b₁.right) (f₂ : a.right ⟶ b₂.right)
    (h₁ : a.hom ≫ f₁ = s ≫ b₁.hom) (h₂ : a.hom ≫ f₂ = s ≫ b₂.hom) :
    F.map f₁ ≫ coprj d b₁ = F.map f₂ ≫ coprj d b₂ := by
  obtain ⟨b, g₁, g₂, hg₁, hg₂⟩ := exists_under_common b₁ b₂
  have key : a.hom ≫ f₁ ≫ g₁ = a.hom ≫ f₂ ≫ g₂ := by
    rw [reassoc_of% h₁, reassoc_of% h₂, hg₁, hg₂]
  obtain ⟨b', q, hq, heq⟩ :=
    exists_under_postcomp_eq b a.hom a.prop (f₁ ≫ g₁) (f₂ ≫ g₂) key
  have heq' : f₁ ≫ g₁ ≫ q = f₂ ≫ g₂ ≫ q := by simpa using heq
  rw [← map_comp_coprj F d g₁ hg₁, ← map_comp_coprj F d g₂ hg₂, ← map_comp_coprj F d q hq]
  calc F.map f₁ ≫ F.map g₁ ≫ F.map q ≫ coprj d b'
      = F.map (f₁ ≫ g₁ ≫ q) ≫ coprj d b' := by simp
    _ = F.map (f₂ ≫ g₂ ≫ q) ≫ coprj d b' := by rw [heq']
    _ = F.map f₂ ≫ F.map g₂ ≫ F.map q ≫ coprj d b' := by simp

/-- The coprojection at `a : X/W` of the cocone transported from a cocone on the ind-object
at `Y` along a morphism `s : X ⟶ Y`. -/
private noncomputable def transportι (s : X ⟶ Y) (F : C ⥤ H)
    (d : Cocone (MorphismProperty.Under.forget W ⊤ Y ⋙ Under.forget Y ⋙ F))
    (a : W.Under ⊤ X) : F.obj a.right ⟶ d.pt :=
  F.map (exists_under_sq s a).choose_spec.choose ≫ coprj d (exists_under_sq s a).choose

private lemma transportι_eq (s : X ⟶ Y) (F : C ⥤ H)
    (d : Cocone (MorphismProperty.Under.forget W ⊤ Y ⋙ Under.forget Y ⋙ F))
    (a : W.Under ⊤ X) (b : W.Under ⊤ Y) (f : a.right ⟶ b.right)
    (hf : a.hom ≫ f = s ≫ b.hom) : transportι s F d a = F.map f ≫ coprj d b :=
  map_comp_coprj_eq F d _ f (exists_under_sq s a).choose_spec.choose_spec hf

/-- At an object of `X/W` of the form `s ≫ b.hom`, for `b : Y/W`, the transported coprojection
is the coprojection at `b`. -/
private lemma transportι_precompUnder {s : X ⟶ Y} (hs : W s) (F : C ⥤ H)
    (d : Cocone (MorphismProperty.Under.forget W ⊤ Y ⋙ Under.forget Y ⋙ F))
    (b : W.Under ⊤ Y) : transportι s F d (precompUnder hs b) = coprj d b := by
  have h : transportι s F d (precompUnder hs b) = F.map (𝟙 b.right) ≫ coprj d b :=
    transportι_eq s F d (precompUnder hs b) b (𝟙 b.right) (Category.comp_id _)
  rw [h, F.map_id, Category.id_comp]

/-- The cocone on the ind-object at `X` transported from a cocone on the ind-object at `Y`. -/
private noncomputable def transportCocone (s : X ⟶ Y) (F : C ⥤ H)
    (d : Cocone (MorphismProperty.Under.forget W ⊤ Y ⋙ Under.forget Y ⋙ F)) :
    Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F) where
  pt := d.pt
  ι :=
    { app := transportι s F d
      naturality := fun a a' u => by
        obtain ⟨b, f, hf⟩ := exists_under_sq s a'
        have h1 : transportι s F d a' = F.map f ≫ coprj d b := transportι_eq s F d a' b f hf
        have h2 : transportι s F d a = F.map (u.right ≫ f) ≫ coprj d b :=
          transportι_eq s F d a b (u.right ≫ f) (by
            rw [← Category.assoc, MorphismProperty.Under.w, hf])
        change F.map u.right ≫ transportι s F d a' = transportι s F d a ≫ 𝟙 d.pt
        rw [h1, h2]
        simp }

/-- A value of `RF` at `Y` transports to a value of `RF` at `X` along a morphism of `W`. -/
private lemma isRightDerivedValueAt_transportCocone {s : X ⟶ Y} (hs : W s) (F : C ⥤ H)
    {d : Cocone (MorphismProperty.Under.forget W ⊤ Y ⋙ Under.forget Y ⋙ F)}
    (hd : F.IsRightDerivedValueAt W Y d) :
    F.IsRightDerivedValueAt W X (transportCocone s F d) := by
  obtain ⟨b₀, ρ, hρ, hbd⟩ := hd
  have hρ' : ρ ≫ coprj d b₀ = 𝟙 d.pt := hρ
  refine ⟨precompUnder hs b₀, ρ, ?_, ?_⟩
  · change ρ ≫ transportι s F d (precompUnder hs b₀) = 𝟙 d.pt
    rw [transportι_precompUnder hs F d b₀]
    exact hρ'
  · intro a
    obtain ⟨b, f, hf⟩ := exists_under_sq s a
    obtain ⟨b', μ, ν, hμν⟩ := hbd b
    have hμν' : F.map μ.right = coprj d b ≫ ρ ≫ F.map ν.right := hμν
    refine ⟨precompUnder hs b',
      MorphismProperty.Under.homMk (f ≫ μ.right)
        (by
          calc a.hom ≫ f ≫ μ.right = (a.hom ≫ f) ≫ μ.right := by simp
            _ = (s ≫ b.hom) ≫ μ.right := by rw [hf]
            _ = s ≫ b'.hom := by rw [Category.assoc, MorphismProperty.Under.w]),
      MorphismProperty.Under.homMk ν.right (precompUnder_w hs ν.right
        (MorphismProperty.Under.w ν)), ?_⟩
    change F.map (f ≫ μ.right) = transportι s F d a ≫ ρ ≫ F.map ν.right
    rw [transportι_eq s F d a b f hf, F.map_comp, hμν']
    simp

end Transport

section Restriction

variable {W : MorphismProperty C} [W.HasLeftCalculusOfFractions] {X Y : C} {s : X ⟶ Y}

/-- The cocone on the ind-object at `Y` obtained by restricting a cocone on the ind-object
at `X` along precomposition with `s`. -/
private def restrictCocone (hs : W s) (F : C ⥤ H)
    (c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)) :
    Cocone (MorphismProperty.Under.forget W ⊤ Y ⋙ Under.forget Y ⋙ F) where
  pt := c.pt
  ι :=
    { app := fun b => coprjPrecomp hs c b
      naturality := fun b b' p => by
        have h : F.map p.right ≫ coprjPrecomp hs c b' = coprjPrecomp hs c b :=
          map_comp_coprjPrecomp hs F c p.right (MorphismProperty.Under.w p)
        change F.map p.right ≫ coprjPrecomp hs c b' = coprjPrecomp hs c b ≫ 𝟙 c.pt
        simpa using h }

/-- A value of `RF` at `X` restricts to a value of `RF` at `Y`. -/
private lemma isRightDerivedValueAt_restrictCocone (hs : W s) (F : C ⥤ H)
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
    (hc : F.IsRightDerivedValueAt W X c) :
    F.IsRightDerivedValueAt W Y (restrictCocone hs F c) := by
  obtain ⟨a₀, r, hr, hb⟩ := hc
  have hr' : r ≫ coprj c a₀ = 𝟙 c.pt := hr
  have hb' : ∀ a : W.Under ⊤ X, ∃ (t : W.Under ⊤ X) (u : a ⟶ t) (v : a₀ ⟶ t),
    F.map u.right = coprj c a ≫ r ≫ F.map v.right := hb
  obtain ⟨b₀, f₀, hf₀⟩ := exists_under_sq s a₀
  refine ⟨b₀, r ≫ F.map f₀, ?_, ?_⟩
  · have h : F.map f₀ ≫ coprjPrecomp hs c b₀ = coprj c a₀ :=
      map_comp_coprjPrecomp_sq hs F c a₀ b₀ f₀ hf₀
    change (r ≫ F.map f₀) ≫ coprjPrecomp hs c b₀ = 𝟙 c.pt
    rwa [Category.assoc, h]
  · intro b
    obtain ⟨t, u, v, huv⟩ := hb' (precompUnder hs b)
    obtain ⟨g, hut, hg⟩ : ∃ g : b.right ⟶ t.right, (s ≫ b.hom) ≫ g = t.hom ∧
        F.map g = coprjPrecomp hs c b ≫ r ≫ F.map v.right :=
      ⟨u.right, MorphismProperty.Under.w u, huv⟩
    obtain ⟨b₁, w, hw⟩ := exists_under_sq s t
    obtain ⟨b₂, p₀, p₁, hp₀, hp₁⟩ := exists_under_common b₀ b₁
    have hvt : a₀.hom ≫ v.right = t.hom := MorphismProperty.Under.w v
    simp only [Category.assoc] at hut
    have hA : s ≫ b.hom ≫ g ≫ w ≫ p₁ = s ≫ b₂.hom := by
      rw [reassoc_of% hut, reassoc_of% hw, hp₁]
    have hB : a₀.hom ≫ v.right ≫ w ≫ p₁ = s ≫ b₂.hom := by
      rw [reassoc_of% hvt, reassoc_of% hw, hp₁]
    have hC : a₀.hom ≫ f₀ ≫ p₀ = s ≫ b₂.hom := by
      rw [← Category.assoc, hf₀, Category.assoc, hp₀]
    obtain ⟨b₃, q₁, hq₁, e₁⟩ :=
      exists_under_postcomp_eq b₂ s hs (b.hom ≫ g ≫ w ≫ p₁) b₂.hom hA
    obtain ⟨b₄, q₂, hq₂, e₂⟩ :=
      exists_under_postcomp_eq b₃ a₀.hom a₀.prop ((f₀ ≫ p₀) ≫ q₁) ((v.right ≫ w ≫ p₁) ≫ q₁)
        (by simp only [Category.assoc, reassoc_of% hC, reassoc_of% hB])
    have hfin : ∀ {x : W.Under ⊤ Y} (m : x.right ⟶ b₂.right),
        (x.hom ≫ m) ≫ q₁ = b₂.hom ≫ q₁ → x.hom ≫ m ≫ q₁ ≫ q₂ = b₄.hom := fun m h => by
      rw [← Category.assoc, ← Category.assoc, h, hq₁, hq₂]
    have hU : b.hom ≫ (g ≫ w ≫ p₁) ≫ q₁ ≫ q₂ = b₄.hom := hfin _ e₁
    have hV : b₀.hom ≫ p₀ ≫ q₁ ≫ q₂ = b₄.hom := hfin _ (by rw [hp₀])
    refine ⟨b₄, MorphismProperty.Under.homMk ((g ≫ w ≫ p₁) ≫ q₁ ≫ q₂) hU,
      MorphismProperty.Under.homMk (p₀ ≫ q₁ ≫ q₂) hV, ?_⟩
    have step : F.map (f₀ ≫ p₀ ≫ q₁ ≫ q₂) = F.map (v.right ≫ w ≫ p₁ ≫ q₁ ≫ q₂) := by
      congr 1
      calc f₀ ≫ p₀ ≫ q₁ ≫ q₂ = ((f₀ ≫ p₀) ≫ q₁) ≫ q₂ := by simp
        _ = ((v.right ≫ w ≫ p₁) ≫ q₁) ≫ q₂ := e₂
        _ = v.right ≫ w ≫ p₁ ≫ q₁ ≫ q₂ := by simp
    change F.map ((g ≫ w ≫ p₁) ≫ q₁ ≫ q₂)
        = coprjPrecomp hs c b ≫ (r ≫ F.map f₀) ≫ F.map (p₀ ≫ q₁ ≫ q₂)
    calc F.map ((g ≫ w ≫ p₁) ≫ q₁ ≫ q₂)
        = F.map g ≫ F.map ((w ≫ p₁) ≫ q₁ ≫ q₂) := by
          rw [← F.map_comp]; congr 1; simp
      _ = (coprjPrecomp hs c b ≫ r ≫ F.map v.right)
            ≫ F.map ((w ≫ p₁) ≫ q₁ ≫ q₂) := by rw [hg]
      _ = coprjPrecomp hs c b ≫ r ≫ F.map (v.right ≫ w ≫ p₁ ≫ q₁ ≫ q₂) := by simp
      _ = coprjPrecomp hs c b ≫ r ≫ F.map (f₀ ≫ p₀ ≫ q₁ ≫ q₂) := by rw [step]
      _ = coprjPrecomp hs c b ≫ (r ≫ F.map f₀) ≫ F.map (p₀ ≫ q₁ ≫ q₂) := by simp

end Restriction

/-- **Stacks 05SB**(1). Let `F : C ⥤ H` be a functor, `W` a class of morphisms of
`C` with left calculus of fractions and `s : X ⟶ Y` a morphism in `W`. Then:

* the right derived functor of `F` is defined at `X` if and only if it is defined
  at `Y`, definedness being essential constancy of the ind-object on `X/W` as in
  Stacks 05S9;
* if `c` is a value of `RF` at `X` and `d` is a value of `RF` at `Y`, there is a
  morphism `φ : RF(X) ⟶ RF(Y)` compatible with the coprojections of `c` and `d`
  along every square `a.hom ≫ f = s ≫ b.hom` — that is, the map `RF(s)` of Stacks
  05SA — and `φ` is an isomorphism.

Item (2) of the source, for the left derived functor, is
`Functor.exists_isLeftDerivedValueAt_iff_and_isIso_of_mem`. -/
@[stacks 05SB "(1)"]
public theorem Functor.exists_isRightDerivedValueAt_iff_and_isIso_of_mem
    (F : C ⥤ H) (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    {X Y : C} {s : X ⟶ Y} (hs : W s) :
    ((∃ c, F.IsRightDerivedValueAt W X c) ↔ (∃ d, F.IsRightDerivedValueAt W Y d)) ∧
      ∀ {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
        {d : Cocone (MorphismProperty.Under.forget W ⊤ Y ⋙ Under.forget Y ⋙ F)},
        F.IsRightDerivedValueAt W X c → F.IsRightDerivedValueAt W Y d →
          ∃ φ : c.pt ⟶ d.pt,
            (∀ (a : W.Under ⊤ X) (b : W.Under ⊤ Y) (f : a.right ⟶ b.right),
              a.hom ≫ f = s ≫ b.hom → c.ι.app a ≫ φ = F.map f ≫ d.ι.app b) ∧ IsIso φ := by
  refine ⟨⟨fun ⟨_, hc⟩ => ⟨_, isRightDerivedValueAt_restrictCocone hs F hc⟩,
    fun ⟨_, hd⟩ => ⟨_, isRightDerivedValueAt_transportCocone hs F hd⟩⟩, ?_⟩
  intro c d hc hd
  obtain ⟨α, hα, hiso⟩ :=
    exists_isIso_comp_coprj F hc (isRightDerivedValueAt_transportCocone hs F hd)
  refine ⟨α, fun a b f hf => ?_, hiso⟩
  change coprj c a ≫ α = F.map f ≫ coprj d b
  rw [hα a]
  exact transportι_eq s F d a b f hf

section OpBridge

variable {W : MorphismProperty C} {X : C}

/-- The index of the pro-object `W/X` opposite to an index of the ind-object `(op X)/W.op`. -/
private abbrev overOfUnderOp (a : W.op.Under ⊤ (Opposite.op X)) : W.Over ⊤ X :=
  MorphismProperty.Over.mk ⊤ a.hom.unop a.prop

/-- The index of the ind-object `(op X)/W.op` opposite to an index of the pro-object `W/X`. -/
private abbrev underOpOfOver (a : W.Over ⊤ X) : W.op.Under ⊤ (Opposite.op X) :=
  MorphismProperty.Under.mk ⊤ a.hom.op a.prop

/-- The transition morphism of `W/X` opposite to one of `(op X)/W.op`. -/
private abbrev overOfUnderOpMap {a b : W.op.Under ⊤ (Opposite.op X)} (f : a ⟶ b) :
    overOfUnderOp b ⟶ overOfUnderOp a :=
  MorphismProperty.Over.homMk f.right.unop (Quiver.Hom.op_inj (MorphismProperty.Under.w f))

/-- The transition morphism of `(op X)/W.op` opposite to one of `W/X`. -/
private abbrev underOpOfOverMap {a b : W.Over ⊤ X} (f : a ⟶ b) :
    underOpOfOver b ⟶ underOpOfOver a :=
  MorphismProperty.Under.homMk f.left.op (Quiver.Hom.unop_inj (MorphismProperty.Over.w f))

variable (F : C ⥤ H)

/-- The cocone on the ind-object for `F.op`, `W.op` and `op X` opposite to a cone on the
pro-object for `F`, `W` and `X`. -/
private def opCocone (c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F)) :
    Cocone (MorphismProperty.Under.forget W.op ⊤ (Opposite.op X) ⋙
      Under.forget (Opposite.op X) ⋙ F.op) where
  pt := Opposite.op c.pt
  ι :=
    { app a := (c.π.app (overOfUnderOp a)).op
      naturality _ _ f :=
        (congrArg Quiver.Hom.op (c.w (overOfUnderOpMap f))).trans (Category.comp_id _).symm }

/-- The cone on the pro-object for `F`, `W` and `X` opposite to a cocone on the ind-object for
`F.op`, `W.op` and `op X`. -/
private def unopCone (c : Cocone (MorphismProperty.Under.forget W.op ⊤ (Opposite.op X) ⋙
      Under.forget (Opposite.op X) ⋙ F.op)) :
    Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) where
  pt := c.pt.unop
  π :=
    { app a := (c.ι.app (underOpOfOver a)).unop
      naturality _ _ f := (Category.id_comp _).trans
        (congrArg Quiver.Hom.unop (c.w (underOpOfOverMap f))).symm }

/-- A cone is a value of `LF` at `X` exactly when its opposite cocone is a value of the right
derived functor of `F.op` relative to `W.op` at `op X`. -/
private lemma isRightDerivedValueAt_op_opCocone_iff
    (c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F)) :
    F.op.IsRightDerivedValueAt W.op (Opposite.op X) (opCocone F c) ↔
      F.IsLeftDerivedValueAt W X c := by
  constructor
  · rintro ⟨a₀, r, hr, hfac⟩
    refine ⟨overOfUnderOp a₀, r.unop, Quiver.Hom.op_inj hr, fun a => ?_⟩
    obtain ⟨t, u, v, huv⟩ := hfac (underOpOfOver a)
    exact ⟨overOfUnderOp t, overOfUnderOpMap u, overOfUnderOpMap v,
      (congrArg Quiver.Hom.unop huv).trans (Category.assoc _ _ _)⟩
  · rintro ⟨a₀, r, hr, hfac⟩
    refine ⟨underOpOfOver a₀, r.op, Quiver.Hom.unop_inj hr, fun a => ?_⟩
    obtain ⟨t, u, v, huv⟩ := hfac (overOfUnderOp a)
    exact ⟨underOpOfOver t, underOpOfOverMap u, underOpOfOverMap v,
      (congrArg Quiver.Hom.op huv).trans
        (Category.assoc ((opCocone F c).ι.app a) r.op (F.op.map (underOpOfOverMap v).right))⟩

/-- `LF` is defined at `X` exactly when the right derived functor of `F.op` relative to `W.op` is
defined at `op X`. -/
private lemma exists_isLeftDerivedValueAt_iff_op :
    (∃ c, F.IsLeftDerivedValueAt W X c) ↔
      ∃ c, F.op.IsRightDerivedValueAt W.op (Opposite.op X) c :=
  ⟨fun ⟨c, hc⟩ => ⟨opCocone F c, (isRightDerivedValueAt_op_opCocone_iff F c).2 hc⟩,
    fun ⟨c, hc⟩ => ⟨unopCone F c, (isRightDerivedValueAt_op_opCocone_iff F (unopCone F c)).1 hc⟩⟩

end OpBridge

/-- **Stacks 05SB**(2). Let `F : C ⥤ H` be a functor, `W` a class of morphisms of
`C` with right calculus of fractions and `s : X ⟶ Y` a morphism in `W`. Then:

* the left derived functor of `F` is defined at `X` if and only if it is defined
  at `Y`, definedness being essential constancy of the pro-object on `W/X` as in
  Stacks 05S9;
* if `c` is a value of `LF` at `X` and `d` is a value of `LF` at `Y`, there is a
  morphism `φ : LF(X) ⟶ LF(Y)` compatible with the projections of `c` and `d`
  along every square `a.hom ≫ s = f ≫ b.hom` — that is, the map `LF(s)` of Stacks
  05SA — and `φ` is an isomorphism.

The proof applies item (1) to `F.op`, `W.op` and `s.op`. -/
@[stacks 05SB "(2)"]
public theorem Functor.exists_isLeftDerivedValueAt_iff_and_isIso_of_mem
    (F : C ⥤ H) (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    {X Y : C} {s : X ⟶ Y} (hs : W s) :
    ((∃ c, F.IsLeftDerivedValueAt W X c) ↔ (∃ d, F.IsLeftDerivedValueAt W Y d)) ∧
      ∀ {c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F)}
        {d : Cone (MorphismProperty.Over.forget W ⊤ Y ⋙ Over.forget Y ⋙ F)},
        F.IsLeftDerivedValueAt W X c → F.IsLeftDerivedValueAt W Y d →
          ∃ φ : c.pt ⟶ d.pt,
            (∀ (a : W.Over ⊤ X) (b : W.Over ⊤ Y) (f : a.left ⟶ b.left),
              a.hom ≫ s = f ≫ b.hom → φ ≫ d.π.app b = c.π.app a ≫ F.map f) ∧ IsIso φ := by
  have hR := F.op.exists_isRightDerivedValueAt_iff_and_isIso_of_mem W.op (s := s.op) hs
  refine ⟨(exists_isLeftDerivedValueAt_iff_op F).trans
    (hR.1.symm.trans (exists_isLeftDerivedValueAt_iff_op F).symm), ?_⟩
  intro c d hc hd
  obtain ⟨φ, hφ, hiso⟩ := hR.2 ((isRightDerivedValueAt_op_opCocone_iff F d).2 hd)
    ((isRightDerivedValueAt_op_opCocone_iff F c).2 hc)
  refine ⟨φ.unop, fun a b f hf => ?_, (asIso φ).unop.isIso_hom⟩
  have h := hφ (underOpOfOver b) (underOpOfOver a) f.op
    (show (f ≫ b.hom).op = (a.hom ≫ s).op by rw [hf])
  exact congrArg Quiver.Hom.unop h

end CategoryTheory

end

end

section

/-!
# Everywhere-definedness of a derived functor from definedness along `W`

Let `F : 𝒟 ⥤ 𝒟'` be a functor and let `W` be a class of morphisms of `𝒟`. For an object `X`
of `𝒟`, the right derived functor `RF` is *defined at* `X` when the ind-object
$$ X/W ⟶ 𝒟', \qquad (s : X ⟶ X') ⟼ F(X'), $$
is essentially constant, its value being `RF(X)`; dually `LF` is *defined at* `X` when the
pro-object `W/X ⟶ 𝒟'`, `(s : X' ⟶ X) ↦ F(X')`, is essentially constant ([Stacks 05S9]). `RF`
is *everywhere defined*, i.e. `F` is right derivable, when `RF` is defined at every object,
and likewise for `LF` ([Stacks 05SV]).

Definedness of `RF` is insensitive to replacing an object by any object it maps to by a
morphism of `W`, as soon as `W` admits a left calculus of fractions ([Stacks 05SB]).
Consequently it is enough to find, for each object `X`, a *single* morphism `s : X ⟶ X'` of
`W` at whose target `RF` is defined, and then `RF` is everywhere defined; dually for `LF`,
with a morphism `s : X' ⟶ X` of `W` and a right calculus of fractions. This is how derivability
is proved in practice: one exhibits a class of objects at which `F` may be evaluated — bounded
below complexes of injectives, K-injective complexes — into which every object maps by a
quasi-isomorphism.

## Main results

* `CategoryTheory.Functor.isRightDerivable_and_isLeftDerivable_of_forall_exists_isDerivedValueAt`
  ([Stacks 05T1]): both parts of the tag, part (1) for `RF` and part (2) for `LF`.

## Implementation notes

*Faithfulness.* (1) No hypothesis is dead: each conjunct assumes exactly the calculus of
fractions on its own side — the input to [Stacks 05SB], which is what moves definedness along a
morphism of `W` — together with the source's family of morphisms of `W`, and nothing else; the
source's hypothesis that `X'` *computes* `RF` ([Stacks 05SX]) is weakened to `RF` being defined
at `X'`, because invertibility of the canonical map `F(X') ⟶ RF(X')` is used nowhere, and the
source's statement is the instance of this one at a computing object. (2) The data are the
source's: one class `W` of morphisms of the *source* category `𝒟`, the index categories `X/W`
and `W/X` of morphisms of `W` out of, resp. into, the object in question, and the diagram valued
in `𝒟'` through `F` — no localization of `𝒟`, no change of `W`, and definedness in the source's
sense of essential constancy rather than in the Kan-extension sense of
`CategoryTheory.Functor.HasPointwiseRightDerivedFunctorAt`. (3) The source names no canonical map
in this lemma; the one canonical map in sight, `F(X') ⟶ RF(X')`, belongs to the hypothesis
"computes" that is dropped, and the notion of value that remains is pinned rather than merely
asserted, a value being a cocone, resp. cone, satisfying `IsRightDerivedValueAt`, resp.
`IsLeftDerivedValueAt`, hence carrying the coprojections, resp. projections, of [Stacks 05S9].
(4) Not degenerate: for `W = MorphismProperty.isomorphisms 𝒟` both calculi of fractions hold and
each `X` satisfies the hypothesis with `s = 𝟙 X`, the value being `F(X)`; and the hypothesis is
satisfiable non-trivially — for `W` the quasi-isomorphisms in `K⁺(𝒜)` with `𝒜` having enough
injectives, every object admits an injective resolution ([Stacks 013K]) and a bounded below
complex of injectives computes `RF` ([Stacks 05TH]), which is how [Stacks 05TI] concludes that
`RF : D⁺(𝒜) ⟶ 𝒟` is everywhere defined — while the conclusion is not automatic,
definedness being a genuine condition on `F` and `W`.

*Generality.* Situation 05S8 — `F` exact between triangulated categories and `W` a saturated
multiplicative system compatible with the triangulated structure — is not assumed: the argument
consists of [Stacks 05SB] applied at each object, and that lemma needs only a left, resp. right,
calculus of fractions on `W`. Nothing of the source's assertion is weakened by this, a saturated
multiplicative system having both calculi of fractions.

*Side conditions inside the conjuncts.* `W.HasLeftCalculusOfFractions` is an antecedent of the
first conjunct and `W.HasRightCalculusOfFractions` of the second, rather than instance arguments
of the theorem, so that neither part carries the other's hypothesis; a user with both available
supplies `inferInstance`.

*Duality.* Part (2) is stated directly in the pro-object form the source gives it, not as part
(1) for `F.op` and `W.op`; the two agree through the equivalence
`(W.Over ⊤ X)ᵒᵖ ≌ W.op.Under ⊤ (Opposite.op X)`, as for the underlying notions of value.

## Proof outline

# Everywhere-definedness of a derived functor from definedness along `W`

Let `F : 𝒟 ⥤ 𝒟'` be a functor and let `W` be a class of morphisms of `𝒟`. The right derived
functor `RF` is *defined at* `X` when the ind-object `X/W ⟶ 𝒟'`, `(s : X ⟶ X') ↦ F(X')`, is
essentially constant, and `LF` is *defined at* `X` when the pro-object `W/X ⟶ 𝒟'`,
`(s : X' ⟶ X) ↦ F(X')`, is essentially constant (Tag 05S9); `F` is right, resp. left, derivable
when this holds at every object (Tag 05SV).

Definedness of `RF` is insensitive to replacing an object by any object it maps to by a morphism
of `W` (Tag 05SB), so a single morphism `s : X ⟶ X'` of `W` with `RF` defined at `X'` suffices at
each `X`, and `RF` is everywhere defined; this is Tag 05SB(1) applied at each object. Dually a
single morphism `s : X' ⟶ X` of `W` with `LF` defined at `X'` suffices, and the pro-side
transport it rests on is proved here: a value of `LF` at the source `X'` of a morphism of `W`
induces one at its target `X`, on the same vertex, whose projection at `a : W/X` is
`LF(X') ⟶ F(b.left) ⟶ F(a.left)` for any square `f ≫ a.hom = b.hom ≫ s` with `b : W/X'` — this
is well defined and independent of the square because two objects of `W/X'` admit a common
source and two morphisms out of one of them that agree after postcomposition with a morphism of
`W` agree after refining it, which are the axioms MS2 and MS3 of a right calculus of fractions.

## Implementation notes

Part (1) is Tag 05SB(1) applied at each object, in the direction that carries definedness from
the target of a morphism of `W` to its source. Part (2) needs the pro-side statement, which Tag
05SB does not carry: it is stated there for the ind-object only, with the remark that the
pro-side is the ind-side for `F.op`, `W.op` and `s.op`. Rather than transporting values through
the equivalence `(W.Over ⊤ X)ᵒᵖ ≌ W.op.Under ⊤ (Opposite.op X)` and the identification of the
two ind-objects it induces, the one implication needed, `exists_isLeftDerivedValueAt_of_mem`, is
proved directly in the pro-object form; it is the dual of the transport half of Tag 05SB(1) and
does not need the restriction half, which is the long one. The full pro-side statement of Tag
05SB — the equivalence of definedness at source and target together with the isomorphism `LF(s)`
of Tag 05SA — is a genuine missing lemma of the theory rather than a step of this tag.

Each projection is named: `prj` at an object of `W/X`, and the object of `W/X`
attached to `b : W/X'` by postcomposition with `s` is `postcompOver`, so that the
equalities below are between morphisms whose sources and targets are projections of the
variables in play.

## References

* [Stacks project, Tag 05T1](https://stacks.math.columbia.edu/tag/05T1); the situation is
  Tag 05S8, definedness and values are Tag 05S9, everywhere-definedness is Tag 05SV, computing
  objects are Tag 05SX, and the transport of definedness along a morphism of `W` is Tag 05SB.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace DerivedFunctorDerivable

open CategoryTheory Limits

section Pro

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']

/-- The projection of a cone on the pro-object at `X`, with its target written as
`F(a.left)`. -/
private abbrev prj {W : MorphismProperty D} {X : D} {F : D ⥤ D'}
    (c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F))
    (a : W.Over ⊤ X) : c.pt ⟶ F.obj a.left := c.π.app a

/-- Cone compatibility on the pro-object at `X`, in terms of morphisms of `𝒟`. -/
private lemma prj_comp_map {W : MorphismProperty D} {X : D} (F : D ⥤ D')
    (c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F))
    {a a' : W.Over ⊤ X} (g : a.left ⟶ a'.left) (hg : g ≫ a'.hom = a.hom) :
    prj c a ≫ F.map g = prj c a' :=
  c.w (MorphismProperty.Over.homMk g hg)

/-- Postcomposition with a morphism `s : X' ⟶ X` of `W`, as a map from the objects of `W/X'` to
the objects of `W/X`. -/
private abbrev postcompOver {W : MorphismProperty D} [W.IsStableUnderComposition] {X X' : D}
    {s : X' ⟶ X} (hs : W s) (b : W.Over ⊤ X') : W.Over ⊤ X :=
  MorphismProperty.Over.mk ⊤ (b.hom ≫ s) (W.comp_mem _ _ b.prop hs)

section Fractions

variable {W : MorphismProperty D} [W.HasRightCalculusOfFractions]

/-- **MS2**, first use: any `s : X' ⟶ X` and any `a : W/X` fit into a square
`f ≫ a.hom = b.hom ≫ s` with `b : W/X'`. -/
public lemma exists_over_sq {X X' : D} (s : X' ⟶ X) (a : W.Over ⊤ X) :
    ∃ (b : W.Over ⊤ X') (f : b.left ⟶ a.left), f ≫ a.hom = b.hom ≫ s := by
  obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk s a.hom a.prop).exists_rightFraction
  exact ⟨MorphismProperty.Over.mk ⊤ ψ.s ψ.hs, ψ.f, hψ.symm⟩

/-- **MS2**, second use: any two objects of `W/X'` admit a common source. -/
private lemma exists_over_common {X' : D} (b₁ b₂ : W.Over ⊤ X') :
    ∃ (b : W.Over ⊤ X') (g₁ : b.left ⟶ b₁.left) (g₂ : b.left ⟶ b₂.left),
      g₁ ≫ b₁.hom = b.hom ∧ g₂ ≫ b₂.hom = b.hom := by
  obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk b₁.hom b₂.hom b₂.prop).exists_rightFraction
  exact ⟨MorphismProperty.Over.mk ⊤ (ψ.s ≫ b₁.hom) (W.comp_mem _ _ ψ.hs b₁.prop), ψ.s, ψ.f,
    rfl, hψ.symm⟩

/-- **MS3**: two morphisms out of an object of `W/X'` that agree after postcomposition with a
morphism of `W` agree after refining the object of `W/X'`. -/
private lemma exists_over_precomp_eq {X' : D} (b : W.Over ⊤ X') {Z Z' : D} (σ : Z ⟶ Z')
    (hσ : W σ) (h₁ h₂ : b.left ⟶ Z) (h : h₁ ≫ σ = h₂ ≫ σ) :
    ∃ (b' : W.Over ⊤ X') (q : b'.left ⟶ b.left),
      q ≫ b.hom = b'.hom ∧ q ≫ h₁ = q ≫ h₂ := by
  obtain ⟨V, t, ht, hteq⟩ := MorphismProperty.HasRightCalculusOfFractions.ext h₁ h₂ σ hσ h
  exact ⟨MorphismProperty.Over.mk ⊤ (t ≫ b.hom) (W.comp_mem _ _ ht b.prop), t, rfl, hteq⟩

end Fractions

section Transport

variable {W : MorphismProperty D} [W.HasRightCalculusOfFractions] {X X' : D}

/-- The transported projection does not depend on the chosen square. -/
private lemma prj_comp_map_eq {s : X' ⟶ X} (F : D ⥤ D')
    (d : Cone (MorphismProperty.Over.forget W ⊤ X' ⋙ Over.forget X' ⋙ F))
    {a : W.Over ⊤ X} {b₁ b₂ : W.Over ⊤ X'}
    (f₁ : b₁.left ⟶ a.left) (f₂ : b₂.left ⟶ a.left)
    (h₁ : f₁ ≫ a.hom = b₁.hom ≫ s) (h₂ : f₂ ≫ a.hom = b₂.hom ≫ s) :
    prj d b₁ ≫ F.map f₁ = prj d b₂ ≫ F.map f₂ := by
  obtain ⟨b, g₁, g₂, hg₁, hg₂⟩ := exists_over_common b₁ b₂
  have key : (g₁ ≫ f₁) ≫ a.hom = (g₂ ≫ f₂) ≫ a.hom := by
    rw [Category.assoc, Category.assoc, h₁, h₂, reassoc_of% hg₁, reassoc_of% hg₂]
  obtain ⟨b', q, hq, heq⟩ :=
    exists_over_precomp_eq b a.hom a.prop (g₁ ≫ f₁) (g₂ ≫ f₂) key
  have heq' : (q ≫ g₁) ≫ f₁ = (q ≫ g₂) ≫ f₂ := by simpa using heq
  rw [← prj_comp_map F d g₁ hg₁, ← prj_comp_map F d g₂ hg₂, ← prj_comp_map F d q hq]
  calc ((prj d b' ≫ F.map q) ≫ F.map g₁) ≫ F.map f₁
      = prj d b' ≫ F.map ((q ≫ g₁) ≫ f₁) := by simp
    _ = prj d b' ≫ F.map ((q ≫ g₂) ≫ f₂) := by rw [heq']
    _ = ((prj d b' ≫ F.map q) ≫ F.map g₂) ≫ F.map f₂ := by simp

/-- The projection at `a : W/X` of the cone transported from a cone on the pro-object at `X'`
along a morphism `s : X' ⟶ X`. -/
private noncomputable def transportπ (s : X' ⟶ X) (F : D ⥤ D')
    (d : Cone (MorphismProperty.Over.forget W ⊤ X' ⋙ Over.forget X' ⋙ F))
    (a : W.Over ⊤ X) : d.pt ⟶ F.obj a.left :=
  prj d (exists_over_sq s a).choose ≫ F.map (exists_over_sq s a).choose_spec.choose

private lemma transportπ_eq (s : X' ⟶ X) (F : D ⥤ D')
    (d : Cone (MorphismProperty.Over.forget W ⊤ X' ⋙ Over.forget X' ⋙ F))
    (a : W.Over ⊤ X) (b : W.Over ⊤ X') (f : b.left ⟶ a.left)
    (hf : f ≫ a.hom = b.hom ≫ s) : transportπ s F d a = prj d b ≫ F.map f :=
  prj_comp_map_eq F d _ f (exists_over_sq s a).choose_spec.choose_spec hf

/-- At an object of `W/X` of the form `b.hom ≫ s`, for `b : W/X'`, the transported projection is
the projection at `b`. -/
private lemma transportπ_postcompOver {s : X' ⟶ X} (hs : W s) (F : D ⥤ D')
    (d : Cone (MorphismProperty.Over.forget W ⊤ X' ⋙ Over.forget X' ⋙ F))
    (b : W.Over ⊤ X') : transportπ s F d (postcompOver hs b) = prj d b := by
  have h : transportπ s F d (postcompOver hs b) = prj d b ≫ F.map (𝟙 b.left) :=
    transportπ_eq s F d (postcompOver hs b) b (𝟙 b.left) (Category.id_comp _)
  rw [h, F.map_id, Category.comp_id]

/-- The cone on the pro-object at `X` transported from a cone on the pro-object at `X'`. -/
private noncomputable def transportCone (s : X' ⟶ X) (F : D ⥤ D')
    (d : Cone (MorphismProperty.Over.forget W ⊤ X' ⋙ Over.forget X' ⋙ F)) :
    Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) where
  pt := d.pt
  π :=
    { app := transportπ s F d
      naturality := fun a a' u => by
        obtain ⟨b, f, hf⟩ := exists_over_sq s a
        have h1 : transportπ s F d a = prj d b ≫ F.map f := transportπ_eq s F d a b f hf
        have h2 : transportπ s F d a' = prj d b ≫ F.map (f ≫ u.left) :=
          transportπ_eq s F d a' b (f ≫ u.left) (by
            rw [Category.assoc, MorphismProperty.Over.w, hf])
        change 𝟙 d.pt ≫ transportπ s F d a' = transportπ s F d a ≫ F.map u.left
        rw [h1, h2]
        simp }

/-- A value of `LF` at the source of a morphism of `W` transports to a value of `LF` at its
target: the pro-side of Tag 05SB(1), in the direction Tag 05T1(2) uses. -/
private lemma isLeftDerivedValueAt_transportCone {s : X' ⟶ X} (hs : W s) (F : D ⥤ D')
    {d : Cone (MorphismProperty.Over.forget W ⊤ X' ⋙ Over.forget X' ⋙ F)}
    (hd : F.IsLeftDerivedValueAt W X' d) :
    F.IsLeftDerivedValueAt W X (transportCone s F d) := by
  obtain ⟨b₀, ρ, hρ, hbd⟩ := hd
  have hρ' : prj d b₀ ≫ ρ = 𝟙 d.pt := hρ
  refine ⟨postcompOver hs b₀, ρ, ?_, ?_⟩
  · change transportπ s F d (postcompOver hs b₀) ≫ ρ = 𝟙 d.pt
    rw [transportπ_postcompOver hs F d b₀]
    exact hρ'
  · intro a
    obtain ⟨b, f, hf⟩ := exists_over_sq s a
    obtain ⟨b', μ, ν, hμν⟩ := hbd b
    have hμν' : F.map μ.left = F.map ν.left ≫ ρ ≫ prj d b := hμν
    refine ⟨postcompOver hs b',
      MorphismProperty.Over.homMk (μ.left ≫ f)
        (by
          calc (μ.left ≫ f) ≫ a.hom = μ.left ≫ f ≫ a.hom := by simp
            _ = μ.left ≫ b.hom ≫ s := by rw [hf]
            _ = b'.hom ≫ s := by rw [← Category.assoc, MorphismProperty.Over.w]),
      MorphismProperty.Over.homMk ν.left (by
        calc ν.left ≫ b₀.hom ≫ s = (ν.left ≫ b₀.hom) ≫ s := by simp
          _ = b'.hom ≫ s := by rw [MorphismProperty.Over.w]), ?_⟩
    change F.map (μ.left ≫ f) = F.map ν.left ≫ ρ ≫ transportπ s F d a
    rw [transportπ_eq s F d a b f hf, F.map_comp, hμν']
    simp

/-- If `LF` is defined at the source `X'` of a morphism `s : X' ⟶ X` of `W`, it is defined at
`X`; the dual of the transport half of Tag 05SB(1). -/
private lemma exists_isLeftDerivedValueAt_of_mem (F : D ⥤ D') {s : X' ⟶ X} (hs : W s)
    (h : ∃ d, F.IsLeftDerivedValueAt W X' d) : ∃ c, F.IsLeftDerivedValueAt W X c :=
  ⟨_, isLeftDerivedValueAt_transportCone hs F h.choose_spec⟩

end Transport

end Pro

end DerivedFunctorDerivable

namespace CategoryTheory.Functor

open DerivedFunctorDerivable
open CategoryTheory Limits

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']

/-- **Stacks 05T1**. Let `F : 𝒟 ⥤ 𝒟'` be a functor and let `W` be a class of morphisms of `𝒟`.

1. If `W` has a left calculus of fractions and if for every object `X` of `𝒟` there is a
   morphism `s : X ⟶ X'` in `W` such that the right derived functor `RF` is defined at `X'`,
   then `RF` is everywhere defined, i.e. `F` is right derivable.
2. If `W` has a right calculus of fractions and if for every object `X` of `𝒟` there is a
   morphism `s : X' ⟶ X` in `W` such that the left derived functor `LF` is defined at `X'`,
   then `LF` is everywhere defined, i.e. `F` is left derivable.

Definedness and values are those of Stacks 05S9, and everywhere-definedness that of Stacks 05SV.
The source assumes the stronger hypothesis that `X'` *computes* `RF`, resp. `LF` (Stacks 05SX),
and works in Situation 05S8; the canonical map `F(X') ⟶ RF(X')` plays no role and neither does
the triangulated structure, only the relevant calculus of fractions on `W`. -/
@[stacks 05T1]
public theorem isRightDerivable_and_isLeftDerivable_of_forall_exists_isDerivedValueAt
    (F : D ⥤ D') (W : MorphismProperty D) :
    (W.HasLeftCalculusOfFractions →
        (∀ X : D, ∃ (X' : D) (s : X ⟶ X'), W s ∧ ∃ c, F.IsRightDerivedValueAt W X' c) →
        F.IsRightDerivable W) ∧
      (W.HasRightCalculusOfFractions →
        (∀ X : D, ∃ (X' : D) (s : X' ⟶ X), W s ∧ ∃ c, F.IsLeftDerivedValueAt W X' c) →
        F.IsLeftDerivable W) := by
  refine ⟨fun hW h X => ?_, fun hW h X => ?_⟩
  · have := hW
    obtain ⟨X', s, hs, hX'⟩ := h X
    exact (Functor.exists_isRightDerivedValueAt_iff_and_isIso_of_mem F W hs).1.mpr hX'
  · have := hW
    obtain ⟨X', s, hs, hX'⟩ := h X
    exact exists_isLeftDerivedValueAt_of_mem F hs hX'

end CategoryTheory.Functor

end

end
