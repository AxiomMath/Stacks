module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CategoricalPullbackDiagonal

/-!
# Full faithfulness of a comparison functor and the diagonal of its square (Stacks 0CMW)

Fix a 2-commutative square of categories

```
C' --a--> C
|         |
u         p
↓         ↓
D' --b--> D
```

that is, functors `a`, `u`, `p`, `b` together with a natural isomorphism `α : a ⋙ p ≅ u ⋙ b`.
It has two comparison functors into explicit 2-fibre products
(`CategoryTheory.Limits.CategoricalPullback`):

* `A : C' ⥤ C ×_D D'`, the comparison of the square itself;
* `B : C' ⥤ C ×_{Δ_p, C ×_D C} (C' ×_{D'} C')`, the comparison of the square obtained by
  passing to relative diagonals.

This file proves that, when `C` and `D'` are groupoids, `A` is fully faithful if and only if `B`
is an equivalence. This is the statement of pure category theory that the proof of Stacks 0CMW
reduces the equivalence of its conditions (1) and (2) to, once "2-fibre products commute with
filtered colimits" has replaced the colimits of fibre categories by `C'` and `D'`: condition (2)
is full faithfulness of `A` and condition (1) is `B` being an equivalence.

The proof is the source's: the target of `B` is identified with the 2-fibre product
`C' ×_{A, C ×_D D', A} C'`, under which `B` becomes the diagonal of `A`, and then Stacks 04Z7 in
the form `CategoryTheory.Limits.CategoricalPullback.fullyFaithful_iff_isEquivalence_diagonal`
applies. The identification sends a quadruple `(c, (x, y, χ), (ξ₁, ξ₂))` to
`(x, y, (ξ₁⁻¹ ≫ ξ₂, χ))`; it is an equivalence rather than an isomorphism of categories, since
`c` is only isomorphic to `a x`, not equal to it.

## Main definitions

* `CategoryTheory.Limits.CategoricalPullback.squareComparison`: the comparison `A` of the square.
* `CategoryTheory.Limits.CategoricalPullback.mapDiagonal`: the functor
  `C' ×_{D'} C' ⥤ C ×_D C` induced by `a` and the filler `α`.
* `CategoryTheory.Limits.CategoricalPullback.diagonalComparison`: the comparison `B` of the
  square of relative diagonals.

## Main results

* `CategoryTheory.Limits.CategoricalPullback.diagonalTargetEquivalence`: the target of `B` is
  equivalent to `C' ×_{A} C'`.
* `CategoryTheory.Limits.CategoricalPullback.diagonalComparisonIso`: under that equivalence `B`
  becomes the diagonal of `A`.
* `CategoryTheory.Limits.CategoricalPullback.full_squareComparison_of_essSurj_diagonalComparison`:
  `A` is full as soon as `B` is essentially surjective.
* `CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff`: `A` is fully
  faithful if and only if `B` is an equivalence.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 04Z7](https://stacks.math.columbia.edu/tag/04Z7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.CategoricalPullback

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C' : Type u₁} {C : Type u₂} {D' : Type u₃} {D : Type u₄}
  [Category.{v₁} C'] [Category.{v₂} C] [Category.{v₃} D'] [Category.{v₄} D]
  (a : C' ⥤ C) (u : C' ⥤ D') (p : C ⥤ D) (b : D' ⥤ D) (α : a ⋙ p ≅ u ⋙ b)

/-! ### The two comparison functors -/

/-- The comparison functor `A : C' ⥤ C ×_D D'` of a 2-commutative square: it sends `x` to the
triple `(a x, u x, α_x)`. -/
@[implicit_reducible]
def squareComparison : C' ⥤ p ⊡ b where
  obj x := { fst := a.obj x, snd := u.obj x, iso := α.app x }
  map f := { fst := a.map f, snd := u.map f, w := α.hom.naturality f }

/-- The first component of `A x` is `a x`. -/
@[simp] lemma squareComparison_obj_fst (x : C') :
    ((squareComparison a u p b α).obj x).fst = a.obj x := rfl

/-- The second component of `A x` is `u x`. -/
@[simp] lemma squareComparison_obj_snd (x : C') :
    ((squareComparison a u p b α).obj x).snd = u.obj x := rfl

/-- The structural isomorphism of `A x` is the component `α_x`. -/
@[simp] lemma squareComparison_obj_iso (x : C') :
    ((squareComparison a u p b α).obj x).iso = α.app x := rfl

/-- The first component of `A f` is `a f`. -/
@[simp] lemma squareComparison_map_fst {x y : C'} (f : x ⟶ y) :
    ((squareComparison a u p b α).map f).fst = a.map f := rfl

/-- The second component of `A f` is `u f`. -/
@[simp] lemma squareComparison_map_snd {x y : C'} (f : x ⟶ y) :
    ((squareComparison a u p b α).map f).snd = u.map f := rfl

/-- The functor `C' ×_{D'} C' ⥤ C ×_D C` induced by `a` and the filler `α`: it sends a triple
`(x, y, χ : u x ≅ u y)` to `(a x, a y, α_x ≫ b χ ≫ α_y⁻¹)`. -/
@[implicit_reducible]
def mapDiagonal : u ⊡ u ⥤ p ⊡ p where
  obj t :=
    { fst := a.obj t.fst
      snd := a.obj t.snd
      iso := α.app t.fst ≪≫ b.mapIso t.iso ≪≫ (α.app t.snd).symm }
  map {t t'} m :=
    { fst := a.map m.fst
      snd := a.map m.snd
      w := by
        have h₁ := α.hom.naturality m.fst
        have h₄ := α.inv.naturality m.snd
        have h₃ : b.map (u.map m.fst) ≫ b.map t'.iso.hom =
            b.map t.iso.hom ≫ b.map (u.map m.snd) := by
          rw [← b.map_comp, ← b.map_comp, m.w]
        simp only [Functor.comp_map] at h₁ h₄
        simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
          Category.assoc]
        rw [reassoc_of% h₁, reassoc_of% h₃, h₄] }
  map_id t := by apply CategoricalPullback.hom_ext <;> simp
  map_comp f g := by apply CategoricalPullback.hom_ext <;> simp

/-- The first component of the image of `(x, y, χ)` under `mapDiagonal` is `a x`. -/
@[simp] lemma mapDiagonal_obj_fst (t : u ⊡ u) :
    ((mapDiagonal a u p b α).obj t).fst = a.obj t.fst := rfl

/-- The second component of the image of `(x, y, χ)` under `mapDiagonal` is `a y`. -/
@[simp] lemma mapDiagonal_obj_snd (t : u ⊡ u) :
    ((mapDiagonal a u p b α).obj t).snd = a.obj t.snd := rfl

/-- The structural isomorphism of the image of `(x, y, χ)` under `mapDiagonal` is
`α_x ≫ b χ ≫ α_y⁻¹`. -/
@[simp] lemma mapDiagonal_obj_iso (t : u ⊡ u) :
    ((mapDiagonal a u p b α).obj t).iso =
      α.app t.fst ≪≫ b.mapIso t.iso ≪≫ (α.app t.snd).symm := rfl

/-- The first component of the image of a morphism under `mapDiagonal` is `a` applied to its
first component. -/
@[simp] lemma mapDiagonal_map_fst {t t' : u ⊡ u} (m : t ⟶ t') :
    ((mapDiagonal a u p b α).map m).fst = a.map m.fst := rfl

/-- The second component of the image of a morphism under `mapDiagonal` is `a` applied to its
second component. -/
@[simp] lemma mapDiagonal_map_snd {t t' : u ⊡ u} (m : t ⟶ t') :
    ((mapDiagonal a u p b α).map m).snd = a.map m.snd := rfl

/-- The filler of the square of relative diagonals: on an object `x` of `C'` both `Δ_p (a x)`
and `(a ×_α a) (Δ_u x)` are the triple `(a x, a x, 𝟙)`. -/
def diagonalSquareFiller : a ⋙ diagonal p ≅ diagonal u ⋙ mapDiagonal a u p b α :=
  NatIso.ofComponents (fun _ => mkIso (Iso.refl _) (Iso.refl _) (by simp))
    (fun _ => by apply CategoricalPullback.hom_ext <;> simp)

/-- The first component of the filler of the square of relative diagonals at `x` is the
identity of `a x`. -/
@[simp] lemma diagonalSquareFiller_hom_app_fst (x : C') :
    ((diagonalSquareFiller a u p b α).hom.app x).fst = 𝟙 (a.obj x) := by
  simp [diagonalSquareFiller]

/-- The second component of the filler of the square of relative diagonals at `x` is the
identity of `a x`. -/
@[simp] lemma diagonalSquareFiller_hom_app_snd (x : C') :
    ((diagonalSquareFiller a u p b α).hom.app x).snd = 𝟙 (a.obj x) := by
  simp [diagonalSquareFiller]

/-- The comparison functor `B : C' ⥤ C ×_{Δ_p, C ×_D C} (C' ×_{D'} C')` of the square of
relative diagonals of a 2-commutative square. -/
@[implicit_reducible]
def diagonalComparison : C' ⥤ (diagonal p) ⊡ (mapDiagonal a u p b α) :=
  squareComparison a (diagonal u) (diagonal p) (mapDiagonal a u p b α)
    (diagonalSquareFiller a u p b α)

/-! ### The target of `B` is the 2-fibre product of `A` with itself -/

/-- The first component of the compatibility condition on a morphism of the target of `B`. -/
lemma diagonalTarget_fst_eq {t t' : (diagonal p) ⊡ (mapDiagonal a u p b α)} (m : t ⟶ t') :
    m.fst ≫ t'.iso.hom.fst = t.iso.hom.fst ≫ a.map m.snd.fst := by
  simpa only [comp_fst, diagonal_map_fst, mapDiagonal_map_fst] using
    congrArg CategoricalPullback.Hom.fst m.w

/-- The second component of the compatibility condition on a morphism of the target of `B`. -/
lemma diagonalTarget_snd_eq {t t' : (diagonal p) ⊡ (mapDiagonal a u p b α)} (m : t ⟶ t') :
    m.fst ≫ t'.iso.hom.snd = t.iso.hom.snd ≫ a.map m.snd.snd := by
  simpa only [comp_snd, diagonal_map_snd, mapDiagonal_map_snd] using
    congrArg CategoricalPullback.Hom.snd m.w

/-- The compatibility condition on the filler of an object of the target of `B`, written out. -/
lemma diagonalTarget_iso_w (t : (diagonal p) ⊡ (mapDiagonal a u p b α)) :
    p.map t.iso.hom.fst ≫ (α.app t.snd.fst).hom ≫ b.map t.snd.iso.hom ≫
      (α.app t.snd.snd).inv = p.map t.iso.hom.snd := by
  have h := t.iso.hom.w.trans (Category.id_comp (p.map t.iso.hom.snd))
  simpa only [mapDiagonal_obj_iso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc] using h

/-- The pair `(ξ₁⁻¹ ≫ ξ₂, χ)` attached to a quadruple of the target of `B` is compatible with
the structural isomorphisms of `A`. -/
lemma diagonalTarget_w (t : (diagonal p) ⊡ (mapDiagonal a u p b α)) :
    p.map (inv t.iso.hom.fst ≫ t.iso.hom.snd) ≫ (α.app t.snd.snd).hom =
      (α.app t.snd.fst).hom ≫ b.map t.snd.iso.hom := by
  rw [p.map_comp, Functor.map_inv, ← diagonalTarget_iso_w a u p b α t]
  simp

/-- The structural isomorphism of the image of a quadruple `(c, (x, y, χ), (ξ₁, ξ₂))` of the
target of `B`: the pair `(ξ₁⁻¹ ≫ ξ₂, χ)`, read as an isomorphism `A x ≅ A y`. -/
@[implicit_reducible]
noncomputable def diagonalTargetIso (t : (diagonal p) ⊡ (mapDiagonal a u p b α)) :
    (squareComparison a u p b α).obj t.snd.fst ≅
      (squareComparison a u p b α).obj t.snd.snd :=
  mkIso ((asIso t.iso.hom.fst).symm ≪≫ asIso t.iso.hom.snd) t.snd.iso
    (diagonalTarget_w a u p b α t)

/-- The first component of `diagonalTargetIso` at `(c, (x, y, χ), (ξ₁, ξ₂))` is `ξ₁⁻¹ ≫ ξ₂`. -/
@[simp] lemma diagonalTargetIso_hom_fst (t : (diagonal p) ⊡ (mapDiagonal a u p b α)) :
    (diagonalTargetIso a u p b α t).hom.fst = inv t.iso.hom.fst ≫ t.iso.hom.snd := rfl

/-- The second component of `diagonalTargetIso` at `(c, (x, y, χ), (ξ₁, ξ₂))` is `χ`. -/
@[simp] lemma diagonalTargetIso_hom_snd (t : (diagonal p) ⊡ (mapDiagonal a u p b α)) :
    (diagonalTargetIso a u p b α t).hom.snd = t.snd.iso.hom := rfl

/-- Compatibility of the structural isomorphisms with a morphism of the target of `B`. -/
lemma diagonalTarget_map_fst {t t' : (diagonal p) ⊡ (mapDiagonal a u p b α)} (m : t ⟶ t') :
    a.map m.snd.fst ≫ inv t'.iso.hom.fst ≫ t'.iso.hom.snd =
      (inv t.iso.hom.fst ≫ t.iso.hom.snd) ≫ a.map m.snd.snd := by
  have h₁ := diagonalTarget_fst_eq a u p b α m
  have h₂ := diagonalTarget_snd_eq a u p b α m
  rw [Category.assoc, ← h₂, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact h₁.symm

/-- The identification of the target of `B` with `C' ×_{A} C'`: the quadruple
`(c, (x, y, χ), (ξ₁, ξ₂))` goes to `(x, y, (ξ₁⁻¹ ≫ ξ₂, χ))`, and a morphism to its second
component. -/
@[implicit_reducible]
noncomputable def diagonalTargetToPullback :
    (diagonal p) ⊡ (mapDiagonal a u p b α) ⥤
      (squareComparison a u p b α) ⊡ (squareComparison a u p b α) where
  obj t := { fst := t.snd.fst, snd := t.snd.snd, iso := diagonalTargetIso a u p b α t }
  map {t t'} m :=
    { fst := m.snd.fst
      snd := m.snd.snd
      w := by
        apply CategoricalPullback.hom_ext
        · simpa only [comp_fst, squareComparison_map_fst, diagonalTargetIso_hom_fst] using
            diagonalTarget_map_fst a u p b α m
        · simpa only [comp_snd, squareComparison_map_snd, diagonalTargetIso_hom_snd] using
            m.snd.w }
  map_id t := by apply CategoricalPullback.hom_ext <;> simp
  map_comp f g := by apply CategoricalPullback.hom_ext <;> simp

/-- The first component of the image of `(c, (x, y, χ), (ξ₁, ξ₂))` under
`diagonalTargetToPullback` is `x`. -/
@[simp] lemma diagonalTargetToPullback_obj_fst (t : (diagonal p) ⊡ (mapDiagonal a u p b α)) :
    ((diagonalTargetToPullback a u p b α).obj t).fst = t.snd.fst := rfl

/-- The second component of the image of `(c, (x, y, χ), (ξ₁, ξ₂))` under
`diagonalTargetToPullback` is `y`. -/
@[simp] lemma diagonalTargetToPullback_obj_snd (t : (diagonal p) ⊡ (mapDiagonal a u p b α)) :
    ((diagonalTargetToPullback a u p b α).obj t).snd = t.snd.snd := rfl

/-- The structural isomorphism of the image of an object under `diagonalTargetToPullback` is
`diagonalTargetIso`. -/
@[simp] lemma diagonalTargetToPullback_obj_iso (t : (diagonal p) ⊡ (mapDiagonal a u p b α)) :
    ((diagonalTargetToPullback a u p b α).obj t).iso = diagonalTargetIso a u p b α t := rfl

/-- The first component of the image of a morphism `m` under `diagonalTargetToPullback` is the
first component of the second component of `m`. -/
@[simp] lemma diagonalTargetToPullback_map_fst
    {t t' : (diagonal p) ⊡ (mapDiagonal a u p b α)} (m : t ⟶ t') :
    ((diagonalTargetToPullback a u p b α).map m).fst = m.snd.fst := rfl

/-- The second component of the image of a morphism `m` under `diagonalTargetToPullback` is the
second component of the second component of `m`. -/
@[simp] lemma diagonalTargetToPullback_map_snd
    {t t' : (diagonal p) ⊡ (mapDiagonal a u p b α)} (m : t ⟶ t') :
    ((diagonalTargetToPullback a u p b α).map m).snd = m.snd.snd := rfl

/-- The first component of the compatibility condition on a morphism of `C' ×_{A} C'`. -/
lemma squarePullback_fst_eq
    {s s' : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)} (m : s ⟶ s') :
    a.map m.fst ≫ s'.iso.hom.fst = s.iso.hom.fst ≫ a.map m.snd := by
  simpa only [comp_fst, squareComparison_map_fst] using
    congrArg CategoricalPullback.Hom.fst m.w

/-- The second component of the compatibility condition on a morphism of `C' ×_{A} C'`. -/
lemma squarePullback_snd_eq
    {s s' : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)} (m : s ⟶ s') :
    u.map m.fst ≫ s'.iso.hom.snd = s.iso.hom.snd ≫ u.map m.snd := by
  simpa only [comp_snd, squareComparison_map_snd] using
    congrArg CategoricalPullback.Hom.snd m.w

/-- The filler of an object of `C' ×_{A} C'`, read in `D`. -/
lemma squarePullback_iso_w
    (s : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)) :
    (α.app s.fst).hom ≫ b.map s.iso.hom.snd ≫ (α.app s.snd).inv = p.map s.iso.hom.fst := by
  have h : p.map s.iso.hom.fst ≫ (α.app s.snd).hom =
      (α.app s.fst).hom ≫ b.map s.iso.hom.snd := by
    simpa only [squareComparison_obj_iso] using s.iso.hom.w
  rw [← Category.assoc, ← h, Category.assoc]
  simp

/-- The structural isomorphism `u x ≅ u y` underlying an object `(x, y, (ψ₁, ψ₂))` of
`C' ×_{A} C'`. -/
def squarePullbackSndIso
    (s : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)) :
    u.obj s.fst ≅ u.obj s.snd :=
  Iso.mk s.iso.hom.snd s.iso.inv.snd (by simp [← comp_snd]) (by simp [← comp_snd])

/-- The structural isomorphism `a x ≅ a y` underlying an object `(x, y, (ψ₁, ψ₂))` of
`C' ×_{A} C'`. -/
def squarePullbackFstIso
    (s : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)) :
    a.obj s.fst ≅ a.obj s.snd :=
  Iso.mk s.iso.hom.fst s.iso.inv.fst (by simp [← comp_fst]) (by simp [← comp_fst])

/-- The quasi-inverse of `CategoryTheory.Limits.CategoricalPullback.diagonalTargetToPullback`:
the triple `(x, y, (ψ₁, ψ₂))` goes to the quadruple `(a x, (x, y, ψ₂), (𝟙, ψ₁))`. -/
@[implicit_reducible]
def pullbackToDiagonalTarget :
    (squareComparison a u p b α) ⊡ (squareComparison a u p b α) ⥤
      (diagonal p) ⊡ (mapDiagonal a u p b α) where
  obj s :=
    { fst := a.obj s.fst
      snd := { fst := s.fst, snd := s.snd, iso := squarePullbackSndIso a u p b α s }
      iso := mkIso (Iso.refl _) (squarePullbackFstIso a u p b α s) (by
        simp only [mapDiagonal_obj_iso, squarePullbackSndIso, squarePullbackFstIso,
          diagonal_obj_iso, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Functor.map_id,
          Functor.mapIso_hom, Category.id_comp]
        exact (squarePullback_iso_w a u p b α s).trans (Category.id_comp _).symm) }
  map {s s'} m :=
    { fst := a.map m.fst
      snd :=
        { fst := m.fst
          snd := m.snd
          w := by
            simpa only [squarePullbackSndIso] using
              squarePullback_snd_eq a u p b α m }
      w := by
        apply CategoricalPullback.hom_ext
        · simp
        · simpa only [comp_snd, diagonal_map_snd, mapDiagonal_map_snd, mkIso_hom_snd,
            squarePullbackFstIso] using squarePullback_fst_eq a u p b α m }
  map_id s := by
    apply CategoricalPullback.hom_ext
    · simp
    · apply CategoricalPullback.hom_ext <;> simp
  map_comp f g := by
    apply CategoricalPullback.hom_ext
    · simp
    · apply CategoricalPullback.hom_ext <;> simp

/-- The first component of the image of `(x, y, (ψ₁, ψ₂))` under `pullbackToDiagonalTarget` is
`a x`. -/
@[simp] lemma pullbackToDiagonalTarget_obj_fst
    (s : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)) :
    ((pullbackToDiagonalTarget a u p b α).obj s).fst = a.obj s.fst := rfl

/-- The image of `(x, y, (ψ₁, ψ₂))` under `pullbackToDiagonalTarget` has `x` as the first
component of its second component. -/
@[simp] lemma pullbackToDiagonalTarget_obj_snd_fst
    (s : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)) :
    ((pullbackToDiagonalTarget a u p b α).obj s).snd.fst = s.fst := rfl

/-- The image of `(x, y, (ψ₁, ψ₂))` under `pullbackToDiagonalTarget` has `y` as the second
component of its second component. -/
@[simp] lemma pullbackToDiagonalTarget_obj_snd_snd
    (s : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)) :
    ((pullbackToDiagonalTarget a u p b α).obj s).snd.snd = s.snd := rfl

/-- The image of `(x, y, (ψ₁, ψ₂))` under `pullbackToDiagonalTarget` has `ψ₂` as the
structural isomorphism of its second component. -/
@[simp] lemma pullbackToDiagonalTarget_obj_snd_iso_hom
    (s : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)) :
    ((pullbackToDiagonalTarget a u p b α).obj s).snd.iso.hom = s.iso.hom.snd := rfl

/-- The forward morphism of `squarePullbackSndIso` at `(x, y, (ψ₁, ψ₂))` is `ψ₂`. -/
@[simp] lemma squarePullbackSndIso_hom
    (s : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)) :
    (squarePullbackSndIso a u p b α s).hom = s.iso.hom.snd := rfl

/-- The forward morphism of `squarePullbackFstIso` at `(x, y, (ψ₁, ψ₂))` is `ψ₁`. -/
@[simp] lemma squarePullbackFstIso_hom
    (s : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)) :
    (squarePullbackFstIso a u p b α s).hom = s.iso.hom.fst := rfl

/-- The first component of the filler of the image of `(x, y, (ψ₁, ψ₂))` under
`pullbackToDiagonalTarget` is the identity of `a x`. -/
@[simp] lemma pullbackToDiagonalTarget_obj_iso_hom_fst
    (s : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)) :
    ((pullbackToDiagonalTarget a u p b α).obj s).iso.hom.fst = 𝟙 (a.obj s.fst) := rfl

/-- The second component of the filler of the image of `(x, y, (ψ₁, ψ₂))` under
`pullbackToDiagonalTarget` is `ψ₁`. -/
@[simp] lemma pullbackToDiagonalTarget_obj_iso_hom_snd
    (s : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)) :
    ((pullbackToDiagonalTarget a u p b α).obj s).iso.hom.snd = s.iso.hom.fst := rfl

/-- The first component of the image of a morphism `m` under `pullbackToDiagonalTarget` is `a`
applied to the first component of `m`. -/
@[simp] lemma pullbackToDiagonalTarget_map_fst
    {s s' : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)} (m : s ⟶ s') :
    ((pullbackToDiagonalTarget a u p b α).map m).fst = a.map m.fst := rfl

/-- The image of a morphism `m` under `pullbackToDiagonalTarget` has the first component of `m`
as the first component of its second component. -/
@[simp] lemma pullbackToDiagonalTarget_map_snd_fst
    {s s' : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)} (m : s ⟶ s') :
    ((pullbackToDiagonalTarget a u p b α).map m).snd.fst = m.fst := rfl

/-- The image of a morphism `m` under `pullbackToDiagonalTarget` has the second component of `m`
as the second component of its second component. -/
@[simp] lemma pullbackToDiagonalTarget_map_snd_snd
    {s s' : (squareComparison a u p b α) ⊡ (squareComparison a u p b α)} (m : s ⟶ s') :
    ((pullbackToDiagonalTarget a u p b α).map m).snd.snd = m.snd := rfl

/-- The unit of `CategoryTheory.Limits.CategoricalPullback.diagonalTargetEquivalence`: the first
component `c` of a quadruple is carried to `a x` by the first component of its filler. -/
@[implicit_reducible]
noncomputable def diagonalTargetUnitIso :
    𝟭 ((diagonal p) ⊡ (mapDiagonal a u p b α)) ≅
      diagonalTargetToPullback a u p b α ⋙ pullbackToDiagonalTarget a u p b α :=
  NatIso.ofComponents
    (fun t => mkIso (asIso t.iso.hom.fst)
      (mkIso (Iso.refl _) (Iso.refl _) (by simp)) (by
        apply CategoricalPullback.hom_ext <;> simp))
    (fun {t t'} m => by
      apply CategoricalPullback.hom_ext
      · simpa only [Functor.id_map, comp_fst, asIso_hom, Functor.comp_map,
          diagonalTargetToPullback_map_fst, pullbackToDiagonalTarget_map_fst, mkIso_hom_fst]
          using diagonalTarget_fst_eq a u p b α m
      · apply CategoricalPullback.hom_ext <;> simp)

/-- The counit of `CategoryTheory.Limits.CategoricalPullback.diagonalTargetEquivalence`: the
round trip on `C' ×_{A} C'` changes the filler only by an identity. -/
@[implicit_reducible]
noncomputable def diagonalTargetCounitIso :
    pullbackToDiagonalTarget a u p b α ⋙ diagonalTargetToPullback a u p b α ≅
      𝟭 ((squareComparison a u p b α) ⊡ (squareComparison a u p b α)) :=
  NatIso.ofComponents
    (fun _ => mkIso (Iso.refl _) (Iso.refl _) (by
      apply CategoricalPullback.hom_ext <;> simp))
    (fun _ => by apply CategoricalPullback.hom_ext <;> simp)

/-- **The target of `B` is the 2-fibre product of `A` with itself.** A quadruple
`(c, (x, y, χ), (ξ₁, ξ₂))` of `C ×_{Δ_p, C ×_D C} (C' ×_{D'} C')` is determined up to canonical
isomorphism by the triple `(x, y, (ξ₁⁻¹ ≫ ξ₂, χ))` of `C' ×_{A, C ×_D D', A} C'`. -/
noncomputable def diagonalTargetEquivalence :
    ((diagonal p) ⊡ (mapDiagonal a u p b α)) ≌
      ((squareComparison a u p b α) ⊡ (squareComparison a u p b α)) :=
  CategoryTheory.Equivalence.mk (diagonalTargetToPullback a u p b α)
    (pullbackToDiagonalTarget a u p b α) (diagonalTargetUnitIso a u p b α)
    (diagonalTargetCounitIso a u p b α)

/-- **Under the identification of its target with `C' ×_{A} C'`, the comparison `B` of the
square of relative diagonals is the diagonal of `A`.** -/
noncomputable def diagonalComparisonIso :
    diagonalComparison a u p b α ⋙ diagonalTargetToPullback a u p b α ≅
      diagonal (squareComparison a u p b α) :=
  NatIso.ofComponents
    (fun _ => mkIso (Iso.refl _) (Iso.refl _) (by
      apply CategoricalPullback.hom_ext <;> simp [diagonalComparison]))
    (fun _ => by apply CategoricalPullback.hom_ext <;> simp [diagonalComparison])

/-- The comparison `diagonalTargetToPullback` is an equivalence. -/
private instance isEquivalence_diagonalTargetToPullback :
    (diagonalTargetToPullback a u p b α).IsEquivalence :=
  (diagonalTargetEquivalence a u p b α).isEquivalence_functor

/-- **The fullness half of the category-theoretic core of Stacks 0CMW.** For a 2-commutative
square of categories whose corners `C` and `D'` are groupoids, the comparison functor
`A : C' ⥤ C ×_D D'` is full as soon as the comparison functor `B` of the square of relative
diagonals is essentially surjective. -/
theorem full_squareComparison_of_essSurj_diagonalComparison [IsGroupoid C] [IsGroupoid D']
    (h : (diagonalComparison a u p b α).EssSurj) : (squareComparison a u p b α).Full := by
  have : (diagonal (squareComparison a u p b α)).EssSurj :=
    Functor.essSurj_of_iso (diagonalComparisonIso a u p b α)
  exact full_of_essSurj_diagonal (squareComparison a u p b α) inferInstance

/-- **The category-theoretic core of Stacks 0CMW.** For a 2-commutative square of categories
whose corners `C` and `D'` are groupoids, the comparison functor `A : C' ⥤ C ×_D D'` is fully
faithful if and only if the comparison functor `B : C' ⥤ C ×_{Δ_p, C ×_D C} (C' ×_{D'} C')` of
the square of relative diagonals is an equivalence. -/
@[stacks 0CMW "the category-theoretic reduction of the equivalence (1) <=> (2)"]
theorem fullyFaithful_squareComparison_iff [IsGroupoid C] [IsGroupoid D'] :
    ((squareComparison a u p b α).Full ∧ (squareComparison a u p b α).Faithful) ↔
      (diagonalComparison a u p b α).IsEquivalence := by
  rw [fullyFaithful_iff_isEquivalence_diagonal (squareComparison a u p b α),
    ← Functor.isEquivalence_iff_of_iso (diagonalComparisonIso a u p b α)]
  exact ⟨fun _ => Functor.isEquivalence_of_comp_right (diagonalComparison a u p b α)
      (diagonalTargetToPullback a u p b α),
    fun _ => Functor.isEquivalence_trans (diagonalComparison a u p b α)
      (diagonalTargetToPullback a u p b α)⟩

end CategoryTheory.Limits.CategoricalPullback

end
