module

public import StacksFrontier.CategoryTheory.TwoOpenBiprodGlueing

/-!
# Composing split lifts whose complement is recorded

Fix a functor `F : D ⥤ H` — read it as restriction along an inclusion of opens — and call a
*split lift* of `α : P ⟶ F.obj E` a triple of an object `R` over `D`, a morphism `β : R ⟶ E` and
an isomorphism `f : F.obj R ≅ P ⊞ J` through which `F.map β` is `biprod.fst ≫ α`. Three
statements about such data are proved here, all pure category theory: the problem is solved with
`J` a zero object when `F` is isomorphic to the identity; a split lift along `F` composes with one
along `G` into a split lift along a functor isomorphic to `G ⋙ F`; and a split lift transports
along a functor with a comparison isomorphism.

This is the skeleton of the affine-cover induction in the proof of [Stacks, Tag 09IM] in the form
[Stacks, Tag 09IN] needs it. `Stacks.LiftingProblem.exists_retract_lift_comp` of
`StacksFrontier/CategoryTheory/LiftingProblemRetract.lean` is the same induction carrying only a
retraction `P ⟶ F.obj R ⟶ P`; the remark of [Stacks, Tag 09IN] is about the *complement* of `P`,
so the induction has to carry the splitting itself, and the complement it produces at the next
stage is `J ⊞ (P ⊞ J)⟦1⟧` — the shape
`Stacks.SumOfPositiveShifts.IsSumOfPositiveShifts.biprod_shift_self` is stated at.

## Main results

* `Stacks.LiftingProblem.biprodShiftAssoc_hom_fst`: the projection onto `P` through the comparison
  `F(R ⊞ R⟦1⟧) ≅ (P ⊞ J) ⊞ (P ⊞ J)⟦1⟧ ≅ P ⊞ (J ⊞ (P ⊞ J)⟦1⟧)`.
* `Stacks.LiftingProblem.exists_biprod_lift_of_isoId`: the base case.
* `Stacks.LiftingProblem.exists_biprod_lift_comp`: **the step**, which also produces the new
  complement.
* `Stacks.LiftingProblem.exists_biprod_lift_of_transport`: a split lift carried along a functor
  `Φ` with a comparison `Φ ⋙ F' ≅ F`. This is the move from the top open of a scheme to the
  scheme itself.

## Implementation notes

The comparison of `F(R ⊞ R⟦1⟧)` with `F R ⊞ (F R)⟦1⟧` is
`Stacks.Perfect.SupportedBiprodShiftAffine.biprodShiftIsoOfObjIso`, which takes the additivity
and the shift-commutation of `F` as explicit arguments rather than as instances; that is what
lets the geometric consumer pass the two witnesses it has rather than hope instance search finds
them at the spelling of the category it is working in.

Nothing here assumes an abelian category or a derived category: the three statements are about
functors, natural isomorphisms and the naturality squares of those isomorphisms at the morphism
being lifted. Elaborating them against the restriction functors of a scheme costs an elaboration
budget that the generic statements do not.

## References

* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 09IN](https://stacks.math.columbia.edu/tag/09IN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category ZeroObject
open Stacks.Perfect.SupportedBiprodShiftAffine (biprodShiftIsoOfObjIso)

namespace Stacks.LiftingProblem

universe v₁ v₂ v₃ u₁ u₂ u₃

/-! ### The projection onto `P` through the two comparisons -/

/-- **The projection of the new splitting onto `P`.** Reading `F(R ⊞ R⟦1⟧)` first as
`(P ⊞ J) ⊞ (P ⊞ J)⟦1⟧` through a splitting `f : F.obj R ≅ P ⊞ J`, then as `P ⊞ (J ⊞ (P ⊞ J)⟦1⟧)`
through the associator, the projection onto `P` is the image of the projection of `R ⊞ R⟦1⟧` onto
`R`, followed by `f` and its own projection.

The trailing morphism `α` is carried along because every use occurs under one; stated without it
the rewrite has to be reassociated at each call site. -/
theorem biprodShiftAssoc_hom_fst {D : Type u₂} [Category.{v₂} D]
    {H : Type u₃} [Category.{v₃} H] [Preadditive D] [Preadditive H]
    [HasBinaryBiproducts D] [HasBinaryBiproducts H] [HasShift D ℤ] [HasShift H ℤ]
    (F : D ⥤ H) (hF : F.Additive) (cF : F.CommShift ℤ) {R : D} {P J : H}
    (f : F.obj R ≅ P ⊞ J) {Y : H} (α : P ⟶ Y) :
    (biprodShiftIsoOfObjIso F hF cF f).hom ≫
        (biprod.associator P J ((P ⊞ J)⟦(1 : ℤ)⟧)).hom ≫ biprod.fst ≫ α =
      F.map (biprod.fst : R ⊞ R⟦(1 : ℤ)⟧ ⟶ R) ≫ f.hom ≫ biprod.fst ≫ α := by
  rw [show (biprod.associator P J ((P ⊞ J)⟦(1 : ℤ)⟧)).hom ≫ biprod.fst ≫ α =
      biprod.fst ≫ biprod.fst ≫ α by
    rw [← assoc, ← assoc]
    congr 1
    simp [biprod.associator]]
  rw [← assoc (biprodShiftIsoOfObjIso F hF cF f).hom, biprodShiftIsoOfObjIso_hom_fst, assoc]

/-! ### The base case -/

/-- **The lifting problem is solved, with zero complement, where the functor is the identity.**
If `θ : F ≅ 𝟭 C` then any `a : P ⟶ F.obj A` is `f.hom ≫ biprod.fst ≫ a` for some `β : P ⟶ A` and
the splitting `F.obj P ≅ P ⊞ 0` given by `θ` and
`CategoryTheory.Limits.isoBiprodZero`.

This is the base case of the affine-cover induction of [Stacks, Tag 09IM]: over the given open
`U` the lift is `P` itself, and the complement is zero — which is the empty biproduct of positive
shifts of `P`. -/
theorem exists_biprod_lift_of_isoId {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [HasBinaryBiproducts C] [HasZeroObject C] (F : C ⥤ C) (θ : F ≅ 𝟭 C) (P A : C)
    (a : P ⟶ F.obj A) :
    ∃ (β : P ⟶ A) (f : F.obj P ≅ P ⊞ (0 : C)), F.map β = f.hom ≫ biprod.fst ≫ a := by
  refine ⟨a ≫ θ.hom.app A, θ.app P ≪≫ Limits.isoBiprodZero (isZero_zero C), ?_⟩
  have h : θ.inv.app P ≫ F.map (a ≫ θ.hom.app A) = a := by
    have hnat := θ.inv.naturality (a ≫ θ.hom.app A)
    simp only [Functor.id_map] at hnat
    rw [← hnat]
    simp
  have h2 : F.map (a ≫ θ.hom.app A) = θ.hom.app P ≫ a :=
    calc F.map (a ≫ θ.hom.app A)
        = θ.hom.app P ≫ θ.inv.app P ≫ F.map (a ≫ θ.hom.app A) := by simp
      _ = θ.hom.app P ≫ a := by rw [h]
  rw [h2]
  simp [Limits.isoBiprodZero]

/-! ### The step -/

/-- **Two split lifts compose, and the new complement is `J ⊞ (P ⊞ J)⟦1⟧`.** Let `e : G ⋙ F ≅ L`.
Given a split lift of `b : R₁ ⟶ G.obj E` along `G` whose splitting is `G.obj R₂ ≅ R₁ ⊞ R₁⟦1⟧`,
and a split lift of `b` itself along `F` with splitting `F.obj R₁ ≅ P ⊞ J` compatible with
`α : P ⟶ L.obj E`, the object `R₂` carries a split lift of `α` along `L` with complement
`J ⊞ (P ⊞ J)⟦1⟧`.

This is the step of the affine-cover induction of [Stacks, Tag 09IM]: a lift already obtained
over an open `W` is composed with the enlargement of `W` by one affine open, which replaces the
lift by `R₁ ⊞ R₁⟦1⟧`. The compatibility with the map to the ambient object is transported by the
naturality of `e`, and the new complement is read off by
`Stacks.LiftingProblem.biprodShiftAssoc_hom_fst`. -/
theorem exists_biprod_lift_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {H : Type u₃} [Category.{v₃} H] [Preadditive D] [Preadditive H]
    [HasBinaryBiproducts D] [HasBinaryBiproducts H] [HasShift D ℤ] [HasShift H ℤ]
    (F : D ⥤ H) (G : C ⥤ D) (L : C ⥤ H) (e : G ⋙ F ≅ L)
    (hF : F.Additive) (cF : F.CommShift ℤ)
    {E R₂ : C} {R₁ : D} {P J : H}
    (ρ : R₂ ⟶ E) (b : R₁ ⟶ G.obj E)
    (g : G.obj R₂ ≅ R₁ ⊞ R₁⟦(1 : ℤ)⟧) (hg : G.map ρ = g.hom ≫ biprod.fst ≫ b)
    (f : F.obj R₁ ≅ P ⊞ J) (α : P ⟶ L.obj E)
    (hf : F.map b = f.hom ≫ biprod.fst ≫ α ≫ (e.app E).inv) :
    ∃ f' : L.obj R₂ ≅ P ⊞ (J ⊞ (P ⊞ J)⟦(1 : ℤ)⟧),
      L.map ρ = f'.hom ≫ biprod.fst ≫ α := by
  refine ⟨(e.app R₂).symm ≪≫ F.mapIso g ≪≫ biprodShiftIsoOfObjIso F hF cF f ≪≫
    biprod.associator P J ((P ⊞ J)⟦(1 : ℤ)⟧), ?_⟩
  calc L.map ρ
      = (e.app R₂).inv ≫ F.map (G.map ρ) ≫ e.hom.app E := (NatIso.naturality_1 e ρ).symm
    _ = (e.app R₂).inv ≫ F.map g.hom ≫ F.map (biprod.fst : R₁ ⊞ R₁⟦(1 : ℤ)⟧ ⟶ R₁) ≫
          F.map b ≫ e.hom.app E := by
        rw [hg]
        simp only [Functor.map_comp, assoc]
    _ = (e.app R₂).inv ≫ F.map g.hom ≫ F.map (biprod.fst : R₁ ⊞ R₁⟦(1 : ℤ)⟧ ⟶ R₁) ≫
          f.hom ≫ biprod.fst ≫ α := by
        rw [hf]
        simp
    _ = _ := by
        simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, assoc,
          biprodShiftAssoc_hom_fst]

/-! ### Transporting a split lift along a functor -/

/-- **A split lift transports along a functor with a comparison isomorphism.** Let
`cmp : Φ ⋙ F' ≅ F` and let `ν : Φ.obj Ec ≅ E'` identify the image of the ambient object. A split
lift of `R` over `Ec` along `F`, compatible with the map read through `cmp` and `ν`, is carried
to a split lift of `Φ.obj R` over `E'` along `F'` with the *same* complement.

This is the last move of the proof of [Stacks, Tag 09IM]: the induction produces its lift over
the top open of the scheme, and `Φ` is the pullback along the inverse of the identification of
that open subscheme with the scheme. The given map is composed with
`(F'.mapIso ν).inv ≫ cmp.hom.app Ec` rather than with a comparison of `F'` and `F` in the other
direction, which is what makes the conclusion free of any coherence between the two. -/
theorem exists_biprod_lift_of_transport {C : Type u₁} [Category.{v₁} C] {C' : Type u₂}
    [Category.{v₂} C'] {H : Type u₃} [Category.{v₃} H] [Preadditive H] [HasBinaryBiproducts H]
    (Φ : C ⥤ C') (F : C ⥤ H) (F' : C' ⥤ H) (cmp : Φ ⋙ F' ≅ F)
    {Ec : C} {E' : C'} (ν : Φ.obj Ec ≅ E') {R : C} {P J : H}
    (ρ : R ⟶ Ec) (f : F.obj R ≅ P ⊞ J) (α : P ⟶ F'.obj E')
    (hf : F.map ρ = f.hom ≫ biprod.fst ≫ (α ≫ (F'.mapIso ν).inv ≫ cmp.hom.app Ec)) :
    ∃ f' : F'.obj (Φ.obj R) ≅ P ⊞ J,
      F'.map (Φ.map ρ ≫ ν.hom) = f'.hom ≫ biprod.fst ≫ α := by
  refine ⟨cmp.app R ≪≫ f, ?_⟩
  calc F'.map (Φ.map ρ ≫ ν.hom)
      = F'.map (Φ.map ρ) ≫ F'.map ν.hom := F'.map_comp _ _
    _ = cmp.hom.app R ≫ F.map ρ ≫ (cmp.app Ec).inv ≫ F'.map ν.hom := by
        rw [Iso.app_inv, NatIso.naturality_2_assoc cmp ρ]
        rfl
    _ = cmp.hom.app R ≫ f.hom ≫ biprod.fst ≫ α := by
        rw [hf]
        simp
    _ = _ := by simp

end Stacks.LiftingProblem

end
