module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Limits.StageFactorizationOfLimitMorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian

/-!
# A morphism to a scheme of finite type over `Spec ℤ` factors through a stage

Let `D : I ⥤ Scheme` be a cofiltered diagram of affine schemes over a locally Noetherian scheme
`S`, with limit cone `c` and induced morphism `m : c.pt ⟶ S`. Let `T` be locally of finite type
over `Spec ℤ`. Then every morphism `c.pt ⟶ T` — a morphism which need not be a morphism over `S`
at all — factors through a stage of the diagram.

This is the step "Since `T` is of finite type over `Z` by Limits, Proposition 32.6.1 we can choose
an `i` and a morphism `σ_i : (S_i, s_i) → (T, t)` whose composition with
`Spec(𝒪^∧_{S,s}) → S_i` is equal to `σ`" in the proof of Stacks Tag 0GDX.

## Main results

* `AlgebraicGeometry.exists_stage_morphism_of_locallyOfFiniteTypeOverZ`: the factorization, with
  the pointed form of Tag 0GDX's clause (3) as an immediate corollary
  (`AlgebraicGeometry.exists_stage_morphism_of_locallyOfFiniteTypeOverZ_apply`).

## Implementation notes

Tag 01ZC, in the form
`AlgebraicGeometry.exists_stage_comp_eq_of_locallyOfFinitePresentation`, factors morphisms *over
`S`* into a target *locally of finite presentation over `S`*. Neither applies to `T` directly, and
the device for both is the same as the one Tag 0GDX's clauses (1) and (3) already use: replace `T`
by `T ×_{Spec ℤ} S`, which is locally of finite type over `S` because `T` is over `Spec ℤ`, hence
locally of finite presentation since `S` is locally Noetherian; a morphism `c.pt ⟶ T` together
with `m` is a morphism over `S` into that product, because `Spec ℤ` is terminal so the square
commutes automatically.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A morphism out of a cofiltered limit of affine schemes over `S` into a scheme locally of
finite type over `Spec ℤ` factors through a stage.** No compatibility over `S` is required of the
morphism, and none is asserted of the factorization. -/
public theorem exists_stage_morphism_of_locallyOfFiniteTypeOverZ
    {S T : Scheme.{u}} [IsLocallyNoetherian S] {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (m : c.pt ⟶ S) (hm : ∀ i, c.π.app i ≫ p.app i = m)
    (haff : ∀ i, IsAffine (D.obj i))
    (hT : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from T))
    (bT : c.pt ⟶ T) :
    ∃ (i : I) (τ : D.obj i ⟶ T), c.π.app i ≫ τ = bT := by
  have hTi := hT
  have hq : LocallyOfFiniteType
      (pullback.snd (specULiftZIsTerminal.{u}.from T) (specULiftZIsTerminal.{u}.from S)) :=
    inferInstance
  have hqfp : LocallyOfFinitePresentation
      (pullback.snd (specULiftZIsTerminal.{u}.from T) (specULiftZIsTerminal.{u}.from S)) :=
    inferInstance
  have hsq : bT ≫ specULiftZIsTerminal.{u}.from T = m ≫ specULiftZIsTerminal.{u}.from S :=
    specULiftZIsTerminal.{u}.hom_ext _ _
  obtain ⟨i, gi, -, hgi⟩ := exists_stage_comp_eq_of_locallyOfFinitePresentation D p c hc m hm haff
    (pullback.snd (specULiftZIsTerminal.{u}.from T) (specULiftZIsTerminal.{u}.from S))
    (pullback.lift bT m hsq) (pullback.lift_snd _ _ hsq)
  refine ⟨i, gi ≫ pullback.fst _ _, ?_⟩
  rw [← Category.assoc, hgi]
  exact pullback.lift_fst _ _ hsq

/-- The pointed form of the factorization: the image of a point of the limit under the
factorization at the stage is its image under the original morphism. This is the shape in which
Tag 0GDX's clause `τ(v) = t` is used. -/
public theorem exists_stage_morphism_of_locallyOfFiniteTypeOverZ_apply
    {S T : Scheme.{u}} [IsLocallyNoetherian S] {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (m : c.pt ⟶ S) (hm : ∀ i, c.π.app i ≫ p.app i = m)
    (haff : ∀ i, IsAffine (D.obj i))
    (hT : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from T))
    (bT : c.pt ⟶ T) (z : c.pt) :
    ∃ (i : I) (τ : D.obj i ⟶ T), c.π.app i ≫ τ = bT ∧ τ (c.π.app i z) = bT z := by
  obtain ⟨i, τ, hτ⟩ :=
    exists_stage_morphism_of_locallyOfFiniteTypeOverZ D p c hc m hm haff hT bT
  exact ⟨i, τ, hτ, congrArg (fun k : c.pt ⟶ T => k z) hτ⟩

end AlgebraicGeometry

end
