module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CofilteredLimit
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.HilbertBaseChange

/-!
# Base change of families of cycles along a cartesian square

The base change `g^*α` of a family of `r`-cycles on the fibres of `X/S` along `g : T ⟶ S`
(Section 0H4N) is a family on the fibres of the chosen fibre product `X ×_S T ⟶ T`. In a limit
argument the base changes of one family along many morphisms are compared, and the fibre
products which occur are only canonically isomorphic to the chosen ones. This file reads a base
change through an arbitrary cartesian square

  `P --a--> X`
  `|p       |f`
  `T --g--> S`

by restricting `g^*α` along the canonical isomorphism `P ≅ X ×_S T` over `T`, and records the
three rules that make such base changes computable: a chosen fibre product gives back `g^*α`,
restriction along an isomorphism over `T` moves to the restricted square, and two base changes in
succession are the base change along the pasted square (Tag 0H4P, part (1)).

## Main definitions

* `Stacks.Chow.baseChangeFamilyOfIsPullback` — the base change of a family of cycles through a
  cartesian square.
* `Stacks.Chow.HilbertCycleDatum.ofIsPullback` — the inverse image of a member of `Hilb(X/S, r)`
  through a cartesian square, a member of `Hilb(P/T, r)`.

## Main results

* `Stacks.Chow.baseChangeFamilyOfIsPullback_of_hasPullback`,
  `Stacks.Chow.fiberCycleRestrict_baseChangeFamilyOfIsPullback`,
  `Stacks.Chow.baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback` — the three rules.
* `Stacks.Chow.HilbertCycleDatum.cycleClassMap_map_ofIsPullback` — the cycle class map commutes
  with base change through a square.
* `Stacks.Chow.baseChangeFamilyOfIsPullback_eq_iff` — two base changes through a square agree
  exactly when the two families agree over the image of `g`.

## References

* [Stacks Project, Section 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
* [Stacks Project, Tag 0H4P](https://stacks.math.columbia.edu/tag/0H4P)
* [Stacks Project, Tag 0H4T](https://stacks.math.columbia.edu/tag/0H4T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X S T T' P P' : Scheme.{u}}

/-- Restriction of fibrewise cycles along an open immersion only depends on the open immersion,
not on the proof that it lies over the base. -/
theorem fiberCycleRestrict_congr {U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ S) [LocallyOfFiniteType fU] {j₁ j₂ : U ⟶ X} [IsOpenImmersion j₁]
    [IsOpenImmersion j₂] (h₁ : j₁ ≫ f = fU) (h₂ : j₂ ≫ f = fU) (e : j₁ = j₂) (s : S) (r : ℕ)
    (c : FiberCycleGroup f s r) :
    fiberCycleRestrict f fU j₁ h₁ s r c = fiberCycleRestrict f fU j₂ h₂ s r c := by
  subst e
  rfl

/-! ### Base change through a cartesian square -/

section Square

variable (f : X ⟶ S) [LocallyOfFiniteType f] {g : T ⟶ S} {a : P ⟶ X} {p : P ⟶ T}
  [LocallyOfFiniteType p] (sq : IsPullback a p f g) (r : ℕ)

/-- **The base change of a family of cycles through a cartesian square.** For a cartesian square
with right-hand column `f : X ⟶ S`, bottom edge `g : T ⟶ S` and left-hand column `p : P ⟶ T`,
the base change `g^*α`, read on the fibres of `p` through the canonical isomorphism
`P ≅ X ×_S T` over `T`. -/
def baseChangeFamilyOfIsPullback (α : FamilyOfCycles f r) : FamilyOfCycles p r :=
  fun t => fiberCycleRestrict (pullback.snd f g) p sq.isoPullback.hom sq.isoPullback_hom_snd t r
    (baseChangeFamily f g r α t)

/-- Any isomorphism `P ≅ X ×_S T` compatible with the two projections computes the base change
through the square. -/
theorem baseChangeFamilyOfIsPullback_eq (φ : P ⟶ pullback f g) [IsIso φ]
    (hφ₁ : φ ≫ pullback.fst f g = a) (hφ₂ : φ ≫ pullback.snd f g = p) (α : FamilyOfCycles f r) :
    baseChangeFamilyOfIsPullback f sq r α =
      fun t => fiberCycleRestrict (pullback.snd f g) p φ hφ₂ t r (baseChangeFamily f g r α t) := by
  funext t
  exact fiberCycleRestrict_congr _ _ _ _
    (pullback.hom_ext (by rw [hφ₁, sq.isoPullback_hom_fst])
      (by rw [hφ₂, sq.isoPullback_hom_snd])) t r _

/-- Read through the chosen fibre product, the base change through a square is `g^*α`. -/
theorem baseChangeFamilyOfIsPullback_of_hasPullback (α : FamilyOfCycles f r) :
    baseChangeFamilyOfIsPullback f (IsPullback.of_hasPullback f g) r α =
      baseChangeFamily f g r α := by
  rw [baseChangeFamilyOfIsPullback_eq f (IsPullback.of_hasPullback f g) r (𝟙 _)
    (Category.id_comp _) (Category.id_comp _)]
  funext t
  exact fiberCycleRestrict_eq_self _ _ _ rfl t r _

/-- Base change through a square is additive. -/
theorem baseChangeFamilyOfIsPullback_add (α β : FamilyOfCycles f r) :
    baseChangeFamilyOfIsPullback f sq r (α + β) =
      baseChangeFamilyOfIsPullback f sq r α + baseChangeFamilyOfIsPullback f sq r β := by
  funext t
  simp only [baseChangeFamilyOfIsPullback, Pi.add_apply]
  rw [baseChangeFamily_add, Pi.add_apply, map_add]

/-- Base change through a square, as a homomorphism of groups of families. -/
def baseChangeFamilyOfIsPullbackHom : FamilyOfCycles f r →+ FamilyOfCycles p r where
  toFun := baseChangeFamilyOfIsPullback f sq r
  map_zero' := by
    funext t
    simp only [baseChangeFamilyOfIsPullback]
    rw [baseChangeFamily_zero, Pi.zero_apply, map_zero]
    rfl
  map_add' := baseChangeFamilyOfIsPullback_add f sq r

/-- **Restriction along an isomorphism over the base.** Restricting a base change through a
square along an isomorphism `ψ : P' ⟶ P` over `T` is the base change through the restricted
square. -/
theorem fiberCycleRestrict_baseChangeFamilyOfIsPullback {p' : P' ⟶ T} [LocallyOfFiniteType p']
    (ψ : P' ⟶ P) [IsIso ψ] (hψ : ψ ≫ p = p') (sq' : IsPullback (ψ ≫ a) p' f g)
    (α : FamilyOfCycles f r) :
    (fun t => fiberCycleRestrict p p' ψ hψ t r (baseChangeFamilyOfIsPullback f sq r α t)) =
      baseChangeFamilyOfIsPullback f sq' r α := by
  funext t
  simp only [baseChangeFamilyOfIsPullback]
  rw [fiberCycleRestrict_fiberCycleRestrict]
  exact fiberCycleRestrict_congr _ _ _ _
    (pullback.hom_ext (by simp) (by simp [hψ])) t r _

/-- **Tag 0H4P, part (1), along squares.** Two base changes in succession, through cartesian
squares `(a₁, p₁)` over `g` and `(a₂, p₂)` over `h`, are the base change through the pasted
square over `h ≫ g`. -/
theorem baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback {h : T' ⟶ T} {a₂ : P' ⟶ P}
    {p₂ : P' ⟶ T'} [LocallyOfFiniteType p₂] (sq₂ : IsPullback a₂ p₂ p h)
    (α : FamilyOfCycles f r) :
    baseChangeFamilyOfIsPullback p sq₂ r (baseChangeFamilyOfIsPullback f sq r α) =
      baseChangeFamilyOfIsPullback f (sq₂.paste_horiz sq) r α := by
  funext t
  simp only [baseChangeFamilyOfIsPullback]
  have hres := baseChangeFamily_fiberCycleRestrict (pullback.snd f g) p sq.isoPullback.hom
    sq.isoPullback_hom_snd h r (baseChangeFamily f g r α)
  have hbc := baseChangeFamily_baseChangeFamily_comp f g h r α
  change fiberCycleRestrict (pullback.snd p h) p₂ sq₂.isoPullback.hom _ t r
      (baseChangeFamily p h r (fun s => fiberCycleRestrict (pullback.snd f g) p
        sq.isoPullback.hom sq.isoPullback_hom_snd s r (baseChangeFamily f g r α s)) t) = _
  rw [hres t, hbc, fiberCycleRestrict_fiberCycleRestrict, fiberCycleRestrict_fiberCycleRestrict]
  refine fiberCycleRestrict_congr _ _ _ _ (pullback.hom_ext ?_ ?_) t r _ <;> simp [pullbackRestrict]

/-- Two base changes through a square agree exactly when the two families agree over the image
of the bottom edge. -/
theorem baseChangeFamilyOfIsPullback_eq_iff (α β : FamilyOfCycles f r) :
    baseChangeFamilyOfIsPullback f sq r α = baseChangeFamilyOfIsPullback f sq r β ↔
      ∀ t : T, α (g t) = β (g t) := by
  rw [← baseChangeFamily_eq_iff]
  exact ⟨fun h => funext fun t => fiberCycleRestrict_injective_of_isIso _ _ _ _ t r (congrFun h t),
    fun h => funext fun t => by simp only [baseChangeFamilyOfIsPullback, h]⟩

/-- The base change of a relative `r`-cycle through a square is a relative `r`-cycle. -/
theorem isRelativeCycle_baseChangeFamilyOfIsPullback [IsLocallyNoetherian S]
    [IsLocallyNoetherian T] {α : FamilyOfCycles f r} (hα : IsRelativeCycle f r α) :
    IsRelativeCycle p r (baseChangeFamilyOfIsPullback f sq r α) :=
  isRelativeCycle_fiberCycleRestrict _ _ _ _ r (isRelativeCycle_baseChangeFamily f g r hα)

end Square

/-- Base change through the trivial square, with identities as top and bottom edges, is the
identity: along `𝟙 S` the residue field extensions are trivial and the fibre maps are the
identities. -/
theorem baseChangeFamilyOfIsPullback_id {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (sq : IsPullback (𝟙 X) f f (𝟙 S)) (r : ℕ) (α : FamilyOfCycles f r) :
    baseChangeFamilyOfIsPullback f sq r α = α := by
  have hfst : pullback.fst f (𝟙 S) ≫ f = pullback.snd f (𝟙 S) := by
    rw [pullback.condition, Category.comp_id]
  have key : baseChangeFamily f (𝟙 S) r α = fun t =>
      fiberCycleRestrict f (pullback.snd f (𝟙 S)) (pullback.fst f (𝟙 S)) hfst t r (α t) := by
    funext t
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro x
    have : IsIso (Scheme.Hom.residueFieldMap (𝟙 S) t) := by
      rw [Scheme.residueFieldMap_id]
      exact IsIso.id _
    rw [baseChangeFamily_apply_of_isIso_residueFieldMap f (𝟙 S) t r α x, fiberCycleRestrict_apply,
      restrictedFiberMap_id_eq_fiberRestrict f _ _ hfst pullback.condition t]
    rfl
  funext t
  simp only [baseChangeFamilyOfIsPullback]
  rw [key, fiberCycleRestrict_fiberCycleRestrict]
  exact fiberCycleRestrict_eq_self _ _ _ sq.isoPullback_hom_fst t r _

/-! ### Members of `Hilb` through a square -/

namespace HilbertCycleDatum

variable {f : X ⟶ S} {g : T ⟶ S} {a : P ⟶ X} {p : P ⟶ T} {r : ℕ}

/-- The inverse image of a member of `Hilb(X/S, r)` through a cartesian square, a member of
`Hilb(P/T, r)`: the restriction of its base change along the canonical isomorphism
`P ≅ X ×_S T`. Its ideal sheaf is the inverse image along the top edge. -/
def ofIsPullback (Z : HilbertCycleDatum f r) (sq : IsPullback a p f g) : HilbertCycleDatum p r :=
  (Z.baseChange g).restrict sq.isoPullback.hom sq.isoPullback_hom_snd

/-- The ideal sheaf of the inverse image of a member of `Hilb(X/S, r)` through a cartesian square
is the inverse image of its ideal sheaf along the top edge `a : P ⟶ X`. -/
theorem ofIsPullback_ideal (Z : HilbertCycleDatum f r) (sq : IsPullback a p f g) :
    (Z.ofIsPullback sq).ideal = Z.ideal.comap a := by
  rw [ofIsPullback, restrict_ideal, baseChange_ideal, ← Scheme.IdealSheafData.comap_comp,
    sq.isoPullback_hom_fst]

/-- The cycle class of the inverse image through a square is the base change of the cycle class
through the square. -/
theorem cycleFamily_ofIsPullback [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation p]
    (Z : HilbertCycleDatum f r) (sq : IsPullback a p f g) :
    (Z.ofIsPullback sq).cycleFamily p = baseChangeFamilyOfIsPullback f sq r (Z.cycleFamily f) := by
  rw [ofIsPullback, cycleFamily_restrict, cycleFamily_baseChange]
  rfl

/-- The cycle class map commutes with base change through a square. -/
theorem cycleClassMap_map_ofIsPullback [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation p] (sq : IsPullback a p f g)
    (c : FreeAbelianGroup (HilbertCycleDatum f r)) :
    cycleClassMap p r (FreeAbelianGroup.map (fun Z ↦ Z.ofIsPullback sq) c) =
      baseChangeFamilyOfIsPullback f sq r (cycleClassMap f r c) := by
  have h := FreeAbelianGroup.lift_ext
    ((cycleClassMap p r).comp (FreeAbelianGroup.map fun Z ↦ Z.ofIsPullback sq))
    ((baseChangeFamilyOfIsPullbackHom f sq r).comp (cycleClassMap f r)) fun Z => by
      simp only [AddMonoidHom.comp_apply, FreeAbelianGroup.map_of_apply, cycleClassMap_of]
      exact cycleFamily_ofIsPullback Z sq
  exact DFunLike.congr_fun h c

end HilbertCycleDatum

end Stacks.Chow

end
