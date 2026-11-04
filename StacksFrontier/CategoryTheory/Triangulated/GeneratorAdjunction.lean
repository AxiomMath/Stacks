module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Retract
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability
public import StacksFrontier.CategoryTheory.Triangulated.Generators
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability

/-!
# Gluing a weak generator across an adjunction

Let `L ⊣ R` be an adjunction between categories with a shift by `ℤ`, with `L` commuting with the
shift. Think of `L` as restriction `j^*` to an open subspace and of `R` as derived direct image
`Rj_*`. This file proves the one abstract statement that the generation arguments of
[Stacks, Tag 09IS] and [Stacks, Tag 0A9A] end with:

> Let `Q`, `K` be objects of the source and `P` a direct summand of `L Q`. Suppose `P` is a weak
> generator of the target, and suppose that an object killed by all maps out of the shifts of `K`
> has invertible unit. Then `Q ⊕ K` is a weak generator of the source.

In the source `Q` is a perfect object of `D(𝒪_X)` whose restriction to the quasi-compact open `U`
has the generator of `D_{QCoh}(𝒪_U)` as a direct summand, `K` is the pushforward of a Koszul
complex on the affine `V = X \ U`, and the hypothesis about the unit is [Stacks, Tag 09IR]
combined with the identification `R(V → X)_* = R(V → X)_!` of [Stacks, Tag 08DF]. Those two are
geometric and are not proved here; everything that is not is.

The argument has three steps and each is a declaration below. First, right orthogonality to the
shifts of an object passes to a direct summand of it, so orthogonality to `Q ⊕ K` gives
orthogonality to `Q` and to `K` separately. Second, orthogonality to the shifts of `Q` transports
along `L` to orthogonality of `L E` to the shifts of `L Q`, provided the unit at `E` is
invertible: a map `(L Q)⟦a⟧ ⟶ L E` is the image under the hom-set bijection of a map
`Q⟦a⟧ ⟶ R (L E) ≅ E`, which vanishes. Third, `P` is a summand of `L Q`, so `L E` is orthogonal to
the shifts of `P` and hence zero; and `E ≅ R (L E) ≅ R 0 = 0`.

## Main results

* `CategoryTheory.ObjectProperty.rightOrthogonal_shiftClosure_singleton_of_retract` — right
  orthogonality to the shifts of an object passes to a retract of that object.
* `CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_of_retract` — an object with a weak
  generator as a direct summand is a weak generator.
* `CategoryTheory.ObjectProperty.rightOrthogonal_shiftClosure_singleton_biprod_iff` — an object is
  right orthogonal to the shifts of `Q ⊞ K` exactly when it is right orthogonal to the shifts of
  `Q` and to the shifts of `K`.
* `CategoryTheory.ObjectProperty.rightOrthogonal_shiftClosure_singleton_map_of_isIso_unit` — right
  orthogonality transports along the left adjoint at an object whose unit is invertible.
* `CategoryTheory.ObjectProperty.isZero_of_rightOrthogonal_of_adjunction` — the argument itself,
  concluding that `E` is zero.
* `CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_singleton_biprod_of_adjunction` —
  the same packaged as a generation statement about `Q ⊞ K`.

## Implementation notes

Nothing here is triangulated: the statements need only zero morphisms, a shift by `ℤ` and — for
the two biproduct statements — preadditivity and additivity of the shift functors. In particular
there is no `HasDerivedCategory` instance anywhere, so no choice of model of the derived category
is made and the results apply to the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which is the only one at which
[Stacks, Tag 09IS] and [Stacks, Tag 0A9A] have content.

The hypothesis on the unit is phrased as `IsIso (adj.unit.app E)` rather than as an isomorphism
`E ≅ R.obj (L.obj E)`, because the source's conclusion `E = R(U → X)_* E|_U` is about the
canonical map and the argument uses it: `adj.unit.app E` is what the hom-set bijection is built
from.

`Retract` is Mathlib's `CategoryTheory.Retract`, so "direct summand" is read as "retract"
throughout; that is what the source's "`P` is a direct summand of `R|_U`" is used for, and it
needs no additive structure.

No `@[stacks]` attribute is attached. Neither tag is proved here: what is proved is the last
paragraph of each of the two source proofs, with the geometric input isolated as the hypothesis
`hunit`.

## References

* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [Stacks Project, Tag 09SJ](https://stacks.math.columbia.edu/tag/09SJ)
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty

/-! ### Direct summands -/

section Retracts

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasShift C ℤ]

/-- **Right orthogonality to the shifts of an object passes to a retract of it.** If `P` is a
retract of `Q` and every morphism from a shift of `Q` to `K` vanishes, then so does every
morphism from a shift of `P`: the shift functor carries the retract `P ⟶ Q ⟶ P` to a retract
`P⟦a⟧ ⟶ Q⟦a⟧ ⟶ P⟦a⟧`, so a morphism `P⟦a⟧ ⟶ K` factors through `Q⟦a⟧`. -/
theorem rightOrthogonal_shiftClosure_singleton_of_retract {P Q : C} (h : Retract P Q) {K : C}
    (hK : ((singleton Q).shiftClosure ℤ).rightOrthogonal K) :
    ((singleton P).shiftClosure ℤ).rightOrthogonal K := by
  rw [rightOrthogonal_shiftClosure_ofObj_iff] at hK ⊢
  intro _ a f
  rw [show f = (shiftFunctor C a).map h.i ≫ ((shiftFunctor C a).map h.r ≫ f) by
        rw [← Category.assoc, ← Functor.map_comp, h.retract, Functor.map_id, Category.id_comp],
    hK () a ((shiftFunctor C a).map h.r ≫ f), comp_zero]

/-- **An object with a weak generator as a direct summand is a weak generator.** An object right
orthogonal to the shifts of `Q` is right orthogonal to the shifts of its retract `P`, hence
zero. -/
theorem isWeakTriangulatedGenerator_of_retract {P Q : C} (h : Retract P Q)
    (hP : (singleton P).IsWeakTriangulatedGenerator) :
    (singleton Q).IsWeakTriangulatedGenerator :=
  fun _ hK => hP _ (rightOrthogonal_shiftClosure_singleton_of_retract h hK)

variable [∀ n : ℤ, (shiftFunctor C n).Additive]

/-- **Right orthogonality to a direct sum of two objects, componentwise.** An object `E` is right
orthogonal to the shifts of `Q ⊞ K` exactly when it is right orthogonal to the shifts of `Q` and
to the shifts of `K`.

The two easy directions are `rightOrthogonal_shiftClosure_singleton_of_retract` applied to the
retracts `biprod.inl, biprod.fst` and `biprod.inr, biprod.snd`. The remaining one is the identity
`fst ≫ inl + snd ≫ inr = 𝟙` of the biproduct, carried through the shift functor, which is
additive. This is why the source's single generator `Q ⊕ K'` and the two-element generating
family `{Q, K'}` are interchangeable. -/
theorem rightOrthogonal_shiftClosure_singleton_biprod_iff (Q K E : C)
    [HasBinaryBiproduct Q K] :
    ((singleton (Q ⊞ K)).shiftClosure ℤ).rightOrthogonal E ↔
      ((singleton Q).shiftClosure ℤ).rightOrthogonal E ∧
        ((singleton K).shiftClosure ℤ).rightOrthogonal E := by
  refine ⟨fun h => ⟨rightOrthogonal_shiftClosure_singleton_of_retract
      ⟨biprod.inl, biprod.fst, by simp⟩ h,
    rightOrthogonal_shiftClosure_singleton_of_retract ⟨biprod.inr, biprod.snd, by simp⟩ h⟩,
    fun ⟨hQ, hK⟩ => ?_⟩
  rw [rightOrthogonal_shiftClosure_ofObj_iff] at hQ hK ⊢
  intro _ a f
  have htotal : (shiftFunctor C a).map (biprod.fst (X := Q) (Y := K)) ≫
        (shiftFunctor C a).map (biprod.inl (X := Q) (Y := K)) +
      (shiftFunctor C a).map (biprod.snd (X := Q) (Y := K)) ≫
        (shiftFunctor C a).map (biprod.inr (X := Q) (Y := K)) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, biprod.total,
      Functor.map_id]
  rw [show f = ((shiftFunctor C a).map biprod.fst ≫ (shiftFunctor C a).map biprod.inl +
        (shiftFunctor C a).map biprod.snd ≫ (shiftFunctor C a).map biprod.inr) ≫ f by
      rw [htotal, Category.id_comp],
    Preadditive.add_comp, Category.assoc, Category.assoc,
    hQ () a ((shiftFunctor C a).map biprod.inl ≫ f),
    hK () a ((shiftFunctor C a).map biprod.inr ≫ f), comp_zero, comp_zero, add_zero]

end Retracts

/-! ### Transport along the left adjoint -/

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasShift C ℤ]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasShift D ℤ]

/-- **Right orthogonality transports along the left adjoint, at an object whose unit is
invertible.** Let `L ⊣ R` with `L` commuting with the shift, and let `E` be an object at which the
unit `E ⟶ R (L E)` is invertible. If `E` is right orthogonal to the shifts of `Q`, then `L E` is
right orthogonal to the shifts of `L Q`.

A morphism `g : (L Q)⟦a⟧ ⟶ L E` becomes, after the shift-commutation isomorphism
`L (Q⟦a⟧) ≅ (L Q)⟦a⟧`, a morphism out of `L (Q⟦a⟧)`; its image under the hom-set bijection is a
morphism `Q⟦a⟧ ⟶ R (L E)`, which composed with the inverse of the unit is a morphism
`Q⟦a⟧ ⟶ E` and therefore vanishes. The bijection is injective and sends `0` to `0`, so `g`
vanishes. -/
theorem rightOrthogonal_shiftClosure_singleton_map_of_isIso_unit {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [L.CommShift ℤ] {Q E : C} (hE : IsIso (adj.unit.app E))
    (hQ : ((singleton Q).shiftClosure ℤ).rightOrthogonal E) :
    ((singleton (L.obj Q)).shiftClosure ℤ).rightOrthogonal (L.obj E) := by
  have : R.IsRightAdjoint := adj.isRightAdjoint
  rw [rightOrthogonal_shiftClosure_ofObj_iff] at hQ ⊢
  intro _ a g
  set e := (L.commShiftIso (A := ℤ) a).app Q with he
  -- The adjoint of `e.hom ≫ g`, read in `C`.
  set φ := adj.unit.app ((shiftFunctor C a).obj Q) ≫ R.map (e.hom ≫ g) with hφ
  have hψ : φ ≫ inv (adj.unit.app E) = 0 := hQ () a _
  have hφ0 : φ = 0 := zero_of_comp_mono _ hψ
  have hg0 : e.hom ≫ g = 0 := by
    refine (adj.homEquiv ((shiftFunctor C a).obj Q) (L.obj E)).injective ?_
    rw [adj.homEquiv_unit, adj.homEquiv_unit, ← hφ, hφ0, Functor.map_zero, comp_zero]
  exact zero_of_epi_comp e.hom hg0

/-- **The last paragraph of the generation arguments of [Stacks, Tag 09IS] and
[Stacks, Tag 0A9A].** Let `L ⊣ R` with `L` commuting with the shift. Let `Q`, `K` be objects of
the source and `P` an object of the target which is a direct summand of `L Q`, and assume

* `P` is a weak generator of the target;
* an object of the source right orthogonal to the shifts of `K` has invertible unit (`hunit`).

Then an object `E` right orthogonal to the shifts of both `Q` and `K` is zero.

In the source, `hunit` is [Stacks, Tag 09IR] — the vanishing of `Hom(K[n], E)` for the Koszul
complex `K` on generators of the ideal cutting out `X \ U` forces `E = Rj_*(E|_U)` — together
with the identification of `R(V → X)_*` with extension by zero, [Stacks, Tag 08DF]. -/
theorem isZero_of_rightOrthogonal_of_adjunction {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.CommShift ℤ] {Q K : C} {P : D} (hret : Retract P (L.obj Q))
    (hP : (singleton P).IsWeakTriangulatedGenerator)
    (hunit : ∀ E : C, ((singleton K).shiftClosure ℤ).rightOrthogonal E →
      IsIso (adj.unit.app E))
    (E : C) (hQ : ((singleton Q).shiftClosure ℤ).rightOrthogonal E)
    (hK : ((singleton K).shiftClosure ℤ).rightOrthogonal E) :
    IsZero E := by
  have : R.IsRightAdjoint := adj.isRightAdjoint
  have hiso := hunit E hK
  have hLE : IsZero (L.obj E) :=
    hP _ (rightOrthogonal_shiftClosure_singleton_of_retract hret
      (rightOrthogonal_shiftClosure_singleton_map_of_isIso_unit adj hiso hQ))
  exact (R.map_isZero hLE).of_iso (asIso (adj.unit.app E))

/-- **`Q ⊕ K` is a weak generator**: the generation step of [Stacks, Tag 09IS] and
[Stacks, Tag 0A9A] in the form the sources state it, with the one geometric input left as the
hypothesis `hunit`. -/
theorem isWeakTriangulatedGenerator_singleton_biprod_of_adjunction
    [∀ n : ℤ, (shiftFunctor C n).Additive] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.CommShift ℤ] {Q K : C} [HasBinaryBiproduct Q K] {P : D} (hret : Retract P (L.obj Q))
    (hP : (singleton P).IsWeakTriangulatedGenerator)
    (hunit : ∀ E : C, ((singleton K).shiftClosure ℤ).rightOrthogonal E →
      IsIso (adj.unit.app E)) :
    (singleton (Q ⊞ K)).IsWeakTriangulatedGenerator := fun E hE =>
  have h := (rightOrthogonal_shiftClosure_singleton_biprod_iff Q K E).1 hE
  isZero_of_rightOrthogonal_of_adjunction adj hret hP hunit E h.1 h.2

end Adjunction

end CategoryTheory.ObjectProperty

end
