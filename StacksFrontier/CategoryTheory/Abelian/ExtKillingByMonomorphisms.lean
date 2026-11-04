module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Data.Fintype.EquivFin

/-!
# Killing an `Ext` class by a monomorphism, after an exact functor

Let `Φ : C ⥤ D` be an exact additive functor between abelian categories, `A` an object of `D`
and `P` a property of objects of `C` closed under quotients and extensions. For an object `G`
of `C` and a class `ζ ∈ Ext^q(A, Φ G)`, say that `ζ` *can be killed* when there is a
monomorphism `f : G ⟶ G'` with `P G'` such that `ζ` maps to zero in `Ext^q(A, Φ G')`.

This is the shape of the conclusion of
[Stacks, Tag 09ZE](https://stacks.math.columbia.edu/tag/09ZE), with `Φ` the restriction of
abelian sheaves from `X_étale` to `Z_étale`, `A` the constant sheaf `ℤ` on `Z` and `P` the torsion
sheaves. The source reduces that statement three times, each time by one of the closure
properties proved here:

* along a morphism `G ⟶ F` into a member of `P` — the pushout `G' ⊔_G F` kills the image of the
  class (`Stacks.ExtKilling.canBeKilled_comp_of_canBeKilled`);
* to an object containing `G` — a monomorphism out of the larger object restricts to `G`
  (`Stacks.ExtKilling.canBeKilled_of_mono`);
* to the summands of a binary biproduct (`Stacks.ExtKilling.canBeKilled_biprod`), and of a
  finite biproduct (`Stacks.ExtKilling.canBeKilled_biproduct`): a constructible sheaf embeds in a
  finite direct sum `⨁ᵢ fᵢ_* Mᵢ`.

## Main definitions

* `Stacks.ExtKilling.CanBeKilled` — the property above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' v v' u u'

namespace Stacks.ExtKilling

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} D]
  (Φ : C ⥤ D) [Φ.Additive] (P : ObjectProperty C) (A : D) (q : ℕ)

/-- A class `ζ ∈ Ext^q(A, Φ G)` **can be killed** when some monomorphism `G ⟶ G'` into an
object with property `P` sends it to zero in `Ext^q(A, Φ G')`. -/
def CanBeKilled {G : C} (ζ : Ext.{w} A (Φ.obj G) q) : Prop :=
  ∃ (G' : C) (f : G ⟶ G'), Mono f ∧ P G' ∧ ζ.comp (Ext.mk₀ (Φ.map f)) (add_zero q) = 0

variable {Φ P A q}

/-- Composing a class with `Φ.map (a ≫ b)` is composing with `Φ.map a` and then `Φ.map b`. -/
private theorem comp_mk₀_map_comp {X : Type u} [Category.{v} X] {Y : Type u'} [Category.{v'} Y]
    [Abelian Y] [HasExt.{w} Y] (Ψ : X ⥤ Y) {B : Y} {n : ℕ} {G H K : X} (ζ : Ext.{w} B (Ψ.obj G) n)
    (a : G ⟶ H) (b : H ⟶ K) :
    ζ.comp (Ext.mk₀ (Ψ.map (a ≫ b))) (add_zero n) =
      (ζ.comp (Ext.mk₀ (Ψ.map a)) (add_zero n)).comp (Ext.mk₀ (Ψ.map b)) (add_zero n) := by
  rw [Ψ.map_comp, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero]

omit [Φ.Additive] in
/-- **Reduction along a morphism into a member of `P`.** If `ζ ∈ Ext^q(A, Φ G)` can be killed
and `φ : G ⟶ F` is a morphism into an object with property `P`, then the image of `ζ` in
`Ext^q(A, Φ F)` can be killed: by the pushout of the killing monomorphism along `φ`. -/
theorem canBeKilled_comp_of_canBeKilled [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    {G F : C} (φ : G ⟶ F) (hF : P F) {ζ : Ext.{w} A (Φ.obj G) q}
    (h : CanBeKilled Φ P A q ζ) :
    CanBeKilled Φ P A q (ζ.comp (Ext.mk₀ (Φ.map φ)) (add_zero q)) := by
  obtain ⟨G', f, hf, hG', hζ⟩ := h
  refine ⟨pushout f φ, pushout.inr f φ, Abelian.mono_pushout_of_mono_f f φ, ?_, ?_⟩
  · have hsum : P (G' ⊞ F) := P.prop_biprod hG' hF
    have : Epi (biprod.desc (pushout.inl f φ) (pushout.inr f φ)) :=
      ⟨fun a b h => pushout.hom_ext (by simpa using biprod.inl ≫= h)
        (by simpa using biprod.inr ≫= h)⟩
    exact P.prop_of_epi (biprod.desc (pushout.inl f φ) (pushout.inr f φ)) hsum
  · rw [← comp_mk₀_map_comp, ← pushout.condition, comp_mk₀_map_comp, hζ, Ext.zero_comp]

omit [Abelian C] [Φ.Additive] in
/-- **Reduction to a larger object.** If `m : G ⟶ H` is a monomorphism and the image of `ζ` in
`Ext^q(A, Φ H)` can be killed, then so can `ζ`. -/
theorem canBeKilled_of_mono {G H : C} (m : G ⟶ H) [Mono m] {ζ : Ext.{w} A (Φ.obj G) q}
    (h : CanBeKilled Φ P A q (ζ.comp (Ext.mk₀ (Φ.map m)) (add_zero q))) :
    CanBeKilled Φ P A q ζ := by
  obtain ⟨H', f, hf, hH', hζ⟩ := h
  refine ⟨H', m ≫ f, mono_comp m f, hH', ?_⟩
  rw [comp_mk₀_map_comp, hζ]

/-- **Reduction to the summands of a binary biproduct.** A class in `Ext^q(A, Φ(H₁ ⊞ H₂))` can be
killed as soon as its two components can. -/
theorem canBeKilled_biprod [P.IsClosedUnderExtensions] {H₁ H₂ : C}
    {ζ : Ext.{w} A (Φ.obj (H₁ ⊞ H₂)) q}
    (h₁ : CanBeKilled Φ P A q (ζ.comp (Ext.mk₀ (Φ.map biprod.fst)) (add_zero q)))
    (h₂ : CanBeKilled Φ P A q (ζ.comp (Ext.mk₀ (Φ.map biprod.snd)) (add_zero q))) :
    CanBeKilled Φ P A q ζ := by
  obtain ⟨H₁', f₁, hf₁, hP₁, hζ₁⟩ := h₁
  obtain ⟨H₂', f₂, hf₂, hP₂, hζ₂⟩ := h₂
  refine ⟨H₁' ⊞ H₂', biprod.map f₁ f₂, inferInstance, P.prop_biprod hP₁ hP₂, ?_⟩
  have htotal : biprod.map f₁ f₂ = biprod.fst ≫ f₁ ≫ biprod.inl + biprod.snd ≫ f₂ ≫ biprod.inr := by
    ext <;> simp
  rw [htotal, Φ.map_add, Ext.mk₀_add, Ext.comp_add, comp_mk₀_map_comp, comp_mk₀_map_comp,
    comp_mk₀_map_comp, comp_mk₀_map_comp, hζ₁, hζ₂, Ext.zero_comp, Ext.zero_comp, add_zero]


section FiniteBiproducts

attribute [local instance] Abelian.hasFiniteBiproducts

/-- **A property closed under quotients and extensions and containing zero is closed under
finite biproducts.** By induction on the number of summands: `⨁ E` is an extension of `E i` by
the kernel of the projection to `E i`, which is the biproduct of the remaining summands. -/
theorem prop_biproduct [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions] [P.ContainsZero]
    {J : Type} [Finite J] (E : J → C) (h : ∀ j, P (E j)) : P (⨁ E) := by
  classical
  suffices H : ∀ (n : ℕ) {J : Type} [Finite J] (E : J → C), Nat.card J = n →
      (∀ j, P (E j)) → P (⨁ E) from H _ E rfl h
  intro n
  induction n with
  | zero =>
    intro J _ E hcard _
    have : IsEmpty J := Finite.card_eq_zero_iff.mp hcard
    refine P.prop_of_isZero ?_
    rw [IsZero.iff_id_eq_zero]
    exact biproduct.hom_ext _ _ fun j => isEmptyElim j
  | succ m ih =>
    intro J _ E hcard h
    obtain ⟨i⟩ : Nonempty J := Finite.card_pos_iff.mp (by omega)
    have hcard' : Nat.card {j // j ≠ i} = m := by
      have := Fintype.ofFinite J
      rw [Nat.card_eq_fintype_card] at hcard ⊢
      rw [Fintype.card_subtype_compl (p := fun j => j = i), Fintype.card_subtype_eq, hcard]
      omega
    have : IsSplitEpi (biproduct.π E i) := IsSplitEpi.mk' ⟨biproduct.ι E i, by simp⟩
    have hSE : (ShortComplex.kernelSequence (biproduct.π E i)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _) inferInstance
        (inferInstanceAs (Epi (biproduct.π E i)))
    exact P.prop_X₂_of_shortExact hSE
      (P.prop_of_iso (kernelBiproductπIso E i).symm (ih _ hcard' fun j => h j.1)) (h i)

/-- **Reduction to the summands of a finite biproduct.** A class in `Ext^q(A, Φ(⨁ⱼ Hⱼ))` can be
killed as soon as each of its components can: the biproduct of the killing monomorphisms kills
it. -/
theorem canBeKilled_biproduct [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    [P.ContainsZero] {J : Type} [Finite J] {H : J → C} {ζ : Ext.{w} A (Φ.obj (⨁ H)) q}
    (h : ∀ j, CanBeKilled Φ P A q (ζ.comp (Ext.mk₀ (Φ.map (biproduct.π H j))) (add_zero q))) :
    CanBeKilled Φ P A q ζ := by
  classical
  have := Fintype.ofFinite J
  choose H' f hf hP hζ using h
  refine ⟨⨁ H', biproduct.map f, inferInstance, prop_biproduct H' hP, ?_⟩
  rw [biproduct.map_eq, Φ.map_sum, Ext.mk₀_sum, Ext.comp_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [comp_mk₀_map_comp, comp_mk₀_map_comp, hζ j, Ext.zero_comp]

end FiniteBiproducts

end Stacks.ExtKilling

end
