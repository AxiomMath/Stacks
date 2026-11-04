module

public import StacksFrontier.Algebra.Homology.DerivedCategory.HasRightDerivedFunctorPlus
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# `Ext` groups along an adjunction whose right adjoint is only acyclic

Let `L ⊣ R` be an adjunction of abelian categories with `L` exact and the target of `L` having
enough injectives. `StacksFrontier/CategoryTheory/Abelian/ExtAdjunction.lean` shows that `L` is then
bijective on all `Ext` groups provided `R` is *exact* and the unit is invertible. Exactness of
`R` is far stronger than what the argument needs: the dimension shifting there runs over an
injective presentation `M ↪ I` of the target, and all it asks of `R` is that the resulting
`0 ⟶ M ⟶ I ⟶ I/M ⟶ 0` stay short exact after applying `R`, and that `I` and `I/M` be again
admissible targets. This file replaces exactness of `R` by exactly those two closure properties,
and then discharges them from right acyclicity
(`CategoryTheory.Functor.rightAcyclic`) of the single object in question.

The situation this is written for is a right adjoint which is left exact and whose higher right
derived functors vanish only on the subcategory of interest, so that the hypothesis of
`Stacks.ExtAdjunction.extMap_bijective` is unavailable — and false — while its conclusion still
holds on that subcategory.

## Main results

* `Stacks.ExtAdjunction.extMap_naturality_extClass_of_shortExact` — naturality of the adjunction
  map in the extension class, for a short exact sequence whose image under `R` is short exact;
  this is `Stacks.ExtAdjunction.extMap_naturality_extClass` with that short exactness taken as a
  hypothesis instead of deduced from exactness of `R`.
* `Stacks.ExtAdjunction.extMap_bijective_of_acyclicClass` — the adjunction map
  `Ext^n(A, R M) ⟶ Ext^n(L A, M)` is bijective at every member of a class of objects which
  contains the injectives and is stable under the cokernel of an injective presentation, `R`
  keeping that cokernel sequence short exact.
* `Stacks.ExtAdjunction.mapExtAddHom_bijective_of_acyclicClass` — the same read for `L` itself,
  where the unit is invertible at `B` and `L B` belongs to the class.
* `Stacks.ExtAdjunction.rightAcyclic_shortExact_map_of_injective` — the class of `R`-acyclic
  objects has those two properties, which is [Stacks, Tag 015D].
* `Stacks.ExtAdjunction.mapExtAddHom_bijective_of_rightAcyclic` and
  `Stacks.ExtAdjunction.mapExtAddHom_bijective_of_isZero_rightDerived` — the two together: if
  the unit is invertible at `B` and `L B` is `R`-acyclic then `Ext^n(A, B) ⟶ Ext^n(L A, L B)` is
  bijective, with acyclicity spelled either as
  `CategoryTheory.Functor.rightAcyclic` or as the vanishing of the higher right derived functors
  of `R` at `L B`, which is the form in which such a vanishing is usually proved.

## Implementation notes

The `Ext`-level work is done in the first section, which deliberately has no
`HasDerivedCategory` instance in scope: with one in scope the elaboration of the `Ext`
operations takes a different instance path, and the commutativity goals of
`AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact` then do not match the
naturality lemmas, the two sides differing under an opaque `Shrink`. Hence the abstract class
`𝒜` in the first section and its discharge in the second, rather than one statement about
`CategoryTheory.Functor.rightAcyclic`.

The side condition of `CategoryTheory.Functor.rightAcyclic` is supplied by
`CategoryTheory.Functor.hasRightDerivedFunctor_mapHomotopyCategoryPlus_comp_Qh`, which exists
only because the general instance search for it exhausts the default
`synthInstance.maxHeartbeats` in a context of this size.

## References

* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
-/

@[expose] public noncomputable section

universe t t' w w' v v' u u'

namespace Stacks.ExtAdjunction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C}
  (adj : L ⊣ R) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [HasExt.{w} C] [HasExt.{w'} D] [R.Additive]

/-! ### The dimension shifting, over an abstract class of admissible targets -/

/-- Naturality of the adjunction map `Ext^n(A, R −) ⟶ Ext^n(L A, −)` in the extension class of a
short exact sequence `S`, for an `S` whose image under `R` is again short exact. This is
`Stacks.ExtAdjunction.extMap_naturality_extClass` with that short exactness as a hypothesis
rather than a consequence of exactness of `R`. -/
public lemma extMap_naturality_extClass_of_shortExact (A : C) {S : ShortComplex D}
    (hS : S.ShortExact) (hSR : (S.map R).ShortExact) (n : ℕ)
    (e : Ext.{w} A (R.obj S.X₃) n) :
    extMap adj A S.X₁ (n + 1) (e.comp hSR.extClass rfl) =
      (extMap adj A S.X₃ n e).comp hS.extClass rfl := by
  rw [extMap_apply, extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
    Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero]
  congr 1
  exact (hSR.map_of_exact L).extClass_naturality hS (counitShortComplexHom adj S)

/-- Exactness at `Ext^n(A, S.X₃)` of the covariant `Ext` sequence, as an exact pair of maps. -/
private theorem function_exact_postcomp_mk₀_postcomp_extClass {E : Type*} [Category* E]
    [Abelian E] [HasExt.{w} E] (A : E) {S : ShortComplex E} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact ((Ext.mk₀ S.g).postcomp A (add_zero n) : Ext A S.X₂ n → _)
      (hS.extClass.postcomp A (rfl : n + 1 = n + 1)) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.covariant_sequence_exact₃' A hS n (n + 1) rfl)

variable [EnoughInjectives D]

attribute [local instance] Ext.subsingleton_of_injective in
/-- **The adjunction map `Ext^n(A, R M) ⟶ Ext^n(L A, M)` is bijective at every member of a class
of admissible targets.** The class `𝒜` must contain the injective objects and, for a short exact
`0 ⟶ M ⟶ I ⟶ N ⟶ 0` with `M` in `𝒜` and `I` injective, must contain `N` and have that sequence
stay short exact after applying `R`. Those are the only two uses the dimension shifting of
`Stacks.ExtAdjunction.extMap_bijective` makes of exactness of `R`. -/
public lemma extMap_bijective_of_acyclicClass (𝒜 : ObjectProperty D)
    (hinj : ∀ I : D, Injective I → 𝒜 I)
    (hstep : ∀ S : ShortComplex D, S.ShortExact → 𝒜 S.X₁ → Injective S.X₂ →
      𝒜 S.X₃ ∧ (S.map R).ShortExact)
    (A : C) (M : D) (hM : 𝒜 M) (n : ℕ) :
    Function.Bijective (extMap adj A M n : Ext.{w} A (R.obj M) n → Ext.{w'} (L.obj A) M n) := by
  have : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  induction n generalizing M with
  | zero => exact extMap_zero_bijective adj A M
  | succ k hk =>
    let I : InjectivePresentation M := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hinj₂ : Injective S.X₂ := I.injective
    obtain ⟨hac₃, hSR⟩ := hstep S hS hM hinj₂
    have : Injective (S.map R).X₂ := R.injective_obj_of_injective I.injective
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (extMap adj A S.X₂ k) (extMap adj A S.X₃ k) (extMap adj A S.X₁ (k + 1))
      (by ext e; exact (extMap_naturality_mk₀ adj A S.g k e).symm)
      (by ext e; exact (extMap_naturality_extClass_of_shortExact adj A hS hSR k e).symm)
      (function_exact_postcomp_mk₀_postcomp_extClass A hSR k)
      (function_exact_postcomp_mk₀_postcomp_extClass (L.obj A) hS k)
      (hk S.X₂ (hinj S.X₂ hinj₂)).surjective (hk S.X₃ hac₃)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hSR x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ hS y₁ (by subsingleton) rfl)

/-- **`L` is bijective on `Ext^n(A, B)` as soon as the unit is invertible at `B` and `L B` is an
admissible target.** The triangle identity writes `Ext.mapExactFunctor L` as the adjunction map
precomposed with postcomposition by the unit, a bijection; the adjunction map is bijective at
`L B` by `Stacks.ExtAdjunction.extMap_bijective_of_acyclicClass`. -/
public lemma mapExtAddHom_bijective_of_acyclicClass (𝒜 : ObjectProperty D)
    (hinj : ∀ I : D, Injective I → 𝒜 I)
    (hstep : ∀ S : ShortComplex D, S.ShortExact → 𝒜 S.X₁ → Injective S.X₂ →
      𝒜 S.X₃ ∧ (S.map R).ShortExact)
    (A B : C) (hB : IsIso (adj.unit.app B)) (hLB : 𝒜 (L.obj B)) (n : ℕ) :
    Function.Bijective
      (L.mapExtAddHom A B n : Ext.{w} A B n → Ext.{w'} (L.obj A) (L.obj B) n) := by
  have := hB
  have key : ∀ e : Ext.{w} A B n, L.mapExtAddHom A B n e =
      extMap adj A (L.obj B) n (e.comp (Ext.mk₀ (adj.unit.app B)) (add_zero n)) := by
    intro e
    rw [extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, adj.left_triangle_components,
      Ext.comp_mk₀_id]
    rfl
  have h : (L.mapExtAddHom A B n : Ext.{w} A B n → Ext.{w'} (L.obj A) (L.obj B) n) =
      (extMap adj A (L.obj B) n) ∘
        ((Ext.mk₀ (adj.unit.app B)).postcomp (a := n) (b := n) A (add_zero n)) := funext key
  rw [h]
  exact (extMap_bijective_of_acyclicClass adj 𝒜 hinj hstep A (L.obj B) hLB n).comp
    (postcomp_mk₀_bijective_of_isIso (adj.unit.app B) n)

/-! ### The class of `R`-acyclic objects is admissible -/

section Acyclic

variable [PreservesFiniteLimits R]
  [HasDerivedCategory.{t} D] [HasDerivedCategory.{t'} C]

omit [HasExt C] [HasExt D] in
/-- **The `R`-acyclic objects are stable under the cokernel of an injective presentation, and
`R` keeps such a sequence short exact.** This is part (2) of [Stacks, Tag 015D], the middle term
of the sequence being injective and hence acyclic. -/
public lemma rightAcyclic_shortExact_map_of_injective (S : ShortComplex D) (hS : S.ShortExact)
    (h₁ : R.rightAcyclic S.X₁) (h₂ : Injective S.X₂) :
    R.rightAcyclic S.X₃ ∧ (S.map R).ShortExact :=
  have := h₂
  (R.rightAcyclic_and_shortExact_map_of_shortExact S hS).2.1 h₁
    (Functor.rightAcyclic_of_injective R S.X₂)

end Acyclic

/-! ### `Ext` along the adjunction at an acyclic object -/

section

variable [PreservesFiniteLimits R]

/-- **`L` is bijective on `Ext^n(A, B)` as soon as the unit is invertible at `B` and `L B` is
`R`-acyclic.** The `R`-acyclic objects are an admissible class of targets for
`Stacks.ExtAdjunction.mapExtAddHom_bijective_of_acyclicClass` by [Stacks, Tag 015D]. -/
public lemma mapExtAddHom_bijective_of_rightAcyclic
    [HasDerivedCategory.{t} D] [HasDerivedCategory.{t'} C] (A B : C)
    (hB : IsIso (adj.unit.app B)) (hLB : R.rightAcyclic (L.obj B)) (n : ℕ) :
    Function.Bijective
      (L.mapExtAddHom A B n : Ext.{w} A B n → Ext.{w'} (L.obj A) (L.obj B) n) :=
  mapExtAddHom_bijective_of_acyclicClass adj R.rightAcyclic
    (fun _ hI ↦ have := hI; Functor.rightAcyclic_of_injective R _)
    rightAcyclic_shortExact_map_of_injective A B hB hLB n

/-- **`Stacks.ExtAdjunction.mapExtAddHom_bijective_of_rightAcyclic` with acyclicity spelled as a
vanishing of higher right derived functors.** For a left exact `R` the two readings agree, by
[Stacks, Tag 015C]; this is the form in which such a vanishing is usually proved. -/
public lemma mapExtAddHom_bijective_of_isZero_rightDerived
    [HasDerivedCategory.{t} D] [HasDerivedCategory.{t'} C] (A B : C) (hB : IsIso (adj.unit.app B))
    (hLB : ∀ p : ℕ, 0 < p → IsZero ((R.rightDerived p).obj (L.obj B))) (n : ℕ) :
    Function.Bijective
      (L.mapExtAddHom A B n : Ext.{w} A B n → Ext.{w'} (L.obj A) (L.obj B) n) :=
  mapExtAddHom_bijective_of_rightAcyclic adj A B hB
    ((Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat R (L.obj B)).2 hLB) n

end

end Stacks.ExtAdjunction

end
