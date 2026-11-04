module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # Ext out of a coproduct

Let `𝒜` be an abelian category with enough injectives and `(X i)_{i ∈ ι}` a family of objects
of `𝒜` admitting a coproduct. Restriction along the inclusions `X i ⟶ ∐ X` identifies the
extension groups out of the coproduct with the product of the extension groups out of the
summands:

`Ext^n(∐ X, Y) ≅ ∏ Ext^n(X i, Y)`.

Mathlib has this for a *finite* family, as `CategoryTheory.Abelian.Ext.biproductAddEquiv`; the
statement here is for an arbitrary index type.

The proof is an induction on `n`, over all second arguments simultaneously. In degree zero the
statement is the universal property of the coproduct, transported along
`CategoryTheory.Abelian.Ext.homEquiv₀`. For the inductive step, embed `Y` in an injective object
`I` with cokernel `Q`; since `Ext^{n+1}(-, I)` vanishes, the connecting map
`Ext^n(-, Q) ⟶ Ext^{n+1}(-, Y)` of the covariant long exact sequence is surjective, and its
kernel is the image of `Ext^n(-, I)`. Both surjectivity of the restriction and its injectivity
then follow from the inductive hypothesis at `I` and at `Q`, because restriction commutes with
the connecting map and with `Ext^n(-, I) ⟶ Ext^n(-, Q)`: both are postcompositions, and
restriction is a precomposition, so this is associativity of the Yoneda composition.

## Main definitions

* `CategoryTheory.Abelian.Ext.coproductRestriction`: restriction of an extension class out of a
  coproduct to the summands.
* `CategoryTheory.Abelian.Ext.coproductAddEquiv`: the resulting isomorphism
  `Ext^n(∐ X, Y) ≅ ∏ Ext^n(X i, Y)`.

## Main results

* `CategoryTheory.Abelian.Ext.bijective_coproductRestriction`: restriction to the summands is
  bijective.
* `CategoryTheory.Abelian.Ext.coproductRestriction_comp`: restriction commutes with Yoneda
  postcomposition, which is its naturality in the second variable.

## Implementation notes

The coefficient universe of the extension groups is the universe `w` of `HasExt.{w} 𝒜` and the
index type of the family is in an unrelated universe, so the product is taken in the universe
containing both. No relation between them, and none between either of them and the universes of
`𝒜`, is needed: the whole argument is carried out inside Mathlib's `Ext` API, which is developed
at an arbitrary `HasExt` universe.
-/

@[expose] public noncomputable section

universe t w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {ι : Type t} (X : ι → C) [HasCoproduct X]

/-- Restriction of an extension class out of a coproduct to its summands: the map
`Ext^n(∐ X, Y) ⟶ ∏ Ext^n(X i, Y)` given by precomposition with the inclusions. -/
def coproductRestriction (Y : C) (n : ℕ) :
    Ext.{w} (∐ X) Y n →+ ((i : ι) → Ext.{w} (X i) Y n) where
  toFun e i := (mk₀ (Sigma.ι X i)).precomp Y (zero_add n) e
  map_zero' := by funext i; exact map_zero _
  map_add' a b := by funext i; exact map_add _ _ _

/-- The `i`-th component of `coproductRestriction X Y n e` is the Yoneda composition of the
inclusion `X i ⟶ ∐ X` with `e`. -/
lemma coproductRestriction_apply (Y : C) (n : ℕ) (e : Ext.{w} (∐ X) Y n) (i : ι) :
    coproductRestriction X Y n e i = (mk₀ (Sigma.ι X i)).comp e (zero_add n) :=
  rfl

/-- Restriction to the summands commutes with Yoneda postcomposition. This is the naturality of
`coproductRestriction` in the second variable. -/
lemma coproductRestriction_comp {Y Z : C} {a b c : ℕ} (e : Ext.{w} (∐ X) Y a)
    (β : Ext.{w} Y Z b) (h : a + b = c) (i : ι) :
    coproductRestriction X Z c (e.comp β h) i =
      (coproductRestriction X Y a e i).comp β h :=
  (comp_assoc (mk₀ (Sigma.ι X i)) e β (zero_add a) h (by lia)).symm

/-- In degree zero, restriction to the summands is the restriction of a morphism out of the
coproduct. -/
lemma homEquiv₀_coproductRestriction (Y : C) (e : Ext.{w} (∐ X) Y 0) (i : ι) :
    homEquiv₀ (coproductRestriction X Y 0 e i) = Sigma.ι X i ≫ homEquiv₀ e := by
  apply (mk₀_bijective _ _).injective
  rw [mk₀_homEquiv₀_apply, ← mk₀_comp_mk₀, mk₀_homEquiv₀_apply]
  rfl

/-- The inductive step of `bijective_coproductRestriction`: for a short exact sequence whose
middle term is injective, bijectivity of restriction in degree `n` at the middle and the last
term gives bijectivity in degree `n + 1` at the first term. -/
private lemma bijective_coproductRestriction_succ {S : ShortComplex C} (hS : S.ShortExact)
    [Injective S.X₂] (n : ℕ)
    (h₂ : Function.Bijective (coproductRestriction X S.X₂ n))
    (h₃ : Function.Bijective (coproductRestriction X S.X₃ n)) :
    Function.Bijective (coproductRestriction X S.X₁ (n + 1)) := by
  have hδ : ∀ (Z : C) (y : Ext.{w} Z S.X₁ (n + 1)),
      ∃ z : Ext.{w} Z S.X₃ n, z.comp hS.extClass rfl = y := fun Z y =>
    covariant_sequence_exact₁ Z hS y (eq_zero_of_injective _) rfl
  have key : ∀ e : Ext.{w} (∐ X) S.X₁ (n + 1),
      coproductRestriction X S.X₁ (n + 1) e = 0 → e = 0 := by
    intro e he
    obtain ⟨z, hz⟩ := hδ (∐ X) e
    have hzero : ∀ i : ι,
        ∃ u : Ext.{w} (X i) S.X₂ n,
          u.comp (mk₀ S.g) (add_zero n) = coproductRestriction X S.X₃ n z i := by
      intro i
      refine covariant_sequence_exact₃ (X i) hS _ (n₁ := n + 1) rfl ?_
      rw [← coproductRestriction_comp X z hS.extClass rfl i, hz, he]
      rfl
    choose u hu using hzero
    obtain ⟨v, hv⟩ := h₂.2 u
    have hvz : v.comp (mk₀ S.g) (add_zero n) = z := by
      refine h₃.1 (funext fun i => ?_)
      rw [coproductRestriction_comp X v (mk₀ S.g) (add_zero n) i, hv, hu]
    rw [← hz, ← hvz, comp_assoc v (mk₀ S.g) hS.extClass (add_zero n) (zero_add 1) (by lia),
      hS.comp_extClass, comp_zero]
  refine ⟨fun e₁ e₂ he => ?_, fun y => ?_⟩
  · rw [← sub_eq_zero]
    exact key _ (by rw [map_sub, he, sub_self])
  · choose z hz using fun i => hδ (X i) (y i)
    obtain ⟨zz, hzz⟩ := h₃.2 z
    refine ⟨zz.comp hS.extClass rfl, funext fun i => ?_⟩
    rw [coproductRestriction_comp X zz hS.extClass rfl i, hzz, hz]

/-- **Restriction to the summands is bijective.** For a family `(X i)` of objects of an abelian
category with enough injectives admitting a coproduct, precomposition with the inclusions
`X i ⟶ ∐ X` identifies `Ext^n(∐ X, Y)` with the product of the groups `Ext^n(X i, Y)`. -/
theorem bijective_coproductRestriction [EnoughInjectives C] (n : ℕ) (Y : C) :
    Function.Bijective (coproductRestriction X Y n) := by
  induction n generalizing Y with
  | zero =>
    refine ⟨fun e₁ e₂ he => ?_, fun y => ?_⟩
    · refine homEquiv₀.injective (Sigma.hom_ext _ _ fun i => ?_)
      rw [← homEquiv₀_coproductRestriction, ← homEquiv₀_coproductRestriction, congrFun he i]
    · refine ⟨homEquiv₀.symm (Sigma.desc fun i => homEquiv₀ (y i)), funext fun i => ?_⟩
      refine homEquiv₀.injective ?_
      rw [homEquiv₀_coproductRestriction, Equiv.apply_symm_apply, Sigma.ι_desc]
  | succ n ih =>
    exact bijective_coproductRestriction_succ X
      (S := ShortComplex.mk (Injective.ι Y) (cokernel.π (Injective.ι Y)) (cokernel.condition _))
      ⟨ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)⟩ n (ih _) (ih _)

/-- **`Ext` out of a coproduct is the product of the `Ext`s.** For a family `(X i)` of objects of
an abelian category with enough injectives admitting a coproduct, restriction along the
inclusions is an isomorphism `Ext^n(∐ X, Y) ≅ ∏ Ext^n(X i, Y)`. -/
def coproductAddEquiv [EnoughInjectives C] (Y : C) (n : ℕ) :
    Ext.{w} (∐ X) Y n ≃+ ((i : ι) → Ext.{w} (X i) Y n) where
  __ := Equiv.ofBijective _ (bijective_coproductRestriction X n Y)
  map_add' := (coproductRestriction X Y n).map_add

/-- The `i`-th component of `coproductAddEquiv X Y n e` is the Yoneda composition of the
inclusion `X i ⟶ ∐ X` with `e`. -/
lemma coproductAddEquiv_apply [EnoughInjectives C] (Y : C) (n : ℕ) (e : Ext.{w} (∐ X) Y n)
    (i : ι) : coproductAddEquiv X Y n e i = (mk₀ (Sigma.ι X i)).comp e (zero_add n) :=
  rfl

end CategoryTheory.Abelian.Ext

end
