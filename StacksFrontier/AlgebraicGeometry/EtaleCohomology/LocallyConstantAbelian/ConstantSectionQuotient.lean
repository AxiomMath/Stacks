module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Grp.AB
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom

/-!
# Separating the value of a constant abelian sheaf

Let `J` be a Grothendieck topology on a category `C` with a final object `T`. The constant sheaf
functor on abelian groups is left adjoint to sections over `T`
(`CategoryTheory.constantSheafAdj`), and the unit of that adjunction is the map `B ⟶ B̲(T)` sending
an element of `B` to the corresponding constant section. That map need not be injective: over a
site in which the empty sieve is covering every sheaf is zero, and in general nothing identifies
`B` with a subgroup of `B̲(T)`.

What *is* true is that the kernel `N` of the unit is invisible to the constant sheaf functor. A
homomorphism from `B` to the sections of any sheaf over `T` factors through the unit, hence kills
`N`, so `B` and `B/N` corepresent the same functor and `B̲ ⟶ (B/N)̲` is an isomorphism. Replacing
`B` by `B/N` therefore changes nothing about the sheaf `B̲` and makes the unit injective.

This is the device that replaces the hypothesis
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`, under which injectivity of the unit
follows from local injectivity of the sheafification map, but which is available for `Ab.{w}` only
when the carrier universe `w` is the universe `max u v` fixed by the site.

## Main results

* `Stacks.ConstantSheaf.constantSheafUnitKernel` — the kernel of `B ⟶ B̲(T)`.
* `Stacks.ConstantSheaf.constantQuotient` and `Stacks.ConstantSheaf.constantQuotientMk` — the
  quotient of `B` by that kernel, and the projection onto it.
* `Stacks.ConstantSheaf.constantSheafUnitKernel_le_ker` — every homomorphism from `B` to the
  sections of a sheaf over `T` kills that kernel.
* `Stacks.ConstantSheaf.isIso_constantSheaf_map_constantQuotientMk` — the constant sheaf functor
  carries the projection to an isomorphism.
* `Stacks.ConstantSheaf.injective_constantSection_constantQuotient` — the constant section map of
  the quotient is injective.

## References

* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{w}]

/-- The subgroup of elements of `B` whose constant section over `T` vanishes. -/
def constantSheafUnitKernel (T : C) (B : Ab.{w}) : AddSubgroup B :=
  ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op T)).hom.ker

/-- The quotient of `B` by the elements whose constant section over `T` vanishes. -/
def constantQuotient (T : C) (B : Ab.{w}) : Ab.{w} :=
  AddCommGrpCat.of (B ⧸ constantSheafUnitKernel J T B)

/-- The projection of `B` onto `Stacks.ConstantSheaf.constantQuotient`. -/
def constantQuotientMk (T : C) (B : Ab.{w}) : B ⟶ constantQuotient J T B :=
  AddCommGrpCat.ofHom (QuotientAddGroup.mk' _)

/-- The constant section map of `B` over `T`, read on the quotient by its kernel. -/
def constantQuotientSection (T : C) (B : Ab.{w}) :
    constantQuotient J T B ⟶ ((sheafSections J Ab.{w}).obj (op T)).obj
      ((constantSheaf J Ab.{w}).obj B) :=
  AddCommGrpCat.ofHom (QuotientAddGroup.lift _
    ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op T)).hom fun _ hx => hx)

/-- The projection followed by the descended section map is the constant section map. -/
lemma constantQuotientMk_comp_constantQuotientSection (T : C) (B : Ab.{w}) :
    constantQuotientMk J T B ≫ constantQuotientSection J T B =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op T) := by
  ext _
  rfl

/-- The descended section map is injective: the quotient was taken by its kernel. -/
lemma injective_constantQuotientSection (T : C) (B : Ab.{w}) :
    Function.Injective (constantQuotientSection J T B) := by
  intro x y h
  induction x using QuotientAddGroup.induction_on with
  | H a =>
  induction y using QuotientAddGroup.induction_on with
  | H b =>
  have h' : a - b ∈ constantSheafUnitKernel J T B := by
    show ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op T)).hom (a - b) = 0
    rw [map_sub, sub_eq_zero]
    exact h
  exact QuotientAddGroup.eq_iff_sub_mem.mpr h'

/-- The constant section map of the quotient, precomposed with the quotient's own section map,
is the constant section map of `B` read on the quotient. This is naturality of the sheafification
map together with surjectivity of the projection. -/
lemma constantQuotientSection_comp_map (T : C) (B : Ab.{w}) :
    constantQuotientSection J T B ≫ ((sheafSections J Ab.{w}).obj (op T)).map
        ((constantSheaf J Ab.{w}).map (constantQuotientMk J T B)) =
      (CategoryTheory.toSheafify J
        ((Functor.const Cᵒᵖ).obj (constantQuotient J T B))).app (op T) := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H b =>
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app (CategoryTheory.toSheafify_naturality J
    ((Functor.const Cᵒᵖ).map (constantQuotientMk J T B))) (op T)) b).symm

section Terminal

variable {T : C} (hT : IsTerminal T) (B : Ab.{w})

include hT in
/-- The identity of a constant sheaf corresponds, under the constant sheaf adjunction, to the
constant section map. -/
lemma constantSheafAdj_homEquiv_id :
    (constantSheafAdj J Ab.{w} hT).homEquiv B ((constantSheaf J Ab.{w}).obj B) (𝟙 _) =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op T) := by
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).trans (constantSheafAdj_unit_app J Ab.{w} hT B)

include hT in
/-- A homomorphism from `B` to the sections of a sheaf over the final object annihilates the
kernel of the constant section map: by the constant sheaf adjunction it factors through that
map. -/
lemma constantSheafUnitKernel_le_ker (S : Sheaf J Ab.{w})
    (k : B ⟶ ((sheafSections J Ab.{w}).obj (op T)).obj S) :
    constantSheafUnitKernel J T B ≤ k.hom.ker := by
  intro b hb
  have hk := (constantSheafAdj J Ab.{w} hT).homEquiv_unit
    (f := ((constantSheafAdj J Ab.{w} hT).homEquiv B S).symm k)
  rw [Equiv.apply_symm_apply] at hk
  have hb' : ((constantSheafAdj J Ab.{w} hT).unit.app B) b = 0 := by
    rw [constantSheafAdj_unit_app J Ab.{w} hT B]
    exact hb
  show k b = 0
  rw [ConcreteCategory.congr_hom hk b, ConcreteCategory.comp_apply, hb', map_zero]

include hT in
/-- **The quotient does not change the constant sheaf.** The constant sheaf functor carries the
projection `B ⟶ B/N`, with `N` the kernel of the constant section map over the final object, to an
isomorphism: by the constant sheaf adjunction both `B` and `B/N` corepresent sections over the
final object, because every homomorphism from `B` to such sections kills `N`. -/
lemma isIso_constantSheaf_map_constantQuotientMk :
    IsIso ((constantSheaf J Ab.{w}).map (constantQuotientMk J T B)) := by
  refine ⟨((constantSheafAdj J Ab.{w} hT).homEquiv _ _).symm (constantQuotientSection J T B),
    ?_, ?_⟩
  · rw [← Adjunction.homEquiv_naturality_left_symm,
      constantQuotientMk_comp_constantQuotientSection J T B,
      ← constantSheafAdj_homEquiv_id J hT B, Equiv.symm_apply_apply]
  · apply ((constantSheafAdj J Ab.{w} hT).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
      constantSheafAdj_homEquiv_id J hT (constantQuotient J T B),
      constantQuotientSection_comp_map J T B]

include hT in
/-- **The constant section map of the quotient is injective.** -/
lemma injective_constantSection_constantQuotient :
    Function.Injective ((CategoryTheory.toSheafify J
      ((Functor.const Cᵒᵖ).obj (constantQuotient J T B))).app (op T)) := by
  have hiso := isIso_constantSheaf_map_constantQuotientMk J hT B
  have hbij := ConcreteCategory.bijective_of_isIso
    (((sheafSections J Ab.{w}).obj (op T)).map
      ((constantSheaf J Ab.{w}).map (constantQuotientMk J T B)))
  rw [← constantQuotientSection_comp_map J T B]
  exact hbij.injective.comp (injective_constantQuotientSection J T B)

end Terminal

end Stacks.ConstantSheaf

end
