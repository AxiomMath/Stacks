module

public import StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsite
public import StacksFrontier.CategoryTheory.Sites.Pretopology.TautologicalRelaxed
public import Mathlib.CategoryTheory.Sites.Coverage

/-!
# Sheaves on a site only depend on its coverings up to refinement (Stacks 00VX)

A site in the sense of Stacks 00VH is a category `C` with a class `IsCov` of families of
morphisms with fixed target satisfying the isomorphism, composition and base change axioms
(`IsSite`). No fibre products are assumed in `C`: the base change axiom only asks that the fibre
products of a covering along a morphism exist. A presheaf of sets is a *sheaf* on the site
(Stacks 00VM) if it satisfies the sheaf condition for every covering of `IsCov`
(`Covering.IsSheaf`).

Stacks 00VX compares the sheaves of two site structures `IsCov₁`, `IsCov₂` on the same category.

## Main definitions

* `Covering.IsSheaf IsCov P`: `P` satisfies the sheaf condition for every covering in `IsCov`.

## Main results

* `Covering.isSheaf_of_tautologicallyEquivalent` and
  `Covering.isSheaf_iff_of_tautologicallyEquivalent`: Stacks 00VX (1).
* `Covering.isSheaf_of_factorsThru`, `Covering.isSheaf_iff_of_factorsThru`: Stacks 00VX (2).

## The sheaf condition

The sheaf condition for a covering `{Uᵢ ⟶ U}` is Mathlib's `Presieve.IsSheafFor` for the presieve
of its arrows. In a site the fibre products `Uᵢ ×_U Uⱼ` exist
(`Covering.hasPairwisePullbacks_of_baseChangeCond`), and there `Presieve.IsSheafFor` is the
equalizer condition of Stacks 00VN with them
(`Covering.isSheafFor_presieve₀_iff_pullbackCompatible`).

Refinement of families (Stacks 00VT (2)) is Mathlib's `Presieve.FactorsThru` of the presieves of
arrows, and tautological equivalence (Stacks 00VU (2)) is
`PreZeroHypercover.TautologicallyEquivalent`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w w₁ w₂ v u

variable {C : Type u} [Category.{v} C]

namespace Covering

/-- A presheaf of sets `P` is a *sheaf* on the site given by the class of coverings `IsCov`
(Stacks 00VM) if it satisfies the sheaf condition for every covering in `IsCov`. -/
def IsSheaf (IsCov : Covering.{u, v, w} C → Prop) (P : Cᵒᵖ ⥤ Type t) : Prop :=
  ∀ 𝒰 : Covering.{u, v, w} C, IsCov 𝒰 → Presieve.IsSheafFor P 𝒰.2.presieve₀

/-- In a class of coverings satisfying the base change axiom, the fibre products `Uᵢ ×_U Uⱼ` of
the members of a covering exist. -/
lemma hasPairwisePullbacks_of_baseChangeCond {IsCov : Covering.{u, v, w} C → Prop}
    (hBC : BaseChangeCond IsCov) {𝒰 : Covering.{u, v, w} C} (h𝒰 : IsCov 𝒰) :
    𝒰.2.presieve₀.HasPairwisePullbacks := by
  refine ⟨?_⟩
  rintro _ _ _ ⟨i⟩ _ ⟨j⟩
  obtain ⟨P, π₁, π₂, hpb, -⟩ := hBC 𝒰 h𝒰 (𝒰.2.X j) (𝒰.2.f j)
  exact (hpb i).hasPullback

/-- When the fibre products `Uᵢ ×_U Uⱼ` exist, the sheaf condition for the covering `{Uᵢ ⟶ U}` is
the equalizer condition of Stacks 00VN: every family of sections agreeing on the fibre products
glues uniquely. -/
lemma isSheafFor_presieve₀_iff_pullbackCompatible (𝒰 : Covering.{u, v, w} C)
    [𝒰.2.presieve₀.HasPairwisePullbacks] (P : Cᵒᵖ ⥤ Type t) :
    Presieve.IsSheafFor P 𝒰.2.presieve₀ ↔
      ∀ x : (i : 𝒰.2.I₀) → P.obj (op (𝒰.2.X i)), Presieve.Arrows.PullbackCompatible P 𝒰.2.f x →
        ∃! s, ∀ i, P.map (𝒰.2.f i).op s = x i :=
  Presieve.isSheafFor_arrows_iff_pullbacks P 𝒰.2.f

/-- **Stacks 00VX (1)**, the inclusion: if every covering of the site `IsCov₁` is tautologically
equivalent to some covering of the site `IsCov₂`, then `Sh(C, IsCov₂) ⊆ Sh(C, IsCov₁)`. -/
@[stacks 00VX "(1)"]
theorem isSheaf_of_tautologicallyEquivalent {IsCov₁ : Covering.{u, v, w₁} C → Prop}
    {IsCov₂ : Covering.{u, v, w₂} C → Prop} (_h₁ : IsSite IsCov₁) (_h₂ : IsSite IsCov₂)
    (h : ∀ 𝒰 : Covering.{u, v, w₁} C, IsCov₁ 𝒰 → ∃ 𝒱 : PreZeroHypercover.{w₂} 𝒰.1,
      IsCov₂ ⟨𝒰.1, 𝒱⟩ ∧ PreZeroHypercover.TautologicallyEquivalent 𝒰.2 𝒱)
    (P : Cᵒᵖ ⥤ Type t) (hP : IsSheaf IsCov₂ P) : IsSheaf IsCov₁ P := by
  intro 𝒰 h𝒰
  obtain ⟨𝒱, h𝒱, hequiv⟩ := h 𝒰 h𝒰
  exact (PreZeroHypercover.isSheafFor_presieve₀_iff_of_tautologicallyEquivalent _ _ hequiv P).2
    (hP _ h𝒱)

/-- **Stacks 00VX (1)**, the equality: if moreover every covering of `IsCov₂` is tautologically
equivalent to some covering of `IsCov₁`, then the two sites have the same sheaves. -/
@[stacks 00VX "(1)"]
theorem isSheaf_iff_of_tautologicallyEquivalent {IsCov₁ : Covering.{u, v, w₁} C → Prop}
    {IsCov₂ : Covering.{u, v, w₂} C → Prop} (h₁ : IsSite IsCov₁) (h₂ : IsSite IsCov₂)
    (h₁₂ : ∀ 𝒰 : Covering.{u, v, w₁} C, IsCov₁ 𝒰 → ∃ 𝒱 : PreZeroHypercover.{w₂} 𝒰.1,
      IsCov₂ ⟨𝒰.1, 𝒱⟩ ∧ PreZeroHypercover.TautologicallyEquivalent 𝒰.2 𝒱)
    (h₂₁ : ∀ 𝒰 : Covering.{u, v, w₂} C, IsCov₂ 𝒰 → ∃ 𝒱 : PreZeroHypercover.{w₁} 𝒰.1,
      IsCov₁ ⟨𝒰.1, 𝒱⟩ ∧ PreZeroHypercover.TautologicallyEquivalent 𝒰.2 𝒱)
    (P : Cᵒᵖ ⥤ Type t) : IsSheaf IsCov₁ P ↔ IsSheaf IsCov₂ P :=
  ⟨isSheaf_of_tautologicallyEquivalent h₂ h₁ h₂₁ P,
    isSheaf_of_tautologicallyEquivalent h₁ h₂ h₁₂ P⟩

/-- **Stacks 00VX (2)**, the inclusion: if every covering of the site `IsCov₁` is refined by some
covering of the site `IsCov₂`, then `Sh(C, IsCov₂) ⊆ Sh(C, IsCov₁)`.

As in the source, a sheaf for `IsCov₂` is a sheaf for the refining covering `{Vⱼ ⟶ U}` and,
by the base change axiom of `IsCov₂`, separated for each `{Vⱼ ×_U Uᵢ ⟶ Uᵢ}`; this is the input
of Stacks 0G1L, here `Presieve.isSheafFor_of_factorsThru`. -/
@[stacks 00VX "(2)"]
theorem isSheaf_of_factorsThru {IsCov₁ : Covering.{u, v, w₁} C → Prop}
    {IsCov₂ : Covering.{u, v, w₂} C → Prop} (_h₁ : IsSite IsCov₁) (h₂ : IsSite IsCov₂)
    (h : ∀ 𝒰 : Covering.{u, v, w₁} C, IsCov₁ 𝒰 → ∃ 𝒱 : PreZeroHypercover.{w₂} 𝒰.1,
      IsCov₂ ⟨𝒰.1, 𝒱⟩ ∧ 𝒱.presieve₀.FactorsThru 𝒰.2.presieve₀)
    (P : Cᵒᵖ ⥤ Type t) (hP : IsSheaf IsCov₂ P) : IsSheaf IsCov₁ P := by
  intro 𝒰 h𝒰
  obtain ⟨𝒱, h𝒱, hfac⟩ := h 𝒰 h𝒰
  refine Presieve.isSheafFor_of_factorsThru P hfac (hP _ h𝒱) ?_
  rintro Y f ⟨i⟩
  obtain ⟨Q, π₁, π₂, hpb, hcov⟩ := h₂.2.2 ⟨𝒰.1, 𝒱⟩ h𝒱 (𝒰.2.X i) (𝒰.2.f i)
  refine ⟨_, (hP _ hcov).isSeparatedFor, ?_⟩
  rintro Z g ⟨j⟩
  exact ⟨𝒱.X j, π₁ j, 𝒱.f j, ⟨j⟩, (hpb j).w⟩

/-- **Stacks 00VX (2)**, the equality: if moreover every covering of `IsCov₂` is refined by some
covering of `IsCov₁`, then the two sites have the same sheaves. -/
@[stacks 00VX "(2)"]
theorem isSheaf_iff_of_factorsThru {IsCov₁ : Covering.{u, v, w₁} C → Prop}
    {IsCov₂ : Covering.{u, v, w₂} C → Prop} (h₁ : IsSite IsCov₁) (h₂ : IsSite IsCov₂)
    (h₁₂ : ∀ 𝒰 : Covering.{u, v, w₁} C, IsCov₁ 𝒰 → ∃ 𝒱 : PreZeroHypercover.{w₂} 𝒰.1,
      IsCov₂ ⟨𝒰.1, 𝒱⟩ ∧ 𝒱.presieve₀.FactorsThru 𝒰.2.presieve₀)
    (h₂₁ : ∀ 𝒰 : Covering.{u, v, w₂} C, IsCov₂ 𝒰 → ∃ 𝒱 : PreZeroHypercover.{w₁} 𝒰.1,
      IsCov₁ ⟨𝒰.1, 𝒱⟩ ∧ 𝒱.presieve₀.FactorsThru 𝒰.2.presieve₀)
    (P : Cᵒᵖ ⥤ Type t) : IsSheaf IsCov₁ P ↔ IsSheaf IsCov₂ P :=
  ⟨isSheaf_of_factorsThru h₂ h₁ h₂₁ P, isSheaf_of_factorsThru h₁ h₂ h₁₂ P⟩

end Covering
