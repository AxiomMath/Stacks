module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Conjugation by equivalences of categories over a base

Stacks 03YT: for categories `𝒮₁, …, 𝒮₄` over `𝒞` and equivalences `φ : 𝒮₁ ⟶ 𝒮₂`,
`ψ : 𝒮₃ ⟶ 𝒮₄` over `𝒞`, conjugation `α ↦ ψ ∘ α ∘ φ` is an equivalence of hom-categories
`Mor_{Cat/𝒞}(𝒮₂, 𝒮₃) ⥤ Mor_{Cat/𝒞}(𝒮₁, 𝒮₄)`. The source assumes each `𝒮ᵢ` is fibred in
groupoids, but only bicategorical formalism is used: pre- and postcomposition with an
equivalence in a bicategory are equivalences of hom-categories, so the hypothesis is dropped.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

variable {𝒞 : Type*} [Category 𝒞]

/-- Conjugation by `φ` and `ψ`: the functor `Mor_{Cat/𝒞}(𝒳₂, 𝒳₃) ⥤ Mor_{Cat/𝒞}(𝒳₁, 𝒳₄)`
sending a 1-morphism `α` to `ψ ∘ α ∘ φ`. -/
def conjugationFunctor {𝒳₁ 𝒳₂ 𝒳₃ 𝒳₄ : BasedCategory 𝒞}
    (φ : 𝒳₁ ⟶ 𝒳₂) (ψ : 𝒳₃ ⟶ 𝒳₄) : (𝒳₂ ⟶ 𝒳₃) ⥤ (𝒳₁ ⟶ 𝒳₄) :=
  Bicategory.precomp 𝒳₃ φ ⋙ Bicategory.postcomp 𝒳₁ ψ

section BicategoryHelpers

variable {B : Type*} [Bicategory B] {a b : B}

/-- Precomposition by an equivalence is an equivalence of hom-categories. -/
@[sga "1 VI 4.5" "more general"]
lemma precomp_isEquivalence_of_equiv (e : Bicategory.Equivalence a b) (c : B) :
    (Bicategory.precomp c e.hom).IsEquivalence :=
  let unit : 𝟭 (b ⟶ c) ≅ Bicategory.precomp c e.hom ⋙ Bicategory.precomp c e.inv :=
    NatIso.ofComponents
      (fun f => (Bicategory.leftUnitor f).symm ≪≫
        (Bicategory.whiskerRightIso e.counit f).symm ≪≫
        Bicategory.associator e.inv e.hom f)
      (fun {X Y} θ => by
        simp only [Functor.id_obj, precomp, Functor.comp_obj, Functor.id_map, Iso.trans_hom,
          Iso.symm_hom, whiskerRightIso_inv, Functor.comp_map, Category.assoc]
        slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
        slice_lhs 2 3 => rw [whisker_exchange]
        slice_lhs 3 4 => rw [associator_naturality_right])
  let counit : Bicategory.precomp c e.inv ⋙ Bicategory.precomp c e.hom ≅ 𝟭 (a ⟶ c) :=
    NatIso.ofComponents
      (fun g => (α_ e.hom e.inv g).symm ≪≫ Bicategory.whiskerRightIso e.unit.symm g ≪≫ λ_ g)
      (fun {f g} η => by
        simp only [Functor.id_obj, precomp, Functor.comp_obj, Functor.id_map, Iso.trans_hom,
          Iso.symm_hom, whiskerRightIso_hom, Functor.comp_map, Category.assoc]
        rw [comp_whiskerLeft_symm e.hom e.inv η]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        rw [whisker_exchange_assoc, leftUnitor_naturality])
  (CategoryTheory.Equivalence.mk
    (Bicategory.precomp c e.hom) (Bicategory.precomp c e.inv) unit counit).isEquivalence_functor

/-- Postcomposition by an equivalence is an equivalence of hom-categories. -/
@[sga "1 VI 4.5" "more general"]
lemma postcomp_isEquivalence_of_equiv (e : Bicategory.Equivalence a b) (c : B) :
    (Bicategory.postcomp c e.hom).IsEquivalence :=
  let unit : 𝟭 (c ⟶ a) ≅ Bicategory.postcomp c e.hom ⋙ Bicategory.postcomp c e.inv :=
    NatIso.ofComponents
      (fun f => (Bicategory.rightUnitor f).symm ≪≫
        Bicategory.whiskerLeftIso f e.unit ≪≫
        (Bicategory.associator f e.hom e.inv).symm)
      (fun {f g} η => by
        simp only [Functor.id_obj, postcomp, Iso.trans_hom, Iso.symm_hom, Functor.id_map,
          Functor.comp_obj, Functor.comp_map, Bicategory.whiskerLeftIso_hom, Category.assoc]
        rw [Bicategory.rightUnitor_inv_naturality_assoc,
            ← Bicategory.whisker_exchange_assoc,
            ← Bicategory.associator_inv_naturality_left])
  let counit : Bicategory.postcomp c e.inv ⋙ Bicategory.postcomp c e.hom ≅ 𝟭 (c ⟶ b) :=
    NatIso.ofComponents
      (fun g => Bicategory.associator g e.inv e.hom ≪≫
        Bicategory.whiskerLeftIso g e.counit ≪≫
        Bicategory.rightUnitor g)
      (fun {X Y} η => by
        simp only [Functor.id_obj, postcomp, Iso.trans_hom, Functor.id_map, Functor.comp_obj,
          Functor.comp_map, Bicategory.whiskerLeftIso_hom, Category.assoc]
        rw [Bicategory.associator_naturality_left_assoc,
            ← Bicategory.whisker_exchange_assoc,
            Bicategory.rightUnitor_naturality])
  (CategoryTheory.Equivalence.mk
    (Bicategory.postcomp c e.hom) (Bicategory.postcomp c e.inv) unit counit).isEquivalence_functor

end BicategoryHelpers

/-- **Stacks 03YT.** For `𝒮₁, …, 𝒮₄` over `𝒞` and equivalences `φ : 𝒮₁ ⟶ 𝒮₂`,
`ψ : 𝒮₃ ⟶ 𝒮₄` over `𝒞`, conjugation `α ↦ ψ ∘ α ∘ φ` is an equivalence of hom-categories
`Mor_{Cat/𝒞}(𝒮₂, 𝒮₃) ⥤ Mor_{Cat/𝒞}(𝒮₁, 𝒮₄)`.

The source additionally assumes each `𝒮ᵢ` is fibred in groupoids over `𝒞`.  Conjugation by
equivalences is an equivalence in any bicategory, so that hypothesis is unused; it is
omitted here and the statement proved is correspondingly more general than the tag. -/
@[stacks 03YT, sga "1 VI 4.5" "both displayed maps"]
theorem main_theorem03YT
    (𝒮₁ 𝒮₂ 𝒮₃ 𝒮₄ : BasedCategory 𝒞)
    (eφ : Bicategory.Equivalence 𝒮₁ 𝒮₂)
    (eψ : Bicategory.Equivalence 𝒮₃ 𝒮₄) :
    (conjugationFunctor eφ.hom eψ.hom).IsEquivalence :=
  have := precomp_isEquivalence_of_equiv eφ 𝒮₃
  have := postcomp_isEquivalence_of_equiv eψ 𝒮₁
  Functor.isEquivalence_trans (Bicategory.precomp 𝒮₃ eφ.hom) (Bicategory.postcomp 𝒮₁ eψ.hom)

