module

import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.CategoryTheory.Sites.LocallyFullyFaithful
import Mathlib.CategoryTheory.Monoidal.Mon

public import StacksCore.CategoryTheory.FiberedInGroupoids
import StacksCore.Tactic.StacksAttribute

/-! # Gerbes over a category fibred in groupoids

A `1`-morphism `F : 𝒳 ⥤ 𝒴` of categories fibred in groupoids over a site `(𝒞, J)` makes `𝒳`
a *gerbe over* `𝒴` when every object of `𝒴` is locally in the image of `F` and every morphism
between `F`-images locally comes from `𝒳`. Being a gerbe over is transitive.

## Main results

* `CategoryTheory.IsGerbeOver`: the definition, spelled out by the two conditions of
  Stacks 06P1 (2).
* `CategoryTheory.IsGerbeOver.comp`: a gerbe over a gerbe is a gerbe.

## Implementation notes

A `1`-morphism of categories over `𝒞` from `p : 𝒳 ⥤ 𝒞` to `q : 𝒴 ⥤ 𝒞` is a functor
`F : 𝒳 ⥤ 𝒴` with `F ⋙ q = p`, so `p` is not carried as separate data: it is `F ⋙ q`.

Coverings are covering sieves rather than covering families. The two agree for a category
fibred in groupoids, because the condition on a family propagates to the sieve it generates
by pulling the witnesses back along the factoring morphism.

A restriction `y|_V` of `y` along `f : V ⟶ U` is not named. The conditions instead quantify
existentially over a morphism lying over `f`, which for a category fibred in groupoids is the
same as a choice of restriction together with an isomorphism onto it, since every morphism of
such a category is strongly cartesian. For the same reason the two conditions may quantify
existentially over the restrictions they use. They carry *separate* coverings, as in
Stacks 06P1 (2): the covering in (2)(b) depends on the morphism `b`, and merging the two into
one covering would strengthen the definition.

Stacks states 06P2 for stacks in groupoids. `IsGerbeOver` asks only that both fibrations be
fibred in groupoids, which every stack in groupoids is; the definition of Stacks 06P2 itself,
with the stacks-in-groupoids hypotheses of Stacks 02ZI, is
`CategoryTheory.IsGerbeOverStackInGroupoids`, which is `IsGerbeOver` together with those
hypotheses. `IsGerbeOver.comp` is proved in the wider generality.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {𝒞 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃} {𝒵 : Type u₄}
  [Category.{v₁} 𝒞] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴] [Category.{v₄} 𝒵]

/-- Refining a covering. If `S₁` covers `U` and every `f : V ⟶ U` in `S₁` admits a covering
`S₂` of `V` such that `P` holds for `g ≫ f` for every `g` in `S₂`, then `U` has a covering
all of whose members satisfy `P`. -/
lemma GrothendieckTopology.exists_covering_of_refine (J : GrothendieckTopology 𝒞) {U : 𝒞}
    {P : ∀ ⦃T : 𝒞⦄, (T ⟶ U) → Prop} {S₁ : Sieve U} (hS₁ : S₁ ∈ J U)
    (h : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), S₁ f →
      ∃ S₂ ∈ J V, ∀ ⦃W : 𝒞⦄ (g : W ⟶ V), S₂ g → P (g ≫ f)) :
    ∃ S ∈ J U, ∀ ⦃T : 𝒞⦄ (k : T ⟶ U), S k → P k := by
  choose S₂ hS₂ h₂ using h
  refine ⟨Sieve.bind S₁ S₂, J.bind_covering hS₁ hS₂, ?_⟩
  rintro T k ⟨V, g, f, hf, hg, rfl⟩
  exact h₂ f hf g hg

/-- In a category fibred in groupoids, two morphisms `ξ : a ⟶ c` and `ξ' : b ⟶ c` lying over the
same `f` differ by a morphism `χ : a ⟶ b` lying over the identity. -/
private theorem exists_fiberHom_of_isHomLift {p : 𝒳 ⥤ 𝒞} (hp : p.IsFiberedInGroupoids)
    {U V : 𝒞} {f : V ⟶ U} {a b c : 𝒳} (ξ : a ⟶ c) (ξ' : b ⟶ c) [p.IsHomLift f ξ]
    [p.IsHomLift f ξ'] : ∃ χ : a ⟶ b, p.IsHomLift (𝟙 V) χ ∧ χ ≫ ξ' = ξ := by
  have h₁ : p.obj a = V := IsHomLift.domain_eq p f ξ
  have h₂ : p.obj b = V := IsHomLift.domain_eq p f ξ'
  obtain ⟨χ, ⟨hmap, hfac⟩, -⟩ := hp.unique_lift ξ' ξ (eqToHom (h₁.trans h₂.symm)) (by
    rw [IsHomLift.fac' p f ξ', IsHomLift.fac' p f ξ]; simp)
  exact ⟨χ, IsHomLift.of_fac' p (𝟙 V) χ h₁ h₂ (by simp [hmap]), hfac⟩

/-- `F` makes `𝒳` a *gerbe over* `𝒴`, where `q : 𝒴 ⥤ 𝒞` fibres `𝒴` over the
site `(𝒞, J)` and `F ⋙ q` fibres `𝒳` over it: both fibrations are fibred in groupoids, every
object of `𝒴` is locally in the image of `F`, and every morphism of a fibre of `q` between
`F`-images is locally the `F`-image of a morphism of a fibre of `F ⋙ q`. The last two
conditions are Stacks 06P1 (2)(a) and (2)(b).

The definition of Stacks 06P2, for stacks in groupoids `F ⋙ q` and `q`, is
`CategoryTheory.IsGerbeOverStackInGroupoids`, which adds those two hypotheses to this one. -/
structure IsGerbeOver (J : GrothendieckTopology 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) : Prop where
  /-- `𝒴` is fibred in groupoids over `𝒞`. -/
  base_isFiberedInGroupoids : q.IsFiberedInGroupoids
  /-- `𝒳` is fibred in groupoids over `𝒞`. -/
  isFiberedInGroupoids : (F ⋙ q).IsFiberedInGroupoids
  /-- Stacks 06P1 (2)(a): for `y` in `𝒴` over `U` there is a covering `S` of `U` such that
  along every `f : V ⟶ U` in `S` there is an object `x` of `𝒳` over `V` and a morphism
  `F.obj x ⟶ y` lying over `f`, that is, `F.obj x ≅ y|_V` in the fibre of `q` over `V`. -/
  locally_essSurj : ∀ {U : 𝒞} (y : 𝒴), q.obj y = U → ∃ S ∈ J U,
    ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), S f → ∃ (x : 𝒳) (ψ : F.obj x ⟶ y), q.IsHomLift f ψ
  /-- Stacks 06P1 (2)(b): for `x`, `x'` in `𝒳` over `U` and `b : F.obj x ⟶ F.obj x'` in the
  fibre of `q` over `U` there is a covering `S` of `U` such that along every `f : V ⟶ U` in
  `S` there are restrictions `ξ : x₁ ⟶ x` and `ξ' : x₁' ⟶ x'` of `x` and `x'` and a morphism
  `a : x₁ ⟶ x₁'` of the fibre of `F ⋙ q` over `V` with `F.map a = b|_V`, the last condition
  being the commuting square stated. -/
  locally_full : ∀ {U : 𝒞} {x x' : 𝒳} (b : F.obj x ⟶ F.obj x'), q.IsHomLift (𝟙 U) b →
    ∃ S ∈ J U, ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), S f →
      ∃ (x₁ x₁' : 𝒳) (ξ : x₁ ⟶ x) (ξ' : x₁' ⟶ x') (a : x₁ ⟶ x₁'),
        (F ⋙ q).IsHomLift f ξ ∧ (F ⋙ q).IsHomLift f ξ' ∧ (F ⋙ q).IsHomLift (𝟙 V) a ∧
          F.map a ≫ F.map ξ' = F.map ξ ≫ b

namespace IsGerbeOver

variable {J : GrothendieckTopology 𝒞} {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴}

/-- The local condition of Stacks 06P1 (2)(b) along a single `f : V ⟶ U`, restated with
`CategoryTheory.Functor.imageSieve`: a restriction `ξ : x₁ ⟶ x` of `x` along `f` admits a
fibre morphism to a restriction of `x'` whose `F`-image is `b|_V` exactly when `ξ` lies in
the image sieve of `b`. -/
lemma exists_fiberHom_iff_mem_imageSieve (hp : (F ⋙ q).IsFiberedInGroupoids) {U V : 𝒞}
    {f : V ⟶ U} {x x' x₁ : 𝒳} {b : F.obj x ⟶ F.obj x'} [q.IsHomLift (𝟙 U) b]
    (ξ : x₁ ⟶ x) [(F ⋙ q).IsHomLift f ξ] :
    (∃ (x₁' : 𝒳) (ξ' : x₁' ⟶ x') (a : x₁ ⟶ x₁'), (F ⋙ q).IsHomLift f ξ' ∧
        (F ⋙ q).IsHomLift (𝟙 V) a ∧ F.map a ≫ F.map ξ' = F.map ξ ≫ b) ↔
      F.imageSieve b ξ := by
  constructor
  · rintro ⟨x₁', ξ', a, -, -, hsq⟩
    exact ⟨a ≫ ξ', by rw [F.map_comp, hsq]⟩
  · rintro ⟨l, hl⟩
    obtain ⟨x₁', ξ', hξ'⟩ := hp.exists_lift f x' (IsHomLift.codomain_eq q (𝟙 U) b)
    have := hξ'
    have hFξ : q.IsHomLift f (F.map ξ) := (Functor.isHomLift_comp_iff F q f ξ).1 inferInstance
    have : q.IsHomLift f (F.map l) := by
      rw [hl]; simpa using IsHomLift.comp q f (𝟙 U) (F.map ξ) b
    have hl' : (F ⋙ q).IsHomLift f l := (Functor.isHomLift_comp_iff F q f l).2 inferInstance
    obtain ⟨a, ha, hafac⟩ := exists_fiberHom_of_isHomLift hp (f := f) l ξ'
    exact ⟨x₁', ξ', a, hξ', ha, by rw [← F.map_comp, hafac, hl]⟩

variable {r : 𝒵 ⥤ 𝒞} {G : 𝒴 ⥤ 𝒵}

/-- **Stacks 06R3**. If `𝒳` is a gerbe over `𝒴` and `𝒴` is a gerbe over `𝒵`, then `𝒳` is a
gerbe over `𝒵`.

This is also **Stacks 06R8**, the same statement for morphisms of algebraic stacks: the
source proves 06R8 by citing 06R3, and an algebraic stack is a category fibred in groupoids
over the big fppf site, so the two differ only in the generality of the ambient site. -/
@[stacks 06R3]
theorem comp (hF : IsGerbeOver J (G ⋙ r) F) (hG : IsGerbeOver J r G) :
    IsGerbeOver J r (F ⋙ G) where
  base_isFiberedInGroupoids := hG.base_isFiberedInGroupoids
  isFiberedInGroupoids := hF.isFiberedInGroupoids
  locally_essSurj := by
    intro U z hz
    obtain ⟨S₁, hS₁, h₁⟩ := hG.locally_essSurj z hz
    refine J.exists_covering_of_refine hS₁ ?_
    intro V f hf
    obtain ⟨y, ψ, hψ⟩ := h₁ f hf
    have := hψ
    obtain ⟨S₂, hS₂, h₂⟩ := hF.locally_essSurj y (IsHomLift.domain_eq r f ψ)
    refine ⟨S₂, hS₂, fun W g hg => ?_⟩
    obtain ⟨x, φ, hφ⟩ := h₂ g hg
    have : r.IsHomLift g (G.map φ) := (Functor.isHomLift_comp_iff G r g φ).1 hφ
    exact ⟨x, G.map φ ≫ ψ, IsHomLift.comp r g f (G.map φ) ψ⟩
  locally_full := by
    intro U x x' c hc
    have := hc
    obtain ⟨S₁, hS₁, h₁⟩ := hG.locally_full (x := F.obj x) (x' := F.obj x') c hc
    refine J.exists_covering_of_refine hS₁ ?_
    intro V f hf
    obtain ⟨y₁, y₁', η, η', β, hη, hη', hβ, hcomm⟩ := h₁ f hf
    have := hη; have := hη'; have := hβ
    -- Restrictions of `x` and `x'` along `f`, in `𝒳`.
    have hxU : r.obj ((F ⋙ G).obj x) = U := IsHomLift.domain_eq r (𝟙 U) c
    have hx'U : r.obj ((F ⋙ G).obj x') = U := IsHomLift.codomain_eq r (𝟙 U) c
    obtain ⟨x₁, ξ, hξ⟩ := hF.isFiberedInGroupoids.exists_lift f x hxU
    obtain ⟨x₁', ξ', hξ'⟩ := hF.isFiberedInGroupoids.exists_lift f x' hx'U
    have := hξ; have := hξ'
    have hFξ : (G ⋙ r).IsHomLift f (F.map ξ) := (Functor.isHomLift_comp_iff F (G ⋙ r) f ξ).1 hξ
    have hFξ' : (G ⋙ r).IsHomLift f (F.map ξ') :=
      (Functor.isHomLift_comp_iff F (G ⋙ r) f ξ').1 hξ'
    obtain ⟨χ, hχ, hχfac⟩ := exists_fiberHom_of_isHomLift hF.base_isFiberedInGroupoids
      (f := f) (F.map ξ) η
    obtain ⟨χ', hχ', hχ'fac⟩ := exists_fiberHom_of_isHomLift hF.base_isFiberedInGroupoids
      (f := f) η' (F.map ξ')
    obtain ⟨S₂, hS₂, h₂⟩ :=
      hF.locally_full (U := V) (x := x₁) (x' := x₁') (χ ≫ β ≫ χ') inferInstance
    refine ⟨S₂, hS₂, fun W g hg => ?_⟩
    obtain ⟨x₂, x₂', ζ, ζ', a, hζ, hζ', ha, heq⟩ := h₂ g hg
    have := hζ; have := hζ'
    refine ⟨x₂, x₂', ζ ≫ ξ, ζ' ≫ ξ', a, IsHomLift.comp (F ⋙ G ⋙ r) g f ζ ξ,
      IsHomLift.comp (F ⋙ G ⋙ r) g f ζ' ξ', ha, ?_⟩
    have e1 : G.map (F.map ξ) = G.map χ ≫ G.map η := by rw [← G.map_comp, hχfac]
    have e2 : G.map χ' ≫ G.map (F.map ξ') = G.map η' := by rw [← G.map_comp, hχ'fac]
    have e3 : G.map (F.map a) ≫ G.map (F.map ζ')
        = G.map (F.map ζ) ≫ G.map χ ≫ G.map β ≫ G.map χ' := by
      rw [← G.map_comp, heq]; simp
    simp only [Functor.comp_map, Functor.map_comp, ← Category.assoc]
    rw [e3]
    simp [Category.assoc, e2, hcomm, e1]

end IsGerbeOver

add_to_stacks 06R8 CategoryTheory.IsGerbeOver.comp

end CategoryTheory
