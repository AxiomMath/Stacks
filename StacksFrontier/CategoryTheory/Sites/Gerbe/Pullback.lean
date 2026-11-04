module

import StacksFrontier.CategoryTheory.FiberedInGroupoids.Factorization
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
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.EffectiveEpi.Comp

public import StacksFrontier.CategoryTheory.Sites.Gerbe.Basic
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-! # Base change of a gerbe

Let `q : 𝒴 ⥤ 𝒞` fibre `𝒴` over a site `(𝒞, J)`, let `F : 𝒳 ⥤ 𝒴` and `G : 𝒴' ⥤ 𝒴` be
1-morphisms over `𝒞` and let `𝒳' = 𝒴' ×_𝒴 𝒳` be the 2-fibre product of `G` and `F` in the
2-category of categories over `𝒞` (`CategoryTheory.TwoFibreProductOver`, Stacks 0040). Being
a gerbe transfers between the two sides of the square: `F` makes `𝒳` a gerbe over `𝒴` only
if the first projection makes `𝒳'` a gerbe over `𝒴'`, and conversely as soon as every object
of `𝒴` is locally in the image of `G`.

As in `StacksFrontier.CategoryTheory.Sites.Gerbe.Basic`, a category over `𝒞` presented by a
1-morphism is presented as a composite: `𝒳` sits over `𝒞` by `F ⋙ q` and `𝒴'` by `G ⋙ q`,
so that the compatibility of `F` and `G` with the structure functors holds by definition.

## Main results

* `CategoryTheory.TwoFibreProductOver.structureFunctor_isFiberedInGroupoids`: the 2-fibre
  product of categories fibred in groupoids over `𝒞` is fibred in groupoids over `𝒞`.
* `CategoryTheory.IsGerbeOver.twoFibreProduct`: **Stacks 06P3**.
* `CategoryTheory.IsGerbeOver.of_twoFibreProduct`: **Stacks 06P4**.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒴' : Type u₄} [Category.{v₄} 𝒴']
  {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} {G : 𝒴' ⥤ 𝒴}

namespace TwoFibreProductOver

/-- A morphism of the 2-fibre product lies over its own base component. -/
lemma isHomLift_hbase {P Q : TwoFibreProductOver (G ⋙ q) (F ⋙ q) q G F} (Φ : P ⟶ Q) :
    (structureFunctor (G ⋙ q) (F ⋙ q) q G F).IsHomLift Φ.hbase Φ :=
  IsHomLift.map (p := structureFunctor (G ⋙ q) (F ⋙ q) q G F) Φ

open Functor.IsFiberedInGroupoids.Factorization in
/-- The 2-fibre product `𝒴' ×_𝒴 𝒳` of categories fibred in groupoids over `𝒞` is again
fibred in groupoids over `𝒞`.

A base morphism is lifted by lifting it in each of `𝒴'` and `𝒳` and then producing the
comparison isomorphism of the lift from the universal property of `𝒴`, where the two lifts
`G ζ ≫ φ` and `F ξ` of it agree up to a unique vertical isomorphism; a fill-in is assembled
from the fill-ins in `𝒴'` and `𝒳`, its comparison square being forced by the same
uniqueness in `𝒴`. -/
lemma structureFunctor_isFiberedInGroupoids (hq : q.IsFiberedInGroupoids)
    (hF : (F ⋙ q).IsFiberedInGroupoids) (hG : (G ⋙ q).IsFiberedInGroupoids) :
    (structureFunctor (G ⋙ q) (F ⋙ q) q G F).IsFiberedInGroupoids := by
  constructor
  · intro V U g P hU
    have hU' : P.base = U := hU
    subst hU'
    obtain ⟨y₁, ζ, hζ⟩ := hG.exists_lift g P.x P.hx
    obtain ⟨x₁, ξ, hξ⟩ := hF.exists_lift g P.y P.hy
    have := hζ; have := hξ; have := P.vertical
    have hGζ : q.IsHomLift g (G.map ζ) := (Functor.isHomLift_comp_iff G q g ζ).1 hζ
    have hFξ : q.IsHomLift g (F.map ξ) := (Functor.isHomLift_comp_iff F q g ξ).1 hξ
    have hy₁ : q.obj (G.obj y₁) = V := IsHomLift.domain_eq (G ⋙ q) g ζ
    have hx₁ : q.obj (F.obj x₁) = V := IsHomLift.domain_eq (F ⋙ q) g ξ
    -- the two lifts `G ζ ≫ φ` and `F ξ` of `g` with target `F P.y` agree up to a
    -- unique vertical isomorphism
    have hcompat : eqToHom (hy₁.trans hx₁.symm) ≫ q.map (F.map ξ)
        = q.map (G.map ζ ≫ P.iso.hom) := by
      rw [q.map_comp, IsHomLift.fac' q g (F.map ξ), IsHomLift.fac' q g (G.map ζ),
        IsHomLift.fac' q (𝟙 P.base) P.iso.hom]
      simp
    obtain ⟨β, hβmap, hβcomp⟩ :=
      liftIsoData q hq (F.map ξ) (G.map ζ ≫ P.iso.hom) (hy₁.trans hx₁.symm) hcompat
    let Q : TwoFibreProductOver (G ⋙ q) (F ⋙ q) q G F :=
      { base := V, x := y₁, y := x₁, hx := hy₁, hy := hx₁, iso := β
        vertical := IsHomLift.of_fac' q (𝟙 V) β.hom hy₁ hx₁ (by simp [hβmap]) }
    let Φ : Q ⟶ P := { hbase := g, a := ζ, b := ξ, ha := hζ, hb := hξ, w := hβcomp.symm }
    exact ⟨Q, Φ, isHomLift_hbase Φ⟩
  · intro P Q R Φ Ψ base hcomm
    -- give the base morphism its type in the form the fibres' structure functors see
    obtain ⟨base, rfl⟩ : ∃ b : R.base ⟶ Q.base, b = base := ⟨base, rfl⟩
    have hcomm' : base ≫ Φ.hbase = Ψ.hbase := hcomm
    have := Φ.ha; have := Φ.hb
    have := Q.vertical; have := R.vertical
    -- read the compatibility of the base morphisms into the two components of `Ψ`
    have hΨa : (G ⋙ q).IsHomLift (base ≫ Φ.hbase) Ψ.a := by rw [hcomm']; exact Ψ.ha
    have hΨb : (F ⋙ q).IsHomLift (base ≫ Φ.hbase) Ψ.b := by rw [hcomm']; exact Ψ.hb
    obtain ⟨k, ⟨hk₁, hk₂⟩, hkuniq⟩ := hG.unique_lift Φ.a Ψ.a
      (eqToHom R.hx ≫ base ≫ eqToHom Q.hx.symm) (by
        rw [IsHomLift.fac' (G ⋙ q) Φ.hbase Φ.a,
          IsHomLift.fac' (G ⋙ q) (base ≫ Φ.hbase) Ψ.a]
        simp)
    obtain ⟨l, ⟨hl₁, hl₂⟩, hluniq⟩ := hF.unique_lift Φ.b Ψ.b
      (eqToHom R.hy ≫ base ≫ eqToHom Q.hy.symm) (by
        rw [IsHomLift.fac' (F ⋙ q) Φ.hbase Φ.b,
          IsHomLift.fac' (F ⋙ q) (base ≫ Φ.hbase) Ψ.b]
        simp)
    have hk₁' : q.map (G.map k) = eqToHom R.hx ≫ base ≫ eqToHom Q.hx.symm := hk₁
    have hl₁' : q.map (F.map l) = eqToHom R.hy ≫ base ≫ eqToHom Q.hy.symm := hl₁
    -- the comparison square of the fill-in is forced by uniqueness in `𝒴`
    have e₁ : (G.map k ≫ Q.iso.hom) ≫ F.map Φ.b = R.iso.hom ≫ F.map Ψ.b := by
      rw [Category.assoc, ← Φ.w, ← Category.assoc, ← G.map_comp, hk₂, Ψ.w]
    have e₂ : (R.iso.hom ≫ F.map l) ≫ F.map Φ.b = R.iso.hom ≫ F.map Ψ.b := by
      rw [Category.assoc, ← F.map_comp, hl₂]
    have e₃ : q.map (R.iso.hom ≫ F.map l) = q.map (G.map k ≫ Q.iso.hom) := by
      rw [q.map_comp, q.map_comp, hk₁', hl₁', IsHomLift.fac' q (𝟙 R.base) R.iso.hom,
        IsHomLift.fac' q (𝟙 Q.base) Q.iso.hom]
      simp
    obtain ⟨m, -, huniq⟩ := hq.unique_lift (F.map Φ.b) (R.iso.hom ≫ F.map Ψ.b)
      (q.map (G.map k ≫ Q.iso.hom)) (by rw [← q.map_comp, e₁])
    have hw : G.map k ≫ Q.iso.hom = R.iso.hom ≫ F.map l :=
      (huniq _ ⟨rfl, e₁⟩).trans (huniq _ ⟨e₃, e₂⟩).symm
    refine ⟨{ hbase := base, a := k, b := l
              ha := IsHomLift.of_fac' (G ⋙ q) base k R.hx Q.hx hk₁
              hb := IsHomLift.of_fac' (F ⋙ q) base l R.hy Q.hy hl₁
              w := hw }, ⟨rfl, Hom.ext' hk₂ hl₂⟩, ?_⟩
    rintro Χ ⟨hΧ₁, hΧ₂⟩
    have hΧbase : Χ.hbase = base := hΧ₁
    have hΧa : (G ⋙ q).IsHomLift base Χ.a := by rw [← hΧbase]; exact Χ.ha
    have hΧb : (F ⋙ q).IsHomLift base Χ.b := by rw [← hΧbase]; exact Χ.hb
    refine Hom.ext' (hkuniq Χ.a ⟨?_, congrArg Hom.a hΧ₂⟩) (hluniq Χ.b ⟨?_, congrArg Hom.b hΧ₂⟩)
    · rw [IsHomLift.fac' (G ⋙ q) base Χ.a]
    · rw [IsHomLift.fac' (F ⋙ q) base Χ.b]


/-- The two components of a morphism of the 2-fibre product lie over the same morphism of
`𝒞`: if the first one lies over `f`, so does the second. -/
lemma isHomLift_b_of_isHomLift_a {P Q : TwoFibreProductOver (G ⋙ q) (F ⋙ q) q G F}
    (Φ : P ⟶ Q) {V U : 𝒞}
    (f : V ⟶ U) (h : (G ⋙ q).IsHomLift f Φ.a) : (F ⋙ q).IsHomLift f Φ.b := by
  have := h; have := Φ.ha; have := Φ.hb
  have hd : (G ⋙ q).obj P.x = V := IsHomLift.domain_eq (G ⋙ q) f Φ.a
  have hc : (G ⋙ q).obj Q.x = U := IsHomLift.codomain_eq (G ⋙ q) f Φ.a
  have hbase : Φ.hbase = eqToHom P.hx.symm ≫ eqToHom hd ≫ f ≫ eqToHom hc.symm ≫ eqToHom Q.hx := by
    have h₂ := IsHomLift.fac' (G ⋙ q) f Φ.a
    rw [IsHomLift.fac' (G ⋙ q) Φ.hbase Φ.a] at h₂
    simpa using congrArg (fun t => eqToHom P.hx.symm ≫ t ≫ eqToHom Q.hx) h₂
  have hb := Φ.hb
  rw [hbase] at hb
  rwa [show eqToHom P.hx.symm ≫ eqToHom hd ≫ f ≫ eqToHom hc.symm ≫ eqToHom Q.hx
      = eqToHom (P.hx.symm.trans hd) ≫ f ≫ eqToHom (hc.symm.trans Q.hx) by simp,
    IsHomLift.lift_eqToHom_comp_iff, IsHomLift.lift_comp_eqToHom_iff] at hb


open Functor.IsFiberedInGroupoids.Factorization in
/-- The local fullness of Stacks 06P1 (2)(b) for the first projection of the 2-fibre product,
which is the substance of Stacks 06P3: a morphism `b'` of a fibre of `𝒴'` between the first
components of two objects of `𝒳'` is, locally on the base, the first component of a morphism
of a fibre of `𝒳'` between restrictions of those two objects.

Its second component is a morphism of `𝒳` between restrictions matching the `G`-image of
`b'`, which is what `F` being a gerbe over `𝒴` provides, and its comparison square is forced
by the uniqueness of fill-ins in `𝒴`. -/
lemma exists_locally_full {J : GrothendieckTopology 𝒞} (hF : IsGerbeOver J q F)
    (hG : (G ⋙ q).IsFiberedInGroupoids) {U : 𝒞}
    {P₁ P₂ : TwoFibreProductOver (G ⋙ q) (F ⋙ q) q G F} (b' : P₁.x ⟶ P₂.x)
    (hb' : (G ⋙ q).IsHomLift (𝟙 U) b') :
    ∃ S ∈ J U, ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), S f →
      ∃ (Q₁ Q₂ : TwoFibreProductOver (G ⋙ q) (F ⋙ q) q G F) (Ξ₁ : Q₁ ⟶ P₁)
        (Ξ₂ : Q₂ ⟶ P₂) (A : Q₁ ⟶ Q₂),
        (fst (G ⋙ q) (F ⋙ q) q G F ⋙ G ⋙ q).IsHomLift f Ξ₁ ∧
          (fst (G ⋙ q) (F ⋙ q) q G F ⋙ G ⋙ q).IsHomLift f Ξ₂ ∧
          (fst (G ⋙ q) (F ⋙ q) q G F ⋙ G ⋙ q).IsHomLift (𝟙 V) A ∧
          A.a ≫ Ξ₂.a = Ξ₁.a ≫ b' := by
  have hq := hF.base_isFiberedInGroupoids
  have := hb'; have := P₁.vertical; have := P₂.vertical
  have h₁ : (G ⋙ q).obj P₁.x = U := IsHomLift.domain_eq (G ⋙ q) (𝟙 U) b'
  have h₂ : (G ⋙ q).obj P₂.x = U := IsHomLift.codomain_eq (G ⋙ q) (𝟙 U) b'
  have hU₁ : P₁.base = U := P₁.hx.symm.trans h₁
  have hU₂ : P₂.base = U := P₂.hx.symm.trans h₂
  have hv₁ : q.IsHomLift (𝟙 U) P₁.iso.inv := by rw [← hU₁]; infer_instance
  have hv₂ : q.IsHomLift (𝟙 U) P₂.iso.hom := by rw [← hU₂]; infer_instance
  have hGb' : q.IsHomLift (𝟙 U) (G.map b') := (Functor.isHomLift_comp_iff G q (𝟙 U) b').1 hb'
  obtain ⟨S, hS, hcov⟩ := hF.locally_full (U := U) (x := P₁.y) (x' := P₂.y)
    (P₁.iso.inv ≫ G.map b' ≫ P₂.iso.hom) inferInstance
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨x₁, x₂, ξ₁, ξ₂, α, hξ₁, hξ₂, hα, heq⟩ := hcov f hf
  obtain ⟨y₁, ζ₁, hζ₁⟩ := hG.exists_lift f P₁.x (P₁.hx.trans hU₁)
  obtain ⟨y₂, ζ₂, hζ₂⟩ := hG.exists_lift f P₂.x (P₂.hx.trans hU₂)
  have := hξ₁; have := hξ₂; have := hα; have := hζ₁; have := hζ₂
  have hFξ₁ : q.IsHomLift f (F.map ξ₁) := (Functor.isHomLift_comp_iff F q f ξ₁).1 hξ₁
  have hFξ₂ : q.IsHomLift f (F.map ξ₂) := (Functor.isHomLift_comp_iff F q f ξ₂).1 hξ₂
  have hFα : q.IsHomLift (𝟙 V) (F.map α) := (Functor.isHomLift_comp_iff F q (𝟙 V) α).1 hα
  have hGζ₁ : q.IsHomLift f (G.map ζ₁) := (Functor.isHomLift_comp_iff G q f ζ₁).1 hζ₁
  have hGζ₂ : q.IsHomLift f (G.map ζ₂) := (Functor.isHomLift_comp_iff G q f ζ₂).1 hζ₂
  have hy₁ : q.obj (G.obj y₁) = V := IsHomLift.domain_eq (G ⋙ q) f ζ₁
  have hy₂ : q.obj (G.obj y₂) = V := IsHomLift.domain_eq (G ⋙ q) f ζ₂
  have hx₁ : q.obj (F.obj x₁) = V := IsHomLift.domain_eq (F ⋙ q) f ξ₁
  have hx₂ : q.obj (F.obj x₂) = V := IsHomLift.domain_eq (F ⋙ q) f ξ₂
  -- the comparison isomorphisms of the two restrictions, in `𝒳'`
  obtain ⟨β₁, hβ₁map, hβ₁comp⟩ :=
    liftIsoData q hq (F.map ξ₁) (G.map ζ₁ ≫ P₁.iso.hom) (hy₁.trans hx₁.symm) (by
      rw [q.map_comp, IsHomLift.fac' q f (F.map ξ₁), IsHomLift.fac' q f (G.map ζ₁),
        IsHomLift.fac' q (𝟙 P₁.base) P₁.iso.hom]
      simp)
  obtain ⟨β₂, hβ₂map, hβ₂comp⟩ :=
    liftIsoData q hq (F.map ξ₂) (G.map ζ₂ ≫ P₂.iso.hom) (hy₂.trans hx₂.symm) (by
      rw [q.map_comp, IsHomLift.fac' q f (F.map ξ₂), IsHomLift.fac' q f (G.map ζ₂),
        IsHomLift.fac' q (𝟙 P₂.base) P₂.iso.hom]
      simp)
  -- the restriction of `b'` to `V`, from the uniqueness of fill-ins in `𝒴'`
  obtain ⟨b₁, ⟨hb₁, hb₂⟩, -⟩ := hG.unique_lift ζ₂ (ζ₁ ≫ b')
    (eqToHom hy₁ ≫ eqToHom hy₂.symm) (by
      rw [Functor.map_comp, IsHomLift.fac' (G ⋙ q) f ζ₂, IsHomLift.fac' (G ⋙ q) f ζ₁,
        IsHomLift.fac' (G ⋙ q) (𝟙 U) b']
      simp)
  have hb₁' : q.map (G.map b₁) = eqToHom hy₁ ≫ eqToHom hy₂.symm := hb₁
  -- the comparison square of the morphism of `𝒳'` over `𝟙 V`
  have c₁ : (G.map b₁ ≫ β₂.hom) ≫ F.map ξ₂ = G.map ζ₁ ≫ G.map b' ≫ P₂.iso.hom := by
    rw [Category.assoc, hβ₂comp, ← Category.assoc, ← G.map_comp, hb₂, G.map_comp,
      Category.assoc]
  have c₂ : (β₁.hom ≫ F.map α) ≫ F.map ξ₂ = G.map ζ₁ ≫ G.map b' ≫ P₂.iso.hom := by
    rw [Category.assoc, heq, ← Category.assoc, hβ₁comp]; simp
  have c₃ : q.map (β₁.hom ≫ F.map α) = q.map (G.map b₁ ≫ β₂.hom) := by
    rw [q.map_comp, q.map_comp, hβ₁map, hβ₂map, hb₁', IsHomLift.fac' q (𝟙 V) (F.map α)]
    simp
  obtain ⟨m, -, huniq⟩ := hq.unique_lift (F.map ξ₂) (G.map ζ₁ ≫ G.map b' ≫ P₂.iso.hom)
    (q.map (G.map b₁ ≫ β₂.hom)) (by rw [← q.map_comp, c₁])
  have hw : G.map b₁ ≫ β₂.hom = β₁.hom ≫ F.map α :=
    (huniq _ ⟨rfl, c₁⟩).trans (huniq _ ⟨c₃, c₂⟩).symm
  let Q₁ : TwoFibreProductOver (G ⋙ q) (F ⋙ q) q G F :=
    { base := V, x := y₁, y := x₁, hx := hy₁, hy := hx₁, iso := β₁
      vertical := IsHomLift.of_fac' q (𝟙 V) β₁.hom hy₁ hx₁ (by simp [hβ₁map]) }
  let Q₂ : TwoFibreProductOver (G ⋙ q) (F ⋙ q) q G F :=
    { base := V, x := y₂, y := x₂, hx := hy₂, hy := hx₂, iso := β₂
      vertical := IsHomLift.of_fac' q (𝟙 V) β₂.hom hy₂ hx₂ (by simp [hβ₂map]) }
  let Ξ₁ : Q₁ ⟶ P₁ := { hbase := f ≫ eqToHom hU₁.symm, a := ζ₁, b := ξ₁
                        ha := inferInstance, hb := inferInstance, w := hβ₁comp.symm }
  let Ξ₂ : Q₂ ⟶ P₂ := { hbase := f ≫ eqToHom hU₂.symm, a := ζ₂, b := ξ₂
                        ha := inferInstance, hb := inferInstance, w := hβ₂comp.symm }
  let A : Q₁ ⟶ Q₂ := { hbase := 𝟙 V, a := b₁, b := α
                       ha := IsHomLift.of_fac' (G ⋙ q) (𝟙 V) b₁ hy₁ hy₂ (by simpa using hb₁)
                       hb := hα, w := hw }
  exact ⟨Q₁, Q₂, Ξ₁, Ξ₂, A,
    (Functor.isHomLift_comp_iff (fst (G ⋙ q) (F ⋙ q) q G F) (G ⋙ q) f Ξ₁).2 hζ₁,
    (Functor.isHomLift_comp_iff (fst (G ⋙ q) (F ⋙ q) q G F) (G ⋙ q) f Ξ₂).2 hζ₂,
    (Functor.isHomLift_comp_iff (fst (G ⋙ q) (F ⋙ q) q G F) (G ⋙ q) (𝟙 V) A).2
      (IsHomLift.of_fac' (G ⋙ q) (𝟙 V) b₁ hy₁ hy₂ (by simpa using hb₁)), hb₂⟩

end TwoFibreProductOver

open Functor.IsFiberedInGroupoids.Factorization TwoFibreProductOver in
/-- **Stacks 06P3**. Let `𝒳' = 𝒴' ×_𝒴 𝒳` be the 2-fibre product over `𝒞` of `G : 𝒴' ⥤ 𝒴`
and `F : 𝒳 ⥤ 𝒴`, where `𝒳` sits over `𝒞` by `F ⋙ q` and `𝒴'` by `G ⋙ q`. If `F` makes `𝒳`
a gerbe over `𝒴` and `𝒴'` is fibred in groupoids over `𝒞`, then the first projection makes
`𝒳'` a gerbe over `𝒴'`.

Both local conditions are pulled back along `G`: an object of `𝒳` over a member of a covering
whose `F`-image is a restriction of `G y'` is the second component of an object of `𝒳'` over
that member whose first component is a restriction of `y'`, and a morphism of `𝒳` matching
the `G`-image of `b'` is the second component of a morphism of `𝒳'` whose first component is
the restriction of `b'`. -/
@[stacks 06P3]
theorem IsGerbeOver.twoFibreProduct {J : GrothendieckTopology 𝒞} (hF : IsGerbeOver J q F)
    (hG : (G ⋙ q).IsFiberedInGroupoids) :
    IsGerbeOver J (G ⋙ q) (fst (G ⋙ q) (F ⋙ q) q G F) where
  base_isFiberedInGroupoids := hG
  isFiberedInGroupoids := by
    rw [fst_comp_eq]
    exact structureFunctor_isFiberedInGroupoids hF.base_isFiberedInGroupoids
      hF.isFiberedInGroupoids hG
  locally_essSurj := by
    intro U y' hy'
    obtain ⟨S, hS, hcov⟩ := hF.locally_essSurj (G.obj y') hy'
    refine ⟨S, hS, fun V f hf => ?_⟩
    obtain ⟨x, ψ, hψ⟩ := hcov f hf
    obtain ⟨y₁, ζ, hζ⟩ := hG.exists_lift f y' hy'
    have := hψ; have := hζ
    have hGζ : q.IsHomLift f (G.map ζ) := (Functor.isHomLift_comp_iff G q f ζ).1 hζ
    have hy₁ : q.obj (G.obj y₁) = V := IsHomLift.domain_eq (G ⋙ q) f ζ
    have hx : q.obj (F.obj x) = V := IsHomLift.domain_eq q f ψ
    obtain ⟨β, hβmap, hβcomp⟩ :=
      liftIsoData q hF.base_isFiberedInGroupoids ψ (G.map ζ) (hy₁.trans hx.symm) (by
        rw [IsHomLift.fac' q f ψ, IsHomLift.fac' q f (G.map ζ)]; simp)
    exact ⟨{ base := V, x := y₁, y := x, hx := hy₁, hy := hx, iso := β
             vertical := IsHomLift.of_fac' q (𝟙 V) β.hom hy₁ hx (by simp [hβmap]) },
           ζ, hζ⟩
  locally_full := fun b' hb' => TwoFibreProductOver.exists_locally_full hF hG b' hb'

open Functor.IsFiberedInGroupoids.Factorization TwoFibreProductOver in
/-- **Stacks 06P4**. Let `𝒳' = 𝒴' ×_𝒴 𝒳` be the 2-fibre product over `𝒞` of `G : 𝒴' ⥤ 𝒴`
and `F : 𝒳 ⥤ 𝒴`. If every object of `𝒴` is locally in the image of `G` — the condition
`CategoryTheory.IsGerbeOver.locally_essSurj` for `G` — and the first projection makes `𝒳'` a
gerbe over `𝒴'`, then `F` makes `𝒳` a gerbe over `𝒴`.

This is the converse direction of Stacks 06P3: the two local conditions are descended along
`G`. For the first, an object `y'` of `𝒴'` whose `G`-image restricts `y` is refined by a
covering along which `𝒳'` has objects over `y'`, and their second components are objects of
`𝒳` whose `F`-images restrict `y`. For the second, two restrictions of `x₁` and `x₂` and the
comparison isomorphisms `G y' ≅ F x₁|_V`, `G y' ≅ F x₂|_V` obtained from `b` assemble into two
objects of `𝒳'` with the *same* first component `y'`, so that the identity of `y'` is a
morphism of a fibre between their images; local fullness of the first projection then supplies
the morphism of `𝒳` wanted. -/
@[stacks 06P4]
theorem IsGerbeOver.of_twoFibreProduct {J : GrothendieckTopology 𝒞} (hq : q.IsFiberedInGroupoids)
    (hFq : (F ⋙ q).IsFiberedInGroupoids)
    (hGsurj : ∀ {U : 𝒞} (y : 𝒴), q.obj y = U → ∃ S ∈ J U,
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), S f → ∃ (y' : 𝒴') (ψ : G.obj y' ⟶ y), q.IsHomLift f ψ)
    (h : IsGerbeOver J (G ⋙ q) (fst (G ⋙ q) (F ⋙ q) q G F)) :
    IsGerbeOver J q F where
  base_isFiberedInGroupoids := hq
  isFiberedInGroupoids := hFq
  locally_essSurj := by
    intro U y hy
    obtain ⟨S₁, hS₁, h₁⟩ := hGsurj y hy
    refine J.exists_covering_of_refine hS₁ fun V f hf => ?_
    obtain ⟨y', ψ, hψ⟩ := h₁ f hf
    have := hψ
    obtain ⟨S₂, hS₂, h₂⟩ := h.locally_essSurj y' (IsHomLift.domain_eq q f ψ)
    refine ⟨S₂, hS₂, fun W g hg => ?_⟩
    obtain ⟨P, χ, hχ⟩ := h₂ g hg
    have := hχ; have := P.vertical
    have hGχ : q.IsHomLift g (G.map χ) := (Functor.isHomLift_comp_iff G q g χ).1 hχ
    have hd := IsHomLift.domain_eq (G ⋙ q) g χ
    have hW : P.base = W := P.hx.symm.trans hd
    have hvert : q.IsHomLift (𝟙 W) P.iso.inv := by rw [← hW]; infer_instance
    have hcomp : q.IsHomLift (g ≫ f) (G.map χ ≫ ψ : G.obj P.x ⟶ y) :=
      IsHomLift.comp q g f (G.map χ) ψ
    refine ⟨P.y, P.iso.inv ≫ G.map χ ≫ ψ, ?_⟩
    simpa using IsHomLift.comp q (𝟙 W) (g ≫ f) P.iso.inv (G.map χ ≫ ψ)
  locally_full := by
    intro U x₁ x₂ b hb
    have := hb
    have hx₁U : (F ⋙ q).obj x₁ = U := IsHomLift.domain_eq q (𝟙 U) b
    have hx₂U : (F ⋙ q).obj x₂ = U := IsHomLift.codomain_eq q (𝟙 U) b
    obtain ⟨S₁, hS₁, h₁⟩ := hGsurj (F.obj x₁) hx₁U
    refine J.exists_covering_of_refine hS₁ fun V f hf => ?_
    obtain ⟨y', α, hα⟩ := h₁ f hf
    obtain ⟨z₁, ξ₁, hξ₁⟩ := hFq.exists_lift f x₁ hx₁U
    obtain ⟨z₂, ξ₂, hξ₂⟩ := hFq.exists_lift f x₂ hx₂U
    have := hα; have := hξ₁; have := hξ₂
    have hFξ₁ : q.IsHomLift f (F.map ξ₁) := (Functor.isHomLift_comp_iff F q f ξ₁).1 hξ₁
    have hFξ₂ : q.IsHomLift f (F.map ξ₂) := (Functor.isHomLift_comp_iff F q f ξ₂).1 hξ₂
    have hy' : q.obj (G.obj y') = V := IsHomLift.domain_eq q f α
    have hz₁ : q.obj (F.obj z₁) = V := IsHomLift.domain_eq (F ⋙ q) f ξ₁
    have hz₂ : q.obj (F.obj z₂) = V := IsHomLift.domain_eq (F ⋙ q) f ξ₂
    have hαb : q.IsHomLift f (α ≫ b) := by simpa using IsHomLift.comp q f (𝟙 U) α b
    -- the two objects of `𝒳'` over `V` with common first component `y'`
    obtain ⟨δ₁, hδ₁map, hδ₁comp⟩ := liftIsoData q hq (F.map ξ₁) α (hy'.trans hz₁.symm) (by
      rw [IsHomLift.fac' q f (F.map ξ₁), IsHomLift.fac' q f α]; simp)
    obtain ⟨δ₂, hδ₂map, hδ₂comp⟩ := liftIsoData q hq (F.map ξ₂) (α ≫ b) (hy'.trans hz₂.symm) (by
      rw [IsHomLift.fac' q f (F.map ξ₂), IsHomLift.fac' q f (α ≫ b)]; simp)
    let P₁ : TwoFibreProductOver (G ⋙ q) (F ⋙ q) q G F :=
      { base := V, x := y', y := z₁, hx := hy', hy := hz₁, iso := δ₁
        vertical := IsHomLift.of_fac' q (𝟙 V) δ₁.hom hy' hz₁ (by simp [hδ₁map]) }
    let P₂ : TwoFibreProductOver (G ⋙ q) (F ⋙ q) q G F :=
      { base := V, x := y', y := z₂, hx := hy', hy := hz₂, iso := δ₂
        vertical := IsHomLift.of_fac' q (𝟙 V) δ₂.hom hy' hz₂ (by simp [hδ₂map]) }
    obtain ⟨S₂, hS₂, h₂⟩ := h.locally_full (U := V) (x := P₁) (x' := P₂) (𝟙 y')
      (IsHomLift.id hy')
    refine ⟨S₂, hS₂, fun W g hg => ?_⟩
    obtain ⟨Q₁, Q₂, Ξ₁, Ξ₂, A, hΞ₁, hΞ₂, hA, hcomm⟩ := h₂ g hg
    have hΞ₁a : (G ⋙ q).IsHomLift g Ξ₁.a :=
      (Functor.isHomLift_comp_iff (fst (G ⋙ q) (F ⋙ q) q G F) (G ⋙ q) g Ξ₁).1 hΞ₁
    have hΞ₂a : (G ⋙ q).IsHomLift g Ξ₂.a :=
      (Functor.isHomLift_comp_iff (fst (G ⋙ q) (F ⋙ q) q G F) (G ⋙ q) g Ξ₂).1 hΞ₂
    have hAa : (G ⋙ q).IsHomLift (𝟙 W) A.a :=
      (Functor.isHomLift_comp_iff (fst (G ⋙ q) (F ⋙ q) q G F) (G ⋙ q) (𝟙 W) A).1 hA
    have hΞ₁b := isHomLift_b_of_isHomLift_a Ξ₁ g hΞ₁a
    have hΞ₂b := isHomLift_b_of_isHomLift_a Ξ₂ g hΞ₂a
    have hAb := isHomLift_b_of_isHomLift_a A (𝟙 W) hAa
    refine ⟨Q₁.y, Q₂.y, Ξ₁.b ≫ ξ₁, Ξ₂.b ≫ ξ₂, A.b,
      IsHomLift.comp (F ⋙ q) g f Ξ₁.b ξ₁, IsHomLift.comp (F ⋙ q) g f Ξ₂.b ξ₂, hAb, ?_⟩
    have hcomm' : A.a ≫ Ξ₂.a = Ξ₁.a := hcomm.trans (Category.comp_id Ξ₁.a)
    have hP₁iso : P₁.iso.hom ≫ F.map ξ₁ = α := hδ₁comp
    have hP₂iso : P₂.iso.hom ≫ F.map ξ₂ = α ≫ b := hδ₂comp
    rw [← cancel_epi Q₁.iso.hom]
    simp only [F.map_comp, Category.assoc]
    rw [← A.w_assoc, ← Ξ₂.w_assoc, hP₂iso, ← Category.assoc, ← G.map_comp, hcomm', ← hP₁iso]
    simp only [Category.assoc]
    rw [Ξ₁.w_assoc]

end CategoryTheory
