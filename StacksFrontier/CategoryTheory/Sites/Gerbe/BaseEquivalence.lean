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

public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence

/-! # Being a gerbe over a base is invariant under equivalence over the site

Stacks 06P0 says that two categories over a site are gerbes at the same time when they are
equivalent as categories over that site, and `CategoryTheory.isGerbeOver_iff_of_isEquivalenceOver`
in `StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence` proves it in the relative form, over an
arbitrary base `q : 𝒴 ⥤ 𝒞` — but with the comparison functor `a` assumed to be an equivalence
*over `𝒴`*, that is with unit and counit `F'`-vertical.

That hypothesis is too strong for the use Stacks 06P1 makes of it. The factorization
`F = F' ∘ a` that Stacks 06N7 produces has `a` an equivalence over `𝒞` only: the counit of the
concrete factorization through `𝒳 ×_{F, 𝒴, id} 𝒴` is, at an object `(x, y, φ : F x ≅ y)`, the
comparison `φ` itself, whose `F'`-image is `φ` and not an identity. So this file reproves the
relative Stacks 06P0 with `a` an equivalence over `𝒞`,
`CategoryTheory.Functor.IsEquivalenceOver (F ⋙ q) (F' ⋙ q) a`, which is what the source's
clause 06P1 (1) quantifies over and what 06N7 delivers.

## Main results

* `CategoryTheory.IsGerbeOver.of_isEquivalenceOver_base` and
  `CategoryTheory.IsGerbeOver.of_isEquivalenceOver_base_symm`, the two directions;
* `CategoryTheory.isGerbeOver_iff_of_isEquivalenceOver_base`, the biconditional.

## Implementation notes

The counit is used only where a *`𝒞`-vertical* comparison suffices: to move an object of `𝒳'`
to `a`-image of an object of `𝒳` up to a vertical isomorphism of `𝒴`. Its `F'`-image is then an
honest, generally non-identity morphism of `𝒴` lying over an identity of `𝒞`, and it is carried
along explicitly through the two local conditions; being an isomorphism is all that is asked of
it, so no triangle identity between unit and counit — which
`CategoryTheory.Functor.IsEquivalenceOver` does not carry — is needed.

The second direction never uses the unit. Instead of transporting the restrictions supplied for
`F'` back along the quasi-inverse, it takes restrictions in `𝒳` directly, which
`(F ⋙ q).IsFiberedInGroupoids` provides, and compares their `a`-images with the given ones by the
uniqueness of fill-ins for `F' ⋙ q`; the morphism between them is then pulled back through `a`,
using that `a` is full. This is what avoids the incoherence of the raw unit/counit data: the two
comparison isomorphisms cancel against each other in the commuting square, so nothing has to be
known about how the unit and the counit interact.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {𝒞 : Type u₁} {𝒳 : Type u₂} {𝒳' : Type u₃} {𝒴 : Type u₄}
  [Category.{v₁} 𝒞] [Category.{v₂} 𝒳] [Category.{v₃} 𝒳'] [Category.{v₄} 𝒴]
  {J : GrothendieckTopology 𝒞} {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} {F' : 𝒳' ⥤ 𝒴} {a : 𝒳 ⥤ 𝒳'}

namespace IsGerbeOver

/-- The counit of an equivalence over `𝒞` is `F' ⋙ q`-vertical at any object of `𝒳'` lying over
`U`. -/
private theorem isHomLift_counit_hom_id (e : Functor.IsEquivalenceOver (F ⋙ q) (F' ⋙ q) a)
    {U : 𝒞} {u : 𝒳'} (hu : (F' ⋙ q).obj u = U) :
    (F' ⋙ q).IsHomLift (𝟙 U) (e.counitIso.hom.app u) := by
  have h0 := e.counit_vertical u
  have hX : (F' ⋙ q).obj ((e.inv ⋙ a).obj u) = U :=
    (IsHomLift.codomain_eq (F' ⋙ q)
      (𝟙 ((F' ⋙ q).obj ((e.inv ⋙ a).obj u))) (e.counitIso.hom.app u)).symm.trans hu
  rwa [hX] at h0

/-- The relative Stacks 06P0, forward direction, with `a` assumed an equivalence over `𝒞` rather
than over `𝒴`: if `a : 𝒳 ⥤ 𝒳'` is a 1-morphism over `𝒴` (so `a ⋙ F' = F`) which is an
equivalence over `𝒞`, then `F` making `𝒳` a gerbe over `𝒴` forces `F'` to make `𝒳'` one.

Both local conditions transport along `a`, the second one after conjugating the given morphism of
a fibre of `q` by the `F'`-images of the counit at the two objects. Those images are isomorphisms
of `𝒴` lying over identities of `𝒞`, not identities, and they reappear in the two restrictions
produced, where they cancel in the commuting square. -/
theorem of_isEquivalenceOver_base (ha : a ⋙ F' = F)
    (e : Functor.IsEquivalenceOver (F ⋙ q) (F' ⋙ q) a) (h : IsGerbeOver J q F) :
    IsGerbeOver J q F' := by
  subst ha
  have hF'q : (F' ⋙ q).IsFiberedInGroupoids :=
    Functor.IsFiberedInGroupoids.of_isEquivalenceOver rfl e h.isFiberedInGroupoids
  refine ⟨h.base_isFiberedInGroupoids, hF'q, ?_, ?_⟩
  · intro U y hy
    obtain ⟨S, hS, hcov⟩ := h.locally_essSurj y hy
    exact ⟨S, hS, fun V f hf => by
      obtain ⟨x, ψ, hψ⟩ := hcov f hf
      exact ⟨a.obj x, ψ, hψ⟩⟩
  · intro U u u' b₀ hb₀
    have := hb₀
    have hU : (F' ⋙ q).obj u = U := IsHomLift.domain_eq q (𝟙 U) b₀
    have hU' : (F' ⋙ q).obj u' = U := IsHomLift.codomain_eq q (𝟙 U) b₀
    have hc := isHomLift_counit_hom_id e hU
    have hc' := isHomLift_counit_hom_id e hU'
    have hcinv' : (F' ⋙ q).IsHomLift (𝟙 U) (e.counitIso.inv.app u') :=
      @IsHomLift.lift_id_inv _ _ _ _ (F' ⋙ q) U _ _ (e.counitIso.app u') hc'
    have hcq : q.IsHomLift (𝟙 U) (F'.map (e.counitIso.hom.app u)) :=
      (Functor.isHomLift_comp_iff F' q (𝟙 U) (e.counitIso.hom.app u)).1 hc
    have hcqinv' : q.IsHomLift (𝟙 U) (F'.map (e.counitIso.inv.app u')) :=
      (Functor.isHomLift_comp_iff F' q (𝟙 U) (e.counitIso.inv.app u')).1 hcinv'
    have hb₁ : q.IsHomLift (𝟙 U) (F'.map (e.counitIso.hom.app u) ≫ b₀ ≫
        F'.map (e.counitIso.inv.app u')) := inferInstance
    obtain ⟨S, hS, hcov⟩ := h.locally_full (x := e.inv.obj u) (x' := e.inv.obj u')
      (F'.map (e.counitIso.hom.app u) ≫ b₀ ≫ F'.map (e.counitIso.inv.app u')) hb₁
    refine ⟨S, hS, fun V f hf => ?_⟩
    obtain ⟨z, z', ξ, ξ', α, hξ, hξ', hα, hsq⟩ := hcov f hf
    have haξ : (F' ⋙ q).IsHomLift f (a.map ξ) :=
      (Functor.isHomLift_comp_iff a (F' ⋙ q) f ξ).1 hξ
    have haξ' : (F' ⋙ q).IsHomLift f (a.map ξ') :=
      (Functor.isHomLift_comp_iff a (F' ⋙ q) f ξ').1 hξ'
    have haα : (F' ⋙ q).IsHomLift (𝟙 V) (a.map α) :=
      (Functor.isHomLift_comp_iff a (F' ⋙ q) (𝟙 V) α).1 hα
    have := haξ; have := haξ'; have := hc; have := hc'
    refine ⟨a.obj z, a.obj z', a.map ξ ≫ e.counitIso.hom.app u,
      a.map ξ' ≫ e.counitIso.hom.app u', a.map α, ?_, ?_, haα, ?_⟩
    · simpa using IsHomLift.comp (F' ⋙ q) f (𝟙 U) (a.map ξ) (e.counitIso.hom.app u)
    · simpa using IsHomLift.comp (F' ⋙ q) f (𝟙 U) (a.map ξ') (e.counitIso.hom.app u')
    · have hsq' : F'.map (a.map α) ≫ F'.map (a.map ξ') = F'.map (a.map ξ) ≫
          F'.map (e.counitIso.hom.app u) ≫ b₀ ≫ F'.map (e.counitIso.inv.app u') := hsq
      simp only [F'.map_comp, ← Category.assoc]
      rw [hsq']
      have hcancel :
          F'.map (e.counitIso.inv.app u') ≫ F'.map (e.counitIso.hom.app u') = 𝟙 (F'.obj u') := by
        calc
          _ = F'.map (e.counitIso.inv.app u' ≫ e.counitIso.hom.app u') :=
            (F'.map_comp _ _).symm
          _ = F'.map (𝟙 u') := congrArg F'.map (e.counitIso.inv_hom_id_app u')
          _ = 𝟙 (F'.obj u') := F'.map_id u'
      simp [Category.assoc, hcancel, Category.comp_id]

/-- The relative Stacks 06P0, reverse direction, with `a` assumed an equivalence over `𝒞`: if `F'`
makes `𝒳'` a gerbe over `𝒴` then so does `F` for `𝒳`.

Restrictions in `𝒳` are taken directly, by lifting the covering morphism for `F ⋙ q`; their
`a`-images are compared with the restrictions that `F'` supplies by the uniqueness of fill-ins for
`F' ⋙ q`, giving vertical isomorphisms `κ`, `κ'`. The morphism of the fibre wanted in `𝒳` is the
`a`-preimage of `κ ≫ γ ≫ κ'⁻¹`, which exists because `a` is full, and the commuting square holds
because `κ` and `κ'` cancel against the comparisons in the two restrictions. -/
theorem of_isEquivalenceOver_base_symm (ha : a ⋙ F' = F)
    (e : Functor.IsEquivalenceOver (F ⋙ q) (F' ⋙ q) a) (h' : IsGerbeOver J q F') :
    IsGerbeOver J q F := by
  subst ha
  have hae : a.IsEquivalence :=
    ((CategoryTheory.Equivalence.mk a e.inv e.unitIso.symm e.counitIso : 𝒳 ≌ 𝒳')
      ).isEquivalence_functor
  have hF'q : (F' ⋙ q).IsFiberedInGroupoids := h'.isFiberedInGroupoids
  have hFq : ((a ⋙ F') ⋙ q).IsFiberedInGroupoids :=
    Functor.IsFiberedInGroupoids.of_isEquivalenceOver e.inv_over
      (Functor.IsEquivalenceOver.symm e rfl) hF'q
  refine ⟨h'.base_isFiberedInGroupoids, hFq, ?_, ?_⟩
  · intro U y hy
    obtain ⟨S, hS, hcov⟩ := h'.locally_essSurj y hy
    refine ⟨S, hS, fun V f hf => ?_⟩
    obtain ⟨w, ψ, hψ⟩ := hcov f hf
    have := hψ
    have hV : (F' ⋙ q).obj w = V := IsHomLift.domain_eq q f ψ
    have hc := isHomLift_counit_hom_id e hV
    have hcq : q.IsHomLift (𝟙 V) (F'.map (e.counitIso.hom.app w)) :=
      (Functor.isHomLift_comp_iff F' q (𝟙 V) (e.counitIso.hom.app w)).1 hc
    exact ⟨e.inv.obj w, F'.map (e.counitIso.hom.app w) ≫ ψ, by
      simpa using IsHomLift.comp q (𝟙 V) f (F'.map (e.counitIso.hom.app w)) ψ⟩
  · intro U x x' b₀ hb₀
    have := hb₀
    obtain ⟨S, hS, hcov⟩ := h'.locally_full (x := a.obj x) (x' := a.obj x') b₀ hb₀
    refine ⟨S, hS, fun V f hf => ?_⟩
    obtain ⟨z, z', ζ, ζ', γ, hζ, hζ', hγ, hsq⟩ := hcov f hf
    have hxU : ((a ⋙ F') ⋙ q).obj x = U := IsHomLift.domain_eq q (𝟙 U) b₀
    have hx'U : ((a ⋙ F') ⋙ q).obj x' = U := IsHomLift.codomain_eq q (𝟙 U) b₀
    obtain ⟨w, ξ, hξ⟩ := hFq.exists_lift f x hxU
    obtain ⟨w', ξ', hξ'⟩ := hFq.exists_lift f x' hx'U
    have := hξ; have := hξ'; have := hζ; have := hζ'; have := hγ
    have haξ : (F' ⋙ q).IsHomLift f (a.map ξ) :=
      (Functor.isHomLift_comp_iff a (F' ⋙ q) f ξ).1 hξ
    have haξ' : (F' ⋙ q).IsHomLift f (a.map ξ') :=
      (Functor.isHomLift_comp_iff a (F' ⋙ q) f ξ').1 hξ'
    have h1 : (F' ⋙ q).obj (a.obj w) = V := IsHomLift.domain_eq (F' ⋙ q) f (a.map ξ)
    have h1' : (F' ⋙ q).obj (a.obj w') = V := IsHomLift.domain_eq (F' ⋙ q) f (a.map ξ')
    have h2 : (F' ⋙ q).obj z = V := IsHomLift.domain_eq (F' ⋙ q) f ζ
    have h2' : (F' ⋙ q).obj z' = V := IsHomLift.domain_eq (F' ⋙ q) f ζ'
    obtain ⟨κ, ⟨hκmap, hκfac⟩, -⟩ :=
      hF'q.unique_lift ζ (a.map ξ) (eqToHom (h1.trans h2.symm)) (by
        rw [IsHomLift.fac' (F' ⋙ q) f ζ, IsHomLift.fac' (F' ⋙ q) f (a.map ξ)]; simp)
    obtain ⟨κ', ⟨hκ'map, hκ'fac⟩, -⟩ :=
      hF'q.unique_lift ζ' (a.map ξ') (eqToHom (h1'.trans h2'.symm)) (by
        rw [IsHomLift.fac' (F' ⋙ q) f ζ', IsHomLift.fac' (F' ⋙ q) f (a.map ξ')]; simp)
    simp only [Functor.comp_map] at hκmap hκ'map
    have hκ : (F' ⋙ q).IsHomLift (𝟙 V) κ :=
      IsHomLift.of_fac' (F' ⋙ q) (𝟙 V) κ h1 h2 (by simp [hκmap])
    have hκ' : (F' ⋙ q).IsHomLift (𝟙 V) κ' :=
      IsHomLift.of_fac' (F' ⋙ q) (𝟙 V) κ' h1' h2' (by simp [hκ'map])
    have hisoκ' : IsIso κ' := Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id hF'q κ' hκ'
    have hκinv : (F' ⋙ q).IsHomLift (𝟙 V) (asIso κ').inv :=
      @IsHomLift.lift_id_inv _ _ _ _ (F' ⋙ q) V _ _ (asIso κ') hκ'
    have := hκ; have := hκinv
    have hA : (F' ⋙ q).IsHomLift (𝟙 V) (κ ≫ γ ≫ (asIso κ').inv) := inferInstance
    refine ⟨w, w', ξ, ξ', a.preimage (κ ≫ γ ≫ (asIso κ').inv), hξ, hξ',
      (Functor.isHomLift_comp_iff a (F' ⋙ q) (𝟙 V) _).2 (by rw [a.map_preimage]; exact hA), ?_⟩
    simp only [Functor.comp_map]
    rw [a.map_preimage, ← hκfac, ← hκ'fac]
    have hsq' : F'.map γ ≫ F'.map ζ' = F'.map ζ ≫ b₀ := hsq
    have key : (κ ≫ γ ≫ (asIso κ').inv) ≫ κ' ≫ ζ' = κ ≫ γ ≫ ζ' := by simp
    rw [← F'.map_comp, key]
    simp only [F'.map_comp, Category.assoc]
    rw [hsq']



end IsGerbeOver

/-- The relative Stacks 06P0 with `a` an equivalence over `𝒞`: `F` makes `𝒳` a gerbe over `𝒴`
exactly when `F'` makes `𝒳'` one. Unlike
`CategoryTheory.isGerbeOver_iff_of_isEquivalenceOver`, whose two directions are the one statement
applied to `a` and to its quasi-inverse, the two directions here are proved separately: the
quasi-inverse is a 1-morphism over `𝒞` but only a 1-morphism over `𝒴` up to the counit, so the
hypothesis is not symmetric in `a`. -/
theorem isGerbeOver_iff_of_isEquivalenceOver_base (ha : a ⋙ F' = F)
    (e : Functor.IsEquivalenceOver (F ⋙ q) (F' ⋙ q) a) :
    IsGerbeOver J q F ↔ IsGerbeOver J q F' :=
  ⟨IsGerbeOver.of_isEquivalenceOver_base ha e, IsGerbeOver.of_isEquivalenceOver_base_symm ha e⟩

end CategoryTheory
