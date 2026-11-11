module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PushforwardDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PushforwardMorSheaf

/-!
# The pushforward of a stack along a functor preserving all fibre products

Let `u : 𝒞 ⥤ 𝒟` be a continuous functor of sites and `p : 𝒮 ⥤ 𝒟` a category over `𝒟`. This file
proves that the pushforward `u^p𝒮 ⥤ 𝒞` of `StacksDraft.CategoryTheory.Sites.Stack.Functoriality`
is a stack over `𝒞` when `p` is a stack over `𝒟`, and a stack in groupoids when `p` is one, in the
special case where `𝒞` has all fibre products and `u` preserves them.

The three conditions of Stacks 026F are discharged in three different places: condition (1) is
Stacks 04WB, `CategoryTheory.StrictPullback.isFibered_structureFunctor`; condition (2) is
`CategoryTheory.StrictPullback.isMorSheaf_structureFunctor`; condition (3) is
`CategoryTheory.StrictPullback.hasEffectiveDescent_structureFunctor`.

Stacks 04WC and 04WD themselves, for a site in the sense of Stacks 00VH and a continuous functor
in the sense of Stacks 00WU, which ask for the fibre products of the members of a covering only
and for their preservation by `u` only, are
`CategoryTheory.StrictPullback.isStack_structureFunctor_toGrothendieck` and
`CategoryTheory.StrictPullback.isStack_isFiberedInGroupoids_structureFunctor_toGrothendieck`, in
`StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PushforwardStackCovering`.

## Main results

* `CategoryTheory.StrictPullback.isStack_structureFunctor`, the pushforward of a stack is a stack,
  over a base with all fibre products preserved by `u`;
* `CategoryTheory.StrictPullback.isFiberedInGroupoids_structureFunctor`, the fibres of `u^p𝒮` are
  groupoids as soon as those of `𝒮` are;
* `CategoryTheory.StrictPullback.isStack_isFiberedInGroupoids_structureFunctor`, the same for
  stacks in groupoids.

## Implementation notes

Mathlib's `Functor.IsContinuous` is the sheaf-theoretic condition, which gives that `u` sends
covering sieves to covering sieves (`CoverPreserving.of_isContinuous`) but not that it commutes
with fibre products. The commutation with fibre products is genuinely used — see
`CategoryTheory.StrictPullback.glue` — and is assumed here in the form `[HasPullbacks 𝒞]` and
`[PreservesLimitsOfShape WalkingCospan u]`, which is stronger than what Stacks 00WU asks.

"Stack in groupoids" is read here as the conjunction of `CategoryTheory.Functor.IsStack`
(Stacks 026F) and `CategoryTheory.Functor.IsFiberedInGroupoids` (Stacks 003S), which is how the
source words Stacks 02ZI (1) and how its proof of Stacks 04WD proceeds: "this follows immediately
from Lemma 04WC and the fact that all fibre categories are groupoids". The library's other
rendering `CategoryTheory.Functor.IsStackInGroupoids`, which spells the descent conditions out for
covering families with fibre-product overlaps, is not related to `Functor.IsStack` by any lemma, so
no statement about it can be deduced from Stacks 04WC.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮]

namespace StrictPullback

/-- The pushforward `u^p𝒮 ⥤ 𝒞` of a stack `p : 𝒮 ⥤ 𝒟` over `(𝒟, K)` is a stack over `(𝒞, J)`,
for a continuous functor `u : 𝒞 ⥤ 𝒟` from a category with all fibre products that preserves them.

This is a special case of Stacks 04WC, which is
`CategoryTheory.StrictPullback.isStack_structureFunctor_toGrothendieck`: Stacks 00VH and 00WU
ask for the fibre products of the members of a covering only, and for their preservation by `u`
only. -/
theorem isStack_structureFunctor (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟)
    (u : 𝒞 ⥤ 𝒟) [u.IsContinuous J K] [HasPullbacks 𝒞] [PreservesLimitsOfShape WalkingCospan u]
    (p : 𝒮 ⥤ 𝒟) (hp : Functor.IsStack p K) :
    Functor.IsStack (structureFunctor u p) J :=
  have := hp.isFibered
  { isFibered := inferInstance
    isMorSheaf := isMorSheaf_structureFunctor J K u p hp.isMorSheaf
    hasEffectiveDescent :=
      hasEffectiveDescent_structureFunctor J K u p hp.hasEffectiveDescent }

/-- The fibres of the pushforward `u^p𝒮` are groupoids as soon as the fibres of `𝒮` are: an object
of `u^p𝒮` over `U` is an object of `𝒮` over `u U`, and a morphism of `u^p𝒮` is determined by its
`𝒞`-component together with its `𝒮`-component. No topology and no continuity is involved. -/
theorem isFiberedInGroupoids_structureFunctor (u : 𝒞 ⥤ 𝒟) (p : 𝒮 ⥤ 𝒟)
    (hp : p.IsFiberedInGroupoids) : (structureFunctor u p).IsFiberedInGroupoids where
  exists_lift {V U} a X hX := by
    obtain ⟨y, β, hβ⟩ := hp.exists_lift (u.map a) X.fib (X.over.trans (congrArg u.obj hX))
    have := hβ
    have hy : p.obj y = u.obj V := IsHomLift.domain_eq p (u.map a) β
    have hlift : p.IsHomLift (u.map (a ≫ eqToHom hX.symm)) β := by
      rw [u.map_comp, eqToHom_map]
      exact (IsHomLift.lift_comp_eqToHom_iff p (u.map a) β _).2 hβ
    refine ⟨⟨V, y, hy⟩, homMk' (X := ⟨V, y, hy⟩) (a ≫ eqToHom hX.symm) β hlift, ?_⟩
    exact IsHomLift.of_fac' (structureFunctor u p) a _ rfl hX (by simp)
  unique_lift {X Y Z} φ ψ f hf := by
    have hf' : (f : Z.base ⟶ Y.base) ≫ φ.base = ψ.base := hf
    have hcompat : (eqToHom Z.over ≫ u.map (f : Z.base ⟶ Y.base) ≫ eqToHom Y.over.symm) ≫
        p.map φ.fib = p.map ψ.fib := by
      rw [φ.over, ψ.over, ← hf']
      simp [u.map_comp]
    obtain ⟨χ, ⟨hχ₁, hχ₂⟩, hχuniq⟩ := hp.unique_lift φ.fib ψ.fib _ hcompat
    refine ⟨⟨f, χ, hχ₁⟩, ⟨rfl, Hom.ext hf' hχ₂⟩, ?_⟩
    rintro χ' ⟨hχ'₁, hχ'₂⟩
    have hb : χ'.base = (f : Z.base ⟶ Y.base) := hχ'₁
    exact Hom.ext hχ'₁ (hχuniq χ'.fib ⟨by rw [χ'.over, hb], congrArg Hom.fib hχ'₂⟩)

/-- The pushforward `u^p𝒮 ⥤ 𝒞` of a stack in groupoids `p : 𝒮 ⥤ 𝒟` over `(𝒟, K)` is a stack in
groupoids over `(𝒞, J)`, for a continuous functor `u : 𝒞 ⥤ 𝒟` from a category with all fibre
products that preserves them.

This is a special case of Stacks 04WD, which is
`CategoryTheory.StrictPullback.isStack_isFiberedInGroupoids_structureFunctor_toGrothendieck`. -/
theorem isStack_isFiberedInGroupoids_structureFunctor (J : GrothendieckTopology 𝒞)
    (K : GrothendieckTopology 𝒟) (u : 𝒞 ⥤ 𝒟) [u.IsContinuous J K] [HasPullbacks 𝒞]
    [PreservesLimitsOfShape WalkingCospan u] (p : 𝒮 ⥤ 𝒟) (hp : Functor.IsStack p K)
    (hp' : p.IsFiberedInGroupoids) :
    Functor.IsStack (structureFunctor u p) J ∧
      (structureFunctor u p).IsFiberedInGroupoids :=
  ⟨isStack_structureFunctor J K u p hp, isFiberedInGroupoids_structureFunctor u p hp'⟩


end StrictPullback

end CategoryTheory
