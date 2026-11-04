module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PushforwardDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PushforwardMorSheaf

/-!
# The pushforward of a stack along a continuous functor of sites

Let `u : 𝒞 ⥤ 𝒟` be a continuous functor of sites and `p : 𝒮 ⥤ 𝒟` a category over `𝒟`. This file
proves that the pushforward `u^p𝒮 ⥤ 𝒞` of `StacksDraft.CategoryTheory.Sites.Stack.Functoriality`
is a stack over `𝒞` when `p` is a stack over `𝒟`, and a stack in groupoids when `p` is one.

The three conditions of Stacks 026F are discharged in three different places: condition (1) is
Stacks 04WB, `CategoryTheory.StrictPullback.isFibered_structureFunctor`; condition (2) is
`CategoryTheory.StrictPullback.isMorSheaf_structureFunctor`; condition (3) is
`CategoryTheory.StrictPullback.hasEffectiveDescent_structureFunctor`.

## Main results

* `CategoryTheory.StrictPullback.isStack_structureFunctor`, Stacks 04WC;
* `CategoryTheory.StrictPullback.isFiberedInGroupoids_structureFunctor`, the fibres of `u^p𝒮` are
  groupoids as soon as those of `𝒮` are;
* `CategoryTheory.StrictPullback.isStack_isFiberedInGroupoids_structureFunctor`, Stacks 04WD.

## Implementation notes

Stacks 00WU asks of a continuous functor of sites both that it send coverings to coverings and that
it commute with the fibre products appearing in them; Mathlib's `Functor.IsContinuous` is the
sheaf-theoretic condition, which gives the first (`CoverPreserving.of_isContinuous`) but not the
second. The commutation with fibre products is genuinely used — see
`CategoryTheory.StrictPullback.glue` — so it is assumed here, in the form `[HasPullbacks 𝒞]` and
`[PreservesLimitsOfShape WalkingCospan u]`. Both hold for the functor underlying a morphism of
sites in the source's sense.

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

/-- **Stacks 04WC**.
If `p : 𝒮 ⥤ 𝒟` is a stack over the site `(𝒟, K)`, then the pushforward `u^p𝒮 ⥤ 𝒞` along a
continuous functor of sites `u : 𝒞 ⥤ 𝒟` is a stack over `(𝒞, J)`.

Continuity of `u` in the sense of Stacks 00WU is `[u.IsContinuous J K]` together with the
commutation with fibre products, `[HasPullbacks 𝒞]` and `[PreservesLimitsOfShape WalkingCospan u]`;
see the implementation notes. -/
@[stacks 04WC]
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

/-- **Stacks 04WD**.
If `p : 𝒮 ⥤ 𝒟` is a stack in groupoids over the site `(𝒟, K)`, then the pushforward `u^p𝒮 ⥤ 𝒞`
along a continuous functor of sites `u : 𝒞 ⥤ 𝒟` is a stack in groupoids over `(𝒞, J)`. -/
@[stacks 04WD]
theorem isStack_isFiberedInGroupoids_structureFunctor (J : GrothendieckTopology 𝒞)
    (K : GrothendieckTopology 𝒟) (u : 𝒞 ⥤ 𝒟) [u.IsContinuous J K] [HasPullbacks 𝒞]
    [PreservesLimitsOfShape WalkingCospan u] (p : 𝒮 ⥤ 𝒟) (hp : Functor.IsStack p K)
    (hp' : p.IsFiberedInGroupoids) :
    Functor.IsStack (structureFunctor u p) J ∧
      (structureFunctor u p).IsFiberedInGroupoids :=
  ⟨isStack_structureFunctor J K u p hp, isFiberedInGroupoids_structureFunctor u p hp'⟩

end StrictPullback

end CategoryTheory
