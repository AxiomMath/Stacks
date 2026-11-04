module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation

/-!
# Étale-local cancellation, and the étale charts of a morphism of the site

Let `P` be a property of morphisms of schemes which is étale local on the source and target
in the sense of Stacks 04R3 (`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget`). Then `P` can
be *cancelled* across a commuting square of étale morphisms: if

```
U' --h--> V'
|         |
a         b
v         v
V --k---> U
```

commutes with `a` and `b` étale and `k` having `P`, then `h` has `P`.

The consequence this is built for: a morphism `k` of the big fppf site of `S` whose
underlying morphism of schemes has `P` satisfies the every-chart condition
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Stacks 03MJ for `P`, because an étale
chart of a representable presheaf is, by full faithfulness of Yoneda, a morphism of the site
whose scheme morphism is étale, so every chart square of `yoneda.map k` *is* a square of the
above shape.

## Main results

* `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.of_commSq_etale`: the cancellation.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map`: the every-chart condition for
  a morphism of the site.
* `AlgebraicGeometry.Space.isFlat_yoneda_map` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_yoneda_map`: its instances at
  flatness (Stacks 03ML) and local finite presentation (Stacks 03XP), the two properties an
  fppf covering of algebraic spaces (Stacks 03Y8) asks of its members.

## Implementation notes

The cancellation is proved by factoring `h` through the fibre product `V ×_U V'`. The first
projection is a base change of the étale `b`, hence étale, and the second projection is a base
change of `k` along the étale `b`, hence has `P` by the `pullbackSnd_of_etale` clause of
Stacks 04R3. The comparison morphism `m : U' ⟶ V ×_U V'` composes with the first projection
to the étale `a`, so it is itself étale by Mathlib's
`CategoryTheory.MorphismProperty.HasOfPostcompProperty` for étale morphisms, and `h` is `m`
followed by the second projection, so the `precomp` clause of Stacks 04R3 — which is Stacks
04QV in the étale case — finishes.

Only `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget` is assumed, not base-change
stability of `P` in general: the only base change used is along an étale morphism, which is
what that structure provides. Base-change stability does enter
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map`, but only for *étaleness*, in
order to read an étale chart of a representable presheaf as an étale morphism of schemes.

## References

* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace IsEtaleLocalOnSourceAndTarget

variable {P : MorphismProperty Scheme.{u}} (hP : IsEtaleLocalOnSourceAndTarget P)

include hP

/-- **Étale-local cancellation.** If `h ≫ b = a ≫ k` with `a` and `b` étale and `k` having a
property `P` which is étale local on the source and target, then `h` has `P`. -/
theorem of_commSq_etale {U' V' V U : Scheme.{u}} (a : U' ⟶ V) (b : V' ⟶ U) (k : V ⟶ U)
    (h : U' ⟶ V') (ha : Etale a) (hb : Etale b) (hk : P k) (w : h ≫ b = a ≫ k) : P h := by
  have hm : Etale (pullback.lift a h w.symm) :=
    MorphismProperty.of_postcomp (W := @Etale.{u}) (W' := @Etale.{u}) _ (pullback.fst k b)
      inferInstance (by rwa [pullback.lift_fst])
  rw [← pullback.lift_snd a h w.symm]
  exact hP.precomp.precomp _ hm _ (hP.pullbackSnd_of_etale k hk b hb)

end IsEtaleLocalOnSourceAndTarget

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism `k` of the big fppf site of `S` whose underlying morphism of schemes has a
property `P` that is étale local on the source and target satisfies the every-chart condition
of Stacks 03MJ for `P`: every commuting square of étale charts of `yoneda.map k` comes, by
full faithfulness of Yoneda, from a commuting square of the site whose two chart edges are
étale morphisms of schemes, so étale-local cancellation applies. -/
theorem holdsOnEveryEtaleChart_yoneda_map {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P) {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (hk : P ((BigFppfOver.toScheme B S hS).map k)) :
    HoldsOnEveryEtaleChart B S hS P (yoneda.map k) := by
  intro U' V' a b h ha hb hsq
  obtain ⟨α, rfl⟩ := yoneda.map_surjective a
  obtain ⟨β, rfl⟩ := yoneda.map_surjective b
  have hsite : h ≫ β = α ≫ k := yoneda.map_injective (by simpa using hsq)
  refine hP.of_commSq_etale ((BigFppfOver.toScheme B S hS).map α)
    ((BigFppfOver.toScheme B S hS).map β) ((BigFppfOver.toScheme B S hS).map k) _
    ((presheaf_yoneda_map_etale_iff B S hS α).1 ha)
    ((presheaf_yoneda_map_etale_iff B S hS β).1 hb) hk ?_
  simpa using congrArg (BigFppfOver.toScheme B S hS).map hsite

/-- **Stacks 03ML** for a morphism of the site: a morphism of the big fppf site of `S` whose
underlying morphism of schemes is flat is a flat morphism of algebraic spaces over `S`. -/
theorem isFlat_yoneda_map {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (hk : Flat ((BigFppfOver.toScheme B S hS).map k)) :
    IsFlat B S hS (yoneda.map k) :=
  holdsOnEveryEtaleChart_yoneda_map B S hS Flat.isEtaleLocalOnSourceAndTarget k hk

/-- **Stacks 03XP**, part (1), for a morphism of the site: a morphism of the big fppf site of
`S` whose underlying morphism of schemes is locally of finite presentation is a morphism of
algebraic spaces over `S` which is locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_yoneda_map {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (hk : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k)) :
    IsLocallyOfFinitePresentation B S hS (yoneda.map k) :=
  holdsOnEveryEtaleChart_yoneda_map B S hS
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget k hk

end Space

end AlgebraicGeometry

end
