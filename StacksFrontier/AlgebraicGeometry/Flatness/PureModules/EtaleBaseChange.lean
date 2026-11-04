module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale morphisms after base change along a morphism to the base

Given a commutative square whose horizontal morphisms are étale, the induced morphism between
the base changes along an arbitrary morphism to the upper-right corner is again étale. The case
of the spectrum of a local ring of that corner is the one Stacks 05H2 states.

## Main definitions

* `AlgebraicGeometry.etaleBaseChangeMap` is the morphism between the two base changes induced
  by a commutative square, and `AlgebraicGeometry.stalkBaseChangeMap` is its special case for
  the spectrum of a local ring.

## Main results

* `AlgebraicGeometry.etale_etaleBaseChangeMap`: that induced morphism is étale when the two
  horizontal morphisms of the square are, and
  `AlgebraicGeometry.etale_stalkBaseChangeMap` is the special case which is Stacks 05H2.

## Implementation notes

The scheme `Spec 𝒪_{S', s'}` and its canonical morphism to `S'` are `Spec (S'.presheaf.stalk s')`
and `S'.fromSpecStalk s'`. Both fibre products are categorical pullbacks and the canonical
comparison between them is a `pullback.map`.

The local ring plays no part in the argument: what makes the comparison étale is that `X' ⟶ X`
is a morphism of schemes étale over `X`, hence étale, and that étale morphisms are stable under
base change. So the statement is proved for an arbitrary morphism to `S'` and specialized
afterwards.

## References

* [Stacks Project, Tag 05H2](https://stacks.math.columbia.edu/tag/05H2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {X' X S' S : Scheme.{u}}

/-- The canonical morphism between the base changes along a morphism `l : T ⟶ S'`, induced by a
commutative square. -/
noncomputable def etaleBaseChangeMap (f' : X' ⟶ S') (g' : X' ⟶ X)
    (g : S' ⟶ S) (f : X ⟶ S) (h : g' ≫ f = f' ≫ g) {T : Scheme.{u}} (l : T ⟶ S') :
    pullback f' l ⟶ pullback f (l ≫ g) :=
  pullback.map _ _ _ _ g' (𝟙 _) g h.symm (by simp)

/-- The canonical morphism between the base changes to the spectrum of the local ring of `S'`
at `s'`, induced by a commutative square. -/
noncomputable def stalkBaseChangeMap (f' : X' ⟶ S') (g' : X' ⟶ X)
    (g : S' ⟶ S) (f : X ⟶ S) (h : g' ≫ f = f' ≫ g) (s' : S') :
    pullback f' (S'.fromSpecStalk s') ⟶ pullback f (S'.fromSpecStalk s' ≫ g) :=
  etaleBaseChangeMap f' g' g f h (S'.fromSpecStalk s')

/-- The morphism between the base changes along an arbitrary morphism to the base, induced by a
commutative square with étale horizontal morphisms, is étale. -/
lemma etale_etaleBaseChangeMap (f' : X' ⟶ S') (g' : X' ⟶ X)
    (g : S' ⟶ S) (f : X ⟶ S) (h : g' ≫ f = f' ≫ g) {T : Scheme.{u}} (l : T ⟶ S')
    [Etale g'] [Etale g] : Etale (etaleBaseChangeMap f' g' g f h l) := by
  have _ : MorphismProperty.IsStableUnderComposition @Etale :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  let k : X' ⟶ pullback f g := pullback.lift g' f' h
  have hkf : k ≫ pullback.fst f g = g' := pullback.lift_fst _ _ _
  have hks : f' = k ≫ pullback.snd f g := (pullback.lift_snd _ _ _).symm
  have hk : Etale k := MorphismProperty.of_postcomp @Etale (W' := @Etale) k
    (pullback.fst f g) inferInstance (by rwa [hkf])
  let a : pullback f' l ⟶ pullback (pullback.snd f g) l :=
    pullback.map f' l (pullback.snd f g) l k (𝟙 _) (𝟙 _) hks (Category.id_comp _).symm
  rw [show etaleBaseChangeMap f' g' g f h l = a ≫ (pullbackLeftPullbackSndIso f g l).hom by
    dsimp only [etaleBaseChangeMap, a, pullback.map]
    ext
    · rw [pullback.lift_fst, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
        ← Category.assoc, pullback.lift_fst, Category.assoc, hkf]
    · rw [pullback.lift_snd, Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
        pullback.lift_snd]]
  exact MorphismProperty.comp_mem @Etale _ _
    (MorphismProperty.pullbackMap hk (inferInstance : Etale (𝟙 _)) hks (Category.id_comp _).symm)
    inferInstance

/-- **Stacks Project, Tag 05H2.** The morphism between the base changes to the spectrum of a
local ring, induced by a commutative square with étale horizontal morphisms, is étale. -/
@[stacks 05H2]
lemma etale_stalkBaseChangeMap (f' : X' ⟶ S') (g' : X' ⟶ X)
    (g : S' ⟶ S) (f : X ⟶ S) (h : g' ≫ f = f' ≫ g) (s' : S')
    [Etale g'] [Etale g] : Etale (stalkBaseChangeMap f' g' g f h s') :=
  etale_etaleBaseChangeMap f' g' g f h (S'.fromSpecStalk s')

end AlgebraicGeometry
