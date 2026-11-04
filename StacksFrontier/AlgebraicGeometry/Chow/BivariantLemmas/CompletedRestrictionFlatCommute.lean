module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedOpenImmersionComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedSmoothPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward

/-!
# Restriction of completed bivariant classes, and commuting with flat pullback

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` and
`h : Y' ⟶ Y` be morphisms of schemes locally of finite type over `S` and write
`X' = X ×_Y Y'`. **Stacks 0F9Z** attaches to a bivariant class `c ∈ A^p(X ⟶ Y)` its restriction
`res(c) ∈ A^p(X' ⟶ Y')`, characterized by `res(c) ∩ α = c ∩ α`. This file carries that restriction
to the completed bivariant groups of **Stacks 0FE0**,

  `res : A^*(X ⟶ Y)^∧ ⟶ A^*(X' ⟶ Y')^∧`,

and proves that every bivariant class commutes with flat pullback, in the form

  `res(c) ∘ p^* = p̄^* ∘ c`

for `c` a class for `i : X ⟶ P`, `p : P' ⟶ P` flat and `p̄ : X ×_P P' ⟶ X` its base change; this
is Stacks 0B76 (2), "bivariant classes commute with flat pullbacks", read as an identity of
composites (Stacks 0B75). It is proved for homogeneous classes and `p` flat of a fixed relative
dimension, and for completed classes and `p` smooth, whose relative dimension is only locally
constant. The proofs of Stacks 0FF2, Stacks 0FF5 and Stacks 0FF6 use it in this form, as
`j^! ∘ p^* = p̄^* ∘ i^!`.

## Main definitions

* `Stacks.Chow.completedBivariantRestrictionViaSequence` — **Stacks 0F9Z** on completions, the
  restriction `A^*(X ⟶ Y)^∧ ⟶ A^*(X' ⟶ Y')^∧`.

## Main results

* `Stacks.Chow.bivariantCompositeOfInvertible_bivariantRestriction_flatPullbackBivariantClass` —
  `res(c) ∘ p^* = p̄^* ∘ c` for `c ∈ A^q(X ⟶ P)` and `p` flat of relative dimension `r`.
* `Stacks.Chow.completedBivariantSequenceOfInvertible_completedBivariantRestriction` — degree by
  degree, the restriction on completions is the restriction of Stacks 0F9Z;
  `Stacks.Chow.completedBivariantRestriction_apply` reads it on a connected component and
  `Stacks.Chow.completedBivariantRestriction_cap` gives the cap formula `res(c) ∩ α = c ∩ α`.
* `Stacks.Chow.bivariantConnectedComponentRestriction_bivariantRestriction_eq_zero` — restriction
  preserves the vanishing of a class on a connected component, which is what makes the
  restriction of an element of the completed group again an element of the completed group.
* `Stacks.Chow.bivariantCompositeOfInvertible_connectedComponentRestriction_flatPullback` —
  `res(c) ∘ p^* = p̄^* ∘ c` on a connected component of `X ×_P P'`.
* `Stacks.Chow.completedBivariantRestriction_composite_completedFlatPullbackOfSmooth` —
  `res(c) ∘ p^* = p̄^* ∘ c` for `c ∈ A^*(X ⟶ P)^∧` and `p` smooth.

## Implementation notes

### The restriction on completions

An element of `A^*(X ⟶ Y)^∧` is read, by Stacks 0FE0
(`Stacks.Chow.completedBivariantGroupEquivOfInvertible`), as a tuple `(c_n)_n` in
`∏_n A^n(X ⟶ Y)` vanishing in almost all degrees on each connected component of `X`, and
`res(c)` is the tuple `(res(c_n))_n`. That this tuple again vanishes in almost all degrees on each
connected component `X'_w` of `X'` is the one point that needs proof: `X'_w` lies over a connected
component `X_a` of `X`, and wherever `c_n` vanishes on `X_a` its restriction vanishes on `X'_w`,
because on a test scheme the cap operation of the restriction of `res(c_n)` to `X'_w` is the cap
operation of `c_n` restricted to an open subscheme lying over `X_a`
(`Stacks.Chow.chowGroupRestrict_cap_eq_zero_of_connectedComponentRestriction_eq_zero`). Defining
`res` through the tuples makes its comparison with Stacks 0F9Z degree by degree a definitional
unfolding.

### Commuting with flat pullback

On a test scheme `t : T ⟶ P` both composites cap `α` by first capping with `c` and then pulling
back flatly along one of two base changes of `p`, possibly restricted to an open subscheme: on the
side of `res(c) ∘ p^*` the flat pullback happens first, and Stacks 0B76 (2) for `c` moves it past
the cap operation. The remaining comparison of the two flat pullbacks across the canonical
isomorphisms of iterated fibre products is the isomorphism case of Stacks 02RG together with
Stacks 02RD for open immersions (`Stacks.Chow.chowGroupRestrict_flatPullbackChow_of_comm`,
`Stacks.Chow.chowPushforwardOfIso_chowGroupRestrict_flatPullbackChow_eq`).

The two composites are classes for the equal morphisms `X ×_P P' ⟶ P' ⟶ P` and
`X ×_P P' ⟶ X ⟶ P`, and their degrees `q + -r` and `-r + q` are equal integers written two ways,
so the identities are heterogeneous equalities. On completions the component of `P` that a
connected component of `X ×_P P'` lands in is reached once through `P'` and once through `X`;
the restriction of `p` to components is therefore replaced by the restriction of `p` into the
component reached through `X`, and the relative dimension of `p` on the component of `P'` is that
of `p̄` on the component of `X ×_P P'`
(`Stacks.Chow.smoothComponentRelativeDimension_pullbackFst`).

Everything is stated at the Gysin system of the first Chern class rule of invertible modules,
`Stacks.Chow.gysinSystemOfInvertible`, where every Gysin compatibility used is a theorem and
nothing is assumed; the vanishing lemmas, which hold for any Gysin system with the compatibilities
they use, are stated in that generality.

## References

* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
* [Stacks Project, Tag 0FF2](https://stacks.math.columbia.edu/tag/0FF2)
* [Stacks Project, Tag 0FF5](https://stacks.math.columbia.edu/tag/0FF5)
* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Flat pullback across two isomorphisms onto a common target -/

/-- Two flat pullbacks of one class, along `d : A ⟶ W` and `v : B ⟶ W`, agree after pushing
forward along isomorphisms `U : A ⟶ Z` and `V : B ⟶ Z` onto a common scheme, as soon as a single
morphism `Φ : Z ⟶ W` recovers `d` from `U` and `v` from `V`. This is the isomorphism case of
Stacks 02RG (`Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`) with one leg the identity. -/
theorem chowPushforwardOfIso_flatPullbackChow_eq_of_comp (C : ChowSituation.{u})
    {A B Z W : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (d : A ⟶ W) [LocallyOfFiniteType d] [Flat d] (hd : d ≫ sW = sA)
    (v : B ⟶ W) [LocallyOfFiniteType v] [Flat v] (hv : v ≫ sW = sB)
    (U : A ⟶ Z) [IsIso U] (hU : U ≫ sZ = sA) (V : B ⟶ Z) [IsIso V] (hV : V ≫ sZ = sB)
    (Φ : Z ⟶ W) (hUΦ : U ≫ Φ = d) (hVΦ : V ≫ Φ = v) (r : ℕ)
    (hdr : AlgebraicGeometry.RelativeDimension d r)
    (hvr : AlgebraicGeometry.RelativeDimension v r) (k : ℤ)
    (hfacd : FlatPullbackFactorsThroughRationalEquivalence C sA sW d hd r hdr k)
    (hfacv : FlatPullbackFactorsThroughRationalEquivalence C sB sW v hv r hvr k)
    (γ : chowGroup C sW k) :
    chowPushforwardOfIso C sB sZ V hV (k + (r : ℤ))
        (flatPullbackChow C sB sW v hv r hvr k hfacv γ) =
      chowPushforwardOfIso C sA sZ U hU (k + (r : ℤ))
        (flatPullbackChow C sA sW d hd r hdr k hfacd γ) := by
  have hu₁ : (U ≫ inv V) ≫ sB = sA := by
    rw [← hV, Category.assoc, IsIso.inv_hom_id_assoc, hU]
  have hsq : d ≫ 𝟙 W = (U ≫ inv V) ≫ v := by
    rw [Category.comp_id, ← hVΦ, Category.assoc, IsIso.inv_hom_id_assoc, hUΦ]
  have h := flatPullbackChow_chowPushforwardOfIso C sW sA sW sB (𝟙 W) (Category.id_comp sW)
    (U ≫ inv V) hu₁ d hd v hv hsq r hdr hvr k hfacd hfacv γ
  rw [chowPushforwardOfIso_id] at h
  rw [h, chowPushforwardOfIso_comp_apply]
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ (by simp) _ _ _ _

/-- Pushforward along the inverse of an isomorphism over the base is restriction along the
isomorphism, an isomorphism being an open immersion. -/
theorem chowGroupRestrict_eq_chowPushforwardOfIso_inv (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (e : B ≅ A)
    (he : e.hom ≫ sA = sB) (k : ℤ) (x : chowGroup C sA k) :
    chowGroupRestrict C sA sB e.hom he k x =
      chowPushforwardOfIso C sA sB e.inv (by rw [← he, Iso.inv_hom_id_assoc]) k x := by
  rw [chowGroupRestrict_of_isIso]
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ (by simp) _ _ k x

/-- An open immersion composed with an open immersion equal to `u` is an open immersion. -/
private theorem isOpenImmersion_of_comp_eq {A B D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ D) (u : A ⟶ D)
    [IsOpenImmersion g] [IsOpenImmersion u] (h : f ≫ g = u) : IsOpenImmersion f := by
  subst h
  exact IsOpenImmersion.of_comp f g

/-- The base change of a flat morphism of relative dimension `r` which is locally of finite type
is again flat, locally of finite type, and of relative dimension `r`. -/
private theorem isPullback_locallyOfFiniteType_flat_relativeDimension {A B D E : Scheme.{u}}
    {a : A ⟶ B} {b : A ⟶ D} {f : B ⟶ E} {g : D ⟶ E} (sq : IsPullback a b f g)
    [LocallyOfFiniteType f] [Flat f] {r : ℕ} (hr : AlgebraicGeometry.RelativeDimension f r) :
    ∃ (_ : LocallyOfFiniteType b) (_ : Flat b), AlgebraicGeometry.RelativeDimension b r :=
  ⟨MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance,
    MorphismProperty.of_isPullback sq (P := @Flat) inferInstance,
    AlgebraicGeometry.RelativeDimension.of_isPullback sq hr⟩

/-- **Flat pullback commutes with restriction to opens along a commutative square.** If
`u : Q ⟶ M` and `o : Z' ⟶ Z` are open immersions and `q' : M ⟶ Z`, `d : Q ⟶ Z'` are flat of
relative dimension `r` with `u ≫ q' = d ≫ o`, then restricting the flat pullback along `q'` to `Q`
is the flat pullback along `d` of the restriction to `Z'`. The square need not be cartesian: `Q` is
an open subscheme of the fibre product `M ×_Z Z'`, on which this is
`Stacks.Chow.chowGroupRestrict_flatPullbackChow`, and on the open subscheme it is Stacks 02RD, an
open immersion being flat of relative dimension `0`. -/
theorem chowGroupRestrict_flatPullbackChow_of_comm (C : ChowSituation.{u}) {Q M Z' Z : Scheme.{u}}
    (sQ : Q ⟶ C.S) [LocallyOfFiniteType sQ] (sM : M ⟶ C.S) [LocallyOfFiniteType sM]
    (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ'] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (q' : M ⟶ Z) [LocallyOfFiniteType q'] [Flat q'] (hq' : q' ≫ sZ = sM)
    (d : Q ⟶ Z') [LocallyOfFiniteType d] [Flat d] (hd : d ≫ sZ' = sQ)
    (u : Q ⟶ M) [IsOpenImmersion u] (hu : u ≫ sM = sQ)
    (o : Z' ⟶ Z) [IsOpenImmersion o] (ho : o ≫ sZ = sZ') (hsq : u ≫ q' = d ≫ o) (r : ℕ)
    (hq'r : AlgebraicGeometry.RelativeDimension q' r)
    (hdr : AlgebraicGeometry.RelativeDimension d r) (k : ℤ) (γ : chowGroup C sZ k) :
    chowGroupRestrict C sM sQ u hu (k + (r : ℤ))
        (flatPullbackChow C sM sZ q' hq' r hq'r k (flatPullbackDescends C _ _ _ _ _ _ _) γ) =
      flatPullbackChow C sQ sZ' d hd r hdr k (flatPullbackDescends C _ _ _ _ _ _ _)
        (chowGroupRestrict C sZ sZ' o ho k γ) := by
  have hsqP := IsPullback.of_hasPullback q' o
  have hq'' : pullback.snd q' o ≫ sZ' = pullback.fst q' o ≫ sM := by
    rw [← ho, ← Category.assoc, ← pullback.condition, Category.assoc, hq']
  have hr'' : AlgebraicGeometry.RelativeDimension (pullback.snd q' o) r :=
    relativeDimension_pullback_snd q' o r hq'r
  have hcart := chowGroupRestrict_flatPullbackChow C sM sZ (pullback.fst q' o ≫ sM) sZ' q' hq' r
    hq'r (pullback.fst q' o) rfl o ho (pullback.snd q' o) hq'' hsqP hr'' k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) γ
  have hκ : pullback.lift u d hsq ≫ pullback.fst q' o = u := pullback.lift_fst _ _ _
  have hκd : pullback.lift u d hsq ≫ pullback.snd q' o = d := pullback.lift_snd _ _ _
  have := isOpenImmersion_of_comp_eq _ _ _ hκ
  have hκbase : pullback.lift u d hsq ≫ (pullback.fst q' o ≫ sM) = sQ := by
    rw [← Category.assoc, hκ, hu]
  have h₁ : chowGroupRestrict C sM sQ u hu (k + (r : ℤ))
      (flatPullbackChow C sM sZ q' hq' r hq'r k (flatPullbackDescends C _ _ _ _ _ _ _) γ) =
      chowGroupRestrict C _ sQ (pullback.lift u d hsq) hκbase (k + (r : ℤ))
        (chowGroupRestrict C sM _ (pullback.fst q' o) rfl (k + (r : ℤ))
          (flatPullbackChow C sM sZ q' hq' r hq'r k (flatPullbackDescends C _ _ _ _ _ _ _) γ)) := by
    rw [chowGroupRestrict_comp]
    exact DFunLike.congr_fun (chowGroupRestrict_congr C _ _ _ _ _ _ hκ.symm _) _
  rw [h₁, hcart]
  have hκr := relativeDimension_of_isOpenImmersion (pullback.lift u d hsq)
  refine eq_of_heq ((heq_chowGroupRestrict_flatPullbackChow C _ sQ _ hκbase hκr _
    (flatPullbackDescends C _ _ _ _ _ _ _) _).trans ?_)
  refine (flatPullbackChow_comp_heq C (flatPullbackDescends C) sQ _ sZ' _ _ hκbase hq'' 0 r hκr
    hr'' k _).trans ?_
  exact flatPullbackChow_heq_congr_base C rfl rfl hκd _ _ (by simp) _ _ rfl _ _ _ _ HEq.rfl

/-- Pushforward along an isomorphism over the base is restriction along its inverse. -/
theorem chowPushforwardOfIso_hom_eq_chowGroupRestrict (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (e : A ≅ B)
    (he : e.hom ≫ sB = sA) (k : ℤ) (x : chowGroup C sA k) :
    chowPushforwardOfIso C sA sB e.hom he k x =
      chowGroupRestrict C sA sB e.inv (by rw [← he, Iso.inv_hom_id_assoc]) k x :=
  (chowGroupRestrict_eq_chowPushforwardOfIso_inv C sA sB e.symm _ k x).symm

/-- Pushforward along the inverse of an isomorphism over the base is restriction along the
isomorphism. -/
theorem chowPushforwardOfIso_iso_inv_eq_chowGroupRestrict (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (e : B ≅ A)
    (he : e.inv ≫ sB = sA) (k : ℤ) (x : chowGroup C sA k) :
    chowPushforwardOfIso C sA sB e.inv he k x =
      chowGroupRestrict C sA sB e.hom (by rw [← he, Iso.hom_inv_id_assoc]) k x :=
  (chowGroupRestrict_eq_chowPushforwardOfIso_inv C sA sB e _ k x).symm

/-- **Flat pullback and restriction across isomorphisms onto a common target.** Restricting the
flat pullback of `γ` along `v : B ⟶ Z` to an open subscheme `A₁` of `B` and pushing it forward
along an isomorphism `V : A₁ ⟶ F` gives the flat pullback along `d : A₂ ⟶ Z'` of the restriction
of `γ` to an open subscheme `Z'` of `Z`, pushed forward along an isomorphism `U : A₂ ⟶ F`, as soon
as one morphism `Θ : F ⟶ Z` recovers both composites to `Z`. This is
`Stacks.Chow.chowGroupRestrict_flatPullbackChow_of_comm` across the isomorphisms. -/
theorem chowPushforwardOfIso_chowGroupRestrict_flatPullbackChow_eq (C : ChowSituation.{u})
    {A₁ A₂ B Z Z' F : Scheme.{u}} (sA₁ : A₁ ⟶ C.S) [LocallyOfFiniteType sA₁] (sA₂ : A₂ ⟶ C.S)
    [LocallyOfFiniteType sA₂] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ'] (sF : F ⟶ C.S)
    [LocallyOfFiniteType sF] (v : B ⟶ Z) [LocallyOfFiniteType v] [Flat v] (hv : v ≫ sZ = sB)
    (u₁ : A₁ ⟶ B) [IsOpenImmersion u₁] (hu₁ : u₁ ≫ sB = sA₁) (V : A₁ ⟶ F) [IsIso V]
    (hV : V ≫ sF = sA₁) (o : Z' ⟶ Z) [IsOpenImmersion o] (ho : o ≫ sZ = sZ') (d : A₂ ⟶ Z')
    [LocallyOfFiniteType d] [Flat d] (hd : d ≫ sZ' = sA₂) (U : A₂ ⟶ F) [IsIso U]
    (hU : U ≫ sF = sA₂) (Θ : F ⟶ Z) (hVΘ : V ≫ Θ = u₁ ≫ v) (hUΘ : U ≫ Θ = d ≫ o) (r : ℕ)
    (hvr : AlgebraicGeometry.RelativeDimension v r)
    (hdr : AlgebraicGeometry.RelativeDimension d r) (k : ℤ) (γ : chowGroup C sZ k) :
    chowPushforwardOfIso C sA₁ sF V hV (k + (r : ℤ))
        (chowGroupRestrict C sB sA₁ u₁ hu₁ (k + (r : ℤ))
          (flatPullbackChow C sB sZ v hv r hvr k (flatPullbackDescends C _ _ _ _ _ _ _) γ)) =
      chowPushforwardOfIso C sA₂ sF U hU (k + (r : ℤ))
        (flatPullbackChow C sA₂ sZ' d hd r hdr k (flatPullbackDescends C _ _ _ _ _ _ _)
          (chowGroupRestrict C sZ sZ' o ho k γ)) := by
  have hu : (U ≫ inv V ≫ u₁) ≫ sB = sA₂ := by
    rw [Category.assoc, Category.assoc, hu₁, ← hV, IsIso.inv_hom_id_assoc, hU]
  have hsq : (U ≫ inv V ≫ u₁) ≫ v = d ≫ o := by
    rw [Category.assoc, Category.assoc, ← hVΘ, IsIso.inv_hom_id_assoc, hUΘ]
  have hUV : (U ≫ inv V) ≫ sA₁ = sA₂ := by
    rw [Category.assoc, ← hV, IsIso.inv_hom_id_assoc, hU]
  have hcomp := chowGroupRestrict_comp C sB sA₁ u₁ hu₁ (k + (r : ℤ)) sA₂ (U ≫ inv V) hUV
    (flatPullbackChow C sB sZ v hv r hvr k (flatPullbackDescends C _ _ _ _ _ _ _) γ)
  rw [← chowGroupRestrict_flatPullbackChow_of_comm C sA₂ sB sZ' sZ v hv d hd _ hu o ho hsq r hvr hdr
    k γ]
  rw [chowGroupRestrict_congr C sB sA₂ (U ≫ inv V ≫ u₁) hu (k + (r : ℤ)) ((U ≫ inv V) ≫ u₁)
    (Category.assoc _ _ _).symm (by rw [Category.assoc]; exact hu), ← hcomp,
    chowGroupRestrict_of_isIso C sA₁ sA₂ (k + (r : ℤ)) _ hUV,
    chowPushforwardOfIso_comp_apply]
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ (by simp) _ _ _ _

/-- The base change `X ×_P P' ⟶ X` of a morphism `p : P' ⟶ P` of relative dimension `r` has
relative dimension `r` (Stacks 02NK). -/
theorem relativeDimension_pullbackFst {X P P' : Scheme.{u}} (i : X ⟶ P) (p : P' ⟶ P)
    [LocallyOfFiniteType p] {r : ℕ} (hpr : AlgebraicGeometry.RelativeDimension p r) :
    AlgebraicGeometry.RelativeDimension (pullback.fst i p) r :=
  AlgebraicGeometry.RelativeDimension.of_isPullback (IsPullback.of_hasPullback i p).flip hpr

/-! ### Restriction composed with flat pullback -/

section FlatCommute

variable (C : ChowSituation.{u}) {X P P' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (i : X ⟶ P) [LocallyOfFiniteType i]
  (hi : i ≫ sP = sX) (p : P' ⟶ P) [LocallyOfFiniteType p] [Flat p] (r : ℕ)
  (hpr : AlgebraicGeometry.RelativeDimension p r) (q : ℤ)

/-- **`res(c) ∘ p^* = p̄^* ∘ c`.** For a bivariant class `c ∈ A^q(X ⟶ P)` and a flat morphism
`p : P' ⟶ P` of relative dimension `r`, the restriction `res(c) ∈ A^q(X ×_P P' ⟶ P')` of `c`
along `p` (Stacks 0F9Z) composed with the flat-pullback class `p^* ∈ A^{-r}(P' ⟶ P)` of
Stacks 0B78 is the flat-pullback class of the base change `X ×_P P' ⟶ X` of `p` composed with
`c`. The two composites are classes for `X ×_P P' ⟶ P' ⟶ P` and `X ×_P P' ⟶ X ⟶ P`, which are
equal morphisms (`pullback.condition`), and of degrees `q + -r` and `-r + q`, whence the
heterogeneous equality. This is Stacks 0B76 (2) for `c` — bivariant classes commute with flat
pullback — read as an identity of composite classes. -/
theorem bivariantCompositeOfInvertible_bivariantRestriction_flatPullbackBivariantClass
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sP i hi q) :
    bivariantCompositeOfInvertible C (pullback.fst i p ≫ sX) (p ≫ sP) sP (pullback.snd i p) p
        (pullbackSnd_comp_structureMorphism_eq C sX sP i hi p) rfl q (-(r : ℤ))
        (bivariantRestriction C (gysinSystemOfInvertible C) sX sP i hi p q
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
        (flatPullbackBivariantClassOfInvertible C (p ≫ sP) sP p rfl r hpr) ≍
      bivariantCompositeOfInvertible C (pullback.fst i p ≫ sX) sX sP (pullback.fst i p) i rfl hi
        (-(r : ℤ)) q
        (flatPullbackBivariantClassOfInvertible C (pullback.fst i p ≫ sX) sX (pullback.fst i p) rfl
            r (relativeDimension_pullbackFst i p hpr)) c := by
  refine BivariantClass.heq_of_congrHom_cap_heq pullback.condition.symm (by ring) _ _ ?_
  intro T t _ k α
  have e : pullback.snd p t ≫ t = pullback.fst p t ≫ p := pullback.condition.symm
  have sq := isPullback_baseChangeMapOfEq i t (pullback.snd p t) (pullback.fst p t ≫ p) e
  have hrt : AlgebraicGeometry.RelativeDimension (pullback.snd p t) r :=
    relativeDimension_pullbackSnd p hpr t
  obtain ⟨_, _, hr'⟩ := isPullback_locallyOfFiniteType_flat_relativeDimension sq hrt
  have hqY : pullback.snd p t ≫ (t ≫ sP) = (pullback.fst p t ≫ p) ≫ sP := by
    rw [← Category.assoc, e]
  -- Stacks 0B76 (2) for `c`, along the base change of `p` to the test scheme
  have hflat := BivariantClass.flat_naturality_of_eq C (gysinSystemOfInvertible C) sX sP i hi q c
    t (pullback.snd p t) (pullback.fst p t ≫ p) e r hrt
    (baseChangeMapOfEq i t (pullback.snd p t) (pullback.fst p t ≫ p) e) sq
    (baseChangeMapOfEq_fst i t (pullback.snd p t) (pullback.fst p t ≫ p) e) k hqY hr'
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) α
  -- the left side: the restriction caps by `c` at `P' ×_P T ⟶ P`, on the flat pullback of `α`
  have hL : (bivariantCompositeOfInvertible C (pullback.fst i p ≫ sX) (p ≫ sP) sP
      (pullback.snd i p) p (pullbackSnd_comp_structureMorphism_eq C sX sP i hi p) rfl q (-(r : ℤ))
      (bivariantRestriction C (gysinSystemOfInvertible C) sX sP i hi p q
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
      (flatPullbackBivariantClassOfInvertible C (p ≫ sP) sP p rfl r hpr)).cap t k α ≍
      chowPushforwardOfIso C (pullback.fst i (pullback.fst p t ≫ p) ≫ sX)
        (pullback.fst (pullback.snd i p ≫ p) t ≫ (pullback.fst i p ≫ sX))
        ((pullbackLeftPullbackSndIso i p (pullback.fst p t)).inv ≫
          (pullbackRightPullbackFstIso p t (pullback.snd i p)).hom) (by simp) ((k - q) + (r : ℤ))
        (flatPullbackChow C (pullback.fst i (pullback.fst p t ≫ p) ≫ sX) (pullback.fst i t ≫ sX)
          (baseChangeMapOfEq i t (pullback.snd p t) (pullback.fst p t ≫ p) e)
          (baseChangeMapOfEq_comp_structure sX i t (pullback.snd p t) _ e) r hr' (k - q)
          (flatPullbackDescends C _ _ _ _ _ _ _) (c.cap t k α)) := by
    rw [bivariantCompositeOfInvertible, bivariantComposite_cap, bivariantCompositeCap_apply]
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    rw [bivariantRestriction_cap, bivariantRestrictionCap_apply,
      properChowPushforward_eq_chowPushforwardOfIso, chowPushforwardOfIso_comp_apply]
    refine chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _ ?_
    refine (c.cap_heq_congr (pullback.fst p t ≫ p) (by ring) _ _ ?_).trans hflat
    refine (chowGroupCongr_heq C _ _ _).trans ((flatPullbackBivariantCap_heq C (p ≫ sP) sP p rfl r
      hpr (flatPullbackDescends C) t k α).trans ?_)
    exact flatPullbackChow_heq_congr_base C (Category.assoc _ _ _).symm rfl rfl _ _ rfl _ _ rfl
      _ _ α α HEq.rfl
  -- the right side: the flat pullback along `X ×_P P' ⟶ X` of `c ∩ α`
  have hR : (bivariantCompositeOfInvertible C (pullback.fst i p ≫ sX) sX sP (pullback.fst i p) i
      rfl hi (-(r : ℤ)) q
      (flatPullbackBivariantClassOfInvertible C (pullback.fst i p ≫ sX) sX (pullback.fst i p) rfl r
          (relativeDimension_pullbackFst i p hpr)) c).cap t k α ≍
      chowPushforwardOfIso C
        (pullback.fst (pullback.fst i p) (pullback.fst i t) ≫ (pullback.fst i p ≫ sX))
        (pullback.fst (pullback.fst i p ≫ i) t ≫ (pullback.fst i p ≫ sX))
        (pullbackRightPullbackFstIso i t (pullback.fst i p)).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp _ _ _ _) ((k - q) + (r : ℤ))
        (flatPullbackChow C
          (pullback.fst (pullback.fst i p) (pullback.fst i t) ≫ (pullback.fst i p ≫ sX))
          (pullback.fst i t ≫ sX) (pullback.snd (pullback.fst i p) (pullback.fst i t))
          (pullbackSnd_comp_structureMorphism_eq C _ sX (pullback.fst i p) rfl _) r
          (relativeDimension_pullback_snd _ _ r (relativeDimension_pullbackFst i p hpr)) (k - q)
          (flatPullbackDescends C _ _ _ _ _ _ _) (c.cap t k α)) := by
    rw [bivariantCompositeOfInvertible, bivariantComposite_cap, bivariantCompositeCap_apply]
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    refine chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _ ?_
    exact flatPullbackBivariantCap_heq C (pullback.fst i p ≫ sX) sX (pullback.fst i p) rfl r
      (relativeDimension_pullbackFst i p hpr) (flatPullbackDescends C) (pullback.fst i t)
      (k - q) (c.cap t k α)
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _ hL).trans ?_
  rw [chowPushforwardOfIso_comp_apply]
  refine HEq.trans (heq_of_eq ?_) hR.symm
  -- the comparison `(X ×_P P') ×_P T ⟶ X ×_P T` that both sides factor through
  have hΦ : (pullback.fst (pullback.fst i p ≫ i) t ≫ pullback.fst i p) ≫ i =
      pullback.snd (pullback.fst i p ≫ i) t ≫ t := by
    rw [Category.assoc]; exact pullback.condition
  have hΦfst : pullback.lift _ _ hΦ ≫ pullback.fst i t =
      pullback.fst (pullback.fst i p ≫ i) t ≫ pullback.fst i p := pullback.lift_fst _ _ _
  have hΦsnd : pullback.lift _ _ hΦ ≫ pullback.snd i t = pullback.snd (pullback.fst i p ≫ i) t :=
    pullback.lift_snd _ _ _
  refine chowPushforwardOfIso_flatPullbackChow_eq_of_comp C _ _ _ _ _ _ _ _ _ _ _ _
    (pullback.lift _ _ hΦ) ?_ ?_ r _ _ (k - q) _ _ (c.cap t k α)
  · apply pullback.hom_ext
    · simp only [Category.assoc, hΦfst, pullbackRightPullbackFstIso_hom_fst_assoc]
      exact pullback.condition
    · simp only [Category.assoc, hΦsnd, pullbackRightPullbackFstIso_hom_snd]
  · apply pullback.hom_ext
    · simp only [Category.assoc, hΦfst, baseChangeMapOfEq_fst]
      simp
    · simp only [Category.assoc, hΦsnd, baseChangeMapOfEq_snd]
      simp

end FlatCommute

/-! ### A class vanishing on a connected component caps to zero over it -/

section Vanishing

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : ℤ) (hgysO : G.IsNaturalUnderOpenImmersion)

/-- **The cap operation of the restriction to a connected component** (Stacks 0FDZ): on a test
scheme `g : T ⟶ Y_{a(i)}` it is the cap operation of `c` at `T ⟶ Y_{a(i)} ⟶ Y`, restricted along
the open immersion `X_i ×_{Y_{a(i)}} T ⟶ X ×_Y T`. -/
theorem bivariantConnectedComponentRestriction_cap (c : BivariantClass C G sX sY f hf p)
    (i : _root_.ConnectedComponents X) {T : Scheme.{u}}
    (g : T ⟶ (Y.connectedComponentOpens (f.continuous.connectedComponentsMap i) : Scheme.{u}))
    [LocallyOfFiniteType g] (k : ℤ)
    (β : chowGroup C (g ≫ ((Y.connectedComponentOpens
      (f.continuous.connectedComponentsMap i)).ι ≫ sY)) k) :
    (bivariantConnectedComponentRestriction C G sX sY f hf p hgysO c i).cap g k β =
      chowGroupRestrict C (pullback.fst f (g ≫ (Y.connectedComponentOpens
          (f.continuous.connectedComponentsMap i)).ι) ≫ sX)
        (pullback.fst (f.resConnectedComponent i) g ≫ ((X.connectedComponentOpens i).ι ≫ sX))
        (opensPullbackComparison f (X.connectedComponentOpens i)
          (Y.connectedComponentOpens (f.continuous.connectedComponentsMap i))
          (f.resConnectedComponent i) (f.resConnectedComponent_comp_ι i) g)
        (by rw [← Category.assoc, opensPullbackComparison_fst, Category.assoc]) (k - p)
        (c.cap (g ≫ (Y.connectedComponentOpens (f.continuous.connectedComponentsMap i)).ι) k
          (chowGroupCongr C (Category.assoc _ _ _).symm k β)) :=
  rfl

/-- **A class vanishing on a connected component caps to zero over it.** If the restriction
(Stacks 0FDZ) of `c ∈ A^p(X ⟶ Y)` to a connected component `X_i` of `X` vanishes, then for every
test scheme `t : T ⟶ Y` the class `c ∩ α ∈ CH_{k-p}(X ×_Y T)` restricts to zero on every open
subscheme of `X ×_Y T` lying over `X_i`.

The open subscheme `X_i ×_Y T` lies over the open subscheme `T_V = T ×_Y Y_{a(i)}` of `T`, where it
is the base change of `X_i ⟶ Y_{a(i)}`; there the cap operation of `c` restricts to that of its
restriction to `X_i` (Stacks 0B76 (2) along the open immersion `T_V ⟶ T`,
`Stacks.Chow.BivariantClass.cap_chowGroupRestrict`), which is zero. -/
theorem chowGroupRestrict_cap_eq_zero_of_connectedComponentRestriction_eq_zero
    (c : BivariantClass C G sX sY f hf p) (i : _root_.ConnectedComponents X)
    (hc : bivariantConnectedComponentRestriction C G sX sY f hf p hgysO c i = 0)
    {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sY) k)
    {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (u : W ⟶ pullback f t)
    [IsOpenImmersion u] (hu : u ≫ (pullback.fst f t ≫ sX) = sW)
    (a : W ⟶ (X.connectedComponentOpens i : Scheme.{u}))
    (ha : a ≫ (X.connectedComponentOpens i).ι = u ≫ pullback.fst f t) :
    chowGroupRestrict C (pullback.fst f t ≫ sX) sW u hu (k - p) (c.cap t k α) = 0 := by
  set V := Y.connectedComponentOpens (f.continuous.connectedComponentsMap i)
  set v := pullback.fst t V.ι
  set g' := pullback.snd t V.ι
  have hg' : g' ≫ V.ι = v ≫ t := pullback.condition.symm
  -- restricting the test scheme to `T_V`
  have sq := isPullback_baseChangeMapOfEq f t v (v ≫ t) rfl
  have : IsOpenImmersion (baseChangeMapOfEq f t v (v ≫ t) rfl) :=
    MorphismProperty.of_isPullback sq (P := @IsOpenImmersion) inferInstance
  have hvY : v ≫ (t ≫ sY) = (v ≫ t) ≫ sY := (Category.assoc _ _ _).symm
  have hcap := BivariantClass.cap_chowGroupRestrict C G sX sY f hf p c t v (v ≫ t) rfl
    (baseChangeMapOfEq f t v (v ≫ t) rfl) sq (baseChangeMapOfEq_fst f t v (v ≫ t) rfl) k hvY
    (baseChangeMapOfEq_comp_structure sX f t v (v ≫ t) rfl) α
  -- the cap operation of the restriction of `c` to `X_i`, over `T_V`
  have hmY : g' ≫ (V.ι ≫ sY) = (v ≫ t) ≫ sY := by rw [← Category.assoc, hg']
  have hpiece := bivariantPieceRestrictionCap_eq C G sX sY f hf p X.connectedComponentOpens
    Y.connectedComponentOpens f.continuous.connectedComponentsMap
    f.connectedComponentOpens_le_preimage i c g' (v ≫ t) hg' hmY
    (pieceComparisonCongr f X.connectedComponentOpens Y.connectedComponentOpens
      f.continuous.connectedComponentsMap f.connectedComponentOpens_le_preimage i g' (v ≫ t) hg')
    (pieceComparisonCongr_fst _ _ _ _ _ _ _ _ _) (pieceComparisonCongr_snd _ _ _ _ _ _ _ _ _) k
    (pieceComparisonCongr_comp_structureMorphism _ _ _ _ _ _ _ _ _ sX)
    (chowGroupCongr C hmY.symm k (chowGroupRestrict C (t ≫ sY) ((v ≫ t) ≫ sY) v hvY k α))
  have hzero : bivariantPieceRestrictionCap C G sX sY f hf p X.connectedComponentOpens
      Y.connectedComponentOpens f.continuous.connectedComponentsMap
      f.connectedComponentOpens_le_preimage i c g' k
      (chowGroupCongr C hmY.symm k (chowGroupRestrict C (t ≫ sY) ((v ≫ t) ≫ sY) v hvY k α)) =
      0 := by
    have h0 := congrArg (fun d ↦ BivariantClass.cap d g' k
      (chowGroupCongr C hmY.symm k (chowGroupRestrict C (t ≫ sY) ((v ≫ t) ≫ sY) v hvY k α))) hc
    simp only [BivariantClass.zero_cap] at h0
    exact h0
  rw [chowGroupCongr_chowGroupCongr] at hpiece
  have hid : ∀ y : chowGroup C ((v ≫ t) ≫ sY) k, chowGroupCongr C (hmY.symm.trans hmY) k y = y :=
    fun _ ↦ rfl
  rw [hid] at hpiece
  -- `W ⟶ X ×_Y T` factors through the open subscheme `X_i ×_{Y_{a(i)}} T_V`
  have hT : (u ≫ pullback.snd f t) ≫ t =
      (a ≫ f.resConnectedComponent i) ≫ V.ι := by
    simp only [Category.assoc]
    rw [Scheme.Hom.resConnectedComponent_comp_ι, ← Category.assoc a, ha, Category.assoc,
      pullback.condition]
  have hW : a ≫ pieceMap f X.connectedComponentOpens Y.connectedComponentOpens
      f.continuous.connectedComponentsMap f.connectedComponentOpens_le_preimage i =
      pullback.lift _ _ hT ≫ g' := by
    rw [pullback.lift_snd]; rfl
  have hfac : pullback.lift a (pullback.lift _ _ hT) hW ≫
      (pieceComparisonCongr f X.connectedComponentOpens Y.connectedComponentOpens
        f.continuous.connectedComponentsMap f.connectedComponentOpens_le_preimage i g' (v ≫ t) hg' ≫
        baseChangeMapOfEq f t v (v ≫ t) rfl) = u := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, baseChangeMapOfEq_fst, pieceComparisonCongr_fst,
        pullback.lift_fst_assoc, ha]
    · rw [Category.assoc, Category.assoc, baseChangeMapOfEq_snd, pieceComparisonCongr_snd_assoc,
        pullback.lift_snd_assoc, pullback.lift_fst]
  have := isOpenImmersion_of_comp_eq _ _ _ hfac
  have hbase₁ : pullback.lift a (pullback.lift _ _ hT) hW ≫
      (pullback.fst (pieceMap f X.connectedComponentOpens Y.connectedComponentOpens
        f.continuous.connectedComponentsMap f.connectedComponentOpens_le_preimage i) g' ≫
        ((X.connectedComponentOpens i).ι ≫ sX)) = sW := by
    have h2 := congrArg (· ≫ (pullback.fst f t ≫ sX)) hfac
    simp only [Category.assoc, baseChangeMapOfEq_fst_assoc, pieceComparisonCongr_fst_assoc] at h2
    rw [h2, hu]
  calc chowGroupRestrict C (pullback.fst f t ≫ sX) sW u hu (k - p) (c.cap t k α)
      = chowGroupRestrict C _ sW (pullback.lift a (pullback.lift _ _ hT) hW) hbase₁ (k - p)
          (chowGroupRestrict C _ _ (pieceComparisonCongr f X.connectedComponentOpens
            Y.connectedComponentOpens f.continuous.connectedComponentsMap
            f.connectedComponentOpens_le_preimage i g' (v ≫ t) hg')
            (pieceComparisonCongr_comp_structureMorphism _ _ _ _ _ _ _ _ _ sX) (k - p)
            (chowGroupRestrict C _ _ (baseChangeMapOfEq f t v (v ≫ t) rfl)
              (baseChangeMapOfEq_comp_structure sX f t v (v ≫ t) rfl) (k - p)
              (c.cap t k α))) := by
        rw [chowGroupRestrict_comp, chowGroupRestrict_comp]
        exact DFunLike.congr_fun (chowGroupRestrict_congr C _ _ _ _ _ _
          (by rw [Category.assoc, hfac]) _) _
    _ = 0 := by
        rw [hcap, ← hpiece, hzero, map_zero]

variable {Y' : Scheme.{u}} (h : Y' ⟶ Y) [LocallyOfFiniteType h] [IsLocallyNoetherian Y']
  [IsLocallyNoetherian (pullback f h)] (hgys : G.IsNaturalUnderBaseChangeIso)

end Vanishing

/-! ### The restriction on completions -/

section Completed

variable (C : ChowSituation.{u}) {X Y Y' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) (h : Y' ⟶ Y) [LocallyOfFiniteType h] [IsLocallyNoetherian X]
  [IsLocallyNoetherian Y] [IsLocallyNoetherian Y'] [IsLocallyNoetherian (pullback f h)]

/-- The degreewise restriction `∏_p A^p(X ⟶ Y) ⟶ ∏_p A^p(X ×_Y Y' ⟶ Y')` of the tuple attached to
an element of the completed group (Stacks 0FE0), at the Gysin system of the first Chern class
rule. -/
def completedBivariantRestrictionSequence :
    completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf →+
      ∀ n : ℤ, BivariantClass C (gysinSystemOfInvertible C) (pullback.fst f h ≫ sX) (h ≫ sY)
        (pullback.snd f h) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) n :=
  (Pi.addMonoidHom fun n ↦ (bivariantRestrictionAddHom C (gysinSystemOfInvertible C) sX sY f hf
    h n (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)).comp
      (Pi.evalAddMonoidHom _ n)).comp (completedBivariantSequenceOfInvertible C sX sY f hf)

/-- The degreewise restriction of the tuple attached to an element of the completed group still
vanishes in almost all degrees on each connected component of `X ×_Y Y'`: on a component lying
over `X_i` it vanishes wherever the tuple vanishes on `X_i`, by
`Stacks.Chow.bivariantConnectedComponentRestriction_bivariantRestriction_eq_zero`. -/
theorem completedBivariantRestrictionSequence_mem
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf) :
    completedBivariantRestrictionSequence C sX sY f hf h c ∈
      completedBivariantSubgroupOfInvertible C (pullback.fst f h ≫ sX) (h ≫ sY)
        (pullback.snd f h) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) := by
  intro j
  refine (completedBivariantSequence_mem C (gysinSystemOfInvertible C) sX sY f hf
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) c
    ((pullback.fst f h).continuous.connectedComponentsMap j)).subset fun n hn ↦ ?_
  intro hzero
  exact hn (bivariantConnectedComponentRestriction_bivariantRestriction_eq_zero C
    (gysinSystemOfInvertible C) sX sY f hf h n
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) _ j hzero)

/-- **Stacks 0F9Z on completions.** The restriction
`res : A^*(X ⟶ Y)^∧ ⟶ A^*(X ×_Y Y' ⟶ Y')^∧` of completed bivariant classes (Stacks 0FE0) along
`h : Y' ⟶ Y`, at the Gysin system of the first Chern class rule: reading an element of the
completed group as the tuple `(c_p)_p` of Stacks 0FE0, it is the tuple `(res(c_p))_p` of the
restrictions of Stacks 0F9Z, which again vanishes in almost all degrees on each connected
component. -/
@[stacks 0F9Z "the restriction on the completed bivariant groups A^*(X → Y)^∧ → A^*(X' → Y')^∧"]
def completedBivariantRestrictionViaSequence :
    completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf →+
      completedBivariantGroup C (gysinSystemOfInvertible C) (pullback.fst f h ≫ sX) (h ≫ sY)
        (pullback.snd f h) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) :=
  (completedBivariantGroupEquivOfInvertible C (pullback.fst f h ≫ sX) (h ≫ sY)
      (pullback.snd f h)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h)).symm.toAddMonoidHom.comp
    ((completedBivariantRestrictionSequence C sX sY f hf h).codRestrict _
      (completedBivariantRestrictionSequence_mem C sX sY f hf h))

/-- **Stacks 0F9Z on completions, degree by degree.** The degree `n` term of the tuple attached to
`res(c)` (Stacks 0FE0) is the restriction (Stacks 0F9Z) of the degree `n` term of the tuple
attached to `c`. -/
@[simp]
theorem completedBivariantSequenceOfInvertible_completedBivariantRestriction
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf) (n : ℤ) :
    completedBivariantSequenceOfInvertible C (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h)
        (completedBivariantRestrictionViaSequence C sX sY f hf h c) n =
      bivariantRestriction C (gysinSystemOfInvertible C) sX sY f hf h n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (completedBivariantSequenceOfInvertible C sX sY f hf c n) := by
  have h₁ := completedBivariantGroupEquiv_apply C (gysinSystemOfInvertible C)
    (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
    (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h)
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C)
    (completedBivariantRestrictionViaSequence C sX sY f hf h c)
  have h₂ := congrArg Subtype.val ((completedBivariantGroupEquivOfInvertible C
    (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
    (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h)).apply_symm_apply
      ⟨completedBivariantRestrictionSequence C sX sY f hf h c,
        completedBivariantRestrictionSequence_mem C sX sY f hf h c⟩)
  exact congrFun (h₁.symm.trans h₂) n

/-- **Stacks 0F9Z on completions, on connected components.** On the connected component
`X'_j` of `X' = X ×_Y Y'`, the degree `n` part of `res(c)` is the restriction (Stacks 0FDZ) to
`X'_j` of the restriction (Stacks 0F9Z) of the degree `n` term of the tuple attached to `c`. -/
theorem completedBivariantRestriction_apply
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (j : _root_.ConnectedComponents ↥(pullback f h)) (n : ℤ) :
    completedBivariantRestrictionViaSequence C sX sY f hf h c j n =
      bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C)
        (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) n
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (bivariantRestriction C (gysinSystemOfInvertible C) sX sY f hf h n
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (completedBivariantSequenceOfInvertible C sX sY f hf c n)) j := by
  rw [← completedBivariantSequenceOfInvertible_completedBivariantRestriction]
  exact (restriction_completedBivariantSequence C (gysinSystemOfInvertible C) _ _ _ _
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) _ n j).symm

/-- **Stacks 0F9Z on completions, the cap formula.** In every degree `n`, the tuple attached to
`res(c)` caps as the tuple attached to `c`: `res(c)_n ∩ α = c_n ∩ α` for a test scheme
`t : T ⟶ Y'`, after the canonical identification `(X ×_Y Y') ×_{Y'} T ≅ X ×_Y T`. -/
theorem completedBivariantRestriction_cap
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf) (n : ℤ)
    {T : Scheme.{u}} (t : T ⟶ Y') [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ (h ≫ sY)) k) :
    (completedBivariantSequenceOfInvertible C (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h)
        (completedBivariantRestrictionViaSequence C sX sY f hf h c) n).cap t k α =
      chowPushforwardOfIso C (pullback.fst f (t ≫ h) ≫ sX)
        (pullback.fst (pullback.snd f h) t ≫ (pullback.fst f h ≫ sX))
        (pullbackLeftPullbackSndIso f h t).inv (by simp) (k - n)
        ((completedBivariantSequenceOfInvertible C sX sY f hf c n).cap (t ≫ h) k
          (chowGroupCongr C (Category.assoc t h sY).symm k α)) := by
  rw [completedBivariantSequenceOfInvertible_completedBivariantRestriction,
    bivariantRestriction_cap, bivariantRestrictionCap_apply]

end Completed

/-! ### Restriction composed with flat pullback, on a connected component -/

/-- The restriction of a flat morphism to a connected component of its source is flat. -/
instance flat_resConnectedComponent {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (a : _root_.ConnectedComponents X) :
    Flat (f.resConnectedComponent a) :=
  inferInstanceAs (Flat (f.resLE _ _ _))

section ComponentFlatCommute

variable (C : ChowSituation.{u}) {X P P' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (i : X ⟶ P) [LocallyOfFiniteType i]
  (hi : i ≫ sP = sX) (p : P' ⟶ P) [LocallyOfFiniteType p] [Flat p] [IsLocallyNoetherian X]
  [IsLocallyNoetherian P] [IsLocallyNoetherian P'] [IsLocallyNoetherian (pullback i p)] (q : ℤ)

/-- **`res(c) ∘ p^* = p̄^* ∘ c` on a connected component.** Let `X'_w` be a connected component
of `X' = X ×_P P'`, lying over the components `X_a` of `X` and `P'_b` of `P'`, and let
`ψ : P'_b ⟶ P_j` be a restriction of `p` into the component `P_j` that `X_a` lands in, flat of
relative dimension `r`, the restriction `X'_w ⟶ X_a` of the base change of `p` having the same
relative dimension. Then the restriction to `X'_w` (Stacks 0FDZ) of `res(c)` (Stacks 0F9Z),
composed with `ψ^*` (Stacks 0B78), is `(X'_w ⟶ X_a)^*` composed with the restriction of `c` to
`X_a`. Both cap, on a test scheme over `P_j`, by restricting to an open subscheme the flat
pullback of `c ∩ α` along one base change of `p`: this is Stacks 0B76 (2) for `c`. -/
theorem bivariantCompositeOfInvertible_connectedComponentRestriction_flatPullback
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sP i hi q)
    (w : _root_.ConnectedComponents ↥(pullback i p))
    (ψ : (P'.connectedComponentOpens ((pullback.snd i p).continuous.connectedComponentsMap w) :
        Scheme.{u}) ⟶ (P.connectedComponentOpens (i.continuous.connectedComponentsMap
          ((pullback.fst i p).continuous.connectedComponentsMap w)) : Scheme.{u}))
    [LocallyOfFiniteType ψ] [Flat ψ]
    (hψ : ψ ≫ (P.connectedComponentOpens (i.continuous.connectedComponentsMap
          ((pullback.fst i p).continuous.connectedComponentsMap w))).ι =
      (P'.connectedComponentOpens ((pullback.snd i p).continuous.connectedComponentsMap w)).ι ≫ p)
    (hψs : ψ ≫ ((P.connectedComponentOpens (i.continuous.connectedComponentsMap
          ((pullback.fst i p).continuous.connectedComponentsMap w))).ι ≫ sP) =
      (P'.connectedComponentOpens ((pullback.snd i p).continuous.connectedComponentsMap w)).ι ≫
        (p ≫ sP))
    (r : ℕ) (hψr : AlgebraicGeometry.RelativeDimension ψ r)
    (hφr : AlgebraicGeometry.RelativeDimension ((pullback.fst i p).resConnectedComponent w) r) :
    bivariantCompositeOfInvertible C _ _ _ ((pullback.snd i p).resConnectedComponent w) ψ
        ((pullback.snd i p).resConnectedComponent_comp_ι_comp
          (pullbackSnd_comp_structureMorphism_eq C sX sP i hi p) w) hψs q (-(r : ℤ))
        (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C)
          (pullback.fst i p ≫ sX) (p ≫ sP) (pullback.snd i p)
          (pullbackSnd_comp_structureMorphism_eq C sX sP i hi p) q
          (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
          (bivariantRestriction C (gysinSystemOfInvertible C) sX sP i hi p q
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c) w)
        (flatPullbackBivariantClassOfInvertible C _ _ ψ hψs r hψr) ≍
      bivariantCompositeOfInvertible C _ _ _ ((pullback.fst i p).resConnectedComponent w)
        (i.resConnectedComponent ((pullback.fst i p).continuous.connectedComponentsMap w))
        ((pullback.fst i p).resConnectedComponent_comp_ι_comp (rfl : pullback.fst i p ≫ sX = _) w)
        (i.resConnectedComponent_comp_ι_comp hi _) (-(r : ℤ)) q
        (flatPullbackBivariantClassOfInvertible C _ _ ((pullback.fst i p).resConnectedComponent w)
            ((pullback.fst i p).resConnectedComponent_comp_ι_comp
              (rfl : pullback.fst i p ≫ sX = _) w)
            r hφr)
        (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sP i hi q
          (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) c
          ((pullback.fst i p).continuous.connectedComponentsMap w)) := by
  have hff : (pullback.snd i p).resConnectedComponent w ≫ ψ =
      (pullback.fst i p).resConnectedComponent w ≫
        i.resConnectedComponent ((pullback.fst i p).continuous.connectedComponentsMap w) := by
    rw [← cancel_mono (P.connectedComponentOpens _).ι, Category.assoc, hψ, Category.assoc,
      Scheme.Hom.resConnectedComponent_comp_ι, Scheme.Hom.resConnectedComponent_comp_ι_assoc,
      Scheme.Hom.resConnectedComponent_comp_ι_assoc, pullback.condition]
  refine BivariantClass.heq_of_congrHom_cap_heq hff (by ring) _ _ ?_
  intro T t _ k α
  -- the base change of `ψ` to the test scheme, and Stacks 0B76 (2) for `c` along it
  have e : pullback.snd ψ t ≫ (t ≫ (P.connectedComponentOpens (i.continuous.connectedComponentsMap
      ((pullback.fst i p).continuous.connectedComponentsMap w))).ι) =
      (pullback.fst ψ t ≫ (P'.connectedComponentOpens
        ((pullback.snd i p).continuous.connectedComponentsMap w)).ι) ≫ p := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, hψ, Category.assoc]
  have sq := isPullback_baseChangeMapOfEq i _ (pullback.snd ψ t) _ e
  have hrt : AlgebraicGeometry.RelativeDimension (pullback.snd ψ t) r :=
    relativeDimension_pullbackSnd ψ hψr t
  obtain ⟨_, _, hr'⟩ := isPullback_locallyOfFiniteType_flat_relativeDimension sq hrt
  have hqY : pullback.snd ψ t ≫ ((t ≫ (P.connectedComponentOpens
      (i.continuous.connectedComponentsMap
        ((pullback.fst i p).continuous.connectedComponentsMap w))).ι) ≫ sP) =
      ((pullback.fst ψ t ≫ (P'.connectedComponentOpens
        ((pullback.snd i p).continuous.connectedComponentsMap w)).ι) ≫ p) ≫ sP := by
    rw [← Category.assoc, e]
  have hflat := BivariantClass.flat_naturality_of_eq C (gysinSystemOfInvertible C) sX sP i hi q c
    _ (pullback.snd ψ t) _ e r hrt (baseChangeMapOfEq i _ (pullback.snd ψ t) _ e) sq
    (baseChangeMapOfEq_fst i _ (pullback.snd ψ t) _ e) k hqY hr'
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (chowGroupCongr C (Category.assoc _ _ _).symm k α)
  -- the open immersion through which the left side restricts
  have huL : (((pullbackRightPullbackFstIso ψ t ((pullback.snd i p).resConnectedComponent w)).inv ≫
      opensPullbackComparison (pullback.snd i p) ((pullback i p).connectedComponentOpens w)
        (P'.connectedComponentOpens ((pullback.snd i p).continuous.connectedComponentsMap w))
        ((pullback.snd i p).resConnectedComponent w)
        ((pullback.snd i p).resConnectedComponent_comp_ι w) (pullback.fst ψ t)) ≫
      (pullbackLeftPullbackSndIso i p (pullback.fst ψ t ≫ (P'.connectedComponentOpens
        ((pullback.snd i p).continuous.connectedComponentsMap w)).ι)).hom) ≫
      (pullback.fst i ((pullback.fst ψ t ≫ (P'.connectedComponentOpens
        ((pullback.snd i p).continuous.connectedComponentsMap w)).ι) ≫ p) ≫ sX) =
      pullback.fst ((pullback.snd i p).resConnectedComponent w ≫ ψ) t ≫
        (((pullback i p).connectedComponentOpens w).ι ≫ (pullback.fst i p ≫ sX)) := by
    simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_fst_assoc,
      opensPullbackComparison_fst_assoc, pullbackRightPullbackFstIso_inv_fst_assoc]
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring : k - (q + -(r : ℤ)) = (k - q) + r) _
    (chowGroupRestrict C _ _ _ huL ((k - q) + (r : ℤ))
      (flatPullbackChow C _ _ (baseChangeMapOfEq i _ (pullback.snd ψ t) _ e)
        (baseChangeMapOfEq_comp_structure sX i _ _ _ e) r hr' (k - q)
        (flatPullbackDescends C _ _ _ _ _ _ _)
        (c.cap _ k (chowGroupCongr C (Category.assoc _ _ _).symm k α)))) ?_).trans ?_
  · rw [bivariantCompositeOfInvertible, bivariantComposite_cap]
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    simp only [bivariantCompositeCap_apply, properChowPushforward_eq_chowPushforwardOfIso,
      bivariantConnectedComponentRestriction_cap, bivariantRestriction_cap,
      bivariantRestrictionCap_apply, chowPushforwardOfIso_iso_inv_eq_chowGroupRestrict,
      chowPushforwardOfIso_hom_eq_chowGroupRestrict, chowGroupRestrict_comp]
    refine chowGroupRestrict_heq_of_heq C _ _ _ _ (by ring) _ _ ?_
    refine (c.cap_heq_congr _ (by ring) _ _ ?_).trans hflat
    refine (chowGroupCongr_heq C _ _ _).trans ((chowGroupCongr_heq C _ _ _).trans ?_)
    refine (flatPullbackBivariantCap_heq C _ _ ψ hψs r hψr (flatPullbackDescends C) t k α).trans ?_
    exact flatPullbackChow_heq_congr_base C (by simp only [Category.assoc])
      (Category.assoc _ _ _).symm rfl _ _ rfl _ _ rfl _ _ α _ (chowGroupCongr_heq C _ _ _).symm
  · refine HEq.symm ((isBivariantClassComposition_bivariantCompositeOfInvertible C _ _ _ _ _ _ _ _ _
      _ _ t k α).trans ?_)
    simp only [bivariantCompositeCap_apply, properChowPushforward_eq_chowPushforwardOfIso,
      bivariantConnectedComponentRestriction_cap]
    refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring : (k - q) - -(r : ℤ) = (k - q) + r)
      _ _ (flatPullbackBivariantCap_heq C
        (((pullback i p).connectedComponentOpens w).ι ≫ (pullback.fst i p ≫ sX))
        ((X.connectedComponentOpens ((pullback.fst i p).continuous.connectedComponentsMap w)).ι ≫
          sX) ((pullback.fst i p).resConnectedComponent w)
        ((pullback.fst i p).resConnectedComponent_comp_ι_comp (rfl : pullback.fst i p ≫ sX = _) w)
        r hφr (flatPullbackDescends C) (pullback.fst (i.resConnectedComponent
          ((pullback.fst i p).continuous.connectedComponentsMap w)) t) (k - q)
        (chowGroupRestrict C _ _ (opensPullbackComparison i
          (X.connectedComponentOpens ((pullback.fst i p).continuous.connectedComponentsMap w))
          (P.connectedComponentOpens (i.continuous.connectedComponentsMap
            ((pullback.fst i p).continuous.connectedComponentsMap w)))
          (i.resConnectedComponent ((pullback.fst i p).continuous.connectedComponentsMap w))
          (i.resConnectedComponent_comp_ι _) t)
          (by rw [← Category.assoc, opensPullbackComparison_fst, Category.assoc]) (k - q)
          (c.cap _ k (chowGroupCongr C (Category.assoc _ _ _).symm k α))))).trans ?_
    -- the comparison `X'_w ×_{P_j} T ⟶ X ×_P T` that both sides factor through
    have hΘ : (pullback.fst ((pullback.fst i p).resConnectedComponent w ≫
        i.resConnectedComponent ((pullback.fst i p).continuous.connectedComponentsMap w)) t ≫
        ((pullback i p).connectedComponentOpens w).ι ≫ pullback.fst i p) ≫ i =
        pullback.snd ((pullback.fst i p).resConnectedComponent w ≫
          i.resConnectedComponent ((pullback.fst i p).continuous.connectedComponentsMap w)) t ≫
          (t ≫ (P.connectedComponentOpens (i.continuous.connectedComponentsMap
            ((pullback.fst i p).continuous.connectedComponentsMap w))).ι) := by
      rw [← pullback.condition_assoc]
      simp only [Category.assoc, Scheme.Hom.resConnectedComponent_comp_ι,
        Scheme.Hom.resConnectedComponent_comp_ι_assoc]
    refine heq_of_eq (chowPushforwardOfIso_chowGroupRestrict_flatPullbackChow_eq C _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ (pullback.lift _ _ hΘ) ?_ ?_ r hr' _ (k - q) _).symm
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, baseChangeMapOfEq_fst,
          pullbackLeftPullbackSndIso_hom_fst, opensPullbackComparison_fst_assoc,
          pullbackRightPullbackFstIso_inv_fst_assoc, pullback.congrHom_hom, pullback.lift_fst_assoc,
          Category.id_comp]
      · simp only [Category.assoc, pullback.lift_snd, baseChangeMapOfEq_snd,
          pullbackLeftPullbackSndIso_hom_snd_assoc, opensPullbackComparison_snd_assoc,
          pullbackRightPullbackFstIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd,
          Category.comp_id]
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, opensPullbackComparison_fst,
          pullbackRightPullbackFstIso_hom_fst_assoc]
        rw [← pullback.condition_assoc, Scheme.Hom.resConnectedComponent_comp_ι]
      · simp only [Category.assoc, pullback.lift_snd, opensPullbackComparison_snd,
          pullbackRightPullbackFstIso_hom_snd]

end ComponentFlatCommute

/-! ### Relative dimensions of the base change of a smooth morphism on components -/

section SmoothComponent

variable {X P P' : Scheme.{u}} (i : X ⟶ P) (p : P' ⟶ P) [LocallyOfFiniteType p] [Smooth p]
  [IsLocallyNoetherian X] [IsLocallyNoetherian P] [IsLocallyNoetherian P']
  [IsLocallyNoetherian (pullback i p)]

/-- The restriction `X'_w ⟶ X_a` of the base change `X' = X ×_P P' ⟶ X` of a smooth morphism `p`
to a connected component `X'_w` has the relative dimension of `p` on the connected component
`P'_b` of `P'` that `X'_w` lands in: it is an open restriction of the base change of `P'_b ⟶ P`
(Stacks 02NK). -/
theorem relativeDimension_resConnectedComponent_pullbackFst
    (w : _root_.ConnectedComponents ↥(pullback i p)) :
    AlgebraicGeometry.RelativeDimension ((pullback.fst i p).resConnectedComponent w)
      (smoothComponentRelativeDimension p
        ((pullback.snd i p).continuous.connectedComponentsMap w)) := by
  set b := (pullback.snd i p).continuous.connectedComponentsMap w
  set ιb := (P'.connectedComponentOpens b).ι
  have hb : AlgebraicGeometry.RelativeDimension (ιb ≫ p)
      (smoothComponentRelativeDimension p b) := by
    have h := AlgebraicGeometry.RelativeDimension.comp_of_flat (p.resConnectedComponent b) _
      (relativeDimension_smoothComponentRelativeDimension p b)
      (relativeDimension_of_isOpenImmersion
        (P.connectedComponentOpens (p.continuous.connectedComponentsMap b)).ι)
    rw [Nat.add_zero] at h
    exact AlgebraicGeometry.RelativeDimension.of_comp_isOpenImmersion _ (𝟙 P) _
      (by rw [Category.comp_id, Scheme.Hom.resConnectedComponent_comp_ι]) h
  have hfst : AlgebraicGeometry.RelativeDimension (pullback.fst i (ιb ≫ p))
      (smoothComponentRelativeDimension p b) :=
    AlgebraicGeometry.RelativeDimension.of_isPullback (IsPullback.of_hasPullback i (ιb ≫ p)).flip hb
  -- `X'_w` is an open subscheme of `X ×_P P'_b`
  have hκ : (((pullback i p).connectedComponentOpens w).ι ≫ pullback.fst i p) ≫ i =
      (pullback.snd i p).resConnectedComponent w ≫ ιb ≫ p := by
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      ← Scheme.Hom.resConnectedComponent_comp_ι, Category.assoc]
  have sq := isPullback_baseChangeMapOfEq i p ιb (ιb ≫ p) rfl
  have : IsOpenImmersion (baseChangeMapOfEq i p ιb (ιb ≫ p) rfl) :=
    MorphismProperty.of_isPullback sq (P := @IsOpenImmersion) inferInstance
  have hκι : pullback.lift _ _ hκ ≫ baseChangeMapOfEq i p ιb (ιb ≫ p) rfl =
      ((pullback i p).connectedComponentOpens w).ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeMapOfEq_fst, pullback.lift_fst]
    · rw [Category.assoc, baseChangeMapOfEq_snd, pullback.lift_snd_assoc,
        Scheme.Hom.resConnectedComponent_comp_ι]
  have := isOpenImmersion_of_comp_eq _ _ _ hκι
  have hcomp := hfst.comp_isOpenImmersion (pullback.lift _ _ hκ) (pullback.fst i (ιb ≫ p))
  exact AlgebraicGeometry.RelativeDimension.of_comp_isOpenImmersion _ _ _
    (Scheme.Hom.resConnectedComponent_comp_ι _ w)
    (AlgebraicGeometry.RelativeDimension.of_comp_isOpenImmersion _ (𝟙 X) _
      (by rw [Category.comp_id, pullback.lift_fst]) hcomp)

/-- The relative dimension of the base change `X ×_P P' ⟶ X` of a smooth morphism `p` on a
connected component `X'_w` is that of `p` on the connected component of `P'` it lands in. -/
theorem smoothComponentRelativeDimension_pullbackFst
    (w : _root_.ConnectedComponents ↥(pullback i p)) :
    smoothComponentRelativeDimension (pullback.fst i p) w =
      smoothComponentRelativeDimension p ((pullback.snd i p).continuous.connectedComponentsMap w) :=
  (relativeDimension_smoothComponentRelativeDimension (pullback.fst i p) w).eq_of_nonempty
    (relativeDimension_resConnectedComponent_pullbackFst i p w)

end SmoothComponent

/-! ### The composite on completions against a homogeneous factor -/

section HomogeneousFactor

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX)
  (hg : g ≫ sZ = sY) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]

/-- **The composite on completions against a right factor concentrated in one degree.** If the
completed class `d` is concentrated in degree `q` on the component `Y_{a(w)}` that `X_w` lands in,
then in degree `n` on `X_w` the composite `c ∘ d` (Stacks 0FE0) is the composite of Stacks 0B75 of
the degree `n - q` part of `c` with that homogeneous part of `d`. -/
theorem completedBivariantCompositeOfInvertible_apply_heq_of_right
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (d : completedBivariantGroup C (gysinSystemOfInvertible C) sY sZ g hg)
    (w : _root_.ConnectedComponents X) (q : ℤ) (y)
    (hd : d (f.continuous.connectedComponentsMap w) = DirectSum.of _ q y) (n : ℤ) :
    completedBivariantCompositeOfInvertible C sX sY sZ f g hf hg c d w n ≍
      bivariantCompositeOfInvertible C _ _ _ (f.resConnectedComponent w)
        (g.resConnectedComponent (f.continuous.connectedComponentsMap w))
        (f.resConnectedComponent_comp_ι_comp hf w) (g.resConnectedComponent_comp_ι_comp hg _)
        (n - q) q (c w (n - q)) y := by
  rw [completedBivariantCompositeOfInvertible, completedBivariantComposite_apply,
    DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_apply, hd]
  exact (bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ n _).trans
    (directSumBilinear_of_apply_heq _ _ _ _ n)

/-- **The composite on completions against a left factor concentrated in one degree.** If the
completed class `c` is concentrated in degree `p` on the component `X_w`, then in degree `n` on
`X_w` the composite `c ∘ d` (Stacks 0FE0) is the composite of Stacks 0B75 of that homogeneous part
of `c` with the degree `n - p` part of `d` on the component `Y_{a(w)}`. -/
theorem completedBivariantCompositeOfInvertible_apply_heq_of_left
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (d : completedBivariantGroup C (gysinSystemOfInvertible C) sY sZ g hg)
    (w : _root_.ConnectedComponents X) (p : ℤ) (x) (hc : c w = DirectSum.of _ p x) (n : ℤ) :
    completedBivariantCompositeOfInvertible C sX sY sZ f g hf hg c d w n ≍
      bivariantCompositeOfInvertible C _ _ _ (f.resConnectedComponent w)
        (g.resConnectedComponent (f.continuous.connectedComponentsMap w))
        (f.resConnectedComponent_comp_ι_comp hf w) (g.resConnectedComponent_comp_ι_comp hg _)
        p (n - p) x (d (f.continuous.connectedComponentsMap w) (n - p)) := by
  rw [completedBivariantCompositeOfInvertible, completedBivariantComposite_apply,
    DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_apply, hc]
  exact (bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ n _).trans
    (directSumBilinear_of_left_apply_heq _ _ _ _ n)

end HomogeneousFactor

/-! ### Bivariant classes commute with flat pullback, on completions -/

section CompletedFlatCommute

variable (C : ChowSituation.{u}) {X P P' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (i : X ⟶ P) [LocallyOfFiniteType i]
  (hi : i ≫ sP = sX) (p : P' ⟶ P) [LocallyOfFiniteType p] [Smooth p] [IsLocallyNoetherian X]
  [IsLocallyNoetherian P] [IsLocallyNoetherian P'] [IsLocallyNoetherian (pullback i p)]

/-- **`res(c) ∘ p^* = p̄^* ∘ c` on completions.** For a completed bivariant class
`c ∈ A^*(X ⟶ P)^∧` (Stacks 0FE0) and a smooth morphism `p : P' ⟶ P`, the restriction
`res(c) ∈ A^*(X ×_P P' ⟶ P')^∧` of `c` along `p` (Stacks 0F9Z) composed with the flat pullback
`p^* ∈ A^*(P' ⟶ P)^∧` is the flat pullback along the base change `X ×_P P' ⟶ X` of `p`
composed with `c`. The two sides are completed classes for the equal morphisms
`X ×_P P' ⟶ P' ⟶ P` and `X ×_P P' ⟶ X ⟶ P`, whence the heterogeneous equality. On a connected
component of `X ×_P P'` and in each degree this is
`Stacks.Chow.bivariantCompositeOfInvertible_connectedComponentRestriction_flatPullback`. This is
the identity `j^! ∘ p^* = p̄^* ∘ i^!` used in the proof of Stacks 0FF2, read for an arbitrary
completed class in place of `i^!`. -/
theorem completedBivariantRestriction_composite_completedFlatPullbackOfSmooth
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sP i hi) :
    completedBivariantCompositeOfInvertible C (pullback.fst i p ≫ sX) (p ≫ sP) sP
        (pullback.snd i p) p (pullbackSnd_comp_structureMorphism_eq C sX sP i hi p) rfl
        (completedBivariantRestrictionViaSequence C sX sP i hi p c)
        (completedFlatPullbackOfSmooth C (p ≫ sP) sP p rfl) ≍
      completedBivariantCompositeOfInvertible C (pullback.fst i p ≫ sX) sX sP (pullback.fst i p) i
        rfl hi (completedFlatPullbackOfSmooth C (pullback.fst i p ≫ sX) sX (pullback.fst i p) rfl)
        c := by
  refine completedBivariantGroup_heq_of_apply_heq C pullback.condition.symm _ _ fun w n ↦ ?_
  refine (completedBivariantCompositeOfInvertible_apply_heq_of_right C _ _ _ _ _ _ _ _ _ w _ _
    (completedFlatPullbackOfSmooth_apply C (p ≫ sP) sP p rfl _) n).trans
    (HEq.trans ?_ (completedBivariantCompositeOfInvertible_apply_heq_of_left C _ _ _ _ _ _ _ _ _ w
      _ _ (completedFlatPullbackOfSmooth_apply C _ sX (pullback.fst i p) rfl w) n).symm)
  rw [completedBivariantRestriction_apply, ← restriction_completedBivariantSequence C
    (gysinSystemOfInvertible C) sX sP i hi (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) c]
  -- the restriction of `p` into the component of `P` that `X'_w` lands in through `X`
  have he : p.continuous.connectedComponentsMap
      ((pullback.snd i p).continuous.connectedComponentsMap w) =
      i.continuous.connectedComponentsMap
        ((pullback.fst i p).continuous.connectedComponentsMap w) := by
    rw [← Scheme.Hom.connectedComponentsMap_comp, ← Scheme.Hom.connectedComponentsMap_comp,
      pullback.condition]
  have hle : P'.connectedComponentOpens ((pullback.snd i p).continuous.connectedComponentsMap w) ≤
      p ⁻¹ᵁ P.connectedComponentOpens (i.continuous.connectedComponentsMap
        ((pullback.fst i p).continuous.connectedComponentsMap w)) := by
    rw [← he]; exact p.connectedComponentOpens_le_preimage _
  have hψ : p.resLE _ _ hle ≫ (P.connectedComponentOpens (i.continuous.connectedComponentsMap
      ((pullback.fst i p).continuous.connectedComponentsMap w))).ι =
      (P'.connectedComponentOpens ((pullback.snd i p).continuous.connectedComponentsMap w)).ι ≫ p :=
    Scheme.Hom.resLE_comp_ι _ _
  have hψs : p.resLE _ _ hle ≫ ((P.connectedComponentOpens (i.continuous.connectedComponentsMap
      ((pullback.fst i p).continuous.connectedComponentsMap w))).ι ≫ sP) =
      (P'.connectedComponentOpens ((pullback.snd i p).continuous.connectedComponentsMap w)).ι ≫
        (p ≫ sP) := by
    rw [← Category.assoc, hψ, Category.assoc]
  have hψheq : p.resLE _ _ hle ≍
      p.resConnectedComponent ((pullback.snd i p).continuous.connectedComponentsMap w) :=
    Scheme.Hom.heq_of_comp_connectedComponentOpens_ι he.symm _ _
      (by rw [hψ, Scheme.Hom.resConnectedComponent_comp_ι])
  have hr := smoothComponentRelativeDimension_pullbackFst i p w
  have hψr : AlgebraicGeometry.RelativeDimension (p.resLE _ _ hle)
      (smoothComponentRelativeDimension (pullback.fst i p) w) := by
    refine relativeDimension_of_heq_component he.symm _ _ hψheq ?_
    rw [hr]
    exact relativeDimension_smoothComponentRelativeDimension p _
  -- replace `P'_b ⟶ P_{p(b)}` by the restriction of `p` into the component `X'_w` lands in
  have key : ∀ (s₁ s₂ : ℕ) (hs : s₁ = s₂)
      (h₁ : AlgebraicGeometry.RelativeDimension
        (p.resConnectedComponent ((pullback.snd i p).continuous.connectedComponentsMap w)) s₁)
      (h₂ : AlgebraicGeometry.RelativeDimension (p.resLE _ _ hle) s₂),
      bivariantCompositeOfInvertible C _ _ _ ((pullback.snd i p).resConnectedComponent w)
          (p.resConnectedComponent ((pullback.snd i p).continuous.connectedComponentsMap w))
          ((pullback.snd i p).resConnectedComponent_comp_ι_comp
            (pullbackSnd_comp_structureMorphism_eq C sX sP i hi p) w)
          (p.resConnectedComponent_comp_ι_comp rfl _) (n - -(s₁ : ℤ)) (-(s₁ : ℤ))
          (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C)
            (pullback.fst i p ≫ sX) (p ≫ sP) (pullback.snd i p)
            (pullbackSnd_comp_structureMorphism_eq C sX sP i hi p) (n - -(s₁ : ℤ))
            (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
            (bivariantRestriction C (gysinSystemOfInvertible C) sX sP i hi p (n - -(s₁ : ℤ))
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
              (completedBivariantSequenceOfInvertible C sX sP i hi c (n - -(s₁ : ℤ)))) w)
          (flatPullbackBivariantClassOfInvertible C _ _
              (p.resConnectedComponent ((pullback.snd i p).continuous.connectedComponentsMap w))
              (p.resConnectedComponent_comp_ι_comp rfl _) s₁ h₁) ≍
        bivariantCompositeOfInvertible C _ _ _ ((pullback.snd i p).resConnectedComponent w)
          (p.resLE _ _ hle)
          ((pullback.snd i p).resConnectedComponent_comp_ι_comp
            (pullbackSnd_comp_structureMorphism_eq C sX sP i hi p) w) hψs
          (n - -(s₂ : ℤ)) (-(s₂ : ℤ))
          (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C)
            (pullback.fst i p ≫ sX) (p ≫ sP) (pullback.snd i p)
            (pullbackSnd_comp_structureMorphism_eq C sX sP i hi p) (n - -(s₂ : ℤ))
            (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
            (bivariantRestriction C (gysinSystemOfInvertible C) sX sP i hi p (n - -(s₂ : ℤ))
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
              (completedBivariantSequenceOfInvertible C sX sP i hi c (n - -(s₂ : ℤ)))) w)
          (flatPullbackBivariantClassOfInvertible C _ _ (p.resLE _ _ hle) hψs s₂ h₂) := by
    intro s₁ s₂ hs h₁ h₂
    subst hs
    exact bivariantCompositeOfInvertible_heq_of_target_component C _ sP
      ((P'.connectedComponentOpens ((pullback.snd i p).continuous.connectedComponentsMap w)).ι ≫
        (p ≫ sP)) _ _ he _ _ hψheq.symm _ _ _ _ _ _ _
      (flatPullbackBivariantClass_heq_of_component C _ sP he _ _ hψheq.symm _ _ rfl _ _)
  refine (key _ _ hr.symm _ hψr).trans ?_
  exact bivariantCompositeOfInvertible_connectedComponentRestriction_flatPullback C sX sP i hi p _
    _ w _ hψ hψs _ hψr (relativeDimension_smoothComponentRelativeDimension (pullback.fst i p) w)

end CompletedFlatCommute

end Stacks.Chow

end
