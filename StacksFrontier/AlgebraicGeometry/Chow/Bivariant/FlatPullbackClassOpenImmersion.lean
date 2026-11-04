module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceGysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent

/-!
# Flat pullback along an open immersion as a bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `j : U ⟶ X` be an
open immersion of schemes locally of finite type over `S`. An open immersion is flat of relative
dimension `0`, so **Stacks 0B78** makes flat pullback `j^*` a bivariant class
`j^* ∈ A^0(U ⟶ X)`: on a test scheme `T ⟶ X` it restricts a cycle class on `T` to the open
subscheme `U ×_X T`.

`Stacks.Chow.flatPullbackBivariantClass` constructs the class of Stacks 0B78 for an arbitrary
flat morphism, carrying Stacks 02RG and Stacks 0B71 as hypotheses. For an open immersion both
inputs are theorems of this repository, and this file assembles the class with nothing assumed:

* the proper-pushforward law is the open-immersion case of Stacks 02RG,
  `Stacks.Chow.chowGroupRestrict_properChowPushforward`, flat pullback along an open immersion
  being restriction (`Stacks.Chow.heq_chowGroupRestrict_flatPullbackChow`);
* the flat-pullback law is Stacks 02RD, `Stacks.Chow.flatPullbackBivariantCap_flat_naturality`,
  which assumes nothing;
* the Gysin law is the open-immersion case of Stacks 0B71 for a Gysin system,
  `Stacks.Chow.GysinSystem.IsNaturalUnderOpensRestriction`, which is a theorem at the Gysin system
  of the first Chern class rule
  (`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpensRestriction`).

The cap operation is literally the one of Stacks 0B78, `Stacks.Chow.flatPullbackBivariantCap` at
relative dimension `0`, so the class satisfies the characterization
`Stacks.Chow.IsBivariantFlatPullback` of that tag by `rfl`: this is the class of Stacks 0B78 for an
open immersion, not a second construction.

## Main definitions

* `Stacks.Chow.flatPullbackBivariantClassOfIsOpenImmersion` — **Stacks 0B78** for an open
  immersion, at a Gysin system natural under restriction to opens.
* `Stacks.Chow.flatPullbackBivariantClassOfIsOpenImmersionOfInvertible` — **Stacks 0B78** for an
  open immersion at the Gysin system of the first Chern class rule, with nothing assumed.

## References

* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section OpenImmersion

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [IsOpenImmersion f] (hf : f ≫ sY = sX)

/-- The cap operation of Stacks 0B78 along an open immersion is restriction to the open subscheme
`X ×_Y T` of the test scheme, up to the transport of the degree from `k` to `k - -0`. -/
theorem flatPullbackBivariantCap_heq_chowGroupRestrict {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    flatPullbackBivariantCap C sX sY f hf 0 (relativeDimension_of_isOpenImmersion f)
        (flatPullbackDescends C) g k α ≍
      chowGroupRestrict C (g ≫ sY) (pullback.fst f g ≫ sX) (pullback.snd f g)
        (pullbackSnd_comp_structureMorphism hf g) k α :=
  (flatPullbackBivariantCap_heq C sX sY f hf 0 (relativeDimension_of_isOpenImmersion f)
      (flatPullbackDescends C) g k α).trans
    (heq_chowGroupRestrict_flatPullbackChow C (g ≫ sY) (pullback.fst f g ≫ sX)
      (pullback.snd f g) (pullbackSnd_comp_structureMorphism hf g)
      (relativeDimension_pullback_snd f g 0 (relativeDimension_of_isOpenImmersion f)) k
      (flatPullbackDescends C _ _ _ _ _ _ _) α).symm

/-- **Stacks 02RG for an open immersion.** The proper-pushforward law of Stacks 0B76 (1) for the
cap operation of Stacks 0B78 along an open immersion: restriction to the open subscheme commutes
with proper pushforward. This is `Stacks.Chow.chowGroupRestrict_properChowPushforward`. -/
theorem flatPullbackBivariantCap_proper_naturality_of_isOpenImmersion {T T' : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h]
    (h' : pullback f (h ≫ g) ⟶ pullback f g) [IsProper h']
    (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sY) (g ≫ sY) h
      (by simp [Category.assoc]) k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
      (by rw [← Category.assoc, hfst]) (k - -((0 : ℕ) : ℤ)))
    (α : chowGroup C ((h ≫ g) ≫ sY) k) :
    flatPullbackBivariantCap C sX sY f hf 0 (relativeDimension_of_isOpenImmersion f)
        (flatPullbackDescends C) g k
        (properChowPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) k hfac
          α) =
      properChowPushforward C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
        (by rw [← Category.assoc, hfst]) (k - -((0 : ℕ) : ℤ)) hfac'
        (flatPullbackBivariantCap C sX sY f hf 0 (relativeDimension_of_isOpenImmersion f)
          (flatPullbackDescends C) (h ≫ g) k α) := by
  have hdeg : k = k - -((0 : ℕ) : ℤ) := by simp
  have hfac'' : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
      (by rw [← Category.assoc, hfst]) k :=
    properPushforwardFactorsThroughRationalEquivalence C _ _ h' _ k
  have hrg := chowGroupRestrict_properChowPushforward C ((h ≫ g) ≫ sY) (g ≫ sY)
    (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h (by simp [Category.assoc])
    (pullback.snd f (h ≫ g)) (pullbackSnd_comp_structureMorphism hf (h ≫ g))
    (pullback.snd f g) (pullbackSnd_comp_structureMorphism hf g) h'
    (by rw [← Category.assoc, hfst]) sq k hfac hfac'' α
  refine eq_of_heq ((flatPullbackBivariantCap_heq_chowGroupRestrict C sX sY f hf g k _).trans
    ((heq_of_eq hrg).trans ?_))
  exact properChowPushforward_heq_congr C _ _ h' _ hdeg hfac'' hfac' _ _
    (flatPullbackBivariantCap_heq_chowGroupRestrict C sX sY f hf (h ≫ g) k α).symm

/-- **Stacks 0B71 for an open immersion.** The Gysin law of Stacks 0B76 (3) for the cap operation
of Stacks 0B78 along an open immersion, at a Gysin system natural under restriction to opens:
restriction to the open subscheme commutes with the Gysin map of the zero scheme of a section of
an invertible module on a test scheme. -/
theorem flatPullbackBivariantCap_gysin_naturality_of_isOpenImmersion
    (hgysR : G.IsNaturalUnderOpensRestriction)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback f g).sheaf.obj
      (pullback f g).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd f g)).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ)
    (e : pullback f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≅
      (Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subscheme)
    (he : e.hom ≫ (Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι =
      bivariantBaseChangeMap f g (Stacks.Divisors.zeroScheme T L s).subschemeι)
    (hbase : e.hom ≫ ((Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
        pullback.fst f g ≫ sX) =
      pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
      ((Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
        pullback.fst f g ≫ sX) e.hom hbase (k - -((0 : ℕ) : ℤ)))
    (α : chowGroup C (g ≫ sY) (k + 1)) :
    properChowPushforward C
        (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
        ((Stacks.Divisors.zeroScheme (pullback f g)
          ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
          pullback.fst f g ≫ sX) e.hom hbase (k - -((0 : ℕ) : ℤ)) hfac
        (flatPullbackBivariantCap C sX sY f hf 0 (relativeDimension_of_isOpenImmersion f)
          (flatPullbackDescends C) ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k
          (G.onChow (g ≫ sY) L s k α)) =
      G.onChow (pullback.fst f g ≫ sX)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s) (k - -((0 : ℕ) : ℤ))
        (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
          (by omega : k + 1 - -((0 : ℕ) : ℤ) = k - -((0 : ℕ) : ℤ) + 1))
          (flatPullbackBivariantCap C sX sY f hf 0 (relativeDimension_of_isOpenImmersion f)
            (flatPullbackDescends C) g (k + 1) α)) := by
  have hdeg : k = k - -((0 : ℕ) : ℤ) := by simp
  have hjsq : (e.inv ≫ pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) ≫
        (Stacks.Divisors.zeroScheme T L s).subschemeι =
      (Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
        pullback.snd f g := by
    have h1 : pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫
        (Stacks.Divisors.zeroScheme T L s).subschemeι =
        bivariantBaseChangeMap f g (Stacks.Divisors.zeroScheme T L s).subschemeι ≫
          pullback.snd f g := by
      simp [bivariantBaseChangeMap]
    rw [Category.assoc, h1, ← he, Category.assoc, Iso.inv_hom_id_assoc]
  have hjbase : (e.inv ≫ pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) ≫
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ (g ≫ sY)) =
      (Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
        (pullback.fst f g ≫ sX) := by
    rw [← Category.assoc, hjsq, Category.assoc, pullbackSnd_comp_structureMorphism hf g]
  have hgys := hgysR (g ≫ sY) (pullback.fst f g ≫ sX) (pullback.snd f g)
    (pullbackSnd_comp_structureMorphism hf g) L s k _ hjsq hjbase α
  have hv''base : pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ (g ≫ sY)) =
      pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX :=
    pullbackSnd_comp_structureMorphism hf ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)
  have hfac0 : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
      ((Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
        pullback.fst f g ≫ sX) e.hom hbase k :=
    properPushforwardFactorsThroughRationalEquivalence C _ _ e.hom hbase k
  have hL : ∀ β, properChowPushforward C
        (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
        ((Stacks.Divisors.zeroScheme (pullback f g)
          ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
          pullback.fst f g ≫ sX) e.hom hbase k hfac0
        (chowGroupRestrict C ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ (g ≫ sY))
          (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
          (pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) hv''base k β) =
      chowGroupRestrict C ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ (g ≫ sY))
        ((Stacks.Divisors.zeroScheme (pullback f g)
          ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
          (pullback.fst f g ≫ sX))
        (e.inv ≫ pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) hjbase k
        β := by
    intro β
    rw [properChowPushforward_eq_chowPushforwardOfIso,
      ← chowGroupRestrict_eq_chowPushforwardOfIso_of_comp_id C _ _ e.inv
        (by rw [← hbase, Iso.inv_hom_id_assoc]) e.hom hbase e.inv_hom_id k,
      chowGroupRestrict_comp]
  refine eq_of_heq (HEq.trans ?_ ((heq_of_eq (hL _)).trans ((heq_of_eq hgys).trans ?_)))
  · refine properChowPushforward_heq_congr C _ _ e.hom hbase hdeg.symm hfac hfac0 _ _ ?_
    exact flatPullbackBivariantCap_heq_chowGroupRestrict C sX sY f hf
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k _
  · refine gysinSystemOnChow_heq_congr G (pullback.fst f g ≫ sX) _ _ hdeg _ _ ?_
    exact ((flatPullbackBivariantCap_heq_chowGroupRestrict C sX sY f hf g (k + 1) α).symm.trans
      (eq_mp_chowGroup_heq C (pullback.fst f g ≫ sX)
        (by omega : k + 1 - -((0 : ℕ) : ℤ) = k - -((0 : ℕ) : ℤ) + 1) _).symm)

/-- **Stacks 0B78 for an open immersion.** For an open immersion `f : X ⟶ Y` of schemes locally of
finite type over the base, flat pullback along the base changes of `f` — restriction of cycle
classes to the open subschemes `X ×_Y T` of the test schemes — is a bivariant class
`f^* ∈ A^0(X ⟶ Y)`, at any Gysin system natural under restriction to opens.

The cap operation is that of `Stacks.Chow.flatPullbackBivariantClass`; the two hypotheses that
construction carries, Stacks 02RG and Stacks 0B71, are discharged here in the case of an open
immersion. -/
def flatPullbackBivariantClassOfIsOpenImmersion (hgysR : G.IsNaturalUnderOpensRestriction) :
    BivariantClass C G sX sY f hf (-((0 : ℕ) : ℤ)) where
  cap := fun {_T} g _ k ↦ flatPullbackBivariantCap C sX sY f hf 0
    (relativeDimension_of_isOpenImmersion f) (flatPullbackDescends C) g k
  cap_properPushforward := by
    intro T T' g _ h _ h' sq hfst k α
    have : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    exact flatPullbackBivariantCap_proper_naturality_of_isOpenImmersion C sX sY f hf g h h' sq
      hfst k _ _ α
  cap_flatPullbackChow := by
    intro T T' g _ h _ _ m hm h' sq hfst k α
    have : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    have : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    exact flatPullbackBivariantCap_flat_naturality C sX sY f hf 0
      (relativeDimension_of_isOpenImmersion f) (flatPullbackDescends C) g h m hm h' sq hfst k
      _ _ _ α
  cap_gysin := by
    intro T g _ L _ s k
    dsimp only
    intro e he hbase α
    exact flatPullbackBivariantCap_gysin_naturality_of_isOpenImmersion C G sX sY f hf hgysR g L
      s k e he hbase _ α

/-- The class of Stacks 0B78 along an open immersion caps by the cap operation of Stacks 0B78. -/
@[simp]
theorem flatPullbackBivariantClassOfIsOpenImmersion_cap
    (hgysR : G.IsNaturalUnderOpensRestriction) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) :
    (flatPullbackBivariantClassOfIsOpenImmersion C G sX sY f hf hgysR).cap g k =
      flatPullbackBivariantCap C sX sY f hf 0 (relativeDimension_of_isOpenImmersion f)
        (flatPullbackDescends C) g k :=
  rfl

/-- **Stacks 0B78.** The class along an open immersion is *the* flat-pullback class: it satisfies
the characterization `Stacks.Chow.IsBivariantFlatPullback`, by construction. -/
theorem isBivariantFlatPullback_flatPullbackBivariantClassOfIsOpenImmersion
    (hgysR : G.IsNaturalUnderOpensRestriction) :
    IsBivariantFlatPullback C G sX sY f hf 0 (relativeDimension_of_isOpenImmersion f)
      (flatPullbackDescends C) (flatPullbackBivariantClassOfIsOpenImmersion C G sX sY f hf hgysR) :=
  fun _ _ _ _ ↦ rfl

/-- **Stacks 0B78 for an open immersion, with nothing assumed.** The flat-pullback class
`f^* ∈ A^0(X ⟶ Y)` of an open immersion at the Gysin system of the first Chern class rule, where
naturality under restriction to opens is
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpensRestriction`. -/
def flatPullbackBivariantClassOfIsOpenImmersionOfInvertible :
    BivariantClass C (gysinSystemOfInvertible C) sX sY f hf (-((0 : ℕ) : ℤ)) :=
  flatPullbackBivariantClassOfIsOpenImmersion C (gysinSystemOfInvertible C) sX sY f hf
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)

end OpenImmersion

end Stacks.Chow

end
