module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent

/-!
# The bivariant class of a flat morphism, at the Gysin system of an invertible module

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
flat morphism of relative dimension `r` between schemes locally of finite type over `S`. The rule
which sends a test scheme `g : T ⟶ Y` to flat pullback

  `(f')^* : CH_k(T) ⟶ CH_{k+r}(X ×_Y T)`

along the base change `f' : X ×_Y T ⟶ T` of `f` is a bivariant class `f^* ∈ A^{-r}(X ⟶ Y)`
(Stacks 0B78), in the group `A^{-r}(X ⟶ Y)` of the source, the group of bivariant classes read
at the Gysin system `Stacks.Chow.gysinSystemOfInvertible` of the first Chern class of an
invertible module, with nothing assumed. That class is
`Stacks.Chow.flatPullbackBivariantClassOfInvertible`; this file proves its Gysin law in the form
tied to the projection, and its cap formula.

## Main results

* `Stacks.Chow.flatPullbackBivariantCap_gysin_naturality_ofInvertible` — the Gysin law of
  Stacks 0B76 (3) for the rule, at the canonical Gysin system.
* `Stacks.Chow.flatPullbackBivariantClassOfInvertible_cap` — the class
  `f^* ∈ A^{-r}(X ⟶ Y)` caps by flat pullback along the base change of `f`.

## References

* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Class

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX) (r : ℕ)
  (hfr : AlgebraicGeometry.RelativeDimension f r)

omit [LocallyOfFiniteType f] [Flat f] in
/-- The identification `e : X ×_Y Z(s) ≅ Z(f'^* s)` of Remark 0B6Y followed by the morphism
`Z(f'^* s) ⟶ Z(s)` is the projection `X ×_Y Z(s) ⟶ Z(s)`. -/
theorem bivariantDivisorIso_comp_zeroSchemePullbackHom {T : Scheme.{u}} (g : T ⟶ Y)
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (e : pullback f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≅
      (Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subscheme)
    (he : e.hom ≫ (Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι =
      bivariantBaseChangeMap f g (Stacks.Divisors.zeroScheme T L s).subschemeι) :
    e.hom ≫ zeroSchemePullbackHom (pullback.snd f g) L s =
      pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) := by
  refine (cancel_mono (Stacks.Divisors.zeroScheme T L s).subschemeι).1 ?_
  rw [Category.assoc, zeroSchemePullbackHom_subschemeι, ← Category.assoc, he]
  simp [bivariantBaseChangeMap]

/-- **Stacks 0B71, in the form of the Gysin law of Stacks 0B76 (3).** At the Gysin system of the
first Chern class of an invertible module, flat pullback along the base change of `f` commutes
with the Gysin map of the zero scheme of a section of an invertible module on a test scheme, the
base change of the zero scheme being read on the zero scheme of the pulled-back section through
the identification `e` of Remark 0B6Y. -/
theorem flatPullbackBivariantCap_gysin_naturality_ofInvertible
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
        pullback.fst f g ≫ sX) e.hom hbase (k - -(r : ℤ)))
    (α : chowGroup C (g ≫ sY) (k + 1)) :
    properChowPushforward C
        (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
        ((Stacks.Divisors.zeroScheme (pullback f g)
          ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
          pullback.fst f g ≫ sX) e.hom hbase (k - -(r : ℤ)) hfac
        (flatPullbackBivariantCap C sX sY f hf r hfr (flatPullbackDescends C)
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k
          ((gysinSystemOfInvertible C).onChow (g ≫ sY) L s k α)) =
      (gysinSystemOfInvertible C).onChow (pullback.fst f g ≫ sX)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s) (k - -(r : ℤ))
        (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
          (by omega : k + 1 - -(r : ℤ) = k - -(r : ℤ) + 1))
          (flatPullbackBivariantCap C sX sY f hf r hfr (flatPullbackDescends C) g (k + 1) α)) := by
  have hdeg : k + (r : ℤ) = k - -(r : ℤ) := by ring
  have hFr : AlgebraicGeometry.RelativeDimension (pullback.snd f g) r :=
    relativeDimension_pullbackSnd f hfr g
  have hdr : AlgebraicGeometry.RelativeDimension
      (pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) r :=
    relativeDimension_pullbackSnd f hfr ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)
  have hg₀r : AlgebraicGeometry.RelativeDimension
      (zeroSchemePullbackHom (pullback.snd f g) L s) r :=
    relativeDimension_zeroSchemePullbackHom (pullback.snd f g) L s r hFr
  have hcomp : e.hom ≫ zeroSchemePullbackHom (pullback.snd f g) L s =
      pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) :=
    bivariantDivisorIso_comp_zeroSchemePullbackHom f g L s e he
  have hsq : IsPullback (pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))
      e.hom (𝟙 (Stacks.Divisors.zeroScheme T L s).subscheme)
      (zeroSchemePullbackHom (pullback.snd f g) L s) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, hcomp]⟩
  have hpA : pullback.snd f g ≫ (g ≫ sY) = pullback.fst f g ≫ sX :=
    pullbackSnd_comp_structureMorphism hf g
  have hg : zeroSchemePullbackHom (pullback.snd f g) L s ≫
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ (g ≫ sY)) =
      (pullbackZeroScheme (pullback.snd f g) L s).subschemeι ≫ (pullback.fst f g ≫ sX) := by
    rw [← Category.assoc, zeroSchemePullbackHom_subschemeι, Category.assoc, hpA]
  have hdb : pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ (g ≫ sY)) =
      pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX := by
    rw [← hcomp, Category.assoc, hg, ← Category.assoc]
    exact (Category.assoc _ _ _).trans hbase
  have hrg := properPushforwardFlatPullbackBaseChange C
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ (g ≫ sY))
    (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ (g ≫ sY))
    ((pullbackZeroScheme (pullback.snd f g) L s).subschemeι ≫ (pullback.fst f g ≫ sX))
    (𝟙 (Stacks.Divisors.zeroScheme T L s).subscheme) (Category.id_comp _) e.hom hbase
    (pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) hdb
    (zeroSchemePullbackHom (pullback.snd f g) L s) hg hsq r hdr hg₀r k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    ((gysinSystemOfInvertible C).onChow (g ≫ sY) L s k α)
  rw [properChowPushforward_id] at hrg
  have h71 := gysinSystemOfInvertible_onChow_flatPullbackChow C (g ≫ sY) (pullback.snd f g) r
    hFr k L s (pullback.fst f g ≫ sX) hpA (flatPullbackDescends C _ _ _ _ _ _ _) hg
    (flatPullbackDescends C _ _ _ _ _ _ _) α
  have hleft := properChowPushforward_heq_congr C
    (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
    ((pullbackZeroScheme (pullback.snd f g) L s).subschemeι ≫ (pullback.fst f g ≫ sX)) e.hom
    hbase hdeg.symm hfac (properPushforwardDescends C _ _ _ _ _) _ _
    (flatPullbackBivariantCap_heq C sX sY f hf r hfr (flatPullbackDescends C)
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k
      ((gysinSystemOfInvertible C).onChow (g ≫ sY) L s k α))
  have harg := (eq_mp_chowGroup_heq C (pullback.fst f g ≫ sX)
      (by omega : k + 1 - -(r : ℤ) = k - -(r : ℤ) + 1)
      (flatPullbackBivariantCap C sX sY f hf r hfr (flatPullbackDescends C) g (k + 1) α)).trans
    ((flatPullbackBivariantCap_heq C sX sY f hf r hfr (flatPullbackDescends C) g (k + 1) α).trans
      (chowGroupDegreeEquiv_heq C (pullback.fst f g ≫ sX)
        (by ring : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
        (flatPullbackChow C (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g) hpA r hFr
          (k + 1) (flatPullbackDescends C _ _ _ _ _ _ _) α)).symm)
  have hright := gysinSystemOnChow_heq_congr (gysinSystemOfInvertible C)
    (pullback.fst f g ≫ sX) ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s) hdeg.symm _ _ harg
  exact eq_of_heq (hleft.trans ((heq_of_eq (hrg.symm.trans h71.symm)).trans hright.symm))

/-- **Stacks 0B78.** The class `f^*` caps by flat pullback along the base change of `f`. -/
@[simp]
theorem flatPullbackBivariantClassOfInvertible_cap {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (flatPullbackBivariantClassOfInvertible C sX sY f hf r hfr).cap g k α =
      flatPullbackBivariantCap C sX sY f hf r hfr (flatPullbackDescends C) g k α :=
  rfl

end Class

end Stacks.Chow

end
