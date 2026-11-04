module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinClass

/-!
# Flat pullback and Gysin maps at the comparison morphism

For an invertible module `L` with section `s` on `T` and a flat morphism `v : A ⟶ T`, the
pullback of `Z(s)` along `v` is identified with the zero scheme of the pulled-back section through
the comparison morphism `Stacks.Chow.zeroSchemePullbackHom` of Remark 0B6Y. At that comparison
morphism, flat pullback commutes with the Gysin map of the zero scheme on Chow groups (Stacks
0B71), and this gives the Gysin law of Stacks 0B76 for the flat-pullback cap operation.

## Main definitions

* `Stacks.Chow.GysinSystem.FlatPullbackNaturalityAtZeroSchemeComparison`: flat pullback commutes
  with the Gysin maps of a Gysin system on Chow groups, for identifications compatible with the
  comparison morphism of Remark 0B6Y.

## Main results

* `Stacks.Chow.gysinSystemOfInvertible_flatPullbackNaturalityAtZeroSchemeComparison`: the Gysin
  system of an invertible module satisfies this condition.
* `Stacks.Chow.flatPullbackBivariantCap_gysin_naturality_of_comparison`: under this condition, the
  flat-pullback cap operation of Stacks 0B78 satisfies the Gysin law of Stacks 0B76.

## References

* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Flat pullback commutes with the Gysin maps of `G` on Chow groups (Stacks 0B71), for every
flat `v` of relative dimension `r` and every identification `ε` of `A''` with the zero scheme of
the pulled-back section whose composite with `Stacks.Chow.zeroSchemePullbackHom` is `v''`. -/
def GysinSystem.FlatPullbackNaturalityAtZeroSchemeComparison {C : ChowSituation.{u}}
    (G : GysinSystem C) (r : ℕ) : Prop :=
  ∀ {T A A'' : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sA'' : A'' ⟶ C.S) [LocallyOfFiniteType sA''] (v : A ⟶ T)
    [LocallyOfFiniteType v] [Flat v] (hv : v ≫ q = sA)
    (hvr : AlgebraicGeometry.RelativeDimension v r) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property
      ((Scheme.Modules.pullback v).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ) (v'' : A'' ⟶ (Stacks.Divisors.zeroScheme T L s).subscheme)
    [LocallyOfFiniteType v''] [Flat v'']
    (hv'' : v'' ≫ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q) = sA'')
    (hv''r : AlgebraicGeometry.RelativeDimension v'' r)
    (ε : A'' ≅ (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback v).obj L)
      (AlgebraicGeometry.pullbackGlobalSections v L s)).subscheme)
    (hε : ε.hom ≫ ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback v).obj L)
      (AlgebraicGeometry.pullbackGlobalSections v L s)).subschemeι ≫ sA) = sA'')
    (hcanon : ε.hom ≫ zeroSchemePullbackHom v L s = v'')
    (hfacv'' : FlatPullbackFactorsThroughRationalEquivalence C sA''
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q) v'' hv'' r hv''r k)
    (hfacv : FlatPullbackFactorsThroughRationalEquivalence C sA q v hv r hvr (k + 1))
    (hpp : ProperPushforwardFactorsThroughRationalEquivalence C sA''
      ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback v).obj L)
        (AlgebraicGeometry.pullbackGlobalSections v L s)).subschemeι ≫ sA) ε.hom hε
      (k + (r : ℤ)))
    (α : chowGroup C q (k + 1)),
    properChowPushforward C sA''
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback v).obj L)
          (AlgebraicGeometry.pullbackGlobalSections v L s)).subschemeι ≫ sA) ε.hom hε
        (k + (r : ℤ)) hpp
        (flatPullbackChow C sA'' ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q) v'' hv'' r
          hv''r k hfacv'' (G.onChow q L s k α)) =
      G.onChow sA ((Scheme.Modules.pullback v).obj L)
        (AlgebraicGeometry.pullbackGlobalSections v L s) (k + (r : ℤ))
        (chowGroupDegreeEquiv C sA (by ring : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
          (flatPullbackChow C sA q v hv r hvr (k + 1) hfacv α))

/-- The Gysin system `Stacks.Chow.gysinSystemOfInvertible` satisfies
`Stacks.Chow.GysinSystem.FlatPullbackNaturalityAtZeroSchemeComparison`. -/
theorem gysinSystemOfInvertible_flatPullbackNaturalityAtZeroSchemeComparison
    (C : ChowSituation.{u}) (r : ℕ) :
    (gysinSystemOfInvertible C).FlatPullbackNaturalityAtZeroSchemeComparison r := by
  intro T A A'' q _ sA _ sA'' _ v _ _ hv hvr L _ _ s k v'' _ _ hv'' hv''r ε hε hcanon hfacv''
    hfacv hpp α
  have hg := zeroSchemePullbackHom_comp v L s C q sA hv
  have hgr := relativeDimension_zeroSchemePullbackHom v L s r hvr
  have hfac' := flatPullbackFactorsThroughRationalEquivalence_general C
    ((pullbackZeroScheme v L s).subschemeι ≫ sA)
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q) (zeroSchemePullbackHom v L s) hg r hgr k
  refine Eq.trans ?_ (gysinSystemOfInvertible_onChow_flatPullbackChow C q v r hvr k L s sA hv
    hfacv hg hfac' α).symm
  have htr := flatPullbackChow_chowPushforwardOfIso C
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q) sA''
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q)
    ((pullbackZeroScheme v L s).subschemeι ≫ sA) (𝟙 _) (Category.id_comp _) ε.hom hε v'' hv''
    (zeroSchemePullbackHom v L s) hg (by rw [Category.comp_id, hcanon]) r hv''r hgr k hfacv''
    hfac' ((gysinSystemOfInvertible C).onChow q L s k α)
  rwa [chowPushforwardOfIso_id, eq_comm] at htr

section Class

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX) (r : ℕ)
  (hfr : AlgebraicGeometry.RelativeDimension f r) (hS1 : FlatPullbackDescends C)

/-- The Gysin law of Stacks 0B76 (3) for the cap operation of Stacks 0B78: if `G` satisfies
`Stacks.Chow.GysinSystem.FlatPullbackNaturalityAtZeroSchemeComparison`, flat pullback along the
base change of `f` commutes with the Gysin map of the zero scheme of a section of an invertible
module on a test scheme. -/
theorem flatPullbackBivariantCap_gysin_naturality_of_comparison
    (h71 : G.FlatPullbackNaturalityAtZeroSchemeComparison r)
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
        (flatPullbackBivariantCap C sX sY f hf r hfr hS1
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k
          (G.onChow (g ≫ sY) L s k α)) =
      G.onChow (pullback.fst f g ≫ sX)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s) (k - -(r : ℤ))
        (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
          (by omega : k + 1 - -(r : ℤ) = k - -(r : ℤ) + 1))
          (flatPullbackBivariantCap C sX sY f hf r hfr hS1 g (k + 1) α)) := by
  have hdeg : k + (r : ℤ) = k - -(r : ℤ) := by ring
  have hpp2 : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
      ((Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
        pullback.fst f g ≫ sX) e.hom hbase (k + (r : ℤ)) :=
    hdeg ▸ hfac
  have hvb : pullback.snd f g ≫ (g ≫ sY) = pullback.fst f g ≫ sX :=
    pullbackSnd_comp_structureMorphism hf g
  have hvbr : AlgebraicGeometry.RelativeDimension (pullback.snd f g) r :=
    relativeDimension_pullbackSnd f hfr g
  have hdb : pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫
      (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sY) =
      pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX :=
    pullbackSnd_comp_structureMorphism hf ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)
  have hdbr : AlgebraicGeometry.RelativeDimension
      (pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) r :=
    relativeDimension_pullbackSnd f hfr ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)
  have hfacv := hS1 (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g) hvb r hvbr (k + 1)
  have hfacv'' := hS1 (pullback.fst f
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
    (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sY)
    (pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) hdb r hdbr k
  have hmove := (properChowPushforward_heq_congr C
    (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX) _ e.hom hbase hdeg
    hpp2 hfac _ _ (flatPullbackBivariantCap_heq C sX sY f hf r hfr hS1
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k
      (G.onChow (g ≫ sY) L s k α)).symm).symm
  have hcanon : e.hom ≫ zeroSchemePullbackHom (pullback.snd f g) L s =
      pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) := by
    rw [← cancel_mono (Stacks.Divisors.zeroScheme T L s).subschemeι, Category.assoc,
      zeroSchemePullbackHom_subschemeι, ← Category.assoc, he]
    exact (isPullback_bivariantBaseChangeMap f g
      (Stacks.Divisors.zeroScheme T L s).subschemeι).w.symm
  have h71inst := h71 (g ≫ sY) (pullback.fst f g ≫ sX)
    (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
    (pullback.snd f g) hvb hvbr L s k
    (pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) hdb hdbr
    e hbase hcanon hfacv'' hfacv hpp2 α
  have harg := (chowGroupDegreeEquiv_heq C (pullback.fst f g ≫ sX)
    (by ring : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
    (flatPullbackChow C (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g) hvb r hvbr (k + 1)
      hfacv α)).trans
    (((flatPullbackBivariantCap_heq C sX sY f hf r hfr hS1 g (k + 1) α).symm).trans
      ((eq_mp_chowGroup_heq C (pullback.fst f g ≫ sX)
        (by omega : k + 1 - -(r : ℤ) = k - -(r : ℤ) + 1)
        (flatPullbackBivariantCap C sX sY f hf r hfr hS1 g (k + 1) α)).symm))
  have hgys := gysinSystemOnChow_heq_congr G (pullback.fst f g ≫ sX)
    ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s) hdeg _ _ harg
  exact eq_of_heq (hmove.trans ((heq_of_eq h71inst).trans hgys))

end Class

end Stacks.Chow

end
