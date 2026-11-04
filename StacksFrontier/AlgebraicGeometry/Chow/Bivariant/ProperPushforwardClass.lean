module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Composition

/-!
# The proper pushforward of a bivariant Chow class, constructed

Let `(S, δ)` be the base situation of [Stacks, Chapter 42], let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of schemes locally of finite type over `S` with `f` proper, and let
`c ∈ A^p(X ⟶ Z)` be a bivariant class for the composite. By [Stacks, Tag 0EPK] the rule sending a
test scheme `t : T ⟶ Z` and a class `α ∈ A_k(T)` to

  `f'_*(c ∩ α) ∈ A_{k-p}(T ×_Z Y)`,

where `f' : T ×_Z X ⟶ T ×_Z Y` is the base change of `f`, is again a bivariant class, written
`f_* ∘ c ∈ A^p(Y ⟶ Z)`. The rule is `Stacks.Chow.bivariantProperPushforwardCap`.

## Main definitions

* `Stacks.Chow.bivariantProperPushforward`: the class `f_* ∘ c ∈ A^p(Y ⟶ Z)`, against an
  arbitrary Gysin system.

## Main results

* `Stacks.Chow.isPullback_bivariantPushforwardBaseChange_baseChange`: the two base changes of `f`
  and the two base changes of a morphism of test schemes form a cartesian square.
* `Stacks.Chow.GysinSystem.onChow_properPushforward_over_base`: [Stacks, Tag 02TA] for a Gysin
  system, for a proper morphism of two schemes over a common base carrying the divisor.
* `Stacks.Chow.bivariantProperPushforwardCap_flat_naturality` and
  `Stacks.Chow.bivariantProperPushforwardCap_gysin_naturality`: the flat-pullback and the
  Gysin axiom of [Stacks, Tag 0B76] for the rule.
* `Stacks.Chow.isBivariantProperPushforward_bivariantProperPushforward` and
  `Stacks.Chow.exists_isBivariantProperPushforward`: the constructed class caps by the rule, so
  the rule is realized by a bivariant class.

## Implementation notes

[Stacks, Tag 02RG] on Chow groups is the hypothesis
`Stacks.Chow.ProperPushforwardFlatPullbackBaseChange`, proved as
`Stacks.Chow.properPushforwardFlatPullbackBaseChange`. [Stacks, Tag 02TA] for the Gysin system is
the pair of hypotheses `Stacks.Chow.GysinSystem.IsNaturalUnderProperPushforward` and
`Stacks.Chow.GysinSystem.IsNaturalUnderPullbackCompPushforward`, both of which hold for
`Stacks.Chow.gysinSystemOfInvertible`.

## References

* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The base change of the proper morphism along a morphism of test schemes -/

/-- The map `T' ×_Y X ⟶ T ×_Y X` induced by `h : T' ⟶ T` is compatible with the projections
to `X`. -/
private theorem bivariantBaseChangeMap_fst {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    (h : T' ⟶ T) :
    bivariantBaseChangeMap f g h ≫ pullback.fst f g = pullback.fst f (h ≫ g) := by
  rw [bivariantBaseChangeMap, pullbackMap_fst, Category.comp_id]

/-- The base change of `f` along a test scheme is natural in the test scheme: the two base
changes of `f`, over `T` and over `T'`, and the two base changes of a morphism `h : T' ⟶ T` of
test schemes, over `X` and over `Y`, form a commuting square. -/
theorem bivariantBaseChangeMap_comp_bivariantPushforwardBaseChange {X Y Z T T' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z) (h : T' ⟶ T)
    (h' : pullback g (h ≫ t) ⟶ pullback g t)
    (sq : IsPullback (pullback.snd g (h ≫ t)) h' h (pullback.snd g t))
    (hfst : h' ≫ pullback.fst g t = pullback.fst g (h ≫ t)) :
    bivariantBaseChangeMap (f ≫ g) t h ≫ bivariantPushforwardBaseChange f g t =
      bivariantPushforwardBaseChange f g (h ≫ t) ≫ h' := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, bivariantPushforwardBaseChange_fst, ← Category.assoc,
      bivariantBaseChangeMap_fst,
      Category.assoc, hfst, bivariantPushforwardBaseChange_fst]
  · rw [Category.assoc, bivariantPushforwardBaseChange_snd, Category.assoc, ← sq.w,
      bivariantPushforwardBaseChange_snd_assoc,
      (isPullback_bivariantBaseChangeMap (f ≫ g) t h).w]

/-- The square of `Stacks.Chow.bivariantBaseChangeMap_comp_bivariantPushforwardBaseChange` is
cartesian: `T' ×_Z X` is the fibre product of `T ×_Z X` and `T' ×_Z Y` over `T ×_Z Y`. -/
theorem isPullback_bivariantPushforwardBaseChange_baseChange {X Y Z T T' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (t : T ⟶ Z) (h : T' ⟶ T) (h' : pullback g (h ≫ t) ⟶ pullback g t)
    (sq : IsPullback (pullback.snd g (h ≫ t)) h' h (pullback.snd g t))
    (hfst : h' ≫ pullback.fst g t = pullback.fst g (h ≫ t)) :
    IsPullback (bivariantBaseChangeMap (f ≫ g) t h)
      (bivariantPushforwardBaseChange f g (h ≫ t)) (bivariantPushforwardBaseChange f g t) h' := by
  refine IsPullback.of_bot ?_
    (bivariantBaseChangeMap_comp_bivariantPushforwardBaseChange f g t h h' sq hfst) sq.flip
  rw [bivariantPushforwardBaseChange_snd, bivariantPushforwardBaseChange_snd]
  exact (isPullback_bivariantBaseChangeMap (f ≫ g) t h).flip

/-! ### Gysin maps along a proper morphism over a common base -/

/-- **Gysin maps commute with proper pushforward over a common base** ([Stacks, Tag 02TA] for a
Gysin system). Let `u : A ⟶ B` be proper over the base of the Chow situation, and let
`qB : B ⟶ W` and `qA : A ⟶ W` with `u ≫ qB = qA` present `A` and `B` over a scheme `W` carrying an
invertible module `L` with a global section `s`. Let `j : Z(q_A^*s) ⟶ Z(q_B^*s)` fill the square
of [Stacks, Tag 0B6Y]. Then `i^* u_* α = j_* (i')^* α`. -/
theorem GysinSystem.onChow_properPushforward_over_base {C : ChowSituation.{u}} {G : GysinSystem C}
    (hgysP : G.IsNaturalUnderProperPushforward)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) {A B W : Scheme.{u}} (pA : A ⟶ C.S)
    [LocallyOfFiniteType pA] (pB : B ⟶ C.S) [LocallyOfFiniteType pB] (u : A ⟶ B) [IsProper u]
    (hu : u ≫ pB = pA) (qB : B ⟶ W) (qA : A ⟶ W) (hq : u ≫ qB = qA) (L : W.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ)
    (j : (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
            (AlgebraicGeometry.pullbackGlobalSections qA L s)).subscheme ⟶
          (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
            (AlgebraicGeometry.pullbackGlobalSections qB L s)).subscheme) [IsProper j]
    (hjsq : j ≫ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι =
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ u)
    (hj : j ≫ ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB) =
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ pA)
    (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C pA pB u hu (k + 1))
    (hfacj : ProperPushforwardFactorsThroughRationalEquivalence C
      ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ pA)
      ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB) j hj k)
    (α : chowGroup C pA (k + 1)) :
    G.onChow pB ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s) k
        (properChowPushforward C pA pB u hu (k + 1) hfacu α) =
      properChowPushforward C
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ pA)
        ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB) j hj k hfacj
        (G.onChow pA ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s) k α) := by
  subst hq
  have hZZ : pullbackZeroScheme u ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s) =
      Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback (u ≫ qB)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (u ≫ qB) L s) :=
    Stacks.Divisors.zeroScheme_pullback_comp u qB L s
  have hιbase : eqToHom (congrArg Scheme.IdealSheafData.subscheme hZZ) ≫
      ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback (u ≫ qB)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (u ≫ qB) L s)).subschemeι ≫ pA) =
      (pullbackZeroScheme u ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pA := by
    rw [← Category.assoc, subschemeι_eqToHom hZZ]
  have hι : eqToHom (congrArg Scheme.IdealSheafData.subscheme hZZ) ≫ j =
      zeroSchemePullbackHom u ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s) := by
    refine eq_zeroSchemePullbackHom u ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s) _ ?_
    rw [Category.assoc, hjsq, ← Category.assoc, subschemeι_eqToHom hZZ]
  have h1 := hgysP pA pB u hu ((Scheme.Modules.pullback qB).obj L)
    (AlgebraicGeometry.pullbackGlobalSections qB L s) k
    (zeroSchemePullbackHom u ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s))
    (zeroSchemePullbackHom_subschemeι u ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s))
    hfacu (properPushforwardDescends C _ _ _ _ _) α
  have h2 := hgysc u qB pA L s k α
  rw [h1, ← h2]
  exact properChowPushforward_comp_apply C
    ((pullbackZeroScheme u ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pA)
    ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback (u ≫ qB)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (u ≫ qB) L s)).subschemeι ≫ pA)
    ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB)
    (eqToHom (congrArg Scheme.IdealSheafData.subscheme hZZ)) j
    (zeroSchemePullbackHom u ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s)) hι hιbase hj
    (zeroSchemeSquare_comp_structureMorphism C pA pB u hu
      ((Scheme.Modules.pullback qB).obj L) (AlgebraicGeometry.pullbackGlobalSections qB L s)
      (zeroSchemePullbackHom u ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s))
      (zeroSchemePullbackHom_subschemeι u ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s))) k
    (properPushforwardDescends C _ _ _ _ _) hfacj (properPushforwardDescends C _ _ _ _ _) _

/-! ### The flat-pullback and Gysin axioms of the pushed-forward class -/

section Pushforward

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f]
  (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
  (hpp : ProperPushforwardDescends C) (p : ℤ)
  (c : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p)

/-- **The flat-pullback axiom of [Stacks, Tag 0B76] for the rule of [Stacks, Tag 0EPK].** The cap
operation `α ↦ f'_*(c ∩ α)` commutes with flat pullback along a morphism `h` of test schemes of
relative dimension `r`, given [Stacks, Tag 02RG] as `hRG`. The degree is `(k + r) - p` on one side
and `(k - p) + r` on the other, whence the heterogeneous equality. -/
theorem bivariantProperPushforwardCap_flat_naturality
    (hRG : ProperPushforwardFlatPullbackBaseChange C) {T T' : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback g (h ≫ t) ⟶ pullback g t) [LocallyOfFiniteType h'] [Flat h']
    (sq : IsPullback (pullback.snd g (h ≫ t)) h' h (pullback.snd g t))
    (hfst : h' ≫ pullback.fst g t = pullback.fst g (h ≫ t)) (k : ℤ)
    (hr' : AlgebraicGeometry.RelativeDimension h' r)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ t) ≫ sZ) (t ≫ sZ) h
      (by simp [Category.assoc]) r hr k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C (pullback.fst g (h ≫ t) ≫ sY)
      (pullback.fst g t ≫ sY) h' (by rw [← Category.assoc, hfst]) r hr' (k - p))
    (α : chowGroup C (t ≫ sZ) k) :
    HEq
      (bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c (h ≫ t) (k + (r : ℤ))
        (flatPullbackChow C ((h ≫ t) ≫ sZ) (t ≫ sZ) h (by simp [Category.assoc]) r hr k hfac α))
      (flatPullbackChow C (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY) h'
        (by rw [← Category.assoc, hfst]) r hr' (k - p) hfac'
        (bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c t k α)) := by
  set hX : pullback (f ≫ g) (h ≫ t) ⟶ pullback (f ≫ g) t :=
    bivariantBaseChangeMap (f ≫ g) t h with hXdef
  have hXsq : IsPullback (pullback.snd (f ≫ g) (h ≫ t)) hX h (pullback.snd (f ≫ g) t) :=
    isPullback_bivariantBaseChangeMap (f ≫ g) t h
  have hXfst : hX ≫ pullback.fst (f ≫ g) t = pullback.fst (f ≫ g) (h ≫ t) :=
    bivariantBaseChangeMap_fst _ _ _
  have : LocallyOfFiniteType hX :=
    MorphismProperty.of_isPullback hXsq (P := @LocallyOfFiniteType) inferInstance
  have : Flat hX := MorphismProperty.of_isPullback hXsq (P := @Flat) inferInstance
  have hXr : AlgebraicGeometry.RelativeDimension hX r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback hXsq hr
  have hfacX : FlatPullbackFactorsThroughRationalEquivalence C
      (pullback.fst (f ≫ g) (h ≫ t) ≫ sX) (pullback.fst (f ≫ g) t ≫ sX) hX
      (by rw [← Category.assoc, hXfst]) r hXr (k - p) :=
    flatPullbackDescends C _ _ _ _ _ _ _
  have hc := c.flat_naturality t h r hr hX hXsq hXfst k hXr hfac hfacX α
  have hrg := hRG (pullback.fst (f ≫ g) t ≫ sX) (pullback.fst (f ≫ g) (h ≫ t) ≫ sX)
    (pullback.fst g t ≫ sY) (pullback.fst g (h ≫ t) ≫ sY)
    (bivariantPushforwardBaseChange f g t)
    (bivariantPushforwardBaseChange_comp_structure hf g t)
    (bivariantPushforwardBaseChange f g (h ≫ t))
    (bivariantPushforwardBaseChange_comp_structure hf g (h ≫ t)) hX
    (by rw [← Category.assoc, hXfst]) h' (by rw [← Category.assoc, hfst])
    (isPullback_bivariantPushforwardBaseChange_baseChange f g t h h' sq hfst) r hXr hr' (k - p)
    hfacX hfac' (hpp _ _ _ _ _) (hpp _ _ _ _ _) (c.cap t k α)
  rw [bivariantProperPushforwardCap_apply, bivariantProperPushforwardCap_apply]
  exact (heq_map_index (by ring : k + (r : ℤ) - p = k - p + (r : ℤ)) hc
    (fun n x ↦ properChowPushforward C (pullback.fst (f ≫ g) (h ≫ t) ≫ sX)
      (pullback.fst g (h ≫ t) ≫ sY) (bivariantPushforwardBaseChange f g (h ≫ t))
      (bivariantPushforwardBaseChange_comp_structure hf g (h ≫ t)) n (hpp _ _ _ _ _)
      x)).trans (heq_of_eq hrg.symm)

/-- **The Gysin axiom of [Stacks, Tag 0B76] for the rule of [Stacks, Tag 0EPK].** The cap
operation `α ↦ f'_*(c ∩ α)` commutes with the Gysin map of the zero scheme of a section of an
invertible module on a test scheme, for a Gysin system `G` satisfying `hgysP` and `hgysc`. -/
theorem bivariantProperPushforwardCap_gysin_naturality
    (hgysP : G.IsNaturalUnderProperPushforward)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ)
    (e : pullback g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≅
      (Stacks.Divisors.zeroScheme (pullback g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subscheme)
    (he : e.hom ≫ (Stacks.Divisors.zeroScheme (pullback g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι =
      bivariantBaseChangeMap g t (Stacks.Divisors.zeroScheme T L s).subschemeι)
    (hbase : e.hom ≫ ((Stacks.Divisors.zeroScheme (pullback g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
        pullback.fst g t ≫ sY) =
      pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY)
      ((Stacks.Divisors.zeroScheme (pullback g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
        pullback.fst g t ≫ sY) e.hom hbase (k - p))
    (α : chowGroup C (t ≫ sZ) (k + 1)) :
    properChowPushforward C
        (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY)
        ((Stacks.Divisors.zeroScheme (pullback g t)
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
          pullback.fst g t ≫ sY) e.hom hbase (k - p) hfac
        (bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) k
          (G.onChow (t ≫ sZ) L s k α)) =
      G.onChow (pullback.fst g t ≫ sY) ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s) (k - p)
        (Eq.mp (congrArg (chowGroup C (pullback.fst g t ≫ sY))
          (by omega : k + 1 - p = k - p + 1))
          (bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c t (k + 1) α)) := by
  have hsnd : bivariantPushforwardBaseChange f g t ≫ pullback.snd g t = pullback.snd (f ≫ g) t :=
    bivariantPushforwardBaseChange_snd f g t
  have hZZ : Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
        ((Scheme.Modules.pullback (bivariantPushforwardBaseChange f g t)).obj
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L))
        (AlgebraicGeometry.pullbackGlobalSections (bivariantPushforwardBaseChange f g t)
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)) =
      Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
        ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s) := by
    rw [Stacks.Divisors.zeroScheme_pullback_comp, hsnd]
  set jXY := eqToHom (congrArg Scheme.IdealSheafData.subscheme hZZ.symm) ≫
    zeroSchemePullbackHom (bivariantPushforwardBaseChange f g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s) with hjXY
  have : IsProper jXY := by rw [hjXY]; infer_instance
  have hjsq : jXY ≫ (Stacks.Divisors.zeroScheme (pullback g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι =
      (Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
        ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s)).subschemeι ≫
        bivariantPushforwardBaseChange f g t := by
    rw [hjXY, Category.assoc, zeroSchemePullbackHom_subschemeι, ← Category.assoc,
      subschemeι_eqToHom hZZ.symm]
  have hz := comp_comp_of_comp hjsq (bivariantPushforwardBaseChange_comp_structure hf g t)
  have hwbase : (zeroSchemeBaseChangeIso (f ≫ g) t L s).hom ≫
      ((Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
        ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s)).subschemeι ≫
        pullback.fst (f ≫ g) t ≫ sX) =
      pullback.fst (f ≫ g) ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sX :=
    comp_comp_of_eq (zeroSchemeBaseChangeIso_hom_subschemeι (f ≫ g) t L s)
      (by rw [← Category.assoc, bivariantBaseChangeMap_fst])
  have hcomp : bivariantPushforwardBaseChange f g
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ e.hom =
      (zeroSchemeBaseChangeIso (f ≫ g) t L s).hom ≫ jXY := by
    refine (cancel_mono (Stacks.Divisors.zeroScheme (pullback g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι).1 ?_
    rw [Category.assoc, Category.assoc, he, hjsq, ← Category.assoc,
      zeroSchemeBaseChangeIso_hom_subschemeι]
    exact (bivariantBaseChangeMap_comp_bivariantPushforwardBaseChange f g t
      (Stacks.Divisors.zeroScheme T L s).subschemeι
      (bivariantBaseChangeMap g t (Stacks.Divisors.zeroScheme T L s).subschemeι)
      (isPullback_bivariantBaseChangeMap g t (Stacks.Divisors.zeroScheme T L s).subschemeι)
      (bivariantBaseChangeMap_fst _ _ _)).symm
  have hc := c.gysin_naturality t L s k (zeroSchemeBaseChangeIso (f ≫ g) t L s)
    (zeroSchemeBaseChangeIso_hom_subschemeι (f ≫ g) t L s) hwbase (hpp _ _ _ _ _) α
  have hgysb := GysinSystem.onChow_properPushforward_over_base hgysP hgysc
    (pullback.fst (f ≫ g) t ≫ sX) (pullback.fst g t ≫ sY)
    (bivariantPushforwardBaseChange f g t)
    (bivariantPushforwardBaseChange_comp_structure hf g t)
    (pullback.snd g t) (pullback.snd (f ≫ g) t) hsnd L s (k - p) jXY hjsq hz
    (hpp _ _ _ _ _) (hpp _ _ _ _ _)
    (Eq.mp (congrArg (chowGroup C (pullback.fst (f ≫ g) t ≫ sX))
      (by omega : k + 1 - p = k - p + 1)) (c.cap t (k + 1) α))
  exact gysinNaturalityAssemble C
    (bivariantPushforwardBaseChange_comp_structure hf g
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t))
    hbase hwbase hz (bivariantPushforwardBaseChange_comp_structure hf g t) hcomp
    (by omega : k + 1 - p = k - p + 1) (hpp _ _ _ _ _) hfac (hpp _ _ _ _ _) (hpp _ _ _ _ _)
    (hpp _ _ _ _ _) (hpp _ _ _ _ _)
    (bivariantProperPushforwardCap_apply C G sX sY sZ f g hf hg hpp p c
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) k (G.onChow (t ≫ sZ) L s k α))
    (bivariantProperPushforwardCap_apply C G sX sY sZ f g hf hg hpp p c t (k + 1) α) hc hgysb

/-! ### The pushed-forward class -/

/-- **The proper pushforward `f_* ∘ c ∈ A^p(Y ⟶ Z)` of [Stacks, Tag 0EPK]** of a bivariant
class `c ∈ A^p(X ⟶ Z)` along a proper morphism `f : X ⟶ Y`: the cap operation
`α ↦ f'_*(c ∩ α)` of `Stacks.Chow.bivariantProperPushforwardCap`, a bivariant class given
[Stacks, Tag 02RG] as `hRG` and [Stacks, Tag 02TA] for the Gysin system as `hgysP` and
`hgysc`. -/
def bivariantProperPushforward (hRG : ProperPushforwardFlatPullbackBaseChange C)
    (hgysP : G.IsNaturalUnderProperPushforward)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) :
    BivariantClass C G sY sZ g hg p where
  cap := fun {_T} t _ k ↦ bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c t k
  cap_properPushforward := by
    intro T T' t _ h _ h' sq hfst k α
    have : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    exact bivariantProperPushforwardCap_proper_naturality C G sX sY sZ f g hf hg hpp p c t h h'
      sq hfst k α
  cap_flatPullbackChow := by
    intro T T' t _ h _ _ r hr h' sq hfst k α
    have : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    have : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    have hr' : AlgebraicGeometry.RelativeDimension h' r :=
      AlgebraicGeometry.RelativeDimension.of_isPullback sq hr
    exact bivariantProperPushforwardCap_flat_naturality C G sX sY sZ f g hf hg hpp p c hRG t h r
      hr h' sq hfst k hr' (flatPullbackDescends C _ _ _ _ _ _ _)
      (flatPullbackDescends C _ _ _ _ _ _ _) α
  cap_gysin := by
    intro T t _ L _ s k
    dsimp only
    intro e he hbase α
    exact bivariantProperPushforwardCap_gysin_naturality C G sX sY sZ f g hf hg hpp p c hgysP
      hgysc t L s k e he hbase (hpp _ _ _ _ _) α

/-- **`Stacks.Chow.bivariantProperPushforward` caps by the rule of [Stacks, Tag 0EPK]**, so it is
the proper pushforward in the sense of `Stacks.Chow.IsBivariantProperPushforward`. -/
theorem isBivariantProperPushforward_bivariantProperPushforward
    (hRG : ProperPushforwardFlatPullbackBaseChange C)
    (hgysP : G.IsNaturalUnderProperPushforward)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) :
    IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p c
      (bivariantProperPushforward C G sX sY sZ f g hf hg hpp p c hRG hgysP hgysc) :=
  fun _ _ _ _ ↦ rfl

/-- **[Stacks, Tag 0EPK]**: for a proper `f : X ⟶ Y`, a morphism `g : Y ⟶ Z` and a bivariant
class `c` of degree `p` for `f ≫ g`, there is a bivariant class of degree `p` for `g` whose cap
operation is `α ↦ f'_*(c ∩ α)`. -/
theorem exists_isBivariantProperPushforward
    (hRG : ProperPushforwardFlatPullbackBaseChange C)
    (hgysP : G.IsNaturalUnderProperPushforward)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) :
    ∃ d : BivariantClass C G sY sZ g hg p,
      IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p c d :=
  ⟨bivariantProperPushforward C G sX sY sZ f g hf hg hpp p c hRG hgysP hgysc,
    isBivariantProperPushforward_bivariantProperPushforward C G sX sY sZ f g hf hg hpp p c hRG
      hgysP hgysc⟩

end Pushforward

end Stacks.Chow

end
