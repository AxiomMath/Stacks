module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality

/-!
# The Gysin condition of a composite of bivariant Chow classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of schemes locally of finite type over `S`, and let
`a ∈ A^p(X ⟶ Y)` and `b ∈ A^q(Y ⟶ Z)` be bivariant classes. Stacks 0B75 asserts that the cap
operation `α ↦ a ∩ (b ∩ α)` of `Stacks.Chow.bivariantCompositeCap` is again a bivariant class,
that is, that it satisfies the three naturality conditions of Stacks 0B76.
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality` proves the first two. This
file proves the third, the Gysin condition.

Fix a test scheme `t : T ⟶ Z` and a global section `s` of an invertible module `L` on `T` with
zero scheme `D = Z(s)`. The condition compares the cap operation at the test scheme `D ⟶ T ⟶ Z`
with the cap operation at `t` followed by the Gysin map of the divisor pulled back to `T ×_Z X`.
For a composite the comparison runs through the middle fibre product `T ×_Z Y`: the divisor is
pulled back there first, `b` is natural for *that* Gysin map, `a` is natural for the Gysin map of
the divisor pulled back once more to `(T ×_Z Y) ×_Y X`, and the associativity isomorphism
`(T ×_Z Y) ×_Y X ≅ T ×_Z X` carries the result to the divisor pulled back along the composite
projection. The three zero schemes involved are identified by Stacks 0B6Y, in the two shapes
`Stacks.Chow.bivariantDivisorBaseChangeIso` and `Stacks.Divisors.zeroScheme_pullback_comp`.

## Main results

* `Stacks.Chow.compositeDivisorIso_square` — the commuting square of divisor identifications the
  condition rests on: the associativity isomorphism of the two fibre products over the divisor
  agrees with the composite of the three Stacks 0B6Y identifications. This is the geometric
  content.
* `Stacks.Chow.bivariantCompositeOuterCap_gysin_naturality` — the outer cap operation
  `Stacks.Chow.bivariantCompositeOuterCap` commutes with the Gysin map of a pulled-back divisor:
  if a class on `D ×_Z Y`, read on the zero scheme of the pulled-back section, is the Gysin image
  of a class on `T ×_Z Y`, the same holds for their outer caps on `D ×_Z X` and `T ×_Z X`. Only
  the conditions for `a` enter.
* `Stacks.Chow.bivariantCompositeCap_gysin_naturality` — **the Gysin condition of Stacks 0B76 for
  the composite of Stacks 0B75**, granted the isomorphism case of Stacks 02TA for the Gysin system
  (`Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso`) and its iterated-pullback case
  (`Stacks.Chow.GysinSystem.IsNaturalUnderPullbackCompPushforward`).

## Implementation notes

### The two side conditions, and why they are properties of `G` rather than missing theorems

A `Stacks.Chow.GysinSystem` is a *choice*, for every base, every invertible module and every
degree, of a first Chern class rule (Stacks 02SO) together with its vanishing on rational
equivalences (Stacks 02TO). Nothing in that datum relates the choices made at two different
invertible modules, even when the two modules are isomorphic or indeed equal. The Gysin condition
for a composite compares three such choices:

* the one at `π₂^* ρ^* L`, where `π₂ : (T ×_Z Y) ×_Y X ⟶ T ×_Z Y` and `ρ : T ×_Z Y ⟶ T`, which is
  what the Gysin condition of `a` produces;
* the one at `(π₂ ≫ ρ)^* L`, the same invertible module read in one step — the two zero schemes
  are *equal* by `Stacks.Divisors.zeroScheme_pullback_comp`, but the two Chern class rules are
  unrelated data;
* the one at the pullback of `L` along `T ×_Z X ⟶ T`, which is what the condition being proved
  speaks about, and which sits on the scheme `T ×_Z X` isomorphic to `(T ×_Z Y) ×_Y X`.

`Stacks.Chow.GysinSystem.IsNaturalUnderPullbackCompPushforward` and
`Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso` are exactly the assertions that the first
two and the last two choices agree. Both hold for the Gysin map of Stacks 02TO, whose Chern class
rule depends on the invertible module only through its isomorphism class, and both are already
carried as hypotheses by `Stacks.Chow.bivariantRestriction` and `Stacks.Chow.bivariantTransport`
for the same reason. They are hypotheses here and not theorems because a
`Stacks.Chow.GysinSystem` is axiomatised, not constructed.

Neither hypothesis mentions a bivariant class, a cap operation or a composite: each is a statement
about `G` alone, quantified over arbitrary schemes and sections. In particular the proof below
assumes neither the Gysin condition it proves, nor `Stacks.Chow.IsBivariantClassComposition`, nor
the existence of a composite class. Everything else it uses is a naturality condition of `a` or of
`b`, an identification of zero schemes from Stacks 0B6Y, or the functoriality of proper pushforward
(Stacks 02R5) — the latter supplied for every proper morphism over the base by the instance of
Stacks 02S2 that `Stacks.Chow.bivariantCompositeCap` already carries.

### Why no instance of Stacks 02S1 is needed

Unlike the flat condition of `Stacks.Chow.bivariantCompositeCap_flat_naturality_of_factors`, the
Gysin condition needs no new instance of Stacks 02S1: every pushforward it performs is along an
isomorphism or along a base change of one, and `Stacks.Chow.ProperPushforwardDescends` — carried by
the composite's cap operation — supplies Stacks 02S2 for all of them.

### Reuse of the restriction assembly

The final diagram chase is `Stacks.Chow.gysinNaturalityAssemble` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction`, written for the Gysin condition of a
restricted class and fitting a composite unchanged: the three legs it wants are the associativity
isomorphism of the fibre products over the divisor, the composite of the Stacks 0B6Y
identifications, and the base-change isomorphism of the divisors, and the square relating them is
`Stacks.Chow.compositeDivisorIso_square`.

## References

* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport of a Chow class along an equality of degrees -/

/-- A transport along an equality of degrees is determined by the heterogeneous equality it
witnesses. -/
theorem eq_mp_index_of_heq {α : ℤ → Sort*} {i j : ℤ} (hij : i = j) {x : α i} {y : α j}
    (hxy : HEq x y) : Eq.mp (congrArg α hij) x = y := by
  cases hij
  exact eq_of_heq hxy

/-- A transport along an equality of degrees changes nothing. -/
theorem heq_eq_mp_index {α : ℤ → Sort*} {i j : ℤ} (hij : i = j) (x : α i) :
    HEq x (Eq.mp (congrArg α hij) x) := by
  cases hij
  rfl

/-! ### Pushforward along a threefold composite -/

/-- Proper pushforward on Chow groups along a morphism presented as a composite of three
morphisms is the composite of the three proper pushforwards. -/
theorem properChowPushforward_comp₃_apply (C : ChowSituation.{u}) {A B D' O' : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sD : D' ⟶ C.S) [LocallyOfFiniteType sD] (sO : O' ⟶ C.S) [LocallyOfFiniteType sO]
    (u : A ⟶ B) [IsProper u] (v : B ⟶ D') [IsProper v] (w : D' ⟶ O') [IsProper w]
    (hu : u ≫ sB = sA) (hv : v ≫ sD = sB) (hw : w ≫ sO = sD) (hvw : (v ≫ w) ≫ sO = sB)
    (huvw : (u ≫ v ≫ w) ≫ sO = sA) (k : ℤ)
    (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hfacv : ProperPushforwardFactorsThroughRationalEquivalence C sB sD v hv k)
    (hfacw : ProperPushforwardFactorsThroughRationalEquivalence C sD sO w hw k)
    (hfacvw : ProperPushforwardFactorsThroughRationalEquivalence C sB sO (v ≫ w) hvw k)
    (hfacuvw : ProperPushforwardFactorsThroughRationalEquivalence C sA sO (u ≫ v ≫ w) huvw k)
    (x : chowGroup C sA k) :
    properChowPushforward C sA sO (u ≫ v ≫ w) huvw k hfacuvw x =
      properChowPushforward C sD sO w hw k hfacw
        (properChowPushforward C sB sD v hv k hfacv
          (properChowPushforward C sA sB u hu k hfacu x)) := by
  rw [properChowPushforward_comp_apply C sA sB sO u (v ≫ w) (u ≫ v ≫ w) rfl hu hvw huvw k
      hfacu hfacvw hfacuvw x,
    properChowPushforward_comp_apply C sB sD sO v w (v ≫ w) rfl hv hw hvw k hfacv hfacw hfacvw]

/-! ### The structure morphisms of the two fibre products of a composite -/

/-- The projection `T ×_Z X ⟶ T` of the outer fibre product of a composite carries the structure
morphism of the test scheme to the structure morphism of `T ×_Z X`. -/
theorem compositeOuterSnd_comp_structure {C : ChowSituation.{u}} {X Y Z T : Scheme.{u}}
    (sX : X ⟶ C.S) (sY : Y ⟶ C.S) (sZ : Z ⟶ C.S) (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z)
    (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) :
    pullback.snd (f ≫ g) t ≫ (t ≫ sZ) = pullback.fst (f ≫ g) t ≫ sX := by
  rw [← Category.assoc, ← pullback.condition, Category.assoc,
    comp_comp_structureMorphism_eq hf hg]

/-- The projection `(T ×_Z Y) ×_Y X ⟶ T` of the inner fibre product of a composite carries the
structure morphism of the test scheme to the structure morphism of `(T ×_Z Y) ×_Y X`. -/
theorem compositeInnerSnd_comp_structure {C : ChowSituation.{u}} {X Y Z T : Scheme.{u}}
    (sX : X ⟶ C.S) (sY : Y ⟶ C.S) (sZ : Z ⟶ C.S) (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z)
    (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) :
    (pullback.snd f (pullback.fst g t) ≫ pullback.snd g t) ≫ (t ≫ sZ) =
      pullback.fst f (pullback.fst g t) ≫ sX := by
  rw [Category.assoc, ← Category.assoc (pullback.snd g t), ← pullback.condition, Category.assoc,
    hg, ← Category.assoc, ← pullback.condition, Category.assoc, hf]

/-! ### The identification of Stacks 0B6Y read against the projections of the middle fibre
product -/

section Divisor

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z) (L : T.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- The identification of Stacks 0B6Y lies over `Y`: composed with the projection of the base
change of the divisor to `Y` it is the projection of the base change of the test scheme. -/
theorem bivariantDivisorBaseChangeIso_hom_comp_fst :
    (bivariantDivisorBaseChangeIso g t L s).hom ≫
        ((Stacks.Divisors.zeroScheme (pullback g t)
            ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
          pullback.fst g t) =
      pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) :=
  comp_comp_of_eq (bivariantDivisorBaseChangeIso_hom_subschemeι g t L s)
    (compositeMiddleBaseChange_fst g t (Stacks.Divisors.zeroScheme T L s).subschemeι)

/-- The identification of Stacks 0B6Y lies over `T`: composed with the projection of the base
change of the divisor to `T` it is the closed immersion of the divisor, read through the
projection of the base change of the test scheme. -/
@[reassoc (attr := simp)]
theorem bivariantDivisorBaseChangeIso_hom_comp_snd :
    (bivariantDivisorBaseChangeIso g t L s).hom ≫
        ((Stacks.Divisors.zeroScheme (pullback g t)
            ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
          pullback.snd g t) =
      pullback.snd g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫
        (Stacks.Divisors.zeroScheme T L s).subschemeι :=
  comp_comp_of_eq (bivariantDivisorBaseChangeIso_hom_subschemeι g t L s)
    (compositeMiddleBaseChange_snd g t (Stacks.Divisors.zeroScheme T L s).subschemeι)

/-- **The geometric heart of the Gysin condition for a composite.** The associativity isomorphism

  `(D ×_Z Y) ×_Y X ≅ D ×_Z X`

of the fibre products over the zero scheme `D = Z(s)` agrees with the composite of the three
identifications of Stacks 0B6Y: the base change of `D` to `T ×_Z Y`, its base change once more to
`(T ×_Z Y) ×_Y X`, the equality of the two readings of the twice pulled-back section, and the
comparison of the zero schemes on the two isomorphic fibre products `(T ×_Z Y) ×_Y X` and
`T ×_Z X`.

Both sides are checked after composition with the closed immersion of the zero scheme on
`T ×_Z X`, which is a monomorphism; this is where the hypothesis `he` on the identification `e`
supplied by the Gysin condition is used. -/
theorem compositeDivisorIso_square
    (e : pullback (f ≫ g) ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≅
      (Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
        ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s)).subscheme)
    (he : e.hom ≫ (Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
          ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s)).subschemeι =
        bivariantBaseChangeMap (f ≫ g) t (Stacks.Divisors.zeroScheme T L s).subschemeι) :
    (pullbackRightPullbackFstIso g
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) f).hom ≫ e.hom =
      (baseChangeMapOfEq f
            ((Stacks.Divisors.zeroScheme (pullback g t)
                ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
                (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
              pullback.fst g t)
            (bivariantDivisorBaseChangeIso g t L s).hom
            (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t))
            (bivariantDivisorBaseChangeIso_hom_comp_fst g t L s) ≫
          (bivariantDivisorBaseChangeIso f (pullback.fst g t)
              ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
              (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).hom ≫
            eqToHom (congrArg Scheme.IdealSheafData.subscheme
              (Stacks.Divisors.zeroScheme_pullback_comp (pullback.snd f (pullback.fst g t))
                (pullback.snd g t) L s))) ≫
        (zeroSchemePullbackIso (pullback.snd f (pullback.fst g t) ≫ pullback.snd g t)
          (pullback.snd (f ≫ g) t) (pullbackRightPullbackFstIso g t f).hom
          (pullbackRightPullbackFstIso_hom_snd g t f) L s).hom := by
  rw [← cancel_mono (Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
    ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s)).subschemeι]
  simp only [Category.assoc]
  rw [he, zeroSchemePullbackIso_hom_subschemeι,
    ← Category.assoc (eqToHom (congrArg Scheme.IdealSheafData.subscheme
      (Stacks.Divisors.zeroScheme_pullback_comp (pullback.snd f (pullback.fst g t))
        (pullback.snd g t) L s))),
    subschemeι_eqToHom (Stacks.Divisors.zeroScheme_pullback_comp
      (pullback.snd f (pullback.fst g t)) (pullback.snd g t) L s),
    ← Category.assoc (bivariantDivisorBaseChangeIso f (pullback.fst g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).hom,
    bivariantDivisorBaseChangeIso_hom_subschemeι]
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp


end Divisor

/-! ### The comparison of divisors, read over the base -/

section DivisorStructure

variable {C : ChowSituation.{u}} {X Y Z T : Scheme.{u}} (sX : X ⟶ C.S) (sY : Y ⟶ C.S)
  (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z) (L : T.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- The identification of Stacks 0B6Y lies over the base: this is the hypothesis `hbase` of the
Gysin condition of `Stacks.Chow.BivariantClass` for the canonical identification. -/
theorem bivariantDivisorBaseChangeIso_hom_comp_structure :
    (bivariantDivisorBaseChangeIso g t L s).hom ≫
        ((Stacks.Divisors.zeroScheme (pullback g t)
            ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
          pullback.fst g t ≫ sY) =
      pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY :=
  comp_comp_of_eq (bivariantDivisorBaseChangeIso_hom_subschemeι g t L s) (by simp)

/-- The equality of the two readings of a twice pulled-back section lies over the base. -/
theorem zeroScheme_pullback_comp_eqToHom_comp_structure :
    eqToHom (congrArg Scheme.IdealSheafData.subscheme
        (Stacks.Divisors.zeroScheme_pullback_comp (pullback.snd f (pullback.fst g t))
          (pullback.snd g t) L s)) ≫
      ((Stacks.Divisors.zeroScheme (pullback f (pullback.fst g t))
        ((Scheme.Modules.pullback (pullback.snd f (pullback.fst g t) ≫
          pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections
          (pullback.snd f (pullback.fst g t) ≫ pullback.snd g t) L s)).subschemeι ≫
        pullback.fst f (pullback.fst g t) ≫ sX) =
      (Stacks.Divisors.zeroScheme (pullback f (pullback.fst g t))
        ((Scheme.Modules.pullback (pullback.snd f (pullback.fst g t))).obj
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L))
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f (pullback.fst g t))
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s))).subschemeι ≫
        pullback.fst f (pullback.fst g t) ≫ sX := by
  rw [← Category.assoc, subschemeι_eqToHom (Stacks.Divisors.zeroScheme_pullback_comp
    (pullback.snd f (pullback.fst g t)) (pullback.snd g t) L s)]

/-- The second and third legs of the divisor comparison of a composite, read over the base. -/
theorem compositeDivisorComparisonMiddle_comp_structure :
    ((bivariantDivisorBaseChangeIso f (pullback.fst g t)
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).hom ≫
        eqToHom (congrArg Scheme.IdealSheafData.subscheme
          (Stacks.Divisors.zeroScheme_pullback_comp (pullback.snd f (pullback.fst g t))
            (pullback.snd g t) L s))) ≫
      ((Stacks.Divisors.zeroScheme (pullback f (pullback.fst g t))
        ((Scheme.Modules.pullback (pullback.snd f (pullback.fst g t) ≫
          pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections
          (pullback.snd f (pullback.fst g t) ≫ pullback.snd g t) L s)).subschemeι ≫
        pullback.fst f (pullback.fst g t) ≫ sX) =
      pullback.fst f ((Stacks.Divisors.zeroScheme (pullback g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
        pullback.fst g t) ≫ sX := by
  rw [Category.assoc, zeroScheme_pullback_comp_eqToHom_comp_structure,
    bivariantDivisorBaseChangeIso_hom_comp_structure]

/-- The divisor comparison of a composite — the base change of the divisor to the middle fibre
product, its base change once more, and the equality of the two readings of the twice
pulled-back section — read over the base. -/
theorem compositeDivisorComparison_comp_structure :
    (baseChangeMapOfEq f
          ((Stacks.Divisors.zeroScheme (pullback g t)
            ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
            pullback.fst g t) (bivariantDivisorBaseChangeIso g t L s).hom
          (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t))
          (bivariantDivisorBaseChangeIso_hom_comp_fst g t L s) ≫
        (bivariantDivisorBaseChangeIso f (pullback.fst g t)
            ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).hom ≫
          eqToHom (congrArg Scheme.IdealSheafData.subscheme
            (Stacks.Divisors.zeroScheme_pullback_comp (pullback.snd f (pullback.fst g t))
              (pullback.snd g t) L s))) ≫
      ((Stacks.Divisors.zeroScheme (pullback f (pullback.fst g t))
        ((Scheme.Modules.pullback (pullback.snd f (pullback.fst g t) ≫
          pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections
          (pullback.snd f (pullback.fst g t) ≫ pullback.snd g t) L s)).subschemeι ≫
        pullback.fst f (pullback.fst g t) ≫ sX) =
      pullback.fst f (pullback.fst g
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t)) ≫ sX := by
  rw [Category.assoc, compositeDivisorComparisonMiddle_comp_structure,
    baseChangeMapOfEq_comp_structure]

end DivisorStructure

/-! ### The inner leg of the Gysin condition, abstractly -/

/-- The formal core of the inner leg of the Gysin condition for a composite: a cap product
pushed forward along a threefold composite, assembled from the Gysin naturality of the inner
class (`h2`), the proper naturality of the outer class (`h1`), the Gysin naturality of the outer
class (`h3`) and the comparison of the two readings of the twice pulled-back section (`h4`). -/
theorem gysinInnerLegAssemble (C : ChowSituation.{u}) {A B D' O' M : Scheme.{u}}
    {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {sB : B ⟶ C.S} [LocallyOfFiniteType sB]
    {sD : D' ⟶ C.S} [LocallyOfFiniteType sD] {sO : O' ⟶ C.S} [LocallyOfFiniteType sO]
    {sM : M ⟶ C.S} [LocallyOfFiniteType sM] {u : A ⟶ B} [IsProper u] {v : B ⟶ D'} [IsProper v]
    {w : D' ⟶ O'} [IsProper w] (hu : u ≫ sB = sA) (hv : v ≫ sD = sB) (hw : w ≫ sO = sD)
    (hvw : (v ≫ w) ≫ sO = sB) (huvw : (u ≫ v ≫ w) ≫ sO = sA) (m n : ℤ)
    (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu m)
    (hfacv : ProperPushforwardFactorsThroughRationalEquivalence C sB sD v hv m)
    (hfacw : ProperPushforwardFactorsThroughRationalEquivalence C sD sO w hw m)
    (hfacvw : ProperPushforwardFactorsThroughRationalEquivalence C sB sO (v ≫ w) hvw m)
    (hfacuvw : ProperPushforwardFactorsThroughRationalEquivalence C sA sO (u ≫ v ≫ w) huvw m)
    {x : chowGroup C sA m} {ξ y : chowGroup C sM n} {z : chowGroup C sD m}
    {r : chowGroup C sO m} {cap : chowGroup C sM n →+ chowGroup C sB m}
    (h1 : cap ξ = properChowPushforward C sA sB u hu m hfacu x) (h2 : ξ = y)
    (h3 : properChowPushforward C sB sD v hv m hfacv (cap y) = z)
    (h4 : properChowPushforward C sD sO w hw m hfacw z = r) :
    properChowPushforward C sA sO (u ≫ v ≫ w) huvw m hfacuvw x = r := by
  rw [properChowPushforward_comp₃_apply C sA sB sD sO u v w hu hv hw hvw huvw m hfacu hfacv
    hfacw hfacvw hfacuvw, ← h1, h2, h3, h4]

/-! ### The Gysin condition of a composite -/

section Composite

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z)
  [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
  (hpp : ProperPushforwardDescends C) (p q : ℤ) (a : BivariantClass C G sX sY f hf p)
  (b : BivariantClass C G sY sZ g hg q)

include hg in
/-- The outer cap operation of a composite commutes with the Gysin map of the zero scheme of a
section of an invertible module on a test scheme, in the following form. Let `t : T ⟶ Z` be a
test scheme, `D = Z(s) ⊆ T` the zero scheme of a section `s` of an invertible module `L` on `T`,
and let `ξ` on `D ×_Z Y` and `y` on `T ×_Z Y` be classes such that `ξ`, read on the zero scheme
of the pulled-back section by the identification of Stacks 0B6Y, is the Gysin map of `y`. Then
the outer cap of `ξ`, read on the zero scheme of the section pulled back to `T ×_Z X`, is the
Gysin map of the outer cap of `y`.

For `ξ` and `y` the inner caps `b ∩ i^* α` and `b ∩ α`, the hypothesis is the Gysin condition of
`b` and the conclusion is that of the composite,
`Stacks.Chow.bivariantCompositeCap_gysin_naturality`. The proof uses `a` alone: the
proper-pushforward condition of `a` along the Stacks 0B6Y identification of `D ×_Z Y` with the
pulled-back divisor — an isomorphism of test schemes over `Y`, hence proper — carries the outer
cap to that test scheme; the Gysin condition of `a` moves the Gysin map past it and onto the
divisor pulled back once more to `(T ×_Z Y) ×_Y X`; and the two hypotheses on `G` identify the
Gysin map there with the Gysin map of the divisor pulled back along `T ×_Z X ⟶ T`.
`Stacks.Chow.compositeDivisorIso_square` is the square that makes the four pushforwards agree.
The structure morphism `sZ` of `Z` only serves to put `T` over the base, which the hypothesis
`hgys` on the Gysin system quantifies over. -/
theorem bivariantCompositeOuterCap_gysin_naturality (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback (f ≫ g) t).sheaf.obj
      (pullback (f ≫ g) t).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)]
    (s : Γ(L, ⊤)) (m m' : ℤ) (hm : m' = m + 1)
    (ξ : chowGroup C
      (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY) m)
    (y : chowGroup C (pullback.fst g t ≫ sY) m')
    (hb : properChowPushforward C
        (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY)
        ((Stacks.Divisors.zeroScheme (pullback g t)
            ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
          pullback.fst g t ≫ sY)
        (bivariantDivisorBaseChangeIso g t L s).hom
        (bivariantDivisorBaseChangeIso_hom_comp_structure sY g t L s) m (hpp _ _ _ _ _) ξ =
      G.onChow (pullback.fst g t ≫ sY) ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s) m
        (Eq.mp (congrArg (chowGroup C (pullback.fst g t ≫ sY)) hm) y)) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s
    let E := Stacks.Divisors.zeroScheme (pullback (f ≫ g) t) L' s'
    ∀ (e : pullback (f ≫ g) (D.subschemeι ≫ t) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap (f ≫ g) t D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst (f ≫ g) t ≫ sX) =
        pullback.fst (f ≫ g) (D.subschemeι ≫ t) ≫ sX)
      (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst (f ≫ g) (D.subschemeι ≫ t) ≫ sX)
        (E.subschemeι ≫ pullback.fst (f ≫ g) t ≫ sX) e.hom hbase (m - p)),
      properChowPushforward C (pullback.fst (f ≫ g) (D.subschemeι ≫ t) ≫ sX)
          (E.subschemeι ≫ pullback.fst (f ≫ g) t ≫ sX) e.hom hbase (m - p) hfac
          (bivariantCompositeOuterCap C G sX sY f g hf hpp p a (D.subschemeι ≫ t) m ξ) =
        G.onChow (pullback.fst (f ≫ g) t ≫ sX) L' s' (m - p)
          (Eq.mp (congrArg (chowGroup C (pullback.fst (f ≫ g) t ≫ sX))
            (by omega : m' - p = (m - p) + 1))
            (bivariantCompositeOuterCap C G sX sY f g hf hpp p a t m' y)) := by
  dsimp only
  intro e he hbase hfac
  have hidxa : m + 1 - p = (m - p) + 1 := by omega
  have hidx : m' - p = (m - p) + 1 := by omega
  have hMfst := bivariantDivisorBaseChangeIso_hom_comp_fst g t L s
  have sqX := isPullback_baseChangeMapOfEq f
    ((Stacks.Divisors.zeroScheme (pullback g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
      pullback.fst g t) (bivariantDivisorBaseChangeIso g t L s).hom
    (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t)) hMfst
  have hpropX := MorphismProperty.of_isPullback sqX (P := @IsProper) inferInstance
  have hQ := pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t
  have hQD := pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t)
  have hpA := compositeInnerSnd_comp_structure sX sY sZ f g t hf hg
  have hpB := compositeOuterSnd_comp_structure sX sY sZ f g t hf hg
  have hMbase := bivariantDivisorBaseChangeIso_hom_comp_structure sY g t L s
  have hXfst := baseChangeMapOfEq_fst f
    ((Stacks.Divisors.zeroScheme (pullback g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
      pullback.fst g t) (bivariantDivisorBaseChangeIso g t L s).hom
    (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t)) hMfst
  have hXbase := baseChangeMapOfEq_comp_structure sX f
    ((Stacks.Divisors.zeroScheme (pullback g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
      pullback.fst g t) (bivariantDivisorBaseChangeIso g t L s).hom
    (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t)) hMfst
  have hEbase := bivariantDivisorBaseChangeIso_hom_subschemeι f (pullback.fst g t)
    ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)
  have hAbase := bivariantDivisorBaseChangeIso_hom_comp_structure sX f (pullback.fst g t)
    ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)
  have hzcbase := zeroScheme_pullback_comp_eqToHom_comp_structure sX f g t L s
  have hvbase := compositeDivisorComparisonMiddle_comp_structure sX f g t L s
  have hwbase := compositeDivisorComparison_comp_structure sX f g t L s
  have hj := zeroSchemePullbackIso_hom_subschemeι
    (pullback.snd f (pullback.fst g t) ≫ pullback.snd g t) (pullback.snd (f ≫ g) t)
    (pullbackRightPullbackFstIso g t f).hom (pullbackRightPullbackFstIso_hom_snd g t f) L s
  have hjbase := comp_comp_of_comp hj hQ
  -- the proper-pushforward condition of `a`, along the Stacks 0B6Y identification of test
  -- schemes over `Y`
  have ha := a.proper_naturality_of_test_eq
    ((Stacks.Divisors.zeroScheme (pullback g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
      pullback.fst g t) (bivariantDivisorBaseChangeIso g t L s).hom
    (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t)) hMfst _ sqX hXfst
    m hMbase (hpp _ _ _ _ _) (hpp _ _ _ _ _) ξ
  -- the Gysin condition of `a`, at the test scheme `T ×_Z Y ⟶ Y`
  have hagys := a.gysin_naturality (pullback.fst g t)
    ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s) m
    (bivariantDivisorBaseChangeIso f (pullback.fst g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)) hEbase hAbase
    (hpp _ _ _ _ _)
    (Eq.mp (congrArg (chowGroup C (pullback.fst g t ≫ sY)) hm) y)
  -- the two readings of the twice pulled-back section
  have hcomp := hgysc (pullback.snd f (pullback.fst g t)) (pullback.snd g t)
    (pullback.fst f (pullback.fst g t) ≫ sX) L s (m - p)
    (Eq.mp (congrArg (chowGroup C (pullback.fst f (pullback.fst g t) ≫ sX)) hidxa)
      (a.cap (pullback.fst g t) (m + 1)
        (Eq.mp (congrArg (chowGroup C (pullback.fst g t ≫ sY)) hm) y)))
  -- the two degree transports agree
  have hdelta : Eq.mp (congrArg (chowGroup C (pullback.fst f (pullback.fst g t) ≫ sX)) hidx)
        (a.cap (pullback.fst g t) m' y) =
      Eq.mp (congrArg (chowGroup C (pullback.fst f (pullback.fst g t) ≫ sX)) hidxa)
        (a.cap (pullback.fst g t) (m + 1)
          (Eq.mp (congrArg (chowGroup C (pullback.fst g t ≫ sY)) hm) y)) :=
    eq_mp_index_of_heq hidx
      ((heq_map_index (α := fun n ↦ chowGroup C (pullback.fst g t ≫ sY) n)
          (β := fun n ↦ chowGroup C (pullback.fst f (pullback.fst g t) ≫ sX) (n - p)) hm
          (heq_eq_mp_index hm y)
          fun n x ↦ a.cap (pullback.fst g t) n x).trans
        (heq_eq_mp_index hidxa _))
  -- the isomorphism case of Stacks 02TA, along the associativity isomorphism of the fibre
  -- products
  have hgysApplied := GysinSystem.onChow_baseChangeIso hgys (t ≫ sZ)
    (pullback.snd f (pullback.fst g t) ≫ pullback.snd g t) (pullback.snd (f ≫ g) t)
    (pullback.fst f (pullback.fst g t) ≫ sX) (pullback.fst (f ≫ g) t ≫ sX) hpA hpB
    (pullbackRightPullbackFstIso g t f).hom (pullbackRightPullbackFstIso_hom_snd g t f) hQ L s
    (m - p)
    (zeroSchemePullbackIso (pullback.snd f (pullback.fst g t) ≫ pullback.snd g t)
      (pullback.snd (f ≫ g) t) (pullbackRightPullbackFstIso g t f).hom
      (pullbackRightPullbackFstIso_hom_snd g t f) L s).hom
    hj hjbase (hpp _ _ _ _ _)
    (hpp _ _ _ _ _)
    (Eq.mp (congrArg (chowGroup C (pullback.fst f (pullback.fst g t) ≫ sX)) hidx)
      (a.cap (pullback.fst g t) m' y))
  refine gysinNaturalityAssemble C hQD hbase hwbase hjbase hQ
    (compositeDivisorIso_square f g t L s e he) hidx (hpp _ _ _ _ _) hfac (hpp _ _ _ _ _)
    (hpp _ _ _ _ _) (hpp _ _ _ _ _) (hpp _ _ _ _ _)
    (bivariantCompositeOuterCap_apply C G sX sY f g hf hpp p a
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) m ξ)
    (bivariantCompositeOuterCap_apply C G sX sY f g hf hpp p a t m' y) ?_
    hgysApplied
  rw [hdelta]
  exact gysinInnerLegAssemble C hXbase hAbase hzcbase hvbase hwbase (m - p) m
    (hpp _ _ _ _ _) (hpp _ _ _ _ _) (hpp _ _ _ _ _) (hpp _ _ _ _ _) (hpp _ _ _ _ _) ha hb
    hagys hcomp

/-- **Stacks 0B75.** The Gysin condition of Stacks 0B76 for the composite of two bivariant
classes: the cap operation `α ↦ a ∩ (b ∩ α)` commutes with the Gysin map of the zero scheme of a
section of an invertible module on a test scheme.

The Gysin condition of `b`, applied at the test scheme `t`, moves the Gysin map past the inner cap
and onto the divisor pulled back to the middle fibre product `T ×_Z Y`;
`Stacks.Chow.bivariantCompositeOuterCap_gysin_naturality` moves it past the outer cap.

Both hypotheses on the Gysin system are properties of the system alone and neither involves a
bivariant class; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinNaturality`. -/
theorem bivariantCompositeCap_gysin_naturality (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback (f ≫ g) t).sheaf.obj
      (pullback (f ≫ g) t).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s
    let E := Stacks.Divisors.zeroScheme (pullback (f ≫ g) t) L' s'
    ∀ (e : pullback (f ≫ g) (D.subschemeι ≫ t) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap (f ≫ g) t D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst (f ≫ g) t ≫ sX) =
        pullback.fst (f ≫ g) (D.subschemeι ≫ t) ≫ sX)
      (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst (f ≫ g) (D.subschemeι ≫ t) ≫ sX)
        (E.subschemeι ≫ pullback.fst (f ≫ g) t ≫ sX) e.hom hbase (k - q - p))
      (α : chowGroup C (t ≫ sZ) (k + 1)),
      properChowPushforward C (pullback.fst (f ≫ g) (D.subschemeι ≫ t) ≫ sX)
          (E.subschemeι ≫ pullback.fst (f ≫ g) t ≫ sX) e.hom hbase (k - q - p) hfac
          (bivariantCompositeCap C G sX sY sZ f g hf hg hpp p q a b (D.subschemeι ≫ t) k
            (G.onChow (t ≫ sZ) L s k α)) =
        G.onChow (pullback.fst (f ≫ g) t ≫ sX) L' s' (k - q - p)
          (Eq.mp (congrArg (chowGroup C (pullback.fst (f ≫ g) t ≫ sX))
            (by omega : (k + 1) - q - p = (k - q - p) + 1))
            (bivariantCompositeCap C G sX sY sZ f g hf hg hpp p q a b t (k + 1) α)) := by
  dsimp only
  intro e he hbase hfac α
  exact bivariantCompositeOuterCap_gysin_naturality C G sX sY sZ f g hf hg hpp p a hgys hgysc t
    L s (k - q) ((k + 1) - q) (by omega)
    (b.cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) k (G.onChow (t ≫ sZ) L s k α))
    (b.cap t (k + 1) α)
    (b.gysin_naturality t L s k (bivariantDivisorBaseChangeIso g t L s)
      (bivariantDivisorBaseChangeIso_hom_subschemeι g t L s)
      (bivariantDivisorBaseChangeIso_hom_comp_structure sY g t L s) (hpp _ _ _ _ _) α)
    e he hbase hfac

end Composite

end Stacks.Chow

end
