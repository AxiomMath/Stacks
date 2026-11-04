module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem

/-!
# The Gysin axiom of a proper pushforward of a bivariant Chow class

Let `f : X ⟶ Y` be proper, `g : Y ⟶ Z` locally of finite type, and let `c ∈ A^p(X ⟶ Z)` be a
bivariant class for the composite. Stacks 0EPK asserts that the rule

  `α ↦ f'_*(c ∩ α)`,

where `f' : T ×_Z X ⟶ T ×_Z Y` is the base change of `f` along a test scheme `t : T ⟶ Z`, is a
bivariant class of degree `p` for `g`. This file supplies the third naturality axiom of Stacks
0B76 for that rule, the Gysin axiom, which is the part of the source proof carried by Stacks 02TA.
The first two are `Stacks.Chow.bivariantProperPushforwardCap_proper_naturality` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward` and
`Stacks.Chow.bivariantProperPushforwardCap_flat_naturality_of_factors` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardFlatPullback`.

## Main results

* `Stacks.Chow.bivariantBaseChangeMap_bivariantPushforwardBaseChange` — the two base changes of
  `f` and the two base-change maps of test schemes commute. This is the square the whole file runs
  on, extracted so that it is proved once.
* `Stacks.Chow.bivariantPushforwardDivisorHom` — the morphism of Remark 0B6Y of the base change
  of `f`, read between the two zero schemes the Gysin axiom speaks about, and
  `Stacks.Chow.bivariantPushforwardDivisorSquare` — the square it fills with the two
  identifications of the base changes of the divisor.
* `Stacks.Chow.bivariantProperPushforwardGysinTransport` — **Stacks 02TA along the base change of
  `f`**, in the shape the axiom needs: the Gysin map of the divisor pulled back to `T ×_Z Y`,
  applied to a class pushed forward from `T ×_Z X`, is the pushforward along
  `Stacks.Chow.bivariantPushforwardDivisorHom` of the Gysin map read at the module pulled back to
  `T ×_Z X` in one step.
* `Stacks.Chow.bivariantProperPushforwardCap_gysin_naturality_of_isNatural` — **the Gysin axiom of
  Stacks 0B76
  for the rule of Stacks 0EPK**.
* `Stacks.Chow.bivariantProperPushforwardOfNaturality` — **Stacks 0EPK, existence**: with the three
  axioms in
  hand, the rule assembled into a bivariant class, and
  `Stacks.Chow.isBivariantProperPushforward_bivariantProperPushforwardOfNaturality` the
  verification that it
  caps by that rule.
* `Stacks.Chow.existsUnique_isBivariantProperPushforward` — **the full statement of Stacks 0EPK**:
  the pushed-forward class exists and is unique.

## Implementation notes

### The shape of the argument

The axiom for `f_* ∘ c` is handed one identification of the base change of a zero scheme with the
zero scheme of a pulled-back section, namely the one for `g`; invoking the axiom for `c` needs the
one for `f ≫ g`, which is `Stacks.Chow.bivariantDivisorBaseChangeIso`. The two meet in the square
`Stacks.Chow.bivariantPushforwardDivisorSquare`, whose fourth leg is the morphism of Remark 0B6Y
(Stacks 0B6Y) of the base change of `f`. So the axiom is the composite of three steps:

* the Gysin axiom of `c` at the same test scheme, module and section, taken at
  `Stacks.Chow.bivariantDivisorBaseChangeIso`;
* functoriality of proper pushforward (Stacks 02R5) traversing that square, which is
  `Stacks.Chow.properChowPushforward_comp_eq`;
* Stacks 02TA along the base change of `f`, which is
  `Stacks.Chow.bivariantProperPushforwardGysinTransport`.

The square is proved once, as
`Stacks.Chow.bivariantBaseChangeMap_bivariantPushforwardBaseChange`, and the identification of
the two zero schemes over `T ×_Z X` once, as `Stacks.Chow.bivariantPushforwardDivisorHom` together
with `Stacks.Chow.bivariantPushforwardDivisorHom_subschemeι`; no declaration below pays twice for
either. The final diagram chase is term-mode with every argument pinned.

### The two carried hypotheses, and why they are not theorems

A `Stacks.Chow.GysinSystem` is a *choice*, for every base, every invertible module and every
degree, of a first Chern class rule (Stacks 02SO) together with its vanishing on rational
equivalences (Stacks 02TO); nothing in that datum relates the choices made at two different
invertible modules, even isomorphic or equal ones. Two cases of Stacks 02TA for the system are
therefore carried as hypotheses:

* `Stacks.Chow.GysinSystem.IsNaturalUnderProperPushforward`, the proper-pushforward case, used
  along the base change `T ×_Z X ⟶ T ×_Z Y` of `f`;
* `Stacks.Chow.GysinSystem.IsNaturalUnderPullbackCompPushforward`, the iterated-pullback case,
  which reconciles the module pulled back to `T ×_Z Y` and then to `T ×_Z X` with the module
  pulled back to `T ×_Z X` in one step — the two zero schemes are *equal*, by
  `Stacks.Divisors.zeroScheme_pullback_comp_eq`, but the two Chern class rules are unrelated data.

Both are properties of `G` alone, quantified over arbitrary schemes and sections, and both are
discharged for the canonical system of the genuine first Chern class rule:
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderProperPushforward` of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem` and
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.BaseChangeIsoGysinSystem`. The same two hypotheses
are carried in exactly this way by `Stacks.Chow.envelopeDescentCap_gysin_naturality` and
`Stacks.Chow.bivariantCompositeCap_gysin_naturality`.

Since both hold for the canonical Gysin system, the declarations below are not registered under
Stacks 0EPK themselves: the full statement, for `A^p(-) = Stacks.Chow.CanonicalBivariantClass`
with nothing carried, is `Stacks.Chow.canonicalBivariantProperPushforward` and
`Stacks.Chow.existsUnique_canonicalBivariantProperPushforward` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardCanonical`, instantiating them.

Nothing else is assumed. In particular the integral-component hypothesis
`Stacks.Chow.GysinCompatibleWithPushforward` is *not* carried: the instance of Stacks 02TA behind
the proper-pushforward case is
`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_of_gysinCompatible`, which despite
its name assumes nothing beyond the properness of the morphism and its commutativity over the
base — the suffix is a leftover from a superseded conditional version, and the conditional
statement is the separate `Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward`.

### Why no instance of Stacks 02S1 is needed

Every pushforward performed here is along the base change of the proper morphism `f`, along an
isomorphism, or along the morphism of Remark 0B6Y of one of those; the instance of Stacks 02S2
that `Stacks.Chow.bivariantProperPushforwardCap` already carries supplies all of them.

## References

* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
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

/-! ### The square of the two base changes of the proper morphism -/

/-- The two base changes of `f : X ⟶ Y` along test schemes `h ≫ t` and `t` commute with the two
base-change maps of the test schemes induced by `h`:

  `T' ×_Z X --> T ×_Z X`
  `|              |`
  `T' ×_Z Y --> T ×_Z Y`

the vertical legs being the base changes of `f` and the horizontal ones the maps induced by `h`.
All four legs are determined by their composites with the projections, so this is
`CategoryTheory.Limits.pullback.hom_ext`. -/
theorem bivariantBaseChangeMap_bivariantPushforwardBaseChange {X Y Z T T' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z) (h : T' ⟶ T) :
    bivariantBaseChangeMap (f ≫ g) t h ≫ bivariantPushforwardBaseChange f g t =
      bivariantPushforwardBaseChange f g (h ≫ t) ≫ bivariantBaseChangeMap g t h := by
  refine pullback.hom_ext ?_ ?_ <;> simp [bivariantBaseChangeMap]

/-! ### The morphism of Remark 0B6Y of the base change of the proper morphism -/

section Divisor

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {T : Scheme.{u}} (t : T ⟶ Z)
  (L : T.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **The morphism of Remark 0B6Y of the base change of `f`.** The zero scheme of the section
pulled back to `T ×_Z X` lies over the zero scheme of the section pulled back to `T ×_Z Y`.

The morphism of Remark 0B6Y, `Stacks.Chow.zeroSchemePullbackHom`, is stated for the module pulled
back along the base change of `f` from `T ×_Z Y`; the Gysin axiom of `Stacks.Chow.BivariantClass`
for `f ≫ g` speaks about the module pulled back from `T` in one step. The two zero schemes are
equal by `Stacks.Divisors.zeroScheme_pullback_comp_eq`, since the base change of `f` composed with
the projection to `T` *is* the projection to `T`, and the transport along that equality is
prefixed here. -/
def bivariantPushforwardDivisorHom :
    (Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
        ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s)).subscheme ⟶
      (Stacks.Divisors.zeroScheme (pullback g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subscheme :=
  eqToHom (congrArg Scheme.IdealSheafData.subscheme
      (Stacks.Divisors.zeroScheme_pullback_comp_eq (bivariantPushforwardBaseChange f g t)
        (pullback.snd g t) (pullback.snd (f ≫ g) t)
        (bivariantPushforwardBaseChange_snd f g t) L s).symm) ≫
    zeroSchemePullbackHom (bivariantPushforwardBaseChange f g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)

/-- The morphism of Remark 0B6Y of the base change of `f` is proper: it is an isomorphism followed
by the morphism of Remark 0B6Y of a proper morphism. -/
instance isProper_bivariantPushforwardDivisorHom [IsProper f] :
    IsProper (bivariantPushforwardDivisorHom f g t L s) := by
  unfold bivariantPushforwardDivisorHom
  infer_instance

/-- **The square of Remark 0B6Y for the base change of `f`.** The morphism of
`Stacks.Chow.bivariantPushforwardDivisorHom` lies over the base change of `f`. -/
theorem bivariantPushforwardDivisorHom_subschemeι :
    bivariantPushforwardDivisorHom f g t L s ≫
        (Stacks.Divisors.zeroScheme (pullback g t)
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι =
      (Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
          ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s)).subschemeι ≫
        bivariantPushforwardBaseChange f g t := by
  rw [bivariantPushforwardDivisorHom, Category.assoc, zeroSchemePullbackHom_subschemeι,
    ← Category.assoc, subschemeι_eqToHom (Stacks.Divisors.zeroScheme_pullback_comp_eq _ _ _
      (bivariantPushforwardBaseChange_snd f g t) L s).symm]

/-- The morphism of Remark 0B6Y of the base change of `f` commutes over the base scheme of the
Chow situation. -/
theorem bivariantPushforwardDivisorHom_comp_structure {C : ChowSituation.{u}} (sX : X ⟶ C.S)
    (sY : Y ⟶ C.S) (hf : f ≫ sY = sX) :
    bivariantPushforwardDivisorHom f g t L s ≫
        ((Stacks.Divisors.zeroScheme (pullback g t)
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
            (pullback.fst g t ≫ sY)) =
      (Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
          ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s)).subschemeι ≫
        (pullback.fst (f ≫ g) t ≫ sX) :=
  comp_comp_of_eq (bivariantPushforwardDivisorHom_subschemeι f g t L s)
    (by rw [Category.assoc, bivariantPushforwardBaseChange_comp_structure hf g t])

/-- **The square of divisor identifications the Gysin axiom of Stacks 0EPK rests on.** The base
change of `f` over the divisor, followed by the identification of the base change of the divisor
along `g`, is the identification of the base change of the divisor along `f ≫ g` followed by the
morphism of Remark 0B6Y of the base change of `f`.

Both sides are morphisms into the zero scheme of the section pulled back to `T ×_Z Y`, so the
closed immersion of that zero scheme may be cancelled; what remains is
`Stacks.Chow.bivariantBaseChangeMap_bivariantPushforwardBaseChange`. -/
theorem bivariantPushforwardDivisorSquare
    (e : pullback g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≅
      (Stacks.Divisors.zeroScheme (pullback g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subscheme)
    (he : e.hom ≫ (Stacks.Divisors.zeroScheme (pullback g t)
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι =
      bivariantBaseChangeMap g t (Stacks.Divisors.zeroScheme T L s).subschemeι) :
    bivariantPushforwardBaseChange f g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫
        e.hom =
      (bivariantDivisorBaseChangeIso (f ≫ g) t L s).hom ≫
        bivariantPushforwardDivisorHom f g t L s := by
  refine (cancel_mono (Stacks.Divisors.zeroScheme (pullback g t)
    ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι).1 ?_
  rw [Category.assoc, he, Category.assoc, bivariantPushforwardDivisorHom_subschemeι,
    ← Category.assoc, bivariantDivisorBaseChangeIso_hom_subschemeι,
    bivariantBaseChangeMap_bivariantPushforwardBaseChange]

end Divisor

/-! ### Stacks 02TA along the base change of the proper morphism -/

section Gysin

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f]
  (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
  (hpp : ProperPushforwardDescends C) (p : ℤ)

omit [LocallyOfFiniteType g] in
/-- **Stacks 02TA along the base change of `f`.** The Gysin map of the divisor pulled back to
`T ×_Z Y`, applied to a class pushed forward from `T ×_Z X` along the base change of `f`, is the
pushforward along `Stacks.Chow.bivariantPushforwardDivisorHom` of the Gysin map there -- read at
the invertible module pulled back from `T` in one step, which is the reading the Gysin axiom of a
bivariant class for `f ≫ g` produces.

Two cases of Stacks 02TA for the Gysin system are used: the proper-pushforward case along the base
change of `f`, which produces the module pulled back to `T ×_Z Y` and then to `T ×_Z X`, and the
iterated-pullback case `Stacks.Chow.GysinSystem.onChow_pullbackComp`, which reconciles that
reading with the one-step one. -/
theorem bivariantProperPushforwardGysinTransport (hgysP : G.IsNaturalUnderProperPushforward)
    (hgysC : G.IsNaturalUnderPullbackCompPushforward) {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (m : ℤ) (x : chowGroup C (pullback.fst (f ≫ g) t ≫ sX) (m + 1)) :
    G.onChow (pullback.fst g t ≫ sY) ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s) m
        (properChowPushforward C (pullback.fst (f ≫ g) t ≫ sX) (pullback.fst g t ≫ sY)
          (bivariantPushforwardBaseChange f g t)
          (bivariantPushforwardBaseChange_comp_structure hf g t) (m + 1)
          (hpp _ _ _ _ _) x) =
      properChowPushforward C
        ((Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
          ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s)).subschemeι ≫
            (pullback.fst (f ≫ g) t ≫ sX))
        ((Stacks.Divisors.zeroScheme (pullback g t)
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
            (pullback.fst g t ≫ sY))
        (bivariantPushforwardDivisorHom f g t L s)
        (bivariantPushforwardDivisorHom_comp_structure f g t L s sX sY hf) m (hpp _ _ _ _ _)
        (G.onChow (pullback.fst (f ≫ g) t ≫ sX)
          ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s) m x) := by
  have hsnd := bivariantPushforwardBaseChange_snd f g t
  have hcomp := Stacks.Divisors.zeroScheme_pullback_comp_eq
    (bivariantPushforwardBaseChange f g t) (pullback.snd g t) (pullback.snd (f ≫ g) t) hsnd L s
  have huv : eqToHom (congrArg Scheme.IdealSheafData.subscheme hcomp) ≫
      bivariantPushforwardDivisorHom f g t L s =
      zeroSchemePullbackHom (bivariantPushforwardBaseChange f g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s) := by
    rw [bivariantPushforwardDivisorHom, ← Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp]
  have hu : eqToHom (congrArg Scheme.IdealSheafData.subscheme hcomp) ≫
      ((Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
        ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s)).subschemeι ≫
          (pullback.fst (f ≫ g) t ≫ sX)) =
      (pullbackZeroScheme (bivariantPushforwardBaseChange f g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
        (pullback.fst (f ≫ g) t ≫ sX) :=
    comp_comp_of_eq (subschemeι_eqToHom hcomp) rfl
  exact (hgysP (pullback.fst (f ≫ g) t ≫ sX) (pullback.fst g t ≫ sY)
        (bivariantPushforwardBaseChange f g t)
        (bivariantPushforwardBaseChange_comp_structure hf g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s) m
        (zeroSchemePullbackHom (bivariantPushforwardBaseChange f g t)
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s))
        (zeroSchemePullbackHom_subschemeι _ _ _) (hpp _ _ _ _ _) (hpp _ _ _ _ _) x).trans
    ((properChowPushforward_comp_apply C _ _ _
          (eqToHom (congrArg Scheme.IdealSheafData.subscheme hcomp))
          (bivariantPushforwardDivisorHom f g t L s)
          (zeroSchemePullbackHom (bivariantPushforwardBaseChange f g t)
            ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)) huv hu
          (bivariantPushforwardDivisorHom_comp_structure f g t L s sX sY hf)
          (zeroSchemeSquare_comp_structureMorphism C (pullback.fst (f ≫ g) t ≫ sX)
            (pullback.fst g t ≫ sY) (bivariantPushforwardBaseChange f g t)
            (bivariantPushforwardBaseChange_comp_structure hf g t)
            ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)
            (zeroSchemePullbackHom (bivariantPushforwardBaseChange f g t)
              ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
              (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s))
            (zeroSchemePullbackHom_subschemeι _ _ _)) m (hpp _ _ _ _ _) (hpp _ _ _ _ _)
          (hpp _ _ _ _ _) _).trans
      (DFunLike.congr_arg (properChowPushforward C _ _
          (bivariantPushforwardDivisorHom f g t L s)
          (bivariantPushforwardDivisorHom_comp_structure f g t L s sX sY hf) m (hpp _ _ _ _ _))
        (GysinSystem.onChow_pullbackComp hgysC (bivariantPushforwardBaseChange f g t)
          (pullback.snd g t) (pullback.snd (f ≫ g) t) hsnd
          (pullback.fst (f ≫ g) t ≫ sX) L s m x)))

/-! ### The Gysin axiom of the pushed-forward class -/

/-- **Stacks 0EPK.** The Gysin axiom of Stacks 0B76 for the rule of Stacks 0EPK: the cap operation
`α ↦ f'_*(c ∩ α)` commutes with the Gysin map of the zero scheme of a section of an invertible
module on a test scheme.

Two cases of Stacks 02TA for the Gysin system are carried, the proper-pushforward case and the
iterated-pullback case; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardGysin` for why they are hypotheses
on `G` rather than missing theorems, and that nothing else is assumed. -/
theorem bivariantProperPushforwardCap_gysin_naturality_of_isNatural
    (hgysP : G.IsNaturalUnderProperPushforward)
    (hgysC : G.IsNaturalUnderPullbackCompPushforward)
    (c : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p)
    {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd g t)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s
    let E := Stacks.Divisors.zeroScheme (pullback g t) L' s'
    ∀ (e : pullback g (D.subschemeι ≫ t) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap g t D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst g t ≫ sY) =
        pullback.fst g (D.subschemeι ≫ t) ≫ sY)
      (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst g (D.subschemeι ≫ t) ≫ sY) (E.subschemeι ≫ pullback.fst g t ≫ sY) e.hom
        hbase (k - p))
      (α : chowGroup C (t ≫ sZ) (k + 1)),
      properChowPushforward C (pullback.fst g (D.subschemeι ≫ t) ≫ sY)
          (E.subschemeι ≫ pullback.fst g t ≫ sY) e.hom hbase (k - p) hfac
          (bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c (D.subschemeι ≫ t) k
            (G.onChow (t ≫ sZ) L s k α)) =
        G.onChow (pullback.fst g t ≫ sY) L' s' (k - p)
          (Eq.mp (congrArg (chowGroup C (pullback.fst g t ≫ sY))
              (by omega : (k + 1) - p = (k - p) + 1))
            (bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c t (k + 1) α)) := by
  dsimp only
  intro e he hbase hfac α
  have hidx : (k + 1) - p = (k - p) + 1 := by omega
  -- the identification of Stacks 0B6Y of the base change of the divisor along `f ≫ g`
  have heX := bivariantDivisorBaseChangeIso_hom_subschemeι (f ≫ g) t L s
  have hbcmX : bivariantBaseChangeMap (f ≫ g) t (Stacks.Divisors.zeroScheme T L s).subschemeι ≫
      (pullback.fst (f ≫ g) t ≫ sX) =
      pullback.fst (f ≫ g) ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sX := by
    simp [bivariantBaseChangeMap]
  have hbaseX := comp_comp_of_eq heX hbcmX
  have hfacX := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ hbaseX (k - p)
  -- the Gysin axiom of `c` at the same test scheme, module and section
  have hcX := c.gysin_naturality t L s k (bivariantDivisorBaseChangeIso (f ≫ g) t L s) heX
    hbaseX hfacX α
  -- the square of the two identifications and the two base changes of `f`
  have hsq := bivariantPushforwardDivisorSquare f g t L s e he
  -- Stacks 02TA along the base change of `f`
  have hT := bivariantProperPushforwardGysinTransport C G sX sY f g hf hpp hgysP hgysC t L s
    (k - p) (Eq.mp (congrArg (chowGroup C (pullback.fst (f ≫ g) t ≫ sX)) hidx)
      (c.cap t (k + 1) α))
  exact (properChowPushforward_comp_eq C (pullback.fst (f ≫ g)
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sX)
        (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY)
        ((Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
          ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s)).subschemeι ≫
            (pullback.fst (f ≫ g) t ≫ sX))
        ((Stacks.Divisors.zeroScheme (pullback g t)
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
            (pullback.fst g t ≫ sY))
        (bivariantPushforwardBaseChange f g
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t))
        e.hom (bivariantDivisorBaseChangeIso (f ≫ g) t L s).hom
        (bivariantPushforwardDivisorHom f g t L s) hsq
        (bivariantPushforwardBaseChange_comp_structure hf g
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t))
        hbase hbaseX (bivariantPushforwardDivisorHom_comp_structure f g t L s sX sY hf) (k - p)
        (hpp _ _ _ _ _) hfac hfacX (hpp _ _ _ _ _)
        (c.cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) k
          (G.onChow (t ≫ sZ) L s k α))).trans
    ((DFunLike.congr_arg (properChowPushforward C _ _
          (bivariantPushforwardDivisorHom f g t L s)
          (bivariantPushforwardDivisorHom_comp_structure f g t L s sX sY hf) (k - p)
          (hpp _ _ _ _ _)) hcX).trans
      (hT.symm.trans
        (DFunLike.congr_arg (G.onChow (pullback.fst g t ≫ sY)
            ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s) (k - p))
          (properChowPushforward_cast C (pullback.fst (f ≫ g) t ≫ sX) (pullback.fst g t ≫ sY)
            (bivariantPushforwardBaseChange f g t)
            (bivariantPushforwardBaseChange_comp_structure hf g t) hidx (hpp _ _ _ _ _)
            (hpp _ _ _ _ _) (c.cap t (k + 1) α)).symm)))

/-! ### The pushed-forward bivariant class -/

/-- **Stacks 0EPK, existence.** The rule `α ↦ f'_*(c ∩ α)` is a bivariant class of degree `p` for
`g : Y ⟶ Z`: the three naturality axioms of Stacks 0B76 are
`Stacks.Chow.bivariantProperPushforwardCap_proper_naturality` (Stacks 02R5),
`Stacks.Chow.bivariantProperPushforwardCap_flat_naturality_of_factors` (Stacks 02RG) and
`Stacks.Chow.bivariantProperPushforwardCap_gysin_naturality_of_isNatural` (Stacks 02TA).

Beyond the hypotheses of the tag -- the properness of `f` and the finite type of `g` as instances,
the two commutations over the base, and the instance of Stacks 02S2 that the cap operation needs
-- two cases of Stacks 02TA for the Gysin system are carried, the proper-pushforward case and the
iterated-pullback case. They are not theorems because a `Stacks.Chow.GysinSystem` is axiomatised
data which assigns unrelated first Chern class rules to isomorphic invertible modules; both are
discharged for the canonical system of the genuine first Chern class rule. The same two hypotheses
are carried for the same reason by `Stacks.Chow.envelopeDescentClass` and
`Stacks.Chow.bivariantComposite`. -/
def bivariantProperPushforwardOfNaturality (hgysP : G.IsNaturalUnderProperPushforward)
    (hgysC : G.IsNaturalUnderPullbackCompPushforward)
    (c : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p) :
    BivariantClass C G sY sZ g hg p where
  cap := fun t _ k => bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c t k
  cap_properPushforward := fun t _ h _ h' sq hfst k α =>
    bivariantProperPushforwardCap_proper_naturality C G sX sY sZ f g hf hg hpp p c t h h' sq
      hfst k α
  cap_flatPullbackChow := by
    intro T T' t _ h _ _ r hr h' sq hfst k α
    have : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    have : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    exact bivariantProperPushforwardCap_flat_naturality_of_factors C G sX sY sZ f g hf hg hpp p c t
      h r hr h' sq hfst k _ _ _ α
  cap_gysin := fun t _ L _ s k e he hbase α =>
    bivariantProperPushforwardCap_gysin_naturality_of_isNatural C G sX sY sZ f g hf hg hpp p hgysP
      hgysC c t L s k e he hbase
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _) α

/-- **Stacks 0EPK, existence.** The class of Stacks 0EPK caps by the rule of Stacks 0EPK. -/
@[simp]
theorem bivariantProperPushforwardOfNaturality_cap (hgysP : G.IsNaturalUnderProperPushforward)
    (hgysC : G.IsNaturalUnderPullbackCompPushforward)
    (c : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p)
    {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sZ) k) :
    (bivariantProperPushforwardOfNaturality C G sX sY sZ f g hf hg hpp p hgysP hgysC c).cap t k α =
      bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c t k α :=
  rfl

/-- **Stacks 0EPK, existence.** The class of Stacks 0EPK *is* the proper pushforward of `c` along
`f`, in the characterizing form `Stacks.Chow.IsBivariantProperPushforward`. -/
theorem isBivariantProperPushforward_bivariantProperPushforwardOfNaturality
    (hgysP : G.IsNaturalUnderProperPushforward)
    (hgysC : G.IsNaturalUnderPullbackCompPushforward)
    (c : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p) :
    IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p c
      (bivariantProperPushforwardOfNaturality C G sX sY sZ f g hf hg hpp p hgysP hgysC c) := by
  intro T t _ k α
  rfl

/-- **Stacks 0EPK.** The proper pushforward `f_* ∘ c` of a bivariant class `c ∈ A^p(X ⟶ Z)` along
a proper `f : X ⟶ Y` exists and is unique: there is exactly one bivariant class of degree `p` for
`g` whose cap operation is `α ↦ f'_*(c ∩ α)`.

Existence is `Stacks.Chow.bivariantProperPushforwardOfNaturality` together with
`Stacks.Chow.isBivariantProperPushforward_bivariantProperPushforwardOfNaturality`, uniqueness is
`Stacks.Chow.eq_of_isBivariantProperPushforward`. -/
theorem existsUnique_isBivariantProperPushforward
    (hgysP : G.IsNaturalUnderProperPushforward)
    (hgysC : G.IsNaturalUnderPullbackCompPushforward)
    (c : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p) :
    ∃! d : BivariantClass C G sY sZ g hg p,
      IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p c d :=
  ⟨bivariantProperPushforwardOfNaturality C G sX sY sZ f g hf hg hpp p hgysP hgysC c,
    isBivariantProperPushforward_bivariantProperPushforwardOfNaturality C G sX sY sZ f g hf hg hpp
      p hgysP hgysC c,
    fun _ hd => eq_of_isBivariantProperPushforward (hpp := hpp) hd
      (isBivariantProperPushforward_bivariantProperPushforwardOfNaturality C G sX sY sZ f g hf hg
        hpp p hgysP hgysC c)⟩

end Gysin

end Stacks.Chow

end
