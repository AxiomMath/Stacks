module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Composition

/-!
# The naturality conditions of a composite of bivariant Chow classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of schemes locally of finite type over `S`, and let
`a ∈ A^p(X ⟶ Y)`, `b ∈ A^q(Y ⟶ Z)` be bivariant classes. Stacks 0B75 asserts, after the
definition of a bivariant class, that there is a bilinear composition

  `A^p(X ⟶ Y) × A^q(Y ⟶ Z) ⟶ A^{p+q}(X ⟶ Z)`.

Its cap operation is `Stacks.Chow.bivariantCompositeCap`, which the formula `α ↦ a ∩ (b ∩ α)`
determines uniquely. This file proves the proper-pushforward condition of Stacks 0B76 for that cap
operation and isolates the base-change bookkeeping the other two conditions need.

## Main definitions

* `Stacks.Chow.baseChangeMapOfEq` — the map `T' ×_Y X ⟶ T ×_Y X` induced by `h : T' ⟶ T`, for a
  test morphism `m : T' ⟶ Y` presented by an equality `h ≫ g = m` rather than as the literal
  composite. This is `Stacks.Chow.bivariantBaseChangeMap` with the composite loosened to an
  equality, which is what the middle base change of a composite needs.
* `Stacks.Chow.compositeMiddleBaseChange` — the base change `T' ×_Z Y ⟶ T ×_Z Y` of a morphism
  `h : T' ⟶ T` of test schemes, along which `b` is natural.
* `Stacks.Chow.compositeTopBaseChange` — the base change `(T' ×_Z Y) ×_Y X ⟶ (T ×_Z Y) ×_Y X`,
  along which `a` is natural.
* `Stacks.Chow.bivariantCompositeOuterCap` — the cap operation of the outer factor `a` at the base
  change `T ×_Z Y ⟶ Y` of a test scheme, read on `T ×_Z X`; the cap operation of the composite is
  this operation after the cap operation of `b`.

## Main results

* `Stacks.Chow.BivariantClass.proper_naturality_of_test_eq`,
  `Stacks.Chow.BivariantClass.flat_naturality_of_test_eq` — the proper and the flat condition of
  Stacks 0B76 read against a test morphism presented by an equality `h ≫ g = m`.
* `Stacks.Chow.compositeTopBaseChange_comp_pullbackRightPullbackFstIso` — the commuting square
  relating the two base changes to the associativity isomorphisms of pullbacks, which is the
  geometric content of all three conditions for a composite.
* `Stacks.Chow.bivariantCompositeOuterCap_proper_naturality`,
  `Stacks.Chow.bivariantCompositeOuterCap_flat_naturality` — the outer cap operation commutes
  with proper pushforward and with flat pullback along the middle base change, by the conditions
  for `a` alone.
* `Stacks.Chow.bivariantCompositeCap_proper_naturality` — the proper-pushforward condition of
  Stacks 0B76 for the composite of Stacks 0B75, from that condition for `a` and for `b` and the
  functoriality of proper pushforward on Chow groups (Stacks 02R5).
* `Stacks.Chow.bivariantCompositeCap_flat_naturality_of_factors` — the flat-pullback condition of
  Stacks 0B76 for the composite, given Stacks 02S1 for the middle base change.

## Implementation notes

The cap operation of the composite at a test scheme `t : T ⟶ Z` is

  `α ↦ a ∩ (b ∩ α)`,

where `b ∩ α` lives on `T ×_Z Y` and is capped by `a` *as a test scheme over `Y`*, i.e. at the
test morphism `pullback.fst g t : T ×_Z Y ⟶ Y`. For a morphism `h : T' ⟶ T` of test schemes the
naturality conditions of `a` must therefore be invoked at the morphism

  `compositeMiddleBaseChange g t h : T' ×_Z Y ⟶ T ×_Z Y`

of test schemes over `Y`. The conditions of `Stacks.Chow.BivariantClass` are stated with the source
test morphism written as the literal composite `h ≫ g`, whereas here it has to be
`pullback.fst g (h ≫ t)` — the same morphism as
`compositeMiddleBaseChange g t h ≫ pullback.fst g t`, but not the same term, and the two choices
give *different* fibre products as the target of the cap operation. The transported conditions
`Stacks.Chow.BivariantClass.proper_naturality_of_test_eq` and `.flat_naturality_of_test_eq` take
the source test morphism as a parameter `m` together with `hm : h ≫ g = m`; substituting `hm`
reduces them to the conditions themselves.

Invoking the flat condition of `b` along `h : T' ⟶ T` requires an instance of Stacks 02S1 — flat
pullback of cycles carries rational equivalences to rational equivalences — for the base change

  `compositeMiddleBaseChange g t h : T' ×_Z Y ⟶ T ×_Z Y`.

The flat condition of the composite being proved hands over Stacks 02S1 for `h` itself and for the
base change `T' ×_Z X ⟶ T ×_Z X`, and neither yields the middle one: the three test schemes are
not isomorphic, so
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isIso_square` does not bridge them.
Stacks 02S1 in general is `Stacks.Chow.flatPullbackDescends`. Accordingly
`Stacks.Chow.bivariantCompositeCap_flat_naturality_of_factors` takes the instance for the middle
base change as an argument.

By contrast the proper condition needs no new instance of Stacks 02S2: the composite's cap operation
already carries `Stacks.Chow.ProperPushforwardDescends`, which supplies the instance for every
proper morphism over the base, so `Stacks.Chow.bivariantCompositeCap_proper_naturality` is
unconditional.

The Gysin condition for a composite needs, besides Stacks 02TA for the Gysin system under a
base-change isomorphism (`Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso`), two
identifications of the base change of a zero scheme with the zero scheme of a pulled-back
section — one over `Y` and one over `Z` — of which the condition being proved supplies only the one
for `f ≫ g`. Those are instances of Stacks 0B6Y, available here as
`Stacks.Divisors.zeroScheme_pullback`.

## References

* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport of a Chow group along equalities -/

/-- The transport of a Chow group along an equality of structure morphisms commutes with the
transport along an equality of degrees. -/
theorem chowGroupCongr_chowGroupDegreeEquiv (C : ChowSituation.{u}) {A : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (hA : sA = sA')
    {k l : ℤ} (hkl : k = l) (x : chowGroup C sA k) :
    chowGroupCongr C hA l (chowGroupDegreeEquiv C sA hkl x) =
      chowGroupDegreeEquiv C sA' hkl (chowGroupCongr C hA k x) := by
  subst hA
  subst hkl
  rfl

/-- Pushforward along an isomorphism over the base absorbs the transport of a Chow group along an
equality of the structure morphism of the target. -/
theorem chowGroupCongr_chowPushforwardOfIso_target (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB]
    [LocallyOfFiniteType sB'] (hB : sB = sB') (u : A ⟶ B) [IsIso u] (hu : u ≫ sB = sA)
    (hu' : u ≫ sB' = sA) (k : ℤ) (x : chowGroup C sA k) :
    chowGroupCongr C hB k (chowPushforwardOfIso C sA sB u hu k x) =
      chowPushforwardOfIso C sA sB' u hu' k x := by
  subst hB
  rfl

/-! ### Base change along a test morphism presented by an equality -/

/-- The map `T' ×_Y X ⟶ T ×_Y X` between two base changes of `f : X ⟶ Y` induced by a morphism
`h : T' ⟶ T` of their bases, where the test morphism `m : T' ⟶ Y` downstairs is presented by an
equality `h ≫ g = m` instead of being the literal composite. For `m = h ≫ g` this is
`Stacks.Chow.bivariantBaseChangeMap`. -/
def baseChangeMapOfEq {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (h : T' ⟶ T) (m : T' ⟶ Y)
    (hm : h ≫ g = m) : pullback f m ⟶ pullback f g :=
  pullback.map f m f g (𝟙 X) h (𝟙 Y) (by simp) (by rw [Category.comp_id]; exact hm.symm)

@[reassoc (attr := simp)]
theorem baseChangeMapOfEq_fst {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (h : T' ⟶ T)
    (m : T' ⟶ Y) (hm : h ≫ g = m) :
    baseChangeMapOfEq f g h m hm ≫ pullback.fst f g = pullback.fst f m := by
  simp [baseChangeMapOfEq]

@[reassoc (attr := simp)]
theorem baseChangeMapOfEq_snd {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (h : T' ⟶ T)
    (m : T' ⟶ Y) (hm : h ≫ g = m) :
    baseChangeMapOfEq f g h m hm ≫ pullback.snd f g = pullback.snd f m ≫ h := by
  simp [baseChangeMapOfEq]

/-- The base-change map of test schemes sits in a cartesian square over `h : T' ⟶ T`, the
vertical legs being the projections to the test schemes. -/
theorem isPullback_baseChangeMapOfEq {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (h : T' ⟶ T)
    (m : T' ⟶ Y) (hm : h ≫ g = m) :
    IsPullback (pullback.snd f m) (baseChangeMapOfEq f g h m hm) h (pullback.snd f g) := by
  have hright : IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
    IsPullback.of_hasPullback f g
  have hbig : IsPullback (baseChangeMapOfEq f g h m hm ≫ pullback.fst f g)
      (pullback.snd f m) f (h ≫ g) := by
    rw [baseChangeMapOfEq_fst, hm]
    exact IsPullback.of_hasPullback f m
  exact (hbig.of_right (by simp) hright).flip

/-- The base change of the structure morphism of `T ×_Y X` over the base along a test morphism
presented by an equality. -/
theorem baseChangeMapOfEq_comp_structure {C : ChowSituation.{u}} {X Y T T' : Scheme.{u}}
    (sX : X ⟶ C.S) (f : X ⟶ Y) (g : T ⟶ Y) (h : T' ⟶ T) (m : T' ⟶ Y) (hm : h ≫ g = m) :
    baseChangeMapOfEq f g h m hm ≫ (pullback.fst f g ≫ sX) = pullback.fst f m ≫ sX := by
  rw [← Category.assoc, baseChangeMapOfEq_fst]

/-- The base change of a proper morphism of test schemes is proper. -/
theorem isProper_baseChangeMapOfEq {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (h : T' ⟶ T)
    [IsProper h] (m : T' ⟶ Y) (hm : h ≫ g = m) : IsProper (baseChangeMapOfEq f g h m hm) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeMapOfEq f g h m hm) (P := @IsProper)
    inferInstance

/-- The base change of a flat morphism of test schemes is flat. -/
theorem flat_baseChangeMapOfEq {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (h : T' ⟶ T)
    [Flat h] (m : T' ⟶ Y) (hm : h ≫ g = m) : Flat (baseChangeMapOfEq f g h m hm) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeMapOfEq f g h m hm) (P := @Flat)
    inferInstance

/-- The base change of a morphism of test schemes locally of finite type is locally of finite
type. -/
theorem locallyOfFiniteType_baseChangeMapOfEq {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    (h : T' ⟶ T) [LocallyOfFiniteType h] (m : T' ⟶ Y) (hm : h ≫ g = m) :
    LocallyOfFiniteType (baseChangeMapOfEq f g h m hm) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeMapOfEq f g h m hm)
    (P := @LocallyOfFiniteType) inferInstance

/-- Base change of morphisms of test schemes is functorial. -/
theorem baseChangeMapOfEq_comp {X Y T T' T'' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (h : T' ⟶ T)
    (m : T' ⟶ Y) (hm : h ≫ g = m) (h' : T'' ⟶ T') (m' : T'' ⟶ Y) (hm' : h' ≫ m = m')
    (hcomp : (h' ≫ h) ≫ g = m') :
    baseChangeMapOfEq f m h' m' hm' ≫ baseChangeMapOfEq f g h m hm =
      baseChangeMapOfEq f g (h' ≫ h) m' hcomp := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, baseChangeMapOfEq_fst, baseChangeMapOfEq_fst, baseChangeMapOfEq_fst]
  · rw [Category.assoc, baseChangeMapOfEq_snd, baseChangeMapOfEq_snd_assoc,
      baseChangeMapOfEq_snd]

/-- The square formed by the base changes of a cartesian square of test schemes is cartesian, so
a condition of Stacks 0B76 invoked at one of its legs may be invoked at the base change. -/
theorem baseChangeMapOfEq_square {X Y A B D E : Scheme.{u}} (f : X ⟶ Y) (tA : A ⟶ Y) (tB : B ⟶ Y)
    (tD : D ⟶ Y) (tE : E ⟶ Y) (a : A ⟶ B) (b : A ⟶ D) (q : B ⟶ E) (h : D ⟶ E)
    (ha : a ≫ tB = tA) (hb : b ≫ tD = tA) (hq : q ≫ tE = tB) (hh : h ≫ tE = tD)
    (sq : IsPullback a b q h) :
    IsPullback (baseChangeMapOfEq f tB a tA ha) (baseChangeMapOfEq f tD b tA hb)
      (baseChangeMapOfEq f tE q tB hq) (baseChangeMapOfEq f tE h tD hh) := by
  have hcomp : baseChangeMapOfEq f tB a tA ha ≫ baseChangeMapOfEq f tE q tB hq =
      baseChangeMapOfEq f tD b tA hb ≫ baseChangeMapOfEq f tE h tD hh := by
    rw [baseChangeMapOfEq_comp f tE q tB hq a tA ha (by rw [Category.assoc, hq, ha]),
      baseChangeMapOfEq_comp f tE h tD hh b tA hb (by rw [Category.assoc, hh, hb])]
    refine pullback.hom_ext ?_ ?_
    · rw [baseChangeMapOfEq_fst, baseChangeMapOfEq_fst]
    · rw [baseChangeMapOfEq_snd, baseChangeMapOfEq_snd, sq.w]
  have houter := (isPullback_baseChangeMapOfEq f tB a tA ha).flip.paste_vert sq
  have hfull : IsPullback (baseChangeMapOfEq f tB a tA ha)
      (baseChangeMapOfEq f tD b tA hb ≫ pullback.snd f tD)
      (baseChangeMapOfEq f tE q tB hq ≫ pullback.snd f tE) h := by
    simpa only [baseChangeMapOfEq_snd] using houter
  exact hfull.of_bot hcomp (isPullback_baseChangeMapOfEq f tE h tD hh).flip

/-! ### Stacks 0B6Y along an arbitrary base change, as an isomorphism

For a single base change `q : A ⟶ T`, however far from an isomorphism, the zero scheme of the
pulled-back section is the fibre product `A ×_T Z(s)`. That is the cartesian square of Stacks
0B6Y, and it is `Stacks.Divisors.zeroScheme_pullback` composed with
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso`. -/

/-- The cartesian square of Stacks 0B6Y, as an isomorphism: for any morphism `q : A ⟶ T` and any
global section `s` of an invertible module `L` on `T`, the zero scheme of `q^* s` is the fibre
product `A ×_T Z(s)`. This is the one-leg form; composed with the associativity comparison of
pullbacks it gives the two-leg statement `Stacks.Chow.bivariantDivisorBaseChangeIso`. -/
def zeroSchemeFibreProductIso {A T : Scheme.{u}} (q : A ⟶ T) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback q).obj L)
        (AlgebraicGeometry.pullbackGlobalSections q L s)).subscheme ≅
      pullback q (Stacks.Divisors.zeroScheme T L s).subschemeι :=
  (eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (Stacks.Divisors.zeroScheme_pullback q L s))).trans
    ((Stacks.Divisors.zeroScheme T L s).comapIso q)

/-- The isomorphism of Stacks 0B6Y lies over `A`: composed with the projection to `A` it is the
closed immersion of the zero scheme of the pulled-back section. -/
@[reassoc (attr := simp)]
theorem zeroSchemeFibreProductIso_hom_fst {A T : Scheme.{u}} (q : A ⟶ T) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (zeroSchemeFibreProductIso q L s).hom ≫
        pullback.fst q (Stacks.Divisors.zeroScheme T L s).subschemeι =
      (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback q).obj L)
        (AlgebraicGeometry.pullbackGlobalSections q L s)).subschemeι := by
  rw [zeroSchemeFibreProductIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst,
    subschemeι_eqToHom (Stacks.Divisors.zeroScheme_pullback q L s)]

/-- The inverse isomorphism of Stacks 0B6Y lies over `A`. -/
@[reassoc (attr := simp)]
theorem zeroSchemeFibreProductIso_inv_subschemeι {A T : Scheme.{u}} (q : A ⟶ T) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (zeroSchemeFibreProductIso q L s).inv ≫
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback q).obj L)
          (AlgebraicGeometry.pullbackGlobalSections q L s)).subschemeι =
      pullback.fst q (Stacks.Divisors.zeroScheme T L s).subschemeι := by
  rw [Iso.inv_comp_eq, zeroSchemeFibreProductIso_hom_fst]

/-! ### The divisor base change the Gysin condition of a composite needs

The Gysin condition of `Stacks.Chow.BivariantClass` carries, as a hypothesis, an identification of
the base change of a zero scheme with the zero scheme of the pulled-back section. A composite
`f ≫ g` inherits exactly one such identification — the one for `f ≫ g` — and verifying the condition
for the composite needs two more, one for `g` and one for `f`;
`Stacks.Chow.bivariantDivisorBaseChangeIso` produces it for an arbitrary first leg, so both are
instances of it. -/

/-- Stacks 0B6Y for the base change of a test scheme: let `g : Y ⟶ Z`, let `t : T ⟶ Z` be a test
scheme and let `s` be a global section of an invertible module `L` on `T` with zero scheme `D`.
Then the base change of `g` along `D ⟶ T ⟶ Z` is the zero scheme of the section pulled back to
`T ×_Z Y`. -/
def bivariantDivisorBaseChangeIso {Y Z T : Scheme.{u}} (g : Y ⟶ Z) (t : T ⟶ Z) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    pullback g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≅
      (Stacks.Divisors.zeroScheme (pullback g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subscheme :=
  (pullbackLeftPullbackSndIso g t (Stacks.Divisors.zeroScheme T L s).subschemeι).symm.trans
    (zeroSchemeFibreProductIso (pullback.snd g t) L s).symm

/-- The identification of Stacks 0B6Y lies over the canonical base-change map of test schemes:
this is exactly the hypothesis `_he` of the Gysin condition of `Stacks.Chow.BivariantClass`. -/
theorem bivariantDivisorBaseChangeIso_hom_subschemeι {Y Z T : Scheme.{u}} (g : Y ⟶ Z) (t : T ⟶ Z)
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (bivariantDivisorBaseChangeIso g t L s).hom ≫
        (Stacks.Divisors.zeroScheme (pullback g t)
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι =
      bivariantBaseChangeMap g t (Stacks.Divisors.zeroScheme T L s).subschemeι := by
  rw [bivariantDivisorBaseChangeIso, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Category.assoc,
    zeroSchemeFibreProductIso_inv_subschemeι]
  refine pullback.hom_ext ?_ ?_
  · simp [bivariantBaseChangeMap]
  · simp [bivariantBaseChangeMap, pullback.condition]

/-! ### Invariance of a Gysin system under the comparison of iterated pullbacks -/

/-- Invariance of a Gysin system under the comparison of iterated pullbacks: on a scheme `A` over
`T` through `q₁ : A ⟶ B` and `q₂ : B ⟶ T`, the two readings of the section `s` pulled back to `A` —
along `q₁ ≫ q₂` in one step, or along `q₂` and then `q₁` — have the same zero scheme by
`Stacks.Divisors.zeroScheme_pullback_comp`, while a `Stacks.Chow.GysinSystem` assigns the two
invertible modules unrelated first Chern class rules. This is the assertion that the two Gysin
maps agree under the transport along that equality of zero schemes. Like
`Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso` it is a property of the datum `G`, and it
holds for the Gysin map of Stacks 02TO, whose first Chern class rule depends on the invertible
module only through its isomorphism class. -/
def GysinSystem.IsNaturalUnderPullbackCompPushforward {C : ChowSituation.{u}}
    (G : GysinSystem C) : Prop :=
  ∀ {A B T : Scheme.{u}} (q₁ : A ⟶ B) (q₂ : B ⟶ T) (p : A ⟶ C.S) [LocallyOfFiniteType p]
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) (α : chowGroup C p (k + 1)),
    chowPushforwardOfIso C
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback q₁).obj
          ((Scheme.Modules.pullback q₂).obj L))
          (AlgebraicGeometry.pullbackGlobalSections q₁
            ((Scheme.Modules.pullback q₂).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q₂ L s))).subschemeι ≫ p)
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback (q₁ ≫ q₂)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (q₁ ≫ q₂) L s)).subschemeι ≫ p)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme
          (Stacks.Divisors.zeroScheme_pullback_comp q₁ q₂ L s)))
        (by
          rw [← Category.assoc,
            subschemeι_eqToHom (Stacks.Divisors.zeroScheme_pullback_comp q₁ q₂ L s)]) k
        (G.onChow p ((Scheme.Modules.pullback q₁).obj ((Scheme.Modules.pullback q₂).obj L))
          (AlgebraicGeometry.pullbackGlobalSections q₁ ((Scheme.Modules.pullback q₂).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q₂ L s)) k α) =
      G.onChow p ((Scheme.Modules.pullback (q₁ ≫ q₂)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (q₁ ≫ q₂) L s) k α

/-! ### The naturality conditions against a test morphism presented by an equality -/

variable {C : ChowSituation.{u}} {G : GysinSystem C}

/-- The proper-pushforward condition of a bivariant class read against a test morphism presented
by an equality: the source test morphism is given as a morphism `m` together with
`hm : h ≫ g = m` rather than as the literal composite `h ≫ g` [Stacks, Tag 0B76] (1). -/
theorem BivariantClass.proper_naturality_of_test_eq {X Y : Scheme.{u}} {sX : X ⟶ C.S}
    [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
    [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ} (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h]
    (m : T' ⟶ Y) [LocallyOfFiniteType m] (hm : h ≫ g = m) (h' : pullback f m ⟶ pullback f g)
    (sq : IsPullback (pullback.snd f m) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f m) (k : ℤ)
    (hmb : h ≫ (g ≫ sY) = m ≫ sY) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C (m ≫ sY) (g ≫ sY) h hmb k)
      (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C (pullback.fst f m ≫ sX)
        (pullback.fst f g ≫ sX) h' (by rw [← Category.assoc, hfst]) (k - p))
      (α : chowGroup C (m ≫ sY) k),
      c.cap g k (properChowPushforward C (m ≫ sY) (g ≫ sY) h hmb k hfac α) =
        properChowPushforward C (pullback.fst f m ≫ sX) (pullback.fst f g ≫ sX) h'
          (by rw [← Category.assoc, hfst]) (k - p) hfac' (c.cap m k α) := by
  subst hm
  exact fun hfac hfac' α ↦ c.proper_naturality g h h' sq hfst k hfac hfac' α

/-- The flat-pullback condition of a bivariant class read against a test morphism presented by an
equality: the source test morphism is given as a morphism `m` together with `hm : h ≫ g = m`
rather than as the literal composite `h ≫ g` [Stacks, Tag 0B76] (2). -/
theorem BivariantClass.flat_naturality_of_test_eq {X Y : Scheme.{u}} {sX : X ⟶ C.S}
    [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
    [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ} (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (h : T' ⟶ T)
    [LocallyOfFiniteType h] [Flat h] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension h r)
    (m : T' ⟶ Y) [LocallyOfFiniteType m] (hm : h ≫ g = m) (h' : pullback f m ⟶ pullback f g)
    (sq : IsPullback (pullback.snd f m) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f m) (k : ℤ)
    (hmb : h ≫ (g ≫ sY) = m ≫ sY) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    ∀ (hr' : AlgebraicGeometry.RelativeDimension h' r)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C (m ≫ sY) (g ≫ sY) h hmb r hr k)
      (hfac' : FlatPullbackFactorsThroughRationalEquivalence C (pullback.fst f m ≫ sX)
        (pullback.fst f g ≫ sX) h' (by rw [← Category.assoc, hfst]) r hr' (k - p))
      (α : chowGroup C (g ≫ sY) k),
      HEq
        (c.cap m (k + (r : ℤ))
          (flatPullbackChow C (m ≫ sY) (g ≫ sY) h hmb r hr k hfac α))
        (flatPullbackChow C (pullback.fst f m ≫ sX) (pullback.fst f g ≫ sX) h'
          (by rw [← Category.assoc, hfst]) r hr' (k - p) hfac' (c.cap g k α)) := by
  subst hm
  exact fun hr' hfac hfac' α ↦ c.flat_naturality g h r hr h' sq hfst k hr' hfac hfac' α

/-! ### The two base changes of a composite -/

/-- The base change `T' ×_Z Y ⟶ T ×_Z Y` of a morphism `h : T' ⟶ T` of test schemes over `Z`,
viewed as a morphism of test schemes over `Y`. This is the morphism along which the inner class
`b` of a composite is natural. -/
abbrev compositeMiddleBaseChange {Y Z T T' : Scheme.{u}} (g : Y ⟶ Z) (t : T ⟶ Z) (h : T' ⟶ T) :
    pullback g (h ≫ t) ⟶ pullback g t :=
  bivariantBaseChangeMap g t h

/-- The middle base change is compatible with the projections to `Y`. -/
@[reassoc (attr := simp)]
theorem compositeMiddleBaseChange_fst {Y Z T T' : Scheme.{u}} (g : Y ⟶ Z) (t : T ⟶ Z)
    (h : T' ⟶ T) :
    compositeMiddleBaseChange g t h ≫ pullback.fst g t = pullback.fst g (h ≫ t) :=
  (pullbackMap_fst g (h ≫ t) g t (𝟙 Y) h (𝟙 Z) (by simp) (by simp)).trans (Category.comp_id _)

/-- The middle base change is a morphism over the morphism of test schemes. -/
@[reassoc (attr := simp)]
theorem compositeMiddleBaseChange_snd {Y Z T T' : Scheme.{u}} (g : Y ⟶ Z) (t : T ⟶ Z)
    (h : T' ⟶ T) :
    compositeMiddleBaseChange g t h ≫ pullback.snd g t = pullback.snd g (h ≫ t) ≫ h :=
  pullbackMap_snd g (h ≫ t) g t (𝟙 Y) h (𝟙 Z) (by simp) (by simp)

/-- The base change `(T' ×_Z Y) ×_Y X ⟶ (T ×_Z Y) ×_Y X` of the middle base change along the
projection `T ×_Z Y ⟶ Y`. This is the morphism along which the outer class `a` of a composite is
natural. -/
abbrev compositeTopBaseChange {X Y Z T T' : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z)
    (h : T' ⟶ T) :
    pullback f (pullback.fst g (h ≫ t)) ⟶ pullback f (pullback.fst g t) :=
  baseChangeMapOfEq f (pullback.fst g t) (compositeMiddleBaseChange g t h)
    (pullback.fst g (h ≫ t)) (compositeMiddleBaseChange_fst g t h)

/-- The two base changes of a morphism `h : T' ⟶ T` of test schemes — the one on
`(T ×_Z Y) ×_Y X` and the one on `T ×_Z X` — correspond under the associativity isomorphisms of
pullbacks. -/
theorem compositeTopBaseChange_comp_pullbackRightPullbackFstIso {X Y Z T T' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z) (h : T' ⟶ T)
    (h' : pullback (f ≫ g) (h ≫ t) ⟶ pullback (f ≫ g) t)
    (sq : IsPullback (pullback.snd (f ≫ g) (h ≫ t)) h' h (pullback.snd (f ≫ g) t))
    (hfst : h' ≫ pullback.fst (f ≫ g) t = pullback.fst (f ≫ g) (h ≫ t)) :
    compositeTopBaseChange f g t h ≫ (pullbackRightPullbackFstIso g t f).hom =
      (pullbackRightPullbackFstIso g (h ≫ t) f).hom ≫ h' := by
  refine pullback.hom_ext ?_ ?_
  · simp [hfst]
  · simp [← sq.w]

/-- The base change of a flat morphism locally of finite type, of relative dimension `r`, has the
same properties. -/
private theorem flat_lft_relativeDimension_of_isPullback {P Q A B : Scheme.{u}} {u : P ⟶ A}
    {v : Q ⟶ B} {k : P ⟶ Q} {h : A ⟶ B} (sq : IsPullback u k h v) [LocallyOfFiniteType h]
    [Flat h] {r : ℕ} (hr : AlgebraicGeometry.RelativeDimension h r) :
    ∃ (_ : LocallyOfFiniteType k) (_ : Flat k), AlgebraicGeometry.RelativeDimension k r :=
  ⟨MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance,
    MorphismProperty.of_isPullback sq (P := @Flat) inferInstance,
    AlgebraicGeometry.RelativeDimension.of_isPullback sq hr⟩

/-! ### The outer cap operation of a composite -/

section Composite

variable (C) (G) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX)
  (hg : g ≫ sZ = sY) (hpp : ProperPushforwardDescends C) (p q : ℤ)
  (a : BivariantClass C G sX sY f hf p) (b : BivariantClass C G sY sZ g hg q)

/-- The cap operation of the outer factor of a composite, on a test scheme `t : T ⟶ Z` of the
composite: the class `a ∈ A^p(X ⟶ Y)` capped at the base change `T ×_Z Y ⟶ Y` of `t`, read on
`T ×_Z X` through the associativity isomorphism `(T ×_Z Y) ×_Y X ≅ T ×_Z X` of pullbacks.

The cap operation of the composite `a ∘ b` is this operation after the cap operation of `b`
(`Stacks.Chow.bivariantCompositeCap_eq_outerCap`). Its three naturality properties below
involve `a` alone, so they serve wherever the inner factor is not yet known to be a bivariant
class. -/
def bivariantCompositeOuterCap {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (m : ℤ) :
    chowGroup C (pullback.fst g t ≫ sY) m →+
      chowGroup C (pullback.fst (f ≫ g) t ≫ sX) (m - p) :=
  (properChowPushforward C (pullback.fst f (pullback.fst g t) ≫ sX)
      (pullback.fst (f ≫ g) t ≫ sX) (pullbackRightPullbackFstIso g t f).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t) (m - p)
      (hpp _ _ _ _ _)).comp
    (a.cap (pullback.fst g t) m)

omit [LocallyOfFiniteType g] in
/-- The outer cap operation of a composite, read on an element. -/
theorem bivariantCompositeOuterCap_apply {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t]
    (m : ℤ) (β : chowGroup C (pullback.fst g t ≫ sY) m) :
    bivariantCompositeOuterCap C G sX sY f g hf hpp p a t m β =
      properChowPushforward C (pullback.fst f (pullback.fst g t) ≫ sX)
        (pullback.fst (f ≫ g) t ≫ sX) (pullbackRightPullbackFstIso g t f).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t) (m - p) (hpp _ _ _ _ _)
        (a.cap (pullback.fst g t) m β) :=
  rfl

/-- The cap operation of a composite is the outer cap operation after the cap operation of the
inner factor. -/
theorem bivariantCompositeCap_eq_outerCap {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ sZ) k) :
    bivariantCompositeCap C G sX sY sZ f g hf hg hpp p q a b t k α =
      bivariantCompositeOuterCap C G sX sY f g hf hpp p a t (k - q) (b.cap t k α) :=
  rfl

omit [LocallyOfFiniteType g] in
/-- The outer cap operation of a composite is injective as soon as the cap operation of the outer
factor at the base change of the test scheme is: the associativity isomorphism of pullbacks
pushes forward injectively. -/
theorem bivariantCompositeOuterCap_injective {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t]
    (m : ℤ) (ha : Function.Injective (a.cap (pullback.fst g t) m)) :
    Function.Injective (bivariantCompositeOuterCap C G sX sY f g hf hpp p a t m) :=
  (chowGroupEquivOfIso C (pullback.fst f (pullback.fst g t) ≫ sX)
      (pullback.fst (f ≫ g) t ≫ sX) (pullbackRightPullbackFstIso g t f).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t) (m - p)).injective.comp ha

omit [LocallyOfFiniteType g] in
/-- The outer cap operation of a composite is surjective as soon as the cap operation of the
outer factor at the base change of the test scheme is. -/
theorem bivariantCompositeOuterCap_surjective {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (m : ℤ) (ha : Function.Surjective (a.cap (pullback.fst g t) m)) :
    Function.Surjective (bivariantCompositeOuterCap C G sX sY f g hf hpp p a t m) :=
  (chowGroupEquivOfIso C (pullback.fst f (pullback.fst g t) ≫ sX)
      (pullback.fst (f ≫ g) t ≫ sX) (pullbackRightPullbackFstIso g t f).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t) (m - p)).surjective.comp ha

/-! ### The proper-pushforward condition of a composite -/

omit [LocallyOfFiniteType g] in
/-- The outer cap operation of a composite commutes with proper pushforward: pushing forward
along the middle base change `T' ×_Z Y ⟶ T ×_Z Y` and then capping is capping and then pushing
forward along the base change `T' ×_Z X ⟶ T ×_Z X`.

The condition for `a`, read at the middle base change as a morphism of test schemes over `Y`,
moves the pushforward onto the top base change `(T' ×_Z Y) ×_Y X ⟶ (T ×_Z Y) ×_Y X`, and the
functoriality of proper pushforward (Stacks 02R5) traverses the square
`Stacks.Chow.compositeTopBaseChange_comp_pullbackRightPullbackFstIso` both ways. -/
theorem bivariantCompositeOuterCap_proper_naturality {T T' : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [IsProper h]
    (h' : pullback (f ≫ g) (h ≫ t) ⟶ pullback (f ≫ g) t)
    (sq : IsPullback (pullback.snd (f ≫ g) (h ≫ t)) h' h (pullback.snd (f ≫ g) t))
    (hfst : h' ≫ pullback.fst (f ≫ g) t = pullback.fst (f ≫ g) (h ≫ t)) (m : ℤ)
    (β : chowGroup C (pullback.fst g (h ≫ t) ≫ sY) m) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    letI : IsProper (compositeMiddleBaseChange g t h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap g t h) (P := @IsProper)
        inferInstance
    bivariantCompositeOuterCap C G sX sY f g hf hpp p a t m
        (properChowPushforward C (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY)
          (compositeMiddleBaseChange g t h)
          (by rw [← Category.assoc, compositeMiddleBaseChange_fst]) m (hpp _ _ _ _ _) β) =
      properChowPushforward C (pullback.fst (f ≫ g) (h ≫ t) ≫ sX)
        (pullback.fst (f ≫ g) t ≫ sX) h' (by rw [← Category.assoc, hfst]) (m - p)
        (hpp _ _ _ _ _)
        (bivariantCompositeOuterCap C G sX sY f g hf hpp p a (h ≫ t) m β) := by
  have hprop : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  have sqT := isPullback_baseChangeMapOfEq f (pullback.fst g t) (compositeMiddleBaseChange g t h)
    (pullback.fst g (h ≫ t)) (compositeMiddleBaseChange_fst g t h)
  have hpropT : IsProper (compositeTopBaseChange f g t h) :=
    MorphismProperty.of_isPullback sqT (P := @IsProper) inferInstance
  rw [bivariantCompositeOuterCap_apply, bivariantCompositeOuterCap_apply,
    a.proper_naturality_of_test_eq (pullback.fst g t) (compositeMiddleBaseChange g t h)
      (pullback.fst g (h ≫ t)) (compositeMiddleBaseChange_fst g t h)
      (compositeTopBaseChange f g t h) sqT
      (baseChangeMapOfEq_fst f (pullback.fst g t) (compositeMiddleBaseChange g t h)
        (pullback.fst g (h ≫ t)) (compositeMiddleBaseChange_fst g t h))
      m (by rw [← Category.assoc, compositeMiddleBaseChange_fst]) (hpp _ _ _ _ _)
      (hpp _ _ _ _ _)]
  exact properChowPushforward_comp_eq C
    (pullback.fst f (pullback.fst g (h ≫ t)) ≫ sX) (pullback.fst f (pullback.fst g t) ≫ sX)
    (pullback.fst (f ≫ g) (h ≫ t) ≫ sX) (pullback.fst (f ≫ g) t ≫ sX)
    (compositeTopBaseChange f g t h) (pullbackRightPullbackFstIso g t f).hom
    (pullbackRightPullbackFstIso g (h ≫ t) f).hom h'
    (compositeTopBaseChange_comp_pullbackRightPullbackFstIso f g t h h' sq hfst)
    (baseChangeMapOfEq_comp_structure sX f (pullback.fst g t)
      (compositeMiddleBaseChange g t h) (pullback.fst g (h ≫ t))
      (compositeMiddleBaseChange_fst g t h))
    (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t)
    (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g (h ≫ t))
    (by rw [← Category.assoc, hfst]) (m - p) (hpp _ _ _ _ _) (hpp _ _ _ _ _)
    (hpp _ _ _ _ _) (hpp _ _ _ _ _) (a.cap (pullback.fst g (h ≫ t)) m β)

/-- The proper-pushforward condition of Stacks 0B76 for the composite of two bivariant classes:
the cap operation `α ↦ a ∩ (b ∩ α)` commutes with proper pushforward along a morphism of test
schemes. The condition for `b` moves the pushforward past the inner cap and onto the middle base
change `T' ×_Z Y ⟶ T ×_Z Y`, and the outer cap operation's condition moves it past the outer
cap. -/
@[stacks 0B75 "the proper-pushforward condition of the composite"]
theorem bivariantCompositeCap_proper_naturality {T T' : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [IsProper h]
    (h' : pullback (f ≫ g) (h ≫ t) ⟶ pullback (f ≫ g) t)
    (sq : IsPullback (pullback.snd (f ≫ g) (h ≫ t)) h' h (pullback.snd (f ≫ g) t))
    (hfst : h' ≫ pullback.fst (f ≫ g) t = pullback.fst (f ≫ g) (h ≫ t)) (k : ℤ)
    (α : chowGroup C ((h ≫ t) ≫ sZ) k) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    bivariantCompositeCap C G sX sY sZ f g hf hg hpp p q a b t k
        (properChowPushforward C ((h ≫ t) ≫ sZ) (t ≫ sZ) h (by simp [Category.assoc]) k
          (hpp _ _ _ _ _) α) =
      properChowPushforward C (pullback.fst (f ≫ g) (h ≫ t) ≫ sX)
        (pullback.fst (f ≫ g) t ≫ sX) h' (by rw [← Category.assoc, hfst]) (k - q - p)
        (hpp _ _ _ _ _)
        (bivariantCompositeCap C G sX sY sZ f g hf hg hpp p q a b (h ≫ t) k α) := by
  have sqM := isPullback_bivariantBaseChangeMap g t h
  have hpropM : IsProper (compositeMiddleBaseChange g t h) :=
    MorphismProperty.of_isPullback sqM (P := @IsProper) inferInstance
  rw [bivariantCompositeCap_eq_outerCap, bivariantCompositeCap_eq_outerCap,
    b.proper_naturality t h (compositeMiddleBaseChange g t h) sqM
      (compositeMiddleBaseChange_fst g t h) k (hpp _ _ _ _ _) (hpp _ _ _ _ _) α]
  exact bivariantCompositeOuterCap_proper_naturality C G sX sY f g hf hpp p a t h h' sq hfst
    (k - q) (b.cap (h ≫ t) k α)

/-! ### The flat-pullback condition of a composite -/

omit [LocallyOfFiniteType g] in
/-- The outer cap operation of a composite commutes with flat pullback: pulling back along the
middle base change `T' ×_Z Y ⟶ T ×_Z Y` and then capping is capping and then pulling back along
the base change `T' ×_Z X ⟶ T ×_Z X`.

The condition for `a`, read at the middle base change as a morphism of test schemes over `Y`,
moves the flat pullback onto the top base change; and the isomorphism case of Stacks 02RG
(`Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`) commutes it past the associativity
isomorphism of pullbacks, which is where the two degrees `(m + r) - p` and `(m - p) + r` are
reconciled. -/
theorem bivariantCompositeOuterCap_flat_naturality {T T' : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback (f ≫ g) (h ≫ t) ⟶ pullback (f ≫ g) t)
    (sq : IsPullback (pullback.snd (f ≫ g) (h ≫ t)) h' h (pullback.snd (f ≫ g) t))
    (hfst : h' ≫ pullback.fst (f ≫ g) t = pullback.fst (f ≫ g) (h ≫ t)) (m : ℤ) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    letI : LocallyOfFiniteType (compositeMiddleBaseChange g t h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap g t h)
        (P := @LocallyOfFiniteType) inferInstance
    letI : Flat (compositeMiddleBaseChange g t h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap g t h) (P := @Flat)
        inferInstance
    ∀ (hr' : AlgebraicGeometry.RelativeDimension h' r)
      (hfacM : FlatPullbackFactorsThroughRationalEquivalence C (pullback.fst g (h ≫ t) ≫ sY)
        (pullback.fst g t ≫ sY) (compositeMiddleBaseChange g t h)
        (by rw [← Category.assoc, compositeMiddleBaseChange_fst]) r
        (AlgebraicGeometry.RelativeDimension.of_isPullback
          (isPullback_bivariantBaseChangeMap g t h) hr) m)
      (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
        (pullback.fst (f ≫ g) (h ≫ t) ≫ sX) (pullback.fst (f ≫ g) t ≫ sX) h'
        (by rw [← Category.assoc, hfst]) r hr' (m - p))
      (β : chowGroup C (pullback.fst g t ≫ sY) m),
      HEq
        (bivariantCompositeOuterCap C G sX sY f g hf hpp p a (h ≫ t) (m + (r : ℤ))
          (flatPullbackChow C (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY)
            (compositeMiddleBaseChange g t h)
            (by rw [← Category.assoc, compositeMiddleBaseChange_fst]) r
            (AlgebraicGeometry.RelativeDimension.of_isPullback
              (isPullback_bivariantBaseChangeMap g t h) hr) m hfacM β))
        (flatPullbackChow C (pullback.fst (f ≫ g) (h ≫ t) ≫ sX)
          (pullback.fst (f ≫ g) t ≫ sX) h' (by rw [← Category.assoc, hfst]) r hr'
          (m - p) hfac' (bivariantCompositeOuterCap C G sX sY f g hf hpp p a t m β)) := by
  intro hr' hfacM hfac' β
  obtain ⟨_, _, _⟩ := flat_lft_relativeDimension_of_isPullback sq hr
  have sqM := isPullback_bivariantBaseChangeMap g t h
  obtain ⟨_, _, hrM⟩ := flat_lft_relativeDimension_of_isPullback sqM hr
  have hMfst := compositeMiddleBaseChange_fst g t h
  have sqT := isPullback_baseChangeMapOfEq f (pullback.fst g t) (compositeMiddleBaseChange g t h)
    (pullback.fst g (h ≫ t)) hMfst
  obtain ⟨_, _, hrT⟩ := flat_lft_relativeDimension_of_isPullback sqT hrM
  have hTfst := baseChangeMapOfEq_fst f (pullback.fst g t) (compositeMiddleBaseChange g t h)
    (pullback.fst g (h ≫ t)) hMfst
  have hbQt := pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t
  have hbQht := pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g (h ≫ t)
  have hbT := baseChangeMapOfEq_comp_structure sX f (pullback.fst g t)
    (compositeMiddleBaseChange g t h) (pullback.fst g (h ≫ t)) hMfst
  have hbM : compositeMiddleBaseChange g t h ≫ (pullback.fst g t ≫ sY) =
      pullback.fst g (h ≫ t) ≫ sY := by rw [← Category.assoc, hMfst]
  have hbh' : h' ≫ (pullback.fst (f ≫ g) t ≫ sX) = pullback.fst (f ≫ g) (h ≫ t) ≫ sX := by
    rw [← Category.assoc, hfst]
  have hsqIso := compositeTopBaseChange_comp_pullbackRightPullbackFstIso f g t h h' sq hfst
  have hfacT := flatPullbackFactorsThroughRationalEquivalence_of_isIso_square C
    (pullback.fst f (pullback.fst g t) ≫ sX)
    (pullback.fst f (pullback.fst g (h ≫ t)) ≫ sX) (pullback.fst (f ≫ g) t ≫ sX)
    (pullback.fst (f ≫ g) (h ≫ t) ≫ sX) (pullbackRightPullbackFstIso g t f).hom hbQt
    (pullbackRightPullbackFstIso g (h ≫ t) f).hom hbQht (compositeTopBaseChange f g t h) hbT
    h' hbh' hsqIso r hrT hr' (m - p) hfac'
  have ha := a.flat_naturality_of_test_eq (pullback.fst g t)
    (compositeMiddleBaseChange g t h) r hrM
    (pullback.fst g (h ≫ t)) hMfst (compositeTopBaseChange f g t h) sqT hTfst m hbM hrT
    hfacM hfacT β
  have hidx : (m + (r : ℤ)) - p = (m - p) + (r : ℤ) := by omega
  have hres := heq_map_index hidx ha fun n x ↦
    properChowPushforward C (pullback.fst f (pullback.fst g (h ≫ t)) ≫ sX)
      (pullback.fst (f ≫ g) (h ≫ t) ≫ sX) (pullbackRightPullbackFstIso g (h ≫ t) f).hom
      hbQht n (hpp _ _ _ _ _) x
  refine hres.trans (heq_of_eq ?_)
  exact (flatPullbackChow_chowPushforwardOfIso C (pullback.fst f (pullback.fst g t) ≫ sX)
    (pullback.fst f (pullback.fst g (h ≫ t)) ≫ sX) (pullback.fst (f ≫ g) t ≫ sX)
    (pullback.fst (f ≫ g) (h ≫ t) ≫ sX) (pullbackRightPullbackFstIso g t f).hom hbQt
    (pullbackRightPullbackFstIso g (h ≫ t) f).hom hbQht (compositeTopBaseChange f g t h) hbT
    h' hbh' hsqIso r hrT hr' (m - p) hfacT hfac'
    (a.cap (pullback.fst g t) m β)).symm

/-- The flat-pullback condition of Stacks 0B76 for the composite of two bivariant classes, given
Stacks 02S1 — flat pullback of cycles preserves rational equivalence — for the middle base
change `T' ×_Z Y ⟶ T ×_Z Y` as the argument `hfacM`.

The condition for `b` moves the flat pullback past the inner cap and onto the middle base
change, and `Stacks.Chow.bivariantCompositeOuterCap_flat_naturality` moves it past the outer
cap. -/
theorem bivariantCompositeCap_flat_naturality_of_factors {T T' : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback (f ≫ g) (h ≫ t) ⟶ pullback (f ≫ g) t)
    (sq : IsPullback (pullback.snd (f ≫ g) (h ≫ t)) h' h (pullback.snd (f ≫ g) t))
    (hfst : h' ≫ pullback.fst (f ≫ g) t = pullback.fst (f ≫ g) (h ≫ t)) (k : ℤ) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    letI : LocallyOfFiniteType (compositeMiddleBaseChange g t h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap g t h)
        (P := @LocallyOfFiniteType) inferInstance
    letI : Flat (compositeMiddleBaseChange g t h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap g t h) (P := @Flat)
        inferInstance
    ∀ (hr' : AlgebraicGeometry.RelativeDimension h' r)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ t) ≫ sZ) (t ≫ sZ) h
        (by simp [Category.assoc]) r hr k)
      (_hfacM : FlatPullbackFactorsThroughRationalEquivalence C (pullback.fst g (h ≫ t) ≫ sY)
        (pullback.fst g t ≫ sY) (compositeMiddleBaseChange g t h)
        (by rw [← Category.assoc, compositeMiddleBaseChange_fst]) r
        (AlgebraicGeometry.RelativeDimension.of_isPullback
          (isPullback_bivariantBaseChangeMap g t h) hr) (k - q))
      (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
        (pullback.fst (f ≫ g) (h ≫ t) ≫ sX) (pullback.fst (f ≫ g) t ≫ sX) h'
        (by rw [← Category.assoc, hfst]) r hr' (k - q - p))
      (α : chowGroup C (t ≫ sZ) k),
      HEq
        (bivariantCompositeCap C G sX sY sZ f g hf hg hpp p q a b (h ≫ t) (k + (r : ℤ))
          (flatPullbackChow C ((h ≫ t) ≫ sZ) (t ≫ sZ) h (by simp [Category.assoc]) r hr k
            hfac α))
        (flatPullbackChow C (pullback.fst (f ≫ g) (h ≫ t) ≫ sX)
          (pullback.fst (f ≫ g) t ≫ sX) h' (by rw [← Category.assoc, hfst]) r hr'
          (k - q - p) hfac'
          (bivariantCompositeCap C G sX sY sZ f g hf hg hpp p q a b t k α)) := by
  intro hr' hfac hfacM hfac' α
  have sqM := isPullback_bivariantBaseChangeMap g t h
  obtain ⟨_, _, hrM⟩ := flat_lft_relativeDimension_of_isPullback sqM hr
  have hb := b.flat_naturality t h r hr (compositeMiddleBaseChange g t h) sqM
    (compositeMiddleBaseChange_fst g t h) k hrM hfac hfacM α
  have hidx : (k + (r : ℤ)) - q = (k - q) + (r : ℤ) := by omega
  exact (heq_map_index hidx hb fun n x ↦
    bivariantCompositeOuterCap C G sX sY f g hf hpp p a (h ≫ t) n x).trans
    (bivariantCompositeOuterCap_flat_naturality C G sX sY f g hf hpp p a t h r hr h' sq hfst
      (k - q) hr' hfacM hfac' (b.cap t k α))

end Composite

end Stacks.Chow

/-! ### The abelian group of bivariant classes

The first assertion Section 42.33 makes after defining a bivariant class is that `A^p(X ⟶ Y)` is
an abelian group. That group is `Stacks.Chow.instAddCommGroupBivariantClass`, and it is the
pointwise one: `Stacks.Chow.BivariantClass.zero_cap`, `.add_cap` and `.neg_cap` read its
operations on cap products. -/

add_to_stacks 0B75 "the abelian group of bivariant classes"
  Stacks.Chow.instAddCommGroupBivariantClass

end
