module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic

/-!
# Proper pushforward of a bivariant Chow class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of schemes locally of finite type over `S` with `f` proper, and let
`c ∈ A^p(X ⟶ Z)` be a bivariant class for the composite. Stacks 0EPK asserts that the rule
sending a test scheme `t : T ⟶ Z` and a class `α ∈ A_k(T)` to

  `f'_*(c ∩ α) ∈ A_{k-p}(T ×_Z Y)`,

where `f' : T ×_Z X ⟶ T ×_Z Y` is the base change of `f`, is again a bivariant class, written
`f_* ∘ c ∈ A^p(Y ⟶ Z)`.

This file supplies the base change and the rule: the base change of `f` is proper, so the rule is
defined; the rule determines `f_* ∘ c` uniquely; it is additive in `c`; and it satisfies the
proper-pushforward axiom of Stacks 0B76, which is the part of the source proof carried by Stacks
02R5. The flat-pullback axiom, the part carried by Stacks 02RG, is in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardFlatPullback`: it cannot be stated
here, because Stacks 02RG on Chow groups is downstream of this module. The Gysin axiom, the part
carried by Stacks 02TA, is in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardGysin`, which also assembles the
class from the three.

## Main definitions

* `Stacks.Chow.bivariantPushforwardBaseChange` — the base change `T ×_Z X ⟶ T ×_Z Y` of `f`
  along a test scheme `t : T ⟶ Z`.
* `Stacks.Chow.bivariantProperPushforwardCap` — the cap operation `α ↦ f'_*(c ∩ α)` of
  `f_* ∘ c`.
* `Stacks.Chow.IsBivariantProperPushforward` — the assertion that a bivariant class of degree `p`
  for `g` caps by that rule. This is the defining property of `f_* ∘ c`.

## Main results

* `Stacks.Chow.isPullback_bivariantPushforwardBaseChange` — the square exhibiting
  `T ×_Z X ⟶ T ×_Z Y` as a base change of `f`, whence
  `Stacks.Chow.isProper_bivariantPushforwardBaseChange`: the base change of a proper morphism
  along a test scheme is proper.
* `Stacks.Chow.isPullback_bivariantBaseChangeMap` — the base-change map of test schemes
  `T' ×_Y X ⟶ T ×_Y X` of `Stacks.Chow.bivariantBaseChangeMap` sits in a cartesian square over
  `T' ⟶ T`.
* `Stacks.Chow.bivariantProperPushforwardCap_proper_naturality` — **the proper-pushforward axiom
  of Stacks 0B76 for the rule of Stacks 0EPK**, from functoriality of proper pushforward on Chow
  groups (Stacks 02R5).
* `Stacks.Chow.eq_of_isBivariantProperPushforward` — **uniqueness**: two bivariant classes
  satisfying the rule for the same `c` are equal.
* `Stacks.Chow.IsBivariantProperPushforward.add`, `.neg`, `.zero` — the rule transports along the
  group operations, so `c ↦ f_* ∘ c` is additive.

## Implementation notes

### The two parameters

`Stacks.Chow.BivariantClass` carries a `Stacks.Chow.GysinSystem` parameter, which supplies the
first Chern class rule of Stacks 02SO and the vanishing of Stacks 02TO; it is threaded through
unchanged. See the implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic`
for why a datum of that kind must be a parameter rather than quantified.

The cap operation pushes forward along the base change of `f`, so writing it down needs an
instance of Stacks 02S2 for that morphism at every test scheme and every degree. Stacks 02S2 is a
`Prop`, and the rule recorded in `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic` is that a
`Prop` is quantified rather than parameterized; `Stacks.Chow.ProperPushforwardDescends` bundles
the instances needed. As in `StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic`, the
quantification is a hypothesis of the enclosing declarations and is **not** put inside
`Stacks.Chow.IsBivariantProperPushforward`: inside, it would weaken the characterization, and were
Stacks 02S2 uninhabited the characterization would be vacuously true and the uniqueness theorem
would say nothing.

### What the rule is, and what is still missing

Unlike the composition rule of Stacks 0FE0, the rule here needs no transport of degrees: a
bivariant class of degree `p` for `f ≫ g` and one of degree `p` for `g` both cap `A_k(T)` into
degree `k - p`, and the proper pushforward along `T ×_Z X ⟶ T ×_Z Y` preserves the degree. So
`Stacks.Chow.IsBivariantProperPushforward` is an equality of Chow classes rather than a
heterogeneous equality, and uniqueness is immediate from
`Stacks.Chow.BivariantClass.ext`.

Constructing `f_* ∘ c` is therefore exactly filling the three naturality fields of
`Stacks.Chow.BivariantClass` for `Stacks.Chow.bivariantProperPushforwardCap`. The source proof of
Stacks 0EPK invokes Stacks 02R5, 02RG and 02TA, one for each field, and the first two are
available here:

* **Proper** (Stacks 02R5). Done:
  `Stacks.Chow.bivariantProperPushforwardCap_proper_naturality`. The two base changes of `f`,
  over `T` and over `T'`, and the two base changes of the proper test morphism `h : T' ⟶ T`, over
  `X` and over `Y`, form a commuting square of proper morphisms, and functoriality of proper
  pushforward on Chow groups traverses it both ways.
* **Flat** (Stacks 02RG). Done, as
  `Stacks.Chow.bivariantProperPushforwardCap_flat_naturality_of_factors` of
  `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardFlatPullback`. The axiom asks
  flat pullback to commute with proper pushforward in the cartesian square formed by the two base
  changes of `f` and the two base-change maps of the test schemes
  (`Stacks.Chow.isPullback_bivariantPushforwardBaseChange_baseChange` of
  `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardClass`), and 02RG is proved in
  full:
  `Stacks.Chow.flatPullbackChow_properChowPushforward_unconditional` of
  `StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChangeGenuine`
  gives `g^* f_* c = f'_* (g')^* c` on Chow groups for an arbitrary class and an arbitrary
  cartesian square with `f` proper and `g` flat, every side condition discharged — the 02S1 and
  02S2 descents, coherence of the two direct images (02O5) and invertibility of the flat base
  change comparison (02KH) are proved there, not assumed. Nothing need be assumed here either:
  the relative dimension of the base-changed test morphism comes from Stacks 02NK,
  `AlgebraicGeometry.RelativeDimension.of_isPullback`. The special case where both flat legs are
  isomorphisms is `Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`; this field is discharged
  from the unconditional form.
* **Gysin** (Stacks 02TA). Done, as
  `Stacks.Chow.bivariantProperPushforwardCap_gysin_naturality_of_isNatural` of
  `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardGysin`. The axiom of Stacks 0B76
  for `f_* ∘ c` hands one identification of the base change of a zero scheme with the zero scheme
  of a pulled-back section, namely the one for `g`; invoking the axiom for `c` needs the one for
  `f ≫ g`, which that one does not produce. That identification is Stacks 0B6Y and it is
  available — `Stacks.Divisors.zeroScheme_pullback`
  (`StacksFrontier/AlgebraicGeometry/Chow/ZeroSchemePullback/Basic.lean:95`), with the composite
  form `Stacks.Divisors.zeroScheme_pullback_comp` — and the identity it was guarding, Stacks 02TA
  for the base change of `f`, is available too: it does not need the integral-component
  hypothesis `Stacks.Chow.GysinCompatibleWithPushforward`, since
  `Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_of_gysinCompatible`
  (`StacksFrontier/AlgebraicGeometry/Chow/Gysin42/ProperPushforwardInvertible.lean:271`) takes no
  such argument, despite its name; the conditional form is the separate
  `Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward`.

With the three fields the class itself is assembled, as
`Stacks.Chow.bivariantProperPushforwardOfNaturality`, and with the uniqueness theorem below the
full statement
of Stacks 0EPK is `Stacks.Chow.existsUnique_isBivariantProperPushforward`.

### Where the full statement is

The content of Stacks 0EPK is that the rule *is* a bivariant class. For an arbitrary Gysin system
the assembly carries two cases of Stacks 02TA for that axiomatised datum -- the proper-pushforward
case and the iterated-pullback case -- so the declarations of this file carry the tag only with a
qualifier naming the part of the lemma they discharge. Both cases are theorems for the canonical
Gysin system, and the full statement, for `A^p(-) = Stacks.Chow.CanonicalBivariantClass` with
nothing assumed beyond the hypotheses of the tag, is
`Stacks.Chow.existsUnique_canonicalBivariantProperPushforward` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardCanonical`.

## References

* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The base change of the proper morphism -/

/-- The base change `T ×_Z X ⟶ T ×_Z Y` of `f : X ⟶ Y` along a test scheme `t : T ⟶ Z`, for a
composable pair `f : X ⟶ Y`, `g : Y ⟶ Z`. -/
def bivariantPushforwardBaseChange {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z) :
    pullback (f ≫ g) t ⟶ pullback g t :=
  pullback.map (f ≫ g) t g t f (𝟙 T) (𝟙 Z) (by simp) (by simp)

/-- The base change of `f` is compatible with the projections to `X` and to `Y`. -/
@[reassoc (attr := simp)]
theorem bivariantPushforwardBaseChange_fst {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : T ⟶ Z) :
    bivariantPushforwardBaseChange f g t ≫ pullback.fst g t = pullback.fst (f ≫ g) t ≫ f := by
  simp [bivariantPushforwardBaseChange]

/-- The base change of `f` is a morphism over the test scheme. -/
@[reassoc (attr := simp)]
theorem bivariantPushforwardBaseChange_snd {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : T ⟶ Z) :
    bivariantPushforwardBaseChange f g t ≫ pullback.snd g t = pullback.snd (f ≫ g) t := by
  simp [bivariantPushforwardBaseChange]

/-- The base change of `f` along a test scheme is a morphism over the base. -/
theorem bivariantPushforwardBaseChange_comp_structure {C : ChowSituation.{u}}
    {X Y Z T : Scheme.{u}} {sX : X ⟶ C.S} {sY : Y ⟶ C.S} {f : X ⟶ Y} (hf : f ≫ sY = sX)
    (g : Y ⟶ Z) (t : T ⟶ Z) :
    bivariantPushforwardBaseChange f g t ≫ (pullback.fst g t ≫ sY) =
      pullback.fst (f ≫ g) t ≫ sX := by
  rw [← Category.assoc, bivariantPushforwardBaseChange_fst, Category.assoc, hf]

/-- The base change `T ×_Z X ⟶ T ×_Z Y` of `f` along a test scheme `t : T ⟶ Z` is a base change
of `f` in the strict sense: it sits in a cartesian square over `f`, the vertical legs being the
projections to `X` and to `Y`. -/
theorem isPullback_bivariantPushforwardBaseChange {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : T ⟶ Z) :
    IsPullback (pullback.fst (f ≫ g) t) (bivariantPushforwardBaseChange f g t) f
      (pullback.fst g t) := by
  have hright : IsPullback (pullback.snd g t) (pullback.fst g t) t g :=
    (IsPullback.of_hasPullback g t).flip
  have hbig : IsPullback (bivariantPushforwardBaseChange f g t ≫ pullback.snd g t)
      (pullback.fst (f ≫ g) t) t (f ≫ g) := by
    rw [bivariantPushforwardBaseChange_snd]
    exact (IsPullback.of_hasPullback (f ≫ g) t).flip
  exact (hbig.of_right (bivariantPushforwardBaseChange_fst f g t) hright).flip

/-- **Stacks 0EPK.** The base change of a proper morphism along a test scheme is proper, so the
rule of Stacks 0EPK can push forward along it. -/
@[stacks 0EPK "properness of the base change of the proper morphism"]
instance isProper_bivariantPushforwardBaseChange {X Y Z T : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (g : Y ⟶ Z) (t : T ⟶ Z) : IsProper (bivariantPushforwardBaseChange f g t) :=
  MorphismProperty.of_isPullback (isPullback_bivariantPushforwardBaseChange f g t)
    (P := @IsProper) inferInstance

/-- The base-change map of test schemes is proper as soon as the morphism of test schemes is. -/
instance isProper_bivariantBaseChangeMap {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    (h : T' ⟶ T) [IsProper h] : IsProper (bivariantBaseChangeMap f g h) :=
  MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f g h) (P := @IsProper)
    inferInstance

/-! ### The cap operation of the pushed-forward class -/

section Pushforward

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f]
  (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
  (hpp : ProperPushforwardDescends C) (p : ℤ)
  (c : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p)

/-- **Stacks 0EPK.** The cap operation of the proper pushforward `f_* ∘ c` of a bivariant class
`c` for `f ≫ g`: cap with `c`, then push forward along the base change of `f`. -/
def bivariantProperPushforwardCap {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ) :
    chowGroup C (t ≫ sZ) k →+ chowGroup C (pullback.fst g t ≫ sY) (k - p) :=
  (properChowPushforward C (pullback.fst (f ≫ g) t ≫ sX) (pullback.fst g t ≫ sY)
      (bivariantPushforwardBaseChange f g t)
      (bivariantPushforwardBaseChange_comp_structure hf g t) (k - p)
      (hpp _ _ _ _ _)).comp
    (c.cap t k)

/-- The cap operation of a proper pushforward, read on an element. -/
theorem bivariantProperPushforwardCap_apply {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ sZ) k) :
    bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c t k α =
      properChowPushforward C (pullback.fst (f ≫ g) t ≫ sX) (pullback.fst g t ≫ sY)
        (bivariantPushforwardBaseChange f g t)
        (bivariantPushforwardBaseChange_comp_structure hf g t) (k - p)
        (hpp _ _ _ _ _) (c.cap t k α) :=
  rfl

/-- **Stacks 0EPK.** The proper-pushforward axiom of Stacks 0B76 for the rule of Stacks 0EPK: the
cap operation `α ↦ f'_*(c ∩ α)` commutes with proper pushforward along a morphism of test
schemes. -/
@[stacks 0EPK "the proper-pushforward axiom of the pushed-forward class"]
theorem bivariantProperPushforwardCap_proper_naturality {T T' : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [IsProper h]
    (h' : pullback g (h ≫ t) ⟶ pullback g t)
    (sq : IsPullback (pullback.snd g (h ≫ t)) h' h (pullback.snd g t))
    (hfst : h' ≫ pullback.fst g t = pullback.fst g (h ≫ t)) (k : ℤ)
    (α : chowGroup C ((h ≫ t) ≫ sZ) k) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c t k
        (properChowPushforward C ((h ≫ t) ≫ sZ) (t ≫ sZ) h (by simp [Category.assoc]) k
          (hpp _ _ _ _ _) α) =
      properChowPushforward C (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY) h'
        (by rw [← Category.assoc, hfst]) (k - p) (hpp _ _ _ _ _)
        (bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c (h ≫ t) k α) := by
  have : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  set hX : pullback (f ≫ g) (h ≫ t) ⟶ pullback (f ≫ g) t :=
    bivariantBaseChangeMap (f ≫ g) t h with hXdef
  have hXfst : hX ≫ pullback.fst (f ≫ g) t = pullback.fst (f ≫ g) (h ≫ t) := by
    rw [hXdef, pullbackMap_fst, Category.comp_id]
  have hXsq : IsPullback (pullback.snd (f ≫ g) (h ≫ t)) hX h (pullback.snd (f ≫ g) t) :=
    isPullback_bivariantBaseChangeMap (f ≫ g) t h
  have hsquare : hX ≫ bivariantPushforwardBaseChange f g t =
      bivariantPushforwardBaseChange f g (h ≫ t) ≫ h' := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, bivariantPushforwardBaseChange_fst, ← Category.assoc, hXfst,
        Category.assoc, hfst, bivariantPushforwardBaseChange_fst]
    · rw [Category.assoc, bivariantPushforwardBaseChange_snd, Category.assoc, ← sq.w,
        bivariantPushforwardBaseChange_snd_assoc, hXsq.w]
  rw [bivariantProperPushforwardCap_apply, bivariantProperPushforwardCap_apply,
    c.proper_naturality t h hX hXsq hXfst k (hpp _ _ _ _ _) (hpp _ _ _ _ _) α]
  exact properChowPushforward_comp_eq C (pullback.fst (f ≫ g) (h ≫ t) ≫ sX)
    (pullback.fst (f ≫ g) t ≫ sX) (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY)
    hX (bivariantPushforwardBaseChange f g t) (bivariantPushforwardBaseChange f g (h ≫ t)) h'
    hsquare (by rw [← Category.assoc, hXfst])
    (bivariantPushforwardBaseChange_comp_structure hf g t)
    (bivariantPushforwardBaseChange_comp_structure hf g (h ≫ t))
    (by rw [← Category.assoc, hfst]) (k - p) (hpp _ _ _ _ _) (hpp _ _ _ _ _) (hpp _ _ _ _ _)
    (hpp _ _ _ _ _) (c.cap (h ≫ t) k α)

/-- **Stacks 0EPK.** The assertion that a bivariant class of degree `p` for `g` is *the* proper
pushforward `f_* ∘ c` of `c` along `f`: on every test scheme its cap operation is cap with `c`
followed by proper pushforward along the base change of `f`. -/
def IsBivariantProperPushforward (d : BivariantClass C G sY sZ g hg p) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sZ) k),
    d.cap t k α = bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c t k α

end Pushforward

/-! ### Uniqueness and additivity of the pushed-forward class -/

section Properties

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y Z : Scheme.{u}}
  {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {f : X ⟶ Y} [IsProper f]
  {g : Y ⟶ Z} [LocallyOfFiniteType g] {hf : f ≫ sY = sX} {hg : g ≫ sZ = sY}
  {hpp : ProperPushforwardDescends C} {p : ℤ}
  {c c' : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p}
  {d d' : BivariantClass C G sY sZ g hg p}

/-- **Stacks 0EPK.** The rule of Stacks 0EPK determines the pushed-forward class: two bivariant
classes that both push `c` forward along `f` are equal. -/
@[stacks 0EPK "uniqueness of the pushed-forward class"]
theorem eq_of_isBivariantProperPushforward
    (h : IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p c d)
    (h' : IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p c d') : d = d' := by
  refine BivariantClass.ext C G sY sZ g hg p ?_
  intro T t _ k α
  exact (h t k α).trans (h' t k α).symm

namespace IsBivariantProperPushforward

/-- Proper pushforward of bivariant classes is additive. -/
theorem add (h : IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p c d)
    (h' : IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p c' d') :
    IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p (c + c') (d + d') := by
  intro T t _ k α
  simp [bivariantProperPushforwardCap_apply, h t k α, h' t k α]

/-- Proper pushforward of bivariant classes commutes with negation. -/
theorem neg (h : IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p c d) :
    IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p (-c) (-d) := by
  intro T t _ k α
  simp [bivariantProperPushforwardCap_apply, h t k α]

/-- The proper pushforward of the zero bivariant class is zero. -/
theorem zero :
    IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p
      (0 : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p) 0 := by
  intro T t _ k α
  simp [bivariantProperPushforwardCap_apply]

/-- Proper pushforward of bivariant classes commutes with subtraction. -/
theorem sub (h : IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p c d)
    (h' : IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p c' d') :
    IsBivariantProperPushforward C G sX sY sZ f g hf hg hpp p (c - c') (d - d') := by
  intro T t _ k α
  simp [bivariantProperPushforwardCap_apply, h t k α, h' t k α]

end IsBivariantProperPushforward

end Properties

end Stacks.Chow

end
