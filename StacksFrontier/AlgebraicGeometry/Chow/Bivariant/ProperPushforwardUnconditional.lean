module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverFieldSurjective
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksCore.Tactic.StacksAttribute

/-!
# The proper pushforward of a bivariant class, with nothing assumed

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. This file states
[Stacks, Tag 0EPK] with the following inputs supplied as theorems:

* Stacks 02RG on Chow groups, `Stacks.Chow.ProperPushforwardFlatPullbackBaseChange`, is
  `Stacks.Chow.properPushforwardFlatPullbackBaseChange`.
* Stacks 02S2 on Chow groups, `Stacks.Chow.ProperPushforwardDescends`, is
  `Stacks.Chow.properPushforwardDescends`, and Stacks 02S1 is `Stacks.Chow.flatPullbackDescends`.
* Stacks 02TA holds for the Gysin system of the first Chern class rule, by
  `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderProperPushforward` and
  `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward`.

The flat-pullback and proper-pushforward axioms hold for an arbitrary Gysin system; the
Gysin axiom and the pushed-forward class are stated at `Stacks.Chow.gysinSystemOfInvertible`.

## Main results

* `Stacks.Chow.bivariantProperPushforwardCap_proper_naturality_unconditional`,
  `Stacks.Chow.bivariantProperPushforwardCap_flat_naturality_unconditional` and
  `Stacks.Chow.bivariantProperPushforwardCap_gysin_naturality_ofInvertible` — **the three axioms
  of Stacks 0B76 for the rule of Stacks 0EPK**, with nothing assumed.
* `Stacks.Chow.bivariantProperPushforwardOfInvertible` — **Stacks 0EPK**, the class
  `f_* ∘ c ∈ A^p(Y ⟶ Z)`, with nothing assumed.
* `Stacks.Chow.isBivariantProperPushforward_bivariantProperPushforwardOfInvertible` and
  `Stacks.Chow.exists_isBivariantProperPushforward_ofInvertible` — **Stacks 0EPK**: that class
  caps by the rule of the lemma, so the rule is realized.
* `Stacks.Chow.bivariantProperPushforwardExistsOfInvertible` — Stacks 0EPK in bundled form.
* `Stacks.Chow.eq_of_isBivariantProperPushforward_unconditional` — **uniqueness** of the
  pushed-forward class.

## References

* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Axioms

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f]
  (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (p : ℤ)
  (c : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p)

/-- The proper-pushforward axiom of Stacks 0B76 for the rule of Stacks 0EPK, with proper
pushforward on Chow groups taken along the descent `Stacks.Chow.properPushforwardDescends`. -/
@[stacks 0EPK "the proper-pushforward axiom of the pushed-forward class, with NOTHING ASSUMED: \
the descent of Stacks 02S2 is the theorem Stacks.Chow.properPushforwardDescends"]
theorem bivariantProperPushforwardCap_proper_naturality_unconditional {T T' : Scheme.{u}}
    (t : T ⟶ Z) [LocallyOfFiniteType t] (h : T' ⟶ T) [IsProper h]
    (h' : pullback g (h ≫ t) ⟶ pullback g t)
    (sq : IsPullback (pullback.snd g (h ≫ t)) h' h (pullback.snd g t))
    (hfst : h' ≫ pullback.fst g t = pullback.fst g (h ≫ t)) (k : ℤ)
    (α : chowGroup C ((h ≫ t) ≫ sZ) k) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    bivariantProperPushforwardCap C G sX sY sZ f g hf hg (properPushforwardDescends C) p c t k
        (properChowPushforward C ((h ≫ t) ≫ sZ) (t ≫ sZ) h (by simp [Category.assoc]) k
          (properPushforwardDescends C _ _ _ _ _) α) =
      properChowPushforward C (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY) h'
        (by rw [← Category.assoc, hfst]) (k - p) (properPushforwardDescends C _ _ _ _ _)
        (bivariantProperPushforwardCap C G sX sY sZ f g hf hg (properPushforwardDescends C) p c
          (h ≫ t) k α) :=
  bivariantProperPushforwardCap_proper_naturality C G sX sY sZ f g hf hg
    (properPushforwardDescends C) p c t h h' sq hfst k α

/-- The flat-pullback axiom of Stacks 0B76 for the rule of Stacks 0EPK, with flat pullback and
proper pushforward on Chow groups taken along the descents `Stacks.Chow.flatPullbackDescends` and
`Stacks.Chow.properPushforwardDescends`, and the relative dimension of the base change given by
Stacks 02NK. -/
@[stacks 0EPK "the flat-pullback axiom of the pushed-forward class, with NOTHING ASSUMED: \
Stacks 02RG on Chow groups is the theorem Stacks.Chow.properPushforwardFlatPullbackBaseChange, \
and the two descents are Stacks.Chow.flatPullbackDescends and \
Stacks.Chow.properPushforwardDescends"]
theorem bivariantProperPushforwardCap_flat_naturality_unconditional {T T' : Scheme.{u}}
    (t : T ⟶ Z) [LocallyOfFiniteType t] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback g (h ≫ t) ⟶ pullback g t)
    (sq : IsPullback (pullback.snd g (h ≫ t)) h' h (pullback.snd g t))
    (hfst : h' ≫ pullback.fst g t = pullback.fst g (h ≫ t)) (k : ℤ)
    (α : chowGroup C (t ≫ sZ) k) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    HEq
      (bivariantProperPushforwardCap C G sX sY sZ f g hf hg (properPushforwardDescends C) p c
        (h ≫ t) (k + (r : ℤ))
        (flatPullbackChow C ((h ≫ t) ≫ sZ) (t ≫ sZ) h (by simp [Category.assoc]) r hr k
          (flatPullbackDescends C _ _ _ _ _ _ _) α))
      (flatPullbackChow C (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY) h'
        (by rw [← Category.assoc, hfst]) r
        (AlgebraicGeometry.RelativeDimension.of_isPullback sq hr) (k - p)
        (flatPullbackDescends C _ _ _ _ _ _ _)
        (bivariantProperPushforwardCap C G sX sY sZ f g hf hg (properPushforwardDescends C) p c t k
          α)) := by
  have : LocallyOfFiniteType h' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  exact bivariantProperPushforwardCap_flat_naturality C G sX sY sZ f g hf hg
    (properPushforwardDescends C) p c (properPushforwardFlatPullbackBaseChange C) t h r hr h' sq
    hfst k (AlgebraicGeometry.RelativeDimension.of_isPullback sq hr)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) α

end Axioms

section OfInvertible

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f]
  (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (p : ℤ)
  (c : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
    (comp_comp_structureMorphism_eq hf hg) p)

/-- The Gysin axiom of Stacks 0B76 for the rule of Stacks 0EPK at the Gysin system
`Stacks.Chow.gysinSystemOfInvertible` of the first Chern class rule, with proper pushforward on
Chow groups taken along the descent `Stacks.Chow.properPushforwardDescends`. -/
@[stacks 0EPK "the Gysin axiom of the pushed-forward class at the Gysin system of the first Chern \
class rule, with NOTHING ASSUMED: Stacks 02TA for that Gysin system is a pair of theorems here, \
the identification is Stacks 0B6Y, and the descent of Stacks 02S2 is \
Stacks.Chow.properPushforwardDescends"]
theorem bivariantProperPushforwardCap_gysin_naturality_ofInvertible {T : Scheme.{u}} (t : T ⟶ Z)
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
    (α : chowGroup C (t ≫ sZ) (k + 1)) :
    properChowPushforward C
        (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY)
        ((Stacks.Divisors.zeroScheme (pullback g t)
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
          pullback.fst g t ≫ sY) e.hom hbase (k - p)
        (properPushforwardDescends C _ _ _ _ _)
        (bivariantProperPushforwardCap C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
          (properPushforwardDescends C) p c
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) k
          ((gysinSystemOfInvertible C).onChow (t ≫ sZ) L s k α)) =
      (gysinSystemOfInvertible C).onChow (pullback.fst g t ≫ sY)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s) (k - p)
        (Eq.mp (congrArg (chowGroup C (pullback.fst g t ≫ sY))
          (by omega : k + 1 - p = k - p + 1))
          (bivariantProperPushforwardCap C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
            (properPushforwardDescends C) p c t (k + 1) α)) :=
  bivariantProperPushforwardCap_gysin_naturality C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
    (properPushforwardDescends C) p c
    (gysinSystemOfInvertible_isNaturalUnderProperPushforward C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) t L s k e he hbase
    (properPushforwardDescends C _ _ _ _ _) α

/-- The proper pushforward `f_* ∘ c ∈ A^p(Y ⟶ Z)` of a bivariant class `c ∈ A^p(X ⟶ Z)` along a
proper `f : X ⟶ Y`, at the Gysin system of the first Chern class rule: the bivariant class whose
cap operation is the rule `α ↦ f'_*(c ∩ α)` of `Stacks.Chow.bivariantProperPushforwardCap`. -/
@[stacks 0EPK "the pushed-forward class f_* ∘ c itself, at the Gysin system of the first Chern \
class rule, with NOTHING ASSUMED: the rule of the lemma IS a bivariant class, so the three \
axioms of Stacks 0B76 for it are the three fields of this term, and Stacks 02RG, Stacks 02TA for \
this Gysin system and Stacks 02S2 are all theorems of this repository"]
def bivariantProperPushforwardOfInvertible :
    BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg p :=
  bivariantProperPushforward C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
    (properPushforwardDescends C) p c (properPushforwardFlatPullbackBaseChange C)
    (gysinSystemOfInvertible_isNaturalUnderProperPushforward C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)

/-- The class `Stacks.Chow.bivariantProperPushforwardOfInvertible` caps by the rule
`α ↦ f'_*(c ∩ α)`, so it is the proper pushforward of `c` in the sense of
`Stacks.Chow.IsBivariantProperPushforward`. -/
@[stacks 0EPK "the constructed class satisfies the characterization \
Stacks.Chow.IsBivariantProperPushforward of the same tag, with NOTHING ASSUMED, so the \
uniqueness statement is about a nonempty collection"]
theorem isBivariantProperPushforward_bivariantProperPushforwardOfInvertible :
    IsBivariantProperPushforward C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
      (properPushforwardDescends C) p c
      (bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c) :=
  isBivariantProperPushforward_bivariantProperPushforward C (gysinSystemOfInvertible C) sX sY sZ f
    g hf hg (properPushforwardDescends C) p c (properPushforwardFlatPullbackBaseChange C)
    (gysinSystemOfInvertible_isNaturalUnderProperPushforward C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)

/-- For a proper `f : X ⟶ Y`, a morphism `g : Y ⟶ Z` and a bivariant class `c` of degree `p` for
`f ≫ g` against the Gysin system of the first Chern class rule, there is a bivariant class of
degree `p` for `g` whose cap operation is `α ↦ f'_*(c ∩ α)`. -/
@[stacks 0EPK "existence of the pushed-forward class at the Gysin system of the first Chern class \
rule, with NOTHING ASSUMED"]
theorem exists_isBivariantProperPushforward_ofInvertible :
    ∃ d : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg p,
      IsBivariantProperPushforward C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
        (properPushforwardDescends C) p c d :=
  ⟨bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c,
    isBivariantProperPushforward_bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c⟩

end OfInvertible

/-- The bundled existence statement `Stacks.Chow.BivariantProperPushforwardExists` of
Stacks 0EPK holds at the Gysin system of the first Chern class rule. -/
@[stacks 0EPK "the bundled existence statement at the Gysin system of the first Chern class rule, \
with NOTHING ASSUMED: Stacks 02RG on Chow groups and Stacks 02TA for this Gysin system are both \
theorems of this repository"]
theorem bivariantProperPushforwardExistsOfInvertible (C : ChowSituation.{u}) :
    BivariantProperPushforwardExists C (gysinSystemOfInvertible C) :=
  bivariantProperPushforwardExists C (gysinSystemOfInvertible C)
    (properPushforwardFlatPullbackBaseChange C)
    (gysinSystemOfInvertible_isNaturalUnderProperPushforward C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)

/-- Two bivariant classes that both push `c` forward along `f`, with proper pushforward on Chow
groups taken along the descent `Stacks.Chow.properPushforwardDescends`, are equal. -/
@[stacks 0EPK "uniqueness of the pushed-forward class, with NOTHING ASSUMED: the descent of \
Stacks 02S2 is the theorem Stacks.Chow.properPushforwardDescends"]
theorem eq_of_isBivariantProperPushforward_unconditional {C : ChowSituation.{u}}
    {G : GysinSystem C} {X Y Z : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
    {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {f : X ⟶ Y}
    [IsProper f] {g : Y ⟶ Z} [LocallyOfFiniteType g] {hf : f ≫ sY = sX} {hg : g ≫ sZ = sY}
    {p : ℤ} {c : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p}
    {d d' : BivariantClass C G sY sZ g hg p}
    (h : IsBivariantProperPushforward C G sX sY sZ f g hf hg (properPushforwardDescends C) p c d)
    (h' : IsBivariantProperPushforward C G sX sY sZ f g hf hg (properPushforwardDescends C) p c
      d') : d = d' :=
  eq_of_isBivariantProperPushforward (hpp := properPushforwardDescends C) h h'

end Stacks.Chow

end
