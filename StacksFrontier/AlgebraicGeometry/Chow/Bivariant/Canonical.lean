module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge

/-!
# The group `A^p(X ⟶ Y)` at the canonical Gysin system

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S`. The canonical Gysin system is the one whose
first Chern class rule is the rule of an invertible module (Stacks 02SO), with the vanishing of
Stacks 02TO. Reading Stacks 0B76 against it gives the group `A^p(X ⟶ Y)` of bivariant classes,
whose flat and Gysin axioms hold with the descent conditions Stacks 02S1 and Stacks 02S2
discharged.

## Main definitions

* `Stacks.Chow.canonicalGysinSystem`: the canonical Gysin system of the base situation, the
  first Chern class rule of an invertible module together with Stacks 02TO.
* `Stacks.Chow.CanonicalBivariantClass`: the group `A^p(X ⟶ Y)` of bivariant classes of degree
  `p` for `f`, read against the canonical Gysin system.

## Main results

* `Stacks.Chow.eq_canonicalGysinSystem_of_chern`: every Gysin system whose first Chern class rule
  is the rule of an invertible module is the canonical one.
* `Stacks.Chow.gysinSystemOfInvertible_eq_canonicalGysinSystem`:
  `Stacks.Chow.gysinSystemOfInvertible` is the canonical Gysin system.
* `Stacks.Chow.canonicalGysinSystem_onChow`: the Gysin map on Chow groups of the canonical Gysin
  system is the map `i^* : A_{k+1}(T) ⟶ A_k(Z(s))` of Stacks 02TO,
  `Stacks.Chow.gysinChowOfInvertible`.
* `Stacks.Chow.BivariantClass.flat_naturality_of_relativeDimension`: the flat axiom of Stacks 0B76
  with the descent condition Stacks 02S1 discharged.
* `Stacks.Chow.BivariantClass.gysin_naturality_gysinChowOfInvertible`: the Gysin axiom of Stacks
  0B76 at the canonical Gysin system, for the Gysin map of Stacks 02TO and with the descent
  condition Stacks 02S2 discharged.

## References

* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The canonical Gysin system -/

/-- **The canonical Gysin system of the base situation.** Its first Chern class rule is the rule
of an invertible module, `Stacks.Chow.firstChernComponentClass`, and its vanishing is Stacks 02TO,
`Stacks.Chow.gysinOfInvertibleDescends`. -/
def canonicalGysinSystem (C : ChowSituation.{u}) : GysinSystem C :=
  gysinSystemOfInvertible C

/-- The first Chern class rule of the canonical Gysin system is the rule of the invertible
module. -/
@[simp]
theorem canonicalGysinSystem_chern (C : ChowSituation.{u}) {T : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (k : ℤ) :
    (canonicalGysinSystem C).chern q L k = firstChernComponentClass C q k L :=
  rfl

/-- Every Gysin system whose first Chern class rule is the rule of an invertible module is the
canonical one. -/
theorem eq_canonicalGysinSystem_of_chern {C : ChowSituation.{u}} {G : GysinSystem C}
    (h : ∀ {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (L : T.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
      (k : ℤ), G.chern q L k = firstChernComponentClass C q k L) :
    G = canonicalGysinSystem C :=
  GysinSystem.eq_of_chern_eq h

/-- The Gysin system `Stacks.Chow.gysinSystemOfInvertible` is the canonical one. -/
@[simp]
theorem gysinSystemOfInvertible_eq_canonicalGysinSystem (C : ChowSituation.{u}) :
    gysinSystemOfInvertible C = canonicalGysinSystem C :=
  rfl

/-- **Stacks 02TO.** The Gysin map on Chow groups of the canonical Gysin system is the
unconditional descended Gysin map `i^* : A_{k+1}(T) ⟶ A_k(Z(s))` of the invertible module and the
section. -/
@[simp]
theorem canonicalGysinSystem_onChow (C : ChowSituation.{u}) {T : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) :
    (canonicalGysinSystem C).onChow q L s k = gysinChowOfInvertible C q k L s :=
  rfl

/-! ### The group `A^p(X ⟶ Y)` -/

/-- **Stacks 0B76.** The group `A^p(X ⟶ Y)` of bivariant classes of degree `p` for a morphism
`f : X ⟶ Y` of schemes locally of finite type over the base: a rule assigning to every morphism
`g : T ⟶ Y` locally of finite type and every `k` an additive map
`A_k(T) ⟶ A_{k-p}(T ×_Y X)`, natural for proper pushforward, for flat pullback of fixed relative
dimension, and for the Gysin map of the zero scheme of a section of an invertible module.

This is `Stacks.Chow.BivariantClass` read against `Stacks.Chow.canonicalGysinSystem`, with the
abelian group structure of `Stacks.Chow.BivariantClass`. -/
@[stacks 0B76 "the group A^p(X ⟶ Y) of bivariant classes of degree p for f, with nothing \
assumed: the Gysin system is the canonical one, whose first Chern class rule is the rule of an \
invertible module and whose vanishing is Stacks 02TO, and the descent conditions Stacks 02S1 and \
02S2 of the proper and flat axioms are discharged"]
abbrev CanonicalBivariantClass (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ) :=
  BivariantClass C (canonicalGysinSystem C) sX sY f hf p

/-! ### The three axioms, with the descent conditions discharged -/

section Axioms

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
  [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}

/-- **Stacks 0B76 (2), with Stacks 02S1 discharged.** Cap product with a bivariant class commutes
with flat pullback of fixed relative dimension, the relative dimension of the base change being a
hypothesis. -/
@[stacks 0B76 "the flat pullback axiom, with the descent condition Stacks 02S1 discharged; the \
relative dimension of the base change is assumed, Stacks 02NK being absent"]
theorem BivariantClass.flat_naturality_of_relativeDimension (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (h : T' ⟶ T) [LocallyOfFiniteType h]
    [Flat h] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback f (h ≫ g) ⟶ pullback f g)
    (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (k : ℤ) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    ∀ (hr' : AlgebraicGeometry.RelativeDimension h' r) (α : chowGroup C (g ≫ sY) k),
      HEq
        (c.cap (h ≫ g) (k + (r : ℤ))
          (flatPullbackChow C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) r hr k
            (flatPullbackDescends C _ _ _ _ _ _ _) α))
        (flatPullbackChow C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
          (by rw [← Category.assoc, hfst]) r hr' (k - p)
          (flatPullbackDescends C _ _ _ _ _ _ _) (c.cap g k α)) :=
  fun hr' α ↦ c.flat_naturality g h r hr h' sq hfst k hr' _ _ α

/-- **Stacks 0B76 (3), for the canonical Gysin system.** Cap product with a bivariant class read
against `Stacks.Chow.canonicalGysinSystem` commutes with the unconditional Gysin map
`Stacks.Chow.gysinChowOfInvertible` of Stacks 02TO, for every pulled-back divisor; the descent
condition Stacks 02S2 for the identification of the base change of the zero scheme with the zero
scheme of the pulled-back section is discharged. -/
@[stacks 0B76 "the Gysin axiom for a class at the canonical Gysin system, stated for the \
unconditional Gysin map of Stacks 02TO and with the descent condition Stacks 02S2 discharged"]
theorem BivariantClass.gysin_naturality_gysinChowOfInvertible
    (c : CanonicalBivariantClass C sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback f g).sheaf.obj
      (pullback f g).ringCatSheaf.property ((Scheme.Modules.pullback (pullback.snd f g)).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd f g)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s
    let E := Stacks.Divisors.zeroScheme (pullback f g) L' s'
    ∀ (e : pullback f (D.subschemeι ≫ g) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap f g D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst f g ≫ sX) =
        pullback.fst f (D.subschemeι ≫ g) ≫ sX)
      (α : chowGroup C (g ≫ sY) (k + 1)),
      properChowPushforward C (pullback.fst f (D.subschemeι ≫ g) ≫ sX)
          (E.subschemeι ≫ pullback.fst f g ≫ sX) e.hom hbase (k - p)
          (properPushforwardDescends C _ _ _ _ _)
          (c.cap (D.subschemeι ≫ g) k (gysinChowOfInvertible C (g ≫ sY) k L s α)) =
        gysinChowOfInvertible C (pullback.fst f g ≫ sX) (k - p) L' s'
          (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
            (by omega : (k + 1) - p = (k - p) + 1)) (c.cap g (k + 1) α)) :=
  fun e he hbase α ↦ c.gysin_naturality g L s k e he hbase _ α

end Axioms

end Stacks.Chow

end
