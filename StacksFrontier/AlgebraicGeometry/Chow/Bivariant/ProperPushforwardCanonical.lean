module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Canonical
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardGysin
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible

/-!
# Proper pushforward of a bivariant class in `A^p(X ⟶ Z)`

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of schemes locally of finite type over `S` with `f` proper, and let
`c ∈ A^p(X ⟶ Z)`. Stacks 0EPK asserts that the rule sending a test scheme `t : T ⟶ Z` and a class
`α ∈ A_k(T)` to

  `f'_*(c ∩ α) ∈ A_{k-p}(T ×_Z Y)`,

where `f' : T ×_Z X ⟶ T ×_Z Y` is the base change of `f`, is a bivariant class
`f_* ∘ c ∈ A^p(Y ⟶ Z)`.

Here `A^p(-)` is `Stacks.Chow.CanonicalBivariantClass`, the group of Stacks 0B76 read against the
canonical Gysin system, the system of the first Chern class rule of an invertible module. For that
system the two cases of Stacks 02TA which the construction of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardGysin` uses for an arbitrary Gysin
system are theorems, and the descent condition Stacks 02S2 is the theorem
`Stacks.Chow.properPushforwardDescends`; so nothing is assumed beyond the hypotheses of the tag.

## Main results

* `Stacks.Chow.canonicalGysinSystem_isNaturalUnderProperPushforward`,
  `Stacks.Chow.canonicalGysinSystem_isNaturalUnderPullbackCompPushforward` — the two cases of
  Stacks 02TA for the canonical Gysin system.
* `Stacks.Chow.canonicalBivariantProperPushforwardCap_gysin_naturality` — the Gysin axiom of
  Stacks 0B76 for the rule `α ↦ f'_*(c ∩ α)`, for the genuine Gysin map of Stacks 02TO.
* `Stacks.Chow.canonicalBivariantProperPushforward` — **Stacks 0EPK**: the class
  `f_* ∘ c ∈ A^p(Y ⟶ Z)`, with `Stacks.Chow.canonicalBivariantProperPushforward_cap` its cap
  formula.
* `Stacks.Chow.existsUnique_canonicalBivariantProperPushforward` — **Stacks 0EPK**: there is
  exactly one class in `A^p(Y ⟶ Z)` whose cap operation is `α ↦ f'_*(c ∩ α)`.

## References

* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The two cases of Stacks 02TA for the canonical Gysin system -/

/-- **Stacks 02TA, proper-pushforward case.** The Gysin map of the canonical Gysin system commutes
with proper pushforward. -/
theorem canonicalGysinSystem_isNaturalUnderProperPushforward (C : ChowSituation.{u}) :
    (canonicalGysinSystem C).IsNaturalUnderProperPushforward :=
  gysinSystemOfInvertible_isNaturalUnderProperPushforward C

/-- **Stacks 02TA, iterated-pullback case.** The Gysin map of the canonical Gysin system at a
section pulled back in two steps agrees with the one at the section pulled back along the
composite. -/
theorem canonicalGysinSystem_isNaturalUnderPullbackCompPushforward (C : ChowSituation.{u}) :
    (canonicalGysinSystem C).IsNaturalUnderPullbackCompPushforward :=
  gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C

section Canonical

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f]
  (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (p : ℤ)

/-! ### The Gysin axiom -/

/-- **Stacks 0EPK, the Gysin axiom.** For `c ∈ A^p(X ⟶ Z)` and `f` proper, the rule
`α ↦ f'_*(c ∩ α)` commutes with the Gysin map `i^*` of Stacks 02TO of the zero scheme of a section
of an invertible module on a test scheme: pushing `f'_*(c ∩ i^* α)` to the zero scheme of the
pulled-back section on `T ×_Z Y` gives `i'^* f'_*(c ∩ α)`. -/
@[stacks 0EPK "the Gysin axiom of Stacks 0B76 for the rule α ↦ f'_*(c ∩ α)"]
theorem canonicalBivariantProperPushforwardCap_gysin_naturality
    (c : CanonicalBivariantClass C sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p)
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
      (α : chowGroup C (t ≫ sZ) (k + 1)),
      properChowPushforward C (pullback.fst g (D.subschemeι ≫ t) ≫ sY)
          (E.subschemeι ≫ pullback.fst g t ≫ sY) e.hom hbase (k - p)
          (properPushforwardDescends C _ _ _ _ _)
          (bivariantProperPushforwardCap C (canonicalGysinSystem C) sX sY sZ f g hf hg
            (properPushforwardDescends C) p c (D.subschemeι ≫ t) k
            (gysinChowOfInvertible C (t ≫ sZ) k L s α)) =
        gysinChowOfInvertible C (pullback.fst g t ≫ sY) (k - p) L' s'
          (Eq.mp (congrArg (chowGroup C (pullback.fst g t ≫ sY))
              (by omega : (k + 1) - p = (k - p) + 1))
            (bivariantProperPushforwardCap C (canonicalGysinSystem C) sX sY sZ f g hf hg
              (properPushforwardDescends C) p c t (k + 1) α)) :=
  fun e he hbase α ↦
    bivariantProperPushforwardCap_gysin_naturality_of_isNatural C (canonicalGysinSystem C) sX sY sZ
      f g hf hg (properPushforwardDescends C) p
      (canonicalGysinSystem_isNaturalUnderProperPushforward C)
      (canonicalGysinSystem_isNaturalUnderPullbackCompPushforward C) c t L s k e he hbase
      (properPushforwardDescends C _ _ _ _ _) α

/-! ### The pushed-forward class -/

/-- **Stacks 0EPK.** For `f : X ⟶ Y` proper, `g : Y ⟶ Z` and `c ∈ A^p(X ⟶ Z)`, the rule which to
a test scheme `t : T ⟶ Z` assigns `α ↦ f'_*(c ∩ α)`, with `f' : T ×_Z X ⟶ T ×_Z Y` the base change
of `f`, is a bivariant class `f_* ∘ c ∈ A^p(Y ⟶ Z)`. Its cap formula is
`Stacks.Chow.canonicalBivariantProperPushforward_cap`. -/
@[stacks 0EPK]
def canonicalBivariantProperPushforward
    (c : CanonicalBivariantClass C sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p) :
    CanonicalBivariantClass C sY sZ g hg p :=
  bivariantProperPushforwardOfNaturality C (canonicalGysinSystem C) sX sY sZ f g hf hg
    (properPushforwardDescends C) p (canonicalGysinSystem_isNaturalUnderProperPushforward C)
    (canonicalGysinSystem_isNaturalUnderPullbackCompPushforward C) c

/-- **Stacks 0EPK, the cap formula.** `(f_* ∘ c) ∩ α = f'_*(c ∩ α)`. -/
@[simp]
theorem canonicalBivariantProperPushforward_cap
    (c : CanonicalBivariantClass C sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p)
    {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sZ) k) :
    (canonicalBivariantProperPushforward C sX sY sZ f g hf hg p c).cap t k α =
      properChowPushforward C (pullback.fst (f ≫ g) t ≫ sX) (pullback.fst g t ≫ sY)
        (bivariantPushforwardBaseChange f g t)
        (bivariantPushforwardBaseChange_comp_structure hf g t) (k - p)
        (properPushforwardDescends C _ _ _ _ _) (c.cap t k α) :=
  rfl

/-- **Stacks 0EPK.** For `f : X ⟶ Y` proper, `g : Y ⟶ Z` and `c ∈ A^p(X ⟶ Z)` there is exactly one
bivariant class `f_* ∘ c ∈ A^p(Y ⟶ Z)` whose cap operation is `α ↦ f'_*(c ∩ α)` on every test
scheme `t : T ⟶ Z`, with `f' : T ×_Z X ⟶ T ×_Z Y` the base change of `f`. -/
@[stacks 0EPK "existence and uniqueness of f_* ∘ c with its cap formula"]
theorem existsUnique_canonicalBivariantProperPushforward
    (c : CanonicalBivariantClass C sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p) :
    ∃! d : CanonicalBivariantClass C sY sZ g hg p,
      ∀ {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ)
        (α : chowGroup C (t ≫ sZ) k),
        d.cap t k α =
          properChowPushforward C (pullback.fst (f ≫ g) t ≫ sX) (pullback.fst g t ≫ sY)
            (bivariantPushforwardBaseChange f g t)
            (bivariantPushforwardBaseChange_comp_structure hf g t) (k - p)
            (properPushforwardDescends C _ _ _ _ _) (c.cap t k α) :=
  existsUnique_isBivariantProperPushforward C (canonicalGysinSystem C) sX sY sZ f g hf hg
    (properPushforwardDescends C) p (canonicalGysinSystem_isNaturalUnderProperPushforward C)
    (canonicalGysinSystem_isNaturalUnderPullbackCompPushforward C) c

end Canonical

end Stacks.Chow

end
