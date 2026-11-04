module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.Conormal.ConormalSequence

/-!
# Composition of the localized Chern classes of a pair of immersions

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let
`Z ⟶ Y ⟶ X` be immersions of schemes locally of finite type over `S`. Let `𝒩` be a virtual
normal sheaf for `Z ⊆ X`, `𝒩'` one for `Z ⊆ Y` and `𝒩''` one for `Y ⊆ X`. Stacks 0FEC assumes a
commutative diagram

```
  (𝒩'')^∨|_Z  ⟶  𝒩^∨   ⟶  (𝒩')^∨
      ↓            ↓           ↓
  𝒞_{Y/X}|_Z  ⟶  𝒞_{Z/X} ⟶  𝒞_{Z/Y}
```

whose bottom row is the conormal sequence of More on Morphisms 37.7.12 (Stacks 062S), whose
three vertical maps are the structural surjections of the three virtual normal sheaves and
whose top row is a short exact sequence, and concludes

  `c(Z ⟶ X, 𝒩) = c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')`   in `A^*(Z ⟶ X)^∧`.

We state the hypothesis as a datum and, for a given rule `c` attaching bivariant classes to
immersions with virtual normal bundles, reduce the conclusion to the composition of bivariant
classes, degree by degree.

## Main definitions

* `Stacks.Chow.IsShortExactSequenceOfModules` — a composable pair of maps of modules on a scheme
  is a short exact sequence.
* `Stacks.Chow.ConormalCompatibleVirtualNormalBundles` — the hypothesis of Stacks 0FEC: three
  virtual normal bundles for `Z ⟶ Y ⟶ X` together with the two maps of the top row, its short
  exactness, and the two squares against the conormal sequence.
* `Stacks.Chow.LocalizedChernClassRule` — a rule attaching a bivariant class `c(Z ⟶ X, 𝒩)` to an
  immersion, a virtual normal bundle for it and a degree, as the class of Stacks 0FBK does.

## Main results

* `Stacks.Chow.localizedChernClass_cap_eq_bivariantCompositeCap` — the conclusion of
  Stacks 0FEC, read on cap products: granted that `c(Z ⟶ X, 𝒩)` composes `c(Z ⟶ Y, 𝒩')` with
  `c(Y ⟶ X, 𝒩'')`, its cap operation on every test scheme is "cap with `c(Y ⟶ X, 𝒩'')`, then cap
  with `c(Z ⟶ Y, 𝒩')`", pushed forward along the associativity isomorphism of pullbacks.
* `Stacks.Chow.eq_localizedChernClass_of_isBivariantClassComposition` — uniqueness: any
  bivariant class composing `c(Z ⟶ Y, 𝒩')` with `c(Y ⟶ X, 𝒩'')` equals `c(Z ⟶ X, 𝒩)`.

## References

* [Stacks Project, Tag 0FEC](https://stacks.math.columbia.edu/tag/0FEC)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.Immersion Stacks.Thickenings

universe u

namespace Stacks.Chow

/-! ### Short exact sequences of modules on a scheme -/

/-- A composable pair `A ⟶ B ⟶ D` of maps of modules on a scheme is a *short exact sequence*:
the composite vanishes and the resulting short complex is short exact, that is, the first map is
a monomorphism, the second an epimorphism, and the complex is exact in the middle. -/
def IsShortExactSequenceOfModules {W : Scheme.{u}} {A B D : W.Modules} (a : A ⟶ B)
    (b : B ⟶ D) : Prop :=
  letI : Preadditive W.Modules := SheafOfModules.instPreadditive W.ringCatSheaf
  letI : HasZeroMorphisms W.Modules := Preadditive.preadditiveHasZeroMorphisms
  ∃ h : a ≫ b = 0, (ShortComplex.mk a b h).ShortExact

/-! ### The hypothesis of Stacks 0FEC -/

/-- For immersions `i : Z ⟶ Y` and `j : Y ⟶ X`, three virtual
normal bundles — `𝒩` for `Z ⊆ X`, `𝒩'` for `Z ⊆ Y` and `𝒩''` for `Y ⊆ X` — together with a
short exact sequence

  `(𝒩'')^∨|_Z ⟶ 𝒩^∨ ⟶ (𝒩')^∨`

of duals and the two commutative squares identifying it, through the structural surjections of
the three virtual normal bundles, with the conormal sequence

  `𝒞_{Y/X}|_Z ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}`

of Stacks 062S. -/
@[stacks 0FEC "the hypothesis of the lemma: the three virtual normal bundles of Stacks 0FBQ \
for Z ⊆ Y ⊆ X, the short exact sequence of their duals, and its two commutative squares \
against the genuine conormal sequence of Stacks 062S; stated for immersions rather than \
closed subschemes, which is a generalization"]
structure ConormalCompatibleVirtualNormalBundles {Z Y X : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] where
  /-- The virtual normal bundle `𝒩` for `Z ⊆ X`. -/
  bundleZX : VirtualNormalBundle (i ≫ j)
  /-- The virtual normal bundle `𝒩'` for `Z ⊆ Y`. -/
  bundleZY : VirtualNormalBundle i
  /-- The virtual normal bundle `𝒩''` for `Y ⊆ X`. -/
  bundleYX : VirtualNormalBundle j
  /-- The left-hand map `(𝒩'')^∨|_Z ⟶ 𝒩^∨` of the top row. -/
  dualLeft : (modulePullback i.toLRSHom.toShHom).obj (dualSheaf bundleYX.bundle) ⟶
    dualSheaf bundleZX.bundle
  /-- The right-hand map `𝒩^∨ ⟶ (𝒩')^∨` of the top row. -/
  dualRight : dualSheaf bundleZX.bundle ⟶ dualSheaf bundleZY.bundle
  /-- The top row is a short exact sequence. -/
  shortExact : IsShortExactSequenceOfModules dualLeft dualRight
  /-- The left-hand square commutes: the left map of the top row followed by the surjection of
  `𝒩` is the restriction to `Z` of the surjection of `𝒩''` followed by the canonical map
  `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}` of Stacks 01R4. -/
  leftSquare : dualLeft ≫ bundleZX.surjection =
    (modulePullback i.toLRSHom.toShHom).map bundleYX.surjection ≫
      immersionConormalSheafMap (i ≫ j) j i (𝟙 X) (toShHom_square (by simp))
  /-- The right-hand square commutes: the right map of the top row followed by the surjection of
  `𝒩'` is the surjection of `𝒩` followed by the right-hand map `𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` of the
  conormal sequence of Stacks 062S. -/
  rightSquare : dualRight ≫ bundleZY.surjection =
    bundleZX.surjection ≫ conormalSequenceRightMap i j

/-! ### The localized Chern class as a parameter -/

/-- A rule attaching a bivariant class `c(Z ⟶ X, 𝒩) ∈ A^p(Z ⟶ X)` to an immersion `i : Z ⟶ X` of
schemes locally of finite type over the base, a virtual normal bundle `𝒩` for it and a degree
`p`, as the localized Chern class of Stacks 0FBK does. -/
abbrev LocalizedChernClassRule (C : ChowSituation.{u}) (G : GysinSystem C) : Type (u + 1) :=
  ∀ {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsImmersion i] [LocallyOfFiniteType i]
    (hi : i ≫ sX = sZ), VirtualNormalBundle i → (p : ℤ) → BivariantClass C G sZ sX i hi p

/-! ### The conclusion of Stacks 0FEC -/

section Composition

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z Y X : Scheme.{u}} (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i : Z ⟶ Y) [IsImmersion i] [LocallyOfFiniteType i] (j : Y ⟶ X)
  [IsImmersion j] [LocallyOfFiniteType j] (hi : i ≫ sY = sZ) (hj : j ≫ sX = sY)
  (hpp : ProperPushforwardDescends C) (p q : ℤ) (cloc : LocalizedChernClassRule C G)
  (D : ConormalCompatibleVirtualNormalBundles i j)

/-- Granted that the class attached to
`𝒩` composes the class attached to `𝒩'` with the class attached to `𝒩''`, its cap operation on
a test scheme `t : T ⟶ X` is: cap with `c(Y ⟶ X, 𝒩'')`, then cap with `c(Z ⟶ Y, 𝒩')`, then push
forward along the associativity isomorphism `(T ×_X Y) ×_Y Z ≅ T ×_X Z` of pullbacks, the
degrees `k - (p + q)` and `(k - q) - p` being identified. -/
@[stacks 0FEC "the conclusion, reduced to the composition of bivariant classes and read on \
cap products; the localized Chern class c(Z ⟶ X, 𝒩) of Stacks 0FBK is not constructed in this \
repository and is carried as a parameter, as everywhere else here, so that the composition \
formula is a hypothesis"]
theorem localizedChernClass_cap_eq_bivariantCompositeCap
    (hc : IsBivariantClassComposition C G sZ sY sX i j hi hj hpp p q
      (cloc sZ sY i hi D.bundleZY p) (cloc sY sX j hj D.bundleYX q)
      (cloc sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj) D.bundleZX (p + q)))
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    chowGroupDegreeEquiv C (pullback.fst (i ≫ j) t ≫ sZ)
        (by ring : k - (p + q) = (k - q) - p)
        ((cloc sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj) D.bundleZX (p + q)).cap
          t k α) =
      bivariantCompositeCap C G sZ sY sX i j hi hj hpp p q (cloc sZ sY i hi D.bundleZY p)
        (cloc sY sX j hj D.bundleYX q) t k α :=
  (isBivariantClassComposition_iff C G sZ sY sX i j hi hj hpp p q (cloc sZ sY i hi D.bundleZY p)
    (cloc sY sX j hj D.bundleYX q) _).1 hc t k α

/-- Any bivariant class of degree `p + q` for `Z ⟶ X` that composes `c(Z ⟶ Y, 𝒩')` with
`c(Y ⟶ X, 𝒩'')` is `c(Z ⟶ X, 𝒩)`, provided the latter composes them. -/
@[stacks 0FEC "uniqueness: the composition formula determines c(Z ⟶ X, 𝒩), so the content of \
the lemma reduces to exhibiting the composite; the localized Chern class of Stacks 0FBK is \
carried as a parameter"]
theorem eq_localizedChernClass_of_isBivariantClassComposition
    (hc : IsBivariantClassComposition C G sZ sY sX i j hi hj hpp p q
      (cloc sZ sY i hi D.bundleZY p) (cloc sY sX j hj D.bundleYX q)
      (cloc sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj) D.bundleZX (p + q)))
    (c : BivariantClass C G sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj) (p + q))
    (hc' : IsBivariantClassComposition C G sZ sY sX i j hi hj hpp p q
      (cloc sZ sY i hi D.bundleZY p) (cloc sY sX j hj D.bundleYX q) c) :
    cloc sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj) D.bundleZX (p + q) = c :=
  eq_of_isBivariantClassComposition (hpp := hpp) hc hc'

end Composition

end Stacks.Chow

end
