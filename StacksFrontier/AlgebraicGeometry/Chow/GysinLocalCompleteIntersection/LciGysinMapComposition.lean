module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalImmersionComposition
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0FF0, 0FF2 and 0FF5: composition and independence of Gysin maps

Let `(S, δ)` be as in Situation 02QL.

* **Stacks 0FF0.** For regular immersions `i : X ⟶ Y` and `j : Y ⟶ Z` of schemes locally of finite
  type over `S`, `j ∘ i` is a regular immersion and `(j ∘ i)^! = i^! ∘ j^!`. The first assertion is
  Stacks 067Q; the second is the immersion counterpart of Stacks 0FEC at the conormal-compatible
  triple of the three normal bundles (Stacks 063N).
* **Stacks 0FF2.** The Gysin map `f^! = i^! ∘ g^*` of a factorization `f = g ∘ i` of a local
  complete intersection morphism does not depend on the factorization.
* **Stacks 0FF5.** For local complete intersection morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` such that
  the Gysin maps of `g ∘ f` and of `g` exist, the Gysin map of `f` exists and
  `(g ∘ f)^! = f^! ∘ g^!`.

The proofs of 0FF2 and 0FF5 are those of the source and are carried out in
`StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.FactorizationIndependenceClass`
and `StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinComposition`, from
Stacks 0FF0 (`Stacks.Chow.regularImmersionCompositionCase` below), the base change of
Stacks 0FBK (`Stacks.Chow.regularImmersionSmoothBaseChangeCase`), Stacks 02RD, the commutation of
bivariant classes with flat pullback and Stacks 0FF1.

## Main results

* `Stacks.Chow.completedVirtualNormalGysinClassOfImmersion_comp_ofIsRegularImmersion` —
  **Stacks 0FF0**.
* `Stacks.Chow.SmoothFactorization.gysinMap_eq` — **Stacks 0FF2**.
* `Stacks.Chow.SmoothFactorization.gysinMap_eq_lciGysinMap` — the Gysin map of any factorization
  is `Stacks.Chow.lciGysinMap`.
* `Stacks.Chow.lciGysinMap_comp` — **Stacks 0FF5**.

## References

* [Stacks Project, Tag 0FF0](https://stacks.math.columbia.edu/tag/0FF0)
* [Stacks Project, Tag 0FF2](https://stacks.math.columbia.edu/tag/0FF2)
* [Stacks Project, Tag 0FF5](https://stacks.math.columbia.edu/tag/0FF5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

/-- The second assertion of Stacks 0FF0 in the form consumed by the proofs of Stacks 0FF2 and
Stacks 0FF5: the immersion counterpart of Stacks 0FEC at the normal bundles of two regular
immersions. -/
theorem regularImmersionCompositionCase (C : ChowSituation.{u}) :
    RegularImmersionCompositionCase C := by
  intro X W P sX _ sW _ sP _ s j _ _ hs hj hsr hjr hr
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  exact completedVirtualNormalGysinClassOfImmersion_comp sX sW sP hs hj
    (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion s j hsr hjr)

/-- **Stacks 0FF0.** Let `s : X ⟶ W` and `j : W ⟶ P` be regular immersions of schemes locally of
finite type over the base. Then `s ≫ j` is a regular immersion and

  `(j ∘ s)^! = s^! ∘ j^!`   in `A^*(X ⟶ P)^∧`,

where `(−)^!` is the class `c(− , 𝒩)` of Stacks 0FBQ (3) of the normal bundle `𝒩 = 𝒞^∨` of the
regular immersion. -/
@[stacks 0FF0, sga "6 VIII 1.5" "special case"]
theorem completedVirtualNormalGysinClassOfImmersion_comp_ofIsRegularImmersion
    (C : ChowSituation.{u}) {X W P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (s : X ⟶ W) (j : W ⟶ P) [IsImmersion s] [IsImmersion j] (hs : s ≫ sW = sX)
    (hj : j ≫ sP = sW) (hsr : IsRegularImmersion s) (hjr : IsRegularImmersion j) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
    letI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
    ∃ hr : IsRegularImmersion (s ≫ j),
      completedVirtualNormalGysinClassOfImmersion C sX sP (s ≫ j)
          (comp_comp_structureMorphism_eq hs hj)
          (VirtualNormalBundle.ofIsRegularImmersion (s ≫ j) hr) =
        completedBivariantCompositeOfInvertible C sX sW sP s j hs hj
          (completedVirtualNormalGysinClassOfImmersion C sX sW s hs
            (VirtualNormalBundle.ofIsRegularImmersion s hsr))
          (completedVirtualNormalGysinClassOfImmersion C sW sP j hj
            (VirtualNormalBundle.ofIsRegularImmersion j hjr)) :=
  ⟨Stacks.AlgebraicGeometry.isRegularImmersion_comp s j hsr hjr,
    regularImmersionCompositionCase C sX sW sP s j hs hj hsr hjr _⟩

section Independence

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX)

/-- **Stacks 0FF2.** Let `f : X ⟶ Y` be a local complete intersection morphism of schemes locally
of finite type over the base. The Gysin map `f^! = i^! ∘ g^* ∈ A^*(X ⟶ Y)^∧` of a factorization
`f = g ∘ i`, `i` an immersion and `g` smooth (Stacks 0FF3), does not depend on the
factorization. -/
@[stacks 0FF2]
theorem SmoothFactorization.gysinMap_eq (F F' : SmoothFactorization f)
    (hlci : IsLocalCompleteIntersectionMorphism f) :
    F.gysinMap C sX sY hf hlci = F'.gysinMap C sX sY hf hlci :=
  SmoothFactorization.gysinMap_eq_of_regularImmersionCompositionCase C sX sY hf
    (regularImmersionCompositionCase C) F F' hlci

/-- The Gysin map of any factorization of a local complete intersection morphism is the Gysin map
`Stacks.Chow.lciGysinMap` of Stacks 0FF3, by Stacks 0FF2. -/
theorem SmoothFactorization.gysinMap_eq_lciGysinMap (F : SmoothFactorization f)
    (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f) :
    F.gysinMap C sX sY hf hlci = lciGysinMap C sX sY hf hlci h :=
  SmoothFactorization.gysinMap_eq_lciGysinMap_of_regularImmersionCompositionCase C sX sY hf
    (regularImmersionCompositionCase C) F hlci h

end Independence

section Composition

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  {f : X ⟶ Y} {g : Y ⟶ Z} [LocallyOfFiniteType f] [LocallyOfFiniteType g] (hf : f ≫ sY = sX)
  (hg : g ≫ sZ = sY)

/-- **Stacks 0FF5.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be local complete intersection morphisms of
schemes locally of finite type over the base, and assume the Gysin map exists for `g ∘ f` and
for `g` (Stacks 0FF3). Then the Gysin map exists for `f`, and

  `(g ∘ f)^! = f^! ∘ g^!`   in `A^*(X ⟶ Z)^∧`.

(`g ∘ f` is a local complete intersection morphism by Stacks 069J.) -/
@[stacks 0FF5]
theorem lciGysinMap_comp (hlf : IsLocalCompleteIntersectionMorphism f)
    (hlg : IsLocalCompleteIntersectionMorphism g) (hgf : GysinMapExists (f ≫ g))
    (hG : GysinMapExists g) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    ∃ hF : GysinMapExists f,
      lciGysinMap C sX sZ (comp_comp_structureMorphism_eq hf hg)
          (isLocalCompleteIntersectionMorphism_comp f g hlf hlg) hgf =
        completedBivariantCompositeOfInvertible C sX sY sZ f g hf hg
          (lciGysinMap C sX sY hf hlf hF) (lciGysinMap C sY sZ hg hlg hG) :=
  lciGysinMap_comp_of_regularImmersionCompositionCase C sX sY sZ hf hg
    (regularImmersionCompositionCase C) hlf hlg hgf hG

end Composition

end Stacks.Chow

end
