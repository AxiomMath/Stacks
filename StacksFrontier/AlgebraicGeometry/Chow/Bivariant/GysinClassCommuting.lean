module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Commuting

/-!
# The bivariant Gysin class of a divisor commutes with every bivariant class (Stacks 0FA3)

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let
`(𝓛, s, i : D ⟶ X)` be a triple as in Definition 02T8. Let `f : Z ⟶ X` be locally of finite type
and let `c ∈ A^p(Z ⟶ X)`. Stacks 0FA3 asserts that the bivariant Gysin class `i^* ∈ A^1(D ⟶ X)`
of Stacks 0B79 commutes with `c` in the sense of Remark 0FA2:

  `i^* ∩ (c ∩ α) = c ∩ (i^* ∩ α)`   for `α ∈ CH_k(T)` and every `T ⟶ X` locally of finite type,

equivalently `res(i^*) ∘ c = res(c) ∘ i^*` in `A^{p+1}(D ×_X Z ⟶ X)`.

Here `A^p(Z ⟶ X)` is the group `Stacks.Chow.BivariantChowClass` of Definition 0B76, whose
third axiom is stated against the Gysin map of Stacks 02TO, and `i^*` is
`Stacks.Chow.gysinBivariantClass`, read through the bridge
`Stacks.Chow.BivariantChowClass.equivBivariantClass`.

## Main results

* `Stacks.Chow.gysinBivariantClass_bivariantCommute` — **Stacks 0FA3**: `i^*` and `c` commute in
  the sense of Remark 0FA2.
* `Stacks.Chow.gysinBivariantClass_comp_comm` — **Stacks 0FA3**, read on composites:
  `res(i^*) ∘ c = res(c) ∘ i^*`.

## Implementation notes

As in the source, the commutation is a restatement of condition (3) of Definition 0B76 for `c`:
this is `Stacks.Chow.gysinBivariantCommute`, instantiated at the Gysin system of the first Chern
class rule of an invertible module, for which the invariance of the Gysin map under iterated
pullback of the invertible module is
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward`, and at the class of
Stacks 0B79, which caps by the Gysin map of the pulled-back section by construction.

## References

* [Stacks Project, Tag 0FA3](https://stacks.math.columbia.edu/tag/0FA3)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (f : Z ⟶ X) [LocallyOfFiniteType f] (p : ℤ)

/-- **Stacks 0FA3.** Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over
`S`, let `(𝓛, s, i : D ⟶ X)` be a triple as in Definition 02T8, let `f : Z ⟶ X` be locally of
finite type and let `c ∈ A^p(Z ⟶ X)` be a bivariant class of Definition 0B76. Then the bivariant
Gysin class `i^* ∈ A^1(D ⟶ X)` of Stacks 0B79 commutes with `c` in the sense of Remark 0FA2:
`i^* ∩ (c ∩ α) = c ∩ (i^* ∩ α)` for every `α ∈ CH_k(T)` and every `T ⟶ X` locally of finite
type, the two sides compared by the canonical isomorphism `D ×_X (Z ×_X T) ≅ Z ×_X (D ×_X T)`.

This is a restatement of condition (3) of Definition 0B76 for `c`. -/
@[stacks 0FA3 "the Gysin class i^* of Stacks 0B79 commutes with every c ∈ A^p(Z → X), in the \
sense of Remark 0FA2"]
theorem gysinBivariantClass_bivariantCommute
    (c : BivariantChowClass C (f ≫ sX) sX f rfl p) :
    BivariantCommute C (gysinSystemOfInvertible C) sX (gysinTripleInclusion L s) f 1 p
      (gysinBivariantClass C sX L s).1 (BivariantChowClass.equivBivariantClass c) :=
  gysinBivariantCommute C (gysinSystemOfInvertible C) sX L s f p
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)
    (BivariantChowClass.equivBivariantClass c) (gysinBivariantClass C sX L s).1
    (gysinBivariantClass C sX L s).2

/-- **Stacks 0FA3, on composites.** In the situation of
`Stacks.Chow.gysinBivariantClass_bivariantCommute`, with `i^* ∈ A^1(D ⟶ X)` the bivariant Gysin
class of Stacks 0B79 and `c ∈ A^p(Z ⟶ X)`,

  `res(i^*) ∘ c = res(c) ∘ i^*`   in   `A^{1+p}(D ×_X Z ⟶ X)`,

which Remark 0FA2 identifies with the commutation of `i^*` and `c`. Here
`res(i^*) ∈ A^1(D ×_X Z ⟶ Z)` and `res(c) ∈ A^p(Z ×_X D ⟶ D)` are the restrictions of
Remark 0F9Z; the second composite lives on `Z ×_X D` and in degree `p + 1`, and is read on
`D ×_X Z` through the canonical isomorphism and in degree `1 + p`. -/
@[stacks 0FA3 "res(i^*) ∘ c = res(c) ∘ i^* in A^{1+p}(D ×_X Z → X), the form of Remark 0FA2 on \
composites"]
theorem gysinBivariantClass_comp_comm {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ]
    (hZ : f ≫ sX = sZ) (c : BivariantChowClass C sZ sX f hZ p) :
    ((BivariantChowClass.equivBivariantClass.symm (gysinBivariantClass C sX L s).1).restrict f
        hZ).comp c =
      (((c.restrict (gysinTripleInclusion L s) rfl).comp
          (BivariantChowClass.equivBivariantClass.symm
            (gysinBivariantClass C sX L s).1)).degreeCongr (add_comm p 1)).transport
        (comp_comp_structureMorphism_eq (BivariantChowClass.restrict_structure_eq rfl f hZ) hZ)
        (pullbackSymmetry f (gysinTripleInclusion L s))
        (pullbackSymmetry_hom_comp_snd_comp (gysinTripleInclusion L s) f) := by
  subst hZ
  exact BivariantChowClass.restrict_comp_eq_of_bivariantCommute sX (gysinTripleInclusion L s) f _ c
    (gysinBivariantClass_bivariantCommute C sX L s f p c)

end Stacks.Chow

end
