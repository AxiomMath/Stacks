module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantChernCentral
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernClassBivariant
import StacksCore.Tactic.StacksAttribute

/-!
# The first Chern class is central (Stacks 0B7B)

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let `ℒ` be an
invertible `𝒪_X`-module. Stacks 0B7B asserts:

1. `c₁(ℒ) ∈ A^1(X)` is in the center of `A^*(X)`;
2. if `f : X' ⟶ X` is locally of finite type and `c ∈ A^*(X' ⟶ X)`, then
   `c ∘ c₁(ℒ) = c₁(f^*ℒ) ∘ c`.

Here `c₁(ℒ)` is the bivariant class `Stacks.Chow.GenuineChern.firstChernClass` of Stacks 0B77,
which caps by `c₁(g^*ℒ) ∩ -` on every test scheme `g : T ⟶ X`; the bivariant classes of clause (2)
are those of Stacks 0B76, `Stacks.Chow.BivariantChowClass`; and `A^*(X)` is the Chow cohomology
ring of Stacks 0B7E, `Stacks.Chow.chowCohomologyRingOfInvertible`.

## The argument

On a test scheme `g : T ⟶ X` both clauses come down to the identity
`c ∩ (c₁(g^*ℒ) ∩ α) = c₁(ℒ') ∩ (c ∩ α)` on `T ×_X X'`, which is
`Stacks.Chow.BivariantChowClass.cap_firstChernClassCapChow`: the zero scheme of the zero section
of `g^*ℒ` together with Stacks 02T9 and conditions (1) and (3) of Stacks 0B76. The invertible
module `ℒ` is finite locally free of rank one and `c₁(ℒ)` is by definition the bivariant Chern
class `c_1(ℒ)` of Stacks 0B7H, so the passage from this identity to the equalities of bivariant
classes is the one carried out for every Chern class in
`Stacks.Chow.GenuineChern.comp_chernClass` and `Stacks.Chow.GenuineChern.chernClass_mem_center`,
here at rank one.

## Main results

* `Stacks.Chow.GenuineChern.comp_firstChernClass` — **Stacks 0B7B (2)**: `c ∘ c₁(ℒ) = c₁(f^*ℒ) ∘ c`
  in `A^{p+1}(X' ⟶ X)`.
* `Stacks.Chow.GenuineChern.firstChernClass_mem_center` — **Stacks 0B7B (1)**: `c₁(ℒ)` lies in the
  center of `A^*(X)`.

## Implementation notes

The two composites of clause (2) are classes for `f ≫ 𝟙 X` and for `𝟙 X' ≫ f`, of degrees `p + 1`
and `1 + p`. The second is read as a class for `f ≫ 𝟙 X` of degree `p + 1` through
`Stacks.Chow.BivariantChowClass.degreeCongr` and the transport along the identity of `X'`.

## References

* [Stacks Project, Tag 0B7B](https://stacks.math.columbia.edu/tag/0B7B)
* [Stacks Project, Tag 0B77](https://stacks.math.columbia.edu/tag/0B77)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- **Stacks 0B7B (2).** Let `ℒ` be an invertible `𝒪_X`-module, let `f : X' ⟶ X` be locally of
finite type and let `c ∈ A^p(X' ⟶ X)` be a bivariant class. Then

  `c ∘ c₁(ℒ) = c₁(f^*ℒ) ∘ c`   in   `A^{p+1}(X' ⟶ X)`,

with `c₁(ℒ) ∈ A^1(X)` and `c₁(f^*ℒ) ∈ A^1(X')` the bivariant first Chern classes of Stacks 0B77.
The left side is a class for `f ≫ 𝟙 X` of degree `p + 1`; the right side, a class for `𝟙 X' ≫ f` of
degree `1 + p`, is read as one for `f ≫ 𝟙 X` of degree `p + 1` along the identity of `X'`. -/
@[stacks 0B7B "(2): c ∘ c_1(L) = c_1(f^*L) ∘ c in A^{p+1}(X' → X) for every f : X' → X locally \
of finite type and every bivariant class c in A^p(X' → X) of Stacks 0B76"]
theorem comp_firstChernClass {X' : Scheme.{u}} {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX']
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (f : X' ⟶ X) (hf : f ≫ sX = sX') {p : ℤ} (c : BivariantChowClass C sX' sX f hf p) :
    haveI := isInvertible_pullback f L
    c.comp (BivariantChowClass.equivBivariantClass.symm (firstChernClass C sX L)) =
      (((BivariantChowClass.equivBivariantClass.symm
          (firstChernClass C sX' ((Scheme.Modules.pullback f).obj L))).comp c).degreeCongr
        (add_comm 1 p)).transport (comp_comp_structureMorphism_eq hf (Category.id_comp sX))
        (Iso.refl X') (by simp) := by
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  exact comp_chernClass L 1 1 f hf c

/-- **Stacks 0B7B (1).** The first Chern class `c₁(ℒ) ∈ A^1(X)` of an invertible `𝒪_X`-module lies
in the center of the Chow cohomology ring `A^*(X)` of Stacks 0B7E. The ring structure is an
`@[instance_reducible] def` and not an `instance`, which is why it is supplied by hand. -/
@[stacks 0B7B "(1): c_1(L) in A^1(X) is in the center of the Chow cohomology ring A^*(X) of \
Stacks 0B7E, for the bivariant first Chern class of Stacks 0B77"]
theorem firstChernClass_mem_center (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    letI : Ring (chowCohomology C (gysinSystemOfInvertible C) sX) :=
      chowCohomologyRingOfInvertible C sX
    DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) 1
        (firstChernClass C sX L) ∈
      Subring.center (chowCohomology C (gysinSystemOfInvertible C) sX) := by
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  exact chernClass_mem_center L 1 1

end Stacks.Chow.GenuineChern

end
