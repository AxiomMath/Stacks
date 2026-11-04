module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalk
public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.SheafCondition

/-!
# The stalks of the Koszul complex on a family of sections

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalk` develops the stalk theory of the Koszul
complex of a family of global sections `f₁, …, f_r` of the structure sheaf of a ringed space `X`,
for an arbitrary *presentation* of that complex: a family of presheaves of modules `E n` together
with a sectionwise identification `ξ` of `E n` with the exterior powers of `O_X(U)^r`, the exterior
products `b` of the free generators, and a differential `D` which under `ξ` is the ring-level
Koszul differential. Its conclusion, `seqComplexIsoStalkComplex`, is that the complex of stalks at
a point `x` is the ring-level Koszul complex of the sequence of germs over `O_{X,x}`.

This file supplies that presentation for the Koszul complex built in
`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Sequence`, and so makes the stalk comparison a
statement about an actual object: **the stalk at `x` of `K_•(O_X, f₁, …, f_r)` is the ring-level
Koszul complex `K_•(O_{X,x}, f₁,ₓ, …, f_r,ₓ)`.** That is the reduction the proofs of Stacks tags
063C and 063D use.

## Main definitions

* `Stacks.AlgebraicGeometry.SeqKoszul.pieceEquiv`: the identification of the sections of the
  degree-`n` term with `⋀ⁿ(O_X(U)^r)`; it is the identity.
* `Stacks.AlgebraicGeometry.SeqKoszul.gen`: the exterior products of the free generators.
* `Stacks.AlgebraicGeometry.SeqKoszul.stalkComplex`: the complex of stalks at a point of
  `K_•(O_X, f₁, …, f_r)`.
* `Stacks.AlgebraicGeometry.SeqKoszul.stalkIso`: **the comparison isomorphism.**

## Main results

* `Stacks.AlgebraicGeometry.SeqKoszul.pieceEquiv_wedgeSection`: the identification takes the
  restriction of an exterior product of free generators to the corresponding wedge of standard
  basis vectors. This is the hypothesis `hξ` of the stalk comparison, and the only part of the
  presentation needing a proof.
* `Stacks.AlgebraicGeometry.SeqKoszul.pieceEquiv_diff`: under the identification the differential
  is the ring-level Koszul differential of the restricted family.
* `Stacks.AlgebraicGeometry.SeqKoszul.stalkIso`: the complex of stalks is the ring-level Koszul
  complex of the germs.

## Implementation notes

**The identification `ξ` is the identity, but is built in two steps.** The sections of the
degree-`n` term over `U` are `⋀^n_{O_X(U)}(O_X(U)^r)` definitionally, so `ξ` is the identity map;
but the stalk comparison asks for a linear equivalence over `X.presheaf.obj (op U)`, whereas the
module structure on the sections is over `(X.presheaf ⋙ forget₂ CommRingCat RingCat).obj (op U)`.
Those are the same ring with its `Semiring` instance reached by two different routes, and asking
the elaborator to check that the two `Module` instances agree *while* unfolding a scalar
multiplication exhausts its budget. `pieceEquivAux` is therefore the identity written in the
second spelling, where the check is immediate, and `pieceEquiv` is that term re-typed in the
first, where the check is a single comparison of instances rather than one inside a `whnf`.

**The remaining three pieces of the presentation are definitional.** `gen` is
`PresheafOfModules.finFreeWedge`; the differential is `Stacks.AlgebraicGeometry.SeqKoszul.diff`,
whose source is the degree-`(n + 1)` term because `((n + 1 : ℕ) : ℤ)` and `(n : ℤ) + 1` are
definitionally equal; and the hypothesis that it is the ring-level Koszul differential is
`Subtype.ext rfl`, because both sides are contraction by `Koszul.seqDual` of the restricted family.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
* [Stacks Project, Tag 063C](https://stacks.math.columbia.edu/tag/063C)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

open scoped ExteriorAlgebra

open AlgebraicGeometry PresheafOfModules Stacks.RegularSequence

universe u

namespace Stacks.AlgebraicGeometry.SeqKoszul

variable (X : RingedSpace.{u, u}) (r : ℕ)

/-- The identity identification of the sections of the degree-`n` term of `K_•(O_X, f_•)` with
`⋀ⁿ(O_X(U)^r)`, written over the ring of sections in the spelling the presheaf of modules uses. -/
noncomputable def pieceEquivAux (n : ℕ) (U : Opens X) :
    (piece X r n).obj (op U) ≃ₗ[(X.presheaf ⋙ forget₂ CommRingCat RingCat).obj (op U)]
      (⋀[(X.presheaf ⋙ forget₂ CommRingCat RingCat).obj (op U)]^n
        (Fin r → (X.presheaf ⋙ forget₂ CommRingCat RingCat).obj (op U))) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The sections of the degree-`n` term of `K_•(O_X, f_•)` over `U` are `⋀ⁿ(O_X(U)^r)`**, by the
identity map. This is the datum `ξ` of the stalk comparison. -/
noncomputable def pieceEquiv (n : ℕ) (U : Opens X) :
    (piece X r n).obj (op U) ≃ₗ[X.presheaf.obj (op U)]
      (⋀[X.presheaf.obj (op U)]^n (Fin r → X.presheaf.obj (op U))) :=
  pieceEquivAux X r n U

/-- **The exterior product of the free generators indexed by a tuple**, as a global section of the
degree-`n` term of `K_•(O_X, f_•)`. This is the datum `b` of the stalk comparison. -/
noncomputable def gen (n : ℕ) (i : Fin n → Fin r) : (piece X r n).obj (op (⊤ : Opens X)) :=
  finFreeWedge X.presheaf r n (op (⊤ : Opens X)) i

/-- The identity identification takes an exterior product of free generators to the wedge of the
standard basis vectors with the same indices, over the ring of sections in the spelling the
presheaf of modules uses. -/
theorem pieceEquivAux_wedgeSection (n : ℕ) (U : Opens X) (i : Fin n → Fin r) :
    pieceEquivAux X r n U (wedgeSection X (piece X r) (gen X r) n i U) =
      exteriorPower.ιMulti ((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj (op U)) n
        (fun j => finFreeSingle X.presheaf r (op U) (i j)) := by
  have h : wedgeSection X (piece X r) (gen X r) n i U = finFreeWedge X.presheaf r n (op U) i :=
    map_finFreeWedge X.presheaf r n (homOfLE (le_top : U ≤ ⊤)).op i
  rw [h]
  rfl

/-- **The identification takes an exterior product of free generators to the corresponding wedge of
standard basis vectors.** This is the hypothesis `hξ` of the stalk comparison. -/
theorem pieceEquiv_wedgeSection (n : ℕ) (U : Opens X) (i : Fin n → Fin r) :
    pieceEquiv X r n U (wedgeSection X (piece X r) (gen X r) n i U) =
      exteriorPower.ιMulti (X.presheaf.obj (op U)) n
        (fun j => Pi.single (i j) (1 : X.presheaf.obj (op U))) :=
  pieceEquivAux_wedgeSection X r n U i

variable (f : Fin r → X.presheaf.obj (op (⊤ : Opens X)))

/-- **Under the identification the Koszul differential is the ring-level Koszul differential of the
restricted family.** This is the hypothesis `hD` of the stalk comparison. -/
theorem pieceEquiv_diff (n : ℕ) (U : Opens X) (s : (piece X r (n + 1)).obj (op U)) :
    pieceEquiv X r n U ((diff X r f n).app (op U) s) =
      Koszul.d (Koszul.seqDual (resSequence X f U)) n (pieceEquiv X r (n + 1) U s) :=
  Subtype.ext rfl

/-- **The complex of stalks at `x` of `K_•(O_X, f₁, …, f_r)`**: in degree `n` the stalk of the
degree-`n` term, with the maps induced on stalks by the Koszul differentials. -/
noncomputable def stalkComplex (x : X) : ChainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℕ :=
  Stacks.RegularSequence.stalkComplex X f (piece X r) (pieceEquiv X r) (gen X r)
    (pieceEquiv_wedgeSection X r) (diff X r f) (pieceEquiv_diff X r f) x

/-- **The stalk of the Koszul complex is the Koszul complex of the germs.** At every point `x` the
complex of stalks of `K_•(O_X, f₁, …, f_r)` is isomorphic to the ring-level Koszul complex of the
sequence of germs `f₁,ₓ, …, f_r,ₓ` over the stalk `O_{X,x}`. -/
noncomputable def stalkIso (x : X) :
    Koszul.seqComplex (germSequence X f x) ≅ stalkComplex X r f x :=
  seqComplexIsoStalkComplex X f (piece X r) (pieceEquiv X r) (gen X r)
    (pieceEquiv_wedgeSection X r) (diff X r f) (pieceEquiv_diff X r f) x

end Stacks.AlgebraicGeometry.SeqKoszul

end
