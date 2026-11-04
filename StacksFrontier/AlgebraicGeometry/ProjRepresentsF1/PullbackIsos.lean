module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.Representation
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Invertible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# The pullback comparison on tensor algebras, constructed

`Stacks.AlgebraicGeometry.ProjRepresentsF1.TensorAlgebraPullbackIsos` is taken as a hypothesis
by the statement of Tag 01O4 in
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.Representation`. This file constructs one,
so that hypothesis is no longer a hypothesis: `tensorAlgebraPullbackIsos` is a term of that
type for an arbitrary choice of tensor algebras.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso`: Stacks 01CD read at the
  scheme spelling — for `g : T' ⟶ T` and sheaves of modules `M`, `N` on `T`,
  `g^*(M ⊗ N) ≅ g^*M ⊗ g^*N`, where the tensor product is the one
  `SheafOfModules.tensorPower` is built from and the pullback is
  `AlgebraicGeometry.Scheme.Modules.pullback`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorPowerIso`: pullback commutes with
  every tensor power, `g^*(L^{⊗n}) ≅ (g^*L)^{⊗n}`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorAlgebraPullbackIsos`: **the point of the
  file.** A term of `TensorAlgebraPullbackIsos TA`, for every choice `TA` of tensor algebras.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1RepresentationCanonical`: Tag 01O4's
  representation with that comparison supplied rather than assumed — the type of the
  representation Tag 01O4 asks for, with one parameter fewer.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isZero_tensorPiece_of_neg`: a negative-degree
  piece of a tensor algebra is a zero object, and
  `Stacks.AlgebraicGeometry.ProjRepresentsF1.isZero_pullback_obj`: pullback carries a zero
  object to a zero object.

## Implementation notes

**Stacks 01CD needs no bridge to reach the scheme spelling.** `Stacks.PullbackTensorIso.pullbackTensorIso` is stated for a morphism of ringed
spaces, with the pullback `RingedSpaceModuleAdjunction.modulePullback` and the tensor product
`Stacks.RingedSpace.tensorSheaf`. Both of those unfold to exactly what the scheme spelling
uses: `modulePullback f` is `CategoryTheory.SheafOfModules.pullback (structureSheafHom f)` and
`AlgebraicGeometry.Scheme.Modules.pullback g` is `SheafOfModules.pullback g.toRingCatSheafHom`,
with the same structure-sheaf morphism; and `Stacks.RingedSpace.tensorSheaf` is literally
`Stacks.SheafOfModules.Tensor.sheafTensor`, which is what `SheafOfModules.tensorPower` iterates.
So `pullbackTensorSchemeIso` is one component of that bifunctor isomorphism, applied to
the ringed-space morphism underlying `g`, with no transport and no comparison lemma.

**The hypothesis is pure data, with no coherence, and that is why this is short.**
`TensorAlgebraPullbackIsos` asks only for an isomorphism in each degree: no multiplicativity,
no unitality, no compatibility with the generator. So the three degree ranges can be settled
independently — negative degrees because both sides are zero objects, degree zero by the
pullback of the structure sheaf, and the rest by induction on the tensor power.

**The pullback of the structure sheaf is taken from the library.**
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` is Mathlib's comparison
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit`, which is an isomorphism because the
inverse-image functor on opens of a morphism of schemes is final, and it is stated there at the
scheme spelling. So degree zero of `pullbackTensorPowerIso` is that isomorphism itself: the
degree-zero tensor power is the structure sheaf as a module over itself, which is what
`AlgebraicGeometry.Scheme.unitModule` names.

**No `rw` on a morphism of sheaves of modules appears here**, as in the rest of this
directory; the degree transport in `tensorAlgebraPullbackIsos` is
`CategoryTheory.eqToIso` of a `congrArg`, which is term-level.

## Not done here

This removes one of the two hypotheses from Tag 01O4's statement. The other,
`Stacks.AlgebraicGeometry.ProjRepresentsF1.TensorAlgebras`, is supplied at a canonical value by
`Stacks.AlgebraicGeometry.ProjRepresentsF1.canonicalTensorAlgebras`, built from
`SheafOfModules.algebras`; `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1RepresentationOf` is the
resulting type, depending on the graded algebra alone.
`Stacks.AlgebraicGeometry.ProjRepresentsF1.Representation` still takes
`TensorAlgebraPullbackIsos` as a parameter; de-parameterising it would change the signature of
`F1Representation`, so the construction is supplied here instead, to be passed in.

**No project tag is attached.** The label `01O4 "represents_f1"` covers four assertions, and
the fourth — the construction of an
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation` — is not here. Nothing in this
file is a clause of Tag 01O4; it is Tag 01CD put to work.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

variable {T T' : Scheme.{u}} (g : T' ⟶ T)

/-! ### Stacks 01CD at the scheme spelling -/

/-- **Stacks 01CD, at the scheme spelling.** Pullback along a morphism of schemes commutes
with the tensor product of sheaves of modules.

This is one component of the isomorphism of bifunctors
`Stacks.PullbackTensorIso.pullbackTensorIso`, applied to the morphism of ringed spaces
underlying `g`. No transport is involved: see the implementation notes. -/
public def pullbackTensorSchemeIso (M N : T.Modules) :
    (Scheme.Modules.pullback g).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(T).presheaf, (T).IsSheaf⟩).obj M).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(T').presheaf, (T').IsSheaf⟩).obj ((Scheme.Modules.pullback g).obj M)).obj
        ((Scheme.Modules.pullback g).obj N) :=
  (Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).app (M, N)

/-! ### Pullback commutes with tensor powers -/

/-- **Pullback commutes with every tensor power.** `g^*(L^{⊗n}) ≅ (g^*L)^{⊗n}`.

In degree zero both sides are the structure sheaf, by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`; in degree one both sides are `g^*L` on the
nose; and the step from `n + 1` to `n + 2` is `pullbackTensorSchemeIso` followed by the
inductive isomorphism in the second tensor factor. -/
public def pullbackTensorPowerIso (L : T.Modules) : ∀ n : ℕ,
    (Scheme.Modules.pullback g).obj
        (SheafOfModules.tensorPower (Opens.grothendieckTopology ↥T) L n) ≅
      SheafOfModules.tensorPower (Opens.grothendieckTopology ↥T')
        ((Scheme.Modules.pullback g).obj L) n
  | 0 => Scheme.Modules.pullbackUnitIso g
  | 1 => Iso.refl _
  | (n + 2) =>
      pullbackTensorSchemeIso g L
          (SheafOfModules.tensorPower (Opens.grothendieckTopology ↥T) L (n + 1)) ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(T').presheaf, (T').IsSheaf⟩).obj
          ((Scheme.Modules.pullback g).obj L)).mapIso (pullbackTensorPowerIso L (n + 1))

/-! ### The negative degrees -/

/-- Pullback carries a zero object to a zero object, being an additive functor. -/
public theorem isZero_pullback_obj {X : T.Modules} (h : IsZero X) :
    IsZero ((Scheme.Modules.pullback g).obj X) :=
  IsZero.of_iso (isZero_zero _)
    ((Scheme.Modules.pullback g).mapIso h.isoZero ≪≫ (Scheme.Modules.pullback g).mapZeroObject)

/-- In a negative degree the tensor algebra is a zero object.

The bundle records the vanishing of negative degrees as the vanishing of every local section;
that makes any two morphisms into the piece equal, so in particular its identity is zero. -/
public theorem isZero_tensorPiece_of_neg {X : Scheme.{u}} (TA : TensorAlgebras.{u})
    (L : X.Modules) {n : ℤ} (hn : n < 0) : IsZero ((TA X L).tensor.piece n) :=
  (IsZero.iff_id_eq_zero _).2 ((TA X L).hom_ext_tensorPiece_of_neg hn _ _)

/-! ### The comparison, in one degree and then in all -/

/-- The degree-`m` comparison for a natural number `m`: the pullback of the degree-`m` piece of
the tensor algebra of `L` is the degree-`m` piece of the tensor algebra of `g^*L`.

Both pieces are identified with tensor powers by the bundle's own `tensorPieceIso`, and the
tensor powers are compared by `pullbackTensorPowerIso`. -/
public def pullbackTensorPieceIso (TA : TensorAlgebras.{u}) (L : T.Modules) (m : ℕ) :
    (Scheme.Modules.pullback g).obj ((TA T L).tensor.piece (m : ℤ)) ≅
      (TA T' ((Scheme.Modules.pullback g).obj L)).tensor.piece (m : ℤ) :=
  (Scheme.Modules.pullback g).mapIso ((TA T L).tensorPieceIso m) ≪≫
    pullbackTensorPowerIso g L m ≪≫
    ((TA T' ((Scheme.Modules.pullback g).obj L)).tensorPieceIso m).symm

/-- **The pullback comparison of Tag 01O4's statement, constructed.** For every choice `TA` of
tensor algebras there is a degreewise comparison of the pullback of a tensor algebra with the
tensor algebra of the pullback, so
`Stacks.AlgebraicGeometry.ProjRepresentsF1.TensorAlgebraPullbackIsos` need not be assumed.

In a nonnegative degree this is `pullbackTensorPieceIso`, transported along
`Int.toNat_of_nonneg`; in a negative degree both sides are zero objects, by
`isZero_tensorPiece_of_neg` and `isZero_pullback_obj`. -/
public def tensorAlgebraPullbackIsos (TA : TensorAlgebras.{u}) :
    TensorAlgebraPullbackIsos.{u} TA := fun {T T'} g L n =>
  if hn : 0 ≤ n then
    eqToIso (congrArg
        (fun k : ℤ => (Scheme.Modules.pullback g).obj ((TA T L).tensor.piece k))
        (Int.toNat_of_nonneg hn).symm) ≪≫
      pullbackTensorPieceIso g TA L n.toNat ≪≫
      eqToIso (congrArg
        (fun k : ℤ => (TA T' ((Scheme.Modules.pullback g).obj L)).tensor.piece k)
        (Int.toNat_of_nonneg hn))
  else
    IsZero.iso (isZero_pullback_obj g (isZero_tensorPiece_of_neg TA L (not_le.1 hn)))
      (isZero_tensorPiece_of_neg TA ((Scheme.Modules.pullback g).obj L) (not_le.1 hn))

/-- Tag 01O4's representation with its pullback comparison supplied canonically, rather than
assumed.

This is `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation` at
`tensorAlgebraPullbackIsos`, and it exists in order to make the claim machine-checkable: the
parameter `ι` of that structure is dischargeable, so the only hypotheses Tag 01O4's statement
still carries are the choice of tensor algebras and the twist datum. It is the type of the
representation whose construction the fourth assertion of Tag 01O4 asks for. -/
public abbrev F1RepresentationCanonical {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S)
    (TA : TensorAlgebras.{u}) (D : TwistData A) : Type (u + 1) :=
  F1Representation A TA (tensorAlgebraPullbackIsos TA) D

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
