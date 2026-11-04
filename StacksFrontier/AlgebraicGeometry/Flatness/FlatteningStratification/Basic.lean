module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.Basic

/-!
# Universal flattenings and flattening stratifications

A quasi-coherent module on a scheme over `S` admits a *universal flattening* when its flatness
functor is representable, and admits a *flattening stratification* when the representing object
is the disjoint union of the locally closed strata of a locally finite scheme-theoretic
stratification of `S`. A scheme over `S` admits either when its structure sheaf does.

## Main definitions

* `AlgebraicGeometry.FlatnessSituation.HasUniversalFlattening` is representability of the
  flatness functor of a quasi-coherent module.
* `AlgebraicGeometry.structureSheafFlatnessSituation` is the flatness situation of the
  structure sheaf of a scheme over `S`.
* `AlgebraicGeometry.HasUniversalFlattening` is the universal flattening condition for a
  morphism of schemes.
* `AlgebraicGeometry.FlatnessSituation.HasFlatteningStratification` is the flattening
  stratification condition for a quasi-coherent module.
* `AlgebraicGeometry.HasFlatteningStratification` is the flattening stratification condition
  for a morphism of schemes.

## References

* [Stacks Project, Tag 05P6](https://stacks.math.columbia.edu/tag/05P6)
* [Stacks Project, Tag 05P7](https://stacks.math.columbia.edu/tag/05P7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- A quasi-coherent module admits a universal flattening when its flatness functor is
represented by a scheme over the base. -/
@[stacks 05P6 "the universal flattening of a module"]
public noncomputable abbrev FlatnessSituation.HasUniversalFlattening
    (D : FlatnessSituation.{u}) : Prop :=
  D.flatFunctor.IsRepresentable

/-- The flatness situation for the structure sheaf of a scheme over `S`. -/
public noncomputable abbrev structureSheafFlatnessSituation {X S : Scheme.{u}} (f : X ⟶ S) :
    FlatnessSituation.{u} where
  S := S
  X := X
  f := f
  F := SheafOfModules.unit (structureSheafRing X.toRingedSpace)
  isQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X

/-- A scheme over `S` admits a universal flattening when its structure sheaf does. -/
@[stacks 05P6 "the universal flattening of a scheme"]
public noncomputable abbrev HasUniversalFlattening {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  FlatnessSituation.HasUniversalFlattening (structureSheafFlatnessSituation f)

/-- A quasi-coherent module has a flattening stratification if its flatness functor is
represented by the monomorphism associated to a locally finite scheme-theoretic stratification
of the base: closed subschemes `J i`, indexed by a partial order, whose supports cover `S` and
form a locally finite family, with `J i ⊔ J j` the infimum of the `J k` for `k ≤ i` and `k ≤ j`,
together with opens `U i` of the subschemes `J i` whose images are the supports of `J i` minus
those of the `J j` with `j < i`, such that the representing object is isomorphic over `S` to the
coproduct of the `U i` and its structure morphism is a monomorphism. -/
@[stacks 05P7 "the module"]
public def FlatnessSituation.HasFlatteningStratification (D : FlatnessSituation.{u}) : Prop :=
  ∃ (I : Type u) (hI : PartialOrder I), letI := hI;
    ∃ (J : I → D.S.IdealSheafData),
      (⋃ i, (J i).support : Set D.S) = Set.univ ∧
      LocallyFinite (fun i => ((J i).support : Set D.S)) ∧
      (∀ i j, J i ⊔ J j = ⨅ k ∈ {k | k ≤ i ∧ k ≤ j}, J k) ∧
      ∃ (U : ∀ i, (J i).subscheme.Opens),
        (∀ i, Set.range ((U i).ι ≫ (J i).subschemeι) =
          ((J i).support : Set D.S) \ (⋃ j ∈ {j | j < i}, ((J j).support : Set D.S))) ∧
        let Y : I → Scheme.{u} := fun i => (U i).toScheme;
        let g : ∀ i, Y i ⟶ D.S := fun i => (U i).ι ≫ (J i).subschemeι;
        ∃ (W : Over D.S) (e : W.left ≅ ∐ Y),
          Mono W.hom ∧ W.hom = e.hom ≫ Sigma.desc g ∧
            Nonempty (D.flatFunctor.RepresentableBy W)

/-- A scheme over `S` has a flattening stratification when its structure sheaf does. -/
@[stacks 05P7 "the scheme"]
public abbrev HasFlatteningStratification {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  letI : (SheafOfModules.unit (structureSheafRing X.toRingedSpace)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  FlatnessSituation.HasFlatteningStratification
    { S := S, X := X, f := f, F := SheafOfModules.unit (structureSheafRing X.toRingedSpace) }

end AlgebraicGeometry
