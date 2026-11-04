module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The functor of invertible degree-one quotients of a graded algebra

Let `S` be a scheme and `A` a commutative, nonnegatively graded, quasi-coherent graded
`𝒪_S`-algebra — Situation 01NN, in the sheaf-level form
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`. Tag 01O4 asserts that, when
`A` is generated in degree one, the relative homogeneous spectrum of `A` represents the functor
sending a scheme `f : T ⟶ S` over `S` to the set of surjective graded `𝒪_T`-algebra maps
`f^*A ⟶ T(L)` with `L` invertible, taken up to strict isomorphism.

This file writes down that functor and settles its quotient: the relation "strictly isomorphic"
is an equivalence relation, so a point of the functor is a single strict isomorphism class and
not a chain of them.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.TensorAlgebras`: a choice, for every scheme and
  every sheaf of modules on it, of the tensor algebra of that sheaf together with its exterior
  and symmetric quotients. See the implementation notes: this is a *hypothesis*, because the
  construction of `SheafOfModules.TensorExteriorSymmetricAlgebras` is not in the library.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne`: the graded algebra is
  generated in degree one over every affine open of the base.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair`: an invertible sheaf `L` on `T` together
  with a surjective-in-degree-one graded map `f^*A ⟶ T(L)`, written through the
  pullback–pushforward adjunction as a family of maps `A n ⟶ f_* T(L) n`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.StrictlyEquivalent`: strict isomorphism of pairs.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1`: the set of strict isomorphism classes.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.strictlyEquivalent_equivalence`: strict isomorphism
  of pairs is an equivalence relation.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.quot_mk_eq_iff_strictlyEquivalent`: two pairs have
  the same class exactly when they are strictly isomorphic — not merely joined by a chain of
  strict isomorphisms, which is all that the quotient by the generated equivalence relation says
  on the face of it.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.gradedAlgebraIsoApp`: an isomorphism of sheaves of
  graded algebras is an isomorphism in every degree, with the inverse's component as inverse.
  This is what makes the symmetry and transitivity arguments above term-level.

## Implementation notes

**The tensor algebra is taken as a parameter rather than fixed, and the parameter is
satisfiable.** `SheafOfModules.algebras`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk`, constructs
`SheafOfModules.TensorExteriorSymmetricAlgebras J F` for an arbitrary sheaf of modules, and
`Stacks.AlgebraicGeometry.ProjRepresentsF1.canonicalTensorAlgebras` instantiates it at the site
of open subsets of a scheme, so the parameter below has a canonical value; the statements are
proved for an arbitrary one, and therefore hold at that value as well.
`TensorAlgebras` packages the choice uniformly over all schemes because `F1Pair` carries `L` as
a field, so the tensor algebra of `L` has to be available as a function of `L`, and because the
pullback clauses of Tag 01O4 compare the tensor algebras of a sheaf and of its pullback, which
live on two different schemes. Nothing below depends on the choice being canonical or on its
behaviour under pullback; the two theorems are proved for an arbitrary `TensorAlgebras`, so they
specialise to the canonical choice as soon as one exists.

**The graded algebra on `T` is indexed by `T.ringCatSheaf`, with no transport.** A sheaf of
graded algebras on the site of opens of `T` over `CategoryTheory.Sheaf.toRingCat` of the
structure sheaf is, by `SheafOfModules.ringSheaf_eq`, one over `T.ringCatSheaf` on the nose, so
`(TA T L).tensor.piece n` is already an object of `T.Modules` and `f_*` applies to it directly.

**`rw` is unusable on these morphisms**: it fails to find
patterns that the error message prints character-for-character identically to the goal, the
mismatch being in the `Category` instance argument. Both proofs below are therefore term-mode,
built from `gradedAlgebraIsoApp` and `CategoryTheory.Iso.comp_inv_eq`; the two `sectionsMap`
clauses go through `congrArg` because `SheafOfModules.sectionsMap_comp` and `sectionsMap_id`
hold by `rfl`, so the composite of the two components can be replaced by the identity inside a
`sectionsMap` with no rewriting at all.

**The quotient is by the generated equivalence relation, as in the source.** `F1` is a `Quot` of
`Relation.EqvGen.setoid`, which is the shape the source's "modulo strict isomorphism" is written
in, and `quot_mk_eq_iff_strictlyEquivalent` is the statement that this is no coarser than strict
isomorphism itself.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)

## Not done here

Nothing is said about the relative homogeneous spectrum: the universal pair, the representing
bijections and the classifying morphism are in
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.Representation`, and the construction of the
representation itself is not proved anywhere. No project tag is attached in this directory; the
label `01O4 "represents_f1"` covers four assertions and only three of them are available, so the
covering set is incomplete. See the accompanying report.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

/-! ### Isomorphisms of sheaves of graded algebras, degreewise -/

/-- An isomorphism of sheaves of graded algebras is an isomorphism of sheaves of modules in
every degree, the inverse being the corresponding component of the inverse homomorphism. -/
public def gradedAlgebraIsoApp {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {P Q : SheafOfModules.GradedAlgebra.{u, u} R} (γ : P ≅ Q)
    (n : ℤ) : P.piece n ≅ Q.piece n where
  hom := γ.hom.app n
  inv := γ.inv.app n
  hom_inv_id := congrArg (fun h : P ⟶ P => h.app n) γ.hom_inv_id
  inv_hom_id := congrArg (fun h : Q ⟶ Q => h.app n) γ.inv_hom_id

/-- The forward map of `gradedAlgebraIsoApp γ n` is the degree `n` component of `γ.hom`. -/
@[simp]
public theorem gradedAlgebraIsoApp_hom {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {P Q : SheafOfModules.GradedAlgebra.{u, u} R} (γ : P ≅ Q) (n : ℤ) :
    (gradedAlgebraIsoApp γ n).hom = γ.hom.app n :=
  rfl

/-- The inverse of `gradedAlgebraIsoApp γ n` is the degree `n` component of `γ.inv`. -/
@[simp]
public theorem gradedAlgebraIsoApp_inv {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {P Q : SheafOfModules.GradedAlgebra.{u, u} R} (γ : P ≅ Q) (n : ℤ) :
    (gradedAlgebraIsoApp γ n).inv = γ.inv.app n :=
  rfl

/-! ### The tensor algebras, as a hypothesis -/

/-- A choice of the tensor algebra, with its exterior and symmetric quotients, for every sheaf
of modules on every scheme.

`SheafOfModules.TensorExteriorSymmetricAlgebras` is stated but not constructed in this library,
so this is the form in which Tag 01O4's statement can be written down at all. See the
implementation notes. -/
public abbrev TensorAlgebras : Type (u + 1) :=
  ∀ (T : Scheme.{u}) (L : T.Modules),
    SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥T) L

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})

/-! ### Generation in degree one -/

/-- The graded algebra is generated in degree one: over every affine open of the base, the
degree-one part generates the ring of homogeneous sections as an algebra over the degree-zero
part. -/
public def IsGeneratedInDegreeOne : Prop :=
  ∀ (U : S.Opens), IsAffineOpen U →
    Algebra.adjoin (A.grading U 0) (A.grading U 1 : Set (A.sectionRing U)) = ⊤

/-! ### Pairs: an invertible sheaf and a degree-one-surjective graded map to its tensor
algebra -/

/-- A surjective graded homomorphism from the pulled-back algebra to the tensor algebra of an
invertible sheaf on a scheme over the base.

The component maps are written under the pullback–pushforward adjunction, as maps
`A n ⟶ f_* T(L) n`; `degreeOneSurjective` is the surjectivity of the adjoint transpose in degree
one, read through the identification of the degree-one piece of `T(L)` with `L`. -/
public structure F1Pair {T : Scheme.{u}} (f : T ⟶ S) where
  /-- The invertible sheaf on the test scheme. -/
  L : T.Modules
  /-- It is invertible. -/
  invertible : Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L
  /-- The graded map, adjoint form: a map out of each homogeneous piece of the algebra on the
  base, into the direct image of the corresponding piece of the tensor algebra. -/
  ψ (n : ℤ) : A.piece n ⟶ (Scheme.Modules.pushforward f).obj ((TA T L).tensor.piece n)
  /-- The graded map is multiplicative on homogeneous local sections. -/
  map_mul (i j : ℤ) (U : S.Opens) (a : Γ(A.piece i, U)) (b : Γ(A.piece j, U)) :
    (ψ (i + j)).val.app (op U) ((A.mul i j).app U a b) =
      ((TA T L).tensor.mul i j).app (op (f ⁻¹ᵁ U)) ((ψ i).val.app (op U) a)
        ((ψ j).val.app (op U) b)
  /-- The graded map is unital. -/
  map_one (U : S.Opens) :
    (ψ 0).val.app (op U) (A.one U) = (TA T L).tensor.one.eval (op (f ⁻¹ᵁ U))
  /-- The adjoint transpose is surjective in degree one. -/
  degreeOneSurjective : Epi
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (ψ 1) ≫
      ((TA T L).tensorPieceIso 1).hom ≫
      (eqToHom (by rfl : SheafOfModules.tensorPower (Opens.grothendieckTopology ↥T) L 1 = L)))

/-! ### Strict isomorphism of pairs -/

/-- Strict isomorphism of pairs: an isomorphism of the invertible sheaves together with an
isomorphism of their tensor algebras that is unital, extends the isomorphism of the sheaves on
the degree-one generators, and carries one graded map to the other. -/
public def StrictlyEquivalent {T : Scheme.{u}} {f : T ⟶ S} (P Q : F1Pair A TA f) : Prop :=
  ∃ (β : P.L ≅ Q.L) (γ : (TA T P.L).tensor ≅ (TA T Q.L).tensor),
    ((TA T P.L).tensorGenerator ≫ γ.hom.app 1 = β.hom ≫ (TA T Q.L).tensorGenerator) ∧
    (SheafOfModules.sectionsMap (γ.hom.app 0) (TA T P.L).tensor.one =
      (TA T Q.L).tensor.one) ∧
    (∀ n, P.ψ n ≫ (Scheme.Modules.pushforward f).map (γ.hom.app n) = Q.ψ n)

/-- The strict isomorphism classes of invertible degree-one quotients of the graded algebra. -/
public abbrev F1 {T : Scheme.{u}} (f : T ⟶ S) : Type _ :=
  Quot (Relation.EqvGen.setoid (StrictlyEquivalent A TA (f := f)))

/-- **Tag 01O4.** Strict isomorphism of invertible degree-one quotients is an equivalence
relation.

Reflexivity takes both isomorphisms to be the identity. Symmetry and transitivity take the
inverse and the composite; the degreewise components of those are the components of
`gradedAlgebraIsoApp`, which is what lets the three clauses be transported without rewriting
inside a morphism of sheaves of modules. -/
public theorem strictlyEquivalent_equivalence {T : Scheme.{u}} {f : T ⟶ S} :
    Equivalence (StrictlyEquivalent A TA (f := f)) where
  refl P :=
    ⟨Iso.refl _, Iso.refl _, Eq.trans (Category.comp_id _) (Category.id_comp _).symm, rfl,
      fun n => Eq.trans
        (congrArg (P.ψ n ≫ ·) ((Scheme.Modules.pushforward f).map_id _)) (Category.comp_id _)⟩
  symm := by
    rintro P Q ⟨β, γ, hgen, hone, hψ⟩
    refine ⟨β.symm, γ.symm, ?_, ?_, fun n => ?_⟩
    · refine (Iso.comp_inv_eq (gradedAlgebraIsoApp γ 1)).mpr (Eq.symm ?_)
      exact Eq.trans (Category.assoc _ _ _)
        (Eq.trans (congrArg (β.inv ≫ ·) hgen) (β.inv_hom_id_assoc _))
    · have h1 : SheafOfModules.sectionsMap (γ.inv.app 0)
          (SheafOfModules.sectionsMap (γ.hom.app 0) (TA T P.L).tensor.one) =
            (TA T P.L).tensor.one :=
        congrArg (fun h : (TA T P.L).tensor.piece 0 ⟶ (TA T P.L).tensor.piece 0 =>
          SheafOfModules.sectionsMap h (TA T P.L).tensor.one)
          (gradedAlgebraIsoApp γ 0).hom_inv_id
      exact Eq.trans (congrArg (SheafOfModules.sectionsMap (γ.inv.app 0)) hone).symm h1
    · refine (Iso.comp_inv_eq ((Scheme.Modules.pushforward f).mapIso
        (gradedAlgebraIsoApp γ n))).mpr ?_
      exact (hψ n).symm
  trans := by
    rintro P Q R ⟨β₁, γ₁, hgen₁, hone₁, hψ₁⟩ ⟨β₂, γ₂, hgen₂, hone₂, hψ₂⟩
    refine ⟨β₁ ≪≫ β₂, γ₁ ≪≫ γ₂, ?_, ?_, fun n => ?_⟩
    · refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (· ≫ γ₂.hom.app 1) hgen₁) ?_
      exact Eq.trans (Category.assoc _ _ _) (congrArg (β₁.hom ≫ ·) hgen₂)
    · exact Eq.trans (congrArg (SheafOfModules.sectionsMap (γ₂.hom.app 0)) hone₁) hone₂
    · refine Eq.trans (congrArg (P.ψ n ≫ ·)
        ((Scheme.Modules.pushforward f).map_comp (γ₁.hom.app n) (γ₂.hom.app n))) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      exact Eq.trans (congrArg (· ≫ (Scheme.Modules.pushforward f).map (γ₂.hom.app n)) (hψ₁ n))
        (hψ₂ n)

/-- **Tag 01O4.** Two pairs have the same strict isomorphism class exactly when they are
strictly isomorphic.

The class is taken in the quotient by the equivalence relation *generated* by strict
isomorphism, so on the face of it the two pairs are only joined by a chain; this says the chain
can be contracted, which is `Relation.Equivalence.eqvGen_iff` for
`strictlyEquivalent_equivalence`. -/
public theorem quot_mk_eq_iff_strictlyEquivalent {T : Scheme.{u}} {f : T ⟶ S}
    (P Q : F1Pair A TA f) :
    Quot.mk (Relation.EqvGen.setoid (StrictlyEquivalent A TA (f := f))) P =
        Quot.mk (Relation.EqvGen.setoid (StrictlyEquivalent A TA (f := f))) Q ↔
      StrictlyEquivalent A TA P Q := by
  refine ⟨fun h => ?_, fun h => Quot.sound (Relation.EqvGen.rel _ _ h)⟩
  exact (strictlyEquivalent_equivalence A TA).eqvGen_iff.mp (Quotient.exact h)

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
