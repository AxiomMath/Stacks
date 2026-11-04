module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.DescentData
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackAssoc

/-!
# The canonical comparison of two inverse images of a module

Let `A` be an algebraic space over `S`, let `M` be an `𝒪_A`-module and let `a : P ⟶ Q` and
`b : P ⟶ R` be two morphisms out of one algebraic space whose composites `a ≫ fi` and `b ≫ fj`
to `A` agree.  The two iterated inverse images `a^*fi^*M` and `b^*fj^*M` are then canonically
isomorphic, both being identified with the inverse image of `M` along the common composite.

This comparison is the pairwise isomorphism of the canonical descent datum of Stacks 04W5: at
the two projections of a pairwise fibre product `Y i ×_X Y j` it is the transition isomorphism
of the descent datum of a module on `X` relative to a family `(f i : Y i ⟶ X)`.  Its
compatibility with a further inverse image is what makes the cocycle condition of
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum` hold for that datum, and that
compatibility is the associativity coherence of the comparison of inverse images of
Stacks 03LU.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison` is the comparison.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_eq` writes it out through
  the comparisons of iterated inverse images of Stacks 03LU.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_mapIso_compIso` solves the
  associativity coherence of Stacks 03LU for the inverse image of one comparison, which is the
  form in which the canonical comparison consumes it.

## Implementation notes

The associativity coherence of the comparison `g^* ∘ f^* ≅ (f ≫ g)^*` of inverse images is not
available in this development; it is isolated as
`AlgebraicGeometry.Space.ModulePullbackCompIsoAssoc` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackAssoc.lean` and carried here as a
hypothesis, in the shape that file uses.

Associativity of composition in `AlgebraicGeometry.AlgebraicSpaces` holds by definitional
unfolding, so no transport along `CategoryTheory.Category.assoc` appears below.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The canonical comparison of the two inverse images of a module `M` on `A` along two
morphisms `a : P ⟶ Q` and `b : P ⟶ R` out of one space whose composites to `A` agree: the two
iterated inverse images are both identified with the inverse image along the common
composite. -/
def canonicalComparison {A P Q R : AlgebraicSpaces B S hS} (a : P ⟶ Q) (b : P ⟶ R)
    (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    (modulePullback B S hS a).obj ((modulePullback B S hS fi).obj M) ≅
      (modulePullback B S hS b).obj ((modulePullback B S hS fj).obj M) :=
  (pullbackComparison B S hS a fi (a ≫ fi) rfl M).symm ≪≫
    eqToIso (congrArg (fun q : P ⟶ A => (modulePullback B S hS q).obj M) h) ≪≫
    pullbackComparison B S hS b fj (b ≫ fj) rfl M

/-- At the composite itself, the comparison of an inverse image with an iterated inverse image
is the comparison of Stacks 03LU. -/
theorem pullbackComparison_rfl {A P T : AlgebraicSpaces B S hS} (g : T ⟶ P) (p : P ⟶ A)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    pullbackComparison B S hS g p (g ≫ p) rfl M =
      ((modulePullbackCompIso B S hS g p).app M).symm := by
  apply Iso.ext
  simp only [pullbackComparison, Iso.trans_hom, Iso.symm_hom, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Iso.app_inv]

/-- The canonical comparison, written out through the comparisons of iterated inverse images of
Stacks 03LU. -/
theorem canonicalComparison_eq {A P Q R : AlgebraicSpaces B S hS} (a : P ⟶ Q) (b : P ⟶ R)
    (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    canonicalComparison a b fi fj h M =
      (modulePullbackCompIso B S hS a fi).app M ≪≫
        eqToIso (congrArg (fun q : P ⟶ A => (modulePullback B S hS q).obj M) h) ≪≫
        ((modulePullbackCompIso B S hS b fj).app M).symm := by
  rw [canonicalComparison, pullbackComparison_rfl, pullbackComparison_rfl, Iso.symm_symm_eq]

/-- Transporting the inverse image of a module along an equality of morphisms commutes with the
comparison of iterated inverse images. -/
theorem modulePullbackCompIso_eqToIso {A P T : AlgebraicSpaces B S hS} (g : T ⟶ P)
    {p q : P ⟶ A} (h : p = q) (M : Modules.{u, u} B S hS A.1 A.2) :
    ((modulePullbackCompIso B S hS g p).app M).symm ≪≫
        (modulePullback B S hS g).mapIso
          (eqToIso (congrArg (fun r : P ⟶ A => (modulePullback B S hS r).obj M) h)) ≪≫
        (modulePullbackCompIso B S hS g q).app M =
      eqToIso (congrArg (fun r : P ⟶ A => (modulePullback B S hS (g ≫ r)).obj M) h) := by
  cases h
  apply Iso.ext
  simp

/-- The inverse image along `v` of the comparison of iterated inverse images along `a` and `fi`,
read through the comparisons for `v`.  This is the associativity coherence of Stacks 03LU,
solved for the inverse image of one comparison. -/
theorem modulePullback_mapIso_compIso (hassoc : ModulePullbackCompIsoAssoc B S hS)
    {A P Q T : AlgebraicSpaces B S hS} (v : T ⟶ P) (a : P ⟶ Q) (fi : Q ⟶ A)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    (modulePullback B S hS v).mapIso ((modulePullbackCompIso B S hS a fi).app M) =
      (modulePullbackCompIso B S hS v a).app ((modulePullback B S hS fi).obj M) ≪≫
        (modulePullbackCompIso B S hS (v ≫ a) fi).app M ≪≫
        ((modulePullbackCompIso B S hS v (a ≫ fi)).app M).symm := by
  apply Iso.ext
  simp only [Functor.mapIso_hom, Iso.app_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_inv]
  rw [← Category.assoc, ← hassoc.hom_app v a fi M]
  simp

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
