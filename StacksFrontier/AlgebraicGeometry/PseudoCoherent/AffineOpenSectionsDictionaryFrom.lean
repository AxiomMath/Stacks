module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineOpenSectionsDictionary

/-!
# Stacks 08E7 at an affine open in a fixed degree

Let `X` be a scheme, let `E` be an object of the derived category of `𝒪_X`-modules whose
cohomology sheaves are quasi-coherent, let `U` be an affine open of `X` and let `m` be an integer.
Then the restriction `E|_U` is `m`-pseudo-coherent on the ringed space `U` exactly when the
complex `RΓ(U, E)` of `Γ(X, U)`-modules is `m`-pseudo-coherent.

This is the fixed-degree companion of
`AlgebraicGeometry.isPseudoCoherent_restrictFunctor_iff_derivedSectionsUnbounded`
(`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineOpenSectionsDictionary.lean`), and the
fixed-degree form is the one the étale-chart localization of Stacks 0DII needs: the locality
criterion it is assembled over,
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general`, exists in a fixed degree
only, so every link of that chain has to be available degree by degree.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedTilde_iff`: Stacks 08E7 at an object
  of `D(R)` in a fixed degree.
* `AlgebraicGeometry.isPseudoCoherentFrom_pushforwardTilde_iff`: the same across an isomorphism
  with a spectrum.
* `AlgebraicGeometry.isPseudoCoherentFrom_restrictFunctor_iff_derivedSectionsUnbounded`: the
  statement of the header.

## How it is proved

Each of the three is the all-degrees statement of `AffineOpenSectionsDictionary.lean` with its
inputs replaced by their fixed-degree forms, all of which are available:
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_tilde_iff` (Stacks 08E7 in a fixed degree, at
a cochain complex), `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_isIso_iff`
(Stacks 09VA at an isomorphism in a fixed degree),
`AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom.of_iso` and
`StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso`.

The presentation of Stacks 06Z0 at an affine open,
`AlgebraicGeometry.affineDerivedSectionsPresentation`, carries no degree: it produces an object
`K` of `D(Γ(X, U))` together with isomorphisms `E|_U ≅ (isoSpec⁻¹)_*(K^~)` and `K ≅ RΓ(U, E)`, and
those serve in every degree at once.  So the degree enters only through the two `iff`s it is
composed with, and the split of the middle two steps into their own declaration is kept for the
reason recorded in the implementation notes of `AffineOpenSectionsDictionary.lean`: taken together
with the presentation they exceed the heartbeat ceiling.

`AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom.of_iso` is spelled in full with its ringed
space passed by name, for the two reasons recorded there as well — the predicate is an `abbrev`,
so resolving the projection against a hypothesis of that type sends the elaborator through the
unfolded existential, and leaving the ringed space implicit asks it to invert a projection on
`U.toScheme`, which does not terminate inside the ceiling.

No `stacks` tag is placed, for the reason recorded in `AffineOpenSectionsDictionary.lean`: the
statement is Stacks 08E7 transported along Stacks 06Z0 and Stacks 09VA, and the bare attributes
for all three sit on their own statements.

## References

* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 09VA](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- A predicate on a category stable under isomorphism holds for one object iff for the other. -/
private theorem iff_of_iso_of_forall {C : Type*} [Category C] {P : C → Prop}
    (hP : ∀ {a b : C}, P a → (a ≅ b) → P b) {a b : C} (e : a ≅ b) : P a ↔ P b :=
  ⟨fun h => hP h e, fun h => hP h e.symm⟩

namespace RingedSpace

/-- **Stacks 08E7 at an object of `D(R)`, in a fixed degree.**  An object of `D(R)` is
`m`-pseudo-coherent exactly when its derived sheafification on `Spec R` is.

The fixed-degree companion of
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedTilde_iff`, proved the same way: a cochain
complex representing the object carries the statement to
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_tilde_iff`, and both predicates depend only on
the isomorphism class of their object. -/
public theorem isPseudoCoherentFrom_derivedTilde_iff (R : CommRingCat.{u})
    (L : DerivedCategory (ModuleCat.{u} R)) (m : ℤ) :
    IsPseudoCoherentFrom (X := (Spec R).toRingedSpace)
        ((tilde.functor R).mapDerivedCategory.obj L) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom L m := by
  obtain ⟨M, eQ⟩ : Σ' M : CochainComplex (ModuleCat.{u} R) ℤ,
      DerivedCategory.Q.obj M ≅ L :=
    ⟨DerivedCategory.Q.objPreimage L, DerivedCategory.Q.objObjPreimageIso L⟩
  have eT : (tilde.functor R).mapDerivedCategory.obj L ≅
      DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
    (tilde.functor R).mapDerivedCategory.mapIso eQ.symm ≪≫
      (tilde.functor R).mapDerivedCategoryFactors.app M
  exact (iff_of_iso_of_forall
      (IsPseudoCoherentFrom.of_iso (X := (Spec R).toRingedSpace)) eT).trans
    ((isPseudoCoherentFrom_tilde_iff M m).trans
      (iff_of_iso_of_forall StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso eQ))

end RingedSpace

/-- **Stacks 08E7 across an isomorphism with a spectrum, in a fixed degree.**  Let
`k : Spec R ⟶ Y` be an isomorphism of schemes, let `K` be an object of `D(R)` and let `m` be an
integer.  Then `k_*(K^~)` is `m`-pseudo-coherent on the ringed space `Y` if and only if `K` is
`m`-pseudo-coherent.

Pushforward along an isomorphism neither creates nor destroys `m`-pseudo-coherence
(`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_isIso_iff`, Stacks 09VA at an
isomorphism), and on `Spec R` the condition on `K^~` is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedTilde_iff`. -/
public theorem isPseudoCoherentFrom_pushforwardTilde_iff {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (k : Spec R ⟶ Y) [IsIso k] (K : DerivedCategory (ModuleCat.{u} R)) (m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace)
        ((Scheme.Modules.pushforward k).mapDerivedCategory.obj
          ((tilde.functor R).mapDerivedCategory.obj K)) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom K m :=
  (Scheme.Modules.isPseudoCoherentFrom_pushforward_isIso_iff k
      ((tilde.functor R).mapDerivedCategory.obj K) m).trans
    (RingedSpace.isPseudoCoherentFrom_derivedTilde_iff R K m)

/-- **Stacks 08E7 at an affine open, in a fixed degree.**  Let `E` be an object of the derived
category of `𝒪_X`-modules all of whose cohomology sheaves are quasi-coherent, let `U` be an
affine open of `X` and let `m` be an integer.  Then `E|_U` is `m`-pseudo-coherent on the ringed
space `U` if and only if the complex `RΓ(U, E)` of `Γ(X, U)`-modules is `m`-pseudo-coherent.

The fixed-degree companion of
`AlgebraicGeometry.isPseudoCoherent_restrictFunctor_iff_derivedSectionsUnbounded`.  See "How it is
proved" in the module documentation; the only quasi-coherence used is the hypothesis `hE`, which
is what Stacks 06Z0 consumes, and the presentation it supplies carries no degree. -/
public theorem isPseudoCoherentFrom_restrictFunctor_iff_derivedSectionsUnbounded {X : Scheme.{u}}
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    {U : X.Opens} (hU : IsAffineOpen U) (m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := U.toScheme.toRingedSpace)
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((derivedSectionsUnbounded X U).obj E) m := by
  obtain ⟨K, ⟨hEK⟩, ⟨hKΓ⟩⟩ := affineDerivedSectionsPresentation E hE U hU
  exact (iff_of_iso_of_forall
      (RingedSpace.IsPseudoCoherentFrom.of_iso (X := U.toScheme.toRingedSpace)) hEK).trans
    ((isPseudoCoherentFrom_pushforwardTilde_iff hU.isoSpec.inv K m).trans
      (iff_of_iso_of_forall StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso hKΓ))

end AlgebraicGeometry

end
