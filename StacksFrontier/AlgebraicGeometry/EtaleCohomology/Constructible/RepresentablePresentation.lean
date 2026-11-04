module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite coequalizer presentations of étale sheaves of sets

A sheaf of sets on the small étale site of a scheme has a *finite presentation by
quasi-compact quasi-separated representables* when it is a coequalizer of two maps between
finite coproducts of sheaves represented by étale objects whose underlying schemes are
quasi-compact and quasi-separated. On a quasi-compact and quasi-separated scheme these are
exactly the constructible sheaves of sets (Stacks Project, Tag 09Y9); this file records the
notion itself.

## Main definitions

* `AlgebraicGeometry.HasFiniteQCSRepresentableCoequalizerPresentation` — the presentation.

## Implementation notes

The sheaf represented by an object of the site is its sheafified Yoneda image
`CategoryTheory.Sheaf.sheafifiedYoneda`, which on the small étale site agrees with the
representable sheaf because that site is subcanonical. Quasi-compactness and
quasi-separatedness are properties of the underlying scheme of the étale object. The finite
coproducts are the ones supplied by `CategoryTheory.Sheaf.instHasFiniteColimits`, named
explicitly so that the definition does not depend on how instance resolution happens to
produce them.

## References

* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- `F` is a coequalizer of a pair of maps between finite coproducts of sheaves represented by
quasi-compact, quasi-separated objects of the small étale site of `X`. -/
public def HasFiniteQCSRepresentableCoequalizerPresentation
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) : Prop :=
  let J := SmallEtale.topology B X.1 X.property
  letI : HasFiniteColimits (Sheaf J (Type (u + 1))) :=
    CategoryTheory.Sheaf.instHasFiniteColimits
  ∃ (n m : ℕ) (U : Fin n → SmallEtale B X.1 X.property)
      (V : Fin m → SmallEtale B X.1 X.property),
    letI : HasColimitsOfShape (Discrete (Fin n)) (Sheaf J (Type (u + 1))) :=
      HasFiniteColimits.out _
    letI : HasColimitsOfShape (Discrete (Fin m)) (Sheaf J (Type (u + 1))) :=
      HasFiniteColimits.out _
    (∀ i, CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj (U i)) ∧
      QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj (U i))) ∧
    (∀ j, CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj (V j)) ∧
      QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj (V j))) ∧
      ∃ (f g : (∐ fun j ↦ (Sheaf.sheafifiedYoneda J).obj (V j)) ⟶
          (∐ fun i ↦ (Sheaf.sheafifiedYoneda J).obj (U i))),
        Nonempty (coequalizer f g ≅ F)

end AlgebraicGeometry

end
