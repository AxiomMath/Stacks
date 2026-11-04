module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.SubcanonicalYoneda
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.FiniteEtaleCovers
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# Finite étale covers as finite locally constant sheaves of sets

Let `B` be a big étale site and `X` an object of `B`. Sending an object of the small étale site
of `X` to the sheaf of sets it represents takes the *finite* objects — those whose structure
morphism is finite, equivalently the finite étale covers of `X` — to finite locally constant
sheaves, and does so fully faithfully.

Composing with the identification of the finite objects of the small étale site with the
category `FÉt_X` of finite étale covers gives a fully faithful embedding of `FÉt_X` into the
finite locally constant sheaves of sets.

## Main definitions

* `AlgebraicGeometry.finiteSmallEtaleToFiniteLocallyConstant`: the functor from the finite
  objects of the small étale site of `X` to the finite locally constant sheaves of sets.
* `AlgebraicGeometry.finiteEtaleToFiniteLocallyConstant`: the same functor read on `FÉt_X`.

## Main results

* `AlgebraicGeometry.finiteSmallEtaleToFiniteLocallyConstantFullyFaithful` and
  `AlgebraicGeometry.finiteEtaleToFiniteLocallyConstantFullyFaithful`: both functors are fully
  faithful.

## References

* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- The finite locally constant sheaves of sets on the small étale site of `X`. -/
abbrev FiniteLocallyConstantSheaf :=
  ObjectProperty.FullSubcategory
    (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)) ↦
      IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2) F)

/-- The functor taking a finite object of the small étale site of `X` to the finite locally
constant sheaf of sets it represents. -/
def finiteSmallEtaleToFiniteLocallyConstant :
    (finiteSmallEtaleObjects B X).FullSubcategory ⥤ FiniteLocallyConstantSheaf B X where
  obj U := ⟨(Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.2)).obj U.1,
    Stacks.EtaleCohomology.isFiniteLocallyConstant_of_finiteEtaleRepresentable B X _
      ⟨U.1, U.2, ⟨Iso.refl _⟩⟩⟩
  map f := ObjectProperty.homMk
    ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.2)).map f.1)
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

/-- The functor `AlgebraicGeometry.finiteSmallEtaleToFiniteLocallyConstant` is fully
faithful. -/
@[sga "4 VII 2.1" "special case"]
def finiteSmallEtaleToFiniteLocallyConstantFullyFaithful :
    (finiteSmallEtaleToFiniteLocallyConstant B X).FullyFaithful := by
  set J := SmallEtale.topology B X.1 X.2
  let F := finiteSmallEtaleToFiniteLocallyConstant B X
  let G := (ObjectProperty.ι (fun F : Sheaf J (Type (u + 1)) ↦ IsFiniteLocallyConstant J F))
  have hComp : F ⋙ G ≅ (finiteSmallEtaleObjects B X).ι ⋙ Sheaf.sheafifiedYoneda J :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by
      simp [F, G, J, finiteSmallEtaleToFiniteLocallyConstant]
  exact Functor.FullyFaithful.ofCompFaithful (F := F) (G := G)
    ((((finiteSmallEtaleObjects B X).fullyFaithfulι).comp
      (Sheaf.fullyFaithfulSheafifiedYoneda J)).ofIso hComp.symm)

/-- The functor taking a finite étale cover of `X` to the finite locally constant sheaf of sets
it represents on the small étale site of `X`. -/
def finiteEtaleToFiniteLocallyConstant :
    FiniteEtaleOver X.1 ⥤ FiniteLocallyConstantSheaf B X :=
  (finiteEtaleSiteEquivalence B X).inverse ⋙ finiteSmallEtaleToFiniteLocallyConstant B X

/-- The functor `AlgebraicGeometry.finiteEtaleToFiniteLocallyConstant` from finite étale covers
to finite locally constant sheaves of sets is fully faithful. -/
def finiteEtaleToFiniteLocallyConstantFullyFaithful :
    (finiteEtaleToFiniteLocallyConstant B X).FullyFaithful :=
  ((finiteEtaleSiteEquivalence B X).symm.fullyFaithfulFunctor).comp
    (finiteSmallEtaleToFiniteLocallyConstantFullyFaithful B X)

end AlgebraicGeometry
