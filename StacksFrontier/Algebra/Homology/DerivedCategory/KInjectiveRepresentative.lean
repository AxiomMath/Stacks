module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective

/-!
# Computing a right derived functor on a K-injective representative

Let `C` be an abelian category with an unbounded derived category. If K-injective resolutions
exist in `C`, then every object of `DerivedCategory C` is isomorphic to the image of a K-injective
cochain complex (Stacks 079P), and on such a complex a right derived functor of `F` is computed
by `F` itself, because the canonical comparison is invertible there (Stacks 070K).

Together these two facts reduce an identity between two right derived functors to an identity
between the underlying functors: choose a K-injective representative of the object, evaluate both
derived functors there, and compare the resulting cochain complexes.

## Main results

* `CategoryTheory.exists_isKInjective_representative`: every object of the unbounded derived
  category is `DerivedCategory.Q` of a K-injective complex. This is Stacks 079P.
* `CategoryTheory.rightDerivedObjIso`: the value of a right derived functor of `F` at a
  K-injective complex is `F` applied to that complex. This is Stacks 070K.

## Implementation notes

Both results take every typeclass fact they use as an **explicit argument** rather than as an
instance. This is load-bearing for their consumers: a category can carry two definitionally equal
but separately declared spellings — `AlgebraicGeometry.Scheme.Modules X` and
`CategoryTheory.SheafOfModules (structureSheafRing X.toSheafedSpace)` are one
such pair — and while *terms* cross that boundary by definitional unfolding, instance search does
not, so a goal mixing the two spellings is not provable by search. Passing the facts explicitly
lets the caller decide at which spelling each one is resolved.

For the same reason `hres`, the existence of K-injective resolutions, is an argument rather than a
consequence of `CategoryTheory.IsGrothendieckAbelian` deduced on the spot.

## References

* [The Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [The Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory

universe u

/-- Every object of the unbounded derived category is represented by a K-injective complex, as
soon as K-injective resolutions exist.

The hypothesis `hres` is Stacks 079P; it is taken as an argument rather than deduced from
`CategoryTheory.IsGrothendieckAbelian` so that the caller controls at which spelling of its
category the instances are resolved. -/
public lemma exists_isKInjective_representative
    {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasDerivedCategory.{u + 1} C]
    (hres : ∀ K : CochainComplex C ℤ,
      ∃ (J : CochainComplex C ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (E : DerivedCategory C) :
    ∃ I : CochainComplex C ℤ, I.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj I ≅ E) := by
  obtain ⟨I, i, hI, hi⟩ := hres (DerivedCategory.Q.objPreimage E)
  have := hi
  exact ⟨I, hI, ⟨(asIso (DerivedCategory.Q.map i)).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso E⟩⟩

/-- A right derived functor of `F` is computed on a K-injective complex by `F` itself: the
canonical comparison `α` is invertible there, which is Stacks 070K.

Every typeclass fact is an explicit argument, so that the lemma can be applied at a category with
two definitionally equal spellings without instance search having to choose between them. -/
public def rightDerivedObjIso
    {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasDerivedCategory.{u + 1} C]
    {A : Type (u + 1)} [Category.{u} A] [Abelian A] [HasDerivedCategory.{u + 1} A]
    (hres : ∀ K : CochainComplex C ℤ,
      ∃ (J : CochainComplex C ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (F : C ⥤ A) (hF : F.Additive)
    (RF : DerivedCategory C ⥤ DerivedCategory A)
    (α : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (.up ℤ)))
    (I : CochainComplex C ℤ) (hI : I.IsKInjective) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      RF.obj (DerivedCategory.Q.obj I) := by
  have := hF
  have := hRF
  have := hI
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) hres).2
    DerivedCategory.Qh RF α I inferInstance
  exact (DerivedCategory.quotientCompQhIso A).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).symm.app I) ≪≫
    asIso (α.app ((HomotopyCategory.quotient C (.up ℤ)).obj I)) ≪≫
    RF.mapIso ((DerivedCategory.quotientCompQhIso C).app I)

end CategoryTheory

end
