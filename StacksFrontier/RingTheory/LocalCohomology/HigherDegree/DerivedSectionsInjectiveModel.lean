module

public import StacksFrontier.Homology.DerivedCategory.RightDerivedInjectiveModel
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.DerivedSectionsOverBase

/-!
# An explicit complex of `A`-modules computing `RΓ(V, F)`

Let `A` be a commutative ring, let `f : V ⟶ Spec A` be a morphism of schemes and let `F` be a
sheaf of modules on `V`. The object `Stacks.LocalCohomology.derivedSectionsOverBase` of the
derived category of `A`-modules is the image of an explicit cochain complex of `A`-modules, namely
the termwise global sections of an injective resolution of `F`.

## Main results

* `Stacks.LocalCohomology.exists_nonempty_Q_obj_iso_derivedSectionsOverBase` — the injective
  resolution `J` of `F` and the isomorphism `Γ(V, J) ≅ RΓ(V, F)` in the derived category of
  `A`-modules.

## References

* [Stacks Project, Tag 0ECC](https://stacks.math.columbia.edu/tag/0ECC)
* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] {V : Scheme.{u}}

/-- **`RΓ(V, F)` is the global sections of an injective resolution of `F`.** There is a cochain
complex `J` of injective sheaves of modules on `V`, concentrated in degrees `≥ 0`, whose termwise
global sections with scalars restricted to `A` represent `RΓ(V, F)` in the derived category of
`A`-modules. -/
theorem exists_nonempty_Q_obj_iso_derivedSectionsOverBase (f : V ⟶ Spec (.of A))
    (F : SheafOfModules.{u} V.ringCatSheaf) :
    ∃ J : CochainComplex.Plus (InjectiveObject (SheafOfModules.{u} V.ringCatSheaf)),
      J.obj.IsStrictlyGE 0 ∧
      Nonempty (DerivedCategory.Q.obj
        (((sectionsOverBase.{u, u} A f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((InjectiveObject.ι (SheafOfModules.{u} V.ringCatSheaf)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J.obj)) ≅ derivedSectionsOverBase A f F) :=
  Stacks.InjectiveModel.exists_nonempty_Q_obj_iso_rightDerivedFunctorPlus
    (sectionsOverBase.{u, u} A f)
    ((DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} V.ringCatSheaf) 0).obj F) 0

end Stacks.LocalCohomology

end
