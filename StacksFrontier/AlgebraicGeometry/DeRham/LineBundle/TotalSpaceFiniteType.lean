module

public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraAffineSections
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.FiniteTypeDominating.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput

/-!
# The total space of a line bundle is locally of finite type over its base

The total space of a line bundle `L` on a scheme `X` is the relative spectrum of the algebra
sheaf `Stacks.LineBundle.Situation.algebraSheaf`, the ungraded realization of `Sym(L)`
sheafified in `CommRingCat`. This algebra sheaf is of finite type in the sense of
`Stacks.RelativeSpec.AlgebraSheaf.IsFiniteType`: the structural ring map
`Γ(X, U) ⟶ Γ(U, Sym(L))` is of finite type over every affine open `U`. Hence the structure
morphism `Stacks.LineBundle.Situation.totalSpaceToBase` is `AlgebraicGeometry.LocallyOfFiniteType`.

## Main definitions

* `Stacks.RelativeSpec.ungradedSectionsRingEquiv`: the sections of the `CommRingCat` ungraded
  realization over an affine open, as the direct sum of the sections of the homogeneous pieces.
* `Stacks.SymAlgSections.ungradedSymSectionsRingEquiv`: `Γ(V, Sym(ℰ))` is the symmetric algebra
  of `Γ(ℰ, V)` over `Γ(X, V)`, for the `CommRingCat` ungraded realization.

## Main results

* `Stacks.RelativeSpec.bijective_ungradedCommUnit_of_isAffineOpen`: the `CommRingCat`
  sheafification unit of the ungraded realization is bijective on the sections over an affine
  open.
* `Stacks.SymAlgSections.ungradedSymSectionsRingEquiv_algebraMap`: the identification carries
  `algebraMap` to the structural ring map.
* `Stacks.SymAlgSections.finiteType_ungradedApp` and
  `Stacks.LineBundle.Situation.isFiniteType_algebraSheaf`: the algebra sheaf of a line bundle is
  of finite type.
* `Stacks.LineBundle.Situation.locallyOfFiniteType_totalSpaceToBase`: the total space of a line
  bundle is locally of finite type over its base.

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01S9](https://stacks.math.columbia.edu/tag/01S9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open PresheafOfModules

universe u

namespace Stacks.RelativeSpec

variable (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
    HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))
  {V : X.Opens}

/-- **The `CommRingCat` sheafification unit of the ungraded realization is bijective on the
sections over an affine open**: over an affine open the sections of the ungraded algebra sheaf of
a sheaf of graded algebras are the direct sum of the sections of its homogeneous pieces. -/
theorem bijective_ungradedCommUnit_of_isAffineOpen (hV : IsAffineOpen V) :
    Function.Bijective (ungradedCommUnit X A hA V).hom :=
  (Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff (𝟙 X.ringCatSheaf.obj)
      (AlgebraSheaf.underlyingModule (ungradedAlgebraSheaf X A hA))
      (ungradedDirectSumHom X A hA)
      (Stacks.GradedAlgebra.isLocallyInjective_toPresheaf_map_directSumHom _ _ _ _
        (isLocallyInjective_ungradedRingUnit X A hA))
      (Stacks.GradedAlgebra.isLocallySurjective_toPresheaf_map_directSumHom _ _ _ _
        (isLocallySurjective_ungradedRingUnit X A hA))
      (op V)).1
    (Stacks.DirectSumSections.bijective_sheafifyUnit_directSum_app (fun n : ℤ => A.piece n) V
      (Stacks.SheafOfModules.isQuasiCompactObject_of_isCompact V hV.isCompact))

/-- The ring of sections of the `CommRingCat` ungraded algebra sheaf over an affine open is the
direct sum of the sections of the homogeneous pieces, via the sheafification unit. -/
def ungradedSectionsRingEquiv (hV : IsAffineOpen V) :
    A.toPresheafGradedAlgebra.Total (op V) ≃+*
      AlgebraSheaf.sections (ungradedAlgebraSheaf X A hA) V :=
  RingEquiv.ofBijective (ungradedCommUnit X A hA V).hom
    (bijective_ungradedCommUnit_of_isAffineOpen X A hA hV)

end Stacks.RelativeSpec

namespace Stacks.SymAlgSections

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] {V : X.Opens}
  (hV : IsAffineOpen V)

/-- The ungraded algebra sheaf of `Sym(ℰ)`, sheafified in `CommRingCat`. -/
abbrev ungradedSymAlgebraSheaf : Stacks.RelativeSpec.AlgebraSheaf X :=
  Stacks.RelativeSpec.ungradedAlgebraSheaf X (Scheme.Modules.symmetricAlgebra X E)
    (Scheme.Modules.symmetricAlgebra_mul_comm X E)

include hV in
/-- The graded decomposition of `algebraMap r` is carried to the structure map `r ↦ r • 1` of
`Sym(ℰ)` by the degreewise sheafification unit. -/
theorem symPowersRingEquiv_decompose_algebraMap (r : Γ(X, V)) :
    symPowersRingEquiv E hV (DirectSum.decomposeRingEquiv
        (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))
        (algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(E, V)) r)) =
      (symPresheafAlgebra E).structureMap (op V) r :=
  (Stacks.RelativeSpec.totalSectionsRingEquiv X (Scheme.Modules.symmetricAlgebra X E)
      (Scheme.Modules.symmetricAlgebra_mul_comm X E) hV).injective
    (symSectionsRingEquiv_algebraMap E hV r)

/-- Over an affine open `V`, the sections of the `CommRingCat` ungraded realization of `Sym(ℰ)`
are the symmetric algebra of `Γ(ℰ, V)` over `Γ(X, V)`. -/
def ungradedSymSectionsRingEquiv : SymmetricAlgebra Γ(X, V) Γ(E, V) ≃+*
    Stacks.RelativeSpec.AlgebraSheaf.sections (ungradedSymAlgebraSheaf E) V :=
  (DirectSum.decomposeRingEquiv
      (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))).trans
    ((symPowersRingEquiv E hV).trans
      (Stacks.RelativeSpec.ungradedSectionsRingEquiv X (Scheme.Modules.symmetricAlgebra X E)
        (Scheme.Modules.symmetricAlgebra_mul_comm X E) hV))

/-- The identification `Stacks.SymAlgSections.ungradedSymSectionsRingEquiv` carries `algebraMap`
to the structural ring map of the algebra sheaf. -/
theorem ungradedSymSectionsRingEquiv_algebraMap (r : Γ(X, V)) :
    ungradedSymSectionsRingEquiv E hV
        (algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(E, V)) r) =
      ((ungradedSymAlgebraSheaf E).hom.hom.app (op V)).hom r :=
  congrArg
    (Stacks.RelativeSpec.ungradedCommUnit X (Scheme.Modules.symmetricAlgebra X E)
      (Scheme.Modules.symmetricAlgebra_mul_comm X E) V).hom
    (symPowersRingEquiv_decompose_algebraMap E hV r)

include hV in
/-- For `ℰ` of finite presentation, the structural ring map of the `CommRingCat` ungraded
realization of `Sym(ℰ)` over an affine open is of finite type. -/
theorem finiteType_ungradedApp [E.IsFinitePresentation] :
    RingHom.FiniteType ((ungradedSymAlgebraSheaf E).hom.hom.app (op V)).hom := by
  have hmod : Module.FinitePresentation Γ(X, V) Γ(E, V) :=
    AlgebraicGeometry.finitePresentation_sections_on_affine E ⟨V, hV⟩
  have halg : RingHom.FiniteType (algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(E, V))) :=
    RingHom.finiteType_algebraMap.2 (Stacks.SymAlg.finiteType _ _)
  have h : (ungradedSymSectionsRingEquiv E hV).toRingHom.comp
      (algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(E, V))) =
        ((ungradedSymAlgebraSheaf E).hom.hom.app (op V)).hom :=
    RingHom.ext (ungradedSymSectionsRingEquiv_algebraMap E hV)
  exact h ▸ RingHom.finiteType_respectsIso.1 _ (ungradedSymSectionsRingEquiv E hV) halg

/-- The `CommRingCat` ungraded realization of `Sym(ℰ)` is an algebra sheaf of finite type for
`ℰ` quasi-coherent of finite presentation. -/
theorem isFiniteType_ungradedSymAlgebraSheaf [E.IsFinitePresentation] :
    Stacks.RelativeSpec.AlgebraSheaf.IsFiniteType (ungradedSymAlgebraSheaf E) :=
  fun _ hU => finiteType_ungradedApp E hU

end Stacks.SymAlgSections

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- The line bundle of a situation is of finite presentation. -/
instance isFinitePresentation_lineBundle : D.L.IsFinitePresentation :=
  Stacks.ModuleDescent.isFinitePresentation_of_isInvertible D.X D.L D.invertible

/-- The algebra sheaf of a line bundle is of finite type. -/
theorem Situation.isFiniteType_algebraSheaf :
    Stacks.RelativeSpec.AlgebraSheaf.IsFiniteType D.algebraSheaf :=
  Stacks.SymAlgSections.isFiniteType_ungradedSymAlgebraSheaf D.L

/-- The total space of a line bundle is locally of finite type over the scheme on which the line
bundle lives. -/
instance Situation.locallyOfFiniteType_totalSpaceToBase :
    LocallyOfFiniteType D.totalSpaceToBase :=
  Stacks.AlgebraicGeometry.FiniteTypeDominating.locallyOfFiniteType_relativeSpecOver
    D.algebraSheaf D.isFiniteType_algebraSheaf

end Stacks.LineBundle

end
