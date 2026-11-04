module

public import Mathlib.Algebra.Module.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Flatness.EssentialFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Flat.FlatLocalExtension

/-!
# Finite presentation of a flat stalk

Let `f : X ⟶ S` be locally of finite presentation and let `F` be a quasi-coherent module of
finite type on `X`. If `F` is flat over `S` at a point `x`, then the stalk `F_x` is a finitely
presented module over the local ring `O_{X,x}`.

The scheme-theoretic statement reduces to one about local rings. The stalk `F_x` is a finite
`O_{X,x}`-module because `F` is of finite type (`SheafOfModules.finite_stalk`), the stalk map
`O_{S,s} → O_{X,x}` is a local homomorphism essentially of finite presentation
(`AlgebraicGeometry.LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap`), and
flatness over the base at `x` is by definition flatness of `F_x` over `O_{S,s}` along that map.
What is left is pure commutative algebra, and it is recorded here as the hypothesis
`Stacks.Flatness.ExistsFlatLocalExtensionFinitePresentation`: the content of the étale
localization proposition for flat finite type modules. That hypothesis is logically equivalent to
the local-algebra form of Tag 05I7 itself, since one may take the extension to be the local ring,
so it is not a weakening; it is discharged below from
`Stacks.Flatness.ExistsSpreadOutFinitePresentation`, the local-algebra form of Tag 05I5, which is
strictly stronger because it asks for the finite presentation to hold over an algebra that is
again of finite presentation over a local base.

## Main definitions

* `Stacks.Flatness.ExistsFlatLocalExtensionFinitePresentation` is the local-algebra obligation
  that remains: a finite module over a local ring, flat over a local base along a local
  homomorphism essentially of finite presentation, becomes finitely presented after base change
  to some flat local extension of that local ring.

## Main results

* `Stacks.Flatness.finitePresentation_of_existsFlatLocalExtension` descends finite presentation
  from the flat local extension back to the local ring itself.
* `AlgebraicGeometry.finitePresentation_stalk_of_isFlatOverAt` is the geometric statement: the
  stalk of a finite type quasi-coherent module which is flat over the base at a point is a
  finitely presented module over the local ring at that point.
* `Stacks.Flatness.existsFlatLocalExtensionFinitePresentation_of_existsSpreadOut` discharges the
  obligation from `Stacks.Flatness.ExistsSpreadOutFinitePresentation`, the local-algebra content
  of Stacks 05I5, and
  `AlgebraicGeometry.finitePresentation_stalk_of_existsSpreadOut` is the resulting form of the
  geometric statement, whose only hypothesis is that statement of Stacks 05I5.

## Implementation notes

The obligation is stated with the extension `T'` carrying an `Algebra T T'` structure and with
the base change spelled as the tensor product `T' ⊗[T] M`, which is the shape consumed by
`Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat` through
`TensorProduct.isBaseChange`. A flat local homomorphism of local rings is faithfully flat, so no
further hypothesis on `T'` is needed for the descent.

Flatness of the module over the base is spelled exactly as `AlgebraicGeometry.IsFlatOverAt`,
i.e. with the `O_{S,s}`-action on the stalk obtained from its `O_{X,x}`-action by
`Module.compHom` along the stalk map.

## References

* [Stacks Project, Tag 05I7](https://stacks.math.columbia.edu/tag/05I7)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
* [Stacks Project, Tag 03C4](https://stacks.math.columbia.edu/tag/03C4)
* [Stacks Project, Tag 00HR](https://stacks.math.columbia.edu/tag/00HR)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.Flatness

/-- The local-algebra content of the étale localization proposition for flat finite type
modules. Let `φ : R →+* T` be a local homomorphism of local rings which is essentially of finite
presentation and let `M` be a finite `T`-module which is flat over `R` along `φ`. The assertion
is that there is a flat local extension `T → T'` of local rings over which `M` becomes a
finitely presented module. -/
def ExistsFlatLocalExtensionFinitePresentation : Prop :=
  ∀ (R T : Type u) [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]
    (φ : R →+* T) [IsLocalHom φ], φ.EssentiallyOfFinitePresentation →
      ∀ (M : Type u) [AddCommGroup M] [Module T M] [Module.Finite T M],
        (letI := Module.compHom M φ; Module.Flat R M) →
        ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T'),
          IsLocalRing T' ∧ IsLocalHom (algebraMap T T') ∧ Module.Flat T T' ∧
            Module.FinitePresentation T' (TensorProduct T T' M)

/-- Granting `ExistsFlatLocalExtensionFinitePresentation`, a finite module over a local ring
which is flat over a local base along a local homomorphism essentially of finite presentation is
finitely presented. A flat local homomorphism of local rings is faithfully flat, so finite
presentation descends from the extension provided by the hypothesis. -/
theorem finitePresentation_of_existsFlatLocalExtension
    (halg : ExistsFlatLocalExtensionFinitePresentation.{u})
    (R T : Type u) [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]
    (φ : R →+* T) [IsLocalHom φ] (hφ : φ.EssentiallyOfFinitePresentation)
    (M : Type u) [AddCommGroup M] [Module T M] [Module.Finite T M]
    (hM : letI := Module.compHom M φ; Module.Flat R M) :
    Module.FinitePresentation T M := by
  obtain ⟨T', _, _, _, _, _, _⟩ := halg R T φ hφ M hM
  have : Module.FaithfullyFlat T T' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat
    (TensorProduct.mk T T' M 1) (TensorProduct.isBaseChange T M T')

/-- The local-algebra obligation `ExistsFlatLocalExtensionFinitePresentation` left open by
`AlgebraicGeometry.finitePresentation_stalk_of_isFlatOverAt` follows from
`ExistsSpreadOutFinitePresentation`, the local-algebra form of Stacks 05I5.

This is the reduction proved in `StacksFrontier.RingTheory.Flat.FlatLocalExtension`: the target of
an essentially-of-finite-presentation local homomorphism is a localization at a prime of an
algebra of finite presentation, a finite module over it is the localization of a finitely
generated submodule, and a spreading out of that submodule which is finitely presented over a
flat extension of the algebra produces the required flat local extension as a localization of
that extension. -/
theorem existsFlatLocalExtensionFinitePresentation_of_existsSpreadOut
    (H : ExistsSpreadOutFinitePresentation.{u}) :
    ExistsFlatLocalExtensionFinitePresentation.{u} :=
  exists_flatLocalExtension_finitePresentation_of_existsSpreadOut H

end Stacks.Flatness

namespace AlgebraicGeometry

/-- A quasi-coherent module of finite type which is flat over the base at a point has a finitely
presented stalk at that point, granting the local-algebra obligation
`Stacks.Flatness.ExistsFlatLocalExtensionFinitePresentation`. -/
theorem finitePresentation_stalk_of_isFlatOverAt
    (halg : Stacks.Flatness.ExistsFlatLocalExtensionFinitePresentation.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    Module.FinitePresentation (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) := by
  let : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module.Finite (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    SheafOfModules.finite_stalk X.sheaf F x
  exact Stacks.Flatness.finitePresentation_of_existsFlatLocalExtension halg _ _
    (f.stalkMap x).hom
    (LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap f x) _ hflat

/-- **Stacks Project, Tag 05I7, granted the local-algebra form of Tag 05I5.** A quasi-coherent
module of finite type which is flat over the base at a point has a finitely presented stalk at
that point.

This is `AlgebraicGeometry.finitePresentation_stalk_of_isFlatOverAt` with its obligation
discharged by `Stacks.Flatness.existsFlatLocalExtensionFinitePresentation_of_existsSpreadOut`, so
that the only hypothesis left is the spreading out of Stacks 05I5. -/
theorem finitePresentation_stalk_of_existsSpreadOut
    (H : Stacks.Flatness.ExistsSpreadOutFinitePresentation.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    Module.FinitePresentation (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
  finitePresentation_stalk_of_isFlatOverAt
    (Stacks.Flatness.existsFlatLocalExtensionFinitePresentation_of_existsSpreadOut H) f F x hflat

end AlgebraicGeometry

end
