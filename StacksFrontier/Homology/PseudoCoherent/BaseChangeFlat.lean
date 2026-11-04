module

public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings

/-!
# Derived extension of scalars of a bounded above complex of flat modules

Let `φ : A → A'` be a homomorphism of commutative rings and let `P` be a cochain complex of
`A`-modules which is bounded above and flat in every degree. Then the canonical comparison from
the *derived* extension of scalars `P ⊗^L_A A'` to the *termwise* one `P ⊗_A A'` is an
isomorphism: a bounded above complex of flat modules is K-flat
([Stacks, Tag 064K], `CochainComplex.KFlat.kFlat_of_flat`), and the counit of any total left
derived functor of termwise extension of scalars is invertible at a K-flat complex.

This is the step the source of [Stacks, Tag 07VK] invokes as "by the definition of derived tensor
products, see More on Algebra, Section 06XY": having a bounded above termwise flat representative
is exactly what lets the ordinary extension of scalars of that representative be read as the
derived extension of scalars of the object it represents.

## Main results

* `StacksDraft.PseudoCoherence.isIso_extendScalarsDerivedCounit_app_of_flat`: the comparison map
  `extendScalarsDerivedCounit` is invertible at a bounded above termwise flat complex.
* `StacksDraft.PseudoCoherence.extendScalarsDerivedIsoOfFlat`: the resulting isomorphism
  `P ⊗^L_A A' ≅ P ⊗_A A'` in `D(A')`.

## Implementation notes

Everything runs under `CategoryTheory.HasDerivedCategory.standard`, which is the model
`StacksFrontier/Homology/PseudoCoherent/BaseChange.lean` fixes for `extendScalarsDerived` and its
counit.

`CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat` states its
comparison against `CochainComplex.extendScalarsLarge φ`, which is
`(ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)` with a different — but
definitionally equal, both fields being propositions — witness of additivity. Unification crosses
the two spellings on the `comparison` argument but then fails to find the
`Functor.IsLeftDerivedFunctor` instance at the crossed spelling, so that instance is supplied
positionally rather than by search.

`CochainComplex.KFlat` is two-universe, and the flatness hypothesis is an instance argument of
`CochainComplex.KFlat.kFlat_of_flat`; both are pinned at the ring's universe here, which is the
case every consumer in this library needs.

## References

* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 06XY](https://stacks.math.columbia.edu/tag/06XY)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace StacksDraft.PseudoCoherence

attribute [local instance] HasDerivedCategory.standard

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- **Derived extension of scalars agrees with termwise extension of scalars on a bounded above
complex of flat modules.** The comparison map is the counit `extendScalarsDerivedCounit` of the
total left derived functor, and it is invertible here because a bounded above complex of flat
modules is K-flat ([Stacks, Tag 064K]).

This is the [Stacks, Tag 06XY] step of the proof of [Stacks, Tag 07VK]: for such a complex the
ordinary extension of scalars *is* the derived one. -/
theorem isIso_extendScalarsDerivedCounit_app_of_flat
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (d : ℤ) [P.IsStrictlyLE d]
    [∀ n : ℤ, Module.Flat A (P.X n)] :
    IsIso ((extendScalarsDerivedCounit φ).app P) :=
  have hK : CochainComplex.KFlat.{u, u} P := CochainComplex.KFlat.kFlat_of_flat P d
  @CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat.{u, u, u}
    A A' _ _ φ _ _ (extendScalarsDerived φ) (extendScalarsDerivedCounit φ)
    (isLeftDerivedFunctor_extendScalarsDerivedCounit φ) P hK

/-- **`P ⊗^L_A A' ≅ P ⊗_A A'` for `P` bounded above and termwise flat**, through the canonical
comparison map. -/
def extendScalarsDerivedIsoOfFlat
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (d : ℤ) [P.IsStrictlyLE d]
    [∀ n : ℤ, Module.Flat A (P.X n)] :
    (extendScalarsDerived φ).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  have := isIso_extendScalarsDerivedCounit_app_of_flat φ P d
  asIso ((extendScalarsDerivedCounit φ).app P)

end StacksDraft.PseudoCoherence

end
