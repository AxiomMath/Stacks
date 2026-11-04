module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsCompGeneral
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Homology.RelativelyPerfect.ColimitHom

/-!
# The three composition isomorphisms for derived extension of scalars are one

Three isomorphisms `(- ⊗ᴸ_R S) ⋙ (- ⊗ᴸ_S T) ≅ - ⊗ᴸ_R T` are built independently in this
development:

* `StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIsoGeneral`, which
  `AlgebraicGeometry.derivedStalkExtensionCompIsoGeneral` is built from;
* `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp`, which carries the
  cocycle condition and the two unit laws and which
  `RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso` is built from;
* `PseudoCoherence.derivedExtensionScalarsComp`, which the descent statements of Stacks 0DHX are
  phrased with.

All three are obtained from the universal property of the total left derived functor on the
right, applied to the same comparison, so they agree.  This file records the agreement, so that a
chase begun with one of the three can be finished with the lemmas proved about another.

## Main results

* `StacksDraft.DerivedExtensionScalarsComp.extensionScalarsComplexCompIso_eq_comp_symm`: the
  degreewise ingredient of the three constructions is one isomorphism, up to direction.
* `StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso_eq_totalComp`: the
  first two agree.
* `PseudoCoherence.derivedExtensionScalarsComp_eq_totalComp` and
  `PseudoCoherence.derivedExtensionScalarsComp_eq_compIso`: the third agrees with the other two.

## Implementation notes

*Why the degreewise step is the whole content.*  The three constructions differ in exactly one
place: the comparison they factor is assembled from the two one-step comparisons and a
degreewise composition isomorphism, and
`StacksDraft.DerivedExtensionScalarsComp.extensionScalarsComplexCompIsoGeneral` is written as a
`CategoryTheory.Functor.mapHomologicalComplexCompIso` of the inverse of
`ModuleCat.extendScalarsComp` where
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexComp` is written as the inverse
of a `CategoryTheory.NatIso.mapHomologicalComplex` of `ModuleCat.extendScalarsComp` itself.
Those two are definitionally equal, so the comparisons are equal and uniqueness of maps into a
total left derived functor does the rest.

*Why the equalities are stated at the level of isomorphisms.*  A chase rewriting with an equation
between isomorphisms replaces the isomorphism wherever it occurs, including under `Iso.hom`,
`Iso.inv` and `CategoryTheory.NatTrans.app`; component-level equations would have to be stated
once per component shape.  The `Iso.hom` forms are kept as well, since the three canonical
natural transformations, and not only the isomorphisms, occur in the characterizing equations.

*Why the third construction carries no model argument.*
`PseudoCoherence.derivedExtensionScalarsComp` is defined with `HasDerivedCategory.standard` a
local instance, so its statement names that model; the comparisons with it are therefore stated
at the standard model, while the comparison of the first two is stated at an arbitrary one.

## References

* [The Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [The Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars

universe u v w

namespace StacksDraft.DerivedExtensionScalarsComp

section Degreewise

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [HasDerivedCategory.{w} (ModuleCat.{u} T)] (f : R →+* S) (g : S →+* T)

/-- **The degreewise composition isomorphisms agree.**  The forward map of
`extensionScalarsComplexCompIsoGeneral` is the inverse of `extensionOfScalarsComplexComp`: one is
`CategoryTheory.Functor.mapHomologicalComplexCompIso` of the inverse of
`ModuleCat.extendScalarsComp` and the other is the inverse of
`CategoryTheory.NatIso.mapHomologicalComplex` of `ModuleCat.extendScalarsComp`, and these are the
same map. -/
theorem extensionScalarsComplexCompIso_hom_eq_comp_inv :
    (extensionScalarsComplexCompIsoGeneral f g).hom =
      (extensionOfScalarsComplexComp.{u, u, w} f g).inv :=
  rfl

/-- **The degreewise composition isomorphisms agree**, as isomorphisms:
`extensionScalarsComplexCompIsoGeneral` is `extensionOfScalarsComplexComp` read backwards. -/
theorem extensionScalarsComplexCompIso_eq_comp_symm :
    extensionScalarsComplexCompIsoGeneral f g =
      (extensionOfScalarsComplexComp.{u, u, w} f g).symm :=
  Iso.ext (extensionScalarsComplexCompIso_hom_eq_comp_inv f g)

end Degreewise

section Derived

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
  [HasDerivedCategory.{w} (ModuleCat.{u} T)] (f : R →+* S) (g : S →+* T)

/-- **The canonical morphisms of the first two composition isomorphisms agree.**  Both factor the
same comparison through the comparison of the total derived extension of scalars along `g ∘ f`,
by `derivedExtensionScalarsCompIsoGeneral_hom_app_comp_comparison` and
`totalDerivedExtensionScalarsComp_comparison` together with
`extensionScalarsComplexCompIso_hom_eq_comp_inv`, and a map into a total left derived functor is
determined by the factorization it gives. -/
theorem derivedExtensionScalarsCompIso_hom_eq_totalComp_hom :
    (derivedExtensionScalarsCompIsoGeneral f g).hom =
      (totalDerivedExtensionScalarsComp.{u, u} f g).hom := by
  refine Functor.leftDerived_ext (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor
    (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _ _ _ ?_
  ext P
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [derivedExtensionScalarsCompIsoGeneral_hom_app_comp_comparison,
    ← totalDerivedExtensionScalarsComp_comparison,
    extensionScalarsComplexCompIso_hom_eq_comp_inv]

/-- **The first two composition isomorphisms agree.**  So the cocycle condition and the unit laws
proved for `totalDerivedExtensionScalarsComp` hold for `derivedExtensionScalarsCompIsoGeneral`, and
the characterizing equation proved for the latter holds for the former. -/
theorem derivedExtensionScalarsCompIso_eq_totalComp :
    derivedExtensionScalarsCompIsoGeneral f g = totalDerivedExtensionScalarsComp.{u, u} f g :=
  Iso.ext (derivedExtensionScalarsCompIso_hom_eq_totalComp_hom f g)

end Derived

end StacksDraft.DerivedExtensionScalarsComp

namespace PseudoCoherence

attribute [local instance] HasDerivedCategory.standard

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)

/-- **The canonical morphism of the third composition isomorphism is that of the second.**  The
comparison that `derivedExtensionScalarsCompHom` factors is the one
`totalDerivedExtensionScalarsComp` factors, so `derivedExtensionScalarsCompHom_eq` identifies the
two. -/
theorem derivedExtensionScalarsCompHom_eq_totalComp_hom :
    derivedExtensionScalarsCompHom.{u, v} f g =
      (totalDerivedExtensionScalarsComp.{u, v} f g).hom :=
  (derivedExtensionScalarsCompHom_eq.{u, v} f g _
    fun P => (totalDerivedExtensionScalarsComp_comparison.{u, v} f g P).symm).symm

/-- **The third composition isomorphism is the second.** -/
theorem derivedExtensionScalarsComp_eq_totalComp :
    derivedExtensionScalarsComp.{u, v} f g = totalDerivedExtensionScalarsComp.{u, v} f g :=
  Iso.ext (derivedExtensionScalarsCompHom_eq_totalComp_hom.{u, v} f g)

/-- **The third composition isomorphism is the first**, by way of the second. -/
theorem derivedExtensionScalarsComp_eq_compIso :
    derivedExtensionScalarsComp.{u, u} f g =
      StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIsoGeneral f g :=
  (derivedExtensionScalarsComp_eq_totalComp.{u, u} f g).trans
    (StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso_eq_totalComp
      f g).symm

end PseudoCoherence

end
