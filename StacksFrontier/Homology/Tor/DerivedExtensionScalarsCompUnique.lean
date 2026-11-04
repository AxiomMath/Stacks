module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsComp
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp

/-!
# The two constructions of the composition isomorphism agree

The library builds the composition isomorphism of derived extension of scalars twice, from the
same universal property and with the same characterizing equation against the three comparisons
with degreewise extension of scalars:

* `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp`, whose equation is
  `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_comparison`;
* `StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso`, whose equation is
  `StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso_hom_app_comp_comparison`.

They are the same isomorphism.  This file says so, which is what a consumer holding one of them
and a lemma stated at the other needs; both are kept.

## Main results

* `StacksDraft.DerivedExtensionScalarsComp.totalDerivedExtensionScalarsComp_eq`: the two agree.

## Implementation notes

Both are maps into the total left derived functor of degreewise extension of scalars along the
composite, so `CategoryTheory.Functor.leftDerived_ext` reduces the equality to the two
characterizing equations, which differ only in how the degreewise merge is spelled: one quotes
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexComp` read backwards, the other
`StacksDraft.DerivedExtensionScalarsComp.extensionScalarsComplexCompIso`.  Both are
`DerivedCategory.Q` of `ModuleCat.extendScalarsComp` applied degreewise and read backwards, so
they agree degreewise.

## References

* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars

noncomputable section

namespace StacksDraft.DerivedExtensionScalarsComp

universe u

attribute [local instance] HasDerivedCategory.standard

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)

/-- The two spellings of the degreewise merge agree: both are `DerivedCategory.Q` of
`ModuleCat.extendScalarsComp` applied degreewise and read backwards. -/
theorem extensionScalarsComplexCompIso_hom_app
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extensionScalarsComplexCompIso f g).hom.app P =
      (extensionOfScalarsComplexComp.{u, u} f g).inv.app P := by
  refine congrArg DerivedCategory.Q.map ?_
  ext i : 1
  rfl

/-- **The two constructions of the composition isomorphism agree.**  Both satisfy the same
characterizing equation against the comparisons with degreewise extension of scalars, and a map
into a total left derived functor is determined by that equation. -/
theorem totalDerivedExtensionScalarsComp_eq :
    totalDerivedExtensionScalarsComp.{u, u} f g = derivedExtensionScalarsCompIso f g := by
  refine Iso.ext (Functor.leftDerived_ext _
    (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _ _ _ ?_)
  ext P
  dsimp only [Functor.whiskerLeft_app, Category.id_comp, NatTrans.comp_app]
  exact (totalDerivedExtensionScalarsComp_comparison.{u, u} f g P).symm.trans
    (Eq.trans (congrArg (fun t =>
      (totalDerivedExtensionScalars.{u, u, u} g).functor.map
            ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P) ≫
          (totalDerivedExtensionScalars.{u, u, u} g).comparison.app
              (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) ≫ t)
        (extensionScalarsComplexCompIso_hom_app f g P).symm)
      (derivedExtensionScalarsCompIso_hom_app_comp_comparison f g P).symm)

/-- `totalDerivedExtensionScalarsComp_eq` on the underlying morphisms: the form a chase holding
one spelling and a lemma stated at the other rewrites with. -/
theorem totalDerivedExtensionScalarsComp_hom_eq :
    (totalDerivedExtensionScalarsComp.{u, u} f g).hom =
      (derivedExtensionScalarsCompIso f g).hom :=
  congrArg Iso.hom (totalDerivedExtensionScalarsComp_eq f g)

end StacksDraft.DerivedExtensionScalarsComp

end

end
