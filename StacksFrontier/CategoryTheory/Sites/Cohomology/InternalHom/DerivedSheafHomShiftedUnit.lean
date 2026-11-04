module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSheafHomContravariantCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf

/-!
# The derived internal Hom out of a translate of the structure sheaf

Let `(C, O)` be a ringed site. The derived internal Hom out of the structure sheaf placed in
degree zero is the identity functor (`AlgebraicGeometry.RingedSite.derivedStructureSheafHomNatIso`)
and the derived internal Hom commutes with the translation in its contravariant variable
(`AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIso`). Together they identify
`RSheafHom(O[0]⟦n⟧, -)` with the translation `(-)⟦-n⟧`, so `RSheafHom(P, -)` is an
autoequivalence of `D(O)` for every `P` isomorphic to a translate of `O[0]`.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedSheafHomShiftedUnitIso`:
  `RSheafHom(O[0]⟦n⟧, -) ≅ (-)⟦-n⟧`.

## Main results

* `AlgebraicGeometry.RingedSite.isEquivalence_derivedSheafHomBifunctor_obj_of_iso`:
  `RSheafHom(P, -)` is an equivalence for `P ≅ O[0]⟦n⟧`.

## References

* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- **The derived internal Hom out of a translate of the structure sheaf is a translation**:
`RSheafHom(O[0]⟦n⟧, -) ≅ (-)⟦-n⟧`, the commutation with the translation in the contravariant
variable followed by the identification of `RSheafHom(O[0], -)` with the identity. -/
def derivedSheafHomShiftedUnitIso (n : ℤ) :
    (derivedSheafHomBifunctor X).obj (op ((derivedStructureSheaf X)⟦n⟧)) ≅
      shiftFunctor (DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (-n) :=
  NatIso.ofComponents
    (fun L => derivedSheafHomSourceShiftIso X (derivedStructureSheaf X) L n ≪≫
      (shiftFunctor _ (-n)).mapIso (derivedStructureSheafHomIso X L))
    (fun {L L'} ψ => by
      have h := derivedSheafHomSourceShiftIso_hom_naturality X (𝟙 (derivedStructureSheaf X)) ψ n
      simp only [CategoryTheory.Functor.map_id, op_id, NatTrans.id_app, Category.id_comp] at h
      simp only [Iso.trans_hom, Functor.mapIso_hom, ← Category.assoc, h]
      simp only [Category.assoc, ← Functor.map_comp, derivedStructureSheafHomIso_naturality])

/-- **`RSheafHom(P, -)` is an autoequivalence of `D(O)` when `P` is a translate of the structure
sheaf**: it is isomorphic to the translation `(-)⟦-n⟧`. -/
theorem isEquivalence_derivedSheafHomBifunctor_obj_of_iso
    {P : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (n : ℤ)
    (e : P ≅ (derivedStructureSheaf X)⟦n⟧) :
    ((derivedSheafHomBifunctor X).obj (op P)).IsEquivalence :=
  Functor.isEquivalence_of_iso
    ((derivedSheafHomShiftedUnitIso X n).symm ≪≫ (derivedSheafHomBifunctor X).mapIso e.op)

end AlgebraicGeometry.RingedSite

end
