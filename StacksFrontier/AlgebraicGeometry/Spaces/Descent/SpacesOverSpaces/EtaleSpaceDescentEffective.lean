module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EtaleDescentDataSitesEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EtaleEffectiveAlongProper
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpaceInverseImage

/-!
# Étale descent data of spaces are effective along morphisms of sheaf descent

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` along which descent of sheaves of
sets on the spaces-étale sites is effective. Then every descent datum `(U/X, φ)` of algebraic
spaces relative to `f` whose underlying space `U` is étale over `X` is isomorphic to the
canonical descent datum of an algebraic space `V` étale over `Y`. This is the passage, in the
proof of Stacks 0GG0, from the sheaf-theoretic descent of Stacks 0GFW back to algebraic spaces,
and it settles the statement
`AlgebraicGeometry.Space.EtaleSpaceDescentEffectiveOfSheafDescent`, which the base carries as a
hypothesis of its formalization of Stacks 0GG0.

The proof: the space datum `(U/X, φ)` is read as a descent datum of spaces-étale sites, and then,
through the strong transformation `V ↦ h_V`, as a descent datum of sheaves
(`AlgebraicGeometry.Space.Descent.HomDescentData.toSpacesEtaleDescentData`). By hypothesis it
descends to a sheaf `M` on `Y` with `f⁻¹ M ≅ h_U`. The inverse image `f⁻¹` is faithful, since
`toDescentData` is an equivalence, and a left adjoint, so `M ≅ h_W` for an algebraic space `W`
étale over `Y` by `AlgebraicGeometry.Space.SheafGivesSpace.exists_iso_yoneda_of_inverseImage_iso`
(the set-theoretic condition of Stacks 0GF6). Finally an iso of sheaf descent data
`f⁻¹ h_W ≅ h_U` compatible with the descent data is an iso of space descent data, by
`AlgebraicGeometry.Space.Descent.HomDescentData.exists_isEtale_nonempty_iso_of_toDescentData_iso`.

## Main results

* `AlgebraicGeometry.Space.etaleSpaceDescentEffectiveOfSheafDescent`: the statement above.

## References

* [Stacks Project, Tag 0GG0](https://stacks.math.columbia.edu/tag/0GG0)
* [Stacks Project, Tag 0GF6](https://stacks.math.columbia.edu/tag/0GF6)
* [Stacks Project, Tag 0GFW](https://stacks.math.columbia.edu/tag/0GFW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] uliftCategory in
/-- **Étale descent data of spaces are effective along morphisms of sheaf descent.** If descent
of spaces-étale sheaves along `f : X ⟶ Y` is effective, then every descent datum relative to
`f` whose underlying space is étale over `X` is isomorphic to the canonical descent datum of an
algebraic space étale over `Y`. This proves the translation step of Stacks 0GG0, carried by the
base as the hypothesis `AlgebraicGeometry.Space.EtaleSpaceDescentEffectiveOfSheafDescent`. -/
theorem etaleSpaceDescentEffectiveOfSheafDescent :
    EtaleSpaceDescentEffectiveOfSheafDescent B S hS := by
  intro X Y f hdescent D hD
  let Φ := (spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit ↦ f)
  let DG := ((spacesEtaleYonedaStrongTrans B S hS).descentDataFunctor (fun _ : Unit ↦ f)).obj
    (D.toSpacesEtaleDescentData hD).uliftObj.{u + 2}
  let M := Φ.objPreimage DG
  let eM : Φ.obj M ≅ DG := Φ.objObjPreimageIso DG
  have hfaith : ((spacesEtalePseudofunctor B S hS).map f.op.toLoc).toFunctor.Faithful :=
    ⟨fun {a b} p q h ↦ Φ.map_injective (by ext; exact h)⟩
  let iU : ((spacesEtalePseudofunctor B S hS).map f.op.toLoc).toFunctor.obj M ≅
      (SpacesEtale.topology B S hS X).yoneda.obj (Descent.HomDescentData.etaleObj D hD) :=
    { hom := eM.hom.hom ()
      inv := eM.inv.hom ()
      hom_inv_id := congrArg (fun φ ↦ φ.hom ()) eM.hom_inv_id
      inv_hom_id := congrArg (fun φ ↦ φ.hom ()) eM.inv_hom_id }
  obtain ⟨W, ⟨iW⟩⟩ := @SheafGivesSpace.exists_iso_yoneda_of_inverseImage_iso _ _ _ _ _ _ _ _ iU _
    (spacesEtalePseudofunctorAdjunction B S hS f) hfaith
  exact Descent.HomDescentData.exists_isEtale_nonempty_iso_of_toDescentData_iso D hD W
    (Φ.mapIso iW.symm ≪≫ eM)

end AlgebraicGeometry.Space

end
