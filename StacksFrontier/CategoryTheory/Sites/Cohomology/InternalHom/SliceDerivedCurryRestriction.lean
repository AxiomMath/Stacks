module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTransposeIsIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTransposeIso

/-!
# Restricting the tensor–internal-hom bijection to a slice site

Let `(C, O)` be a ringed site, `U` an object of `C`, and `K`, `L`, `M` objects of `D(O)`. The
bijection of [Stacks, Tag 08J8] turns `ψ : K ⟶ R𝓗om_O(L, M)` into a morphism
`K ⊗^𝐋_O L ⟶ M`. Restricting that morphism to the slice site `C/U` gives a morphism
`(K ⊗^𝐋_O L)|_U ⟶ M|_U`, and the slice tensor comparison
`Stacks.Cohomology.SliceDerivedSheafHom.sliceTensorRestrictionObjIso` reads it as a morphism
`K|_U ⊗^𝐋_{O|_U} L|_U ⟶ M|_U`. The one morphism of that shape the data at hand produce is the
transpose, over `C/U`, of

`ψ|_U` followed by the mate
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose`.

The theorem below says the two agree. So the bijection of 08J8 commutes with restriction to a
slice site, with the mate as the comparison on internal homs.

## Main results

* `Stacks.Cohomology.SliceDerivedSheafHom.map_derivedCurryHomEquiv`: the compatibility.
* `Stacks.Cohomology.SliceDerivedSheafHom.inv_comp_map_derivedCurryHomEquiv`: the same with the
  slice tensor comparison moved to the other side, which is the form a consumer rewriting a
  restricted transpose uses.

## Implementation notes

No 2-cell identity is assumed. In particular the *mate statement* — that the mate is the
comparison [Stacks, Tag 08DL] asserts to be an isomorphism — is not used; the module
documentation of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/SliceDerivedSheafHomTranspose.lean`
records that it is unproved in this development. What is used is the *definition* of the mate,
that its transpose over `C/U` is the slice tensor comparison followed by the restricted
evaluation morphism, together with the formula
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_apply` for the bijection and the naturality
of the slice tensor comparison in its first variable.

Consequently nothing here needs `U` to be subterminal, and the statement holds at every object
of `C`. Invertibility of the mate, which does need subterminality, is
`Stacks.Cohomology.SliceDerivedSheafHom.isIso_derivedSheafHomRestrictionTranspose` and is not
invoked.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction)

universe u

namespace Stacks.Cohomology.SliceDerivedSheafHom

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]

/-! ### Why every slice functor below is written with its instances pinned

`AlgebraicGeometry.RingedSite.over` is `@[implicit_reducible]`, so `(X.over U).J` and `X.J.over U`
are the same topology by `rfl`, and `(X.over U).O` and `X.O.over U` the same structure sheaf — but
not at the transparency instance search uses. A slice functor written plainly as `… (X.over U)`
therefore raises its instance goals at `(X.over U).J` and `(X.over U).O`, does not find this
file's hypotheses, and builds a second witness. Imported slice declarations disagree on which
spelling they carry — `SliceDerivedSheafHomTranspose.lean` pins at `X.J.over U` and `X.O.over U`,
`SliceDerivedSheafHomTransposeIsIso.lean` carries its slice hypotheses at `(X.over U).O` — so
composing them makes the kernel reconcile the two, which unfolds
`Stacks.SheafOfModules.derivedTensorProductFunctor` into `Classical.choice` and costs minutes per
declaration. That disagreement is a known, tracked problem of the ring-sheaf canonicalisation,
issue #1226, and `SliceDerivedSheafHomTransposeIsIso.lean` carries an accepted raised heartbeat
budget of 400000 for it, with that issue cited; it is not fixed here.

What is done here is to make this file internally consistent at the one spelling
`X.J.over U` / `X.O.over U`, the one the transpose file pins at: every slice functor below is
applied with `@` and its instance arguments given as `inferInstance` at that spelling, so the
witnesses are this file's own hypotheses and agree with the imported ones on the nose. Do not
replace such an application by the plain `… (X.over U)` form — the file does not then elaborate
inside the default budgets. -/

/-- **The transpose datum is tensoring the mate with the identity and then evaluating.** This is
`derivedSheafHomRestrictionDatum_eq_sliceCurryEquiv_transpose` in the same namespace, with the
bijection of [Stacks, Tag 08J8] eliminated by
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_apply`. -/
theorem derivedSheafHomRestrictionDatum_eq
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedSheafHomRestrictionDatum X U L M =
      ((@Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))
      (inferInstance : HasDerivedCategory (Modules (X.O.over U)))).map
          (derivedSheafHomRestrictionTranspose X U L M)).app ((restrictD X U).obj L) ≫
        (@AlgebraicGeometry.RingedSite.derivedSheafHomCounit (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))) ((restrictD X U).obj L)
          ((restrictD X U).obj M) := by
  have h := derivedSheafHomRestrictionDatum_eq_sliceCurryEquiv_transpose X U L M
  rw [sliceCurryEquiv_eq, RingedSite.derivedCurryHomEquiv_apply] at h
  exact h

/-- **Restriction to the slice site of the restricted evaluation morphism**, read through the
slice tensor comparison: it is the transpose datum, by the definition of the datum. -/
alias map_derivedSheafHomCounit := map_derivedSheafHomCounit_eq

/-- The transpose of `ψ`, restricted to `C/U` and expanded by the formula of [Stacks, Tag 08J8]
and by the definition of the transpose datum. -/
private theorem map_derivedCurryHomEquiv_aux_left
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ψ : K ⟶ ((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) :
    (restrictD X U).map (RingedSite.derivedCurryHomEquiv X K L M ψ) =
      (restrictD X U).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map ψ).app L) ≫
        ((sliceTensorRestrictionObjIso X U
            (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) L).hom ≫
          derivedSheafHomRestrictionDatum X U L M) := by
  rw [RingedSite.derivedCurryHomEquiv_apply X K L M ψ, (restrictD X U).map_comp,
    map_derivedSheafHomCounit X U L M]

/-- The transpose datum precomposed with `ψ|_U ⊗ 1` is the transpose, over `C/U`, of `ψ|_U`
followed by the mate. -/
private theorem map_derivedCurryHomEquiv_aux_right
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ψ : K ⟶ ((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) :
    ((@Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))
      (inferInstance : HasDerivedCategory (Modules (X.O.over U)))).map
          ((restrictD X U).map ψ)).app ((restrictD X U).obj L) ≫
        derivedSheafHomRestrictionDatum X U L M =
      (@AlgebraicGeometry.RingedSite.derivedCurryHomEquiv (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))) ((restrictD X U).obj K)
        ((restrictD X U).obj L) ((restrictD X U).obj M)
        ((restrictD X U).map ψ ≫ derivedSheafHomRestrictionTranspose X U L M) := by
  rw [RingedSite.derivedCurryHomEquiv_apply, Functor.map_comp, NatTrans.comp_app,
    derivedSheafHomRestrictionDatum_eq X U L M, Category.assoc]

/-- **The bijection of [Stacks, Tag 08J8] commutes with restriction to a slice site.** For
objects `K`, `L`, `M` of `D(O)` and `ψ : K ⟶ R𝓗om_O(L, M)`, restricting the transpose
`K ⊗^𝐋_O L ⟶ M` of `ψ` to `C/U` and reading the source through the slice tensor comparison gives
the transpose, formed over `C/U`, of `ψ|_U` followed by the mate
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose`. -/
theorem map_derivedCurryHomEquiv
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ψ : K ⟶ ((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) :
    (restrictD X U).map (RingedSite.derivedCurryHomEquiv X K L M ψ) =
      (sliceTensorRestrictionObjIso X U K L).hom ≫
        (@AlgebraicGeometry.RingedSite.derivedCurryHomEquiv (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))) ((restrictD X U).obj K)
          ((restrictD X U).obj L) ((restrictD X U).obj M)
          ((restrictD X U).map ψ ≫ derivedSheafHomRestrictionTranspose X U L M) := by
  have hnat := (@Stacks.Cohomology.SliceDerivedSheafHom.sliceTensorRestrictionObjIso_naturality X U
      (inferInstance : HasSheafify X.J AddCommGrpCat.{u})
      (inferInstance : X.J.WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} X.O).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules X.O) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ))
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))) ψ L
  exact (map_derivedCurryHomEquiv_aux_left X U K L M ψ).trans
    (((reassoc_of% hnat) (derivedSheafHomRestrictionDatum X U L M)).trans
      (congrArg (fun g => (sliceTensorRestrictionObjIso X U K L).hom ≫ g)
        (map_derivedCurryHomEquiv_aux_right X U K L M ψ)))

/-- `Stacks.Cohomology.SliceDerivedSheafHom.map_derivedCurryHomEquiv` with the slice tensor
comparison moved to the left-hand side. -/
theorem inv_comp_map_derivedCurryHomEquiv
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ψ : K ⟶ ((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) :
    (sliceTensorRestrictionObjIso X U K L).inv ≫
        (restrictD X U).map (RingedSite.derivedCurryHomEquiv X K L M ψ) =
      (@AlgebraicGeometry.RingedSite.derivedCurryHomEquiv (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (ComplexShape.up ℤ))) ((restrictD X U).obj K)
        ((restrictD X U).obj L) ((restrictD X U).obj M)
        ((restrictD X U).map ψ ≫ derivedSheafHomRestrictionTranspose X U L M) := by
  rw [map_derivedCurryHomEquiv, Iso.inv_hom_id_assoc]

end Stacks.Cohomology.SliceDerivedSheafHom

end
