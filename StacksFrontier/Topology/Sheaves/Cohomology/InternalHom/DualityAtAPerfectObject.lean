module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModelIndependence
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedDualOfAPerfectObject

/-!
# Morphisms out of a perfect object as degree-zero cohomology of a tensor product

Let `X` be a ringed site, let `F` be a **perfect** object of `D(O)` and suppose given an object
`G` of `D(O)`, an integer `d` and an identification

`RSheafHom(F, O[0]) ≅ G[-d]`

of the derived dual of `F` with a shift of `G`. Then for every `M` in `D(O)`

`Hom_{D(O)}(F, M) ≅ H⁰(X, M ⊗^L_O G[-d])`,

and the identification is additive and **natural in `M`**.

This is the shape of the duality statement of Stacks 0G02: there `X` is a regular scheme of
finite type over a field, `F` a coherent module supported at a closed point `x`, `G` a coherent
module supported at `x` whose stalk is the Matlis dual of `F_x`, and `d = dim 𝒪_{X,x}`. What the
statement below isolates is the part of that lemma which is pure sheaf theory on a ringed site,
and what it leaves to the geometry is exactly two inputs: that `F` is perfect, and the
identification of its derived dual with `G[-d]`.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedSheafHomIsoDerivedTensorOfDual`: the isomorphism
  `RSheafHom(F, M) ≅ M ⊗^L_O G[-d]` carried by the two inputs, natural in `M`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomIsoDerivedTensorOfDual_hom_naturality`: that
  isomorphism is natural in `M`.
* `AlgebraicGeometry.RingedSite.homAddEquivHomologyDerivedTensorOfDual` and
  `AlgebraicGeometry.RingedSite.homAddEquivHomologyDerivedTensorOfDual_naturality`: **the
  duality identification and its functoriality in `M`.**

## Implementation notes

Three inputs, all in the library:

* `AlgebraicGeometry.RingedSite.derivedDualTensorIsoDerivedSheafHom` — the derived dual of a
  perfect object computes the derived internal Hom, `M ⊗^L_O F^∨ ≅ RSheafHom(F, M)`, naturally
  in `M`. This is where perfection of `F` is used, and only here.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv` and its naturality
  `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality` — Tag 08JA: the
  degree-zero global hypercohomology of `RSheafHom(F, M)` is `Hom_{D(O)}(F, M)`, naturally in
  both variables.
* the two-variable functoriality of the derived tensor product, used as the naturality of
  `(derivedTensorProductFunctor X).map g` at the given identification of the dual.

The target is the degree-zero cohomology of derived global sections of the derived tensor
product, which is `H⁰(X, M ⊗^L_O G[-d])` in the spelling the duality statements of the
development use; by `Stacks.SheafOfModules.derivedGlobalSectionsExtEquiv` it may equivalently be
read as `Hom_{D(O)}(O[0], M ⊗^L_O G[-d])`.

The functoriality clause is stated in the form the source states it: for `g : M ⟶ N` the
identification carries postcomposition with `g` to the map induced on degree-zero cohomology of
derived global sections by `g ⊗ 𝟙`. It is not packaged as an isomorphism of functors, since the
family is indexed by objects of `D(O)` and the two sides are already functors.

*No attribute is placed in this file.* Tag 0G02 asserts the duality under its own hypotheses —
a regular scheme of finite type over a field and coherent modules supported at a closed point —
and the statements below replace those by the two sheaf-theoretic inputs above, which is a
different statement; neither the perfection of a coherent module supported at a closed point on
a regular scheme nor the identification of its derived dual with the shifted Matlis dual is
proved here.

## References

* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor
open Stacks.Cohomology.ModuleSections

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

variable (F D : DerivedCategory
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)))
  (hF : X.IsPerfect F)
  (e : ((derivedSheafHomBifunctor X).obj (op F)).obj
    (Stacks.DerivedTensor.RingedSite.unitObject X) ≅ D)

/-- **The derived internal Hom out of a perfect object is a derived tensor product with its
dual.** Given an identification `e : F^∨ ≅ D` of the derived dual of a perfect `F`,

`RSheafHom(F, M) ≅ M ⊗^L_O D`.

It is `AlgebraicGeometry.RingedSite.derivedDualTensorIsoDerivedSheafHom` read backwards and
followed by `e` inside the tensor product, and it is natural in `M` by
`AlgebraicGeometry.RingedSite.derivedSheafHomIsoDerivedTensorOfDual_hom_naturality`. -/
def derivedSheafHomIsoDerivedTensorOfDual
    (M : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))) :
    ((derivedSheafHomBifunctor X).obj (op F)).obj M ≅
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj M).obj D :=
  (derivedDualTensorIsoDerivedSheafHom X M F hF).symm ≪≫
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj M).mapIso e

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- `AlgebraicGeometry.RingedSite.derivedSheafHomIsoDerivedTensorOfDual` is natural in `M`: the
morphism induced by `g : M ⟶ N` on the derived internal Hom corresponds to `g ⊗ 𝟙 D`.

The first factor is natural by
`AlgebraicGeometry.RingedSite.derivedDualTensorIsoDerivedSheafHom_hom_naturality` and the second
by the two-variable functoriality of the derived tensor product. -/
theorem derivedSheafHomIsoDerivedTensorOfDual_hom_naturality
    {M N : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))}
    (g : M ⟶ N) :
    ((derivedSheafHomBifunctor X).obj (op F)).map g ≫
        (derivedSheafHomIsoDerivedTensorOfDual X F D hF e N).hom =
      (derivedSheafHomIsoDerivedTensorOfDual X F D hF e M).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map g).app D := by
  have hdual := derivedDualTensorIsoDerivedSheafHom_hom_naturality X F hF g
  have hsymm : ((derivedSheafHomBifunctor X).obj (op F)).map g ≫
      (derivedDualTensorIsoDerivedSheafHom X N F hF).inv =
    (derivedDualTensorIsoDerivedSheafHom X M F hF).inv ≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map g).app
        (((derivedSheafHomBifunctor X).obj (op F)).obj
          (Stacks.DerivedTensor.RingedSite.unitObject X)) := by
    rw [Iso.comp_inv_eq, Category.assoc, hdual, Iso.inv_hom_id_assoc]
  dsimp only [derivedSheafHomIsoDerivedTensorOfDual, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, hsymm, Category.assoc, Category.assoc,
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map g).naturality e.hom]

/-- **Duality at a perfect object.** For a perfect `F` with derived dual identified with `D`,
the group of morphisms `F ⟶ M` in `D(O)` is the degree-zero cohomology of the derived global
sections of `M ⊗^L_O D`:

`Hom_{D(O)}(F, M) ≅ H⁰(X, M ⊗^L_O D)`.

Taken at `D = G[-d]` this is the conclusion of Stacks 0G02; the functoriality in `M` that the
source asserts is
`AlgebraicGeometry.RingedSite.homAddEquivHomologyDerivedTensorOfDual_naturality`. -/
def homAddEquivHomologyDerivedTensorOfDual
    (M : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))) :
    (F ⟶ M) ≃+
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj M).obj D)) : Type u) :=
  (derivedSheafHomGlobalSectionsEquiv X F M).symm.trans
    (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
      ((derivedModuleGlobalSections X).mapIso
        (derivedSheafHomIsoDerivedTensorOfDual X F D hF e M))).addCommGroupIsoToAddEquiv)

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **The duality identification of Stacks 0G02 is functorial in `M`.** For `g : M ⟶ N` and
`a : F ⟶ M` the class attached to `a ≫ g` is the image of the class attached to `a` under the map
induced on degree-zero cohomology of derived global sections by `g ⊗ 𝟙 D`.

Tag 08JA is natural in its covariant variable
(`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality`), and the
isomorphism of
`AlgebraicGeometry.RingedSite.derivedSheafHomIsoDerivedTensorOfDual` is natural in `M`, so both
sides are the class of `a` moved along one and the same morphism of `D(O)`. -/
theorem homAddEquivHomologyDerivedTensorOfDual_naturality
    {M N : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))}
    (g : M ⟶ N) (a : F ⟶ M) :
    homAddEquivHomologyDerivedTensorOfDual X F D hF e N (a ≫ g) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map g).app D))
        (homAddEquivHomologyDerivedTensorOfDual X F D hF e M a) := by
  obtain ⟨ξ, rfl⟩ : ∃ ξ, derivedSheafHomGlobalSectionsEquiv X F M ξ = a :=
    ⟨_, (derivedSheafHomGlobalSectionsEquiv X F M).apply_symm_apply a⟩
  have h08JA := derivedSheafHomGlobalSectionsEquiv_naturality X (𝟙 F) g ξ
  rw [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.id_comp] at h08JA
  simp only [homAddEquivHomologyDerivedTensorOfDual, AddEquiv.trans_apply,
    Iso.addCommGroupIsoToAddEquiv_apply, Functor.mapIso_hom, AddEquiv.symm_apply_apply]
  rw [← h08JA, AddEquiv.symm_apply_apply, homologyGlobalSections_map_comp_apply,
    homologyGlobalSections_map_comp_apply,
    derivedSheafHomIsoDerivedTensorOfDual_hom_naturality X F D hF e g]

end AlgebraicGeometry.RingedSite

end
