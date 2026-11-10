module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorIsoCompositionModel
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackComparisonQCompositionLaw
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatKFlatDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorTotalCompositionLaw

/-!
# The Tag 07A4 comparison along a composite, on the whole derived category

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` and `g : (Sh(D), O') ⟶ (Sh(E), O'')` be morphisms of ringed
topoi.  `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso` is the comparison of
**Stacks 07A4**,

`Lf^*(K ⊗^L_{O'} L) ≅ Lf^*K ⊗^L_O Lf^*L`,

and `Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso` is the
composition isomorphism `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*` of **Stacks 0D6D**.  The composition law
relating the two is proved at a pair of K-flat complexes with flat terms in
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_comp_app_of_kFlat`; this file descends it
to the whole of `D(O'') × D(O'')`, where it becomes an identity of natural transformations with no
hypothesis on the objects.

## Main results

* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_comp`: **the composition law for
  Stacks 07A4**, as an equality of natural transformations
  `(K, L) ↦ Lf^*Lg^*(K ⊗^L_{O''} L) ⟶ Lf^*Lg^*K ⊗^L_O Lf^*Lg^*L` on `D(O'') × D(O'')`.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_comp`: the same identity read
  at an arbitrary pair of objects of `D(O'')`, which is the form its consumers need.

## Implementation notes

*Where the work is.*  Nowhere here.  The model identity
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_comp_app_of_kFlat` holds at a pair of
K-flat complexes with flat terms, and by **Stacks 06YS** such complexes resolve every complex of
`O''`-modules, so pairs of them localize to `D(O'') × D(O'') `; two natural transformations
agreeing on that image are therefore equal, which is
`Stacks.Sheaves.DerivedPullback.natTrans_ext_of_flatKFlat`.  This file instantiates the model
identity at the two inputs it asks for and applies that extensionality principle.

*The three inputs supplied here.*  **No hypothesis is carried**: all three hypotheses of the
model identity are discharged from the tree, so both results below assume nothing beyond `hmosf`,
`hmosg` and the ambient instances.  `e` is
`Stacks.Sheaves.DerivedPullback.CompositionLaw.pullbackComplexCompIso`, the composition law
`g^* ⋙ f^* ≅ (g ∘ f)^*` for degreewise pullback read on cochain complexes; `hcompQ` is
`CompositionLaw.derivedPullbackCompIso_hom_app_comp_pullbackComparisonQ` of the same namespace,
the composition law of **Stacks 06YY** for the comparison `Lf^*(QM) ⟶ Q(f^*M)` read against it;
and `htotal`, the composition law of **Stacks 03EL** for the comparison
`f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)` carried along `CategoryTheory.DerivedCategory.Q` and read
against `pullbackComplexCompIso`, is
`Stacks.Sheaves.DerivedPullback.map_pullbackToposTensorTotalIso_comp` of
the module `PullbackToposTensorTotalCompositionLaw`
in this directory, where the Stacks 03EL composition law is **proved** — for arbitrary cochain
complexes of `O''`-modules, with no K-flatness, no boundedness and no flatness of terms.  All
three hold at arbitrary complexes.

*Why the pointwise form is stated separately.*  The consumers of this composition law — the
monoidality step of [Stacks, Tag 0FPN],
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.relativeCupProduct_comp_pushforwardCompIso`,
among them — ask for it at a pair of objects, with the three whiskerings already reduced to a
`map`, an `app` and a `map` of a pair.  Those reductions are definitional, so the pointwise
statement is the natural-transformation identity read at `(P, Q)`; it is recorded because reading
it off at the use site means reducing the whiskerings there, against a goal in which the ambient
functors are derived functors on categories of sheaves of modules.

*No `stacks` attribute.*  Stacks 07A4 is claimed, bare, by
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso`
(in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison`)
and Stacks 0D6D by
`Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso`
(in `StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOnRingedTopoi`).  A
bare attribute claims the whole tag, so a clause here would assert full and partial coverage of
the same tag at once; the ringed-space twin records the same decision at
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp`.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi
open Stacks.Sheaves.DerivedPullback.KFlatPullback
open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

section Composite

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
  (hmosf : f.u.IsMorphismOfSites Y.J X.J) (hmosg : g.u.IsMorphismOfSites Z.J Y.J)

/-- **The comparison of Stacks 07A4 is compatible with composition of morphisms of ringed topoi**,
as an identity of natural transformations on `D(O'') × D(O'')` with no hypothesis on the objects.
The composition isomorphism `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*` of Stacks 0D6D, followed by the comparison

`L(g ∘ f)^*(K ⊗^L_{O''} L) ≅ L(g ∘ f)^*K ⊗^L_O L(g ∘ f)^*L`

of Stacks 07A4, is the derived pullback along `f` of the comparison for `g`, followed by the
comparison for `f` and by the composition isomorphism in each tensor factor.

Both sides are transformations out of `(K, L) ↦ Lf^*Lg^*(K ⊗^L_{O''} L)`, and by Stacks 06YS the
K-flat complexes with flat terms resolve every complex of `O''`-modules, so pairs of them localize
to `D(O'') × D(O'') `; the two sides therefore agree as soon as they agree at a pair of such
complexes, which is `derivedPullbackTensorIso_comp_app_of_kFlat` through
`natTrans_ext_of_flatKFlat`.

This statement carries no hypothesis beyond `hmosf`, `hmosg` and the ambient instances.  The one
further input the model identity consumes is the composition law of Stacks 03EL for the
comparison `f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)`, carried along `CategoryTheory.DerivedCategory.Q`
and read against `CompositionLaw.pullbackComplexCompIso`; that law is proved, at arbitrary
cochain complexes, as `Stacks.Sheaves.DerivedPullback.map_pullbackToposTensorTotalIso_comp` in
the module `PullbackToposTensorTotalCompositionLaw`
of this directory, and is supplied from there. -/
theorem derivedPullbackTensorIso_comp :
    Functor.whiskerLeft
          (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.O))
          (derivedPullbackCompIso f g hmosf hmosg).hom ≫
        (derivedPullbackTensorIso (g.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg)).hom =
      Functor.whiskerRight (derivedPullbackTensorIso g hmosg).hom (derivedPullback f) ≫
        Functor.whiskerLeft ((derivedPullback g).prod (derivedPullback g))
            (derivedPullbackTensorIso f hmosf).hom ≫
          Functor.whiskerRight
            (NatTrans.prod (derivedPullbackCompIso f g hmosf hmosg).hom
              (derivedPullbackCompIso f g hmosf hmosg).hom)
            (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)) :=
  natTrans_ext_of_flatKFlat Z _ _ fun K L hK hL hflatK hflatL =>
    derivedPullbackTensorIso_comp_app_of_kFlat f g hmosf hmosg
      (CompositionLaw.pullbackComplexCompIso f g)
      (CompositionLaw.derivedPullbackCompIso_hom_app_comp_pullbackComparisonQ f g hmosf hmosg)
      (map_pullbackToposTensorTotalIso_comp f g hmosf hmosg) K L hK hL hflatK hflatL

/-- **The comparison of Stacks 07A4 is compatible with composition, at an arbitrary pair of
objects of `D(O'')`.**  This is `derivedPullbackTensorIso_comp` read at `(P, Q)`, with the three
whiskerings reduced: the left whiskering becomes a component at the derived tensor product, the
right whiskering by `Lf^*` becomes `(derivedPullback f).map`, and the right whiskering of the
product transformation becomes the action of the uncurried derived tensor bifunctor on the pair of
composition isomorphisms.

Each of those reductions holds by definition, so this is the previous identity with no further
argument; it is recorded because its consumers ask for the composition law in this form, and
reducing the whiskerings at the use site would do so against a goal whose ambient functors are
derived functors on categories of sheaves of modules.

Like `derivedPullbackTensorIso_comp`, this carries no hypothesis beyond `hmosf`, `hmosg` and the
ambient instances. -/
theorem derivedPullbackTensorIso_hom_app_comp
    (P Q : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    (derivedPullbackCompIso f g hmosf hmosg).hom.app
          ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.O)).obj (P, Q)) ≫
        (derivedPullbackTensorIso (g.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg)).hom.app (P, Q) =
      (derivedPullback f).map ((derivedPullbackTensorIso g hmosg).hom.app (P, Q)) ≫
        (derivedPullbackTensorIso f hmosf).hom.app
            ((derivedPullback g).obj P, (derivedPullback g).obj Q) ≫
          (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
            ((derivedPullbackCompIso f g hmosf hmosg).hom.app P ×ₘ
              (derivedPullbackCompIso f g hmosf hmosg).hom.app Q) :=
  NatTrans.congr_app (derivedPullbackTensorIso_comp f g hmosf hmosg) (P, Q)

end Composite

end Stacks.Sheaves.DerivedPullback

end
