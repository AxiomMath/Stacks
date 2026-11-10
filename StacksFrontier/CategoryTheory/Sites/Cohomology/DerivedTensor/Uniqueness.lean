module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity

/-!
# The derived tensor product is unique, with all of its structure

Let `(C, O)` be a ringed site.  A derived tensor product on `D(Mod(O))` in the sense of Stacks
06YU is a bifunctor together with its comparisons with the ordinary total tensor complex, and
this development hands its consumers two, each a construction made opaque with
`irreducible_def`: the one indexed by the ringed site,
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, and the one indexed by the structure
sheaf, `Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`.  A statement proved
over one of them is unavailable over the other until they are identified.

`AlgebraicGeometry.RingedSite.derivedTensorFunctorIso` identifies the two *bifunctors*.  This
file proves that the identification is compatible with everything else a derived tensor product
carries, so that a statement transported across it keeps its meaning:

* the two-sided and the two one-sided K-flat comparisons with the total tensor complex;
* the canonical map `toTensor` to the total tensor complex, for **arbitrary** complexes, which
  is the datum that pins the bifunctor down as the *derived* tensor product;
* the associativity constraint of [Stacks, Tag 0FPT];
* the commutativity constraint and both unit constraints of [Stacks, Tag 0FPT].

Everything is proved for an arbitrary pair of derived tensor products over one structure sheaf,
the comparison being
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.tensorIso`; the statements about
`AlgebraicGeometry.RingedSite.derivedTensorFunctorIso` are that comparison at the two canonical
choices.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.tensorIso`: the canonical isomorphism
  `T.tensor ≅ T'.tensor` between the bifunctors of two derived tensor products over the same
  structure sheaf.

## Main results

* `…DerivedTensorProduct.tensorIso_hom_app_app`: on a pair of K-flat complexes the comparison is
  the two K-flat comparisons, `T.comparison ≫ T'.comparison⁻¹`.
* `…DerivedTensorProduct.tensorIso_refl`, `…tensorIso_trans`, `…tensorIso_symm`: the comparison
  of a derived tensor product with itself is the identity, the comparisons compose, and
  exchanging the two derived tensor products inverts the comparison.  So the family is a genuine
  canonical identification and not merely a choice of isomorphism for each pair.
* `…DerivedTensorProduct.comp_toTensor_of_comp_comparison`: **a bifunctor isomorphism compatible
  with the K-flat comparisons is compatible with the canonical map to the total tensor complex at
  every pair of complexes**, K-flat or not.  This is the one step with mathematical content: the
  canonical map is characterized by its naturality together with its values on K-flat
  representatives (Stacks 0FPH), and the proof runs that characterization through a pair of
  K-flat resolutions.
* `…DerivedTensorProduct.tensorIso_hom_app_app_comp_toTensor`,
  `…_comp_comparison`, `…_comp_comparisonRight`, `…_comp_comparisonLeft`: the comparison is
  compatible with all four maps to the total tensor complex.
* `…DerivedTensorProduct.comparison_inv_comp_tensorIso_hom_app_app`: the same for the inverse of
  the two-sided comparison, which is the form in which the comparison is pushed out of a
  composite.
* `…DerivedTensorProduct.tensorIso_hom_app_app_comp_associator`: compatibility with the
  associativity constraint.
* `…DerivedTensorProduct.tensorIso_hom_app_app_comp_braidingIso`,
  `…_comp_rightUnitIso`, `…_comp_leftUnitIso`: compatibility with the commutativity constraint
  and with both unit constraints.
* `AlgebraicGeometry.RingedSite.derivedTensorFunctorIso_eq_tensorIso` and the
  `derivedTensorObjIso_*` corollaries: the same statements for the comparison of the two
  canonical derived tensor products of the library.

## Implementation notes

**At what generality the bridge is stated, exactly.**  The site's object, morphism, structure
sheaf and module universes are all one `u` and the site is small, i.e.
`X : AlgebraicGeometry.RingedSite.{u, u, u}` with the `SmallCategory` instance coming from
`X.category`; the derived category's own hom universe `d` is free, as `HasDerivedCategory.{d}`.
This is *not* a restriction imposed here: it is the generality of the right-hand side.
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` is defined only at a small site with all
four universes tied to one `u`, because its existence theorem rests on
`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution`, which pins the ring universe to
the site's hom universe.  `Stacks.SheafOfModules.canonicalDerivedTensorProduct` is available
more generally — at a `RingedSite.{c, u, u}` with the object universe `c` free — and the bridge
says nothing at `c ≠ u`, for the simple reason that there is nothing on the other side to bridge
to.  The two compatibilities with the commutativity and unit constraints carry one further
pinning, `CategoryTheory.HasDerivedCategory.standard` in place of `HasDerivedCategory.{d}`,
inherited from `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso` and
`rightUnitIso`, which are stated there because `AlgebraicGeometry.RingedSite.kFlatModel` is.

**Where the content is.**  Three of the compatibilities are formal consequences of the value on
K-flat pairs: the one-sided comparisons and the commutativity and unit constraints are built
from `comparison`, `comparisonRight` and the bifunctor's own action, so moving the comparison
across them is naturality plus the K-flat value.  The compatibility with `toTensor` is not: at a
pair of arbitrary complexes neither side is computed by anything, and the identification has to
be propagated from a pair of K-flat resolutions, which is `comp_toTensor_of_comp_comparison`.

**The associator.**  Both associators are the associator of
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`, re-seated onto the respective bifunctor
by `CategoryTheory.MonoidalCategory.reseat`.  So their compatibility is a statement about two
re-seatings of one monoidal structure, with no reference to derived categories, and it is proved
in that generality as `CategoryTheory.MonoidalCategory.reseat_associator_comparison`.  The unit
isomorphisms of the two re-seatings play no part — the associator of `reseatStruct` does not
mention them — so they are allowed to differ there.

That lemma is the companion of `CategoryTheory.MonoidalCategory.reseat_associativity` and belongs
beside it in `StacksFrontier.CategoryTheory.Monoidal.Reseat`; it is stated here instead only because
that module sits near the bottom of the import graph, so adding a declaration to it re-checks
every one of its transitive importers.  Anyone with two re-seatings of one monoidal structure
should use this lemma rather than prove it again, and its natural home
is `Reseat`.

**Why the two canonical choices are not merged instead.**  They are elements of two distinct Lean
types, `Stacks.SheafOfModules.DerivedTensorProduct` at a bundled ringed site and
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` at a bare sheaf of rings, each with its
own development; the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface` record why neither can be
deleted in favour of the other.  The field-by-field reading
`AlgebraicGeometry.RingedSite.derivedTensorProductDatumOfSite` turns a site-indexed one into a
sheaf-indexed one, and that is what lets every statement here be proved once, over the
sheaf-indexed structure.

**No Stacks tag is claimed.**  Both sides are the derived tensor product of Stacks 06YU, which is
formalized and tagged, and the constraints are those of [Stacks, Tag 0FPT], tagged where they are
constructed.  What this file adds is the compatibility of an identification internal to the
development, which neither tag asserts.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

universe v u d

/-! ### Two re-seatings of one monoidal structure -/

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {T₁ T₂ : C ⥤ C ⥤ C} {U₁ U₂ : C}

/-- **The comparison of two re-seatings of one monoidal structure is compatible with their
associativity constraints.**

Given `e₁ : curriedTensor C ≅ T₁` and `e₂ : curriedTensor C ≅ T₂`, the composite
`γ = e₁⁻¹ ≫ e₂ : T₁ ≅ T₂` is the only comparison of the two prescribed bifunctors that the two
re-seatings afford, and the threefold square it spans commutes.  The unit isomorphisms `ε₁`, `ε₂`
are unconstrained: the associator of `CategoryTheory.MonoidalCategory.reseatStruct` does not
mention the unit.

The hypothesis on `γ` is its value at a pair of objects rather than an equality of isomorphisms,
which is what a caller can supply cheaply when `e₁` and `e₂` are themselves composites. -/
lemma reseat_associator_comparison (e₁ : curriedTensor C ≅ T₁) (e₂ : curriedTensor C ≅ T₂)
    (ε₁ : 𝟙_ C ≅ U₁) (ε₂ : 𝟙_ C ≅ U₂) {γ : T₁ ≅ T₂}
    (hγ : ∀ A B : C, (γ.hom.app A).app B = (reseatIso e₁ A B).inv ≫ (reseatIso e₂ A B).hom)
    (X Y Z : C) :
    (γ.hom.app ((T₁.obj X).obj Y)).app Z ≫ (T₂.map ((γ.hom.app X).app Y)).app Z ≫
        (@associator C _ (reseat e₂ ε₂).toMonoidalCategoryStruct X Y Z).hom =
      (@associator C _ (reseat e₁ ε₁).toMonoidalCategoryStruct X Y Z).hom ≫
        (γ.hom.app X).app ((T₁.obj Y).obj Z) ≫ (T₂.obj X).map ((γ.hom.app Y).app Z) := by
  rw [reseat_associator, reseat_associator, hγ, hγ, hγ, hγ, reseat_whiskerRight e₂,
    reseat_whiskerLeft e₂]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, tensorHom_id,
    id_tensorHom, comp_whiskerRight, whiskerLeft_comp, whiskerLeft_hom_inv_assoc]
  simp only [← Category.assoc]
  simp only [Category.assoc, Category.comp_id, ← comp_whiskerRight, Iso.hom_inv_id]

end CategoryTheory.MonoidalCategory

/-! ### The comparison of two derived tensor products -/

namespace Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

open Stacks.SheafOfModules.DerivedMonoidal

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

attribute [local instance] Stacks.SheafOfModules.DerivedMonoidal.kFlatQ_isLocalization
  Stacks.SheafOfModules.DerivedMonoidal.kFlatQLeft_isLocalization

section OverAStructureSheaf

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Modules R)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

private theorem aux_comp_inv_hom {D : Type*} [Category D] {W X Y Z : D} (a : W ⟶ X) (e : Y ≅ X)
    (f : X ⟶ Z) : (a ≫ e.inv) ≫ e.hom ≫ f = a ≫ f := by
  rw [Category.assoc, Iso.inv_hom_id_assoc]

/-- **The canonical comparison of the bifunctors of two derived tensor products** over one
structure sheaf.  Both descend the total tensor complex of K-flat complexes along the same
localization, by `Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso`, so each is
isomorphic to `CochainComplex.KFlatBifunctor.derivedBifunctor` and hence to the other. -/
def tensorIso (T T' : DerivedTensorProduct R) : T.tensor ≅ T'.tensor :=
  (derivedBifunctorTensorIso R T).symm ≪≫ derivedBifunctorTensorIso R T'

/-- The comparison of a derived tensor product with itself is the identity. -/
@[simp]
theorem tensorIso_refl (T : DerivedTensorProduct R) : tensorIso R T T = Iso.refl _ :=
  (derivedBifunctorTensorIso R T).symm_self_id

/-- The comparisons compose: the identification of the bifunctors of two derived tensor products
is canonical, not a choice made separately for each pair. -/
@[simp]
theorem tensorIso_trans (T T' T'' : DerivedTensorProduct R) :
    tensorIso R T T' ≪≫ tensorIso R T' T'' = tensorIso R T T'' := by
  rw [tensorIso, tensorIso, tensorIso, Iso.trans_assoc, ← Iso.trans_assoc
    (derivedBifunctorTensorIso R T'), Iso.self_symm_id, Iso.refl_trans]

/-- The comparison is inverted by exchanging the two derived tensor products. -/
@[simp]
theorem tensorIso_symm (T T' : DerivedTensorProduct R) :
    (tensorIso R T T').symm = tensorIso R T' T := by
  rw [tensorIso, tensorIso, Iso.trans_symm, Iso.symm_symm_eq]

/-- **On a pair of K-flat complexes the comparison is the two K-flat comparisons.**  Both derived
tensor products compute the total tensor complex there, and the comparison is the composite of
the one with the inverse of the other. -/
theorem tensorIso_hom_app_app (T T' : DerivedTensorProduct R)
    (K L : CochainComplex (Modules R) ℤ)
    (hK : Stacks.SheafOfModules.KFlat R K) (hL : Stacks.SheafOfModules.KFlat R L) :
    ((tensorIso R T T').hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) =
      (T.comparison K L hK hL).hom ≫ (T'.comparison K L hK hL).inv := by
  have hL' : CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Mod R)) L := hL
  have hiso : ((derivedBifunctorTensorIso R T).app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) =
      CochainComplex.KFlatBifunctor.comparisonRight (curriedTensor (Mod R)) K L hL' ≪≫
        (T.comparison K L hK hL).symm :=
    Iso.ext (derivedBifunctorTensorIso_hom_app_app R T K L hK hL)
  have hinv : ((derivedBifunctorTensorIso R T).inv.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) =
      (T.comparison K L hK hL).hom ≫
        (CochainComplex.KFlatBifunctor.comparisonRight (curriedTensor (Mod R)) K L hL').inv :=
    congrArg (fun i : _ ≅ _ => i.inv) hiso
  have hom' : ((derivedBifunctorTensorIso R T').hom.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) =
      (CochainComplex.KFlatBifunctor.comparisonRight (curriedTensor (Mod R)) K L hL').hom ≫
        (T'.comparison K L hK hL).inv :=
    derivedBifunctorTensorIso_hom_app_app R T' K L hK hL
  change ((derivedBifunctorTensorIso R T).inv.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) ≫
      ((derivedBifunctorTensorIso R T').hom.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) = _
  rw [hinv, hom']
  exact aux_comp_inv_hom _ _ _

/-- **The comparison carries the K-flat comparison of one derived tensor product to that of the
other.** -/
theorem tensorIso_hom_app_app_comp_comparison (T T' : DerivedTensorProduct R)
    (K L : CochainComplex (Modules R) ℤ)
    (hK : Stacks.SheafOfModules.KFlat R K) (hL : Stacks.SheafOfModules.KFlat R L) :
    ((tensorIso R T T').hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫
        (T'.comparison K L hK hL).hom = (T.comparison K L hK hL).hom := by
  rw [tensorIso_hom_app_app, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The comparison carries the inverse of one K-flat comparison to the inverse of the
other.**  This is the form in which the comparison is pushed *out* of a composite, and it is
what the commutativity constraint needs. -/
theorem comparison_inv_comp_tensorIso_hom_app_app (T T' : DerivedTensorProduct R)
    (K L : CochainComplex (Modules R) ℤ)
    (hK : Stacks.SheafOfModules.KFlat R K) (hL : Stacks.SheafOfModules.KFlat R L) :
    (T.comparison K L hK hL).inv ≫
        ((tensorIso R T T').hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) =
      (T'.comparison K L hK hL).inv := by
  rw [tensorIso_hom_app_app, Iso.inv_hom_id_assoc]

/-! ### The canonical map to the total tensor complex -/

/-- **An isomorphism of the two bifunctors compatible with the K-flat comparisons is compatible
with the canonical maps to the total tensor complex, at an arbitrary pair of complexes.**

Neither factor is assumed K-flat, so neither `toTensor` is computed by anything; what makes the
statement available is that the canonical map is determined by its naturality together with its
values on K-flat representatives, as in the proof of [Stacks, Tag 0FPH]
(`toTensor_eq_of_resolutions`).  The proof propagates the identification from a pair of K-flat
resolutions `P ⟶ K`, `N ⟶ L`, which exist by Stacks 06YS. -/
theorem comp_toTensor_of_comp_comparison (T T' : DerivedTensorProduct R)
    (α : T.tensor ≅ T'.tensor)
    (hα : ∀ (K L : CochainComplex (Modules R) ℤ)
        (hK : Stacks.SheafOfModules.KFlat R K)
        (hL : Stacks.SheafOfModules.KFlat R L),
      (α.hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫
        (T'.comparison K L hK hL).hom = (T.comparison K L hK hL).hom)
    (K L : CochainComplex (Modules R) ℤ) :
    (α.hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫ T'.toTensor K L =
      T.toTensor K L := by
  obtain ⟨P, p, hP₀, hp⟩ := exists_kFlat_quasiIso R K
  obtain ⟨N, q, hN₀, hq⟩ := exists_kFlat_quasiIso R L
  have hP : Stacks.SheafOfModules.KFlat R P := hP₀
  have hN : Stacks.SheafOfModules.KFlat R N := hN₀
  have : IsIso (DerivedCategory.Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  have : IsIso (DerivedCategory.Q.map q) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  have hPN : (α.hom.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N) ≫
      T'.toTensor P N = T.toTensor P N := by
    rw [T'.toTensor_eq_comparison P N hP hN, hα P N hP hN,
      T.toTensor_eq_comparison P N hP hN]
  refine (cancel_epi ((T.tensor.obj (DerivedCategory.Q.obj K)).map
    (DerivedCategory.Q.map q))).1 ?_
  refine (cancel_epi ((T.tensor.map (DerivedCategory.Q.map p)).app
    (DerivedCategory.Q.obj N))).1 ?_
  rw [T.toTensor_naturality p q, ← hPN, NatTrans.app_naturality_assoc,
    NatTrans.naturality_app_assoc, T'.toTensor_naturality p q]
  exact (Category.assoc _ _ _).symm

/-- **The comparison is compatible with the canonical maps to the total tensor complex**, at
every pair of complexes. -/
theorem tensorIso_hom_app_app_comp_toTensor (T T' : DerivedTensorProduct R)
    (K L : CochainComplex (Modules R) ℤ) :
    ((tensorIso R T T').hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫
        T'.toTensor K L = T.toTensor K L :=
  comp_toTensor_of_comp_comparison R T T' (tensorIso R T T')
    (tensorIso_hom_app_app_comp_comparison R T T') K L

/-- **The comparison is compatible with the right one-sided K-flat comparisons**: no flatness is
assumed of the left factor. -/
theorem tensorIso_hom_app_app_comp_comparisonRight (T T' : DerivedTensorProduct R)
    (K L : CochainComplex (Modules R) ℤ) (hL : Stacks.SheafOfModules.KFlat R L) :
    ((tensorIso R T T').hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫
        (T'.comparisonRight K L hL).hom = (T.comparisonRight K L hL).hom := by
  rw [← T.toTensor_eq_comparisonRight K L hL, ← T'.toTensor_eq_comparisonRight K L hL]
  exact tensorIso_hom_app_app_comp_toTensor R T T' K L

/-- **The comparison is compatible with the left one-sided K-flat comparisons**: no flatness is
assumed of the right factor. -/
theorem tensorIso_hom_app_app_comp_comparisonLeft (T T' : DerivedTensorProduct R)
    (K L : CochainComplex (Modules R) ℤ) (hK : Stacks.SheafOfModules.KFlat R K) :
    ((tensorIso R T T').hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫
        (T'.comparisonLeft K L hK).hom = (T.comparisonLeft K L hK).hom := by
  rw [← T.toTensor_eq_comparisonLeft K L hK, ← T'.toTensor_eq_comparisonLeft K L hK]
  exact tensorIso_hom_app_app_comp_toTensor R T T' K L

/-! ### The associativity constraint -/

/-- The comparison of the two bifunctors is the comparison of the two re-seatings of the
monoidal structure of [Stacks, Tag 0FPT] they define: the isomorphism with the tensor product of
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` cancels. -/
theorem derivedTensorMonoidalIso_symm_trans (T T' : DerivedTensorProduct R) :
    (derivedTensorMonoidalIso R T).symm ≪≫ derivedTensorMonoidalIso R T' = tensorIso R T T' := by
  rw [derivedTensorMonoidalIso, derivedTensorMonoidalIso, Iso.trans_symm, Iso.trans_assoc,
    ← Iso.trans_assoc (derivedTensorBifunctorIso R).symm, Iso.symm_self_id, Iso.refl_trans,
    tensorIso]

/-- **The comparison is compatible with the associativity constraints** of [Stacks, Tag 0FPT]:
the threefold square relating `(K ⊗^L L) ⊗^L M ≅ K ⊗^L (L ⊗^L M)` for the two derived tensor
products commutes. -/
theorem tensorIso_hom_app_app_comp_associator (T T' : DerivedTensorProduct R)
    (K L M : DerivedModules R) :
    ((tensorIso R T T').hom.app ((T.tensor.obj K).obj L)).app M ≫
        (T'.tensor.map (((tensorIso R T T').hom.app K).app L)).app M ≫
        (derivedTensorAssociator R T' K L M).hom =
      (derivedTensorAssociator R T K L M).hom ≫
        ((tensorIso R T T').hom.app K).app ((T.tensor.obj L).obj M) ≫
        (T'.tensor.obj K).map (((tensorIso R T T').hom.app L).app M) := by
  have hcomp : ∀ A B : DerivedModules R,
      ((tensorIso R T T').hom.app A).app B =
        (@reseatIso (DerivedModules R) _ (derivedMonoidal R) T.tensor
            (derivedTensorMonoidalIso R T) A B).inv ≫
          (@reseatIso (DerivedModules R) _ (derivedMonoidal R) T'.tensor
            (derivedTensorMonoidalIso R T') A B).hom := by
    intro A B
    rw [← derivedTensorMonoidalIso_symm_trans]
    rfl
  exact @reseat_associator_comparison (DerivedModules R) _ (derivedMonoidal R) T.tensor T'.tensor
    _ _ (derivedTensorMonoidalIso R T) (derivedTensorMonoidalIso R T') (canonicalUnitIso R)
    (canonicalUnitIso R) (tensorIso R T T') hcomp K L M

end OverAStructureSheaf

/-! ### The commutativity and unit constraints -/

section Constraints

attribute [local instance 100000] HasDerivedCategory.standard

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The comparison is compatible with the commutativity constraints** of [Stacks, Tag 0FPT]:
`A ⊗^L B ≅ B ⊗^L A` for one derived tensor product goes over to the same for the other. -/
theorem tensorIso_hom_app_app_comp_braidingIso (T T' : DerivedTensorProduct X.O)
    (A B : DerivedModules X.O) :
    ((tensorIso X.O T T').hom.app A).app B ≫ (T'.braidingIso X A B).hom =
      (T.braidingIso X A B).hom ≫ ((tensorIso X.O T T').hom.app B).app A := by
  have h₁ := tensorIso_hom_app_app_comp_comparison X.O T T' (X.kFlatModel A) (X.kFlatModel B)
    (X.isKFlat_kFlatModel A) (X.isKFlat_kFlatModel B)
  have h₂ := comparison_inv_comp_tensorIso_hom_app_app X.O T T' (X.kFlatModel B)
    (X.kFlatModel A) (X.isKFlat_kFlatModel B) (X.isKFlat_kFlatModel A)
  simp only [braidingIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_inv,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [← NatTrans.naturality_app_assoc, ← NatTrans.app_naturality_assoc, reassoc_of% h₁,
    ← reassoc_of% h₂, ← NatTrans.app_naturality_assoc, ← NatTrans.naturality_app]

/-- **The comparison is compatible with the unit constraints on the right** of
[Stacks, Tag 0FPT]: the two identifications of `A ⊗^L 𝒪` with `A` agree. -/
theorem tensorIso_hom_app_app_comp_rightUnitIso (T T' : DerivedTensorProduct X.O)
    (A : DerivedModules X.O) :
    ((tensorIso X.O T T').hom.app A).app (unitObject X) ≫ (T'.rightUnitIso X A).hom =
      (T.rightUnitIso X A).hom := by
  have h : ((tensorIso X.O T T').hom.app (DerivedCategory.Q.obj (X.kFlatModel A))).app
        (unitObject X) ≫
        (T'.comparisonRight (X.kFlatModel A) (unitComplex X)
          (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom =
      (T.comparisonRight (X.kFlatModel A) (unitComplex X)
        (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom :=
    tensorIso_hom_app_app_comp_comparisonRight X.O T T' (X.kFlatModel A)
      (unitComplex X) (Stacks.SheafOfModules.isKFlat_single_unit X.O)
  simp only [rightUnitIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_inv,
    Functor.mapIso_hom]
  rw [← NatTrans.naturality_app_assoc, reassoc_of% h]

/-- **The comparison is compatible with the unit constraints on the left** of
[Stacks, Tag 0FPT]: the two identifications of `𝒪 ⊗^L A` with `A` agree.  This is the two
preceding compatibilities, the left unit constraint being the right one read through the
commutativity constraint. -/
theorem tensorIso_hom_app_app_comp_leftUnitIso (T T' : DerivedTensorProduct X.O)
    (A : DerivedModules X.O) :
    ((tensorIso X.O T T').hom.app (unitObject X)).app A ≫ (T'.leftUnitIso X A).hom =
      (T.leftUnitIso X A).hom := by
  simp only [leftUnitIso, Iso.trans_hom]
  rw [reassoc_of% (tensorIso_hom_app_app_comp_braidingIso X T T' (unitObject X) A),
    tensorIso_hom_app_app_comp_rightUnitIso]

end Constraints

end Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

/-! ### The two canonical derived tensor products of the library -/

namespace AlgebraicGeometry.RingedSite

open Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (Modules.{u, u, u} X)]

/-- **The bridge between the library's two canonical derived tensor products is the canonical
comparison of two derived tensor products over one structure sheaf**, at the site-indexed
canonical one read through `derivedTensorProductDatumOfSite` and the sheaf-indexed canonical
one.  So every compatibility proved above holds of it. -/
theorem derivedTensorFunctorIso_eq_tensorIso :
    derivedTensorFunctorIso.{u, d} X =
      tensorIso X.O
        (derivedTensorProductDatumOfSite X
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X))
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O) :=
  rfl

/-- **On a pair of K-flat complexes the bridge is the two K-flat comparisons.** -/
theorem derivedTensorObjIso_hom (K L : CochainComplex (Modules.{u, u, u} X) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat X.O K) (hL : Stacks.SheafOfModules.IsKFlat X.O L) :
    (derivedTensorObjIso.{u, d} X (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X).comparison
          K L hK hL).hom ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
          K L hK hL).inv :=
  tensorIso_hom_app_app X.O _ _ K L hK hL

/-- **The bridge carries the K-flat comparison of one canonical derived tensor product to that
of the other.** -/
theorem derivedTensorObjIso_hom_comp_comparison (K L : CochainComplex (Modules.{u, u, u} X) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat X.O K) (hL : Stacks.SheafOfModules.IsKFlat X.O L) :
    (derivedTensorObjIso.{u, d} X (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
          K L hK hL).hom =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X).comparison
        K L hK hL).hom :=
  tensorIso_hom_app_app_comp_comparison X.O _ _ K L hK hL

/-- **The bridge is compatible with the canonical maps to the ordinary total tensor complex**,
at an arbitrary pair of complexes.  This is the compatibility that identifies the two bifunctors
as the *derived* tensor product and not merely as isomorphic bifunctors. -/
theorem derivedTensorObjIso_hom_comp_toTensor (K L : CochainComplex (Modules.{u, u, u} X) ℤ) :
    (derivedTensorObjIso.{u, d} X (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor K L =
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X).toTensor K L :=
  tensorIso_hom_app_app_comp_toTensor X.O _ _ K L

/-- **The bridge is compatible with the right one-sided K-flat comparisons.** -/
theorem derivedTensorObjIso_hom_comp_comparisonRight
    (K L : CochainComplex (Modules.{u, u, u} X) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) :
    (derivedTensorObjIso.{u, d} X (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparisonRight
          K L hL).hom =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X).comparisonRight
        K L hL).hom :=
  tensorIso_hom_app_app_comp_comparisonRight X.O _ _ K L hL

/-- **The bridge is compatible with the left one-sided K-flat comparisons.** -/
theorem derivedTensorObjIso_hom_comp_comparisonLeft
    (K L : CochainComplex (Modules.{u, u, u} X) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat X.O K) :
    (derivedTensorObjIso.{u, d} X (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparisonLeft
          K L hK).hom =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X).comparisonLeft
        K L hK).hom :=
  tensorIso_hom_app_app_comp_comparisonLeft X.O _ _ K L hK

/-- **The bridge is compatible with the associativity constraints** of [Stacks, Tag 0FPT]: the
associator of `Stacks.SheafOfModules.DerivedTensorProduct` at the site-indexed canonical derived
tensor product goes over to `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator` at
the sheaf-indexed one. -/
theorem derivedTensorObjIso_hom_comp_associator (K L M : DerivedModules.{u, u, u, d} X) :
    (derivedTensorObjIso.{u, d} X
        (((Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X).obj K).obj L) M).hom ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).map
          (derivedTensorObjIso.{u, d} X K L).hom).app M ≫
        (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator X.O
          (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O) K L M).hom =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X).associator K L M).hom ≫
        (derivedTensorObjIso.{u, d} X K
          (((Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X).obj L).obj M)).hom ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).obj K).map
          (derivedTensorObjIso.{u, d} X L M).hom :=
  tensorIso_hom_app_app_comp_associator X.O _ _ K L M

end AlgebraicGeometry.RingedSite

end
