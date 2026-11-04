module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ZariskiRingedSiteOpenSlice
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherenceAlongAnExactFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Pseudo-coherence transported along an equivalence of ringed sites, and at an open slice

`AlgebraicGeometry.Scheme.zariskiOverRingedSiteHom` identifies the slice `X.zariskiRingedSite.over
V` of a scheme's Zariski ringed site at an open `V` with the Zariski ringed site of the open
subscheme `V`.  That identification is of *sites*; it does not by itself move a statement about
objects of the derived category of one across to the other.  This module moves
`AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom`.

## The general statement

`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse` is
the transport along an arbitrary equivalence of ringed sites, in the data of Mathlib's
`SheafOfModules.pushforwardPushforwardEquivalence`: an equivalence `e : D ≌ C` of the underlying
sites, continuous in both directions, together with structure maps `φ : O_D ⟶ e_* O_C` and
`ψ : O_C ⟶ (e^{-1})_* O_D` and their two compatibilities.  If `E` is an `m`-pseudo-coherent
object of `D(O_D)` then its transport along the inverse of the induced equivalence of categories
of sheaves of modules is an `m`-pseudo-coherent object of `D(O_C)`.

It is `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses` with
its five inputs supplied, and each of the five is recorded separately below.

* the **covering** is a hypothesis, because the statement is applied at a site where it is
  already available (`AlgebraicGeometry.Scheme.zariskiOver_coversTop`);
* the **slice factors** are the inverses of
  `Stacks.SheafOfModules.InternalHom.siteEquivModulesOver`, the equivalences of sheaves of
  modules on the slices induced by `e`; being inverses of equivalences they are exact with no
  argument, and additive because the pushforward of sheaves of modules is;
* the **localization square** is
  `AlgebraicGeometry.RingedSite.siteEquivModulesOverInverseSquare`, and it is `Iso.refl`: both
  sides are the pushforward along the same composite, because the slice structure maps of
  `Stacks.SheafOfModules.InternalHom.siteEquivPsiOver` are `ψ` whiskered along the slice
  projection;
* the **unit comparison** is
  `Stacks.SheafOfModules.InternalHom.siteEquivModulesOverInverseUnitIso`, built from
  `Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit` at the localized structure map exactly as
  Mathlib's `TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit` is built from the
  functor-direction comparison;
* **invertibility of `φ`** is a hypothesis.  It is what makes the localized structure maps
  invertible and so the unit comparison available; at the open slice it holds for the strongest
  possible reason, `φ` being the identity there.

Two general facts about the structure maps are proved on the way, and both are about `φ` alone.

* `Stacks.SheafOfModules.InternalHom.psiOfIso_eq`: **the inverse structure map is unique.**  If
  `φ` is invertible then any `ψ` satisfying the first compatibility equals
  `Stacks.SheafOfModules.InternalHom.psiOfIso φ` — that map was defined by cancelling `φ` off
  the first compatibility, so the compatibility determines it.
* `Stacks.SheafOfModules.InternalHom.unit_of_counit`: consequently **the second compatibility is
  automatic**, being `psiOfIso_unit` read through the uniqueness.  A consumer who has `φ`
  invertible and a `ψ` satisfying the first compatibility owes nothing further.

## The form a consumer uses

The transport above concludes about the *image* of a given object of `D(O_D)`, which is not the
shape a consumer meets: the locality reduction hands over an object of `D(O_C)` — the restriction
of a global object to the slice — and wants its pseudo-coherence.
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_pushforwardPushforwardEquivalence_functor`
is that shape, and the two are joined by cancelling the two actions on derived categories against
each other.  That cancellation,
`CategoryTheory.Equivalence.mapDerivedCategoryInverseFunctorObjIso`, is proved for an arbitrary
additive equivalence of abelian categories with derived categories: on a representative cochain
complex both actions are the degreewise ones
(`CategoryTheory.Functor.mapDerivedCategoryFactors`), and there the cancellation is the unit of
Mathlib's `CategoryTheory.Equivalence.mapHomologicalComplex`.  Pseudo-coherence is carried across
the resulting isomorphism by
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_iso`.

## Which `φ` at the open slice, and why it is not a second equivalence

The equivalence of module categories at the open slice is **Mathlib's**,
`AlgebraicGeometry.Scheme.Modules.overEquiv`, and no copy of it is made here.  That is a
statement with content, because the data it is built from is not the data one would guess:
Mathlib's structure maps are `(V.overPullbackSheafEquivOver.app R).inv` and
`(V.sheafRestrictSheafEquivOver.app R).inv`, neither of which is syntactically an identity.
The resolution is recorded as two declarations.

* `AlgebraicGeometry.Scheme.zariskiOverPhi`, Mathlib's `φ` at the open slice, **is the
  identity**: `TopologicalSpace.Opens.overPullbackSheafEquivOver` is `Iso.refl`, so its inverse
  at the structure sheaf is `𝟙`, and that is consistent with
  `AlgebraicGeometry.Scheme.zariskiOver_pushforward_ringSheaf`, by which the two sheaves of rings
  it compares are *equal*.
* `AlgebraicGeometry.Scheme.zariskiOver_modulesEquiv`: with that `φ` and
  with Mathlib's `ψ`, `SheafOfModules.pushforwardPushforwardEquivalence` **is**
  `AlgebraicGeometry.Scheme.Modules.overEquiv`.  The two compatibilities are propositions, so
  only the two structure maps carry data, and both agree.

What is *not* true is that Mathlib's `ψ` may be replaced by
`Stacks.SheafOfModules.InternalHom.psiOfIso` and the equivalence still obtained on the nose:
`psiOfIso` inverts `φ` through `CategoryTheory.inv`, which does not reduce to `𝟙` at an
identity.  The two are nevertheless *equal*, by `psiOfIso_eq` above, and that equality is what
`AlgebraicGeometry.Scheme.zariskiOverPsi_eq_psiOfIso` records and what supplies the second
compatibility at the open slice.  Choosing Mathlib's `ψ` rather than `psiOfIso` is what keeps the
equivalence Mathlib's own and the tree free of a second encoding of it.

## Main results

* `Stacks.SheafOfModules.InternalHom.psiOfIso_eq` and
  `Stacks.SheafOfModules.InternalHom.unit_of_counit`: uniqueness of the inverse structure map,
  and the second compatibility it gives for free.
* `AlgebraicGeometry.RingedSite.siteEquivModulesOverInverseSquare`: the localization square for
  the inverse transports.
* `CategoryTheory.Equivalence.mapDerivedCategoryInverseFunctorObjIso`: the two degreewise actions
  on derived categories of an equivalence of abelian categories cancel.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse`:
  **the transport of `m`-pseudo-coherence along an equivalence of ringed sites**, and
  `.isPseudoCoherentFrom_of_pushforwardPushforwardEquivalence_functor`, the same statement in the
  form a consumer uses.
* `AlgebraicGeometry.Scheme.zariskiOver_modulesEquiv`: the reconciliation of
  the structure-map data with Mathlib's `AlgebraicGeometry.Scheme.Modules.overEquiv`.
* `AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiOver_of_toScheme`: **the transport at the
  open slice.**  An `m`-pseudo-coherent object of `D(𝒪_V)` becomes, along
  `AlgebraicGeometry.Scheme.Modules.overEquiv`, an `m`-pseudo-coherent object of the derived
  category of the localized ringed site `X.zariskiRingedSite.over V`, which is the side the
  locality reduction Stacks 08FU (3)
  (`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general`) consumes.
* `AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiOver_of_modulesOverEquiv`: **the statement
  that joins the two sides.**  An object of the derived category of `X.zariskiRingedSite.over V`
  is `m`-pseudo-coherent as soon as its reading as a complex of `𝒪_V`-modules is; no transported
  object appears in either half, so it applies directly to the restriction `E|_V` that the
  locality reduction hands over.

## Implementation notes

The localized structure maps are invertible, and the localized unit comparison available, only
because `φ` is invertible; nothing here asks `ψ` to be.  The universes of the two ringed sites do
have to agree, because `Stacks.SheafOfModules.InternalHom.siteEquivModulesOver` is stated at a
single `RingedSite.{u, v, w}`; the slice of a scheme's Zariski ringed site has object universe
`max u u`, which is that universe, so the application below is not affected.

At the open slice the instance arguments are passed positionally rather than synthesized, for
the reason recorded at
`AlgebraicGeometry.Scheme.zariskiOver_isContinuous_symm_functor`: at an object universe spelled
`max u u` the synthesis of continuity inside these transports produces a stuck universe
constraint.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u v w dX dY

namespace CategoryTheory.Equivalence

/-- **The two degreewise actions on derived categories of an equivalence of abelian categories
cancel.**  For an additive equivalence `e : A ≌ B` of abelian categories with derived categories,
`e^{-1}` applied to `e` applied to an object of `D(A)` is that object.

A representative cochain complex is chosen; there both actions are the degreewise ones, by
`CategoryTheory.Functor.mapDerivedCategoryFactors`, and the cancellation is the unit of Mathlib's
`CategoryTheory.Equivalence.mapHomologicalComplex`, the equivalence of categories of complexes
that `e` induces. -/
def mapDerivedCategoryInverseFunctorObjIso {A : Type*} [Category* A] {B : Type*} [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{dX} A] [HasDerivedCategory.{dY} B]
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive] (K : DerivedCategory A) :
    e.inverse.mapDerivedCategory.obj (e.functor.mapDerivedCategory.obj K) ≅ K :=
  let P := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  e.inverse.mapDerivedCategory.mapIso (e.functor.mapDerivedCategory.mapIso eK.symm) ≪≫
    e.inverse.mapDerivedCategory.mapIso (e.functor.mapDerivedCategoryFactors.app P) ≪≫
    e.inverse.mapDerivedCategoryFactors.app
      ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≪≫
    DerivedCategory.Q.mapIso
      (((e.mapHomologicalComplex (ComplexShape.up ℤ)).unitIso.app P).symm) ≪≫ eK

end CategoryTheory.Equivalence

namespace Stacks.SheafOfModules.InternalHom

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous

variable {X Y : RingedSite.{u, v, w}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [hφ : IsIso φ]

/-- **The inverse structure map of an equivalence of ringed sites is unique.**  If `φ` is
invertible then any `ψ` satisfying the first compatibility is
`Stacks.SheafOfModules.InternalHom.psiOfIso`: that map is the first compatibility with `φ`
cancelled off it. -/
theorem psiOfIso_eq
    (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
      ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom) :
    psiOfIso eqv φ = ψ := by
  refine Sheaf.hom_ext ?_
  show Functor.whiskerRight (NatTrans.op eqv.counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ≫
      Functor.whiskerLeft eqv.inverse.op (inv φ.hom) = ψ.hom
  rw [H₁, Category.assoc, ← Functor.whiskerLeft_comp, IsIso.hom_inv_id,
    Functor.whiskerLeft_id']
  exact Category.comp_id _

/-- **For an invertible `φ`, the second compatibility follows from the first.**  The first
compatibility determines `ψ` to be `Stacks.SheafOfModules.InternalHom.psiOfIso`
(`psiOfIso_eq`), for which the second compatibility is `psiOfIso_unit`. -/
theorem unit_of_counit
    (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
      ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom) :
    φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
        𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj := by
  rw [← psiOfIso_eq eqv φ ψ H₁]
  exact psiOfIso_unit eqv φ

/-- The localized structure map at an object `W` is invertible when `φ` is: it is `φ` whiskered
along the slice projection, and sheaves of rings are a full subcategory of presheaves of
rings. -/
instance isIso_siteEquivPhiOver (W : Y.C) : IsIso (siteEquivPhiOver eqv φ W) := by
  rw [← isIso_iff_of_reflects_iso (siteEquivPhiOver eqv φ W)
    (sheafToPresheaf (Y.J.over W) RingCat.{w})]
  exact inferInstanceAs (IsIso (Functor.whiskerLeft (Over.forget W).op φ.hom))

variable
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

/-- **The equivalence of slice module categories carries the unit to the unit.**  On underlying
presheaves of abelian groups the comparison is the localized structure map, which is invertible
because `φ` is. -/
def siteEquivModulesOverFunctorUnitIso (W : Y.C) :
    (siteEquivModulesOver.{u, v, w, w} eqv φ ψ H₁ H₂ W).functor.obj
        (_root_.SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W))) ≅
      _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) :=
  letI := Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit (siteEquivPhiOver eqv φ W)
  (asIso (_root_.SheafOfModules.unitToPushforwardObjUnit
    (siteEquivPhiOver eqv φ W))).symm

/-- **The inverse of the equivalence of slice module categories carries the unit to the unit.**
This is `siteEquivModulesOverFunctorUnitIso` conjugated by the unit of the equivalence, exactly
as Mathlib's `TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit` is obtained from
`TopologicalSpace.Opens.sheafOfModulesEquivOverUnit`. -/
def siteEquivModulesOverInverseUnitIso (W : Y.C) :
    (siteEquivModulesOver.{u, v, w, w} eqv φ ψ H₁ H₂ W).inverse.obj
        (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ≅
      _root_.SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W)) :=
  (siteEquivModulesOver.{u, v, w, w} eqv φ ψ H₁ H₂ W).inverse.mapIso
      (siteEquivModulesOverFunctorUnitIso eqv φ ψ H₁ H₂ W).symm ≪≫
    ((siteEquivModulesOver.{u, v, w, w} eqv φ ψ H₁ H₂ W).unitIso.app _).symm

end Stacks.SheafOfModules.InternalHom

namespace AlgebraicGeometry.RingedSite

variable {X Y : RingedSite.{u, v, w}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

/-- The inverse of the equivalence of categories of sheaves of modules induced by an equivalence
of ringed sites is additive: it is a pushforward, and a pushforward acts on a morphism by acting
on its underlying map of presheaves. -/
instance pushforwardPushforwardEquivalence_inverse_additive :
    (SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂ :
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
        SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).inverse.Additive where
  map_add := by intros; rfl

/-- The equivalence of categories of sheaves of modules induced by an equivalence of ringed
sites is additive, for the same reason as
`pushforwardPushforwardEquivalence_inverse_additive`. -/
instance pushforwardPushforwardEquivalence_functor_additive :
    (SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂ :
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
        SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).functor.Additive where
  map_add := by intros; rfl

/-- The inverse of the equivalence of slice module categories is additive, for the same reason as
`pushforwardPushforwardEquivalence_inverse_additive`. -/
instance siteEquivModulesOver_inverse_additive (W : Y.C) :
    (Stacks.SheafOfModules.InternalHom.siteEquivModulesOver.{u, v, w, w}
      eqv φ ψ H₁ H₂ W).inverse.Additive where
  map_add := by intros; rfl

/-- **The localization square for the inverse transports.**  Restricting to the slice over `W`
and then transporting to the slice over `e(W)` is transporting and then restricting to the slice
over `e(W)`.

This holds on the nose, and that is the point of the presentation chosen in
`Stacks.SheafOfModules.InternalHom.siteEquivPsiOver`: both sides are the pushforward of sheaves
of modules along the functor `D/e(W) ⥤ C` sending an object over `e(W)` to its image under
`e^{-1}`, with structure map `ψ` read at the underlying object. -/
def siteEquivModulesOverInverseSquare (W : Y.C) :
    SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W ⋙
        (Stacks.SheafOfModules.InternalHom.siteEquivModulesOver.{u, v, w, w}
          eqv φ ψ H₁ H₂ W).inverse ≅
      SheafOfModules.pushforward.{w} ψ ⋙
        SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (eqv.functor.obj W) :=
  Iso.refl _

section Transfer

variable [hφ : IsIso φ]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **Pseudo-coherence transports along an equivalence of ringed sites.**  Let `e : D ≌ C` be an
equivalence of the underlying sites of two ringed sites, continuous in both directions, with
structure maps `φ : O_D ⟶ e_* O_C` and `ψ : O_C ⟶ (e^{-1})_* O_D` satisfying the two
compatibilities of `SheafOfModules.pushforwardPushforwardEquivalence`, and with `φ` invertible.
If `E` is an `m`-pseudo-coherent object of `D(O_D)` then its image under the inverse of the
induced equivalence of categories of sheaves of modules is `m`-pseudo-coherent.

This is `isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses`; the module documentation lists
where each of its five inputs comes from.  The covering of the final object of `C` by the images
`e(W)` is a hypothesis rather than a consequence of `e` being an equivalence, because at the use
site it is already available. -/
theorem isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse
    (hTop : X.J.CoversTop eqv.functor.obj)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (m : ℤ)
    (hE : Y.IsPseudoCoherentFrom E m) :
    X.IsPseudoCoherentFrom
      ((SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂ :
          SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
            SheafOfModules.{w}
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).inverse.mapDerivedCategory.obj E) m :=
  isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses eqv.functor
    (SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂ :
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
        SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).inverse
    (fun W => (Stacks.SheafOfModules.InternalHom.siteEquivModulesOver.{u, v, w, w}
      eqv φ ψ H₁ H₂ W).inverse)
    inferInstance inferInstance inferInstance
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
    inferInstance hTop
    (fun W => Stacks.SheafOfModules.InternalHom.siteEquivModulesOverInverseUnitIso
      eqv φ ψ H₁ H₂ W)
    (fun W => siteEquivModulesOverInverseSquare eqv φ ψ H₁ H₂ W) E m hE

/-- **Pseudo-coherence transports along an equivalence of ringed sites, in the form a consumer
uses.**  An object `F` of `D(O_C)` is `m`-pseudo-coherent as soon as its image under the induced
equivalence of categories of sheaves of modules is `m`-pseudo-coherent on `(D, O_D)`.

This is `isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse` with the two actions on
derived categories cancelled against each other
(`CategoryTheory.Equivalence.mapDerivedCategoryInverseFunctorObjIso`), pseudo-coherence being
invariant under isomorphism in the derived category
(`isPseudoCoherentFrom_of_iso`).  It is the form that applies to an object one already has on
`(C, O_C)` — the restriction of a global object to a slice, say — rather than to one produced by
the transport. -/
theorem isPseudoCoherentFrom_of_pushforwardPushforwardEquivalence_functor
    (hTop : X.J.CoversTop eqv.functor.obj)
    (F : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (hF : Y.IsPseudoCoherentFrom
      ((SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂ :
          SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
            SheafOfModules.{w}
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).functor.mapDerivedCategory.obj F) m) :
    X.IsPseudoCoherentFrom F m :=
  isPseudoCoherentFrom_of_iso X m
    (isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse eqv φ ψ H₁ H₂ hTop _ m hF)
    ((SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂ :
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
        SheafOfModules.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapDerivedCategoryInverseFunctorObjIso
      F).symm

end Transfer

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (V : X.Opens)

/-- **The structure map of the identification of the open slice is the identity.**  This is
Mathlib's `(V.overPullbackSheafEquivOver.app X.ringCatSheaf).inv`, which is an identity because
`TopologicalSpace.Opens.overPullbackSheafEquivOver` is `Iso.refl`; that it typechecks as an
identity at all is `AlgebraicGeometry.Scheme.zariskiOver_pushforward_ringSheaf`, by which its two
sides are equal sheaves of rings. -/
def zariskiOverPhi : (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.zariskiRingedSite.O) ⟶
    ((Opens.overEquivalence V).symm.functor.sheafPushforwardContinuous RingCat.{u}
      V.toScheme.zariskiRingedSite.J (X.zariskiRingedSite.over V).J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.zariskiRingedSite.over V).O) :=
  𝟙 _

/-- `AlgebraicGeometry.Scheme.zariskiOverPhi` is Mathlib's structure map. -/
theorem zariskiOverPhi_eq :
    zariskiOverPhi X V =
      (Iso.app (V.overPullbackSheafEquivOver (A := RingCat.{u})) X.ringCatSheaf).inv := rfl

/-- The inverse structure map of the identification of the open slice, Mathlib's
`(V.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv`.  Unlike `zariskiOverPhi` it is not an
identity: it restricts along the counit of the equivalence of sites, which is the comparison of
an open of the subspace `V` with the preimage of its image in `X`. -/
def zariskiOverPsi : (Stacks.SheafOfModules.Tensor.ringSheaf (X.zariskiRingedSite.over V).O) ⟶
    ((Opens.overEquivalence V).symm.inverse.sheafPushforwardContinuous RingCat.{u}
      (X.zariskiRingedSite.over V).J V.toScheme.zariskiRingedSite.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.zariskiRingedSite.O) :=
  (Iso.app (V.sheafRestrictSheafEquivOver (A := RingCat.{u})) X.ringCatSheaf).inv

/-- **The first compatibility of the two structure maps at the open slice.**  With `φ` the
identity it says that the inverse structure map *is* restriction along the counit, and it holds
definitionally. -/
theorem zariskiOverPhi_counit :
    Functor.whiskerRight (NatTrans.op (Opens.overEquivalence V).symm.counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.zariskiRingedSite.over V).O).obj =
      (zariskiOverPsi X V).hom ≫
        (Opens.overEquivalence V).symm.inverse.op.whiskerLeft (zariskiOverPhi X V).hom := rfl

/-- The structure map of the identification of the open slice is invertible, being the
identity. -/
instance isIso_zariskiOverPhi : IsIso (zariskiOverPhi X V) :=
  inferInstanceAs
    (IsIso (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.zariskiRingedSite.O)))

/-- **Mathlib's inverse structure map at the open slice is the one `φ` determines.**  This is
`Stacks.SheafOfModules.InternalHom.psiOfIso_eq` at the open slice; it is what supplies the second
compatibility below, and it is the reconciliation of the two spellings of the inverse structure
map that the identification can be built from. -/
theorem zariskiOverPsi_eq_psiOfIso :
    @Stacks.SheafOfModules.InternalHom.psiOfIso.{u, u, u} (X.zariskiRingedSite.over V)
        V.toScheme.zariskiRingedSite (Opens.overEquivalence V).symm
        (zariskiOver_isContinuous_symm_functor X V)
        (zariskiOver_isContinuous_symm_inverse X V) (zariskiOverPhi X V)
        (isIso_zariskiOverPhi X V) =
      zariskiOverPsi X V :=
  @Stacks.SheafOfModules.InternalHom.psiOfIso_eq.{u, u, u} (X.zariskiRingedSite.over V)
    V.toScheme.zariskiRingedSite (Opens.overEquivalence V).symm
    (zariskiOver_isContinuous_symm_functor X V)
    (zariskiOver_isContinuous_symm_inverse X V) (zariskiOverPhi X V)
    (isIso_zariskiOverPhi X V) (zariskiOverPsi X V) (zariskiOverPhi_counit X V)

/-- **The second compatibility of the two structure maps at the open slice.**  It is
`Stacks.SheafOfModules.InternalHom.unit_of_counit`: `φ` is invertible and the first compatibility
holds, which already determines `ψ` and the compatibility it satisfies. -/
theorem zariskiOverPhi_unit :
    (zariskiOverPhi X V).hom ≫
        (Opens.overEquivalence V).symm.functor.op.whiskerLeft (zariskiOverPsi X V).hom ≫
        Functor.whiskerRight (NatTrans.op (Opens.overEquivalence V).symm.unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.zariskiRingedSite.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.zariskiRingedSite.O).obj :=
  @Stacks.SheafOfModules.InternalHom.unit_of_counit.{u, u, u} (X.zariskiRingedSite.over V)
    V.toScheme.zariskiRingedSite (Opens.overEquivalence V).symm
    (zariskiOver_isContinuous_symm_functor X V)
    (zariskiOver_isContinuous_symm_inverse X V) (zariskiOverPhi X V)
    (isIso_zariskiOverPhi X V) (zariskiOverPsi X V) (zariskiOverPhi_counit X V)

/-- **The identification of the module categories at the open slice is Mathlib's.**  The
equivalence that the two structure maps above induce between sheaves of modules on the localized
ringed site `X.zariskiRingedSite.over V` and on the Zariski ringed site of the open subscheme `V`
*is* `AlgebraicGeometry.Scheme.Modules.overEquiv`.

Only the two structure maps carry data — the two compatibilities are propositions — and both
agree with Mathlib's: `AlgebraicGeometry.Scheme.zariskiOverPhi_eq` for the first and the
definition of `AlgebraicGeometry.Scheme.zariskiOverPsi` for the second.  So no second encoding of
this equivalence is introduced, and the transport below is a statement about Mathlib's. -/
theorem zariskiOver_modulesEquiv :
    @AlgebraicGeometry.RingedSite.modulesEquiv.{u} (X.zariskiRingedSite.over V)
        V.toScheme.zariskiRingedSite (Opens.overEquivalence V).symm
        (zariskiOver_isContinuous_symm_functor X V)
        (zariskiOver_isContinuous_symm_inverse X V)
        (zariskiOverPhi X V) (zariskiOverPsi X V)
        (zariskiOverPhi_counit X V) (zariskiOverPhi_unit X V) =
      Scheme.Modules.overEquiv V := rfl

variable
  [HasDerivedCategory.{dY}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.zariskiRingedSite.O))]
  [HasDerivedCategory.{dX}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.zariskiRingedSite.over V).O))]

/-- The inverse of Mathlib's identification of the two module categories is additive: it is a
pushforward of sheaves of modules, which acts on a morphism by acting on its underlying map of
presheaves.  This is
`AlgebraicGeometry.RingedSite.pushforwardPushforwardEquivalence_inverse_additive` at the open
slice, read through `AlgebraicGeometry.Scheme.zariskiOver_modulesEquiv`. -/
instance additive_modulesOverEquiv_inverse :
    (Scheme.Modules.overEquiv V).inverse.Additive where
  map_add := by intros; rfl

/-- Mathlib's identification of the two module categories is additive, for the same reason as
`AlgebraicGeometry.Scheme.additive_modulesOverEquiv_inverse`. -/
instance additive_modulesOverEquiv_functor :
    (Scheme.Modules.overEquiv V).functor.Additive where
  map_add := by intros; rfl

/-- Mathlib's category `AlgebraicGeometry.Scheme.Modules` of modules on the open subscheme `V`
*is* the category of sheaves of modules on its Zariski ringed site, by
`AlgebraicGeometry.Scheme.zariskiRingedSite_ringSheaf`; it is a definition and not an
abbreviation, so a derived-category model for one is not found by instance search at the
other. -/
local instance hasDerivedCategory_toScheme_modules :
    HasDerivedCategory.{dY} V.toScheme.Modules :=
  inferInstanceAs (HasDerivedCategory.{dY}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.zariskiRingedSite.O)))

/-- The sheaf of rings of the localized ringed site is `X.ringCatSheaf.over V`, by
`AlgebraicGeometry.Scheme.zariskiRingedSite_over_ringSheaf`; that is the spelling Mathlib's
identification of the two module categories is stated at, and `RingedSite.ringSheaf` does not
reduce to it at instance transparency. -/
local instance hasDerivedCategory_ringCatSheaf_over :
    HasDerivedCategory.{dX} (SheafOfModules.{u} (X.ringCatSheaf.over V)) :=
  inferInstanceAs (HasDerivedCategory.{dX}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.zariskiRingedSite.over V).O)))

/-- **Pseudo-coherence travels from the open subscheme to the open slice.**  If `E` is an
`m`-pseudo-coherent object of the derived category of `𝒪_V`-modules, then its image under the
inverse of `AlgebraicGeometry.Scheme.Modules.overEquiv` is an `m`-pseudo-coherent object of the
derived category of sheaves of modules on the localized ringed site `X.zariskiRingedSite.over V`.

This is the transport the locality reduction asks for.  Stacks 08FU (3),
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general`, reduces
`m`-pseudo-coherence of an object of `D(𝒪_X)` to `m`-pseudo-coherence of its restrictions on the
localized ringed sites `X.zariskiRingedSite.over V`, whereas the affine-chart statements that
discharge those are about the *scheme* `V` and so about `V.toScheme.zariskiRingedSite`.  This
carries one to the other.

It is `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse`
at the identification of ringed sites of
`AlgebraicGeometry.Scheme.zariskiOverRingedSiteHom`, whose covering hypothesis is
`AlgebraicGeometry.Scheme.zariskiOver_coversTop`. -/
theorem isPseudoCoherentFrom_zariskiOver_of_toScheme
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.zariskiRingedSite.O)))
    (m : ℤ)
    (hE : V.toScheme.zariskiRingedSite.IsPseudoCoherentFrom E m) :
    (X.zariskiRingedSite.over V).IsPseudoCoherentFrom
      ((Scheme.Modules.overEquiv V).inverse.mapDerivedCategory.obj E) m :=
  @AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse.{u,
      u, u, dX, dY} (X.zariskiRingedSite.over V) V.toScheme.zariskiRingedSite
    (Opens.overEquivalence V).symm
    (zariskiOver_isContinuous_symm_functor X V)
    (zariskiOver_isContinuous_symm_inverse X V)
    (zariskiOverPhi X V) (zariskiOverPsi X V)
    (zariskiOverPhi_counit X V) (zariskiOverPhi_unit X V)
    (isIso_zariskiOverPhi X V)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance
    (zariskiOver_coversTop X V) E m hE

/-- **Pseudo-coherence at the open slice is pseudo-coherence on the open subscheme**, in the form
the locality reduction consumes.  An object `F` of the derived category of the localized ringed
site `X.zariskiRingedSite.over V` is `m`-pseudo-coherent as soon as its reading as an object of
the derived category of `𝒪_V`-modules, along `AlgebraicGeometry.Scheme.Modules.overEquiv`, is
`m`-pseudo-coherent.

This is the statement that joins the two sides.  Stacks 08FU (3),
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general`, asks for
`m`-pseudo-coherence of the restriction `E|_V` *on* `X.zariskiRingedSite.over V`; taking `F` to be
that restriction, what has to be proved instead is `m`-pseudo-coherence of `E|_V` read as a
complex of `𝒪_V`-modules on the scheme `V`, which is what the affine-chart statements are about.
No transported object appears in either the hypothesis or the conclusion: the two actions on
derived categories have been cancelled
(`CategoryTheory.Equivalence.mapDerivedCategoryInverseFunctorObjIso`). -/
theorem isPseudoCoherentFrom_zariskiOver_of_modulesOverEquiv
    (F : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.zariskiRingedSite.over V).O)))
    (m : ℤ)
    (hF : V.toScheme.zariskiRingedSite.IsPseudoCoherentFrom
      ((Scheme.Modules.overEquiv V).functor.mapDerivedCategory.obj F) m) :
    (X.zariskiRingedSite.over V).IsPseudoCoherentFrom F m :=
  RingedSite.isPseudoCoherentFrom_of_iso.{u, u, u, dX} _ m
    (isPseudoCoherentFrom_zariskiOver_of_toScheme X V _ m hF)
    (@Equivalence.mapDerivedCategoryInverseFunctorObjIso.{dX, dY} _ _ _ _ _ _
      (hasDerivedCategory_ringCatSheaf_over.{u, dX} X V) _
      (Scheme.Modules.overEquiv V) _ _ F).symm

end AlgebraicGeometry.Scheme

end
