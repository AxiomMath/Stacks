module

public import Mathlib.CategoryTheory.Functor.Currying
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorEncodings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The tensor product of two quasi-coherent modules on a site is quasi-coherent

Let `(C, J)` be a site and let `𝒪` be a sheaf of commutative rings on it.  A sheaf of
`𝒪`-modules is quasi-coherent when every object of the site has a covering on whose members the
restricted module is the cokernel of a map between free modules.  This file proves that the
tensor product of two quasi-coherent sheaves of modules is again quasi-coherent, on an arbitrary
site.

This is part (5) of Stacks 06WV, the clause about an algebraic stack, and also part (2) of
Stacks 06WN.  The same statement for a ringed space is Stacks 01CE (3), already proved and
tagged in `StacksFrontier/CategoryTheory/Sites/Modules/TensorProduct/Basic.lean`; the proof carried
out here is the same one, with the intersection of two open covers replaced by a common
refinement of two coverings of a site: a quasi-coherent module is locally the cokernel of a map
between free modules, the tensor product of two such presentations presents the tensor product,
and presentations restrict along a morphism of the site.

## Main definitions

* `Stacks.SheafOfModules.TensorProduct.overRestrictionTensorPresheafIso`: the restriction to a
  localization of the objectwise tensor product of two presheaves of modules is the objectwise
  tensor product of their restrictions.
* `Stacks.SheafOfModules.TensorProduct.tensorSheafOverIso`: **the localization case of
  Stacks 03EL** — the restriction of a tensor product of sheaves of modules to a localization of
  the site is the tensor product formed on the localized site.
* `Stacks.SheafOfModules.TensorProduct.quasicoherentTensorBifunctor`: the tensor product as a
  bifunctor `QCoh(𝒪) × QCoh(𝒪) ⥤ QCoh(𝒪)`, which exists exactly because of the clause below,
  and `Stacks.SheafOfModules.TensorProduct.quasicoherentTensorBifunctorCompι`, which identifies
  it with the tensor product of `Mod(𝒪)` and so gives it that tensor product's universal
  property.

## Main results

* `Stacks.SheafOfModules.TensorProduct.coversTop_prod`: the objectwise binary products of two
  families covering the final object form a family covering the final object.  This is the
  common refinement of the two coverings.
* `Stacks.SheafOfModules.TensorProduct.quasicoherentDataTensor`,
  `Stacks.SheafOfModules.TensorProduct.isQuasicoherent_tensorSheaf` and
  `Stacks.SheafOfModules.TensorProduct.isQuasicoherent_tensorObj`: the clause of
  **Stacks 06WV (5)** for Mathlib's `SheafOfModules.IsQuasicoherent`, on an arbitrary site, for
  the two descriptions of the tensor product of sheaves of modules which the development
  carries — the sheafified objectwise tensor product and the tensor product of the monoidal
  category `Mod(𝒪)`.
* `Stacks.SheafOfModules.TensorProduct.isQuasicoherentOnSite_tensorSheaf`,
  `…isQuasicoherentOnSite_tensorObj` and `…quasicoherentOnSiteTensorBifunctor`: the tensor
  clause of **Stacks 06WV (5)** and of **Stacks 06WN (2)** for
  `SheafOfModules.IsQuasicoherentOnSite`, the quasi-coherence of Stacks 03DL (6) that the
  `QCoh(𝒪_𝒳)` of Stacks 06WG is defined by — but **on a site satisfying the five hypotheses
  of that section, which the fibred fppf site of Stacks 06WG does not**.  Which of the five it
  does and does not satisfy is settled in
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Descent/FibredTensorHypotheses.lean`; the
  two it fails are the size hypothesis and binary products.  The big `τ`-site of a scheme, the
  site of Stacks 0GNC (5), fails the size hypothesis for the same reason.

## Implementation notes

The tensor product is `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, the sheafification
of the objectwise tensor product of the underlying presheaves of modules.

**Two quasi-coherence predicates, and which one carries the clause.** The source's `QCoh` is
Stacks 03DL (6), here `SheafOfModules.IsQuasicoherentOnSite`: for *every* object of the site a
covering on whose members the restricted module has a global presentation.  Mathlib's
`SheafOfModules.IsQuasicoherent` instead asks for one family covering the *final* object
carrying `SheafOfModules.Presentation`s.  Mathlib's implies the source's unconditionally
(`SheafOfModules.isQuasicoherentOnSite_of_isQuasicoherent`); the converse holds exactly when
`UnivLE.{max u v w, w}` — the index types of a global presentation lie in `Type (max u v w)`
whereas `SheafOfModules.free` is indexed by `Type w` — and is
`SheafOfModules.IsQuasicoherentOnSite.isQuasicoherent`.  So the statements proved first, for
Mathlib's predicate, carry a clause string qualified by the predicate, and the `…OnSite`
statements of the last section, which add that one size hypothesis, carry one qualified by the
site: the size hypothesis is false at the universes of the fibred fppf site of Stacks 06WG, and
`HasBinaryProducts` — used only to refine two coverings of the *final* object, which is what
Mathlib's predicate asks for and the source's does not — fails there too.

The three inputs that are not proved here are taken from the library rather than reproved:

* `Stacks.SheafOfModules.TensorProduct.tensorPresentation` tensors two global presentations.  Its
  mathematical content is right exactness of the tensor product in each variable, Stacks 05NB,
  and the identification of the tensor product of two free modules with a free module.
* `Stacks.SheafOfModules.LocalKernel.presentationOver` restricts a global presentation along a
  morphism of the site; it is where `CategoryTheory.Limits.HasPullbacks` is used, the restriction
  functor being a left adjoint only then.
* `PresheafOfModules.sheafificationOverIso` is the half of `tensorSheafOverIso` which says that
  restriction to a localization commutes with sheafification; the other half is the pointwise
  `overRestrictionTensorPresheafIso`.

The ringed-space case of the final result is `AlgebraicGeometry.tensorSheaf_isQuasicoherent`,
which refines the two open covers by intersecting them; `coversTop_prod` is the same step with
the intersection of opens replaced by a binary product in `C`, which is what makes the argument
work on an arbitrary site.  Over a ringed space the two agree, the product of two opens being
their intersection.

`overRestrictionTensorPresheafIso` is proved pointwise rather than as an identification of whole
structures, exactly as `AlgebraicGeometry.tensorPresheafRestrictionIso` is: over each object of
the localized site both sides are literally the same tensor product of modules, while the two
sides as structures reach their restriction maps by different routes.

## References

* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.SheafOfModules.TensorEncodings (isSheaf_structureRingPresheaf)

universe t v u w

namespace Stacks.SheafOfModules.TensorProduct

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Refinement

/-- **The common refinement of two coverings of the final object.**  If the families `X` and `Y`
both cover the final object of a site with binary products, so does the family of products
`X i ⨯ Y j`.  This is the step which, over a ringed space, intersects two open covers. -/
public theorem coversTop_prod [HasBinaryProducts C] {I K : Type*} (X : I → C) (Y : K → C)
    (hX : J.CoversTop X) (hY : J.CoversTop Y) :
    J.CoversTop (fun ij : I × K ↦ X ij.1 ⨯ Y ij.2) := by
  intro U
  refine J.superset_covering ?_ (J.intersection_covering (hX U) (hY U))
  rintro Z f ⟨hf, hg⟩
  obtain ⟨i, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp hf
  obtain ⟨k, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp hg
  exact (Sieve.mem_ofObjects_iff ..).mpr ⟨(i, k), ⟨prod.lift a b⟩⟩

end Refinement

section Localization

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (O : Sheaf J CommRingCat.{w})

/-- The restriction to the localization of the site at `V` of the objectwise tensor product of
two presheaves of modules is the objectwise tensor product of their restrictions.  Both sides are
the same tensor product of modules over each object of the localized site. -/
public noncomputable def overRestrictionTensorPresheafIso (V : C)
    (P Q : PresheafOfModules.{w} (TensorSheafification.structureRingPresheaf O.obj)) :
    (PresheafOfModules.overRestriction (Osharp := O) V).obj
        ((PresheafOfModules.tensorObj (O := O.obj) (P) (Q))) ≅
      (PresheafOfModules.tensorObj (O := (O.over V).obj)
        (((PresheafOfModules.overRestriction (Osharp := O) V).obj P))
        (((PresheafOfModules.overRestriction (Osharp := O) V).obj Q))) :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **The localization case of Stacks 03EL.**  The restriction to the localization of the site at
`V` of the tensor product of two sheaves of modules is the tensor product, formed on the
localized site, of their restrictions. -/
public noncomputable def tensorSheafOverIso (V : C)
    (F G : SheafOfModules.{w}
      (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O)))
    : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O.obj, Presheaf.isSheaf_of_isSheaf_comp _ (O.obj) (forget₂ CommRingCat RingCat)
          ((isSheaf_structureRingPresheaf O))⟩).obj (F)).obj (G))).over V ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(O.over V).obj, Presheaf.isSheaf_of_isSheaf_comp _ ((O.over V).obj)
          (forget₂ CommRingCat RingCat) ((isSheaf_structureRingPresheaf (O.over V)))⟩).obj
        ((F.over V))).obj ((G.over V))) :=
  PresheafOfModules.sheafificationOverIso (Osharp := O) V
      ((PresheafOfModules.tensorObj (O := O.obj) (F.val) (G.val))) ≪≫
    (PresheafOfModules.sheafification
      (𝟙 ((Sheaf.toRingCat J O).over V).obj)).mapIso
        (overRestrictionTensorPresheafIso O V F.val G.val)

end Localization

section Quasicoherent

variable [UnivLE.{max v u, w}] [HasPullbacks C] [HasBinaryProducts C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w})

/-- Quasi-coherent data for the tensor product of two sheaves of modules, assembled from
quasi-coherent data for each factor: the covering is the family of binary products of the two
coverings, and over a member of it both factors have a global presentation, so
`Stacks.SheafOfModules.TensorProduct.tensorPresentation` presents the tensor product. -/
@[ega "I 9.1.1" "more general"]
public noncomputable def quasicoherentDataTensor
    {F G : SheafOfModules.{w}
      (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O))}
    (qF : F.QuasicoherentData.{t}) (qG : G.QuasicoherentData.{t}) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O.obj, Presheaf.isSheaf_of_isSheaf_comp _ (O.obj) (forget₂ CommRingCat RingCat)
        ((isSheaf_structureRingPresheaf O))⟩).obj (F)).obj (G))).QuasicoherentData.{t}
    where
  I := qF.I × qG.I
  X ij := qF.X ij.1 ⨯ qG.X ij.2
  coversTop := coversTop_prod _ _ qF.coversTop qG.coversTop
  presentation ij :=
    letI e := (tensorSheafOverIso O (qF.X ij.1 ⨯ qG.X ij.2) F G).symm
    letI : IsIso e.hom := e.isIso_hom
    (tensorPresentation (O.over (qF.X ij.1 ⨯ qG.X ij.2)).obj
        (isSheaf_structureRingPresheaf (O.over (qF.X ij.1 ⨯ qG.X ij.2)))
        (LocalKernel.presentationOver prod.fst (qF.presentation ij.1))
        (LocalKernel.presentationOver prod.snd (qG.presentation ij.2))).ofIsIso e.hom

/-- **Stacks 06WV (5) for Mathlib's `SheafOfModules.IsQuasicoherent`**: the tensor product of
two quasi-coherent sheaves of modules on a site is quasi-coherent.  Quasi-coherence is a local
condition, and over a common refinement of the two coverings on which the factors are presented,
the tensored presentation presents the tensor product.

The quasi-coherence here is Mathlib's — a covering of the final object carrying
`SheafOfModules.Presentation`s — and *not* the `SheafOfModules.IsQuasicoherentOnSite` of
Stacks 03DL (6), which is the notion `QCoh(𝒪_𝒳)` of Stacks 06WG means; hence the qualified
clause string.  The clause for that notion is
`Stacks.SheafOfModules.TensorProduct.isQuasicoherentOnSite_tensorSheaf` below, which is this
statement plus `SheafOfModules.isQuasicoherent_iff_isQuasicoherentOnSite` and so carries one
further size hypothesis on the site.

This is also the site-level form of Stacks 01CE (3), which is a statement about a ringed space
and is tagged there, on `AlgebraicGeometry.tensorSheaf_isQuasicoherent` in
`StacksFrontier/CategoryTheory/Sites/Modules/TensorProduct/Basic.lean`. -/
@[stacks 06WV "tensor_product, for Mathlib's IsQuasicoherent, not 03DL(6)",
  ega "I 9.1.1" "more general",
  ega "IV 8.2.7" "case A = O_S"]
public instance isQuasicoherent_tensorSheaf
    (F G : SheafOfModules.{w}
      (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O)))
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O.obj, Presheaf.isSheaf_of_isSheaf_comp _ (O.obj) (forget₂ CommRingCat RingCat)
        ((isSheaf_structureRingPresheaf O))⟩).obj (F)).obj (G))).IsQuasicoherent :=
  (quasicoherentDataTensor O
    (SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := F)).some
    (SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := G)).some).isQuasicoherent

attribute [local instance] Stacks.SheafOfModules.monoidalCategory

/-- **Stacks 06WV (5) for Mathlib's `SheafOfModules.IsQuasicoherent`**, for the tensor product
of the monoidal category `Mod(𝒪)` itself: given quasi-coherent sheaves of modules `F` and `G`,
the tensor product `F ⊗_𝒪 G` formed in `Mod(𝒪)` is quasi-coherent.  This is the shape in which
the source states the clause;
`Stacks.SheafOfModules.TensorProduct.isQuasicoherent_tensorSheaf` is the same statement for the
explicit model of that tensor product as a sheafified objectwise tensor product, and the two
together are the covering set at this predicate, the development carrying both descriptions.
The same pair for the quasi-coherence of Stacks 03DL (6) is
`Stacks.SheafOfModules.TensorProduct.isQuasicoherentOnSite_tensorObj` and
`…isQuasicoherentOnSite_tensorSheaf`. -/
@[stacks 06WV "tensor_product, for Mathlib's IsQuasicoherent, not 03DL(6)",
  ega "I 9.1.1" "more general",
  ega "IV 8.2.7" "case A = O_S"]
public instance isQuasicoherent_tensorObj
    (F G : SheafOfModules.{w}
      (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O)))
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (MonoidalCategory.tensorObj F G).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent
      (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O))).prop_of_iso
    (Stacks.SheafOfModules.tensorObjIso O.obj (isSheaf_structureRingPresheaf O) F G).symm
    (isQuasicoherent_tensorSheaf O F G)

/-- **The tensor product as a bifunctor on quasi-coherent modules**, `QCoh(𝒪) × QCoh(𝒪) ⥤
QCoh(𝒪)`.  It is the restriction of the tensor product of `Mod(𝒪)` to the full subcategory of
quasi-coherent modules, and it exists exactly because that tensor product preserves
quasi-coherence, which is Stacks 06WV (5): a bifunctor valued in `QCoh(𝒪)` cannot be written
down before the clause is proved.  The quasi-coherence cutting out the subcategory is Mathlib's;
`Stacks.SheafOfModules.TensorProduct.quasicoherentOnSiteTensorBifunctor` is the same bifunctor
on the subcategory cut out by the quasi-coherence of Stacks 03DL (6), which is the category
`QCoh(𝒪_𝒳)` of Stacks 06WG. -/
@[stacks 06WV "tensor_product, for Mathlib's IsQuasicoherent, not 03DL(6)"]
public noncomputable def quasicoherentTensorBifunctor :
    (SheafOfModules.isQuasicoherent (TensorSheafification.structureSheaf O.obj
        (isSheaf_structureRingPresheaf O))).FullSubcategory ×
      (SheafOfModules.isQuasicoherent (TensorSheafification.structureSheaf O.obj
        (isSheaf_structureRingPresheaf O))).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent (TensorSheafification.structureSheaf O.obj
        (isSheaf_structureRingPresheaf O))).FullSubcategory :=
  ObjectProperty.lift _
    (Functor.prod (SheafOfModules.isQuasicoherent
          (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O))).ι
        (SheafOfModules.isQuasicoherent
          (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O))).ι ⋙
      Functor.uncurry.obj (MonoidalCategory.curriedTensor _))
    (fun X ↦ isQuasicoherent_tensorObj O X.1.obj X.2.obj)

/-- The bifunctor of `Stacks.SheafOfModules.TensorProduct.quasicoherentTensorBifunctor` is the
tensor product of `Mod(𝒪)`: the tensor product of two quasi-coherent modules formed in
`QCoh(𝒪)` is their tensor product in `Mod(𝒪)`.  So it carries that tensor product's universal
property — the bilinear one of Stacks 01CA — and no separate universal property has to be
constructed for `QCoh(𝒪)`. -/
public noncomputable def quasicoherentTensorBifunctorCompι :
    quasicoherentTensorBifunctor O ⋙ (SheafOfModules.isQuasicoherent
        (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O))).ι ≅
      Functor.prod (SheafOfModules.isQuasicoherent
          (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O))).ι
        (SheafOfModules.isQuasicoherent
          (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O))).ι ⋙
      Functor.uncurry.obj (MonoidalCategory.curriedTensor _) :=
  ObjectProperty.liftCompιIso _ _ _

section OnSite

variable [UnivLE.{max u v w, w}]

/-- **The tensor clause of Stacks 06WV (5) and of Stacks 06WN (2), for the quasi-coherence of
Stacks 03DL (6), on a site satisfying the hypotheses of this section**: the tensor product of
two sheaves of modules which are quasi-coherent in the sense of
`SheafOfModules.IsQuasicoherentOnSite` is again quasi-coherent in that sense.  That is the
quasi-coherence the notion `QCoh(𝒪_𝒳)` of Stacks 06WG is defined by, and not Mathlib's
predicate.

**The hypotheses of this section exclude the site of Stacks 06WG**, which is why both clause
strings say so.  Of the five, the fibred fppf site of a category fibred in groupoids over
`(Sch/S)_fppf` satisfies three and fails two; the two failures are
`AlgebraicGeometry.FibredSite.not_univLE_associatedSite`, the size hypothesis, which at that
site's universes reads `UnivLE.{u + 1, u}`, and
`AlgebraicGeometry.FibredSite.not_hasBinaryProducts_twoLabel`, binary products, which such a
category generally lacks for want of a final object.  See
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Descent/FibredTensorHypotheses.lean`, where
the five are settled one by one.  So this statement does not instantiate to the source's clause,
and the source's clause is not proved anywhere on this development.

The proof is the proof of
`Stacks.SheafOfModules.TensorProduct.isQuasicoherent_tensorSheaf` run through
`SheafOfModules.isQuasicoherent_iff_isQuasicoherentOnSite`, the identification of the two
predicates on a site whose objects and morphisms are small relative to the universe of the
sections — which is the extra hypothesis `UnivLE.{max u v w, w}` and the only thing separating
the two statements.  It is not removable: on a big site, whose objects live one universe above
its sections, the two predicates genuinely differ.

What is *not* asserted is the rest of Stacks 06WN (2), namely that the tensor products formed in
`Mod(𝒳_Zar, 𝒪)`, `Mod(𝒳_étale, 𝒪)` and `Mod(𝒪_𝒳)` agree.  Those are formed in different
categories, where sheafification is a different functor, so the agreement is not a consequence
of this statement and the comparison is not available; hence the qualified clause string, as in
`AlgebraicGeometry.FibredSite.colimits_quasicoherentModules_of_descent` for part (1). -/
@[stacks 06WV "tensor_product, not 06WG's site",
  stacks 06WN "tensor_product, not 06WG's site",
  ega "I 9.1.1" "more general"]
public instance isQuasicoherentOnSite_tensorSheaf
    (F G : SheafOfModules.{w}
      (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O)))
    [F.IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite] :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O.obj, Presheaf.isSheaf_of_isSheaf_comp _ (O.obj) (forget₂ CommRingCat RingCat)
        ((isSheaf_structureRingPresheaf O))⟩).obj (F)).obj (G))).IsQuasicoherentOnSite := by
  have hF : F.IsQuasicoherent := ‹F.IsQuasicoherentOnSite›.isQuasicoherent
  have hG : G.IsQuasicoherent := ‹G.IsQuasicoherentOnSite›.isQuasicoherent
  exact SheafOfModules.isQuasicoherentOnSite_of_isQuasicoherent _

/-- **The tensor clause of Stacks 06WV (5) and of Stacks 06WN (2), for the quasi-coherence of
Stacks 03DL (6)**, for the tensor product of the monoidal category `Mod(𝒪)` itself.  Together
with `Stacks.SheafOfModules.TensorProduct.isQuasicoherentOnSite_tensorSheaf` this is the
covering set of the clause at the source's predicate, the development carrying both
descriptions of the tensor product.

As there, the hypotheses of this section **exclude the fibred fppf site of Stacks 06WG**, by
`AlgebraicGeometry.FibredSite.not_univLE_associatedSite` and
`AlgebraicGeometry.FibredSite.not_hasBinaryProducts_twoLabel`; hence the qualified clause
strings. -/
@[stacks 06WV "tensor_product, not 06WG's site", stacks 06WN "tensor_product, not 06WG's site"]
public instance isQuasicoherentOnSite_tensorObj
    (F G : SheafOfModules.{w}
      (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O)))
    [F.IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite] :
    (MonoidalCategory.tensorObj F G).IsQuasicoherentOnSite :=
  (SheafOfModules.isQuasicoherentOnSite
      (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O))).prop_of_iso
    (Stacks.SheafOfModules.tensorObjIso O.obj (isSheaf_structureRingPresheaf O) F G).symm
    (isQuasicoherentOnSite_tensorSheaf O F G)

/-- **The tensor product as a bifunctor on the quasi-coherent modules of Stacks 03DL (6)**: the
restriction of the tensor product of `Mod(𝒪)` to the full subcategory cut out by that
quasi-coherence.  It exists exactly because that tensor product preserves that
quasi-coherence, which is the tensor clause of Stacks 06WV (5).

On the fibred fppf site of Stacks 06WG this subcategory is `QCoh(𝒪_𝒳)`
(`AlgebraicGeometry.FibredSite.quasicoherentModules`), but the hypotheses of this section do
not hold at that site — see
`AlgebraicGeometry.FibredSite.not_univLE_associatedSite` and
`AlgebraicGeometry.FibredSite.not_hasBinaryProducts_twoLabel` — so this bifunctor is not the
one the source asserts; hence the qualified clause strings. -/
@[stacks 06WV "tensor_product, not 06WG's site", stacks 06WN "tensor_product, not 06WG's site"]
public noncomputable def quasicoherentOnSiteTensorBifunctor :
    (SheafOfModules.isQuasicoherentOnSite (TensorSheafification.structureSheaf O.obj
        (isSheaf_structureRingPresheaf O))).FullSubcategory ×
      (SheafOfModules.isQuasicoherentOnSite (TensorSheafification.structureSheaf O.obj
        (isSheaf_structureRingPresheaf O))).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite (TensorSheafification.structureSheaf O.obj
        (isSheaf_structureRingPresheaf O))).FullSubcategory :=
  ObjectProperty.lift _
    (Functor.prod (SheafOfModules.isQuasicoherentOnSite
          (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O))).ι
        (SheafOfModules.isQuasicoherentOnSite
          (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O))).ι ⋙
      Functor.uncurry.obj (MonoidalCategory.curriedTensor _))
    (fun X ↦ isQuasicoherentOnSite_tensorObj O X.1.obj X.2.obj)

/-- The bifunctor of
`Stacks.SheafOfModules.TensorProduct.quasicoherentOnSiteTensorBifunctor` is the tensor product
of `Mod(𝒪)`, so it carries that tensor product's universal property and no separate one has to
be constructed for `QCoh(𝒪_𝒳)`. -/
public noncomputable def quasicoherentOnSiteTensorBifunctorCompι :
    quasicoherentOnSiteTensorBifunctor O ⋙ (SheafOfModules.isQuasicoherentOnSite
        (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O))).ι ≅
      Functor.prod (SheafOfModules.isQuasicoherentOnSite
          (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O))).ι
        (SheafOfModules.isQuasicoherentOnSite
          (TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf O))).ι ⋙
      Functor.uncurry.obj (MonoidalCategory.curriedTensor _) :=
  ObjectProperty.liftCompιIso _ _ _

end OnSite

end Quasicoherent

end Stacks.SheafOfModules.TensorProduct

end
