module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOnKFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import StacksCore.Tactic.StacksAttribute

/-!
# The derived pullback of the structure sheaf

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a morphism of
the underlying sites. This file identifies the derived pullback of the structure sheaf of the
target, placed in degree zero:

`Lf^*(𝒪_D[0]) ≅ (f^*𝒪_D)[0]`,

and composes that identification with the ordinary (underived) comparison
`f^*𝒪_D ⟶ 𝒪_C` of `SheafOfModules.pullbackObjUnitToUnit` to produce the canonical map

`Lf^*(𝒪_D[0]) ⟶ 𝒪_C[0]`.

The first identification is unconditional and is the content here: `𝒪_D[0]` is a K-flat complex
with flat terms, so the derived pullback is computed by the degreewise pullback, which on a
complex concentrated in degree zero is the degreewise pullback of that one module. The second
step is invertible exactly when the ordinary comparison is, and it always is
(`Stacks.Sheaves.DerivedPullback.isIso_pullbackObjUnitToUnit`), so the composite is an
isomorphism with no hypothesis beyond `f` being presented by a morphism of the underlying sites.

## Main definitions

* `derivedPullbackSingleUnitIso`: `Lf^*(𝒪_D[0]) ≅ (f^*𝒪_D)[0]`, unconditional.
* `derivedPullbackUnitMap`: the canonical map `Lf^*(𝒪_D[0]) ⟶ 𝒪_C[0]`, unconditional.
* `derivedPullbackUnitIsoOfIso`: the same map read as an isomorphism, from an *ordinary*
  isomorphism `f^*𝒪_D ≅ 𝒪_C` supplied by the caller.
* `derivedPullbackUnitIso`: the unit comparison `ν : Lf^*(𝒪_D[0]) ≅ 𝒪_C[0]`, unconditional.

## Main results

* `isFlat_single_unit_X`: the complex `𝒪_D[0]` has flat terms.
* `derivedPullbackUnitMap_eq`: the canonical map is `(𝒪_D[0] ↦ (f^*𝒪_D)[0])` followed by degree
  zero of the ordinary comparison. This is what makes the invertibility statement below a
  restatement of the ordinary one rather than new content.
* `derivedPullbackUnitIsoOfIso_hom`: the isomorphism above has `derivedPullbackUnitMap` as its
  underlying morphism when it is built from the ordinary comparison.
* `derivedPullbackUnitIso_hom`: the unit comparison has `derivedPullbackUnitMap` as its
  underlying morphism.
* `isIso_derivedPullbackUnitMap_unconditional`: **the canonical map is invertible**,
  unconditionally.
* `isIso_derivedPullbackUnitMap`: the canonical map is invertible as soon as the ordinary
  comparison is; a corollary of the previous one, kept for callers that supply the ordinary
  invertibility.

## Implementation notes

**What is new and what is imported.** The mathematics added is the first identification. The
two inputs it is assembled from are
`Stacks.Sheaves.DerivedPullback.flatPullbackIso` (Stacks 06YY: a K-flat complex with flat terms
computes the derived pullback) and `HomologicalComplex.singleMapHomologicalComplex` (an additive
functor commutes with placing an object in a degree). The flatness and K-flatness of `𝒪_D[0]`
come from `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit`,
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero` and
`Stacks.SheafOfModules.isKFlat_single_unit`; only the assembly of `isFlat_single_unit_X` out of
the first two is done here.

**Why the invertibility is unconditional.** `Lf^*` is applied to a complex in degree zero, so
`Lf^*(𝒪_D[0]) ≅ 𝒪_C[0]` holds if and only if `f^*𝒪_D ≅ 𝒪_C` does: the first identification above
is an isomorphism outright, so the two statements differ by nothing. Mathlib's `IsIso` instance
for `SheafOfModules.pullbackObjUnitToUnit` carries `CategoryTheory.Functor.Final` on the functor
presenting `f`, which is a hypothesis beyond Stacks 03LU's; but that instance is not the only
route. `Stacks.Sheaves.DerivedPullback.isIso_pullbackObjUnitToUnit` identifies the ordinary
comparison, after composition with an isomorphism, with the inverse of the 03LU
corepresentability isomorphism, and so proves it invertible outright.
`derivedPullbackUnitIsoOfIso` is kept stated against an ordinary isomorphism supplied by the
caller, and `derivedPullbackUnitIso` is that construction at Mathlib's comparison.

**The ringed site presenting the ringed topos.** `isFlat_unit` and `isFlat_of_isZero` are stated
for an `AlgebraicGeometry.RingedSite`, which carries the same three fields as an
`AlgebraicGeometry.RingedTopos`; they are used here at the ringed site built from those fields,
written out rather than going through `AlgebraicGeometry.RingedTopos.toRingedSite` so as not to
import the locally-ringed-sites development for a reassociation of three fields.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Sheaves.DerivedPullback

universe u

/-! ## The structure sheaf in degree zero is a K-flat complex with flat terms -/

section Flatness

variable (Y : RingedTopos.{u, u, u})
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The complex `𝒪[0]` has flat terms.** In degree zero the term is the structure sheaf,
which is flat by `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit`; in every other
degree it is a zero object, which is flat by
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero`. -/
theorem isFlat_single_unit_X (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).X i) := by
  by_cases h : i = 0
  · subst h
    exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso Y.O
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).symm
      (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
        (Y := ⟨Y.C, Y.J, Y.O⟩))
  · exact Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero
      (Y := ⟨Y.C, Y.J, Y.O⟩) _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i h)

end Flatness

/-! ## The derived pullback of the structure sheaf -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

/-- **The derived pullback of the structure sheaf in degree zero is the degreewise pullback of
the structure sheaf in degree zero**: `Lf^*(𝒪_D[0]) ≅ (f^*𝒪_D)[0]`.

The complex `𝒪_D[0]` is K-flat (`Stacks.SheafOfModules.isKFlat_single_unit`) with flat terms
(`isFlat_single_unit_X`), so `Stacks.Sheaves.DerivedPullback.flatPullbackIso` computes the
derived pullback by the degreewise pullback; and the degreewise pullback of a complex
concentrated in degree zero is the pullback of its one module placed in degree zero, by
`HomologicalComplex.singleMapHomologicalComplex`. -/
def derivedPullbackSingleUnitIso (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (f.pullbackTopos.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :=
  flatPullbackIso f hmos
      ((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
      (Stacks.SheafOfModules.isKFlat_single_unit Y.O) (isFlat_single_unit_X Y) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex f.pullbackTopos
          (ComplexShape.up ℤ) 0).app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))

/-- **The canonical map `Lf^*(𝒪_D[0]) ⟶ 𝒪_C[0]`.** It is `derivedPullbackSingleUnitIso`
followed by degree zero of the ordinary comparison `f^*𝒪_D ⟶ 𝒪_C`. -/
def derivedPullbackUnitMap (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ⟶
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (derivedPullbackSingleUnitIso f hmos).hom ≫
    (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
      (SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing)

/-- The canonical map is, by construction, the identification of `Lf^*(𝒪_D[0])` with
`(f^*𝒪_D)[0]` followed by degree zero of the ordinary comparison. -/
theorem derivedPullbackUnitMap_eq (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    derivedPullbackUnitMap f hmos =
      (derivedPullbackSingleUnitIso f hmos).hom ≫
        (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
          (SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing) :=
  rfl

/-- **The derived unit comparison `Lf^*(𝒪_D[0]) ≅ 𝒪_C[0]`**, built from an *ordinary*
isomorphism `f^*𝒪_D ≅ 𝒪_C`. Taking that isomorphism as an argument rather than synthesising it
is deliberate: the ordinary statement is exactly as strong as this one, and Mathlib's route to
it (`SheafOfModules.pullbackObjUnitToUnit`, invertible when the functor presenting `f` is
final) is the only one available. By `derivedPullbackUnitIsoOfIso_hom` the underlying morphism
is `derivedPullbackUnitMap` whenever the argument is Mathlib's comparison. -/
def derivedPullbackUnitIsoOfIso (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (e : f.pullbackTopos.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  derivedPullbackSingleUnitIso f hmos ≪≫
    (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).mapIso e

/-- The derived unit comparison is the canonical map, as soon as the ordinary isomorphism it is
built from is the ordinary comparison. -/
theorem derivedPullbackUnitIsoOfIso_hom (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (e : f.pullbackTopos.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (he : e.hom = SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing) :
    (derivedPullbackUnitIsoOfIso f hmos e).hom = derivedPullbackUnitMap f hmos := by
  rw [derivedPullbackUnitMap_eq, ← he]
  rfl

/-- **The derived unit comparison `ν : Lf^*(𝒪_D[0]) ≅ 𝒪_C[0]`, unconditionally.** Both legs of
`derivedPullbackUnitMap` are isomorphisms: the first by construction, the second because the
ordinary comparison `f^*𝒪_D ⟶ 𝒪_C` is invertible for any morphism of ringed topoi presented by a
morphism of the underlying sites
(`Stacks.Sheaves.DerivedPullback.isIso_pullbackObjUnitToUnit`). -/
def derivedPullbackUnitIso (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  derivedPullbackUnitIsoOfIso f hmos
    (@asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing)
      (isIso_pullbackObjUnitToUnit f hmos))

/-- The derived unit comparison has `derivedPullbackUnitMap` as its underlying morphism. -/
theorem derivedPullbackUnitIso_hom (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    (derivedPullbackUnitIso f hmos).hom = derivedPullbackUnitMap f hmos :=
  derivedPullbackUnitIsoOfIso_hom f hmos _ rfl

/-- **The canonical map `Lf^*(𝒪_D[0]) ⟶ 𝒪_C[0]` is invertible**, for any morphism of ringed topoi
presented by a morphism of the underlying sites. The first leg of the composite is an isomorphism
outright and the second is `Stacks.Sheaves.DerivedPullback.isIso_pullbackObjUnitToUnit`. -/
theorem isIso_derivedPullbackUnitMap_unconditional (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    IsIso (derivedPullbackUnitMap f hmos) := by
  rw [← derivedPullbackUnitIso_hom f hmos]
  infer_instance

/-- **The canonical map `Lf^*(𝒪_D[0]) ⟶ 𝒪_C[0]` is invertible as soon as the ordinary
comparison `f^*𝒪_D ⟶ 𝒪_C` is.** The first leg of the composite is an isomorphism outright, so
this is the ordinary statement read in the derived category and nothing more. The hypothesis is
passed positionally because the two sheaf-of-rings spellings make instance search miss it. It is
in fact never needed: `isIso_derivedPullbackUnitMap_unconditional` above drops it. -/
theorem isIso_derivedPullbackUnitMap (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (h : IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing)) :
    IsIso (derivedPullbackUnitMap f hmos) := by
  rw [← derivedPullbackUnitIsoOfIso_hom f hmos
    (@asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing) h) rfl]
  infer_instance

end Derived

end Stacks.Sheaves.DerivedPullback

end
