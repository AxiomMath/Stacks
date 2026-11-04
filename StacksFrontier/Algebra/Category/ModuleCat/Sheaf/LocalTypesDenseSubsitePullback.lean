module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderSpecialCocontinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentRestrictScalars
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentRestrictScalars
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposReplacement

/-!
# Local types of modules under the pullback along a dense subsite inclusion

Let `w : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)`.  The morphism of topoi it
induces is an equivalence (Stacks 03A0), and together with a structure map it is a morphism of
ringed topoi `(Sh(C), O_C) ⟶ (Sh(D), O_D)`.  This file identifies the pullback of sheaves of
modules along that morphism with the restriction of modules along `w`, up to restriction of
scalars, and carries the five clauses 03DL (1), (2), (3), (6) and (8) across it.

These are the two vertical arrows of the square of Stacks 03CR, which is how Stacks 03DO reduces
its clauses for an arbitrary morphism of ringed topoi to the case of a morphism of ringed sites
presented by a left exact continuous functor; the clause (8) travels along these two arrows only,
Stacks 03DO having no coherence clause to reduce, and it reaches an arbitrary equivalence of
ringed topoi through the *one-sided* factorization instead.  Stacks 03DM is stated for the
restriction of modules, which is the functor of *sites*; what the reduction consumes is the
pullback along the morphism of ringed *topoi*, and the identification of the two is what this file
supplies.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.ofDenseSubsite`: the morphism of ringed topoi induced by a
  dense subsite inclusion together with a structure map.
* `AlgebraicGeometry.RingedToposHom.pullbackModulesIsoModuleRestriction`: **the pullback of
  modules along it is the restriction of modules along the inclusion, up to restriction of
  scalars twice.**

## Main results

* `AlgebraicGeometry.RingedToposHom.isLocallyFreeOnSite_pullbackModules_ofDenseSubsite`,
  `.isFiniteLocallyFreeOnSite_pullbackModules_ofDenseSubsite`,
  `.isLocallyGeneratedBySectionsOnSite_pullbackModules_ofDenseSubsite`,
  `.isQuasicoherentOnSite_pullbackModules_ofDenseSubsite` and
  `.isCoherentOnSite_pullbackModules_ofDenseSubsite`: **the clauses 03DL (1), (2), (3), (6) and
  (8) are carried by the pullback of modules along a dense subsite inclusion.**

## Implementation notes

The structure map is required to be invertible only in its inverse-image form
`f⁻¹O_D ⟶ O_C`, which is what extension of scalars runs on; for the morphisms Stacks 03CR
produces the direct-image form is the identity, and the inverse-image form is then the counit of
an equivalence of topoi.

Each clause is one application of Stacks 03DM followed by two applications of the invariance of
that clause under restriction of scalars along an isomorphism of sheaves of rings
(`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentRestrictScalars`) and one of its
invariance under an isomorphism of sheaves of modules
(`StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesIsoInvariance`).  The two restrictions of
scalars are kept separate rather than composed into one: the clauses are then carried by two
applications of one lemma, and no comparison of iterated restrictions of scalars is needed.

Every factor of the chain is given explicitly rather than left to unification.  The instance
`IsIso` of the inverse of the structure map is not found when the module and the sheaf of rings
are still metavariables, which is what happens if the module argument of the invariance lemma is
left to be inferred from the expected type.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom

universe u

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})] [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (w : X.C ⥤ Y.C) [w.IsDenseSubsite X.J Y.J]

/-- **The morphism of ringed topoi induced by a dense subsite inclusion**, with a prescribed
structure map.  Its underlying morphism of topoi is the equivalence of Stacks 03A0 attached to
the inclusion, and the structure map is the argument; Stacks 03CR produces its two vertical
arrows in exactly this shape, with the identity as structure map. -/
noncomputable def ofDenseSubsite
    (φ : Y.O ⟶ (pushforwardCommRingFunctor
      (Functor.IsDenseSubsite.morphismOfTopoi X.J Y.J w)).obj X.O) :
    RingedToposHom X Y where
  toToposHom := Functor.IsDenseSubsite.morphismOfTopoi X.J Y.J w
  fSharp := φ

open Stacks.Sheaves.RingedToposModules.RingedToposHom
  (extendScalarsFSharpIsoRestrictScalarsOfIsIso) in
/-- **The pullback of sheaves of modules along a dense subsite inclusion is the restriction of
modules along the inclusion, up to restriction of scalars twice.**  This is the identification
Stacks 03DM is stated across and Stacks 03DO consumes.

The pullback of Stacks 03D6 is the inverse image of Stacks 03D2 followed by extension of
scalars along the structure map.  Its geometric factor is restriction of sections along the
functor, which is `Stacks.Sheaves.ToposPullback.restrictionModuleIso`, the inverse image of a
morphism of topoi induced by a dense subsite inclusion being restriction on the nose; and its
scalar factor collapses, the structure map being invertible, to restriction of scalars along the
inverse, which is
`Stacks.Sheaves.RingedToposModules.RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso`.
No comparison of the development's two notions of a morphism of ringed topoi is needed: the
pullback of `AlgebraicGeometry.RingedToposHom` is by definition the modules development's
pullback along `AlgebraicGeometry.RingedToposHom.toModulesHom`. -/
noncomputable def pullbackModulesIsoModuleRestriction
    (φ : Y.O ⟶ (pushforwardCommRingFunctor
      (Functor.IsDenseSubsite.morphismOfTopoi X.J Y.J w)).obj X.O)
    [IsIso (ofDenseSubsite w φ).fSharpInverseImage] :
    ((ofDenseSubsite w φ).toModulesHom.pullbackModules) ≅
      (Stacks.DenseSubsiteModules.moduleRestriction X.J Y.J w
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
          SheafOfModules.restrictScalars
            (restrictionRingIso X.J Y.J w (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).hom) ⋙
        SheafOfModules.restrictScalars
          (asIso (ofDenseSubsite w φ).toModulesHom.fSharpInverseImage).inv :=
  Functor.isoWhiskerRight
      (restrictionModuleIso X.J Y.J w (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (Stacks.Sheaves.RingedToposModules.extendScalarsFSharp
        (ofDenseSubsite w φ).toModulesHom) ≪≫
    Functor.isoWhiskerLeft _
      (extendScalarsFSharpIsoRestrictScalarsOfIsIso (ofDenseSubsite w φ).toModulesHom)

section Transport

variable [w.IsCocontinuous X.J Y.J]
  [∀ (U : X.C) (Z : (Over (w.obj U))ᵒᵖ),
    HasLimitsOfShape (StructuredArrow Z (Over.post (X := U) w).op) AddCommGrpCat.{u}]
  [∀ V : Y.C, HasWeakSheafify (Y.J.over V) AddCommGrpCat.{u}]
  [∀ V : Y.C, (Y.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Local freeness is carried by the pullback of modules along a dense subsite inclusion.**
This is Stacks 03DL (1) along the equivalence of ringed topoi that Stacks 03CR produces: the
clause travels along the restriction of modules by Stacks 03DM, then across the two restrictions
of scalars of
`AlgebraicGeometry.RingedToposHom.pullbackModulesIsoModuleRestriction`, and finally across that
isomorphism itself. -/
theorem isLocallyFreeOnSite_pullbackModules_ofDenseSubsite
    (φ : Y.O ⟶ (pushforwardCommRingFunctor
      (Functor.IsDenseSubsite.morphismOfTopoi X.J Y.J w)).obj X.O)
    [IsIso (ofDenseSubsite w φ).fSharpInverseImage]
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : F.IsLocallyFreeOnSite) :
    (((ofDenseSubsite w φ).toModulesHom.pullbackModules).obj F).IsLocallyFreeOnSite := by
  have _ : IsIso (asIso (ofDenseSubsite w φ).toModulesHom.fSharpInverseImage).inv :=
    Iso.isIso_inv _
  exact Stacks.SheafOfModules.Intrinsic.isLocallyFreeOnSite_of_iso
    ((pullbackModulesIsoModuleRestriction w φ).app F).symm
    (Stacks.SheafOfModules.isLocallyFreeOnSite_restrictScalars_of_isIso
      (asIso (ofDenseSubsite w φ).toModulesHom.fSharpInverseImage).inv _
      (Stacks.SheafOfModules.isLocallyFreeOnSite_restrictScalars_of_isIso
        (restrictionRingIso X.J Y.J w (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).hom _
        ((Stacks.Sheaves.SpecialCocontinuous.isLocallyFreeOnSite_iff X.J Y.J w
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F).1 hF)))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Finite local freeness is carried by the pullback of modules along a dense subsite
inclusion.**  This is Stacks 03DL (2) along the equivalence of ringed topoi of Stacks 03CR; the
rank on each member of the covering is unchanged throughout. -/
theorem isFiniteLocallyFreeOnSite_pullbackModules_ofDenseSubsite
    (φ : Y.O ⟶ (pushforwardCommRingFunctor
      (Functor.IsDenseSubsite.morphismOfTopoi X.J Y.J w)).obj X.O)
    [IsIso (ofDenseSubsite w φ).fSharpInverseImage]
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : F.IsFiniteLocallyFreeOnSite) :
    (((ofDenseSubsite w φ).toModulesHom.pullbackModules).obj F).IsFiniteLocallyFreeOnSite := by
  have _ : IsIso (asIso (ofDenseSubsite w φ).toModulesHom.fSharpInverseImage).inv :=
    Iso.isIso_inv _
  exact Stacks.SheafOfModules.Intrinsic.isFiniteLocallyFreeOnSite_of_iso
    ((pullbackModulesIsoModuleRestriction w φ).app F).symm
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_restrictScalars_of_isIso
      (asIso (ofDenseSubsite w φ).toModulesHom.fSharpInverseImage).inv _
      (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_restrictScalars_of_isIso
        (restrictionRingIso X.J Y.J w (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).hom _
        ((Stacks.Sheaves.SpecialCocontinuous.isFiniteLocallyFreeOnSite_iff X.J Y.J w
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F).1 hF)))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- **Local generation by sections is carried by the pullback of modules along a dense subsite
inclusion.**  This is Stacks 03DL (3) along the equivalence of ringed topoi of Stacks 03CR; the
index type of the generating family is unchanged throughout. -/
theorem isLocallyGeneratedBySectionsOnSite_pullbackModules_ofDenseSubsite
    (φ : Y.O ⟶ (pushforwardCommRingFunctor
      (Functor.IsDenseSubsite.morphismOfTopoi X.J Y.J w)).obj X.O)
    [IsIso (ofDenseSubsite w φ).fSharpInverseImage]
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : F.IsLocallyGeneratedBySectionsOnSite) :
    (((ofDenseSubsite w φ).toModulesHom.pullbackModules).obj
      F).IsLocallyGeneratedBySectionsOnSite := by
  have _ : IsIso (asIso (ofDenseSubsite w φ).toModulesHom.fSharpInverseImage).inv :=
    Iso.isIso_inv _
  exact Stacks.SheafOfModules.Intrinsic.isLocallyGeneratedBySectionsOnSite_of_iso
    ((pullbackModulesIsoModuleRestriction w φ).app F).symm
    (Stacks.SheafOfModules.isLocallyGeneratedBySectionsOnSite_restrictScalars_of_isIso
      (asIso (ofDenseSubsite w φ).toModulesHom.fSharpInverseImage).inv _
      (Stacks.SheafOfModules.isLocallyGeneratedBySectionsOnSite_restrictScalars_of_isIso
        (restrictionRingIso X.J Y.J w (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).hom _
        ((Stacks.Sheaves.SpecialCocontinuous.isLocallyGeneratedBySectionsOnSite_iff X.J Y.J w
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F).1 hF)))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- **Quasi-coherence is carried by the pullback of modules along a dense subsite inclusion.**
This is Stacks 03DL (6) along the equivalence of ringed topoi of Stacks 03CR.  The slices of the
source site are asked to be essentially small in the universe of the module sections, which is
what Stacks 03DM's quasi-coherent clause needs in order to recover a quasi-coherent datum; the
sites of Stacks 03CR are small, so this is no restriction there. -/
theorem isQuasicoherentOnSite_pullbackModules_ofDenseSubsite
    [∀ Z : Y.Cᵒᵖ, HasLimitsOfShape (StructuredArrow Z w.op) AddCommGrpCat.{u}]
    [∀ W : X.C, EssentiallySmall.{u} (Over W)]
    (φ : Y.O ⟶ (pushforwardCommRingFunctor
      (Functor.IsDenseSubsite.morphismOfTopoi X.J Y.J w)).obj X.O)
    [IsIso (ofDenseSubsite w φ).fSharpInverseImage]
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : F.IsQuasicoherentOnSite) :
    (((ofDenseSubsite w φ).toModulesHom.pullbackModules).obj F).IsQuasicoherentOnSite := by
  have _ : IsIso (asIso (ofDenseSubsite w φ).toModulesHom.fSharpInverseImage).inv :=
    Iso.isIso_inv _
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((pullbackModulesIsoModuleRestriction w φ).app F).symm
    (Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso
      (asIso (ofDenseSubsite w φ).toModulesHom.fSharpInverseImage).inv _
      (Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso
        (restrictionRingIso X.J Y.J w (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).hom _
        ((Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff X.J Y.J w
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F).1 hF)))


omit [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [∀ (U : X.C) (Z : (Over (w.obj U))ᵒᵖ),
    HasLimitsOfShape (StructuredArrow Z (Over.post (X := U) w).op) AddCommGrpCat.{u}]
  [∀ V : Y.C, HasWeakSheafify (Y.J.over V) AddCommGrpCat.{u}]
  [∀ V : Y.C, (Y.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Coherence is carried by the pullback of modules along a dense subsite inclusion.**
This is Stacks 03DL (8) along the equivalence of ringed topoi of Stacks 03CR.  It is the one
clause of Stacks 03DL which is *not* carried by the pullback along an arbitrary morphism of
ringed topoi, so the dense subsite inclusions are the only sides of the square of Stacks 03CR it
travels along; see the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesToposPullback` for the
counterexample. -/
theorem isCoherentOnSite_pullbackModules_ofDenseSubsite
    (φ : Y.O ⟶ (pushforwardCommRingFunctor
      (Functor.IsDenseSubsite.morphismOfTopoi X.J Y.J w)).obj X.O)
    [IsIso (ofDenseSubsite w φ).fSharpInverseImage]
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : F.IsCoherentOnSite) :
    (((ofDenseSubsite w φ).toModulesHom.pullbackModules).obj F).IsCoherentOnSite := by
  have _ : IsIso (asIso (ofDenseSubsite w φ).toModulesHom.fSharpInverseImage).inv :=
    Iso.isIso_inv _
  exact Stacks.SheafOfModules.isCoherentOnSite_of_iso
    ((pullbackModulesIsoModuleRestriction w φ).app F).symm
    (Stacks.SheafOfModules.isCoherentOnSite_restrictScalars_of_isIso
      (asIso (ofDenseSubsite w φ).toModulesHom.fSharpInverseImage).inv _
      (Stacks.SheafOfModules.isCoherentOnSite_restrictScalars_of_isIso
        (restrictionRingIso X.J Y.J w (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).hom _
        ((Stacks.Sheaves.SpecialCocontinuous.isCoherentOnSite_iff X.J Y.J w
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F).1 hF)))

end Transport

end AlgebraicGeometry.RingedToposHom

end
