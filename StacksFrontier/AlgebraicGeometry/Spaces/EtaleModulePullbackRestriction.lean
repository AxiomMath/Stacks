module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleNatIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleInverseImageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleRestrictionRingSheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of modules along an étale morphism is étale restriction

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Stacks' Equation 03LW is the abuse of notation

`G|_{X_étale} = f^*G = f_{small}^{-1}G`

for an `𝒪_Y`-module `G`: the pullback of modules of Stacks 03LU, the inverse image of modules of
Stacks 03D2 and plain restriction of sections along small étale postcomposition with `f` all
agree.  The middle identification is
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModuleInverseImage`; this file supplies the outer
one, which is clause (2) of Stacks 03LV read through the restriction description of the inverse
image.

Restriction of sections is `AlgebraicGeometry.Space.etaleModulePullback`, a functor with no
tensor product and no sheafification in it: its sections over an étale chart `U` of `X` are the
sections of `G` over the composite chart of `Y`.  So the comparison below exhibits `f^*` as a
reindexing of sections.

## Main definitions

* `AlgebraicGeometry.Space.etaleInverseImageRestrictionRingMap` is the morphism
  `f⁻¹𝒪_Y ⟶ 𝒪_Y|_{X_étale}` of the two transported sheaves of rings over which the two
  descriptions of the pullback are indexed.
* `AlgebraicGeometry.Space.etaleModuleInverseImageIsoRestrictionTransport` reads the inverse
  image of modules as the transport of modules along étale restriction of sheaves of sets.
* `AlgebraicGeometry.Space.etaleRestrictionModuleTransportIso` identifies that transport, after
  restriction of scalars, with étale restriction of modules.
* `Stacks.Sheaves.RingedPoint.sheafRestrictScalarsComp₃IsoId` cancels three successive
  restrictions of scalars whose composite map of sheaves of rings is the identity.

## Main results

* `AlgebraicGeometry.Space.etaleInverseImageRestrictionRingMap_comp`: the ring-sheaf triangle —
  the comparison of the two transported sheaves of rings, followed by the identification of the
  transported structure sheaf with `𝒪_X`, is the inverse-image form of the structure map.
* `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`: **Stacks Equation 03LW**, that
  is clause (2) of **Stacks 03LV** — pullback of `𝒪_Y`-modules along an étale morphism is
  naturally isomorphic to étale restriction.
* `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app`: on sections the
  comparison is the inverse-image comparison of Stacks 03LQ and nothing further, so it is the
  canonical identification and not merely some natural isomorphism of the two functors.
* `AlgebraicGeometry.Space.forgetRing_fSharpInverseImage_eq_inverseImageIso`: on underlying
  sheaves of sets the inverse-image form of the structure map is the comparison of Stacks 03LQ
  at the structure sheaf.

## Implementation notes

The comparison is uniqueness of the topos inverse image plus transport of the ring and the
module structures.  Both halves of the étale identification are left adjoints of the same direct
image of sheaves of sets, so `AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso`
identifies them; `Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans` carries that
identification to the transported sheaves of rings and
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso` carries it to the transported
sheaves of modules.  What remains is the ring-sheaf triangle, proved on underlying sheaves of
sets, where the étale-restriction comparison is the identity
(`Stacks.Sheaves.ToposPullback.restrictionRingIso_hom_ringSheafMap`) and the structure map is the
comparison of Stacks 03LQ at the structure sheaf.

Three forms of the inverse-image structure map occur and have to be matched: the
`CommRingCat` form, the `RingCat` form along which scalars are extended, and the underlying
morphism of sheaves of sets.
`AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage` and
`AlgebraicGeometry.RingedToposHom.forgetRing_map_fSharpInverseImage` are the two bridges.
Neither can be used as a rewrite inside the goal: the intermediate goals are type-correct only
after unfolding the structure sheaf of a ringed topos, which `rw` refuses, so the comparison is
assembled from `Eq.trans` and `congrArg` on both sides of the faithful
`CategoryTheory.sheafCompose _ (CategoryTheory.forget RingCat)`.

Every intermediate functor is named with its type written out, and the three successive
restrictions of scalars are cancelled in one step by
`Stacks.Sheaves.RingedPoint.sheafRestrictScalarsComp₃IsoId` rather than by merging two of them
first: merging them is `SheafOfModules.restrictScalars_comp`, which holds by `Eq.refl` for
variable arguments but whose definitional check does not terminate at these concrete sheaves of
rings, so an `CategoryTheory.eqToIso` built from it blocks the sectionwise computation below.

## References

* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.RingedPoint

universe w vv uu

variable {T : Type uu} [Category.{vv} T] {J : GrothendieckTopology T}
  {O P Q : Sheaf J RingCat.{w}}

/-- Restricting a sheaf of `Q`-modules along `x : P ⟶ Q`, then along `y : O ⟶ P`, then along
`z : Q ⟶ O` returns it, naturally, as soon as the composite `z ≫ y ≫ x` is the identity.

This is `Stacks.Sheaves.RingedPoint.sheafRestrictScalarsCompIsoId` for the two maps `y ≫ x` and
`z`; what the three-fold form adds is that the first two restrictions stay separate, so no
definitional merge of two restriction functors is demanded of a consumer. -/
noncomputable def sheafRestrictScalarsComp₃IsoId (x : P ⟶ Q) (y : O ⟶ P) (z : Q ⟶ O)
    (h : z ≫ (y ≫ x) = 𝟙 Q) :
    SheafOfModules.restrictScalars.{w} x ⋙ (SheafOfModules.restrictScalars.{w} y ⋙
        SheafOfModules.restrictScalars.{w} z) ≅ 𝟭 (SheafOfModules.{w} Q) :=
  sheafRestrictScalarsCompIsoId (y ≫ x) z h

/-- The three-fold cancellation of restrictions of scalars is the identity on sections:
restriction of scalars does not change the sections of a sheaf of modules. -/
theorem sheafRestrictScalarsComp₃IsoId_val_app (x : P ⟶ Q) (y : O ⟶ P) (z : Q ⟶ O)
    (h : z ≫ (y ≫ x) = 𝟙 Q) (M : SheafOfModules.{w} Q) (U : Tᵒᵖ) (m : (M.val.obj U)) :
    ((sheafRestrictScalarsComp₃IsoId x y z h).hom.app M).val.app U m = m :=
  rfl

end Stacks.Sheaves.RingedPoint

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

include hf

/-! ### The ring-sheaf triangle -/

/-- **Stacks 03LV, clause (1), on underlying sheaves of sets.**  The inverse-image form
`f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map of Stacks 03G8 is, after forgetting the ring operations, the
comparison `AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso` of Stacks 03LQ at
the structure sheaf of `Y`.

The inverse-image form is the adjunct of the direct-image form
(`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`), the direct-image form on
sheaves of sets is `AlgebraicGeometry.Space.structureSharpSet`
(`AlgebraicGeometry.Space.forgetRing_map_fSharp`), that is the unit of the restriction adjunction
(`AlgebraicGeometry.Space.structureSharpSet_eq_unit`), and the adjunct of the unit of a second
left adjoint is the comparison of the two left adjoints
(`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app`). -/
theorem forgetRing_fSharpInverseImage_eq_inverseImageIso :
    (smallEtaleRingedTopos B S hS X).forgetRing.map
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage =
      (smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
        (structureSetSheaf B S hS Y) := by
  have key := AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv
    (smallEtaleRingedToposHom B S hS f)
  have e : ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O)
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj
          (smallEtaleRingedTopos B S hS X).O)).symm
      ((smallEtaleSetRestrictionAdjunction B S hS f hf).unit.app
        (structureSetSheaf B S hS Y)) =
        (smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
          (structureSetSheaf B S hS Y) :=
    (Equiv.symm_apply_eq _).mpr
      (Adjunction.homEquiv_leftAdjointUniq_hom_app
        (smallToposMorphismTypeU B S hS f).adj
        (smallEtaleSetRestrictionAdjunction B S hS f hf)
        (structureSetSheaf B S hS Y)).symm
  rw [key, forgetRing_map_fSharp, structureSharpSet_eq_unit B S hS f hf, e]

/-- The comparison `f⁻¹𝒪_Y ⟶ 𝒪_Y|_{X_étale}` of the two transported sheaves of rings of an
étale morphism: the inverse image of `𝒪_Y` along the morphism of small étale topoi, and its
transport along restriction of sheaves of sets to the small étale site of `X`.

It is the morphism of transported sheaves of rings induced by the comparison of Stacks 03LQ
between the two functors of sheaves of sets. -/
noncomputable def etaleInverseImageRestrictionRingMap :
    inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS Y) ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
        (smallEtaleSetRestriction B S hS f hf) (structureRingSheaf B S hS Y) :=
  pullbackRingSheafMapOfNatTrans.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
    (structureRingSheaf B S hS Y) (smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom

/-- **The ring-sheaf triangle of Stacks' Equation 03LW.**  The comparison of the two transported
sheaves of rings, followed by the identification
`AlgebraicGeometry.Space.etaleRestrictionRingSheafIso` of the transported structure sheaf with
`𝒪_X`, is the inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map of Stacks 03G8.

Both sides are compared on underlying sheaves of sets, where `CategoryTheory.sheafCompose` of
the forgetful functor is faithful.  There the second factor is the identity
(`Stacks.Sheaves.ToposPullback.restrictionRingIso_hom_ringSheafMap`), the first is the comparison
of Stacks 03LQ (`Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMapOfNatTrans`), and
so is the structure map, by
`AlgebraicGeometry.Space.forgetRing_fSharpInverseImage_eq_inverseImageIso`. -/
theorem etaleInverseImageRestrictionRingMap_comp :
    etaleInverseImageRestrictionRingMap B S hS f hf ≫
        (etaleRestrictionRingSheafIso B S hS f hf).hom =
      (etaleStructureRingSheafIso B S hS f hf).hom := by
  have h2 : (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
        (etaleRestrictionRingSheafIso B S hS f hf).hom =
      𝟙 ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).obj
        (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
          (smallEtaleSetRestriction B S hS f hf) (structureRingSheaf B S hS Y))) :=
    restrictionRingIso_hom_ringSheafMap (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Y.1) (smallEtalePostcomp B S hS f hf)
      (structureRingSheaf B S hS Y)
  have h3 : (etaleStructureRingSheafIso B S hS f hf).hom =
      (smallEtaleRingedToposHom B S hS f).fSharpInverseImageRing :=
    AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage
      (smallEtaleRingedToposHom B S hS f)
  have h4 : (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImageRing =
      (smallEtaleRingedTopos B S hS X).forgetRing.map
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage :=
    (AlgebraicGeometry.RingedToposHom.forgetRing_map_fSharpInverseImage
      (smallEtaleRingedToposHom B S hS f)).symm
  have hL : (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
        (etaleInverseImageRestrictionRingMap B S hS f hf ≫
          (etaleRestrictionRingSheafIso B S hS f hf).hom) =
      (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
        (etaleInverseImageRestrictionRingMap B S hS f hf) :=
    ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget RingCat.{u})).map_comp _ _).trans
      ((congrArg (fun q ↦ (sheafCompose (SmallEtale.topology B S hS X.1)
            (forget RingCat.{u})).map (etaleInverseImageRestrictionRingMap B S hS f hf) ≫ q)
          h2).trans (Category.comp_id _))
  have hR : (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
        (etaleStructureRingSheafIso B S hS f hf).hom =
      (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
        (etaleInverseImageRestrictionRingMap B S hS f hf) :=
    (congrArg (fun m ↦ (sheafCompose (SmallEtale.topology B S hS X.1)
          (forget RingCat.{u})).map m) h3).trans
      (h4.trans ((forgetRing_fSharpInverseImage_eq_inverseImageIso B S hS f hf).trans
        (ringSheafMap_pullbackRingSheafMapOfNatTrans.{u, u, u, u + 1, u, u + 1}
          (SmallEtale.topology B S hS X.1) (structureRingSheaf B S hS Y)
          (smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom).symm))
  exact (sheafCompose (SmallEtale.topology B S hS X.1)
    (forget RingCat.{u})).map_injective (hL.trans hR.symm)

/-! ### Transport of the modules -/

/-- **Stacks 03D2 along an étale morphism, as a transport.**  The inverse image of
`𝒪_Y`-modules along the morphism of small étale topoi of Stacks 03G8 is the transport of modules
along restriction of sheaves of sets to the small étale site of `X`, with scalars read through
`AlgebraicGeometry.Space.etaleInverseImageRestrictionRingMap`.

This is `Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso` at the comparison of
Stacks 03LQ; the inverse image of modules and of the sheaf of rings are the transports along the
inverse-image functor itself, so no unfolding is needed. -/
noncomputable def etaleModuleInverseImageIsoRestrictionTransport :
    inverseImageModules.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS Y) ≅
      pullbackModuleFunctor.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
          (smallEtaleSetRestriction B S hS f hf) (structureRingSheaf B S hS Y) ⋙
        SheafOfModules.restrictScalars (etaleInverseImageRestrictionRingMap B S hS f hf) :=
  pullbackModuleFunctorIsoOfNatIso.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
    (structureRingSheaf B S hS Y) (smallToposMorphismTypeU_inverseImageIso B S hS f hf)
    (etaleInverseImageRestrictionRingMap B S hS f hf)
    (ringSheafMap_pullbackRingSheafMapOfNatTrans.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS X.1) (structureRingSheaf B S hS Y)
      (smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom)

/-- **The transported modules of an étale restriction are the restricted modules.**  The
transport of `𝒪_Y`-modules along restriction of sheaves of sets to the small étale site of `X`,
with scalars read over `f⁻¹𝒪_Y` through
`AlgebraicGeometry.Space.etaleInverseImageRestrictionRingMap` and then over `𝒪_X` through the
inverse of the canonical isomorphism of structure sheaves, is
`AlgebraicGeometry.Space.etaleModulePullback`: plain restriction of sections along small étale
postcomposition with `f`.

The transport is restriction of modules by
`Stacks.Sheaves.ToposPullback.restrictionModuleIso`, which is Stacks 03D2 for a continuous
functor of sites, and the three restrictions of scalars that remain cancel because their
composite map of sheaves of rings is the identity, by
`AlgebraicGeometry.Space.etaleInverseImageRestrictionRingMap_comp`. -/
noncomputable def etaleRestrictionModuleTransportIso :
    (pullbackModuleFunctor.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
            (smallEtaleSetRestriction B S hS f hf) (structureRingSheaf B S hS Y) ⋙
          SheafOfModules.restrictScalars (etaleInverseImageRestrictionRingMap B S hS f hf)) ⋙
        SheafOfModules.restrictScalars (etaleStructureRingSheafIso B S hS f hf).inv ≅
      etaleModulePullback.{u, u} B S hS f hf :=
  let A : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u} :=
    inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
      (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS Y)
  let A' : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u} :=
    pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
      (smallEtaleSetRestriction B S hS f hf) (structureRingSheaf B S hS Y)
  let iota : A ≅ structureRingSheaf B S hS X := etaleStructureRingSheafIso B S hS f hf
  let rho : A' ⟶ structureRingSheaf B S hS X := (etaleRestrictionRingSheafIso B S hS f hf).hom
  let bet : A ⟶ A' := etaleInverseImageRestrictionRingMap B S hS f hf
  let PL : Modules.{u, u} B S hS Y.1 Y.2 ⥤ SheafOfModules.{u} A' :=
    pullbackModuleFunctor.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
      (smallEtaleSetRestriction B S hS f hf) (structureRingSheaf B S hS Y)
  let EP : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2 :=
    etaleModulePullback.{u, u} B S hS f hf
  let RSb : SheafOfModules.{u} A' ⥤ SheafOfModules.{u} A := SheafOfModules.restrictScalars bet
  let RSr : Modules.{u, u} B S hS X.1 X.2 ⥤ SheafOfModules.{u} A' :=
    SheafOfModules.restrictScalars rho
  let RSi : SheafOfModules.{u} A ⥤ Modules.{u, u} B S hS X.1 X.2 :=
    SheafOfModules.restrictScalars iota.inv
  let a₁ : (PL ⋙ RSb) ⋙ RSi ≅ PL ⋙ (RSb ⋙ RSi) := Functor.associator PL RSb RSi
  let rIso : PL ≅ EP ⋙ RSr :=
    restrictionModuleIso (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
      (smallEtalePostcomp B S hS f hf) (structureRingSheaf B S hS Y)
  let a₂ : PL ⋙ (RSb ⋙ RSi) ≅ (EP ⋙ RSr) ⋙ (RSb ⋙ RSi) :=
    Functor.isoWhiskerRight rIso (RSb ⋙ RSi)
  let a₃ : (EP ⋙ RSr) ⋙ (RSb ⋙ RSi) ≅ EP ⋙ (RSr ⋙ (RSb ⋙ RSi)) :=
    Functor.associator EP RSr (RSb ⋙ RSi)
  let hid : iota.inv ≫ (bet ≫ rho) = 𝟙 (structureRingSheaf B S hS X) :=
    (congrArg (fun q ↦ iota.inv ≫ q)
      (etaleInverseImageRestrictionRingMap_comp B S hS f hf)).trans iota.inv_hom_id
  let a₄ : EP ⋙ (RSr ⋙ (RSb ⋙ RSi)) ≅ EP ⋙ 𝟭 (Modules.{u, u} B S hS X.1 X.2) :=
    Functor.isoWhiskerLeft EP
      (Stacks.Sheaves.RingedPoint.sheafRestrictScalarsComp₃IsoId rho bet iota.inv hid)
  let a₅ : EP ⋙ 𝟭 (Modules.{u, u} B S hS X.1 X.2) ≅ etaleModulePullback.{u, u} B S hS f hf :=
    EP.rightUnitor
  a₁ ≪≫ a₂ ≪≫ a₃ ≪≫ a₄ ≪≫ a₅

/-- `AlgebraicGeometry.Space.etaleRestrictionModuleTransportIso` is the identity on sections:
restriction of a sheaf of modules along a functor of sites reindexes its sections, and
restriction of scalars does not change them at all. -/
theorem etaleRestrictionModuleTransportIso_val_app (G : Modules.{u, u} B S hS Y.1 Y.2)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (n : ((pullbackModuleFunctor.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
      (smallEtaleSetRestriction B S hS f hf) (structureRingSheaf B S hS Y)).obj G).val.obj U) :
    ((etaleRestrictionModuleTransportIso B S hS f hf).hom.app G).val.app U n = n :=
  rfl

/-! ### Stacks' Equation 03LW -/

/-- **Stacks' Equation 03LW**, the outer identification `G|_{X_étale} = f_{small}^{-1}G`: the
inverse image of `𝒪_Y`-modules along an étale morphism, read over `𝒪_X` through the canonical
isomorphism of structure sheaves, is étale restriction of modules. -/
@[stacks 03LW "the inverse image of modules is étale restriction"]
noncomputable def etaleModuleInverseImageIsoEtaleModulePullback :
    etaleModuleInverseImage B S hS f hf ≅ etaleModulePullback.{u, u} B S hS f hf :=
  Functor.isoWhiskerRight (etaleModuleInverseImageIsoRestrictionTransport B S hS f hf)
      (SheafOfModules.restrictScalars (etaleStructureRingSheafIso B S hS f hf).inv) ≪≫
    etaleRestrictionModuleTransportIso B S hS f hf

/-- On sections, the identification of the inverse image of modules with étale restriction is
the comparison of Stacks 03LQ at the sheaf of modules and nothing further: the transport of the
modules is the only content, the remaining steps being reindexings of sections and restrictions
of scalars. -/
theorem etaleModuleInverseImageIsoEtaleModulePullback_val_app
    (G : Modules.{u, u} B S hS Y.1 Y.2) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (m : ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
      (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).obj G).val.obj U) :
    ((etaleModuleInverseImageIsoEtaleModulePullback B S hS f hf).hom.app G).val.app U m =
      ((etaleModuleInverseImageIsoRestrictionTransport B S hS f hf).hom.app G).val.app U m :=
  etaleRestrictionModuleTransportIso_val_app B S hS f hf G U _

/-- **Stacks Equation 03LW, that is clause (2) of Stacks 03LV.**  Along an étale morphism
`f : X ⟶ Y` of algebraic spaces the pullback of `𝒪_Y`-modules of Stacks 03LU is naturally
isomorphic to étale restriction: `f^*G` is the sheaf whose sections over an étale chart `U` of
`X` are the sections of `G` over the composite chart of `Y`.

The comparison factors through the inverse image of modules by
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModuleInverseImage`, which is clause (2) of
Stacks 03LV in its inverse-image reading. -/
@[stacks 03LW "pullback of modules along an étale morphism is étale restriction",
  stacks 03LV "the identification f^*G = G|_{X_étale}"]
noncomputable def modulePullbackIsoEtaleModulePullback :
    modulePullback B S hS f ≅ etaleModulePullback.{u, u} B S hS f hf :=
  modulePullbackIsoEtaleModuleInverseImage B S hS f hf ≪≫
    etaleModuleInverseImageIsoEtaleModulePullback B S hS f hf

/-- **Stacks Equation 03LW, canonicity.**  The comparison of the pullback of modules with étale
restriction sends the canonical image of a section of the inverse image of modules to the
comparison of Stacks 03LQ applied to that section, so it introduces no twist of its own: it is
the canonical identification and not merely some natural isomorphism of the two functors.

This is `AlgebraicGeometry.Space.modulePullbackIsoEtaleModuleInverseImage_unit_app`, which pins
the extension-of-scalars half, followed by
`AlgebraicGeometry.Space.etaleModuleInverseImageIsoEtaleModulePullback_val_app`, which pins the
transport half. -/
@[stacks 03LW "canonical module comparison"]
theorem modulePullbackIsoEtaleModulePullback_unit_app (G : Modules.{u, u} B S hS Y.1 Y.2)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (m : ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
      (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).obj G).val.obj U) :
    ((extendScalarsFSharpAdjunction B S hS f).unit.app
          ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
            (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y)).obj G) ≫
        (SheafOfModules.restrictScalars
          (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map
            ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app G)).val.app U m =
      ((etaleModuleInverseImageIsoRestrictionTransport B S hS f hf).hom.app G).val.app U m :=
  (congrArg (fun x ↦ ((etaleModuleInverseImageIsoEtaleModulePullback B S hS f hf).hom.app
        G).val.app U x)
      (modulePullbackIsoEtaleModuleInverseImage_unit_app B S hS f hf G U m)).trans
    (etaleModuleInverseImageIsoEtaleModulePullback_val_app B S hS f hf G U m)

end AlgebraicGeometry.Space

end
