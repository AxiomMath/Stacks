module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullback

/-!
# The associated module of a restriction to an open

Stacks 03DV proves that `𝓕^a` is quasi-coherent by choosing a Zariski covering of `S` on which
`𝓕` is presented and transporting the presentation to each member of the covering.  The step the
source leaves implicit is that the associated module of the restriction of `𝓕` to an open `V` of
`S` is the restriction of `𝓕^a` to the localization of the big fppf site at `V`,
`(𝓕|_V)^a ≅ (𝓕^a)|_{(Sch/V)}`.  This file proves it.

The geometric content is that the intersection of two opens of `S` is their fibre product over
`S`: the localization of the big fppf category at the open `V` receives the small Zariski site of
`V`, which is the slice `Opens S / V`, by `V' ↦ V'`, and also receives it as `W ↦ W ×_S V`, and
the two agree.  In Lean that is the statement that the inclusion of the small Zariski site of `S`
into the big fppf category over `S` preserves the binary products `V ⨯ -`, which is *already* a
consequence of `AlgebraicGeometry.BigFppfOver.representablyFlat_opensToBig`: a representably flat
functor preserves all finite limits.

With that in hand the comparison is an instance of `SheafOfModules.pullbackSquareIso` for the
square of ringed sites

    Opens S  --- Over.star V --->  Opens S / V
       |                              |
    opensToBig                    Over.post opensToBig
       |                              |
       v                              v
    (Sch/S)  -- Over.star V^big -->  (Sch/S) / V

whose two composite structure-sheaf comparisons agree because the comparison of structure sheaves
is natural and the product projection of the square is the product comparison map.

## Main definitions

* `SheafOfModules.overComparison`: the comparison of sheaves of rings carried by the localization
  of a morphism of ringed sites at an object of its source.
* `AlgebraicGeometry.BigFppfOver.sliceStructureMap`: that comparison for the inclusion of the
  small Zariski site of `S`, so that its pullback is the associated-module functor of `(Sch/V)`.
* `AlgebraicGeometry.BigFppfOver.opensObjInfIsoProd`: the intersection of two opens of `S` is
  their fibre product over `S` in the big fppf category.
* `AlgebraicGeometry.BigFppfOver.opensStarIso`: the natural isomorphism `W ⊓ V ≅ W ×_S V` of
  functors into the localization of the big fppf category at `V`.

## Main results

* `SheafOfModules.overFunctorPullbackIso`: pullback of sheaves of modules along a morphism of
  ringed sites commutes with restriction to a slice of the source and of the target.
* `AlgebraicGeometry.BigFppfOver.associatedModuleOverIso` and
  `AlgebraicGeometry.BigFppfOver.associatedModuleOverObjIso`: `(𝓕|_V)^a ≅ (𝓕^a)|_{(Sch/V)}`, the
  step Stacks 03DV leaves implicit.

## Implementation notes

The general half of the file mentions no scheme and belongs upstream; it lives here because it is
stated for `SheafOfModules.pullbackSquareIso`, which is itself local to this development.

Nothing is tagged.  Stacks 03DV asserts `SheafOfModules.IsQuasicoherentOnSite` of `𝓕^a` for an
arbitrary quasi-coherent `𝓕`; what is proved here is one of the two obstructions recorded in
`AlgebraicGeometry.BigFppfOver.isQuasicoherent_associatedModule`.  **The other is closed too**:
the isomorphism here produces a `SheafOfModules.Presentation`, and the passage to
`SheafOfModules.HasGlobalPresentation` is `SheafOfModules.Presentation.hasGlobalPresentation`
(`StacksFrontier/AlgebraicGeometry/Topologies/QuasicoherentOnSiteOfPresentation.lean:96`), over the
universe bridge at `:78`.

Two spellings have to be kept apart.  `AlgebraicGeometry.Scheme.Modules` is a `def` carrying its
own `CategoryTheory.Category` instance rather than a reducible abbreviation of
`SheafOfModules.{u} S.ringCatSheaf`, so a natural isomorphism of functors out of the one is not a
natural isomorphism of functors out of the other; the functor-level statement below is therefore
written with `SheafOfModules.pullback (structureMap B S hS)`, which is
`AlgebraicGeometry.BigFppfOver.associatedModule` by definition, and only the object-level
statement names the associated-module functor.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u u₁ u₂ v₁ v₂

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [HasBinaryProducts C] [HasBinaryProducts D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} [F.IsContinuous J K]
  {R : Sheaf J RingCat.{u}} {R' : Sheaf K RingCat.{u}}
  (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R') (X : C)
  [(Over.post (X := X) F).IsContinuous (J.over X) (K.over (F.obj X))]
  [(Over.star X ⋙ Over.post F).IsContinuous J (K.over (F.obj X))]
  [(F ⋙ Over.star (F.obj X)).IsContinuous J (K.over (F.obj X))]

/-- The comparison of sheaves of rings carried by the localization of a morphism of ringed sites
at an object `X` of its source: restriction of `φ` to the slice over `X`, read along the
localized continuous functor `Over.post F`. -/
public noncomputable def overComparison :
    R.over X ⟶ ((Over.post F).sheafPushforwardContinuous RingCat.{u} (J.over X)
      (K.over (F.obj X))).obj (R'.over (F.obj X)) :=
  ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (J.over X) J).map φ

/-- The two routes round the square of ringed sites carry the same comparison of structure
sheaves.  Both composites restrict a section along the product projection and then transport it
along `φ`; they agree because `φ` is natural and the horizontal isomorphism of the square is the
product comparison map, whose composite with the projection is the image of the projection. -/
public theorem comparisonComp_overComparison
    (e : Over.star X ⋙ Over.post F ≅ F ⋙ Over.star (F.obj X))
    (hleft : ∀ Y : C, (e.hom.app Y).left = prodComparison F X Y) :
    comparisonComp φ (pushforwardOver (F.obj X)) ≫
        (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J
          (K.over (F.obj X))).app (R'.over (F.obj X)) =
      comparisonComp (pushforwardOver X) (overComparison φ X) := by
  ext : 2
  funext Y
  show φ.hom.app Y ≫ R'.obj.map (prod.snd).op ≫
      R'.obj.map ((e.hom.app Y.unop).left).op =
    R.obj.map (prod.snd).op ≫ φ.hom.app _
  have h1 : R'.obj.map ((prod.snd : F.obj X ⨯ F.obj Y.unop ⟶ F.obj Y.unop)).op ≫
      R'.obj.map (prodComparison F X Y.unop).op
      = R'.obj.map ((F.map (prod.snd : X ⨯ Y.unop ⟶ Y.unop)).op) := by
    rw [← R'.obj.map_comp, ← op_comp, prodComparison_snd]
  rw [hleft]
  exact (congrArg (fun k ↦ φ.hom.app Y ≫ k) h1).trans (φ.hom.naturality (prod.snd).op).symm

/-- Pushforward along the comparison `SheafOfModules.pushforwardOver` has a left adjoint:
restriction to the slice is that adjoint. -/
public instance isRightAdjoint_pushforward_pushforwardOver (Y : C) :
    (pushforward.{v} (pushforwardOver (R := R) Y)).IsRightAdjoint :=
  (overPushforwardOverAdj.{v} Y).isRightAdjoint

/-- Pullback along `SheafOfModules.pushforwardOver` is restriction to the slice: the two are left
adjoints of the same pushforward. -/
public noncomputable def pullbackPushforwardOverIso (Y : C) :
    pullback.{v} (pushforwardOver (R := R) Y) ≅ overFunctor.{v} R Y :=
  Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction.{v} _) (overPushforwardOverAdj.{v} Y)

variable [(pushforward.{v} φ).IsRightAdjoint]
  [(pushforward.{v} (overComparison φ X)).IsRightAdjoint]

/-- **Stacks 03FH (2) for a localization.**  Pullback of sheaves of modules along a morphism of
ringed sites commutes with restriction to the slice over an object `X` of the source and the
slice over its image, provided the continuous functor preserves the binary products `X ⨯ -`. -/
public noncomputable def overFunctorPullbackIso
    (e : Over.star X ⋙ Over.post F ≅ F ⋙ Over.star (F.obj X))
    (hleft : ∀ Y : C, (e.hom.app Y).left = prodComparison F X Y) :
    overFunctor.{v} R X ⋙ pullback.{v} (overComparison φ X) ≅
      pullback.{v} φ ⋙ overFunctor.{v} R' (F.obj X) :=
  Functor.isoWhiskerRight (pullbackPushforwardOverIso.{v} X).symm _ ≪≫
    pullbackSquareIso.{v} (pushforwardOver X) (overComparison φ X) φ
      (pushforwardOver (F.obj X)) e (comparisonComp_overComparison φ X e hleft) ≪≫
    Functor.isoWhiskerLeft _ (pullbackPushforwardOverIso.{v} (F.obj X))

end SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of the small Zariski site of `S` into the big fppf category over `S` preserves
finite limits, being representably flat. -/
public instance preservesFiniteLimits_opensToBig : PreservesFiniteLimits (opensToBig B S hS) :=
  preservesFiniteLimits_of_flat _

/-- The inclusion of the small Zariski site of `S` into the big fppf category over `S` preserves
`1`-hypercovers: it is cover preserving and preserves fibre products. -/
public instance preservesOneHypercovers_opensToBig :
    (opensToBig B S hS).PreservesOneHypercovers.{u}
      (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  Functor.PreservesOneHypercovers.of_coverPreserving (coverPreserving_opensToBig B S hS)

/-- There is at most one morphism from an object of the big fppf category over `S` into a product
of two opens of `S`, each factor admitting at most one. -/
public theorem subsingleton_hom_prodOpens (Z : BigFppfOver B S hS) (V W : S.Opens)
    [HasBinaryProduct ((opensToBig B S hS).obj V) ((opensToBig B S hS).obj W)] :
    Subsingleton (Z ⟶ (opensToBig B S hS).obj V ⨯ (opensToBig B S hS).obj W) :=
  ⟨fun _ _ ↦ prod.hom_ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

/-- **The geometric content of Stacks 03DV.**  The intersection of two opens of `S` is their
fibre product over `S`: the open `V ⊓ W`, with its two inclusions, is a product of `V` and `W` in
the big fppf category of schemes over `S`. -/
public noncomputable def opensObjInfIsoProd (V W : S.Opens) :
    opensObj B S hS (V ⊓ W) ≅ opensObj B S hS V ⨯ opensObj B S hS W :=
  eqToIso (congrArg (opensObj B S hS) (CompleteLattice.prod_eq_inf V W).symm) ≪≫
    PreservesLimitPair.iso (opensToBig B S hS) V W

/-- The first projection of `AlgebraicGeometry.BigFppfOver.opensObjInfIsoProd` is the inclusion
of `V ⊓ W` into `V`. -/
@[simp]
public theorem opensObjInfIsoProd_hom_fst (V W : S.Opens) :
    (opensObjInfIsoProd B S hS V W).hom ≫ prod.fst = opensHom B S hS inf_le_left :=
  Subsingleton.elim (h := subsingleton_hom_opensObj B S hS _ V) _ _

/-- The second projection of `AlgebraicGeometry.BigFppfOver.opensObjInfIsoProd` is the inclusion
of `V ⊓ W` into `W`. -/
@[simp]
public theorem opensObjInfIsoProd_hom_snd (V W : S.Opens) :
    (opensObjInfIsoProd B S hS V W).hom ≫ prod.snd = opensHom B S hS inf_le_right :=
  Subsingleton.elim (h := subsingleton_hom_opensObj B S hS _ W) _ _

/-- **The geometric content of Stacks 03DV, naturally.**  The two functors from the small Zariski
site of `S` to the localization of the big fppf category at an open `V` — intersect with `V`, and
take the fibre product with `V` over `S` — are isomorphic. -/
public noncomputable def opensStarIso (V : S.Opens) :
    Over.star V ⋙ Over.post (opensToBig B S hS) ≅
      opensToBig B S hS ⋙ Over.star ((opensToBig B S hS).obj V) :=
  have hp : ∀ W : S.Opens, IsIso (prodComparison (opensToBig B S hS) V W) := fun _ ↦ inferInstance
  NatIso.ofComponents
    (fun W ↦ Over.isoMk (@asIso _ _ _ _ _ (hp W))
      (Subsingleton.elim (h := subsingleton_hom_opensToBig B S hS _ V) _ _))
    (fun {_ Y} _ ↦ Over.OverMorphism.ext
      (Subsingleton.elim (h := subsingleton_hom_prodOpens B S hS _ V Y) _ _))

/-- The horizontal isomorphism of the square is the product comparison map of the inclusion. -/
public theorem opensStarIso_hom_app_left (V W : S.Opens) :
    ((opensStarIso B S hS V).hom.app W).left = prodComparison (opensToBig B S hS) V W := rfl

/-- Intersecting with `V` and then including into the localized big fppf category is a continuous
functor. -/
public instance isContinuous_starPost (V : S.Opens) :
    (Over.star V ⋙ Over.post (opensToBig B S hS)).IsContinuous
      (Opens.grothendieckTopology ↥S)
      ((topology B S hS).over ((opensToBig B S hS).obj V)) :=
  Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology ↥S).over V) _

/-- Including into the big fppf category and then taking the fibre product with `V` over `S` is a
continuous functor. -/
public instance isContinuous_opensToBigStar (V : S.Opens) :
    (opensToBig B S hS ⋙ Over.star ((opensToBig B S hS).obj V)).IsContinuous
      (Opens.grothendieckTopology ↥S)
      ((topology B S hS).over ((opensToBig B S hS).obj V)) :=
  Functor.isContinuous_comp _ _ _ (topology B S hS) _

/-- The comparison of structure sheaves of the morphism of ringed sites
`((Sch/S)_fppf / V, 𝒪) → (V_Zar, 𝒪_V)`, the localization at `V` of the inclusion of the small
Zariski site of `S`.  Its pullback is the associated-module functor of `(Sch/V)_fppf`. -/
public noncomputable abbrev sliceStructureMap (V : S.Opens) :
    (S.ringCatSheaf).over V ⟶
      ((Over.post (opensToBig B S hS)).sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology ↥S).over V)
        ((topology B S hS).over ((opensToBig B S hS).obj V))).obj
        ((structureSheaf B S hS).over ((opensToBig B S hS).obj V)) :=
  SheafOfModules.overComparison (structureMap B S hS) V

/-- The pushforward of presheaves of modules along the localized comparison has a left adjoint:
the source of the localized continuous functor is a small category. -/
public instance presheafPushforward_sliceStructureMap_isRightAdjoint (V : S.Opens) :
    (PresheafOfModules.pushforward.{u} (sliceStructureMap B S hS V).hom).IsRightAdjoint :=
  Stacks.ModulePullback.isRightAdjoint_pushforward _

/-- **Stacks 03DV, the step the source leaves implicit.**  The associated module of the
restriction of an `𝒪_S`-module to an open `V` of `S` is the restriction of its associated module
to the localization of the big fppf site of `S` at `V`.  Stated for
`SheafOfModules.pullback (structureMap B S hS)`, which is
`AlgebraicGeometry.BigFppfOver.associatedModule` by definition. -/
public noncomputable def associatedModuleOverIso (V : S.Opens) :
    SheafOfModules.overFunctor.{u} S.ringCatSheaf V ⋙
        SheafOfModules.pullback.{u} (sliceStructureMap B S hS V) ≅
      SheafOfModules.pullback.{u} (structureMap B S hS) ⋙
        SheafOfModules.overFunctor.{u} (structureSheaf B S hS) ((opensToBig B S hS).obj V) :=
  SheafOfModules.overFunctorPullbackIso.{u} (structureMap B S hS) V (opensStarIso B S hS V)
    (opensStarIso_hom_app_left B S hS V)

/-- **Stacks 03DV, the step the source leaves implicit, at one module.**
`(𝓕|_V)^a ≅ (𝓕^a)|_{(Sch/V)}`. -/
public noncomputable def associatedModuleOverObjIso (V : S.Opens) (𝓕 : S.Modules) :
    (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)).obj
        (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V) ≅
      ((associatedModule B S hS).obj 𝓕).over ((opensToBig B S hS).obj V) :=
  (associatedModuleOverIso B S hS V).app 𝓕

end AlgebraicGeometry.BigFppfOver

end
