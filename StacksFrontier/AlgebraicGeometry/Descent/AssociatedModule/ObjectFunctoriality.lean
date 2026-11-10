module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BigSiteDescentDatum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Sites.OverMapComp

/-!
# Stacks 03DV is functorial in the object of the big fppf site

`AlgebraicGeometry.BigFppfOver.associatedModuleObjIso` proves the comparison Stacks 03DV leaves
implicit at an arbitrary object `T` of the big fppf category over `S`: for `f : X ⟶ S` the
structure morphism of `T`,

    `(f^*𝓕)^a ≅ (𝓕^a)|_{(Sch/S)_fppf / T}`.

Two things are missing before that comparison can be used, and this file supplies both.

**The target is on the wrong site.**  The comparison lands in modules on the *localization*
`(Sch/S)_fppf / T`, through `SheafOfModules.pullback (objSliceStructureMap B S hS T)`, whereas
the consumers of Stacks 03DX (1) — `AlgebraicGeometry.BigFppfOver.HasLocalAssociatedModule` and
the hypotheses that feed on it — speak of `AlgebraicGeometry.BigFppfOver.objRestrict` and of the
associated module of the big fppf site of the scheme `X` of `T`, that is, of the localization
*reindexed* along the equivalence `AlgebraicGeometry.BigFppfOver.objEquiv`.  The two are the same
ringed site, but no lemma connected the two spellings:
`AlgebraicGeometry.BigFppfOver.objSliceStructureMap` occurred in exactly one file.
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso` is that bridge, and
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` is Stacks 03DV in the usable
spelling: restricting a module along `f` and forming its associated module on `X` is forming its
associated module on `S` and restricting to the big fppf site of `X`.

**Restriction to an object is not functorial on the nose.**  For `g : T' ⟶ T` the composite of
the restriction to the site of `X` and the restriction to the site of the scheme of `T'` over `X`
is *not* definitionally the restriction to the site of the scheme of `T'`: the two are
pushforwards along `Over.map g.left ⋙ Over.map T.hom` and along `Over.map T'.hom`, which agree
only through `CategoryTheory.Over.mapComp` together with `CategoryTheory.Over.w`.
`AlgebraicGeometry.BigFppfOver.objRestrictComp` is that comparison.

Together they transport the local datum of Stacks 03DX (1) along a morphism of the big site:
if the restriction of `𝒢` to the site of the scheme of `T` is an associated module, so is its
restriction to the site of the scheme of any `T'` over `T`, the module downstairs being pulled
back along `g`.  That is what makes a *refinement* of a covering family usable — the refinement
produced by `AlgebraicGeometry.BigFppfOver.exists_coversTop_fpqc_refinement` only comes with
morphisms into the members of the original family, so a datum carried on the original family has
to be moved along those morphisms.

Read through `AlgebraicGeometry.BigFppfOver.objInverseImageIso`, which identifies restriction to
the big fppf site of the scheme of `T` with the inverse image of sheaves of modules along the
morphism of ringed sites `f_big` of Stacks 021W, that functoriality is Stacks 03LC (1) at
`τ = fppf`: forming the associated quasi-coherent module commutes with pullback.

## Main definitions

* `Stacks.SheafOfModules.pullbackCongr`: the pullbacks of sheaves of modules along two *equal*
  morphisms of sheaves of rings are isomorphic.
* `AlgebraicGeometry.BigFppfOver.objBaseChangeSharp`: the comparison of structure sheaves of the
  morphism of ringed big fppf sites `f_big` attached to an object `T` of the big fppf site, that
  is, restriction of functions along the projection of the fibre product.
* `AlgebraicGeometry.BigFppfOver.objInverseImageIso`: **the inverse image of sheaves of modules
  along `f_big` is restriction to the big fppf site of the scheme of `T`**, `f_big^* = (-)|_{X}`.
  The inverse image exists because the pushforward along `f_big` is
  `SheafOfModules.overPullback` of the structure morphism of `T`, right adjoint to restriction
  along postcomposition.

## Main results

* `AlgebraicGeometry.BigFppfOver.objRestrict_eq_overMap`: restriction to the big fppf site of the
  scheme of `T` *is* restriction along the structure morphism of `T`, as an equality of functors.
* `AlgebraicGeometry.BigFppfOver.objRestrictComp`: **restriction to an object is functorial**,
  `𝒢|_{(Sch/X)}|_{(Sch/X')} ≅ 𝒢|_{(Sch/X')}` for `T' ⟶ T`.
* `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso`: **the comparison of Stacks 03DV
  in the spelling its consumers use**, the associated-module functor of the big fppf site of the
  scheme of `T` identified with the localized pullback followed by the reindexing.
* `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`: **Stacks 03DV, functorial in
  the object of the big site**, `(f^*𝓕)^a ≅ (𝓕^a)|_{(Sch/X)_fppf}`.
* `AlgebraicGeometry.BigFppfOver.hasLocalAssociatedModule_of_hom` and
  `AlgebraicGeometry.BigFppfOver.hasLocalAssociatedModule_of_refinement`: **the local datum of
  Stacks 03DX (1) transports along a morphism of the big site**, hence along a refinement of a
  covering family.  Both are unconditional.
* `AlgebraicGeometry.BigFppfOver.associatedModuleBaseChangeIso`: **Stacks 03LC (1) at
  `τ = fppf`**, the equivalence of Stacks 03DX is compatible with pullback,
  `f_big^*(𝓕^a) ≅ (f^*𝓕)^a`.

## Implementation notes

Apart from the two clauses of Stacks 03LC, nothing here carries a `stacks` attribute.  The
covering set of Stacks 03DV is
`AlgebraicGeometry.BigFppfOver.associatedModuleIsQuasicoherent`; the comparison
`AlgebraicGeometry.BigFppfOver.associatedModuleObjIso` that this file transports is a step the
source leaves implicit and carries no tag of its own, and neither does its functoriality in the
object, which the source does not state separately.

`AlgebraicGeometry.BigFppfOver.objRestrict_eq_overMap` is proved by citing
`Stacks.SheafOfModules.overFunctor_comp_sliceBackward` rather than by `rfl`: both sides are the
same pushforward of sheaves of modules, but checking that at the concrete structure sheaf of the
big fppf site exhausts the heartbeat budget, whereas the general lemma — whose proof *is* `rfl` —
instantiates at once.  The same reason governs `Stacks.SheafOfModules.overMapCompIso`, which
`StacksFrontier/AlgebraicGeometry/Sites/OverMapComp.lean` states at an arbitrary site: its
specialization to `AlgebraicGeometry.BigFppfSite.structureSheaf` cannot be proved in place,
because instance search no longer finds the continuity of `CategoryTheory.Over.map` once the
objects of the slice are written out.

`Stacks.SheafOfModules.pullbackCongr` is needed because `SheafOfModules.pullbackComp` states its
conclusion for `φ ≫ (F.sheafPushforwardContinuous RingCat _ _).map ψ`, and the comparison of
structure sheaves of the localization at `T` is `objSliceStructureMap`, which is that composite
with `ψ` the identity.  `SheafOfModules.pushforwardCongr` is Mathlib's analogue for pushforwards;
there is no `pullbackCongr` there because the pullback is only defined through its adjunction, so
the transport has to go through `CategoryTheory.Adjunction.leftAdjointUniq`.

The right-adjointness instance for that composite is obtained by substituting along the equality
rather than by instance search: the two readings of the composite's source — pushforward along
`opensToBig` into modules on the reindexed site, and pushforward along `objToBig` into modules on
the localization — are definitionally equal but not syntactically so, and only the second is the
one Mathlib's instance is stated for.

`AlgebraicGeometry.BigFppfOver.objBaseChangeSharp` restates
`CategoryTheory.Sheaf.toPushforwardOverPullback` with the two topologies written as
`AlgebraicGeometry.BigFppfOver.topology`, which is the form in which the associated-module
functor presents them; `AlgebraicGeometry.BigFppfOver.isContinuous_objBaseChange` is Mathlib's
continuity instance for `CategoryTheory.Over.pullback` in that same form, where instance search
does not find it, and is used as a local instance.

The two sides of `AlgebraicGeometry.BigFppfOver.associatedModuleBaseChangeIso` are in the order
they are because `SheafOfModules.pullback` takes the continuity of the functor of sites as an
instance argument while its value mentions only the two sheaves of rings: against a fully known
expected type that instance is synthesized before the comparison of structure sheaves has
determined the functor, and the synthesis fails.  As the source of the isomorphism the comparison
is elaborated first and the functor is known.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 021W](https://stacks.math.columbia.edu/tag/021W)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ v₂ u₁ u₂ u₃ u₄ u

namespace Stacks.SheafOfModules

section Congr

variable {C₁ : Type u₁} [Category.{v₁} C₁] {D₁ : Type u₂} [Category.{v₂} D₁]
  {J₁ : GrothendieckTopology C₁} {K₁ : GrothendieckTopology D₁} {F : C₁ ⥤ D₁}
  {S₁ : Sheaf J₁ RingCat.{w}} {R₁ : Sheaf K₁ RingCat.{w}} [Functor.IsContinuous F J₁ K₁]

/-- **The pullback of sheaves of modules depends on the morphism of sheaves of rings only up to
equality.**  This is `SheafOfModules.pushforwardCongr` for the left adjoints: the pullback is
defined only through its adjunction, so the transport goes through the uniqueness of a left
adjoint rather than through a comparison of sections. -/
public noncomputable def pullbackCongr
    {φ ψ : S₁ ⟶ (F.sheafPushforwardContinuous RingCat.{w} J₁ K₁).obj R₁}
    [(SheafOfModules.pushforward.{w} φ).IsRightAdjoint]
    [(SheafOfModules.pushforward.{w} ψ).IsRightAdjoint] (h : φ = ψ) :
    SheafOfModules.pullback.{w} φ ≅ SheafOfModules.pullback.{w} ψ :=
  Adjunction.leftAdjointUniq (SheafOfModules.pullbackPushforwardAdjunction.{w} φ)
    ((SheafOfModules.pullbackPushforwardAdjunction.{w} ψ).ofNatIsoRight
      (SheafOfModules.pushforwardCongr.{w} h.symm))

end Congr

end Stacks.SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-! ### Restriction to an object of the big site -/

/-- **Restriction to the big fppf site of the scheme of `T` is restriction along the structure
morphism of `T`.**  The restriction `𝒢 ↦ 𝒢|_{(Sch/X)_fppf}` of the source's proof of
Stacks 03DX (1) is defined as the restriction to the localization at `T` followed by the
reindexing along the equivalence of Stacks 06WI; both steps are pushforwards of sheaves of
modules, along `CategoryTheory.Over.forget` and along
`CategoryTheory.Over.iteratedSliceBackward`, whose composite is `CategoryTheory.Over.map` of the
structure morphism of `T`.  So the composite is the pushforward along that one functor, on the
nose. -/
public theorem objRestrict_eq_overMap :
    objRestrict B S hS T = SheafOfModules.overMap.{u} B.structureSheaf T.hom :=
  Stacks.SheafOfModules.overFunctor_comp_sliceBackward.{u} B.structureSheaf T.hom

/-- **Restriction to an object of the big fppf site is functorial in the object.**  For
`g : T' ⟶ T` the restriction of `𝒢` to the big fppf site of the scheme `X` of `T`, further
restricted to the big fppf site of the scheme of `T'` read as an object over `X`, is the
restriction of `𝒢` to the big fppf site of the scheme of `T'`.

This is *not* an equality.  The two composites are the pushforwards along
`Over.map g.left ⋙ Over.map T.hom` and along `Over.map T'.hom`, and the comparison of those two
functors of slice categories is `CategoryTheory.Over.mapComp` followed by the identification
`g.left ≫ T.hom = T'.hom`, which is `CategoryTheory.Over.w` for `g`. -/
public noncomputable def objRestrictComp {T T' : BigFppfOver B S hS} (g : T' ⟶ T) :
    objRestrict B S hS T ⋙
        objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left) ≅
      objRestrict B S hS T' := by
  rw [objRestrict_eq_overMap, objRestrict_eq_overMap, objRestrict_eq_overMap]
  exact Stacks.SheafOfModules.overMapCompIso.{u} B.structureSheaf T.hom g.left ≪≫
    eqToIso (congrArg (fun k : T'.left ⟶ B.obj hS =>
      SheafOfModules.overMap.{u} B.structureSheaf k) (Over.w g))

/-! ### Stacks 03DV in the spelling its consumers use -/

/-- **The associated-module functor of the big fppf site of the scheme of `T`, read on the
localization at `T`.**  Pulling an `𝒪_X`-module back along the morphism of ringed sites
`((Sch/S)_fppf / T, 𝒪) → (X_Zar, 𝒪_X)` and then reindexing along the equivalence of Stacks 06WI
is the associated-module functor of the big fppf site of `X`.

This is the bridge between the two spellings of one and the same ringed site.  The comparison of
structure sheaves of the localization at `T` is literally
`AlgebraicGeometry.BigFppfOver.structureMap` of `X` composed with the identity, so the localized
pullback factors as the associated-module functor of `X` followed by the pullback along that
identity; and the pullback along the identity is inverse to the reindexing, which is an
equivalence of module categories by `Stacks.SheafOfModules.reindexEquivalence`. -/
public noncomputable def associatedModuleObjRestrictIso :
    SheafOfModules.pullback.{u} (objSliceStructureMap B S hS T) ⋙ objRestrictFunctor B S hS T ≅
      associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T) := by
  haveI := isContinuous_iteratedSliceBackward B S hS T
  haveI := isContinuous_objToBig B S hS T
  let e := Stacks.SheafOfModules.reindexEquivalence
    (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
    (objEquiv B S hS T) ((structureSheaf B S hS).over T)
  let ψ : structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T) ⟶
      ((Over.iteratedSliceBackward T).sheafPushforwardContinuous RingCat.{u}
        (topology B (objScheme B S hS T) (contains_objScheme B S hS T))
        ((topology B S hS).over T)).obj ((structureSheaf B S hS).over T) := 𝟙 _
  haveI : (SheafOfModules.pushforward.{u} ψ).IsRightAdjoint :=
    e.symm.toAdjunction.isRightAdjoint
  have hEq : objSliceStructureMap B S hS T =
      structureMap B (objScheme B S hS T) (contains_objScheme B S hS T) ≫
      ((opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T)
        ).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥(objScheme B S hS T))
        (topology B (objScheme B S hS T) (contains_objScheme B S hS T))).map ψ :=
    ((congrArg (fun k => structureMap B (objScheme B S hS T) (contains_objScheme B S hS T) ≫ k)
      (((opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T)
        ).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥(objScheme B S hS T))
        (topology B (objScheme B S hS T) (contains_objScheme B S hS T))).map_id _)).trans
      (Category.comp_id _)).symm
  have key : ∀ χ : (objScheme B S hS T).ringCatSheaf ⟶
      ((objToBig B S hS T).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥(objScheme B S hS T))
        ((topology B S hS).over T)).obj ((structureSheaf B S hS).over T),
      objSliceStructureMap B S hS T = χ →
        (SheafOfModules.pushforward.{u} χ).IsRightAdjoint := by
    rintro χ rfl
    infer_instance
  haveI := key _ hEq
  exact Functor.isoWhiskerRight
      (Stacks.SheafOfModules.pullbackCongr hEq ≪≫
        (SheafOfModules.pullbackComp.{u}
          (structureMap B (objScheme B S hS T) (contains_objScheme B S hS T)) ψ).symm)
      (objRestrictFunctor B S hS T) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (Adjunction.leftAdjointUniq (SheafOfModules.pullbackPushforwardAdjunction.{u} ψ)
        e.symm.toAdjunction) _ ≪≫ e.counitIso) ≪≫
    Functor.rightUnitor _

/-- **Stacks 03DV, the step the source leaves implicit, functorial in the object of the big fppf
site.**  For `f : X ⟶ S` the structure morphism of an object `T` of the big fppf category over
`S`, the associated module on the big fppf site of `X` of the pullback `f^*𝓕` of an
`𝒪_S`-module is the restriction to that site of the associated module of `𝓕` on the big fppf
site of `S`:

    `(f^*𝓕)^a ≅ (𝓕^a)|_{(Sch/X)_fppf}`,

naturally in `𝓕`.  This is
`AlgebraicGeometry.BigFppfOver.associatedModuleObjIso` with its target transported from the
localization `(Sch/S)_fppf / T` to the big fppf site of `X` by
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso`, which is the form in which the
proof of Stacks 03DX (1) uses it. -/
public noncomputable def associatedModuleObjRestrictNatIso :
    Scheme.Modules.pullback (objHom B S hS T) ⋙
        associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T) ≅
      associatedModule B S hS ⋙ objRestrict B S hS T :=
  (Functor.isoWhiskerLeft (Scheme.Modules.pullback (objHom B S hS T))
      (associatedModuleObjRestrictIso B S hS T)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (associatedModuleObjIso B S hS T) (objRestrictFunctor B S hS T) ≪≫
    Functor.associator _ _ _

/-! ### Transporting the local datum of Stacks 03DX (1) -/

/-- **The local datum of Stacks 03DX (1) transports along a morphism of the big fppf site.**  If
the restriction of `𝒢` to the big fppf site of the scheme of `T` is the associated module of a
quasi-coherent module `𝓕` there, then for any `g : T' ⟶ T` the restriction of `𝒢` to the big
fppf site of the scheme of `T'` is the associated module of the pullback of `𝓕` along `g`, which
is quasi-coherent by Stacks 01BG.

The isomorphism is the one Stacks 03DV supplies — functoriality in the object,
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` at the object `g` of the big
fppf category over the scheme of `T` — followed by the restriction of the given isomorphism and
the functoriality of restriction,
`AlgebraicGeometry.BigFppfOver.objRestrictComp`.  Unconditional. -/
public theorem hasLocalAssociatedModule_of_hom
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (h : HasLocalAssociatedModule B S hS G T) : HasLocalAssociatedModule B S hS G T' := by
  obtain ⟨M, hM, ⟨e⟩⟩ := h
  refine ⟨(Scheme.Modules.pullback (objHom B (objScheme B S hS T)
      (contains_objScheme B S hS T) (Over.mk g.left))).obj M,
    Stacks.Modules.isQuasicoherent_pullback _ M hM, ⟨?_⟩⟩
  exact (associatedModuleObjRestrictNatIso B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.mk g.left)).app M ≪≫
    (objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.mk g.left)).mapIso e ≪≫ (objRestrictComp B S hS g).app G

/-- **The local datum of Stacks 03DX (1) transports along a refinement of a covering family.**
If every member of a family `X` carries the datum and every member of a family `Y` admits a
morphism to some member of `X`, then every member of `Y` carries it too.

This is the shape in which the datum has to be moved in Stacks 03DX (1): the refinement supplied
by `AlgebraicGeometry.BigFppfOver.exists_coversTop_fpqc_refinement`, whose structure morphisms
are an fpqc covering family of `S`, comes only with morphisms into the members of the original
family, and `AlgebraicGeometry.BigFppfOver.AssociatedModuleDatumOfRefinement` receives the datum
on the original family. -/
public theorem hasLocalAssociatedModule_of_refinement
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {I : Type u₃} {I' : Type u₄}
    {X : I → BigFppfOver B S hS} {Y : I' → BigFppfOver B S hS}
    (hX : ∀ i, HasLocalAssociatedModule B S hS G (X i))
    (hre : ∀ j, ∃ i, Nonempty (Y j ⟶ X i)) (j : I') :
    HasLocalAssociatedModule B S hS G (Y j) := by
  obtain ⟨i, ⟨g⟩⟩ := hre j
  exact hasLocalAssociatedModule_of_hom B S hS G g (hX i)

/-! ### Stacks 03LC (1): the equivalences are compatible with pullback -/

/-- Base change along the structure morphism of `T` is continuous for the two localized fppf
topologies.  This is Mathlib's instance for `CategoryTheory.Over.pullback`, restated at
`AlgebraicGeometry.BigFppfOver.topology`, in which form instance search does not find it. -/
public theorem isContinuous_objBaseChange :
    (Over.pullback T.hom).IsContinuous (topology B S hS)
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  inferInstanceAs ((Over.pullback T.hom).IsContinuous (B.topology.over (B.obj hS))
    (B.topology.over T.left))

attribute [local instance] isContinuous_objBaseChange

/-- **The comparison of structure sheaves of the morphism of ringed big fppf sites attached to
`T`.**  A global function on the scheme of an object `Z` of the big fppf site of `S` restricts
along the first projection of the fibre product to a global function on the scheme of `Z ×_S X`.
This is `CategoryTheory.Sheaf.toPushforwardOverPullback`, read at the structure sheaves of the
two big fppf sites.

It is also the comparison carried by the fibre-product route round the square of ringed sites of
Stacks 04IR, so
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BigSiteStarPullback.lean` states
`AlgebraicGeometry.BigFppfOver.comparisonComp_objStarPullbackIso` against this declaration
rather than against a second copy of it. -/
public noncomputable def objBaseChangeSharp :
    structureSheaf B S hS ⟶
      ((Over.pullback T.hom).sheafPushforwardContinuous RingCat.{u} (topology B S hS)
        (topology B (objScheme B S hS T) (contains_objScheme B S hS T))).obj
        (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  Sheaf.toPushforwardOverPullback B.structureSheaf T.hom

/-- **Pushforward along the morphism of ringed sites attached to `T` is
`SheafOfModules.overPullback`.**  The two are the same functor, the comparison of structure
sheaves of base change being
`AlgebraicGeometry.BigFppfOver.objBaseChangeSharp` on one side and
`CategoryTheory.Sheaf.toPushforwardOverPullback` on the other. -/
public theorem pushforward_objBaseChangeSharp_eq :
    SheafOfModules.pushforward.{u} (objBaseChangeSharp B S hS T) =
      SheafOfModules.overPullback.{u} B.structureSheaf T.hom := rfl

/-- Pushforward of sheaves of modules along the morphism of ringed sites attached to `T` has a
left adjoint: it is `SheafOfModules.overPullback` of the structure morphism `f : X ⟶ S` of `T`,
right adjoint to restriction along postcomposition by `f`. -/
public instance isRightAdjoint_pushforward_objBaseChangeSharp :
    (SheafOfModules.pushforward.{u} (objBaseChangeSharp B S hS T)).IsRightAdjoint :=
  (SheafOfModules.overMapPushforwardAdj.{u} B.structureSheaf T.hom).isRightAdjoint

/-- **The inverse image of sheaves of modules along the morphism of ringed big fppf sites
attached to `T` is restriction to the big fppf site of the scheme of `T`.**  The morphism of
ringed sites `f_big : ((Sch/X)_fppf, 𝒪_X) → ((Sch/S)_fppf, 𝒪_S)` of Stacks 021W is base change
along the structure morphism `f : X ⟶ S` of `T` together with the comparison
`AlgebraicGeometry.BigFppfOver.objBaseChangeSharp`; its pushforward of sheaves of modules is
`SheafOfModules.overPullback` of `f`, which is right adjoint to restriction along
postcomposition, and that restriction is `AlgebraicGeometry.BigFppfOver.objRestrict` by
`AlgebraicGeometry.BigFppfOver.objRestrict_eq_overMap`.  So the inverse image `f_big^*` exists
and agrees with restriction to the big fppf site of `X`, by uniqueness of left adjoints. -/
public noncomputable def objInverseImageIso :
    SheafOfModules.pullback.{u} (objBaseChangeSharp B S hS T) ≅ objRestrict B S hS T :=
  Adjunction.leftAdjointUniq
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (objBaseChangeSharp B S hS T))
      (SheafOfModules.overMapPushforwardAdj.{u} B.structureSheaf T.hom) ≪≫
    eqToIso (objRestrict_eq_overMap B S hS T).symm

/-- **Stacks Project, Tag 03LC part (1), at `τ = fppf`.**  The equivalence of Stacks 03DX is
compatible with pullback: for `f : X ⟶ S` the structure morphism of an object `T` of the big fppf
category over `S`, with `f_big` the induced morphism of ringed big fppf sites of Stacks 021W, and
`𝓕` a quasi-coherent module on `S`,

    `f_big^*(𝓕^a) ≅ (f^*𝓕)^a`,

naturally in `𝓕`.  This is
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` with the restriction functor
replaced by the inverse image of `f_big` through
`AlgebraicGeometry.BigFppfOver.objInverseImageIso`.

The same clause for an arbitrary morphism of schemes rather than an object of the big site, and
at all five `τ` rather than at `fppf` alone, is
`AlgebraicGeometry.BigFppfOver.associatedModuleBasePullbackIso`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModulePullbackBigSites.lean`); what this
declaration adds over it is the identification of `f_big^*` with restriction to the big fppf site
of the scheme of `T`, which is what the proof of Stacks 03DX (1) consumes. -/
@[stacks 03LC "part (1) at τ = fppf"]
public noncomputable def associatedModuleBaseChangeIso :
    associatedModule B S hS ⋙ SheafOfModules.pullback.{u} (objBaseChangeSharp B S hS T) ≅
      Scheme.Modules.pullback (objHom B S hS T) ⋙
        associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T) :=
  Functor.isoWhiskerLeft (associatedModule B S hS) (objInverseImageIso B S hS T) ≪≫
    (associatedModuleObjRestrictNatIso B S hS T).symm

end AlgebraicGeometry.BigFppfOver

/-! ### Stacks 03LC (3): the first of the part's three conjuncts

Part (3) of the source is a **conjunction of three** statements, for `f : T ⟶ S` quasi-compact
and quasi-separated and `τ ∈ {Zariski, étale}`: that `f_*` preserves quasi-coherent sheaves, that
`f_{small, *}` preserves quasi-coherent `𝒪`-modules on the small `τ`-site, and that the square of
the two associated-module functors commutes, `f_{small, *}(𝓕^a) = (f_*𝓕)^a`.  The registration
below is of the first conjunct alone, and its clause string says so and names the carriers of the
other two.

Those other two are proved and registered, at both topologies, in other modules: at `τ = étale`
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_smallPushforward`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePushforwardCartesian.lean`,
line 834)
and `AlgebraicGeometry.SmallEtale.associatedModuleSmallPushforwardIsoOfQcqs` (`:861`), and at
`τ = Zariski` `AlgebraicGeometry.SmallZariski.lcIsQuasicoherentOnSite_smallPushforward`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallZariskiPushforwardSquare.lean:591`)
and `AlgebraicGeometry.SmallZariski.lcAssociatedModuleSmallPushforwardIso` (`:537`).  So part (3)
is complete at both `τ`, each conjunct carrying only the source's own quasi-compact and
quasi-separated hypothesis.

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePushforwardSquare.lean` records
a weaker route at `τ = étale`, in which the second and third conjuncts were reduced to
each other — `AlgebraicGeometry.SmallEtale.associatedModuleSmallPushforwardIso` is the square over
the second conjunct read at one module, and
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_pushforward` the converse
transport.  That reduction is not needed: the input it relies on, Stacks 02KH in degree `0`
over an arbitrary base, is supplied by the Cartesian module above, so neither declaration there is
tagged.

`add_to_stacks` is a command and not a declaration, so this is a doc comment on the section
heading rather than on the registration. -/

add_to_stacks 03LC "part (3), ordinary pushforward preserves quasi-coherence"
  AlgebraicGeometry.pushforward_isQuasicoherent

end
