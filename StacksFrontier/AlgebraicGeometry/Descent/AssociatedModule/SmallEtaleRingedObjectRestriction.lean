module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullback

/-!
# The associated module of a pullback along an object of the small étale site

`AlgebraicGeometry.SmallEtale.associatedModuleOverObjIso`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleOpenCoverQuasicoherence.lean`)
proves the step Stacks 03DV leaves implicit, `(𝓕|_V)^a ≅ (𝓕^a)|_{V_étale}`, for `V` an **open**
of `S`.  This file proves the same comparison at an **arbitrary object** `U` of the small étale
site of `S`.

The two statements are not the same statement with a wider `V`.  For an open `V` the restriction
of an `𝒪_S`-module downstairs is restriction to a slice of the small Zariski site of `S`, and the
comparison is read off from the inclusion of that site being representably flat, which is what
`SheafOfModules.overFunctorPullbackIso` consumes; for an arbitrary `U` the scheme `Y` of `U` is
not an open subscheme of `S`, `U` is not an object of the small Zariski site at all, and the
restriction downstairs is the pullback `f^*𝓕` along the structure morphism `f : Y ⟶ S` of `U`.
So the comparison proved here is

    `(f^*𝓕)^a ≅ (𝓕^a)|_{S_étale/U}`,

the associated module being formed on the small Zariski site of `Y` on the left and on that of
`S` on the right.  It is the square of ringed sites

    Opens S  --- f⁻¹ --->  Opens Y
       |                      |
    opensToSmallEtale     objToSmallEtaleOver
       |                      |
       v                      v
    S_étale  -- Over.star U -->  S_étale / U

whose horizontal isomorphism is the geometric content: the preimage `f⁻¹(V)` of an open of `S`
is the fibre product `Y ×_S V`, which in the slice over `U` is the binary product `U ⨯ V`.

Through the equivalence of ringed sites of
`AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence` the comparison is then read on
the small étale site of `Y` itself, which is
`AlgebraicGeometry.SmallEtale.associatedModuleObjRestrictIso`:

    `(f^*𝓕)^a ≅ (𝓕^a)|_{Y_étale}`.

This is the small étale counterpart of
`AlgebraicGeometry.BigFppfOver.associatedModuleObjIso`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ObjectRestriction.lean`), and the proof
follows it step for step; the geometric and ring-level inputs are the small étale versions of the
ones used there.

## Main definitions

* `AlgebraicGeometry.SmallEtale.objHom`: the structure morphism `f : Y ⟶ S` of an object `U` of
  the small étale site of `S`.
* `AlgebraicGeometry.SmallEtale.objToSmallEtaleOver`: the small Zariski site of `Y` inside the
  localization of the small étale site of `S` at `U`, `W ↦ (W ↪ Y)`.
* `AlgebraicGeometry.SmallEtale.objStarIso`: the natural isomorphism `f⁻¹(V) ≅ U ⨯ V` of functors
  from the small Zariski site of `S` into the localization at `U`.
* `AlgebraicGeometry.SmallEtale.objSliceStructureMap`: the comparison of structure sheaves of the
  morphism of ringed sites `(S_étale/U, 𝒪) → (Y_Zar, 𝒪_Y)`.

## Main results

* `AlgebraicGeometry.SmallEtale.associatedModuleObjIso` and
  `AlgebraicGeometry.SmallEtale.associatedModuleObjObjIso`: **the comparison at an arbitrary
  object of the small étale site**, `(f^*𝓕)^a ≅ (𝓕^a)|_{S_étale/U}`.
* `AlgebraicGeometry.SmallEtale.associatedModuleObjRestrictIso` and
  `AlgebraicGeometry.SmallEtale.associatedModuleObjRestrictObjIso`: **the same comparison read on
  the small étale site of `Y`**, `(f^*𝓕)^a ≅ (𝓕^a)|_{Y_étale}`, where the right-hand side is the
  crossover `AlgebraicGeometry.SmallEtale.objRestrict`.
* `AlgebraicGeometry.SmallEtale.comparisonComp_objStarIso`: the two routes round the square carry
  the same comparison of structure sheaves, the second proviso of
  `SheafOfModules.pullbackSquareIso`.
* `AlgebraicGeometry.SmallEtale.subsingleton_hom_objToSmallEtaleOver` and
  `AlgebraicGeometry.SmallEtale.subsingleton_hom_starOpens`: the two uniqueness statements that
  make the geometric isomorphism and its naturality formal.
* `AlgebraicGeometry.SmallEtale.associatedModuleObjSliceIso`: the bridge between the two readings
  — the slice associated-module functor followed by the reindexing *is* the associated-module
  functor of the small étale site of `Y`.

## Implementation notes

Nothing here carries a `stacks` attribute.  Stacks 03DV has two clauses, and neither is this:
clause (1) is about the big sites and clause (2) asserts quasi-coherence of `𝓕^a` on the small
sites, which is `AlgebraicGeometry.SmallEtale`
`.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`.  What is proved here is the
compatibility of `𝓕 ↦ 𝓕^a` with pullback, which the source uses inside the proof of 03DV and of
Stacks 03DX (2) without stating it as a clause of either.

The target of the comparison is stated on the slice site `S_étale/U` first and only then
transported to `Y_étale`, for the same reason as on the big site: stating it on the slice keeps
`SheafOfModules.overFunctor` on the right-hand side, which is the functor the globalization step
restricts along.  The transport is
`AlgebraicGeometry.SmallEtale.associatedModuleObjSliceIso`, and it is an adjunction argument
rather than a computation: `SheafOfModules.pushforwardComp` is `Iso.refl`, so the reindexing
followed by restriction along the small Zariski site of `Y` *is* the pushforward along
`AlgebraicGeometry.SmallEtale.objSliceStructureMap` up to the identity
`φ ≫ F(𝟙) = φ`; taking left adjoints and cancelling the equivalence
`AlgebraicGeometry.SmallEtale.objRestrictEquivalence` identifies the two left adjoints.

`AlgebraicGeometry.SmallEtale.objSliceStructureMap` is *literally*
`AlgebraicGeometry.SmallEtale.structureMap` of `Y`: the structure sheaf of the localization at
`U`, restricted along the small Zariski site of `Y`, *is* the structure sheaf of the small étale
site of `Y` restricted along its own small Zariski site, both being the global functions on the
underlying scheme.  The type ascription is what records that, and it is why no comparison of
structure sheaves has to be built for the right-hand column of the square.

`AlgebraicGeometry.SmallEtale.objSliceStructureMap_comparisonComp` is proved by `congrArg` and
`Eq.trans` rather than by `simp` or `rw`: the goal mentions
`AlgebraicGeometry.Scheme.ringCatSheaf`, whose type `TopCat.Sheaf` is the Grothendieck-topology
`CategoryTheory.Sheaf` only at default transparency, and the tactics elaborate the motive at a
lower one.

`AlgebraicGeometry.Scheme.Opens.topIso_inv_appTop_of_comp`, the ring-level content of the square,
is reused from
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ObjectRestriction.lean`, which is why
that big-fppf module is imported here; nothing else is taken from it.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS)

/-- The structure morphism `f : Y ⟶ S` of an object `U` of the small étale site of `S`. -/
abbrev objHom : objScheme B S hS U ⟶ S := U.obj.hom.hom

/-- The small Zariski site of the scheme `Y` of `U` inside the localization of the small étale
site of `S` at `U`: an open `W` of `Y` goes to `W ↪ Y`, read as an object over `U` through the
localization equivalence. -/
noncomputable abbrev objToSmallEtaleOver : (objScheme B S hS U).Opens ⥤ Over U :=
  opensToSmallEtale B (objScheme B S hS U) (contains_objScheme B S hS U) ⋙
    (localizationEquivalence B S hS U).functor

/-- The small Zariski site of the scheme of `U` is continuous into the localization at `U`. -/
instance isContinuous_objToSmallEtaleOver :
    (objToSmallEtaleOver B S hS U).IsContinuous
      (Opens.grothendieckTopology ↥(objScheme B S hS U)) ((topology B S hS).over U) :=
  Functor.isContinuous_comp _ _ _
    (topology B (objScheme B S hS U) (contains_objScheme B S hS U)) _

/-! ### The two uniqueness statements -/

/-- There is at most one morphism from an object of the localization at `U` into an open of the
scheme of `U`: the localization equivalence turns it into a morphism into an open of that scheme
in its own small étale site, where the open immersion is a monomorphism. -/
theorem subsingleton_hom_objToSmallEtaleOver (Z : Over U) (A : (objScheme B S hS U).Opens) :
    Subsingleton (Z ⟶ (objToSmallEtaleOver B S hS U).obj A) :=
  let := subsingleton_hom_opensToSmallEtale B (objScheme B S hS U)
    (contains_objScheme B S hS U) ((localizationEquivalence B S hS U).inverse.obj Z) A
  Equiv.subsingleton
    (((localizationEquivalence B S hS U).symm.toAdjunction.homEquiv Z
      ((opensToSmallEtale B (objScheme B S hS U)
        (contains_objScheme B S hS U)).obj A)).symm)

/-- There is at most one morphism of the localization at `U` from an object into `U ⨯ V` for `V`
an open of `S`: such a morphism is a morphism into `V` in the small étale site of `S` by the
adjunction `CategoryTheory.Over.forgetAdjStar`, and there is at most one of those. -/
theorem subsingleton_hom_starOpens (Z : Over U) (V : S.Opens) :
    Subsingleton (Z ⟶ (Over.star U).obj ((opensToSmallEtale B S hS).obj V)) :=
  let := subsingleton_hom_opensToSmallEtale B S hS ((Over.forget U).obj Z) V
  Equiv.subsingleton
    (((Over.forgetAdjStar U).homEquiv Z ((opensToSmallEtale B S hS).obj V)).symm)

/-! ### Ranges of the structure morphisms -/

/-- The structure morphism over `S` of an open of the scheme of `U`, read in the localization at
`U`, is the open immersion followed by the structure morphism of `U`. -/
theorem objToSmallEtaleOver_obj_left_obj_hom_hom (A : (objScheme B S hS U).Opens) :
    ((objToSmallEtaleOver B S hS U).obj A).left.obj.hom.hom = A.ι ≫ objHom B S hS U := rfl

/-- An open of the scheme of `U` inside the preimage of an open `V` of `S` has structure morphism
over `S` with range inside `V`. -/
theorem range_le_of_le_preimage (V : S.Opens) (A : (objScheme B S hS U).Opens)
    (hA : A ≤ (Opens.map (objHom B S hS U).base).obj V) :
    Set.range ⇑(((objToSmallEtaleOver B S hS U).obj A).left.obj.hom.hom) ⊆ (V : Set ↥S) := by
  rintro x ⟨y, rfl⟩
  have hy : A.ι y ∈ (A : Set ↥(objScheme B S hS U)) := by
    rw [← Scheme.Opens.range_ι]
    exact ⟨y, rfl⟩
  exact hA hy

/-- The structure morphism over `S` of an object of the localization at `U` factors through the
structure morphism of `U`.  This is `CategoryTheory.Over.w` read on underlying schemes. -/
theorem left_obj_hom_hom_eq (Z : Over U) :
    Z.left.obj.hom.hom = Z.hom.hom.left.hom ≫ objHom B S hS U := by
  rw [← ObjectProperty.FullSubcategory.comp_hom]
  exact congrArg (fun k : Z.left.obj.left ⟶ B.obj S hS => k.hom) (Over.w Z.hom.hom).symm

/-- **The range condition for the inverse comparison.**  An object `Z` of the localization at `U`
with a morphism into an open `V` of `S` has, read over the scheme of `U`, structure morphism with
range inside the preimage of `V`. -/
theorem range_inverse_le_preimage (Z : Over U) (V : S.Opens)
    (g : Z.left ⟶ (opensToSmallEtale B S hS).obj V) :
    Set.range ⇑(((localizationEquivalence B S hS U).inverse.obj Z).obj.hom.hom)
      ⊆ (((Opens.map (objHom B S hS U).base).obj V) : Set ↥(objScheme B S hS U)) := by
  rintro x ⟨y, rfl⟩
  have h := BigEtaleOver.range_le_of_hom B S hS g.hom (Set.mem_range_self y)
  have key : ⇑(Z.left.obj.hom.hom) y
      = ⇑(objHom B S hS U) (⇑(Z.hom.hom.left.hom) y) := by
    rw [left_obj_hom_hom_eq B S hS U Z]
    rfl
  rw [key] at h
  exact h

/-! ### The geometric content of the comparison -/

/-- **The geometric content of the comparison at an arbitrary object.**  The preimage `f⁻¹(V)` of
an open `V` of `S` under the structure morphism of `U` maps to the product `U ⨯ V` of the
localization at `U`: its structure morphism over `S` has range inside `V`, so it maps to `V` in
the small étale site of `S`, and the adjunction `CategoryTheory.Over.forgetAdjStar` turns that
into a morphism into `U ⨯ V`. -/
noncomputable def objStarHom (V : S.Opens) :
    (objToSmallEtaleOver B S hS U).obj ((Opens.map (objHom B S hS U).base).obj V) ⟶
      (Over.star U).obj ((opensToSmallEtale B S hS).obj V) :=
  (Over.forgetAdjStar U).homEquiv _ ((opensToSmallEtale B S hS).obj V)
    (homOfRangeLe B S hS V (range_le_of_le_preimage B S hS U V _ le_rfl))

/-- The product `U ⨯ V` maps back to `f⁻¹(V)`: read over the scheme of `U` its structure
morphism has range inside the preimage of `V`, because it maps to `V` over `S` by the second
projection. -/
noncomputable def objStarInv (V : S.Opens) :
    (Over.star U).obj ((opensToSmallEtale B S hS).obj V) ⟶
      (objToSmallEtaleOver B S hS U).obj ((Opens.map (objHom B S hS U).base).obj V) :=
  ((localizationEquivalence B S hS U).counitIso.app
      ((Over.star U).obj ((opensToSmallEtale B S hS).obj V))).inv ≫
    (localizationEquivalence B S hS U).functor.map
      (homOfRangeLe B (objScheme B S hS U) (contains_objScheme B S hS U)
        ((Opens.map (objHom B S hS U).base).obj V)
        (range_inverse_le_preimage B S hS U
          ((Over.star U).obj ((opensToSmallEtale B S hS).obj V)) V prod.snd))

/-- **The geometric content of the comparison at an arbitrary object, naturally.**  The two
functors from the small Zariski site of `S` to the localization of the small étale site of `S` at
`U` — take the preimage under the structure morphism of `U`, and take the product with `U` — are
isomorphic.  Both composites of the two maps are endomorphisms with at most one inhabitant. -/
noncomputable def objStarIso :
    Opens.map (objHom B S hS U).base ⋙ objToSmallEtaleOver B S hS U ≅
      opensToSmallEtale B S hS ⋙ Over.star U :=
  NatIso.ofComponents
    (fun V =>
      { hom := objStarHom B S hS U V
        inv := objStarInv B S hS U V
        hom_inv_id := Subsingleton.elim
          (h := subsingleton_hom_objToSmallEtaleOver B S hS U _ _) _ _
        inv_hom_id := Subsingleton.elim
          (h := subsingleton_hom_starOpens B S hS U _ V) _ _ })
    (fun {_ Y} _ => Subsingleton.elim (h := subsingleton_hom_starOpens B S hS U _ Y) _ _)

/-- The comparison `f⁻¹(V) ⟶ U ⨯ V`, followed by the projection to `V`, is the unique morphism
`f⁻¹(V) ⟶ V` of the small étale site of `S`.  This is the counit identity of
`CategoryTheory.Over.forgetAdjStar`, the counit being the second projection. -/
theorem objStarIso_hom_app_left_comp_snd (V : S.Opens) :
    (((objStarIso B S hS U).hom.app V).left :
        ((objToSmallEtaleOver B S hS U).obj
          ((Opens.map (objHom B S hS U).base).obj V)).left ⟶
          U ⨯ (opensToSmallEtale B S hS).obj V) ≫ prod.snd
      = homOfRangeLe B S hS V (range_le_of_le_preimage B S hS U V _ le_rfl) := by
  have h := ((Over.forgetAdjStar U).homEquiv
      ((objToSmallEtaleOver B S hS U).obj ((Opens.map (objHom B S hS U).base).obj V))
      ((opensToSmallEtale B S hS).obj V)).symm_apply_apply
    (homOfRangeLe B S hS V (range_le_of_le_preimage B S hS U V _ le_rfl))
  simp only [Adjunction.homEquiv_counit] at h
  refine Eq.trans ?_ h
  exact congrArg
    (fun k : U ⨯ (opensToSmallEtale B S hS).obj V ⟶ (opensToSmallEtale B S hS).obj V =>
      ((objStarIso B S hS U).hom.app V).left ≫ k)
    (Over.forgetAdjStar_counit_app U ((opensToSmallEtale B S hS).obj V)).symm

/-! ### The structure-sheaf comparison -/

/-- Including the small Zariski site of `S` and then taking the product with `U` is a continuous
functor into the localization at `U`. -/
instance isContinuous_opensToSmallEtaleStarObj :
    (opensToSmallEtale B S hS ⋙ Over.star U).IsContinuous
      (Opens.grothendieckTopology ↥S) ((topology B S hS).over U) :=
  Functor.isContinuous_comp _ _ _ (topology B S hS) _

/-- Taking the preimage under the structure morphism of `U` and then including the small Zariski
site of the scheme of `U` is a continuous functor into the localization at `U`. -/
instance isContinuous_mapObjToSmallEtaleOver :
    (Opens.map (objHom B S hS U).base ⋙ objToSmallEtaleOver B S hS U).IsContinuous
      (Opens.grothendieckTopology ↥S) ((topology B S hS).over U) :=
  Functor.isContinuous_comp _ _ _
    (Opens.grothendieckTopology ↥(objScheme B S hS U)) _

/-- The comparison of structure sheaves of the morphism of ringed sites
`(S_étale/U, 𝒪) → (Y_Zar, 𝒪_Y)`, the localization of the small étale site of `S` at `U` read
through the scheme `Y` of `U`.  It is literally
`AlgebraicGeometry.SmallEtale.structureMap` of `Y`: the structure sheaf of the localization at
`U`, restricted along the small Zariski site of `Y`, *is* the structure sheaf of the small étale
site of `Y` restricted along its own small Zariski site. -/
noncomputable abbrev objSliceStructureMap :
    (objScheme B S hS U).ringCatSheaf ⟶
      ((objToSmallEtaleOver B S hS U).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥(objScheme B S hS U))
        ((topology B S hS).over U)).obj ((structureSheaf B S hS).over U) :=
  structureMap B (objScheme B S hS U) (contains_objScheme B S hS U)

/-- **The two routes round the square of ringed sites carry the same comparison of structure
sheaves.**  Both composites restrict a section of `𝒪_S` over `V` to the open `f⁻¹(V)` of the
scheme of `U`: going round the small étale site one restricts along the product projection and
then along the comparison `f⁻¹(V) ⟶ U ⨯ V`, whose composite is the unique morphism
`f⁻¹(V) ⟶ V`; going round the small Zariski sites one applies `f^♯` and then identifies global
functions.  The two agree by
`AlgebraicGeometry.Scheme.Opens.topIso_inv_appTop_of_comp`. -/
theorem comparisonComp_objStarIso :
    SheafOfModules.comparisonComp (structureMap B S hS) (SheafOfModules.pushforwardOver U) ≫
        (Functor.sheafPushforwardContinuousNatTrans (objStarIso B S hS U).hom RingCat.{u}
          (Opens.grothendieckTopology ↥S) ((topology B S hS).over U)).app
          ((structureSheaf B S hS).over U) =
      SheafOfModules.comparisonComp (objHom B S hS U).toRingCatSheafHom
        (objSliceStructureMap B S hS U) := by
  ext : 2
  funext V
  show (structureMap B S hS).hom.app V ≫
      (structureSheaf B S hS).obj.map
        (prod.snd : U ⨯ (opensToSmallEtale B S hS).obj V.unop ⟶
          (opensToSmallEtale B S hS).obj V.unop).op ≫
      (structureSheaf B S hS).obj.map
        ((((objStarIso B S hS U).hom.app V.unop).left :
          ((objToSmallEtaleOver B S hS U).obj
            ((Opens.map (objHom B S hS U).base).obj V.unop)).left ⟶
            U ⨯ (opensToSmallEtale B S hS).obj V.unop)).op =
    ((objHom B S hS U).toRingCatSheafHom).hom.app V ≫
      (objSliceStructureMap B S hS U).hom.app
        (Opposite.op ((Opens.map (objHom B S hS U).base).obj V.unop))
  have hcomb : (structureSheaf B S hS).obj.map
        (prod.snd : U ⨯ (opensToSmallEtale B S hS).obj V.unop ⟶
          (opensToSmallEtale B S hS).obj V.unop).op ≫
      (structureSheaf B S hS).obj.map
        ((((objStarIso B S hS U).hom.app V.unop).left :
          ((objToSmallEtaleOver B S hS U).obj
            ((Opens.map (objHom B S hS U).base).obj V.unop)).left ⟶
            U ⨯ (opensToSmallEtale B S hS).obj V.unop)).op
      = (structureSheaf B S hS).obj.map
        (homOfRangeLe B S hS V.unop
          (range_le_of_le_preimage B S hS U V.unop _ le_rfl)).op :=
    ((structureSheaf B S hS).obj.map_comp _ _).symm.trans
      (congrArg (fun k : ((objToSmallEtaleOver B S hS U).obj
            ((Opens.map (objHom B S hS U).base).obj V.unop)).left ⟶
          (opensToSmallEtale B S hS).obj V.unop =>
        (structureSheaf B S hS).obj.map k.op)
        (objStarIso_hom_app_left_comp_snd B S hS U V.unop))
  refine Eq.trans (congrArg (fun k => (structureMap B S hS).hom.app V ≫ k) hcomb) ?_
  have key := Scheme.Opens.topIso_inv_appTop_of_comp (objHom B S hS U) V.unop
    ((homOfRangeLe B S hS V.unop
      (range_le_of_le_preimage B S hS U V.unop _ le_rfl)).hom.left.hom)
    ((BigEtaleOver.hom_hom_eq B S hS (homOfRangeLe B S hS V.unop
        (range_le_of_le_preimage B S hS U V.unop _ le_rfl)).hom).symm.trans
      (objToSmallEtaleOver_obj_left_obj_hom_hom B S hS U _))
  show (forget₂ CommRingCat RingCat.{u}).map (Scheme.Opens.topIso (X := S) V.unop).inv ≫
      (forget₂ CommRingCat RingCat.{u}).map
        ((homOfRangeLe B S hS V.unop
          (range_le_of_le_preimage B S hS U V.unop _ le_rfl)).hom.left.hom).appTop =
    (forget₂ CommRingCat RingCat.{u}).map ((objHom B S hS U).app V.unop) ≫
      (forget₂ CommRingCat RingCat.{u}).map
        (Scheme.Opens.topIso (X := objScheme B S hS U)
          ((Opens.map (objHom B S hS U).base).obj V.unop)).inv
  exact ((forget₂ CommRingCat RingCat.{u}).map_comp _ _).symm.trans
    ((congrArg (forget₂ CommRingCat RingCat.{u}).map key).trans
      ((forget₂ CommRingCat RingCat.{u}).map_comp _ _))

/-! ### The comparison on the slice site -/

/-- The pushforward of presheaves of modules along the localized comparison has a left adjoint:
the source of the localized continuous functor, the small Zariski site of the scheme of `U`, is a
small category. -/
instance presheafPushforward_objSliceStructureMap_isRightAdjoint :
    (PresheafOfModules.pushforward.{u} (objSliceStructureMap B S hS U).hom).IsRightAdjoint :=
  Stacks.ModulePullback.isRightAdjoint_pushforward _

/-- The pushforward of sheaves of modules along the localized comparison has a left adjoint. -/
instance sheafPushforward_objSliceStructureMap_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (objSliceStructureMap B S hS U)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u}
    (objSliceStructureMap B S hS U)).isRightAdjoint

/-- **Stacks 03DV, the step the source leaves implicit, at an arbitrary object of the small étale
site of `S`.**  The associated module of the pullback of an `𝒪_S`-module along the structure
morphism `f : Y ⟶ S` of an object `U` of the small étale site of `S` is the restriction of its
associated module to the localization of `S_étale` at `U`. -/
noncomputable def associatedModuleObjIso :
    Scheme.Modules.pullback (objHom B S hS U) ⋙
        SheafOfModules.pullback.{u} (objSliceStructureMap B S hS U) ≅
      SheafOfModules.pullback.{u} (structureMap B S hS) ⋙
        SheafOfModules.overFunctor.{u} (structureSheaf B S hS) U :=
  haveI : (SheafOfModules.pushforward.{u} (objHom B S hS U).toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward (objHom B S hS U)).IsRightAdjoint
  SheafOfModules.pullbackSquareIso.{u} (objHom B S hS U).toRingCatSheafHom
      (objSliceStructureMap B S hS U) (structureMap B S hS)
      (SheafOfModules.pushforwardOver U) (objStarIso B S hS U)
      (comparisonComp_objStarIso B S hS U) ≪≫
    Functor.isoWhiskerLeft _ (SheafOfModules.pullbackPushforwardOverIso.{u} U)

/-- **Stacks 03DV, the step the source leaves implicit, at an arbitrary object of the small étale
site and at one module.**  `(f^*𝓕)^a ≅ (𝓕^a)|_{S_étale/U}`. -/
noncomputable def associatedModuleObjObjIso (𝓕 : S.Modules) :
    (SheafOfModules.pullback.{u} (objSliceStructureMap B S hS U)).obj
        ((Scheme.Modules.pullback (objHom B S hS U)).obj 𝓕) ≅
      ((associatedModule B S hS).obj 𝓕).over U :=
  (associatedModuleObjIso B S hS U).app 𝓕

/-! ### Reading the comparison on the small étale site of the scheme of `U` -/

/-- The comparison of structure sheaves of the composite morphism of ringed sites is the
comparison of the small étale site of the scheme of `U`: the second factor is the identity. -/
theorem objSliceStructureMap_comparisonComp :
    SheafOfModules.comparisonComp
        (structureMap B (objScheme B S hS U) (contains_objScheme B S hS U))
        (𝟙 (Stacks.SheafOfModules.reindexRing
          (topology B (objScheme B S hS U) (contains_objScheme B S hS U))
          (localizationEquivalence B S hS U) ((structureSheaf B S hS).over U)))
      = objSliceStructureMap B S hS U :=
  (congrArg
    (fun k => structureMap B (objScheme B S hS U) (contains_objScheme B S hS U) ≫ k)
    (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)

/-- Reindexing along the localization equivalence and then restricting along the small Zariski
site of the scheme of `U` is restriction along the localized comparison.  Pushforward is
compatible with composition on the nose, `SheafOfModules.pushforwardComp` being `Iso.refl`. -/
noncomputable def pushforwardObjSliceCompIso :
    objRestrictFunctor B S hS U ⋙
        restrictModule B (objScheme B S hS U) (contains_objScheme B S hS U) ≅
      SheafOfModules.pushforward.{u} (objSliceStructureMap B S hS U) :=
  SheafOfModules.pushforwardComp.{u}
      (structureMap B (objScheme B S hS U) (contains_objScheme B S hS U))
      (𝟙 (Stacks.SheafOfModules.reindexRing
        (topology B (objScheme B S hS U) (contains_objScheme B S hS U))
        (localizationEquivalence B S hS U) ((structureSheaf B S hS).over U))) ≪≫
    SheafOfModules.pushforwardCongr.{u} (objSliceStructureMap_comparisonComp B S hS U)

/-- The right adjoint of the slice associated-module functor, composed with the inverse of the
reindexing equivalence, is restriction along the small Zariski site of the scheme of `U`. -/
noncomputable def rightAdjointObjSliceIso :
    (objRestrictEquivalence B S hS U).inverse ⋙
        SheafOfModules.pushforward.{u} (objSliceStructureMap B S hS U) ≅
      restrictModule B (objScheme B S hS U) (contains_objScheme B S hS U) :=
  Functor.isoWhiskerLeft _ (pushforwardObjSliceCompIso B S hS U).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (objRestrictEquivalence B S hS U).counitIso _ ≪≫
    Functor.leftUnitor _

/-- **The slice associated-module functor, read on the small étale site of the scheme of `U`, is
its associated-module functor.**  Both are left adjoints, and
`AlgebraicGeometry.SmallEtale.rightAdjointObjSliceIso` identifies their right adjoints. -/
noncomputable def associatedModuleObjSliceIso :
    SheafOfModules.pullback.{u} (objSliceStructureMap B S hS U) ⋙ objRestrictFunctor B S hS U ≅
      associatedModule B (objScheme B S hS U) (contains_objScheme B S hS U) :=
  Adjunction.leftAdjointUniq
    (((SheafOfModules.pullbackPushforwardAdjunction.{u} (objSliceStructureMap B S hS U)).comp
        (objRestrictEquivalence B S hS U).toAdjunction).ofNatIsoRight
      (rightAdjointObjSliceIso B S hS U))
    (associatedModuleAdjunction B (objScheme B S hS U) (contains_objScheme B S hS U))

/-- **Stacks 03DV, the step the source leaves implicit, at an arbitrary object of the small étale
site, read on the small étale site of the scheme of `U`.**  The associated module of the pullback
of an `𝒪_S`-module along the structure morphism `f : Y ⟶ S` of `U` is the crossover restriction
of its associated module to the small étale site of `Y`. -/
noncomputable def associatedModuleObjRestrictIso :
    Scheme.Modules.pullback (objHom B S hS U) ⋙
        associatedModule B (objScheme B S hS U) (contains_objScheme B S hS U) ≅
      associatedModule B S hS ⋙ objRestrict B S hS U :=
  Functor.isoWhiskerLeft _ (associatedModuleObjSliceIso B S hS U).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (associatedModuleObjIso B S hS U) (objRestrictFunctor B S hS U) ≪≫
    Functor.associator _ _ _

/-- **Stacks 03DV, the step the source leaves implicit, at an arbitrary object of the small étale
site and at one module, on the small étale site of the scheme of `U`.**
`(f^*𝓕)^a ≅ (𝓕^a)|_{Y_étale}`. -/
noncomputable def associatedModuleObjRestrictObjIso (𝓕 : S.Modules) :
    (associatedModule B (objScheme B S hS U) (contains_objScheme B S hS U)).obj
        ((Scheme.Modules.pullback (objHom B S hS U)).obj 𝓕) ≅
      (objRestrict B S hS U).obj ((associatedModule B S hS).obj 𝓕) :=
  (associatedModuleObjRestrictIso B S hS U).app 𝓕

end AlgebraicGeometry.SmallEtale

end
