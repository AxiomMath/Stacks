module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The associated module of a restriction to an arbitrary object of the big fppf site

`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenRestriction` proves the step Stacks
03DV leaves implicit, `(𝓕|_V)^a ≅ (𝓕^a)|_{(Sch/V)}`, for `V` an **open** of `S`.  This file
proves the same comparison at an **arbitrary object** `T` of the big fppf category over `S`.

The two statements are not the same statement with a wider `V`.  For an open `V` of `S` the
restriction of an `𝒪_S`-module downstairs is restriction to a slice of the *small Zariski site*
of `S`; for an arbitrary `T` the scheme `X` of `T` is not an open subscheme of `S` and the
restriction downstairs is the pullback `f^*𝓕` along the structure morphism `f : X ⟶ S` of `T`.
So the comparison proved here is

    `(f^*𝓕)^a ≅ (𝓕^a)|_{(Sch/S)_fppf / T}`,

the associated module being formed on the small Zariski site of `X` on the left and on that of
`S` on the right.  It is the square of ringed sites

    Opens S  --- f⁻¹ --->  Opens X
       |                      |
    opensToBig            objToBig T
       |                      |
       v                      v
    (Sch/S)  -- Over.star T -->  (Sch/S)/T

whose horizontal isomorphism is the geometric content: the preimage `f⁻¹(V)` of an open of `S`
is the fibre product `T ×_S V`, which in the slice over `T` is the binary product `T ⨯ V`.

For `V : S.Opens` that content came from the *small Zariski site* inclusion preserving finite
limits, `AlgebraicGeometry.BigFppfOver.preservesFiniteLimits_opensToBig`, and there is no
analogue of that for an arbitrary `T`: `T` is not an object of the small Zariski site at all, so
`AlgebraicGeometry.BigFppfOver.opensObjInfIsoProd` has nothing to say about `V ⨯ T`.  What
replaces it is that a morphism *into* an open of `S` is unique and exists exactly when the
structure morphism has range inside that open
(`AlgebraicGeometry.BigFppfOver.subsingleton_hom_opensObj` and
`AlgebraicGeometry.BigFppfOver.homOfRangeLe`), which identifies `T ⨯ V` with `f⁻¹(V)` without
any flatness.  Nothing here is false at an arbitrary object; the flatness in the open case is a
convenience of that case, not a hypothesis of the comparison.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.objScheme` and `AlgebraicGeometry.BigFppfOver.objHom`: the
  scheme `X` of an object `T` of the big fppf category over `S`, and its structure morphism
  `f : X ⟶ S`.
* `AlgebraicGeometry.BigFppfOver.objToBig`: the small Zariski site of `X` inside the
  localization of the big fppf category at `T`, `W ↦ (W ↪ X)`.
* `AlgebraicGeometry.BigFppfOver.objSliceStructureMap`: the comparison of structure sheaves of
  the morphism of ringed sites `((Sch/S)_fppf / T, 𝒪) → (X_Zar, 𝒪_X)`, whose pullback is the
  associated-module functor of the localization at `T`.
* `AlgebraicGeometry.BigFppfOver.objStarIso`: the natural isomorphism `f⁻¹(V) ≅ T ⨯ V` of
  functors from the small Zariski site of `S` into the localization at `T`.

## Main results

* `AlgebraicGeometry.BigFppfOver.associatedModuleObjIso` and
  `AlgebraicGeometry.BigFppfOver.associatedModuleObjObjIso`: **the comparison at an arbitrary
  object**, `(f^*𝓕)^a ≅ (𝓕^a)|_{(Sch/S)_fppf / T}`.
* `AlgebraicGeometry.BigFppfOver.comparisonComp_objStarIso`: the two routes round the square
  carry the same comparison of structure sheaves, the second proviso of
  `SheafOfModules.pullbackSquareIso`.
* `AlgebraicGeometry.Scheme.Opens.topIso_inv_appTop_of_comp`: restriction along a morphism of
  schemes commutes with the identification `Γ(Y, V) ≅ Γ(V, 𝒪_V)`, which is the ring-level
  content of the square.
* `AlgebraicGeometry.BigFppfOver.subsingleton_hom_objToBig` and
  `AlgebraicGeometry.BigFppfOver.subsingleton_hom_starOpens`: the two uniqueness statements that
  make the geometric isomorphism and its naturality formal.

## Implementation notes

Nothing is tagged.  This is infrastructure for Stacks 03DX (1), whose covering set is the
*equivalence of categories* it asserts, and for the globalization step
`AlgebraicGeometry.BigFppfOver.EssImageAssociatedModuleQcohLocal`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EssImageGlobalization.lean:137`), whose
covering family is a family of arbitrary objects of the site — which is exactly why the open
case does not suffice.

The target of the comparison is stated on the slice site `(Sch/S)_fppf / T` rather than on
`(Sch/X)_fppf`.  The two are equivalent as ringed sites — `CategoryTheory.Over.iteratedSliceEquiv`
on the nose for the structure sheaves, which is how `objSliceStructureMap` can be literally
`AlgebraicGeometry.BigFppfOver.structureMap` of `X` — and quasi-coherence transports along that
equivalence by `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff`.  Stating it on the
slice keeps `SheafOfModules.overFunctor` on the right-hand side, which is the functor the
globalization step restricts along.

`AlgebraicGeometry.BigFppfOver.isContinuous_iteratedSliceBackward` is an `inferInstanceAs`
bridge and is *not* found by instance search: its statement mentions `topology B X hX`, whose
`hX` is a proposition that unification cannot recover at the transparency instance search uses.
Every use below therefore introduces it with `haveI`.

`CategoryTheory.Over.star` resists the tactic framework here: `((Over.star T).obj Y).left` is
accepted as `T ⨯ Y` by term elaboration, but `((Over.star T).obj Y).hom` is not accepted as
`prod.fst`, because unfolding it reaches `CategoryTheory.Limits.getLimitCone`, which this
library does not see exposed.  `rw` and `simp only` additionally fail on motives that are only
type-correct at default transparency.  So the comparisons below are built through
`CategoryTheory.Over.forgetAdjStar` rather than through `prod.lift`, and the structure-sheaf
identity is assembled from `congrArg` and `Eq.trans` rather than rewritten.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Restriction along a morphism commutes with the identification of global functions.**  For
`f : X ⟶ Y` and `V` an open of `Y`, the morphism `f⁻¹(V) ⟶ V` that `f` restricts to carries the
identification `Γ(Y, V) ≅ Γ(V, 𝒪_V)` to `f^♯`.  This is
`AlgebraicGeometry.Scheme.Opens.topIso_inv_appTop` with the inclusion of one open in another
replaced by an arbitrary morphism of schemes. -/
public theorem Scheme.Opens.topIso_inv_appTop_of_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (l : (f ⁻¹ᵁ V).toScheme ⟶ V.toScheme)
    (hl : l ≫ V.ι = (f ⁻¹ᵁ V).ι ≫ f) :
    (V.topIso).inv ≫ l.appTop = f.app V ≫ ((f ⁻¹ᵁ V).topIso).inv := by
  have hres : l = f.resLE V (f ⁻¹ᵁ V) le_rfl := by
    rw [← cancel_mono V.ι, hl, Scheme.Hom.resLE_comp_ι]
  rw [hres, show Scheme.Hom.appTop (Scheme.Hom.resLE f V (f ⁻¹ᵁ V) le_rfl)
      = Scheme.Hom.app (Scheme.Hom.resLE f V (f ⁻¹ᵁ V) le_rfl) ⊤ from rfl,
    Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app, Iso.inv_hom_id_assoc]

end AlgebraicGeometry

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- The scheme of an object of the big fppf category over `S`. -/
public abbrev objScheme : Scheme.{u} := (toScheme B S hS).obj T

/-- The scheme of an object of the big fppf category over `S` is one of the site. -/
public theorem contains_objScheme : B.Contains (objScheme B S hS T) := T.left.2

/-- The structure morphism `f : X ⟶ S` of an object of the big fppf category over `S`. -/
public abbrev objHom : objScheme B S hS T ⟶ S := T.hom.hom

/-- The structure morphism of an object of the big fppf category over `S` factors any morphism
out of it: this is `CategoryTheory.Over.w` read on underlying schemes. -/
public theorem hom_hom_comp {Z W : BigFppfOver B S hS} (g : Z ⟶ W) :
    Z.hom.hom = g.left.hom ≫ W.hom.hom := by
  rw [← ObjectProperty.FullSubcategory.comp_hom]
  exact congrArg (fun k : Z.left ⟶ B.obj hS => k.hom) (Over.w g).symm

/-- The small Zariski site of the scheme `X` of `T` inside the localization of the big fppf
category over `S` at `T`: an open `W` of `X` goes to `W ↪ X`, read as an object over `T`. -/
public noncomputable abbrev objToBig :
    (objScheme B S hS T).Opens ⥤ Over T :=
  opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T) ⋙ Over.iteratedSliceBackward T

/-- Passing from the big fppf site of the scheme of `T` to the localization at `T` is
continuous.  This is Mathlib's instance for `CategoryTheory.Over.iteratedSliceBackward`, restated
at `AlgebraicGeometry.BigFppfOver.topology`; instance search does not find it in that form. -/
@[sga "3 IV 4.5.1" "partial"]
public instance isContinuous_iteratedSliceBackward :
    (Over.iteratedSliceBackward T).IsContinuous
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T))
      ((topology B S hS).over T) :=
  inferInstanceAs ((Over.iteratedSliceBackward T).IsContinuous (B.topology.over T.left)
    ((B.topology.over (B.obj hS)).over T))

/-- The small Zariski site of the scheme of `T` is continuous into the localization at `T`. -/
public instance isContinuous_objToBig :
    (objToBig B S hS T).IsContinuous
      (Opens.grothendieckTopology ↥(objScheme B S hS T)) ((topology B S hS).over T) :=
  haveI := isContinuous_iteratedSliceBackward B S hS T
  Functor.isContinuous_comp _ _ _
    (topology B (objScheme B S hS T) (contains_objScheme B S hS T)) _

/-- There is at most one morphism from an object of the localization at `T` into an open of the
scheme of `T`: the iterated slice equivalence turns it into a morphism into an open of that
scheme in its own big fppf site, where the open immersion is a monomorphism. -/
public theorem subsingleton_hom_objToBig (Z : Over T) (A : (objScheme B S hS T).Opens) :
    Subsingleton (Z ⟶ (objToBig B S hS T).obj A) := by
  refine ⟨fun g₁ g₂ => (Over.iteratedSliceEquiv T).functor.map_injective ?_⟩
  exact Subsingleton.elim (h := subsingleton_hom_opensObj B (objScheme B S hS T)
    (contains_objScheme B S hS T) _ A) _ _

/-- There is at most one morphism of the localization at `T` from an object into `T ⨯ V` for `V`
an open of `S`: such a morphism is a morphism into `V` over `S` by the adjunction
`CategoryTheory.Over.forgetAdjStar`, and there is at most one of those. -/
public theorem subsingleton_hom_starOpens (Z : Over T) (V : S.Opens) :
    Subsingleton (Z ⟶ (Over.star T).obj (opensObj B S hS V)) :=
  let := subsingleton_hom_opensObj B S hS ((Over.forget T).obj Z) V
  Equiv.subsingleton ((Over.forgetAdjStar T).homEquiv Z (opensObj B S hS V)).symm

/-- The structure morphism over `S` of an open of the scheme of `T`, read in the big fppf
category over `S`, is the open immersion followed by the structure morphism of `T`. -/
public theorem objToBig_obj_left_hom_hom (A : (objScheme B S hS T).Opens) :
    ((objToBig B S hS T).obj A).left.hom.hom = A.ι ≫ objHom B S hS T := rfl

/-- An open of the scheme of `T` inside the preimage of an open `V` of `S` has structure
morphism over `S` with range inside `V`. -/
public theorem range_le_of_le_preimage (V : S.Opens) (A : (objScheme B S hS T).Opens)
    (hA : A ≤ (Opens.map (objHom B S hS T).base).obj V) :
    Set.range ⇑(((objToBig B S hS T).obj A).left.hom.hom) ⊆ (V : Set ↥S) := by
  rintro x ⟨y, rfl⟩
  have hy : A.ι y ∈ (A : Set ↥(objScheme B S hS T)) := by
    rw [← Scheme.Opens.range_ι]
    exact ⟨y, rfl⟩
  exact hA hy

/-- **The range condition for the inverse comparison.**  An object `Z` of the localization at
`T` with a morphism into an open `V` of `S` has, read over the scheme of `T`, structure
morphism with range inside the preimage of `V`. -/
public theorem range_forward_le_preimage (Z : Over T) (V : S.Opens)
    (g : Z.left ⟶ opensObj B S hS V) :
    Set.range ⇑(((Over.iteratedSliceForward T).obj Z).hom.hom)
      ⊆ (((Opens.map (objHom B S hS T).base).obj V) : Set ↥(objScheme B S hS T)) := by
  rintro x ⟨y, rfl⟩
  have h := range_le_of_hom B S hS g ⟨y, rfl⟩
  have key : ⇑(Z.left.hom.hom) y
      = ⇑(objHom B S hS T) (⇑(Z.hom.left.hom) y) := by
    rw [hom_hom_comp B S hS Z.hom]
    rfl
  rwa [key] at h

/-- **The geometric content of the comparison at an arbitrary object.**  The preimage `f⁻¹(V)`
of an open `V` of `S` under the structure morphism of `T` maps to the product `T ⨯ V` of the
localization at `T`: its structure morphism over `S` has range inside `V`, so it maps to `V`
over `S`, and the adjunction `CategoryTheory.Over.forgetAdjStar` turns that into a morphism into
`T ⨯ V`. -/
public noncomputable def objStarHom (V : S.Opens) :
    (objToBig B S hS T).obj ((Opens.map (objHom B S hS T).base).obj V) ⟶
      (Over.star T).obj (opensObj B S hS V) :=
  (Over.forgetAdjStar T).homEquiv _ (opensObj B S hS V)
    (homOfRangeLe B S hS V (range_le_of_le_preimage B S hS T V _ le_rfl))

/-- The product `T ⨯ V` maps back to `f⁻¹(V)`: read over the scheme of `T` its structure
morphism has range inside the preimage of `V`, because it maps to `V` over `S` by the second
projection. -/
public noncomputable def objStarInv (V : S.Opens) :
    (Over.star T).obj (opensObj B S hS V) ⟶
      (objToBig B S hS T).obj ((Opens.map (objHom B S hS T).base).obj V) :=
  ((Over.iteratedSliceEquiv T).unitIso.app ((Over.star T).obj (opensObj B S hS V))).hom ≫
    (Over.iteratedSliceBackward T).map (homOfRangeLe B (objScheme B S hS T)
      (contains_objScheme B S hS T) _
      (range_forward_le_preimage B S hS T ((Over.star T).obj (opensObj B S hS V)) V prod.snd))

/-- **The geometric content of the comparison at an arbitrary object, naturally.**  The two
functors from the small Zariski site of `S` to the localization of the big fppf category at `T`
— take the preimage under the structure morphism of `T`, and take the product with `T` — are
isomorphic.  Both composites of the two maps are endomorphisms with at most one inhabitant. -/
public noncomputable def objStarIso :
    Opens.map (objHom B S hS T).base ⋙ objToBig B S hS T ≅
      opensToBig B S hS ⋙ Over.star T :=
  NatIso.ofComponents
    (fun V =>
      { hom := objStarHom B S hS T V
        inv := objStarInv B S hS T V
        hom_inv_id := Subsingleton.elim
          (h := subsingleton_hom_objToBig B S hS T _ _) _ _
        inv_hom_id := Subsingleton.elim
          (h := subsingleton_hom_starOpens B S hS T _ V) _ _ })
    (fun {_ Y} _ => Subsingleton.elim (h := subsingleton_hom_starOpens B S hS T _ Y) _ _)

/-- Including the small Zariski site of `S` and then taking the product with `T` is a continuous
functor into the localization at `T`. -/
public instance isContinuous_opensToBigStarObj :
    (opensToBig B S hS ⋙ Over.star T).IsContinuous
      (Opens.grothendieckTopology ↥S) ((topology B S hS).over T) :=
  Functor.isContinuous_comp _ _ _ (topology B S hS) _

/-- Taking the preimage under the structure morphism of `T` and then including the small Zariski
site of the scheme of `T` is a continuous functor into the localization at `T`. -/
public instance isContinuous_mapObjToBig :
    (Opens.map (objHom B S hS T).base ⋙ objToBig B S hS T).IsContinuous
      (Opens.grothendieckTopology ↥S) ((topology B S hS).over T) :=
  haveI := isContinuous_objToBig B S hS T
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology ↥(objScheme B S hS T)) _

/-- The comparison of structure sheaves of the morphism of ringed sites
`((Sch/S)_fppf / T, 𝒪) → (X_Zar, 𝒪_X)`, the localization at `T` of the big fppf site of `S`
read through the scheme `X` of `T`.  It is literally
`AlgebraicGeometry.BigFppfOver.structureMap` of `X`: the structure sheaf of the localization at
`T`, restricted along the small Zariski site of `X`, *is* the structure sheaf of the big fppf
site of `X` restricted along its own small Zariski site. -/
public noncomputable abbrev objSliceStructureMap :
    (objScheme B S hS T).ringCatSheaf ⟶
      ((objToBig B S hS T).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥(objScheme B S hS T))
        ((topology B S hS).over T)).obj ((structureSheaf B S hS).over T) :=
  structureMap B (objScheme B S hS T) (contains_objScheme B S hS T)

/-- The comparison `f⁻¹(V) ⟶ T ⨯ V`, followed by the projection to `V`, is the unique morphism
`f⁻¹(V) ⟶ V` over `S`.  This is the counit identity of
`CategoryTheory.Over.forgetAdjStar`, the counit being the second projection. -/
public theorem objStarIso_hom_app_left_comp_snd (V : S.Opens) :
    (((objStarIso B S hS T).hom.app V).left :
        ((objToBig B S hS T).obj ((Opens.map (objHom B S hS T).base).obj V)).left ⟶
          T ⨯ (opensToBig B S hS).obj V) ≫ prod.snd
      = homOfRangeLe B S hS V (range_le_of_le_preimage B S hS T V _ le_rfl) := by
  have h := ((Over.forgetAdjStar T).homEquiv
      ((objToBig B S hS T).obj ((Opens.map (objHom B S hS T).base).obj V))
      (opensObj B S hS V)).symm_apply_apply
    (homOfRangeLe B S hS V (range_le_of_le_preimage B S hS T V _ le_rfl))
  simp only [Adjunction.homEquiv_counit] at h
  refine Eq.trans ?_ h
  exact congrArg
    (fun k : T ⨯ (opensToBig B S hS).obj V ⟶ (opensToBig B S hS).obj V =>
      ((objStarIso B S hS T).hom.app V).left ≫ k)
    (Over.forgetAdjStar_counit_app T (opensObj B S hS V)).symm

/-- **The two routes round the square of ringed sites carry the same comparison of structure
sheaves.**  Both composites restrict a section of `𝒪_S` over `V` to the open `f⁻¹(V)` of the
scheme of `T`: going round the big site one restricts along the product projection and then
along the comparison `f⁻¹(V) ⟶ T ⨯ V`, whose composite is the unique morphism `f⁻¹(V) ⟶ V`;
going round the small sites one applies `f^♯` and then identifies global functions.  The two
agree by `AlgebraicGeometry.Scheme.Opens.topIso_inv_appTop_of_comp`. -/
public theorem comparisonComp_objStarIso :
    SheafOfModules.comparisonComp (structureMap B S hS) (SheafOfModules.pushforwardOver T) ≫
        (Functor.sheafPushforwardContinuousNatTrans (objStarIso B S hS T).hom RingCat.{u}
          (Opens.grothendieckTopology ↥S) ((topology B S hS).over T)).app
          ((structureSheaf B S hS).over T) =
      SheafOfModules.comparisonComp (objHom B S hS T).toRingCatSheafHom
        (objSliceStructureMap B S hS T) := by
  ext : 2
  funext V
  change (structureMap B S hS).hom.app V ≫
      (structureSheaf B S hS).obj.map
        (prod.snd : T ⨯ (opensToBig B S hS).obj V.unop ⟶ (opensToBig B S hS).obj V.unop).op ≫
      (structureSheaf B S hS).obj.map
        ((((objStarIso B S hS T).hom.app V.unop).left :
          ((objToBig B S hS T).obj ((Opens.map (objHom B S hS T).base).obj V.unop)).left ⟶
            T ⨯ (opensToBig B S hS).obj V.unop)).op =
    ((objHom B S hS T).toRingCatSheafHom).hom.app V ≫
      (objSliceStructureMap B S hS T).hom.app
        (Opposite.op ((Opens.map (objHom B S hS T).base).obj V.unop))
  have hcomb : (structureSheaf B S hS).obj.map
        (prod.snd : T ⨯ (opensToBig B S hS).obj V.unop ⟶ (opensToBig B S hS).obj V.unop).op ≫
      (structureSheaf B S hS).obj.map
        ((((objStarIso B S hS T).hom.app V.unop).left :
          ((objToBig B S hS T).obj ((Opens.map (objHom B S hS T).base).obj V.unop)).left ⟶
            T ⨯ (opensToBig B S hS).obj V.unop)).op
      = (structureSheaf B S hS).obj.map
        (homOfRangeLe B S hS V.unop
          (range_le_of_le_preimage B S hS T V.unop _ le_rfl)).op :=
    ((structureSheaf B S hS).obj.map_comp _ _).symm.trans
      (congrArg (fun k : ((objToBig B S hS T).obj
            ((Opens.map (objHom B S hS T).base).obj V.unop)).left ⟶
          (opensToBig B S hS).obj V.unop =>
        (structureSheaf B S hS).obj.map k.op)
        (objStarIso_hom_app_left_comp_snd B S hS T V.unop))
  refine Eq.trans (congrArg (fun k => (structureMap B S hS).hom.app V ≫ k) hcomb) ?_
  have key := Scheme.Opens.topIso_inv_appTop_of_comp (objHom B S hS T) V.unop
    ((homOfRangeLe B S hS V.unop
      (range_le_of_le_preimage B S hS T V.unop _ le_rfl)).left.hom)
    ((hom_hom_eq B S hS (homOfRangeLe B S hS V.unop
        (range_le_of_le_preimage B S hS T V.unop _ le_rfl))).symm.trans
      (objToBig_obj_left_hom_hom B S hS T _))
  change (forget₂ CommRingCat RingCat.{u}).map (Scheme.Opens.topIso (X := S) V.unop).inv ≫
      (forget₂ CommRingCat RingCat.{u}).map
        ((homOfRangeLe B S hS V.unop
          (range_le_of_le_preimage B S hS T V.unop _ le_rfl)).left.hom).appTop =
    (forget₂ CommRingCat RingCat.{u}).map ((objHom B S hS T).app V.unop) ≫
      (forget₂ CommRingCat RingCat.{u}).map
        (Scheme.Opens.topIso (X := objScheme B S hS T)
          ((Opens.map (objHom B S hS T).base).obj V.unop)).inv
  exact ((forget₂ CommRingCat RingCat.{u}).map_comp _ _).symm.trans
    ((congrArg (forget₂ CommRingCat RingCat.{u}).map key).trans
      ((forget₂ CommRingCat RingCat.{u}).map_comp _ _))

/-- The pushforward of presheaves of modules along the localized comparison has a left adjoint:
the source of the localized continuous functor, the small Zariski site of the scheme of `T`, is
a small category. -/
public instance presheafPushforward_objSliceStructureMap_isRightAdjoint :
    (PresheafOfModules.pushforward.{u} (objSliceStructureMap B S hS T).hom).IsRightAdjoint :=
  Stacks.ModulePullback.isRightAdjoint_pushforward _

/-- The pushforward of sheaves of modules along the localized comparison has a left adjoint. -/
public instance sheafPushforward_objSliceStructureMap_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (objSliceStructureMap B S hS T)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u}
    (objSliceStructureMap B S hS T)).isRightAdjoint

/-- **Stacks 03DV, the step the source leaves implicit, at an arbitrary object of the big fppf
site.**  The associated module of the pullback of an `𝒪_S`-module along the structure morphism
`f : X ⟶ S` of an object `T` of the big fppf category over `S` is the restriction of its
associated module to the localization of the big fppf site of `S` at `T`. -/
public noncomputable def associatedModuleObjIso :
    Scheme.Modules.pullback (objHom B S hS T) ⋙
        SheafOfModules.pullback.{u} (objSliceStructureMap B S hS T) ≅
      SheafOfModules.pullback.{u} (structureMap B S hS) ⋙
        SheafOfModules.overFunctor.{u} (structureSheaf B S hS) T :=
  haveI : (SheafOfModules.pushforward.{u} (objHom B S hS T).toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward (objHom B S hS T)).IsRightAdjoint
  SheafOfModules.pullbackSquareIso.{u} (objHom B S hS T).toRingCatSheafHom
      (objSliceStructureMap B S hS T) (structureMap B S hS)
      (SheafOfModules.pushforwardOver T) (objStarIso B S hS T)
      (comparisonComp_objStarIso B S hS T) ≪≫
    Functor.isoWhiskerLeft _ (SheafOfModules.pullbackPushforwardOverIso.{u} T)

/-- **Stacks 03DV, the step the source leaves implicit, at an arbitrary object and at one
module.**  `(f^*𝓕)^a ≅ (𝓕^a)|_{(Sch/S)_fppf / T}`. -/
public noncomputable def associatedModuleObjObjIso (𝓕 : S.Modules) :
    (SheafOfModules.pullback.{u} (objSliceStructureMap B S hS T)).obj
        ((Scheme.Modules.pullback (objHom B S hS T)).obj 𝓕) ≅
      ((associatedModule B S hS).obj 𝓕).over T :=
  (associatedModuleObjIso B S hS T).app 𝓕

end AlgebraicGeometry.BigFppfOver

end
