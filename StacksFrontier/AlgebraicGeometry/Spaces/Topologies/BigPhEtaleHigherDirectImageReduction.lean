module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.PhComparisonSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhEtaleSchemeSlices
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SheafVanishingTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImages
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheavesAndRestriction
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact

/-!
# Higher direct images of the ph-to-étale comparison for algebraic spaces

Let `X` be an algebraic space and `ℱ` a torsion abelian sheaf on `X_étale`. Stacks 0DGT,
part (2), says that `R^i ε_{X,*}(a_X⁻¹ℱ) = 0` for `i > 0`, where
`ε_X : (Spaces/X)_ph ⟶ (Spaces/X)_étale` is the change of topology and `a_X = π_X ∘ ε_X`. This
file reduces that statement to the same statement for schemes, Stacks 0DE4, part (1).

## Main definitions

* `AlgebraicGeometry.PhEtaleHigherDirectImageVanishingOnSchemes`: the vanishing for schemes, in
  the form of the second conjunct of Stacks 0DE4, part (1), for a big ph site of schemes.

## Main results

* `BigPHSpaceSite.isZero_rightDerived_phToBigEtale_abelianInverseImage_of_schemes`: the vanishing
  for algebraic spaces, from the vanishing for the schemes of the chosen big ph site of schemes.

## Implementation notes

The étale sheaf `R^i ε_{X,*}(a_X⁻¹ℱ)` vanishes as soon as its sections vanish over every scheme
`U ⟶ X`, schemes being cover-dense in algebraic spaces for the étale topology (Stacks 0DFV). Those
sections are the global sections of its restriction to `Spaces/U`, which is
`R^i ε_{U,*}(a_U⁻¹ f_{small}⁻¹ ℱ)`: restriction commutes with `ε_*` and is exact and preserves
injectives, and `(a_X⁻¹ℱ)|_U = a_U⁻¹(f_{small}⁻¹ℱ)` by the second square of Stacks 0DGW. Over a
scheme `U` the slices of the big ph and étale sites of algebraic spaces are equivalent to those of
schemes (Stacks 0DFV, localized), compatibly with `ε`, and the small étale site of `U` is
equivalent to the spaces-étale site of the algebraic space it represents (Stacks 03G1), so the
vanishing there is the vanishing for schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ComparingTopologies

universe u

namespace AlgebraicGeometry

/-- **The vanishing of the higher direct images of the ph-to-étale comparison, for the schemes of
a big ph site.** For every scheme `X` of the big ph site `B`, every torsion abelian sheaf `F` on
`X_étale` and every `i ≥ 1`, `R^i ε_{X,*}(a_X⁻¹F) = 0`, where `ε_X` is the change of topology from
the ph to the étale topology on the slice of `B` at `X` and `a_X⁻¹F` is the ph sheafification of
the pullback `π_X⁻¹F` of `F` to the big étale site. This is the second conjunct of Stacks 0DE4,
part (1). -/
def PhEtaleHigherDirectImageVanishingOnSchemes (B : BigPHSite.{u}) : Prop :=
  ∀ (X : (phAssociatedBigEtaleSite B).Scheme)
    (F : Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1}),
    Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) F →
    ∀ i : ℕ, 1 ≤ i → IsZero (((abelianComparisonPushforward B.precoverage
          (phAssociatedBigEtaleSite B).precoverage
          (BigPHSite.etalePrecoverage_le_precoverage B) X).rightDerived i).obj
        ((abelianComparisonPullback B.precoverage
          (phAssociatedBigEtaleSite B).precoverage X).obj
          (((SmallEtale.inclusion (phAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
            Ab.{u + 1} (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
            ((phAssociatedBigEtaleSite B).topology.over X)).obj F)))

namespace BigPHSpaceSite

variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : P.fppfSite = E.fppfSite)

/-- Restriction of abelian sheaves along a continuous functor is additive. -/
local instance sheafPushforwardContinuous_additive {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K] :
    (F.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).Additive where
  map_add := rfl

/-- `ε_{X,*}` on abelian sheaves: restriction along the identity-on-spaces functor of slice
categories. -/
abbrev phToBigEtaleAbelianPushforward (X : P.Spaces) :
    Sheaf (BigPHSpaceOver.topology P X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (E.bigEtaleTopology (etaleSpace P E h X)) AddCommGrpCat.{u + 1} :=
  (Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := X)).inverse.sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace P E h X)) (BigPHSpaceOver.topology P X)

/-- `a_X⁻¹` on abelian sheaves: the abelian inverse image of Stacks 04JC attached to `a_X`. -/
abbrev phToSmallEtaleAbelianInverseImage (X : P.Spaces) :
    Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
        AddCommGrpCat.{u + 1} ⥤
      Sheaf (BigPHSpaceOver.topology P X) AddCommGrpCat.{u + 1} :=
  Sites.abelianInverseImage (phToSmallEtaleMorphism P E h X)

/-! ### Over a scheme -/

set_option maxHeartbeats 1600000 in
-- elaborating the sheaf pushforwards and right derived functors over the ph and étale slices
set_option synthInstance.maxHeartbeats 400000 in
/-- **The change of topology over a scheme, through the scheme slices.** For a scheme `U` of the
big ph site of schemes of `P`, the higher direct images of `ε_U` on the slices of algebraic
spaces vanish on a sheaf `M` as soon as those of the change of topology on the slice of schemes
at `U` vanish on the restriction of `M`: the restrictions along the two slice functors are
equivalences compatible with `ε`. -/
theorem isZero_rightDerived_phToBigEtaleAbelianPushforward_of_schemeSlice (U : P.Schemes)
    (M : Sheaf (BigPHSpaceOver.topology P (P.schemeToSpace.obj U)) AddCommGrpCat.{u + 1})
    (i : ℕ)
    (hz : IsZero (((abelianComparisonPushforward P.schemeSite.precoverage
        (phAssociatedBigEtaleSite P.schemeSite).precoverage
        (BigPHSite.etalePrecoverage_le_precoverage P.schemeSite) U.left).rightDerived i).obj
      (((schemeSliceToSpaceSlice P U).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (P.schemeSite.topology.over U.left)
        (BigPHSpaceOver.topology P (P.schemeToSpace.obj U))).obj M))) :
    IsZero (((phToBigEtaleAbelianPushforward P E h (P.schemeToSpace.obj U)).rightDerived i).obj
      M) := by
  let R := (schemeSliceToSpaceSlice P U).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (P.schemeSite.topology.over U.left) (BigPHSpaceOver.topology P (P.schemeToSpace.obj U))
  let T := (schemeSliceToEtaleSpaceSlice P E h U).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    ((phAssociatedBigEtaleSite P.schemeSite).topology.over U.left)
    (E.bigEtaleTopology (etaleSpace P E h (P.schemeToSpace.obj U)))
  have e : phToBigEtaleAbelianPushforward P E h (P.schemeToSpace.obj U) ⋙ T ≅
      R ⋙ abelianComparisonPushforward P.schemeSite.precoverage
        (phAssociatedBigEtaleSite P.schemeSite).precoverage
        (BigPHSite.etalePrecoverage_le_precoverage P.schemeSite) U.left :=
    ((fullyFaithfulSheafToPresheaf _ _).whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (sheafToPresheaf (BigPHSpaceOver.topology P (P.schemeToSpace.obj U))
          AddCommGrpCat.{u + 1})
        ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).mapIso
          (NatIso.op (schemeSliceToEtaleSpaceSliceCompIso P E h U)).symm))
  exact Stacks.Cohomology.isZero_rightDerived_obj_of_commSquare _ _ R T e M i hz

set_option synthInstance.maxHeartbeats 400000 in
-- instance search over sheaf categories of the big ph, big étale and small étale slice sites
/-- **`a⁻¹` over a scheme, through the scheme slices.** Let `σ` be a functor from the small étale
site of a scheme `U` of the big ph site of schemes of `P` to the spaces-étale site of the algebraic
space represented by `U`, restriction along which is an equivalence, and which is compatible with
the inclusions of both sites into the big ph slice at `U`. Then restricting `a_U⁻¹G` to the slice
of schemes at `U` is the ph sheafification of the pullback of `σ^*G` to the big étale slice of
schemes at `U`, naturally in `G`: both are left adjoint to the same restriction functor. -/
def phToSmallEtaleAbelianInverseImageSchemeSliceIso (U : P.Schemes)
    (σ : SmallEtale (phAssociatedBigEtaleSite P.schemeSite) U.left.obj U.left.property ⥤
      Space.SpacesEtale E.fppfSite S E.fppf_mem (etaleSpace P E h (P.schemeToSpace.obj U)))
    [σ.IsContinuous
      (SmallEtale.topology (phAssociatedBigEtaleSite P.schemeSite) U.left.obj U.left.property)
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
        (etaleSpace P E h (P.schemeToSpace.obj U)))]
    [(σ.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite P.schemeSite) U.left.obj U.left.property)
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
        (etaleSpace P E h (P.schemeToSpace.obj U)))).IsEquivalence]
    (ι : σ ⋙ Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem
          (etaleSpace P E h (P.schemeToSpace.obj U)) ⋙
          (Over.postEquiv (canonicalSpaceEquivalence P E h).1
            (X := P.schemeToSpace.obj U)).inverse ≅
        SmallEtale.inclusion (phAssociatedBigEtaleSite P.schemeSite) U.left.obj U.left.property ⋙
          schemeSliceToSpaceSlice P U) :
    phToSmallEtaleAbelianInverseImage P E h (P.schemeToSpace.obj U) ⋙
        (schemeSliceToSpaceSlice P U).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (P.schemeSite.topology.over U.left)
          (BigPHSpaceOver.topology P (P.schemeToSpace.obj U)) ≅
      σ.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology (phAssociatedBigEtaleSite P.schemeSite) U.left.obj U.left.property)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
            (etaleSpace P E h (P.schemeToSpace.obj U))) ⋙
        (SmallEtale.inclusion (phAssociatedBigEtaleSite P.schemeSite) U.left.obj
            U.left.property).sheafPullback AddCommGrpCat.{u + 1}
          (SmallEtale.topology (phAssociatedBigEtaleSite P.schemeSite) U.left.obj U.left.property)
          ((phAssociatedBigEtaleSite P.schemeSite).topology.over U.left) ⋙
        abelianComparisonPullback P.schemeSite.precoverage
          (phAssociatedBigEtaleSite P.schemeSite).precoverage U.left := by
  let Y := P.schemeToSpace.obj U
  let JP := BigPHSpaceOver.topology P Y
  let JS := Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h Y)
  let Js := SmallEtale.topology (phAssociatedBigEtaleSite P.schemeSite) U.left.obj U.left.property
  let incl := SmallEtale.inclusion (phAssociatedBigEtaleSite P.schemeSite) U.left.obj
    U.left.property
  let Φ := schemeSliceToSpaceSlice P U
  let RΦ := Φ.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (P.schemeSite.topology.over U.left) JP
  let Rσ := σ.sheafPushforwardContinuous AddCommGrpCat.{u + 1} Js JS
  let acp := abelianComparisonPushforward P.schemeSite.precoverage
    (phAssociatedBigEtaleSite P.schemeSite).precoverage
    (BigPHSite.etalePrecoverage_le_precoverage P.schemeSite) U.left
  let Rincl := incl.sheafPushforwardContinuous AddCommGrpCat.{u + 1} Js
    ((phAssociatedBigEtaleSite P.schemeSite).topology.over U.left)
  let a := Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward JP
    (phToSmallEtaleMorphism P E h Y)
  let b := (incl.sheafAdjunctionContinuous AddCommGrpCat.{u + 1} Js
      ((phAssociatedBigEtaleSite P.schemeSite).topology.over U.left)).comp
    (abelianComparisonAdjunction P.schemeSite.precoverage
      (phAssociatedBigEtaleSite P.schemeSite).precoverage
      (BigPHSite.etalePrecoverage_le_precoverage P.schemeSite) U.left)
  have : HasBinaryBiproducts (Sheaf JP AddCommGrpCat.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  let aY := phToSmallEtaleMorphism P E h Y
  let pY := Stacks.Topos.AbelianPushforward.abelianPushforward JP aY
  let RσT := σ.sheafPushforwardContinuous (Type (u + 1)) Js JS
  let fJP := sheafCompose JP (forget AddCommGrpCat.{u + 1})
  let fJS := sheafCompose JS (forget AddCommGrpCat.{u + 1})
  let fJs := sheafCompose Js (forget AddCommGrpCat.{u + 1})
  let φ₂ : Rσ ⋙ fJs ≅ fJS ⋙ RσT := Iso.refl _
  let φL : (pY ⋙ Rσ) ⋙ fJs ≅ (fJP ⋙ aY.pushforward) ⋙ RσT :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft pY φ₂ ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Stacks.Topos.AbelianPushforward.abelianPushforward_forgetIso JP aY)
        RσT
  let ψ : ((fJP ⋙ aY.pushforward) ⋙ RσT) ⋙ sheafToPresheaf Js (Type (u + 1)) ≅
      ((RΦ ⋙ acp ⋙ Rincl) ⋙ fJs) ⋙ sheafToPresheaf Js (Type (u + 1)) :=
    Functor.isoWhiskerLeft
      (sheafToPresheaf JP AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{u + 1}))
      ((Functor.whiskeringLeft _ _ (Type (u + 1))).mapIso (NatIso.op ι).symm)
  let α : pY ⋙ Rσ ≅ RΦ ⋙ acp ⋙ Rincl :=
    Stacks.Cohomology.abelianSheafNatIsoOfUnderlying Js _ _
      (((fullyFaithfulSheafToPresheaf Js (Type (u + 1))).whiskeringRight _).preimageIso
        (Functor.isoWhiskerRight φL (sheafToPresheaf Js (Type (u + 1))) ≪≫ ψ))
  exact Stacks.Cohomology.leftAdjointCompIsoOfRightAdjointComp a b Rσ.asEquivalence
    RΦ.asEquivalence α

/-- **Stacks 0DGT, part (2), over a scheme, from the scheme case.** For a scheme `U` of the big ph
site of schemes of `P` and a torsion abelian sheaf `G` on the small étale site of the algebraic
space represented by `U`, the higher direct images `R^i ε_{U,*}(a_U⁻¹G)` vanish for `i > 0`,
granted the same statement for the schemes of the big ph site of schemes. -/
theorem isZero_rightDerived_phToBigEtaleAbelianPushforward_scheme
    (hsch : PhEtaleHigherDirectImageVanishingOnSchemes P.schemeSite) (U : P.Schemes)
    (G : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace P E h (P.schemeToSpace.obj U))) AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace P E h (P.schemeToSpace.obj U))) G)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((phToBigEtaleAbelianPushforward P E h (P.schemeToSpace.obj U)).rightDerived i).obj
      ((phToSmallEtaleAbelianInverseImage P E h (P.schemeToSpace.obj U)).obj G)) := by
  obtain ⟨σ, hc, hcc, -, hAb, ⟨ι⟩⟩ := exists_smallEtaleSchemeChart P E h U
  have ht := Stacks.Torsion.torsionSheafProperty_sheafPushforwardContinuous
    (J := SmallEtale.topology (phAssociatedBigEtaleSite P.schemeSite) U.left.obj U.left.property)
    σ G hG
  refine isZero_rightDerived_phToBigEtaleAbelianPushforward_of_schemeSlice P E h U _ i ?_
  exact (hsch U.left _ ht i hi).of_iso
    (((abelianComparisonPushforward P.schemeSite.precoverage
      (phAssociatedBigEtaleSite P.schemeSite).precoverage
      (BigPHSite.etalePrecoverage_le_precoverage P.schemeSite) U.left).rightDerived i).mapIso
      ((phToSmallEtaleAbelianInverseImageSchemeSliceIso P E h U σ ι).app G))

/-! ### Restriction along a morphism of algebraic spaces -/

/-- The identity-on-objects functor of an equivalence commutes with composition by a morphism, on
slices. -/
def overMapPostEquivInverseIso {C D : Type*} [Category* C] [Category* D] (G : C ≌ D)
    {X Y : C} (g : Y ⟶ X) :
    Over.map (G.functor.map g) ⋙ (Over.postEquiv G (X := X)).inverse ≅
      (Over.postEquiv G (X := Y)).inverse ⋙ Over.map g :=
  NatIso.ofComponents (fun W ↦ Over.isoMk (Iso.refl (G.inverse.obj W.left)) (by
    change 𝟙 _ ≫ (G.inverse.map W.hom ≫ G.unitIso.inv.app Y) ≫ g =
      G.inverse.map (W.hom ≫ G.functor.map g) ≫ G.unitIso.inv.app X
    rw [Category.id_comp, Functor.map_comp, Category.assoc, Category.assoc]
    congr 1
    exact (G.unitIso.inv.naturality g).symm)) (by
    intro V W f
    ext
    change G.inverse.map f.left ≫ 𝟙 _ = 𝟙 _ ≫ G.inverse.map f.left
    rw [Category.comp_id, Category.id_comp])

/-- **`a⁻¹` commutes with restriction along a morphism of algebraic spaces.** For `g : Y ⟶ X`,
the restriction of `a_X⁻¹F` to the big ph site of `Y` is `a_Y⁻¹(g_{small}⁻¹F)`, naturally in `F`;
this is the second square of Stacks 0DGW on left adjoints. -/
def phToSmallEtaleAbelianInverseImageOverMapIso {X Y : P.Spaces} (g : Y ⟶ X) :
    phToSmallEtaleAbelianInverseImage P E h X ⋙
        (Over.map g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (BigPHSpaceOver.topology P Y) (BigPHSpaceOver.topology P X) ≅
      Sites.abelianInverseImage (E.smallEtaleMorphism (etaleMap P E h g)) ⋙
        phToSmallEtaleAbelianInverseImage P E h Y :=
  have : HasBinaryBiproducts (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace P E h X)) AddCommGrpCat.{u + 1}) := HasBinaryBiproducts.of_hasBinaryProducts
  have := Functor.additive_of_preserves_binary_products (phToSmallEtaleAbelianInverseImage P E h X)
  have := Functor.additive_of_preserves_binary_products (phToSmallEtaleAbelianInverseImage P E h Y)
  have := Functor.additive_of_preserves_binary_products
    (Sites.abelianInverseImage (E.smallEtaleMorphism (etaleMap P E h g)))
  Stacks.Cohomology.abelianSheafNatIsoOfUnderlying (BigPHSpaceOver.topology P Y) _ _
    (Functor.isoWhiskerLeft
      (sheafCompose (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
        (forget AddCommGrpCat.{u + 1}))
      (Adjunction.leftAdjointUniq
        (((phToSmallEtaleMorphism P E h X).comp (bigPHMorphism P g)).adj.ofNatIsoRight
          (bigPHSmallEtale_pushforwardCommIso P E h g).symm)
        ((E.smallEtaleMorphism (etaleMap P E h g)).comp (phToSmallEtaleMorphism P E h Y)).adj))

/-- **Restriction commutes with the higher direct images of `ε`.** For `g : Y ⟶ X`, restricting
`R^i ε_{X,*}M` along `g` is `R^i ε_{Y,*}` of the restriction of `M`: restriction is exact and
preserves injective objects, and commutes with `ε_*`. -/
def rightDerivedPhToBigEtaleOverMapIso {X Y : P.Spaces} (g : Y ⟶ X)
    (M : Sheaf (BigPHSpaceOver.topology P X) AddCommGrpCat.{u + 1}) (i : ℕ) :
    ((Over.map (etaleMap P E h g)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (E.bigEtaleTopology (etaleSpace P E h Y)) (E.bigEtaleTopology (etaleSpace P E h X))).obj
        (((phToBigEtaleAbelianPushforward P E h X).rightDerived i).obj M) ≅
      ((phToBigEtaleAbelianPushforward P E h Y).rightDerived i).obj
        (((Over.map g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (BigPHSpaceOver.topology P Y) (BigPHSpaceOver.topology P X)).obj M) :=
  let R := (Over.map g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (BigPHSpaceOver.topology P Y) (BigPHSpaceOver.topology P X)
  let T := (Over.map (etaleMap P E h g)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (E.bigEtaleTopology (etaleSpace P E h Y)) (E.bigEtaleTopology (etaleSpace P E h X))
  have : R.PreservesHomology := Functor.preservesHomologyOfExact R
  have : T.PreservesHomology := Functor.preservesHomologyOfExact T
  Stacks.Cohomology.rightDerivedObjIsoOfCommSquare (phToBigEtaleAbelianPushforward P E h X)
    (phToBigEtaleAbelianPushforward P E h Y) R T
    (((fullyFaithfulSheafToPresheaf _ _).whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (sheafToPresheaf (BigPHSpaceOver.topology P X) AddCommGrpCat.{u + 1})
        ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).mapIso
          (NatIso.op (overMapPostEquivInverseIso (canonicalSpaceEquivalence P E h).1 g)).symm)))
    M i

/-! ### The reduction -/

/-- **Stacks 0DGT, part (2), from the scheme case.** Let `X` be an algebraic space of the big ph
site `P` and `ℱ` a torsion abelian sheaf on `X_étale`. Then the higher direct images
`R^i ε_{X,*}(a_X⁻¹ℱ)` vanish for `i > 0`, provided the same holds for the schemes of the chosen
big ph site of schemes of `P` (`AlgebraicGeometry.PhEtaleHigherDirectImageVanishingOnSchemes`,
the second conjunct of Stacks 0DE4, part (1)). -/
theorem isZero_rightDerived_phToBigEtale_abelianInverseImage_of_schemes (X : P.Spaces)
    [HasSheafify (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
      AddCommGrpCat.{u + 1}]
    [HasSheafify (E.bigEtaleTopology (etaleSpace P E h X)) AddCommGrpCat.{u + 1}]
    [HasSheafify (BigPHSpaceOver.topology P X) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (BigPHSpaceOver.topology P X) AddCommGrpCat.{u + 1})]
    [(phToBigEtaleAbelianPushforward P E h X).Additive]
    (hsch : PhEtaleHigherDirectImageVanishingOnSchemes P.schemeSite)
    (ℱ : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
      AddCommGrpCat.{u + 1})
    (hℱ : Stacks.Torsion.torsionSheafProperty
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X)) ℱ)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((phToBigEtaleAbelianPushforward P E h X).rightDerived i).obj
      ((phToSmallEtaleAbelianInverseImage P E h X).obj ℱ)) := by
  let G := (canonicalSpaceEquivalence P E h).1
  refine Stacks.Cohomology.isZero_sheafOver_of_isZero_sections_overImage
    (schemeToEtaleSpace P E h) E.topology (etaleSpace P E h X) _ fun U f ↦ ?_
  obtain ⟨g, rfl⟩ : ∃ g : P.schemeToSpace.obj U ⟶ X, G.functor.map g = f :=
    ⟨G.functor.preimage f, G.functor.map_preimage f⟩
  have hF := Stacks.Torsion.torsionSheafProperty_abelianInverseImage
    (E.smallEtaleMorphism (etaleMap P E h g)) ℱ hℱ
  have hz := (((isZero_rightDerived_phToBigEtaleAbelianPushforward_scheme P E h hsch U _ hF i
    hi).of_iso (((phToBigEtaleAbelianPushforward P E h
      (P.schemeToSpace.obj U)).rightDerived i).mapIso
        ((phToSmallEtaleAbelianInverseImageOverMapIso P E h g).app ℱ))).of_iso
    (rightDerivedPhToBigEtaleOverMapIso P E h g
      ((phToSmallEtaleAbelianInverseImage P E h X).obj ℱ) i))
  have hz' := (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
    (op (Over.mk (𝟙 (etaleSpace P E h (P.schemeToSpace.obj U)))))).map_isZero hz
  change IsZero ((((phToBigEtaleAbelianPushforward P E h X).rightDerived i).obj
    ((phToSmallEtaleAbelianInverseImage P E h X).obj ℱ)).obj.obj
      (op (Over.mk (𝟙 _ ≫ etaleMap P E h g)))) at hz'
  rwa [Category.id_comp] at hz'

end BigPHSpaceSite

end AlgebraicGeometry
