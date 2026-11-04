module

public import StacksFrontier.CategoryTheory.Action.DiscreteRestriction
public import StacksFrontier.CategoryTheory.Functor.AmbientCommutingSquare
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianFiniteGModules
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.InverseImage
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.MorphismOfSites

/-!
# Inverse image of finite locally constant abelian sheaves, and restriction of the action

Let `(C, J)` and `(D, K)` be sites and let `u : C ⥤ D` be a continuous functor whose inverse
image of sheaves of sets preserves finite products. Suppose the finite locally constant sheaves
of sets on each site have been identified with the finite continuous sets of a topological group,
and that the two identifications match the inverse image with restriction along a continuous
homomorphism of those groups. This file supplies what is needed to deduce the same for sheaves of
abelian groups: the transport of Stacks Tag 0DV5 part (2) then carries the inverse image of
finite locally constant abelian sheaves to restriction of finite discrete modules.

## Main definitions

* `Stacks.Sites.AbelianPullback.abelianSheafPullbackIso` — the inverse image of abelian sheaves
  is the inverse image of the underlying sheaves of sets carrying the induced group operations.
* `AlgebraicGeometry.ContinuousGSet.resIsFinite` and
  `CategoryTheory.ContinuousGAddCommGrp.resIsFinite` — restriction along a continuous
  homomorphism, on the finite continuous sets and the finite discrete modules.
* `Stacks.ConstantSheaf.abDictSheaf` and `Stacks.ConstantSheaf.abDictAction` — the two
  dictionaries out of which the transport of Tag 0DV5 (2) is built.

## Main results

* `Stacks.Sites.AbelianPullback.internalSheafPullbackSquare` — the square of
  `CategoryTheory.Sites.AbelianSheaf.internalSheaf` against the two inverse images commutes.
* `Stacks.ConstantSheaf.abDict_eq` — the transport of Tag 0DV5 (2) is the composite of the two
  dictionaries with the given equivalence of sheaves of sets, read on commutative group objects.

## Implementation notes

The only factor of the transport of Tag 0DV5 (2) depending on the equivalence of sheaves of sets
is `CategoryTheory.Functor.mapCommGrp` applied to it, which is why a commuting square for that
equivalence transports: the transport is `CategoryTheory.commGrpTransportSquare`. Its two
remaining inputs compare the vertical functors with their commutative-group counterparts, and
both are squares of lifts to full subcategories, so both come from
`CategoryTheory.Functor.squareOfAmbient` over an ambient square. On the sheaf side the ambient
square is `internalSheafPullbackSquare` below; on the action side it is
`CategoryTheory.resCommGrpContinuousGSetEquivalenceSquare`.

`internalSheafPullbackSquare` needs no exactness hypothesis beyond finite products: the direct
image of abelian sheaves is the direct image of sheaves of sets with its induced group
operations with no hypothesis at all, which is
`Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso`, and uniqueness of left adjoints
carries that to the inverse images, the left adjoint on the group-object side being
`CategoryTheory.Adjunction.mapCommGrp` of the adjunction of sheaves of sets. That last step is
where finite products enter, since `CategoryTheory.Functor.mapCommGrp` of the inverse image of
sheaves of sets has to be formed at all.

The two dictionaries are read off the definition of
`Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence`, so `abDict_eq`
holds by `rfl`. Their coefficient universe is determined by the site, which is why a square for
two sites needs them in one universe pair; the small étale sites of two schemes of one big étale
site satisfy this.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 0DV6](https://stacks.math.columbia.edu/tag/0DV6)
* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites

universe w v₁ v₂ u₁ u₂ uG

attribute [local instance] cartesianMonoidalSheafType braidedSheafType
  discreteForget₂Type discreteForget₂AddCommGrpCat
  cartesianMonoidalContinuousGSet braidedContinuousGSet
  CategoryTheory.braidedContinuousGSetIsFinite
  CategoryTheory.braidedι_continuousGSetIsFinite

/-! ### The inverse image of abelian sheaves as the inverse image of sheaves of sets -/

namespace Stacks.Sites.AbelianPullback

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]
  [(F.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [(F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
  [PreservesFiniteProducts (F.sheafPullback (Type w) J K)]

/-- The inverse image of sheaves of sets is braided, which is the hypothesis that it preserves
finite products. -/
local instance braidedSheafPullbackType : (F.sheafPullback (Type w) J K).Braided :=
  .ofChosenFiniteProducts _

/-- The direct image of sheaves of sets is braided: it is a right adjoint, hence preserves all
limits. -/
local instance braidedSheafPushforwardTypeOfAdjoint :
    (F.sheafPushforwardContinuous (Type w) J K).Braided :=
  have : PreservesLimitsOfSize.{0, 0} (F.sheafPushforwardContinuous (Type w) J K) :=
    (F.sheafAdjunctionContinuous (Type w) J K).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (F.sheafPushforwardContinuous (Type w) J K) := inferInstance
  .ofChosenFiniteProducts _

/-- **The inverse image of abelian sheaves is the inverse image of the underlying sheaves of sets
carrying the induced group operations.** Both are left adjoint to the direct image of abelian
sheaves, which is the direct image of sheaves of sets with its induced operations by
`Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso`; the left adjoint of that composite is
built from the adjunction of sheaves of sets read on commutative group objects
(`CategoryTheory.Adjunction.mapCommGrp`) and the two directions of the group-object dictionary
for abelian sheaves. -/
public def abelianSheafPullbackIso :
    F.sheafPullback AddCommGrpCat.{w} J K ≅
      AbelianSheaf.internalSheaf J ⋙ (F.sheafPullback (Type w) J K).mapCommGrp ⋙
        AbelianSheaf.externalSheaf K :=
  (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).leftAdjointUniq
    ((((AbelianSheaf.equivalence J).toAdjunction).comp
        (((F.sheafAdjunctionContinuous (Type w) J K).mapCommGrp).comp
          (AbelianSheaf.equivalence K).symm.toAdjunction)).ofNatIsoRight
      (abelianSheafPushforwardIso F J K))

/-- **The square of the group-object dictionary for abelian sheaves against the two inverse
images commutes.** Internalizing the group operations of an abelian sheaf and then taking the
inverse image of the resulting commutative group object in sheaves of sets is taking the inverse
image of the abelian sheaf and internalizing afterwards. -/
public def internalSheafPullbackSquare :
    AbelianSheaf.internalSheaf J ⋙ (F.sheafPullback (Type w) J K).mapCommGrp ≅
      F.sheafPullback AddCommGrpCat.{w} J K ⋙ AbelianSheaf.internalSheaf K :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft
      (AbelianSheaf.internalSheaf J ⋙ (F.sheafPullback (Type w) J K).mapCommGrp)
      (AbelianSheaf.externalInternalIso K).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (abelianSheafPullbackIso F J K).symm
      (AbelianSheaf.internalSheaf K)

end Stacks.Sites.AbelianPullback

/-! ### Restriction of the action on the finite objects -/

namespace AlgebraicGeometry

variable {G H : Type uG} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  (φ : G →ₜ* H)

/-- **Restriction along `φ : G →ₜ* H` on the finite continuous sets.** The underlying set is
unchanged, so it stays finite. -/
public def ContinuousGSet.resIsFinite :
    (ContinuousGSet.isFinite H).FullSubcategory ⥤ (ContinuousGSet.isFinite G).FullSubcategory :=
  (ContinuousGSet.isFinite G).lift
    ((ContinuousGSet.isFinite H).ι ⋙ ContinuousGSet.res φ) fun X ↦ X.property

/-- Restriction on the finite continuous sets is restriction on all of them. -/
public theorem ContinuousGSet.resIsFinite_comp_ι :
    ContinuousGSet.resIsFinite φ ⋙ (ContinuousGSet.isFinite G).ι =
      (ContinuousGSet.isFinite H).ι ⋙ ContinuousGSet.res φ := rfl

/-- Restriction on the finite continuous sets preserves finite products: the inclusion of the
finite objects creates them, and restriction on all continuous sets preserves them. -/
public instance resIsFinite_preservesFiniteProducts :
    PreservesFiniteProducts (ContinuousGSet.resIsFinite φ) :=
  letI : PreservesFiniteProducts
      (ContinuousGSet.resIsFinite φ ⋙ (ContinuousGSet.isFinite G).ι) := by
    rw [ContinuousGSet.resIsFinite_comp_ι]
    infer_instance
  preservesFiniteProducts_of_reflects_of_preserves _ (ContinuousGSet.isFinite G).ι

end AlgebraicGeometry

namespace CategoryTheory

variable {G H : Type uG} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  (φ : G →ₜ* H)

/-- **Restriction along `φ : G →ₜ* H` on the finite discrete modules.** The underlying abelian
group is unchanged, so it stays finite. -/
public def ContinuousGAddCommGrp.resIsFinite :
    (ContinuousGAddCommGrp.isFinite H).FullSubcategory ⥤
      (ContinuousGAddCommGrp.isFinite G).FullSubcategory :=
  (ContinuousGAddCommGrp.isFinite G).lift
    ((ContinuousGAddCommGrp.isFinite H).ι ⋙ ContinuousGAddCommGrp.res φ)
    fun X ↦ X.property

/-- Restriction on the finite discrete modules is restriction on all of them. -/
public theorem ContinuousGAddCommGrp.resIsFinite_comp_ι :
    ContinuousGAddCommGrp.resIsFinite φ ⋙ (ContinuousGAddCommGrp.isFinite G).ι =
      (ContinuousGAddCommGrp.isFinite H).ι ⋙ ContinuousGAddCommGrp.res φ := rfl

end CategoryTheory

/-! ### The two dictionaries of the transport of Tag 0DV5 (2) -/

namespace Stacks.ConstantSheaf

/-- The braiding of the finite locally constant sheaves of sets, as in
`Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence`. -/
local instance braidedFiniteLocallyConstantSetSheafHere {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) :
    BraidedCategory (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).FullSubcategory :=
  .ofCartesianMonoidalCategory

/-- The inclusion of the finite locally constant sheaves of sets is braided. -/
local instance braidedIotaFiniteLocallyConstantSetSheafHere {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) :
    (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).ι.Braided :=
  .ofChosenFiniteProducts _

section SheafDictionary

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u₁ v₁}]

/-- An abelian sheaf which is finite locally constant is a commutative group object of the
sheaves of sets whose underlying sheaf is finite locally constant. This is the first half of the
sheaf-side dictionary. -/
public def abDictSheafToCommGrpProp :
    (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).FullSubcategory ≌
      (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).commGrpProp.FullSubcategory :=
  (Sites.AbelianSheaf.equivalence J).congrFullSubcategory
    (commGrpProp_inverseImage_internalSheaf J)

/-- **The sheaf-side dictionary of the transport of Tag 0DV5 (2).** A finite locally constant
sheaf of abelian groups is a commutative group object among the finite locally constant sheaves
of sets. -/
public def abDictSheaf :
    (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).FullSubcategory ≌
      CommGrp (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).FullSubcategory :=
  (abDictSheafToCommGrpProp J).trans
    (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).commGrpEquivalence.symm

end SheafDictionary

section ActionDictionary

variable (G : Type uG) [Group G] [TopologicalSpace G]

/-- A commutative group object of the continuous `G`-sets whose underlying set is finite is a
finite discrete `G`-module. This is the second half of the action-side dictionary. -/
public def abDictActionFromCommGrpProp :
    (AlgebraicGeometry.ContinuousGSet.isFinite G).commGrpProp.FullSubcategory ≌
      (ContinuousGAddCommGrp.isFinite G).FullSubcategory :=
  (commGrpContinuousGSetEquivalence (G := G)).congrFullSubcategory
    (isFinite_inverseImage_commGrpContinuousGSetEquivalence G)

/-- **The action-side dictionary of the transport of Tag 0DV5 (2).** A finite discrete
`G`-module is a commutative group object among the finite continuous `G`-sets. -/
public def abDictAction :
    CommGrp (AlgebraicGeometry.ContinuousGSet.isFinite G).FullSubcategory ≌
      (ContinuousGAddCommGrp.isFinite G).FullSubcategory :=
  (AlgebraicGeometry.ContinuousGSet.isFinite G).commGrpEquivalence.trans
    (abDictActionFromCommGrpProp G)

end ActionDictionary

section Transport

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (G : Type uG) [Group G] [TopologicalSpace G]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u₁ v₁}]

/-- **The transport of Tag 0DV5 (2) is the two dictionaries with the given equivalence of sheaves
of sets read on commutative group objects.** The only factor depending on that equivalence is
`CategoryTheory.Functor.mapCommGrp` applied to it. -/
public theorem abDict_eq
    (e : (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).FullSubcategory ≌
      (AlgebraicGeometry.ContinuousGSet.isFinite G).FullSubcategory) :
    letI : e.functor.Braided := .ofChosenFiniteProducts _
    (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor =
      (abDictSheaf J).functor ⋙ e.functor.mapCommGrp ⋙ (abDictAction G).functor := rfl

end Transport

/-! ### The abelian square from the one for sheaves of sets -/

section Square

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u₁ v₁}]
  [∀ U : D, HasWeakSheafify (K.over U) AddCommGrpCat.{max u₁ v₁}]
  {GX GY : Type uG} [Group GX] [TopologicalSpace GX] [Group GY] [TopologicalSpace GY]
  (φ : GY →ₜ* GX)
  (pt : Sheaf J (Type (max u₁ v₁)) ⥤ Sheaf K (Type (max u₁ v₁)))
  [PreservesFiniteProducts pt]
  (pab : Sheaf J AddCommGrpCat.{max u₁ v₁} ⥤ Sheaf K AddCommGrpCat.{max u₁ v₁})

/-- The ambient inverse image of sheaves of sets is braided, which is the hypothesis that it
preserves finite products. -/
local instance braidedPt : pt.Braided := .ofChosenFiniteProducts _

/-- Restriction of continuous sets is braided. -/
local instance braidedRes : (AlgebraicGeometry.ContinuousGSet.res φ).Braided :=
  .ofChosenFiniteProducts _

/-- Restriction of finite continuous sets is braided. -/
local instance braidedResIsFinite :
    (AlgebraicGeometry.ContinuousGSet.resIsFinite φ).Braided :=
  .ofChosenFiniteProducts _

variable
  (hpt : ∀ A : Sheaf J (Type (max u₁ v₁)), isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J A →
    isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K (pt.obj A))

/-- The inverse image of sheaves of sets, read on the commutative group objects whose underlying
sheaf is finite locally constant. -/
public def pullbackCommGrpProp :
    (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).commGrpProp.FullSubcategory ⥤
      (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K).commGrpProp.FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ pt.mapCommGrp) fun A ↦ hpt _ A.property

/-- Restriction of continuous sets, read on the commutative group objects whose underlying set is
finite. -/
public def resCommGrpProp :
    (AlgebraicGeometry.ContinuousGSet.isFinite GX).commGrpProp.FullSubcategory ⥤
      (AlgebraicGeometry.ContinuousGSet.isFinite GY).commGrpProp.FullSubcategory :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (AlgebraicGeometry.ContinuousGSet.res φ).mapCommGrp)
    fun A ↦ A.property

/-- **The first half of the sheaf-side dictionary commutes with the two inverse images.** Both
vertical functors are lifts to full subcategories, so the square is the ambient one
`hint`. -/
public def abDictSheafToCommGrpPropSquare
    (Pab : (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).FullSubcategory ⥤
      (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} K).FullSubcategory)
    (hPab : Pab ⋙ (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} K).ι ≅
      (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).ι ⋙ pab)
    (hint : Sites.AbelianSheaf.internalSheaf J ⋙ pt.mapCommGrp ≅
      pab ⋙ Sites.AbelianSheaf.internalSheaf K) :
    (abDictSheafToCommGrpProp J).functor ⋙ pullbackCommGrpProp J K pt hpt ≅
      Pab ⋙ (abDictSheafToCommGrpProp K).functor :=
  Functor.squareOfAmbient
    (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).ι
    (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} K).ι
    (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).commGrpProp.ι
    (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K).commGrpProp.ι
    (Iso.refl _) (Iso.refl _) hPab (Iso.refl _) hint

/-- **The second half of the action-side dictionary commutes with the two restrictions.** Both
vertical functors are lifts to full subcategories, so the square is the ambient one
`CategoryTheory.resCommGrpContinuousGSetEquivalenceSquare`. -/
public def abDictActionFromCommGrpPropSquare :
    resCommGrpProp φ ⋙ (abDictActionFromCommGrpProp GY).functor ≅
      (abDictActionFromCommGrpProp GX).functor ⋙ ContinuousGAddCommGrp.resIsFinite φ :=
  Functor.squareOfAmbient
    (AlgebraicGeometry.ContinuousGSet.isFinite GX).commGrpProp.ι
    (ContinuousGAddCommGrp.isFinite GX).ι
    (AlgebraicGeometry.ContinuousGSet.isFinite GY).commGrpProp.ι
    (ContinuousGAddCommGrp.isFinite GY).ι
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (eqToIso (ContinuousGAddCommGrp.resIsFinite_comp_ι φ))
    (resCommGrpContinuousGSetEquivalenceSquare φ)

omit [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u₁ v₁}]
  [∀ U : D, HasWeakSheafify (K.over U) AddCommGrpCat.{max u₁ v₁}] in
/-- The inverse image of finite locally constant sheaves of sets preserves finite products: the
inclusion of the finite locally constant sheaves creates them and the ambient inverse image
preserves them. -/
public theorem preservesFiniteProducts_of_comp_ι
    (Pfin : (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).FullSubcategory ⥤
      (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K).FullSubcategory)
    (hPfin : Pfin ⋙ (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K).ι ≅
      (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).ι ⋙ pt) :
    PreservesFiniteProducts Pfin :=
  have : PreservesFiniteProducts
      (Pfin ⋙ (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K).ι) :=
    ⟨fun _ ↦ preservesLimitsOfShape_of_natIso hPfin.symm⟩
  preservesFiniteProducts_of_reflects_of_preserves _
    (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K).ι

/-- **The sheaf-side dictionary commutes with the two inverse images.** The first half is
`abDictSheafToCommGrpPropSquare` and the second is the square of
`CategoryTheory.ObjectProperty.commGrpEquivalence` for the lifted inverse image, which holds
because both of its legs become `CategoryTheory.Functor.mapCommGrpSquare` of `hPfin` after the
fully faithful inclusion. -/
public def abDictSheafPullbackSquare
    (Pfin : (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).FullSubcategory ⥤
      (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K).FullSubcategory)
    (hPfin : Pfin ⋙ (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K).ι ≅
      (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).ι ⋙ pt)
    (Pab : (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).FullSubcategory ⥤
      (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} K).FullSubcategory)
    (hPab : Pab ⋙ (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} K).ι ≅
      (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).ι ⋙ pab)
    (hint : Sites.AbelianSheaf.internalSheaf J ⋙ pt.mapCommGrp ≅
      pab ⋙ Sites.AbelianSheaf.internalSheaf K) :
    letI : PreservesFiniteProducts Pfin := preservesFiniteProducts_of_comp_ι J K pt Pfin hPfin
    letI : Pfin.Braided := .ofChosenFiniteProducts _
    Pab ⋙ (abDictSheaf K).functor ≅ (abDictSheaf J).functor ⋙ Pfin.mapCommGrp := by
  letI : PreservesFiniteProducts Pfin := preservesFiniteProducts_of_comp_ι J K pt Pfin hPfin
  letI : Pfin.Braided := .ofChosenFiniteProducts _
  have γ' : Pfin.mapCommGrp ⋙ (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K).commGrpι ≅
      (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).commGrpι ⋙
        pullbackCommGrpProp J K pt hpt :=
    Functor.fullyFaithfulCancelRight
      (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K).commGrpProp.ι
      (Functor.mapCommGrpSquare hPfin)
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (abDictSheafToCommGrpPropSquare J K pt pab hpt Pab hPab hint).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (abDictSheafToCommGrpProp J).functor
      (Equivalence.conjugateSquare
        (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).commGrpEquivalence
        (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K).commGrpEquivalence γ'.symm).symm ≪≫
    (Functor.associator _ _ _).symm

/-- **The square of `CategoryTheory.ObjectProperty.commGrpEquivalence` for restriction.** Both
legs become `CategoryTheory.Functor.mapCommGrpSquare` of the identification of restriction on the
finite continuous sets with restriction on all of them, after the fully faithful inclusion of the
commutative group objects with finite underlying set. -/
public def resCommGrpιSquare :
    (AlgebraicGeometry.ContinuousGSet.resIsFinite φ).mapCommGrp ⋙
        (AlgebraicGeometry.ContinuousGSet.isFinite GY).commGrpι ≅
      (AlgebraicGeometry.ContinuousGSet.isFinite GX).commGrpι ⋙ resCommGrpProp φ :=
  Functor.fullyFaithfulCancelRight
    (AlgebraicGeometry.ContinuousGSet.isFinite GY).commGrpProp.ι
    (Functor.mapCommGrpSquare
      (eqToIso (AlgebraicGeometry.ContinuousGSet.resIsFinite_comp_ι φ)))

/-- **The action-side dictionary commutes with the two restrictions.** -/
public def abDictActionResSquare :
    (AlgebraicGeometry.ContinuousGSet.resIsFinite φ).mapCommGrp ⋙
        (abDictAction GY).functor ≅
      (abDictAction GX).functor ⋙ ContinuousGAddCommGrp.resIsFinite φ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (resCommGrpιSquare φ) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (AlgebraicGeometry.ContinuousGSet.isFinite GX).commGrpι
      (abDictActionFromCommGrpPropSquare φ) ≪≫
    (Functor.associator _ _ _).symm

/-- **The square of Stacks Tag 0DV5 (2) against the inverse image and restriction, from the one
for sheaves of sets.** If the equivalences of sheaves of sets on the two sites carry the inverse
image to restriction along `φ`, then the transports of Tag 0DV5 (2) carry the inverse image of
finite locally constant abelian sheaves to restriction of finite discrete modules. -/
public def finiteLocallyConstantAbelianPullbackSquare
    (eX : (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).FullSubcategory ≌
      (AlgebraicGeometry.ContinuousGSet.isFinite GX).FullSubcategory)
    (eY : (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K).FullSubcategory ≌
      (AlgebraicGeometry.ContinuousGSet.isFinite GY).FullSubcategory)
    (Pfin : (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).FullSubcategory ⥤
      (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K).FullSubcategory)
    (hPfin : Pfin ⋙ (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} K).ι ≅
      (isFiniteLocallyConstantSetSheaf.{v₁, u₁, u₁} J).ι ⋙ pt)
    (Pab : (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).FullSubcategory ⥤
      (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} K).FullSubcategory)
    (hPab : Pab ⋙ (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} K).ι ≅
      (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).ι ⋙ pab)
    (hint : Sites.AbelianSheaf.internalSheaf J ⋙ pt.mapCommGrp ≅
      pab ⋙ Sites.AbelianSheaf.internalSheaf K)
    (α : eX.functor ⋙ AlgebraicGeometry.ContinuousGSet.resIsFinite φ ≅ Pfin ⋙ eY.functor) :
    (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J GX eX).functor ⋙
        ContinuousGAddCommGrp.resIsFinite φ ≅
      Pab ⋙ (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence K GY eY).functor := by
  letI : PreservesFiniteProducts Pfin := preservesFiniteProducts_of_comp_ι J K pt Pfin hPfin
  letI : Pfin.Braided := .ofChosenFiniteProducts _
  letI : eX.functor.Braided := .ofChosenFiniteProducts _
  letI : eY.functor.Braided := .ofChosenFiniteProducts _
  exact commGrpTransportSquare (abDictSheaf J) (abDictSheaf K) (abDictAction GX)
    (abDictAction GY)
    (abDictSheafPullbackSquare J K pt pab hpt Pfin hPfin Pab hPab hint)
    (abDictActionResSquare φ) α

end Square

end Stacks.ConstantSheaf

end
