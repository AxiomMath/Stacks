module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections

/-!
# The restriction unit of Tag 08DF is the unit of the derived adjunction `j^* ⊣ Rj_*`

[Stacks, Tag 08DF] is stated for an open subspace `U` of a *ringed space*, through the
restriction and direct-image functors `jStar U O` and `jPush U O` of
`StacksFrontier/Topology/Sheaves/OpenImmersion/ModuleExtensionByZero.lean`, and it is parametric in
an arbitrary right derived functor `(Rj, αj)` of `jPush U O`. Its conclusion is about the map
`derivedPushforwardRestrictionUnit O U Rj αj`, constructed by descending the underived unit of
`j^* ⊣ j_*` along the localization `Qh`. The consumer — the generation step
`Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_openImmersion` of
`StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/DerivedRestrictAdjunction.lean` — speaks of
an open immersion of *schemes*, through `AlgebraicGeometry.Scheme.Modules.restrictFunctor` and
`Stacks.Duality.derivedPushforward`, and its hypothesis `hunit` is about the unit of the
adjunction `derivedRestrictPushforwardAdjunction`. This file identifies the two.

The identification is in two halves.

The first is abstract and is the content: for an adjunction `adj : F ⊣ G` of additive functors
between abelian categories with `F` exact, a right derived functor `(RG, β)` of `G`, and
K-injective resolutions in the target, the natural transformation obtained by descending the
degreewise unit of `adj` along `Qh` **is** the unit of
`Stacks.SmallDerivedCategory.derivedAdjunction`. Both are preimages under
`Localization.fullyFaithfulWhiskeringLeft`, so it suffices to compare them after whiskering with
`Qh`, where the derived unit is pinned down by
`Stacks.SmallDerivedCategory.derivedAdjunction_unit_app_Qh`; what remains is the identity
`homotopyAdjunction_unit_eq`, which says that the unit of the homotopy-category adjunction is the
degreewise unit, in the spelling Tag 08DF uses.

The second half is the crossing between the two spellings of a sheaf of modules on an open
subscheme. The categories agree definitionally:
`resRing U Y.ringCatSheaf = U.toScheme.ringCatSheaf` holds by `rfl`, hence so does
`SheafOfModules (resRing U Y.ringCatSheaf) = U.toScheme.Modules`. The *functors* do not: Mathlib's
`restrictFunctor U.ι` is `SheafOfModules.pushforward` along `U.ι.opensFunctor` for the structural
ring morphism built from `U.ι.appIso`, while `jStar U O` uses the identity ring morphism, and
`Scheme.Opens.ι_appIso` is proved by `ext1; simp` rather than by `rfl`. So the two are equal but
not definitionally equal; `jStar_eq_restrictFunctor` proves the equality, `jPush_eq_pushforward` is
`rfl`, and `restrictAdjunction_unit_heq` transports the unit across using that
`SheafOfModules.pushforwardPushforwardAdj` depends on its two ring morphisms only through their
values. `isIso_descendedUnit_app_of_eq` then substitutes those equalities and reduces to Tag 08DF.

## Main results

* `Stacks.SmallDerivedCategory.descendedUnit_eq_derivedAdjunction_unit` — the abstract
  identification.
* `Stacks.Duality.OpenImmersion.derivedPushforwardRestrictionUnit_eq_derivedAdjunction_unit` —
  Tag 08DF's map is an adjunction unit.
* `Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction_unit_eq_descendedUnit` — the
  consumer's unit has the same shape.
* `isIso_derivedRestrictPushforwardAdjunction_unit_app_of_cohomologySupportedOn` — **Tag 08DF,
  part (1), for an open subscheme of a scheme**, at an arbitrary model of the two derived
  categories.
* `isIso_liftDerivedRestrictPushforwardAdjunction_unit_app_of_cohomologySupportedOn` — the same
  after restricting to full subcategories, which is the shape of the `hunit` hypothesis of the
  generation step.

## Implementation notes

No `HasDerivedCategory.standard` appears in any statement here: every derived category is an
instance argument, inherited from Tag 08DF and from `derivedRestrictPushforwardAdjunction`, both of
which were restated at a free model. This is what makes the results usable at the locally small
model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, the only model at which the
compact-generation statements of [Stacks, Tag 09IS] and [Stacks, Tag 0A9A] have content.

The three-spellings crossing forces positional instance arguments in two places: the
`CohomologySupportedOn` hypothesis of the two scheme-level statements names the
`HasDerivedCategory` instance explicitly, because instance search does not cross `Y.Modules`
against `SheafOfModules Y.ringCatSheaf`; and the appeal to Tag 08DF inside
`isIso_descendedUnit_app_of_eq` passes all six of its instance arguments by hand. Both are the
device recorded for this crossing; no `set_option` is used.

The gap to `hunit` is not a model problem and not a crossing: Tag 08DF's hypothesis is
`CohomologySupportedOn O T E`, while `hunit` asks for right orthogonality to the shifts of the
Koszul object, and the passage from the second to the first is [Stacks, Tag 09IR]. The
implication `(2) ⇒ (1)` of 09IR is proved and tagged, as `Stacks.Koszul.Truncation.isIso_unit_of_hom_koszulObject_eq_zero` of
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineSituation.lean`
(registered for 09IR, implication (2) to (1)), and it bypasses the passage described
above: it concludes
the invertibility of the unit of `derivedRestrictPushforwardAdjunction` from right orthogonality
to the shifts of the Koszul object, with no `CohomologySupportedOn` anywhere in it, and
`CategoryTheory.Adjunction.isIso_restrictFullyFaithful_unit_app_iff` carries that to the lifted
unit `hunit` names. What it asks instead of `CohomologySupportedOn` is that the
object lie in `D_QCoh`, and it is stated on
`Spec A` with `j` the open complement of a finite sequence. So what is left of the gap is the two
restrictions of that statement — the affine base and the Koszul-complement shape of `j` — and not
the tag.

## References

* [The Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [The Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [The Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry TopologicalSpace ExtensionByZeroModules

universe w u v₁ v₂ u₁ u₂

namespace Stacks.SmallDerivedCategory

variable {C₁ : Type*} [Category* C₁] [Abelian C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂]
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} [F.Additive] [G.Additive]

/-- The functor induced on homotopy categories by the identity functor is the identity. -/
def mapHomotopyCategoryIdIso (C : Type*) [Category* C] [Preadditive C] :
    (𝟭 C).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory C (ComplexShape.up ℤ)) :=
  CategoryTheory.Quotient.natIsoLift _
    (isoWhiskerRight (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ))
      (HomotopyCategory.quotient _ _))

section Components

private lemma mapHomotopyCategoryFactors_inv_app (K : CochainComplex C₁ ℤ) :
    (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K = 𝟙 _ := rfl

private lemma mapHomologicalComplex_unit (adj : F ⊣ G) :
    (adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit =
      NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ) := rfl

end Components

/-- **The unit of `homotopyAdjunction` is the degreewise unit, read on homotopy categories.**
Both sides are natural transformations `𝟙 ⟶ F_K ⋙ G_K`; the right-hand side is the spelling
used by [Stacks, Tag 08DF]. -/
lemma homotopyAdjunction_unit_eq (adj : F ⊣ G) :
    (homotopyAdjunction adj).unit =
      (mapHomotopyCategoryIdIso C₁).inv ≫
        NatTrans.mapHomotopyCategory adj.unit (ComplexShape.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv := by
  refine NatTrans.ext (funext fun Z => ?_)
  obtain ⟨M⟩ := Z
  refine (homotopyAdjunction_unit_app_quotient adj M).trans ?_
  have hcomp : (Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).inv.app M ≫
        (NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app M ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (ComplexShape.up ℤ)).inv.app M =
      (adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M := by
    ext n
    simp [mapHomologicalComplex_unit]
  have e : (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app M) = 𝟙 _ := by
    rw [mapHomotopyCategoryFactors_inv_app (F := F), mapHomotopyCategoryFactors_inv_app (F := G)]
    exact (Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _)
  refine ((congrArg (_ ≫ ·) e).trans (Category.comp_id _)).trans ?_
  exact (congrArg (HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).map hcomp).symm

section

variable [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (adj : F ⊣ G) (RG : DerivedCategory C₂ ⥤ DerivedCategory C₁)
  (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RG)

/-- The homotopy-category level comparison `𝟙 ⟶ F_K ⋙ Qh ⋙ RG` whose descent along the
localization `Qh` is `Stacks.SmallDerivedCategory.descendedUnit`. -/
def homotopyDescendedUnit :
    DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory C₁) ⟶
      DerivedCategory.Qh ⋙ (F.mapDerivedCategory ⋙ RG) :=
  whiskerRight (mapHomotopyCategoryIdIso C₁).inv DerivedCategory.Qh ≫
    whiskerRight (NatTrans.mapHomotopyCategory adj.unit (ComplexShape.up ℤ))
      DerivedCategory.Qh ≫
    whiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) β ≫
    whiskerRight F.mapDerivedCategoryFactorsh.inv RG

/-- **The descended unit `𝟙 ⟶ LF ⋙ RG`**: the unique natural transformation whose
restriction along the localization `Qh` is the degreewise unit of `adj` followed by the
comparison `β` for `RG`. This is the generic form of
`Stacks.Cohomology.PushforwardRestriction.derivedPushforwardRestrictionUnit`. -/
def descendedUnit : 𝟭 (DerivedCategory C₁) ⟶ F.mapDerivedCategory ⋙ RG :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _).preimage
      (homotopyDescendedUnit adj RG β)

/-- The restriction of `descendedUnit adj RG β` along `Qh` is `homotopyDescendedUnit adj RG β`. -/
lemma whiskerLeft_descendedUnit :
    whiskerLeft DerivedCategory.Qh (descendedUnit adj RG β) =
      homotopyDescendedUnit adj RG β := by
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _).map_preimage _

/-- `homotopyDescendedUnit adj RG β` is the unit of `homotopyAdjunction adj`, restricted along
`Qh`, followed by the comparison `β` and the inverse of `F.mapDerivedCategoryFactorsh`. -/
lemma homotopyDescendedUnit_eq :
    homotopyDescendedUnit adj RG β =
      whiskerRight (homotopyAdjunction adj).unit DerivedCategory.Qh ≫
        whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) β ≫
        whiskerRight F.mapDerivedCategoryFactorsh.inv RG := by
  rw [homotopyAdjunction_unit_eq adj, whiskerRight_comp, whiskerRight_comp]
  unfold homotopyDescendedUnit
  rw [Category.assoc, Category.assoc]

private lemma leftDerivedFactorsQh_refl_hom_app
    (Z : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    (leftDerivedFactorsQh (Iso.refl F.mapDerivedCategory)).hom.app Z =
      F.mapDerivedCategoryFactorsh.hom.app Z := by
  simp [leftDerivedFactorsQh]

/-- `descendedUnit` depends on the adjunction only through its unit. -/
lemma descendedUnit_congr {adj' : F ⊣ G} (h : adj.unit = adj'.unit) :
    descendedUnit adj RG β = descendedUnit adj' RG β := by
  unfold descendedUnit homotopyDescendedUnit
  rw [h]

variable (hC₂ : ∀ K : CochainComplex C₂ ℤ, ∃ (I : CochainComplex C₂ ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  [RG.IsRightDerivedFunctor β (HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ))]

include hC₂ in
/-- **The descended unit is the unit of the derived adjunction.** For an adjunction `F ⊣ G`
of additive functors between abelian categories with `F` exact, a right derived functor
`(RG, β)` of `G`, and K-injective resolutions in the target, the natural transformation
`𝟙 ⟶ LF ⋙ RG` obtained by descending the degreewise unit along the localization is exactly
the unit of `Stacks.SmallDerivedCategory.derivedAdjunction`. -/
theorem descendedUnit_eq_derivedAdjunction_unit :
    descendedUnit adj RG β =
      (derivedAdjunction adj (Iso.refl F.mapDerivedCategory) β hC₂).unit := by
  refine (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) _).map_injective ?_
  show whiskerLeft DerivedCategory.Qh (descendedUnit adj RG β) =
    whiskerLeft DerivedCategory.Qh _
  rw [whiskerLeft_descendedUnit, homotopyDescendedUnit_eq]
  refine NatTrans.ext (funext fun Z => ?_)
  have hd := derivedAdjunction_unit_app_Qh adj (Iso.refl F.mapDerivedCategory) β hC₂ Z
  rw [leftDerivedFactorsQh_refl_hom_app] at hd
  dsimp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  rw [← Category.assoc, ← hd, Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id_app]
  simp

end

end Stacks.SmallDerivedCategory

namespace Stacks.Duality.OpenImmersion

section RingedSpace

open Stacks.Cohomology.PushforwardRestriction

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (U : Opens X)
  [HasDerivedCategory (SheafOfModules.{u} O)]
  [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
  (Rj : DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤
    DerivedCategory (SheafOfModules.{u} O))
  (αj : (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)

/-- The restriction unit of [Stacks, Tag 08DF] is the generic descended unit of the underived
adjunction `j^* ⊣ j_*`. -/
lemma derivedPushforwardRestrictionUnit_eq_descendedUnit :
    derivedPushforwardRestrictionUnit O U Rj αj =
      Stacks.SmallDerivedCategory.descendedUnit (jStarAdjunction U O) Rj αj :=
  rfl

variable [Rj.IsRightDerivedFunctor αj (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
  (hC : ∀ K : CochainComplex (SheafOfModules.{u} (resRing U O)) ℤ,
    ∃ (I : CochainComplex (SheafOfModules.{u} (resRing U O)) ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)

/-- **The restriction unit of [Stacks, Tag 08DF] is the unit of the derived adjunction
`j^* ⊣ Rj_*`.** -/
theorem derivedPushforwardRestrictionUnit_eq_derivedAdjunction_unit :
    derivedPushforwardRestrictionUnit O U Rj αj =
      (Stacks.SmallDerivedCategory.derivedAdjunction (jStarAdjunction U O)
        (Iso.refl (jStar U O).mapDerivedCategory) αj hC).unit :=
  Stacks.SmallDerivedCategory.descendedUnit_eq_derivedAdjunction_unit _ _ _ _

/-- **[Stacks, Tag 08DF], part (1), read on the derived adjunction.** -/
theorem isIso_jStarDerivedAdjunction_unit_app_of_cohomologySupportedOn
    (T : Set X) (hT : IsClosed T) (hTU : T ⊆ U)
    (E : DerivedCategory (SheafOfModules.{u} O)) (hE : CohomologySupportedOn O T E) :
    IsIso ((Stacks.SmallDerivedCategory.derivedAdjunction (jStarAdjunction U O)
      (Iso.refl (jStar U O).mapDerivedCategory) αj hC).unit.app E) := by
  rw [← derivedPushforwardRestrictionUnit_eq_derivedAdjunction_unit O U Rj αj hC]
  exact isIso_derivedPushforwardRestriction_unit_of_supported O U T hT hTU Rj αj E hE

end RingedSpace

section Schemes

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-- **The unit of `derivedRestrictPushforwardAdjunction` is the descended underived unit**,
i.e. exactly the shape [Stacks, Tag 08DF] proves invertible. -/
theorem derivedRestrictPushforwardAdjunction_unit_eq_descendedUnit :
    (derivedRestrictPushforwardAdjunction j).unit =
      Stacks.SmallDerivedCategory.descendedUnit (Scheme.Modules.restrictAdjunction j)
        (Stacks.Duality.derivedPushforward j)
        ((Stacks.Duality.homotopyPushforward j).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))) :=
  (Stacks.SmallDerivedCategory.descendedUnit_eq_derivedAdjunction_unit _ _ _
    (AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective X)).symm

/-- **The subcategory lift costs nothing.** For strictly full subcategories `A ⊆ D(𝒪_Y)` and
`B ⊆ D(𝒪_X)` preserved by `j^*` and `Rj_*`, the unit of the restricted adjunction is invertible
at an object of `A` exactly when the unit of `j^* ⊣ Rj_*` is invertible at the underlying object:
the inclusion `A.ι` carries one to the other, and a fully faithful functor reflects
isomorphisms. -/
theorem isIso_liftDerivedRestrictPushforwardAdjunction_unit_app_iff
    (A : ObjectProperty (DerivedCategory Y.Modules))
    (B : ObjectProperty (DerivedCategory X.Modules))
    (hres : ∀ K : A.FullSubcategory, B ((derivedRestrict j).obj K.obj))
    (hpush : ∀ L : B.FullSubcategory,
      A ((Stacks.Duality.derivedPushforward j).obj L.obj))
    (E : A.FullSubcategory) :
    IsIso ((liftDerivedRestrictPushforwardAdjunction j A B hres hpush).unit.app E) ↔
      IsIso ((derivedRestrictPushforwardAdjunction j).unit.app E.obj) := by
  have h : A.ι.map ((liftDerivedRestrictPushforwardAdjunction j A B hres hpush).unit.app E) =
      (derivedRestrictPushforwardAdjunction j).unit.app E.obj := by
    unfold liftDerivedRestrictPushforwardAdjunction
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp [ObjectProperty.liftCompιIso]
  rw [← h]
  exact (isIso_iff_of_reflects_iso _ A.ι).symm

end Schemes

/-! ### The ringed-space spelling and the scheme spelling agree -/

section Crossing

/-- Generic transport: the unit of `pushforwardPushforwardAdj` depends on the two sheaf-of-rings
morphisms only through their values. -/
lemma pushforwardPushforwardAdj_unit_heq
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {G : D ⥤ C}
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    [Functor.IsContinuous F J K] [Functor.IsContinuous G K J]
    (adj : F ⊣ G)
    {φ φ' : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R}
    {ψ ψ' : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj S}
    (hφ : φ = φ') (hψ : ψ = ψ')
    (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom)
    (H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj)
    (H₁' : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      ψ'.hom ≫ G.op.whiskerLeft φ'.hom)
    (H₂' : φ'.hom ≫ F.op.whiskerLeft ψ'.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj) :
    HEq ((SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit :
          𝟭 (SheafOfModules.{u} R) ⟶
            SheafOfModules.pushforward.{u} φ ⋙ SheafOfModules.pushforward.{u} ψ)
      ((SheafOfModules.pushforwardPushforwardAdj adj φ' ψ' H₁' H₂').unit :
          𝟭 (SheafOfModules.{u} R) ⟶
            SheafOfModules.pushforward.{u} φ' ⋙ SheafOfModules.pushforward.{u} ψ') := by
  subst hφ hψ
  rfl

/-- The sheaf-of-rings morphism built into Mathlib's `Scheme.Modules.restrictFunctor`, for the
inclusion of an open subscheme. -/
def restrictRingHom (Y : Scheme.{u}) (U : Y.Opens) :
    U.toScheme.ringCatSheaf ⟶
      (U.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology U.toScheme) (Opens.grothendieckTopology Y)).obj
        Y.ringCatSheaf :=
  ⟨Functor.whiskerRight
    ({ app := fun V => (U.ι.appIso V.unop).inv } :
      U.toScheme.presheaf ⟶ U.ι.opensFunctor.op ⋙ Y.presheaf)
    (forget₂ CommRingCat RingCat)⟩

/-- Mathlib's restriction along the inclusion `U.ι` of an open subscheme is the pushforward of
sheaves of modules along `restrictRingHom Y U`. -/
lemma restrictFunctor_ι_eq (Y : Scheme.{u}) (U : Y.Opens) :
    Scheme.Modules.restrictFunctor U.ι =
      SheafOfModules.pushforward (restrictRingHom Y U) := rfl

/-- The ring morphism `restrictRingHom Y U` is the identity of `resRing U Y.ringCatSheaf`. -/
lemma restrictRingHom_eq_id (Y : Scheme.{u}) (U : Y.Opens) :
    restrictRingHom Y U = 𝟙 (resRing U Y.ringCatSheaf) := by
  refine Sheaf.hom_ext ?_
  ext V r
  simp only [restrictRingHom, Functor.whiskerRight_app, Scheme.Opens.ι_appIso, Iso.refl_inv]
  rfl

/-- `j^*` on a ringed space and Mathlib's restriction along the inclusion of an open subscheme
are the same functor. -/
theorem jStar_eq_restrictFunctor (Y : Scheme.{u}) (U : Y.Opens) :
    jStar U Y.ringCatSheaf = Scheme.Modules.restrictFunctor U.ι := by
  rw [restrictFunctor_ι_eq, restrictRingHom_eq_id]
  rfl

/-- `j_*` on a ringed space and Mathlib's direct image along the inclusion of an open subscheme
are the same functor. -/
theorem jPush_eq_pushforward (Y : Scheme.{u}) (U : Y.Opens) :
    jPush U Y.ringCatSheaf = Scheme.Modules.pushforward U.ι := rfl

/-- The unit of Mathlib's adjunction `Scheme.Modules.restrictAdjunction U.ι` agrees, up to the
equality of functors `jStar_eq_restrictFunctor`, with the unit of
`jStarAdjunction U Y.ringCatSheaf`. -/
theorem restrictAdjunction_unit_heq (Y : Scheme.{u}) (U : Y.Opens) :
    HEq (Scheme.Modules.restrictAdjunction U.ι).unit
      (jStarAdjunction U Y.ringCatSheaf).unit :=
  pushforwardPushforwardAdj_unit_heq _ (restrictRingHom_eq_id Y U) rfl _ _ _ _

open Stacks.Cohomology.PushforwardRestriction in
/-- **Transport of [Stacks, Tag 08DF], part (1), to any adjunction equal to `j^* ⊣ j_*`**, with
the two categories in the scheme spelling. -/
theorem isIso_descendedUnit_app_of_eq
    {Y : Scheme.{u}} (U : Y.Opens)
    [i₁ : HasDerivedCategory.{w} Y.Modules] [i₂ : HasDerivedCategory.{w} U.toScheme.Modules]
    {F : Y.Modules ⥤ U.toScheme.Modules} {G : U.toScheme.Modules ⥤ Y.Modules}
    [iF : F.Additive] [iLim : PreservesFiniteLimits F] [iColim : PreservesFiniteColimits F]
    [iG : G.Additive]
    (adj : F ⊣ G)
    (hF : F = jStar U Y.ringCatSheaf) (hG : G = jPush U Y.ringCatSheaf)
    (hu : HEq adj.unit (jStarAdjunction U Y.ringCatSheaf).unit)
    (Rj : DerivedCategory U.toScheme.Modules ⥤ DerivedCategory Y.Modules)
    (αj : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ Rj)
    [iRj : Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ))]
    (T : Set Y) (hT : IsClosed T) (hTU : T ⊆ U)
    (E : DerivedCategory Y.Modules)
    (hE : @CohomologySupportedOn _ Y.ringCatSheaf i₁ T E) :
    IsIso ((Stacks.SmallDerivedCategory.descendedUnit adj Rj αj).app E) := by
  subst hF hG
  rw [Stacks.SmallDerivedCategory.descendedUnit_congr adj Rj αj (eq_of_heq hu)]
  exact @isIso_derivedPushforwardRestriction_unit_of_supported _ Y.ringCatSheaf U T hT hTU
    i₁ i₂ Rj αj iRj E hE

open Stacks.Cohomology.PushforwardRestriction in
/-- **[Stacks, Tag 08DF], part (1), for the inclusion of an open subscheme**: if every
cohomology sheaf of `E` is supported on a closed `T ⊆ U`, the unit of the derived adjunction
`derivedRestrictPushforwardAdjunction U.ι : j^* ⊣ Rj_*` is invertible at `E`. -/
theorem isIso_derivedRestrictPushforwardAdjunction_unit_app_of_cohomologySupportedOn
    {Y : Scheme.{u}} (U : Y.Opens)
    [i₁ : HasDerivedCategory.{w} Y.Modules] [i₂ : HasDerivedCategory.{w} U.toScheme.Modules]
    (T : Set Y) (hT : IsClosed T) (hTU : T ⊆ U)
    (E : DerivedCategory Y.Modules)
    (hE : @CohomologySupportedOn _ Y.ringCatSheaf i₁ T E) :
    IsIso ((derivedRestrictPushforwardAdjunction U.ι).unit.app E) := by
  rw [derivedRestrictPushforwardAdjunction_unit_eq_descendedUnit]
  exact isIso_descendedUnit_app_of_eq U (Scheme.Modules.restrictAdjunction U.ι)
    (jStar_eq_restrictFunctor Y U).symm (jPush_eq_pushforward Y U).symm
    (restrictAdjunction_unit_heq Y U) _ _ T hT hTU E hE

open Stacks.Cohomology.PushforwardRestriction in
/-- **The hypothesis `hunit` of
`Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_openImmersion`, discharged
for objects with cohomology supported on a closed subset of the open.** What separates this from
`hunit` itself is exactly [Stacks, Tag 09IR]: `hunit` asks for objects right orthogonal to the
shifts of the Koszul object, and the passage from that to `CohomologySupportedOn` is 09IR. The
repository does have 09IR — the implication `(2) ⇒ (1)` is tagged on
`Stacks.Koszul.Truncation.isIso_unit_of_hom_koszulObject_eq_zero` of
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineSituation.lean`, which reaches
`hunit` without `CohomologySupportedOn` at all, for an object of `D_QCoh(𝒪_{Spec A})` and `j` the
open complement of a finite sequence. What this statement adds over it is the arbitrary `Y` and
the arbitrary quasi-compact open `U`. -/
theorem isIso_liftDerivedRestrictPushforwardAdjunction_unit_app_of_cohomologySupportedOn
    {Y : Scheme.{u}} (U : Y.Opens)
    [i₁ : HasDerivedCategory.{w} Y.Modules] [i₂ : HasDerivedCategory.{w} U.toScheme.Modules]
    (A : ObjectProperty (DerivedCategory Y.Modules))
    (B : ObjectProperty (DerivedCategory U.toScheme.Modules))
    (hres : ∀ K : A.FullSubcategory, B ((derivedRestrict U.ι).obj K.obj))
    (hpush : ∀ L : B.FullSubcategory,
      A ((Stacks.Duality.derivedPushforward U.ι).obj L.obj))
    (T : Set Y) (hT : IsClosed T) (hTU : T ⊆ U)
    (E : A.FullSubcategory) (hE : @CohomologySupportedOn _ Y.ringCatSheaf i₁ T E.obj) :
    IsIso ((liftDerivedRestrictPushforwardAdjunction U.ι A B hres hpush).unit.app E) :=
  (isIso_liftDerivedRestrictPushforwardAdjunction_unit_app_iff U.ι A B hres hpush E).mpr
    (isIso_derivedRestrictPushforwardAdjunction_unit_app_of_cohomologySupportedOn
      U T hT hTU E.obj hE)

end Crossing

end Stacks.Duality.OpenImmersion

end
