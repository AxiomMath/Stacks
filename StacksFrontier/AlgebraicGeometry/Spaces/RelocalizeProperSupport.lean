module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeSupport

/-!
# Proper support across the relocalization of an algebraic space

Let `g : T ⟶ S` be a morphism of a big fppf site and `f : X ⟶ Y` a morphism of algebraic spaces
over `T`, locally of finite type. A closed subspace of `X` extends to a closed subspace of `Λ X`
with the corresponding set of points, and properness is unchanged by the extension, so a closed
subset of `X` is proper over `Y` (Stacks 0CZD) exactly when its image in `Λ X` is proper over
`Λ Y`. With the correspondence of supports, an abelian sheaf (or a module) on `X` has support
proper over `Y` exactly when the corresponding one on `Λ X` has support proper over `Λ Y`.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeSubfunctor`: the subfunctor of `Λ X` cut out by a subfunctor
  of `X`, isomorphic to its extension by `AlgebraicGeometry.Space.relocalizeSubfunctorIso`.

## Main results

* `AlgebraicGeometry.Space.isProperOver_relocalize_iff`: closed subsets proper over the target.
* `AlgebraicGeometry.Space.hasProperSupport_relocalize_iff`,
  `AlgebraicGeometry.Space.hasProperSupport_relocalizeModulesEquivalence_functor_iff` and
  `AlgebraicGeometry.Space.hasProperSupport_relocalizeModulesEquivalence_inverse_iff`: proper
  support is preserved and reflected.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.OverShriek

/-- The lower-shriek extension of presheaves preserves monomorphisms: a section of `Λ F` is a
factorization of the structure morphism together with a section of `F` over it. -/
instance relocalizePresheafFunctor_preservesMonomorphisms {C : Type*} [Category.{u} C]
    {U V : C} (f : V ⟶ U) : (relocalizePresheafFunctor f).PreservesMonomorphisms where
  preserves {F G} i _ := by
    rw [NatTrans.mono_iff_mono_app]
    intro W
    rw [CategoryTheory.mono_iff_injective]
    rintro ⟨⟨a, x⟩, ha⟩ ⟨⟨b, y⟩, hb⟩ h
    obtain rfl : a = b := congrArg (fun z => z.val.fst) h
    have hxy : i.app (op (Over.mk a)) x = i.app (op (Over.mk a)) y :=
      eq_of_heq (Sigma.mk.inj (congrArg Subtype.val h)).2
    obtain rfl : x = y := (CategoryTheory.mono_iff_injective (i.app _)).1 inferInstance hxy
    rfl

end CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) {X Y : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u}

private instance : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).RespectsIso := by
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact MorphismProperty.RespectsIso.inverseImage _ _

/-- **Closed immersions are preserved by the lower-shriek extension.** -/
theorem isClosedImmersion_relocalize_map {X' : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} {k : X' ⟶ X}
    (hk : IsClosedImmersion B T hT k) :
    IsClosedImmersion B S hS ((OverShriek.relocalizePresheafFunctor g).map k) := by
  exact OverShriek.presheaf_map_relocalize g (fun _ h => h) hk

/-- The subfunctor of `Λ X` cut out by a subfunctor of `X`: the image of its extension. -/
def relocalizeSubfunctor (Z : Subfunctor X) :
    Subfunctor ((OverShriek.relocalizePresheafFunctor g).obj X) :=
  Subfunctor.range ((OverShriek.relocalizePresheafFunctor g).map Z.ι)

/-- The extension of a subfunctor is the subfunctor it cuts out. -/
def relocalizeSubfunctorIso (Z : Subfunctor X) :
    (OverShriek.relocalizePresheafFunctor g).obj Z.toFunctor ≅
      (relocalizeSubfunctor B hT hS g Z).toFunctor :=
  @asIso _ _ _ _ (Subfunctor.toRange ((OverShriek.relocalizePresheafFunctor g).map Z.ι))
    (@Subfunctor.instIsIsoFunctorTypeToRangeOfMono _ _ _ _ _
      (Functor.map_mono (OverShriek.relocalizePresheafFunctor g) Z.ι))

/-- The isomorphism `AlgebraicGeometry.Space.relocalizeSubfunctorIso` is compatible with the
inclusions into `Λ X`. -/
theorem relocalizeSubfunctorIso_hom_ι (Z : Subfunctor X) :
    (relocalizeSubfunctorIso B hT hS g Z).hom ≫ (relocalizeSubfunctor B hT hS g Z).ι =
      (OverShriek.relocalizePresheafFunctor g).map Z.ι :=
  Subfunctor.toRange_ι _

/-- **The subfunctor of `Λ X` cut out by a closed subspace of `X` is a closed subspace.** -/
theorem isClosedSubspace_relocalizeSubfunctor {Z : Subfunctor X}
    (hZ : IsClosedSubspace B T hT Z) :
    IsClosedSubspace B S hS (relocalizeSubfunctor B hT hS g Z) := by
  refine ⟨(isAlgebraicSpace_relocalize' B hT hS g Z.toFunctor hZ.1).of_iso
    (relocalizeSubfunctorIso B hT hS g Z), ?_⟩
  have h := isClosedImmersion_relocalize_map B hT hS g hZ.2
  rw [← relocalizeSubfunctorIso_hom_ι B hT hS g Z] at h
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).1 h

/-- The points of the subfunctor of `Λ X` cut out by a subfunctor of `X` are the points of that
subfunctor, read in `Λ X`. -/
theorem range_pointsMap_relocalizeSubfunctor_ι (Z : Subfunctor X) :
    Set.range (pointsMap B S hS _ (relocalizeSubfunctor B hT hS g Z).ι) =
      pointsRelocalize B T S hT hS g X '' Set.range (pointsMap B T hT _ Z.ι) := by
  have hsurj : Function.Surjective
      (pointsMap B S hS _ (relocalizeSubfunctorIso B hT hS g Z).hom) := fun y =>
    ⟨pointsMap B S hS _ (relocalizeSubfunctorIso B hT hS g Z).inv y, by
      rw [← Function.comp_apply (f := pointsMap B S hS _ (relocalizeSubfunctorIso B hT hS g Z).hom),
        ← pointsMap_comp, Iso.inv_hom_id, pointsMap_id, id]⟩
  rw [← hsurj.range_comp, ← pointsMap_comp, relocalizeSubfunctorIso_hom_ι,
    ← (pointsRelocalize_surjective B T S hT hS g Z.toFunctor).range_comp, ← Set.range_comp]
  exact congrArg Set.range
    (funext fun x => (pointsRelocalize_naturality B T S hT hS g Z.ι x).symm)

variable (hX : IsAlgebraicSpace B T hT X) (hY : IsAlgebraicSpace B T hT Y) (f : X ⟶ Y)

/-- **A closed subset of `X` is proper over `Y` exactly when its image in `Λ X` is proper over
`Λ Y`.** -/
theorem isProperOver_relocalize_iff (hf : IsLocallyOfFiniteType B T hT f)
    (Z : Set (points B T hT X)) (hZ : IsClosed Z) :
    IsProperOver B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX)
        (isAlgebraicSpace_relocalize' B hT hS g Y hY)
        ((OverShriek.relocalizePresheafFunctor g).map f)
        ((isLocallyOfFiniteType_relocalize_iff B T hT S hS g f).2 hf)
        (pointsRelocalize B T S hT hS g X '' Z)
        (isClosedMap_pointsRelocalize B T S hT hS g X Z hZ) ↔
      IsProperOver B T hT hX hY f hf Z hZ := by
  let R := reducedClosedSubspace B T hT X hX Z hZ
  have hR'c := isClosedSubspace_relocalizeSubfunctor B hT hS g
    (isClosedSubspace_reducedClosedSubspace B T hT X hX Z hZ)
  have hR'pts : Set.range (pointsMap B S hS _ (relocalizeSubfunctor B hT hS g R).ι) =
      pointsRelocalize B T S hT hS g X '' Z := by
    rw [range_pointsMap_relocalizeSubfunctor_ι,
      range_pointsMap_ι_reducedClosedSubspace B T hT X hX Z hZ]
  have key : IsProper B S hS ((relocalizeSubfunctor B hT hS g R).ι ≫
        (OverShriek.relocalizePresheafFunctor g).map f) ↔ IsProper B T hT (R.ι ≫ f) := by
    refine (isProper_isIso_comp_iff B S hS
      (relocalizeSubfunctorIso B hT hS g R).hom _).symm.trans ?_
    rw [← Category.assoc, relocalizeSubfunctorIso_hom_ι, ← Functor.map_comp]
    exact isProper_relocalize_iff B T hT S hS g
      (isAlgebraicSpace_reducedClosedSubspace B T hT X hX Z hZ) hY (R.ι ≫ f)
  have hiff := isProper_reducedClosedSubspace_iff_exists B S hS
    (isAlgebraicSpace_relocalize' B hT hS g X hX) (isAlgebraicSpace_relocalize' B hT hS g Y hY)
    _ ((isLocallyOfFiniteType_relocalize_iff B T hT S hS g f).2 hf) _
    (isClosedMap_pointsRelocalize B T S hT hS g X Z hZ)
  have hall := exists_isProper_closedSubspace_iff_forall B S hS
    (isAlgebraicSpace_relocalize' B hT hS g X hX) (isAlgebraicSpace_relocalize' B hT hS g Y hY)
    _ ((isLocallyOfFiniteType_relocalize_iff B T hT S hS g f).2 hf) _
    (isClosedMap_pointsRelocalize B T S hT hS g X Z hZ)
  exact ⟨fun h => key.1 (hall.1 (hiff.1 h) _ hR'c hR'pts),
    fun h => hiff.2 ⟨_, hR'c, hR'pts, key.2 h⟩⟩

omit hX in
/-- Properness over the target of a closed subset only depends on the subset. -/
private theorem isProperOver_congr {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) {s t : Set (points B S hS X)} (hst : s = t)
    (hs : IsClosed s) (ht : IsClosed t) :
    IsProperOver B S hS hX hY f hf s hs ↔ IsProperOver B S hS hX hY f hf t ht := by
  subst hst
  rfl

/-- **Proper support of an abelian sheaf on `Λ X`, read on `X`.** The restriction of `M` to the
small étale site of `X` has support proper over `Y` exactly when `M` has support proper over
`Λ Y`. -/
theorem hasProperSupport_relocalize_iff (hf : IsLocallyOfFiniteType B T hT f)
    (M : Sheaf (SmallEtale.topology B S hS ((OverShriek.relocalizePresheafFunctor g).obj X))
      AddCommGrpCat.{v}) :
    HasProperSupport B T hT hX hY f hf
        (((SmallEtale.relocalize B hT hS g X hX).functor.sheafPushforwardContinuous
          AddCommGrpCat.{v} (SmallEtale.topology B T hT X) (SmallEtale.topology B S hS _)).obj M) ↔
      HasProperSupport B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX)
        (isAlgebraicSpace_relocalize' B hT hS g Y hY)
        ((OverShriek.relocalizePresheafFunctor g).map f)
        ((isLocallyOfFiniteType_relocalize_iff B T hT S hS g f).2 hf) M := by
  have hsupp := supportOfSheaf_relocalize_eq_image B hT hS g hX M
  constructor
  · rintro ⟨hcl, hp⟩
    have hcl₁ := isClosedMap_pointsRelocalize B T S hT hS g X _ hcl
    have hcl₂ : IsClosed (supportOfSheaf B S hS _ M) := hsupp ▸ hcl₁
    exact ⟨hcl₂, (isProperOver_congr B hS (isAlgebraicSpace_relocalize' B hT hS g X hX)
      (isAlgebraicSpace_relocalize' B hT hS g Y hY) ((OverShriek.relocalizePresheafFunctor g).map f)
      ((isLocallyOfFiniteType_relocalize_iff B T hT S hS g f).2 hf) hsupp.symm hcl₁ hcl₂).1
      ((isProperOver_relocalize_iff B hT hS g hX hY f hf _ hcl).2 hp)⟩
  · rintro ⟨hcl, hp⟩
    have hcl' : IsClosed (supportOfSheaf B T hT X
        (((SmallEtale.relocalize B hT hS g X hX).functor.sheafPushforwardContinuous
          AddCommGrpCat.{v} (SmallEtale.topology B T hT X)
            (SmallEtale.topology B S hS _)).obj M)) := by
      rw [supportOfSheaf_relocalize B hT hS g hX M]
      exact hcl.preimage (continuous_pointsRelocalize B T S hT hS g X)
    exact ⟨hcl', (isProperOver_relocalize_iff B hT hS g hX hY f hf _ hcl').1
      ((isProperOver_congr B hS (isAlgebraicSpace_relocalize' B hT hS g X hX)
        (isAlgebraicSpace_relocalize' B hT hS g Y hY)
        ((OverShriek.relocalizePresheafFunctor g).map f)
        ((isLocallyOfFiniteType_relocalize_iff B T hT S hS g f).2 hf) hsupp hcl
        (isClosedMap_pointsRelocalize B T S hT hS g X _ hcl')).1 hp)⟩

omit hY f in
/-- The abelian sheaf of the `𝒪_X`-module attached to an `𝒪_{Λ X}`-module is the restriction of
the abelian sheaf of the latter. -/
theorem toSheaf_relocalizeModulesEquivalence_inverse_obj
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX)) :
    (SheafOfModules.toSheaf _).obj ((relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M) =
      ((SmallEtale.relocalize B hT hS g X hX).functor.sheafPushforwardContinuous
        AddCommGrpCat.{u} (SmallEtale.topology B T hT X) (SmallEtale.topology B S hS _)).obj
        ((SheafOfModules.toSheaf _).obj M) :=
  rfl

/-- **Proper support is invariant under relocalization**, read from `Λ X`: the `𝒪_X`-module
attached to an `𝒪_{Λ X}`-module `M` has support proper over `Y` exactly when `M` has support
proper over `Λ Y`. -/
theorem hasProperSupport_relocalizeModulesEquivalence_inverse_iff
    (hf : IsLocallyOfFiniteType B T hT f)
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX)) :
    HasProperSupport B T hT hX hY f hf ((SheafOfModules.toSheaf _).obj
        ((relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M)) ↔
      HasProperSupport B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX)
        (isAlgebraicSpace_relocalize' B hT hS g Y hY)
        ((OverShriek.relocalizePresheafFunctor g).map f)
        ((isLocallyOfFiniteType_relocalize_iff B T hT S hS g f).2 hf)
        ((SheafOfModules.toSheaf _).obj M) :=
  hasProperSupport_relocalize_iff B hT hS g hX hY f hf ((SheafOfModules.toSheaf _).obj M)

/-- **Proper support is invariant under relocalization.** An `𝒪_X`-module has support proper
over `Y` along `f` exactly when the corresponding `𝒪_{Λ X}`-module has support proper over
`Λ Y` along `Λ f`. -/
theorem hasProperSupport_relocalizeModulesEquivalence_functor_iff
    (hf : IsLocallyOfFiniteType B T hT f) (F : Modules.{u, u} B T hT X hX) :
    HasProperSupport B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX)
        (isAlgebraicSpace_relocalize' B hT hS g Y hY)
        ((OverShriek.relocalizePresheafFunctor g).map f)
        ((isLocallyOfFiniteType_relocalize_iff B T hT S hS g f).2 hf)
        ((SheafOfModules.toSheaf _).obj
          ((relocalizeModulesEquivalence B hT hS g X hX).functor.obj F)) ↔
      HasProperSupport B T hT hX hY f hf ((SheafOfModules.toSheaf _).obj F) := by
  refine (hasProperSupport_relocalizeModulesEquivalence_inverse_iff B hT hS g hX hY f hf
    ((relocalizeModulesEquivalence B hT hS g X hX).functor.obj F)).symm.trans ?_
  have h : supportOfSheaf B T hT X ((SheafOfModules.toSheaf _).obj
        ((relocalizeModulesEquivalence B hT hS g X hX).inverse.obj
          ((relocalizeModulesEquivalence B hT hS g X hX).functor.obj F))) =
      supportOfSheaf B T hT X ((SheafOfModules.toSheaf _).obj F) :=
    (supportOfSheaf_eq_of_isoSheaf B T hT X hX ((SheafOfModules.toSheaf _).mapIso
      ((relocalizeModulesEquivalence B hT hS g X hX).unitIso.app F))).symm
  constructor
  · rintro ⟨hcl, hp⟩
    have hcl' : IsClosed (supportOfSheaf B T hT X ((SheafOfModules.toSheaf _).obj F)) := h ▸ hcl
    exact ⟨hcl', (isProperOver_congr B hT hX hY f hf h hcl hcl').1 hp⟩
  · rintro ⟨hcl, hp⟩
    have hcl' : IsClosed (supportOfSheaf B T hT X ((SheafOfModules.toSheaf _).obj
        ((relocalizeModulesEquivalence B hT hS g X hX).inverse.obj
          ((relocalizeModulesEquivalence B hT hS g X hX).functor.obj F)))) := h.symm ▸ hcl
    exact ⟨hcl', (isProperOver_congr B hT hX hY f hf h.symm hcl hcl').1 hp⟩

end AlgebraicGeometry.Space

end
